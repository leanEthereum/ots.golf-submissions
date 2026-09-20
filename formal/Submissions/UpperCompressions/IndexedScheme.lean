import OptimalOTS.Dag
import Submissions.UpperCompressions.Adapter

/-!
# DAG schemes with an explicit accepted-index count

The protected graph semantics, nonce format and trial budget are unchanged.
The submitted index program keeps the same query and takes127 output bits.
Only the scheme/program layer is generalized from `Dag.numCuts` to a parameter `M`.
This permits a cut family whose cardinality is not a power of two. No admissibility
or security of a particular new graph follows from this interface alone.

Graph and key-generation specialization helpers remain available. The
typed adapter preserves the full oracle experiment and its security statement.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.IndexedAnalysis

/-- Submitted index width; protected nonce and graph words remain128 bits. -/
def idxBits : ℕ := 127

end OptimalOTS.IndexedAnalysis

namespace OptimalOTS.SubmittedIndex

def index (m : Message) (η : Dag.Nonce) : OracleComp Spec ℕ :=
  (fun y => (y.setWidth IndexedAnalysis.idxBits).toNat) <$> hash (m ++ η)

end OptimalOTS.SubmittedIndex

namespace OptimalOTS.IndexedDag

/-- A DAG scheme with exactly `M` accepted disclosure indices. -/
structure Scheme (M : ℕ) where
  graph : Dag.Graph
  sets : Fin M → Finset (Fin graph.size)
  root_not_mem : ∀ i, graph.root ∉ sets i
  no_hidden_source :
    ∀ i v, graph.Visited (sets i) v → v ∉ sets i → ¬ (graph.kind v).IsSource
  reveal_le : ∀ i, graph.revealBits (sets i) + Dag.nonceBits ≤ maxSignatureBits
  keygen_le : graph.keygenCost ≤ keygenBudget

namespace Scheme

variable {M : ℕ} (S : Scheme M)

def publicKey (x : S.graph.Assignment) : PublicKey := (x S.graph.root).setWidth pkBits

def keygen : OracleComp Spec (PublicKey × S.graph.Assignment) := do
  let x ← S.graph.keygen
  return (S.publicKey x, x)

/-- The protected nonce-without-replacement program, accepting precisely indices below `M`. -/
def signLoop (x : S.graph.Assignment) (m : Message) :
    ℕ → Finset Dag.Nonce → OracleComp Spec (Option Dag.Signature)
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp Spec (Fin (fresh.card - 1 + 1)))
      let η : Dag.Nonce := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let i ← SubmittedIndex.index m η
      if hi : i < M then
        return some (η, S.graph.encode (S.sets ⟨i, hi⟩) x)
      else
        signLoop x m k (insert η tried)
    else
      pure none

def sign (x : S.graph.Assignment) (m : Message) : OracleComp Spec (Option Dag.Signature) :=
  S.signLoop x m Dag.trials ∅

def verify (pk : PublicKey) (m : Message) (σ : Dag.Signature) : OracleComp Spec Bool := do
  let i ← SubmittedIndex.index m σ.1
  if hi : i < M then
    let A := S.sets ⟨i, hi⟩
    if σ.2.length = S.graph.revealBits A then
      let y ← S.graph.reconstruct A (S.graph.decode A σ.2)
      return decide (S.publicKey y = pk)
    else
      return false
  else
    return false

def verifyCost (i : Fin M) : ℕ := Dag.idxCost + S.graph.reconstructCost (S.sets i)

/-- Reuse a valid cut as a constant family only to invoke protected key-generation lemmas.
This construction makes no security claim about the repeated disclosure sets. -/
def keygenProxy (i : Fin M) : Dag.Scheme where
  graph := S.graph
  sets := fun _ => S.sets i
  root_not_mem := fun _ => S.root_not_mem i
  no_hidden_source := fun _ => S.no_hidden_source i
  reveal_le := fun _ => S.reveal_le i
  keygen_le := S.keygen_le

@[simp] theorem keygenProxy_publicKey (i : Fin M) (x : S.graph.Assignment) :
    (S.keygenProxy i).publicKey x = S.publicKey x := rfl

@[simp] theorem keygenProxy_keygen (i : Fin M) :
    (S.keygenProxy i).keygen = S.keygen := rfl

/-- Convert the protected scheme without changing its graph or disclosure sets. -/
abbrev ofDag (S : Dag.Scheme) : Scheme Dag.numCuts where
  graph := S.graph
  sets := S.sets
  root_not_mem := S.root_not_mem
  no_hidden_source := S.no_hidden_source
  reveal_le := S.reveal_le
  keygen_le := S.keygen_le

/-- The reverse specialization at the protected acceptance count. -/
abbrev toDag (S : Scheme Dag.numCuts) : Dag.Scheme where
  graph := S.graph
  sets := S.sets
  root_not_mem := S.root_not_mem
  no_hidden_source := S.no_hidden_source
  reveal_le := S.reveal_le
  keygen_le := S.keygen_le

@[simp] theorem toDag_ofDag (S : Dag.Scheme) : (ofDag S).toDag = S := rfl

@[simp] theorem ofDag_toDag (S : Scheme Dag.numCuts) : ofDag S.toDag = S := rfl

@[simp] theorem ofDag_publicKey (S : Dag.Scheme) (x : S.graph.Assignment) :
    (ofDag S).publicKey x = S.publicKey x := rfl

@[simp] theorem ofDag_keygen (S : Dag.Scheme) : (ofDag S).keygen = S.keygen := rfl

/- The protected128-bit index programs do not specialize to this127-bit
prototype. Their sign/verify equalities are intentionally absent. -/

@[simp] theorem ofDag_verifyCost (S : Dag.Scheme) (i : Fin Dag.numCuts) :
    (ofDag S).verifyCost i = S.verifyCost i := rfl

/-- Same programs and injective wire encoding, with the existing typed proof interface. -/
def toAlgorithm : TypedScheme where
  SecretKey := S.graph.Assignment
  Signature := Dag.Signature
  encodeSignature := AlgorithmAdapter.encodeSignature
  encodeSignature_injective := AlgorithmAdapter.encodeSignature_injective
  keygen := S.keygen
  sign := S.sign
  verify := S.verify

end Scheme

/-- The adversary format is independent of the number of accepted indices. -/
def experiment {M : ℕ} (S : Scheme M) (A : Dag.Adversary) : OracleComp Spec Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

def Scheme.Secure {M : ℕ} (S : Scheme M) : Prop :=
  ∀ (A : Dag.Adversary) (B : ℕ), CostAtMost (experiment S A) B →
    probTrue (experiment S A) < (B : ℝ≥0∞) / 2 ^ securityBits

namespace AlgorithmAdapter

variable {M : ℕ} (S : Scheme M)

def toIndexedAdversary (A : S.toAlgorithm.Adversary) : Dag.Adversary where
  State := A.State
  choose := A.choose
  forge := A.forge

def fromIndexedAdversary (A : Dag.Adversary) : S.toAlgorithm.Adversary where
  State := A.State
  choose := A.choose
  forge := A.forge

theorem experiment_eq (A : S.toAlgorithm.Adversary) :
    S.toAlgorithm.experiment A = experiment S (toIndexedAdversary S A) := by
  simp only [TypedScheme.experiment, experiment, Scheme.toAlgorithm, toIndexedAdversary]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr
  intro ok
  congr 1
  by_cases h : signed.map (fun s => (chosen.1, s)) ≠ some (forged.1, forged.2) <;> simp [h]

theorem experiment_fromIndexed_eq (A : Dag.Adversary) :
    S.toAlgorithm.experiment (fromIndexedAdversary S A) = experiment S A := by
  simp only [TypedScheme.experiment, experiment, Scheme.toAlgorithm, fromIndexedAdversary]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr
  intro ok
  congr 1
  by_cases h : signed.map (fun s => (chosen.1, s)) ≠ some (forged.1, forged.2) <;> simp [h]

theorem secure_iff : S.toAlgorithm.Secure ↔ S.Secure := by
  constructor
  · intro h A B hB
    have he := experiment_fromIndexed_eq S A
    rw [← he] at hB ⊢
    exact h (fromIndexedAdversary S A) B hB
  · intro h A B hB
    rw [experiment_eq] at hB ⊢
    exact h (toIndexedAdversary S A) B hB

end AlgorithmAdapter

end OptimalOTS.IndexedDag
