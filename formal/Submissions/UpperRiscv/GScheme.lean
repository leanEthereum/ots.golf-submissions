import Submissions.UpperRiscv.Valid

/-!
# Graph schemes with an accepted-index predicate

The paper scheme of `OptimalOTS.Dag` accepts an index when it is below `numCuts`. The
scheme of this root accepts an index when it lies in `validSet` (its 32 nibbles sum to
`target`), so that the machine reads the chain positions directly from the index.
Everything else (graph, key generation, signing loop, verification, strong-forgery experiment)
is the paper's definition verbatim.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- A graph-based one-time signature scheme whose disclosure sets are indexed by the accepted
indices. -/
structure GScheme where
  /-- The public computation. -/
  graph : Graph
  /-- The disclosure sets. -/
  sets : Idx → Finset (Fin graph.size)
  /-- The verifier must recompute the root. -/
  root_not_mem : ∀ i, graph.root ∉ sets i
  /-- The revealed values suffice: `sets i` meets every path from a secret source to the root. -/
  no_hidden_source :
    ∀ i v, graph.Visited (sets i) v → v ∉ sets i → ¬ (graph.kind v).IsSource
  /-- Signatures reveal at most `maxRevealBits` bits besides the nonce. -/
  reveal_le : ∀ i, graph.revealBits (sets i) ≤ (maxSignatureBits - nonceBits)
  /-- Key generation costs at most `keygenBudget`. -/
  keygen_le : graph.keygenCost ≤ keygenBudget

namespace GScheme

variable (S : GScheme)

/-- Resize the root value to `pkBits`: truncation keeps the low bits; extension pads with zeros. -/
def publicKey (x : S.graph.Assignment) : PublicKey := (x S.graph.root).setWidth pkBits

/-- Key generation; the secret key is the value of every node. -/
def keygen : OracleComp Spec (PublicKey × S.graph.Assignment) := do
  let x ← S.graph.keygen
  return (S.publicKey x, x)

/-- Signing with at most `k` further trials, never retrying a nonce in `tried`. -/
def signLoop (x : S.graph.Assignment) (m : Message) :
    ℕ → Finset Nonce → OracleComp Spec (Option Signature)
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp Spec (Fin (fresh.card - 1 + 1)))
      let η : Nonce := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let i ← index m η
      if hi : i ∈ validSet then
        return some (η, S.graph.encode (S.sets ⟨i, hi⟩) x)
      else
        signLoop x m k (insert η tried)
    else
      pure none

/-- Try at most `trials` distinct uniform nonces; return `none` if none selects a valid index. -/
def sign (x : S.graph.Assignment) (m : Message) : OracleComp Spec (Option Signature) :=
  S.signLoop x m trials ∅

/-- Reject invalid indices or payload lengths; otherwise reconstruct the root and compare its
public-key bits with `pk`. -/
def verify (pk : PublicKey) (m : Message) (σ : Signature) : OracleComp Spec Bool := do
  let i ← index m σ.1
  if hi : i ∈ validSet then
    let A := S.sets ⟨i, hi⟩
    if σ.2.length = S.graph.revealBits A then
      let y ← S.graph.reconstruct A (S.graph.decode A σ.2)
      return decide (S.publicKey y = pk)
    else
      return false
  else
    return false

/-- Verification cost at a valid index and payload length: the index query plus reconstruction. -/
def verifyCost (i : Idx) : ℕ := idxCost + S.graph.reconstructCost (S.sets i)

/-- Strong-forgery experiment. The attacker wins when its pair is accepted and differs from the
signed pair; after signing failure, any accepted pair wins. All parties share one oracle table. -/
def experiment (A : Adversary) : OracleComp Spec Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Strong unforgeability: for every attacker and pathwise budget `B` for the entire experiment,
the probability of an accepted fresh pair is strictly below `B / 2 ^ securityBits`. -/
def Secure : Prop :=
  ∀ (A : Adversary) (B : ℕ), CostAtMost (S.experiment A) B →
    probTrue (S.experiment A) < (B : ℝ≥0∞) / 2 ^ securityBits

end GScheme

end OptimalOTS
