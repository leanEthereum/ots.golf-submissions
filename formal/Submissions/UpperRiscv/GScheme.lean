import Submissions.UpperRiscv.Valid

/-!
# Graph schemes with an accepted-index predicate

The paper scheme of `OptimalOTS.Dag` accepts an index when it is below `numCuts`. The
scheme of this root reads its index as `pack` of the 256-bit answer to `H(message ‖ nonce)` (the
low bits of the first 28 bytes, packed) and accepts it when it lies in `validSet` (its 28 digits
sum to `target`), so that the machine reads the chain positions directly from the answer bytes.
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

/-! ### Exchanging the halves of an encoding input -/

theorem setWidth_append_lo {a b : ℕ} (x : BitVec a) (y : BitVec b) : (x ++ y).setWidth b = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi]

theorem extract_append_hi {a b : ℕ} (x : BitVec a) (y : BitVec b) :
    (x ++ y).extractLsb' b a = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_append,
    show ¬ (b + i < b) by omega, if_false, Nat.add_sub_cancel_left]

theorem append_extract_setWidth {a b : ℕ} (v : BitVec (a + b)) :
    v.extractLsb' b a ++ v.setWidth b = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split_ifs with h
  · simp [BitVec.getLsbD_setWidth, h]
  · rw [BitVec.getLsbD_extractLsb']
    have : i - b < a := by omega
    simp [this, show b + (i - b) = i by omega]

theorem getLsbD_cast' {n m : ℕ} (h : n = m) (x : BitVec n) (i : ℕ) :
    (x.cast h).getLsbD i = x.getLsbD i := by
  subst h; rfl

theorem setWidth_cast' {n m k : ℕ} (h : n = m) (x : BitVec n) :
    (x.cast h).setWidth k = x.setWidth k := by
  subst h; rfl

theorem extractLsb'_cast' {n m s l : ℕ} (h : n = m) (x : BitVec n) :
    (x.cast h).extractLsb' s l = x.extractLsb' s l := by
  subst h; rfl

/-- The two halves of an encoding input exchanged: the nonce above the message, as the machine
finds them in memory. -/
def swapHalves {w : ℕ} (u : BitVec (w + nonceBits)) : BitVec (w + nonceBits) :=
  (u.setWidth nonceBits ++ u.extractLsb' nonceBits w).cast (Nat.add_comm _ _)

/-- The inverse exchange. -/
def swapBack {w : ℕ} (v : BitVec (w + nonceBits)) : BitVec (w + nonceBits) :=
  v.setWidth w ++ v.extractLsb' w nonceBits

theorem swapHalves_append {w : ℕ} (m : BitVec w) (η : Nonce) :
    swapHalves (m ++ η) = (η ++ m).cast (Nat.add_comm _ _) := by
  unfold swapHalves
  rw [setWidth_append_lo, extract_append_hi]

theorem swapBack_swapHalves {w : ℕ} (u : BitVec (w + nonceBits)) : swapBack (swapHalves u) = u := by
  unfold swapBack swapHalves
  rw [setWidth_cast', extractLsb'_cast', setWidth_append_lo, extract_append_hi,
    append_extract_setWidth]

theorem swapHalves_swapBack {w : ℕ} (v : BitVec (w + nonceBits)) : swapHalves (swapBack v) = v := by
  unfold swapBack
  rw [swapHalves_append]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_cast', BitVec.getLsbD_append]
  by_cases h1 : i < w
  · rw [if_pos h1]
    simp [BitVec.getLsbD_setWidth, h1]
  · rw [if_neg h1]
    rw [BitVec.getLsbD_extractLsb']
    have : i - w < nonceBits := by omega
    simp [this, show w + (i - w) = i by omega]

theorem swapHalves_injective {w : ℕ} : Function.Injective (swapHalves (w := w)) := by
  intro u v h
  rw [← swapBack_swapHalves u, ← swapBack_swapHalves v, h]

/-! ### The extended message: the message above the public key -/

/-- The width of an extended message. -/
abbrev emsgBits : ℕ := msgBits + pkBits

/-- An extended message: the message above the public key, as the loader lays them out. -/
abbrev EMessage := BitVec emsgBits

/-- The extended message of `m` under the public key `pk`. -/
def emsg (m : Message) (pk : PublicKey) : EMessage := m ++ pk

theorem emsg_inj {m m' : Message} {pk pk' : PublicKey} (h : emsg m pk = emsg m' pk') :
    m = m' ∧ pk = pk' := by
  unfold emsg at h
  constructor
  · have := congrArg (fun v : BitVec (msgBits + pkBits) => v.extractLsb' pkBits msgBits) h
    simpa only [extract_append_hi] using this
  · have := congrArg (fun v : BitVec (msgBits + pkBits) => v.setWidth pkBits) h
    simpa only [setWidth_append_lo] using this

/-- The disclosure index selected by the extended message `M` and nonce `η`: the packed digits of
the answer to the query `η ‖ M`, that is `η ‖ m ‖ pk`. The index query shares the one oracle with
the graph's hash nodes. -/
def packIndex (M : EMessage) (η : Nonce) : OracleComp Spec ℕ :=
  (fun y => pack y) <$> hash (swapHalves (M ++ η))

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
      let i ← packIndex (emsg m (S.publicKey x)) η
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
  let i ← packIndex (emsg m pk) σ.1
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
