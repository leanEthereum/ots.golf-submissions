import Submissions.UpperRiscv.ChainSplit
import Submissions.UpperRiscv.RejectAdapter

/-!
# The verifier with dispatch-time rejection, for every signature length

The machine reads the count byte `v` (signature bits 5456–5463) and rejects unless the 32 index
digits and `v` sum to 146 modulo 255. It hashes the free chain once, rejects `v ≥ 16`, finishes
the free chain with `v` as its digit, and then runs the sixteen pairs; an expanding left chain is
hashed once before its pair's cap is tested. Every signature runs through the whole verifier: the
chains read the signature padded with zeros to 5504 bits (`padded`), and the root query is the
first `a + 936` bits of the memory from the root region on, where `a = min |σ| 5505` is the
loaded length. The six bytes past the region remain zero (`rootTail`). The verdict is the public-key test and `a < 5465`.

`strictVerify` is the verifier of the security proof (`Forest.WireVerifier`): the forest verifier
on full-length signatures, this verifier on shorter ones, and immediate rejection of longer
ones. `stagedVerify` only adds terminal constant-answer suffixes to it (`strict_prunes_staged`).
-/

noncomputable section
open scoped Classical
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag
open Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph pkBits
attribute [local irreducible] Forest.fixedDigits

/-- Full node list of the remaining chain pairs, without any digit-cap rejection. -/
def pairNodes : (n q : ℕ) → List Name
  | 0, _ => []
  | n+1, q => if hq : q < 16 then
      chainNodes ⟨2*q+1, by omega⟩ ++ chainNodes ⟨2*q+2, by omega⟩ ++ pairNodes n (q+1)
    else []

/-- The signature as the loader leaves it in memory: its first 5504 bits, then zeros. -/
def padded (bits : List Bool) : List Bool :=
  bits.take 5504 ++ List.replicate (5504 - bits.length) false

theorem length_padded (bits : List Bool) : (padded bits).length = 5504 := by
  unfold padded
  simp only [List.length_append, List.length_take, List.length_replicate]
  omega

/-- The count byte: the free digit as the machine loads it. -/
def countByte (bits : List Bool) : ℕ := (ofBits 8 ((padded bits).drop 5456)).toNat

/-- The loaded signature suffix retained as an argument of the staged interface. -/
def sigTail (bits : List Bool) : BitVec 48 := ofBits 48 ((padded bits).drop 5456)

/-- The chain tops of an assignment. -/
def topsOf (x : graph.Assignment) : (k : Fin 33) → BitVec (topBits k) :=
  fun k => (x (tp k).fin).cast (lenF_fin _)

/-- The six bytes past the root region: outside all loader and chain writes, hence zero. -/
def rootTail (index : RawIdx) (v : ℕ) (tail : BitVec 48) (x : graph.Assignment) : BitVec 48 :=
  0

/-- The root query for the loaded length `a`, and the decision. -/
def rootStep (index : RawIdx) (v : ℕ) (pk : PublicKey) (a : ℕ) (tail : BitVec 48)
    (x : graph.Assignment) : OracleComp Spec Bool := do
  let y ← hash ((rootTail index v tail x ++ rootRegion (topsOf x)).setWidth (a + 936))
  return (decide (y.setWidth 128 = pk) && decide (a < 5465))

/-- The exact staged oracle program of the pairs. `payload` is already in chain execution
order. -/
def stagedBlocks (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey) (a : ℕ)
    (tail : BitVec 48) : (n q : ℕ) → graph.Assignment → ℕ → OracleComp Spec Bool
  | 0, _, x, _ => rootStep index v pk a tail x
  | n+1, q, x, cursor => if hq : q < 16 then do
      let r ← runNodes' index v payload (entryNodes index v ⟨2*q+1, by omega⟩) x cursor
      if PairAllowed index.val q then
        let r' ← runNodes' index v payload
          (tableNodes index v ⟨2*q+1, by omega⟩ ++ chainNodes ⟨2*q+2, by omega⟩) r.1 r.2
        stagedBlocks index v payload pk a tail n (q+1) r'.1 r'.2
      else pure false
    else pure false

attribute [local irreducible] stagedBlocks

/-- Machine-facing expansion: `some` changes the output interface, never the query trace. -/
theorem stagedBlocks_some_succ (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    (a : ℕ) (tail : BitVec 48) (n q : ℕ) (hq : q < 16) (x : graph.Assignment) (cursor : ℕ) :
    some <$> stagedBlocks index v payload pk a tail (n+1) q x cursor = (do
      let r ← runNodes' index v payload (entryNodes index v ⟨2*q+1, by omega⟩) x cursor
      if PairAllowed index.val q then
        let r' ← runNodes' index v payload
          (tableNodes index v ⟨2*q+1, by omega⟩ ++ chainNodes ⟨2*q+2, by omega⟩) r.1 r.2
        some <$> stagedBlocks index v payload pk a tail n (q+1) r'.1 r'.2
      else pure (some false)) := by
  rw [stagedBlocks, dif_pos hq, map_bind]
  congr 1
  funext r
  split_ifs <;> simp only [map_bind, map_pure]

theorem stagedBlocks_some_zero (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    (a : ℕ) (tail : BitVec 48) (q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    some <$> stagedBlocks index v payload pk a tail 0 q x cursor = (do
      let y ← hash ((rootTail index v tail x ++ rootRegion (topsOf x)).setWidth (a + 936))
      return some (decide (y.setWidth 128 = pk) && decide (a < 5465))) := by
  simp only [stagedBlocks, rootStep, map_bind, map_pure]

theorem stagedBlocks_eq_of_allowed (index : RawIdx) (v : ℕ) (payload : List Bool)
    (pk : PublicKey) (a : ℕ) (tail : BitVec 48) (n q : ℕ) (hq : q+n ≤ 16)
    (caps : ∀ j, q ≤ j → j < q+n → PairAllowed index.val j)
    (x : graph.Assignment) (cursor : ℕ) :
    stagedBlocks index v payload pk a tail n q x cursor =
      runNodes' index v payload (pairNodes n q) x cursor >>= fun r =>
        rootStep index v pk a tail r.1 := by
  induction n generalizing q x cursor with
  | zero => rw [stagedBlocks, pairNodes, runNodes', pure_bind]
  | succ n ih =>
    have hq16 : q < 16 := by omega
    rw [stagedBlocks, dif_pos hq16, pairNodes, dif_pos hq16]
    rw [chain_entry_split index v ⟨2*q+1, by omega⟩]
    simp only [List.append_assoc, runNodes'_append, bind_assoc]
    apply bind_congr
    intro r
    rw [if_pos (caps q le_rfl (by omega))]
    apply bind_congr
    intro r'
    apply bind_congr
    intro r''
    exact ih (q+1) (by omega) (fun j hj hj' => caps j (by omega) (by omega)) r''.1 r''.2

/-- A failed cap eventually returns false, despite any earlier chain queries. -/
theorem stagedBlocks_rejects (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    (a : ℕ) (tail : BitVec 48) (n q : ℕ)
    (bad : ∃ j, q ≤ j ∧ j < q+n ∧ ¬ PairAllowed index.val j)
    (x : graph.Assignment) (cursor : ℕ) :
    ∀ b ∈ support (stagedBlocks index v payload pk a tail n q x cursor), b = false := by
  induction n generalizing q x cursor with
  | zero => obtain ⟨j, hj, hj', _⟩ := bad; omega
  | succ n ih =>
    rw [stagedBlocks]
    by_cases hq : q < 16
    · rw [dif_pos hq]
      intro b hb
      rw [support_bind] at hb
      simp only [Set.mem_iUnion] at hb
      obtain ⟨r, _, hb⟩ := hb
      split_ifs at hb with allowed
      · rw [support_bind] at hb
        simp only [Set.mem_iUnion] at hb
        obtain ⟨r', _, hb⟩ := hb
        apply ih (q+1) ?_ r'.1 r'.2 b hb
        obtain ⟨j, hj, hj', bad⟩ := bad
        have hne : j ≠ q := by intro h; apply bad; simpa only [h] using allowed
        exact ⟨j, by omega, by omega, bad⟩
      · simpa only [support_pure, Set.mem_singleton_iff] using hb
    · rw [dif_neg hq]
      intro b hb
      simpa only [support_pure, Set.mem_singleton_iff] using hb

/-- An oversized loaded length always returns false, after its queries. -/
theorem stagedBlocks_oversized (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    {a : ℕ} (ha : 5465 ≤ a) (tail : BitVec 48) (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    ∀ b ∈ support (stagedBlocks index v payload pk a tail n q x cursor), b = false := by
  induction n generalizing q x cursor with
  | zero =>
    intro b hb
    rw [stagedBlocks, rootStep, support_bind] at hb
    simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hb
    obtain ⟨y, -, rfl⟩ := hb
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  | succ n ih =>
    rw [stagedBlocks]
    by_cases hq : q < 16
    · rw [dif_pos hq]
      intro b hb
      rw [support_bind] at hb
      simp only [Set.mem_iUnion] at hb
      obtain ⟨r, _, hb⟩ := hb
      split_ifs at hb
      · rw [support_bind] at hb
        simp only [Set.mem_iUnion] at hb
        obtain ⟨r', _, hb⟩ := hb
        exact ih (q+1) r'.1 r'.2 b hb
      · simpa only [support_pure, Set.mem_singleton_iff] using hb
    · rw [dif_neg hq]
      intro b hb
      simpa only [support_pure, Set.mem_singleton_iff] using hb

/-- An accepting run leaves the root query of loaded length `a` in the cache, with an answer
beginning with the public key. -/
theorem stagedBlocks_accept (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    (a : ℕ) (tail : BitVec 48) (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) (c : Cache)
    (p : Bool × Cache)
    (hp : p ∈ support (run (stagedBlocks index v payload pk a tail n q x cursor) c))
    (hok : p.1 = true) :
    ∃ u : BitVec (a + 936), ∃ w, p.2 ⟨a + 936, u⟩ = some w ∧ w.setWidth 128 = pk ∧ a < 5465 := by
  induction n generalizing q x cursor c with
  | zero =>
    rw [stagedBlocks, rootStep, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨y, c'⟩, hy, hp⟩ := hp
    obtain ⟨-, hc'⟩ := hash_support _ c _ hy
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨_, y, hc', hok.1, hok.2⟩
  | succ n ih =>
    rw [stagedBlocks] at hp
    by_cases hq : q < 16
    · rw [dif_pos hq, run_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨r, c₁⟩, -, hp⟩ := hp
      dsimp only at hp
      split_ifs at hp
      · rw [run_bind, support_bind] at hp
        simp only [Set.mem_iUnion] at hp
        obtain ⟨⟨r', c₂⟩, -, hp⟩ := hp
        exact ih (q+1) r'.1 r'.2 c₂ hp
      · rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
        subst hp
        cases hok
    · rw [dif_neg hq, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      cases hok

set_option maxRecDepth 100000 in
theorem pairNodes_idx :
    (chainNodes 0 ++ pairNodes 16 0 ++ [rc, rh]).map Name.idx = List.range 3236 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem order_idx : order.map Name.idx = List.range 3236 := by
  have h := congrArg (List.map Fin.val) order_fin
  rw [List.map_map] at h
  refine h.trans (List.ext_getElem (by simp [N]) fun j h1 h2 => by simp)

theorem pairNodes_all : chainNodes 0 ++ pairNodes 16 0 ++ [rc, rh] = order :=
  List.map_injective_iff.mpr Name.idx_injective (pairNodes_idx.trans order_idx.symm)

/-- Raw-signature verifier matching the machine's complete oracle behavior on every input. -/
def stagedVerify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool := do
  let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits (bits.take 128)))
  let index : RawIdx := ⟨pack answer, pack_lt answer⟩
  let v := countByte bits
  let payload := Payload.permute ((padded bits).drop 128)
  if (digitSum index.val + v) % 255 = 146 then do
    let r ← runNodes' index v payload (entryNodes index v 0) (fun _ => 0) 0
    if v < 16 then do
      let r' ← runNodes' index v payload (tableNodes index v 0) r.1 r.2
      stagedBlocks index v payload pk (min bits.length 5505) (sigTail bits) 16 0 r'.1 r'.2
    else pure false
  else pure false

/-! ## Costs and determinism -/

theorem evalName_cost (x : graph.Assignment) (n : Name) :
    CostAtMost (evalName x n) n.cost := by
  rw [evalName_eq, ← graph_nodeCost_fin]
  exact AlgorithmCosts.Dag.Graph.costAtMost_evalNode graph x n.fin (pure 0)
    (AlgorithmCosts.costAtMost_pure _ _)

theorem cursorStep_cost (index : RawIdx) (v : ℕ) (payload : List Bool)
    (x : graph.Assignment) (cursor : ℕ) (n : Name) :
    CostAtMost (cursorStep index v payload x cursor n) n.cost := by
  unfold cursorStep
  split_ifs
  · exact AlgorithmCosts.costAtMost_pure _ _
  · exact AlgorithmCosts.CostAtMost.map (evalName_cost x n) _
  · exact AlgorithmCosts.costAtMost_pure _ _

theorem runNodes'_cost (index : RawIdx) (v : ℕ) (payload : List Bool)
    (nodes : List Name) (x : graph.Assignment) (cursor : ℕ) :
    CostAtMost (runNodes' index v payload nodes x cursor) (nodes.map Name.cost).sum := by
  induction nodes generalizing x cursor with
  | nil => exact AlgorithmCosts.costAtMost_pure _ _
  | cons n nodes ih =>
    rw [runNodes', List.map_cons, List.sum_cons]
    exact AlgorithmCosts.CostAtMost.bind (cursorStep_cost index v payload x cursor n)
      fun r => ih r.1 r.2

theorem chainNodes_cost (k : Fin 33) : ((chainNodes k).map Name.cost).sum = 32 := by
  have h : ∀ k : Fin 33, ((chainNodes k).map Name.cost).sum = 32 := by decide +kernel
  exact h k

/-- A root query of at most 6448 bits costs at most thirteen compressions. -/
theorem blockCost_root_le {a : ℕ} (ha : a ≤ 5505) : blockCost (a + 936) ≤ 13 := by
  unfold blockCost blockBits
  exact max_le (by norm_num) (by omega)

theorem rootStep_cost (index : RawIdx) (v : ℕ) (pk : PublicKey) {a : ℕ} (ha : a ≤ 5505)
    (tail : BitVec 48) (x : graph.Assignment) :
    CostAtMost (rootStep index v pk a tail x) 13 :=
  AlgorithmCosts.CostAtMost.bind_le (AlgorithmCosts.costAtMost_hash _ (blockCost_root_le ha))
    (b₂ := 0) (fun _ => AlgorithmCosts.costAtMost_pure _ _) (by norm_num)

theorem stagedBlocks_cost (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    {a : ℕ} (ha : a ≤ 5505) (tail : BitVec 48) (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    CostAtMost (stagedBlocks index v payload pk a tail n q x cursor) (64*n+13) := by
  induction n generalizing q x cursor with
  | zero =>
    unfold stagedBlocks
    exact rootStep_cost index v pk ha tail x
  | succ n ih =>
    rw [stagedBlocks]
    by_cases hq : q < 16
    · rw [dif_pos hq]
      let k₀ : Fin 33 := ⟨2*q+1, by omega⟩
      let k₁ : Fin 33 := ⟨2*q+2, by omega⟩
      let e := ((entryNodes index v k₀).map Name.cost).sum
      let t := ((tableNodes index v k₀ ++ chainNodes k₁).map Name.cost).sum
      have total : e+t = 64 := by
        dsimp [e, t]
        rw [List.map_append, List.sum_append, ← Nat.add_assoc,
          ← List.sum_append, ← List.map_append, ← chain_entry_split, chainNodes_cost,
          chainNodes_cost]
      apply AlgorithmCosts.CostAtMost.bind_le
        (runNodes'_cost index v payload (entryNodes index v k₀) x cursor)
        (b₂ := t+(64*n+13))
      · intro r
        split_ifs
        · exact AlgorithmCosts.CostAtMost.bind
            (runNodes'_cost index v payload (tableNodes index v k₀ ++ chainNodes k₁) r.1 r.2)
            (fun r' => ih (q+1) r'.1 r'.2)
        · exact AlgorithmCosts.costAtMost_pure _ _
      · change e + (t + (64*n+13)) ≤ 64*(n+1)+13
        omega
    · rw [dif_neg hq]
      exact AlgorithmCosts.costAtMost_pure _ _

theorem evalName_deterministic (x : graph.Assignment) (n : Name) :
    Deterministic (evalName x n) := by
  rw [evalName_eq]
  exact Dag.Graph.deterministic_evalNode graph x n.fin (pure 0) (Deterministic.of_pure _)

theorem cursorStep_deterministic (index : RawIdx) (v : ℕ) (payload : List Bool)
    (x : graph.Assignment) (cursor : ℕ) (n : Name) :
    Deterministic (cursorStep index v payload x cursor n) := by
  unfold cursorStep
  split_ifs
  · exact Deterministic.of_pure _
  · exact Deterministic.map (evalName_deterministic x n) _
  · exact Deterministic.of_pure _

theorem runNodes'_deterministic (index : RawIdx) (v : ℕ) (payload : List Bool)
    (nodes : List Name) (x : graph.Assignment) (cursor : ℕ) :
    Deterministic (runNodes' index v payload nodes x cursor) := by
  induction nodes generalizing x cursor with
  | nil => exact Deterministic.of_pure _
  | cons n nodes ih =>
    rw [runNodes']
    exact Deterministic.bind (cursorStep_deterministic index v payload x cursor n)
      fun r => ih r.1 r.2

theorem stagedBlocks_deterministic (index : RawIdx) (v : ℕ) (payload : List Bool)
    (pk : PublicKey) (a : ℕ) (tail : BitVec 48) (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    Deterministic (stagedBlocks index v payload pk a tail n q x cursor) := by
  induction n generalizing q x cursor with
  | zero =>
    rw [stagedBlocks, rootStep]
    exact Deterministic.bind (Deterministic.hash _) fun _ => Deterministic.of_pure _
  | succ n ih =>
    rw [stagedBlocks]
    by_cases hq : q < 16
    · rw [dif_pos hq]
      apply Deterministic.bind (runNodes'_deterministic _ _ _ _ _ _)
      intro r
      split_ifs
      · exact Deterministic.bind (runNodes'_deterministic _ _ _ _ _ _)
          fun r' => ih (q+1) r'.1 r'.2
      · exact Deterministic.of_pure _
    · rw [dif_neg hq]
      exact Deterministic.of_pure _

attribute [local irreducible] Deterministic CostAtMost

private theorem deterministic_ite (p : Prop) [Decidable p] (left right : OracleComp Spec Bool)
    (hl : Deterministic left) (hr : Deterministic right) :
    Deterministic (if p then left else right) := by
  split_ifs <;> assumption

private theorem cost_ite (p : Prop) [Decidable p] (left right : OracleComp Spec Bool) (B : ℕ)
    (hl : CostAtMost left B) (hr : CostAtMost right B) :
    CostAtMost (if p then left else right) B := by
  split_ifs <;> assumption

/-- The free chain, then the pairs and the root. -/
def stagedChains (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey) (a : ℕ)
    (tail : BitVec 48) : OracleComp Spec Bool := do
  let r ← runNodes' index v payload (entryNodes index v 0) (fun _ => 0) 0
  if v < 16 then do
    let r' ← runNodes' index v payload (tableNodes index v 0) r.1 r.2
    stagedBlocks index v payload pk a tail 16 0 r'.1 r'.2
  else pure false

theorem stagedVerify_eq (pk : PublicKey) (m : Message) (bits : List Bool) :
    stagedVerify pk m bits = (do
      let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits (bits.take 128)))
      if (digitSum (pack answer) + countByte bits) % 255 = 146 then
        stagedChains ⟨pack answer, pack_lt answer⟩ (countByte bits)
          (Payload.permute ((padded bits).drop 128)) pk (min bits.length 5505) (sigTail bits)
      else pure false) := rfl

theorem stagedChains_deterministic (index : RawIdx) (v : ℕ) (payload : List Bool)
    (pk : PublicKey) (a : ℕ) (tail : BitVec 48) :
    Deterministic (stagedChains index v payload pk a tail) := by
  unfold stagedChains
  apply Deterministic.bind (runNodes'_deterministic _ _ _ _ _ _)
  intro r
  exact deterministic_ite _ _ _
    (Deterministic.bind (runNodes'_deterministic _ _ _ _ _ _)
      fun r' => stagedBlocks_deterministic _ _ _ _ _ _ 16 0 r'.1 r'.2)
    (Deterministic.of_pure _)

theorem stagedChains_cost (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    {a : ℕ} (ha : a ≤ 5505) (tail : BitVec 48) :
    CostAtMost (stagedChains index v payload pk a tail) 1069 := by
  unfold stagedChains
  let e := ((entryNodes index v 0).map Name.cost).sum
  let t := ((tableNodes index v 0).map Name.cost).sum
  have total : e+t = 32 := by
    dsimp [e, t]
    rw [← List.sum_append, ← List.map_append, ← chain_entry_split, chainNodes_cost]
  apply AlgorithmCosts.CostAtMost.bind_le
    (runNodes'_cost index v payload (entryNodes index v 0) _ 0) (b₂ := t + (64*16+13))
  · intro r
    exact cost_ite _ _ _ _
      (AlgorithmCosts.CostAtMost.bind (runNodes'_cost index v payload _ r.1 r.2)
        fun r' => stagedBlocks_cost index v payload pk ha tail 16 0 r'.1 r'.2)
      (AlgorithmCosts.costAtMost_pure _ _)
  · change e + (t + (64*16+13)) ≤ 1069
    omega

theorem stagedVerify_deterministic (pk : PublicKey) (m : Message) (bits : List Bool) :
    Deterministic (stagedVerify pk m bits) := by
  rw [stagedVerify_eq]
  apply Deterministic.bind (Deterministic.hash _)
  intro answer
  exact deterministic_ite _ _ _ (stagedChains_deterministic _ _ _ _ _ _)
    (Deterministic.of_pure false)

/-- A deliberately loose independent admission bound; the machine proof establishes the cycles. -/
theorem stagedVerify_cost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (stagedVerify pk m bits) 1070 := by
  rw [stagedVerify_eq]
  apply AlgorithmCosts.CostAtMost.bind_le
    (AlgorithmCosts.costAtMost_hash _ (b := 1) (by decide)) (b₂ := 1069)
  · intro answer
    exact cost_ite _ _ _ 1069
      (stagedChains_cost _ _ _ pk (min_le_right _ _) _)
      (AlgorithmCosts.costAtMost_pure false 1069)
  · decide

/-! ## Rejection and acceptance -/

theorem stagedChains_rejects (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    (a : ℕ) (tail : BitVec 48) (bad : ¬ v < 16 ∨ ∃ q, q < 16 ∧ ¬ PairAllowed index.val q) :
    ∀ b ∈ support (stagedChains index v payload pk a tail), b = false := by
  unfold stagedChains
  intro b hb
  rw [support_bind] at hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨r, -, hb⟩ := hb
  split_ifs at hb with hv
  · rw [support_bind] at hb
    simp only [Set.mem_iUnion] at hb
    obtain ⟨r', -, hb⟩ := hb
    rcases bad with bad | ⟨q, hq, bad⟩
    · exact absurd hv bad
    · exact stagedBlocks_rejects _ _ _ _ _ _ 16 0 ⟨q, Nat.zero_le _, by omega, bad⟩ _ _ b hb
  · simpa only [support_pure, Set.mem_singleton_iff] using hb

theorem stagedChains_oversized (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    {a : ℕ} (ha : 5465 ≤ a) (tail : BitVec 48) :
    ∀ b ∈ support (stagedChains index v payload pk a tail), b = false := by
  unfold stagedChains
  intro b hb
  rw [support_bind] at hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨r, -, hb⟩ := hb
  split_ifs at hb with hv
  · rw [support_bind] at hb
    simp only [Set.mem_iUnion] at hb
    obtain ⟨r', -, hb⟩ := hb
    exact stagedBlocks_oversized _ _ _ _ ha _ 16 0 _ _ b hb
  · simpa only [support_pure, Set.mem_singleton_iff] using hb

theorem stagedChains_accept (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    (a : ℕ) (tail : BitVec 48) (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stagedChains index v payload pk a tail) c)) (hok : p.1 = true) :
    ∃ u : BitVec (a + 936), ∃ w, p.2 ⟨a + 936, u⟩ = some w ∧ w.setWidth 128 = pk ∧ a < 5465 := by
  unfold stagedChains at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨r, c₁⟩, -, hp⟩ := hp
  dsimp only at hp
  split_ifs at hp
  · rw [run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨r', c₂⟩, -, hp⟩ := hp
    exact stagedBlocks_accept _ _ _ _ _ _ 16 0 _ _ c₂ p hp hok
  · rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    cases hok

theorem staged_pair_sum (i : ℕ) :
    (∑ q : Fin 16, (digit i (2*q.val) + digit i (2*q.val+1))) = digitSum i := by
  rw [digitSum, ← Fin.sum_univ_eq_sum_range]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  simp only [Nat.add_assoc]
  rfl

/-- The caps bound the digit sum below the high alias of the count check. -/
theorem staged_caps_sum_le (i : ℕ) (caps : ∀ q : Fin 16, PairAllowed i q.val) :
    digitSum i ≤ 385 := by
  rw [← staged_pair_sum]
  have h : (∑ q : Fin 16, (digit i (2*q.val) + digit i (2*q.val+1))) ≤
      ∑ q : Fin 16, PairCode.cap q.val := by
    apply Finset.sum_le_sum
    intro q _
    exact caps q
  have total : (∑ q : Fin 16, PairCode.cap q.val) = 385 := by decide +kernel
  omega

theorem digitSum_le (i : ℕ) : digitSum i ≤ 480 := by
  have h : ∀ k ∈ Finset.range 32, digit i k ≤ 15 := fun k _ => by
    have := digit_lt_16 i k; omega
  have := Finset.sum_le_sum h
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  unfold digitSum
  omega

/-- A passing count check with a small byte and the caps give an accepted index with the byte as
its free digit. -/
theorem staged_accepted (i v : ℕ) (hc : (digitSum i + v) % 255 = 146) (hv : v < 16)
    (caps : ∀ q : Fin 16, PairAllowed i q.val) : Accepted i ∧ v = freeDigit i := by
  have h1 := staged_caps_sum_le i caps
  have key : digitSum i + v = 146 := by omega
  refine ⟨⟨⟨?_, ?_⟩, caps⟩, ?_⟩
  · unfold freeLow; omega
  · unfold target; omega
  · unfold freeDigit target; omega

/-- On an accepted index the count check holds exactly at the free digit. -/
theorem count_iff_free (i : ℕ) (hi : Accepted i) {v : ℕ} (hv : v < 16) :
    (digitSum i + v) % 255 = 146 ↔ v = freeDigit i := by
  obtain ⟨⟨hlo, hhi⟩, -⟩ := hi
  unfold freeLow at hlo
  unfold target at hhi
  unfold freeDigit target
  omega

/-! ## Agreement with the strict forest verifier -/

theorem padded_of_length {bits : List Bool} (h : bits.length = 5464) :
    padded bits = bits ++ List.replicate 40 false := by
  unfold padded
  rw [List.take_of_length_le (by omega), h]

theorem ofBits_congr {n : ℕ} {l l' : List Bool} (h : ∀ j < n, l.getD j false = l'.getD j false) :
    ofBits n l = ofBits n l' := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [ofBits, BitVec.getLsbD_ofNat, hj, decide_true, Bool.true_and, testBit_foldr_bits]
  exact h j hj

/-- At the honest length the count byte is the tag's value. -/
theorem countByte_of_length {bits : List Bool} (h : bits.length = 5464) :
    ofBits 8 ((padded bits).drop 5456) = ofBits 8 (bits.drop 5456) := by
  apply ofBits_congr
  intro j hj
  rw [padded_of_length h, List.drop_append_of_le_length (by omega)]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [h]; omega)]

theorem freeDigit_lt (i : Idx) : freeDigit i.val < 16 := by
  have := digitSum_bounds i
  unfold freeDigit
  unfold freeLow target at this
  unfold target
  omega

theorem freeTag_iff {bits : List Bool} (h : bits.length = 5464) (i : Idx) :
    bits.drop 5456 = freeTag i ↔ countByte bits = freeDigit i.val := by
  have hl : (bits.drop 5456).length = 8 := by simp [h]
  unfold countByte
  rw [countByte_of_length h]
  constructor
  · intro e
    rw [e, freeTag, ofBits_toBits, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have := freeDigit_lt i
    omega
  · intro e
    rw [freeTag, ← e, BitVec.ofNat_toNat, BitVec.setWidth_eq, toBits_ofBits _ hl]

theorem offset_add_len_le (G : Graph) (A : Finset (Fin G.size)) {u : Fin G.size} (hu : u ∈ A) :
    G.offset A u + G.len u ≤ G.revealBits A := by
  unfold Graph.offset Graph.revealBits
  rw [← Finset.sum_filter_add_sum_filter_not A (· < u)]
  have : G.len u ≤ ∑ w ∈ A.filter (fun w => ¬ w < u), G.len w :=
    Finset.single_le_sum (f := G.len) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨hu, lt_irrefl u⟩)
  omega

/-- The decoded values at a disclosure set read only the revealed prefix. -/
theorem decode_congr (G : Graph) (A : Finset (Fin G.size)) {l l' : List Bool}
    (h : l.take (G.revealBits A) = l'.take (G.revealBits A)) {u : Fin G.size} (hu : u ∈ A) :
    G.decode A l u = G.decode A l' u := by
  unfold Graph.decode
  have hb := offset_add_len_le G A hu
  have e : ∀ m : List Bool, (m.drop (G.offset A u)).take (G.len u) =
      ((m.take (G.revealBits A)).drop (G.offset A u)).take (G.len u) := by
    intro m
    rw [List.drop_take, List.take_take]
    congr 1
    omega
  rw [e l, e l', h]

theorem step_congr (A : Finset Name) {g g' x : graph.Assignment} (n : Name)
    (h : n ∈ A → g n.fin = g' n.fin) : step A g x n = step A g' x n := by
  unfold step
  split_ifs with hn
  · rw [h hn]
  · rfl
  · rfl

theorem foldlM_step_congr (A : Finset Name) {g g' : graph.Assignment}
    (h : ∀ n ∈ A, g n.fin = g' n.fin) (l : List Name) (x : graph.Assignment) :
    l.foldlM (step A g) x = l.foldlM (step A g') x := by
  induction l generalizing x with
  | nil => rfl
  | cons n l ih =>
    simp only [List.foldlM_cons]
    rw [step_congr A n (h n)]
    exact bind_congr fun y => ih y

/-- The direct reconstruction reads only the first 5328 payload bits. -/
theorem directReconstruct_congr (i : Idx) {l l' : List Bool} (h : l.take 5328 = l'.take 5328) :
    directReconstruct i l = directReconstruct i l' := by
  rw [directReconstruct_eq, directReconstruct_eq, reconstruct, reconstruct]
  have hR : graph.revealBits (fins (setsName i)) = 5328 := fixed_revealBits i
  apply foldlM_step_congr
  intro n hn
  apply decode_congr
  · rw [hR]; exact h
  · exact (mem_fins _ n).mpr hn

theorem hash_bind_congr {n m : ℕ} (h : n = m) {u : BitVec n} {u' : BitVec m}
    (hu : u.cast h = u') {β : Type} {f g : BitVec hashBits → OracleComp Spec β}
    (hfg : ∀ y, f y = g y) : hash u >>= f = hash u' >>= g := by
  subst h; subst hu
  exact bind_congr hfg

/-- At the honest length the root step is the graph's root input and root hash. -/
theorem rootStep_eq (index : RawIdx) (v : ℕ) (payload : List Bool) (pk : PublicKey)
    (tail : BitVec 48) (x : graph.Assignment) (cursor : ℕ) :
    rootStep index v pk 5464 tail x = runNodes' index v payload [rc, rh] x cursor >>= fun r =>
      pure (decide ((r.1 rh.fin).setWidth 128 = pk)) := by
  have hlt : decide (5464 < 5465) = true := rfl
  unfold rootStep
  rw [show (5464 + 936 : ℕ) = Name.rootBits from rfl, setWidth_append_lo]
  simp only [runNodes', cursorStep_rc, cursorStep_rh, pure_bind, bind_assoc, bind_map_left,
    Function.update_self]
  refine hash_bind_congr (graph_len_fin rc).symm rfl fun y => ?_
  simp only [hlt, Bool.and_true]
  rfl

set_option maxRecDepth 100000 in
/-- Equality on valid indices at the honest length; no claim on rejecting inputs. -/
theorem stagedChains_eq_direct (index : Idx) (payload : List Bool) (pk : PublicKey)
    (tail : BitVec 48) :
    stagedChains index (freeDigit index.val) payload pk 5464 tail = (do
      let y ← directReconstruct index payload
      return decide ((y rh.fin).setWidth 128 = pk)) := by
  have hv : freeDigit index.val < 16 := freeDigit_lt index
  unfold stagedChains
  simp only [hv, if_true]
  unfold directReconstruct
  rw [runNodes_eq_fst, bind_map_left, ← pairNodes_all, chain_entry_split (index : RawIdx)
    (freeDigit index.val) 0]
  simp only [List.append_assoc, runNodes'_append, bind_assoc]
  apply bind_congr
  intro r
  apply bind_congr
  intro r'
  rw [stagedBlocks_eq_of_allowed _ _ payload pk 5464 tail 16 0 (by omega)
    (fun j _ hj => (mem_validSet_accepted index.2).2 ⟨j, by omega⟩)]
  apply bind_congr
  intro r''
  exact rootStep_eq _ _ payload pk tail r''.1 r''.2

/-- On full-length signatures the strict forest verifier only removes always-reject suffixes. -/
theorem directVerify_prunes_stagedVerify (pk : PublicKey) (m : Message) (bits : List Bool)
    (hlen : bits.length = 5464) :
    RejectAdapter.Prunes (directVerify pk m bits) (stagedVerify pk m bits) := by
  rw [stagedVerify_eq]
  unfold directVerify packIndex
  rw [bind_map_left, show min bits.length 5505 = 5464 by omega]
  apply RejectAdapter.Prunes.bind_left
  intro answer
  dsimp only
  by_cases hi : pack answer ∈ validSet
  · rw [dif_pos hi]
    have acc := mem_validSet_accepted hi
    by_cases htag : bits.drop 5456 = freeTag ⟨pack answer, hi⟩
    · have hc : countByte bits = freeDigit (pack answer) :=
        (freeTag_iff hlen ⟨pack answer, hi⟩).mp htag
      have hv : countByte bits < 16 := hc ▸ freeDigit_lt ⟨pack answer, hi⟩
      rw [if_pos ⟨hlen, htag⟩, if_pos ((count_iff_free _ acc hv).mpr hc), hc]
      have he := stagedChains_eq_direct (⟨pack answer, hi⟩ : Idx)
        (Payload.permute ((padded bits).drop 128)) pk (sigTail bits)
      dsimp only [Idx.toRaw] at he
      rw [he]
      have hp : (Payload.permute ((padded bits).drop 128)).take 5328 =
          ((Payload.permute (bits.drop 128)).take 5328).take 5328 := by
        rw [List.take_take, Nat.min_self]
        apply Payload.take_permute_congr
        · rw [List.length_drop, length_padded]; unfold Payload.valueBits; norm_num
        · rw [List.length_drop, hlen]; unfold Payload.valueBits; norm_num
        · rw [padded_of_length hlen, List.drop_append_of_le_length (by rw [hlen]; norm_num),
            List.take_append_of_le_length
              (by rw [List.length_drop, hlen]; unfold Payload.valueBits; norm_num)]
      rw [directReconstruct_congr _ hp]
      apply RejectAdapter.Prunes.bind_left
      intro y
      convert RejectAdapter.Prunes.refl
        (pure (decide ((y rh.fin).setWidth 128 = pk)) : OracleComp Spec Bool) using 1
      exact congrArg pure (decide_eq_decide.mpr Iff.rfl)
    · rw [if_neg (fun h => htag h.2)]
      split_ifs with guard
      · apply RejectAdapter.Prunes.of_support
        apply stagedChains_rejects
        left
        intro hv
        exact htag ((freeTag_iff hlen ⟨pack answer, hi⟩).mpr ((count_iff_free _ acc hv).mp guard))
      · exact RejectAdapter.Prunes.refl _
  · rw [dif_neg hi]
    split_ifs with guard
    · apply RejectAdapter.Prunes.of_support
      apply stagedChains_rejects
      by_contra hgood
      push Not at hgood
      obtain ⟨hv16, caps⟩ := hgood
      exact hi (mem_validSet.mpr ⟨pack_lt answer,
        (staged_accepted _ _ guard hv16 fun q => caps q.val q.isLt).1⟩)
    · exact RejectAdapter.Prunes.refl _

/-- The verifier of the security proof: strict on full-length signatures, the machine's program
on shorter ones, and immediate rejection of longer ones. -/
def strictVerify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool :=
  if bits.length = 5464 then directVerify pk m bits
  else if bits.length < 5464 then stagedVerify pk m bits
  else pure false

theorem stagedVerify_accept (pk : PublicKey) (m : Message) (bits : List Bool) (c : Cache)
    (p : Bool × Cache) (hp : p ∈ support (run (stagedVerify pk m bits) c)) (hok : p.1 = true) :
    ∃ u : BitVec (min bits.length 5505 + 936), ∃ w, p.2 ⟨_, u⟩ = some w ∧ trunc128 w = pk ∧
      min bits.length 5505 < 5465 := by
  rw [stagedVerify_eq] at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨answer, c₁⟩, -, hp⟩ := hp
  dsimp only at hp
  split_ifs at hp
  · exact stagedChains_accept _ _ _ _ _ _ c₁ p hp hok
  · rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    cases hok

theorem strictVerify_wire : Forest.WireVerifier strictVerify where
  full := fun pk m bits h => by
    unfold strictVerify
    rw [if_pos h, directVerify_eq]
    rfl
  short := fun pk m bits c p hne hp hok => by
    unfold strictVerify at hp
    rw [if_neg hne] at hp
    split_ifs at hp with hlt
    · obtain ⟨u, w, hw, hpk, -⟩ := stagedVerify_accept pk m bits c p hp hok
      exact ⟨_, by unfold ShortLen; omega, u, w, hw, hpk⟩
    · rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      cases hok

theorem stagedVerify_oversized (pk : PublicKey) (m : Message) (bits : List Bool)
    (h : 5464 < bits.length) : ∀ b ∈ support (stagedVerify pk m bits), b = false := by
  rw [stagedVerify_eq]
  intro b hb
  rw [support_bind] at hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨answer, -, hb⟩ := hb
  split_ifs at hb
  · exact stagedChains_oversized _ _ _ _ (by omega) _ b hb
  · simpa only [support_pure, Set.mem_singleton_iff] using hb

/-- The machine's verifier only adds terminal constant-answer suffixes to the strict one. -/
theorem strict_prunes_staged (pk : PublicKey) (m : Message) (bits : List Bool) :
    RejectAdapter.Prunes (strictVerify pk m bits) (stagedVerify pk m bits) := by
  unfold strictVerify
  split_ifs with h5464 hlt
  · exact directVerify_prunes_stagedVerify pk m bits h5464
  · exact RejectAdapter.Prunes.refl _
  · exact RejectAdapter.Prunes.of_support _ _ (stagedVerify_oversized pk m bits (by omega))

theorem strictVerify_deterministic (pk : PublicKey) (m : Message) (bits : List Bool) :
    Deterministic (strictVerify pk m bits) := by
  unfold strictVerify
  refine deterministic_ite _ _ _ ?_
    (deterministic_ite _ _ _ (stagedVerify_deterministic pk m bits) (Deterministic.of_pure _))
  rw [directVerify_eq]
  exact RiscvUpperForest.Wire.admissible.verifyDeterministic pk m bits

theorem strictVerify_cost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (strictVerify pk m bits) 1070 := by
  unfold strictVerify
  refine cost_ite _ _ _ _ ?_
    (cost_ite _ _ _ _ (stagedVerify_cost pk m bits) (AlgorithmCosts.costAtMost_pure _ _))
  rw [directVerify_eq]
  exact (RiscvUpperForest.Wire.cost pk m bits).mono (by decide)

/-- Replacing a verifier by one that agrees on every honest signature keeps correctness. -/
theorem correct_of_honest (S : OracleAlgorithm.Scheme)
    (verify : PublicKey → Message → List Bool → OracleComp Spec Bool)
    (agree : ∀ pk sk m s, some s ∈ support (S.sign sk m) → verify pk m s = S.verify pk m s)
    (h : S.Correct) : (RejectAdapter.scheme S verify).Correct := by
  intro message
  rw [← h message]
  congr 1
  apply bind_congr
  rintro ⟨pk, sk⟩
  dsimp only
  apply bind_congr_of_forall_mem_support
  intro σ hσ
  cases σ with
  | none => rfl
  | some s => simp only [RejectAdapter.scheme, agree pk sk (message pk) s hσ]

section Scheme

attribute [local irreducible] Forest.graph GScheme.sign GScheme.signLoop

/-- Honest signatures have exactly 5464 bits. -/
theorem honest_length (sk : RiscvUpperForest.Wire.scheme.SecretKey) (m : Message)
    (bits : List Bool) (h : some bits ∈ support (RiscvUpperForest.Wire.scheme.sign sk m)) :
    bits.length = 5464 := by
  change some bits ∈ support
    (Option.map AlgorithmAdapter.encodeSignature <$> forestScheme.sign sk m) at h
  rw [support_map] at h
  obtain ⟨σ, hσ, he⟩ := h
  cases σ with
  | none => cases he
  | some σ =>
    obtain ⟨i, hi⟩ := AlgorithmAdapter.sign_returns forestScheme sk m σ hσ
    have e : AlgorithmAdapter.encodeSignature σ = bits := Option.some.inj he
    rw [← e, AlgorithmAdapter.length_encodeSignature, hi, List.length_append,
      AlgorithmAdapter.length_encode _ _ sk, fixed_revealBits i]
    change nonceBits + (5328 + (freeTag i).length) = 5464
    rw [length_freeTag]
    rfl

/-- The forest's keys and signer with the verifier of the security proof. -/
def strictScheme : OracleAlgorithm.Scheme := RejectAdapter.scheme RiscvUpperForest.Wire.scheme strictVerify

theorem strictScheme_eq : strictScheme = Forest.wireScheme strictVerify := rfl

theorem strictScheme_secure : strictScheme.Secure := by
  rw [strictScheme_eq]
  exact Forest.wireScheme_secure strictVerify strictVerify_wire

/-- The strict scheme meets every admission requirement. -/
theorem strictScheme_admissible : strictScheme.Admissible where
  correct := correct_of_honest _ _ (fun pk sk m s hs => by
      unfold strictVerify
      rw [if_pos (honest_length sk m s hs), directVerify_eq])
    RiscvUpperForest.Wire.admissible.correct
  verifyDeterministic := strictVerify_deterministic
  signingFailure := RiscvUpperForest.Wire.admissible.signingFailure
  signatureSize := RiscvUpperForest.Wire.admissible.signatureSize
  rejectsOversized := fun pk m bits h => by
    change true ∉ support (strictVerify pk m bits)
    have h' : 5504 < bits.length := h
    unfold strictVerify
    rw [if_neg (by omega), if_neg (by omega), support_pure]
    simp
  keygenCost := RiscvUpperForest.Wire.admissible.keygenCost
  signCost := RiscvUpperForest.Wire.admissible.signCost
  verifyCost := fun pk m bits => (strictVerify_cost pk m bits).mono (by decide)

end Scheme

/-- The 345-cycle scheme retains the restricted forest's keys and signer. -/
def stagedScheme : OracleAlgorithm.Scheme := RejectAdapter.scheme strictScheme stagedVerify

theorem stagedScheme_secure : stagedScheme.Secure :=
  RejectAdapter.secure strictScheme stagedVerify strict_prunes_staged strictScheme_secure

theorem stagedScheme_admissible : stagedScheme.Admissible :=
  RejectAdapter.admissible strictScheme stagedVerify strict_prunes_staged
    strictScheme_admissible stagedVerify_deterministic
    (fun pk m bits => (stagedVerify_cost pk m bits).mono (by decide))

/--
info: 'OptimalOTS.RiscvMixedProgram.stagedScheme_secure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stagedScheme_secure

/--
info: 'OptimalOTS.RiscvMixedProgram.stagedScheme_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stagedScheme_admissible

end OptimalOTS.RiscvMixedProgram
