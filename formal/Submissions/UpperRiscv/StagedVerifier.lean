import Submissions.UpperRiscv.MixedChain
import Submissions.UpperRiscv.RejectAdapter

/-!
# The verifier with dispatch-time rejection, for every signature length

The machine hashes an expanding left chain once before the digit-pair cap is tested, and it runs
every signature through the whole verifier: the chains read the signature padded with zeros to
5504 bits (`padded`), and the root query is the first `a + 639` bits of the tops region, where
`a = min |σ| 5505` is the loaded length. The verdict is the public-key test and `a < 5505`.

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
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

/-- Full node list of the remaining chain pairs, without any digit-cap rejection. -/
def pairNodes : (n q : ℕ) → List Name
  | 0, _ => []
  | n+1, q => if hq : q < 16 then
      chainNodes ⟨2*q, by omega⟩ ++ chainNodes ⟨2*q+1, by omega⟩ ++ pairNodes n (q+1)
    else []

/-- The signature as the loader leaves it in memory: its first 5504 bits, then zeros. -/
def padded (bits : List Bool) : List Bool :=
  bits.take 5504 ++ List.replicate (5504 - bits.length) false

theorem padded_of_length {bits : List Bool} (h : bits.length = 5504) : padded bits = bits := by
  unfold padded
  rw [List.take_of_length_le (by omega), h, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- The root query for the loaded length `a`, and the decision. -/
def rootStep (pk : PublicKey) (a : ℕ) (x : graph.Assignment) : OracleComp Spec Bool := do
  let y ← hash ((rootRegion fun k => (x (cv k 31).fin).cast (lenF_fin _)).setWidth (a + 639))
  return (decide (y.setWidth 128 = pk) && decide (a < 5505))

/-- The exact staged oracle program. `payload` is already in chain execution order. -/
def stagedBlocks (index : RawIdx) (payload : List Bool) (pk : PublicKey) (a : ℕ) :
    (n q : ℕ) → graph.Assignment → ℕ → OracleComp Spec Bool
  | 0, _, x, _ => rootStep pk a x
  | n+1, q, x, cursor => if hq : q < 16 then do
      let r ← runNodes' index payload (entryNodes index ⟨2*q, by omega⟩) x cursor
      if PairAllowed index.val q then
        let r' ← runNodes' index payload
          (tableNodes index ⟨2*q, by omega⟩ ++ chainNodes ⟨2*q+1, by omega⟩) r.1 r.2
        stagedBlocks index payload pk a n (q+1) r'.1 r'.2
      else pure false
    else pure false

attribute [local irreducible] stagedBlocks

/-- Machine-facing expansion: `some` changes the output interface, never the query trace. -/
theorem stagedBlocks_some_succ (index : RawIdx) (payload : List Bool) (pk : PublicKey) (a : ℕ)
    (n q : ℕ) (hq : q < 16) (x : graph.Assignment) (cursor : ℕ) :
    some <$> stagedBlocks index payload pk a (n+1) q x cursor = (do
      let r ← runNodes' index payload (entryNodes index ⟨2*q, by omega⟩) x cursor
      if PairAllowed index.val q then
        let r' ← runNodes' index payload
          (tableNodes index ⟨2*q, by omega⟩ ++ chainNodes ⟨2*q+1, by omega⟩) r.1 r.2
        some <$> stagedBlocks index payload pk a n (q+1) r'.1 r'.2
      else pure (some false)) := by
  rw [stagedBlocks, dif_pos hq, map_bind]
  congr 1
  funext r
  split_ifs <;> simp only [map_bind, map_pure]

theorem stagedBlocks_some_zero (index : RawIdx) (payload : List Bool) (pk : PublicKey) (a : ℕ)
    (q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    some <$> stagedBlocks index payload pk a 0 q x cursor = (do
      let y ← hash ((rootRegion fun k => (x (cv k 31).fin).cast (lenF_fin _)).setWidth (a + 639))
      return some (decide (y.setWidth 128 = pk) && decide (a < 5505))) := by
  simp only [stagedBlocks, rootStep, map_bind, map_pure]

theorem stagedBlocks_eq_of_allowed (index : RawIdx) (payload : List Bool) (pk : PublicKey) (a : ℕ)
    (n q : ℕ) (hq : q+n ≤ 16)
    (caps : ∀ j, q ≤ j → j < q+n → PairAllowed index.val j)
    (x : graph.Assignment) (cursor : ℕ) :
    stagedBlocks index payload pk a n q x cursor =
      runNodes' index payload (pairNodes n q) x cursor >>= fun r => rootStep pk a r.1 := by
  induction n generalizing q x cursor with
  | zero => rw [stagedBlocks, pairNodes, runNodes', pure_bind]
  | succ n ih =>
    have hq16 : q < 16 := by omega
    rw [stagedBlocks, dif_pos hq16, pairNodes, dif_pos hq16]
    rw [chain_entry_split index ⟨2*q, by omega⟩]
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
theorem stagedBlocks_rejects (index : RawIdx) (payload : List Bool) (pk : PublicKey) (a : ℕ)
    (n q : ℕ) (bad : ∃ j, q ≤ j ∧ j < q+n ∧ ¬ PairAllowed index.val j)
    (x : graph.Assignment) (cursor : ℕ) :
    ∀ b ∈ support (stagedBlocks index payload pk a n q x cursor), b = false := by
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

/-- The oversized loaded length `5505` always returns false, after its queries. -/
theorem stagedBlocks_oversized (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    ∀ b ∈ support (stagedBlocks index payload pk 5505 n q x cursor), b = false := by
  induction n generalizing q x cursor with
  | zero =>
    intro b hb
    rw [stagedBlocks, rootStep, support_bind] at hb
    simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hb
    obtain ⟨y, -, rfl⟩ := hb
    simp
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
theorem stagedBlocks_accept (index : RawIdx) (payload : List Bool) (pk : PublicKey) (a : ℕ)
    (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) (c : Cache) (p : Bool × Cache)
    (hp : p ∈ support (run (stagedBlocks index payload pk a n q x cursor) c)) (hok : p.1 = true) :
    ∃ u : BitVec (a + 639), ∃ w, p.2 ⟨a + 639, u⟩ = some w ∧ w.setWidth 128 = pk := by
  induction n generalizing q x cursor c with
  | zero =>
    rw [stagedBlocks, rootStep, run_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨y, c'⟩, hy, hp⟩ := hp
    obtain ⟨-, hc'⟩ := hash_support _ c _ hy
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact ⟨_, y, hc', hok.1⟩
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
theorem pairNodes_all : pairNodes 16 0 ++ [rc, rh] = order := by decide +kernel

/-- The two checksum ranks admitted before the staged pair checks. -/
def stagedRank (i : ℕ) : Prop :=
  (∑ k ∈ Finset.range 32, digit i k) = 158 ∨
  (∑ k ∈ Finset.range 32, digit i k) = 413

instance : DecidablePred stagedRank := fun _ => inferInstanceAs (Decidable (_ ∨ _))

attribute [local irreducible] stagedRank

/-- Raw-signature verifier matching the machine's complete oracle behavior on every input. -/
def stagedVerify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool := do
  let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits (bits.take 128)))
  let index : RawIdx := ⟨pack answer, pack_lt answer⟩
  if stagedRank index.val then
    stagedBlocks index (Payload.permute ((padded bits).drop 128)) pk (min bits.length 5505)
      16 0 (fun _ => 0) 0
  else pure false

theorem evalName_cost (x : graph.Assignment) (n : Name) :
    CostAtMost (evalName x n) n.cost := by
  rw [evalName_eq, ← graph_nodeCost_fin]
  exact AlgorithmCosts.Dag.Graph.costAtMost_evalNode graph x n.fin (pure 0)
    (AlgorithmCosts.costAtMost_pure _ _)

theorem cursorStep_cost (index : RawIdx) (payload : List Bool)
    (x : graph.Assignment) (cursor : ℕ) (n : Name) :
    CostAtMost (cursorStep index payload x cursor n) n.cost := by
  unfold cursorStep
  split_ifs
  · exact AlgorithmCosts.costAtMost_pure _ _
  · exact AlgorithmCosts.CostAtMost.map (evalName_cost x n) _
  · exact AlgorithmCosts.costAtMost_pure _ _

theorem runNodes'_cost (index : RawIdx) (payload : List Bool)
    (nodes : List Name) (x : graph.Assignment) (cursor : ℕ) :
    CostAtMost (runNodes' index payload nodes x cursor) (nodes.map Name.cost).sum := by
  induction nodes generalizing x cursor with
  | nil => exact AlgorithmCosts.costAtMost_pure _ _
  | cons n nodes ih =>
    rw [runNodes', List.map_cons, List.sum_cons]
    exact AlgorithmCosts.CostAtMost.bind (cursorStep_cost index payload x cursor n)
      fun r => ih r.1 r.2

theorem chainNodes_cost (k : Fin 32) : ((chainNodes k).map Name.cost).sum = 32 := by
  have h : ∀ k : Fin 32, ((chainNodes k).map Name.cost).sum = 32 := by decide +kernel
  exact h k

/-- A root query of at most 6144 bits costs at most twelve compressions. -/
theorem blockCost_root_le {a : ℕ} (ha : a ≤ 5505) : blockCost (a + 639) ≤ 12 := by
  unfold blockCost blockBits
  exact max_le (by norm_num) (by omega)

theorem rootStep_cost (pk : PublicKey) {a : ℕ} (ha : a ≤ 5505) (x : graph.Assignment) :
    CostAtMost (rootStep pk a x) 12 :=
  AlgorithmCosts.CostAtMost.bind_le (AlgorithmCosts.costAtMost_hash _ (blockCost_root_le ha))
    (b₂ := 0) (fun _ => AlgorithmCosts.costAtMost_pure _ _) (by norm_num)

theorem stagedBlocks_cost (index : RawIdx) (payload : List Bool) (pk : PublicKey) {a : ℕ}
    (ha : a ≤ 5505) (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    CostAtMost (stagedBlocks index payload pk a n q x cursor) (64*n+12) := by
  induction n generalizing q x cursor with
  | zero =>
    unfold stagedBlocks
    exact rootStep_cost pk ha x
  | succ n ih =>
    rw [stagedBlocks]
    by_cases hq : q < 16
    · rw [dif_pos hq]
      let k₀ : Fin 32 := ⟨2*q, by omega⟩
      let k₁ : Fin 32 := ⟨2*q+1, by omega⟩
      let e := ((entryNodes index k₀).map Name.cost).sum
      let t := ((tableNodes index k₀ ++ chainNodes k₁).map Name.cost).sum
      have total : e+t = 64 := by
        dsimp [e, t]
        rw [List.map_append, List.sum_append, ← Nat.add_assoc,
          ← List.sum_append, ← List.map_append, ← chain_entry_split, chainNodes_cost,
          chainNodes_cost]
      apply AlgorithmCosts.CostAtMost.bind_le
        (runNodes'_cost index payload (entryNodes index k₀) x cursor)
        (b₂ := t+(64*n+12))
      · intro r
        split_ifs
        · exact AlgorithmCosts.CostAtMost.bind
            (runNodes'_cost index payload (tableNodes index k₀ ++ chainNodes k₁) r.1 r.2)
            (fun r' => ih (q+1) r'.1 r'.2)
        · exact AlgorithmCosts.costAtMost_pure _ _
      · change e + (t + (64*n+12)) ≤ 64*(n+1)+12
        omega
    · rw [dif_neg hq]
      exact AlgorithmCosts.costAtMost_pure _ _

theorem evalName_deterministic (x : graph.Assignment) (n : Name) :
    Deterministic (evalName x n) := by
  rw [evalName_eq]
  exact Dag.Graph.deterministic_evalNode graph x n.fin (pure 0) (Deterministic.of_pure _)

theorem cursorStep_deterministic (index : RawIdx) (payload : List Bool)
    (x : graph.Assignment) (cursor : ℕ) (n : Name) :
    Deterministic (cursorStep index payload x cursor n) := by
  unfold cursorStep
  split_ifs
  · exact Deterministic.of_pure _
  · exact Deterministic.map (evalName_deterministic x n) _
  · exact Deterministic.of_pure _

theorem runNodes'_deterministic (index : RawIdx) (payload : List Bool)
    (nodes : List Name) (x : graph.Assignment) (cursor : ℕ) :
    Deterministic (runNodes' index payload nodes x cursor) := by
  induction nodes generalizing x cursor with
  | nil => exact Deterministic.of_pure _
  | cons n nodes ih =>
    rw [runNodes']
    exact Deterministic.bind (cursorStep_deterministic index payload x cursor n)
      fun r => ih r.1 r.2

theorem stagedBlocks_deterministic (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (a n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    Deterministic (stagedBlocks index payload pk a n q x cursor) := by
  induction n generalizing q x cursor with
  | zero =>
    rw [stagedBlocks, rootStep]
    exact Deterministic.bind (Deterministic.hash _) fun _ => Deterministic.of_pure _
  | succ n ih =>
    rw [stagedBlocks]
    by_cases hq : q < 16
    · rw [dif_pos hq]
      apply Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
      intro r
      split_ifs
      · exact Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
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

theorem stagedVerify_deterministic (pk : PublicKey) (m : Message) (bits : List Bool) :
    Deterministic (stagedVerify pk m bits) := by
  unfold stagedVerify
  apply Deterministic.bind (Deterministic.hash _)
  intro answer
  dsimp only
  exact deterministic_ite (stagedRank (pack answer)) _ (pure false)
    (stagedBlocks_deterministic _ _ pk _ 16 0 (fun _ => 0) 0) (Deterministic.of_pure false)

/-- A deliberately loose independent admission bound; the machine proof establishes the cycles. -/
theorem stagedVerify_cost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (stagedVerify pk m bits) 1037 := by
  unfold stagedVerify
  apply AlgorithmCosts.CostAtMost.bind_le
    (AlgorithmCosts.costAtMost_hash _ (b := 1) (by decide)) (b₂ := 1036)
  · intro answer
    dsimp only
    exact cost_ite (stagedRank (pack answer)) _ (pure false) 1036
      (stagedBlocks_cost _ _ pk (min_le_right _ _) 16 0 (fun _ => 0) 0)
      (AlgorithmCosts.costAtMost_pure false 1036)
  · decide

theorem staged_pair_sum (i : ℕ) :
    (∑ q : Fin 16, (digit i (2*q.val) + digit i (2*q.val+1))) =
      ∑ k ∈ Finset.range 32, digit i k := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  simp only [Nat.add_assoc]
  rfl

/-- Caps remove the only high-rank alias of the cheap checksum. -/
theorem staged_caps_sum_le (i : ℕ) (caps : ∀ q : Fin 16, PairAllowed i q.val) :
    ∑ k ∈ Finset.range 32, digit i k ≤ 412 := by
  rw [← staged_pair_sum]
  have h : (∑ q : Fin 16, (digit i (2*q.val) + digit i (2*q.val+1))) ≤
      ∑ q : Fin 16, PairCode.cap q.val := by
    apply Finset.sum_le_sum
    intro q _
    exact caps q
  have total : (∑ q : Fin 16, PairCode.cap q.val) = 412 := by decide +kernel
  omega

theorem stagedRank_and_caps_iff (i : ℕ) :
    stagedRank i ∧ (∀ q : Fin 16, PairAllowed i q.val) ↔ Accepted i := by
  unfold stagedRank Accepted OptimalOTS.target
  constructor
  · rintro ⟨rank, caps⟩
    have := staged_caps_sum_le i caps
    exact ⟨by omega, caps⟩
  · rintro ⟨rank, caps⟩
    exact ⟨Or.inl rank, caps⟩

/-- At the honest length the root step is the graph's root input and root hash. -/
theorem rootStep_eq (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (x : graph.Assignment) (cursor : ℕ) :
    rootStep pk 5504 x = runNodes' index payload [rc, rh] x cursor >>= fun r =>
      pure (decide ((r.1 rh.fin).setWidth 128 = pk)) := by
  have hlt : decide (5504 < 5505) = true := rfl
  simp only [rootStep, runNodes', cursorStep_rc, cursorStep_rh, pure_bind, bind_assoc,
    bind_map_left, Function.update_self, hlt, Bool.and_true]
  rfl

/-- Equality on valid indices at the honest length; no claim on rejecting inputs. -/
theorem stagedBlocks_eq_direct (index : Idx) (payload : List Bool) (pk : PublicKey) :
    stagedBlocks index payload pk 5504 16 0 (fun _ => 0) 0 = (do
      let y ← directReconstruct index payload
      return decide ((y rh.fin).setWidth 128 = pk)) := by
  rw [stagedBlocks_eq_of_allowed index payload pk 5504 16 0 (by omega) ?_]
  · unfold directReconstruct
    rw [runNodes_eq_fst, bind_map_left, ← pairNodes_all, runNodes'_append, bind_assoc]
    apply bind_congr
    intro r
    exact rootStep_eq index payload pk r.1 r.2
  · intro j _ hj
    exact (mem_validSet_accepted index.2).2 ⟨j, by omega⟩

/-- On full-length signatures the strict forest verifier only removes always-reject suffixes. -/
theorem directVerify_prunes_stagedVerify (pk : PublicKey) (m : Message) (bits : List Bool)
    (hlen : bits.length = 5504) :
    RejectAdapter.Prunes (directVerify pk m bits) (stagedVerify pk m bits) := by
  unfold directVerify stagedVerify packIndex
  rw [bind_map_left, padded_of_length hlen, show min bits.length 5505 = 5504 by omega]
  apply RejectAdapter.Prunes.bind_left
  intro answer
  dsimp only
  by_cases hi : pack answer ∈ validSet
  · rw [dif_pos hi, if_pos hlen]
    have acc := mem_validSet_accepted hi
    have rank : stagedRank (pack answer) := (stagedRank_and_caps_iff _).mpr acc |>.1
    rw [if_pos rank]
    have he := stagedBlocks_eq_direct (⟨pack answer, hi⟩ : Idx)
      (Payload.permute (bits.drop 128)) pk
    dsimp only [Idx.toRaw] at he
    rw [he]
    apply RejectAdapter.Prunes.bind_left
    intro y
    convert RejectAdapter.Prunes.refl
      (pure (decide ((y rh.fin).setWidth 128 = pk)) : OracleComp Spec Bool) using 1
    congr 1
    exact decide_eq_decide.mpr Iff.rfl
  · rw [dif_neg hi]
    split_ifs with guard
    · have bad : ¬ ∀ q : Fin 16, PairAllowed (pack answer) q.val := by
        intro caps
        exact hi (mem_validSet.mpr ⟨pack_lt answer,
          (stagedRank_and_caps_iff _).mp ⟨guard, caps⟩⟩)
      push Not at bad
      obtain ⟨q, hq⟩ := bad
      apply RejectAdapter.Prunes.of_support
      exact stagedBlocks_rejects _ _ _ _ 16 0
        ⟨q.val, Nat.zero_le _, by simpa using q.isLt, hq⟩ _ _
    · exact RejectAdapter.Prunes.refl _

/-- The verifier of the security proof: strict on full-length signatures, the machine's program
on shorter ones, and immediate rejection of longer ones. -/
def strictVerify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool :=
  if bits.length = 5504 then directVerify pk m bits
  else if bits.length < 5504 then stagedVerify pk m bits
  else pure false

theorem stagedVerify_accept (pk : PublicKey) (m : Message) (bits : List Bool) (c : Cache)
    (p : Bool × Cache) (hp : p ∈ support (run (stagedVerify pk m bits) c)) (hok : p.1 = true) :
    ∃ u : BitVec (min bits.length 5505 + 639), ∃ w, p.2 ⟨_, u⟩ = some w ∧ trunc128 w = pk := by
  unfold stagedVerify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨answer, c₁⟩, -, hp⟩ := hp
  dsimp only at hp
  split_ifs at hp
  · exact stagedBlocks_accept _ _ _ _ 16 0 _ _ c₁ p hp hok
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
    · obtain ⟨u, w, hw, hpk⟩ := stagedVerify_accept pk m bits c p hp hok
      exact ⟨_, by unfold ShortLen; omega, u, w, hw, hpk⟩
    · rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      cases hok

theorem stagedVerify_oversized (pk : PublicKey) (m : Message) (bits : List Bool)
    (h : 5504 < bits.length) : ∀ b ∈ support (stagedVerify pk m bits), b = false := by
  have ha : min bits.length 5505 = 5505 := by omega
  unfold stagedVerify
  rw [ha]
  intro b hb
  rw [support_bind] at hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨answer, -, hb⟩ := hb
  split_ifs at hb
  · exact stagedBlocks_oversized _ _ _ 16 0 _ _ b hb
  · simpa only [support_pure, Set.mem_singleton_iff] using hb

/-- The machine's verifier only adds terminal constant-answer suffixes to the strict one. -/
theorem strict_prunes_staged (pk : PublicKey) (m : Message) (bits : List Bool) :
    RejectAdapter.Prunes (strictVerify pk m bits) (stagedVerify pk m bits) := by
  unfold strictVerify
  split_ifs with h5504 hlt
  · exact directVerify_prunes_stagedVerify pk m bits h5504
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
    CostAtMost (strictVerify pk m bits) 1037 := by
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

/-- Honest signatures have exactly 5504 bits. -/
theorem honest_length (sk : RiscvUpperForest.Wire.scheme.SecretKey) (m : Message)
    (bits : List Bool) (h : some bits ∈ support (RiscvUpperForest.Wire.scheme.sign sk m)) :
    bits.length = 5504 := by
  change some bits ∈ support
    (Option.map AlgorithmAdapter.encodeSignature <$> forestScheme.sign sk m) at h
  rw [support_map] at h
  obtain ⟨σ, hσ, he⟩ := h
  cases σ with
  | none => cases he
  | some σ =>
    obtain ⟨i, hi⟩ := AlgorithmAdapter.sign_returns forestScheme sk m σ hσ
    have e : AlgorithmAdapter.encodeSignature σ = bits := Option.some.inj he
    rw [← e, AlgorithmAdapter.length_encodeSignature, hi]
    exact congrArg (nonceBits + ·)
      ((AlgorithmAdapter.length_encode _ _ sk).trans (fixed_revealBits i))

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

/-- The 348-cycle scheme retains the restricted forest's keys and signer. -/
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
