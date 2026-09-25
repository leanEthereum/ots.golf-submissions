import Submissions.UpperRiscvHint.MixedChain
import Submissions.UpperRiscvHint.RejectAdapter

/-!
# The verifier with dispatch-time rejection

The machine hashes an expanding left chain once before the digit-pair cap is tested. This
interpreter preserves that query, including on invalid indices. Strict DAG verification is a
terminal pruning of this computation, not equality of oracle traces on rejected inputs.
-/

noncomputable section
open scoped Classical

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag
open Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph pkBits
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

/-- Full node list of the remaining pair program, without any digit-cap rejection. -/
def pairNodes : (n q : ℕ) → List Name
  | 0, _ => [rc, rh]
  | n+1, q => if hq : q < 16 then
      chainNodes ⟨2*q, by omega⟩ ++ chainNodes ⟨2*q+1, by omega⟩ ++ pairNodes n (q+1)
    else []

/-- The exact staged oracle program. `payload` is already in chain execution order. -/
def stagedBlocks (index : RawIdx) (payload : List Bool) (pk : PublicKey) :
    (n q : ℕ) → graph.Assignment → ℕ → OracleComp Spec Bool
  | 0, _, x, cursor => do
      let r ← runNodes' index payload [rc, rh] x cursor
      return decide ((r.1 rh.fin).setWidth 128 = pk)
  | n+1, q, x, cursor => if hq : q < 16 then do
      let r ← runNodes' index payload (entryNodes index ⟨2*q, by omega⟩) x cursor
      if PairAllowed index.val q then
        let r' ← runNodes' index payload
          (tableNodes index ⟨2*q, by omega⟩ ++ chainNodes ⟨2*q+1, by omega⟩) r.1 r.2
        stagedBlocks index payload pk n (q+1) r'.1 r'.2
      else pure false
    else pure false

attribute [local irreducible] stagedBlocks

/-- Machine-facing expansion: `some` changes the output interface, never the query trace. -/
theorem stagedBlocks_some_succ (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (hq : q < 16) (x : graph.Assignment) (cursor : ℕ) :
    some <$> stagedBlocks index payload pk (n+1) q x cursor = (do
      let r ← runNodes' index payload (entryNodes index ⟨2*q, by omega⟩) x cursor
      if PairAllowed index.val q then
        let r' ← runNodes' index payload
          (tableNodes index ⟨2*q, by omega⟩ ++ chainNodes ⟨2*q+1, by omega⟩) r.1 r.2
        some <$> stagedBlocks index payload pk n (q+1) r'.1 r'.2
      else pure (some false)) := by
  rw [stagedBlocks, dif_pos hq, map_bind]
  congr 1
  funext r
  split_ifs <;> simp only [map_bind, map_pure]

theorem stagedBlocks_some_zero (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    some <$> stagedBlocks index payload pk 0 q x cursor = (do
      let r ← runNodes' index payload [rc, rh] x cursor
      return some (decide ((r.1 rh.fin).setWidth 128 = pk))) := by
  simp only [stagedBlocks, map_bind, map_pure]

theorem stagedBlocks_eq_of_allowed (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (hq : q+n ≤ 16)
    (caps : ∀ j, q ≤ j → j < q+n → PairAllowed index.val j)
    (x : graph.Assignment) (cursor : ℕ) :
    stagedBlocks index payload pk n q x cursor = (do
      let r ← runNodes' index payload (pairNodes n q) x cursor
      return decide ((r.1 rh.fin).setWidth 128 = pk)) := by
  induction n generalizing q x cursor with
  | zero => rw [stagedBlocks, pairNodes]
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
theorem stagedBlocks_rejects (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (bad : ∃ j, q ≤ j ∧ j < q+n ∧ ¬ PairAllowed index.val j)
    (x : graph.Assignment) (cursor : ℕ) :
    ∀ b ∈ support (stagedBlocks index payload pk n q x cursor), b = false := by
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

set_option maxRecDepth 100000 in
theorem pairNodes_all : pairNodes 16 0 = order := by decide +kernel

/-- The two checksum ranks admitted before the staged pair checks. -/
def stagedRank (i : ℕ) : Prop :=
  (∑ k ∈ Finset.range 32, digit i k) = 158 ∨
  (∑ k ∈ Finset.range 32, digit i k) = 413

instance : DecidablePred stagedRank := fun _ => inferInstanceAs (Decidable (_ ∨ _))

attribute [local irreducible] stagedRank

/-- Raw-signature verifier matching the new machine's complete oracle behavior. -/
def stagedVerify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool := do
  let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits (bits.take 128)))
  let index : RawIdx := ⟨pack answer, pack_lt answer⟩
  if stagedRank index.val ∧ bits.length = 5504 then
    stagedBlocks index (Payload.permute (bits.drop 128)) pk 16 0 (fun _ => 0) 0
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

theorem stagedBlocks_cost (index : RawIdx) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    CostAtMost (stagedBlocks index payload pk n q x cursor) (64*n+12) := by
  induction n generalizing q x cursor with
  | zero =>
    unfold stagedBlocks
    exact AlgorithmCosts.CostAtMost.bind_le
      (runNodes'_cost index payload [rc, rh] x cursor)
      (b₂ := 0) (fun _ => AlgorithmCosts.costAtMost_pure _ _) (by decide)
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
    (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    Deterministic (stagedBlocks index payload pk n q x cursor) := by
  induction n generalizing q x cursor with
  | zero =>
    rw [stagedBlocks]
    exact Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
      fun _ => Deterministic.of_pure _
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
  exact deterministic_ite (stagedRank (pack answer) ∧ bits.length = 5504)
    (stagedBlocks ⟨pack answer, pack_lt answer⟩ (Payload.permute (bits.drop 128)) pk 16 0 (fun _ => 0) 0)
    (pure false)
    (stagedBlocks_deterministic ⟨pack answer, pack_lt answer⟩
      (Payload.permute (bits.drop 128)) pk 16 0 (fun _ => 0) 0)
    (Deterministic.of_pure false)

/-- A deliberately loose independent admission bound; the machine proof establishes 349 cycles. -/
theorem stagedVerify_cost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (stagedVerify pk m bits) 1037 := by
  unfold stagedVerify
  apply AlgorithmCosts.CostAtMost.bind_le
    (AlgorithmCosts.costAtMost_hash _ (b := 1) (by decide)) (b₂ := 1036)
  · intro answer
    dsimp only
    exact cost_ite (stagedRank (pack answer) ∧ bits.length = 5504)
      (stagedBlocks ⟨pack answer, pack_lt answer⟩ (Payload.permute (bits.drop 128)) pk 16 0 (fun _ => 0) 0)
      (pure false) 1036
      (stagedBlocks_cost ⟨pack answer, pack_lt answer⟩
        (Payload.permute (bits.drop 128)) pk 16 0 (fun _ => 0) 0)
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

/-- Equality on valid inputs; no claim of trace equality is made on rejecting inputs. -/
theorem stagedBlocks_eq_direct (index : Idx) (payload : List Bool) (pk : PublicKey) :
    stagedBlocks index payload pk 16 0 (fun _ => 0) 0 = (do
      let y ← directReconstruct index payload
      return decide ((y rh.fin).setWidth 128 = pk)) := by
  rw [stagedBlocks_eq_of_allowed index payload pk 16 0 (by omega) ?_]
  · rw [pairNodes_all]
    unfold directReconstruct
    rw [runNodes_eq_fst, bind_map_left]
  · intro j _ hj
    exact (mem_validSet_accepted index.2).2 ⟨j, by omega⟩

/-- The strict certified forest verifier only removes always-reject query suffixes. -/
theorem directVerify_prunes_stagedVerify (pk : PublicKey) (m : Message) (bits : List Bool) :
    RejectAdapter.Prunes (directVerify pk m bits) (stagedVerify pk m bits) := by
  unfold directVerify stagedVerify packIndex
  rw [bind_map_left]
  apply RejectAdapter.Prunes.bind_left
  intro answer
  dsimp only
  by_cases hi : pack answer ∈ validSet
  · rw [dif_pos hi]
    have acc := mem_validSet_accepted hi
    have rank : stagedRank (pack answer) := (stagedRank_and_caps_iff _).mpr acc |>.1
    by_cases hlen : bits.length = 5504
    · rw [if_pos hlen, if_pos ⟨rank, hlen⟩]
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
    · rw [if_neg hlen, if_neg (fun h => hlen h.2)]
      exact RejectAdapter.Prunes.refl _
  · rw [dif_neg hi]
    split_ifs with guard
    · have bad : ¬ ∀ q : Fin 16, PairAllowed (pack answer) q.val := by
        intro caps
        exact hi (mem_validSet.mpr ⟨pack_lt answer,
          (stagedRank_and_caps_iff _).mp ⟨guard.1, caps⟩⟩)
      push Not at bad
      obtain ⟨q, hq⟩ := bad
      apply RejectAdapter.Prunes.of_support
      exact stagedBlocks_rejects _ _ _ 16 0
        ⟨q.val, Nat.zero_le _, by simpa using q.isLt, hq⟩ _ _
    · exact RejectAdapter.Prunes.refl _

/-- The 349-cycle scheme retains the restricted forest's keys and signer. -/
def stagedScheme : OracleAlgorithm.Scheme :=
  RejectAdapter.scheme RiscvUpperForest.Wire.scheme stagedVerify

theorem stagedScheme_secure : stagedScheme.Secure := by
  apply RejectAdapter.secure RiscvUpperForest.Wire.scheme stagedVerify
  · intro pk m bits
    rw [← directVerify_eq]
    exact directVerify_prunes_stagedVerify pk m bits
  · exact RiscvUpperForest.Wire.secure

theorem stagedScheme_admissible : stagedScheme.Admissible := by
  apply RejectAdapter.admissible RiscvUpperForest.Wire.scheme stagedVerify
  · intro pk m bits
    rw [← directVerify_eq]
    exact directVerify_prunes_stagedVerify pk m bits
  · exact RiscvUpperForest.Wire.admissible
  · exact stagedVerify_deterministic
  · intro pk m bits
    exact (stagedVerify_cost pk m bits).mono (by decide)

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
