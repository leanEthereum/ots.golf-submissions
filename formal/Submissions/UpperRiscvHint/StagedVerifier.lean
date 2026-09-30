import Submissions.UpperRiscvHint.Reader
import Submissions.UpperRiscvHint.RejectAdapter
import Submissions.UpperRiscvHint.Valid

/-!
# The canonical staged verifier

The abstract verifier checks the weighted rank, then reconstructs the free chain,
sixteen recoded pairs and root. The retained `PairAllowed` predicates all hold for
the weighted alphabet. `CheckedRun` separately models the machine's delayed root
check, including arbitrary view counts and their preceding chain queries.
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
      chainNodes ⟨2*q+1, by omega⟩ ++ chainNodes ⟨2*q+2, by omega⟩ ++ pairNodes n (q+1)
    else []

/-- The exact staged oracle program; `payload` lists the disclosed values in chain order. -/
def stagedBlocks (index : ChainIndex) (payload : List Bool) (pk : PublicKey) :
    (n q : ℕ) → graph.Assignment → ℕ → OracleComp Spec Bool
  | 0, _, x, cursor => do
      let r ← runNodes' index payload [rc, rh] x cursor
      return decide (flipHi ((r.1 rh.fin).setWidth 128) = pk)
  | n+1, q, x, cursor => if hq : q < 16 then
      if PairAllowed index.val q then do
        let r ← runNodes' index payload
          (chainNodes ⟨2*q+1, by omega⟩ ++ chainNodes ⟨2*q+2, by omega⟩) x cursor
        stagedBlocks index payload pk n (q+1) r.1 r.2
      else pure false
    else pure false

/-- The same query trace, returning the low 128 root bits, or `none` at a forbidden pair. -/
def stagedRun (index : ChainIndex) (payload : List Bool) :
    (n q : ℕ) → graph.Assignment → ℕ → OracleComp Spec (Option (BitVec 128))
  | 0, _, x, cursor => do
      let r ← runNodes' index payload [rc, rh] x cursor
      return some ((r.1 rh.fin).setWidth 128)
  | n+1, q, x, cursor => if hq : q < 16 then
      if PairAllowed index.val q then do
        let r ← runNodes' index payload
          (chainNodes ⟨2*q+1, by omega⟩ ++ chainNodes ⟨2*q+2, by omega⟩) x cursor
        stagedRun index payload n (q+1) r.1 r.2
      else pure none
    else pure none

/-- The free chain, then the pairs from cursor 192. -/
def freeBlocks (index : ChainIndex) (payload : List Bool) (pk : PublicKey) (x : graph.Assignment) :
    OracleComp Spec Bool := do
  let r ← runNodes' index payload (chainNodes 0) x 0
  stagedBlocks index payload pk 16 0 r.1 r.2

/-- The same query trace as `freeBlocks`, returning the low 128 root bits. -/
def freeRun (index : ChainIndex) (payload : List Bool) (x : graph.Assignment) :
    OracleComp Spec (Option (BitVec 128)) := do
  let r ← runNodes' index payload (chainNodes 0) x 0
  stagedRun index payload 16 0 r.1 r.2

theorem stagedBlocks_eq_stagedRun (index : ChainIndex) (payload : List Bool) (pk : PublicKey) :
    ∀ (n q : ℕ) (x : graph.Assignment) (cursor : ℕ),
      stagedBlocks index payload pk n q x cursor =
        (fun o => o.elim false fun r => decide (flipHi r = pk)) <$> stagedRun index payload n q x cursor := by
  intro n
  induction n with
  | zero => intro q x cursor; simp only [stagedBlocks, stagedRun, map_bind, map_pure]; rfl
  | succ n ih =>
    intro q x cursor
    rw [stagedBlocks, stagedRun]
    split_ifs
    · simp only [map_bind, ih]
    · rfl
    · rfl

theorem freeBlocks_eq_freeRun (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (x : graph.Assignment) :
    freeBlocks index payload pk x =
      (fun o => o.elim false fun r => decide (flipHi r = pk)) <$> freeRun index payload x := by
  simp only [freeBlocks, freeRun, map_bind, stagedBlocks_eq_stagedRun]

attribute [local irreducible] stagedBlocks
attribute [local irreducible] stagedRun

theorem stagedBlocks_eq_of_allowed (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (hq : q+n ≤ 16)
    (caps : ∀ j, q ≤ j → j < q+n → PairAllowed index.val j)
    (x : graph.Assignment) (cursor : ℕ) :
    stagedBlocks index payload pk n q x cursor = (do
      let r ← runNodes' index payload (pairNodes n q) x cursor
      return decide (flipHi ((r.1 rh.fin).setWidth 128) = pk)) := by
  induction n generalizing q x cursor with
  | zero => rw [stagedBlocks, pairNodes]
  | succ n ih =>
    have hq16 : q < 16 := by omega
    rw [stagedBlocks, dif_pos hq16, pairNodes, dif_pos hq16, if_pos (caps q le_rfl (by omega))]
    simp only [List.append_assoc, runNodes'_append, bind_assoc]
    apply bind_congr
    intro r
    apply bind_congr
    intro r'
    exact ih (q+1) (by omega) (fun j hj hj' => caps j (by omega) (by omega)) r'.1 r'.2

/-- A failed cap eventually returns false, despite any earlier chain queries. -/
theorem stagedBlocks_rejects (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
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
theorem pairNodes_all : chainNodes 0 ++ pairNodes 16 0 = order := by decide +kernel

/-- The free counts the machine admits before the staged pair checks: `S + c ≡ target` with
`c < 19`. -/
def stagedRank (i : ℕ) : Prop := freeDigit i < 19

instance : DecidablePred stagedRank := fun _ => inferInstanceAs (Decidable (_ < _))

attribute [local irreducible] stagedRank

/-- Raw-signature verifier matching the new machine's complete oracle behavior. -/
def stagedVerify (pk : PublicKey) (m : Message) (bits : List Bool) : OracleComp Spec Bool := do
  let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits (bits.take 128)))
  let index : ChainIndex := ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩
  if stagedRank index.val ∧ bits.length = fullSignatureBits index then
    freeBlocks index (bits.drop 128) pk (fun _ => 0)
  else pure false

theorem evalName_cost (x : graph.Assignment) (n : Name) :
    CostAtMost (evalName x n) n.cost := by
  rw [evalName_eq, ← graph_nodeCost_fin]
  exact AlgorithmCosts.Dag.Graph.costAtMost_evalNode graph x n.fin (pure 0)
    (AlgorithmCosts.costAtMost_pure _ _)

theorem cursorStep_cost (index : ChainIndex) (payload : List Bool)
    (x : graph.Assignment) (cursor : ℕ) (n : Name) :
    CostAtMost (cursorStep index payload x cursor n) n.cost := by
  unfold cursorStep
  split_ifs
  · exact AlgorithmCosts.costAtMost_pure _ _
  · exact AlgorithmCosts.CostAtMost.map (evalName_cost x n) _
  · exact AlgorithmCosts.costAtMost_pure _ _

theorem runNodes'_cost (index : ChainIndex) (payload : List Bool)
    (nodes : List Name) (x : graph.Assignment) (cursor : ℕ) :
    CostAtMost (runNodes' index payload nodes x cursor) (nodes.map Name.cost).sum := by
  induction nodes generalizing x cursor with
  | nil => exact AlgorithmCosts.costAtMost_pure _ _
  | cons n nodes ih =>
    rw [runNodes', List.map_cons, List.sum_cons]
    exact AlgorithmCosts.CostAtMost.bind (cursorStep_cost index payload x cursor n)
      fun r => ih r.1 r.2

theorem chainNodes_cost (k : Chain) : ((chainNodes k).map Name.cost).sum = 32 := by
  have h : ∀ k : Chain, ((chainNodes k).map Name.cost).sum = 32 := by decide +kernel
  exact h k

theorem stagedBlocks_cost (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    CostAtMost (stagedBlocks index payload pk n q x cursor) (64*n+14) := by
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
      let k₀ : Chain := ⟨2*q+1, by omega⟩
      let k₁ : Chain := ⟨2*q+2, by omega⟩
      have total : ((chainNodes k₀ ++ chainNodes k₁).map Name.cost).sum = 64 := by
        rw [List.map_append, List.sum_append, chainNodes_cost, chainNodes_cost]
      split_ifs
      · apply AlgorithmCosts.CostAtMost.bind_le
          (runNodes'_cost index payload (chainNodes k₀ ++ chainNodes k₁) x cursor)
          (b₂ := 64*n+14) (fun r => ih (q+1) r.1 r.2)
        rw [total]; omega
      · exact AlgorithmCosts.costAtMost_pure _ _
    · rw [dif_neg hq]
      exact AlgorithmCosts.costAtMost_pure _ _

theorem evalName_deterministic (x : graph.Assignment) (n : Name) :
    Deterministic (evalName x n) := by
  rw [evalName_eq]
  exact Dag.Graph.deterministic_evalNode graph x n.fin (pure 0) (Deterministic.of_pure _)

theorem cursorStep_deterministic (index : ChainIndex) (payload : List Bool)
    (x : graph.Assignment) (cursor : ℕ) (n : Name) :
    Deterministic (cursorStep index payload x cursor n) := by
  unfold cursorStep
  split_ifs
  · exact Deterministic.of_pure _
  · exact Deterministic.map (evalName_deterministic x n) _
  · exact Deterministic.of_pure _

theorem runNodes'_deterministic (index : ChainIndex) (payload : List Bool)
    (nodes : List Name) (x : graph.Assignment) (cursor : ℕ) :
    Deterministic (runNodes' index payload nodes x cursor) := by
  induction nodes generalizing x cursor with
  | nil => exact Deterministic.of_pure _
  | cons n nodes ih =>
    rw [runNodes']
    exact Deterministic.bind (cursorStep_deterministic index payload x cursor n)
      fun r => ih r.1 r.2

theorem stagedBlocks_deterministic (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
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
      split_ifs
      · exact Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
          fun r => ih (q+1) r.1 r.2
      · exact Deterministic.of_pure _
    · rw [dif_neg hq]
      exact Deterministic.of_pure _

theorem stagedRun_deterministic (index : ChainIndex) (payload : List Bool)
    (n q : ℕ) (x : graph.Assignment) (cursor : ℕ) :
    Deterministic (stagedRun index payload n q x cursor) := by
  induction n generalizing q x cursor with
  | zero =>
    rw [stagedRun]
    exact Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
      fun _ => Deterministic.of_pure _
  | succ n ih =>
    rw [stagedRun]
    by_cases hq : q < 16
    · rw [dif_pos hq]
      split_ifs
      · exact Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
          fun r => ih (q+1) r.1 r.2
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

theorem freeBlocks_deterministic (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (x : graph.Assignment) : Deterministic (freeBlocks index payload pk x) :=
  Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
    fun r => stagedBlocks_deterministic index payload pk 16 0 r.1 r.2

theorem freeRun_deterministic (index : ChainIndex) (payload : List Bool) (x : graph.Assignment) :
    Deterministic (freeRun index payload x) :=
  Deterministic.bind (runNodes'_deterministic _ _ _ _ _)
    fun r => stagedRun_deterministic index payload 16 0 r.1 r.2

theorem freeBlocks_cost (index : ChainIndex) (payload : List Bool) (pk : PublicKey)
    (x : graph.Assignment) : CostAtMost (freeBlocks index payload pk x) 1070 := by
  apply AlgorithmCosts.CostAtMost.bind_le (runNodes'_cost index payload (chainNodes 0) x 0)
    (b₂ := 64*16+14) (fun r => stagedBlocks_cost index payload pk 16 0 r.1 r.2)
  rw [chainNodes_cost]

theorem stagedVerify_deterministic (pk : PublicKey) (m : Message) (bits : List Bool) :
    Deterministic (stagedVerify pk m bits) := by
  unfold stagedVerify
  apply Deterministic.bind (Deterministic.hash _)
  intro answer
  dsimp only
  exact deterministic_ite (stagedRank (pack answer) ∧ bits.length = fullSignatureBits (ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩))
    (freeBlocks (ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩) (bits.drop 128) pk (fun _ => 0))
    (pure false)
    (freeBlocks_deterministic (ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩) (bits.drop 128) pk (fun _ => 0))
    (Deterministic.of_pure false)

/-- A deliberately loose independent admission bound; the machine proof establishes the cycle count. -/
theorem stagedVerify_cost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (stagedVerify pk m bits) 1071 := by
  unfold stagedVerify
  apply AlgorithmCosts.CostAtMost.bind_le
    (AlgorithmCosts.costAtMost_hash _ (b := 1) (by decide)) (b₂ := 1070)
  · intro answer
    dsimp only
    exact cost_ite (stagedRank (pack answer) ∧ bits.length = fullSignatureBits (ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩))
      (freeBlocks (ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩) (bits.drop 128) pk (fun _ => 0))
      (pure false) 1070
      (freeBlocks_cost (ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩) (bits.drop 128) pk (fun _ => 0))
      (AlgorithmCosts.costAtMost_pure false 1070)
  · decide

theorem staged_pair_sum (i : ℕ) :
    (∑ q : Fin 16, PairCode.weight q.val (rawPair i q.val)) = digitSum i := rfl

/-- Weighted pair costs bound the sum by 384, excluding the next checksum alias. -/
theorem staged_caps_sum_le (i : ℕ) (_caps : ∀ q : Fin 16, PairAllowed i q.val) :
    digitSum i ≤ 384 := digitSum_le i

theorem stagedRank_and_caps_iff (i : ℕ) :
    stagedRank i ∧ (∀ q : Fin 16, PairAllowed i q.val) ↔ Accepted i := by
  unfold stagedRank Accepted OptimalOTS.target freeDigit
  constructor
  · rintro ⟨rank, caps⟩
    have := staged_caps_sum_le i caps
    exact ⟨by omega, caps⟩
  · rintro ⟨rank, caps⟩
    exact ⟨by omega, caps⟩

/-- Equality on valid inputs; no claim of trace equality is made on rejecting inputs. -/
theorem stagedBlocks_eq_direct (index : Idx) (payload : List Bool) (pk : PublicKey) :
    freeBlocks index payload pk (fun _ => 0) = (do
      let y ← directReconstruct index payload
      return decide (flipHi ((y rh.fin).setWidth 128) = pk)) := by
  unfold freeBlocks
  simp only [stagedBlocks_eq_of_allowed index payload pk 16 0 (by omega)
    (fun j _ hj => (mem_validSet_accepted index.2).2 ⟨j, by omega⟩)]
  unfold directReconstruct
  rw [← pairNodes_all, runNodes_eq_fst, runNodes'_append, bind_map_left, bind_assoc]

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
    dsimp +instances only [Idx.toRaw]
    have acc := mem_validSet_accepted hi
    have rank : stagedRank (pack answer) := (stagedRank_and_caps_iff _).mpr acc |>.1
    by_cases hlen : bits.length = fullSignatureBits (ChainIndex.ofRaw ⟨pack answer, pack_lt answer⟩)
    · rw [if_pos hlen, if_pos ⟨rank, hlen⟩]
      have he := stagedBlocks_eq_direct (⟨pack answer, hi⟩ : Idx)
        (bits.drop 128) pk
      dsimp only [Idx.toRaw] at he
      rw [he]
      apply RejectAdapter.Prunes.bind_left
      intro y
      convert RejectAdapter.Prunes.refl
        (pure (decide (flipHi ((y rh.fin).setWidth 128) = pk)) : OracleComp Spec Bool) using 1
    · rw [if_neg hlen, if_neg (fun h => hlen h.2)]
      exact RejectAdapter.Prunes.refl _
  · rw [dif_neg hi]
    split_ifs with guard
    · exact False.elim (hi (mem_validSet.mpr ⟨pack_lt answer,
        (stagedRank_and_caps_iff _).mp ⟨guard.1,fun q => pairAllowed_all _ q⟩⟩))
    · exact RejectAdapter.Prunes.refl _

/-- The scheme retains the restricted forest's keys and signer. -/
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

end OptimalOTS.RiscvMixedProgram
