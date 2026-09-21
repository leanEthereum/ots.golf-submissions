import Submissions.UpperRiscv.IndexLanes

/-!
# The arithmetic of the index check

The index answer is held in four words. The sum of the four masked words has four lanes, each
`4 · (fine fields) + 1024 · (coarse fields)`; the fold brings the coarse part down, and the top lane
after the broadcast multiplication is four times the field sum of the answer (`top_fold_answer`),
which the sum check compares with `4 · 215`. Each stored lane holds
`base − (4 · dA + 1024 · dB)` (`lane_halfword`).
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64

theorem wid_le (k : ℕ) : wid k ≤ 5 := by unfold wid; split_ifs <;> omega

theorem fld_lt (u p b : ℕ) : fld u p b < 2 ^ b := Nat.mod_lt _ (by positivity)

theorem fineFld_le (u l : ℕ) : fineFld u l ≤ 31 := by
  have := fld_lt u (16 * l + 2) 5; unfold fineFld; omega

theorem coarseFld_le (u l : ℕ) : coarseFld u l ≤ 15 := by
  have := fld_lt u (16 * l + 10) 4; unfold coarseFld; omega

theorem coarseOf_le (g u l : ℕ) : coarseOf g u l ≤ 15 := by
  unfold coarseOf; split_ifs
  · exact coarseFld_le u l
  · omega

/-- One lane of a masked word is below `15485`. -/
theorem laneEntry_le (g u l : ℕ) : 4 * fineFld u l + 1024 * coarseOf g u l ≤ 15484 := by
  have := fineFld_le u l; have := coarseOf_le g u l; omega

theorem laneNat_le (u g : ℕ) : laneNat u g ≤ 15484 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) := by
  unfold laneNat
  have := laneEntry_le g u 0
  have := laneEntry_le g u 1
  have := laneEntry_le g u 2
  have := laneEntry_le g u 3
  omega

/-- The mask registers hold the two masks. -/
def MasksLoaded (a : MachineState) : Prop := ∀ g, g < 4 → a.getReg (maskReg g) = W (maskNat g)

theorem laneOf_toNat (a : MachineState) (hm : MasksLoaded a) (g : ℕ) (hg : g < 4) :
    (laneOf a g).toNat = laneNat (a.getReg (wordReg g)).toNat g := by
  unfold laneOf
  rw [hm g hg]
  exact laneValue_toNat _ _

theorem laneSum_toNat (a : MachineState) (hm : MasksLoaded a) :
    ∀ n, n ≤ 4 → (laneSum a n).toNat =
      ∑ g ∈ Finset.range n, laneNat (a.getReg (wordReg g)).toNat g := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hb : ∀ n, ∑ g ∈ Finset.range n, laneNat (a.getReg (wordReg g)).toNat g ≤
        n * (15484 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by
      intro n
      calc ∑ g ∈ Finset.range n, laneNat (a.getReg (wordReg g)).toNat g
          ≤ ∑ _g ∈ Finset.range n, 15484 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) :=
            Finset.sum_le_sum fun g _ => laneNat_le _ _
        _ = n * (15484 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by simp
    rw [laneSum, BitVec.toNat_add, ih (by omega), laneOf_toNat a hm n (by omega),
      Finset.sum_range_succ, Nat.mod_eq_of_lt]
    have h1 := hb n
    have h2 := laneNat_le (a.getReg (wordReg n)).toNat n
    have : n * (15484 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) ≤
        3 * (15484 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- The word values of a state. -/
def wordsOf (a : MachineState) (g : ℕ) : ℕ := (a.getReg (wordReg g)).toNat

/-- The fine fields of lane `l` over the four words, and the coarse fields over the three pair
words. -/
def fineTotal (u : ℕ → ℕ) (l : ℕ) : ℕ := ∑ g ∈ Finset.range 4, fineFld (u g) l

def coarseTotal (u : ℕ → ℕ) (l : ℕ) : ℕ := ∑ g ∈ Finset.range 3, coarseFld (u g) l

theorem fineTotal_lt (u : ℕ → ℕ) (l : ℕ) : fineTotal u l < 128 := by
  unfold fineTotal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have := fineFld_le (u 0) l; have := fineFld_le (u 1) l
  have := fineFld_le (u 2) l; have := fineFld_le (u 3) l
  omega

theorem coarseTotal_lt (u : ℕ → ℕ) (l : ℕ) : coarseTotal u l < 48 := by
  unfold coarseTotal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have := coarseFld_le (u 0) l; have := coarseFld_le (u 1) l; have := coarseFld_le (u 2) l
  omega

/-- The lane sum is the pre-fold value of the fine and coarse totals. -/
theorem laneSum_lanes (u : ℕ → ℕ) :
    ∑ g ∈ Finset.range 4, laneNat (u g) g =
      preFold (fineTotal u 0) (fineTotal u 1) (fineTotal u 2) (fineTotal u 3)
        (coarseTotal u 0) (coarseTotal u 1) (coarseTotal u 2) (coarseTotal u 3) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, laneNat, preFold, fineTotal,
    coarseTotal, coarseOf, ↓reduceIte, show (3 : ℕ) < 3 ↔ False by simp,
    show (0 : ℕ) < 3 by norm_num, show (1 : ℕ) < 3 by norm_num, show (2 : ℕ) < 3 by norm_num]
  ring

theorem broadcast_toNat (B : ℕ) (hB : B < 2 ^ 16) :
    (W (broadcast B)).toNat = broadcast B := by
  apply W_toNat
  unfold broadcast
  omega

/-- The fold of the lane sum, lane by lane. -/
theorem fold_laneSum (a : MachineState) (hm : MasksLoaded a) (hfm : a.getReg .x1 = W (broadcast foldMask)) :
    (foldValue (laneSum a 4) (a.getReg .x1)).toNat =
      4 * (fineTotal (wordsOf a) 0 + coarseTotal (wordsOf a) 0) +
      2 ^ 16 * (4 * (fineTotal (wordsOf a) 1 + coarseTotal (wordsOf a) 1)) +
      2 ^ 32 * (4 * (fineTotal (wordsOf a) 2 + coarseTotal (wordsOf a) 2)) +
      2 ^ 48 * (4 * (fineTotal (wordsOf a) 3 + coarseTotal (wordsOf a) 3)) := by
  have hL : (laneSum a 4).toNat = preFold (fineTotal (wordsOf a) 0) (fineTotal (wordsOf a) 1)
      (fineTotal (wordsOf a) 2) (fineTotal (wordsOf a) 3) (coarseTotal (wordsOf a) 0)
      (coarseTotal (wordsOf a) 1) (coarseTotal (wordsOf a) 2) (coarseTotal (wordsOf a) 3) := by
    rw [laneSum_toNat a hm 4 le_rfl]
    exact laneSum_lanes (wordsOf a)
  have f0 := fineTotal_lt (wordsOf a) 0; have f1 := fineTotal_lt (wordsOf a) 1
  have f2 := fineTotal_lt (wordsOf a) 2; have f3 := fineTotal_lt (wordsOf a) 3
  have c0 := coarseTotal_lt (wordsOf a) 0; have c1 := coarseTotal_lt (wordsOf a) 1
  have c2 := coarseTotal_lt (wordsOf a) 2; have c3 := coarseTotal_lt (wordsOf a) 3
  have hfold := fold_toNat _ _ _ _ _ _ _ _ f0 f1 f2 f3 c0 c1 c2 c3
  have hmask : (W (broadcast foldMask)).toNat = broadcast foldMask :=
    broadcast_toNat _ (by norm_num [foldMask])
  unfold foldValue
  rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, hfm, hmask, hL, hfold, Nat.mod_eq_of_lt]
  unfold preFold at *
  omega

/-! ## The fields of the answer -/

/-- Word `g` of the index answer. -/
def wordOf (answer : BitVec hashBits) (g : ℕ) : Word := answer.extractLsb' (64 * g) 64

theorem fld_extract (answer : BitVec hashBits) (w p b : ℕ) (hpb : p + b ≤ 64) :
    fld (wordOf answer w).toNat p b = answer.toNat / 2 ^ (64 * w + p) % 2 ^ b := by
  unfold fld wordOf
  rw [show (BitVec.extractLsb' (64 * w) 64 answer).toNat = answer.toNat / 2 ^ (64 * w) % 2 ^ 64 by
      simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow],
    show (2 : ℕ) ^ 64 = 2 ^ p * 2 ^ (64 - p) by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)),
    Nat.div_div_eq_div_mul, ← pow_add]

/-- The chain whose digit is the fine field of lane `l` of word `g`. -/
def fineChain (g l : ℕ) : ℕ := if g < 3 then 2 * (4 * g + l) else 24 + l

/-- The chain whose digit is the coarse field of lane `l` of pair word `g`. -/
def coarseChain (g l : ℕ) : ℕ := 2 * (4 * g + l) + 1

theorem fieldPos_fine (g l : ℕ) (hg : g < 4) (hl : l < 4) :
    fieldPos (fineChain g l) = 64 * g + (16 * l + 2) ∧ wid (fineChain g l) = 5 := by
  interval_cases g <;> interval_cases l <;> decide

theorem fieldPos_coarse (g l : ℕ) (hg : g < 3) (hl : l < 4) :
    fieldPos (coarseChain g l) = 64 * g + (16 * l + 10) ∧ wid (coarseChain g l) = 4 := by
  interval_cases g <;> interval_cases l <;> decide

/-- The fine field of lane `l` of word `g` is the digit of chain `fineChain g l`. -/
theorem fine_word (answer : BitVec hashBits) (g l : ℕ) (hg : g < 4) (hl : l < 4) :
    fineFld (wordOf answer g).toNat l = fieldDigit answer (fineChain g l) := by
  obtain ⟨hp, hw⟩ := fieldPos_fine g l hg hl
  unfold fineFld fieldDigit
  rw [fld_extract _ _ _ _ (by omega), hp, hw]

theorem coarse_word (answer : BitVec hashBits) (g l : ℕ) (hg : g < 3) (hl : l < 4) :
    coarseFld (wordOf answer g).toNat l = fieldDigit answer (coarseChain g l) := by
  obtain ⟨hp, hw⟩ := fieldPos_coarse g l hg hl
  unfold coarseFld fieldDigit
  rw [fld_extract _ _ _ _ (by omega), hp, hw]

/-- The words of the answer are in the index registers. -/
def WordsLoaded (a : MachineState) (answer : BitVec hashBits) : Prop :=
  ∀ g, g < 4 → a.getReg (wordReg g) = wordOf answer g

/-- The lane totals sum to the digit sum of the answer. -/
theorem field_sum (answer : BitVec hashBits) :
    ∑ l ∈ Finset.range 4, (fineTotal (fun g => (wordOf answer g).toNat) l +
        coarseTotal (fun g => (wordOf answer g).toNat) l) =
      ∑ k ∈ Finset.range 28, fieldDigit answer k := by
  have f := fine_word answer
  have c := coarse_word answer
  simp only [fineTotal, coarseTotal, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [f 0 0 (by norm_num) (by norm_num),
    f 0 1 (by norm_num) (by norm_num),
    f 0 2 (by norm_num) (by norm_num),
    f 0 3 (by norm_num) (by norm_num),
    f 1 0 (by norm_num) (by norm_num),
    f 1 1 (by norm_num) (by norm_num),
    f 1 2 (by norm_num) (by norm_num),
    f 1 3 (by norm_num) (by norm_num),
    f 2 0 (by norm_num) (by norm_num),
    f 2 1 (by norm_num) (by norm_num),
    f 2 2 (by norm_num) (by norm_num),
    f 2 3 (by norm_num) (by norm_num),
    f 3 0 (by norm_num) (by norm_num),
    f 3 1 (by norm_num) (by norm_num),
    f 3 2 (by norm_num) (by norm_num),
    f 3 3 (by norm_num) (by norm_num),
    c 0 0 (by norm_num) (by norm_num),
    c 0 1 (by norm_num) (by norm_num),
    c 0 2 (by norm_num) (by norm_num),
    c 0 3 (by norm_num) (by norm_num),
    c 1 0 (by norm_num) (by norm_num),
    c 1 1 (by norm_num) (by norm_num),
    c 1 2 (by norm_num) (by norm_num),
    c 1 3 (by norm_num) (by norm_num),
    c 2 0 (by norm_num) (by norm_num),
    c 2 1 (by norm_num) (by norm_num),
    c 2 2 (by norm_num) (by norm_num),
    c 2 3 (by norm_num) (by norm_num)]
  simp only [fineChain, coarseChain]
  norm_num
  ring

/-- The top lane of the folded lane sum is four times the digit sum. -/
theorem top_fold_answer (a : MachineState) (hm : MasksLoaded a) (answer : BitVec hashBits)
    (hw : WordsLoaded a answer) (hfm : a.getReg .x1 = W (broadcast foldMask)) :
    ((foldValue (laneSum a 4) (a.getReg .x1)).toNat * broadcast 1) % 2 ^ 64 / 2 ^ 48 =
      4 * ∑ k ∈ Finset.range 28, fieldDigit answer k := by
  rw [fold_laneSum a hm hfm]
  have hf : ∀ l, fineTotal (wordsOf a) l = fineTotal (fun g => (wordOf answer g).toNat) l := by
    intro l
    unfold fineTotal
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [wordsOf, hw g (Finset.mem_range.mp hg)]
  have hc : ∀ l, coarseTotal (wordsOf a) l = coarseTotal (fun g => (wordOf answer g).toNat) l := by
    intro l
    unfold coarseTotal
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [wordsOf, hw g (by have := Finset.mem_range.mp hg; omega)]
  have bound : ∀ l, 4 * (fineTotal (wordsOf a) l + coarseTotal (wordsOf a) l) ≤ 1000 := by
    intro l
    have := fineTotal_lt (wordsOf a) l
    have := coarseTotal_lt (wordsOf a) l
    omega
  rw [topLane _ _ _ _ (bound 0) (bound 1) (bound 2) (bound 3), ← field_sum answer]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf, hc]
  ring

/-- The accepted indices are those with field sum `215`. -/
theorem accepted_iff (answer : BitVec hashBits) :
    Accepted (pack answer) ↔ ∑ k ∈ Finset.range 28, fieldDigit answer k = 215 := by
  unfold Accepted
  rw [Finset.sum_congr rfl fun k hk => digit_pack answer (Finset.mem_range.mp hk)]
  rfl

/-! ## The stored lanes -/

theorem lane_extract (x0 x1 x2 x3 l : ℕ) (h0 : x0 < 2 ^ 16) (h1 : x1 < 2 ^ 16) (h2 : x2 < 2 ^ 16)
    (h3 : x3 < 2 ^ 16) (hl : l < 4) :
    (x0 + 2 ^ 16 * x1 + 2 ^ 32 * x2 + 2 ^ 48 * x3) / 2 ^ (16 * l) % 2 ^ 16 =
      [x0, x1, x2, x3].getD l 0 := by
  interval_cases l <;> simp <;> omega

/-- Lane `l` of `broadcast B - lane word` is `B - (4 · dA + 1024 · dB)`. -/
theorem lane_halfword (B u g l : ℕ) (hB1 : 15484 ≤ B) (hB2 : B < 2 ^ 16) (hl : l < 4) (L : Word)
    (hL : L.toNat = laneNat u g) :
    (W (broadcast B) - L).toNat / 2 ^ (16 * l) % 2 ^ 16 =
      B - (4 * fineFld u l + 1024 * coarseOf g u l) := by
  have n0 := laneEntry_le g u 0
  have n1 := laneEntry_le g u 1
  have n2 := laneEntry_le g u 2
  have n3 := laneEntry_le g u 3
  have hle : L ≤ W (broadcast B) := by
    rw [BitVec.le_def, hL, broadcast_toNat B hB2]
    unfold laneNat broadcast
    omega
  rw [BitVec.toNat_sub_of_le hle, hL, broadcast_toNat B hB2]
  have e : broadcast B - laneNat u g =
      (B - (4 * fineFld u 0 + 1024 * coarseOf g u 0)) +
      2 ^ 16 * (B - (4 * fineFld u 1 + 1024 * coarseOf g u 1)) +
      2 ^ 32 * (B - (4 * fineFld u 2 + 1024 * coarseOf g u 2)) +
      2 ^ 48 * (B - (4 * fineFld u 3 + 1024 * coarseOf g u 3)) := by
    unfold broadcast laneNat; omega
  rw [e, lane_extract _ _ _ _ l (by omega) (by omega) (by omega) (by omega) hl]
  interval_cases l <;> rfl

end OptimalOTS.Riscv2Program
