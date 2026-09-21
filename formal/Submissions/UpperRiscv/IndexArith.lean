import Submissions.UpperRiscv.IndexLanes

/-!
# The arithmetic of the index check

The index answer is held in three words. The sum of the seven lane words has four lanes, each the
sum of seven fields times four; its top lane after the broadcast multiplication is four times the
field sum of the answer (`top_laneSum`), which the sum check compares with `4 · 215`. Each stored
lane holds `jumpBase - 4 · field` (`lane_halfword`).
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64

theorem wid_le (k : ℕ) : wid k ≤ 5 := by unfold wid; split_ifs <;> omega

theorem widthOf_le (g : ℕ) : widthOf g ≤ 5 := by unfold widthOf; split_ifs <;> omega

theorem fld_le (u p b : ℕ) (hb : b ≤ 5) : fld u p b ≤ 31 := by
  have h1 : u / 2 ^ p % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  have h2 : 2 ^ b ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hb
  unfold fld; omega

theorem laneFld_le (u g l : ℕ) : laneFld u g l ≤ 31 := fld_le _ _ _ (widthOf_le _)

theorem laneNat_le (u g : ℕ) : laneNat u g ≤ 124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) := by
  unfold laneNat
  have := laneFld_le u g 0
  have := laneFld_le u g 1
  have := laneFld_le u g 2
  have := laneFld_le u g 3
  omega

/-- The mask registers hold the two masks. -/
def MasksLoaded (a : MachineState) : Prop := ∀ g, g < 7 → a.getReg (maskReg g) = W (maskNat g)

theorem laneOf_toNat (a : MachineState) (hm : MasksLoaded a) (g : ℕ) (hg : g < 7) :
    (laneOf a g).toNat = laneNat (a.getReg (srcReg g)).toNat g := by
  unfold laneOf
  rw [hm g hg]
  exact laneValue_toNat _ _ hg

theorem laneSum_toNat (a : MachineState) (hm : MasksLoaded a) :
    ∀ n, n ≤ 7 → (laneSum a n).toNat =
      ∑ g ∈ Finset.range n, laneNat (a.getReg (srcReg g)).toNat g := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hb : ∀ n, ∑ g ∈ Finset.range n, laneNat (a.getReg (srcReg g)).toNat g ≤
        n * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by
      intro n
      calc ∑ g ∈ Finset.range n, laneNat (a.getReg (srcReg g)).toNat g
          ≤ ∑ _g ∈ Finset.range n, 124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) :=
            Finset.sum_le_sum fun g _ => laneNat_le _ _
        _ = n * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by simp
    rw [laneSum, BitVec.toNat_add, ih (by omega), laneOf_toNat a hm n (by omega),
      Finset.sum_range_succ, Nat.mod_eq_of_lt]
    have h1 := hb n
    have h2 := laneNat_le (a.getReg (srcReg n)).toNat n
    have : n * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) + 124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) <
        2 ^ 64 := by
      have : n * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) ≤
          6 * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    omega

/-- The word values of a state. -/
def wordsOf (a : MachineState) (w : ℕ) : ℕ := (a.getReg (wordReg w)).toNat

/-- Lane `l` of the lane sum, for the word values `u`. -/
def laneTotal (u : ℕ → ℕ) (l : ℕ) : ℕ := ∑ g ∈ Finset.range 7, 4 * laneFld (u (wordIdx g)) g l

theorem laneTotal_le (u : ℕ → ℕ) (l : ℕ) : laneTotal u l ≤ 1000 := by
  unfold laneTotal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have := laneFld_le (u (wordIdx 0)) 0 l
  have := laneFld_le (u (wordIdx 1)) 1 l
  have := laneFld_le (u (wordIdx 2)) 2 l
  have := laneFld_le (u (wordIdx 3)) 3 l
  have := laneFld_le (u (wordIdx 4)) 4 l
  have := laneFld_le (u (wordIdx 5)) 5 l
  have := laneFld_le (u (wordIdx 6)) 6 l
  omega

theorem laneSum_lanes (a : MachineState) :
    ∑ g ∈ Finset.range 7, laneNat (a.getReg (srcReg g)).toNat g =
      laneTotal (wordsOf a) 0 + 2 ^ 16 * laneTotal (wordsOf a) 1 +
      2 ^ 32 * laneTotal (wordsOf a) 2 + 2 ^ 48 * laneTotal (wordsOf a) 3 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, laneNat, laneTotal, wordsOf, srcReg]
  ring

/-- The lane totals sum to four times the sum of all lane fields. -/
theorem laneTotals_sum (u : ℕ → ℕ) :
    laneTotal u 0 + laneTotal u 1 + laneTotal u 2 + laneTotal u 3 =
      4 * ∑ g ∈ Finset.range 7, ∑ l ∈ Finset.range 4, laneFld (u (wordIdx g)) g l := by
  simp only [laneTotal, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The top lane of the lane sum is four times the sum of the lane fields. -/
theorem top_laneSum (a : MachineState) (hm : MasksLoaded a) :
    ((laneSum a 7).toNat * broadcast 1) % 2 ^ 64 / 2 ^ 48 =
      4 * ∑ g ∈ Finset.range 7, ∑ l ∈ Finset.range 4, laneFld (wordsOf a (wordIdx g)) g l := by
  rw [laneSum_toNat a hm 7 le_rfl, laneSum_lanes, topLane _ _ _ _ (laneTotal_le _ _)
    (laneTotal_le _ _) (laneTotal_le _ _) (laneTotal_le _ _), laneTotals_sum]

/-! ## The fields of the answer -/

/-- Word `w` of the index answer. -/
def wordOf (answer : BitVec hashBits) (w : ℕ) : Word := answer.extractLsb' (64 * w) 64

theorem fld_extract (answer : BitVec hashBits) (w p b : ℕ) (hpb : p + b ≤ 64) :
    fld (wordOf answer w).toNat p b = answer.toNat / 2 ^ (64 * w + p) % 2 ^ b := by
  unfold fld wordOf
  rw [show (BitVec.extractLsb' (64 * w) 64 answer).toNat = answer.toNat / 2 ^ (64 * w) % 2 ^ 64 by
      simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow],
    show (2 : ℕ) ^ 64 = 2 ^ p * 2 ^ (64 - p) by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)),
    Nat.div_div_eq_div_mul, ← pow_add]

/-- Digit `k` of the answer is the field of lane `laneIdx k` of lane word `laneOfChain k`. -/
theorem fieldPos_eq (k : ℕ) (hk : k < 28) :
    fieldPos k = 64 * wordIdx (laneOfChain k) + (16 * laneIdx k + 2 + shiftOf (laneOfChain k)) := by
  interval_cases k <;> decide

theorem wid_eq (k : ℕ) (hk : k < 28) : wid k = widthOf (laneOfChain k) := by
  interval_cases k <;> decide

theorem laneOfChain_lt (k : ℕ) (hk : k < 28) : laneOfChain k < 7 := by
  unfold laneOfChain; split_ifs <;> omega

theorem laneIdx_lt (k : ℕ) (hk : k < 28) : laneIdx k < 4 := by
  unfold laneIdx; split_ifs <;> omega

theorem wordIdx_lt (g : ℕ) : wordIdx g < 3 := by
  unfold wordIdx; split_ifs <;> omega

theorem lane_fits (g l : ℕ) (hl : l < 4) : 16 * l + 2 + shiftOf g + widthOf g ≤ 64 := by
  unfold shiftOf widthOf; split_ifs <;> omega

/-- The lane fields of the words are the digits of the answer. -/
theorem laneFld_word (answer : BitVec hashBits) (k : ℕ) (hk : k < 28) :
    laneFld (wordOf answer (wordIdx (laneOfChain k))).toNat (laneOfChain k) (laneIdx k) =
      fieldDigit answer k := by
  unfold laneFld fieldDigit
  rw [fld_extract _ _ _ _ (lane_fits _ _ (laneIdx_lt k hk)), fieldPos_eq k hk, wid_eq k hk]

/-- The lane fields sum to the digit sum of the answer. -/
theorem field_sum (answer : BitVec hashBits) :
    ∑ g ∈ Finset.range 7, ∑ l ∈ Finset.range 4, laneFld (wordOf answer (wordIdx g)).toNat g l =
      ∑ k ∈ Finset.range 28, fieldDigit answer k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [← laneFld_word answer 0 (by norm_num), ← laneFld_word answer 1 (by norm_num),
    ← laneFld_word answer 2 (by norm_num), ← laneFld_word answer 3 (by norm_num),
    ← laneFld_word answer 4 (by norm_num), ← laneFld_word answer 5 (by norm_num),
    ← laneFld_word answer 6 (by norm_num), ← laneFld_word answer 7 (by norm_num),
    ← laneFld_word answer 8 (by norm_num), ← laneFld_word answer 9 (by norm_num),
    ← laneFld_word answer 10 (by norm_num), ← laneFld_word answer 11 (by norm_num),
    ← laneFld_word answer 12 (by norm_num), ← laneFld_word answer 13 (by norm_num),
    ← laneFld_word answer 14 (by norm_num), ← laneFld_word answer 15 (by norm_num),
    ← laneFld_word answer 16 (by norm_num), ← laneFld_word answer 17 (by norm_num),
    ← laneFld_word answer 18 (by norm_num), ← laneFld_word answer 19 (by norm_num),
    ← laneFld_word answer 20 (by norm_num), ← laneFld_word answer 21 (by norm_num),
    ← laneFld_word answer 22 (by norm_num), ← laneFld_word answer 23 (by norm_num),
    ← laneFld_word answer 24 (by norm_num), ← laneFld_word answer 25 (by norm_num),
    ← laneFld_word answer 26 (by norm_num), ← laneFld_word answer 27 (by norm_num)]
  simp only [laneOfChain, laneIdx, wordIdx, Nat.reduceLT, Nat.reduceDiv, Nat.reduceMod,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte]
  ring

/-- The words of the answer are in the index registers. -/
def WordsLoaded (a : MachineState) (answer : BitVec hashBits) : Prop :=
  ∀ w, w < 3 → a.getReg (wordReg w) = wordOf answer w

theorem top_laneSum_answer (a : MachineState) (hm : MasksLoaded a) (answer : BitVec hashBits)
    (hw : WordsLoaded a answer) :
    ((laneSum a 7).toNat * broadcast 1) % 2 ^ 64 / 2 ^ 48 =
      4 * ∑ k ∈ Finset.range 28, fieldDigit answer k := by
  rw [top_laneSum a hm, ← field_sum]
  refine congrArg (4 * ·) (Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun l _ => ?_)
  rw [wordsOf, hw _ (wordIdx_lt g)]

/-- The accepted indices are those with field sum `215`. -/
theorem accepted_iff (answer : BitVec hashBits) :
    Accepted (pack answer) ↔ ∑ k ∈ Finset.range 28, fieldDigit answer k = 215 := by
  unfold Accepted
  rw [Finset.sum_congr rfl fun k hk => digit_pack answer (Finset.mem_range.mp hk)]
  rfl

/-! ## The stored lanes -/

theorem broadcast_toNat (B : ℕ) (hB : B < 2 ^ 16) :
    (W (broadcast B)).toNat = broadcast B := by
  apply W_toNat
  unfold broadcast
  omega

theorem lane_extract (x0 x1 x2 x3 l : ℕ) (h0 : x0 < 2 ^ 16) (h1 : x1 < 2 ^ 16) (h2 : x2 < 2 ^ 16)
    (h3 : x3 < 2 ^ 16) (hl : l < 4) :
    (x0 + 2 ^ 16 * x1 + 2 ^ 32 * x2 + 2 ^ 48 * x3) / 2 ^ (16 * l) % 2 ^ 16 =
      [x0, x1, x2, x3].getD l 0 := by
  interval_cases l <;> simp <;> omega

/-- Lane `l` of `broadcast B - lane word` is `B - 4 · field`. -/
theorem lane_halfword (B u g l : ℕ) (hB1 : 124 ≤ B) (hB2 : B < 2 ^ 16) (hl : l < 4) (L : Word)
    (hL : L.toNat = laneNat u g) :
    (W (broadcast B) - L).toNat / 2 ^ (16 * l) % 2 ^ 16 = B - 4 * laneFld u g l := by
  have n0 := laneFld_le u g 0
  have n1 := laneFld_le u g 1
  have n2 := laneFld_le u g 2
  have n3 := laneFld_le u g 3
  have hle : L ≤ W (broadcast B) := by
    rw [BitVec.le_def, hL, broadcast_toNat B hB2]
    unfold laneNat broadcast
    omega
  rw [BitVec.toNat_sub_of_le hle, hL, broadcast_toNat B hB2]
  have e : broadcast B - laneNat u g =
      (B - 4 * laneFld u g 0) + 2 ^ 16 * (B - 4 * laneFld u g 1) +
      2 ^ 32 * (B - 4 * laneFld u g 2) + 2 ^ 48 * (B - 4 * laneFld u g 3) := by
    unfold broadcast laneNat; omega
  rw [e, lane_extract _ _ _ _ l (by omega) (by omega) (by omega) (by omega) hl]
  interval_cases l <;> rfl

end OptimalOTS.Riscv2Program
