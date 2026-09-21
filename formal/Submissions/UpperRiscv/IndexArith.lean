import Submissions.UpperRiscv.IndexLanes

/-!
# The arithmetic of the index check

The index answer is held in four words. The sum of the seven lane words has four lanes, each the
sum of the fields of its slots times four; its top lane after the broadcast multiplication is four
times the field sum of the answer (`top_laneSum`), which the sum check compares with `4 · 215`.
The eighth lane word `(3, 1)` would carry only the width-zero slots `25, 27, 29, 31`, so it is not
emitted. Each stored lane holds `jumpBase - 4 · field` (`lane_halfword`).
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64

/-- A field of a word: bits `p …` of width `b`. -/
def fld (u p b : ℕ) : ℕ := u / 2 ^ p % 2 ^ b

theorem wid_le (k : ℕ) : wid k ≤ 5 := by unfold wid; split_ifs <;> omega

/-- The four slots of the omitted lane word `(3, 1)`. -/
theorem wid_25 : wid 25 = 0 := by decide

theorem wid_27 : wid 27 = 0 := by decide

theorem wid_29 : wid 29 = 0 := by decide

theorem wid_31 : wid 31 = 0 := by decide

theorem fld_dead (u p : ℕ) : fld u p 0 = 0 := by simp [fld]

theorem fld_le (u p b : ℕ) (hb : b ≤ 5) : fld u p b ≤ 31 := by
  have h1 : u / 2 ^ p % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  have h2 : 2 ^ b ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hb
  unfold fld; omega

theorem laneNat_eq (u w i : ℕ) :
    laneNat u w i = 4 * fld u (8 * i) (wid (8 * w + i)) +
      2 ^ 16 * (4 * fld u (16 + 8 * i) (wid (8 * w + 2 + i))) +
      2 ^ 32 * (4 * fld u (32 + 8 * i) (wid (8 * w + 4 + i))) +
      2 ^ 48 * (4 * fld u (48 + 8 * i) (wid (8 * w + 6 + i))) := rfl

theorem laneNat_le (u w i : ℕ) : laneNat u w i ≤ 124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) := by
  rw [laneNat_eq]
  have := fld_le u (8 * i) _ (wid_le (8 * w + i))
  have := fld_le u (16 + 8 * i) _ (wid_le (8 * w + 2 + i))
  have := fld_le u (32 + 8 * i) _ (wid_le (8 * w + 4 + i))
  have := fld_le u (48 + 8 * i) _ (wid_le (8 * w + 6 + i))
  omega

/-- The mask registers hold the two masks. -/
def MasksLoaded (a : MachineState) : Prop := ∀ w, w < 4 → a.getReg (maskReg w) = W (maskNat w)

theorem laneOf_toNat (a : MachineState) (hm : MasksLoaded a) (j : ℕ) (hj : j < 7) :
    (laneOf a j).toNat = laneNat (a.getReg (srcReg (j / 2))).toNat (j / 2) (j % 2) := by
  unfold laneOf
  rw [hm (j / 2) (by omega)]
  exact laneValue_toNat _ _ _ (by omega) (Nat.mod_lt _ (by norm_num)) (by omega)

theorem laneSum_toNat (a : MachineState) (hm : MasksLoaded a) :
    ∀ n, n ≤ 7 → (laneSum a n).toNat =
      ∑ j ∈ Finset.range n, laneNat (a.getReg (srcReg (j / 2))).toNat (j / 2) (j % 2) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hb : ∀ n, n ≤ 8 → ∑ j ∈ Finset.range n, laneNat (a.getReg (srcReg (j / 2))).toNat (j / 2) (j % 2) ≤
        n * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by
      intro n _
      calc ∑ j ∈ Finset.range n, laneNat (a.getReg (srcReg (j / 2))).toNat (j / 2) (j % 2)
          ≤ ∑ _j ∈ Finset.range n, 124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) :=
            Finset.sum_le_sum fun j _ => laneNat_le _ _ _
        _ = n * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by simp
    rw [laneSum, BitVec.toNat_add, ih (by omega), laneOf_toNat a hm n (by omega),
      Finset.sum_range_succ, Nat.mod_eq_of_lt]
    have h1 := hb n (by omega)
    have h2 := laneNat_le (a.getReg (srcReg (n / 2))).toNat (n / 2) (n % 2)
    have : n * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) + 124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) <
        2 ^ 64 := by
      have : n * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) ≤ 7 * (124 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    omega

/-- Lane `l` of the lane sum, for the word values `u`. -/
def laneTotal (u : ℕ → ℕ) (l : ℕ) : ℕ :=
  ∑ w ∈ Finset.range 4, ∑ i ∈ Finset.range 2, 4 * fld (u w) (16 * l + 8 * i) (wid (8 * w + 2 * l + i))

theorem laneTotal_le (u : ℕ → ℕ) (l : ℕ) : laneTotal u l ≤ 1000 := by
  unfold laneTotal
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have := fld_le (u 0) (16 * l + 8 * 0) (wid (8 * 0 + 2 * l + 0)) (wid_le _)
  have := fld_le (u 0) (16 * l + 8 * 1) (wid (8 * 0 + 2 * l + 1)) (wid_le _)
  have := fld_le (u 1) (16 * l + 8 * 0) (wid (8 * 1 + 2 * l + 0)) (wid_le _)
  have := fld_le (u 1) (16 * l + 8 * 1) (wid (8 * 1 + 2 * l + 1)) (wid_le _)
  have := fld_le (u 2) (16 * l + 8 * 0) (wid (8 * 2 + 2 * l + 0)) (wid_le _)
  have := fld_le (u 2) (16 * l + 8 * 1) (wid (8 * 2 + 2 * l + 1)) (wid_le _)
  have := fld_le (u 3) (16 * l + 8 * 0) (wid (8 * 3 + 2 * l + 0)) (wid_le _)
  have := fld_le (u 3) (16 * l + 8 * 1) (wid (8 * 3 + 2 * l + 1)) (wid_le _)
  omega

/-- The word values of a state. -/
def wordsOf (a : MachineState) (w : ℕ) : ℕ := (a.getReg (srcReg w)).toNat

/-- The seven emitted lane words already carry every nonzero slot: the missing word `(3, 1)`
contributes only width-zero fields. -/
theorem laneSum_lanes (a : MachineState) :
    ∑ j ∈ Finset.range 7, laneNat (a.getReg (srcReg (j / 2))).toNat (j / 2) (j % 2) =
      laneTotal (wordsOf a) 0 + 2 ^ 16 * laneTotal (wordsOf a) 1 +
      2 ^ 32 * laneTotal (wordsOf a) 2 + 2 ^ 48 * laneTotal (wordsOf a) 3 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, laneNat_eq, laneTotal, wordsOf]
  -- `simp only` runs without the default simprocs, so the slot indices of the expanded sums are
  -- still `8 * 3 + 2 * 0 + 1` and the like, and the width lemmas of the four dead slots cannot
  -- match them. `norm_num` does run the simprocs and iterates, so handing it those lemmas
  -- reduces the indices and rewrites the dead fields in one pass.
  norm_num [wid_25, wid_27, wid_29, wid_31, fld_dead]
  all_goals ring

/-- The field sum of the answer, over all 32 bytes (the last four have width zero). -/
theorem laneTotals_sum (u : ℕ → ℕ) :
    laneTotal u 0 + laneTotal u 1 + laneTotal u 2 + laneTotal u 3 =
      4 * ∑ k ∈ Finset.range 32, fld (u (k / 8)) (8 * (k % 8)) (wid k) := by
  simp only [laneTotal, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- The top lane of the lane sum is four times the field sum. -/
theorem top_laneSum (a : MachineState) (hm : MasksLoaded a) :
    ((laneSum a 7).toNat * broadcast 1) % 2 ^ 64 / 2 ^ 48 =
      4 * ∑ k ∈ Finset.range 32, fld (wordsOf a (k / 8)) (8 * (k % 8)) (wid k) := by
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

/-- The fields of the words are the byte fields of the answer. -/
theorem fld_word (answer : BitVec hashBits) (k : ℕ) (hk : k < 32) :
    fld (wordOf answer (k / 8)).toNat (8 * (k % 8)) (wid k) = byteDigit answer k := by
  rw [fld_extract _ _ _ _ (by have := wid_le k; omega),
    show 64 * (k / 8) + 8 * (k % 8) = 8 * k by omega]
  rfl

/-- The words of the answer are in the index registers. -/
def WordsLoaded (a : MachineState) (answer : BitVec hashBits) : Prop :=
  ∀ w, w < 4 → a.getReg (srcReg w) = wordOf answer w

theorem top_laneSum_answer (a : MachineState) (hm : MasksLoaded a) (answer : BitVec hashBits)
    (hw : WordsLoaded a answer) :
    ((laneSum a 7).toNat * broadcast 1) % 2 ^ 64 / 2 ^ 48 =
      4 * ∑ k ∈ Finset.range 32, byteDigit answer k := by
  rw [top_laneSum a hm]
  refine congrArg (4 * ·) (Finset.sum_congr rfl fun k hk => ?_)
  rw [Finset.mem_range] at hk
  rw [wordsOf, hw _ (by omega), fld_word answer k hk]

/-- The accepted indices are those with field sum `215`. -/
theorem accepted_iff (answer : BitVec hashBits) :
    Accepted (pack answer) ↔ ∑ k ∈ Finset.range 32, byteDigit answer k = 215 := by
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

/-- Lane `l` of lane word `(w, i)`: field `8 w + 2 l + i`. -/
def laneFld (u w i l : ℕ) : ℕ := fld u (16 * l + 8 * i) (wid (8 * w + 2 * l + i))

theorem laneNat_eq' (u w i : ℕ) :
    laneNat u w i = 4 * laneFld u w i 0 + 2 ^ 16 * (4 * laneFld u w i 1) +
      2 ^ 32 * (4 * laneFld u w i 2) + 2 ^ 48 * (4 * laneFld u w i 3) := by
  rw [laneNat_eq]
  simp only [laneFld, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one]

theorem laneFld_le (u w i l : ℕ) : laneFld u w i l ≤ 31 := fld_le _ _ _ (wid_le _)

/-- Lane `l` of `broadcast B - lane word` is `B - 4 · field`. -/
theorem lane_halfword (B u w i l : ℕ) (hB1 : 124 ≤ B) (hB2 : B < 2 ^ 16) (hl : l < 4) (L : Word)
    (hL : L.toNat = laneNat u w i) :
    (W (broadcast B) - L).toNat / 2 ^ (16 * l) % 2 ^ 16 = B - 4 * laneFld u w i l := by
  have n0 := laneFld_le u w i 0
  have n1 := laneFld_le u w i 1
  have n2 := laneFld_le u w i 2
  have n3 := laneFld_le u w i 3
  have hle : L ≤ W (broadcast B) := by
    rw [BitVec.le_def, hL, broadcast_toNat B hB2, laneNat_eq']
    unfold broadcast
    omega
  rw [BitVec.toNat_sub_of_le hle, hL, broadcast_toNat B hB2, laneNat_eq']
  have e : broadcast B - (4 * laneFld u w i 0 + 2 ^ 16 * (4 * laneFld u w i 1) +
      2 ^ 32 * (4 * laneFld u w i 2) + 2 ^ 48 * (4 * laneFld u w i 3)) =
      (B - 4 * laneFld u w i 0) + 2 ^ 16 * (B - 4 * laneFld u w i 1) +
      2 ^ 32 * (B - 4 * laneFld u w i 2) + 2 ^ 48 * (B - 4 * laneFld u w i 3) := by
    unfold broadcast; omega
  rw [e, lane_extract _ _ _ _ l (by omega) (by omega) (by omega) (by omega) hl]
  interval_cases l <;> rfl

end OptimalOTS.Riscv2Program
