import Submissions.UpperRiscv.IndexLanes

/-!
# The arithmetic of the index check

The index is the low 128 bits of the answer, held in two words. The sum of the eight lane words
has four lanes, each the sum of eight nibbles times eight; its top lane after the broadcast
multiplication is eight times the nibble sum of the index (`sumCheck_iff`). Each stored lane
holds `jumpBase - 8 · nibble` (`lane_halfword`).
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64

theorem nibble_le15 (u m : ℕ) : nibble u m ≤ 15 := Nat.le_of_lt_succ (nibble_lt u m)

theorem laneNat_le (u i : ℕ) : laneNat u i ≤ 120 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) := by
  unfold laneNat
  have := nibble_le15 u i
  have := nibble_le15 u (4 + i)
  have := nibble_le15 u (8 + i)
  have := nibble_le15 u (12 + i)
  omega

theorem laneOf_toNat (a : MachineState) (j : ℕ) :
    (laneOf a j).toNat = laneNat (a.getReg (wordReg (j / 4))).toNat (j % 4) :=
  laneValue_toNat _ _ (Nat.mod_lt _ (by norm_num))

theorem laneSum_toNat (a : MachineState) :
    ∀ n, n ≤ 8 → (laneSum a n).toNat =
      ∑ j ∈ Finset.range n, laneNat (a.getReg (wordReg (j / 4))).toNat (j % 4) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hb : ∀ n, n ≤ 8 → ∑ j ∈ Finset.range n, laneNat (a.getReg (wordReg (j / 4))).toNat (j % 4) ≤
        n * (120 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by
      intro n _
      calc ∑ j ∈ Finset.range n, laneNat (a.getReg (wordReg (j / 4))).toNat (j % 4)
          ≤ ∑ _j ∈ Finset.range n, 120 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) :=
            Finset.sum_le_sum fun j _ => laneNat_le _ _
        _ = n * (120 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) := by simp
    rw [laneSum, BitVec.toNat_add, ih (by omega), laneOf_toNat, Finset.sum_range_succ,
      Nat.mod_eq_of_lt]
    have h1 := hb n (by omega)
    have h2 := laneNat_le (a.getReg (wordReg (n / 4))).toNat (n % 4)
    have : n * (120 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) + 120 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48) <
        2 ^ 64 := by
      have : n * (120 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) ≤ 7 * (120 * (1 + 2 ^ 16 + 2 ^ 32 + 2 ^ 48)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    omega

/-- The nibble sum of two words. -/
def wordNibbleSum (u0 u1 : ℕ) : ℕ :=
  (∑ m ∈ Finset.range 16, nibble u0 m) + ∑ m ∈ Finset.range 16, nibble u1 m

/-- Lane `l` of the lane sum. -/
def laneTotal (u0 u1 l : ℕ) : ℕ :=
  8 * nibble u0 (4 * l) + 8 * nibble u0 (4 * l + 1) + 8 * nibble u0 (4 * l + 2) +
    8 * nibble u0 (4 * l + 3) + 8 * nibble u1 (4 * l) + 8 * nibble u1 (4 * l + 1) +
    8 * nibble u1 (4 * l + 2) + 8 * nibble u1 (4 * l + 3)

theorem laneTotal_le (u0 u1 l : ℕ) : laneTotal u0 u1 l ≤ 960 := by
  unfold laneTotal
  have := nibble_le15 u0 (4 * l); have := nibble_le15 u0 (4 * l + 1)
  have := nibble_le15 u0 (4 * l + 2); have := nibble_le15 u0 (4 * l + 3)
  have := nibble_le15 u1 (4 * l); have := nibble_le15 u1 (4 * l + 1)
  have := nibble_le15 u1 (4 * l + 2); have := nibble_le15 u1 (4 * l + 3)
  omega

theorem laneSum_lanes (a : MachineState) :
    ∑ j ∈ Finset.range 8, laneNat (a.getReg (wordReg (j / 4))).toNat (j % 4) =
      laneTotal (a.getReg .x20).toNat (a.getReg .x21).toNat 0 +
      2 ^ 16 * laneTotal (a.getReg .x20).toNat (a.getReg .x21).toNat 1 +
      2 ^ 32 * laneTotal (a.getReg .x20).toNat (a.getReg .x21).toNat 2 +
      2 ^ 48 * laneTotal (a.getReg .x20).toNat (a.getReg .x21).toNat 3 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, laneNat, laneTotal, wordReg]
  norm_num
  ring

theorem laneTotals_sum (u0 u1 : ℕ) :
    laneTotal u0 u1 0 + laneTotal u0 u1 1 + laneTotal u0 u1 2 + laneTotal u0 u1 3 =
      8 * wordNibbleSum u0 u1 := by
  simp only [laneTotal, wordNibbleSum, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- The top lane of the lane sum is eight times the nibble sum. -/
theorem top_laneSum (a : MachineState) :
    ((laneSum a 8).toNat * broadcast 1) % 2 ^ 64 / 2 ^ 48 =
      8 * wordNibbleSum (a.getReg .x20).toNat (a.getReg .x21).toNat := by
  rw [laneSum_toNat a 8 le_rfl, laneSum_lanes, topLane _ _ _ _ (laneTotal_le _ _ _)
    (laneTotal_le _ _ _) (laneTotal_le _ _ _) (laneTotal_le _ _ _), laneTotals_sum]

/-! ## The index and its words -/

def joinWords (lo hi : Word) : BitVec 128 := hi ++ lo

theorem joinWords_toNat (lo hi : Word) :
    (joinWords lo hi).toNat = hi.toNat * 2 ^ 64 + lo.toNat := by
  rw [joinWords, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

theorem answer_low128 (answer : BitVec hashBits) :
    joinWords (answer.extractLsb' 0 64) (answer.extractLsb' 64 64) = answer.setWidth 128 := by
  rw [joinWords, BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  ext i hi
  simp

theorem nibble_joinWords_lo (lo hi : Word) (m : ℕ) (hm : m < 16) :
    nibble (joinWords lo hi).toNat m = nibble lo.toNat m := by
  rw [joinWords_toNat, nibble, nibble]
  have split : (16 : ℕ) ^ m * (16 * 16 ^ (15 - m)) = 2 ^ 64 := by
    rw [← pow_succ', ← pow_add, show m + (15 - m + 1) = 16 by omega]
    norm_num
  have e : hi.toNat * 2 ^ 64 + lo.toNat =
      lo.toNat + 16 ^ m * (16 * (hi.toNat * 16 ^ (15 - m))) := by
    rw [← split]
    ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem nibble_joinWords_hi (lo hi : Word) (m : ℕ) (hm : 16 ≤ m) :
    nibble (joinWords lo hi).toNat m = nibble hi.toNat (m - 16) := by
  rw [joinWords_toNat, nibble, nibble]
  have e : (16 : ℕ) ^ m = 2 ^ 64 * 16 ^ (m - 16) := by
    rw [show (2 : ℕ) ^ 64 = 16 ^ 16 by norm_num, ← pow_add, Nat.add_sub_cancel' hm]
  rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_comm hi.toNat, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt lo.isLt, Nat.add_zero]

/-- The index's nibble sum is the nibble sum of its two words. -/
theorem index_nibbleSum (answer : BitVec hashBits) :
    ∑ k ∈ Finset.range 32, nibble (answer.setWidth 128).toNat k =
      wordNibbleSum (answer.extractLsb' 0 64).toNat (answer.extractLsb' 64 64).toNat := by
  rw [← answer_low128]
  unfold wordNibbleSum
  rw [show (32 : ℕ) = 16 + 16 from rfl, Finset.sum_range_add]
  have h1 := Finset.sum_congr (s₁ := Finset.range 16) rfl fun k hk =>
    nibble_joinWords_lo (answer.extractLsb' 0 64) (answer.extractLsb' 64 64) k
      (Finset.mem_range.mp hk)
  have h2 : ∑ k ∈ Finset.range 16,
      nibble (joinWords (answer.extractLsb' 0 64) (answer.extractLsb' 64 64)).toNat (16 + k) =
      ∑ k ∈ Finset.range 16, nibble (answer.extractLsb' 64 64).toNat k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [nibble_joinWords_hi _ _ _ (by omega), Nat.add_sub_cancel_left]
  rw [h1, h2]

theorem accepted_iff_wordSum (answer : BitVec hashBits) :
    Accepted (answer.setWidth 128).toNat ↔
      wordNibbleSum (answer.extractLsb' 0 64).toNat (answer.extractLsb' 64 64).toNat = 160 := by
  unfold Accepted
  rw [index_nibbleSum]
  rfl

theorem index_nibble (answer : BitVec hashBits) (k : ℕ) (hk : k < 32) :
    nibble (answer.setWidth 128).toNat k =
      nibble ((if k / 16 = 0 then answer.extractLsb' 0 64 else answer.extractLsb' 64 64).toNat)
        (k % 16) := by
  rw [← answer_low128]
  by_cases h : k < 16
  · rw [if_pos (by omega), nibble_joinWords_lo _ _ _ h, Nat.mod_eq_of_lt h]
  · rw [if_neg (by omega), nibble_joinWords_hi _ _ _ (by omega)]
    congr 1
    omega

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

/-- Lane `l` of `broadcast B - lane word` is `B - 8 · nibble`. -/
theorem lane_halfword (B u i l : ℕ) (hB1 : 120 ≤ B) (hB2 : B < 2 ^ 16) (hl : l < 4) (L : Word)
    (hL : L.toNat = laneNat u i) :
    (W (broadcast B) - L).toNat / 2 ^ (16 * l) % 2 ^ 16 = B - 8 * nibble u (4 * l + i) := by
  have n0 := nibble_le15 u i
  have n1 := nibble_le15 u (4 + i)
  have n2 := nibble_le15 u (8 + i)
  have n3 := nibble_le15 u (12 + i)
  have hle : L ≤ W (broadcast B) := by
    rw [BitVec.le_def, hL, broadcast_toNat B hB2]
    unfold laneNat broadcast
    omega
  rw [BitVec.toNat_sub_of_le hle, hL, broadcast_toNat B hB2]
  have e : broadcast B - laneNat u i = (B - 8 * nibble u i) + 2 ^ 16 * (B - 8 * nibble u (4 + i)) +
      2 ^ 32 * (B - 8 * nibble u (8 + i)) + 2 ^ 48 * (B - 8 * nibble u (12 + i)) := by
    unfold laneNat broadcast; omega
  rw [e, lane_extract _ _ _ _ l (by omega) (by omega) (by omega) (by omega) hl]
  interval_cases l <;> simp

end OptimalOTS.RiscvUpperProgram
