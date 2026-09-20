import Submissions.UpperRiscv.Program
import Submissions.UpperRiscv.Valid

/-!
# Lane arithmetic of the index check

A lane word holds four 16-bit lanes. The index phase extracts the byte fields of the index answer
into lanes with one shift and one mask (`laneValue_toNat`): the mask keeps `4 · field`, five bits
wide for the first sixteen fields, four for the next twelve, none for the last four bytes. Eight
lane words are summed without carries, and the sum of the four lanes of the total is read from
the top lane of a product (`topLane`). Everything reduces to natural number arithmetic through
`Nat.and_mod_two_pow` and `Nat.and_div_two_pow`.
-/

namespace OptimalOTS.Riscv2Program

open RiscvZkvm.Rv64

/-! ## Masks -/

theorem and_split (x a b : ℕ) (ha : a < 2 ^ 16) :
    x &&& (a + 2 ^ 16 * b) = (x % 2 ^ 16 &&& a) + 2 ^ 16 * (x / 2 ^ 16 &&& b) := by
  rw [← Nat.mod_add_div (x &&& (a + 2 ^ 16 * b)) (2 ^ 16), Nat.and_mod_two_pow,
    Nat.and_div_two_pow]
  have e1 : (a + 2 ^ 16 * b) % 2 ^ 16 = a := by omega
  have e2 : (a + 2 ^ 16 * b) / 2 ^ 16 = b := by omega
  rw [e1, e2]

/-- A mask of `b` bits shifted up by two keeps `4 · (y / 4 % 2 ^ b)`. -/
theorem and_field (y b : ℕ) : y &&& (4 * (2 ^ b - 1)) = 4 * (y / 4 % 2 ^ b) := by
  rw [← Nat.mod_add_div (y &&& (4 * (2 ^ b - 1))) (2 ^ 2), Nat.and_mod_two_pow,
    Nat.and_div_two_pow]
  have e1 : (4 * (2 ^ b - 1)) % 2 ^ 2 = 0 := by omega
  have e2 : (4 * (2 ^ b - 1)) / 2 ^ 2 = 2 ^ b - 1 := by omega
  rw [e1, e2, Nat.and_zero, Nat.and_two_pow_sub_one_eq_mod]
  norm_num

/-- The mask `0x007C007C007C007C` keeps bits `2 … 6` of every lane. -/
theorem and_mask7C (x : ℕ) :
    x &&& broadcast 0x7C =
      4 * (x / 4 % 32) + 2 ^ 16 * (4 * (x / 2 ^ 18 % 32)) +
      2 ^ 32 * (4 * (x / 2 ^ 34 % 32)) + 2 ^ 48 * (4 * (x / 2 ^ 50 % 32)) := by
  have hb : broadcast 0x7C = 4 * (2 ^ 5 - 1) + 2 ^ 16 * (4 * (2 ^ 5 - 1) + 2 ^ 16 *
      (4 * (2 ^ 5 - 1) + 2 ^ 16 * (4 * (2 ^ 5 - 1)))) := by
    norm_num [broadcast]
  rw [hb, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num), and_field, and_field, and_field, and_field]
  omega

/-- The mask `0x003C003C003C003C` keeps bits `2 … 5` of every lane. -/
theorem and_mask3C (x : ℕ) :
    x &&& broadcast 0x3C =
      4 * (x / 4 % 16) + 2 ^ 16 * (4 * (x / 2 ^ 18 % 16)) +
      2 ^ 32 * (4 * (x / 2 ^ 34 % 16)) + 2 ^ 48 * (4 * (x / 2 ^ 50 % 16)) := by
  have hb : broadcast 0x3C = 4 * (2 ^ 4 - 1) + 2 ^ 16 * (4 * (2 ^ 4 - 1) + 2 ^ 16 *
      (4 * (2 ^ 4 - 1) + 2 ^ 16 * (4 * (2 ^ 4 - 1)))) := by
    norm_num [broadcast]
  rw [hb, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num), and_field, and_field, and_field, and_field]
  omega

/-- The mask `0x003C003C` keeps bits `2 … 5` of the two low lanes. -/
theorem and_mask3C2 (x : ℕ) :
    x &&& 0x003C003C = 4 * (x / 4 % 16) + 2 ^ 16 * (4 * (x / 2 ^ 18 % 16)) := by
  have hb : (0x003C003C : ℕ) = 4 * (2 ^ 4 - 1) + 2 ^ 16 * (4 * (2 ^ 4 - 1) + 2 ^ 16 *
      (4 * (2 ^ 0 - 1) + 2 ^ 16 * (4 * (2 ^ 0 - 1)))) := by
    norm_num
  rw [hb, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num), and_field, and_field, and_field, and_field]
  omega

/-! ## Fields of a word -/

/-- The mask register of index word `w`. -/
def maskNat (w : ℕ) : ℕ := if w < 2 then broadcast 0x7C else if w = 2 then broadcast 0x3C else 0x003C003C

/-- The field width of lane `l` of lane word `(w, i)`: the width of field `8 w + 2 l + i`. -/
theorem wid_lane (w i l : ℕ) (hw : w < 4) (hi : i < 2) (hl : l < 4) :
    wid (8 * w + 2 * l + i) = if w < 2 then 5 else if w = 2 then 4 else if l < 2 then 4 else 0 := by
  unfold wid
  split_ifs <;> omega

/-- Lane word `(w, i)` of the index word `u`: the fields of bytes `2 l + i` of `u`, times four,
in the four lanes. -/
def laneNat (u w i : ℕ) : ℕ :=
  4 * (u / 2 ^ (8 * i) % 2 ^ wid (8 * w + i)) +
  2 ^ 16 * (4 * (u / 2 ^ (16 + 8 * i) % 2 ^ wid (8 * w + 2 + i))) +
  2 ^ 32 * (4 * (u / 2 ^ (32 + 8 * i) % 2 ^ wid (8 * w + 4 + i))) +
  2 ^ 48 * (4 * (u / 2 ^ (48 + 8 * i) % 2 ^ wid (8 * w + 6 + i)))

/-- The machine's lane word. -/
def laneValue (u : Word) (i : ℕ) (mask : Word) : Word :=
  (if i = 0 then u <<< 2 else u >>> 6) &&& mask

theorem maskNat_toNat (w : ℕ) : (BitVec.ofNat 64 (maskNat w)).toNat = maskNat w := by
  rw [BitVec.toNat_ofNat]
  unfold maskNat broadcast
  split_ifs <;> norm_num

theorem laneValue_toNat (u : Word) (w i : ℕ) (hw : w < 4) (hi : i < 2) :
    (laneValue u i (BitVec.ofNat 64 (maskNat w))).toNat = laneNat u.toNat w i := by
  have hu := u.isLt
  unfold laneValue laneNat
  rw [BitVec.toNat_and, maskNat_toNat]
  have e0 := wid_lane w i 0 hw hi (by norm_num)
  have e1 := wid_lane w i 1 hw hi (by norm_num)
  have e2 := wid_lane w i 2 hw hi (by norm_num)
  have e3 := wid_lane w i 3 hw hi (by norm_num)
  rw [show 8 * w + i = 8 * w + 2 * 0 + i by ring, show 8 * w + 2 + i = 8 * w + 2 * 1 + i by ring,
    show 8 * w + 4 + i = 8 * w + 2 * 2 + i by ring, show 8 * w + 6 + i = 8 * w + 2 * 3 + i by ring,
    e0, e1, e2, e3]
  unfold maskNat
  interval_cases i
  · rw [if_pos rfl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    interval_cases w
    all_goals simp only [show (0 : ℕ) < 2 by norm_num, show (1 : ℕ) < 2 by norm_num,
      show ¬ (2 : ℕ) < 2 by norm_num, show ¬ (3 : ℕ) < 2 by norm_num, if_true, if_false,
      show (2 : ℕ) = 2 from rfl, show ¬ (3 : ℕ) = 2 by norm_num, show (0 : ℕ) < 2 by norm_num,
      show (1 : ℕ) < 2 by norm_num, and_mask7C, and_mask3C, and_mask3C2]
    all_goals norm_num
    all_goals omega
  · rw [if_neg (by norm_num), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    interval_cases w
    all_goals simp only [show (0 : ℕ) < 2 by norm_num, show (1 : ℕ) < 2 by norm_num,
      show ¬ (2 : ℕ) < 2 by norm_num, show ¬ (3 : ℕ) < 2 by norm_num, if_true, if_false,
      show (2 : ℕ) = 2 from rfl, show ¬ (3 : ℕ) = 2 by norm_num, and_mask7C, and_mask3C, and_mask3C2]
    all_goals norm_num
    all_goals omega

/-! ## Summing lanes -/

/-- The top lane of `A * 0x0001000100010001` is the sum of the lanes of `A`, when no lane of `A`
exceeds `1000`. -/
theorem topLane (a0 a1 a2 a3 : ℕ) (h0 : a0 ≤ 1000) (h1 : a1 ≤ 1000) (h2 : a2 ≤ 1000)
    (h3 : a3 ≤ 1000) :
    (a0 + 2 ^ 16 * a1 + 2 ^ 32 * a2 + 2 ^ 48 * a3) * broadcast 1 % 2 ^ 64 / 2 ^ 48 =
      a0 + a1 + a2 + a3 := by
  have e : (a0 + 2 ^ 16 * a1 + 2 ^ 32 * a2 + 2 ^ 48 * a3) * broadcast 1 =
      (a0 + 2 ^ 16 * (a0 + a1) + 2 ^ 32 * (a0 + a1 + a2) + 2 ^ 48 * (a0 + a1 + a2 + a3)) +
        2 ^ 64 * (a1 + a2 + a3 + 2 ^ 16 * (a2 + a3) + 2 ^ 32 * a3) := by
    unfold broadcast; ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

end OptimalOTS.Riscv2Program
