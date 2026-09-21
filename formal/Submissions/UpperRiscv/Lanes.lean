import Submissions.UpperRiscv.Program
import Submissions.UpperRiscv.Valid

/-!
# Lane arithmetic of the index check

A lane word holds four 16-bit lanes. The index phase extracts the fields of the index answer into
lanes with at most one shift and one mask (`laneValue_toNat`): the fields sit at bits `2 …` of
their lanes after the shift, so the mask keeps `4 · field`, five bits wide for the first four lane
words and four for the last three. Seven lane words are summed without carries, and the sum of
the four lanes of the total is read from the top lane of a product (`topLane`). Everything
reduces to natural number arithmetic through `Nat.and_mod_two_pow` and `Nat.and_div_two_pow`.
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

/-! ## Fields of a word -/

/-- A field of a word: bits `p …` of width `b`. -/
def fld (u p b : ℕ) : ℕ := u / 2 ^ p % 2 ^ b

/-- Lane `l` of lane word `g`: the field of its index word `u` at bits `16 l + 2 + shiftOf g`. -/
def laneFld (u g l : ℕ) : ℕ := fld u (16 * l + 2 + shiftOf g) (widthOf g)

/-- The mask of lane word `g`. -/
def maskNat (g : ℕ) : ℕ := if g < 4 then broadcast 0x7C else broadcast 0x3C

/-- Lane word `g` of the index word `u`: its four fields, times four, in the four lanes. -/
def laneNat (u g : ℕ) : ℕ :=
  4 * laneFld u g 0 + 2 ^ 16 * (4 * laneFld u g 1) + 2 ^ 32 * (4 * laneFld u g 2) +
    2 ^ 48 * (4 * laneFld u g 3)

/-- The machine's lane word. -/
def laneValue (u : Word) (g : ℕ) (mask : Word) : Word :=
  (if shiftOf g = 0 then u else u >>> shiftOf g) &&& mask

theorem maskNat_toNat (g : ℕ) : (BitVec.ofNat 64 (maskNat g)).toNat = maskNat g := by
  rw [BitVec.toNat_ofNat]
  unfold maskNat broadcast
  split_ifs <;> norm_num

theorem laneValue_toNat (u : Word) (g : ℕ) (hg : g < 7) :
    (laneValue u g (BitVec.ofNat 64 (maskNat g))).toNat = laneNat u.toNat g := by
  have hu := u.isLt
  have m7 : broadcast 0x7C % 2 ^ 64 = broadcast 0x7C := Nat.mod_eq_of_lt (by norm_num [broadcast])
  have m3 : broadcast 0x3C % 2 ^ 64 = broadcast 0x3C := Nat.mod_eq_of_lt (by norm_num [broadcast])
  unfold laneValue laneNat laneFld fld maskNat
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  interval_cases g <;>
    simp only [shiftOf, widthOf, Nat.reduceEqDiff, Nat.reduceLT, or_self, or_false, false_or,
      ↓reduceIte, m7, m3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, and_mask7C,
      and_mask3C] <;>
    omega

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
