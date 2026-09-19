import Submissions.UpperRiscv.Program
import Submissions.UpperRiscv.Valid

/-!
# Lane arithmetic of the index check

A lane word holds four 16-bit lanes. The index phase extracts nibbles into lanes with one shift
and one mask (`laneValue_toNat`), sums eight lane words without carries, and reads the sum of the
four lanes of the total from the top lane of a product (`topLane`). Everything reduces to natural
number arithmetic through `Nat.and_mod_two_pow` and `Nat.and_div_two_pow`.
-/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

/-! ## Masks -/

theorem and_split (x a b : ℕ) (ha : a < 2 ^ 16) :
    x &&& (a + 2 ^ 16 * b) = (x % 2 ^ 16 &&& a) + 2 ^ 16 * (x / 2 ^ 16 &&& b) := by
  rw [← Nat.mod_add_div (x &&& (a + 2 ^ 16 * b)) (2 ^ 16), Nat.and_mod_two_pow,
    Nat.and_div_two_pow]
  have e1 : (a + 2 ^ 16 * b) % 2 ^ 16 = a := by omega
  have e2 : (a + 2 ^ 16 * b) / 2 ^ 16 = b := by omega
  rw [e1, e2]

theorem and_120 (y : ℕ) : y &&& 120 = 8 * (y / 8 % 16) := by
  rw [← Nat.mod_add_div (y &&& 120) (2 ^ 3), Nat.and_mod_two_pow, Nat.and_div_two_pow]
  have e1 : (120 : ℕ) % 2 ^ 3 = 0 := by norm_num
  have e2 : (120 : ℕ) / 2 ^ 3 = 2 ^ 4 - 1 := by norm_num
  rw [e1, e2, Nat.and_zero, Nat.and_two_pow_sub_one_eq_mod]
  norm_num

/-- The mask `0x0078007800780078` keeps bits `3 … 6` of every lane. -/
theorem and_mask78 (x : ℕ) (hx : x < 2 ^ 64) :
    x &&& broadcast 120 =
      8 * (x / 2 ^ 3 % 16) + 2 ^ 16 * (8 * (x / 2 ^ 19 % 16)) +
      2 ^ 32 * (8 * (x / 2 ^ 35 % 16)) + 2 ^ 48 * (8 * (x / 2 ^ 51 % 16)) := by
  have hb : broadcast 120 = 120 + 2 ^ 16 * (120 + 2 ^ 16 * (120 + 2 ^ 16 * 120)) := by
    norm_num [broadcast]
  rw [hb, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num), and_120, and_120, and_120, and_120]
  omega

/-! ## Nibbles of a word -/

/-- Nibble `j` of a natural number. -/
theorem nibble_eq (w j : ℕ) : nibble w j = w / 2 ^ (4 * j) % 16 := by
  rw [nibble, pow_mul]
  norm_num

/-- Lane word `i` of `w`: nibbles `i, i + 4, i + 8, i + 12`, times eight, in the four lanes. -/
def laneNat (w i : ℕ) : ℕ :=
  8 * nibble w i + 2 ^ 16 * (8 * nibble w (4 + i)) + 2 ^ 32 * (8 * nibble w (8 + i)) +
    2 ^ 48 * (8 * nibble w (12 + i))

/-- The machine's lane word. -/
def laneValue (w : Word) (i : ℕ) : Word :=
  (if i = 0 then w <<< 3 else w >>> (4 * i - 3)) &&& BitVec.ofNat 64 (broadcast 120)

theorem laneValue_toNat (w : Word) (i : ℕ) (hi : i < 4) :
    (laneValue w i).toNat = laneNat w.toNat i := by
  have hw := w.isLt
  have hm : (BitVec.ofNat 64 (broadcast 120)).toNat = broadcast 120 := by
    rw [BitVec.toNat_ofNat]; norm_num [broadcast]
  unfold laneValue laneNat
  simp only [nibble_eq]
  rw [BitVec.toNat_and, hm]
  split_ifs with h0
  · subst h0
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [and_mask78 _ (Nat.mod_lt _ (by norm_num))]
    omega
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [and_mask78 _ (lt_of_le_of_lt (Nat.div_le_self _ _) hw)]
    simp only [Nat.div_div_eq_div_mul, ← pow_add]
    interval_cases i
    · exact absurd rfl h0
    all_goals norm_num

theorem laneNat_lanes (w i : ℕ) :
    laneNat w i = 8 * nibble w i + 2 ^ 16 * (8 * nibble w (4 + i)) +
      2 ^ 32 * (8 * nibble w (8 + i)) + 2 ^ 48 * (8 * nibble w (12 + i)) := rfl

/-! ## Summing lanes -/

/-- The top lane of `A * 0x0001000100010001` is the sum of the lanes of `A`, when no lane of `A`
exceeds `960`. -/
theorem topLane (a0 a1 a2 a3 : ℕ) (h0 : a0 ≤ 960) (h1 : a1 ≤ 960) (h2 : a2 ≤ 960)
    (h3 : a3 ≤ 960) :
    (a0 + 2 ^ 16 * a1 + 2 ^ 32 * a2 + 2 ^ 48 * a3) * broadcast 1 % 2 ^ 64 / 2 ^ 48 =
      a0 + a1 + a2 + a3 := by
  have e : (a0 + 2 ^ 16 * a1 + 2 ^ 32 * a2 + 2 ^ 48 * a3) * broadcast 1 =
      (a0 + 2 ^ 16 * (a0 + a1) + 2 ^ 32 * (a0 + a1 + a2) + 2 ^ 48 * (a0 + a1 + a2 + a3)) +
        2 ^ 64 * (a1 + a2 + a3 + 2 ^ 16 * (a2 + a3) + 2 ^ 32 * a3) := by
    unfold broadcast; ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

end OptimalOTS.RiscvUpperProgram
