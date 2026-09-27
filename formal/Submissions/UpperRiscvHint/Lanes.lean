import Submissions.UpperRiscvHint.Program
import Submissions.UpperRiscvHint.Valid

/-! Masking a word lane by lane: every mask identity reduces to natural number arithmetic through
`Nat.and_mod_two_pow` and `Nat.and_div_two_pow`. -/

namespace OptimalOTS.Riscv2Program

open RiscvZkvm.Rv64

theorem and_split_at (x a b n : ℕ) (ha : a < 2 ^ n) :
    x &&& (a + 2 ^ n * b) = (x % 2 ^ n &&& a) + 2 ^ n * (x / 2 ^ n &&& b) := by
  rw [← Nat.mod_add_div (x &&& (a + 2 ^ n * b)) (2 ^ n), Nat.and_mod_two_pow,
    Nat.and_div_two_pow]
  have e1 : (a + 2 ^ n * b) % 2 ^ n = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have e2 : (a + 2 ^ n * b) / 2 ^ n = b := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [e1, e2]

theorem and_split (x a b : ℕ) (ha : a < 2 ^ 16) :
    x &&& (a + 2 ^ 16 * b) = (x % 2 ^ 16 &&& a) + 2 ^ 16 * (x / 2 ^ 16 &&& b) :=
  and_split_at x a b 16 ha

/-- A mask of `b` bits shifted up by two keeps `4 · (y / 4 % 2 ^ b)`. -/
theorem and_field (y b : ℕ) : y &&& (4 * (2 ^ b - 1)) = 4 * (y / 4 % 2 ^ b) := by
  rw [← Nat.mod_add_div (y &&& (4 * (2 ^ b - 1))) (2 ^ 2), Nat.and_mod_two_pow,
    Nat.and_div_two_pow]
  have e1 : (4 * (2 ^ b - 1)) % 2 ^ 2 = 0 := by omega
  have e2 : (4 * (2 ^ b - 1)) / 2 ^ 2 = 2 ^ b - 1 := by omega
  rw [e1, e2, Nat.and_zero, Nat.and_two_pow_sub_one_eq_mod]
  norm_num

/-- A field of a word: bits `p …` of width `b`. -/
def fld (u p b : ℕ) : ℕ := u / 2 ^ p % 2 ^ b

/-- The machine's lane word. -/
def laneValue (u mask : Word) : Word := u &&& mask

end OptimalOTS.Riscv2Program
