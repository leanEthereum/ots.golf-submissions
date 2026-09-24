import Submissions.UpperRiscv.MixedIndexArith

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W W_toNat)

theorem baseLane_bounds (q : ℕ) (hq : q < 16) :
    7804 ≤ baseLane q ∧ baseLane q < 65536 := by
  interval_cases q <;> decide +kernel

theorem baseWord_expand (g : ℕ) (hg : g < 4) : baseWord g =
    baseLane (4*g) + 2^16*baseLane (4*g+1) +
      2^32*baseLane (4*g+2) + 2^48*baseLane (4*g+3) := by
  interval_cases g <;> decide +kernel

theorem baseWord_toNat (g : ℕ) (hg : g < 4) : (W (baseWord g)).toNat = baseWord g := by
  interval_cases g <;> decide +kernel

theorem baseWord_third : baseWord 2 = baseWord 0 := by decide +kernel

theorem baseWord_last : baseWord 3 = baseWord 0 := by decide +kernel

theorem lane_extract (x0 x1 x2 x3 l : ℕ) (h0 : x0 < 2 ^ 16) (h1 : x1 < 2 ^ 16)
    (h2 : x2 < 2 ^ 16) (h3 : x3 < 2 ^ 16) (hl : l < 4) :
    (x0 + 2 ^ 16*x1 + 2 ^ 32*x2 + 2 ^ 48*x3)/2^(16*l)%2^16 =
      [x0,x1,x2,x3].getD l 0 := by
  have lo (a b : ℕ) (h : a < 65536) : (a+65536*b)%65536 = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  have hi (a b : ℕ) (h : a < 65536) : (a+65536*b)/65536 = b := by
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt h, Nat.zero_add]
  have e : x0+2^16*x1+2^32*x2+2^48*x3 = x0+65536*(x1+65536*(x2+65536*x3)) := by ring
  rw [e]
  interval_cases l
  · simpa using lo x0 (x1+65536*(x2+65536*x3)) h0
  · change (x0+65536*(x1+65536*(x2+65536*x3)))/65536%65536 = x1
    rw [hi _ _ h0, lo _ _ h1]
  · change (x0+65536*(x1+65536*(x2+65536*x3)))/(65536*65536)%65536 = x2
    rw [← Nat.div_div_eq_div_mul, hi _ _ h0, hi _ _ h1, lo _ _ h2]
  · change (x0+65536*(x1+65536*(x2+65536*x3)))/(65536*(65536*65536))%65536 = x3
    rw [← Nat.div_div_eq_div_mul, hi _ _ h0, ← Nat.div_div_eq_div_mul,
      hi _ _ h1, hi _ _ h2]
    exact Nat.mod_eq_of_lt h3

/-- Each base lane exceeds the masked digit pair, so subtraction never borrows between lanes. -/
theorem lane_halfword (u g l : ℕ) (hg : g < 4) (hl : l < 4) (L : Word)
    (hL : L.toNat = laneNat u g) :
    (W (baseWord g)-L).toNat/2^(16*l)%2^16 =
      baseLane (4*g+l) - (4*fineFld g u l + 512*coarseFld g u l) := by
  have b0 := baseLane_bounds (4*g) (by omega)
  have b1 := baseLane_bounds (4*g+1) (by omega)
  have b2 := baseLane_bounds (4*g+2) (by omega)
  have b3 := baseLane_bounds (4*g+3) (by omega)
  have n0 := laneEntry_le g u 0
  have n1 := laneEntry_le g u 1
  have n2 := laneEntry_le g u 2
  have n3 := laneEntry_le g u 3
  have hle : L ≤ W (baseWord g) := by
    rw [BitVec.le_def, hL, baseWord_toNat g hg, baseWord_expand g hg]
    unfold laneNat
    omega
  rw [BitVec.toNat_sub_of_le hle, hL, baseWord_toNat g hg]
  have e : baseWord g - laneNat u g =
      (baseLane (4*g)-(4*fineFld g u 0+512*coarseFld g u 0)) +
      2^16*(baseLane (4*g+1)-(4*fineFld g u 1+512*coarseFld g u 1)) +
      2^32*(baseLane (4*g+2)-(4*fineFld g u 2+512*coarseFld g u 2)) +
      2^48*(baseLane (4*g+3)-(4*fineFld g u 3+512*coarseFld g u 3)) := by
    rw [baseWord_expand g hg]; unfold laneNat; omega
  rw [e, lane_extract _ _ _ _ l (by omega) (by omega) (by omega) (by omega) hl]
  interval_cases l <;> rfl

end OptimalOTS.RiscvMixedProgram
