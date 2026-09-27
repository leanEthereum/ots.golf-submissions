import Submissions.UpperRiscvHint.BlockExecution
import Submissions.UpperRiscvHint.Program

/-! Verified ordinary-instruction macros used by the assembly proof. -/

namespace OptimalOTS.Riscv2Program

open RiscvZkvm.Rv64

theorem signExtend12_nonnegative (n : ℕ) (hn : n < 2048) :
    signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  have msb : (BitVec.ofNat 12 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [signExtend12, BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end OptimalOTS.Riscv2Program
