import Submissions.UpperRiscv.BlockExecution
import Submissions.UpperRiscv.Program

/-! Verified ordinary-instruction macros used by the assembly proof. -/

namespace OptimalOTS.RiscvUpperProgram

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

theorem signExtend13_nonnegative (n : ℕ) (hn : n < 4096) :
    signExtend13 (BitVec.ofNat 13 n) = BitVec.ofNat 64 n := by
  have msb : (BitVec.ofNat 13 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [signExtend13, BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A forward `BEQ` over a three-instruction rejection. -/
theorem beq_transition (s : MachineState) (r r' : Reg)
    (fetch : s.code s.pc = some (.BEQ r r' 16)) :
    step s = some (s.setPC (s.pc + if s.getReg r = s.getReg r' then 16 else 4)) := by
  rw [step, fetch]
  have hsign : signExtend13 (16 : BitVec 13) = 16 := by decide
  simp only [execInstrBr, hsign]
  by_cases h : s.getReg r = s.getReg r' <;> simp [h]

end OptimalOTS.RiscvUpperProgram
