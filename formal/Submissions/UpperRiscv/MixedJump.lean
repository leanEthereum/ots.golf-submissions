import Submissions.UpperRiscv.MixedDispatchArith
import Submissions.UpperRiscv.MixedContext

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program
open OptimalOTS.Dag

/-- An even address is unchanged by clearing its low bit. -/
theorem and_not_one_of_even (a : Word) (h : a.toNat % 2 = 0) : a &&& ~~~(1#64) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases hi0 : i = 0
  · subst hi0
    have h0 : a.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]
      simp [h]
    rw [h0]
    decide
  · simp [hi0, hi]

theorem jump_offset_range' : ∀ q : Fin 16, -2048 ≤ jumpImm q ∧ jumpImm q < 2048 := by
  decide +kernel

theorem jump_offset_range (q : ℕ) (hq : q < 16) : -2048 ≤ jumpImm q ∧ jumpImm q < 2048 :=
  jump_offset_range' ⟨q, hq⟩

theorem landing0_bounds' : ∀ q : Fin 16, 7804 ≤ landing0 q ∧ landing0 q < 68000 := by
  decide +kernel

theorem landing0_bounds (q : ℕ) (hq : q < 16) : 7804 ≤ landing0 q ∧ landing0 q < 68000 :=
  landing0_bounds' ⟨q, hq⟩

theorem landing0_mod' : ∀ q : Fin 16, landing0 q % 4 = 0 := by decide +kernel

theorem landing0_mod (q : ℕ) (hq : q < 16) : landing0 q % 4 = 0 := landing0_mod' ⟨q, hq⟩

/-- The computed jump lands on `landing0 q` less the dispatch value. -/
theorem jump_target (index : Idx) (q : ℕ) (hq : q < 16) (v : Word)
    (hv : v.toNat = baseLane q - dispatch index q) :
    (v + signExtend12 (imm12 (jumpImm q))) &&& ~~~(1#64) = W (landing0 q - dispatch index q) := by
  obtain ⟨r1, r2⟩ := jump_offset_range q hq
  have hb := baseLane_bounds q hq
  have hl := landing0_bounds q hq
  have hm := landing0_mod q hq
  have hd := dispatch_le index q
  have hv' : v = W (baseLane q - dispatch index q) := by
    apply BitVec.eq_of_toNat_eq
    rw [hv, W_toNat _ (by omega)]
  rw [hv', W_add_imm _ _ r1 r2 (by unfold jumpImm at *; omega) (by omega)]
  have e : (((baseLane q - dispatch index q : ℕ) : ℤ) + jumpImm q).toNat =
      landing0 q - dispatch index q := by
    unfold jumpImm at *
    omega
  rw [e]
  apply and_not_one_of_even
  rw [W_toNat _ (by omega)]
  unfold dispatch at *
  omega

theorem jalr_transition (s : MachineState) (i : BitVec 12)
    (fetch : s.code s.pc = some (.JALR .x0 .x28 i)) :
    RiscvZkvm.Rv64.step s = some (s.setPC ((s.getReg .x28 + signExtend12 i) &&& ~~~(1#64))) := by
  rw [RiscvZkvm.Rv64.step, fetch]
  rfl


end OptimalOTS.RiscvMixedProgram
