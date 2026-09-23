import Submissions.UpperRiscv.MixedChainFrame
import Submissions.UpperRiscv.MixedCode

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name OracleComp
open Riscv2Program

def dispatchCode (q : ℕ) : Code :=
  [.LHU .x28 .x12 (imm12 ((laneAddr q : ℤ)-outAddr (2*q))),
   .JALR .x0 .x28 (imm12 (jumpImm q))]

theorem lane_offset' : ∀ q : Fin 16,
    W (outAddr (2*q)) + signExtend12 (imm12 ((laneAddr q : ℤ)-outAddr (2*q))) = W (laneAddr q) := by
  decide +kernel

theorem lane_access' : ∀ q : Fin 16, isValidHalfwordAccess (W (laneAddr q)) = true := by
  decide +kernel

theorem dispatch_refines (index : Idx) (wire : List Bool) (pk : PublicKey)
    (q : Fin 16) (k : Fin 32) (hk : k.val = 2*q.val) (s : MachineState) (x : graph.Assignment)
    (inv : HashInv index wire pk s x k (work k)) (tail : Code)
    (located : Riscv.CodeAt s s.pc (dispatchCode q ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : 2 ≤ fuel)
    (continuation : ∀ u, HashInv index wire pk u x k (work k) → u.mem=s.mem →
      u.pc = W (landing0 q-dispatch index q) → Riscv.Refines (fuel-2) u Q c) :
    Riscv.Refines fuel s Q (2+c) := by
  let front : Code := [.LHU .x28 .x12 (imm12 ((laneAddr q : ℤ)-outAddr (2*q)))]
  have ready : Riscv.LinearReady s front := by
    simp only [front, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, and_true, true_and]
    rw [inv.out, hk, lane_offset' q]
    exact lane_access' q
  have code : Riscv.CodeAt s s.pc (front ++ ([.JALR .x0 .x28 (imm12 (jumpImm q))] ++ tail)) := located
  set a := front.foldl execInstrBr s with ha
  have apc : a.pc = s.pc+4 := by rfl
  have acode : a.code = s.code := by rfl
  have aregs : ∀ r, r ≠ .x28 → a.getReg r = s.getReg r := by
    intro r hr
    simp [ha, front, execInstrBr, getReg_setReg_ite, hr]
  have ainput : a.getReg .x10 = W (work k) := by rw [aregs .x10 (by decide)]; exact inv.input
  have ainv := HashInv.frame index wire pk inv (work k) ainput inv.inputRange
    (fun r _ h28 => aregs r h28) (by rfl) acode
  have av : (a.getReg .x28).toNat = baseLane q-dispatch index q := by
    simp only [ha, front, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, if_true, inv.out, hk, lane_offset' q]
    have hm : (s.getHalfword (W (laneAddr q))).toNat % 18446744073709551616 =
        (s.getHalfword (W (laneAddr q))).toNat := Nat.mod_eq_of_lt (by
      have := (s.getHalfword (W (laneAddr q))).isLt
      omega)
    simpa only [BitVec.toNat_setWidth, hm] using inv.ctx.lanes q
  have target := jump_target index q q.isLt (a.getReg .x28) av
  have aloc : Riscv.CodeAt a a.pc ([.JALR .x0 .x28 (imm12 (jumpImm q))] ++ tail) := by
    rw [apc]
    exact code.append_right.code_eq acode
  have transition := jalr_transition a (imm12 (jumpImm q)) aloc.head
  rw [target] at transition
  have binv : HashInv index wire pk (a.setPC (W (landing0 q-dispatch index q))) x k (work k) := by
    apply HashInv.frame index wire pk (t := a.setPC (W (landing0 q-dispatch index q))) ainv (work k) ainput inv.inputRange
      (fun r _ _ => rfl) rfl rfl
  rw [show fuel = front.length+((fuel-2)+1) by simp [front]; omega,
    show 2+c = front.length+(c+1) by simp [front]; omega]
  apply Riscv.Refines.linear front code.append_left ready
  rw [← ha]
  exact Riscv.Refines.branch aloc.head rfl (fun h => nomatch h) transition
    (continuation _ binv rfl rfl)

end OptimalOTS.RiscvMixedProgram
