import Submissions.UpperRiscvHint.MixedFree

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

set_option allowUnsafeReducibility true in
attribute [local irreducible] OptimalOTS.RiscvMixedProgram.tables OptimalOTS.RiscvMixedProgram.verifier

namespace OptimalOTS.RiscvMixedProgram

open OptimalOTS.Dag RiscvZkvm.Rv64 Riscv2Program OracleComp

theorem dispatchTarget_guard (bank c : ℕ) (hb : 4 ≤ bank) (hu : bank ≤ 512) (hc : c < 32) :
    dispatchTarget (2048*bank + 4*(31-c)) = W (4096+4*(guardStart bank+(31-c))) := by
  unfold dispatchTarget
  rw [W_add_imm _ _ (by unfold freeLanding freeBase; omega)
    (by unfold freeLanding freeBase; omega) (by unfold freeLanding freeBase; omega) (by omega)]
  have eq : (((2048*bank+4*(31-c) : ℕ) : ℤ) +
      ((freeLanding : ℤ)-freeBase-124)).toNat = 4096+4*(guardStart bank+(31-c)) := by
    unfold freeLanding freeBase guardStart
    omega
  rw [eq]
  apply and_not_one_of_even
  rw [W_toNat _ (by unfold guardStart; omega)]
  omega

theorem guard_delta : ∀ d : Fin 32,
    signExtend13 (BitVec.ofInt 13 (-12-4*(d.val : ℤ))) =
      signExtend12 (imm12 (-12-4*(d.val : ℤ))) ∧
    Riscv.admittedInstruction (.BEQ .x0 .x0 (BitVec.ofInt 13 (-12-4*(d.val : ℤ)))) = true := by
  decide +kernel

/-- All 32 indirect-jump targets of an unexpected length bank reject. -/
theorem guard_refines (s : MachineState) (global : Riscv.CodeAt s (W 4096) verifier)
    (bank d : ℕ) (hb : 4 ≤ bank) (hu : bank ≤ 512) (hd : d < 32)
    (pc : s.pc = W (4096+4*(guardStart bank+d))) (fuel : ℕ) (hf : 4 ≤ fuel) :
    Riscv.Refines fuel s (pure (some false)) 4 := by
  have row := guard_located s global bank hb hu
  have fetch := row d (by simp [guardCode]; omega)
  rw [W_add, show 4096+4*guardStart bank+4*d = 4096+4*(guardStart bank+d) by omega,
    ← pc] at fetch
  change s.code s.pc = ((List.range 32).map (fun d : ℕ =>
    Instr.BEQ .x0 .x0 (BitVec.ofInt 13 (-12-4*(d : ℤ)))))[d]? at fetch
  simp only [List.getElem?_map, List.getElem?_range, hd, decide_true,
    Option.map_some] at fetch
  obtain ⟨delta, admitted⟩ := guard_delta ⟨d,hd⟩
  dsimp only at delta admitted
  have target : s.pc + signExtend13 (BitVec.ofInt 13 (-12-4*(d : ℤ))) =
      W (4096+4*(guardStart bank-3)) := by
    rw [pc, delta, W_add_imm _ _ (by omega) (by omega)
      (by unfold guardStart; omega) (by unfold guardStart; omega)]
    congr 1
    unfold guardStart
    omega
  have transition : step s = some (s.setPC (W (4096+4*(guardStart bank-3)))) := by
    rw [step, fetch]
    simp only [execInstrBr, if_true]
    rw [target]
    rfl
  have member : guardStart bank-3 ∈ rejectStubs := by
    apply List.mem_map.mpr
    refine ⟨bank, ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨bank-4, List.mem_range.mpr (by omega), by omega⟩
  have loc := (rejectStub_located s global _ member).code_eq
    (show (s.setPC (W (4096+4*(guardStart bank-3)))).code = s.code from rfl)
  have stop := reject_refines _ (fuel-1) loc (by omega)
  rw [show fuel = (fuel-1)+1 by omega, show (4 : ℕ) = 3+1 from rfl]
  exact Riscv.Refines.branch fetch admitted (fun h => nomatch h) transition stop

theorem smallBank_outside : ∀ bank : Fin 3, ∀ c : Fin 32,
    260710 ≤ ((dispatchTarget (2048*bank.val+4*(31-c.val)) - W 4096).toNat / 4) := by
  decide +kernel

theorem smallBank_refines (pk : PublicKey) (m : Message) (view : List Bool)
    (s : MachineState) (code : s.code = (S0 pk m view).code)
    (pc : s.pc = dispatchTarget (viewTag view)) (bank : viewBank view < 3) (fuel cost : ℕ) :
    Riscv.Refines fuel s (pure none) cost := by
  apply Riscv.Refines.trap
  have outside := smallBank_outside ⟨viewBank view,bank⟩ ⟨viewDigit view,viewDigit_lt view⟩
  have fetch : s.code s.pc = none := by
    rw [code, pc]
    have hc : (S0 pk m view).code = loadProgram Riscv.codeBase image.code := by
      simp only [S0, RiscvHint.loadView, Riscv.initialState, MachineState.code_setReg,
        MachineState.code_writeBytesAsWords]
      rfl
    rw [hc]
    change loadProgram Riscv.codeBase verifier (dispatchTarget (viewTag view)) = none
    unfold loadProgram
    rw [code_length]
    exact if_neg (fun h => Nat.not_lt_of_ge outside h.2)
  cases fuel with
  | zero => rfl
  | succ fuel => rw [Riscv.execute, fetch]

end OptimalOTS.RiscvMixedProgram
