import OptimalOTS.RiscvMachine

/-! A reusable cost rule for fuel-bounded machine executions. -/

namespace OptimalOTS.Riscv

open RiscvZkvm.Rv64 OracleComp

theorem execute_regular (fuel : ℕ) (s : MachineState) (i : Instr)
    (fetch : s.code s.pc = some i) (admitted : admittedInstruction i = true)
    (ordinary : i ≠ .ECALL) :
    execute (fuel + 1) s = match step s with
      | none => pure none
      | some next => addCycles 1 <$> execute fuel next := by
  rw [execute, fetch]
  simp only [admitted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases i <;> rfl

theorem addCycles_bound (computation : OracleComp Spec Outcome) (a b : ℕ)
    (bound : ∀ decision cycles, some (decision, cycles) ∈ support computation → cycles ≤ b)
    (decision : Bool) (cycles : ℕ)
    (h : some (decision, cycles) ∈ support (addCycles a <$> computation)) : cycles ≤ a + b := by
  rw [support_map] at h
  obtain ⟨result, hr, equal⟩ := h
  cases result with
  | none => cases equal
  | some result =>
    rcases result with ⟨decision', cycles'⟩
    have hc : a + cycles' = cycles := congrArg (fun v : Outcome => (v.getD (false, 0)).2) equal
    have hb := bound decision' cycles' hr
    omega

end OptimalOTS.Riscv
