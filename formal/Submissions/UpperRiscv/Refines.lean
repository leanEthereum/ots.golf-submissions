import Submissions.UpperRiscv.AssemblyMacros

/-!
# Refinement with exact cycle accounting

`Refines fuel s q c` states that the machine's observed decision from `s` is the oracle
computation `q` and that every completed execution path costs at most `c` cycles.
The composition rules mirror the observation rules and add the cost of each region.
-/

namespace OptimalOTS.Riscv

open RiscvZkvm.Rv64 OracleComp

def Refines (fuel : ℕ) (s : MachineState) (q : OracleComp Spec (Option Bool))
    (c : ℕ) : Prop :=
  observe fuel s = q ∧ ∀ b cycles, some (b, cycles) ∈ support (execute fuel s) → cycles ≤ c

theorem Refines.mono {fuel : ℕ} {s : MachineState} {q : OracleComp Spec (Option Bool)}
    {c c' : ℕ} (h : Refines fuel s q c) (hc : c ≤ c') : Refines fuel s q c' :=
  ⟨h.1, fun b cycles hm => (h.2 b cycles hm).trans hc⟩

theorem Refines.congr {fuel : ℕ} {s : MachineState} {q q' : OracleComp Spec (Option Bool)}
    {c : ℕ} (h : Refines fuel s q c) (hq : q = q') : Refines fuel s q' c := hq ▸ h

theorem addCycles_zero (x : Outcome) : addCycles 0 x = x := by
  cases x with
  | none => rfl
  | some p => simp [addCycles]

theorem addCycles_addCycles (a b : ℕ) (x : Outcome) :
    addCycles a (addCycles b x) = addCycles (a + b) x := by
  cases x with
  | none => rfl
  | some p => simp [addCycles, Nat.add_assoc]

theorem PureSteps.execute {n : ℕ} {s final : MachineState} (steps : PureSteps n s final)
    (fuel : ℕ) : execute (n + fuel) s = addCycles n <$> execute fuel final := by
  induction steps with
  | refl s =>
    have h : addCycles 0 = (id : Outcome → Outcome) := funext addCycles_zero
    rw [Nat.zero_add, h]
    simp
  | cons fetch admitted ordinary transition rest ih =>
    rw [Nat.add_right_comm, execute_regular _ _ _ fetch admitted ordinary, transition]
    dsimp only
    rw [ih, Functor.map_map]
    congr 1
    funext x
    rw [addCycles_addCycles, Nat.add_comm]

/-- Ordinary steps add exactly one cycle each. -/
theorem Refines.steps {n : ℕ} {s final : MachineState} (steps : PureSteps n s final)
    {fuel : ℕ} {q : OracleComp Spec (Option Bool)} {c : ℕ}
    (h : Refines fuel final q c) : Refines (n + fuel) s q (n + c) := by
  refine ⟨?_, ?_⟩
  · rw [← h.1]
    exact steps.observe fuel
  · intro b cycles hm
    rw [steps.execute] at hm
    exact addCycles_bound _ n c h.2 b cycles hm

theorem Refines.linear {s : MachineState} (code : List Instr)
    (located : CodeAt s s.pc code) (ready : LinearReady s code)
    {fuel : ℕ} {q : OracleComp Spec (Option Bool)} {c : ℕ}
    (h : Refines fuel (code.foldl execInstrBr s) q c) :
    Refines (code.length + fuel) s q (code.length + c) :=
  Refines.steps (linear_steps s code located ready) h

theorem execute_hash (fuel : ℕ) (s : MachineState)
    (fetch : s.code s.pc = some .ECALL) (call : s.getReg .x5 = hashCall)
    (valid : hashArgumentsValid s = true) :
    execute (fuel + 1) s = (do
      let answer ← hash (hashInput s).2
      addCycles (blockCost (hashInput s).1) <$> execute fuel (writeHash s answer)) := by
  rw [execute, fetch]
  simp only [admittedInstruction, Bool.not_true, Bool.false_eq_true, ↓reduceIte, call,
    show hashCall ≠ 0 by decide, valid]

/-- A hash call costs its block count and continues with the answer written. -/
theorem Refines.hash {fuel : ℕ} {s : MachineState}
    (fetch : s.code s.pc = some .ECALL) (call : s.getReg .x5 = hashCall)
    (valid : hashArgumentsValid s = true)
    {k : BitVec hashBits → OracleComp Spec (Option Bool)} {c : ℕ}
    (h : ∀ answer, Refines fuel (writeHash s answer) (k answer) c) :
    Refines (fuel + 1) s (hash (hashInput s).2 >>= k)
      (blockCost (hashInput s).1 + c) := by
  refine ⟨?_, ?_⟩
  · rw [observe_hash fuel s fetch call valid]
    exact bind_congr_of_forall_mem_support _ (fun answer _ => (h answer).1)
  · intro b cycles hm
    rw [execute_hash fuel s fetch call valid, support_bind] at hm
    simp only [Set.mem_iUnion] at hm
    obtain ⟨answer, _, hm⟩ := hm
    exact addCycles_bound _ _ c (h answer).2 b cycles hm

/-- HALT costs one cycle. -/
theorem Refines.halt {fuel : ℕ} {s : MachineState} (decision : Bool)
    (fetch : s.code s.pc = some .ECALL) (call : s.getReg .x5 = 0)
    (result : s.getReg .x10 = BitVec.ofNat 64 decision.toNat) :
    Refines (fuel + 1) s (pure (some decision)) 1 := by
  refine ⟨observe_halt fuel s decision fetch call result, ?_⟩
  intro b cycles hm
  cases decision <;> simp [execute, fetch, call, result, admittedInstruction] at hm <;> omega

/-- A forward conditional branch costs one cycle. -/
theorem Refines.branch {s next : MachineState} {i : Instr}
    (fetch : s.code s.pc = some i) (admitted : admittedInstruction i = true)
    (ordinary : i ≠ .ECALL) (transition : step s = some next)
    {fuel : ℕ} {q : OracleComp Spec (Option Bool)} {c : ℕ}
    (h : Refines fuel next q c) : Refines (fuel + 1) s q (c + 1) := by
  have := Refines.steps (PureSteps.cons fetch admitted ordinary transition (PureSteps.refl next)) h
  rwa [Nat.add_comm 1 fuel, Nat.add_comm 1 c] at this

end OptimalOTS.Riscv
