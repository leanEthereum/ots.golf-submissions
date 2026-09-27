import Submissions.UpperRiscvHint.AssemblyMacros
import Submissions.UpperRiscvHint.RejectAdapter

/-!
# Refinement with exact cycle accounting

`Refines fuel s q c` states that the machine's observed decision from `s` is the oracle
computation `q`, up to terminal oracle queries after which the decision is already fixed, and
that every completed execution path costs at most `c` cycles. The only such queries are a HASH
that the decision `ECALL` issues on a wrong low key word before the machine traps: its input is
arbitrary memory, so `q` states the trap and omits the query.
The composition rules mirror the observation rules and add the cost of each region.
-/

namespace OptimalOTS.Riscv

open RiscvZkvm.Rv64 OracleComp

def Refines (fuel : ℕ) (s : MachineState) (q : OracleComp Spec (Option Bool))
    (c : ℕ) : Prop :=
  RejectAdapter.Prunes q (observe fuel s) ∧
    ∀ b cycles, some (b, cycles) ∈ support (execute fuel s) → cycles ≤ c

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
  · rw [steps.observe fuel]
    exact h.1
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
    exact RejectAdapter.Prunes.bind_left _ _ _ (fun answer => (h answer).1)
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
  refine ⟨by rw [observe_halt fuel s decision fetch call result]; exact .refl _, ?_⟩
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

/-- A run that can only trap refines `none` at every cost. -/
theorem Refines.trap {fuel : ℕ} {s : MachineState} {c : ℕ} (h : execute fuel s = pure none) :
    Refines fuel s (pure none) c := by
  refine ⟨by rw [observe, h]; exact .refl _, ?_⟩
  intro b cycles hm
  rw [h] at hm
  simp at hm

/-- An `ECALL` whose call number is neither HALT nor HASH traps. -/
theorem execute_badCall (fuel : ℕ) (s : MachineState) (fetch : s.code s.pc = some .ECALL)
    (halt : s.getReg .x5 ≠ 0) (call : s.getReg .x5 ≠ hashCall) :
    execute (fuel + 1) s = pure none := by
  rw [execute, fetch]
  simp only [admittedInstruction, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg halt, if_neg call]

/-- A HALT whose result is not a decision traps. -/
theorem execute_badHalt (fuel : ℕ) (s : MachineState) (fetch : s.code s.pc = some .ECALL)
    (halt : s.getReg .x5 = 0) (zero : s.getReg .x10 ≠ 0) (one : s.getReg .x10 ≠ 1) :
    execute (fuel + 1) s = pure none := by
  rw [execute, fetch]
  simp only [admittedInstruction, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [if_pos halt, if_neg zero, if_neg one]

/-- A jump to address 0, where no code is loaded, traps. -/
theorem execute_jumpNull (fuel : ℕ) (s : MachineState)
    (fetch : s.code s.pc = some (.JALR .x0 .x0 0)) (null : s.code 0 = none) :
    execute fuel s = pure none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [execute_regular fuel s _ fetch rfl (fun h => nomatch h)]
    have hs : step s = some (s.setPC ((s.getReg .x0 + signExtend12 0) &&& ~~~(1#64))) := by
      rw [RiscvZkvm.Rv64.step, fetch]; rfl
    have hpc : (s.getReg .x0 + signExtend12 0) &&& ~~~(1#64) = 0 := by
      change (0 + signExtend12 0) &&& ~~~(1#64) = 0
      decide
    rw [hs, hpc]
    cases fuel with
    | zero => rfl
    | succ fuel =>
      dsimp only
      rw [execute]
      rw [show (s.setPC 0).code (s.setPC 0).pc = none from null]
      rfl

/-- A HASH call that can only trap afterwards refines `none`; its query is a pruned suffix. -/
theorem Refines.junkHash {fuel : ℕ} {s : MachineState} {c : ℕ}
    (fetch : s.code s.pc = some .ECALL) (call : s.getReg .x5 = hashCall)
    (next : ∀ answer, execute fuel (writeHash s answer) = pure none) :
    Refines (fuel + 1) s (pure none) c := by
  by_cases valid : hashArgumentsValid s = true
  · refine ⟨?_, ?_⟩
    · rw [observe_hash fuel s fetch call valid]
      have e : (fun answer => observe fuel (writeHash s answer)) = fun _ => pure none := by
        funext answer; rw [observe, next answer]; rfl
      rw [e]
      exact .stop _ none
    · intro b cycles hm
      rw [execute_hash fuel s fetch call valid, support_bind] at hm
      simp only [Set.mem_iUnion] at hm
      obtain ⟨answer, _, hm⟩ := hm
      rw [next answer] at hm
      simp [addCycles] at hm
  · apply Refines.trap
    rw [execute, fetch]
    simp only [admittedInstruction, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (show s.getReg .x5 ≠ 0 by rw [call]; decide), if_pos call, if_neg valid]

end OptimalOTS.Riscv
