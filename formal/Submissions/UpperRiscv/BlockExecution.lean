import Submissions.UpperRiscv.MachineCost

/-! Compositional execution rules for the RISC-V implementation proof. -/

namespace OptimalOTS.Riscv

open RiscvZkvm.Rv64 OracleComp

/-- Observe the decision while retaining the entire oracle computation. -/
def observe (fuel : ℕ) (s : MachineState) : OracleComp Spec (Option Bool) :=
  Option.map Prod.fst <$> execute fuel s

theorem observe_regular (fuel : ℕ) (s next : MachineState) (i : Instr)
    (fetch : s.code s.pc = some i) (admitted : admittedInstruction i = true)
    (ordinary : i ≠ .ECALL) (transition : step s = some next) :
    observe (fuel + 1) s = observe fuel next := by
  unfold observe
  rw [execute_regular fuel s i fetch admitted ordinary, transition]
  simp only [Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

theorem observe_hash (fuel : ℕ) (s : MachineState)
    (fetch : s.code s.pc = some .ECALL) (call : s.getReg .x5 = hashCall)
    (valid : hashArgumentsValid s = true) :
    observe (fuel + 1) s = (do
      let answer ← hash (hashInput s).2
      observe fuel (writeHash s answer)) := by
  unfold observe
  rw [execute, fetch]
  simp only [admittedInstruction, Bool.not_true, Bool.false_eq_true, ↓reduceIte, call,
    show hashCall ≠ 0 by decide, valid]
  simp only [map_bind, Functor.map_map]
  congr 1
  funext answer
  congr 1
  funext result
  cases result <;> rfl

theorem observe_halt (fuel : ℕ) (s : MachineState) (decision : Bool)
    (fetch : s.code s.pc = some .ECALL) (call : s.getReg .x5 = 0)
    (result : s.getReg .x10 = BitVec.ofNat 64 decision.toNat) :
    observe (fuel + 1) s = pure (some decision) := by
  cases decision <;> simp [observe, execute, fetch, call, result, admittedInstruction]

/-- A concrete sequence of ordinary transitions, including conditional branches. -/
inductive PureSteps : ℕ → MachineState → MachineState → Prop
  | refl (s) : PureSteps 0 s s
  | cons {n s next final i} (fetch : s.code s.pc = some i)
      (admitted : admittedInstruction i = true) (ordinary : i ≠ .ECALL)
      (transition : step s = some next) (rest : PureSteps n next final) :
      PureSteps (n + 1) s final

theorem PureSteps.observe {n s final} (steps : PureSteps n s final) (fuel : ℕ) :
    Riscv.observe (n + fuel) s = Riscv.observe fuel final := by
  induction steps with
  | refl => simp
  | cons fetch admitted ordinary transition rest ih =>
    rw [Nat.add_right_comm,
      observe_regular _ _ _ _ fetch admitted ordinary transition, ih]

/-- A finite instruction list at a given address; the surrounding code is unrestricted. -/
def CodeAt (s : MachineState) (pc : Word) (code : List Instr) : Prop :=
  ∀ n, n < code.length → s.code (pc + BitVec.ofNat 64 (4 * n)) = code[n]?

theorem CodeAt.head {s : MachineState} {pc : Word} {i : Instr} {code : List Instr}
    (located : CodeAt s pc (i :: code)) : s.code pc = some i := by
  simpa using located 0 (by simp)

theorem CodeAt.code_eq {s t : MachineState} {pc : Word} {code : List Instr}
    (located : CodeAt s pc code) (same : t.code = s.code) : CodeAt t pc code := by
  intro n hn
  rw [same]
  exact located n hn

theorem CodeAt.append_left {s : MachineState} {pc : Word} {first last : List Instr}
    (located : CodeAt s pc (first ++ last)) : CodeAt s pc first := by
  intro n hn
  rw [located n (by simp; omega), List.getElem?_append_left hn]

theorem CodeAt.append_right {s : MachineState} {pc : Word} {first last : List Instr}
    (located : CodeAt s pc (first ++ last)) :
    CodeAt s (pc + BitVec.ofNat 64 (4 * first.length)) last := by
  intro n hn
  have h := located (first.length + n) (by simp; omega)
  simpa only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc,
    List.getElem?_append_right (by omega : first.length ≤ first.length + n),
    Nat.add_sub_cancel_left] using h

theorem CodeAt.tail {s : MachineState} {pc : Word} {i : Instr} {code : List Instr}
    (located : CodeAt s pc (i :: code)) : CodeAt s (pc + 4) code := by
  exact CodeAt.append_right (first := [i]) located

/-- The competition loader installs every instruction of a valid image at its specified PC. -/
theorem CodeAt.initial (image : Image) (pk : PublicKey) (m : Message)
    (bits : List Bool) (valid : image.Valid) :
    CodeAt (initialState image pk m bits) codeBase image.code := by
  have code : (initialState image pk m bits).code = loadProgram codeBase image.code := by
    simp only [initialState, MachineState.code_setReg, MachineState.code_writeBytesAsWords]
    rfl
  have bounded : 4 * image.code.length < 2 ^ 64 := by have := valid.1; omega
  intro n hn
  rw [code]
  exact loadProgram_programAt bounded n hn

/-- The straight-line instruction subset used by the verifier. -/
def linearInstruction : Instr → Bool
  | .ADDI .. | .LUI .. | .LD .. | .SD .. | .SH .. | .LHU .. | .ADD .. | .SUB .. | .MUL ..
  | .XOR .. | .XORI .. | .AND .. | .OR .. | .SLTU .. | .SLTIU .. | .SLLI .. | .SRLI .. => true
  | _ => false

/-- The memory checks imposed by the fixed machine on these instructions. -/
def memoryReady (s : MachineState) : Instr → Prop
  | .LD _ base offset | .SD base _ offset =>
      isValidDwordAccess (s.getReg base + signExtend12 offset) = true
  | .SH base _ offset | .LHU _ base offset =>
      isValidHalfwordAccess (s.getReg base + signExtend12 offset) = true
  | _ => True

theorem linear_admitted (i : Instr) (linear : linearInstruction i = true) :
    admittedInstruction i = true ∧ i ≠ .ECALL := by
  cases i <;> simp_all [linearInstruction, admittedInstruction]

theorem linear_pc (s : MachineState) (i : Instr) (linear : linearInstruction i = true) :
    (execInstrBr s i).pc = s.pc + 4 := by
  cases i <;> simp_all [linearInstruction, execInstrBr, MachineState.setPC]

theorem linear_step (s : MachineState) (i : Instr) (linear : linearInstruction i = true)
    (ready : memoryReady s i) (fetch : s.code s.pc = some i) :
    step s = some (execInstrBr s i) := by
  rw [step, fetch]
  cases i <;> simp_all [linearInstruction, memoryReady]

/-- Every instruction in a straight-line block is valid at its actual intermediate state. -/
def LinearReady : MachineState → List Instr → Prop
  | _, [] => True
  | s, i :: code => linearInstruction i = true ∧ memoryReady s i ∧
      LinearReady (execInstrBr s i) code

theorem linear_steps (s : MachineState) (code : List Instr)
    (located : CodeAt s s.pc code) (ready : LinearReady s code) :
    PureSteps code.length s (code.foldl execInstrBr s) := by
  induction code generalizing s with
  | nil => exact PureSteps.refl s
  | cons i code ih =>
    obtain ⟨linear, memory, remaining⟩ := ready
    have tail : CodeAt (execInstrBr s i) (execInstrBr s i).pc code := by
      rw [linear_pc s i linear]
      exact located.tail.code_eq code_execInstrBr
    exact PureSteps.cons located.head (linear_admitted i linear).1
      (linear_admitted i linear).2 (linear_step s i linear memory located.head)
      (ih _ tail remaining)

theorem LinearReady.append {s : MachineState} {first last : List Instr}
    (hfirst : LinearReady s first)
    (hlast : LinearReady (first.foldl execInstrBr s) last) : LinearReady s (first ++ last) := by
  induction first generalizing s with
  | nil => exact hlast
  | cons i first ih => exact ⟨hfirst.1, hfirst.2.1, ih hfirst.2.2 hlast⟩

theorem linear_fold_pc (s : MachineState) (code : List Instr) (ready : LinearReady s code) :
    (code.foldl execInstrBr s).pc = s.pc + BitVec.ofNat 64 (4 * code.length) := by
  induction code generalizing s with
  | nil => simp
  | cons i code ih =>
    rw [List.foldl_cons, ih _ ready.2.2, linear_pc _ _ ready.1]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
    change (s.pc + 4) + BitVec.ofNat 64 (4 * code.length) =
      s.pc + (BitVec.ofNat 64 (4 * code.length) + 4)
    rw [BitVec.add_assoc, BitVec.add_comm (4 : Word)]

theorem fold_code (s : MachineState) (code : List Instr) :
    (code.foldl execInstrBr s).code = s.code := by
  induction code generalizing s with
  | nil => rfl
  | cons i code ih => simpa using ih (execInstrBr s i)

end OptimalOTS.Riscv
