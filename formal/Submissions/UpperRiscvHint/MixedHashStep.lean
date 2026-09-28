import Submissions.UpperRiscvHint.MixedChainSemantics
import Submissions.UpperRiscvHint.MixedMemory
import Submissions.UpperRiscvHint.MixedDispatchArith
import Submissions.UpperRiscvHint.MixedContext

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

theorem landing0_bounds' : ∀ q : Fin 16, 15420 ≤ landing0 q ∧ landing0 q < 68000 := by
  decide +kernel

theorem landing0_bounds (q : ℕ) (hq : q < 16) : 15420 ≤ landing0 q ∧ landing0 q < 68000 :=
  landing0_bounds' ⟨q, hq⟩

theorem landing0_mod' : ∀ q : Fin 16, landing0 q % 4 = 0 := by decide +kernel

theorem landing0_mod (q : ℕ) (hq : q < 16) : landing0 q % 4 = 0 := landing0_mod' ⟨q, hq⟩

theorem lead_le (q : ℕ) : lead q ≤ 1 := by unfold lead; split_ifs <;> omega

/-- The computed jump lands on `landing0 q`, one row later for a cap pair, less the dispatch
value. -/
theorem jump_target (index : RawIdx) (q : ℕ) (hq : q < 16) (v : Word)
    (hv : v.toNat = baseLane q - dispatch index q) :
    (v + signExtend12 (imm12 (jumpImm q))) &&& ~~~(1#64) =
      W (landing0 q + 4 * lead q - dispatch index q) := by
  obtain ⟨r1, r2⟩ := jump_offset_range q hq
  have hb := baseLane_bounds q hq
  have hl := landing0_bounds q hq
  have hm := landing0_mod q hq
  have hd := dispatch_le index q
  have h1 := lead_le q
  have hv' : v = W (baseLane q - dispatch index q) := by
    apply BitVec.eq_of_toNat_eq
    rw [hv, W_toNat _ (by omega)]
  rw [hv', W_add_imm _ _ r1 r2 (by unfold jumpImm at *; omega) (by omega)]
  have e : (((baseLane q - dispatch index q : ℕ) : ℤ) + jumpImm q).toNat =
      landing0 q + 4 * lead q - dispatch index q := by
    unfold jumpImm at *
    omega
  rw [e]
  apply and_not_one_of_even
  rw [W_toNat _ (by omega)]
  unfold dispatch at *
  omega

theorem jalr_transition (s : MachineState) (rd : Reg) (i : BitVec 12)
    (fetch : s.code s.pc = some (.JALR rd .x28 i)) :
    RiscvZkvm.Rv64.step s =
      some ((s.setReg rd (s.pc + 4)).setPC ((s.getReg .x28 + signExtend12 i) &&& ~~~(1#64))) := by
  rw [RiscvZkvm.Rv64.step, fetch]
  rfl


end OptimalOTS.RiscvMixedProgram

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

/-- `x10` before chain `k`'s pointer moves: the previous chain's working address. -/
def prevInput (k : ℕ) : ℕ := if k = 0 then hashBase else work (k-1)

theorem input_delta_range' : ∀ k : Chain,
    -2048 ≤ (work k : ℤ)-prevInput k ∧ (work k : ℤ)-prevInput k < 2048 := by
  decide +kernel

theorem output_delta_range' : ∀ k : Chain,
    -2048 ≤ (outAddr k : ℤ)-work k ∧ (outAddr k : ℤ)-work k < 2048 := by
  decide +kernel

theorem work_bounds (k : Chain) : 32 ≤ work k ∧ work k + 24 < 2^62 := by
  have := wireOffset_contained k
  unfold honestViewBits at this
  rw [work_eq_view]; omega

theorem prevInput_bounds' : ∀ k : Chain, prevInput k < 2^62 := by
  decide +kernel

theorem prevInput_bounds (k : Chain) : prevInput k < 2^62 := prevInput_bounds' k

theorem input_step (s : MachineState) (k : Chain) (hp : s.getReg .x10 = W (prevInput k)) :
    s.getReg .x10 + signExtend12 (imm12 ((work k : ℤ)-prevInput k)) = W (work k) := by
  have h := input_delta_range' k
  rw [hp, W_add_imm _ _ h.1 h.2 (by omega) (prevInput_bounds k)]
  congr 1; omega

theorem output_step (k : Chain) :
    W (work k) + signExtend12 (imm12 ((outAddr k : ℤ)-work k)) = W (outAddr k) := by
  have h := output_delta_range' k
  have b := work_bounds k
  rw [W_add_imm _ _ h.1 h.2 (by omega) (by omega)]
  congr 1; omega

structure EntryEffect (a b : MachineState) (k : Chain) : Prop where
  input : b.getReg .x10 = W (work k)
  out : b.getReg .x12 = W (outAddr k)
  regs : ∀ r, r ≠ .x10 → r ≠ .x12 → b.getReg r = a.getReg r
  mem : b.mem = a.mem
  pc : b.pc = a.pc+8
  code : b.code = a.code

theorem enter_effect (s : MachineState) (k : Chain)
    (hp : s.getReg .x10 = W (prevInput k)) :
    EntryEffect s ((enter k (prevInput k)).foldl execInstrBr s) k := by
  have h1 := input_step s k hp
  have h2 := output_step k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [enter, execInstrBr, getReg_setReg_ite, h1]
  · simp [enter, execInstrBr, getReg_setReg_ite, h1, h2]
  · intro r h10 h12
    simp [enter, execInstrBr, getReg_setReg_ite, h10, h12]
  · rfl
  · change s.pc+4+4 = s.pc+8
    rw [BitVec.add_assoc]; rfl
  · rfl

theorem enter_ready (s : MachineState) (k previous : ℕ) :
    Riscv.LinearReady s (enter k previous) := by
  simp [enter, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

end OptimalOTS.RiscvMixedProgram

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest Forest.Name OracleComp

/-- A chain hash preserves the dispatch table and all fixed registers. -/
theorem Ctx.writeHash {s : MachineState} {index : RawIdx} {view : List Bool} {pk : PublicKey}
    (ctx : Ctx s index view pk) (k : Chain) (y : BitVec hashBits)
    (ho : s.getReg .x12 = W (outAddr k)) : Ctx (Riscv.writeHash s y) index view pk := by
  have b := output_bounds k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [writeHash_code]; exact ctx.null,
    ctx.code.code_eq (writeHash_code s y)⟩
  · rw [writeHash_regs]; exact ctx.pk0
  · rw [writeHash_regs]; exact ctx.pk1
  · rw [writeHash_regs]; exact ctx.call
  · intro q
    have he : (Riscv.writeHash s y).getHalfword (W (laneAddr q)) = s.getHalfword (W (laneAddr q)) := by
      simp only [MachineState.getHalfword]
      rw [writeHash_frame]
      intro j hj he
      have e := congrArg BitVec.toNat he
      have hq := q.isLt
      rw [alignToDword_toNat, ho, W_add,
        W_toNat _ (by unfold laneAddr laneBase; omega), W_toNat _ (by omega)] at e
      unfold laneAddr laneBase at e
      omega
    rw [he]; exact ctx.lanes q
  · simp only [writeHash_regs]; exact ctx.row
  · simp only [writeHash_regs]; exact ctx.base

/-- Each admitted chain input costs one oracle compression, at either state width. -/
theorem chain_blockCost (k : Chain) : blockCost (chainBits k) = 1 := by
  rcases chainBits_cases k with h | h <;> rw [h] <;> decide

/-- A chain hash is valid for the packed initial input as well as the expanded state. -/
theorem chain_hashValid (s : MachineState) (k : Chain) (base : ℕ)
    (hp : s.getReg .x10 = W base) (ho : s.getReg .x12 = W (outAddr k))
    (hn : s.getReg .x11 = W (chainBits k)) (hb : 32 ≤ base ∧ base+24 ≤ 0x78000000) :
    Riscv.hashArgumentsValid s = true := by
  have bo := output_bounds k
  have hlen := chainBits_le k
  have hmin := chainBits_ge k
  have r1 : isValidOutputRange (W base) ((chainBits k+7)/8) = true :=
    range_ok _ _ hb.1 (by omega) (by omega) (by omega)
  have r2 := hashOutput_ok (outAddr k) (by omega) (by omega) bo.2.2
  unfold Riscv.hashArgumentsValid
  rw [hp, ho, hn, W_toNat _ (by omega), r1, Bool.true_and]
  exact r2

end OptimalOTS.RiscvMixedProgram
