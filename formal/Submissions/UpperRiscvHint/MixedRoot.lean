import Submissions.UpperRiscvHint.MixedHashStep
import Submissions.UpperRiscvHint.MixedIndexPhase

/-!
# The root and the decision

The 888 bytes from the free chain's cell are the 7104-bit root input (`rootCat`). Its hash,
charged fourteen cycles, is written into the last chain's answer buffer, and the low 128 bits of
the answer are compared with the public key saved in `x30`/`x31`, whose high word has bit 0
flipped. The root length is the free base in `x1` plus 960. The decision costs five cycles on every
completed path.
-/

namespace OptimalOTS.RiscvMixedProgram

open Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : RawIdx) (payload : List Bool) (view : List Bool) (pk : PublicKey)

def rootLin : Code :=
  [.ADDI .x10 .x10 (imm12 ((outAddr 0 : ℤ) - work 32)),
   .ADDI .x11 .x1 (imm12 (7104 - (freeBase : ℤ)))]

/-- Where the root answer is written: the answer buffer of the last chain. -/
def rootOut : ℕ := outAddr 32

theorem root_parts : root = rootLin ++ [.ECALL] := rfl

/-- The machine's verdict on a root: accept when the low words match and the high words differ
exactly in bit 0, reject when both words match, and otherwise trap. -/
def decisionOutcome (r : BitVec 128) (pk : PublicKey) : Option Bool :=
  if r.extractLsb' 0 64 = pk.extractLsb' 0 64 then
    if r.extractLsb' 64 64 ^^^ pk.extractLsb' 64 64 = 1 then some true
    else if r.extractLsb' 64 64 = pk.extractLsb' 64 64 then some false else none
  else none

/-- The two root words and their differences from the stored key. -/
def decisionLoads : Code :=
  [.LD .x26 .x12 0, .LD .x27 .x12 8, .XOR .x5 .x26 .x30, .XOR .x10 .x27 .x31]

theorem decision_parts : decision = decisionLoads ++ ([.ECALL] ++ [.JALR .x0 .x0 0]) := rfl

theorem split128_equal (a b : BitVec 128) :
    a.extractLsb' 0 64 = b.extractLsb' 0 64 ∧
      a.extractLsb' 64 64 = b.extractLsb' 64 64 ↔ a = b := by
  constructor
  · rintro ⟨lo, hi⟩
    calc
      a = a.extractLsb' 64 64 ++ a.extractLsb' 0 64 :=
        (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := a)).symm
      _ = b.extractLsb' 64 64 ++ b.extractLsb' 0 64 := by rw [lo, hi]
      _ = b := BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := b)
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- After the root hash, the decision halts with `decisionOutcome` or traps, within five cycles on
every completed path. On a low-word difference of 1 the `ECALL` hashes arbitrary memory before
the `JALR` traps; that query is a pruned suffix. -/
theorem decision_refines (s : MachineState) (answer : BitVec hashBits) (fuel : ℕ)
    (x12 : s.getReg .x12 = W rootOut) (located : Riscv.CodeAt s s.pc decision)
    (hroot : MemBits s (W rootOut) answer)
    (pk0 : s.getReg .x30 = pk.extractLsb' 0 64) (pk1 : s.getReg .x31 = pk.extractLsb' 64 64)
    (null : s.code 0 = none) (bound : 5 ≤ fuel) :
    Riscv.Refines fuel s (pure (decisionOutcome (answer.setWidth 128) pk)) 5 := by
  have hs : 32 ≤ rootOut ∧ rootOut + 32 ≤ 0x78000000 ∧ rootOut % 8 = 0 := by
    norm_num [rootOut, outAddr]
  rw [decision_parts] at located
  have l0 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have l8 : signExtend12 (8 : BitVec 12) = W 8 := by decide
  have l0' : signExtend12 0#12 = 0#64 := by decide
  have l8' : signExtend12 8#12 = W 8 := by decide
  have a0 : s.getMem (W rootOut) = answer.extractLsb' 0 64 :=
    getMem_of_memBits (by decide) (aligned_W _ hs.2.2 (by omega)) hroot
  have a1 : s.getMem (W (rootOut + 8)) = answer.extractLsb' 64 64 := by
    have hm := memBits_extract (start := 64) (len := 64) hroot (by decide) (by decide)
    rw [show (64 : ℕ) / 8 = 8 by norm_num, W_add] at hm
    have hw := getMem_of_memBits (by decide : 64 ≤ 64) (aligned_W _ (by omega) (by omega)) hm
    rw [hw]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  have e0 : (answer.setWidth 128).extractLsb' 0 64 = answer.extractLsb' 0 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]; omega
  have e1 : (answer.setWidth 128).extractLsb' 64 64 = answer.extractLsb' 64 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]; omega
  have ready : Riscv.LinearReady s decisionLoads := by
    simp only [decisionLoads, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
      execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, true_and, and_true]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, if_false, false_and, x12, l0, l8,
      BitVec.add_zero, W_add, show ¬ (Reg.x12 = Reg.x26) by decide]
    exact ⟨dword_ok _ (by omega) (by omega) hs.2.2, dword_ok _ (by omega) (by omega) (by omega)⟩
  set w := decisionLoads.foldl execInstrBr s with hw
  have w5 : w.getReg .x5 = answer.extractLsb' 0 64 ^^^ pk.extractLsb' 0 64 := by
    rw [hw]
    simp only [decisionLoads, List.foldl_cons, List.foldl_nil, execInstrBr,
      MachineState.getReg_setPC, getReg_setReg_ite, MachineState.getMem_setPC,
      MachineState.getMem_setReg]
    simp [x12, l0', a0, pk0]
  have w10 : w.getReg .x10 = answer.extractLsb' 64 64 ^^^ pk.extractLsb' 64 64 := by
    rw [hw]
    simp only [decisionLoads, List.foldl_cons, List.foldl_nil, execInstrBr,
      MachineState.getReg_setPC, getReg_setReg_ite, MachineState.getMem_setPC,
      MachineState.getMem_setReg]
    simp [x12, l8', W_add, a1, pk1]
  have wpc : w.pc = s.pc + BitVec.ofNat 64 (4 * decisionLoads.length) :=
    Riscv.linear_fold_pc s _ ready
  have wcode : w.code = s.code := Riscv.fold_code s _
  have loc : Riscv.CodeAt w w.pc ([.ECALL] ++ [.JALR .x0 .x0 0]) := by
    rw [wpc]; exact located.append_right.code_eq wcode
  have fetch : w.code w.pc = some .ECALL := loc.head
  rw [show fuel = decisionLoads.length + ((fuel - 5) + 1) by simp [decisionLoads]; omega,
    show (5 : ℕ) = decisionLoads.length + 1 by rfl]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hw]
  unfold decisionOutcome
  simp only [e0, e1]
  by_cases lo : answer.extractLsb' 0 64 = pk.extractLsb' 0 64
  · have h5 : w.getReg .x5 = 0 := by rw [w5, lo, BitVec.xor_self]; rfl
    rw [if_pos lo]
    by_cases one : answer.extractLsb' 64 64 ^^^ pk.extractLsb' 64 64 = 1
    · rw [if_pos one]
      exact Riscv.Refines.halt true fetch h5 (by rw [w10, one]; rfl)
    · rw [if_neg one]
      by_cases zero : answer.extractLsb' 64 64 = pk.extractLsb' 64 64
      · rw [if_pos zero]
        exact Riscv.Refines.halt false fetch h5 (by rw [w10, zero, BitVec.xor_self]; rfl)
      · rw [if_neg zero]
        apply Riscv.Refines.trap
        apply Riscv.execute_badHalt _ _ fetch h5 _ (by rw [w10]; exact one)
        rw [w10]
        intro h
        apply zero
        have := congrArg (· ^^^ pk.extractLsb' 64 64) h
        simpa [BitVec.xor_assoc] using this
  · rw [if_neg lo]
    have h0 : w.getReg .x5 ≠ 0 := by
      rw [w5]
      intro h
      apply lo
      have := congrArg (· ^^^ pk.extractLsb' 0 64) h
      simpa [BitVec.xor_assoc] using this
    by_cases call : w.getReg .x5 = Riscv.hashCall
    · apply Riscv.Refines.junkHash fetch call
      intro y
      apply Riscv.execute_jumpNull
      · rw [writeHash_code, writeHash_pc]
        exact loc.tail.head
      · rw [writeHash_code, wcode]; exact null
    · exact Riscv.Refines.trap (Riscv.execute_badCall _ _ fetch h0 call)

/-- Machine state at the root after all chains have completed. -/
structure RootInv (s : MachineState) (x : graph.Assignment) : Prop where
  ctx : Ctx s index view pk
  input : s.getReg .x10 = W (work 32)
  out : s.getReg .x12 = W rootOut
  root : MemBits s (W regionAddr) (rootCat (tops x))

theorem root_memBits (s : MachineState) (x : graph.Assignment)
    (inv : RootInv index view pk s x) : MemBits s (W regionAddr) (rootCat (tops x)) := inv.root

/-- The root hash over the region and the decision, at 21 cycles. -/
theorem rootDecision_refines (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : RootInv index view pk s x)
    (located : Riscv.CodeAt s s.pc (root ++ decision)) (bound : 8 ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload [rc, rh] x 5376 >>= fun r =>
        pure (decisionOutcome ((r.1 rh.fin).setWidth 128) pk)) 21 := by
  have hd : 32 ≤ rootOut ∧ rootOut + 32 ≤ 0x78000000 ∧ rootOut % 8 = 0 := by
    norm_num [rootOut, outAddr]
  simp only [runNodes', bind_assoc, pure_bind, cursorStep_rc, cursorStep_rh, Prod.mk.eta]
  set x' := Function.update x rc.fin
    ((rootCat fun k => (x (top k).fin).cast (lenF_fin _)).cast (graph_len_fin rc).symm) with hx'
  have value : x' rc.fin = (rootCat (tops x)).cast (graph_len_fin rc).symm := by
    rw [hx', Function.update_self]
    rfl
  -- the straight-line part
  have ready : Riscv.LinearReady s rootLin := by
    simp [rootLin, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  rw [root_parts, List.append_assoc] at located
  set w := rootLin.foldl execInstrBr s with hw
  have wRegs : ∀ r, r ≠ .x10 → r ≠ .x11 → w.getReg r = s.getReg r := by
    intro r h10 h11
    rw [hw]
    simp only [rootLin, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp [Ne.symm h10, Ne.symm h11, h10, h11]
  have s10 : s.getReg .x10 = W (work 32) := inv.input
  have w10 : w.getReg .x10 = W regionAddr := by
    rw [hw]
    simp only [rootLin, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp only [show ¬ (Reg.x10 = Reg.x11) by decide, false_and, if_false, true_and, ne_eq,
      reduceCtorEq, not_false_eq_true, if_true, s10]
    rw [W_add_imm _ _ (by norm_num [outAddr, work, wireByte])
      (by norm_num [outAddr, work, wireByte]) (by norm_num [outAddr, work, wireByte])
      (by norm_num [work, wireByte])]
    rfl
  have w11 : w.getReg .x11 = 7104 := by
    rw [hw]
    simp only [rootLin, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, false_and, if_false,
      show ¬ (Reg.x11 = Reg.x10) by decide, show ¬ (Reg.x10 = Reg.x11) by decide,
      show ¬ (Reg.x1 = Reg.x10) by decide]
    rw [inv.ctx.base]
    decide
  have w12 : w.getReg .x12 = W rootOut := by
    rw [wRegs .x12 (by decide) (by decide)]
    exact inv.out
  have wMem : ∀ addr, w.getMem addr = s.getMem addr := by
    intro addr; rw [hw]; simp [rootLin, execInstrBr]
  have wPc : w.pc = s.pc + BitVec.ofNat 64 (4 * rootLin.length) := Riscv.linear_fold_pc s _ ready
  have wCode : Riscv.CodeAt w w.pc ([Instr.ECALL] ++ decision) := by
    rw [wPc]; exact located.append_right.code_eq (Riscv.fold_code s _)
  have wCodeEq : w.code = s.code := Riscv.fold_code s _
  have wFetch : w.code w.pc = some .ECALL := wCode.head
  have wCall : w.getReg .x5 = Riscv.hashCall := by
    rw [wRegs .x5 (by decide) (by decide)]; exact inv.ctx.call
  have wValid : Riscv.hashArgumentsValid w = true := by
    have r1 : isValidOutputRange (W regionAddr) 888 = true :=
      range_ok _ _ (by norm_num [regionAddr]) (by norm_num [regionAddr]) (by norm_num)
        (by norm_num)
    have r2 := hashOutput_ok rootOut hd.1 hd.2.1 hd.2.2
    have e : ((7104 : Word).toNat + 7) / 8 = 888 := rfl
    unfold Riscv.hashArgumentsValid
    rw [w10, w11, w12, e, r1, Bool.true_and]
    exact r2
  have wValue : MemBits w (W regionAddr) (rootCat (tops x)) :=
    memBits_of_mem_eq (show w.mem = s.mem from funext fun a => wMem a)
      (root_memBits index view pk s x inv)
  have wInput : Riscv.hashInput w = ⟨graph.len rc.fin, x' rc.fin⟩ := by
    apply hashInput_of_memBits w10 (by rw [w11, graph_len_fin]; rfl)
    rw [value]
    apply (memBits_cast _ _ _ _).mpr
    exact wValue
  have blocks : blockCost (graph.len rc.fin) = 14 := by
    rw [graph_len_fin]; show blockCost 7104 = 14; decide
  rw [show (21 : ℕ) = rootLin.length + (14 + 5) by rfl,
    show fuel = rootLin.length + ((fuel - rootLin.length - 1) + 1) by simp [rootLin]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hw]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  have step := Riscv.Refines.hash (fuel := fuel - rootLin.length - 1) wFetch wCall wValid
    (k := fun y => pure (decisionOutcome (((Function.update x' rh.fin
      (y.cast (graph_len_fin rh).symm)) rh.fin).setWidth 128) pk))
    (c := 5) ?_
  · rw [wInput, blocks] at step
    exact step
  intro y
  set v := Riscv.writeHash w y with hv
  have vRegs : ∀ r, v.getReg r = w.getReg r := fun r => by rw [hv, writeHash_regs]
  have vPc : v.pc = w.pc + 4 := by rw [hv, writeHash_pc]
  have vCode : v.code = s.code := by rw [hv, writeHash_code, wCodeEq]
  have vLocated : Riscv.CodeAt v v.pc decision := by
    rw [vPc]
    exact wCode.tail.code_eq (by rw [vCode, wCodeEq])
  have vRoot : MemBits v (W rootOut) y := by
    have h := writeHash_memBits w y (by rw [w12]; exact aligned_W _ hd.2.2 (by norm_num [rootOut, outAddr]))
    rw [w12] at h
    exact h
  rw [Function.update_self]
  have cast_setWidth :
      ((y.cast (graph_len_fin rh).symm : BitVec (graph.len rh.fin)).setWidth 128) = y.setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    rfl
  rw [cast_setWidth]
  apply decision_refines pk v y _ (by rw [vRegs, w12]) vLocated vRoot
    (by rw [vRegs, wRegs .x30 (by decide) (by decide)]; exact inv.ctx.pk0)
    (by rw [vRegs, wRegs .x31 (by decide) (by decide)]; exact inv.ctx.pk1)
    (by rw [vCode]; exact inv.ctx.null)
  show 5 ≤ fuel - rootLin.length - 1
  have h3 : rootLin.length = 2 := rfl
  rw [h3]
  omega

end OptimalOTS.RiscvMixedProgram
