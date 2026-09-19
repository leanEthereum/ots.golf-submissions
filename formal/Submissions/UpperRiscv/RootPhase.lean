import Submissions.UpperRiscv.ChainPhase

/-!
# The root and the decision

The 32 chain slots with the headers between them are the 6080-bit root input; its hash, charged
twelve cycles, overwrites the last slot, and the low 128 bits of the answer are compared with
the public key saved in `x30`/`x31`.
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx) (payload : List Bool) (pk : PublicKey)

def rootLin : Code := [.ADDI .x10 .x12 (imm12 (-744)), .LUI .x11 1, .ADDI .x11 .x11 1984]

theorem root_parts : root = rootLin ++ [.ECALL] := rfl

def decisionPrefix : Code :=
  [.LD .x26 .x12 0, .XOR .x26 .x26 .x30, .LD .x28 .x12 8, .XOR .x28 .x28 .x31,
   .OR .x26 .x26 .x28, .SLTIU .x10 .x26 1, .ADDI .x5 .x0 0]

theorem decision_parts : decision = decisionPrefix ++ [.ECALL] := rfl

theorem words_equal (a b c d : Word) :
    (if ((a ^^^ b) ||| (c ^^^ d)).ult (signExtend12 1) then (1 : Word) else 0) =
      BitVec.ofNat 64 (decide (a = b ∧ c = d)).toNat := by
  have one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  rw [one]
  simp only [BitVec.ult]
  by_cases h : a = b ∧ c = d <;> simp [h]
  intro hab hcd
  exact h ⟨BitVec.eq_of_toNat_eq hab, BitVec.eq_of_toNat_eq hcd⟩

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

open scoped Classical in
/-- After the root hash, the decision block halts with the specified verdict. -/
theorem decision_refines (s : MachineState) (answer : BitVec hashBits) (fuel : ℕ)
    (x12 : s.getReg .x12 = slotW 31) (located : Riscv.CodeAt s s.pc decision)
    (hroot : MemBits s (slotW 31) answer)
    (pk0 : s.getReg .x30 = pk.extractLsb' 0 64) (pk1 : s.getReg .x31 = pk.extractLsb' 64 64)
    (bound : 8 ≤ fuel) :
    Riscv.Refines fuel s (pure (some (decide (answer.setWidth 128 = pk)))) 8 := by
  have hs := slot_bounds 31 (by norm_num)
  rw [decision_parts] at located
  have l0 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have l8 : signExtend12 (8 : BitVec 12) = W 8 := by decide
  have a0 : s.getMem (slotW 31) = answer.extractLsb' 0 64 :=
    getMem_of_memBits (by decide) (aligned_W _ hs.2.2 (by omega)) hroot
  have a1 : s.getMem (W (Flat.slotAddr 31 + 8)) = answer.extractLsb' 64 64 := by
    have hm := memBits_extract (start := 64) (len := 64) hroot (by decide) (by decide)
    rw [show (64 : ℕ) / 8 = 8 by norm_num, W_add] at hm
    have hw := getMem_of_memBits (by decide : 64 ≤ 64) (aligned_W _ (by omega) (by omega)) hm
    rw [hw]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  have ready : Riscv.LinearReady s decisionPrefix := by
    simp only [decisionPrefix, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
      execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, true_and, and_true]
    simp only [show ¬ (Reg.x12 = Reg.x26) by decide, show ¬ (Reg.x12 = Reg.x28) by decide,
      false_and, if_false, x12, l0, l8, BitVec.add_zero, W_add]
    exact ⟨dword_ok _ (by omega) (by omega) hs.2.2, dword_ok _ (by omega) (by omega) (by omega)⟩
  have rest : Riscv.CodeAt (decisionPrefix.foldl execInstrBr s)
      (decisionPrefix.foldl execInstrBr s).pc [.ECALL] := by
    rw [Riscv.linear_fold_pc _ _ ready]
    exact located.append_right.code_eq (Riscv.fold_code _ _)
  have result : (decisionPrefix.foldl execInstrBr s).getReg .x10 =
      BitVec.ofNat 64 (decide (answer.setWidth 128 = pk)).toNat := by
    simp only [decisionPrefix, List.foldl_cons, List.foldl_nil, execInstrBr,
      MachineState.getReg_setPC, MachineState.getMem_setPC, MachineState.getMem_setReg,
      getReg_setReg_ite]
    simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
      show ¬ (Reg.x10 = Reg.x26) by decide, show ¬ (Reg.x10 = Reg.x28) by decide,
      show ¬ (Reg.x26 = Reg.x28) by decide, show ¬ (Reg.x28 = Reg.x26) by decide,
      show ¬ (Reg.x30 = Reg.x26) by decide, show ¬ (Reg.x31 = Reg.x28) by decide,
      show ¬ (Reg.x31 = Reg.x26) by decide, show ¬ (Reg.x12 = Reg.x26) by decide,
      show ¬ (Reg.x12 = Reg.x28) by decide, false_and, if_false, x12, l0, l8, BitVec.add_zero,
      W_add, pk0, pk1]
    rw [a0, a1, words_equal]
    have e0 : (answer.setWidth 128).extractLsb' 0 64 = answer.extractLsb' 0 64 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]; omega
    have e1 : (answer.setWidth 128).extractLsb' 64 64 = answer.extractLsb' 64 64 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]; omega
    have key : (answer.extractLsb' 0 64 = pk.extractLsb' 0 64 ∧
        answer.extractLsb' 64 64 = pk.extractLsb' 64 64) ↔ answer.setWidth 128 = pk := by
      have h := split128_equal (answer.setWidth 128) pk
      rw [e0, e1] at h
      exact h
    rw [decide_eq_decide.mpr key]
  have call : (decisionPrefix.foldl execInstrBr s).getReg .x5 = 0 := by
    simp only [decisionPrefix, List.foldl_cons, List.foldl_nil, execInstrBr,
      MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [getReg_x0']
    simp
    decide
  rw [show fuel = decisionPrefix.length + ((fuel - decisionPrefix.length - 1) + 1) by
      simp [decisionPrefix]; omega,
    show (8 : ℕ) = decisionPrefix.length + 1 by rfl]
  apply Riscv.Refines.linear _ located.append_left ready
  exact Riscv.Refines.halt _ rest.head call result

theorem lui_literal :
    (((BitVec.ofNat 20 1).zeroExtend 32 <<< 12).signExtend 64 : Word) + signExtend12 1984 = 6080 := by
  decide

theorem rootCat_eq (c : Fin 32 → BitVec 128) :
    rootCat c = (rootAcc (topFun c) 31).cast (by norm_num) := rfl

open scoped Classical in
/-- The root hash over the 32 slots and the decision, at 23 cycles. -/
theorem rootDecision_refines (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index payload pk s x 32)
    (located : Riscv.CodeAt s s.pc (root ++ decision)) (bound : 12 ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload [rc, rh] x 4096 >>= fun r =>
        pure (some (decide ((r.1 rh.fin).setWidth 128 = pk)))) 23 := by
  have hs := slot_bounds 31 (by norm_num)
  have hs0 := slot_bounds 0 (by norm_num)
  simp only [runNodes', bind_assoc, pure_bind, cursorStep_rc, cursorStep_rh, Prod.mk.eta]
  set x' := Function.update x rc.fin
    ((rootCat fun k => Forest.trunc (x (cv k 14).fin)).cast (graph_len_fin rc).symm) with hx'
  have value : x' rc.fin = (rootCat fun k => Forest.trunc (x (cv k 14).fin)).cast
      (graph_len_fin rc).symm := by
    rw [hx', Function.update_self]
  have x12 : s.getReg .x12 = slotW 31 := by rw [inv.slot]; rfl
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
  have w10 : w.getReg .x10 = W Flat.slotBase := by
    rw [hw]
    simp only [rootLin, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp only [show ¬ (Reg.x10 = Reg.x11) by decide, false_and, if_false, true_and, ne_eq,
      reduceCtorEq, not_false_eq_true, if_true, x12]
    rw [W_add_imm _ _ (by norm_num) (by norm_num) (by omega) (by omega)]
    congr 1
  have w11 : w.getReg .x11 = 6080 := by
    rw [hw]
    simp only [rootLin, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true]
    exact lui_literal
  have wMem : ∀ addr, w.getMem addr = s.getMem addr := by
    intro addr; rw [hw]; simp [rootLin, execInstrBr]
  have wPc : w.pc = s.pc + BitVec.ofNat 64 (4 * rootLin.length) := Riscv.linear_fold_pc s _ ready
  have wCode : Riscv.CodeAt w w.pc ([Instr.ECALL] ++ decision) := by
    rw [wPc]; exact located.append_right.code_eq (Riscv.fold_code s _)
  have wCodeEq : w.code = s.code := Riscv.fold_code s _
  have wFetch : w.code w.pc = some .ECALL := wCode.head
  have wCall : w.getReg .x5 = Riscv.hashCall := by
    rw [wRegs .x5 (by decide) (by decide)]; exact inv.ctx.call
  have w12 : w.getReg .x12 = slotW 31 := by rw [wRegs .x12 (by decide) (by decide), x12]
  have wValid : Riscv.hashArgumentsValid w = true := by
    have r1 : isValidOutputRange (W Flat.slotBase) 760 = true :=
      range_ok _ _ (by norm_num [Flat.slotBase]) (by norm_num [Flat.slotBase]) (by norm_num)
        (by norm_num)
    have r2 := hashOutput_ok (Flat.slotAddr 31) (by omega) (by omega) hs.2.2
    have e : ((6080 : Word).toNat + 7) / 8 = 760 := rfl
    unfold Riscv.hashArgumentsValid
    rw [w10, w11, w12, e, r1, Bool.true_and]
    exact r2
  have wValue : MemBits w (W Flat.slotBase)
      ((rootCat fun k => Forest.trunc (x' (cv k 14).fin))) := by
    have h := inv.done (by norm_num)
    rw [rootCat_eq]
    apply (memBits_cast _ _ _ _).mpr
    apply memBits_of_mem_eq (show w.mem = s.mem from funext fun a => wMem a)
    have e : topFun (fun k => Forest.trunc (x' (cv k 14).fin)) = topFun (tops x) := by
      funext j
      unfold topFun tops
      split_ifs with hj
      · show Forest.trunc (x' (cv ⟨j, hj⟩ 14).fin) = Forest.trunc (x (cv ⟨j, hj⟩ 14).fin)
        rw [hx', Function.update_of_ne (fin_ne_of_ne (by simp))]
      · rfl
    rw [e]
    exact h
  have inner : (fun k => Forest.trunc (x' (cv k 14).fin)) = fun k => Forest.trunc (x (cv k 14).fin) := by
    funext k
    rw [hx', Function.update_of_ne (fin_ne_of_ne (by simp))]
  have wInput : Riscv.hashInput w = ⟨graph.len rc.fin, x' rc.fin⟩ := by
    apply hashInput_of_memBits w10 (by rw [w11, graph_len_fin]; rfl)
    rw [value]
    apply (memBits_cast _ _ _ _).mpr
    rw [← inner]
    exact wValue
  have blocks : blockCost (graph.len rc.fin) = 12 := by
    rw [graph_len_fin]; show blockCost 6080 = 12; decide
  rw [show (23 : ℕ) = rootLin.length + (12 + 8) by rfl,
    show fuel = rootLin.length + ((fuel - rootLin.length - 1) + 1) by simp [rootLin]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hw]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  have step := Riscv.Refines.hash (fuel := fuel - rootLin.length - 1) wFetch wCall wValid
    (k := fun y => pure (some (decide (((Function.update x' rh.fin
      (y.cast (graph_len_fin rh).symm)) rh.fin).setWidth 128 = pk))))
    (c := 8) ?_
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
  have vRoot : MemBits v (slotW 31) y := by
    have h := writeHash_memBits w y (by rw [w12]; exact aligned_W _ hs.2.2 (by omega))
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
  simp [rootLin] at bound ⊢
  omega

end OptimalOTS.RiscvUpperProgram
