import Submissions.UpperRiscv.MixedIndexPhase

/-!
# The root and the decision

The 832 bytes from `regionAddr` hold the 826-byte root region and six more bytes. The root
query reads their first `a3 + 1144` bits (6608 for a full signature, at most thirteen blocks), and
its answer is written into the last chain's answer buffer. The low 128 bits of the answer are
compared with the public key saved in `x30`/`x31`; each mismatching word branches to a rejection
after the accepting HALT. On a match the verdict is `a3 < 5465`, the bound held in `x1`, so a
signature longer than 5464 bits is rejected. The decision costs seven cycles on every path.
-/

namespace OptimalOTS.RiscvMixedProgram

open Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] pkBits

variable (index : RawIdx) (v : ℕ) (pk : PublicKey) {a : ℕ}

theorem writeHash_regs (w : MachineState) (a : BitVec hashBits) (r : Reg) :
    (Riscv.writeHash w a).getReg r = w.getReg r := by
  simp [Riscv.writeHash]

theorem writeHash_code (w : MachineState) (a : BitVec hashBits) :
    (Riscv.writeHash w a).code = w.code := by
  simp [Riscv.writeHash]

theorem writeHash_pc (w : MachineState) (a : BitVec hashBits) :
    (Riscv.writeHash w a).pc = w.pc + 4 := rfl

def rootLin : Code := [.ADDI .x10 .x10 (imm12 ((regionAddr : ℤ) - work 32)), .ADDI .x11 .x13 1144]

/-- Where the root answer is written: the answer buffer of the last chain. -/
def rootOut : ℕ := outAddr 32

theorem root_parts : root = rootLin ++ [.ECALL] := rfl

/-- The tail of the decision after both words match: the length verdict and the HALT call. -/
def acceptTail : Code := [.SLTU .x10 .x13 .x1, .ADDI .x5 .x0 0]

theorem decision_parts : decision =
    [.LD .x26 .x12 0] ++ ([.BNE .x26 .x30 24] ++ ([.LD .x28 .x12 8] ++
      ([.BNE .x28 .x31 16] ++ (acceptTail ++ ([.ECALL] ++ reject))))) := rfl

/-- A `BNE` falls through on equal registers and otherwise jumps by its offset. -/
theorem bne_transition (s : MachineState) (r r' : Reg) (off : BitVec 13) (t : Word)
    (hsign : signExtend13 off = t) (fetch : s.code s.pc = some (.BNE r r' off)) :
    step s = some (s.setPC (s.pc + if s.getReg r = s.getReg r' then 4 else t)) := by
  rw [RiscvZkvm.Rv64.step, fetch]
  simp only [execInstrBr, hsign]
  by_cases h : s.getReg r = s.getReg r' <;> simp [h]

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

/-- `SLTU` of the length register against the bound is the length verdict. -/
theorem sltu_bound (a : ℕ) (ha : a ≤ 5505) :
    (if BitVec.ult (W a) (W 5465) then (1 : Word) else 0) =
      BitVec.ofNat 64 (decide (a < 5465)).toNat := by
  have e : BitVec.ult (W a) (W 5465) = decide (a < 5465) := by
    simp only [BitVec.ult, W, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e]
  by_cases h : a < 5465 <;> simp [h]

/-- After the root hash, the decision block halts with the specified verdict, within seven
cycles on every path: the accepting path runs all seven instructions, and a mismatch in the low
or high word rejects after five or seven. -/
theorem decision_refines (s : MachineState) (answer : BitVec hashBits) (fuel : ℕ)
    (x12 : s.getReg .x12 = W rootOut) (located : Riscv.CodeAt s s.pc decision)
    (hroot : MemBits s (W rootOut) answer)
    (pk0 : s.getReg .x30 = pk.extractLsb' 0 64) (pk1 : s.getReg .x31 = pk.extractLsb' 64 64)
    (x13 : s.getReg .x13 = W a) (x1 : s.getReg .x1 = W 5465) (ha : a ≤ 5505)
    (bound : 7 ≤ fuel) :
    Riscv.Refines fuel s
      (pure (some (decide (answer.setWidth 128 = pk) && decide (a < 5465)))) 7 := by
  have hs : 32 ≤ rootOut ∧ rootOut + 32 ≤ 0x78000000 ∧ rootOut % 8 = 0 := by
    decide
  rw [decision_parts] at located
  have l0 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have l8 : signExtend12 (8 : BitVec 12) = W 8 := by decide
  have b24 : signExtend13 (24 : BitVec 13) = 24 := by decide
  have b16 : signExtend13 (16 : BitVec 13) = 16 := by decide
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
  -- the verdict in terms of the two words
  have e0 : (answer.setWidth 128).extractLsb' 0 64 = answer.extractLsb' 0 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]; omega
  have e1 : (answer.setWidth 128).extractLsb' 64 64 = answer.extractLsb' 64 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]; omega
  have key : (answer.extractLsb' 0 64 = pk.extractLsb' 0 64 ∧
      answer.extractLsb' 64 64 = pk.extractLsb' 64 64) ↔ answer.setWidth 128 = pk := by
    have h := split128_equal (answer.setWidth 128) pk
    rw [e0, e1] at h
    exact h
  -- the first load
  have ready1 : Riscv.LinearReady s [.LD .x26 .x12 0] := by
    simp only [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, execInstrBr,
      MachineState.getReg_setPC, getReg_setReg_ite, true_and, and_true]
    simp only [x12, l0, BitVec.add_zero]
    exact dword_ok _ (by omega) (by omega) hs.2.2
  set s1 := [Instr.LD .x26 .x12 0].foldl execInstrBr s with hs1
  have s1_regs : ∀ r, r ≠ .x26 → s1.getReg r = s.getReg r := by
    intro r hr
    rw [hs1]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp [hr, Ne.symm hr]
  have s1_26 : s1.getReg .x26 = answer.extractLsb' 0 64 := by
    rw [hs1]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, false_and, if_false,
      show ¬ (Reg.x12 = Reg.x26) by decide, x12, l0, BitVec.add_zero]
    exact a0
  have s1_mem : ∀ a, s1.getMem a = s.getMem a := by
    intro a; rw [hs1]; simp [execInstrBr]
  have s1_code : s1.code = s.code := Riscv.fold_code s _
  have s1_pc : s1.pc = s.pc + 4 := by
    have h := Riscv.linear_fold_pc s _ ready1
    rw [← hs1] at h
    exact h
  have loc1 : Riscv.CodeAt s1 s1.pc ([.BNE .x26 .x30 24] ++ ([.LD .x28 .x12 8] ++
      ([.BNE .x28 .x31 16] ++ (acceptTail ++ ([.ECALL] ++ reject))))) := by
    have h := located.append_right
    rw [show BitVec.ofNat 64 (4 * [Instr.LD .x26 .x12 0].length) = 4 from rfl, ← s1_pc] at h
    exact h.code_eq s1_code
  rw [show fuel = [Instr.LD .x26 .x12 0].length + (fuel - 1) by simp; omega,
    show (7 : ℕ) = [Instr.LD .x26 .x12 0].length + 6 by rfl]
  apply Riscv.Refines.linear _ located.append_left ready1
  rw [← hs1]
  -- the first branch
  have fetch1 : s1.code s1.pc = some (.BNE .x26 .x30 24) := loc1.head
  have tr1 := bne_transition s1 .x26 .x30 24 24 b24 fetch1
  rw [show fuel - 1 = (fuel - 2) + 1 by omega]
  by_cases eq0 : answer.extractLsb' 0 64 = pk.extractLsb' 0 64
  · have hr : s1.getReg .x26 = s1.getReg .x30 := by
      rw [s1_26, s1_regs .x30 (by decide), pk0, eq0]
    rw [if_pos hr] at tr1
    rw [show (6 : ℕ) = 5 + 1 by rfl]
    apply Riscv.Refines.branch fetch1 rfl (fun h => nomatch h) tr1
    -- the second load, from the fall-through state
    set s2 := s1.setPC (s1.pc + 4) with hs2
    have s2_regs : ∀ r, s2.getReg r = s1.getReg r := fun r => by rw [hs2]; rfl
    have s2_mem : ∀ a, s2.getMem a = s1.getMem a := fun a => by rw [hs2]; rfl
    have s2_code : s2.code = s1.code := by rw [hs2]; rfl
    have loc2 : Riscv.CodeAt s2 s2.pc ([.LD .x28 .x12 8] ++
        ([.BNE .x28 .x31 16] ++ (acceptTail ++ ([.ECALL] ++ reject)))) := loc1.tail
    have ready2 : Riscv.LinearReady s2 [.LD .x28 .x12 8] := by
      simp only [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, execInstrBr,
        MachineState.getReg_setPC, getReg_setReg_ite, true_and, and_true]
      simp only [s2_regs, s1_regs .x12 (by decide), x12, l8, W_add]
      exact dword_ok _ (by omega) (by omega) (by omega)
    set s3 := [Instr.LD .x28 .x12 8].foldl execInstrBr s2 with hs3
    have s3_regs : ∀ r, r ≠ .x28 → s3.getReg r = s2.getReg r := by
      intro r hr
      rw [hs3]
      simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ite]
      simp [hr, Ne.symm hr]
    have s3_28 : s3.getReg .x28 = answer.extractLsb' 64 64 := by
      rw [hs3]
      simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ite]
      simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, false_and, if_false,
        show ¬ (Reg.x12 = Reg.x28) by decide]
      rw [s2_regs, s1_regs .x12 (by decide), x12, l8, W_add, s2_mem, s1_mem, a1]
    have s3_code : s3.code = s2.code := Riscv.fold_code s2 _
    have s3_pc : s3.pc = s2.pc + 4 := by
      have h := Riscv.linear_fold_pc s2 _ ready2
      rw [← hs3] at h
      exact h
    have loc3 : Riscv.CodeAt s3 s3.pc ([.BNE .x28 .x31 16] ++ (acceptTail ++ ([.ECALL] ++ reject))) := by
      have h := loc2.append_right
      rw [show BitVec.ofNat 64 (4 * [Instr.LD .x28 .x12 8].length) = 4 from rfl, ← s3_pc] at h
      exact h.code_eq s3_code
    rw [show fuel - 2 = [Instr.LD .x28 .x12 8].length + (fuel - 3) by simp; omega,
      show (5 : ℕ) = [Instr.LD .x28 .x12 8].length + 4 by rfl]
    apply Riscv.Refines.linear _ loc2.append_left ready2
    rw [← hs3]
    -- the second branch
    have fetch3 : s3.code s3.pc = some (.BNE .x28 .x31 16) := loc3.head
    have tr3 := bne_transition s3 .x28 .x31 16 16 b16 fetch3
    rw [show fuel - 3 = (fuel - 4) + 1 by omega]
    by_cases eq1 : answer.extractLsb' 64 64 = pk.extractLsb' 64 64
    · have hr3 : s3.getReg .x28 = s3.getReg .x31 := by
        rw [s3_28, s3_regs .x31 (by decide), s2_regs, s1_regs .x31 (by decide), pk1, eq1]
      rw [if_pos hr3] at tr3
      rw [show (4 : ℕ) = 3 + 1 by rfl]
      apply Riscv.Refines.branch fetch3 rfl (fun h => nomatch h) tr3
      -- the accepting tail
      set s4 := s3.setPC (s3.pc + 4) with hs4
      have loc4 : Riscv.CodeAt s4 s4.pc (acceptTail ++ ([.ECALL] ++ reject)) := loc3.tail
      have ready4 : Riscv.LinearReady s4 acceptTail := by
        simp [acceptTail, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
      set s5 := acceptTail.foldl execInstrBr s4 with hs5
      have s5_pc : s5.pc = s4.pc + 8 := by
        have h := Riscv.linear_fold_pc s4 _ ready4
        rw [← hs5] at h
        exact h
      have loc5 : Riscv.CodeAt s5 s5.pc ([.ECALL] ++ reject) := by
        have h := loc4.append_right
        rw [show BitVec.ofNat 64 (4 * acceptTail.length) = 8 from rfl, ← s5_pc] at h
        exact h.code_eq (Riscv.fold_code s4 _)
      have r4 : ∀ r, r ≠ .x26 → r ≠ .x28 → s4.getReg r = s.getReg r := by
        intro r h26 h28
        rw [hs4, MachineState.getReg_setPC, s3_regs r h28, s2_regs, s1_regs r h26]
      have s5_10 : s5.getReg .x10 = BitVec.ofNat 64 (decide (a < 5465)).toNat := by
        rw [hs5]
        simp only [acceptTail, List.foldl_cons, List.foldl_nil, execInstrBr,
          MachineState.getReg_setPC, getReg_setReg_ite]
        simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
          false_and, if_false]
        rw [r4 .x13 (by decide) (by decide), r4 .x1 (by decide) (by decide), x13, x1]
        exact sltu_bound a ha
      have s5_5 : s5.getReg .x5 = 0 := by
        rw [hs5]
        simp only [acceptTail, List.foldl_cons, List.foldl_nil, execInstrBr,
          MachineState.getReg_setPC, getReg_setReg_ite]
        simp only [getReg_x0']
        simp
        decide
      have spec : decide (answer.setWidth 128 = pk) = true := decide_eq_true (key.mp ⟨eq0, eq1⟩)
      rw [spec, Bool.true_and,
        show fuel - 4 = acceptTail.length + ((fuel - 7) + 1) by simp [acceptTail]; omega,
        show (3 : ℕ) = acceptTail.length + 1 by rfl]
      apply Riscv.Refines.linear _ loc4.append_left ready4
      rw [← hs5]
      exact Riscv.Refines.halt (decide (a < 5465)) loc5.head s5_5 s5_10
    · have hr3 : s3.getReg .x28 ≠ s3.getReg .x31 := by
        rw [s3_28, s3_regs .x31 (by decide), s2_regs, s1_regs .x31 (by decide), pk1]; exact eq1
      rw [if_neg hr3] at tr3
      have spec : decide (answer.setWidth 128 = pk) = false := by
        rw [decide_eq_false_iff_not]
        intro h
        exact eq1 (key.mpr h).2
      rw [spec, Bool.false_and]
      have locR : Riscv.CodeAt (s3.setPC (s3.pc + 16)) (s3.setPC (s3.pc + 16)).pc reject := by
        have h : Riscv.CodeAt s3 s3.pc (([.BNE .x28 .x31 16] ++ acceptTail ++ [.ECALL]) ++ reject) := by
          simpa only [List.append_assoc] using loc3
        exact h.append_right
      have rej := reject_refines (s3.setPC (s3.pc + 16)) (fuel - 4) locR (by omega)
      exact (Riscv.Refines.branch fetch3 rfl (fun h => nomatch h) tr3 rej).mono (by omega)
  · have hr : s1.getReg .x26 ≠ s1.getReg .x30 := by
      rw [s1_26, s1_regs .x30 (by decide), pk0]; exact eq0
    rw [if_neg hr] at tr1
    have spec : decide (answer.setWidth 128 = pk) = false := by
      rw [decide_eq_false_iff_not]
      intro h
      exact eq0 (key.mpr h).1
    rw [spec, Bool.false_and]
    have locR : Riscv.CodeAt (s1.setPC (s1.pc + 24)) (s1.setPC (s1.pc + 24)).pc reject := by
      have h : Riscv.CodeAt s1 s1.pc (([.BNE .x26 .x30 24] ++ [.LD .x28 .x12 8] ++
          [.BNE .x28 .x31 16] ++ acceptTail ++ [.ECALL]) ++ reject) := by
        simpa only [List.append_assoc] using loc1
      exact h.append_right
    have rej := reject_refines (s1.setPC (s1.pc + 24)) (fuel - 2) locR (by omega)
    exact (Riscv.Refines.branch fetch1 rfl (fun h => nomatch h) tr1 rej).mono (by omega)

theorem memBits_setWidth {n k : ℕ} {s : MachineState} {base : Word} {v : BitVec n}
    (hm : MemBits s base v) (hk : k ≤ n) : MemBits s base (v.setWidth k) := by
  intro i hi
  rw [hm i (by omega), BitVec.getLsbD_setWidth]
  simp [hi]

theorem root_length (a : ℕ) :
    W a + signExtend12 (1144 : BitVec 12) = W (a + 1144) := by
  rw [show (1144 : BitVec 12) = BitVec.ofNat 12 1144 from rfl, signExtend12_nat 1144 (by norm_num),
    W_add]

variable (a) in
/-- Machine state at the root after all chains have completed: the 6656 bits from the region
start are `R`. -/
structure RootInv (s : MachineState) (R : BitVec 6656) : Prop where
  ctx : Ctx s index v pk a
  input : s.getReg .x10 = W (work 32)
  out : s.getReg .x12 = W rootOut
  root : MemBits s (W regionAddr) R

/-- The root hash over the first `a + 1144` region bits and the decision, at most 22 cycles. -/
theorem rootDecision_refines (s : MachineState) (R : BitVec 6656) (fuel : ℕ)
    (inv : RootInv index v pk a s R)
    (located : Riscv.CodeAt s s.pc (root ++ decision)) (bound : 12 ≤ fuel) :
    Riscv.Refines fuel s (hash (R.setWidth (a + 1144)) >>= fun y =>
        pure (some (decide (y.setWidth 128 = pk) && decide (a < 5465)))) 22 := by
  have hd : 32 ≤ rootOut ∧ rootOut + 32 ≤ 0x78000000 ∧ rootOut % 8 = 0 := by decide
  have ha := inv.ctx.short
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
    rw [W_add_imm _ _ (by decide) (by decide) (by decide) (by decide)]
    decide
  have w11 : w.getReg .x11 = W (a + 1144) := by
    rw [hw]
    simp only [rootLin, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ite]
    simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, false_and, if_false,
      show ¬ (Reg.x13 = Reg.x10) by decide, show ¬ (Reg.x11 = Reg.x12) by decide,
      show ¬ (Reg.x13 = Reg.x12) by decide, show ¬ (Reg.x13 = Reg.x11) by decide]
    rw [inv.ctx.sigLen]
    exact root_length a
  have w11n : (w.getReg .x11).toNat = a + 1144 := by
    rw [w11]; exact W_toNat _ (by omega)
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
    have r1 : isValidOutputRange (W regionAddr) ((a + 1144 + 7) / 8) = true :=
      range_ok _ _ (by norm_num [regionAddr]) (by norm_num [regionAddr]; omega) (by omega)
        (by omega)
    have r2 := hashOutput_ok rootOut hd.1 hd.2.1 hd.2.2
    unfold Riscv.hashArgumentsValid
    rw [w10, w11n, w12, r1, Bool.true_and]
    exact r2
  have wValue : MemBits w (W regionAddr) (R.setWidth (a + 1144)) :=
    memBits_setWidth (memBits_of_mem_eq (show w.mem = s.mem from funext fun a => wMem a)
      inv.root) (by omega)
  have wInput : Riscv.hashInput w = ⟨a + 1144, R.setWidth (a + 1144)⟩ :=
    hashInput_of_memBits w10 w11n wValue
  have blocks : blockCost (a + 1144) ≤ 13 := by
    unfold blockCost blockBits
    omega
  rw [show fuel = rootLin.length + ((fuel - rootLin.length - 1) + 1) by simp [rootLin]; omega]
  refine (Riscv.Refines.linear _ located.append_left ready ?_).mono
    (show rootLin.length + (blockCost (a + 1144) + 7) ≤ 22 by simp only [rootLin]; simp; omega)
  rw [← hw]
  have step := Riscv.Refines.hash (fuel := fuel - rootLin.length - 1) wFetch wCall wValid
    (k := fun y => pure (some (decide (y.setWidth 128 = pk) && decide (a < 5465))))
    (c := 7) ?_
  · rw [wInput] at step
    dsimp only at step
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
    have h := writeHash_memBits w y (by rw [w12]; exact aligned_W _ hd.2.2 (by decide))
    rw [w12] at h
    exact h
  apply decision_refines pk v y _ (by rw [vRegs, w12]) vLocated vRoot
    (by rw [vRegs, wRegs .x30 (by decide) (by decide)]; exact inv.ctx.pk0)
    (by rw [vRegs, wRegs .x31 (by decide) (by decide)]; exact inv.ctx.pk1)
    (by rw [vRegs, wRegs .x13 (by decide) (by decide)]; exact inv.ctx.sigLen)
    (by rw [vRegs, wRegs .x1 (by decide) (by decide)]; exact inv.ctx.bound) ha
  show 7 ≤ fuel - rootLin.length - 1
  have h3 : rootLin.length = 2 := rfl
  rw [h3]
  omega

end OptimalOTS.RiscvMixedProgram
