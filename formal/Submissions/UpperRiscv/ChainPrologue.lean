import Submissions.UpperRiscv.ChainContext

/-!
# The prologue of a block, the switch of a pair, and the jump

Block `q`'s prologue moves the input pointer to the slot of its first chain, points the answer
buffer eight bytes below it, loads its dispatch halfword and jumps to the hash step of the first
chain's disclosed position in the copy selected by the second chain's digit. Between the two chains
of a pair, the switch moves both pointers to the next slot.
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

/-- The three straight-line instructions of the prologue. -/
def prologueLinear (q : ℕ) : Code :=
  [.ADDI .x10 .x10 (if q = 0 then 64 else 24), .ADDI .x12 .x10 (imm12 (-8)),
   .LHU .x28 .x12 (imm12 ((laneAddr q : ℤ) - outAddr (firstChain q)))]

theorem prologue_parts (q : ℕ) :
    prologue q = prologueLinear q ++ [.JALR .x0 .x28 (imm12 (jumpImm q))] := by
  simp [prologue, prologueLinear]

theorem prologueLinear_length (q : ℕ) : (prologueLinear q).length = 3 := rfl

theorem prologue_length (q : ℕ) : (prologue q).length = 4 := rfl

theorem signExtend_minus8 : signExtend12 (imm12 (-8)) = BitVec.ofInt 64 (-8) :=
  signExtend12_imm (-8) (by norm_num) (by norm_num)

theorem W_sub8 (a : ℕ) (ha : 8 ≤ a) (hlt : a < 2 ^ 62) :
    W a + signExtend12 (imm12 (-8)) = W (a - 8) := by
  rw [W_add_imm a (-8) (by norm_num) (by norm_num) (by omega) hlt]
  congr 1
  omega

theorem lane_offset (q : ℕ) (hq : q < 16) :
    W (slotAddr (firstChain q) - 8) +
      signExtend12 (imm12 ((laneAddr q : ℤ) - outAddr (firstChain q))) = W (laneAddr q) := by
  have hk := firstChain_lt q hq
  have hs := slot_bounds (firstChain q) hk
  have hl := laneAddr_bounds q hq
  rw [W_add_imm _ _ (by simp only [laneBase, outAddr] at hl ⊢; omega)
    (by simp only [laneBase, outAddr] at hl ⊢; omega)
    (by simp only [laneBase, outAddr, slotAddr, payloadAddr] at hl hs ⊢; omega)
    (by unfold slotAddr payloadAddr; omega)]
  congr 1
  simp only [laneBase, outAddr, slotAddr, payloadAddr] at hl hs ⊢
  omega

/-- The first prologue instruction moves the input pointer onto the slot. -/
theorem prologue_step0 (a : MachineState) (q : ℕ) (hq : q < 16)
    (slot : a.getReg .x10 = W (prevInput (firstChain q))) :
    a.getReg .x10 + signExtend12 (if q = 0 then (64 : BitVec 12) else 24) = slotW (firstChain q) := by
  have hk := firstChain_lt q hq
  have hs := slot_bounds (firstChain q) hk
  rw [slot]
  unfold prevInput
  by_cases hq0 : q = 0
  · have hk0 : firstChain q = 0 := (firstChain_eq_zero q).mpr hq0
    rw [if_pos hq0, if_pos hk0, show (64 : BitVec 12) = BitVec.ofNat 12 64 from rfl,
      signExtend12_nat _ (by norm_num), W_add, hk0]
    rfl
  · have hk0 : firstChain q ≠ 0 := fun h => hq0 ((firstChain_eq_zero q).mp h)
    rw [if_neg hq0, if_neg hk0, show (24 : BitVec 12) = BitVec.ofNat 12 24 from rfl,
      signExtend12_nat _ (by norm_num), W_add]
    show W _ = W _
    congr 1
    unfold slotAddr payloadAddr at hs ⊢
    omega

/-- The effect of the straight-line prologue. -/
structure PrologueEffect (a b : MachineState) (q : ℕ) : Prop where
  input : b.getReg .x10 = slotW (firstChain q)
  out : b.getReg .x12 = W (slotAddr (firstChain q) - 8)
  target : b.getReg .x28 = (a.getHalfword (W (laneAddr q))).zeroExtend 64
  regs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = a.getMem addr
  pc : b.pc = a.pc + 12
  code : b.code = a.code

theorem prologueLinear_effect (a : MachineState) (q : ℕ) (hq : q < 16)
    (slot : a.getReg .x10 = W (prevInput (firstChain q))) :
    PrologueEffect a ((prologueLinear q).foldl execInstrBr a) q := by
  have hk := firstChain_lt q hq
  have hs := slot_bounds (firstChain q) hk
  have step0 := prologue_step0 a q hq slot
  have s8 : slotW (firstChain q) + signExtend12 (imm12 (-8)) = W (slotAddr (firstChain q) - 8) :=
    W_sub8 _ (by unfold slotAddr payloadAddr; omega) (by unfold slotAddr payloadAddr; omega)
  have lane := lane_offset q hq
  simp only [prologueLinear, List.foldl_cons, List.foldl_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
      if_false, show ¬ (Reg.x10 = Reg.x28) by decide, show ¬ (Reg.x10 = Reg.x12) by decide,
      step0]
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
      if_false, show ¬ (Reg.x12 = Reg.x28) by decide, show ¬ (Reg.x12 = Reg.x10) by decide,
      step0, s8]
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
      if_false, show ¬ (Reg.x12 = Reg.x10) by decide, step0, s8, lane]
    rfl
  · intro r h10 h12 h28
    simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp [h10, h12, h28]
  · intro addr
    simp [execInstrBr]
  · show a.pc + 4 + 4 + 4 = a.pc + 12
    simp only [BitVec.add_assoc]; rfl
  · simp [execInstrBr]

theorem prologueLinear_ready (a : MachineState) (q : ℕ) (hq : q < 16)
    (slot : a.getReg .x10 = W (prevInput (firstChain q))) :
    Riscv.LinearReady a (prologueLinear q) := by
  have hk := firstChain_lt q hq
  have hl := laneAddr_bounds q hq
  have hs := slot_bounds (firstChain q) hk
  have step0 := prologue_step0 a q hq slot
  have s8 : slotW (firstChain q) + signExtend12 (imm12 (-8)) = W (slotAddr (firstChain q) - 8) :=
    W_sub8 _ (by unfold slotAddr payloadAddr; omega) (by unfold slotAddr payloadAddr; omega)
  refine ⟨rfl, trivial, rfl, trivial, rfl, ?_, trivial⟩
  show isValidHalfwordAccess (_ + _) = true
  simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
    if_false, show ¬ (Reg.x12 = Reg.x10) by decide, step0, s8, lane_offset q hq]
  exact half_ok _ (by unfold laneBase at hl; omega) (by unfold laneBase at hl; omega) hl.2.2

/-! ## The switch -/

/-- The effect of the switch before chain `k` of a pair. -/
structure SwitchEffect (a b : MachineState) (k : ℕ) : Prop where
  input : b.getReg .x10 = slotW k
  out : b.getReg .x12 = W (slotAddr k - 8)
  regs : ∀ r, r ≠ .x10 → r ≠ .x12 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = a.getMem addr
  pc : b.pc = a.pc + 8
  code : b.code = a.code

theorem switch_length : switch.length = 2 := rfl

theorem switch_step0 (a : MachineState) (k : ℕ) (hk : k < 28) (hk0 : k ≠ 0)
    (slot : a.getReg .x10 = W (prevInput k)) :
    a.getReg .x10 + signExtend12 (24 : BitVec 12) = slotW k := by
  have hs := slot_bounds k hk
  rw [slot]
  unfold prevInput
  rw [if_neg hk0, show (24 : BitVec 12) = BitVec.ofNat 12 24 from rfl,
    signExtend12_nat _ (by norm_num), W_add]
  show W _ = W _
  congr 1
  unfold slotAddr payloadAddr at hs ⊢
  omega

theorem switch_effect (a : MachineState) (k : ℕ) (hk : k < 28) (hk0 : k ≠ 0)
    (slot : a.getReg .x10 = W (prevInput k)) :
    SwitchEffect a (switch.foldl execInstrBr a) k := by
  have hs := slot_bounds k hk
  have step0 := switch_step0 a k hk hk0 slot
  have s8 : slotW k + signExtend12 (imm12 (-8)) = W (slotAddr k - 8) :=
    W_sub8 _ (by unfold slotAddr payloadAddr; omega) (by unfold slotAddr payloadAddr; omega)
  simp only [switch, List.foldl_cons, List.foldl_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
      if_false, show ¬ (Reg.x10 = Reg.x12) by decide, step0]
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true,
      if_false, show ¬ (Reg.x12 = Reg.x10) by decide, step0, s8]
  · intro r h10 h12
    simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp [h10, h12]
  · intro addr
    simp [execInstrBr]
  · show a.pc + 4 + 4 = a.pc + 8
    simp only [BitVec.add_assoc]; rfl
  · simp [execInstrBr]

theorem switch_ready (a : MachineState) : Riscv.LinearReady a switch := by
  simp [switch, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

/-! ## The jump -/

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

theorem landing0_bounds' : ∀ q : Fin 16, 16000 ≤ landing0 q ∧ landing0 q < 60000 := by
  decide +kernel

theorem landing0_bounds (q : ℕ) (hq : q < 16) : 16000 ≤ landing0 q ∧ landing0 q < 60000 :=
  landing0_bounds' ⟨q, hq⟩

theorem landing0_mod' : ∀ q : Fin 16, landing0 q % 4 = 0 := by decide +kernel

theorem landing0_mod (q : ℕ) (hq : q < 16) : landing0 q % 4 = 0 := landing0_mod' ⟨q, hq⟩

theorem laneBaseOf_bounds (g : ℕ) : 15484 ≤ laneBaseOf g ∧ laneBaseOf g < 2 ^ 16 := by
  unfold laneBaseOf; split_ifs <;> norm_num

/-- The computed jump lands on `landing0 q` less the dispatch value. -/
theorem jump_target (index : Idx) (q : ℕ) (hq : q < 16) (v : Word)
    (hv : v.toNat = laneBaseOf (laneGroup q) - dispatch index q) :
    (v + signExtend12 (imm12 (jumpImm q))) &&& ~~~(1#64) = W (landing0 q - dispatch index q) := by
  obtain ⟨r1, r2⟩ := jump_offset_range q hq
  have hb := laneBaseOf_bounds (laneGroup q)
  have hl := landing0_bounds q hq
  have hm := landing0_mod q hq
  have hd := dispatch_le index q
  have hv' : v = W (laneBaseOf (laneGroup q) - dispatch index q) := by
    apply BitVec.eq_of_toNat_eq
    rw [hv, W_toNat _ (by omega)]
  rw [hv', W_add_imm _ _ r1 r2 (by unfold jumpImm at *; omega) (by omega)]
  have e : (((laneBaseOf (laneGroup q) - dispatch index q : ℕ) : ℤ) + jumpImm q).toNat =
      landing0 q - dispatch index q := by
    unfold jumpImm at *
    omega
  rw [e]
  apply and_not_one_of_even
  rw [W_toNat _ (by omega)]
  unfold dispatch at *
  omega

theorem jalr_transition (s : MachineState) (i : BitVec 12)
    (fetch : s.code s.pc = some (.JALR .x0 .x28 i)) :
    RiscvZkvm.Rv64.step s = some (s.setPC ((s.getReg .x28 + signExtend12 i) &&& ~~~(1#64))) := by
  rw [RiscvZkvm.Rv64.step, fetch]
  rfl

theorem notCtx_of_prologue (r : Reg) (h : CtxReg r) : r ≠ .x10 ∧ r ≠ .x12 ∧ r ≠ .x28 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> (refine ⟨?_, ?_, ?_⟩ <;> decide)

end OptimalOTS.Riscv2Program
