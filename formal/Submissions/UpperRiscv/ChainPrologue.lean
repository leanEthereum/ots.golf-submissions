import Submissions.UpperRiscv.ChainContext

/-!
# The prologue of a chain block

Chain `k`'s prologue moves the slot pointer to `slotAddr k`, points the HASH input at the header
eight bytes below, copies the disclosed word into the slot, writes the slot address as the
header, and loads its jump target from the dispatch halfwords.
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 OracleComp

/-- The slot pointer before chain `k`: the data base, then the previous slot. -/
def prevSlot (k : ℕ) : ℕ := if k = 0 then dataAddr else Flat.slotAddr (k - 1)

theorem prevSlot_step (k : ℕ) (hk : k < 32) :
    prevSlot k + (if k = 0 then 136 else 24) = Flat.slotAddr k := by
  unfold prevSlot Flat.slotAddr Flat.slotBase dataAddr
  split_ifs with h
  · subst h; rfl
  · omega

/-- The eight straight-line instructions of the prologue. -/
def prologueLinear (k : ℕ) : Code :=
  [.ADDI .x12 .x12 (BitVec.ofNat 12 (if k = 0 then 136 else 24)), .ADDI .x10 .x12 (imm12 (-8))] ++
  copy128 .x9 (16 * k) .x12 0 ++
  [.SD .x12 .x12 (imm12 (-8)), .LHU .x28 .x12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ)))]

theorem chainPrologue_parts (k : ℕ) :
    chainPrologue k = prologueLinear k ++
      [.JALR .x0 .x28 (imm12 ((tableEnd k : ℤ) - (jumpBase k : ℤ)))] := by
  simp [chainPrologue, prologueLinear]

theorem prologueLinear_length (k : ℕ) : (prologueLinear k).length = 8 := by
  simp [prologueLinear, copy128]

theorem slot_bounds (k : ℕ) (hk : k < 32) :
    0x200088 ≤ Flat.slotAddr k ∧ Flat.slotAddr k ≤ 0x200088 + 744 ∧ Flat.slotAddr k % 8 = 0 := by
  unfold Flat.slotAddr Flat.slotBase; omega

theorem signExtend_minus8 : signExtend12 (imm12 (-8)) = BitVec.ofInt 64 (-8) :=
  signExtend12_imm (-8) (by norm_num) (by norm_num)

theorem W_sub8 (a : ℕ) (ha : 8 ≤ a) (hlt : a < 2 ^ 62) :
    W a + signExtend12 (imm12 (-8)) = W (a - 8) := by
  rw [W_add_imm a (-8) (by norm_num) (by norm_num) (by omega) hlt]
  congr 1
  omega

theorem lane_offset (k : ℕ) (hk : k < 32) :
    W (Flat.slotAddr k) + signExtend12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ))) =
      W (laneAddr k) := by
  have hs := slot_bounds k hk
  have hl := laneAddr_bounds k hk
  rw [W_add_imm _ _ (by omega) (by unfold laneAddr at hl ⊢; omega) (by omega)
    (by omega)]
  congr 1
  omega

/-- The effect of the straight-line prologue. -/
structure PrologueEffect (a b : MachineState) (k : ℕ) : Prop where
  slot : b.getReg .x12 = slotW k
  input : b.getReg .x10 = W (Flat.slotAddr k - 8)
  target : b.getReg .x28 = (a.getHalfword (W (laneAddr k))).zeroExtend 64
  regs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → r ≠ .x27 → r ≠ .x28 → b.getReg r = a.getReg r
  header : b.getMem (W (Flat.slotAddr k - 8)) = slotW k
  word0 : b.getMem (slotW k) = a.getMem (W (payloadAddr + 16 * k))
  word1 : b.getMem (W (Flat.slotAddr k + 8)) = a.getMem (W (payloadAddr + 16 * k + 8))
  frame : ∀ addr, addr ≠ W (Flat.slotAddr k - 8) → addr ≠ slotW k →
    addr ≠ W (Flat.slotAddr k + 8) → b.getMem addr = a.getMem addr
  pc : b.pc = a.pc + 32
  code : b.code = a.code

theorem prologueLinear_effect (a : MachineState) (k : ℕ) (hk : k < 32)
    (slot : a.getReg .x12 = W (prevSlot k)) (payload : a.getReg .x9 = W payloadAddr) :
    PrologueEffect a ((prologueLinear k).foldl execInstrBr a) k := by
  have hs := slot_bounds k hk
  have hl := laneAddr_bounds k hk
  have step0 : a.getReg .x12 + signExtend12 (BitVec.ofNat 12 (if k = 0 then 136 else 24)) =
      slotW k := by
    rw [slot, signExtend12_nat _ (by split_ifs <;> norm_num), W_add, prevSlot_step k hk]
  have s8 : slotW k + signExtend12 (imm12 (-8)) = W (Flat.slotAddr k - 8) :=
    W_sub8 _ (by omega) (by omega)
  have lane := lane_offset k hk
  have p0 : a.getReg .x9 + signExtend12 (BitVec.ofNat 12 (16 * k)) = W (payloadAddr + 16 * k) := by
    rw [payload, signExtend12_nat _ (by omega), W_add]
  have p1 : a.getReg .x9 + signExtend12 (BitVec.ofNat 12 (16 * k + 8)) =
      W (payloadAddr + 16 * k + 8) := by
    rw [payload, signExtend12_nat _ (by omega), W_add, Nat.add_assoc]
  have z0 : slotW k + signExtend12 (BitVec.ofNat 12 0) = slotW k := by
    rw [signExtend12_nat _ (by norm_num), W_add, Nat.add_zero]
  have z8 : slotW k + signExtend12 (BitVec.ofNat 12 (0 + 8)) = W (Flat.slotAddr k + 8) := by
    rw [signExtend12_nat _ (by norm_num), W_add]
  have ne1 : W (Flat.slotAddr k - 8) ≠ slotW k := W_ne (by omega) (by omega) (by omega)
  have ne2 : W (Flat.slotAddr k - 8) ≠ W (Flat.slotAddr k + 8) := W_ne (by omega) (by omega) (by omega)
  have ne3 : slotW k ≠ W (Flat.slotAddr k + 8) := W_ne (by omega) (by omega) (by omega)
  have split : (prologueLinear k).foldl execInstrBr a =
      execInstrBr (execInstrBr ((copy128 .x9 (16 * k) .x12 0).foldl execInstrBr
        (execInstrBr (execInstrBr a (.ADDI .x12 .x12 (BitVec.ofNat 12 (if k = 0 then 136 else 24))))
          (.ADDI .x10 .x12 (imm12 (-8)))))
        (.SD .x12 .x12 (imm12 (-8))))
        (.LHU .x28 .x12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ)))) := by
    simp only [prologueLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [split]
  -- the two pointer updates
  generalize hb2 : execInstrBr (execInstrBr a (.ADDI .x12 .x12
    (BitVec.ofNat 12 (if k = 0 then 136 else 24)))) (.ADDI .x10 .x12 (imm12 (-8))) = b2
  have b2x12 : b2.getReg .x12 = slotW k := by
    rw [← hb2]; simp [execInstrBr, getReg_setReg_ite, step0]
  have b2x10 : b2.getReg .x10 = W (Flat.slotAddr k - 8) := by
    rw [← hb2]; simp [execInstrBr, getReg_setReg_ite, step0, s8]
  have b2regs : ∀ r, r ≠ .x10 → r ≠ .x12 → b2.getReg r = a.getReg r := by
    intro r h10 h12
    rw [← hb2]; simp [execInstrBr, getReg_setReg_ite, h10, h12]
  have b2mem : ∀ addr, b2.getMem addr = a.getMem addr := by
    intro addr; rw [← hb2]; simp [execInstrBr]
  have b2pc : b2.pc = a.pc + 8 := by
    rw [← hb2]
    show a.pc + 4 + 4 = a.pc + 8
    rw [BitVec.add_assoc]; rfl
  have b2code : b2.code = a.code := by rw [← hb2]; simp [execInstrBr]
  -- the copy
  generalize hb6 : (copy128 .x9 (16 * k) .x12 0).foldl execInstrBr b2 = b6
  have b6regs : ∀ r, r ≠ .x26 → r ≠ .x27 → b6.getReg r = b2.getReg r := by
    intro r h26 h27; rw [← hb6]; exact copy128_reg _ _ _ _ _ _ h26 h27
  have b6mem : ∀ addr, b6.getMem addr =
      if addr = W (Flat.slotAddr k + 8) then a.getMem (W (payloadAddr + 16 * k + 8)) else
      if addr = slotW k then a.getMem (W (payloadAddr + 16 * k)) else a.getMem addr := by
    intro addr
    rw [← hb6, copy128_getMem b2 .x9 .x12 (16 * k) 0 (by decide) (by decide) (by decide), b2x12,
      b2regs .x9 (by decide) (by decide), p0, p1, z0, z8, b2mem, b2mem, b2mem]
  have b6pc : b6.pc = b2.pc + 16 := by
    rw [← hb6]
    show b2.pc + 4 + 4 + 4 + 4 = b2.pc + 16
    simp only [BitVec.add_assoc]; rfl
  have b6code : b6.code = b2.code := by rw [← hb6]; exact Riscv.fold_code _ _
  have b6x12 : b6.getReg .x12 = slotW k := by rw [b6regs .x12 (by decide) (by decide), b2x12]
  -- the header and the target load
  have hdrAddr : b6.getReg .x12 + signExtend12 (imm12 (-8)) = W (Flat.slotAddr k - 8) := by
    rw [b6x12, s8]
  have laneAddr' : b6.getReg .x12 + signExtend12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ))) =
      W (laneAddr k) := by rw [b6x12, lane]
  have hal : alignToDword (W (laneAddr k)) = W (laneAddr k / 8 * 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, W_toNat _ (by omega), W_toNat _ (by omega)]
  have d1 : W (laneAddr k / 8 * 8) ≠ W (Flat.slotAddr k - 8) := W_ne (by omega) (by omega) (by omega)
  have d2 : W (laneAddr k / 8 * 8) ≠ slotW k := W_ne (by omega) (by omega) (by omega)
  have d3 : W (laneAddr k / 8 * 8) ≠ W (Flat.slotAddr k + 8) := W_ne (by omega) (by omega) (by omega)
  generalize hb7 : execInstrBr b6 (.SD .x12 .x12 (imm12 (-8))) = b7
  have b7regs : ∀ r, b7.getReg r = b6.getReg r := by
    intro r; rw [← hb7]; simp [execInstrBr]
  have b7mem : ∀ addr, b7.getMem addr =
      if addr = W (Flat.slotAddr k - 8) then slotW k else b6.getMem addr := by
    intro addr
    rw [← hb7]
    simp only [execInstrBr, MachineState.getMem_setPC, getMem_setMem_ite, b6x12, s8]
  have b7pc : b7.pc = b6.pc + 4 := by rw [← hb7]; rfl
  have b7code : b7.code = b6.code := by rw [← hb7]; simp [execInstrBr]
  have b7x12 : b7.getReg .x12 = slotW k := by rw [b7regs, b6x12]
  have laneAddr7 : b7.getReg .x12 + signExtend12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ))) =
      W (laneAddr k) := by rw [b7x12, lane]
  have b8eq : execInstrBr b7 (.LHU .x28 .x12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ)))) =
      (b7.setReg .x28 ((b7.getHalfword (W (laneAddr k))).zeroExtend 64)).setPC (b7.pc + 4) := by
    show (b7.setReg .x28 ((b7.getHalfword (b7.getReg .x12 +
      signExtend12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ))))).zeroExtend 64)).setPC
      (b7.pc + 4) = _
    rw [laneAddr7]
  rw [b8eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide), b7x12]
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide), b7regs,
      b6regs .x10 (by decide) (by decide), b2x10]
  · have hh : b7.getHalfword (W (laneAddr k)) = a.getHalfword (W (laneAddr k)) := by
      apply getHalfword_congr
      rw [hal, b7mem, if_neg d1, b6mem, if_neg d3, if_neg d2]
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide), hh]
  · intro r h10 h12 h26 h27 h28
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h28), b7regs,
      b6regs r h26 h27, b2regs r h10 h12]
  · rw [MachineState.getMem_setPC, MachineState.getMem_setReg, b7mem, if_pos rfl]
  · rw [MachineState.getMem_setPC, MachineState.getMem_setReg, b7mem, if_neg ne1.symm, b6mem,
      if_neg ne3, if_pos rfl]
  · rw [MachineState.getMem_setPC, MachineState.getMem_setReg, b7mem, if_neg ne2.symm, b6mem,
      if_pos rfl]
  · intro addr h1 h2 h3
    rw [MachineState.getMem_setPC, MachineState.getMem_setReg, b7mem, if_neg h1, b6mem, if_neg h3,
      if_neg h2]
  · show b7.pc + 4 = a.pc + 32
    rw [b7pc, b6pc, b2pc]
    simp only [BitVec.add_assoc]; rfl
  · simp only [MachineState.code_setPC, MachineState.code_setReg, b7code, b6code, b2code]

end OptimalOTS.RiscvUpperProgram
