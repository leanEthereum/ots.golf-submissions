import Submissions.UpperRiscv.ChainContext

/-!
# The prologue of a chain block

Chain `k`'s prologue moves the input pointer to its slot, points the answer buffer eight bytes
below it, loads its jump target from the dispatch halfwords and jumps to the hash step of its
disclosed position.
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

/-- The three straight-line instructions of the prologue. -/
def prologueLinear (k : ℕ) : Code :=
  [.ADDI .x10 .x10 (if k = 0 then 64 else 24), .ADDI .x12 .x10 (imm12 (-8)),
   .LHU .x28 .x12 (imm12 ((laneBase + laneHalf k : ℤ) - outAddr k))]

theorem chainPrologue_parts (k : ℕ) :
    chainPrologue k = prologueLinear k ++
      [.JALR .x0 .x28 (imm12 ((tableEnd k : ℤ) - 4 - jumpBase))] := by
  simp [chainPrologue, prologueLinear]

theorem prologueLinear_length (k : ℕ) : (prologueLinear k).length = 3 := rfl

theorem signExtend_minus8 : signExtend12 (imm12 (-8)) = BitVec.ofInt 64 (-8) :=
  signExtend12_imm (-8) (by norm_num) (by norm_num)

theorem W_sub8 (a : ℕ) (ha : 8 ≤ a) (hlt : a < 2 ^ 62) :
    W a + signExtend12 (imm12 (-8)) = W (a - 8) := by
  rw [W_add_imm a (-8) (by norm_num) (by norm_num) (by omega) hlt]
  congr 1
  omega

theorem laneHalf_le (k : ℕ) (hk : k < 28) : laneHalf k ≤ 54 := by
  unfold laneHalf laneOff laneOfChain laneIdx; split_ifs <;> omega

theorem laneHalf_lt (k : ℕ) (hk : k < 28) : laneHalf k < 2048 := by
  have := laneHalf_le k hk; omega

theorem lane_offset (k : ℕ) (hk : k < 28) :
    W (slotAddr k - 8) + signExtend12 (imm12 ((laneBase + laneHalf k : ℤ) - outAddr k)) =
      W (laneAddr k) := by
  have hs := slot_bounds k hk
  have hh := laneHalf_le k hk
  rw [W_add_imm _ _ (by simp only [laneBase, outAddr]; omega)
    (by simp only [laneBase, outAddr]; omega)
    (by simp only [laneBase, outAddr, slotAddr, payloadAddr]; omega)
    (by unfold slotAddr payloadAddr; omega)]
  congr 1
  simp only [laneBase, outAddr, slotAddr, payloadAddr, laneAddr]
  omega

/-- The first prologue instruction moves the input pointer onto the slot. -/
theorem prologue_step0 (a : MachineState) (k : ℕ) (hk : k < 28)
    (slot : a.getReg .x10 = W (prevInput k)) :
    a.getReg .x10 + signExtend12 (if k = 0 then (64 : BitVec 12) else 24) = slotW k := by
  have hs := slot_bounds k hk
  rw [slot]
  unfold prevInput
  by_cases hk0 : k = 0
  · rw [if_pos hk0, if_pos hk0, show (64 : BitVec 12) = BitVec.ofNat 12 64 from rfl,
      signExtend12_nat _ (by norm_num), W_add]
    subst hk0
    rfl
  · rw [if_neg hk0, if_neg hk0, show (24 : BitVec 12) = BitVec.ofNat 12 24 from rfl,
      signExtend12_nat _ (by norm_num), W_add]
    show W _ = W _
    congr 1
    unfold slotAddr payloadAddr at hs ⊢
    omega

/-- The effect of the straight-line prologue. -/
structure PrologueEffect (a b : MachineState) (k : ℕ) : Prop where
  input : b.getReg .x10 = slotW k
  out : b.getReg .x12 = W (slotAddr k - 8)
  target : b.getReg .x28 = (a.getHalfword (W (laneAddr k))).zeroExtend 64
  regs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x28 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = a.getMem addr
  pc : b.pc = a.pc + 12
  code : b.code = a.code

theorem prologueLinear_effect (a : MachineState) (k : ℕ) (hk : k < 28)
    (slot : a.getReg .x10 = W (prevInput k)) :
    PrologueEffect a ((prologueLinear k).foldl execInstrBr a) k := by
  have hs := slot_bounds k hk
  have step0 := prologue_step0 a k hk slot
  have s8 : slotW k + signExtend12 (imm12 (-8)) = W (slotAddr k - 8) :=
    W_sub8 _ (by unfold slotAddr payloadAddr; omega) (by unfold slotAddr payloadAddr; omega)
  have lane := lane_offset k hk
  simp only [prologueLinear, List.foldl_cons, List.foldl_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, false_and,
      if_false, show ¬ (Reg.x10 = Reg.x28) by decide, show ¬ (Reg.x10 = Reg.x12) by decide,
      step0]
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
    simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, false_and,
      if_false, show ¬ (Reg.x12 = Reg.x28) by decide, show ¬ (Reg.x12 = Reg.x10) by decide,
      step0, s8]
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, MachineState.getMem_setPC,
      MachineState.getMem_setReg]
    simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, false_and,
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

theorem prologueLinear_ready (a : MachineState) (k : ℕ) (hk : k < 28)
    (slot : a.getReg .x10 = W (prevInput k)) : Riscv.LinearReady a (prologueLinear k) := by
  have hl := laneAddr_bounds k hk
  have hs := slot_bounds k hk
  have step0 := prologue_step0 a k hk slot
  have s8 : slotW k + signExtend12 (imm12 (-8)) = W (slotAddr k - 8) :=
    W_sub8 _ (by unfold slotAddr payloadAddr; omega) (by unfold slotAddr payloadAddr; omega)
  refine ⟨rfl, trivial, rfl, trivial, rfl, ?_, trivial⟩
  show isValidHalfwordAccess (_ + _) = true
  simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
  simp only [true_and, ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, false_and,
    if_false, show ¬ (Reg.x12 = Reg.x10) by decide, step0, s8, lane_offset k hk]
  exact half_ok _ (by unfold laneBase at hl; omega) (by unfold laneBase at hl; omega) hl.2.2

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

theorem jump_offset_range : ∀ k : Fin 28,
    -2048 ≤ ((tableEnd k : ℤ) - 4 - jumpBase) ∧ ((tableEnd k : ℤ) - 4 - jumpBase) < 2048 := by
  decide

theorem tableEnd_bounds' : ∀ k : Fin 28, 4096 ≤ tableEnd k ∧ tableEnd k < 10000 := by
  decide

theorem tableEnd_bounds (k : ℕ) (hk : k < 28) : 4096 ≤ tableEnd k ∧ tableEnd k < 10000 :=
  tableEnd_bounds' ⟨k, hk⟩

theorem tableEnd_mod (k : ℕ) : tableEnd k % 4 = 0 := by
  unfold tableEnd; omega

theorem jumpBase_bounds : 5000 ≤ jumpBase ∧ jumpBase < 9000 := by unfold jumpBase; omega

/-- The computed jump lands on the hash step of position `p` of chain `k`'s table. -/
theorem jump_target (k : ℕ) (hk : k < 28) (p : ℕ) (hp : p ≤ 31) (v : Word)
    (hv : v.toNat = jumpBase - 4 * (31 - p)) :
    (v + signExtend12 (imm12 ((tableEnd k : ℤ) - 4 - jumpBase))) &&& ~~~(1#64) =
      W (tableEnd k - 4 * (32 - p)) := by
  obtain ⟨r1, r2⟩ := jump_offset_range ⟨k, hk⟩
  have hj := jumpBase_bounds
  have ht := tableEnd_bounds k hk
  have hm := tableEnd_mod k
  have hv' : v = W (jumpBase - 4 * (31 - p)) := by
    apply BitVec.eq_of_toNat_eq
    rw [hv, W_toNat _ (by omega)]
  rw [hv', W_add_imm _ _ r1 r2 (by omega) (by omega)]
  have e : (((jumpBase - 4 * (31 - p) : ℕ) : ℤ) + ((tableEnd k : ℤ) - 4 - jumpBase)).toNat =
      tableEnd k - 4 * (32 - p) := by
    omega
  rw [e]
  apply and_not_one_of_even
  rw [W_toNat _ (by omega)]
  omega

theorem jalr_transition (s : MachineState) (i : BitVec 12)
    (fetch : s.code s.pc = some (.JALR .x0 .x28 i)) :
    RiscvZkvm.Rv64.step s = some (s.setPC ((s.getReg .x28 + signExtend12 i) &&& ~~~(1#64))) := by
  rw [RiscvZkvm.Rv64.step, fetch]
  rfl

theorem notCtx_of_prologue (r : Reg) (h : CtxReg r) : r ≠ .x10 ∧ r ≠ .x12 ∧ r ≠ .x28 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> (refine ⟨?_, ?_, ?_⟩ <;> decide)

end OptimalOTS.Riscv2Program
