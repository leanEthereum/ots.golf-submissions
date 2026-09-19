import Submissions.UpperRiscv.Refines
import Submissions.UpperRiscv.CopyProof
import Submissions.UpperRiscv.HashOutput
import Submissions.UpperRiscv.Lanes

/-!
# Addresses, accesses and headers of the machine image

Numeric facts shared by the three phases of the image: valid accesses, signed immediates, the
header doubleword of a chain slot and its level-tag halfword, halfword loads, and the constants
installed by the data image.
-/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

/-- A 64-bit literal. -/
abbrev W (n : ℕ) : Word := BitVec.ofNat 64 n

/-- The data base, where the index answer, the lane constants and the lane words lie. -/
def dataAddr : ℕ := 0x200000

/-- The disclosed words start after the 128-bit nonce. -/
def payloadAddr : ℕ := 0x400040

theorem W_toNat (n : ℕ) (h : n < 2 ^ 64) : (W n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem W_add (a b : ℕ) : W a + W b = W (a + b) := by
  unfold W
  rw [BitVec.ofNat_add]

theorem W_ne {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) : W a ≠ W b := by
  intro e
  have := congrArg BitVec.toNat e
  rw [W_toNat a ha, W_toNat b hb] at this
  exact h this

/-! ## Accesses -/

theorem dword_ok (a : ℕ) (h1 : 32 ≤ a) (h2 : a ≤ 0x78000000) (h3 : a % 8 = 0) :
    isValidDwordAccess (W a) = true := by
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, BitVec.toNat_ofNat,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem half_ok (a : ℕ) (h1 : 32 ≤ a) (h2 : a ≤ 0x78000000) (h3 : a % 2 = 0) :
    isValidHalfwordAccess (W a) = true := by
  simp only [isValidHalfwordAccess, isAligned2, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, BitVec.toNat_ofNat,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem range_ok (a n : ℕ) (h1 : 32 ≤ a) (h2 : a + n ≤ 0x78000000) (h3 : 0 < n)
    (h4 : n ≤ 16777216) : isValidOutputRange (W a) n = true := by
  have e : (W a).toNat = a := W_toNat a (by omega)
  simp only [isValidOutputRange, MAX_OUTPUT_BYTES, MEM_START, MEM_END, INPUT_MEM_START,
    INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, e, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨decide_eq_true h4, by omega⟩

theorem aligned_W (a : ℕ) (h : a % 8 = 0) (hlt : a < 2 ^ 64) : alignToDword (W a) = W a :=
  (aligned_iff _).mpr (by rw [W_toNat a hlt]; exact h)

/-- The four doublewords of a HASH output buffer are valid. -/
theorem hashOutput_ok (a : ℕ) (h1 : 32 ≤ a) (h2 : a + 32 ≤ 0x78000000) (h3 : a % 8 = 0) :
    (isValidDwordAccess (W a) && isValidDwordAccess (W a + 8) &&
      isValidDwordAccess (W a + 16) && isValidDwordAccess (W a + 24)) = true := by
  simp only [show (8 : Word) = W 8 from rfl, show (16 : Word) = W 16 from rfl,
    show (24 : Word) = W 24 from rfl, W_add, dword_ok a h1 (by omega) h3,
    dword_ok (a + 8) (by omega) (by omega) (by omega), dword_ok (a + 16) (by omega) (by omega)
      (by omega), dword_ok (a + 24) (by omega) (by omega) (by omega), Bool.and_self,
    decide_true]

/-! ## Immediates -/

/-- A signed 12-bit immediate in range extends to its integer. -/
theorem signExtend12_imm (z : ℤ) (h1 : -2048 ≤ z) (h2 : z < 2048) :
    signExtend12 (imm12 z) = BitVec.ofInt 64 z := by
  unfold signExtend12 imm12
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by norm_num), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega),
    Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)]

/-- Adding a signed immediate to a literal address. -/
theorem W_add_imm (a : ℕ) (z : ℤ) (h1 : -2048 ≤ z) (h2 : z < 2048) (h3 : 0 ≤ (a : ℤ) + z)
    (h4 : a < 2 ^ 62) :
    W a + signExtend12 (imm12 z) = W ((a : ℤ) + z).toNat := by
  rw [signExtend12_imm z h1 h2]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, W_toNat a (by omega), BitVec.toNat_ofInt, W_toNat _ (by omega)]
  have : ((((a : ℤ) + z).toNat : ℕ) : ℤ) = (a : ℤ) + z := Int.toNat_of_nonneg h3
  omega

theorem signExtend12_nat (n : ℕ) (hn : n < 2048) :
    signExtend12 (BitVec.ofNat 12 n) = W n := signExtend12_nonnegative n hn

/-! ## Registers and memory through simple updates -/

theorem getReg_x0' (t : MachineState) : t.getReg .x0 = 0 := rfl

theorem getReg_setReg_ite (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r' = r ∧ r ≠ .x0 then v else s.getReg r' := by
  by_cases h0 : r = .x0
  · subst h0
    simp [MachineState.setReg]
  · by_cases h : r' = r
    · subst h
      simp [h0, MachineState.getReg_setReg_eq h0]
    · simp [h, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]

theorem getHalfword_congr {s t : MachineState} {a : Word}
    (h : t.getMem (alignToDword a) = s.getMem (alignToDword a)) :
    t.getHalfword a = s.getHalfword a := by
  simp only [MachineState.getHalfword, h]

theorem getMem_setMem_ite (s : MachineState) (a a' v : Word) :
    (s.setMem a v).getMem a' = if a' = a then v else s.getMem a' := by
  by_cases h : a' = a
  · subst h; simp
  · simp [h]

/-! ## Headers -/

/-- The header doubleword with slot address `a` and level tag `lev`, as an append. -/
theorem W_hdr (a lev : ℕ) (ha : a < 2 ^ 48) (hl : lev < 2 ^ 16) :
    W (a + lev * 2 ^ 48) = BitVec.ofNat 16 lev ++ BitVec.ofNat 48 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hl, ← Nat.shiftLeft_add_eq_or_of_lt ha,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by
      have : lev * 2 ^ 48 ≤ (2 ^ 16 - 1) * 2 ^ 48 := Nat.mul_le_mul_right _ (by omega)
      omega)]
  ring

/-- Replacing the top halfword of a doubleword. -/
theorem replaceHalfword_append (y : BitVec 48) (x h : BitVec 16) :
    replaceHalfword (x ++ y) 3 h = h ++ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceHalfword, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hi]
  by_cases hlow : i < 48
  · simp [hlow]
  · have : i - 48 < 16 := by omega
    have hb : Nat.testBit 65535 (i - 48) = true := by
      rw [show (65535 : ℕ) = 2 ^ 16 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simpa using this
    simp [hlow, this, BitVec.getLsbD_ofNat, hb, show i - 48 < 64 by omega]

/-- A halfword store at byte `6` of an aligned doubleword replaces its top halfword. -/
theorem setHalfword_top (s : MachineState) (a : ℕ) (ha : a % 8 = 0) (hlt : a + 8 < 2 ^ 64)
    (h : BitVec 16) :
    s.setHalfword (W (a + 6)) h = s.setMem (W a) (replaceHalfword (s.getMem (W a)) 3 h) := by
  have hal : alignToDword (W (a + 6)) = W a := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, W_toNat _ (by omega), W_toNat _ (by omega)]
    omega
  have hoff : byteOffset (W (a + 6)) = 6 := by
    rw [byteOffset_eq_mod, W_toNat _ (by omega)]
    omega
  simp only [MachineState.setHalfword, hal, hoff]

/-- A halfword load from an aligned doubleword. -/
theorem getHalfword_lane (s : MachineState) (b l : ℕ) (hb : b % 8 = 0) (hl : l < 4)
    (hlt : b + 8 < 2 ^ 64) :
    (s.getHalfword (W (b + 2 * l))).toNat = (s.getMem (W b)).toNat / 2 ^ (16 * l) % 2 ^ 16 := by
  have hal : alignToDword (W (b + 2 * l)) = W b := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, W_toNat _ (by omega), W_toNat _ (by omega)]
    omega
  have hoff : byteOffset (W (b + 2 * l)) / 2 = l := by
    rw [byteOffset_eq_mod, W_toNat _ (by omega)]
    omega
  simp only [MachineState.getHalfword, hal, hoff, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm l 16]

end OptimalOTS.RiscvUpperProgram
