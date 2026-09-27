import Submissions.UpperRiscvHint.Refines
import Submissions.UpperRiscvHint.AssemblyMacros
import Submissions.UpperRiscvHint.LoaderProof
import Submissions.UpperRiscvHint.Lanes

/-! Exact output words and memory frames for the machine's hash call. -/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag


open RiscvZkvm.Rv64

/-- A bounded sequence of word stores leaves each stored word at its own address. -/
theorem getMem_writeWords_index (s : MachineState) (base : Word) (words : List Word)
    (bounded : 8 * words.length < 2 ^ 64) (j : ℕ) (hj : j < words.length) :
    (s.writeWords base words).getMem (base + BitVec.ofNat 64 (8 * j)) = words[j] := by
  induction words generalizing s base j with
  | nil => simp at hj
  | cons w ws ih =>
    have shift (k : ℕ) : (base + 8) + BitVec.ofNat 64 (8 * k) =
        base + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      exact BitVec.add_comm _ _
    cases j with
    | zero =>
      simp only [Nat.mul_zero, List.getElem_cons_zero]
      rw [show base + 0#64 = base from BitVec.add_zero _]
      rw [MachineState.writeWords_cons, getMem_writeWords_of_disjoint]
      · exact MachineState.getMem_setMem_eq
      · intro k hk
        rw [shift k]
        have h := add_offset_ne base (by norm_num : 0 < 2 ^ 64)
          (by simp only [List.length_cons] at bounded; omega : 8 * (k + 1) < 2 ^ 64)
          (by omega : 0 ≠ 8 * (k + 1))
        simpa using h
    | succ j =>
      rw [MachineState.writeWords_cons, ← shift j]
      exact ih _ _ (by simp only [List.length_cons] at bounded; omega) j (by simpa using hj)

/-- HASH writes all four 64-bit slices of its answer in little-endian order. -/
theorem writeHash_word (s : MachineState) (answer : BitVec hashBits) (j : ℕ) (hj : j < 4) :
    (Riscv.writeHash s answer).getMem (s.getReg .x12 + BitVec.ofNat 64 (8 * j)) =
      answer.extractLsb' (64 * j) 64 := by
  unfold Riscv.writeHash
  rw [MachineState.getMem_setPC, getMem_writeWords_index _ _ _ (by norm_num) j (by simpa using hj)]
  interval_cases j <;> rfl

/-- The output buffer represents the complete hash answer. -/
theorem writeHash_memBits (s : MachineState) (answer : BitVec hashBits)
    (aligned : alignToDword (s.getReg .x12) = s.getReg .x12) :
    MemBits (Riscv.writeHash s answer) (s.getReg .x12) answer := by
  apply memBits_of_words _ _ _ aligned
  exact writeHash_word s answer

/-- HASH preserves each memory word outside its four-word output buffer. -/
theorem writeHash_frame (s : MachineState) (answer : BitVec hashBits) (addr : Word)
    (disjoint : ∀ j, j < 4 → addr ≠ s.getReg .x12 + BitVec.ofNat 64 (8 * j)) :
    (Riscv.writeHash s answer).getMem addr = s.getMem addr := by
  unfold Riscv.writeHash
  rw [MachineState.getMem_setPC]
  exact getMem_writeWords_of_disjoint _ _ _ _ disjoint

end OptimalOTS.Riscv2Program

/-!
# Addresses and accesses of the machine image

Numeric facts shared by the three phases of the image: valid accesses, signed immediates and
halfword loads.
-/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag

open RiscvZkvm.Rv64

@[simp] theorem getReg_store (s : MachineState) (base value : Word) (r : Reg) :
    (s.setMem base value).getReg r = s.getReg r := by cases r <;> rfl

/-- The first aligned memory word can be recovered from a represented vector. -/
theorem getMem_of_memBits {n : ℕ} {s : MachineState} {base : Word} {v : BitVec n}
    (hn : 64 ≤ n) (ha : alignToDword base = base) (hm : MemBits s base v) :
    s.getMem base = v.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := (memBits_word s base ha i hi).symm.trans (hm i (by omega))
  simpa only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add] using h

/-- A 64-bit literal. -/
abbrev W (n : ℕ) : Word := BitVec.ofNat 64 n

/-- The data base, where the index answer, the lane constants and the lane words lie. -/
def dataAddr : ℕ := 0x200000

/-- The root input region: it starts right after the 128-bit nonce. -/
def regionAddr : ℕ := 0x400040

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

theorem getMem_setMem_ite (s : MachineState) (a a' v : Word) :
    (s.setMem a v).getMem a' = if a' = a then v else s.getMem a' := by
  by_cases h : a' = a
  · subst h; simp
  · simp [h]

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

end OptimalOTS.Riscv2Program
