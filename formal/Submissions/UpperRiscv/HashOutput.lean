import Submissions.UpperRiscv.LoaderProof

/-! Exact output words and memory frames for the machine's hash call. -/

namespace OptimalOTS.RiscvUpperProgram

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

end OptimalOTS.RiscvUpperProgram
