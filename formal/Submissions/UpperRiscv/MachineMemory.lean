import Submissions.UpperRiscv.Program
import Submissions.UpperRiscv.Reconstruct

/-!
# Exact memory representations for the forest verifier

The representation records the bits read by the machine's HASH boundary. Its append
lemma follows the little-endian ABI: the low vector occupies the lower addresses.
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag


open RiscvZkvm.Rv64

/-- The next `n` memory bits represent `v`, least significant bit first. -/
def MemBits {n : ℕ} (s : MachineState) (base : Word) (v : BitVec n) : Prop :=
  ∀ i, i < n → (s.getByte (base + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) = v.getLsbD i

/-- The hash boundary reads exactly the represented vector, including its bit length. -/
theorem hashInput_of_memBits {n : ℕ} {s : MachineState} {base : Word} {v : BitVec n}
    (hp : s.getReg .x10 = base) (hn : (s.getReg .x11).toNat = n)
    (hm : MemBits s base v) : Riscv.hashInput s = ⟨n, v⟩ := by
  unfold Riscv.hashInput
  simp only [hp, hn]
  congr 1
  rw [← ofBits_toBits v]
  congr 1
  apply List.ext_getElem
  · simp [toBits]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, toBits, List.getElem_ofFn]
    apply hm
    simpa using hi

/-- Register and PC changes preserve every represented memory vector. -/
theorem memBits_of_mem_eq {n : ℕ} {s t : MachineState} {base : Word} {v : BitVec n}
    (h : t.mem = s.mem) (hm : MemBits s base v) : MemBits t base v := by
  intro i hi
  simpa only [MachineState.getByte, MachineState.getMem, h] using hm i hi

/-- The high vector follows the low vector at the next byte boundary. -/
theorem memBits_append {m n : ℕ} {s : MachineState} {base : Word}
    {lo : BitVec m} {hi : BitVec n} (aligned : m % 8 = 0)
    (hlo : MemBits s base lo) (hhi : MemBits s (base + BitVec.ofNat 64 (m / 8)) hi) :
    MemBits s base (hi ++ lo) := by
  intro i hiBound
  rw [BitVec.getLsbD_append]
  split_ifs with hilow
  · exact hlo i hilow
  · have him : m ≤ i := Nat.le_of_not_gt hilow
    have hsub : i - m < n := by omega
    have hdiv : i / 8 = m / 8 + (i - m) / 8 := by omega
    have hmod : i % 8 = (i - m) % 8 := by omega
    have hadd : base + BitVec.ofNat 64 (i / 8) =
        (base + BitVec.ofNat 64 (m / 8)) + BitVec.ofNat 64 ((i - m) / 8) := by
      rw [hdiv, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hadd, hmod]
    exact hhi (i - m) hsub

/-- Non-overlapping word stores preserve a memory cell. -/
theorem getMem_writeWords_of_disjoint (s : MachineState) (base addr : Word)
    (words : List Word)
    (h : ∀ j, j < words.length → addr ≠ base + BitVec.ofNat 64 (8 * j)) :
    (s.writeWords base words).getMem addr = s.getMem addr := by
  induction words generalizing s base with
  | nil => rfl
  | cons w ws ih =>
    simp only [MachineState.writeWords]
    rw [ih]
    · apply MachineState.getMem_setMem_ne
      simpa using h 0 (by simp)
    · intro j hj
      have := h (j + 1) (by simpa using hj)
      have ha : (base + 8) + BitVec.ofNat 64 (8 * j) =
          base + BitVec.ofNat 64 (8 * (j + 1)) := by
        rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
        congr 1
        exact BitVec.add_comm _ _
      simpa only [ha] using this

/-- The upstream alignment operation rounds the natural address down to a multiple of eight. -/
theorem alignToDword_toNat (base : Word) :
    (alignToDword base).toNat = base.toNat / 8 * 8 := by
  have hlt : base.toNat / 8 < 2 ^ 61 := by have := base.isLt; omega
  have hdiv := Nat.and_div_two_pow (a := base.toNat) (b := 2 ^ 64 - 8) (n := 3)
  have hmod := Nat.and_mod_two_pow (a := base.toNat) (b := 2 ^ 64 - 8) (n := 3)
  norm_num at hdiv hmod
  have hmask : base.toNat / 8 &&& (2 ^ 61 - 1) = base.toNat / 8 :=
    Nat.and_two_pow_sub_one_of_lt_two_pow hlt
  norm_num at hmask
  rw [hmask] at hdiv
  simp only [alignToDword, BitVec.toNat_and]
  norm_num
  omega

theorem byteOffset_eq_mod (base : Word) : byteOffset base = base.toNat % 8 := by
  unfold byteOffset
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact Nat.and_two_pow_sub_one_eq_mod base.toNat 3

theorem aligned_iff (base : Word) : alignToDword base = base ↔ base.toNat % 8 = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [alignToDword_toNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat]
    omega

/-- Each byte within an aligned word has the expected containing address and offset. -/
theorem aligned_byte_address {base : Word} (hbase : alignToDword base = base)
    {j : ℕ} (hj : j < 8) :
    alignToDword (base + BitVec.ofNat 64 j) = base ∧
      byteOffset (base + BitVec.ofNat 64 j) = j := by
  have hb := (aligned_iff base).mp hbase
  have hlt := base.isLt
  have hadd : (base + BitVec.ofNat 64 j).toNat = base.toNat + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, hadd]
    omega
  · rw [byteOffset_eq_mod, hadd]
    omega

/-- Reading a byte within an aligned doubleword extracts the corresponding byte. -/
theorem getByte_of_aligned {s : MachineState} {base : Word}
    (hbase : alignToDword base = base) {j : ℕ} (hj : j < 8) :
    s.getByte (base + BitVec.ofNat 64 j) = extractByte (s.getMem base) j := by
  obtain ⟨ha, ho⟩ := aligned_byte_address hbase hj
  simp only [MachineState.getByte, ha, ho]

/-- One aligned doubleword represents its stored 64 bits. -/
theorem memBits_word (s : MachineState) (base : Word)
    (hbase : alignToDword base = base) : MemBits s base (s.getMem base) := by
  intro i hi
  rw [getByte_of_aligned hbase (by omega)]
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [hm, decide_true, Bool.true_and]
  congr 1
  omega

/-- Aligned adjacent doublewords reconstruct one 128-bit value. -/
theorem memBits_twoWords (s : MachineState) (base : Word)
    (hbase : alignToDword base = base) :
    MemBits s base (s.getMem (base + 8) ++ s.getMem base) := by
  apply memBits_append (by decide) (memBits_word s base hbase)
  apply memBits_word
  apply (aligned_iff _).mpr
  have hb := (aligned_iff base).mp hbase
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A 128-bit value is determined by its two little-endian doublewords. -/
theorem memBits_of_twoWords {s : MachineState} {base : Word} {v : BitVec 128}
    (hbase : alignToDword base = base)
    (hlo : s.getMem base = v.extractLsb' 0 64)
    (hhi : s.getMem (base + 8) = v.extractLsb' 64 64) : MemBits s base v := by
  have h := memBits_twoWords s base hbase
  rw [hlo, hhi] at h
  have heq : v.extractLsb' 64 64 ++ v.extractLsb' 0 64 = v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_append]
    by_cases hlow : i < 64
    · simp [hlow]
    · have hsub : i - 64 < 64 := by omega
      simp [hlow, hsub, show 64 + (i - 64) = i by omega]
  simpa only [heq] using h

/-- Reading one packed byte is the corresponding list lookup, with zero padding. -/
theorem bytesToWordLE_getLsbD (bs : List (BitVec 8)) {i : ℕ} (hi : i < 64) :
    (bytesToWordLE bs).getLsbD i = (bs[i / 8]?.getD 0).getLsbD (i % 8) := by
  interval_cases i <;> simp [bytesToWordLE, BitVec.zeroExtend]

/-- Packing the vector's byte stream recovers each consecutive 64-bit slice. -/
theorem bytesToWordLE_bytesOfVector {n : ℕ} (v : BitVec n) (j : ℕ) :
    bytesToWordLE (((Riscv.bytesOfVector v).drop (8 * j)).take 8) =
      v.extractLsb' (64 * j) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bytesToWordLE_getLsbD _ hi]
  have hi8 : i / 8 < 8 := by omega
  simp only [List.getElem?_take, hi8, ↓reduceIte, List.getElem?_drop,
    Riscv.bytesOfVector, List.getElem?_map]
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  by_cases hb : 8 * j + i / 8 < (n + 7) / 8
  · simp [hb, hi, hm]
    congr 1
    omega
  · simp [hb, hi]
    apply BitVec.getLsbD_of_ge
    omega

private theorem pack_eight_bits (f : ℕ → Bool) :
    BitVec.ofNat 8 ((List.range 8).foldl (fun n k => n + if f k then 2 ^ k else 0) 0) =
      ofBits 8 ((List.range 8).map f) := by
  have hc : (fun n k => n + if f k then 2 ^ k else 0) =
      (fun n k => n + (f k).toNat * 2 ^ k) := by
    funext n k
    cases f k <;> simp
  rw [hc]
  unfold ofBits
  congr 1
  norm_num [List.range_succ, List.foldl_append]
  ring

/-- The loader's raw byte encoding preserves each supplied bit. -/
theorem bytesOfBits_getLsbD (bits : List Bool) {j k : ℕ}
    (hj : j < (bits.length + 7) / 8) (hk : k < 8) :
    ((Riscv.bytesOfBits bits)[j]'(by simpa [Riscv.bytesOfBits] using hj)).getLsbD k =
      bits.getD (j * 8 + k) false := by
  simp only [Riscv.bytesOfBits, List.getElem_map, List.getElem_range]
  rw [pack_eight_bits]
  simp only [ofBits, BitVec.getLsbD_ofNat, hk, decide_true, Bool.true_and,
    testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]

/-- Byte-stream loading only changes the doublewords occupied by that stream. -/
theorem getMem_writeBytesAsWords_of_disjoint (s : MachineState) (base addr : Word)
    (bytes : List (BitVec 8))
    (h : ∀ j, j < (bytes.length + 7) / 8 → addr ≠ base + BitVec.ofNat 64 (8 * j)) :
    (s.writeBytesAsWords base bytes).getMem addr = s.getMem addr := by
  cases bytes with
  | nil => simp
  | cons b bs =>
    rw [MachineState.writeBytesAsWords]
    rw [getMem_writeBytesAsWords_of_disjoint]
    · apply MachineState.getMem_setMem_ne
      simpa using h 0 (by simp)
    · intro j hj
      have hx := h (j + 1) (by simp only [List.length_drop, List.length_cons] at hj ⊢; omega)
      have ha : (base + 8) + BitVec.ofNat 64 (8 * j) =
          base + BitVec.ofNat 64 (8 * (j + 1)) := by
        rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
        congr 1
        exact BitVec.add_comm _ _
      simpa only [ha] using hx
termination_by bytes.length

/-- Distinct representable offsets give distinct addresses, including across wrapping addition. -/
theorem add_offset_ne (base : Word) {i j : ℕ} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (hne : i ≠ j) : base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j := by
  intro h
  have hh := congrArg (fun w : Word => (w - base).toNat) h
  rw [BitVec.add_comm base, BitVec.add_comm base, BitVec.add_sub_cancel,
    BitVec.add_sub_cancel, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hh
  exact hne hh

/-- Every doubleword of a bounded byte stream loads its eight bytes, zero-padding the tail. -/
theorem getMem_writeBytesAsWords (s : MachineState) (base : Word)
    (bytes : List (BitVec 8)) (hlen : bytes.length ≤ 2 ^ 32)
    (j : ℕ) (hj : j < (bytes.length + 7) / 8) :
    (s.writeBytesAsWords base bytes).getMem (base + BitVec.ofNat 64 (8 * j)) =
      bytesToWordLE ((bytes.drop (8 * j)).take 8) := by
  cases bytes with
  | nil => simp at hj
  | cons b bs =>
    rw [MachineState.writeBytesAsWords]
    cases j with
    | zero =>
      simp only [Nat.mul_zero, BitVec.add_zero, List.drop_zero]
      rw [getMem_writeBytesAsWords_of_disjoint]
      · exact MachineState.getMem_setMem_eq
      · intro k hk
        have hkBound : 8 * (k + 1) < 2 ^ 64 := by
          simp only [List.length_drop, List.length_cons] at hk
          simp only [List.length_cons] at hlen
          omega
        have hne := add_offset_ne base (by decide : 0 < 2 ^ 64) hkBound (by omega)
        convert hne using 1 <;> try simp only [BitVec.add_zero]
        rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
        congr 1
        exact BitVec.add_comm _ _
    | succ j =>
      have ha : base + BitVec.ofNat 64 (8 * (j + 1)) =
          (base + 8) + BitVec.ofNat 64 (8 * j) := by
        rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
        congr 1
        exact BitVec.add_comm _ _
      rw [ha, getMem_writeBytesAsWords _ _ _ (by simp only [List.length_drop, List.length_cons] at hlen ⊢; omega) j (by
        simp only [List.length_drop, List.length_cons] at hj ⊢; omega)]
      rw [List.drop_drop]
      congr 3
      omega
termination_by bytes.length

/-- A wordwise memory frame also preserves the represented bit vector. -/
theorem memBits_of_word_frame {width : ℕ} (s t : MachineState) (base : Word)
    (value : BitVec width) (represented : MemBits s base value)
    (frame : ∀ i, i < width → t.getMem (alignToDword (base + BitVec.ofNat 64 (i / 8))) =
      s.getMem (alignToDword (base + BitVec.ofNat 64 (i / 8)))) : MemBits t base value := by
  intro i hi
  simp only [MachineState.getByte, frame i hi]
  exact represented i hi

/-- Width casts do not alter represented bits. -/
theorem memBits_cast {a b : ℕ} (s : MachineState) (base : Word) (v : BitVec a) (equal : a = b) :
    MemBits s base (v.cast equal) ↔ MemBits s base v := by
  subst equal
  rfl

end OptimalOTS.RiscvUpperProgram
