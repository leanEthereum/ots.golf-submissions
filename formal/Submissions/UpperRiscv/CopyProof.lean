import Submissions.UpperRiscv.AssemblyMacros
import Submissions.UpperRiscv.LoaderProof

/-! The four-instruction, 128-bit memory-copy macro. -/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag


open RiscvZkvm.Rv64

@[simp] theorem getReg_store (s : MachineState) (base value : Word) (r : Reg) :
    (s.setMem base value).getReg r = s.getReg r := by cases r <;> rfl

/-- Both source words are read before either destination word is written. -/
theorem copy128_mem (s : MachineState) (src dst : Reg) (srcOff dstOff : ℕ)
    (hs : src ≠ .x26) (hd₀ : dst ≠ .x26) (hd₁ : dst ≠ .x27) :
    ((copy128 src srcOff dst dstOff).foldl execInstrBr s).mem =
      ((s.setMem (s.getReg dst + signExtend12 (BitVec.ofNat 12 dstOff))
        (s.getMem (s.getReg src + signExtend12 (BitVec.ofNat 12 srcOff)))).setMem
        (s.getReg dst + signExtend12 (BitVec.ofNat 12 (dstOff + 8)))
        (s.getMem (s.getReg src + signExtend12 (BitVec.ofNat 12 (srcOff + 8))))).mem := by
  funext addr
  change _ = ((s.setMem _ _).setMem _ _).getMem addr
  simp only [copy128, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, getReg_store, MachineState.getMem_setPC, MachineState.getMem_setReg,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hs),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hd₀),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hd₁),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x27 ≠ Reg.x26),
    MachineState.getReg_setReg_eq (by decide : Reg.x26 ≠ Reg.x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ Reg.x0)]
  rfl

/-- The copy macro preserves registers other than its two temporary registers. -/
theorem copy128_reg (s : MachineState) (src dst r : Reg) (srcOff dstOff : ℕ)
    (hr₀ : r ≠ .x26) (hr₁ : r ≠ .x27) :
    ((copy128 src srcOff dst dstOff).foldl execInstrBr s).getReg r = s.getReg r := by
  simp only [copy128, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, getReg_store,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr₀),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr₁)]

/-- Four valid aligned accesses suffice to run the copy macro. -/
theorem copy128_ready (s : MachineState) (src dst : Reg) (srcOff dstOff : ℕ)
    (hs : src ≠ .x26) (hd₀ : dst ≠ .x26) (hd₁ : dst ≠ .x27)
    (hs₀ : isValidDwordAccess (s.getReg src + signExtend12 (BitVec.ofNat 12 srcOff)) = true)
    (hs₁ : isValidDwordAccess (s.getReg src + signExtend12 (BitVec.ofNat 12 (srcOff + 8))) = true)
    (ht₀ : isValidDwordAccess (s.getReg dst + signExtend12 (BitVec.ofNat 12 dstOff)) = true)
    (ht₁ : isValidDwordAccess (s.getReg dst + signExtend12 (BitVec.ofNat 12 (dstOff + 8))) = true) :
    Riscv.LinearReady s (copy128 src srcOff dst dstOff) := by
  simp only [copy128, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    execInstrBr, MachineState.getReg_setPC, getReg_store,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hs),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hd₀),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hd₁),
    hs₀, hs₁, ht₀, ht₁, true_and]

/-- Exact pointwise memory effect, including overlapping source and destination ranges. -/
theorem copy128_getMem (s : MachineState) (src dst : Reg) (srcOff dstOff : ℕ)
    (hs : src ≠ .x26) (hd₀ : dst ≠ .x26) (hd₁ : dst ≠ .x27) (addr : Word) :
    ((copy128 src srcOff dst dstOff).foldl execInstrBr s).getMem addr =
      if addr = s.getReg dst + signExtend12 (BitVec.ofNat 12 (dstOff + 8)) then
        s.getMem (s.getReg src + signExtend12 (BitVec.ofNat 12 (srcOff + 8))) else
      if addr = s.getReg dst + signExtend12 (BitVec.ofNat 12 dstOff) then
        s.getMem (s.getReg src + signExtend12 (BitVec.ofNat 12 srcOff)) else s.getMem addr := by
  have h := congrFun (copy128_mem s src dst srcOff dstOff hs hd₀ hd₁) addr
  simpa only [MachineState.getMem, MachineState.setMem, beq_iff_eq] using h

/-- With ordinary nonnegative offsets, both destination words equal their original source words. -/
theorem copy128_words (s : MachineState) (src dst : Reg) (srcOff dstOff : ℕ)
    (hs : src ≠ .x26) (hd₀ : dst ≠ .x26) (hd₁ : dst ≠ .x27)
    (hsOff : srcOff + 8 < 2048) (hdOff : dstOff + 8 < 2048) :
    let result := (copy128 src srcOff dst dstOff).foldl execInstrBr s
    result.getMem (s.getReg dst + BitVec.ofNat 64 dstOff) =
      s.getMem (s.getReg src + BitVec.ofNat 64 srcOff) ∧
    result.getMem (s.getReg dst + BitVec.ofNat 64 (dstOff + 8)) =
      s.getMem (s.getReg src + BitVec.ofNat 64 (srcOff + 8)) := by
  have hne := add_offset_ne (s.getReg dst) (by omega : dstOff < 2 ^ 64)
    (by omega : dstOff + 8 < 2 ^ 64) (by omega)
  dsimp only
  constructor <;>
    rw [copy128_getMem s src dst srcOff dstOff hs hd₀ hd₁,
      signExtend12_nonnegative _ hdOff, signExtend12_nonnegative _ hsOff,
      signExtend12_nonnegative _ (by omega : dstOff < 2048),
      signExtend12_nonnegative _ (by omega : srcOff < 2048)] <;> simp [hne]

/-- The first aligned memory word can be recovered from a represented vector. -/
theorem getMem_of_memBits {n : ℕ} {s : MachineState} {base : Word} {v : BitVec n}
    (hn : 64 ≤ n) (ha : alignToDword base = base) (hm : MemBits s base v) :
    s.getMem base = v.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := (memBits_word s base ha i hi).symm.trans (hm i (by omega))
  simpa only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add] using h

/-- The real copy macro transports a represented 128-bit value to its destination. -/
theorem copy128_memBits (s : MachineState) (src dst : Reg) (srcOff dstOff : ℕ)
    (hs : src ≠ .x26) (hd₀ : dst ≠ .x26) (hd₁ : dst ≠ .x27)
    (hsOff : srcOff + 8 < 2048) (hdOff : dstOff + 8 < 2048)
    (sourceAligned : alignToDword (s.getReg src + BitVec.ofNat 64 srcOff) =
      s.getReg src + BitVec.ofNat 64 srcOff)
    (destAligned : alignToDword (s.getReg dst + BitVec.ofNat 64 dstOff) =
      s.getReg dst + BitVec.ofNat 64 dstOff)
    (v : BitVec 128) (hm : MemBits s (s.getReg src + BitVec.ofNat 64 srcOff) v) :
    MemBits ((copy128 src srcOff dst dstOff).foldl execInstrBr s)
      (s.getReg dst + BitVec.ofNat 64 dstOff) v := by
  obtain ⟨hlo, hhi⟩ := copy128_words s src dst srcOff dstOff hs hd₀ hd₁ hsOff hdOff
  have srcHigh : alignToDword ((s.getReg src + BitVec.ofNat 64 srcOff) + 8) =
      (s.getReg src + BitVec.ofNat 64 srcOff) + 8 := by
    apply (aligned_iff _).mpr
    have h := (aligned_iff _).mp sourceAligned
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl] at h ⊢
    omega
  have sourceHigh := getMem_of_memBits (by decide : 64 ≤ 64) srcHigh
    (memBits_extract (start := 64) (len := 64) hm (by decide) (by decide))
  have extract_id : (v.extractLsb' 64 64).extractLsb' 0 64 = v.extractLsb' 64 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  rw [extract_id] at sourceHigh
  apply memBits_of_twoWords destAligned
  · exact hlo.trans (getMem_of_memBits (by decide) sourceAligned hm)
  · have haddr : s.getReg dst + BitVec.ofNat 64 dstOff + 8 =
        s.getReg dst + BitVec.ofNat 64 (dstOff + 8) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [haddr, hhi]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, show (8 : Word) = BitVec.ofNat 64 8 from rfl] using sourceHigh

end OptimalOTS.RiscvUpperProgram
