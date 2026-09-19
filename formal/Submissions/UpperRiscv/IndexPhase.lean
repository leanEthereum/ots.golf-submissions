import Submissions.UpperRiscv.IndexArith

/-!
# The index phase

The machine saves the public key, copies the nonce below the message, hashes `nonce ‖ message`,
rejects wrong lengths, builds the lane words, rejects unless the nibbles sum to `160`, and loads
the remaining level tags: the state `afterIndex` then satisfies the chain-phase invariant.
-/

namespace OptimalOTS.RiscvUpperProgram

open OptimalOTS.Dag
open RiscvZkvm.Rv64 OracleComp

/-! ## The data image -/

theorem dataImage_length : dataImage.length = 64 := by decide

theorem dataImage_word (j : ℕ) (hj : j < 4) :
    bytesToWordLE ((dataImage.drop (8 * (4 + j))).take 8) =
      W (broadcast ([120, 1, Flat.jumpBase0, Flat.jumpBase1].getD j 0)) := by
  interval_cases j <;> decide

theorem initial_data_word (pk : PublicKey) (m : Message) (bits : List Bool) (j : ℕ) (hj : j < 4) :
    (Riscv.initialState image pk m bits).getMem (W (dataAddr + 32 + 8 * j)) =
      W (broadcast ([120, 1, Flat.jumpBase0, Flat.jumpBase1].getD j 0)) := by
  have hlen : image.data.length = 64 := dataImage_length
  have ha : (W (dataAddr + 32 + 8 * j)).toNat = dataAddr + 32 + 8 * j :=
    W_toNat _ (by unfold dataAddr; omega)
  rw [initialState_getMem, getMem_load_outside, loaderMessage, getMem_load_outside, loaderPublic,
    getMem_load_outside, loaderData]
  · have e : W (dataAddr + 32 + 8 * j) = Riscv.dataBase + BitVec.ofNat 64 (8 * (4 + j)) := by
      rw [show Riscv.dataBase = W 2097152 from rfl, W_add]
      unfold dataAddr
      congr 1
      omega
    have h1 : image.data.length ≤ 2 ^ 32 := by rw [hlen]; norm_num
    have h2 : 4 + j < (image.data.length + 7) / 8 := by rw [hlen]; omega
    rw [e, getMem_writeBytesAsWords _ _ _ h1 _ h2]
    exact dataImage_word j hj
  all_goals
    try rw [ha]
    norm_num [Riscv.bytesOfVector, Riscv.bytesOfBits, pkBits, msgBits, maxSignatureBits, dataAddr]
    try omega

/-! ## The prefix and the index query -/

section Prefix

variable (pk : PublicKey) (m : Message) (bits : List Bool)

/-- The loader's state. -/
abbrev S0 : MachineState := Riscv.initialState image pk m bits

theorem S0_regs :
    (S0 pk m bits).getReg .x10 = W 0x400000 ∧ (S0 pk m bits).getReg .x12 = W 0x400030 ∧
    (S0 pk m bits).getReg .x13 = BitVec.ofNat 64 (min bits.length 5505) := ⟨rfl, rfl, rfl⟩

theorem S0_pc : (S0 pk m bits).pc = W 4096 := by
  simp [Riscv.initialState]; rfl

/-- The state before the index query. -/
def afterPrefix : MachineState := indexPrefix.foldl execInstrBr (S0 pk m bits)

theorem indexPrefix_ready : Riscv.LinearReady (S0 pk m bits) indexPrefix := by
  simp [indexPrefix, copy128, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    execInstrBr, Riscv.initialState, MachineState.getReg, MachineState.setReg,
    MachineState.setMem, MachineState.setPC, Riscv.signatureBase, Riscv.publicKeyBase,
    signExtend12, MachineState.getMem, MEM_START, MEM_END]

theorem indexPrefix_length : indexPrefix.length = 10 := rfl

structure PrefixEffect (s : MachineState) : Prop where
  x9 : s.getReg .x9 = W payloadAddr
  x30 : s.getReg .x30 = pk.extractLsb' 0 64
  x31 : s.getReg .x31 = pk.extractLsb' 64 64
  x10 : s.getReg .x10 = W 0x400000
  x11 : s.getReg .x11 = 384
  x12 : s.getReg .x12 = W dataAddr
  x5 : s.getReg .x5 = 1
  x13 : s.getReg .x13 = BitVec.ofNat 64 (min bits.length 5505)
  nonce0 : s.getMem (W 0x400000) = (S0 pk m bits).getMem (W 0x400030)
  nonce1 : s.getMem (W 0x400008) = (S0 pk m bits).getMem (W 0x400038)
  frame : ∀ addr, addr ≠ W 0x400000 → addr ≠ W 0x400008 → s.getMem addr = (S0 pk m bits).getMem addr
  pc : s.pc = W (4096 + 40)
  code : s.code = (S0 pk m bits).code

theorem pk_word0 : (S0 pk m bits).getMem (W 0x400000) = pk.extractLsb' 0 64 := by
  have h := initialState_publicKey_word image pk m bits 0 (by norm_num)
  have e : W 0x400000 = Riscv.publicKeyBase + BitVec.ofNat 64 (8 * 0) := by decide
  rw [e]; exact h

theorem pk_word1 : (S0 pk m bits).getMem (W 0x400008) = pk.extractLsb' 64 64 := by
  have h := initialState_publicKey_word image pk m bits 1 (by norm_num)
  have e : W 0x400008 = Riscv.publicKeyBase + BitVec.ofNat 64 (8 * 1) := by decide
  rw [e]; exact h

theorem prefix_effect : PrefixEffect pk m bits (afterPrefix pk m bits) := by
  have split : afterPrefix pk m bits =
      [Instr.ADDI .x11 .x0 384, .LUI .x12 0x200, .ADDI .x5 .x0 1].foldl execInstrBr
        ((copy128 .x12 0 .x10 0).foldl execInstrBr
          ([Instr.ADDI .x9 .x12 16, .LD .x30 .x10 0, .LD .x31 .x10 8].foldl execInstrBr
            (S0 pk m bits))) := by
    simp only [afterPrefix, indexPrefix, List.foldl_append]
  rw [split]
  generalize ha : [Instr.ADDI .x9 .x12 16, .LD .x30 .x10 0, .LD .x31 .x10 8].foldl execInstrBr
    (S0 pk m bits) = a
  have l16 : signExtend12 (16 : BitVec 12) = W 16 := by decide
  have l0 : signExtend12 (0 : BitVec 12) = W 0 := by decide
  have l8 : signExtend12 (8 : BitVec 12) = W 8 := by decide
  have a9 : a.getReg .x9 = W payloadAddr := by
    rw [← ha]; simp [execInstrBr, getReg_setReg_ite, l16]; rfl
  have a30 : a.getReg .x30 = pk.extractLsb' 0 64 := by
    rw [← ha]; simp [execInstrBr, getReg_setReg_ite, l0]; exact pk_word0 pk m bits
  have a31 : a.getReg .x31 = pk.extractLsb' 64 64 := by
    rw [← ha]; simp [execInstrBr, getReg_setReg_ite, l8]; exact pk_word1 pk m bits
  have aregs : ∀ r, r ≠ .x9 → r ≠ .x30 → r ≠ .x31 → a.getReg r = (S0 pk m bits).getReg r := by
    intro r h9 h30 h31
    rw [← ha]; simp [execInstrBr, getReg_setReg_ite, h9, h30, h31]
  have amem : ∀ addr, a.getMem addr = (S0 pk m bits).getMem addr := by
    intro addr; rw [← ha]; simp [execInstrBr]
  have apc : a.pc = W 4096 + 12 := by
    rw [← ha]
    show (S0 pk m bits).pc + 4 + 4 + 4 = _
    rw [S0_pc]; decide
  have acode : a.code = (S0 pk m bits).code := by rw [← ha]; simp [execInstrBr]
  generalize hb : (copy128 .x12 0 .x10 0).foldl execInstrBr a = b
  have a12 : a.getReg .x12 = W 0x400030 := by
    rw [aregs .x12 (by decide) (by decide) (by decide)]; exact (S0_regs pk m bits).2.1
  have a10 : a.getReg .x10 = W 0x400000 := by
    rw [aregs .x10 (by decide) (by decide) (by decide)]; exact (S0_regs pk m bits).1
  have bregs : ∀ r, r ≠ .x26 → r ≠ .x27 → b.getReg r = a.getReg r := by
    intro r h26 h27; rw [← hb]; exact copy128_reg _ _ _ _ _ _ h26 h27
  have bmem : ∀ addr, b.getMem addr =
      if addr = W 0x400008 then a.getMem (W 0x400038) else
      if addr = W 0x400000 then a.getMem (W 0x400030) else a.getMem addr := by
    intro addr
    rw [← hb, copy128_getMem a .x12 .x10 0 0 (by decide) (by decide) (by decide), a12, a10,
      signExtend12_nat _ (by norm_num), signExtend12_nat _ (by norm_num), W_add, W_add, W_add,
      W_add]
  have bpc : b.pc = a.pc + 16 := by
    rw [← hb]
    show a.pc + 4 + 4 + 4 + 4 = a.pc + 16
    simp only [BitVec.add_assoc]; rfl
  have bcode : b.code = a.code := by rw [← hb]; exact Riscv.fold_code _ _
  have lui : ((BitVec.ofNat 20 0x200).zeroExtend 32 <<< 12).signExtend 64 = W dataAddr := by decide
  have ne1 : W 0x400000 ≠ W 0x400008 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite, MachineState.getMem_setPC, MachineState.getMem_setReg]
  · simp only [show ¬ (Reg.x9 = Reg.x5) by decide, show ¬ (Reg.x9 = Reg.x12) by decide,
      show ¬ (Reg.x9 = Reg.x11) by decide, false_and, if_false]
    rw [bregs .x9 (by decide) (by decide), a9]
  · simp only [show ¬ (Reg.x30 = Reg.x5) by decide, show ¬ (Reg.x30 = Reg.x12) by decide,
      show ¬ (Reg.x30 = Reg.x11) by decide, false_and, if_false]
    rw [bregs .x30 (by decide) (by decide), a30]
  · simp only [show ¬ (Reg.x31 = Reg.x5) by decide, show ¬ (Reg.x31 = Reg.x12) by decide,
      show ¬ (Reg.x31 = Reg.x11) by decide, false_and, if_false]
    rw [bregs .x31 (by decide) (by decide), a31]
  · simp only [show ¬ (Reg.x10 = Reg.x5) by decide, show ¬ (Reg.x10 = Reg.x12) by decide,
      show ¬ (Reg.x10 = Reg.x11) by decide, false_and, if_false]
    rw [bregs .x10 (by decide) (by decide), a10]
  · simp [getReg_x0']; decide
  · simp
    exact lui
  · simp [getReg_x0']; decide
  · simp only [show ¬ (Reg.x13 = Reg.x5) by decide, show ¬ (Reg.x13 = Reg.x12) by decide,
      show ¬ (Reg.x13 = Reg.x11) by decide, false_and, if_false]
    rw [bregs .x13 (by decide) (by decide), aregs .x13 (by decide) (by decide) (by decide)]
    exact (S0_regs pk m bits).2.2
  · rw [bmem, if_neg ne1, if_pos rfl, amem]
  · rw [bmem, if_pos rfl, amem]
  · intro addr h1 h2
    rw [bmem, if_neg h2, if_neg h1, amem]
  · show b.pc + 4 + 4 + 4 = _
    rw [bpc, apc]
    simp only [BitVec.add_assoc]; rfl
  · simp [bcode, acode]

theorem image_data_length : image.data.length ≤ 1048576 := by
  rw [show image.data = dataImage from rfl, dataImage_length]; norm_num

set_option maxRecDepth 100000 in
/-- The prepared HASH input is exactly the specification's message/nonce concatenation. -/
theorem prefix_memBits :
    MemBits (afterPrefix pk m bits) (W 0x400000) (m ++ ofBits 128 bits) := by
  have E := prefix_effect pk m bits
  apply memBits_of_words _ _ _ (by decide)
  intro j hj
  change j < 6 at hj
  rw [W_add]
  by_cases hlow : j < 2
  · have hs := initialState_signature_word image pk m bits image_data_length j (by omega)
    have e : Riscv.signatureBase + BitVec.ofNat 64 (8 * j) = W (0x400030 + 8 * j) := by
      rw [show Riscv.signatureBase = W 0x400030 from rfl, W_add]
    rw [e] at hs
    interval_cases j
    · rw [show (0x400000 + 8 * 0 : ℕ) = 0x400000 by norm_num, E.nonce0, hs,
        BitVec.extractLsb'_append_eq_of_add_le (by omega), ofBits_extract _ (by omega),
        ofBits_drop_take _ (by omega)]
    · rw [show (0x400000 + 8 * 1 : ℕ) = 0x400008 by norm_num, E.nonce1, hs,
        BitVec.extractLsb'_append_eq_of_add_le (by omega), ofBits_extract _ (by omega),
        ofBits_drop_take _ (by omega)]
  · have hm := initialState_message_word image pk m bits (j - 2) (by omega)
    have e : Riscv.messageBase + BitVec.ofNat 64 (8 * (j - 2)) = W (0x400000 + 8 * j) := by
      rw [show Riscv.messageBase = W 0x400010 from rfl, W_add]
      congr 1
      omega
    rw [e] at hm
    rw [E.frame _ (W_ne (by omega) (by norm_num) (by omega)) (W_ne (by omega) (by norm_num)
      (by omega)), hm, BitVec.extractLsb'_append_eq_of_le (by omega)]
    congr 1
    omega

theorem prefix_hashInput :
    Riscv.hashInput (afterPrefix pk m bits) = ⟨384, m ++ ofBits 128 bits⟩ := by
  have E := prefix_effect pk m bits
  apply hashInput_of_memBits E.x10 (by rw [E.x11]; rfl) (prefix_memBits pk m bits)

theorem prefix_hashValid : Riscv.hashArgumentsValid (afterPrefix pk m bits) = true := by
  have E := prefix_effect pk m bits
  have r1 : isValidOutputRange (W 0x400000) 48 = true :=
    range_ok _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r2 := hashOutput_ok dataAddr (by unfold dataAddr; omega) (by unfold dataAddr; omega)
    (by unfold dataAddr; omega)
  have e : ((384 : Word).toNat + 7) / 8 = 48 := rfl
  unfold Riscv.hashArgumentsValid
  rw [E.x10, E.x11, E.x12, e, r1, Bool.true_and]
  exact r2

end Prefix

/-! ## After the index query -/

section Tail

variable (pk : PublicKey) (m : Message) (bits : List Bool) (answer : BitVec hashBits)

abbrev S2 : MachineState := Riscv.writeHash (afterPrefix pk m bits) answer

def lenBlock : Code := [.LUI .x6 1, .ADDI .x6 .x6 128]

theorem lengthCheck_parts : lengthCheck = lenBlock ++ ([.BEQ .x13 .x6 16] ++ reject) := rfl

def S3 : MachineState := lenBlock.foldl execInstrBr (S2 pk m bits answer)

def S4 : MachineState := (S3 pk m bits answer).setPC ((S3 pk m bits answer).pc + 16)

def sumOps : Code := [.MUL .x27 .x27 .x23, .SRLI .x27 .x27 48, .XORI .x27 .x27 1280]

theorem sumCheck_parts : sumCheck = sumOps ++ ([.BEQ .x27 .x0 16] ++ reject) := rfl

def mainBlock : Code := loadWords ++ lanes ++ sumOps

def S5 : MachineState := mainBlock.foldl execInstrBr (S4 pk m bits answer)

def S6 : MachineState := (S5 pk m bits answer).setPC ((S5 pk m bits answer).pc + 16)

/-- The state after the index phase, at the first chain block. -/
def afterIndex : MachineState := levelSetup.foldl execInstrBr (S6 pk m bits answer)

theorem S2_regs (r : Reg) : (S2 pk m bits answer).getReg r = (afterPrefix pk m bits).getReg r := by
  simp [Riscv.writeHash]

theorem S2_answer (j : ℕ) (hj : j < 4) :
    (S2 pk m bits answer).getMem (W (dataAddr + 8 * j)) = answer.extractLsb' (64 * j) 64 := by
  have h := writeHash_word (afterPrefix pk m bits) answer j hj
  rw [(prefix_effect pk m bits).x12, W_add] at h
  exact h

theorem S2_frame (addr : Word) (h : addr.toNat < dataAddr ∨ dataAddr + 32 ≤ addr.toNat) :
    (S2 pk m bits answer).getMem addr = (afterPrefix pk m bits).getMem addr := by
  apply writeHash_frame
  rw [(prefix_effect pk m bits).x12]
  intro j hj e
  rw [e, W_add, W_toNat _ (by unfold dataAddr; omega)] at h
  omega

theorem S3_regs (r : Reg) (hr : r ≠ .x6) :
    (S3 pk m bits answer).getReg r = (afterPrefix pk m bits).getReg r := by
  unfold S3
  simp [lenBlock, execInstrBr, getReg_setReg_ite, Ne.symm hr, hr, S2_regs]

theorem S3_x6 : (S3 pk m bits answer).getReg .x6 = W 4224 := by
  unfold S3
  simp [lenBlock, execInstrBr, getReg_setReg_ite]
  decide

theorem S3_mem (addr : Word) : (S3 pk m bits answer).getMem addr = (S2 pk m bits answer).getMem addr := by
  unfold S3
  simp [lenBlock, execInstrBr]

theorem S3_code : (S3 pk m bits answer).code = (S0 pk m bits).code := by
  unfold S3
  simp [lenBlock, execInstrBr, Riscv.writeHash, (prefix_effect pk m bits).code]

theorem length_iff : (S3 pk m bits answer).getReg .x13 = (S3 pk m bits answer).getReg .x6 ↔
    bits.length = 4224 := by
  rw [S3_x6, S3_regs pk m bits answer .x13 (by decide), (prefix_effect pk m bits).x13]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, W_toNat _ (by norm_num), Nat.mod_eq_of_lt (by omega)] at hn
    omega
  · intro h
    rw [h]
    rfl

theorem S4_regs (r : Reg) : (S4 pk m bits answer).getReg r = (S3 pk m bits answer).getReg r := by
  simp [S4]

theorem S4_mem (addr : Word) : (S4 pk m bits answer).getMem addr = (S2 pk m bits answer).getMem addr := by
  simp [S4, S3_mem]

/-- The constants of the data image are still in place after the index query. -/
theorem S2_const (j : ℕ) (hj : j < 4) :
    (S2 pk m bits answer).getMem (W (dataAddr + 32 + 8 * j)) =
      W (broadcast ([120, 1, Flat.jumpBase0, Flat.jumpBase1].getD j 0)) := by
  rw [S2_frame _ _ _ _ _ (Or.inr (by rw [W_toNat _ (by unfold dataAddr; omega)]; omega)),
    (prefix_effect pk m bits).frame _ (W_ne (by unfold dataAddr; omega) (by norm_num)
      (by unfold dataAddr; omega)) (W_ne (by unfold dataAddr; omega) (by norm_num)
      (by unfold dataAddr; omega)), initial_data_word pk m bits j hj]

/-- The words and constants loaded before the lanes. -/
structure LoadEffect (a b : MachineState) : Prop where
  x20 : b.getReg .x20 = answer.extractLsb' 0 64
  x21 : b.getReg .x21 = answer.extractLsb' 64 64
  x22 : b.getReg .x22 = W (broadcast 120)
  x23 : b.getReg .x23 = W (broadcast 1)
  x24 : b.getReg .x24 = W (broadcast Flat.jumpBase0)
  x25 : b.getReg .x25 = W (broadcast Flat.jumpBase1)
  regs : ∀ r, r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 →
    b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = a.getMem addr

theorem S4_x12 : (S4 pk m bits answer).getReg .x12 = W dataAddr := by
  rw [S4_regs, S3_regs _ _ _ _ _ (by decide), (prefix_effect pk m bits).x12]

theorem loadWords_ready : Riscv.LinearReady (S4 pk m bits answer) loadWords := by
  have h12 := S4_x12 pk m bits answer
  simp only [loadWords, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, true_and, and_true]
  simp only [show ¬ (Reg.x12 = Reg.x20) by decide, show ¬ (Reg.x12 = Reg.x21) by decide,
    show ¬ (Reg.x12 = Reg.x22) by decide, show ¬ (Reg.x12 = Reg.x23) by decide,
    show ¬ (Reg.x12 = Reg.x24) by decide, false_and, if_false, h12]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold dataAddr; decide)

theorem loadWords_effect :
    LoadEffect answer (S4 pk m bits answer) (loadWords.foldl execInstrBr (S4 pk m bits answer)) := by
  have h12 := S4_x12 pk m bits answer
  have mw : ∀ off : ℕ, off < 2048 → (S4 pk m bits answer).getReg .x12 +
      signExtend12 (BitVec.ofNat 12 off) = W (dataAddr + off) := by
    intro off hoff; rw [h12, signExtend12_nat _ hoff, W_add]
  have c : ∀ j, j < 4 → (S4 pk m bits answer).getMem (W (dataAddr + (32 + 8 * j))) =
      W (broadcast ([120, 1, Flat.jumpBase0, Flat.jumpBase1].getD j 0)) := by
    intro j hj; rw [S4_mem, ← Nat.add_assoc, S2_const _ _ _ _ j hj]
  have a0 : (S4 pk m bits answer).getMem (W dataAddr) = answer.extractLsb' 0 64 := by
    rw [S4_mem]
    have h := S2_answer pk m bits answer 0 (by norm_num)
    simp only [Nat.mul_zero, Nat.add_zero] at h
    exact h
  have a1 : (S4 pk m bits answer).getMem (W (dataAddr + 8)) = answer.extractLsb' 64 64 := by
    rw [S4_mem]; exact S2_answer pk m bits answer 1 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [loadWords, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, getReg_setReg_ite, MachineState.getMem_setPC,
    MachineState.getMem_setReg]
  · simp [mw 0 (by norm_num), a0]
  · simp [mw 8 (by norm_num), a1]
  · simp [mw 32 (by norm_num), c 0 (by norm_num)]
  · simp [mw 40 (by norm_num), c 1 (by norm_num)]
  · simp [mw 48 (by norm_num), c 2 (by norm_num)]
  · simp [mw 56 (by norm_num), c 3 (by norm_num)]
  · intro r h20 h21 h22 h23 h24 h25
    simp [h20, h21, h22, h23, h24, h25]
  · intro addr; trivial

/-- After the loads. -/
def S45 : MachineState := loadWords.foldl execInstrBr (S4 pk m bits answer)

/-- After the lanes. -/
def S46 : MachineState := lanes.foldl execInstrBr (S45 pk m bits answer)

theorem S5_eq : S5 pk m bits answer = sumOps.foldl execInstrBr (S46 pk m bits answer) := by
  simp [S5, S46, S45, mainBlock, List.foldl_append]

theorem S45_x12 : (S45 pk m bits answer).getReg .x12 = W dataAddr := by
  rw [S45, (loadWords_effect pk m bits answer).regs .x12 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), S4_x12]

theorem lanes_effect :
    Riscv.LinearReady (S45 pk m bits answer) lanes ∧
      LanesEffect (S45 pk m bits answer) (S46 pk m bits answer) 8 := by
  rw [S46, lanes_eq]
  exact lanesUpTo_effect _ (S45_x12 pk m bits answer) (loadWords_effect pk m bits answer).x22 8 le_rfl

theorem mainBlock_ready : Riscv.LinearReady (S4 pk m bits answer) mainBlock := by
  unfold mainBlock
  refine ((loadWords_ready pk m bits answer).append (lanes_effect pk m bits answer).1).append ?_
  simp [sumOps, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem S5_x27 : (S5 pk m bits answer).getReg .x27 =
    (((laneSum (S45 pk m bits answer) 8) * W (broadcast 1)) >>> 48) ^^^ signExtend12 1280 := by
  have L := (lanes_effect pk m bits answer).2
  have x23 : (S46 pk m bits answer).getReg .x23 = W (broadcast 1) := by
    rw [L.regs .x23 (by decide) (by decide)]; exact (loadWords_effect pk m bits answer).x23
  rw [S5_eq]
  simp only [sumOps, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [L.acc (by norm_num), x23]

theorem S5_regs (r : Reg) (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (S5 pk m bits answer).getReg r = (S45 pk m bits answer).getReg r := by
  have L := (lanes_effect pk m bits answer).2
  rw [S5_eq]
  simp only [sumOps, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [h27, L.regs r h26 h27]

theorem S5_mem (addr : Word) : (S5 pk m bits answer).getMem addr = (S46 pk m bits answer).getMem addr := by
  rw [S5_eq]
  simp [sumOps, execInstrBr]

/-- The machine's sum check accepts exactly the accepted indices. -/
theorem sum_iff : (S5 pk m bits answer).getReg .x27 = (S5 pk m bits answer).getReg .x0 ↔
    Accepted (answer.setWidth 128).toNat := by
  have LE := loadWords_effect pk m bits answer
  rw [S5_x27, accepted_iff_wordSum, show (S5 pk m bits answer).getReg .x0 = 0#64 from rfl,
    BitVec.xor_eq_zero_iff]
  have e1280 : signExtend12 (1280 : BitVec 12) = W 1280 := by decide
  have top := top_laneSum (S45 pk m bits answer)
  rw [show (S45 pk m bits answer).getReg .x20 = answer.extractLsb' 0 64 from LE.x20,
    show (S45 pk m bits answer).getReg .x21 = answer.extractLsb' 64 64 from LE.x21] at top
  rw [e1280]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, broadcast_toNat 1 (by norm_num),
      Nat.shiftRight_eq_div_pow, top, W_toNat _ (by norm_num)] at hn
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, broadcast_toNat 1 (by norm_num),
      Nat.shiftRight_eq_div_pow, top, W_toNat _ (by norm_num), h]

theorem S6_regs (r : Reg) : (S6 pk m bits answer).getReg r = (S5 pk m bits answer).getReg r := by
  simp [S6]

theorem S6_mem (addr : Word) : (S6 pk m bits answer).getMem addr = (S5 pk m bits answer).getMem addr := by
  simp [S6]

theorem levelSetup_ready (s : MachineState) : Riscv.LinearReady s levelSetup := by
  simp [levelSetup, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

/-- The registers written by the level setup. -/
theorem afterIndex_levelRegs :
    (afterIndex pk m bits answer).getReg .x1 = 2 ∧ (afterIndex pk m bits answer).getReg .x2 = 3 ∧
    (afterIndex pk m bits answer).getReg .x3 = 4 ∧ (afterIndex pk m bits answer).getReg .x4 = 5 ∧
    (afterIndex pk m bits answer).getReg .x6 = 6 ∧ (afterIndex pk m bits answer).getReg .x7 = 7 ∧
    (afterIndex pk m bits answer).getReg .x8 = 8 ∧ (afterIndex pk m bits answer).getReg .x11 = 192 := by
  unfold afterIndex
  simp only [levelSetup, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [getReg_x0']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem afterIndex_regs (r : Reg) (h1 : r ≠ .x1) (h2 : r ≠ .x2) (h3 : r ≠ .x3) (h4 : r ≠ .x4)
    (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h8 : r ≠ .x8) (h11 : r ≠ .x11) :
    (afterIndex pk m bits answer).getReg r = (S6 pk m bits answer).getReg r := by
  unfold afterIndex
  simp only [levelSetup, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [h1, h2, h3, h4, h6, h7, h8, h11]

theorem afterIndex_mem (addr : Word) :
    (afterIndex pk m bits answer).getMem addr = (S46 pk m bits answer).getMem addr := by
  unfold afterIndex
  simp [levelSetup, execInstrBr, S6_mem, S5_mem]

/-- A register untouched after the prefix. -/
theorem afterIndex_prefixReg (r : Reg) (h1 : r ≠ .x1) (h2 : r ≠ .x2) (h3 : r ≠ .x3) (h4 : r ≠ .x4)
    (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h8 : r ≠ .x8) (h11 : r ≠ .x11) (h20 : r ≠ .x20)
    (h21 : r ≠ .x21) (h22 : r ≠ .x22) (h23 : r ≠ .x23) (h24 : r ≠ .x24) (h25 : r ≠ .x25)
    (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (afterIndex pk m bits answer).getReg r = (afterPrefix pk m bits).getReg r := by
  rw [afterIndex_regs _ _ _ _ r h1 h2 h3 h4 h6 h7 h8 h11, S6_regs, S5_regs _ _ _ _ r h26 h27, S45,
    (loadWords_effect pk m bits answer).regs r h20 h21 h22 h23 h24 h25, S4_regs,
    S3_regs _ _ _ _ r h6]

theorem afterIndex_loadReg (r : Reg) (h1 : r ≠ .x1) (h2 : r ≠ .x2) (h3 : r ≠ .x3) (h4 : r ≠ .x4)
    (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h8 : r ≠ .x8) (h11 : r ≠ .x11) (h26 : r ≠ .x26)
    (h27 : r ≠ .x27) :
    (afterIndex pk m bits answer).getReg r = (S45 pk m bits answer).getReg r := by
  rw [afterIndex_regs _ _ _ _ r h1 h2 h3 h4 h6 h7 h8 h11, S6_regs, S5_regs _ _ _ _ r h26 h27]

/-- Memory outside the index answer, the nonce copy and the lane words is the loader's. -/
theorem afterIndex_frame (addr : Word)
    (h : addr.toNat < dataAddr ∨ dataAddr + 128 ≤ addr.toNat)
    (hn0 : addr ≠ W 0x400000) (hn8 : addr ≠ W 0x400008) :
    (afterIndex pk m bits answer).getMem addr = (S0 pk m bits).getMem addr := by
  have L := (lanes_effect pk m bits answer).2
  rw [afterIndex_mem, L.frame]
  · rw [S45, (loadWords_effect pk m bits answer).mem, S4_mem, S2_frame _ _ _ _ _ (by omega),
      (prefix_effect pk m bits).frame _ hn0 hn8]
  · intro j hj e
    rw [e, W_toNat _ (by unfold laneWordAddr dataAddr; omega)] at h
    unfold laneWordAddr at h
    omega

/-! ## The context at the first chain -/

/-- The accepted index as an element of the index type. -/
def acceptedIdx (hi : Accepted (answer.setWidth 128).toNat) : Idx :=
  ⟨(answer.setWidth 128).toNat, mem_validSet.mpr ⟨(answer.setWidth 128).isLt, hi⟩⟩

theorem afterIndex_payload :
    MemBits (afterIndex pk m bits answer) (W payloadAddr) (ofBits 4096 (bits.drop 128)) := by
  have h0 := initialState_signature image pk m bits image_data_length
  have h := memBits_extract (start := 128) (len := 4096) h0 (by norm_num) (by norm_num)
  rw [ofBits_extract _ (by norm_num), ofBits_drop_take _ (by norm_num)] at h
  have e : Riscv.signatureBase + BitVec.ofNat 64 (128 / 8) = W payloadAddr := by decide
  rw [e] at h
  apply memBits_of_word_frame _ _ _ _ h
  intro i hi
  have ha : (alignToDword (W payloadAddr + BitVec.ofNat 64 (i / 8))).toNat =
      (payloadAddr + i / 8) / 8 * 8 := by
    rw [alignToDword_toNat, W_add, W_toNat _ (by unfold payloadAddr; omega)]
  apply afterIndex_frame
  · right; rw [ha]; unfold payloadAddr dataAddr; omega
  · intro e; have := congrArg BitVec.toNat e; rw [ha, W_toNat _ (by norm_num)] at this
    unfold payloadAddr at this; omega
  · intro e; have := congrArg BitVec.toNat e; rw [ha, W_toNat _ (by norm_num)] at this
    unfold payloadAddr at this; omega

theorem afterIndex_x13 (hlen : bits.length = 4224) :
    (afterIndex pk m bits answer).getReg .x13 = W 4224 := by
  rw [afterIndex_prefixReg _ _ _ _ .x13 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide), (prefix_effect pk m bits).x13, hlen]
  rfl

theorem afterIndex_levels (hlen : bits.length = 4224) (t : ℕ) (ht : t < 15) :
    ((afterIndex pk m bits answer).getReg (levReg t)).truncate 16 =
      BitVec.ofNat 16 (Flat.levVal t) := by
  obtain ⟨r1, r2, r3, r4, r6, r7, r8, r11⟩ := afterIndex_levelRegs pk m bits answer
  have LE := loadWords_effect pk m bits answer
  have P := prefix_effect pk m bits
  have x5 : (afterIndex pk m bits answer).getReg .x5 = 1 := by
    rw [afterIndex_prefixReg _ _ _ _ .x5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), P.x5]
  have x9 : (afterIndex pk m bits answer).getReg .x9 = W payloadAddr := by
    rw [afterIndex_prefixReg _ _ _ _ .x9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), P.x9]
  have x22 : (afterIndex pk m bits answer).getReg .x22 = W (broadcast 120) := by
    rw [afterIndex_loadReg _ _ _ _ .x22 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact LE.x22
  have x24 : (afterIndex pk m bits answer).getReg .x24 = W (broadcast Flat.jumpBase0) := by
    rw [afterIndex_loadReg _ _ _ _ .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact LE.x24
  have x25 : (afterIndex pk m bits answer).getReg .x25 = W (broadcast Flat.jumpBase1) := by
    rw [afterIndex_loadReg _ _ _ _ .x25 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]; exact LE.x25
  have x13 := afterIndex_x13 pk m bits answer hlen
  interval_cases t
  · rw [show levReg 0 = .x5 from rfl, x5]; decide
  · rw [show levReg 1 = .x11 from rfl, r11]; decide
  · rw [show levReg 2 = .x9 from rfl, x9]; decide
  · rw [show levReg 3 = .x22 from rfl, x22]; decide
  · rw [show levReg 4 = .x13 from rfl, x13]; decide
  · rw [show levReg 5 = .x24 from rfl, x24]; decide
  · rw [show levReg 6 = .x25 from rfl, x25]; decide
  · rw [show levReg 7 = .x1 from rfl, r1]; decide
  · rw [show levReg 8 = .x2 from rfl, r2]; decide
  · rw [show levReg 9 = .x3 from rfl, r3]; decide
  · rw [show levReg 10 = .x4 from rfl, r4]; decide
  · rw [show levReg 11 = .x6 from rfl, r6]; decide
  · rw [show levReg 12 = .x7 from rfl, r7]; decide
  · rw [show levReg 13 = .x8 from rfl, r8]; decide
  · rfl

theorem afterIndex_lanes (hi : Accepted (answer.setWidth 128).toNat) (k : Fin 32) :
    ((afterIndex pk m bits answer).getHalfword (W (laneAddr k))).toNat =
      jumpBase k - 8 * (15 - RiscvUpperForest.ForestVerifier.pos (acceptedIdx answer hi) k) := by
  have L := (lanes_effect pk m bits answer).2
  have LE := loadWords_effect pk m bits answer
  have hk := k.isLt
  set j := 4 * (k.val / 16) + k.val % 4 with hj
  set l := k.val % 16 / 4 with hl
  have addr : laneAddr k = laneWordAddr j + 2 * l := by
    unfold laneAddr laneWordAddr dataAddr; omega
  have hjw : j / 4 = k.val / 16 := by omega
  have hji : j % 4 = k.val % 4 := by omega
  rw [addr, getHalfword_lane _ _ _ (by unfold laneWordAddr dataAddr; omega) (by omega)
    (by unfold laneWordAddr dataAddr; omega), afterIndex_mem, L.stored j (by omega)]
  have base : (S45 pk m bits answer).getReg (baseReg (j / 4)) = W (broadcast (jumpBase k)) := by
    rw [hjw]
    unfold baseReg jumpBase
    by_cases h : k.val < 16
    · rw [if_pos (by omega), if_pos h]; exact LE.x24
    · rw [if_neg (by omega), if_neg h]; exact LE.x25
  have word : (S45 pk m bits answer).getReg (wordReg (j / 4)) =
      if k.val / 16 = 0 then answer.extractLsb' 0 64 else answer.extractLsb' 64 64 := by
    rw [hjw]
    unfold wordReg
    split_ifs
    · exact LE.x20
    · exact LE.x21
  have hB : 120 ≤ jumpBase k ∧ jumpBase k < 2 ^ 16 := by
    unfold jumpBase Flat.jumpBase0 Flat.jumpBase1; split_ifs <;> norm_num
  rw [base, lane_halfword _ _ _ l hB.1 hB.2 (by omega) _ (by
    rw [laneOf, word, hji]; exact laneValue_toNat _ _ (by omega))]
  have e4 : 4 * l + k.val % 4 = k.val % 16 := by omega
  rw [e4, ← index_nibble answer k.val hk]
  have hp : RiscvUpperForest.ForestVerifier.pos (acceptedIdx answer hi) k =
      15 - nibble (answer.setWidth 128).toNat k.val :=
    Forest.fixedPositions_val (acceptedIdx answer hi) k
  rw [hp]
  have := nibble_le15 (answer.setWidth 128).toNat k.val
  rw [show 15 - (15 - nibble (answer.setWidth 128).toNat k.val) =
    nibble (answer.setWidth 128).toNat k.val by omega]

theorem afterIndex_ctx (hi : Accepted (answer.setWidth 128).toNat) (hlen : bits.length = 4224) :
    Ctx (afterIndex pk m bits answer) (acceptedIdx answer hi) (bits.drop 128) pk := by
  have P := prefix_effect pk m bits
  obtain ⟨r1, r2, r3, r4, r6, r7, r8, r11⟩ := afterIndex_levelRegs pk m bits answer
  have pre : ∀ r : Reg, r = .x9 ∨ r = .x30 ∨ r = .x31 ∨ r = .x5 →
      (afterIndex pk m bits answer).getReg r = (afterPrefix pk m bits).getReg r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact afterIndex_prefixReg _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, afterIndex_payload pk m bits answer, ?_, ?_, ?_, r11,
    afterIndex_levels pk m bits answer hlen, afterIndex_lanes pk m bits answer hi⟩
  · rw [pre .x9 (Or.inl rfl), P.x9]
  · rw [pre .x30 (Or.inr (Or.inl rfl)), P.x30]
  · rw [pre .x31 (Or.inr (Or.inr (Or.inl rfl))), P.x31]
  · rw [pre .x5 (Or.inr (Or.inr (Or.inr rfl))), P.x5]; rfl

end Tail

/-! ## Refinement -/

theorem reject_refines (s : MachineState) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc reject) (bound : 3 ≤ fuel) :
    Riscv.Refines fuel s (pure (some false)) 3 := by
  let front : Code := [.ADDI .x5 .x0 0, .ADDI .x10 .x0 0]
  have ready : Riscv.LinearReady s front := by
    simp [front, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  have code : Riscv.CodeAt s s.pc (front ++ [.ECALL]) := located
  have pc : (front.foldl execInstrBr s).pc = s.pc + 8 := by
    simpa [front] using Riscv.linear_fold_pc s front ready
  have halt : Riscv.CodeAt (front.foldl execInstrBr s)
      (front.foldl execInstrBr s).pc [.ECALL] := by
    rw [pc]
    exact code.append_right.code_eq (Riscv.fold_code s front)
  have h := Riscv.Refines.linear front code.append_left ready
    (Riscv.Refines.halt (fuel := fuel - 3) false halt.head rfl rfl)
  have total : front.length + (fuel - 3 + 1) = fuel := by simp [front]; omega
  rw [total] at h
  exact h

/-- A failed comparison reaches HALT false; a passed one jumps over the rejection. -/
theorem beq_refines (s : MachineState) (r r' : Reg) (fuel : ℕ) (tail : Code)
    (located : Riscv.CodeAt s s.pc ([.BEQ r r' 16] ++ reject ++ tail)) (bound : 4 ≤ fuel)
    {q : OracleComp Spec (Option Bool)} {c : ℕ} (hc : 3 ≤ c)
    (h : s.getReg r = s.getReg r' → Riscv.Refines (fuel - 1) (s.setPC (s.pc + 16)) q c) :
    Riscv.Refines fuel s (if s.getReg r = s.getReg r' then q else pure (some false)) (c + 1) := by
  have fetch : s.code s.pc = some (.BEQ r r' 16) := located.head
  have transition := beq_transition s r r' fetch
  rw [show fuel = (fuel - 1) + 1 by omega]
  by_cases eq : s.getReg r = s.getReg r'
  · rw [if_pos eq]
    rw [if_pos eq] at transition
    exact Riscv.Refines.branch fetch rfl (fun h => nomatch h) transition (h eq)
  · rw [if_neg eq]
    rw [if_neg eq] at transition
    have rej := reject_refines (s.setPC (s.pc + 4)) (fuel - 1)
      (by
        have l : Riscv.CodeAt s s.pc (.BEQ r r' 16 :: (reject ++ tail)) := located
        exact l.tail.append_left.code_eq rfl) (by omega)
    exact (Riscv.Refines.branch fetch rfl (fun h => nomatch h) transition rej).mono (by omega)

theorem indexPhase_parts : indexPhase = indexPrefix ++ ([.ECALL] ++ (lenBlock ++
    ([.BEQ .x13 .x6 16] ++ reject ++ (mainBlock ++ ([.BEQ .x27 .x0 16] ++ reject ++
      levelSetup))))) := by
  simp only [indexPhase, lengthCheck_parts, sumCheck_parts, mainBlock, List.append_assoc]

theorem indexPhase_length : indexPhase.length = 77 := by decide

theorem mainBlock_length : mainBlock.length = 48 := by decide

section Refine

variable (pk : PublicKey) (m : Message) (bits : List Bool)

theorem pc_add (p : Word) (a b : ℕ) : p + W a + W b = p + W (a + b) := by
  rw [BitVec.add_assoc, W_add]

/-- The index phase: the specified first query, the length and sum rejections, and otherwise the
continuation from `afterIndex`, at 71 cycles plus the continuation. -/
theorem indexPhase_refines (tail : Code) (rest fuel : ℕ)
    (q : BitVec hashBits → OracleComp Spec (Option Bool)) (c : ℕ) (hc : 3 ≤ c)
    (located : Riscv.CodeAt (S0 pk m bits) (S0 pk m bits).pc (indexPhase ++ tail))
    (bound : indexPhase.length + rest ≤ fuel)
    (continuation : ∀ answer, Accepted (answer.setWidth 128).toNat → bits.length = 4224 →
      ∀ left, rest ≤ left → Riscv.Refines left (afterIndex pk m bits answer) (q answer) c) :
    Riscv.Refines fuel (S0 pk m bits) (do
      let answer ← hash (m ++ ofBits 128 bits)
      if Accepted (answer.setWidth 128).toNat ∧ bits.length = 4224 then q answer
      else pure (some false)) (c + 71) := by
  rw [indexPhase_length] at bound
  rw [indexPhase_parts] at located
  simp only [List.append_assoc] at located
  have P := prefix_effect pk m bits
  -- the prefix
  have ready := indexPrefix_ready pk m bits
  rw [show fuel = indexPrefix.length + ((fuel - 11) + 1) by rw [indexPrefix_length]; omega,
    show c + 71 = indexPrefix.length + (1 + (c + 60)) by rw [indexPrefix_length]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  have callLocated : Riscv.CodeAt (afterPrefix pk m bits) (afterPrefix pk m bits).pc
      ([.ECALL] ++ (lenBlock ++ ([.BEQ .x13 .x6 16] ++ reject ++ (mainBlock ++
        ([.BEQ .x27 .x0 16] ++ reject ++ (levelSetup ++ tail)))))) := by
    have h := located.append_right
    have e : (afterPrefix pk m bits).pc = (S0 pk m bits).pc +
        BitVec.ofNat 64 (4 * indexPrefix.length) := Riscv.linear_fold_pc _ _ ready
    rw [e]
    simpa only [List.append_assoc] using h.code_eq P.code
  have hashed := Riscv.Refines.hash (fuel := fuel - 11) callLocated.head P.x5
    (prefix_hashValid pk m bits) (c := c + 60)
    (k := fun answer => if Accepted (answer.setWidth 128).toNat ∧ bits.length = 4224 then q answer
      else pure (some false)) ?_
  · rw [prefix_hashInput pk m bits] at hashed
    dsimp only at hashed
    rw [show blockCost 384 = 1 by decide] at hashed
    exact hashed
  intro answer
  -- the length check
  have S2code : Riscv.CodeAt (S2 pk m bits answer) (S2 pk m bits answer).pc
      (lenBlock ++ ([.BEQ .x13 .x6 16] ++ reject ++ (mainBlock ++
        ([.BEQ .x27 .x0 16] ++ reject ++ (levelSetup ++ tail))))) :=
    callLocated.tail.code_eq (by simp [Riscv.writeHash])
  have lenReady : Riscv.LinearReady (S2 pk m bits answer) lenBlock := by
    simp [lenBlock, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  rw [show fuel - 11 = lenBlock.length + (fuel - 13) by simp [lenBlock]; omega,
    show c + 60 = lenBlock.length + (c + 58) by simp [lenBlock]; omega]
  apply Riscv.Refines.linear _ S2code.append_left lenReady
  have S3code : Riscv.CodeAt (S3 pk m bits answer) (S3 pk m bits answer).pc
      ([.BEQ .x13 .x6 16] ++ reject ++ (mainBlock ++
        ([.BEQ .x27 .x0 16] ++ reject ++ (levelSetup ++ tail)))) := by
    have h := S2code.append_right
    rw [show (S3 pk m bits answer).pc = (S2 pk m bits answer).pc + BitVec.ofNat 64 (4 * lenBlock.length)
      from Riscv.linear_fold_pc _ _ lenReady]
    exact h.code_eq (Riscv.fold_code _ _)
  have reorder : (if Accepted (answer.setWidth 128).toNat ∧ bits.length = 4224 then q answer
      else pure (some false)) =
      if (S3 pk m bits answer).getReg .x13 = (S3 pk m bits answer).getReg .x6 then
        (if (S5 pk m bits answer).getReg .x27 = (S5 pk m bits answer).getReg .x0 then q answer
          else pure (some false)) else pure (some false) := by
    by_cases hl : bits.length = 4224
    · rw [if_pos ((length_iff pk m bits answer).mpr hl)]
      by_cases ha : Accepted (answer.setWidth 128).toNat
      · rw [if_pos ⟨ha, hl⟩, if_pos ((sum_iff pk m bits answer).mpr ha)]
      · rw [if_neg (fun h => ha h.1), if_neg (fun h => ha ((sum_iff pk m bits answer).mp h))]
    · rw [if_neg (fun h => hl h.2), if_neg (fun h => hl ((length_iff pk m bits answer).mp h))]
  rw [reorder, show c + 58 = (c + 57) + 1 by omega]
  apply beq_refines _ _ _ _ _ S3code (by omega) (by omega)
  intro hlenEq
  have hl := (length_iff pk m bits answer).mp hlenEq
  -- the loads, the lanes and the sum
  have S4code : Riscv.CodeAt (S4 pk m bits answer) (S4 pk m bits answer).pc
      (mainBlock ++ ([.BEQ .x27 .x0 16] ++ reject ++ (levelSetup ++ tail))) := by
    have h := S3code.append_right (first := [.BEQ .x13 .x6 16] ++ reject)
    rw [show (4 * ([Instr.BEQ .x13 .x6 16] ++ reject).length) = 16 from rfl] at h
    exact h.code_eq (by simp [S4])
  have mReady := mainBlock_ready pk m bits answer
  rw [show fuel - 13 - 1 = mainBlock.length + (fuel - 62) by rw [mainBlock_length]; omega,
    show c + 57 = mainBlock.length + (c + 9) by rw [mainBlock_length]; omega]
  apply Riscv.Refines.linear _ (S4code.append_left) mReady
  have S5code : Riscv.CodeAt (S5 pk m bits answer) (S5 pk m bits answer).pc
      ([.BEQ .x27 .x0 16] ++ reject ++ (levelSetup ++ tail)) := by
    have h := S4code.append_right
    rw [show (S5 pk m bits answer).pc = (S4 pk m bits answer).pc +
      BitVec.ofNat 64 (4 * mainBlock.length) from Riscv.linear_fold_pc _ _ mReady]
    exact h.code_eq (Riscv.fold_code _ _)
  rw [show c + 9 = (c + 8) + 1 by omega]
  apply beq_refines _ _ _ _ _ S5code (by omega) (by omega)
  intro hsumEq
  have ha := (sum_iff pk m bits answer).mp hsumEq
  -- the level tags
  have S6code : Riscv.CodeAt (S6 pk m bits answer) (S6 pk m bits answer).pc (levelSetup ++ tail) := by
    have h := S5code.append_right (first := [.BEQ .x27 .x0 16] ++ reject)
    rw [show (4 * ([Instr.BEQ .x27 .x0 16] ++ reject).length) = 16 from rfl] at h
    exact h.code_eq (by simp [S6])
  rw [show fuel - 62 - 1 = levelSetup.length + (fuel - 71) by simp [levelSetup]; omega,
    show c + 8 = levelSetup.length + c by simp [levelSetup]; omega]
  apply Riscv.Refines.linear _ S6code.append_left (levelSetup_ready _)
  exact continuation answer ha hl _ (by omega)

/-- Where the index phase ends. -/
theorem afterIndex_pc (answer : BitVec hashBits) :
    (afterIndex pk m bits answer).pc = W (blockStart 0) := by
  have lenReady : Riscv.LinearReady (S2 pk m bits answer) lenBlock := by
    simp [lenBlock, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  have e1 : (afterIndex pk m bits answer).pc = (S6 pk m bits answer).pc +
      BitVec.ofNat 64 (4 * levelSetup.length) := Riscv.linear_fold_pc _ _ (levelSetup_ready _)
  have e2 : (S6 pk m bits answer).pc = (S5 pk m bits answer).pc + 16 := rfl
  have e3 : (S5 pk m bits answer).pc = (S4 pk m bits answer).pc +
      BitVec.ofNat 64 (4 * mainBlock.length) :=
    Riscv.linear_fold_pc _ _ (mainBlock_ready pk m bits answer)
  have e4 : (S4 pk m bits answer).pc = (S3 pk m bits answer).pc + 16 := rfl
  have e5 : (S3 pk m bits answer).pc = (S2 pk m bits answer).pc +
      BitVec.ofNat 64 (4 * lenBlock.length) := Riscv.linear_fold_pc _ _ lenReady
  have e6 : (S2 pk m bits answer).pc = (afterPrefix pk m bits).pc + 4 := rfl
  rw [e1, e2, e3, e4, e5, e6, (prefix_effect pk m bits).pc, mainBlock_length]
  simp only [levelSetup, lenBlock, List.length_cons, List.length_nil]
  decide

theorem afterIndex_code (answer : BitVec hashBits) :
    (afterIndex pk m bits answer).code = (S0 pk m bits).code := by
  unfold afterIndex S6 S5 S4
  rw [Riscv.fold_code, MachineState.code_setPC, Riscv.fold_code, MachineState.code_setPC,
    S3_code]

end Refine

end OptimalOTS.RiscvUpperProgram
