import Submissions.UpperRiscv.MixedDispatchArith
import Submissions.UpperRiscv.MixedContext

/-!
# The index phase

The machine saves the public key, hashes `pk ‖ message ‖ nonce`, rejects wrong lengths, builds
the four lane words, folds and rejects unless the fields sum to `157`, and sets the chain input
length: the state `afterIndex` then satisfies the chain-phase invariant.
-/

namespace OptimalOTS.RiscvMixedProgram

open Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 OracleComp

/-! ## The data image -/

theorem dataImage_length : dataImage.length = 104 := by decide

/-- The nine constant words of the data image, after the 32-byte answer buffer. -/
def dataWord (j : ℕ) : ℕ :=
  [firstMask, broadcast 0x1e3c, broadcast 0x1fc, 65535, 0, 5504,
    baseWord 0, baseWord 1, baseWord 2].getD j 0

theorem dataImage_word (j : ℕ) (hj : j < 9) :
    bytesToWordLE ((dataImage.drop (8 * (4 + j))).take 8) = W (dataWord j) := by
  interval_cases j <;> decide

theorem initial_data_word (pk : PublicKey) (m : Message) (bits : List Bool) (j : ℕ) (hj : j < 9) :
    (Riscv.initialState image pk m bits).getMem (W (dataAddr + 32 + 8 * j)) = W (dataWord j) := by
  have hlen : image.data.length = 104 := dataImage_length
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

/-- The signature length, the tenth word of the data image. -/
theorem initial_data_len (pk : PublicKey) (m : Message) (bits : List Bool) :
    (Riscv.initialState image pk m bits).getMem (W (dataAddr + 72)) = W 5504 := by
  have h := initial_data_word pk m bits 5 (by norm_num)
  rw [show dataAddr + 32 + 8 * 5 = dataAddr + 72 by norm_num] at h
  exact h

/-! ## The prefix and the index query -/

section Prefix

variable (pk : PublicKey) (m : Message) (bits : List Bool)

/-- The loader's state. -/
abbrev S0 : MachineState := Riscv.initialState image pk m bits

theorem S0_regs :
    (S0 pk m bits).getReg .x10 = W 0x400000 ∧ (S0 pk m bits).getReg .x11 = W 0x400010 ∧
    (S0 pk m bits).getReg .x12 = W 0x400030 ∧
    (S0 pk m bits).getReg .x13 = BitVec.ofNat 64 (min bits.length 5505) := ⟨rfl, rfl, rfl, rfl⟩

theorem S0_pc : (S0 pk m bits).pc = W 4096 := by
  simp [Riscv.initialState]; rfl

/-- The state before the index query. -/
def afterPrefix : MachineState := indexPrefix.foldl execInstrBr (S0 pk m bits)

theorem indexPrefix_ready : Riscv.LinearReady (S0 pk m bits) indexPrefix := by
  simp [indexPrefix, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    execInstrBr, Riscv.initialState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, Riscv.signatureBase, Riscv.publicKeyBase,
    signExtend12, MachineState.getMem, MEM_START, MEM_END]

theorem indexPrefix_length : indexPrefix.length = 5 := rfl

structure PrefixEffect (s : MachineState) : Prop where
  x30 : s.getReg .x30 = pk.extractLsb' 0 64
  x31 : s.getReg .x31 = pk.extractLsb' 64 64
  x10 : s.getReg .x10 = W 0x400000
  x11 : s.getReg .x11 = 512
  x12 : s.getReg .x12 = W dataAddr
  x5 : s.getReg .x5 = 1
  x13 : s.getReg .x13 = BitVec.ofNat 64 (min bits.length 5505)
  frame : ∀ addr, s.getMem addr = (S0 pk m bits).getMem addr
  pc : s.pc = W (4096 + 20)
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
  have l0 : signExtend12 (BitVec.ofNat 12 0) = 0 := by decide
  have l8 : signExtend12 (BitVec.ofNat 12 8) = W 8 := by decide
  have r10 := (S0_regs pk m bits).1
  have r13 := (S0_regs pk m bits).2.2.2
  have w0 := pk_word0 pk m bits
  have w1 := pk_word1 pk m bits
  have hmem : ∀ addr, (afterPrefix pk m bits).getMem addr = (S0 pk m bits).getMem addr := by
    intro addr; simp [afterPrefix, indexPrefix, execInstrBr]
  have hpc : (afterPrefix pk m bits).pc = W (4096 + 20) := by
    show (S0 pk m bits).pc + 4 + 4 + 4 + 4 + 4 = _
    rw [S0_pc]; decide
  have hcode : (afterPrefix pk m bits).code = (S0 pk m bits).code := by
    simp [afterPrefix, indexPrefix, execInstrBr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem, hpc, hcode⟩
  all_goals simp [afterPrefix, indexPrefix, execInstrBr, getReg_setReg_ite, l0, l8, r10, r13, w0,
    w1, W_add, getReg_x0', BitVec.add_zero]
  all_goals rfl

theorem image_data_length : image.data.length ≤ 1048576 := by
  rw [show image.data = dataImage from rfl, dataImage_length]; norm_num

set_option maxRecDepth 100000 in
/-- The public key, the message and the nonce lie at the loader's addresses:
`pk ‖ message ‖ nonce` with the public key in the low bits is the specification's query input. -/
theorem prefix_memBits :
    MemBits (afterPrefix pk m bits) (W 0x400000)
      (swapHalves (emsg m pk ++ ofBits nonceBits bits)) := by
  have E := prefix_effect pk m bits
  have hm : msgBits = 256 := rfl
  have hn : nonceBits = 128 := rfl
  have hp : pkBits = 128 := rfl
  rw [swapHalves_append]
  apply (memBits_cast _ _ _ _).mpr
  apply memBits_of_words _ _ _ (by decide)
  intro j hj
  change j < 8 at hj
  rw [W_add, E.frame]
  unfold emsg
  by_cases hpk : j < 2
  · have hw := initialState_publicKey_word image pk m bits j (by omega)
    have e : Riscv.publicKeyBase + BitVec.ofNat 64 (8 * j) = W (0x400000 + 8 * j) := by
      rw [show Riscv.publicKeyBase = W 0x400000 from rfl, W_add]
    rw [e] at hw
    rw [hw, BitVec.extractLsb'_append_eq_of_add_le (by omega),
      BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  · by_cases hlow : j < 6
    · have hw := initialState_message_word image pk m bits (j - 2) (by omega)
      have e : Riscv.messageBase + BitVec.ofNat 64 (8 * (j - 2)) = W (0x400000 + 8 * j) := by
        rw [show Riscv.messageBase = W 0x400010 from rfl, W_add]
        congr 1
        omega
      rw [e] at hw
      rw [hw, BitVec.extractLsb'_append_eq_of_add_le (by omega),
        BitVec.extractLsb'_append_eq_of_le (by omega),
        show 64 * j - pkBits = 64 * (j - 2) by rw [hp]; omega]
    · have hs := initialState_signature_word image pk m bits image_data_length (j - 6) (by omega)
      have e : Riscv.signatureBase + BitVec.ofNat 64 (8 * (j - 6)) = W (0x400000 + 8 * j) := by
        rw [show Riscv.signatureBase = W 0x400030 from rfl, W_add]
        congr 1
        omega
      rw [e] at hs
      rw [hs, BitVec.extractLsb'_append_eq_of_le (by omega), ofBits_extract _ (by omega),
        ofBits_drop_take _ (by omega),
        show 64 * j - (msgBits + pkBits) = 64 * (j - 6) by rw [hm, hp]; omega]

theorem prefix_hashInput :
    Riscv.hashInput (afterPrefix pk m bits) =
      ⟨512, swapHalves (emsg m pk ++ ofBits nonceBits bits)⟩ := by
  have E := prefix_effect pk m bits
  apply hashInput_of_memBits E.x10 (by rw [E.x11]; rfl) (prefix_memBits pk m bits)

theorem prefix_hashValid : Riscv.hashArgumentsValid (afterPrefix pk m bits) = true := by
  have E := prefix_effect pk m bits
  have r1 : isValidOutputRange (W 0x400000) 64 = true :=
    range_ok _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r2 := hashOutput_ok dataAddr (by unfold dataAddr; omega) (by unfold dataAddr; omega)
    (by unfold dataAddr; omega)
  have e : ((512 : Word).toNat + 7) / 8 = 64 := rfl
  unfold Riscv.hashArgumentsValid
  rw [E.x10, E.x11, E.x12, e, r1, Bool.true_and]
  exact r2

end Prefix

/-! ## After the index query -/

section Tail

variable (pk : PublicKey) (m : Message) (bits : List Bool) (answer : BitVec hashBits)

abbrev S2 : MachineState := Riscv.writeHash (afterPrefix pk m bits) answer

def lenBlock : Code := [.LD .x6 .x12 (BitVec.ofNat 12 72)]

theorem lengthCheck_parts : lengthCheck = lenBlock ++ ([.BEQ .x13 .x6 16] ++ reject) := rfl

def S3 : MachineState := lenBlock.foldl execInstrBr (S2 pk m bits answer)

def S4 : MachineState := (S3 pk m bits answer).setPC ((S3 pk m bits answer).pc + 16)

def sumOps : Code :=
  [.REMU .x27 .x27 .x2, .XORI .x27 .x27 (BitVec.ofNat 12 (4 * target))]

theorem sumCheck_parts : sumCheck = sumOps ++ ([.BEQ .x27 .x0 16] ++ reject) := rfl

def mainBlock : Code := loadWords ++ lanes ++ fold ++ sumOps

def S5 : MachineState := mainBlock.foldl execInstrBr (S4 pk m bits answer)

def S6 : MachineState := (S5 pk m bits answer).setPC ((S5 pk m bits answer).pc + 16)

/-- The state after the index phase, at the first chain block. -/
def afterIndex : MachineState := chainSetup.foldl execInstrBr (S6 pk m bits answer)

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

/-- The constants of the data image are still in place after the index query. -/
theorem S2_const (j : ℕ) (hj : j < 9) :
    (S2 pk m bits answer).getMem (W (dataAddr + 32 + 8 * j)) = W (dataWord j) := by
  rw [S2_frame _ _ _ _ _ (Or.inr (by rw [W_toNat _ (by unfold dataAddr; omega)]; omega)),
    (prefix_effect pk m bits).frame, initial_data_word pk m bits j hj]

/-- The signature-length word survives the index hash and the prefix. -/
theorem S2_len : (S2 pk m bits answer).getMem (W (dataAddr + 72)) = W 5504 := by
  have h := S2_const pk m bits answer 5 (by norm_num)
  rw [show dataAddr + 32 + 8 * 5 = dataAddr + 72 by norm_num] at h
  exact h

theorem S3_regs (r : Reg) (hr : r ≠ .x6) :
    (S3 pk m bits answer).getReg r = (afterPrefix pk m bits).getReg r := by
  unfold S3
  simp [lenBlock, execInstrBr, getReg_setReg_ite, hr, S2_regs]

theorem S3_x6 : (S3 pk m bits answer).getReg .x6 = W 5504 := by
  unfold S3
  simp only [lenBlock, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, if_true]
  rw [S2_regs, (prefix_effect pk m bits).x12, signExtend12_nat 72 (by norm_num), W_add, S2_len]

theorem S3_mem (addr : Word) : (S3 pk m bits answer).getMem addr = (S2 pk m bits answer).getMem addr := by
  unfold S3
  simp [lenBlock, execInstrBr]

theorem S3_code : (S3 pk m bits answer).code = (S0 pk m bits).code := by
  unfold S3
  simp [lenBlock, execInstrBr, Riscv.writeHash, (prefix_effect pk m bits).code]

theorem length_iff : (S3 pk m bits answer).getReg .x13 = (S3 pk m bits answer).getReg .x6 ↔
    bits.length = 5504 := by
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

/-- The words and constants loaded before the lanes. -/
structure LoadEffect (a b : MachineState) : Prop where
  x20 : b.getReg .x20 = wordOf answer 0
  x21 : b.getReg .x21 = wordOf answer 1
  x22 : b.getReg .x22 = wordOf answer 2
  x23 : b.getReg .x23 = wordOf answer 3
  x25 : b.getReg .x25 = W (broadcast 0x1e3c)
  x1 : b.getReg .x1 = W (broadcast 0x1fc)
  x2 : b.getReg .x2 = W (65535)
  x3 : b.getReg .x3 = W (baseWord 0)
  x4 : b.getReg .x4 = W (baseWord 1)
  x7 : b.getReg .x7 = W (baseWord 2)
  regs : ∀ r, r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → r ≠ .x1 →
    r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x7 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = a.getMem addr

/-- A register the loads leave alone. -/
abbrev LoadFree (r : Reg) : Prop :=
  r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x25 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧
    r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x7

theorem LoadEffect.regs' {a b : MachineState} (E : LoadEffect answer a b) (r : Reg)
    (h : LoadFree r) : b.getReg r = a.getReg r :=
  E.regs r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2

theorem S4_x12 : (S4 pk m bits answer).getReg .x12 = W dataAddr := by
  rw [S4_regs, S3_regs _ _ _ _ _ (by decide), (prefix_effect pk m bits).x12]

theorem loadWords_ready : Riscv.LinearReady (S4 pk m bits answer) loadWords := by
  have h12 := S4_x12 pk m bits answer
  simp only [loadWords, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, true_and, and_true]
  simp only [show ¬ (Reg.x12 = Reg.x20) by decide, show ¬ (Reg.x12 = Reg.x21) by decide,
    show ¬ (Reg.x12 = Reg.x22) by decide, show ¬ (Reg.x12 = Reg.x23) by decide,
    show ¬ (Reg.x12 = Reg.x24) by decide, show ¬ (Reg.x12 = Reg.x25) by decide,
    show ¬ (Reg.x12 = Reg.x1) by decide, show ¬ (Reg.x12 = Reg.x2) by decide,
    show ¬ (Reg.x12 = Reg.x3) by decide, show ¬ (Reg.x12 = Reg.x4) by decide,
    false_and, if_false, h12]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold dataAddr; decide)

theorem loadWords_effect :
    LoadEffect answer (S4 pk m bits answer) (loadWords.foldl execInstrBr (S4 pk m bits answer)) := by
  have h12 := S4_x12 pk m bits answer
  have mw : ∀ off : ℕ, off < 2048 → (S4 pk m bits answer).getReg .x12 +
      signExtend12 (BitVec.ofNat 12 off) = W (dataAddr + off) := by
    intro off hoff; rw [h12, signExtend12_nat _ hoff, W_add]
  have c : ∀ j, j < 9 → (S4 pk m bits answer).getMem (W (dataAddr + (32 + 8 * j))) = W (dataWord j) := by
    intro j hj; rw [S4_mem, ← Nat.add_assoc, S2_const _ _ _ _ j hj]
  have a : ∀ j, j < 4 → (S4 pk m bits answer).getMem (W (dataAddr + 8 * j)) = wordOf answer j := by
    intro j hj; rw [S4_mem]; exact S2_answer pk m bits answer j hj
  have a0 := a 0 (by norm_num)
  simp only [Nat.mul_zero, Nat.add_zero] at a0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [loadWords, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, getReg_setReg_ite, MachineState.getMem_setPC,
    MachineState.getMem_setReg]
  · simp [mw 0 (by norm_num), a0]
  · simp [mw 8 (by norm_num), a 1 (by norm_num)]
  · simp [mw 16 (by norm_num), a 2 (by norm_num)]
  · simp [mw 24 (by norm_num), a 3 (by norm_num)]
  · simp [mw 40 (by norm_num), c 1 (by norm_num), dataWord]
  · simp [mw 48 (by norm_num), c 2 (by norm_num), dataWord]
  · simp [mw 56 (by norm_num), c 3 (by norm_num), dataWord]
  · simp [mw 80 (by norm_num), c 6 (by norm_num), dataWord]
  · simp [mw 88 (by norm_num), c 7 (by norm_num), dataWord]
  · simp [mw 96 (by norm_num), c 8 (by norm_num), dataWord]
  · intro r h20 h21 h22 h23 h24 h25 h1 h2 h3 h4 h7
    simp [h20, h21, h22, h23, h24, h25, h1, h2, h3, h4, h7]
  · intro addr; trivial

/-- After the loads. -/
def S45 : MachineState := loadWords.foldl execInstrBr (S4 pk m bits answer)

/-- After the lanes. -/
def S46 : MachineState := lanes.foldl execInstrBr (S45 pk m bits answer)

/-- After the fold. -/
def S47 : MachineState := fold.foldl execInstrBr (S46 pk m bits answer)

theorem S5_eq : S5 pk m bits answer = sumOps.foldl execInstrBr (S47 pk m bits answer) := by
  simp [S5, S47, S46, S45, mainBlock, List.foldl_append]

theorem S45_x12 : (S45 pk m bits answer).getReg .x12 = W dataAddr := by
  rw [S45, LoadEffect.regs' answer (loadWords_effect pk m bits answer) .x12 (by decide), S4_x12]

theorem S45_x10 : (S45 pk m bits answer).getReg .x10 = W hashBase := by
  rw [S45, LoadEffect.regs' answer (loadWords_effect pk m bits answer) .x10 (by decide), S4_regs,
    S3_regs _ _ _ _ _ (by decide), (prefix_effect pk m bits).x10]
  rfl

theorem S45_masks : MasksLoaded (S45 pk m bits answer) := by
  have LE := loadWords_effect pk m bits answer
  intro g _
  exact LE.x25

theorem S45_words : WordsLoaded (S45 pk m bits answer) answer := by
  have LE := loadWords_effect pk m bits answer
  intro w hw
  interval_cases w
  · exact LE.x20
  · exact LE.x21
  · exact LE.x22
  · exact LE.x23

theorem S45_bases (g : ℕ) (hg : g < 4) :
    (S45 pk m bits answer).getReg (baseReg g) = W (baseWord g) := by
  have LE := loadWords_effect pk m bits answer
  interval_cases g
  · exact LE.x3
  · exact LE.x4
  · exact LE.x7
  · rw [baseWord_last]; exact LE.x7

theorem lanes_effect :
    Riscv.LinearReady (S45 pk m bits answer) lanes ∧
      LanesEffect (S45 pk m bits answer) (S46 pk m bits answer) 4 := by
  rw [S46, lanes_eq]
  exact lanesUpTo_effect _ (S45_x10 pk m bits answer) 4 le_rfl

theorem fold_effect' : FoldEffect (S46 pk m bits answer) (S47 pk m bits answer) :=
  fold_effect _

theorem mainBlock_ready : Riscv.LinearReady (S4 pk m bits answer) mainBlock := by
  unfold mainBlock
  refine (((loadWords_ready pk m bits answer).append (lanes_effect pk m bits answer).1).append
    (fold_ready _)).append ?_
  simp [sumOps, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem S46_x1 : (S46 pk m bits answer).getReg .x1 = W (broadcast 0x1fc) := by
  rw [(lanes_effect pk m bits answer).2.regs .x1 (by decide) (by decide)]
  exact (loadWords_effect pk m bits answer).x1

theorem S5_x27 : (S5 pk m bits answer).getReg .x27 =
    (rv64_remu (foldValue (laneSum (S45 pk m bits answer) 4) ((S45 pk m bits answer).getReg .x1))
      (W 65535)) ^^^ signExtend12 (BitVec.ofNat 12 (4 * target)) := by
  have L := (lanes_effect pk m bits answer).2
  have F := fold_effect' pk m bits answer
  have x2 : (S47 pk m bits answer).getReg .x2 = W (65535) := by
    rw [F.regs .x2 (by decide) (by decide), L.regs .x2 (by decide) (by decide)]
    exact (loadWords_effect pk m bits answer).x2
  have x1 : (S46 pk m bits answer).getReg .x1 = (S45 pk m bits answer).getReg .x1 :=
    L.regs .x1 (by decide) (by decide)
  rw [S5_eq]
  simp only [sumOps, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [F.acc, L.acc (by norm_num), x1, x2]

theorem S5_regs (r : Reg) (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (S5 pk m bits answer).getReg r = (S45 pk m bits answer).getReg r := by
  have L := (lanes_effect pk m bits answer).2
  have F := fold_effect' pk m bits answer
  rw [S5_eq]
  simp only [sumOps, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [h27, F.regs r h26 h27, L.regs r h26 h27]

theorem S5_mem (addr : Word) : (S5 pk m bits answer).getMem addr = (S46 pk m bits answer).getMem addr := by
  have F := fold_effect' pk m bits answer
  rw [S5_eq]
  simp [sumOps, execInstrBr, F.mem]

/-- The machine's sum check accepts exactly the accepted indices. -/
theorem sum_iff : (S5 pk m bits answer).getReg .x27 = (S5 pk m bits answer).getReg .x0 ↔
    Accepted (pack answer) := by
  rw [S5_x27, accepted_iff, show (S5 pk m bits answer).getReg .x0 = 0#64 from rfl,
    BitVec.xor_eq_zero_iff]
  have e628 : signExtend12 (BitVec.ofNat 12 (4 * target)) = W 628 := by decide
  have total := remainder_fold_answer (S45 pk m bits answer) (S45_masks pk m bits answer) answer
    (S45_words pk m bits answer) (loadWords_effect pk m bits answer).x1
  rw [e628]
  have e : ∀ x : Word, (rv64_remu x (W 65535)).toNat = x.toNat % 65535 := by
    intro x
    simp [rv64_remu, W, BitVec.toNat_umod]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [e, total, W_toNat _ (by norm_num)] at hn
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [e, total, W_toNat _ (by norm_num), h]

theorem S6_regs (r : Reg) : (S6 pk m bits answer).getReg r = (S5 pk m bits answer).getReg r := by
  simp [S6]

theorem S6_mem (addr : Word) : (S6 pk m bits answer).getMem addr = (S5 pk m bits answer).getMem addr := by
  simp [S6]

theorem setup_ready (s : MachineState) : Riscv.LinearReady s chainSetup := by
  simp [chainSetup, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem minus24 : signExtend12 (BitVec.ofInt 12 (-24)) = BitVec.ofInt 64 (-24) :=
  signExtend12_imm (-24) (by norm_num) (by norm_num)

/-- The registers written by the setup, and the input pointer still at the message. -/
theorem afterIndex_setupRegs :
    (afterIndex pk m bits answer).getReg .x11 = 160 ∧
    (afterIndex pk m bits answer).getReg .x10 = W hashBase := by
  have x10 : (S6 pk m bits answer).getReg .x10 = W hashBase := by
    rw [S6_regs, S5_regs _ _ _ _ _ (by decide) (by decide), S45_x10]
  unfold afterIndex
  simp only [chainSetup, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, if_false, getReg_x0', x10]
  decide

theorem afterIndex_regs (r : Reg) (h11 : r ≠ .x11) :
    (afterIndex pk m bits answer).getReg r = (S6 pk m bits answer).getReg r := by
  unfold afterIndex
  simp only [chainSetup, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [h11]

theorem afterIndex_mem (addr : Word) :
    (afterIndex pk m bits answer).getMem addr = (S46 pk m bits answer).getMem addr := by
  unfold afterIndex
  simp [chainSetup, execInstrBr, S6_mem, S5_mem]

/-- A register untouched after the prefix. -/
theorem afterIndex_prefixReg (r : Reg) (h11 : r ≠ .x11) (h6 : r ≠ .x6) (hl : LoadFree r)
    (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (afterIndex pk m bits answer).getReg r = (afterPrefix pk m bits).getReg r := by
  rw [afterIndex_regs _ _ _ _ r h11, S6_regs, S5_regs _ _ _ _ r h26 h27, S45,
    LoadEffect.regs' answer (loadWords_effect pk m bits answer) r hl, S4_regs,
    S3_regs _ _ _ _ r h6]

theorem afterIndex_code : (afterIndex pk m bits answer).code = (S0 pk m bits).code := by
  unfold afterIndex S6 S5 S4
  rw [Riscv.fold_code, MachineState.code_setPC, Riscv.fold_code, MachineState.code_setPC,
    S3_code]

/-- Memory outside the index answer and the lane words is the loader's. -/
theorem afterIndex_frame (addr : Word)
    (h : (addr.toNat < dataAddr ∨ dataAddr + 32 ≤ addr.toNat) ∧
      (addr.toNat < laneBase ∨ laneBase + 32 ≤ addr.toNat)) :
    (afterIndex pk m bits answer).getMem addr = (S0 pk m bits).getMem addr := by
  have L := (lanes_effect pk m bits answer).2
  rw [afterIndex_mem, L.frame]
  · rw [S45, (loadWords_effect pk m bits answer).mem, S4_mem, S2_frame _ _ _ _ _ h.1,
      (prefix_effect pk m bits).frame]
  · intro j hj e
    have h2 := h.2
    rw [e, W_toNat _ (by unfold laneWordAddr laneBase; omega)] at h2
    unfold laneWordAddr at h2
    omega

/-! ## The context at the first chain -/

/-- The accepted index as an element of the index type. -/
def acceptedIdx (hi : Accepted (pack answer)) : Idx :=
  ⟨pack answer, mem_validSet.mpr ⟨pack_lt answer, hi⟩⟩

theorem afterIndex_x13 (hlen : bits.length = 5504) :
    (afterIndex pk m bits answer).getReg .x13 = W 5504 := by
  rw [afterIndex_prefixReg _ _ _ _ .x13 (by decide) (by decide) (by decide) (by decide)
    (by decide), (prefix_effect pk m bits).x13, hlen]
  rfl

theorem laneGroup_lt (q : ℕ) (hq : q < 16) : laneGroup q < 4 := by
  unfold laneGroup; omega

theorem laneIdx_lt (q : ℕ) (_hq : q < 16) : laneIdx q < 4 := by
  unfold laneIdx; omega

theorem fineChain_lane (q : ℕ) (_hq : q < 16) : fineChain (laneGroup q) (laneIdx q) = firstChain q := by
  unfold fineChain laneGroup laneIdx firstChain; omega

theorem coarseChain_lane (q : ℕ) (_hq : q < 16) : coarseChain (laneGroup q) (laneIdx q) = 2*q+1 := by
  unfold coarseChain laneGroup laneIdx; omega

/-- The stored halfwords hold the dispatch values for all sixteen chain pairs. -/
theorem afterIndex_lanes (hi : Accepted (pack answer)) (q : Fin 16) :
    ((afterIndex pk m bits answer).getHalfword (W (laneAddr q))).toNat =
      baseLane q - dispatch (acceptedIdx answer hi) q := by
  have L := (lanes_effect pk m bits answer).2
  have hq := q.isLt
  have hg := laneGroup_lt q hq
  have hl := laneIdx_lt q hq
  have addr : laneAddr q = laneWordAddr (laneGroup q) + 2*laneIdx q := by
    unfold laneAddr laneWordAddr laneGroup laneIdx; omega
  rw [addr, getHalfword_lane _ _ _ (by unfold laneWordAddr laneBase; omega) hl
    (by unfold laneWordAddr laneBase; omega), afterIndex_mem, L.stored _ hg,
    S45_bases pk m bits answer _ hg,
    lane_halfword _ _ _ hg hl _ (laneOf_toNat _ (S45_masks pk m bits answer) _ hg),
    S45_words pk m bits answer _ hg, fine_word answer _ _ hg hl, fineChain_lane q hq,
    coarse_word answer _ _ hg hl, coarseChain_lane q hq]
  have eq : 4*laneGroup q+laneIdx q = q := by unfold laneGroup laneIdx; omega
  rw [eq]
  unfold dispatch coarseDigit firstChain acceptedIdx
  rw [digit_pack answer (by omega : 2*q.val < 32), digit_pack answer (by omega : 2*q.val+1 < 32)]

theorem afterIndex_ctx (hi : Accepted (pack answer)) (hlen : bits.length = 5504)
    (located : Riscv.CodeAt (S0 pk m bits) (W 4096) verifier) :
    Ctx (afterIndex pk m bits answer) (acceptedIdx answer hi) pk := by
  have P := prefix_effect pk m bits
  obtain ⟨r11, r10⟩ := afterIndex_setupRegs pk m bits answer
  have pre : ∀ r : Reg, r = .x30 ∨ r = .x31 ∨ r = .x5 →
      (afterIndex pk m bits answer).getReg r = (afterPrefix pk m bits).getReg r := by
    intro r hr
    rcases hr with rfl | rfl | rfl <;>
      exact afterIndex_prefixReg _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)
  refine ⟨?_, ?_, ?_, afterIndex_lanes pk m bits answer hi,
    afterIndex_x13 pk m bits answer hlen, located.code_eq (afterIndex_code pk m bits answer)⟩
  · rw [pre .x30 (Or.inl rfl), P.x30]
  · rw [pre .x31 (Or.inr (Or.inl rfl)), P.x31]
  · rw [pre .x5 (Or.inr (Or.inr rfl)), P.x5]; rfl

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
      chainSetup))))) := by
  simp only [indexPhase, lengthCheck_parts, sumCheck_parts, mainBlock, lanes, lanesUpTo, chainSetup, List.append_assoc]

theorem indexPhase_length : indexPhase.length = 46 := by decide

theorem mainBlock_length : mainBlock.length = 30 := by decide

section Refine

variable (pk : PublicKey) (m : Message) (bits : List Bool)

theorem pc_add (p : Word) (a b : ℕ) : p + W a + W b = p + W (a + b) := by
  rw [BitVec.add_assoc, W_add]

/-- The index phase: the specified first query, the length and sum rejections, and otherwise the
continuation from `afterIndex`, at 40 cycles plus the continuation. -/
theorem indexPhase_refines (tail : Code) (rest fuel : ℕ)
    (q : BitVec hashBits → OracleComp Spec (Option Bool)) (c : ℕ) (hc : 3 ≤ c)
    (located : Riscv.CodeAt (S0 pk m bits) (S0 pk m bits).pc (indexPhase ++ tail))
    (bound : indexPhase.length + rest ≤ fuel)
    (continuation : ∀ answer, Accepted (pack answer) → bits.length = 5504 →
      ∀ left, rest ≤ left → Riscv.Refines left (afterIndex pk m bits answer) (q answer) c) :
    Riscv.Refines fuel (S0 pk m bits) (do
      let answer ← hash (swapHalves (emsg m pk ++ ofBits nonceBits bits))
      if Accepted (pack answer) ∧ bits.length = 5504 then q answer
      else pure (some false)) (c + 40) := by
  rw [indexPhase_length] at bound
  rw [indexPhase_parts] at located
  simp only [List.append_assoc] at located
  have P := prefix_effect pk m bits
  -- the prefix
  have ready := indexPrefix_ready pk m bits
  rw [show fuel = indexPrefix.length + ((fuel - 6) + 1) by rw [indexPrefix_length]; omega,
    show c + 40 = indexPrefix.length + (1 + (c + 34)) by rw [indexPrefix_length]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  have callLocated : Riscv.CodeAt (afterPrefix pk m bits) (afterPrefix pk m bits).pc
      ([.ECALL] ++ (lenBlock ++ ([.BEQ .x13 .x6 16] ++ reject ++ (mainBlock ++
        ([.BEQ .x27 .x0 16] ++ reject ++ (chainSetup ++ tail)))))) := by
    have h := located.append_right
    have e : (afterPrefix pk m bits).pc = (S0 pk m bits).pc +
        BitVec.ofNat 64 (4 * indexPrefix.length) := Riscv.linear_fold_pc _ _ ready
    rw [e]
    simpa only [List.append_assoc] using h.code_eq P.code
  have hashed := Riscv.Refines.hash (fuel := fuel - 6) callLocated.head P.x5
    (prefix_hashValid pk m bits) (c := c + 34)
    (k := fun answer => if Accepted (pack answer) ∧ bits.length = 5504 then q answer
      else pure (some false)) ?_
  · rw [prefix_hashInput pk m bits] at hashed
    dsimp only at hashed
    rw [show blockCost 512 = 1 by decide] at hashed
    exact hashed
  intro answer
  -- the length check
  have S2code : Riscv.CodeAt (S2 pk m bits answer) (S2 pk m bits answer).pc
      (lenBlock ++ ([.BEQ .x13 .x6 16] ++ reject ++ (mainBlock ++
        ([.BEQ .x27 .x0 16] ++ reject ++ (chainSetup ++ tail))))) :=
    callLocated.tail.code_eq (by simp [Riscv.writeHash])
  have lenReady : Riscv.LinearReady (S2 pk m bits answer) lenBlock := by
    simp only [lenBlock, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, true_and,
      and_true]
    rw [S2_regs, (prefix_effect pk m bits).x12, signExtend12_nat 72 (by norm_num), W_add]
    exact dword_ok _ (by unfold dataAddr; omega) (by unfold dataAddr; omega)
      (by unfold dataAddr; omega)
  rw [show fuel - 6 = lenBlock.length + (fuel - 7) by simp [lenBlock]; omega,
    show c + 34 = lenBlock.length + (c + 33) by simp [lenBlock]; omega]
  apply Riscv.Refines.linear _ S2code.append_left lenReady
  have S3code : Riscv.CodeAt (S3 pk m bits answer) (S3 pk m bits answer).pc
      ([.BEQ .x13 .x6 16] ++ reject ++ (mainBlock ++
        ([.BEQ .x27 .x0 16] ++ reject ++ (chainSetup ++ tail)))) := by
    have h := S2code.append_right
    rw [show (S3 pk m bits answer).pc = (S2 pk m bits answer).pc + BitVec.ofNat 64 (4 * lenBlock.length)
      from Riscv.linear_fold_pc _ _ lenReady]
    exact h.code_eq (Riscv.fold_code _ _)
  have reorder : (if Accepted (pack answer) ∧ bits.length = 5504 then q answer
      else pure (some false)) =
      if (S3 pk m bits answer).getReg .x13 = (S3 pk m bits answer).getReg .x6 then
        (if (S5 pk m bits answer).getReg .x27 = (S5 pk m bits answer).getReg .x0 then q answer
          else pure (some false)) else pure (some false) := by
    by_cases hl : bits.length = 5504
    · rw [if_pos ((length_iff pk m bits answer).mpr hl)]
      by_cases ha : Accepted (pack answer)
      · rw [if_pos ⟨ha, hl⟩, if_pos ((sum_iff pk m bits answer).mpr ha)]
      · rw [if_neg (fun h => ha h.1), if_neg (fun h => ha ((sum_iff pk m bits answer).mp h))]
    · rw [if_neg (fun h => hl h.2), if_neg (fun h => hl ((length_iff pk m bits answer).mp h))]
  rw [reorder, show c + 33 = (c + 32) + 1 by omega]
  apply beq_refines _ _ _ _ _ S3code (by omega) (by omega)
  intro hlenEq
  have hl := (length_iff pk m bits answer).mp hlenEq
  -- the loads, the lanes and the sum
  have S4code : Riscv.CodeAt (S4 pk m bits answer) (S4 pk m bits answer).pc
      (mainBlock ++ ([.BEQ .x27 .x0 16] ++ reject ++ (chainSetup ++ tail))) := by
    have h := S3code.append_right (first := [.BEQ .x13 .x6 16] ++ reject)
    rw [show (4 * ([Instr.BEQ .x13 .x6 16] ++ reject).length) = 16 from rfl] at h
    exact h.code_eq (by simp [S4])
  have mReady := mainBlock_ready pk m bits answer
  rw [show fuel - 7 - 1 = mainBlock.length + (fuel - 38) by rw [mainBlock_length]; omega,
    show c + 32 = mainBlock.length + (c + 2) by rw [mainBlock_length]; omega]
  apply Riscv.Refines.linear _ (S4code.append_left) mReady
  have S5code : Riscv.CodeAt (S5 pk m bits answer) (S5 pk m bits answer).pc
      ([.BEQ .x27 .x0 16] ++ reject ++ (chainSetup ++ tail)) := by
    have h := S4code.append_right
    rw [show (S5 pk m bits answer).pc = (S4 pk m bits answer).pc +
      BitVec.ofNat 64 (4 * mainBlock.length) from Riscv.linear_fold_pc _ _ mReady]
    exact h.code_eq (Riscv.fold_code _ _)
  rw [show c + 2 = (c + 1) + 1 by omega]
  apply beq_refines _ _ _ _ _ S5code (by omega) (by omega)
  intro hsumEq
  have ha := (sum_iff pk m bits answer).mp hsumEq
  -- the setup
  have S6code : Riscv.CodeAt (S6 pk m bits answer) (S6 pk m bits answer).pc (chainSetup ++ tail) := by
    have h := S5code.append_right (first := [.BEQ .x27 .x0 16] ++ reject)
    rw [show (4 * ([Instr.BEQ .x27 .x0 16] ++ reject).length) = 16 from rfl] at h
    exact h.code_eq (by simp [S6])
  rw [show fuel - 38 - 1 = chainSetup.length + (fuel - 40) by simp [chainSetup]; omega,
    show c + 1 = chainSetup.length + c by simp only [chainSetup, List.length_cons, List.length_nil]; omega]
  apply Riscv.Refines.linear _ S6code.append_left (setup_ready _)
  exact continuation answer ha hl _ (by omega)

/-- Where the index phase ends. -/
theorem afterIndex_pc (answer : BitVec hashBits) :
    (afterIndex pk m bits answer).pc = W blockZero := by
  have lenReady : Riscv.LinearReady (S2 pk m bits answer) lenBlock := by
    simp only [lenBlock, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, true_and,
      and_true]
    rw [S2_regs, (prefix_effect pk m bits).x12, signExtend12_nat 72 (by norm_num), W_add]
    exact dword_ok _ (by unfold dataAddr; omega) (by unfold dataAddr; omega)
      (by unfold dataAddr; omega)
  have e1 : (afterIndex pk m bits answer).pc = (S6 pk m bits answer).pc +
      BitVec.ofNat 64 (4 * chainSetup.length) := Riscv.linear_fold_pc _ _ (setup_ready _)
  have e2 : (S6 pk m bits answer).pc = (S5 pk m bits answer).pc + 16 := rfl
  have e3 : (S5 pk m bits answer).pc = (S4 pk m bits answer).pc +
      BitVec.ofNat 64 (4 * mainBlock.length) :=
    Riscv.linear_fold_pc _ _ (mainBlock_ready pk m bits answer)
  have e4 : (S4 pk m bits answer).pc = (S3 pk m bits answer).pc + 16 := rfl
  have e5 : (S3 pk m bits answer).pc = (S2 pk m bits answer).pc +
      BitVec.ofNat 64 (4 * lenBlock.length) := Riscv.linear_fold_pc _ _ lenReady
  have e6 : (S2 pk m bits answer).pc = (afterPrefix pk m bits).pc + 4 := rfl
  rw [e1, e2, e3, e4, e5, e6, (prefix_effect pk m bits).pc, mainBlock_length]
  simp only [chainSetup, lenBlock, List.length_cons, List.length_nil, blockZero]
  decide

end Refine

end OptimalOTS.RiscvMixedProgram
