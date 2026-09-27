import Submissions.UpperRiscvHint.MixedDispatchArith
import Submissions.UpperRiscvHint.MixedContext
import Submissions.UpperRiscvHint.MixedIndexMemory
import Submissions.UpperRiscvHint.IndexDispatchFields

/-!
# The index phase

The machine saves the public key, hashes `pk ‖ message ‖ nonce`, builds the four dispatch words,
and leaves in `x5` a residue that is the HASH call number exactly when the fields sum to 158 or
413. It loads the honest view length into `x6` for pair 0's raw-form test and sets the cap width.
The state `afterIndex` satisfies a raw-index chain invariant; the pair restrictions remain to be
checked by the dispatch tables.
-/

namespace OptimalOTS.RiscvMixedProgram

open Riscv2Program

open OptimalOTS.Dag
open RiscvZkvm.Rv64 OracleComp

-- Loader reasoning only uses the code through its location invariant. Keeping the
-- assembled dispatch image opaque avoids expanding all table fragments in state goals.
attribute [local irreducible] verifier
attribute [local irreducible] validSet

/-! ## The data image and the view loader -/

theorem dataImage_length : dataImage.length = 64 := by decide

/-- The four constant words of the data image, after the 32-byte answer buffer. -/
def dataWord (j : ℕ) : ℕ := [broadcast 0x3c3c, 255, baseWord 0, honestViewBits].getD j 0

theorem dataImage_word (j : ℕ) (hj : j < 4) :
    bytesToWordLE ((dataImage.drop (8 * (4 + j))).take 8) = W (dataWord j) := by
  interval_cases j <;> decide

theorem initial_data_word (pk : PublicKey) (m : Message) (view : List Bool) (j : ℕ) (hj : j < 4) :
    (RiscvHint.loadView image pk m view).getMem (W (dataAddr + 32 + 8 * j)) = W (dataWord j) := by
  have hlen : image.data.length = 64 := dataImage_length
  have ha : (W (dataAddr + 32 + 8 * j)).toNat = dataAddr + 32 + 8 * j :=
    W_toNat _ (by unfold dataAddr; omega)
  rw [loadView_getMem, getMem_load_outside, loaderMessage, getMem_load_outside, loaderPublic,
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
    norm_num [Riscv.bytesOfVector, Riscv.bytesOfBits, pkBits, msgBits, RiscvHint.maxViewBits,
      dataAddr]
    try omega

/-! ## The prefix and the index query -/

section Prefix

variable (pk : PublicKey) (m : Message) (view : List Bool)

/-- The loader's state. -/
abbrev S0 : MachineState := RiscvHint.loadView image pk m view

theorem S0_regs :
    (S0 pk m view).getReg .x10 = W 0x400000 ∧ (S0 pk m view).getReg .x11 = W 0x400010 ∧
    (S0 pk m view).getReg .x12 = W 0x400030 ∧
    (S0 pk m view).getReg .x13 =
      BitVec.ofNat 64 (min view.length (RiscvHint.maxViewBits + 1)) := ⟨rfl, rfl, rfl, rfl⟩

theorem S0_pc : (S0 pk m view).pc = W 4096 := by
  simp [RiscvHint.loadView]; rfl

/-- The state before the index query. -/
def afterPrefix : MachineState := indexPrefix.foldl execInstrBr (S0 pk m view)

theorem indexPrefix_ready : Riscv.LinearReady (S0 pk m view) indexPrefix := by
  simp [indexPrefix, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    execInstrBr, RiscvHint.loadView, MachineState.getReg, MachineState.setReg,
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
  x13 : s.getReg .x13 = BitVec.ofNat 64 (min view.length (RiscvHint.maxViewBits + 1))
  frame : ∀ addr, s.getMem addr = (S0 pk m view).getMem addr
  pc : s.pc = W (4096 + 20)
  code : s.code = (S0 pk m view).code

theorem pk_word0 : (S0 pk m view).getMem (W 0x400000) = pk.extractLsb' 0 64 := by
  have h := loadView_publicKey_word image pk m view 0 (by norm_num)
  have e : W 0x400000 = Riscv.publicKeyBase + BitVec.ofNat 64 (8 * 0) := by decide
  rw [e]; exact h

theorem pk_word1 : (S0 pk m view).getMem (W 0x400008) = pk.extractLsb' 64 64 := by
  have h := loadView_publicKey_word image pk m view 1 (by norm_num)
  have e : W 0x400008 = Riscv.publicKeyBase + BitVec.ofNat 64 (8 * 1) := by decide
  rw [e]; exact h

theorem prefix_effect : PrefixEffect pk m view (afterPrefix pk m view) := by
  have l0 : signExtend12 (BitVec.ofNat 12 0) = 0 := by decide
  have l8 : signExtend12 (BitVec.ofNat 12 8) = W 8 := by decide
  have r10 := (S0_regs pk m view).1
  have r13 := (S0_regs pk m view).2.2.2
  have w0 := pk_word0 pk m view
  have w1 := pk_word1 pk m view
  have hmem : ∀ addr, (afterPrefix pk m view).getMem addr = (S0 pk m view).getMem addr := by
    intro addr; simp [afterPrefix, indexPrefix, execInstrBr]
  have hpc : (afterPrefix pk m view).pc = W (4096 + 20) := by
    show (S0 pk m view).pc + 4 + 4 + 4 + 4 + 4 = _
    rw [S0_pc]; decide
  have hcode : (afterPrefix pk m view).code = (S0 pk m view).code := by
    simp [afterPrefix, indexPrefix, execInstrBr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hmem, hpc, hcode⟩
  all_goals simp [afterPrefix, indexPrefix, execInstrBr, getReg_setReg_ite, l0, l8, r10, r13, w0,
    w1, W_add, getReg_x0', BitVec.add_zero]
  all_goals rfl

theorem image_data_length : image.data.length ≤ 1048576 := by
  rw [show image.data = dataImage from rfl, dataImage_length]; norm_num

set_option maxRecDepth 100000 in
/-- The public key, the message and the nonce lie at the loader's addresses:
`pk ‖ message ‖ nonce` with the public key in the low view is the specification's query input. -/
theorem prefix_memBits :
    MemBits (afterPrefix pk m view) (W 0x400000)
      (swapHalves (emsg m pk ++ ofBits nonceBits view)) := by
  have E := prefix_effect pk m view
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
  · have hw := loadView_publicKey_word image pk m view j (by omega)
    have e : Riscv.publicKeyBase + BitVec.ofNat 64 (8 * j) = W (0x400000 + 8 * j) := by
      rw [show Riscv.publicKeyBase = W 0x400000 from rfl, W_add]
    rw [e] at hw
    rw [hw, BitVec.extractLsb'_append_eq_of_add_le (by omega),
      BitVec.extractLsb'_append_eq_of_add_le (by omega)]
  · by_cases hlow : j < 6
    · have hw := loadView_message_word image pk m view (j - 2) (by omega)
      have e : Riscv.messageBase + BitVec.ofNat 64 (8 * (j - 2)) = W (0x400000 + 8 * j) := by
        rw [show Riscv.messageBase = W 0x400010 from rfl, W_add]
        congr 1
        omega
      rw [e] at hw
      rw [hw, BitVec.extractLsb'_append_eq_of_add_le (by omega),
        BitVec.extractLsb'_append_eq_of_le (by omega),
        show 64 * j - pkBits = 64 * (j - 2) by rw [hp]; omega]
    · have hs := loadView_word image pk m view image_data_length (j - 6) (by omega)
      have e : Riscv.signatureBase + BitVec.ofNat 64 (8 * (j - 6)) = W (0x400000 + 8 * j) := by
        rw [show Riscv.signatureBase = W 0x400030 from rfl, W_add]
        congr 1
        omega
      rw [e] at hs
      rw [hs, BitVec.extractLsb'_append_eq_of_le (by omega), ofBits_extract _ (by omega),
        ofBits_drop_take _ (by unfold RiscvHint.maxViewBits; omega),
        show 64 * j - (msgBits + pkBits) = 64 * (j - 6) by rw [hm, hp]; omega]

theorem prefix_hashInput :
    Riscv.hashInput (afterPrefix pk m view) =
      ⟨512, swapHalves (emsg m pk ++ ofBits nonceBits view)⟩ := by
  have E := prefix_effect pk m view
  apply hashInput_of_memBits E.x10 (by rw [E.x11]; rfl) (prefix_memBits pk m view)

theorem prefix_hashValid : Riscv.hashArgumentsValid (afterPrefix pk m view) = true := by
  have E := prefix_effect pk m view
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

variable (pk : PublicKey) (m : Message) (view : List Bool) (answer : BitVec hashBits)

abbrev S2 : MachineState := Riscv.writeHash (afterPrefix pk m view) answer

/-- The state before the loads: the index answer is in the data buffer. -/
abbrev S4 : MachineState := S2 pk m view answer

def mainBlock : Code := loadWords ++ lanes ++ sumCheck

def S5 : MachineState := mainBlock.foldl execInstrBr (S4 pk m view answer)

/-- The state after the index phase, at the first chain block. -/
def afterIndex : MachineState := chainSetup.foldl execInstrBr (S5 pk m view answer)

theorem S2_regs (r : Reg) : (S2 pk m view answer).getReg r = (afterPrefix pk m view).getReg r := by
  simp [Riscv.writeHash]

theorem S2_answer (j : ℕ) (hj : j < 4) :
    (S2 pk m view answer).getMem (W (dataAddr + 8 * j)) = answer.extractLsb' (64 * j) 64 := by
  have h := writeHash_word (afterPrefix pk m view) answer j hj
  rw [(prefix_effect pk m view).x12, W_add] at h
  exact h

theorem S2_frame (addr : Word) (h : addr.toNat < dataAddr ∨ dataAddr + 32 ≤ addr.toNat) :
    (S2 pk m view answer).getMem addr = (afterPrefix pk m view).getMem addr := by
  apply writeHash_frame
  rw [(prefix_effect pk m view).x12]
  intro j hj e
  rw [e, W_add, W_toNat _ (by unfold dataAddr; omega)] at h
  omega

/-- The constants of the data image are still in place after the index query. -/
theorem S2_const (j : ℕ) (hj : j < 4) :
    (S2 pk m view answer).getMem (W (dataAddr + 32 + 8 * j)) = W (dataWord j) := by
  rw [S2_frame _ _ _ _ _ (Or.inr (by rw [W_toNat _ (by unfold dataAddr; omega)]; omega)),
    (prefix_effect pk m view).frame, initial_data_word pk m view j hj]

theorem S4_regs (r : Reg) : (S4 pk m view answer).getReg r = (afterPrefix pk m view).getReg r :=
  S2_regs pk m view answer r

theorem S4_mem (addr : Word) : (S4 pk m view answer).getMem addr = (S2 pk m view answer).getMem addr :=
  rfl

/-- The words and constants loaded before the lanes. -/
structure LoadEffect (a b : MachineState) : Prop where
  x20 : b.getReg .x20 = wordOf answer 0
  x21 : b.getReg .x21 = wordOf answer 1
  x22 : b.getReg .x22 = wordOf answer 2
  x23 : b.getReg .x23 = wordOf answer 3
  x25 : b.getReg .x25 = W (broadcast 0x3c3c)
  x2 : b.getReg .x2 = W 255
  x3 : b.getReg .x3 = W (baseWord 0)
  x6 : b.getReg .x6 = W honestViewBits
  regs : ∀ r, r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x6 → r ≠ .x25 → r ≠ .x1 →
    r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x7 → b.getReg r = a.getReg r
  mem : ∀ addr, b.getMem addr = a.getMem addr

/-- A register the loads leave alone. -/
abbrev LoadFree (r : Reg) : Prop :=
  r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x6 ∧ r ≠ .x25 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧
    r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x7

theorem LoadEffect.regs' {a b : MachineState} (E : LoadEffect answer a b) (r : Reg)
    (h : LoadFree r) : b.getReg r = a.getReg r :=
  E.regs r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2

theorem S4_x12 : (S4 pk m view answer).getReg .x12 = W dataAddr := by
  rw [S4_regs, (prefix_effect pk m view).x12]

theorem loadWords_ready : Riscv.LinearReady (S4 pk m view answer) loadWords := by
  have h12 := S4_x12 pk m view answer
  simp only [loadWords, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, true_and, and_true]
  simp only [show ¬ (Reg.x12 = Reg.x20) by decide, show ¬ (Reg.x12 = Reg.x21) by decide,
    show ¬ (Reg.x12 = Reg.x22) by decide, show ¬ (Reg.x12 = Reg.x23) by decide,
    show ¬ (Reg.x12 = Reg.x6) by decide, show ¬ (Reg.x12 = Reg.x25) by decide,
    show ¬ (Reg.x12 = Reg.x1) by decide, show ¬ (Reg.x12 = Reg.x2) by decide,
    show ¬ (Reg.x12 = Reg.x3) by decide, show ¬ (Reg.x12 = Reg.x4) by decide,
    false_and, if_false, h12]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold dataAddr; decide)

theorem loadWords_effect :
    LoadEffect answer (S4 pk m view answer) (loadWords.foldl execInstrBr (S4 pk m view answer)) := by
  have h12 := S4_x12 pk m view answer
  have mw : ∀ off : ℕ, off < 2048 → (S4 pk m view answer).getReg .x12 +
      signExtend12 (BitVec.ofNat 12 off) = W (dataAddr + off) := by
    intro off hoff; rw [h12, signExtend12_nat _ hoff, W_add]
  have c : ∀ j, j < 4 → (S4 pk m view answer).getMem (W (dataAddr + (32 + 8 * j))) = W (dataWord j) := by
    intro j hj; rw [S4_mem, ← Nat.add_assoc, S2_const _ _ _ _ j hj]
  have a : ∀ j, j < 4 → (S4 pk m view answer).getMem (W (dataAddr + 8 * j)) = wordOf answer j := by
    intro j hj; rw [S4_mem]; exact S2_answer pk m view answer j hj
  have a0 := a 0 (by norm_num)
  simp only [Nat.mul_zero, Nat.add_zero] at a0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [loadWords, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, getReg_setReg_ite, MachineState.getMem_setPC,
    MachineState.getMem_setReg]
  · simp [mw 0 (by norm_num), a0]
  · simp [mw 8 (by norm_num), a 1 (by norm_num)]
  · simp [mw 16 (by norm_num), a 2 (by norm_num)]
  · simp [mw 24 (by norm_num), a 3 (by norm_num)]
  · simp [mw 32 (by norm_num), c 0 (by norm_num), dataWord]
  · simp [mw 40 (by norm_num), c 1 (by norm_num), dataWord]
  · simp [mw 48 (by norm_num), c 2 (by norm_num), dataWord]
  · simp [mw 56 (by norm_num), c 3 (by norm_num), dataWord]
  · intro r h20 h21 h22 h23 h6 h25 h1 h2 h3 h4 h7
    simp [h20, h21, h22, h23, h6, h25, h1, h2, h3, h4, h7]
  · intro addr; trivial

/-- After the loads. -/
def S45 : MachineState := loadWords.foldl execInstrBr (S4 pk m view answer)

/-- After the lanes. -/
def S46 : MachineState := lanes.foldl execInstrBr (S45 pk m view answer)

theorem S5_eq : S5 pk m view answer = sumCheck.foldl execInstrBr (S46 pk m view answer) := by
  simp [S5, S46, S45, mainBlock, List.foldl_append]

theorem S45_x12 : (S45 pk m view answer).getReg .x12 = W dataAddr := by
  rw [S45, LoadEffect.regs' answer (loadWords_effect pk m view answer) .x12 (by decide), S4_x12]

theorem S45_x10 : (S45 pk m view answer).getReg .x10 = W hashBase := by
  rw [S45, LoadEffect.regs' answer (loadWords_effect pk m view answer) .x10 (by decide), S4_regs,
    (prefix_effect pk m view).x10]
  rfl

theorem S45_masks : MasksLoaded (S45 pk m view answer) := by
  have LE := loadWords_effect pk m view answer
  intro g _
  exact LE.x25

theorem S45_words : WordsLoaded (S45 pk m view answer) answer := by
  have LE := loadWords_effect pk m view answer
  intro w hw
  interval_cases w
  · exact LE.x20
  · exact LE.x21
  · exact LE.x22
  · exact LE.x23

theorem S45_bases (g : ℕ) (hg : g < 4) :
    (S45 pk m view answer).getReg (baseReg g) = W (baseWord g) := by
  have LE := loadWords_effect pk m view answer
  interval_cases g
  · exact LE.x3
  · rw [baseWord_second]; exact LE.x3
  · rw [baseWord_third]; exact LE.x3
  · rw [baseWord_last]; exact LE.x3

theorem lanes_effect :
    Riscv.LinearReady (S45 pk m view answer) lanes ∧
      LanesEffect (S45 pk m view answer) (S46 pk m view answer) 4 := by
  rw [S46, lanes_eq]
  exact lanesUpTo_effect _ (S45_x10 pk m view answer) 4 le_rfl

theorem mainBlock_ready : Riscv.LinearReady (S4 pk m view answer) mainBlock := by
  unfold mainBlock
  refine ((loadWords_ready pk m view answer).append (lanes_effect pk m view answer).1).append ?_
  simp [sumCheck, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem S5_x5 : (S5 pk m view answer).getReg .x5 =
    rv64_remu (addressSum (S45 pk m view answer) 4) (W 255) := by
  have L := (lanes_effect pk m view answer).2
  have x2 : (S46 pk m view answer).getReg .x2 = W 255 := by
    rw [L.regs .x2 (by decide) (by decide)]
    exact (loadWords_effect pk m view answer).x2
  rw [S5_eq]
  simp only [sumCheck, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [L.acc (by norm_num), x2]

theorem S5_regs (r : Reg) (h26 : r ≠ .x26) (h27 : r ≠ .x27) (h5 : r ≠ .x5) :
    (S5 pk m view answer).getReg r = (S45 pk m view answer).getReg r := by
  have L := (lanes_effect pk m view answer).2
  rw [S5_eq]
  simp only [sumCheck, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [h5, L.regs r h26 h27]

theorem S5_mem (addr : Word) : (S5 pk m view answer).getMem addr = (S46 pk m view answer).getMem addr := by
  rw [S5_eq]
  simp [sumCheck, execInstrBr]

/-- The residue is the HASH call number exactly on the two checksum ranks; tables check the
caps. -/
theorem residue_iff : (S5 pk m view answer).getReg .x5 = Riscv.hashCall ↔
    IndexRank (pack answer) := by
  rw [S5_x5, show Riscv.hashCall = 1#64 from rfl]
  have total := address_remainder_iff (S45 pk m view answer) (S45_masks pk m view answer) answer
    (S45_words pk m view answer) (S45_bases pk m view answer)
  have e : ∀ x : Word, (rv64_remu x (W 255)).toNat = x.toNat % 255 := by
    intro x
    simp [rv64_remu, W, BitVec.toNat_umod]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [e] at hn
    exact total.mp hn
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [e]
    exact total.mpr h

theorem setup_ready (s : MachineState) : Riscv.LinearReady s chainSetup := by
  simp [chainSetup, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

/-- The registers written by the chain setup, and the input pointer still at the public key. -/
theorem afterIndex_setupRegs :
    (afterIndex pk m view answer).getReg .x11 = 192 ∧
    (afterIndex pk m view answer).getReg .x10 = W hashBase := by
  have x10 : (S5 pk m view answer).getReg .x10 = W hashBase := by
    rw [S5_regs _ _ _ _ _ (by decide) (by decide) (by decide), S45_x10]
  unfold afterIndex
  simp only [chainSetup, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, if_false, getReg_x0', x10]
  decide

theorem afterIndex_regs (r : Reg) (h11 : r ≠ .x11) :
    (afterIndex pk m view answer).getReg r = (S5 pk m view answer).getReg r := by
  unfold afterIndex
  simp only [chainSetup, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    getReg_setReg_ite]
  simp [h11]

theorem afterIndex_mem (addr : Word) :
    (afterIndex pk m view answer).getMem addr = (S46 pk m view answer).getMem addr := by
  unfold afterIndex
  simp [chainSetup, execInstrBr, S5_mem]

/-- A register untouched after the prefix. -/
theorem afterIndex_prefixReg (r : Reg) (h11 : r ≠ .x11) (hl : LoadFree r)
    (h26 : r ≠ .x26) (h27 : r ≠ .x27) (h5 : r ≠ .x5) :
    (afterIndex pk m view answer).getReg r = (afterPrefix pk m view).getReg r := by
  rw [afterIndex_regs _ _ _ _ r h11, S5_regs _ _ _ _ r h26 h27 h5, S45,
    LoadEffect.regs' answer (loadWords_effect pk m view answer) r hl, S4_regs]

/-- The honest view length, for pair 0's raw-form test. -/
theorem afterIndex_x6 : (afterIndex pk m view answer).getReg .x6 = W honestViewBits := by
  rw [afterIndex_regs _ _ _ _ .x6 (by decide), S5_regs _ _ _ _ .x6 (by decide) (by decide)
    (by decide), S45]
  exact (loadWords_effect pk m view answer).x6

theorem afterIndex_code : (afterIndex pk m view answer).code = (S0 pk m view).code := by
  unfold afterIndex S5 S4
  rw [Riscv.fold_code, Riscv.fold_code]
  simp [Riscv.writeHash, (prefix_effect pk m view).code]

/-- Memory outside the index answer and the lane words is the loader's. -/
theorem afterIndex_frame (addr : Word)
    (h : (addr.toNat < dataAddr ∨ dataAddr + 32 ≤ addr.toNat) ∧
      (addr.toNat < laneBase ∨ laneBase + 32 ≤ addr.toNat)) :
    (afterIndex pk m view answer).getMem addr = (S0 pk m view).getMem addr := by
  have L := (lanes_effect pk m view answer).2
  rw [afterIndex_mem, L.frame]
  · rw [S45, (loadWords_effect pk m view answer).mem, S4_mem, S2_frame _ _ _ _ _ h.1,
      (prefix_effect pk m view).frame]
  · intro j hj e
    have h2 := h.2
    rw [e, W_toNat _ (by unfold laneWordAddr laneBase; omega)] at h2
    unfold laneWordAddr at h2
    omega

/-! ## The context at the first chain -/

/-- The packed answer without assuming the later pair-cap checks. -/
def rawIdx : RawIdx := ⟨pack answer, pack_lt answer⟩

/-- The accepted subtype, when both the rank and pair restrictions have been established. -/
def acceptedIdx (hi : Accepted (pack answer)) : Idx :=
  ⟨pack answer, mem_validSet.mpr ⟨pack_lt answer, hi⟩⟩

theorem afterIndex_x13 :
    (afterIndex pk m view answer).getReg .x13 =
      BitVec.ofNat 64 (min view.length (RiscvHint.maxViewBits + 1)) := by
  rw [afterIndex_prefixReg _ _ _ _ .x13 (by decide) (by decide) (by decide) (by decide) (by decide),
    (prefix_effect pk m view).x13]

theorem laneGroup_lt (q : ℕ) (hq : q < 16) : laneGroup q < 4 := by
  unfold laneGroup; omega

theorem laneIdx_lt (q : ℕ) (_hq : q < 16) : laneIdx q < 4 := by
  unfold laneIdx; omega

theorem fineChain_lane (q : ℕ) (_hq : q < 16) : fineChain (laneGroup q) (laneIdx q) = firstChain q := by
  unfold fineChain laneGroup laneIdx firstChain; omega

theorem coarseChain_lane (q : ℕ) (_hq : q < 16) : coarseChain (laneGroup q) (laneIdx q) = 2*q+1 := by
  unfold coarseChain laneGroup laneIdx; omega

/-- Eliminate the large concrete register state before doing lane arithmetic. -/
theorem afterIndex_stored (g : ℕ) (hg : g < 4) :
    (afterIndex pk m view answer).getMem (W (laneWordAddr g)) =
      W (baseWord g) - laneValue (wordOf answer g) (W (maskNat g)) := by
  have L := (lanes_effect pk m view answer).2
  rw [afterIndex_mem, L.stored g hg, S45_bases pk m view answer g hg]
  unfold laneOf
  rw [S45_words pk m view answer g hg, S45_masks pk m view answer g hg]

/-- Decode abstract stored words before instantiating the concrete machine state. -/
theorem stored_lanes (s : MachineState)
    (stored : ∀ g, g < 4 → s.getMem (W (laneWordAddr g)) =
      W (baseWord g) - laneValue (wordOf answer g) (W (maskNat g))) (q : Fin 16) :
    (s.getHalfword (W (laneAddr q))).toNat =
      baseLane q - dispatch (rawIdx answer) q := by
  have hq := q.isLt
  have hg := laneGroup_lt q hq
  have hl := laneIdx_lt q hq
  calc
    _ = (W (baseWord (laneGroup q)) -
        laneValue (wordOf answer (laneGroup q)) (W (maskNat (laneGroup q)))).toNat /
        2^(16*laneIdx q) % 2^16 :=
      stored_lane_extract s q _ (stored _ hg)
    _ = baseLane (4*laneGroup q+laneIdx q) -
        (4*fineFld (laneGroup q) (wordOf answer (laneGroup q)).toNat (laneIdx q) +
         1024*coarseFld (laneGroup q) (wordOf answer (laneGroup q)).toNat (laneIdx q)) :=
      lane_halfword _ _ _ hg hl _ (laneValue_toNat (wordOf answer (laneGroup q)) (laneGroup q))
    _ = baseLane q - dispatch (rawIdx answer) q :=
      word_fields_dispatch answer (rawIdx answer) rfl q

/-- The stored halfwords hold the dispatch values for all sixteen chain pairs. -/
theorem afterIndex_lanes (q : Fin 16) :
    ((afterIndex pk m view answer).getHalfword (W (laneAddr q))).toNat =
      baseLane q - dispatch (rawIdx answer) q :=
  stored_lanes answer (afterIndex pk m view answer) (afterIndex_stored pk m view answer) q

/-- The residue left in `x5` by the checksum. -/
theorem afterIndex_x5 :
    (afterIndex pk m view answer).getReg .x5 = (S5 pk m view answer).getReg .x5 :=
  afterIndex_regs _ _ _ _ .x5 (by decide)

theorem afterIndex_x12 : (afterIndex pk m view answer).getReg .x12 = W dataAddr := by
  rw [afterIndex_prefixReg _ _ _ _ .x12 (by decide) (by decide) (by decide) (by decide)
    (by decide), (prefix_effect pk m view).x12]

theorem S0_null : (S0 pk m view).code 0 = none := by
  have hc : (S0 pk m view).code = loadProgram Riscv.codeBase image.code := by
    simp [RiscvHint.loadView]; rfl
  rw [hc, show image.code = verifier from rfl]
  simp only [loadProgram, code_length]
  decide

theorem afterIndex_ctx (located : Riscv.CodeAt (S0 pk m view) (W 4096) verifier)
    (rank : IndexRank (pack answer)) :
    Ctx (afterIndex pk m view answer) (rawIdx answer) view pk := by
  have P := prefix_effect pk m view
  have pre : ∀ r : Reg, r = .x30 ∨ r = .x31 →
      (afterIndex pk m view answer).getReg r = (afterPrefix pk m view).getReg r := by
    intro r hr
    rcases hr with rfl | rfl <;>
      exact afterIndex_prefixReg _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)
  refine ⟨?_, ?_, ?_, afterIndex_lanes pk m view answer, ?_,
    afterIndex_x13 pk m view answer, afterIndex_x6 pk m view answer,
    by rw [afterIndex_code]; exact S0_null pk m view,
    located.code_eq (afterIndex_code pk m view answer)⟩
  · rw [pre .x30 (Or.inl rfl), P.x30]
  · rw [pre .x31 (Or.inr rfl), P.x31]
  · rw [afterIndex_x5]; exact (residue_iff pk m view answer).mpr rank
  · -- `x12` still addresses the index answer, below every chain buffer
    intro q hq
    have hx : ∀ k : ℕ, k < 32 → W dataAddr ≠ W (outAddr k) := fun k hk =>
      W_ne (by unfold dataAddr; omega) (by unfold outAddr; split_ifs <;> omega)
        (by unfold dataAddr outAddr; split_ifs <;> omega)
    rw [afterIndex_x12] at hq
    rcases hq with h | ⟨h, _⟩
    · exact absurd h (hx _ (by omega))
    · exact absurd h (hx _ (by omega))

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

theorem indexPhase_parts : indexPhase = indexPrefix ++ ([.ECALL] ++ (mainBlock ++ chainSetup)) := by
  simp only [indexPhase, mainBlock, lanes, lanesUpTo, chainSetup, List.append_assoc]

theorem indexPhase_length : indexPhase.length = 31 := by decide

theorem mainBlock_length : mainBlock.length = 24 := by decide

section Refine

variable (pk : PublicKey) (m : Message) (view : List Bool)

/-- The index phase: the specified first query, then the continuation from `afterIndex` on every
answer, at 31 cycles plus the continuation. The checksum only sets `x5`. -/
theorem indexPhase_refines (tail : Code) (rest fuel : ℕ)
    (q : BitVec hashBits → OracleComp Spec (Option Bool)) (c : ℕ)
    (located : Riscv.CodeAt (S0 pk m view) (S0 pk m view).pc (indexPhase ++ tail))
    (bound : indexPhase.length + rest ≤ fuel)
    (continuation : ∀ answer,
      ∀ left, rest ≤ left → Riscv.Refines left (afterIndex pk m view answer) (q answer) c) :
    Riscv.Refines fuel (S0 pk m view)
      (hash (swapHalves (emsg m pk ++ ofBits nonceBits view)) >>= q) (c + 31) := by
  rw [indexPhase_length] at bound
  rw [indexPhase_parts] at located
  simp only [List.append_assoc] at located
  have P := prefix_effect pk m view
  -- the prefix
  have ready := indexPrefix_ready pk m view
  rw [show fuel = indexPrefix.length + ((fuel - 6) + 1) by rw [indexPrefix_length]; omega,
    show c + 31 = indexPrefix.length + (1 + (c + 25)) by rw [indexPrefix_length]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  have callLocated : Riscv.CodeAt (afterPrefix pk m view) (afterPrefix pk m view).pc
      ([.ECALL] ++ (mainBlock ++ (chainSetup ++ tail))) := by
    have h := located.append_right
    have e : (afterPrefix pk m view).pc = (S0 pk m view).pc +
        BitVec.ofNat 64 (4 * indexPrefix.length) := Riscv.linear_fold_pc _ _ ready
    rw [e]
    simpa only [List.append_assoc] using h.code_eq P.code
  have hashed := Riscv.Refines.hash (fuel := fuel - 6) callLocated.head P.x5
    (prefix_hashValid pk m view) (c := c + 25) (k := q) ?_
  · rw [prefix_hashInput pk m view] at hashed
    dsimp only at hashed
    rw [show blockCost 512 = 1 by decide] at hashed
    exact hashed
  intro answer
  -- the loads, the lanes and the checksum
  have S4code : Riscv.CodeAt (S4 pk m view answer) (S4 pk m view answer).pc
      (mainBlock ++ (chainSetup ++ tail)) :=
    callLocated.tail.code_eq (by simp [Riscv.writeHash])
  have mReady := mainBlock_ready pk m view answer
  rw [show fuel - 6 = mainBlock.length + (fuel - 30) by rw [mainBlock_length]; omega,
    show c + 25 = mainBlock.length + (1 + c) by rw [mainBlock_length]; omega]
  apply Riscv.Refines.linear _ (S4code.append_left) mReady
  -- the chainSetup
  have S5code : Riscv.CodeAt (S5 pk m view answer) (S5 pk m view answer).pc (chainSetup ++ tail) := by
    have h := S4code.append_right
    rw [show (S5 pk m view answer).pc = (S4 pk m view answer).pc +
      BitVec.ofNat 64 (4 * mainBlock.length) from Riscv.linear_fold_pc _ _ mReady]
    exact h.code_eq (Riscv.fold_code _ _)
  rw [show fuel - 30 = chainSetup.length + (fuel - 31) by simp [chainSetup]; omega,
    show 1 + c = chainSetup.length + c by simp only [chainSetup, List.length_cons, List.length_nil]]
  apply Riscv.Refines.linear _ S5code.append_left (setup_ready _)
  exact continuation answer _ (by omega)

/-- Where the index phase ends. -/
theorem afterIndex_pc (answer : BitVec hashBits) :
    (afterIndex pk m view answer).pc = W blockZero := by
  have e1 : (afterIndex pk m view answer).pc = (S5 pk m view answer).pc +
      BitVec.ofNat 64 (4 * chainSetup.length) := Riscv.linear_fold_pc _ _ (setup_ready _)
  have e3 : (S5 pk m view answer).pc = (S4 pk m view answer).pc +
      BitVec.ofNat 64 (4 * mainBlock.length) :=
    Riscv.linear_fold_pc _ _ (mainBlock_ready pk m view answer)
  have e6 : (S4 pk m view answer).pc = (afterPrefix pk m view).pc + 4 := rfl
  rw [e1, e3, e6, (prefix_effect pk m view).pc, mainBlock_length]
  simp only [chainSetup, List.length_cons, List.length_nil, blockZero]
  decide

end Refine

end OptimalOTS.RiscvMixedProgram
