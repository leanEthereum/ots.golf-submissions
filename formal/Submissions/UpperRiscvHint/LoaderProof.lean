import OptimalOTS.RiscvHint
import Submissions.UpperRiscvHint.MachineMemory

/-! Exact memory contents installed by the hinted loader `RiscvHint.loadView`. -/

namespace OptimalOTS.Riscv2Program

open OptimalOTS.Dag

open RiscvZkvm.Rv64

@[simp] theorem bytesOfBits_length (bits : List Bool) :
    (Riscv.bytesOfBits bits).length = (bits.length + 7) / 8 := by simp [Riscv.bytesOfBits]

@[simp] theorem publicKeyBase_toNat : Riscv.publicKeyBase.toNat = 4194304 := rfl
@[simp] theorem messageBase_toNat : Riscv.messageBase.toNat = 4194320 := rfl
@[simp] theorem signatureBase_toNat : Riscv.signatureBase.toNat = 4194352 := rfl
@[simp] theorem dataBase_toNat : Riscv.dataBase.toNat = 2097152 := rfl

/-- A byte loader preserves every doubleword outside its occupied address interval. -/
theorem getMem_load_outside (s : MachineState) (base addr : Word) (bytes : List (BitVec 8))
    (bounded : base.toNat + 8 * ((bytes.length + 7) / 8) ≤ 2 ^ 64)
    (outside : addr.toNat < base.toNat ∨
      base.toNat + 8 * ((bytes.length + 7) / 8) ≤ addr.toNat) :
    (s.writeBytesAsWords base bytes).getMem addr = s.getMem addr := by
  apply getMem_writeBytesAsWords_of_disjoint
  intro j hj heq
  have hj8 : 8 * j < 2 ^ 64 := by omega
  have hb : base.toNat + 8 * j < 2 ^ 64 := by omega
  have he := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj8,
    Nat.mod_eq_of_lt hb] at he
  omega

/-- The zero-filled state before the loader installs its finite byte streams. -/
def loaderBlank (image : Riscv.Image) : MachineState :=
  { regs := fun _ => 0, mem := fun _ => 0,
    code := loadProgram Riscv.codeBase image.code, pc := Riscv.codeBase }

def loaderData (image : Riscv.Image) : MachineState :=
  (loaderBlank image).writeBytesAsWords Riscv.dataBase image.data

def loaderPublic (image : Riscv.Image) (pk : PublicKey) : MachineState :=
  (loaderData image).writeBytesAsWords Riscv.publicKeyBase (Riscv.bytesOfVector pk)

def loaderMessage (image : Riscv.Image) (pk : PublicKey)
    (m : Message) : MachineState :=
  (loaderPublic image pk).writeBytesAsWords Riscv.messageBase (Riscv.bytesOfVector m)

/-- Packing raw signature bytes agrees with the specification's zero-extending bit decoder. -/
theorem bytesToWordLE_bytesOfBits (bits : List Bool) (j : ℕ) :
    bytesToWordLE (((Riscv.bytesOfBits bits).drop (8 * j)).take 8) =
      ofBits 64 (bits.drop (64 * j)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bytesToWordLE_getLsbD _ hi]
  have hi8 : i / 8 < 8 := by omega
  have himod : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [List.getElem?_take, hi8, ↓reduceIte, List.getElem?_drop]
  by_cases hb : 8 * j + i / 8 < (bits.length + 7) / 8
  · rw [List.getElem?_eq_getElem (by simpa using hb), Option.getD_some,
      bytesOfBits_getLsbD bits hb himod]
    simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
      testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    omega
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hb)]
    simp only [Option.getD_none, ofBits, BitVec.getLsbD_ofNat,
      hi, decide_true, Bool.true_and, testBit_foldr_bits, List.getD_eq_getElem?_getD,
      List.getElem?_drop, List.getElem?_eq_none (by omega : bits.length ≤ 64 * j + i)]
    exact BitVec.getLsbD_zero

/-- Before loading the signature, all addresses above the message are still zero. -/
theorem loaderMessage_zero (image : Riscv.Image) (pk : PublicKey)
    (m : Message) (hdata : image.data.length ≤ 1048576)
    (addr : Word) (ha : 4194352 ≤ addr.toNat) :
    (loaderMessage image pk m).getMem addr = 0 := by
  rw [loaderMessage, getMem_load_outside, loaderPublic, getMem_load_outside,
    loaderData, getMem_load_outside]
  · rfl
  all_goals norm_num [Riscv.bytesOfVector, hashBits, blockBits, pkBits, msgBits, securityBits, maxSignatureBits, keygenBudget, signBudget] <;> omega

/-- Consecutive aligned words determine exactly the vector read by HASH. -/
theorem memBits_of_words {n : ℕ} (s : MachineState) (base : Word) (v : BitVec n)
    (ha : alignToDword base = base)
    (hw : ∀ j, j < (n + 63) / 64 →
      s.getMem (base + BitVec.ofNat 64 (8 * j)) = v.extractLsb' (64 * j) 64) :
    MemBits s base v := by
  intro i hi
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hk : (i / 8) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hword : alignToDword (base + BitVec.ofNat 64 (8 * (i / 64))) =
      base + BitVec.ofNat 64 (8 * (i / 64)) := by
    apply (aligned_iff _).mpr
    have hb := (aligned_iff base).mp ha
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have haddr : base + BitVec.ofNat 64 (i / 8) =
      (base + BitVec.ofNat 64 (8 * (i / 64))) + BitVec.ofNat 64 ((i / 8) % 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [haddr, getByte_of_aligned hword hk, hw (i / 64) (by omega)]
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hm, decide_true, Bool.true_and,
    BitVec.getLsbD_extractLsb']
  have hinner : (i / 8) % 8 * 8 + i % 8 < 64 := by omega
  simp only [hinner, decide_true, Bool.true_and]
  congr 1
  omega

/-- Decoding and taking a fully contained slice commute. -/
theorem ofBits_extract {n start len : ℕ} (bits : List Bool) (contained : start + len ≤ n) :
    (ofBits n bits).extractLsb' start len = ofBits len (bits.drop start) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : start + i < n := by omega
  simp only [BitVec.getLsbD_extractLsb', ofBits, BitVec.getLsbD_ofNat, hi, hn,
    decide_true, Bool.true_and, testBit_foldr_bits, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- A byte-aligned slice of a represented vector occupies the corresponding address interval. -/
theorem memBits_extract {n start len : ℕ} {s : MachineState} {base : Word} {v : BitVec n}
    (hm : MemBits s base v) (aligned : start % 8 = 0) (contained : start + len ≤ n) :
    MemBits s (base + BitVec.ofNat 64 (start / 8)) (v.extractLsb' start len) := by
  intro i hi
  have haddr : (base + BitVec.ofNat 64 (start / 8)) + BitVec.ofNat 64 (i / 8) =
      base + BitVec.ofNat 64 ((start + i) / 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  have hmod : (start + i) % 8 = i % 8 := by omega
  rw [haddr, ← hmod, hm (start + i) (by omega)]
  simp [hi]

/-- Bits beyond the target width cannot change a decoded slice. -/
theorem ofBits_drop_take (bits : List Bool) {cap start len : ℕ}
    (contained : start + len ≤ cap) :
    ofBits len ((bits.take cap).drop start) = ofBits len (bits.drop start) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hcap : start + i < cap := by omega
  simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_take, hcap, ↓reduceIte]

/-! ## The view loader -/

theorem loadView_getMem (image : Riscv.Image) (pk : PublicKey) (m : Message) (view : List Bool)
    (addr : Word) :
    (RiscvHint.loadView image pk m view).getMem addr =
      ((loaderMessage image pk m).writeBytesAsWords Riscv.signatureBase
        (Riscv.bytesOfBits (view.take RiscvHint.maxViewBits))).getMem addr := rfl

theorem loadView_publicKey_word (image : Riscv.Image) (pk : PublicKey)
    (m : Message) (view : List Bool) (j : ℕ) (hj : j < 2) :
    (RiscvHint.loadView image pk m view).getMem (Riscv.publicKeyBase + BitVec.ofNat 64 (8 * j)) =
      pk.extractLsb' (64 * j) 64 := by
  rw [loadView_getMem, getMem_load_outside, loaderMessage, getMem_load_outside, loaderPublic,
    getMem_writeBytesAsWords, bytesToWordLE_bytesOfVector]
  all_goals
    norm_num [Riscv.bytesOfVector, Riscv.bytesOfBits, hashBits, blockBits, pkBits, msgBits,
      securityBits, RiscvHint.maxViewBits, BitVec.toNat_add] <;> omega

theorem loadView_message_word (image : Riscv.Image) (pk : PublicKey)
    (m : Message) (view : List Bool) (j : ℕ) (hj : j < 4) :
    (RiscvHint.loadView image pk m view).getMem (Riscv.messageBase + BitVec.ofNat 64 (8 * j)) =
      m.extractLsb' (64 * j) 64 := by
  rw [loadView_getMem, getMem_load_outside, loaderMessage, getMem_writeBytesAsWords,
    bytesToWordLE_bytesOfVector]
  all_goals
    norm_num [Riscv.bytesOfVector, Riscv.bytesOfBits, hashBits, blockBits, pkBits, msgBits,
      securityBits, RiscvHint.maxViewBits, BitVec.toNat_add] <;> omega

/-- The view buffer holds the view's first `maxViewBits` bits, with zero padding. -/
theorem loadView_word (image : Riscv.Image) (pk : PublicKey) (m : Message) (view : List Bool)
    (hdata : image.data.length ≤ 1048576) (j : ℕ) (hj : j < 16384) :
    (RiscvHint.loadView image pk m view).getMem (Riscv.signatureBase + BitVec.ofNat 64 (8 * j)) =
      ofBits 64 ((view.take RiscvHint.maxViewBits).drop (64 * j)) := by
  rw [loadView_getMem]
  by_cases hb : j < ((Riscv.bytesOfBits (view.take RiscvHint.maxViewBits)).length + 7) / 8
  · rw [getMem_writeBytesAsWords _ _ _ (by simp [RiscvHint.maxViewBits]; omega) j hb,
      bytesToWordLE_bytesOfBits]
  · rw [getMem_load_outside, loaderMessage_zero _ _ _ hdata]
    · have hlen : (view.take RiscvHint.maxViewBits).length ≤ 64 * j := by
        simp only [bytesOfBits_length] at hb; omega
      rw [List.drop_eq_nil_iff.mpr hlen]
      rfl
    all_goals
      norm_num [Riscv.bytesOfBits, RiscvHint.maxViewBits, BitVec.toNat_add] at hb ⊢
      omega

/-- The first 7360 view bits, a whole number of words covering the nonce and every chain value. -/
theorem loadView_memBits (image : Riscv.Image) (pk : PublicKey) (m : Message) (view : List Bool)
    (hdata : image.data.length ≤ 1048576) :
    MemBits (RiscvHint.loadView image pk m view) Riscv.signatureBase (ofBits 7360 view) := by
  apply memBits_of_words _ _ _ (by decide +kernel)
  intro j hj
  rw [loadView_word image pk m view hdata j (by omega), ofBits_extract _ (by omega),
    ofBits_drop_take _ (by unfold RiscvHint.maxViewBits; omega)]

end OptimalOTS.Riscv2Program
