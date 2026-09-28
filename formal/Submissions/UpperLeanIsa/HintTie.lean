import Submissions.UpperLeanIsa.FourMachineLayout
import Submissions.UpperLeanIsa.GenOrderFast

/-! Unit 11's landing hint as its tie pattern.

The block of unit 11's field value `v` starts at slot `e` with `g ^ e = hintMask v ^^^ v · 2 ^ 28`
(`gpow_entry11`). The kernel checks one power and then the 511 products between consecutive
blocks in slot order (`hint11_chain`). So the tie `acc_11 = acc_10 + H_12`
adds unit 11's rotated pattern together with the mask, and the final accumulator unmasks to the
field layout of the index (`unmask_accBits`). -/

namespace OptimalOTS.HLFour

open LeanerVM.Parameters
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits)
open OptimalOTS.HLG3 (cellOfBits_add xor_mul_eq_add)

theorem BASE_11 : BASE 11 = 226031 := by decide +kernel

theorem POS_11 : POS 11 = 109 := by decide

/-- `g ^ e` at the entry of unit 11's block `j` in slot order. -/
def hintT (j : ℕ) : ℕ := Nat.xor (hintMaskV (ord11 j)) (ord11 j * 2 ^ 28)

theorem hint11_chain : GenFast.fpow 2 18 226031 = hintT 0 ∧
    ∀ j < 511, BF64Fast.fastMul (hintT j) (GenFast.fpow 2 8 (gap11 j)) = hintT (j + 1) := by
  decide +kernel

theorem gpow_slot11 (j : ℕ) (hj : j < 512) : (gpow (226031 + bd11 j)).toNat = hintT j := by
  induction j with
  | zero => rw [GenFast.pow_toNat g 18 _ (by decide)]; exact hint11_chain.1
  | succ j ih =>
    rw [bd11_succ, ← add_assoc, ← gpow_mul_gpow, BF64Fast.mul_toNat, ih (by omega),
      GenFast.pow_toNat g 8 (gap11 j) (Nat.mod_lt _ (by norm_num))]
    exact hint11_chain.2 j (by omega)

theorem gpow_entry11 {v : ℕ} (hv : v < 512) :
    (gpow (entryOf 11 v)).toNat = Nat.xor (hintMaskV v) (v * 2 ^ 28) := by
  obtain ⟨hp, hop⟩ := pos11_spec v hv
  simp only [entryOf, if_true, BASE_11]
  rw [gpow_slot11 _ hp, hintT, hop]

theorem ofK_eq_cellOfBits (k : K) : ofK k = cellOfBits (BitVec.ofNat 128 k.toNat) := by
  have hk := k.isLt
  rw [ofK_eq_ofLimbs]
  unfold LeanIsa.cellOfBits
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  · apply BitVec.eq_of_toNat_eq
    have h0 : BitVec.toNat (0 : K) = 0 := rfl
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0]
    omega

theorem rot_field11 {v : ℕ} (hv : v < 512) :
    (BitVec.ofNat 128 (v * 2 ^ 109)).rotateLeft 47 = BitVec.ofNat 128 (v * 2 ^ 28) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : v * 2 ^ 109 < 2 ^ 128), Nat.mod_eq_of_lt (by omega : v * 2 ^ 28 < 2 ^ 128)]
  have h1 : (v * 2 ^ 109) <<< (47 % 128) % 2 ^ 128 = 0 := by
    rw [Nat.shiftLeft_eq, show 47 % 128 = 47 from rfl,
      show v * 2 ^ 109 * 2 ^ 47 = v * 2 ^ 28 * 2 ^ 128 by ring, Nat.mul_mod_left]
  have h2 : (v * 2 ^ 109) >>> (128 - 47 % 128) = v * 2 ^ 28 := by
    rw [Nat.shiftRight_eq_div_pow, show 128 - 47 % 128 = 81 from rfl,
      show v * 2 ^ 109 = v * 2 ^ 28 * 2 ^ 81 by ring, Nat.mul_div_cancel _ (by positivity)]
  rw [h1, h2, Nat.zero_or]

/-- The hint word of unit 11's block `v` is its tie pattern plus the known mask. -/
theorem hint11_cell {v : ℕ} (hv : v < 512) :
    ofK (gpow (entryOf 11 v)) = fpat 11 v + cellOfBits (hintMask v) := by
  have hm := (hintMaskV_bits v).2
  rw [ofK_eq_cellOfBits, gpow_entry11 hv, fpat, POS_11, rot_field11 hv, cellOfBits_add]
  congr 1
  have hA : Nat.xor (hintMaskV v) (v * 2 ^ 28) < 2 ^ 128 :=
    Nat.xor_lt_two_pow (by omega) (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, hintMask, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (by omega : v * 2 ^ 28 < 2 ^ 128),
    Nat.mod_eq_of_lt (by omega : hintMaskV v < 2 ^ 128)]
  exact Nat.xor_comm _ _

/-- The accumulator after group `u`: the rotated field prefix, plus unit 11's mask from `u = 11`. -/
def accBits (x : ℕ → ℕ) (u : ℕ) : BitVec 128 :=
  (BitVec.ofNat 128 (ofDigitsW gb x (u + 1))).rotateLeft 47 ^^^
    (if 11 ≤ u then hintMask (x 11) else 0#128)

section Tie

variable {x : ℕ → ℕ} (hx : ∀ w, x w < 2 ^ gb w)
theorem accBits_congr {x y : ℕ → ℕ} (h : ∀ w < 13, x w = y w) {u : ℕ} (hu : u < 13) :
    accBits x u = accBits y u := by
  unfold accBits
  have hd : ofDigitsW gb x (u + 1) = ofDigitsW gb y (u + 1) := by
    unfold ofDigitsW
    exact Finset.sum_congr rfl fun w hw => by rw [h w (by have := Finset.mem_range.mp hw; omega)]
  rw [hd, h 11 (by omega)]

include hx

theorem ofNat_digits_succ {u : ℕ} (hu : u < 13) :
    BitVec.ofNat 128 (ofDigitsW gb x (u + 1)) =
      BitVec.ofNat 128 (ofDigitsW gb x u) ^^^ BitVec.ofNat 128 (x u * 2 ^ POS u) := by
  have hl1 := ofDigitsW_lt gb x hx u
  have hl2 := ofDigitsW_lt gb x hx (u + 1)
  have hpos : 2 ^ posW gb (u + 1) ≤ 2 ^ 128 := by
    rw [← POS_13]; exact Nat.pow_le_pow_right (by norm_num) (posW_mono gb (by omega))
  rw [ofDigitsW_succ] at hl2 ⊢
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by unfold POS; omega)]
  unfold POS
  exact (xor_mul_eq_add hl1).symm

theorem accBits_zero : cellOfBits (accBits x 0) = fpat 0 (x 0) := by
  unfold accBits fpat
  rw [if_neg (by omega), BitVec.xor_zero, ofNat_digits_succ hx (by omega), ofDigitsW_zero]
  simp

theorem accBits_step {u : ℕ} (hu : u + 1 < 13) (h11 : u + 1 ≠ 11) :
    cellOfBits (accBits x u) + fpat (u + 1) (x (u + 1)) = cellOfBits (accBits x (u + 1)) := by
  unfold accBits fpat
  rw [cellOfBits_add, ofNat_digits_succ hx hu, rotL_xor]
  have hm : (if 11 ≤ u + 1 then hintMask (x 11) else 0#128) =
      (if 11 ≤ u then hintMask (x 11) else 0#128) := by
    by_cases h : 11 ≤ u
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  rw [hm]
  congr 1
  rw [BitVec.xor_assoc, BitVec.xor_comm (if 11 ≤ u then hintMask (x 11) else 0#128) _,
    ← BitVec.xor_assoc]

theorem accBits_zero_step {u : ℕ} (hu : u + 1 < 13) (h11 : u + 1 ≠ 11) (h0 : x (u + 1) = 0) :
    accBits x (u + 1) = accBits x u := by
  have h := accBits_step hx hu h11
  rw [h0] at h
  have hz : fpat (u + 1) 0 = 0 := by
    unfold fpat
    rw [Nat.zero_mul, show (BitVec.ofNat 128 0).rotateLeft 47 = 0#128 by decide]
    exact OptimalOTS.HLG3.cellOfBits_zero
  rw [hz, add_zero] at h
  exact (OptimalOTS.LeanIsa.cellBits_cellOfBits _).symm.trans
    ((congrArg cellBits h).symm.trans (OptimalOTS.LeanIsa.cellBits_cellOfBits _))

theorem accBits_11 (hx11 : x 11 < 512) :
    cellOfBits (accBits x 10) + ofK (gpow (entryOf 11 (x 11))) = cellOfBits (accBits x 11) := by
  rw [hint11_cell hx11, ← add_assoc]
  unfold accBits fpat
  rw [show (10 : ℕ) + 1 = 11 from rfl, if_neg (by omega), if_pos (by omega), BitVec.xor_zero,
    cellOfBits_add, cellOfBits_add, ofNat_digits_succ hx (u := 11) (by omega), rotL_xor]

theorem unmask_accBits : unmask (accBits x 12) = BitVec.ofNat 128 (ofDigitsW gb x 13) := by
  unfold accBits
  rw [if_pos (by omega)]
  apply unmask_hint
  have hl := ofDigitsW_lt gb x hx 13
  rw [show posW gb 13 = 128 from POS_13] at hl
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.shiftRight_eq_div_pow]
  have h := digitW_ofDigitsW gb x hx 13 11 (by omega)
  unfold digitW at h
  rw [show posW gb 11 = 109 from POS_11, show gb 11 = 9 from rfl] at h
  exact h

end Tie

/-- The honest index word is the accumulator of its own fields. -/
theorem accBits_digits (I : BitVec 128) :
    accBits (fun w => digitW gb (unmask I).toNat w) 12 = I := by
  have hlt : (unmask I).toNat < 2 ^ posW gb 13 := by
    rw [show posW gb 13 = 128 from POS_13]; exact (unmask I).isLt
  unfold accBits
  rw [if_pos (by omega), show (12 : ℕ) + 1 = 13 from rfl, ofDigitsW_digitW gb _ 13 hlt,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  conv_rhs => rw [← remask_unmask I]
  unfold remask
  congr 2
  rw [hintField_rotL]
  dsimp only
  unfold digitW
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, show posW gb 11 = 109 from POS_11]
  rfl

end OptimalOTS.HLFour
