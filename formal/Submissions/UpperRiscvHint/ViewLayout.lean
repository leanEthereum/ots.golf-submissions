import Submissions.UpperRiscvHint.MixedLayout

/-! The in-place view. Bits `[0,128)` hold the nonce and the root region follows. Region bits
`[0,144)` hold normal chain 32's value, region bits `[192,384)` the free chain's value and region
byte 48 the free count `v`. From region bit 192 to 5760 the region is a run of 448-bit cells:
cell `i` holds cap `i`'s 192-bit value at bit 0 (`i ≥ 1`) and normal chain `13 + i`'s 144-bit
value at bit 256 (`i < 12`). After it, normal chain `25 + t` has its value at region bit
`5824 + 192 t`. The honest view is 7248 bits and is zero outside the nonce, the values and `v`.

`viewNonce` and `viewPayload` read a view, with zero padding, as the nonce and the chain values in
graph order, which is the signature's order. `honestView σ c` places a 5504-bit signature with
free count `c`. -/

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (W)
open OptimalOTS.Dag Forest

/-- The view bit that holds graph payload bit `p`. -/
def viewIndex (p : ℕ) : ℕ :=
  if p < 2496 then wireOffset (p / 192) + p % 192
  else wireOffset (13 + (p - 2496) / 144) + (p - 2496) % 144

def viewNonce (view : List Bool) : List Bool := List.ofFn fun i : Fin 128 => view.getD i false

def viewPayload (view : List Bool) : List Bool :=
  List.ofFn fun p : Fin 5376 => view.getD (viewIndex p) false

theorem viewIndex_chain (k : Chain) (i : ℕ) (hi : i < chainBits k) :
    viewIndex (cursor k + i) = wireOffset k + i := by
  have hk := k.isLt
  unfold chainBits at hi
  by_cases h13 : k.val < 13
  · rw [if_pos h13] at hi
    have hc : cursor k = 192 * k.val := by unfold cursor; rw [if_pos (by omega)]
    rw [hc]; unfold viewIndex; rw [if_pos (by omega)]
    rw [show (192 * k.val + i) / 192 = k.val by omega, show (192 * k.val + i) % 192 = i by omega]
  · rw [if_neg h13] at hi
    have hc : cursor k = 2496 + 144 * (k.val - 13) := by unfold cursor; split_ifs <;> omega
    rw [hc]; unfold viewIndex; rw [if_neg (by omega)]
    rw [show (2496 + 144 * (k.val - 13) + i - 2496) / 144 = k.val - 13 by omega,
      show (2496 + 144 * (k.val - 13) + i - 2496) % 144 = i by omega,
      show 13 + (k.val - 13) = k.val by omega]

theorem cursor_contained (k : Chain) : cursor k + chainBits k ≤ 5376 := by
  have := k.isLt
  unfold cursor chainBits; split_ifs <;> omega

/-- The payload reader presents exactly the view bits each chain reads from memory. -/
theorem viewPayload_read (view : List Bool) (k : Chain) :
    ofBits (chainBits k) ((viewPayload view).drop (cursor k)) =
      ofBits (chainBits k) (view.drop (wireOffset k)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : cursor k + i < 5376 := by have := cursor_contained k; omega
  simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_drop]
  simp only [viewPayload, List.getElem?_ofFn, hc, List.getD_eq_getElem?_getD, viewIndex_chain k i hi]
  rfl

@[simp] theorem viewNonce_length (view : List Bool) : (viewNonce view).length = 128 :=
  List.length_ofFn

@[simp] theorem viewPayload_length (view : List Bool) : (viewPayload view).length = 5376 :=
  List.length_ofFn

/-- The machine hashes the zero-padded first 128 view bits as the nonce. -/
theorem ofBits_viewNonce (view : List Bool) :
    ofBits nonceBits (viewNonce view) = ofBits nonceBits view := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 128 at hi
  simp only [ofBits, BitVec.getLsbD_ofNat, testBit_foldr_bits, List.getD_eq_getElem?_getD,
    viewNonce, List.getElem?_ofFn]
  simp [hi]

/-! ## The honest view -/

/-- The first view bit of the free count `v`. -/
def freeBit : ℕ := 512

/-- The signature bit placed at view bit `b`; 5504, past every signature, marks padding. -/
def sigIndex (b : ℕ) : ℕ :=
  if b < 128 then b
  else if b < 272 then 5360 + (b - 128)
  else if b < 320 then 5504
  else if b - 320 < 5568 then
    if (b - 320) % 448 < 192 then 128 + 192 * ((b - 320) / 448) + (b - 320) % 448
    else if 256 ≤ (b - 320) % 448 ∧ (b - 320) % 448 < 400 ∧ (b - 320) / 448 < 12 then
      2624 + 144 * ((b - 320) / 448) + ((b - 320) % 448 - 256)
    else 5504
  else if 5632 ≤ b - 320 ∧ (b - 5952) % 192 < 144 ∧ (b - 5952) / 192 < 7 then
    4352 + 144 * ((b - 5952) / 192) + (b - 5952) % 192
  else 5504

/-- The in-place view of a signature with free count `c`: its nonce, every chain value in its
cell, and `v = 4 c`. -/
def honestView (σ : List Bool) (c : ℕ) : List Bool :=
  List.ofFn fun b : Fin honestViewBits =>
    if freeBit ≤ b.val ∧ b.val < freeBit + 8 then (4 * c).testBit (b.val - freeBit)
    else σ.getD (sigIndex b) false

theorem honestView_getD {σ : List Bool} {c b : ℕ} (hb : b < honestViewBits)
    (hv : ¬ (freeBit ≤ b ∧ b < freeBit + 8)) :
    (honestView σ c).getD b false = σ.getD (sigIndex b) false := by
  rw [List.getD_eq_getElem?_getD, honestView, List.getElem?_ofFn, dif_pos hb, Option.getD_some,
    if_neg hv]

theorem viewNonce_honestView {σ : List Bool} (c : ℕ) (h : σ.length = 5504) :
    viewNonce (honestView σ c) = σ.take 128 := by
  apply List.ext_getElem
  · rw [viewNonce_length, List.length_take, h]; rfl
  · intro i h1 h2
    rw [viewNonce_length] at h1
    simp only [viewNonce, List.getElem_ofFn, List.getElem_take]
    change (honestView σ c).getD i false = _
    rw [honestView_getD (by unfold honestViewBits; omega) (by unfold freeBit; omega)]
    unfold sigIndex
    rw [if_pos h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]

theorem viewIndex_lt (p : ℕ) (hp : p < 5376) : viewIndex p < honestViewBits := by
  unfold viewIndex honestViewBits wireOffset wireByte
  split_ifs <;> omega

theorem viewIndex_free (p : ℕ) (hp : p < 5376) :
    ¬ (freeBit ≤ viewIndex p ∧ viewIndex p < freeBit + 8) := by
  unfold viewIndex freeBit wireOffset wireByte
  split_ifs <;> omega

theorem sigIndex_viewIndex (p : ℕ) (hp : p < 5376) : sigIndex (viewIndex p) = 128 + p := by
  unfold viewIndex wireOffset wireByte
  split_ifs <;> (unfold sigIndex; split_ifs <;> omega)

/-- The honest view reads back as the signature's payload, in the same order. -/
theorem viewPayload_honestView {σ : List Bool} (c : ℕ) (h : σ.length = 5504) :
    viewPayload (honestView σ c) = σ.drop 128 := by
  apply List.ext_getElem
  · rw [viewPayload_length, List.length_drop, h]
  · intro p h1 h2
    rw [viewPayload_length] at h1
    simp only [viewPayload, List.getElem_ofFn, List.getElem_drop]
    change (honestView σ c).getD (viewIndex p) false = _
    rw [honestView_getD (viewIndex_lt p h1) (viewIndex_free p h1), sigIndex_viewIndex p h1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

end OptimalOTS.RiscvMixedProgram
