import Submissions.UpperRiscvHint.MixedLayout

/-! The in-place view. Bits `[0,128)` hold the nonce and the root region follows, in 448-bit
cells: cell `j` holds cap `j`'s 192-bit value at bit 0 and normal chain `16 + j`'s 144-bit value at
bit 256. The honest view is 7248 bits and is zero outside the nonce and the values.

`viewNonce` and `viewPayload` read a view, with zero padding, as the nonce and the chain values in
graph order, which is the signature's order. `honestView` places a 5504-bit signature. -/

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (W)
open OptimalOTS.Dag Forest

/-- The view bit that holds graph payload bit `p`. -/
def viewIndex (p : ℕ) : ℕ :=
  if p < 3072 then wireOffset (p / 192) + p % 192
  else wireOffset (16 + (p - 3072) / 144) + (p - 3072) % 144

def viewNonce (view : List Bool) : List Bool := List.ofFn fun i : Fin 128 => view.getD i false

def viewPayload (view : List Bool) : List Bool :=
  List.ofFn fun p : Fin 5376 => view.getD (viewIndex p) false

theorem viewIndex_chain (k : Fin 32) (i : ℕ) (hi : i < chainBits k) :
    viewIndex (cursor k + i) = wireOffset k + i := by
  have hk := k.isLt
  unfold viewIndex cursor
  unfold chainBits at hi
  split_ifs at hi ⊢ with h1 h2 h2
  · rw [show (192 * k.val + i) / 192 = k.val by omega, show (192 * k.val + i) % 192 = i by omega]
  · omega
  · omega
  · rw [show (3072 + 144 * (k.val - 16) + i - 3072) / 144 = k.val - 16 by omega,
      show (3072 + 144 * (k.val - 16) + i - 3072) % 144 = i by omega,
      show 16 + (k.val - 16) = k.val by omega]

theorem cursor_contained (k : Fin 32) : cursor k + chainBits k ≤ 5376 := by
  have := k.isLt
  unfold cursor chainBits; split_ifs <;> omega

/-- The payload reader presents exactly the view bits each chain reads from memory. -/
theorem viewPayload_read (view : List Bool) (k : Fin 32) :
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

/-- The signature bit placed at view bit `b`; 5504, past every signature, marks padding. -/
def sigIndex (b : ℕ) : ℕ :=
  if b < 128 then b
  else if (b - 128) % 448 < 192 then 128 + 192 * ((b - 128) / 448) + (b - 128) % 448
  else if 256 ≤ (b - 128) % 448 ∧ (b - 128) % 448 < 400 then
    3200 + 144 * ((b - 128) / 448) + ((b - 128) % 448 - 256)
  else 5504

/-- The in-place view of a signature: its nonce, then every chain value in its cell. -/
def honestView (σ : List Bool) : List Bool :=
  List.ofFn fun b : Fin honestViewBits => σ.getD (sigIndex b) false

theorem honestView_length (σ : List Bool) : (honestView σ).length = honestViewBits :=
  List.length_ofFn

theorem honestView_getD {σ : List Bool} {b : ℕ} (hb : b < honestViewBits) :
    (honestView σ).getD b false = σ.getD (sigIndex b) false := by
  rw [List.getD_eq_getElem?_getD, honestView, List.getElem?_ofFn, dif_pos hb, Option.getD_some]

theorem viewNonce_honestView {σ : List Bool} (h : σ.length = 5504) :
    viewNonce (honestView σ) = σ.take 128 := by
  apply List.ext_getElem
  · rw [viewNonce_length, List.length_take, h]; rfl
  · intro i h1 h2
    rw [viewNonce_length] at h1
    simp only [viewNonce, List.getElem_ofFn, List.getElem_take]
    change (honestView σ).getD i false = _
    rw [honestView_getD (by unfold honestViewBits; omega)]
    unfold sigIndex
    rw [if_pos h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]

theorem viewIndex_lt (p : ℕ) (hp : p < 5376) : viewIndex p < honestViewBits := by
  unfold viewIndex honestViewBits wireOffset wireByte
  split_ifs <;> omega

theorem sigIndex_viewIndex (p : ℕ) (hp : p < 5376) : sigIndex (viewIndex p) = 128 + p := by
  unfold viewIndex sigIndex wireOffset wireByte
  split_ifs <;> omega

/-- The honest view reads back as the signature's payload, in the same order. -/
theorem viewPayload_honestView {σ : List Bool} (h : σ.length = 5504) :
    viewPayload (honestView σ) = σ.drop 128 := by
  apply List.ext_getElem
  · rw [viewPayload_length, List.length_drop, h]
  · intro p h1 h2
    rw [viewPayload_length] at h1
    simp only [viewPayload, List.getElem_ofFn, List.getElem_drop]
    change (honestView σ).getD (viewIndex p) false = _
    rw [honestView_getD (viewIndex_lt p h1), sigIndex_viewIndex p h1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]

end OptimalOTS.RiscvMixedProgram
