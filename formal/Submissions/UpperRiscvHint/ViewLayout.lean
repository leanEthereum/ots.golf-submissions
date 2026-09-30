import Submissions.UpperRiscvHint.MixedLayout

/-! The in-place view holds the nonce in bits [0,128) and the chain values at
fixed byte positions. Cap 32's value occupies bits [176,320), and the free chain's
value begins at bit 320. The remaining values lie at wireOffset k.

viewNonce and viewPayload extract the nonce and values in graph/signature order.
For a valid free count c, honestView has 7424 + 4*(31-c) bits. Its length supplies
the count to the machine. The former count byte at bit 512 is harmless padding;
the certificate does not rely on its contents. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (W)
open OptimalOTS.Dag Forest

/-- The view bit that holds graph payload bit `p`. -/
def viewIndex (p : ℕ) : ℕ :=
  if p < 2688 then wireOffset (p / 192) + p % 192
  else if p < 5226 then wireOffset (14 + (p - 2688) / 141) + (p - 2688) % 141
  else wireOffset 32 + (p - 5226)

def viewNonce (view : List Bool) : List Bool := List.ofFn fun i : Fin 128 => view.getD i false

def viewPayload (view : List Bool) : List Bool :=
  List.ofFn fun p : Fin 5370 => view.getD (viewIndex p) false

theorem viewIndex_chain (k : Chain) (i : ℕ) (hi : i < wireBits k) :
    viewIndex (cursor k + i) = wireOffset k + i := by
  have all : ∀ k : Chain, ∀ i : Fin 192, i.val < wireBits k →
      viewIndex (cursor k + i.val) = wireOffset k + i.val := by decide +kernel
  exact all k ⟨i, lt_of_lt_of_le hi (wireBits_le k)⟩ hi

theorem cursor_contained (k : Chain) : cursor k + wireBits k ≤ 5370 := by
  have := k.isLt
  unfold cursor wireBits chainBits; split_ifs <;> omega

/-- The payload reader presents exactly the view bits each chain reads from memory. -/
theorem viewPayload_read_width (view : List Bool) (k : Chain) (n : ℕ) (hn : n ≤ wireBits k) :
    ofBits n ((viewPayload view).drop (cursor k)) =
      ofBits n (view.drop (wireOffset k)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc : cursor k + i < 5370 := by have := cursor_contained k; omega
  simp only [ofBits, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    testBit_foldr_bits, List.getD_eq_getElem?_getD, List.getElem?_drop]
  simp only [viewPayload, List.getElem?_ofFn, hc, List.getD_eq_getElem?_getD, viewIndex_chain k i (by omega)]
  rfl

theorem viewPayload_read (view : List Bool) (k : Chain) :
    ofBits (chainBits k) ((viewPayload view).drop (cursor k)) =
      ofBits (chainBits k) (view.drop (wireOffset k)) :=
  viewPayload_read_width view k _ (chainBits_le_wireBits k)

@[simp] theorem viewNonce_length (view : List Bool) : (viewNonce view).length = 128 :=
  List.length_ofFn

@[simp] theorem viewPayload_length (view : List Bool) : (viewPayload view).length = 5370 :=
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

/-- The full-signature bit placed at view bit `b`; 5498 marks zero padding. -/
def sigIndex (b : ℕ) : ℕ :=
  if b < 128 then b
  else if 176 ≤ b ∧ b < 320 then 5354 + (b - 176)
  else if b < 320 then 5498
  else if b - 320 < 6272 then
    if (b - 320) % 448 < 192 then 128 + 192 * ((b - 320) / 448) + (b - 320) % 448
    else if 304 ≤ (b - 320) % 448 ∧ (b - 320) % 448 < 445 then
      2816 + 141 * ((b - 320) / 448) + ((b - 320) % 448 - 304)
    else 5498
  else if 6640 ≤ b ∧ b < 7165 ∧ (b - 6640) % 192 < 141 then
    4790 + 141 * ((b - 6640) / 192) + (b - 6640) % 192
  else if 7168 ≤ b ∧ b < 7309 then 5213 + (b - 7168)
  else 5498

/-- The in-place view of a signature with free count `c`: its nonce, every chain value in its
cell, and `v = 4 c`. -/
def honestView (σ : List Bool) (c : ℕ) : List Bool :=
  List.ofFn fun b : Fin (7424 + 4*(31-c)) =>
    if freeBit ≤ b.val ∧ b.val < freeBit + 8 then (4 * c).testBit (b.val - freeBit)
    else σ.getD (sigIndex b) false

theorem honestView_getD {σ : List Bool} {c b : ℕ} (hb : b < honestViewBits)
    (hv : ¬ (freeBit ≤ b ∧ b < freeBit + 8)) :
    (honestView σ c).getD b false = σ.getD (sigIndex b) false := by
  rw [List.getD_eq_getElem?_getD, honestView, List.getElem?_ofFn, dif_pos (show b < 7424 + 4*(31-c) by unfold honestViewBits at hb; omega), Option.getD_some,
    if_neg hv]

theorem viewNonce_honestView {σ : List Bool} (c : ℕ) (h : σ.length = 5498) :
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

theorem viewIndex_lt (p : ℕ) (hp : p < 5370) : viewIndex p < honestViewBits := by
  unfold viewIndex honestViewBits wireOffset wireByte outAddr
  split_ifs <;> omega

theorem viewIndex_free (p : ℕ) (hp : p < 5370) :
    ¬ (freeBit ≤ viewIndex p ∧ viewIndex p < freeBit + 8) := by
  unfold viewIndex freeBit wireOffset wireByte outAddr
  split_ifs <;> omega

theorem sigIndex_viewIndex (p : ℕ) (hp : p < 5370) : sigIndex (viewIndex p) = 128 + p := by
  unfold viewIndex wireOffset wireByte outAddr
  split_ifs <;> (unfold sigIndex; split_ifs <;> omega)

/-- The honest view reads back as the signature's payload, in the same order. -/
theorem viewPayload_honestView {σ : List Bool} (c : ℕ) (h : σ.length = 5498) :
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
