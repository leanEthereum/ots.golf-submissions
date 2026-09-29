import Submissions.UpperLeanIsa.PartialHintLabels

/-! Complete raw-word permutation for the researched three-hint codec, and
the unchanged 256-bit oracle-output fiber cardinality. Machine integration is
separate: these theorems do not assert that bytecode enforces the new codec. -/
namespace OptimalOTS.PartialHints
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

open LeanIsaBaseline.Layer

def wordBitsEquiv : Word ≃ (Fin 128 → Bool) where
  toFun x := fun i => x.getLsbD i.val
  invFun f := ofBits 128 (List.ofFn f)
  left_inv x := ofBits_bits x
  right_inv f := by
    funext i
    have h := bits_ofBits (List.ofFn f) (by simp : (List.ofFn f).length = 128)
    have hh := congrArg (fun xs : List Bool => xs[i.val]?) h
    simp only [toBits, List.getElem?_ofFn, dif_pos i.isLt] at hh
    exact Option.some.inj hh

def wordPermutation : Word ≃ Word :=
  wordBitsEquiv.trans ((Equiv.arrowCongr bitEquiv (Equiv.refl Bool)).trans wordBitsEquiv.symm)

def field8 (x : Word) : BitVec 10 := x.extractLsb' 79 10
def replace8 (x : Word) (v : BitVec 10) : Word :=
  x.extractLsb' 89 39 ++ v ++ x.extractLsb' 0 79
def field9 (x : Word) : BitVec 10 := x.extractLsb' 89 10
def replace9 (x : Word) (v : BitVec 10) : Word :=
  x.extractLsb' 99 29 ++ v ++ x.extractLsb' 0 89

theorem field8_replace (x : Word) (v : BitVec 10) : field8 (replace8 x v) = v := by
  exact (BitVec.extractLsb'_append_eq_of_le
    (xhi := x.extractLsb' 89 39 ++ v) (xlo := x.extractLsb' 0 79)
    (start := 79) (len := 10) (by decide)).trans BitVec.extractLsb'_append_eq_right
theorem replace8_self (x : Word) : replace8 x (field8 x) = x := by
  unfold field8 replace8
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 89 = 79+10),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 79 = 0+79)]
  exact BitVec.extractLsb'_eq_self
theorem replace8_twice (x : Word) (v w : BitVec 10) : replace8 (replace8 x v) w = replace8 x w := by
  have hh : (replace8 x v).extractLsb' 89 39 = x.extractLsb' 89 39 :=
    (BitVec.extractLsb'_append_eq_of_le
      (xhi := x.extractLsb' 89 39 ++ v) (xlo := x.extractLsb' 0 79)
      (start := 89) (len := 39) (by decide)).trans BitVec.extractLsb'_append_eq_left
  have hl : (replace8 x v).extractLsb' 0 79 = x.extractLsb' 0 79 :=
    BitVec.extractLsb'_append_eq_right
  change (replace8 x v).extractLsb' 89 39 ++ w ++ (replace8 x v).extractLsb' 0 79 = _
  rw [hh, hl]
  rfl
theorem field9_replace (x : Word) (v : BitVec 10) : field9 (replace9 x v) = v := by
  exact (BitVec.extractLsb'_append_eq_of_le
    (xhi := x.extractLsb' 99 29 ++ v) (xlo := x.extractLsb' 0 89)
    (start := 89) (len := 10) (by decide)).trans BitVec.extractLsb'_append_eq_right
theorem replace9_self (x : Word) : replace9 x (field9 x) = x := by
  unfold field9 replace9
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 99 = 89+10),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 89 = 0+89)]
  exact BitVec.extractLsb'_eq_self
theorem replace9_twice (x : Word) (v w : BitVec 10) : replace9 (replace9 x v) w = replace9 x w := by
  have hh : (replace9 x v).extractLsb' 99 29 = x.extractLsb' 99 29 :=
    (BitVec.extractLsb'_append_eq_of_le
      (xhi := x.extractLsb' 99 29 ++ v) (xlo := x.extractLsb' 0 89)
      (start := 99) (len := 29) (by decide)).trans BitVec.extractLsb'_append_eq_left
  have hl : (replace9 x v).extractLsb' 0 89 = x.extractLsb' 0 89 :=
    BitVec.extractLsb'_append_eq_right
  change (replace9 x v).extractLsb' 99 29 ++ w ++ (replace9 x v).extractLsb' 0 89 = _
  rw [hh, hl]
  rfl

def field8Equiv (p : BitVec 10 ≃ BitVec 10) : Word ≃ Word where
  toFun x := replace8 x (p (field8 x))
  invFun x := replace8 x (p.symm (field8 x))
  left_inv x := by
    dsimp only
    rw [field8_replace, p.symm_apply_apply, replace8_twice, replace8_self]
  right_inv x := by
    dsimp only
    rw [field8_replace, p.apply_symm_apply, replace8_twice, replace8_self]

def field9Equiv (p : BitVec 10 ≃ BitVec 10) : Word ≃ Word where
  toFun x := replace9 x (p (field9 x))
  invFun x := replace9 x (p.symm (field9 x))
  left_inv x := by
    dsimp only
    rw [field9_replace, p.symm_apply_apply, replace9_twice, replace9_self]
  right_inv x := by
    dsimp only
    rw [field9_replace, p.apply_symm_apply, replace9_twice, replace9_self]

/-- Semantic tuple codes become physical labels, then permuted bits, then hints. -/
def rawEquiv : Word ≃ Word :=
  (field8Equiv label8Equiv.symm).trans
    ((field9Equiv label9Equiv.symm).trans (wordPermutation.trans hintEquiv))

def encodeRaw (x : Word) : Word := rawEquiv x
def decodeRaw (x : Word) : Word := rawEquiv.symm x

theorem decode_encode_raw (x : Word) : decodeRaw (encodeRaw x) = x := rawEquiv.symm_apply_apply x
theorem encode_decode_raw (x : Word) : encodeRaw (decodeRaw x) = x := rawEquiv.apply_symm_apply x

def effectiveIndex (w : Word) : BitVec 127 := (decodeRaw w).extractLsb' 1 127
def slice (w : BitVec 256) : BitVec 127 := effectiveIndex (w.extractLsb' 0 128)
def rest (w : BitVec 256) : BitVec 129 :=
  w.extractLsb' 128 128 ++ (decodeRaw (w.extractLsb' 0 128)).extractLsb' 0 1
def join (i : BitVec 127) (r : BitVec 129) : BitVec 256 :=
  r.extractLsb' 1 128 ++ encodeRaw (i ++ r.extractLsb' 0 1)

theorem join_split (w : BitVec 256) : join (slice w) (rest w) = w := by
  unfold join slice rest effectiveIndex
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    split_low, encode_decode_raw]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 128 = 0+128)]
  exact BitVec.extractLsb'_eq_self

theorem slice_join (i : BitVec 127) (r : BitVec 129) : slice (join i r) = i := by
  unfold slice join effectiveIndex
  rw [BitVec.extractLsb'_append_eq_right, decode_encode_raw,
    BitVec.extractLsb'_append_eq_of_le (by decide : 1 ≤ 1)]
  simp

theorem rest_join (i : BitVec 127) (r : BitVec 129) : rest (join i r) = r := by
  unfold rest join
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right, decode_encode_raw]
  simp only [BitVec.extractLsb'_append_eq_ite]
  norm_num

/-- Exactly the original factor, for every predicate on the effective index. -/
theorem card_slice (p : BitVec 127 → Prop) [DecidablePred p] :
    (Finset.univ.filter fun w : BitVec 256 => p (slice w)).card =
      (Finset.univ.filter p).card * 2^129 := by
  have hu : (Finset.univ : Finset (BitVec 129)).card = 2^129 := by
    rw [Finset.card_univ, Fintype.card_bitVec]
  rw [← hu, ← Finset.card_product]
  refine Finset.card_nbij' (fun w => (slice w, rest w))
    (fun x => join x.1 x.2) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
    simp [hw]
  · intro x hx
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_ofPred_eq, Finset.coe_univ, Set.mem_univ, and_true] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, slice_join]
    exact hx
  · intro w _
    exact join_split w
  · intro x _
    exact Prod.ext (slice_join _ _) (rest_join _ _)

end OptimalOTS.PartialHints
