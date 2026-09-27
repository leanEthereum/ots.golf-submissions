import Submissions.UpperLeanIsa.AffineCycles
import Submissions.UpperLeanIsa.FourMachineValues

/-! The abstract affine codec agrees with every domain word read by the
machine; the chain lengths, digits, and reconstruction order stay the same. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer OptimalOTS.LeanIsa
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def cV (T : Tab) (c : ℕ) : E := ofK (base T ^ c)
def gV (T : Tab) : E := cV T 14

structure Compat (P : FourFusion.Params) (T : Tab) : Prop where
  len : ∀ k : Fin numChains, P.codec.len k = LEN k.val
  layer : P.codec.layer = 86
  digit_grp : ∀ (I : Word) (u i : ℕ) (hu : u < 13) (hi : i < gk u),
    P.codec.digit (effective I) ⟨chainOf u i, chainOf_lt u hu i hi⟩ = T u (field u I) i
  digit_free : ∀ I : Word, (∀ u < 13, field u I < VF u) →
    P.codec.digit (effective I) 0 = freeDigit (gcost T I)
  live : ∀ I : Word, P.codec.Accepted (effective I) → ∀ u < 13, field u I < VF u
  tag : ∀ (k : Fin numChains) (j : ℕ), j+1 < LEN k.val →
    P.codec.tag k j 0 = cellBits (cV T ((OFFT k.val+j)%9)) ∧
      P.codec.tag k j 1 = cellBits (cV T ((OFFT k.val+j)/9%9)) ∧
      P.codec.tag k j 2 = cellBits (cV T ((OFFT k.val+j)/81))
  hiTop : ∀ k : Fin numChains, P.codec.hiTop k = decide (k.val ∈ [7,8,10,13,19,23,25,31,33,39])
  cv : P.codec.cv = cellBits (gV T) ++ cellBits oneV
  chainMd : P.codec.chainMd = cellBits oneV
  idxMd : P.codec.idxMd = cellBits (gV T)
  fusedMd : ∀ k : Fin 42, P.fusedMd k = AffineCodec.word (layout T) (FourFusion.mdIndex k).val
  fusedTag : ∀ k : Fin 42, P.fusedTag k = AffineCodec.word (layout T) (FourFusion.tagIndex k).val
  rootMd : ∀ r : Fin 1, P.rootMd r = cellBits (cV T (FourFusion.rootIndex r).val)

theorem concrete_compat : Compat (AffineCodec.params (layout fusionTab)) fusionTab where
  len := fusion_compat.len
  layer := fusion_compat.layer
  digit_grp := fusion_compat.digit_grp
  digit_free := fusion_compat.digit_free
  live := fusion_compat.live
  tag k j _ := by
    refine ⟨?_,?_,?_⟩ <;>
    · change AffineCodec.word (layout fusionTab) _ = _
      rw [off_eq k.val k.isLt]
      rfl
  hiTop := fusion_compat.hiTop
  cv := rfl
  chainMd := by
    change cellBits (ofK (base fusionTab^0)) = cellBits oneV
    rw [pow_zero]
    rfl
  idxMd := rfl
  fusedMd _ := rfl
  fusedTag _ := rfl
  rootMd _ := rfl

end
end OptimalOTS.AffineVM
