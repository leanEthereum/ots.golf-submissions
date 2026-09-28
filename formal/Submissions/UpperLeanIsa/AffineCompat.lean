import Submissions.UpperLeanIsa.AffineCycles
import Submissions.UpperLeanIsa.SplitValues

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
  layer : P.codec.layer = 85
  digit_grp : ∀ (I : Word) (u i : ℕ) (hu : u < 13) (hi : i < gk u),
    P.codec.digit (effective I) ⟨chainOf u i, chainOf_lt u hu i hi⟩ = T u (field u I) i
  digit_free : ∀ I : Word, (∀ u < 13, field u I < VF u) →
    P.codec.digit (effective I) 0 = freeDigit (gcost T I)
  live : ∀ I : Word, P.codec.Accepted (effective I) → ∀ u < 13, field u I < VF u
  tag : ∀ (k : Fin numChains) (j : ℕ), j+1 < LEN k.val →
    P.codec.tag k j 0 = cellBits (cV T ((OFFT k.val+j)%9)) ∧
      P.codec.tag k j 1 = cellBits (cV T ((OFFT k.val+j)/9%9)) ∧
      P.codec.tag k j 2 = cellBits (cV T ((OFFT k.val+j)/81))
  hiTop : ∀ k : Fin numChains, P.codec.hiTop k = decide (k.val ∈ [1,19,25,34,12,16,23,33,8])
  cv : P.codec.cv = cellBits (gV T) ++ cellBits oneV
  chainMd : P.codec.chainMd = cellBits oneV
  idxMd : P.codec.idxMd = cellBits (gV T)
  fusedMd : ∀ k : Fin 42, P.fusedMd k = AffineCodec.domainWord (layout T) (FourFusion.mdIndex k).val
  fusedTag : ∀ k : Fin 42, P.fusedTag k = AffineCodec.word (layout T) (FourFusion.tagIndex k).val
  rootMd : ∀ r : Fin 1, P.rootMd r = cellBits (cV T (FourFusion.rootIndex r).val)


end
end OptimalOTS.AffineVM
