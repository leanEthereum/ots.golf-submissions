import Submissions.UpperLeanIsa.AffineGuard

/-! A final checksum can land in the program only at its intended sentinel.
This rules out re-entering the prologue with a wrong checksum. -/

namespace OptimalOTS.AffineFrames

open Polynomial LeanerVM.Parameters
noncomputable section

theorem checksum_landing_exact (L : Layout) {layer s c : ℕ} (target : Slot)
    (hLayer : layer ≤ 300) (hSum : s + c ≤ 300) :
    initialProduct L layer s * safeBase L ^ c = gpow target.val ↔
      s + c = layer ∧ target.val = 2 ^ 18 - 1 := by
  constructor
  · intro h
    by_contra hwrong
    have hf : ¬((⟨s+c,by omega⟩ : Fin 301) = ⟨layer,by omega⟩ ∧
        target.val = 2 ^ 18 - 1) := fun he => hwrong ⟨Fin.mk.inj he.1,he.2⟩
    have avoid := safeBase_exit_avoids L ⟨s+c,by omega⟩ ⟨layer,by omega⟩ target
    simp only [exitPoly,if_neg hf,Polynomial.eval_sub,Polynomial.eval_C_mul,
      Polynomial.eval_X_pow,sub_ne_zero] at avoid
    apply avoid
    rw [initialProduct,mul_assoc,← pow_add,div_mul_eq_mul_div] at h
    exact (div_eq_iff (pow_ne_zero _ (safeBase_ne_zero L))).mp h
  · rintro ⟨hn,ht⟩
    rw [ht]
    exact (checksum_exact L hLayer hSum).mpr hn

end
end OptimalOTS.AffineFrames
