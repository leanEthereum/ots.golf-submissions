import Submissions.UpperLeanIsa.AffineLength
import Submissions.UpperLeanIsa.FourMachineCycles

/-! Exact cost of the proposed straight blocks and a well-formed layer-86 path.
The missing machine-walk proof must still show that every completing execution
has such a path. These results are not `Submission.CyclesAtMost`. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
noncomputable section

def bodyCode (T : Tab) (a : K) (f x : ℕ) : List CInstr :=
  if f = 0 then
    [.setc (gpCell 0) (ofK (gpow sentinel / a ^ 77 * a ^ x))] ++
      chainOps 0 x tfCell ++ [copy (if x = 0 then wCell 0 else tfCell) tfCell,
        .xor (hCell 1) (cCell 1) (h1Cell 1)]
  else (body T (f-1) x false).map rehint

theorem bodyCode_length (T : Tab) (a : K) (f x : ℕ) :
    (bodyCode T a f x).length = (bodyF T f x).length := by
  by_cases hf : f = 0
  · subst f
    simp only [bodyCode,bodyF,ite_true,fbody,List.length_append,List.length_cons,List.length_nil]
  · simp only [bodyCode,bodyF,if_neg hf,List.length_map,gOf]

theorem bodyCode_lcost (T : Tab) (a : K) (f x : ℕ) :
    lcost (bodyCode T a f x) = lcost (bodyF T f x) := by
  by_cases hf : f = 0
  · subst f
    simp only [bodyCode,bodyF,ite_true,fbody,lcost_append,lcost_cons,lcost_nil,CInstr.cost,copy]
  · simp only [bodyCode,bodyF,if_neg hf,lcost,List.map_map,Function.comp_def,rehint_cost,gOf]

theorem bodyCode_straight (T : Tab) (a : K) (f x : ℕ) :
    ∀ ci ∈ bodyCode T a f x, ci.straight = true := by
  intro ci hi
  unfold bodyCode at hi
  by_cases hf : f = 0
  · rw [if_pos hf] at hi
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with (rfl | hi) | rfl | rfl
    · rfl
    · obtain ⟨t,ht,rfl⟩ := mem_chainOps.mp hi
      exact chainOp_straight _ _ _ _
    · rfl
    · rfl
  · rw [if_neg hf] at hi
    obtain ⟨ci',hi',rfl⟩ := List.mem_map.mp hi
    rw [rehint_straight]
    exact body_straight T _ _ _ _ hi'

theorem compile_straight_weight (q : K) (ci : CInstr) (h : ci.straight = true) :
    LeanIsa.weight (compile q ci).opcode = ci.cost := by
  cases ci <;> first | rfl | contradiction

theorem bodyCode_weight (T : Tab) (a q : K) (f x : ℕ) :
    ((bodyCode T a f x).map fun ci => LeanIsa.weight (compile q ci).opcode).sum =
      lcost (bodyF T f x) := by
  rw [← bodyCode_lcost T a f x]
  unfold lcost
  congr 1
  apply List.map_congr_left
  intro ci hi
  exact compile_straight_weight q ci (bodyCode_straight T a f x ci hi)

/-- Each of the fourteen dispatches now costs one instruction. -/
def pathCost (T : Tab) (xs : ℕ → ℕ) : ℕ :=
  27 + ∑ f ∈ Finset.range 14, (1 + lcost (bodyCode T (base T) f (xs f)))

def pathSteps (T : Tab) (xs : ℕ → ℕ) : ℕ :=
  18 + ∑ f ∈ Finset.range 14, (1 + (bodyCode T (base T) f (xs f)).length)

theorem pathCost_eq {T : Tab} (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs)
    (hLayer : xs 0 + gsum T xs = 86) : pathCost T xs = 990 := by
  have h := totalCost_eq hT hV hLayer
  simp only [totalCost,frU,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
    nsmul_eq_mul] at h
  simp only [pathCost,bodyCode_lcost,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul]
  omega

theorem pathSteps_eq {T : Tab} (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs)
    (hLayer : xs 0 + gsum T xs = 86) : pathSteps T xs = 198 := by
  have h := totalSteps_eq hT hV hLayer
  simp only [totalSteps,frU,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
    nsmul_eq_mul] at h
  simp only [pathSteps,bodyCode_length,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul]
  omega

theorem path_with_boundary {T : Tab} (hT : T.Hyp) {xs : ℕ → ℕ} (hV : Valid xs)
    (hLayer : xs 0 + gsum T xs = 86) : LeanIsa.boundaryCycles + pathCost T xs = 1110 := by
  rw [pathCost_eq hT hV hLayer,boundary_eq]

end
end OptimalOTS.AffineVM
