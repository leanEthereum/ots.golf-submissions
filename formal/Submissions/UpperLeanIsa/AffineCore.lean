import Submissions.UpperLeanIsa.AffineCompat

/-! The affine rewrite changes control hints; it preserves the chain, index
tie, root, and public-key assertions used to prove verification soundness. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
noncomputable section

theorem rehint_copy (a b : ℕ) : rehint (copy a b) = copy a b := rfl

theorem rehint_chainOp (readTop : ℕ → ℕ) (k d t dst : ℕ) :
    rehint (chainOp readTop k d t dst) = chainOp readTop k d t dst := by
  unfold chainOp
  split_ifs <;> rfl

theorem rehint_tie {u x : ℕ} {ci : CInstr} (h : ci ∈ tie u x) : rehint ci = ci := by
  unfold tie at h
  split_ifs at h <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  · subst ci; rfl
  · subst ci; rfl
  · rcases h with rfl | rfl <;> rfl

theorem rehint_seg (T : Tab) {u x i : ℕ} {ci : CInstr} (h : ci ∈ seg T u x i) :
    rehint ci = ci := by
  unfold seg at h
  split_ifs at h
  · simp only [List.mem_singleton] at h
    subst ci
    rfl
  · obtain ⟨t,ht,rfl⟩ := mem_chainOps.mp h
    exact rehint_chainOp ..
  · obtain ⟨t,ht,rfl⟩ := mem_chainOps.mp h
    exact rehint_chainOp ..

section Path

variable {T : Tab} {B : BlakeRel} {v : ℕ → E} {xs : ℕ → ℕ}

theorem PathFacts.group_rel (hp : PathFacts T B v xs) {u : ℕ} (hu : u < 13)
    {ci : CInstr} (hm : ci ∈ body T u (xs (u+1)) false) (he : rehint ci = ci) : ci.RelB B v := by
  have h := hp.blk (u+1) (by omega) (rehint ci) (by
    rw [bodyCode,if_neg (by omega),Nat.add_sub_cancel]
    exact List.mem_map.mpr ⟨ci,hm,rfl⟩)
  rwa [he] at h

theorem PathFacts.tie_rel (hp : PathFacts T B v xs) {u : ℕ} (hu : u < 13)
    {ci : CInstr} (hm : ci ∈ tie u (xs (u+1))) : ci.RelB B v :=
  hp.group_rel hu (by unfold body; simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hm)))))
    (rehint_tie hm)

theorem PathFacts.seg_rel (hp : PathFacts T B v xs) {u i : ℕ} (hu : u < 13) (hi : i < gk u)
    {ci : CInstr} (hm : ci ∈ seg T u (xs (u+1)) i) : ci.RelB B v := by
  apply hp.group_rel hu ?_ (rehint_seg T hm)
  unfold body
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (mem_segs.mpr ⟨i,hi,hm⟩))))

theorem PathFacts.free_chain (hp : PathFacts T B v xs) {t : ℕ} (ht : t < xs 0) :
    (chainOp topCell 0 (xs 0) t tfCell).RelB B v := by
  apply hp.blk 0 (by decide)
  rw [free_bodyCode]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (mem_chainOps.mpr ⟨t,ht,rfl⟩))

theorem PathFacts.free_copy (hp : PathFacts T B v xs) :
    (copy (if xs 0 = 0 then wCell 0 else tfCell) tfCell).RelB B v := by
  apply hp.blk 0 (by decide)
  rw [free_bodyCode]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)

theorem PathFacts.pk_copy (hp : PathFacts T B v xs) : (copy (stCell 0) pkCell).RelB B v :=
  hp.group_rel (u:=12) (by decide) (by unfold body nextOp; simp) (rehint_copy _ _)

theorem PathFacts.index (hp : PathFacts T B v xs) :
    (CInstr.blake msgLo msgHi nonceCell pkCell (cCell 1) idxCell (cCell 11)).RelB B v :=
  hp.pro _ (prefixCode_mem T (i:=14) (by decide : 14 < 16))

end Path
end
end OptimalOTS.AffineVM
