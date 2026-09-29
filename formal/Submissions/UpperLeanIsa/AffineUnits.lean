import Submissions.UpperLeanIsa.AffinePrefix

/-! One affine dispatch and its entire straight block, for either fixed-table
or cache-free semantics. No second entry jump is executed. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem chainOp_ne_init (readTop : ℕ → ℕ) (k d t dst : ℕ) : chainOp readTop k d t dst ≠ .init := by
  unfold chainOp
  split_ifs <;> intro h <;> cases h

theorem init_not_chainOps (readTop : ℕ → ℕ) (k d dst : ℕ) : CInstr.init ∉ chainOps readTop k d dst := by
  intro h
  obtain ⟨t,ht,he⟩ := mem_chainOps.mp h
  exact chainOp_ne_init readTop k d t dst he.symm

theorem rehint_eq_init (ci : CInstr) : rehint ci = .init ↔ ci = .init := by
  cases ci <;> simp only [rehint]
  split_ifs <;> simp

theorem init_not_body (T : Tab) (u x : ℕ) (z : Bool) : CInstr.init ∉ body T u x z := by
  intro hi
  unfold body at hi
  simp only [List.mem_append,List.mem_singleton,List.mem_replicate] at hi
  rcases hi with ((((hi | hi) | hi) | hi) | hi) | hi
  · unfold tie at hi
    split_ifs at hi <;> simp [copy] at hi
  · unfold prodOps prodOp at hi
    split_ifs at hi <;> simp [NOP] at hi
  · obtain ⟨i,hi,hseg⟩ := mem_segs.mp hi
    unfold seg at hseg
    split_ifs at hseg
    · simp [copy] at hseg
    · exact init_not_chainOps _ _ _ _ hseg
    · exact init_not_chainOps _ _ _ _ hseg
  · unfold rootIns at hi
    split_ifs at hi <;> simp at hi
  · cases hi.2
  · unfold nextOp at hi
    split_ifs at hi <;> cases hi

theorem bodyCode_ne_init (T : Tab) (a : K) (f x : ℕ) :
    ∀ ci ∈ bodyCode T a f x, ci ≠ .init := by
  intro ci hi he
  subst ci
  by_cases hf : f = 0
  · subst f
    rw [free_bodyCode] at hi
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hi
    rcases hi with hi | hi | hi | hi
    · cases hi
    · exact init_not_chainOps _ _ _ _ hi
    · cases hi
    · cases hi
  · simp only [bodyCode,if_neg hf,List.mem_map] at hi
    obtain ⟨ci,hi,he⟩ := hi
    rw [rehint_eq_init] at he
    subst ci
    exact init_not_body _ _ _ _ hi

def Hint (T : Tab) (v : ℕ → E) (f : ℕ) : Prop :=
  v (h1Cell f) = v (hCell f) + ofK (AffineFrames.stageBias (base T) (stageIndex f))

theorem run_dispatch {κ : ℕ} (T : Tab) (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel)
    (d : AffineFrames.Slot) (hd : d.val < sentinel) (q : K) (hq : q ≠ 0)
    {f : ℕ} (hf : f < 14) (hci : instrAt T d = compile q (.dispatch f))
    (hOne : Lx M oneCell = oneV) (hHint : Hint T (Lx M) f) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow d.val,q⟩)) :
    ∃ x < Wf f, Lx M (hCell f) = ofK (gpow (ent f x)) ∧
      (CInstr.dispatch f).RelB B (Lx M) ∧
      ∃ n' c', n = n'+1 ∧ c = 1+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (program T) M n'
          ⟨gpow (ent f x),blockFrame T f x⟩) := by
  cases n with
  | zero =>
    rw [runCost_zero_slot T M hd q] at h
    exact (Sm.some_not_pure_none h).elim
  | succ n =>
    rw [runCost_slot T M n d hd q,hci,exec_dispatch h16 hκ M _ q hq hf hOne,Sm.bind_iff] at h
    obtain ⟨r,hr,hc⟩ := h
    rw [Sm.pure_iff] at hr
    split_ifs at hr with hK
    · subst r
      rw [Option.elim_some,show LeanIsa.weight (compile q (.dispatch f)).opcode = 1 from rfl] at hc
      obtain ⟨c',hc',hw⟩ := Sm.some_map_add hc
      have hfp : (Lx M (h1Cell f)).limb 0 = incomingFrame T f ((Lx M (hCell f)).limb 0) := by
        rw [hHint,limb_add,limb_ofK_zero]
        exact add_comm _ _
      rw [hfp] at hw
      obtain ⟨x,hx,he⟩ := entry_of_completion hκ M T Sm hf hw
      refine ⟨x,hx,?_,⟨hK.1,hK.2,ent f x,⟨hf,x,hx,rfl⟩,he⟩,n,c',rfl,hc',?_⟩
      · rw [ofK_limb hK.1,he]
      · rw [he] at hw
        exact hw
    · subst r
      exact (Sm.some_not_pure_none hc).elim

theorem run_body {κ : ℕ} {T : Tab} (hT : T.Hyp) (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (Sm : Sem) (B : BlakeRel) (hHash : HashSound Sm B)
    (hd : LengthDomain (Lx M)) {f x : ℕ} (hf : f < 14) (hx : x < Wf f) {n c : ℕ}
    (h : some c ∈ Sm.S (LeanIsa.runCost (program T) M n ⟨gpow (ent f x),blockFrame T f x⟩)) :
    (∀ ci ∈ bodyCode T (base T) f x, ci.RelB B (Lx M)) ∧
      ∃ n' c', n = n'+(bodyCode T (base T) f x).length ∧
        c = lcost (bodyCode T (base T) f x)+c' ∧
        some c' ∈ Sm.S (LeanIsa.runCost (program T) M n'
          ⟨gpow (ent f x+(bodyCode T (base T) f x).length),blockFrame T f x⟩) := by
  apply run_list T M Sm B (blockFrame T f x)
  · intro i hi s hs
    rw [instrAt_body hT hf hx (by omega) s hs,raw_bodyCode T (base T) hi,
      List.getD_eq_getElem _ _ hi]
  · exact bodyCode_straight T _ f x
  · intro ci hci pc r hr
    exact straight_of_sem h16 hκ M T Sm B hHash hd pc _ (blockFrame_ne_zero T hf hx) ci
      (bodyCode_bounded hT _ hf hx ci hci) (bodyCode_straight T _ f x ci hci)
      (fun he => (bodyCode_ne_init T _ f x ci hci he).elim) r hr
  · exact le_of_lt (bodyCode_slot_lt hT (base T) hf hx le_rfl)
  · exact h

end
end OptimalOTS.AffineVM
