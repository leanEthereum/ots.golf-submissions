import Submissions.UpperLeanIsa.AffineCost

/-! Exact block lookup and register frames for the affine program. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem free_bodyCode (T : Tab) (a : K) (x : ℕ) :
    bodyCode T a 0 x =
      .setc (gpCell 0) (ofK (seedProduct a x)) ::
        (chainOps topCell 0 x tfCell ++ [copy (if x = 0 then wCell 0 else tfCell) tfCell,
          .xor (hCell 1) (cCell 1) (h1Cell 1)]) := rfl

theorem chainOps_getD {readTop : ℕ → ℕ} {k x i dst : ℕ} (hi : i < x) :
    (chainOps readTop k x dst).getD i .pad = chainOp readTop k x i dst := by
  simp [chainOps,List.getD_eq_getElem?_getD,hi]

/-- The actual raw instruction is the instruction used by the costed body list. -/
theorem raw_bodyCode (T : Tab) (a : K) {f x i : ℕ}
    (hi : i < (bodyCode T a f x).length) :
    raw T a (.body f x i) = (bodyCode T a f x).getD i .pad := by
  by_cases hf : f = 0
  · subst f
    have hib : i < x+3 := by
      simpa only [bodyCode_length,bodyF_zero,fbody_len,Nat.add_comm] using hi
    rw [free_bodyCode]
    cases i with
    | zero => simp only [raw,ite_true,List.getD_cons_zero]
    | succ i =>
      rw [List.getD_cons_succ]
      by_cases hx : i < x
      · rw [List.getD_append _ _ _ _ (by rw [chainOps_length]; exact hx),chainOps_getD hx]
        simp only [raw,ite_true,if_neg (show i+1 ≠ 0 by omega),if_pos (show i+1 ≤ x by omega),
          Nat.add_sub_cancel]
      · rw [List.getD_append_right _ _ _ _ (by rw [chainOps_length]; omega),chainOps_length]
        have he : i = x ∨ i = x+1 := by omega
        rcases he with he | he
        · subst i
          simp only [Nat.sub_self,List.getD_cons_zero,raw,ite_true,
            if_neg (show x+1 ≠ 0 by omega),if_neg (show ¬x+1 ≤ x by omega)]
        · subst i
          have h1 : x+1-x = 1 := by omega
          have h2 : x+1+1 = x+2 := by omega
          simp only [h1,List.getD_cons_succ,List.getD_cons_zero,raw,ite_true,h2,
            if_neg (show x+2 ≠ 0 by omega),if_neg (show ¬x+2 ≤ x by omega),
            if_neg (show x+2 ≠ x+1 by omega)]
  · have hib : i < (body T (f-1) x false).length := by
      simpa only [bodyCode,if_neg hf,List.length_map] using hi
    rw [raw,if_neg hf,if_pos hib,bodyCode,if_neg hf]
    exact (List.getD_map _ .pad rehint).symm

/-- The first instruction after the straight body is its one control operation. -/
theorem raw_body_control (T : Tab) (a : K) (f x : ℕ) :
    raw T a (.body f x (bodyCode T a f x).length) = ctlOf f x := by
  by_cases hf : f = 0
  · subst f
    have hl : (bodyCode T a 0 x).length = x+3 := by
      rw [bodyCode_length,bodyF_zero,fbody_len]
      omega
    rw [hl]
    simp only [raw,ite_true,if_neg (show x+3 ≠ 0 by omega),
      if_neg (show ¬x+3 ≤ x by omega),if_neg (show x+3 ≠ x+1 by omega),
      if_neg (show x+3 ≠ x+2 by omega),ctlOf,frG0]
  · simp only [bodyCode,if_neg hf,List.length_map,raw,lt_self_iff_false,ite_false,ite_true]

theorem place_group {u x i : ℕ} (hu : u < 13) (hx : x < VF u) (hi : i < SL u x) :
    place (entryOf u x + i) = .body (u+1) x i := by
  have h1 := entryOf_ge hu hx
  have h2 := block_lt_gEnd hu hx hi
  unfold place
  rw [if_neg (by omega),if_pos h2,dec_entry hu hx hi]

theorem place_free {x i : ℕ} (hx : x < 64) (hi : i < 68) :
    place (entF x+i) = .body 0 x i := by
  unfold place entF
  rw [if_neg (by unfold baseF; omega),if_neg (by unfold baseF gEnd; omega),
    if_neg (by omega),if_pos (by omega),
    show (baseF + 68*x+i-baseF)/68 = x by omega,
    show (baseF + 68*x+i-baseF)%68 = i by omega]

theorem stageIndex_injective {f j : ℕ} (hf : f < 14) (hj : j < 14)
    (h : stageIndex f = stageIndex j) : f = j := by
  unfold stageIndex at h
  split_ifs at h <;> omega

theorem place_body_spec {s f x i : ℕ} (h : place s = .body f x i) :
    f < 14 ∧ x < Wf f ∧ s = ent f x+i := by
  unfold place at h
  split_ifs at h with hpro hgroup hgap hfree
  · cases h
    obtain ⟨hu,hx,hi,hs⟩ := dec_spec (by omega) hgroup
    refine ⟨by omega,?_,?_⟩
    · rwa [Wf_succ hu]
    · rwa [ent_succ hu]
  · cases h
    refine ⟨by decide,?_,?_⟩
    · rw [Wf_zero]
      omega
    · rw [ent_zero]
      unfold entF
      have he := Nat.div_add_mod (s-baseF) 68
      omega

/-- A descriptor matched by a fresh affine jump is an entry of the requested stage. -/
theorem matched_isEntry (T : Tab) {f : ℕ} (hf : f < 14) (s : AffineFrames.Slot)
    (d : AffineFrames.BodyDescriptor) (hd : layout T s = .body d)
    (hstage : d.stage.val = stageIndex f) (hentry : s.val = d.entry.val) : IsEntry f s.val := by
  obtain ⟨f',x,i,hp,hf',hstage',hentry'⟩ := body_descriptor T s d hd
  obtain ⟨_,hx,_⟩ := place_body_spec hp
  have he : f = f' := stageIndex_injective hf hf' (hstage.symm.trans hstage')
  subst f'
  exact ⟨hf,x,hx,hentry.trans hentry'⟩

theorem execute_nonentry {κ : ℕ} (hκ : κ ≤ 32) (M : MemImage κ) (T : Tab)
    {f : ℕ} (hf : f < 14) (s : AffineFrames.Slot) (hentry : ¬IsEntry f s.val) :
    LeanIsa.execute M ⟨gpow s.val,
      AffineFrames.frame (layout T) ⟨stageIndex f,stageIndex_lt hf⟩ s⟩ (instrAt T s) = pure none := by
  apply wrong_landing hκ M T
  intro d hd he
  exact hentry (matched_isEntry T hf s d hd
    (congrArg Fin.val he.1).symm (congrArg Fin.val he.2))

theorem biasCell_bound {c : ℕ} (hc : c < 2 ^ 16) : biasCell (c-h1Cell 0) < 2 ^ 16 := by
  unfold biasCell cCell h1Cell oneCell lenCell
  split_ifs <;> omega

theorem rehint_bounded {ci : CInstr} (h : ci.Bounded) : (rehint ci).Bounded := by
  cases ci <;> simp only [rehint] <;> try exact h
  split
  · exact ⟨h.1,biasCell_bound h.2.2,h.2.2⟩
  · exact h

theorem bodyCode_bounded {T : Tab} (hT : T.Hyp) (a : K) {f x : ℕ}
    (hf : f < 14) (hx : x < Wf f) : ∀ ci ∈ bodyCode T a f x, ci.Bounded := by
  intro ci hi
  by_cases hf0 : f = 0
  · subst f
    rw [Wf_zero] at hx
    rw [free_bodyCode] at hi
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | hi | rfl | rfl
    · change 200 < 2 ^ 16; decide
    · obtain ⟨t,ht,rfl⟩ := mem_chainOps.mp hi
      exact chainOp_bounded topCell_read_bound (by decide) ht (by omega) (by unfold tfCell; omega)
    · simp only [copy,CInstr.Bounded,wCell,tfCell,oneCell]
      split_ifs <;> omega
    · change 161 < 2 ^ 16 ∧ 105 < 2 ^ 16 ∧ 181 < 2 ^ 16
      decide
  · simp only [bodyCode,if_neg hf0,List.mem_map] at hi
    obtain ⟨ci',hi',rfl⟩ := hi
    apply rehint_bounded
    exact body_bounded hT (gOf_lt hf0 hf) (by simpa only [Wf,gOf,if_neg hf0] using hx) _ hi'

theorem bodyCode_place {T : Tab} (hT : T.Hyp) (a : K) {f x i : ℕ}
    (hf : f < 14) (hx : x < Wf f) (hi : i ≤ (bodyCode T a f x).length) :
    place (ent f x+i) = .body f x i := by
  rw [bodyCode_length] at hi
  by_cases hf0 : f = 0
  · subst f
    rw [Wf_zero] at hx
    rw [bodyF_zero,fbody_len] at hi
    rw [ent_zero]
    exact place_free hx (by omega)
  · obtain ⟨u,rfl⟩ : ∃ u, f = u+1 := ⟨f-1,by omega⟩
    have hu : u < 13 := by omega
    rw [Wf_succ hu] at hx
    rw [bodyF_succ T hu] at hi
    have hl := body_len_L (z:=false) hT hu hx
    rw [ent_succ hu]
    exact place_group hu hx (by omega)

theorem bodyCode_slot_lt {T : Tab} (hT : T.Hyp) (a : K) {f x i : ℕ}
    (hf : f < 14) (hx : x < Wf f) (hi : i ≤ (bodyCode T a f x).length) :
    ent f x+i < sentinel := by
  rw [bodyCode_length] at hi
  by_cases hf0 : f = 0
  · subst f
    rw [Wf_zero] at hx
    rw [bodyF_zero, fbody_len] at hi
    rw [ent_zero]
    unfold entF baseF sentinel
    omega
  · obtain ⟨u, rfl⟩ : ∃ u, f = u+1 := ⟨f-1, by omega⟩
    have hu : u < 13 := by omega
    rw [Wf_succ hu] at hx
    rw [bodyF_succ T hu] at hi
    have hl := body_len_L (z := false) hT hu hx
    have hb := block_lt_gEnd hu hx (show i < SL u x by omega)
    rw [ent_succ hu]
    unfold gEnd sentinel at *
    omega

def blockFrame (T : Tab) (f x : ℕ) : K :=
  AffineFrames.stageBias (base T) (stageIndex f) + gpow (ent f x)

theorem blockFrame_ne_zero (T : Tab) {f x : ℕ} (hf : f < 14) (hx : x < Wf f) :
    blockFrame T f x ≠ 0 := by
  have he : ent f x < 2 ^ 18 := by have := ent_lt hf hx; unfold sentinel at this; omega
  exact AffineFrames.frame_ne_zero (layout T) ⟨stageIndex f,stageIndex_lt hf⟩ ⟨ent f x,he⟩ (by
    intro hs
    change stageIndex f = 13 at hs
    have hf0 : f = 0 := by unfold stageIndex at hs; split_ifs at hs <;> omega
    subst f
    simp [ent,entF,baseF])

theorem ctlOf_bounded {f x : ℕ} (hf : f < 14) : (ctlOf f x).Bounded := by
  unfold ctlOf
  split
  · change 1 < 14; decide
  · exact ctlF_bounded (by unfold gOf; omega)

theorem ctlOf_ne_pad (f x : ℕ) : ctlOf f x ≠ .pad := by
  unfold ctlOf ctlF
  split_ifs <;> simp

theorem ctlOf_ne_entry (f x j : ℕ) : ctlOf f x ≠ .entry j := by
  unfold ctlOf ctlF
  split_ifs <;> simp

theorem raw_body_facts {T : Tab} (hT : T.Hyp) (a : K) {f x i : ℕ}
    (hf : f < 14) (hx : x < Wf f) (hi : i ≤ (bodyCode T a f x).length) :
    (raw T a (.body f x i)).Bounded ∧ raw T a (.body f x i) ≠ .pad ∧
      ∀ j, raw T a (.body f x i) ≠ .entry j := by
  by_cases hi' : i < (bodyCode T a f x).length
  · rw [raw_bodyCode T a hi']
    have hm : (bodyCode T a f x).getD i .pad ∈ bodyCode T a f x := by
      rw [List.getD_eq_getElem _ _ hi']
      exact List.getElem_mem _
    have hs := bodyCode_straight T a f x _ hm
    refine ⟨bodyCode_bounded hT a hf hx _ hm,?_,fun j => CInstr.ne_entry_of_straight hs j⟩
    intro he
    rw [he] at hs
    contradiction
  · have he : i = (bodyCode T a f x).length := by omega
    subst i
    rw [raw_body_control]
    exact ⟨ctlOf_bounded hf,ctlOf_ne_pad f x,ctlOf_ne_entry f x⟩

theorem layout_body_at {T : Tab} (hT : T.Hyp) {f x i : ℕ}
    (hf : f < 14) (hx : x < Wf f) (hi : i ≤ (bodyCode T 1 f x).length)
    (s : AffineFrames.Slot) (hs : s.val = ent f x+i) :
    ∃ d, layout T s = .body d ∧ d.stage.val = stageIndex f ∧ d.entry.val = ent f x := by
  have hp : place s.val = .body f x i := by rw [hs]; exact bodyCode_place hT 1 hf hx hi
  obtain ⟨hb,hn,he⟩ := raw_body_facts hT 1 hf hx hi
  have hc := CInstr.cell0_lt hb hn he
  have hnp : ¬isPad (raw T 1 (.body f x i)) = true := fun h => hn ((isPad_eq_true _).mp h)
  have hent : ent f x < 2 ^ 18 := by have := ent_lt hf hx; unfold sentinel at this; omega
  unfold layout
  rw [hp,if_neg hnp,dif_pos hc]
  dsimp only
  rw [dif_pos hf,dif_pos hent]
  exact ⟨_,rfl,rfl,rfl⟩

/-- All instructions in a block, including its control, use the same nonzero frame. -/
theorem instrAt_body {T : Tab} (hT : T.Hyp) {f x i : ℕ}
    (hf : f < 14) (hx : x < Wf f) (hi : i ≤ (bodyCode T (base T) f x).length)
    (s : AffineFrames.Slot) (hs : s.val = ent f x+i) :
    instrAt T s = compile (blockFrame T f x) (raw T (base T) (.body f x i)) := by
  have hi' : i ≤ (bodyCode T 1 f x).length := by
    simpa only [bodyCode_length] using hi
  obtain ⟨d,hd,hstage,hentry⟩ := layout_body_at hT hf hx hi' s hs
  have hp : place s.val = .body f x i := by rw [hs]; exact bodyCode_place hT (base T) hf hx hi
  simp only [instrAt,hd,hp]
  have he : AffineFrames.frame (layout T) d.stage d.entry = blockFrame T f x := by
    simp only [AffineFrames.frame,AffineFrames.bias,blockFrame,base,hstage,hentry]
  rw [he]

end
end OptimalOTS.AffineVM
