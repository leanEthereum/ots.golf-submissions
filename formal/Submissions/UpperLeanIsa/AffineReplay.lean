import Submissions.UpperLeanIsa.AffinePath

/-! A path whose cell relations hold yields an actual fixed-oracle execution.
This is the converse direction needed for the honest memory witness. -/

namespace OptimalOTS.AffineVM

open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.HLG3 (HashTable fixed_hash)
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sim_straight {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (M : MemImage κ)
    (T : Tab) (f : HashTable) (hd : LengthDomain (Lx M)) (pc q : K) (hq : q ≠ 0)
    (ci : CInstr) (hb : ci.Bounded) (hs : ci.straight = true)
    (hinit : ci = .init → q = 1 ∧ InitConstants T (Lx M)) (hR : ci.Rel f (Lx M)) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.execute M ⟨pc,q⟩ (compile q ci)) =
      pure (some ⟨g*pc,q⟩) := by
  cases ci with
  | init =>
    obtain ⟨rfl,hp⟩ := hinit rfl
    change Lx M oneCell = oneV ∧ Lx M lenCell = OptimalOTS.HLG3.natV 5504 at hR
    rw [exec_init h16 hκ M pc T hd hp,if_pos hR,simulateQ_pure]
  | xor a b c =>
    change Lx M c = Lx M a+Lx M b at hR
    rw [exec_xor h16 hκ M pc q hq hb,if_pos hR,simulateQ_pure]
  | mul a b c =>
    change Lx M c = Lx M a*Lx M b at hR
    rw [exec_mul h16 hκ M pc q hq hb,if_pos hR,simulateQ_pure]
  | setc a v =>
    change Lx M a = v at hR
    rw [exec_setc h16 hκ M pc q hq hb,if_pos hR,simulateQ_pure]
  | blake m0 m1 m2 m3 cv out md =>
    rw [exec_blake h16 hκ M pc q hq hb,simulateQ_bind,fixed_hash,pure_bind,simulateQ_pure]
    exact congrArg pure (if_pos hR)
  | _ => simp [CInstr.straight] at hs

theorem sim_list {κ : ℕ} (T : Tab) (M : MemImage κ) (f : HashTable)
    (q : K) {l : List CInstr} {t : ℕ}
    (hl : ∀ i (hi : i < l.length) (s : AffineFrames.Slot), s.val = t+i →
      instrAt T s = compile q l[i])
    (hst : ∀ ci ∈ l, ci.straight = true)
    (hbridge : ∀ ci ∈ l, ∀ pc,
      simulateQ (unifFwdAnswerImpl f) (LeanIsa.execute M ⟨pc,q⟩ (compile q ci)) =
        pure (some ⟨g*pc,q⟩))
    (hta : t+l.length ≤ sentinel) {n c : ℕ}
    (h : simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) M n ⟨gpow (t+l.length),q⟩) = pure (some c)) :
    simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) M (n+l.length) ⟨gpow t,q⟩) = pure (some (lcost l+c)) := by
  induction l generalizing t with
  | nil => simpa only [List.length_nil,Nat.add_zero,lcost_nil,Nat.zero_add] using h
  | cons ci l ih =>
    have ht : t < sentinel := by simp only [List.length_cons] at hta; omega
    let s : AffineFrames.Slot := ⟨t,by unfold sentinel at ht; omega⟩
    have h0 : instrAt T s = compile q ci := hl 0 (by simp) s (by simp [s])
    have hsci := hst ci List.mem_cons_self
    have hl' : ∀ i (hi : i < l.length) (s : AffineFrames.Slot),
        s.val = t+1+i → instrAt T s = compile q l[i] := by
      intro i hi s hs
      exact hl (i+1) (by simp; omega) s (by omega)
    have hw := ih hl' (fun y hy => hst y (List.mem_cons_of_mem _ hy))
      (fun y hy => hbridge y (List.mem_cons_of_mem _ hy))
      (by simp only [List.length_cons] at hta; omega) (by
        rwa [show t+1+l.length = t+(ci::l).length by simp only [List.length_cons]; omega])
    rw [List.length_cons,show n+(l.length+1) = (n+l.length)+1 by omega,
      runCost_slot T M (n+l.length) s ht q,h0,simulateQ_bind,
      hbridge ci List.mem_cons_self _,pure_bind,Option.elim_some,
      simulateQ_map,g_mul_gpow,hw,map_pure,Option.map_some,
      compile_straight_weight q ci hsci,lcost_cons]
    congr 2
    omega

/-- The complete path can be assembled backwards from the sentinel. -/
theorem sim_of_path {κ : ℕ} {T : Tab} (hT : T.Hyp) (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (f : HashTable) {xs : ℕ → ℕ} (hV : Valid xs)
    (hP : PathFacts T (oracleRel f) (Lx M) xs) (hL : Landing (Lx M) xs)
    (hF : ∀ j < 14, Lx M (h1Cell j) = ofK (blockFrame T j (xs j))) :
    ∃ n c, simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) M n ⟨gpow 0,1⟩) = pure (some c) := by
  have hOne := pro_one hP.pro
  have hd : LengthDomain (Lx M) := lengthDomain_exact (pro_length hP.pro)
  have hp : InitConstants T (Lx M) := fun c hc hc4 => pro_c hP.pro (by omega)
  have hexit : ∃ n c, simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) M n ⟨gpow (ctlSlot T xs 14),ctlFrame T xs 14⟩) = pure (some c) := by
    obtain ⟨hlt,hq,hcode⟩ := ctl_geometry hT xs (f:=14) le_rfl (fun j hj => hV j hj)
    let s : AffineFrames.Slot := ⟨ctlSlot T xs 14,by unfold sentinel at hlt; omega⟩
    have hci : instrAt T s = compile (ctlFrame T xs 14) .exit := by
      rw [hcode s rfl,if_neg (by decide : ¬14 < 14)]
    have hz : LeanIsa.runCost (program T) M 0 ⟨gpow sentinel,1⟩ = pure (some 0) := by
      rw [LeanIsa.runCost.eq_1,if_pos ⟨(finalPc_eq T).symm,rfl⟩]
    have hx : IsInK (Lx M (gpCell 13)) := hP.exit
    refine ⟨1,1,?_⟩
    rw [runCost_slot T M 0 s hlt _,hci,exec_exit h16 hκ M _ _ hq hOne,if_pos hx,
      pure_bind,Option.elim_some,hP.gp13,limb_ofK_zero,hz,map_pure,simulateQ_pure]
    rfl
  have key : ∀ d ≤ 14, ∃ n c, simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) M n ⟨gpow (ctlSlot T xs (14-d)),ctlFrame T xs (14-d)⟩) = pure (some c) := by
    intro d
    induction d with
    | zero => intro hd; simpa only [Nat.sub_zero] using hexit
    | succ d ih =>
      intro hd'
      obtain ⟨n,c,hw⟩ := ih (by omega)
      let j := 14-(d+1)
      have hj : j < 14 := by omega
      have hnext : 14-d = j+1 := by omega
      rw [hnext,ctlSlot_succ,ctlFrame_succ] at hw
      have hb := sim_list T M f (blockFrame T j (xs j))
        (l:=bodyCode T (base T) j (xs j)) (t:=ent j (xs j))
        (fun i hi s hs => by rw [instrAt_body hT hj (hV j hj) (by omega) s hs,
          raw_bodyCode T (base T) hi,List.getD_eq_getElem _ _ hi])
        (bodyCode_straight T _ j (xs j))
        (fun ci hci pc => sim_straight h16 hκ M T f hd pc _ (blockFrame_ne_zero T hj (hV j hj)) ci
          (bodyCode_bounded hT _ hj (hV j hj) ci hci) (bodyCode_straight T _ j (xs j) ci hci)
          (fun he => (bodyCode_ne_init T _ j (xs j) ci hci he).elim) (hP.blk j hj ci hci))
        (le_of_lt (bodyCode_slot_lt hT (base T) hj (hV j hj) le_rfl)) hw
      obtain ⟨hlt,hq,hcode⟩ := ctl_geometry hT xs (f:=j) (by omega) (fun k hk => hV k (by omega))
      let s : AffineFrames.Slot := ⟨ctlSlot T xs j,by unfold sentinel at hlt; omega⟩
      have hci : instrAt T s = compile (ctlFrame T xs j) (.dispatch j) := by
        rw [hcode s rfl,if_pos hj]
      have hH : Lx M (hCell j) = ofK (gpow (ent j (xs j))) := hL j hj
      have hK : IsInK (Lx M (hCell j)) ∧ IsInK (Lx M (h1Cell j)) :=
        ⟨(hP.disp j hj).1,(hP.disp j hj).2.1⟩
      refine ⟨n+(bodyCode T (base T) j (xs j)).length+1,1+lcost (bodyCode T (base T) j (xs j))+c,?_⟩
      rw [runCost_slot T M _ s hlt _,hci,exec_dispatch h16 hκ M _ _ hq hj hOne,if_pos hK,
        pure_bind,Option.elim_some,hH,hF j hj,limb_ofK_zero,limb_ofK_zero,simulateQ_map,hb,map_pure]
      change pure (some (1+(lcost (bodyCode T (base T) j (xs j))+c))) =
        pure (some (1+lcost (bodyCode T (base T) j (xs j))+c))
      rw [Nat.add_assoc]
  obtain ⟨n,c,hw⟩ := key 14 le_rfl
  change simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost (program T) M n ⟨gpow 16,1⟩) = pure (some c) at hw
  have hrun := sim_list T M f 1 (l:=prefixCode T 16) (t:=0)
    (fun i hi s hs => by
      rw [prefixCode_get T hi]
      rw [prefixCode_length] at hi
      have he : s.val = i := by omega
      rw [instrAt_initial T s (by omega),he])
    (fun ci hci => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
      exact raw_initial_straight T _ (List.mem_range.mp hi))
    (fun ci hci pc => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
      have hi' := List.mem_range.mp hi
      exact sim_straight h16 hκ M T f hd pc 1 one_ne_zero _ (raw_initial_facts T _ (by omega)).1
        (raw_initial_straight T _ hi') (fun _ => ⟨rfl,hp⟩)
        (hP.pro _ (prefixCode_mem T hi')))
    (by rw [prefixCode_length]; decide) (by simpa only [prefixCode_length,Nat.zero_add] using hw)
  exact ⟨_,_,hrun⟩

end
end OptimalOTS.AffineVM
