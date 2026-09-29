import Submissions.UpperLeanIsa.FreeLastHonestPath

/-! Honest execution, faithfulness, and the complete 1089-cycle certificate. -/
namespace OptimalOTS.FreeLastVM
open LeanerVM.Parameters LeanerVM.Semantics OracleComp OptimalOTS.HLFour
open OptimalOTS.HLG3 (fixed_hash)
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.FreeLastProgram (compile)
open OptimalOTS.FreeLastLayout
noncomputable section
open scoped Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sim_straight {κ : ℕ} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (M : MemImage κ)
    (f : HashTable) (hd : LengthDomain (Lx M)) (pc q : K) (hq : q ≠ 0)
    (ci : CInstr) (hb : ci.Bounded) (hs : ci.straight = true)
    (hinit : ci = .init → q = 1 ∧ InitConstants (Lx M)) (hR : ci.Rel f (Lx M)) :
    simulateQ (unifFwdAnswerImpl f) (LeanIsa.execute M ⟨pc,q⟩ (compile q ci)) =
      pure (some ⟨g*pc,q⟩) := by
  cases ci with
  | init =>
    obtain ⟨rfl,hp⟩ := hinit rfl
    change Lx M oneCell = oneV ∧ Lx M lenCell = OptimalOTS.HLG3.natV 5504 at hR
    rw [exec_init h16 hκ M pc hd hp,if_pos hR,simulateQ_pure]
  | xor a b c =>
    change Lx M c = Lx M a+Lx M b at hR
    rw [show compile q (.xor a b c) = AffineVM.compile q (.xor a b c) from rfl,AffineVM.exec_xor h16 hκ M pc q hq hb,if_pos hR,simulateQ_pure]
  | mul a b c =>
    change Lx M c = Lx M a*Lx M b at hR
    rw [show compile q (.mul a b c) = AffineVM.compile q (.mul a b c) from rfl,AffineVM.exec_mul h16 hκ M pc q hq hb,if_pos hR,simulateQ_pure]
  | setc a v =>
    change Lx M a = v at hR
    rw [show compile q (.setc a v) = AffineVM.compile q (.setc a v) from rfl,AffineVM.exec_setc h16 hκ M pc q hq hb,if_pos hR,simulateQ_pure]
  | blake m0 m1 m2 m3 cv out md =>
    rw [show compile q (.blake m0 m1 m2 m3 cv out md) = AffineVM.compile q (.blake m0 m1 m2 m3 cv out md) from rfl,AffineVM.exec_blake h16 hκ M pc q hq hb,simulateQ_bind,fixed_hash,pure_bind,simulateQ_pure]
    exact congrArg pure (if_pos hR)
  | _ => simp [CInstr.straight] at hs

theorem sim_list {κ : ℕ} (M : MemImage κ) (f : HashTable)
    (q : K) {l : List CInstr} {t : ℕ}
    (hl : ∀ i (hi : i < l.length) (s : AffineFrames.Slot), s.val = t+i →
      FreeLastProgram.instruction FreeLastBase.base s.val = compile q l[i])
    (hst : ∀ ci ∈ l, ci.straight = true)
    (hbridge : ∀ ci ∈ l, ∀ pc,
      simulateQ (unifFwdAnswerImpl f) (LeanIsa.execute M ⟨pc,q⟩ (compile q ci)) =
        pure (some ⟨g*pc,q⟩))
    (hta : t+l.length ≤ sentinel) {n c : ℕ}
    (h : simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost FreeLastBase.program M n ⟨gpow (t+l.length),q⟩) = pure (some c)) :
    simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost FreeLastBase.program M (n+l.length) ⟨gpow t,q⟩) = pure (some (lcost l+c)) := by
  induction l generalizing t with
  | nil => simpa only [List.length_nil,Nat.add_zero,lcost_nil,Nat.zero_add] using h
  | cons ci l ih =>
    have ht : t < sentinel := by simp only [List.length_cons] at hta; omega
    let s : AffineFrames.Slot := ⟨t,by unfold sentinel at ht; omega⟩
    have h0 : FreeLastProgram.instruction FreeLastBase.base s.val = compile q ci := hl 0 (by simp) s (by simp [s])
    have hsci := hst ci List.mem_cons_self
    have hl' : ∀ i (hi : i < l.length) (s : AffineFrames.Slot),
        s.val = t+1+i → FreeLastProgram.instruction FreeLastBase.base s.val = compile q l[i] := by
      intro i hi s hs
      exact hl (i+1) (by simp; omega) s (by omega)
    have hw := ih hl' (fun y hy => hst y (List.mem_cons_of_mem _ hy))
      (fun y hy => hbridge y (List.mem_cons_of_mem _ hy))
      (by simp only [List.length_cons] at hta; omega) (by
        rwa [show t+1+l.length = t+(ci::l).length by simp only [List.length_cons]; omega])
    rw [List.length_cons,show n+(l.length+1) = (n+l.length)+1 by omega,
      runCost_slot M (n+l.length) s ht q,h0,simulateQ_bind,
      hbridge ci List.mem_cons_self _,pure_bind,Option.elim_some,
      simulateQ_map,g_mul_gpow,hw,map_pure,Option.map_some,
      FreeLastProgram.compile_weight q hsci,lcost_cons]
    congr 2
    omega


def Completes {κ : Nat} (M : MemImage κ) (f : HashTable) (r : Regs K) : Prop :=
  ∃ n c, simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost FreeLastBase.program M n r) = pure (some c)

theorem sim_halt {κ : Nat} (M : MemImage κ) (f : HashTable) : Completes M f ⟨gpow sentinel,1⟩ := by
  refine ⟨0,0,?_⟩
  rw [LeanIsa.runCost.eq_1,if_pos ⟨finalPc_eq.symm,rfl⟩,simulateQ_pure]

theorem sim_jump {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32) (M : MemImage κ) (f : HashTable)
    {s t a : Nat} (hs : s < sentinel) (ht : t < 2^16) (ha : a < 2^16)
    (q : K) (hq : q ≠ 0)
    (hci : FreeLastProgram.instruction FreeLastBase.base s = FreeLastProgram.jump q t a)
    (hOne : Lx M oneCell = oneV) (hK : IsInK (Lx M t) ∧ IsInK (Lx M a))
    (h : Completes M f ⟨(Lx M t).limb 0,(Lx M a).limb 0⟩) : Completes M f ⟨gpow s,q⟩ := by
  obtain ⟨n,c,h⟩ := h
  refine ⟨n+1,1+c,?_⟩
  rw [runCost_slot M n ⟨s,by unfold sentinel at hs; omega⟩ hs q,hci,
    exec_jump h16 hκ M _ q hq ht ha hOne,if_pos hK,pure_bind,Option.elim_some,
    simulateQ_map,h,map_pure]
  rfl

theorem sim_body {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (f : HashTable) (hd : LengthDomain (Lx M))
    {e : Nat} (he : 27 ≤ e) (hehi : e < sentinel)
    (hentry : (candidateTree.lookup e).entry = e) (hnt : (candidateTree.lookup e).body ≠ .trap)
    (hB : ∀ ci ∈ FreeLastProgram.body (candidateTree.lookup e), ci.Rel f (Lx M))
    (h : Completes M f ⟨gpow (e+(FreeLastProgram.body (candidateTree.lookup e)).length),
      FreeLastProgram.frame FreeLastBase.base (candidateTree.lookup e)⟩) :
    Completes M f ⟨gpow e,FreeLastProgram.frame FreeLastBase.base (candidateTree.lookup e)⟩ := by
  obtain ⟨n,c,h⟩ := h
  have hg := (candidate_lookup_good he hehi).1
  have hf := FreeLastProgram.body_fits hg
  have hb := FreeLastDecode.lookup_bounds he hehi
  have hq : FreeLastProgram.frame FreeLastBase.base (candidateTree.lookup e) ≠ 0 := by
    cases hh : (candidateTree.lookup e).body with
    | trap => exact (hnt hh).elim
    | group u v z => exact FreeLastBase.group_frame_nonzero he hehi hh
    | free k => exact FreeLastBase.free_frame_nonzero he hehi hh
  refine ⟨_,_,sim_list M f _ ?_ (fun _ => FreeLastProgram.body_straight _) ?_ ?_ h⟩
  · intro i hi s hs
    have hh := FreeLastDecode.instruction_body FreeLastBase.base he hehi hi
    rw [hentry,List.getD_eq_getElem _ _ hi] at hh
    simpa only [hs] using hh
  · intro ci hci pc
    exact sim_straight h16 hκ M f hd pc _ hq ci
      (FreeLastDecode.body_bounded hg hci) (FreeLastProgram.body_straight _ hci)
      (fun he => (body_ne_init _ (he ▸ hci)).elim) (hB ci hci)
  · unfold sentinel
    omega

theorem sim_group {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (f : HashTable) (hd : LengthDomain (Lx M))
    {u v : Nat} {z : Bool} (hu : u < 13) (hh : Hint (Lx M) u)
    (hl : GroupLanding (Lx M) u v z)
    (hB : ∀ ci ∈ groupBody u v z, ci.Rel f (Lx M))
    (hOne : Lx M oneCell = oneV)
    (hK : IsInK (Lx M (nextTarget u z)) ∧ IsInK (Lx M (nextFrame u z)))
    (h : Completes M f (afterRegs (Lx M) u z)) : Completes M f (groupRegs (Lx M) u) := by
  obtain ⟨e,he,hehi,hH,hbody,hentry⟩ := hl
  have het : (Lx M (hCell (u+1))).limb 0 = gpow e := by rw [hH,limb_ofK_zero]
  have hq := (hint_incoming hh het).trans (stage_frame hu hbody hentry)
  have hg := (candidate_lookup_good he hehi).1
  have hf := FreeLastProgram.body_fits hg
  have hb := FreeLastDecode.lookup_bounds he hehi
  have hcslot : e+(FreeLastProgram.body (candidateTree.lookup e)).length < sentinel := by
    unfold sentinel; omega
  have hqne := FreeLastBase.group_frame_nonzero he hehi hbody
  have hn : FreeLastBlocks.nextGroup u < 13 := by unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
  have ht : nextTarget u z < 2^16 := by
    unfold nextTarget
    split_ifs <;> simp only [FreeLastBlocks.exitCell,hCell] <;> omega
  have ha : nextFrame u z < 2^16 := by
    unfold nextFrame
    split_ifs <;> simp only [oneCell,h1Cell] <;> omega
  have hci : FreeLastProgram.instruction FreeLastBase.base (e+(FreeLastProgram.body (candidateTree.lookup e)).length) =
      FreeLastProgram.jump (FreeLastProgram.frame FreeLastBase.base (candidateTree.lookup e)) (nextTarget u z) (nextFrame u z) := by
    have ht := FreeLastDecode.instruction_control FreeLastBase.base he hehi
    rw [hentry] at ht
    rw [ht]
    simp only [FreeLastProgram.control,hbody,nextTarget,nextFrame]
    split_ifs <;> rfl
  have hend := sim_jump h16 hκ M f hcslot ht ha _ hqne hci hOne hK h
  have hnt : (candidateTree.lookup e).body ≠ .trap := by rw [hbody]; intro h; cases h
  have hbr : ∀ ci ∈ FreeLastProgram.body (candidateTree.lookup e), ci.Rel f (Lx M) := by
    simpa only [FreeLastProgram.body,hbody,groupBody] using hB
  have hr := sim_body h16 hκ M f hd he hehi hentry hnt hbr hend
  simpa only [groupRegs,het,hq] using hr

theorem sim_free {κ : Nat} (h16 : 16 ≤ κ) (hκ : κ ≤ 32)
    (M : MemImage κ) (f : HashTable) (hd : LengthDomain (Lx M))
    {e s : Nat} (he : FreeLastEntryCheck.Entry e (.free s))
    (hB : ∀ ci ∈ FreeLastBlocks.free s, ci.Rel f (Lx M))
    (hOne : Lx M oneCell = oneV) (hExit : Lx M FreeLastBlocks.exitCell = ofK (gpow sentinel)) :
    Completes M f ⟨gpow e,FreeLastProgram.frame FreeLastBase.base (candidateTree.lookup e)⟩ := by
  obtain ⟨he,hehi,hentry,hbody⟩ := he
  have hg := (candidate_lookup_good he hehi).1
  have hf := FreeLastProgram.body_fits hg
  have hb := FreeLastDecode.lookup_bounds he hehi
  have hcslot : e+(FreeLastProgram.body (candidateTree.lookup e)).length < sentinel := by
    unfold sentinel; omega
  have hqne := FreeLastBase.free_frame_nonzero he hehi hbody
  have hci : FreeLastProgram.instruction FreeLastBase.base (e+(FreeLastProgram.body (candidateTree.lookup e)).length) =
      FreeLastProgram.jump (FreeLastProgram.frame FreeLastBase.base (candidateTree.lookup e)) FreeLastBlocks.exitCell oneCell := by
    have ht := FreeLastDecode.instruction_control FreeLastBase.base he hehi
    rw [hentry] at ht
    rw [ht,FreeLastProgram.control,hbody]
  have hK : IsInK (Lx M FreeLastBlocks.exitCell) ∧ IsInK (Lx M oneCell) := by
    rw [hExit,hOne]
    exact ⟨isInK_ofK _,isInK_ofK _⟩
  have hhalt : Completes M f ⟨(Lx M FreeLastBlocks.exitCell).limb 0,(Lx M oneCell).limb 0⟩ := by
    rw [hExit,hOne,limb_ofK_zero,oneV,limb_ofK_zero]
    exact sim_halt M f
  have hend := sim_jump h16 hκ M f hcslot (by decide) (by decide) _ hqne hci hOne hK hhalt
  have hnt : (candidateTree.lookup e).body ≠ .trap := by rw [hbody]; intro h; cases h
  apply sim_body h16 hκ M f hd he hehi hentry hnt ?_ hend
  simpa only [FreeLastProgram.body,hbody] using hB

section Honest
variable {P : FourFusion.Params} {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
variable (hC : Compat P fusionTab) (hlen : bits.length = 5504)
  (hacc : P.codec.Accepted (effective (IF P f pk m bits)))
  (hroot : rootValue f P (topsOf f P (effective (IF P f pk m bits)) bits) = pk)

theorem hv_exit : hv P fusionTab f pk m bits FreeLastBlocks.exitCell = ofK (gpow sentinel) := by
  apply hv_c (by decide) (by decide)
  unfold hcell FreeLastBlocks.exitCell
  hsimp

theorem honest_hint {u : Nat} (hu : u < 13) : Hint (hv P fusionTab f pk m bits) u := by
  unfold Hint
  rw [hv_h1 (by omega),hv_h (by omega),← ofK_add]
  simp only [frameK,show u+1 ≠ 0 by omega,if_false,Nat.add_sub_cancel]

theorem honest_nextK {u : Nat} (hu : u < 13) (z : Bool) :
    IsInK (hv P fusionTab f pk m bits (nextTarget u z)) ∧
      IsInK (hv P fusionTab f pk m bits (nextFrame u z)) := by
  have hn : FreeLastBlocks.nextGroup u < 13 := by unfold FreeLastBlocks.nextGroup; split_ifs <;> omega
  cases z with
  | true =>
    simp only [nextTarget,nextFrame,if_true,hv_exit,hv_one]
    exact ⟨isInK_ofK _,isInK_ofK _⟩
  | false =>
    simp only [nextTarget,nextFrame,Bool.false_eq_true,if_false]
    split_ifs <;> rw [hv_h (by omega),hv_h1 (by omega)] <;>
      exact ⟨isInK_ofK _,isInK_ofK _⟩

include hC hlen hacc in
theorem honest_group_completes {u : Nat} (hu : u < 13)
    (h : Completes (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) f
      (afterRegs (hv P fusionTab f pk m bits) u
        (if u = 1 then decide (XF P fusionTab f pk m bits 0 = 0) else false))) :
    Completes (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) f
      (groupRegs (hv P fusionTab f pk m bits) u) := by
  apply sim_group (le_refl 16) (by decide) _ f
    (lengthDomain_load (le_refl 16) pk m bits _) hu (honest_hint hu)
    (honest_landing hC hacc hu) ?_ hv_one (honest_nextK hu _) h
  intro ci hci
  apply honest_blocks hC hlen hacc hu ci
  by_cases h1 : u = 1
  · subst u
    cases hz : decide (XF P fusionTab f pk m bits 0 = 0) <;>
      simpa only [FreeLastBlocks.chosen,groupBody,hz,if_true,Bool.false_eq_true,and_false,and_true,
        if_false] using hci
  · simpa only [FreeLastBlocks.chosen,groupBody,if_neg h1,h1,false_and,if_false,Bool.false_eq_true] using hci

include hC hlen hacc in
theorem honest_free_completes (hs : 1 ≤ XF P fusionTab f pk m bits 0) :
    Completes (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) f
      ⟨(hv P fusionTab f pk m bits (hCell 0)).limb 0,
        (hv P fusionTab f pk m bits (h1Cell 0)).limb 0⟩ := by
  have hslt : XF P fusionTab f pk m bits 0 < 64 := by
    simpa only [XF] using hxs_zero_lt fusionTab (IF P f pk m bits)
  have he := FreeLastEntries.free_entry hs (by omega)
  have hr := sim_free (le_refl 16) (by decide)
    (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) f
    (lengthDomain_load (le_refl 16) pk m bits _) he (honest_free hC hlen hacc) hv_one hv_exit
  rw [hv_h (by decide),hv_h1 (by decide),limb_ofK_zero,limb_ofK_zero]
  have hek : entryK fusionTab (IF P f pk m bits) 0 = FreeLastEntries.freeEntry (XF P fusionTab f pk m bits 0) := by
    have hs0 : hxs fusionTab (IF P f pk m bits) 0 ≠ 0 := by
      simpa only [XF] using (show XF P fusionTab f pk m bits 0 ≠ 0 by omega)
    simp only [entryK,if_true,if_neg hs0,XF]
  have hfr : FreeLastProgram.frame FreeLastBase.base
      (candidateTree.lookup (FreeLastEntries.freeEntry (XF P fusionTab f pk m bits 0))) =
      frameK fusionTab (IF P f pk m bits) 0 := by
    rw [FreeLastProgram.frame,he.2.2.1,he.2.2.2,frameK,hek,if_pos rfl,
      zpow_neg,zpow_natCast]
  rwa [hek,← hfr]

include hC hlen hacc in
theorem honest_groups_complete :
    Completes (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) f
      (groupRegs (hv P fusionTab f pk m bits) 0) := by
  have hlast : Completes (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) f
      (groupRegs (hv P fusionTab f pk m bits) 1) := by
    apply honest_group_completes hC hlen hacc (by decide : 1 < 13)
    simp only [if_true]
    by_cases hs : XF P fusionTab f pk m bits 0 = 0
    · simp only [hs,decide_true,afterRegs,nextTarget,nextFrame,if_true,
        hv_exit,hv_one,oneV,limb_ofK_zero]
      exact sim_halt _ f
    · simp only [hs,decide_false,afterRegs,nextTarget,nextFrame,Bool.false_eq_true,if_false,if_true]
      exact honest_free_completes hC hlen hacc (by omega)
  have hall : ∀ d ≤ 12, Completes (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) f
      (groupRegs (hv P fusionTab f pk m bits) (unit (12-d))) := by
    intro d
    induction d with
    | zero => intro _; exact hlast
    | succ d ih =>
      intro hd
      apply honest_group_completes hC hlen hacc (unit_lt (by omega))
      rw [if_neg (unit_ne_one (by omega)),after_normal (unit_ne_one (by omega)),unit_next (by omega)]
      rw [show 12-(d+1)+1 = 12-d by omega]
      exact ih (by omega)
  exact hall 12 (by decide)

include hC hlen hacc hroot in
theorem honest_completes :
    Completes (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) f ⟨gpow 0,1⟩ := by
  let M := LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)
  have hd := lengthDomain_load (le_refl 16) pk m bits (imageF P fusionTab f pk m bits)
  have hci : FreeLastProgram.instruction FreeLastBase.base 16 =
      FreeLastProgram.jump 1 (hCell 1) (h1Cell 1) := by
    simp only [FreeLastProgram.instruction,show 16 < 27 by decide,if_true,
      FreeLastProgram.initial,show (FreeLastBlocks.prologue FreeLastBase.base).length = 16 from rfl,
      Nat.lt_irrefl,if_false]
  have hK : IsInK (Lx M (hCell 1)) ∧ IsInK (Lx M (h1Cell 1)) := by
    change IsInK (hv P fusionTab f pk m bits (hCell 1)) ∧ IsInK (hv P fusionTab f pk m bits (h1Cell 1))
    rw [hv_h (by decide),hv_h1 (by decide)]
    exact ⟨isInK_ofK _,isInK_ofK _⟩
  obtain ⟨n,c,hr⟩ := sim_jump (le_refl 16) (by decide) M f (by decide) (by decide) (by decide)
    1 one_ne_zero hci hv_one hK (honest_groups_complete hC hlen hacc)
  have hpro := honest_pro fusionTab_hyp hC hlen hacc hroot
  refine ⟨n+(prefixCode 16).length,lcost (prefixCode 16)+c,
    sim_list M f 1 (l:=prefixCode 16) (t:=0) (n:=n) (c:=c) ?_ ?_ ?_ ?_ ?_⟩
  · intro i hi s hs
    rw [prefixCode_get hi]
    rw [prefixCode_length] at hi
    have he : s.val = i := by omega
    rw [instrAt_initial s (by omega),he]
  · intro ci hci
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
    exact raw_initial_straight _ (List.mem_range.mp hi)
  · intro ci hci pc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
    have hi16 := List.mem_range.mp hi
    apply sim_straight (le_refl 16) (by decide) M f hd pc 1 one_ne_zero _
      (raw_initial_facts _ hi16).1 (raw_initial_straight _ hi16) ?_
      (hpro _ (prefixCode_mem hi16))
    intro _
    refine ⟨rfl,?_⟩
    intro j hj hj4
    exact hv_cc (by omega)
  · rw [prefixCode_length]; decide
  · simpa only [prefixCode_length,Nat.zero_add] using hr

include hC hlen hacc hroot in
/-- An accepted signature's honest image executes exactly 186 instructions. -/
theorem honest_run : simulateQ (unifFwdAnswerImpl f)
    (LeanIsa.runCost FreeLastBase.program (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits))
      186 Regs.initial) = pure (some 969) := by
  obtain ⟨n,c,he⟩ := honest_completes hC hlen hacc hroot
  have hm : some c ∈ (simSem f).S (LeanIsa.runCost FreeLastBase.program
      (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) n ⟨gpow 0,1⟩) := by
    change some c ∈ support (simulateQ (unifFwdAnswerImpl f) _)
    rw [he,mem_support_pure_iff]
  obtain ⟨hn,hc⟩ := run_exact (le_refl 16) (by decide)
    (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) (simSem f) (oracleRel f)
    (AffineVM.hashSound_sim f) (lengthDomain_load (le_refl 16) pk m bits _) hm
  rw [hn,hc] at he
  rw [initial_eq]
  exact he

end Honest

open OptimalOTS.HLG3 (probTrue_zero_of_fixed)

theorem effective_idxOf (y : BitVec 256) : effective (idxOf y) = indexSlice y := by
  simp only [effective,idxOf,unmask_remask,indexSlice,PartialHints.effectiveIndex]

/-- The machine half of the submission. -/
def machineSubmission (P : FourFusion.Params) : LeanIsa.Submission where
  scheme := P.scheme
  program := FreeLastBase.program
  memLog := 16
  prover := prover P fusionTab
  steps := fun _ _ _ => 186

variable {P : FourFusion.Params}

open scoped Classical in
theorem decision_false {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
    (h : ¬ (bits.length = sigBits ∧ P.codec.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk)) :
    P.verifyValue f pk m bits = false := by
  unfold FourFusion.Params.verifyValue
  by_cases hl : bits.length = sigBits
  · rw [if_neg (not_not.mpr hl)]
    by_cases ha : P.codec.Accepted (idxValue f P m (decodeNonce bits) pk)
    · rw [if_neg (not_not.mpr ha)]
      have hne : rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) ≠ pk :=
        fun he => h ⟨hl,ha,he⟩
      simpa only [rootValue,topsOf,idxValue,beq_eq_false_iff_ne] using hne
    · rw [if_pos ha]
  · rw [if_pos hl]

set_option linter.constructorNameAsVariable false in
/-- **Faithful**: the honest prover's run completes exactly when the verifier accepts. -/
theorem faithful (hC : Compat P fusionTab) : (machineSubmission P).Faithful := by
  refine ⟨show minLogMem ≤ 16 by decide, show (16 : ℕ) ≤ maxLogMem by decide, ?_⟩
  intro pk m bits
  apply probTrue_zero_of_fixed
  intro f
  have hrun : simulateQ (unifFwdAnswerImpl f) ((machineSubmission P).honestRun pk m bits) =
      (fun o : Option ℕ => o.isSome) <$> simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost (FreeLastBase.program) (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) 186
          Regs.initial) := by
    show simulateQ _ (prover P fusionTab pk m bits >>= fun L => (fun o : Option ℕ => o.isSome) <$>
      LeanIsa.runCost (FreeLastBase.program) (LeanIsa.loadInput pk m bits L) 186 Regs.initial) = _
    rw [simulateQ_bind, fixed_prover, pure_bind, simulateQ_map]
  have hver : (machineSubmission P).scheme.verify pk m bits = P.verify pk m bits := rfl
  have hs := fun c => fixed_sound (P:=P) (n:=186) (c:=c) hC (le_refl 16) (by norm_num)
    f pk m bits (imageF P fusionTab f pk m bits)
  have hh : ∀ (h1 : bits.length = sigBits) (h2 : P.codec.Accepted (idxValue f P m (decodeNonce bits) pk))
      (h3 : rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk),
      simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost (FreeLastBase.program) (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) 186
          Regs.initial) = pure (some 969) :=
    fun h1 h2 h3 => honest_run hC h1
      (by simpa only [idxValue, Params.idxValue, IF, effective_idxOf, y0F, HLG3.ans] using h2)
      (by simpa only [idxValue, Params.idxValue, IF, effective_idxOf, y0F, HLG3.ans] using h3)
  rw [simulateQ_bind, hrun, hver]
  generalize simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost (FreeLastBase.program)
    (LeanIsa.loadInput pk m bits (imageF P fusionTab f pk m bits)) 186 Regs.initial) = X at hs hh ⊢
  simp only [simulateQ_bind, simulateQ_pure, FourFusion.Params.fixed_verify, pure_bind]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨b, hb, hmem⟩ := hmem
  rw [mem_support_pure_iff] at hmem
  rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hb
  obtain ⟨o, ho, hb⟩ := hb
  rw [Function.comp_apply, mem_support_pure_iff] at hb
  subst hb
  by_cases hacc : bits.length = sigBits ∧ P.codec.Accepted (idxValue f P m (decodeNonce bits) pk) ∧
      rootValue f P (topsOf f P (idxValue f P m (decodeNonce bits) pk) bits) = pk
  · rw [hh hacc.1 hacc.2.1 hacc.2.2, mem_support_pure_iff] at ho
    subst ho
    rw [decision_true hacc] at hmem
    simp at hmem
  · cases o with
    | none =>
      rw [decision_false hacc] at hmem
      simp at hmem
    | some c => exact hacc (hs c ho)

/-- **Sound** for the machine submission. -/
theorem machine_sound (hC : Compat P fusionTab) : (machineSubmission P).Sound :=
  sound hC (machineSubmission P) rfl rfl

/-- **Cycles** for the machine submission: every completing run costs `1089`. -/
theorem machine_cycles : (machineSubmission P).CyclesAtMost 1089 :=
  cycles (machineSubmission P) rfl

/-- **Valid** bytecode. -/
theorem machine_valid : LeanIsa.BytecodeValid (machineSubmission P).program := FreeLastProgram.valid FreeLastBase.base

/-- The seeded rows: `2 ^ 18 + 2 ^ 16 < 2 ^ 20`. -/
theorem machine_seededRows : (machineSubmission P).seededRows < LeanIsa.maxSeededRows :=
  FreeLastBase.seeded_rows


abbrev freeLastMachine : LeanIsa.Submission := machineSubmission FreeLastCodec.params

theorem freeLast_certificate : freeLastMachine.Certificate 1089 where
  admissible := FreeLastCodec.admissible
  secure := FreeLastCodec.secure
  valid := machine_valid
  faithful := faithful concrete_compat
  sound := machine_sound concrete_compat
  cycles := machine_cycles

theorem freeLast_seededRows : freeLastMachine.seededRows < LeanIsa.maxSeededRows :=
  machine_seededRows

end
end OptimalOTS.FreeLastVM
