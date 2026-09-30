import Submissions.UpperLeanIsa.FreeLastHonest

namespace OptimalOTS.FreeLastVM
open OracleComp LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.HLG3 (natV ans natV_add_disjoint hi_append_lo inputWord_pk inputWord_len_of)
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput inputWord OracleCompressCells)
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {P : FourFusion.Params} {T : Tab} {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length = 5504)
  (hacc : P.codec.Accepted (effective (IF P f pk m bits)))
  (hroot : rootValue f P (topsOf f P (effective (IF P f pk m bits)) bits) = pk)

theorem hd_XF (k : Nat) : hd T (y0F P f pk m bits) k = dg T (XF P T f pk m bits) k := rfl

include hC hacc in
theorem XF_lt_W {u : Nat} (hu : u < 13) : XF P T f pk m bits (u+1) < VF u := by
  simp only [XF,hxs_succ]
  exact hlive hC hacc u hu

theorem honest_acc {u : Nat} (hu : u < 13) :
    hv P T f pk m bits (accCell u) =
      cellOfBits (FreeLastTie.accBits (fun w => XF P T f pk m bits (w+1)) u) := by
  by_cases h12 : u < 12
  · exact hv_accl h12
  · obtain rfl : u = 12 := by omega
    rw [show accCell 12 = idxCell from rfl,hv_idx]
    have hfun : (fun w => XF P T f pk m bits (w+1)) =
        fun w => digitW gb (PartialHints.decodeRaw ((y0F P f pk m bits).extractLsb' 0 128)).toNat w := by
      funext w
      simp only [XF,hxs_succ,field,IF,idxOf,unmask_remask]
    rw [hfun,FreeLastTie.acc_digits]
    rfl

include hT hC hlen hacc in
/-- **The honest chains of a group block.** -/
theorem honest_segs {u : ℕ} (hu : u < 13) :
    ∀ y ∈ segs T u (XF P T f pk m bits (u + 1)), y.Rel f (hv P T f pk m bits) := by
  intro y hy
  obtain ⟨i, hi, hy⟩ := mem_segs.mp hy
  have hk := chainOf_lt u hu i hi
  have hread := honest_groupRead_context hT hC hlen hacc ⟨chainOf u i,hk⟩
  have hunit := unitOf_chainOf u hu i hi
  dsimp only [Fin.val_mk] at hread
  rw [hunit] at hread
  have hdk : hd T (y0F P f pk m bits) (chainOf u i) = T u (XF P T f pk m bits (u + 1)) i := by
    rw [hd_XF, dg_chainOf T _ hu hi]
  unfold seg at hy
  rw [← hdk] at hy
  by_cases hx : copied u i
  · rw [if_pos hx] at hy
    have he : cvTop (chainOf u i) := cvTop_of_exported ((exported_iff u hu i hi).mpr hx)
    by_cases hd0 : hd T (y0F P f pk m bits) (chainOf u i) = 0
    · rw [if_pos hd0] at hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact honest_copyW hlen hk hd0 (hv_top hk he).1
    · rw [if_neg hd0] at hy
      exact honest_chainOps hT hC hlen hacc (groupRead T u (XF P T f pk m bits (u+1))) hk hread (topCell_pos hk) (hv_top hk he) y hy
  · rw [if_neg hx] at hy
    have he : ¬ exported (chainOf u i) := fun h => hx ((exported_iff u hu i hi).mp h)
    have h0 : chainOf u i ≠ 0 := by have := chainOf_pos u hu i hi; omega
    exact honest_chainOps hT hC hlen hacc (groupRead T u (XF P T f pk m bits (u+1))) hk hread (xhCell_pos hk h0 he) (hv_xh hk h0 he) y hy

/-- The honest root tops, with zero values outside the 42-chain domain. -/
abbrev tpsF (P : FourFusion.Params) (T : Tab) (f : HashTable) (pk : PublicKey) (m : Message)
    (bits : List Bool) : FourFusion.Tops :=
  topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits)

theorem rootState_last (f : HashTable) (P : FourFusion.Params) (tp : FourFusion.Tops) :
    ∀ n r st, rootState f P tp r (n+1) st =
      ans f (P.rootInput tp ⟨(r+n)%1,Nat.mod_lt _ (by decide)⟩ (rootState f P tp r n st)) := by
  intro n
  induction n with
  | zero => intro r st; rfl
  | succ n ih =>
    intro r st
    show rootState f P tp (r+1) (n+1) _ = _
    rw [ih,show r+1+n=r+(n+1) by ring]
    rfl

theorem RAF_eq {i : ℕ} (hi : i<1) :
    RAF P T f pk m bits i = rootState f P (tpsF P T f pk m bits) 0 (i+1) 0 := by
  unfold RAF; exact rootAnsF_spec P f _ 1 0 _ i hi

include hlen in
theorem topsV_honest : topsV T (hv P T f pk m bits) (XF P T f pk m bits) = tpsF P T f pk m bits := by
  funext k
  by_cases hk : k<42
  · rw [topsV_at T _ _ hk,← hd_XF,hv_rtop hlen hk,cellBits_cellOfBits]
    simp only [tpsF,topsOfV,if_pos hk]
  · simp only [topsV,tpsF,topsOfV,if_neg hk]

include hlen in
theorem rootSeq_honest {i : ℕ} (hi : i≤1) :
    rootSeq (hv P T f pk m bits) i = rootState f P (tpsF P T f pk m bits) 0 i 0 := by
  unfold rootSeq
  by_cases h0 : i=0
  · subst i; rw [if_pos rfl]; rfl
  · rw [if_neg h0]
    unfold stVal
    rw [(hv_st (by omega)).2,(hv_st (by omega)).1,cellBits_hiC,cellBits_loC,hi_append_lo,
      RAF_eq (by omega),Nat.sub_add_cancel (by omega)]

include hC hlen in
theorem honest_rootCall {r : ℕ} (hr : r<1) :
    (CInstr.blake (rootMsg T (XF P T f pk m bits) r 0) (rootMsg T (XF P T f pk m bits) r 1)
      (rootMsg T (XF P T f pk m bits) r 2) (rootMsg T (XF P T f pk m bits) r 3)
      (rootCv r) (stCell r) (rootMdCell r)).Rel f (hv P T f pk m bits) := by
  have hmd : ∀ r : Fin 1, cellBits (hv P T f pk m bits (rootMdCell r.val)) = P.rootMd r := by
    intro r
    have he : rootMdCell r.val = cCell (FourFusion.rootIndex r).val := by fin_cases r <;> rfl
    have hi : (FourFusion.rootIndex r).val≤13 := by fin_cases r <;> decide
    rw [he,hv_cc hi,hC.rootMd]
  refine blake_rel (a:=RAF P T f pk m bits r)
    (hv_canonical ..) (hv_canonical ..) (hv_canonical ..) (hv_canonical ..)
    (hv_canonical ..) (hv_canonical ..) (hv_canonical ..) ?_ (hv_st hr).1 (hv_st hr).2
  rw [root_query_of hv_one hmd ⟨r,hr⟩,topsV_honest hlen,rootSeq_honest hlen (by omega),
    RAF_eq hr,rootState_last,Nat.zero_add]
  simp only [Nat.mod_eq_of_lt hr]

include hC hlen in
/-- Every root instruction in a home block is the single root call. -/
theorem honest_rootIns {u : ℕ} (hu : u < 13) :
    ∀ y ∈ rootIns T u (XF P T f pk m bits (u + 1)) false,
      y.Rel f (hv P T f pk m bits) := by
  intro y hy
  unfold rootIns at hy
  split_ifs at hy with h5
  · simp only [List.mem_singleton] at hy
    subst y
    have hr : hcall u < 1 := by unfold hcall; omega
    have hU : homeU (hcall u) = u := by
      interval_cases u <;> first | rfl | (exfalso; omega)
    have h := honest_rootCall (f := f) (pk := pk) (m := m) hC hlen hr
    simpa only [rootMsg, hU] using h
  · simp at hy


theorem sum_unit (F : Nat → Nat) :
    (∑ j ∈ Finset.range 13, F (unit j)) = ∑ u ∈ Finset.range 13, F u := by
  rw [← list_sum_range,← list_sum_range]
  have hm : (List.range 13).map (fun j => F (unit j)) = FreeLastBlocks.order.map F := by
    rw [← unit_order,List.map_map]
    rfl
  rw [hm]
  exact List.Perm.sum_eq ((show FreeLastBlocks.order.Perm (List.range 13) by decide).map F)

theorem gpK_step (T : Tab) (I : Word) (j : Nat) :
    CenteredChecksum.Step FreeLastBase.base (chargedCost T (unit j) (hxs T I (unit j+1)))
      (gpK T I j) (gpK T I (j+1)) := by
  apply (CenteredChecksum.step_iff FreeLastBase.base_ne_zero _).mpr
  unfold gpK
  rw [← zpow_natCast FreeLastBase.base 6,
    ← zpow_natCast FreeLastBase.base (chargedCost T (unit j) (hxs T I (unit j+1))),
    ← zpow_add₀ FreeLastBase.base_ne_zero,← zpow_add₀ FreeLastBase.base_ne_zero]
  congr 1
  simp only [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
  ring

theorem honest_gp {j : Nat} (hj : j ≤ 13) :
    hv P T f pk m bits (FreeLastBlocks.gp j) = gpV T (IF P f pk m bits) j := by
  by_cases h0 : j = 0
  · subst j
    rw [show FreeLastBlocks.gp 0 = cCell 1 from rfl,hv_cc (by decide)]
    simp only [cV,gpV,gpK,Finset.sum_range_zero,Nat.cast_zero,add_zero,mul_zero,sub_zero,zpow_one,pow_one]
  · simp only [FreeLastBlocks.gp,if_neg h0]
    exact hv_gpl hj

include hT hC hacc in
theorem honest_gp13 : hv P T f pk m bits (FreeLastBlocks.gp 13) =
    ofK (FreeLastBase.base ^ (-(XF P T f pk m bits 0 : Int))) := by
  rw [honest_gp (by decide),gpV,gpK,sum_unit (fun u => chargedCost T u (hxs T (IF P f pk m bits) (u+1)))]
  have hs := hsum hC hacc
  have hch := charged_sum hT (hxs_valid T _ (hlive hC hacc))
  apply congrArg ofK
  apply congrArg (fun e : Int => FreeLastBase.base^e)
  change hxs T (IF P f pk m bits) 0+gsum T (hxs T (IF P f pk m bits))=85 at hs
  simp only [gsum,XF] at hs ⊢
  omega

include hlen in
theorem honest_bias {u : Nat} (hu : u < 13) :
    hv P T f pk m bits (FreeLastBlocks.bias u) = ofK (stageBias u) := by
  by_cases h12 : u = 12
  · subst u
    have hh : hv P T f pk m bits lenCell = natV 5504 := by
      rw [hv_lt P T f pk m bits (by decide)]
      exact inputWord_len_of pk m bits hlen
    exact hh.trans (HLG3.LengthGate128.natV_ofK (by decide))
  · simp only [FreeLastBlocks.bias,stageBias,if_neg h12]
    by_cases h11 : u = 11
    · simp only [if_pos h11]; exact hv_one
    · simp only [if_neg h11]; exact hv_cc (by omega)

include hlen in
theorem honest_hxor {u : Nat} (hu : u < 13) :
    (CInstr.xor (hCell (u+1)) (FreeLastBlocks.bias u) (h1Cell (u+1))).Rel f (hv P T f pk m bits) := by
  change hv P T f pk m bits (h1Cell (u+1)) =
    hv P T f pk m bits (hCell (u+1))+hv P T f pk m bits (FreeLastBlocks.bias u)
  rw [hv_h1 (by omega),hv_h (by omega),honest_bias hlen hu,← ofK_add]
  simp only [frameK,show u+1 ≠ 0 by omega,if_false,Nat.add_sub_cancel]

include hT hC hlen hacc hroot in
theorem honest_pk_copy : (copy (stCell 0) pkCell).Rel f (hv P T f pk m bits) := by
  change hv P T f pk m bits pkCell = hv P T f pk m bits (stCell 0)*hv P T f pk m bits oneCell
  rw [hv_one,mul_oneV,(hv_st (by decide)).1,show pkCell = 0 from rfl,
    hv_lt P T f pk m bits (by decide),inputWord_pk]
  have hlo : (RAF P T f pk m bits 0).extractLsb' 0 128 = pk := by
    rw [RAF_eq (by decide)]
    change rootValue f P (topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits)) = pk
    rw [topsOfV_eq hacc hT hC]
    exact hroot
  exact (congrArg cellOfBits hlo).symm

include hT hC hlen hacc hroot in
theorem honest_pro : ∀ ci ∈ prefixCode 15, ci.Rel f (hv P T f pk m bits) := by
  intro ci hci
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hci
  have hi16 := List.mem_range.mp hi
  by_cases hi12 : i < 11
  · rw [initialRaw_first hi12]
    exact hv_cc (by omega)
  · have hil : i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by omega
    rcases hil with rfl | rfl | rfl | rfl
    · refine ⟨hv_one,?_⟩
      rw [hv_lt P T f pk m bits (by decide : lenCell < 47)]
      exact inputWord_len_of pk m bits hlen
    · exact honest_pk_copy hT hC hlen hacc hroot
    · change (CInstr.blake msgLo msgHi nonceCell pkCell (cCell 1) idxCell (cCell 11)).Rel f _
      exact blake_rel (hv_canonical ..) (hv_canonical ..) (hv_canonical ..) (hv_canonical ..)
        (hv_canonical ..) (hv_canonical ..) (hv_canonical ..)
        (by rw [honest_idx_query hC hlen]; rfl) hv_idx hv_idx1
    · exact honest_hxor hlen (by decide : 0 < 13)

theorem entryK_group (T : Tab) (I : Word) {u : Nat} (hu : u < 13)
    (hv : hxs T I (u+1) < VF u) :
    FreeLastEntryCheck.Entry (entryK T I (u+1))
      (.group u (hxs T I (u+1)) (if u = 1 then decide (hxs T I 0 = 0) else false)) := by
  by_cases h1 : u = 1
  · subst u
    by_cases hs : hxs T I 0 = 0
    · simpa only [entryK,show ¬((1 : Nat)+1 = 0) by decide,if_false,if_true,
        show (1 : Nat)+1 = 2 from rfl,true_and,hs,decide_true] using FreeLastEntries.zero_entry hv
    · simpa only [entryK,show ¬((1 : Nat)+1 = 0) by decide,if_false,if_true,
        show (1 : Nat)+1 = 2 from rfl,true_and,hs,decide_false,Nat.add_sub_cancel] using
        FreeLastEntries.normal_entry (by decide : 1 < 13) hv
  · simpa only [entryK,show u+1 ≠ 0 by omega,if_false,show u+1 ≠ 2 by omega,false_and,
      Nat.add_sub_cancel,if_neg h1] using FreeLastEntries.normal_entry hu hv

include hC hacc in
theorem honest_landing {u : Nat} (hu : u < 13) :
    GroupLanding (hv P T f pk m bits) u (XF P T f pk m bits (u+1))
      (if u = 1 then decide (XF P T f pk m bits 0 = 0) else false) := by
  have he := entryK_group T (IF P f pk m bits) hu (XF_lt_W hC hacc hu)
  exact ⟨entryK T (IF P f pk m bits) (u+1),he.1,he.2.1,hv_h (by omega),he.2.2.2,he.2.2.1⟩

include hC hacc in
theorem honest_tie {u : Nat} (hu : u < 13) :
    ∀ ci ∈ FreeLastBlocks.tie u (XF P T f pk m bits (u+1)), ci.Rel f (hv P T f pk m bits) := by
  let x := fun w => XF P T f pk m bits (w+1)
  have hx : ∀ w, x w < 2^gb w := by
    intro w
    simp only [x,XF,hxs_succ,field]
    exact digitW_lt _ _ _
  have ha : ∀ w < 13, hv P T f pk m bits (accCell w) = cellOfBits (FreeLastTie.accBits x w) :=
    fun w hw => honest_acc hw
  intro ci hci
  by_cases h0 : u = 0
  · subst u
    simp only [FreeLastBlocks.tie,if_true,List.mem_singleton] at hci
    subst ci
    change hv P T f pk m bits (accCell 0) = FreeLastBlocks.pattern 0 (x 0)
    rw [ha 0 (by decide),FreeLastTie.acc_zero x hx,
      FreeLastTie.part_plain (by decide : 0 < 13) (XF_lt_W hC hacc (by decide)) rfl]
  have he : u-1+1 = u := by omega
  have hstep : hv P T f pk m bits (accCell (u-1)) + cellOfBits (FreeLastTie.part u (x u)) =
      hv P T f pk m bits (accCell u) := by
    rw [ha (u-1) (by omega),ha u hu,HLG3.cellOfBits_add]
    have hh := FreeLastTie.acc_step x hx (u:=u-1) (by omega)
    rw [he] at hh
    exact congrArg cellOfBits hh
  simp only [FreeLastBlocks.tie,if_neg h0] at hci
  cases hh : FreeLastBlocks.hinted u (x u) with
  | true =>
    have hhh : FreeLastBlocks.hinted u (XF P T f pk m bits (u+1)) = true := hh
    simp only [hhh,if_true,List.mem_singleton] at hci
    subst ci
    change hv P T f pk m bits (accCell u) =
      hv P T f pk m bits (accCell (u-1))+hv P T f pk m bits (hCell (u+1))
    rw [FreeLastTie.landing_part (honest_landing hC hacc hu) hhh]
    exact hstep.symm
  | false =>
    have hhh : FreeLastBlocks.hinted u (XF P T f pk m bits (u+1)) = false := hh
    simp only [hhh,Bool.false_eq_true,if_false] at hci
    rw [FreeLastTie.part_plain hu (XF_lt_W hC hacc hu) hh] at hstep
    by_cases hv0 : XF P T f pk m bits (u+1) = 0
    · simp only [if_pos hv0,List.mem_singleton] at hci
      subst ci
      change hv P T f pk m bits (accCell u) = hv P T f pk m bits (accCell (u-1))*hv P T f pk m bits oneCell
      rw [hv_one,mul_oneV]
      change hv P T f pk m bits (accCell (u-1))+FreeLastBlocks.pattern u (XF P T f pk m bits (u+1)) = _ at hstep
      rw [hv0,FreeLastTie.pattern_zero,add_zero] at hstep
      exact hstep.symm
    · simp only [if_neg hv0,List.mem_cons,List.not_mem_nil,or_false] at hci
      rcases hci with rfl | rfl
      · exact hv_t hu
      · change hv P T f pk m bits (accCell u) = hv P T f pk m bits (accCell (u-1))+hv P T f pk m bits (tCell u)
        rw [hv_t hu]
        exact hstep.symm

theorem honest_checksum (hC : Compat P fusionTab)
    (hacc : P.codec.Accepted (effective (IF P f pk m bits))) {u : Nat} (hu : u < 13)
    (z : Bool) (hz : z = true → u = 1 ∧ XF P fusionTab f pk m bits 0 = 0) :
    (FreeLastBlocks.checksum u (XF P fusionTab f pk m bits (u+1)) z).Rel f
      (hv P fusionTab f pk m bits) := by
  have hc := LengthFrame.cost_shift_le fusionTab_hyp hu (XF_lt_W hC hacc hu)
  change chargedCost fusionTab u (XF P fusionTab f pk m bits (u+1)) ≤ 16 at hc
  have hj := position_lt hu
  have hsrc := honest_gp (P:=P) (T:=fusionTab) (f:=f) (pk:=pk) (m:=m) (bits:=bits) hj.le
  have hdst : hv P fusionTab f pk m bits (if z then oneCell else FreeLastBlocks.gp (FreeLastBlocks.position u+1)) =
      gpV fusionTab (IF P f pk m bits) (FreeLastBlocks.position u+1) := by
    cases z with
    | false =>
      change hv P fusionTab f pk m bits (FreeLastBlocks.gp (FreeLastBlocks.position u+1)) = _
      exact honest_gp (j:=FreeLastBlocks.position u+1) (by omega)
    | true =>
      obtain ⟨rfl,hs⟩ := hz rfl
      have hh := honest_gp13 fusionTab_hyp hC hacc
      rw [hs,Int.natCast_zero,neg_zero,zpow_zero] at hh
      have hv13 := honest_gp (P:=P) (T:=fusionTab) (f:=f) (pk:=pk) (m:=m) (bits:=bits) (j:=13) le_rfl
      change hv P fusionTab f pk m bits oneCell = gpV fusionTab (IF P f pk m bits) 13
      rw [hv_one]
      exact hh.symm.trans hv13
  have hs := gpK_step fusionTab (IF P f pk m bits) (FreeLastBlocks.position u)
  rw [unit_inverse hu] at hs
  unfold FreeLastBlocks.checksum CenteredChecksum.Step at *
  by_cases hc6 : 6 ≤ chargedCost fusionTab u (XF P fusionTab f pk m bits (u+1))
  · rw [if_pos hc6] at hs ⊢
    change hv P fusionTab f pk m bits _ = hv P fusionTab f pk m bits _ * hv P fusionTab f pk m bits (cCell _)
    rw [hsrc,hdst,hv_cc (by omega),cV,gpV,gpV,← ofK_mul]
    exact congrArg ofK hs
  · rw [if_neg hc6] at hs ⊢
    change hv P fusionTab f pk m bits _ = hv P fusionTab f pk m bits _ * hv P fusionTab f pk m bits (cCell _)
    rw [hsrc,hdst,hv_cc (by omega),cV,gpV,gpV,← ofK_mul]
    exact congrArg ofK hs

theorem honest_core (hC : Compat P fusionTab) (hlen : bits.length = 5504)
    (hacc : P.codec.Accepted (effective (IF P f pk m bits))) {u : Nat} (hu : u < 13)
    (z : Bool) (hz : z = true → u = 1 ∧ XF P fusionTab f pk m bits 0 = 0) :
    ∀ ci ∈ FreeLastBlocks.core u (XF P fusionTab f pk m bits (u+1)) z,
      ci.Rel f (hv P fusionTab f pk m bits) := by
  intro ci hci
  simp only [FreeLastBlocks.core,List.mem_append,List.mem_singleton,List.mem_replicate] at hci
  rcases hci with (((h | rfl) | h) | h) | ⟨_,rfl⟩
  · exact honest_tie hC hacc hu _ h
  · exact honest_checksum hC hacc hu z hz
  · exact honest_segs fusionTab_hyp hC hlen hacc hu _ h
  · exact honest_rootIns hC hlen hu _ h
  · change hv P fusionTab f pk m bits oneCell = hv P fusionTab f pk m bits oneCell * hv P fusionTab f pk m bits oneCell
    rw [hv_one,mul_oneV]

theorem honest_free (hC : Compat P fusionTab) (hlen : bits.length = 5504)
    (hacc : P.codec.Accepted (effective (IF P f pk m bits))) :
    ∀ ci ∈ FreeLastBlocks.free (XF P fusionTab f pk m bits 0), ci.Rel f (hv P fusionTab f pk m bits) := by
  have hd0 : hd fusionTab (y0F P f pk m bits) 0 = XF P fusionTab f pk m bits 0 := by
    rw [hd_XF]; exact if_pos rfl
  rw [← hd0]
  apply honest_chainOps fusionTab_hyp hC hlen hacc topCell (by decide : 0 < 42)
  · intro u hu
    change none = some u at hu
    cases hu
  · decide
  · exact ⟨hv_tf,hv_tf1⟩

theorem honest_blocks (hC : Compat P fusionTab) (hlen : bits.length = 5504)
    (hacc : P.codec.Accepted (effective (IF P f pk m bits))) {u : Nat} (hu : u < 13) :
    ∀ ci ∈ FreeLastBlocks.chosen (decide (XF P fusionTab f pk m bits 0 = 0)) u
      (XF P fusionTab f pk m bits (u+1)), ci.Rel f (hv P fusionTab f pk m bits) := by
  intro ci hci
  unfold FreeLastBlocks.chosen at hci
  split_ifs at hci with hz
  · obtain ⟨rfl,hs⟩ := hz
    have hs0 : XF P fusionTab f pk m bits 0 = 0 := of_decide_eq_true hs
    simp only [FreeLastBlocks.zero,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hci
    rcases hci with h | rfl | rfl
    · exact honest_core hC hlen hacc (by decide) true (fun _ => ⟨rfl,hs0⟩) _ h
    · have hd0 : hd fusionTab (y0F P f pk m bits) 0 = 0 := by
        rw [hd_XF,dg,if_pos rfl]
        exact hs0
      exact honest_copyW (P:=P) (T:=fusionTab) (f:=f) (pk:=pk) (m:=m) (bits:=bits)
        hlen (by decide : 0 < 42) hd0 hv_tf
    · change hv P fusionTab f pk m bits oneCell = hv P fusionTab f pk m bits oneCell * hv P fusionTab f pk m bits oneCell
      rw [hv_one,mul_oneV]
  · simp only [FreeLastBlocks.normal,List.mem_append,List.mem_singleton] at hci
    rcases hci with h | rfl
    · exact honest_core hC hlen hacc hu false (by intro h; cases h) _ h
    · by_cases h1 : u = 1
      · subst u
        rw [if_pos rfl]
        change hv P fusionTab f pk m bits (h1Cell 0) =
          hv P fusionTab f pk m bits (hCell 0)+hv P fusionTab f pk m bits (FreeLastBlocks.gp 13)
        rw [hv_h1 (by decide),hv_h (by decide),honest_gp13 fusionTab_hyp hC hacc,← ofK_add]
        rfl
      · rw [if_neg h1]
        exact honest_hxor hlen (by unfold FreeLastBlocks.nextGroup; split_ifs <;> omega)

end
end OptimalOTS.FreeLastVM
