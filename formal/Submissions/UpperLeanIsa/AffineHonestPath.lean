import Submissions.UpperLeanIsa.AffineHonestChain
import Submissions.UpperLeanIsa.AffineReplay

/-!
# The honest path and the honest run

Every op of every block on the honest path holds on the loaded honest image (`honest_blk`), so
the relations along the path of `hxs T I` hold (`honest_path`), and the machine completes in
`191` instructions at cost `974` (`honest_run`).
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace OptimalOTS.AffineVM

open OracleComp LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.HLG3 (natV ans natV_add_disjoint hi_append_lo inputWord_pk)
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

section Honest

variable {P : FourFusion.Params} {T : Tab} {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length = 5504)
  (hacc : P.codec.Accepted (effective (IF P f pk m bits)))
  (hroot : rootValue f P (topsOf f P (effective (IF P f pk m bits)) bits) = pk)

theorem hd_XF (k : ℕ) : hd T (y0F P f pk m bits) k = dg T (XF P T f pk m bits) k := by
  unfold hd; rfl

include hC hacc in
theorem XF_lt_W {u : ℕ} (hu : u < 13) : XF P T f pk m bits (u + 1) < VF u := by
  have := hxs_valid T (IF P f pk m bits) (hlive hC hacc) (u + 1) (by omega); rwa [Wf_succ hu] at this

include hT hC hlen hacc in
/-- **The honest free block.** -/
theorem honest_free : ∀ y ∈ bodyCode T (base T) 0 (XF P T f pk m bits 0), y.Rel f (hv P T f pk m bits) := by
  have hd0 : hd T (y0F P f pk m bits) 0 = XF P T f pk m bits 0 := by
    rw [hd_XF]; unfold dg; rw [if_pos rfl]
  have hseed : (CInstr.setc (gpCell 0)
      (ofK (seedProduct (base T) (XF P T f pk m bits 0)))).Rel f
        (hv P T f pk m bits) := by
    show hv P T f pk m bits (gpCell 0) = _
    rw [honest_gp (by omega)]
    unfold gpV gpK
    simp only [Finset.sum_range_zero,Nat.mul_zero,pow_zero,mul_one,div_one]
  intro y hy
  rw [free_bodyCode] at hy
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl | h | rfl | rfl
  · exact hseed
  · rw [← hd0] at h
    have hread : HonestReadContext (P:=P) (T:=T) (f:=f) (pk:=pk) (m:=m) (bits:=bits) topCell 0 := by
      intro u hu
      change none = some u at hu
      cases hu
    have hj : junkCell 0 tfCell = tfCell+1 := by decide
    apply honest_chainOps hT hC hlen hacc topCell (k:=0) (dst:=tfCell) (by decide) hread (by decide) ?_ y h
    rw [hj]
    exact ⟨hv_tf,hv_tf1⟩
  · by_cases hs0 : XF P T f pk m bits 0 = 0
    · rw [if_pos hs0]
      exact honest_copyW hlen (by omega) (hd0.trans hs0) hv_tf
    · rw [if_neg hs0]
      show hv P T f pk m bits tfCell = hv P T f pk m bits tfCell * hv P T f pk m bits oneCell
      rw [hv_one,mul_oneV]
  · exact honest_hxor (by omega)

/-- **The honest tie.** -/
theorem honest_tie {u : ℕ} (hu : u < 13) :
    ∀ y ∈ tie u (XF P T f pk m bits (u + 1)), y.Rel f (hv P T f pk m bits) := by
  intro y hy
  have hlt : ∀ w, (fun w => XF P T f pk m bits (w + 1)) w < 2 ^ gb w := fun w =>
    by show hxs T _ (w + 1) < _; rw [hxs_succ]; exact digitW_lt _ _ _
  unfold tie at hy
  by_cases hu0 : u = 0
  · subst hu0
    rw [if_pos rfl] at hy
    simp only [List.mem_singleton] at hy
    subst hy
    show hv P T f pk m bits (accCell 0) = fpat 0 (XF P T f pk m bits (0 + 1))
    rw [honest_acc (by omega), accBits_zero hlt]
  rw [if_neg hu0] at hy
  by_cases h11 : u = 11
  · subst h11
    rw [if_pos rfl] at hy
    simp only [List.mem_singleton] at hy
    subst hy
    show hv P T f pk m bits (accCell 11) =
      hv P T f pk m bits (accCell 10) + hv P T f pk m bits (hCell 12)
    rw [honest_acc (by omega), honest_acc (by omega), hv_h (by omega), ent_succ (by omega),
      accBits_11 hlt (hlt 11)]
  rw [if_neg h11] at hy
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hy
  have hprev := honest_acc (P := P) (T := T) (f := f) (pk := pk) (m := m) (bits := bits)
    (u := w) (by omega)
  have hcur := honest_acc (P := P) (T := T) (f := f) (pk := pk) (m := m) (bits := bits)
    (u := w + 1) hu
  by_cases hx0 : XF P T f pk m bits (w + 1 + 1) = 0
  · rw [if_pos hx0] at hy
    simp only [List.mem_singleton] at hy
    subst hy
    show hv P T f pk m bits (accCell (w + 1)) =
      hv P T f pk m bits (accCell w) * hv P T f pk m bits oneCell
    rw [hv_one, mul_oneV, hcur, hprev, accBits_zero_step hlt hu h11 hx0]
  · rw [if_neg hx0] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hv_t hu
    · show hv P T f pk m bits (accCell (w + 1)) =
        hv P T f pk m bits (accCell w) + hv P T f pk m bits (tCell (w + 1))
      rw [hv_t hu, hcur, hprev]
      exact (accBits_step hlt hu h11).symm

include hT hC hacc in
/-- **The honest landing product.** -/
theorem honest_prodOps {u : ℕ} (hu : u < 13) :
    ∀ ci ∈ prodOps T u (XF P T f pk m bits (u + 1)), ci.Rel f (hv P T f pk m bits) := by
  have hc := LengthFrame.cost_shift_le hT hu (XF_lt_W hC hacc hu)
  change chargedCost T u (XF P T f pk m bits (u+1)) ≤ 16 at hc
  have hstep := gpK_step T (IF P f pk m bits) u
  have hprod : (prodOp T u (XF P T f pk m bits (u + 1))).Rel f (hv P T f pk m bits) := by
    unfold prodOp
    by_cases hcenter : 6 ≤ chargedCost T u (XF P T f pk m bits (u + 1))
    · rw [if_pos hcenter]
      have he := hstep
      rw [CenteredChecksum.Step, if_pos hcenter] at he
      change hv P T f pk m bits (gpCell (u+1)) =
        hv P T f pk m bits (gpCell u) *
          hv P T f pk m bits (cCell (chargedCost T u (XF P T f pk m bits (u+1)) - 6))
      rw [honest_gp (by omega), honest_gp (by omega), hv_cc (by omega), cV, gpV, gpV, ← ofK_mul]
      exact congrArg ofK he
    · rw [if_neg hcenter]
      have he := hstep
      rw [CenteredChecksum.Step, if_neg hcenter] at he
      change hv P T f pk m bits (gpCell u) =
        hv P T f pk m bits (gpCell (u+1)) *
          hv P T f pk m bits (cCell (6 - chargedCost T u (XF P T f pk m bits (u+1))))
      rw [honest_gp (by omega), honest_gp (by omega), hv_cc (by omega), cV, gpV, gpV, ← ofK_mul]
      exact congrArg ofK he
  intro ci hi
  unfold prodOps at hi
  by_cases he : 14 < chargedCost T u (XF P T f pk m bits (u+1))
  · rw [if_pos he] at hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hprod
    · change hv P T f pk m bits oneCell =
        hv P T f pk m bits oneCell * hv P T f pk m bits oneCell
      rw [hv_one, mul_oneV]
  · rw [if_neg he] at hi
    simp only [List.append_nil, List.mem_singleton] at hi
    subst ci
    exact hprod

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
    ∀ y ∈ rootIns T u (XF P T f pk m bits (u + 1)) (zU (XF P T f pk m bits 0) u),
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
    simpa only [rootMsg, hU, zU] using h
  · simp at hy

include hT hC hacc hroot in
/-- **The honest next op.** -/
theorem honest_next {u : ℕ} (hu : u < 13) : (rehint (nextOp u)).Rel f (hv P T f pk m bits) := by
  unfold nextOp
  by_cases h12 : u < 12
  · rw [if_pos h12]
    simp only [rehint,h1Cell]
    rw [if_pos ⟨True.intro, by unfold hCell; omega⟩]
    rw [show 180+(u+2)-180 = u+2 by omega]
    exact honest_hxor (r:=u+2) (by omega)
  · rw [if_neg h12,rehint_copy]
    show hv P T f pk m bits pkCell = hv P T f pk m bits (stCell 0) * hv P T f pk m bits oneCell
    rw [hv_one, mul_oneV, (hv_st (by omega)).1, show pkCell = 0 from rfl,
      hv_lt P T f pk m bits (by omega), inputWord_pk]
    have hlo : (RAF P T f pk m bits 0).extractLsb' 0 128 = pk := by
      rw [RAF_eq (by omega)]
      show rootValue f P (topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits)) = pk
      rw [topsOfV_eq hacc hT hC]
      exact hroot
    unfold loC
    exact (congrArg cellOfBits hlo).symm

include hT hC hlen hacc hroot in
/-- **The honest blocks.** Every op of every block on the honest path holds. -/
theorem honest_blk : ∀ r < 14, ∀ y ∈ bodyCode T (base T) r (XF P T f pk m bits r),
    y.Rel f (hv P T f pk m bits) := by
  intro r hr y hy
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · exact honest_free hT hC hlen hacc y hy
  · obtain ⟨u,rfl⟩ : ∃ u, r = u+1 := ⟨r-1,by omega⟩
    have hu : u < 13 := by omega
    rw [bodyCode,if_neg (by omega),Nat.add_sub_cancel] at hy
    obtain ⟨ci,hci,rfl⟩ := List.mem_map.mp hy
    unfold body at hci
    simp only [List.mem_append,List.mem_singleton,List.mem_replicate] at hci
    rcases hci with ((((h | h) | h) | h) | h) | h
    · rw [rehint_tie h]
      exact honest_tie hu ci h
    · rw [rehint_prodOps h]
      exact honest_prodOps hT hC hacc hu ci h
    · have he : rehint ci = ci := by
        obtain ⟨i,hi,hmem⟩ := mem_segs.mp h
        exact rehint_seg T hmem
      rw [he]
      exact honest_segs hT hC hlen hacc hu ci h
    · have he : rehint ci = ci := by
        unfold rootIns at h
        split_ifs at h
        · simp only [List.mem_singleton] at h
          subst ci
          rfl
        · simp at h
      rw [he]
      exact honest_rootIns hC hlen hu ci h
    · rw [h.2]
      show hv P T f pk m bits oneCell = hv P T f pk m bits oneCell * hv P T f pk m bits oneCell
      rw [hv_one,mul_oneV]
    · subst ci
      exact honest_next hT hC hacc hroot hu

include hT hC hlen hacc hroot in
/-- **The honest path.** Every op on the path of the honest index vector holds on the loaded
honest image. -/
theorem honest_path : PathFacts T (oracleRel f) (hv P T f pk m bits) (XF P T f pk m bits) :=
  ⟨honest_pro hC hlen hacc, fun r hr => honest_dispatch hC hacc hr, honest_blk hT hC hlen hacc hroot,
    by show IsInK (hv P T f pk m bits (gpCell 13)); rw [honest_gp13 hT hC hacc]; exact isInK_ofK _,
    honest_gp13 hT hC hacc⟩

include hT hC hlen hacc hroot in
/-- **Honest run.** When the verifier accepts under the table, the honest image completes in
`191` instructions. -/
theorem honest_run :
    simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) 191
        Regs.initial) = pure (some 974) := by
  have hV := hxs_valid T _ (hlive hC hacc)
  have hP := honest_path hT hC hlen hacc hroot
  have hL : Landing (hv P T f pk m bits) (XF P T f pk m bits) := fun r hr => hv_h hr
  have hF : ∀ r < 14, hv P T f pk m bits (h1Cell r) =
      ofK (blockFrame T r (XF P T f pk m bits r)) := fun r hr => hv_h1 hr
  obtain ⟨n,c,he⟩ := sim_of_path hT (le_refl 16) (by decide)
    (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) f hV hP hL hF
  have hm : some c ∈ (simSem f).S
      (LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) n ⟨gpow 0,1⟩) := by
    change some c ∈ support (simulateQ (unifFwdAnswerImpl f) _)
    rw [he,mem_support_pure_iff]
  obtain ⟨hn,hc⟩ := run_exact hT (le_refl 16) (by decide)
    (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) (simSem f) (oracleRel f) (hashSound_sim f)
    (lengthDomain_load (le_refl 16) pk m bits (imageF P T f pk m bits)) hm
  rw [hn,hc] at he
  rw [initial_eq]
  exact he

end Honest

end

end OptimalOTS.AffineVM
