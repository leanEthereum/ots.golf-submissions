import Submissions.UpperLeanIsa.MachineHonest

/-!
# The honest path and the honest run

Every op of every block on the honest path holds on the loaded honest image (`honest_blk`), so
the relations along the path of `hxs T I` hold (`honest_path`), and the machine completes in
`205` instructions at cost `1078` (`honest_run`).
-/

namespace OptimalOTS.HLG3

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord OracleCompressCells)

noncomputable section

section Honest

variable {P : Params} {T : Tab} {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}
variable (hT : T.Hyp) (hC : Compat P T) (hlen : bits.length = 5503)
  (hacc : P.Accepted (effective (IF P f pk m bits)))
  (hroot : rootValue f P (topsOf f P (effective (IF P f pk m bits)) bits) = pk)

theorem hd_XF (k : ℕ) : hd T (y0F P f pk m bits) k = dg T (XF P T f pk m bits) k := by
  unfold hd; rfl

include hC hacc in
theorem XF_lt_W {u : ℕ} (hu : u < 13) : XF P T f pk m bits (u + 1) < VF u := by
  have := hxs_valid T (IF P f pk m bits) (hlive hC hacc) (u + 1) (by omega); rwa [Wf_succ hu] at this

include hT hC hlen in
/-- **The honest free block.** -/
theorem honest_free : ∀ y ∈ fbody (XF P T f pk m bits 0), y.Rel f (hv P T f pk m bits) := by
  have hd0 : hd T (y0F P f pk m bits) 0 = XF P T f pk m bits 0 := by
    rw [hd_XF]; unfold dg; rw [if_pos rfl]
  have hseed : (CInstr.setc (gpCell 0)
      (ofK (LeanIsaFieldRescale.initialProduct 87 (XF P T f pk m bits 0)))).Rel f
        (hv P T f pk m bits) := by
    show hv P T f pk m bits (gpCell 0) = _
    rw [honest_gp (by omega)]
    unfold gpV
    rw [Finset.sum_range_zero]
    change ofK (_ * gpow 0) = _
    rw [gpow_zero', mul_one]
  intro y hy
  unfold fbody at hy
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with (rfl | h) | rfl
  · exact hseed
  · by_cases hs0 : XF P T f pk m bits 0 = 0
    · rw [if_pos hs0] at h; simp at h
    · rw [if_neg hs0, ← hd0] at h
      exact honest_chainOps hT hC hlen (by omega) (by decide) ⟨hv_tf, hv_tf1⟩ y h
  · exact honest_hmul (by unfold frG0; split_ifs <;> omega)

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
    rw [honest_acc (by omega), ofDigitsW_succ, ofDigitsW_zero]
    unfold fpat POS; simp only [Nat.zero_add]
  · rw [if_neg hu0] at hy
    obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
    rw [Nat.add_sub_cancel] at hy
    have hprev := honest_acc (P := P) (T := T) (f := f) (pk := pk) (m := m) (bits := bits)
      (u := w) (by omega)
    have hcur := honest_acc (P := P) (T := T) (f := f) (pk := pk) (m := m) (bits := bits)
      (u := w + 1) hu
    have hl1 := ofDigitsW_lt gb _ hlt (w + 1)
    have hl2 := ofDigitsW_lt gb _ hlt (w + 1 + 1)
    have hpos : 2 ^ posW gb (w + 1 + 1) ≤ 2 ^ 128 := by
      rw [← POS_13]; exact Nat.pow_le_pow_right (by norm_num) (posW_mono gb (by omega))
    by_cases hx0 : XF P T f pk m bits (w + 1 + 1) = 0
    · rw [if_pos hx0] at hy
      simp only [List.mem_singleton] at hy
      subst hy
      show hv P T f pk m bits (accCell (w + 1)) =
        hv P T f pk m bits (accCell w) * hv P T f pk m bits oneCell
      rw [hv_one, mul_oneV, hcur, hprev, ofDigitsW_succ _ _ (w + 1)]
      simp only [hx0, Nat.zero_mul, Nat.add_zero]
    · rw [if_neg hx0] at hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact hv_t hu
      · show hv P T f pk m bits (accCell (w + 1)) =
          hv P T f pk m bits (accCell w) + hv P T f pk m bits (tCell (w + 1))
        rw [hv_t hu, hcur, hprev]
        unfold fpat POS
        rw [ofDigitsW_succ _ _ (w + 1)] at hl2 ⊢
        exact (natV_add_disjoint hl1 (by omega)).symm

include hT hC hacc in
/-- **The honest landing product.** -/
theorem honest_prod {u : ℕ} (hu : u < 13) :
    (prodOp T u (XF P T f pk m bits (u + 1))).Rel f (hv P T f pk m bits) := by
  show hv P T f pk m bits (gpCell (u + 1)) = hv P T f pk m bits (gpCell u) *
    hv P T f pk m bits (cCell (cost T u (XF P T f pk m bits (u + 1))))
  rw [honest_gp (by omega), honest_gp (by omega),
    hv_cc (by have := cost_le hT hu (XF_lt_W hC hacc hu); omega), cV]
  unfold gpV
  rw [← ofK_mul, Finset.sum_range_succ]
  change ofK (_ * LeanIsaFieldRescale.costFactor (_ + _)) =
    ofK ((_ * LeanIsaFieldRescale.costFactor _) * LeanIsaFieldRescale.costFactor _)
  rw [mul_assoc, LeanIsaFieldRescale.factor_add]

include hT hC hlen in
/-- **The honest chains of a group block.** -/
theorem honest_segs {u : ℕ} (hu : u < 13) :
    ∀ y ∈ segs T u (XF P T f pk m bits (u + 1)), y.Rel f (hv P T f pk m bits) := by
  intro y hy
  obtain ⟨i, hi, hy⟩ := mem_segs.mp hy
  have hk := chainOf_lt u hu i hi
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
      exact honest_chainOps hT hC hlen hk (topCell_pos hk) (hv_top hk he) y hy
  · rw [if_neg hx] at hy
    have he : ¬ exported (chainOf u i) := fun h => hx ((exported_iff u hu i hi).mp h)
    have h0 : chainOf u i ≠ 0 := by have := chainOf_pos u hu i hi; omega
    exact honest_chainOps hT hC hlen hk (xhCell_pos hk h0 he) (hv_xh hk h0 he) y hy

/-- The honest root tops. -/
abbrev tpsF (P : Params) (T : Tab) (f : HashTable) (pk : PublicKey) (m : Message)
    (bits : List Bool) : Fin numChains → Word :=
  topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits)

theorem rootState_last (f : HashTable) (P : Params) (tp : Fin numChains → Word) :
    ∀ n r st, rootState f P tp r (n + 1) st =
      ans f (P.rootInput tp (r + n) (rootState f P tp r n st)) := by
  intro n
  induction n with
  | zero => intro r st; rfl
  | succ n ih =>
    intro r st
    show rootState f P tp (r + 1) (n + 1) _ = _
    rw [ih, show r + 1 + n = r + (n + 1) by ring]
    rfl

theorem RAF_eq {i : ℕ} (hi : i < 9) :
    RAF P T f pk m bits i = rootState f P (tpsF P T f pk m bits) 0 (i + 1)
      (Params.rootInit (tpsF P T f pk m bits)) := by
  unfold RAF; exact rootAnsF_spec P f _ 9 0 _ i hi

theorem topAt_tps {j : ℕ} (hj : j < 42) :
    Params.topAt (tpsF P T f pk m bits) j = topOf T bits (y0F P f pk m bits) (AF P T f pk m bits) j := by
  unfold Params.topAt; rw [dif_pos hj]; rfl

include hlen in
theorem topsV_honest : topsV T (hv P T f pk m bits) (XF P T f pk m bits) = tpsF P T f pk m bits := by
  funext k
  unfold topsV
  rw [← hd_XF, hv_rtop hlen k.isLt, cellBits_cellOfBits]
  rfl

include hlen in
theorem rootSeq_honest {i : ℕ} (hi : i ≤ 9) :
    rootSeq T (hv P T f pk m bits) (XF P T f pk m bits) i =
      rootState f P (tpsF P T f pk m bits) 0 i (Params.rootInit (tpsF P T f pk m bits)) := by
  unfold rootSeq
  rw [topsV_honest hlen]
  by_cases h0 : i = 0
  · subst i; rw [if_pos rfl]; rfl
  · rw [if_neg h0]
    unfold stVal
    rw [(hv_st (by omega)).2, (hv_st (by omega)).1, cellBits_hiC, cellBits_loC, hi_append_lo,
      RAF_eq (by omega), Nat.sub_add_cancel (by omega)]

include hC hlen in
theorem honest_rootCall {r : ℕ} (hr : r < 9) :
    (CInstr.blake (rootMsg T (XF P T f pk m bits) r 0) (rootMsg T (XF P T f pk m bits) r 1)
      (rootMsg T (XF P T f pk m bits) r 2) (rootMsg T (XF P T f pk m bits) r 3)
      (rootCv r) (stCell r) (fCell r)).Rel f (hv P T f pk m bits) := by
  refine blake_rel (a := RAF P T f pk m bits r)
    (hv_canonical ..) (hv_canonical ..) (hv_canonical ..) (hv_canonical ..)
    (hv_canonical ..) (hv_canonical ..) (hv_canonical ..) ?_ (hv_st hr).1 (hv_st hr).2
  rw [blake2sQuery_eq, rootCv_pair T (hv P T f pk m bits) _ hr,
    rootMsg_block hr, rootMd_cell_of hC (fun r _ => hv_frame (by omega)) hr,
    topsV_honest hlen, rootSeq_honest hlen (by omega), RAF_eq hr, rootState_last, Nat.zero_add]
  rfl

include hC hlen in
/-- Every root instruction in a home block is one of the nine root calls. -/
theorem honest_rootIns {u : ℕ} (hu : u < 13) :
    ∀ y ∈ rootIns T u (XF P T f pk m bits (u + 1)) (zU (XF P T f pk m bits 0) u),
      y.Rel f (hv P T f pk m bits) := by
  intro y hy
  unfold rootIns at hy
  split_ifs at hy with h5
  · simp only [List.mem_singleton] at hy
    subst y
    have hr : hcall u < 9 := by unfold hcall; split_ifs <;> omega
    have hU : homeU (hcall u) = u := by
      interval_cases u <;> first | rfl | (exfalso; omega)
    have h := honest_rootCall (f := f) (pk := pk) (m := m) hC hlen hr
    simpa only [rootMsg, hU] using h
  · simp at hy

include hT hC hacc hroot in
/-- **The honest next op.** -/
theorem honest_next {u : ℕ} (hu : u < 13) : (nextOp u).Rel f (hv P T f pk m bits) := by
  unfold nextOp
  by_cases h12 : u < 12
  · rw [if_pos h12]; exact honest_hmul (by omega)
  · rw [if_neg h12]
    show hv P T f pk m bits pkCell = hv P T f pk m bits (stCell 8) * hv P T f pk m bits oneCell
    rw [hv_one, mul_oneV, (hv_st (by omega)).1, show pkCell = 0 from rfl,
      hv_lt P T f pk m bits (by omega), inputWord_pk]
    have hlo : (RAF P T f pk m bits 8).extractLsb' 0 128 = pk := by
      rw [RAF_eq (by omega)]
      show rootValue f P (topsOfV T bits (y0F P f pk m bits) (AF P T f pk m bits)) = pk
      rw [topsOfV_eq hacc hT hC]
      exact hroot
    unfold loC
    exact (congrArg cellOfBits hlo).symm

include hT hC hlen hacc hroot in
/-- **The honest blocks.** Every op of every block on the honest path holds. -/
theorem honest_blk : ∀ r < 14, ∀ y ∈ bodyF T (frU (XF P T f pk m bits 0) r) (XF P T f pk m bits r),
    y.Rel f (hv P T f pk m bits) := by
  intro r hr y hy
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · rw [bodyF_frU_zero] at hy
    exact honest_free hT hC hlen y hy
  · obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
    have hu : u < 13 := by omega
    rw [bodyF_frU_succ T _ hu] at hy
    unfold body at hy
    simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hy
    rcases hy with ((((h | h) | h) | h) | h) | h
    · exact honest_tie hu y h
    · subst h; exact honest_prod hT hC hacc hu
    · exact honest_segs hT hC hlen hu y h
    · exact honest_rootIns hC hlen hu y h
    · rw [h.2]
      show hv P T f pk m bits oneCell = hv P T f pk m bits oneCell * hv P T f pk m bits oneCell
      rw [hv_one, mul_oneV]
    · subst h; exact honest_next hT hC hacc hroot hu

include hT hC hlen hacc hroot in
/-- **The honest path.** Every op on the path of the honest index vector holds on the loaded
honest image. -/
theorem honest_path : PathFacts T (oracleRel f) (hv P T f pk m bits) (XF P T f pk m bits) :=
  ⟨honest_pro hC hlen hacc, fun r hr => honest_dispatch hC hacc hr, honest_blk hT hC hlen hacc hroot,
    by show IsInK (hv P T f pk m bits (gpCell 13)); rw [honest_gp13 hC hacc]; exact isInK_ofK _,
    honest_gp13 hC hacc⟩

include hT hC hlen hacc hroot in
/-- **Honest run.** When the verifier accepts under the table, the honest image completes in
`205` instructions. -/
theorem honest_run :
    simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost (program T) (LeanIsa.loadInput pk m bits (imageF P T f pk m bits)) 205
          Regs.initial) = pure (some 1078) := by
  obtain ⟨n, c, hw⟩ := walk_mk hT (hxs_valid T _ (hlive hC hacc)) (honest_path hT hC hlen hacc hroot)
    (fun r hr => by rw [hv_h1 (frU_lt _ hr), XFr_frU hr])
  have hpin : Pinned (hv P T f pk m bits) := by
    refine ⟨hv_one, fun r hr => ?_⟩
    exact hv_frame hr
  obtain ⟨hV, hP, hL, hn, hc⟩ := walk_full hT hw
  have hs := layer_of_facts hT hV hP hL
  have := sim_of_walk hT (le_refl 16) (by decide) f hpin hw
  rw [initial_eq]
  rw [hn, hc, totalSteps_eq hT hV hs, totalCost_eq hT hV hs] at this
  exact this

end Honest

end

end OptimalOTS.HLG3
