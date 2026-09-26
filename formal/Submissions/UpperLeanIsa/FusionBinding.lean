import Submissions.UpperLeanIsa.FusionTargets

/-! Binding from actual cached queries. Final chain steps at a hidden boundary
are handled by the same charged target event as exposed steps. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open scoped Classical
noncomputable section
variable {P : Params}

/-- A final step that reaches an honest top uses its honest input, or hits a cut target. -/
theorem final_query_binding (d : Cut) (hd : ValidCut P d) (ζ : Record P) (c : Cache)
    (k : Fin 42) (hlen : 2 ≤ P.codec.len k) (q : Query) (v : BitVec hashBits)
    (hq : queryLocation P q = some (.inl ⟨k,⟨P.codec.len k - 2,by omega⟩⟩))
    (hv : c q = some v) (hout : P.codec.slice k (P.codec.len k - 2) v = ζ.top k)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) :
    q = ζ.query (.inl ⟨k,⟨P.codec.len k - 2,by omega⟩⟩) := by
  let a : Loc P := .inl ⟨k,⟨P.codec.len k - 2,by omega⟩⟩
  have hmem : v ∈ matchingAnswers ζ a := by
    rw [matchingAnswers_inl, mem_sliceAnswers]
    have he : P.codec.len k - 1 = (P.codec.len k - 2) + 1 := by omega
    unfold Record.top at hout
    rw [he,Record.word_succ ζ k (P.codec.len k - 2) (by omega)] at hout
    exact hout
  by_contra hne
  apply hno
  refine ⟨q,v,hv,?_⟩
  by_cases hh : Hidden d a
  · have hb : Boundary d a := by
      change P.codec.len k - 2 + 1 = d k
      change P.codec.len k - 2 < d k at hh
      have := hd k
      omega
    exact mem_cutTargets_boundary hq hh hb hmem
  · exact mem_cutTargets_exposed hq hh (Ne.symm hne) hmem

/-- An executed special final hash binds all five dependency words. -/
theorem final_binds_dependencies (hP : P.Hyp) (d : Cut) (hd : ValidCut P d)
    (ζ : Record P) (c : Cache) (k : Fin 42) (hlen : 2 ≤ P.codec.len k)
    (u : Fin 6) (hu : owner k = some u) (t : Tops) (x : Word) (v : BitVec hashBits)
    (hv : c ⟨896,P.chainInput t k (P.codec.len k - 2) x⟩ = some v)
    (hout : P.codec.slice k (P.codec.len k - 2) v = ζ.top k)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) : ∀ a ∈ children u, t a = ζ.tops a := by
  have hloc := queryLocation_chainInput hP t k ⟨P.codec.len k - 2,by omega⟩ x
  have he := final_query_binding d hd ζ c k hlen _ v hloc hv hout hno
  rw [Record.query_inl] at he
  have hq := query_inj he
  have ha : P.active k (P.codec.len k - 2) = some u := by
    rw [Params.active, if_pos (by omega), hu]
  simp only [Params.chainInput, ha] at hq
  exact fusion_binds_children t ζ.tops u.isLt x (ζ.word k (P.codec.len k - 2)) _ _ hq

/-- Matching a root answer without a target hit forces its input to be honest. -/
theorem root_query_binding (d : Cut) (ζ : Record P) (c : Cache) (r : Fin 3)
    (q : Query) (v : BitVec hashBits) (hq : queryLocation P q = some (.inr r))
    (hv : c q = some v) (hout : v.extractLsb' 0 128 = (ζ.2 (.inr r)).extractLsb' 0 128)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) : q = ζ.query (.inr r) := by
  by_contra hne
  apply hno
  refine ⟨q,v,hv,mem_cutTargets_exposed hq (not_hidden_inr d r) (Ne.symm hne) ?_⟩
  rw [matchingAnswers_inr,mem_lowAnswers]
  exact hout

theorem Params.rootInput_state_low (P : Params) (t t' : Tops) (r : Fin 3) (hr : r.val ≠ 0)
    (st st' : BitVec 256) (h : P.rootInput t r st = P.rootInput t' r st') :
    st.extractLsb' 0 128 = st'.extractLsb' 0 128 := by
  unfold Params.rootInput at h
  rw [if_neg hr,if_neg hr] at h
  split_ifs at h <;> exact (append_inj ((hashInput_eq_iff _ _ _ _ _ _).mp h).1).1

/-- The three-call root is bound backwards from the public key. -/
theorem root_path_inputs (hP : P.Hyp) (d : Cut) (ζ : Record P) (c : Cache)
    (t : Tops) (S : ℕ → BitVec 256)
    (hc : ∀ r : Fin 3, c ⟨896,P.rootInput t r (S r.val)⟩ = some (S (r.val+1)))
    (hpk : (S 3).extractLsb' 0 128 = ζ.pk)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) :
    ∀ r : Fin 3, P.rootInput t r (S r.val) = P.rootInput ζ.tops r (ζ.rootState r.val) := by
  have h2 := root_query_binding d ζ c 2 _ _ (queryLocation_rootInput hP t 2 (S 2)) (hc 2) hpk hno
  rw [Record.query_inr] at h2
  have e2 := query_inj h2
  have hs2 := P.rootInput_state_low t ζ.tops 2 (by decide) (S 2) (ζ.rootState 2) e2
  rw [show ζ.rootState 2 = ζ.2 (.inr 1) from Record.rootState_succ ζ 1] at hs2
  have h1 := root_query_binding d ζ c 1 _ _ (queryLocation_rootInput hP t 1 (S 1)) (hc 1) hs2 hno
  rw [Record.query_inr] at h1
  have e1 := query_inj h1
  have hs1 := P.rootInput_state_low t ζ.tops 1 (by decide) (S 1) (ζ.rootState 1) e1
  rw [show ζ.rootState 1 = ζ.2 (.inr 0) from Record.rootState_succ ζ 0] at hs1
  have h0 := root_query_binding d ζ c 0 _ _ (queryLocation_rootInput hP t 0 (S 0)) (hc 0) hs1 hno
  rw [Record.query_inr] at h0
  have e0 := query_inj h0
  intro r
  fin_cases r
  · exact e0
  · exact e1
  · exact e2

/-- Twelve root anchors are equal whenever the public key matches without a target hit. -/
theorem root_path_anchors (hP : P.Hyp) (d : Cut) (ζ : Record P) (c : Cache)
    (t : Tops) (S : ℕ → BitVec 256)
    (hc : ∀ r : Fin 3, c ⟨896,P.rootInput t r (S r.val)⟩ = some (S (r.val+1)))
    (hpk : (S 3).extractLsb' 0 128 = ζ.pk)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) : ∀ k ∈ rootSet, t k = ζ.tops k := by
  have he := root_path_inputs hP d ζ c t S hc hpk hno
  let tags : ℕ → Word := fun n => if n = 0 then P.rootMd 0 else if n = 1 then P.rootMd 1 else P.rootMd 2
  apply root_binds t ζ.tops (fun n => (S (n+1)).extractLsb' 0 128)
    (fun n => (ζ.rootState (n+1)).extractLsb' 0 128) tags tags
  intro r hr
  interval_cases r
  · simpa [packet,rootWords,Params.rootInput,tags] using he 0
  · simpa [packet,rootWords,Params.rootInput,tags] using he 1
  · simpa [packet,rootWords,Params.rootInput,tags] using he 2

theorem parents_bounded : ∀ u : Fin 6, ∀ k ∈ parents u, k < 42 := by decide

/-- Actual cached final queries propagate the root binding through both dependency levels. -/
theorem all_tops_bound (hP : P.Hyp) (d : Cut) (hd : ValidCut P d)
    (ζ : Record P) (c : Cache) (I : Index) (t : Tops) (S : ℕ → BitVec 256)
    (hc : ∀ r : Fin 3, c ⟨896,P.rootInput t r (S r.val)⟩ = some (S (r.val+1)))
    (hpk : (S 3).extractLsb' 0 128 = ζ.pk)
    (hactive : ∀ u : Fin 6, ∃ k : Fin 42, k.val ∈ parents u ∧ 0 < P.codec.digit I k)
    (hfinal : ∀ k : Fin 42, 0 < P.codec.digit I k → ∃ x v,
      c ⟨896,P.chainInput t k (P.codec.len k - 2) x⟩ = some v ∧
        P.codec.slice k (P.codec.len k - 2) v = t k.val)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) : ∀ k < 42, t k = ζ.tops k := by
  have hroot := root_path_anchors hP d ζ c t S hc hpk hno
  have hclosed : ∀ n ≤ 6, ∀ k ∈ closure n, t k = ζ.tops k := by
    intro n
    induction n with
    | zero => intro _; exact hroot
    | succ n ih =>
      intro hn k hk
      rcases Finset.mem_union.mp hk with hold | hnew
      · exact ih (by omega) k hold
      · obtain ⟨b,hb,hpos⟩ := hactive ⟨n,by omega⟩
        have hbnd := ih (by omega) b.val (schedule n (by omega) hb)
        obtain ⟨x,v,hv,hout⟩ := hfinal b hpos
        have hlen : 2 ≤ P.codec.len b := by have := hP.codec.digit_lt I b; omega
        have hbtop : ζ.tops b.val = ζ.top b := by
          unfold Record.tops Layer.Params.topAt
          rw [dif_pos b.isLt]
        have he := final_binds_dependencies hP d hd ζ c b hlen ⟨n,by omega⟩
          ((owner_mem b ⟨n,by omega⟩).mpr hb) t x v hv (hout.trans (hbnd.trans hbtop)) hno
        exact he k (List.mem_toFinset.mp hnew)
  intro k hk
  exact hclosed 6 le_rfl k (full_coverage (Finset.mem_range.mpr hk))

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
