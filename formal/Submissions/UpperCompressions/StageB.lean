import Submissions.UpperCompressions.Potentials

/-!
# The second stage

After signing, the attacker's second stage and the verifier run from the cache `extend d' (kc ξ)`.
Coupling with the run from `extend d' (fExp _ ξ)` (hidden points removed, `stageB_iub`), the
events lemma turns an accepted forgery into one of the charged events (`events_stB`), and the
master lemma bounds their probability through `ΦB` (`stageB_some`, `stageB_none`); `stageB` is the
continuation bound handed to the signing lemma.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name


variable (A : Adversary)

/-! ## Auxiliary facts -/

theorem ind_of {p : Prop} (h : p) : ind p = 1 := by rw [ind, if_pos h]

theorem ind_not {p : Prop} (h : ¬ p) : ind p = 0 := by rw [ind, if_neg h]

theorem ind_mono {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  unfold ind
  by_cases hp : p
  · rw [if_pos hp, if_pos (h hp)]
  · rw [if_neg hp]; exact zero_le

theorem E_const_mul {α : Type} (p : ProbComp α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    c * E p g = E p (fun x => c * g x) := by
  rw [E, E, expectedValue_def, expectedValue_def, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun x => by ring

theorem E_finsetSum {α ι : Type} (p : ProbComp α) (s : Finset ι) (g : ι → α → ℝ≥0∞) :
    E p (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, E p (g i) :=
  expectedValue_finsetSum p s g

theorem E_add {α : Type} (p : ProbComp α) (g h : α → ℝ≥0∞) :
    E p (fun x => g x + h x) = E p g + E p h :=
  expectedValue_add p g h

theorem sigOf_none (ξ : Rec) : sigOf ξ none = none := rfl

theorem sigOf_some (ξ : Rec) (η : Nonce) (i : Fin numCuts) :
    sigOf ξ (some (η, i)) = some (η, revealed (setsName i) ξ) := rfl

theorem cutOf?_none : cutOf? none = none := rfl

theorem cutOf?_some (η : Nonce) (i : Fin numCuts) :
    cutOf? (some (η, i)) = some (setsName i) := rfl

theorem idxOf?_none : idxOf? none = none := rfl

theorem idxOf?_some (η : Nonce) (i : Fin numCuts) :
    idxOf? (some (η, i)) = some i.val := rfl

theorem sub_extend_left (c f : Cache) : Cache.Sub c (Cache.extend c f) :=
  fun _ _ h => Cache.extend_apply_of_some h

/-- With no keygen point of `ξ` in `d`, none is in `d'` either: the new entries of `d'` are
encoding entries. -/
theorem signExt_kc_none {m₁ : Message} {d d' : Cache}
    {r : Option (Nonce × Fin numCuts)} (hd' : SignExt m₁ d r d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) {q : Query} (hq : (kc ξ q).isSome) : d' q = none := by
  rcases hq' : d' q with _ | v
  · rfl
  · exfalso
    rcases hdq : d q with _ | u
    · obtain ⟨η, hqe, -⟩ := hd'.2.1 q v hdq hq'
      rw [hqe, kc_enc] at hq
      simp at hq
    · exact hξ ⟨q, hq, by rw [hdq]; rfl⟩

theorem not_hits_fHid_of_signExt {m₁ : Message} {d d' : Cache}
    {r : Option (Nonce × Fin numCuts)} (hd' : SignExt m₁ d r d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits d' (fHid A? ξ) := by
  rintro ⟨q, hq, hq'⟩
  have hkq : (kc ξ q).isSome := by
    obtain ⟨h, p, hp, -, hqp⟩ := (fHid_isSome_iff A? ξ q).1 hq
    exact (kc_isSome_iff ξ q).2 ⟨h, p, hp, hqp⟩
  rw [signExt_kc_none hd' hξ hkq] at hq'
  simp at hq'

theorem not_hits_extend_fExp_fHid {m₁ : Message} {d d' : Cache}
    {r : Option (Nonce × Fin numCuts)} (hd' : SignExt m₁ d r d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
  rw [Cache.hits_extend]
  rintro (h | h)
  · exact not_hits_fHid_of_signExt hd' hξ A? h
  · exact (disjoint_fExp_fHid A? ξ).not_hits h

theorem spr_signExt_iff {m₁ : Message} {d d' : Cache}
    {r : Option (Nonce × Fin numCuts)} (hd' : SignExt m₁ d r d')
    (ξ : Rec) : Spr d' ξ ↔ Spr d ξ := by
  constructor
  · rintro ⟨h, p, hp, u, hu, htag, w, hw, htr⟩
    refine ⟨h, p, hp, u, hu, htag, w, ?_, htr⟩
    rcases hdq : d ⟨p.len, u⟩ with _ | v
    · exfalso
      obtain ⟨η, hqe, -⟩ := hd'.2.1 _ w hdq hw
      exact mk_ne_encQuery hp u _ hqe
    · rw [hd'.1 _ _ hdq] at hw
      exact hw
  · exact Spr.mono hd'.1

theorem spr_extend_fExp_iff {m₁ : Message} {d d' : Cache}
    {r : Option (Nonce × Fin numCuts)} (hd' : SignExt m₁ d r d')
    (ξ : Rec) (A? : Option (Finset Name)) :
    Spr (Cache.extend d' (fExp A? ξ)) ξ ↔ Spr d ξ := by
  constructor
  · intro hs
    rcases spr_of_extend hs with hs | hs
    · exact (spr_signExt_iff hd' ξ).1 hs
    · exact absurd hs (not_spr_fExp A? ξ)
  · intro hs
    exact Spr.mono (sub_extend_left d' _) ((spr_signExt_iff hd' ξ).2 hs)

theorem not_idxPost_extend_fExp (d' : Cache) (ξ : Rec) (A? : Option (Finset Name))
    (i : ℕ) : ¬ IdxPost d' (Cache.extend d' (fExp A? ξ)) i :=
  not_idxPost_extend_of_enc_none d' (fExp A? ξ) (fun u => fExp_enc A? ξ u) i

theorem encCount_extend_of_enc_none (d f : Cache)
    (hf : ∀ u : EncInput, f (encQuery u) = none) :
    encCount (Cache.extend d f) = encCount d := by
  unfold encCount
  refine congrArg Finset.card (Finset.filter_congr fun u _ => ?_)
  rw [Cache.extend_apply, hf u, Option.or_none]

theorem Inv_extend_fExp (d' : Cache) (ξ : Rec) (A? : Option (Finset Name)) (b : ℕ) :
    Inv (Cache.extend d' (fExp A? ξ)) b ↔ Inv d' b := by
  unfold Inv
  rw [encCount_extend_of_enc_none d' (fExp A? ξ) (fun u => fExp_enc A? ξ u)]

/-! ## Stage B -/

theorem stB_support (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option Signature)
    (c : Cache) : ∀ p ∈ support (run (stB A pk m₁ st σ) c), Cache.Sub c p.2 ∧
      (p.1 = true → ∃ m₂ σ₂, σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂) ∧
        ∃ w, p.2 (encQuery (m₂ ++ σ₂.1)) = some w ∧
          ∃ hi : idxOf w < numCuts,
            σ₂.2.length = graph.revealBits (fins (setsName ⟨_, hi⟩)) ∧
            ∃ y : graph.Assignment,
              graph.ReconEqs p.2 (fins (setsName ⟨_, hi⟩))
                (graph.decode (fins (setsName ⟨_, hi⟩)) σ₂.2) y ∧ trunc (yv y rh) = pk) := by
  intro p hp
  unfold stB at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨⟨m₂, σ₂⟩, c₁⟩, h₁, hp⟩ := hp
  have hsub₁ := sub_of_mem_support_run _ c _ h₁
  dsimp only at hp hsub₁
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨ok, c₂⟩, h₂, hp⟩ := hp
  obtain ⟨hsub₂, hver⟩ := verify_support forestScheme pk m₂ σ₂ c₁ ⟨ok, c₂⟩ h₂
  dsimp only at hp hsub₂ hver
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hok
  obtain ⟨hok, hne⟩ := hok
  obtain ⟨w, hw, hi, hlen, y, hy, hpk⟩ := hver hok
  refine ⟨m₂, σ₂, hne, w, hw, hi, hlen, y, hy, ?_⟩
  exact (trunc_cast_eq (graph_len_fin rh) (y rh.fin)).trans hpk

/-- An accepted forgery is one of the charged events. -/
theorem events_stB (ξ : Rec) (r : Option (Nonce × Fin numCuts)) (m₁ : Message) (st : A.State)
    (d d' c : Cache) (hd' : SignExt m₁ d r d') (hc : Cache.Sub d' c)
    (p : Bool × Cache) (hp : p ∈ support (run (stB A (pkOf ξ) m₁ st (sigOf ξ r)) c))
    (hok : p.1 = true) :
    Cache.Hits p.2 (fHid (cutOf? r) ξ) ∨ Spr p.2 ξ ∨
      ∃ η i, r = some (η, i) ∧ (IdxPost d' p.2 i.val ∨ IdxPre d (m₁ ++ η) i.val) := by
  obtain ⟨hcp, h⟩ := stB_support A (pkOf ξ) m₁ st (sigOf ξ r) c p hp
  obtain ⟨m₂, σ₂, hne, w, hw, hi, hlen, y, hy, hacc⟩ := h hok
  rcases r with _ | ⟨η, i⟩
  · -- signing failed: everything is hidden
    rcases events_none (isCut_setsName ⟨_, hi⟩) hy hacc with hs | hh
    · exact Or.inr (Or.inl hs)
    · left
      rw [cutOf?_none, fHid_none]
      exact hh
  · by_cases hji : (⟨idxOf w, hi⟩ : Fin (2 ^ 115)) = i
    · -- the forgery uses the signed disclosure set
      have hA : setsName ⟨idxOf w, hi⟩ = setsName i := congrArg setsName hji
      rw [hA] at hy hlen
      by_cases hu : m₂ ++ σ₂.1 = m₁ ++ η
      · -- same encoding input: same message and nonce, different revealed values
        obtain ⟨hm, hσ⟩ := bv_append_inj hu
        right; left
        refine events_same (isCut_setsName i) hy hacc hlen ?_
        intro heq
        apply hne
        rw [sigOf_some, Option.map_some, hm]
        unfold revealed
        rw [← heq, ← hσ]
      · -- a different encoding input with the signed index
        right; right
        refine ⟨η, i, rfl, ?_⟩
        rcases hd'q : d' (encQuery (m₂ ++ σ₂.1)) with _ | w''
        · left
          exact ⟨m₂ ++ σ₂.1, hd'q, w, hw, congrArg Fin.val hji⟩
        · have hw'' : w'' = w := Option.some.inj (((hc.trans hcp) _ _ hd'q).symm.trans hw)
          rcases hdq : d (encQuery (m₂ ++ σ₂.1)) with _ | w₃
          · exfalso
            obtain ⟨η', hqe, hr⟩ := hd'.2.1 _ _ hdq hd'q
            have hr' := hr (by rw [hw'']; exact hi)
            simp only [Option.some.injEq, Prod.mk.injEq] at hr'
            obtain ⟨rfl, -⟩ := hr'
            exact hu (encQuery_inj hqe)
          · right
            refine ⟨m₂ ++ σ₂.1, hu, w₃, hdq, ?_⟩
            have h3 := hd'.1 _ _ hdq
            rw [hd'q] at h3
            rw [← Option.some.inj h3, hw'']
            exact congrArg Fin.val hji
    · -- the forgery uses a different disclosure set of the same cost
      have hne' : setsName i ≠ setsName ⟨_, hi⟩ := fun h => hji (setsName_injective h).symm
      rcases events_ne (isCut_setsName i) (isCut_setsName ⟨_, hi⟩)
          ((cost_setsName i).trans (cost_setsName _).symm) hne' hy hacc with hs | hh
      · exact Or.inr (Or.inl hs)
      · left
        exact hh

/-- The second stage, coupled to the run without the hidden points. -/
theorem stageB_iub (ξ : Rec) (r : Option (Nonce × Fin numCuts)) (m₁ : Message)
    (st : A.State) (d d' : Cache) (hξ : ¬ Cache.Hits d (kc ξ)) (hd' : SignExt m₁ d r d') :
    E (run (stB A (pkOf ξ) m₁ st (sigOf ξ r)) (Cache.extend d' (kc ξ))) g ≤
      E (run (stB A (pkOf ξ) m₁ st (sigOf ξ r)) (Cache.extend d' (fExp (cutOf? r) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (cutOf? r) ξ)) + ind (Spr p.2 ξ) +
          ind (∃ i, idxOf? r = some i ∧ IdxPost d' p.2 i) +
          ind (∃ η i, r = some (η, i) ∧ IdxPre d (m₁ ++ η) i.val)) := by
  have hkc : Cache.extend d' (kc ξ) =
      Cache.extend (Cache.extend d' (fExp (cutOf? r) ξ)) (fHid (cutOf? r) ξ) := by
    rw [Cache.extend_assoc, extend_fExp_fHid]
  have hdisj : Cache.Disjoint (Cache.extend d' (fExp (cutOf? r) ξ)) (fHid (cutOf? r) ξ) := by
    intro q hq
    have hkq : (kc ξ q).isSome := by
      obtain ⟨h, p, hp, -, hqp⟩ := (fHid_isSome_iff _ ξ q).1 hq
      exact (kc_isSome_iff ξ q).2 ⟨h, p, hp, hqp⟩
    rw [Cache.extend_apply, signExt_kc_none hd' hξ hkq, Option.none_or]
    exact disjoint_fExp_fHid _ ξ q hq
  rw [hkc]
  refine (iub (stB A (pkOf ξ) m₁ st (sigOf ξ r)) (fHid (cutOf? r) ξ) g g_le_one _
    hdisj).trans ?_
  refine expectedValue_mono_of_support fun p hp => ?_
  by_cases hh : Cache.Hits p.2 (fHid (cutOf? r) ξ)
  · rw [if_pos hh]
    exact (ind_of hh).symm.le.trans (le_add_right (le_add_right le_self_add))
  · rw [if_neg hh]
    by_cases hok : p.1 = true
    · have hg : g (p.1, Cache.extend p.2 (fHid (cutOf? r) ξ)) = 1 := by
        show (if p.1 = true then (1 : ℝ≥0∞) else 0) = 1
        rw [if_pos hok]
      rw [hg]
      rcases events_stB A ξ r m₁ st d d' _ hd' (sub_extend_left d' _) p hp hok with
        h | h | ⟨η, i, hr, h | h⟩
      · exact absurd h hh
      · exact (ind_of h).symm.le.trans (le_add_right (le_add_right (le_add_left le_rfl)))
      · have h' : ∃ j, idxOf? r = some j ∧ IdxPost d' p.2 j :=
          ⟨i.val, by rw [hr]; rfl, h⟩
        exact (ind_of h').symm.le.trans (le_add_right (le_add_left le_rfl))
      · have h' : ∃ η i, r = some (η, i) ∧ IdxPre d (m₁ ++ η) i.val := ⟨η, i, hr, h⟩
        exact (ind_of h').symm.le.trans (le_add_left le_rfl)
    · have hg : g (p.1, Cache.extend p.2 (fHid (cutOf? r) ξ)) = 0 := by
        show (if p.1 = true then (1 : ℝ≥0∞) else 0) = 0
        rw [if_neg hok]
      rw [hg]
      exact zero_le

/-- The public key of every record of `T ⊆ fiberA pk`. -/
theorem pkOf_of_subset_fiberA {pk : BitVec 128} {T : Finset Rec} (hT : T ⊆ fiberA pk) :
    ∀ ξ ∈ T, pkOf ξ = pk := by
  rw [Finset.subset_iff] at hT
  simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  intro ξ hξ
  exact hT hξ

/-- The second stage for the records `T` of a public key: signing succeeded. -/
theorem stageB_some (pk : BitVec 128) (m₁ : Message) (st : A.State) (d : Cache)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (η : Nonce) (i : Fin numCuts) (d' : Cache) (hd' : SignExt m₁ d (some (η, i)) d')
    (b'' : ℕ) (hI : Inv d' b'')
    (hB : ∀ ξ ∈ T, CostAtMost (stB A pk m₁ st (sigOf ξ (some (η, i)))) b'') :
    ∑ ξ ∈ T, w * E (run (stB A pk m₁ st (sigOf ξ (some (η, i))))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
          ind (IdxPost d' p.2 i.val)) ≤
      ∑ ξ ∈ T, w * ind (Spr d ξ) + κ * sumW (fiberA pk) * b'' := by
  have hTpk : ∀ ξ ∈ T, pkOf ξ = pk := pkOf_of_subset_fiberA hT
  -- regroup the records by their public data
  have hmaps : ∀ ξ ∈ T, dataOf (setsName i) ξ ∈ T.image (dataOf (setsName i)) :=
    fun ξ hξ => Finset.mem_image_of_mem _ hξ
  have hregroup : ∀ f : Rec → ℝ≥0∞, ∑ ξ ∈ T, f ξ =
      ∑ dt ∈ T.image (dataOf (setsName i)), ∑ ξ ∈ T with dataOf (setsName i) ξ = dt, f ξ :=
    fun f => (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  rw [hregroup, hregroup (fun ξ => w * ind (Spr d ξ))]
  -- the bound on one fiber
  have hfiber : ∀ dt ∈ T.image (dataOf (setsName i)),
      ∑ ξ ∈ T with dataOf (setsName i) ξ = dt, w * E (run (stB A pk m₁ st (sigOf ξ (some (η, i))))
          (Cache.extend d' (fExp (some (setsName i)) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
            ind (IdxPost d' p.2 i.val)) ≤
        ∑ ξ ∈ T with dataOf (setsName i) ξ = dt, w * ind (Spr d ξ) +
          κ * sumW (fiberB (setsName i) dt) * b'' := by
    rintro ⟨pk', rev', fe'⟩ hdt
    obtain ⟨ξ₀, hξ₀T, hξ₀⟩ := Finset.mem_image.1 hdt
    have hdata : ∀ ξ ∈ T.filter (fun ξ => dataOf (setsName i) ξ = (pk', rev', fe')),
        ξ ∈ T ∧ pkOf ξ = pk' ∧ revealed (setsName i) ξ = rev' ∧
          fExp (some (setsName i)) ξ = fe' := by
      intro ξ hξ
      rw [Finset.mem_filter] at hξ
      obtain ⟨hξT, hξd⟩ := hξ
      simp only [dataOf, Prod.mk.injEq] at hξd
      exact ⟨hξT, hξd⟩
    have hdata₀ : pkOf ξ₀ = pk' ∧ revealed (setsName i) ξ₀ = rev' ∧
        fExp (some (setsName i)) ξ₀ = fe' := by
      simp only [dataOf, Prod.mk.injEq] at hξ₀
      exact hξ₀
    have hTsub : T.filter (fun ξ => dataOf (setsName i) ξ = (pk', rev', fe')) ⊆
        fiberB (setsName i) (pk', rev', fe') := by
      intro ξ hξ
      rw [Finset.mem_filter] at hξ
      simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hξ.2
    -- every record of the fiber runs the same computation from the same cache
    have hrun : ∀ ξ ∈ T.filter (fun ξ => dataOf (setsName i) ξ = (pk', rev', fe')),
        run (stB A pk m₁ st (sigOf ξ (some (η, i))))
            (Cache.extend d' (fExp (some (setsName i)) ξ)) =
          run (stB A pk m₁ st (some (η, rev'))) (Cache.extend d' fe') := by
      intro ξ hξ
      obtain ⟨-, -, hrev, hfexp⟩ := hdata ξ hξ
      rw [sigOf_some, hrev, hfexp]
    have hsum : ∑ ξ ∈ T with dataOf (setsName i) ξ = (pk', rev', fe'),
          w * E (run (stB A pk m₁ st (sigOf ξ (some (η, i))))
            (Cache.extend d' (fExp (some (setsName i)) ξ)))
            (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
              ind (IdxPost d' p.2 i.val)) =
        E (run (stB A pk m₁ st (some (η, rev'))) (Cache.extend d' fe'))
          (fun p => ∑ ξ ∈ T with dataOf (setsName i) ξ = (pk', rev', fe'),
            w * (ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
              ind (IdxPost d' p.2 i.val))) := by
      rw [E_finsetSum]
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      rw [hrun ξ hξ, E_const_mul]
    have hF : ∀ (x : Bool) (c : Cache),
        ∑ ξ ∈ T with dataOf (setsName i) ξ = (pk', rev', fe'),
            w * (ind (Cache.Hits c (fHid (some (setsName i)) ξ)) + ind (Spr c ξ) +
              ind (IdxPost d' c i.val)) ≤
          ΦB (T.filter (fun ξ => dataOf (setsName i) ξ = (pk', rev', fe'))) (some (setsName i)) d'
            (some i.val) c := by
      intro x c
      unfold ΦB
      refine Finset.sum_le_sum fun ξ _ => ?_
      exact mul_le_mul_right (add_le_add_right (ind_mono fun h => ⟨i.val, rfl, h⟩) _) _
    have hI' : Inv (Cache.extend d' fe') b'' := by
      rw [← hdata₀.2.2, Inv_extend_fExp]; exact hI
    have hB' : CostAtMost (stB A pk m₁ st (some (η, rev'))) b'' := by
      have := hB ξ₀ hξ₀T
      rwa [sigOf_some, hdata₀.2.1] at this
    have hmaster := master_single (κ * sumW (fiberB (setsName i) (pk', rev', fe')))
      (ΦB (T.filter (fun ξ => dataOf (setsName i) ξ = (pk', rev', fe'))) (some (setsName i)) d'
        (some i.val))
      Inv Inv_fresh Inv_cached (ΦB_charge_some (isCut_setsName i) (pk', rev', fe') hTsub d' i.val)
      (stB A pk m₁ st (some (η, rev')))
      (fun _ c => ∑ ξ ∈ T with dataOf (setsName i) ξ = (pk', rev', fe'),
        w * (ind (Cache.Hits c (fHid (some (setsName i)) ξ)) + ind (Spr c ξ) +
          ind (IdxPost d' c i.val)))
      hF (Cache.extend d' fe') b'' hI' hB'
    have hΦ : ΦB (T.filter (fun ξ => dataOf (setsName i) ξ = (pk', rev', fe'))) (some (setsName i)) d'
        (some i.val) (Cache.extend d' fe') =
        ∑ ξ ∈ T with dataOf (setsName i) ξ = (pk', rev', fe'), w * ind (Spr d ξ) := by
      unfold ΦB
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      obtain ⟨hξT, -, -, hfexp⟩ := hdata ξ hξ
      rw [← hfexp]
      have h3 : ¬ ∃ j, some i.val = some j ∧
          IdxPost d' (Cache.extend d' (fExp (some (setsName i)) ξ)) j :=
        fun ⟨j, _, h⟩ => not_idxPost_extend_fExp d' ξ _ j h
      rw [ind_not (not_hits_extend_fExp_fHid hd' (hTd ξ hξT) (some (setsName i))),
        spr_extend_fExp_iff hd' ξ (some (setsName i)), ind_not h3, zero_add, add_zero]
    rw [hsum]
    exact hmaster.trans (by rw [hΦ])
  -- the weights of the fibers add up to at most the weight of the public key
  have hsumW : ∑ dt ∈ T.image (dataOf (setsName i)), sumW (fiberB (setsName i) dt) ≤
      sumW (fiberA pk) := by
    have hsub : ∀ dt ∈ T.image (dataOf (setsName i)), fiberB (setsName i) dt ⊆
        ((fiberA pk).filter fun ξ => dataOf (setsName i) ξ ∈ T.image (dataOf (setsName i))).filter
          fun ξ => dataOf (setsName i) ξ = dt := by
      intro dt hdt
      obtain ⟨ξ₀, hξ₀T, hξ₀⟩ := Finset.mem_image.1 hdt
      have hpk₀ : pkOf ξ₀ = pk := hTpk ξ₀ hξ₀T
      intro ξ hξ
      simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and] at hξ
      have hpk : pkOf ξ = pkOf ξ₀ := by
        have := hξ.trans hξ₀.symm
        simp only [dataOf, Prod.mk.injEq] at this
        exact this.1
      simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨hpk.trans hpk₀, ?_⟩, hξ⟩
      rw [hξ]
      exact hdt
    calc ∑ dt ∈ T.image (dataOf (setsName i)), sumW (fiberB (setsName i) dt)
        ≤ ∑ dt ∈ T.image (dataOf (setsName i)),
            ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf (setsName i) ξ ∈ T.image (dataOf (setsName i)))
              with dataOf (setsName i) ξ = dt, w :=
          Finset.sum_le_sum fun dt hdt => Finset.sum_le_sum_of_subset (hsub dt hdt)
      _ = ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf (setsName i) ξ ∈ T.image (dataOf (setsName i))),
            w :=
          Finset.sum_fiberwise_of_maps_to (fun ξ hξ => (Finset.mem_filter.1 hξ).2) _
      _ ≤ sumW (fiberA pk) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add_right ?_ _
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  exact mul_le_mul_left (mul_le_mul_right hsumW κ) _

/-- The second stage for the records `T` of a public key: signing failed. -/
theorem stageB_none (pk : BitVec 128) (m₁ : Message) (st : A.State) (d : Cache)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (d' : Cache) (hd' : SignExt m₁ d none d') (b'' : ℕ) (hI : Inv d' b'')
    (hB : CostAtMost (stB A pk m₁ st none) b'') :
    ∑ ξ ∈ T, w * E (run (stB A pk m₁ st none) d')
        (fun p => ind (Cache.Hits p.2 (kc ξ)) + ind (Spr p.2 ξ)) ≤
      ∑ ξ ∈ T, w * ind (Spr d ξ) + κ * sumW (fiberA pk) * b'' := by
  have hsum : ∑ ξ ∈ T, w * E (run (stB A pk m₁ st none) d')
        (fun p => ind (Cache.Hits p.2 (kc ξ)) + ind (Spr p.2 ξ)) =
      E (run (stB A pk m₁ st none) d')
        (fun p => ∑ ξ ∈ T, w * (ind (Cache.Hits p.2 (kc ξ)) + ind (Spr p.2 ξ))) := by
    rw [E_finsetSum]
    exact Finset.sum_congr rfl fun ξ _ => E_const_mul _ _ _
  have hF : ∀ (x : Bool) (c : Cache),
      ∑ ξ ∈ T, w * (ind (Cache.Hits c (kc ξ)) + ind (Spr c ξ)) ≤ ΦB T none d' none c := by
    intro x c
    unfold ΦB
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [fHid_none]
    exact mul_le_mul_right le_self_add _
  have hmaster := master_single (κ * sumW (fiberA pk)) (ΦB T none d' none) Inv
    Inv_fresh Inv_cached (ΦB_charge_none pk hT d') (stB A pk m₁ st none)
    (fun _ c => ∑ ξ ∈ T, w * (ind (Cache.Hits c (kc ξ)) + ind (Spr c ξ))) hF d' b'' hI hB
  have hΦ : ΦB T none d' none d' = ∑ ξ ∈ T, w * ind (Spr d ξ) := by
    unfold ΦB
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    have h3 : ¬ ∃ j, (none : Option ℕ) = some j ∧ IdxPost d' d' j := by
      rintro ⟨j, h, -⟩; cases h
    rw [ind_not (not_hits_fHid_of_signExt hd' (hTd ξ hξ) none), spr_signExt_iff hd',
      ind_not h3, zero_add, add_zero]
  rw [hsum]
  exact hmaster.trans (by rw [hΦ])

/-- The second stage: the continuation bound handed to the signing lemma. -/
theorem stageB (pk : BitVec 128) (m₁ : Message) (st : A.State) (d : Cache) (T : Finset Rec)
    (hT : T ⊆ fiberA pk) (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (r : Option (Nonce × Fin numCuts)) (d' : Cache) (hd' : SignExt m₁ d r d') (b'' : ℕ)
    (hI : Inv d' b'') (hB : ∀ ξ ∈ T, CostAtMost (stB A pk m₁ st (sigOf ξ r)) b'') :
    ∑ ξ ∈ T, w * E (run (stB A pk m₁ st (sigOf ξ r)) (Cache.extend d' (kc ξ))) g ≤
      ∑ ξ ∈ T, w * ind (Spr d ξ) +
        sumW T * ind (∃ η i, r = some (η, i) ∧ IdxPre d (m₁ ++ η) i.val) +
        κ * sumW (fiberA pk) * b'' := by
  have hTpk : ∀ ξ ∈ T, pkOf ξ = pk := pkOf_of_subset_fiberA hT
  -- couple every record's run with the run without the hidden points
  have hstep : ∀ ξ ∈ T,
      w * E (run (stB A pk m₁ st (sigOf ξ r)) (Cache.extend d' (kc ξ))) g ≤
        w * E (run (stB A pk m₁ st (sigOf ξ r)) (Cache.extend d' (fExp (cutOf? r) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (cutOf? r) ξ)) + ind (Spr p.2 ξ) +
            ind (∃ i, idxOf? r = some i ∧ IdxPost d' p.2 i)) +
        w * ind (∃ η i, r = some (η, i) ∧ IdxPre d (m₁ ++ η) i.val) := by
    intro ξ hξ
    rw [← mul_add, ← hTpk ξ hξ]
    refine mul_le_mul_right ((stageB_iub A ξ r m₁ st d d' (hTd ξ hξ) hd').trans ?_) _
    rw [E_add]
    exact add_le_add_right (E_const_le _ _) _
  -- the master lemma on the run without the hidden points
  have hmain : ∑ ξ ∈ T, w * E (run (stB A pk m₁ st (sigOf ξ r))
        (Cache.extend d' (fExp (cutOf? r) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (cutOf? r) ξ)) + ind (Spr p.2 ξ) +
          ind (∃ i, idxOf? r = some i ∧ IdxPost d' p.2 i)) ≤
      ∑ ξ ∈ T, w * ind (Spr d ξ) + κ * sumW (fiberA pk) * b'' := by
    rcases r with _ | ⟨η, i⟩
    · rcases T.eq_empty_or_nonempty with rfl | ⟨ξ₀, hξ₀⟩
      · simp
      · refine le_trans ?_ (stageB_none A pk m₁ st d T hT hTd d' hd' b'' hI (hB ξ₀ hξ₀))
        refine Finset.sum_le_sum fun ξ _ => ?_
        rw [sigOf_none, cutOf?_none, idxOf?_none, fExp_none, Cache.extend_empty, fHid_none]
        refine mul_le_mul_right (E_mono _ fun p => ?_) _
        have h3 : ¬ ∃ j, (none : Option ℕ) = some j ∧ IdxPost d' p.2 j := by
          rintro ⟨j, h, -⟩; cases h
        rw [ind_not h3, add_zero]
    · refine le_trans ?_ (stageB_some A pk m₁ st d T hT hTd η i d' hd' b'' hI hB)
      refine Finset.sum_le_sum fun ξ _ => ?_
      rw [cutOf?_some, idxOf?_some]
      refine mul_le_mul_right (E_mono _ fun p => ?_) _
      refine add_le_add_right (ind_mono ?_) _
      rintro ⟨j, hj, h⟩
      rw [Option.some.inj hj]
      exact h
  calc ∑ ξ ∈ T, w * E (run (stB A pk m₁ st (sigOf ξ r)) (Cache.extend d' (kc ξ))) g
      ≤ ∑ ξ ∈ T, (w * E (run (stB A pk m₁ st (sigOf ξ r))
            (Cache.extend d' (fExp (cutOf? r) ξ)))
            (fun p => ind (Cache.Hits p.2 (fHid (cutOf? r) ξ)) + ind (Spr p.2 ξ) +
              ind (∃ i, idxOf? r = some i ∧ IdxPost d' p.2 i)) +
          w * ind (∃ η i, r = some (η, i) ∧ IdxPre d (m₁ ++ η) i.val)) :=
        Finset.sum_le_sum hstep
    _ = ∑ ξ ∈ T, w * E (run (stB A pk m₁ st (sigOf ξ r))
            (Cache.extend d' (fExp (cutOf? r) ξ)))
            (fun p => ind (Cache.Hits p.2 (fHid (cutOf? r) ξ)) + ind (Spr p.2 ξ) +
              ind (∃ i, idxOf? r = some i ∧ IdxPost d' p.2 i)) +
          sumW T * ind (∃ η i, r = some (η, i) ∧ IdxPre d (m₁ ++ η) i.val) := by
        rw [Finset.sum_add_distrib, sumW, Finset.sum_mul]
    _ ≤ (∑ ξ ∈ T, w * ind (Spr d ξ) + κ * sumW (fiberA pk) * b'') +
          sumW T * ind (∃ η i, r = some (η, i) ∧ IdxPre d (m₁ ++ η) i.val) :=
        add_le_add_left hmain _
    _ = _ := add_right_comm _ _ _

end Forest

end OptimalOTS
