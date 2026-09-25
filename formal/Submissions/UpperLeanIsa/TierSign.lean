import Submissions.UpperLeanIsa.TierRow
import Submissions.UpperLeanIsa.TierKernel

/-!
# The rarest-cut signer

`signTierLoop M k tried β` makes `k` further trials on the row of the extended message `M`, each
at a fresh untried nonce, and keeps the best trial `β`: a trial replaces it exactly when its index
is accepted and strictly lighter (`upd`). Every run makes all its trials, so signing costs
exactly two compressions per trial (`signTierLoop_cost`, S0).

The analysis of a run from a cache `d`:

* `Reach`: the invariant of the states of a run (entries added only at tried nonces, the best
  trial cached and accepted, no tried trial better than the best), and `signTier_ext` (S1);
* `run_signTierLoop_extend`: entries at non-index points are irrelevant (S2);
* `trialAvg`: the average of a function of one trial; `loop_value` (lemma V) bounds the value
  of a run by any function `U` that one trial does not increase;
* the one-trial bounds under `RowGood` (T1): `trialAvg_tier_ge`, `trialAvg_fresh_cls`,
  `trialAvg_nonce`;
* the winner law: `win_le` (K1, K2), `win_sc_le` (K3), `tail_le` (K4), `kappaB_le` (K5).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials

namespace Params

variable (P : Params)

/-! ## The loop -/

/-- The rarest-cut signing loop of row `M`: `k` further trials outside `tried`, best trial `β`. -/
def signTierLoop (M : EMessage) :
    ℕ → Finset Nonce → Option (Nonce × Index) → OracleComp Spec (Option (Nonce × Index))
  | 0, _, β => pure β
  | k + 1, tried, β =>
    if hc : 0 < (Finset.univ \ tried).card then do
      let j ← (liftM (Spec.query (.inl ((Finset.univ \ tried).card - 1))) :
        OracleComp Spec (Fin ((Finset.univ \ tried).card - 1 + 1)))
      let w ← (liftM (Spec.query (.inr (P.encQuery (M ++ nonceOf tried hc j)))) :
        OracleComp Spec (BitVec hashBits))
      signTierLoop M k (insert (nonceOf tried hc j) tried)
        (P.upd β (nonceOf tried hc j) (indexSlice w))
    else pure β

/-- Rarest-cut signing of row `M`: `trials` trials. -/
def signTier (M : EMessage) : OracleComp Spec (Option (Nonce × Index)) :=
  P.signTierLoop M trials ∅ none

/-- One trial at nonce `η`: the index query, then the remaining trials. -/
def tierBody (M : EMessage) (k : ℕ) (tried : Finset Nonce) (β : Option (Nonce × Index))
    (η : Nonce) : OracleComp Spec (Option (Nonce × Index)) :=
  (liftM (Spec.query (.inr (P.encQuery (M ++ η)))) : OracleComp Spec (BitVec hashBits)) >>=
    fun w => P.signTierLoop M k (insert η tried) (P.upd β η (indexSlice w))

theorem signTierLoop_succ (M : EMessage) (k : ℕ) (tried : Finset Nonce)
    (β : Option (Nonce × Index)) (hc : 0 < (Finset.univ \ tried).card) :
    P.signTierLoop M (k + 1) tried β =
      (liftM (Spec.query (.inl ((Finset.univ \ tried).card - 1))) :
          OracleComp Spec (Fin ((Finset.univ \ tried).card - 1 + 1))) >>= fun j =>
        P.tierBody M k tried β (nonceOf tried hc j) := by
  rw [signTierLoop, dif_pos hc]
  rfl

/-- The signing loop of the scheme is the image of the tier loop under the signature. -/
theorem signLoop_eq_map (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (β : Option (Nonce × Index)),
      P.signLoop sk m k tried β = P.sigOf sk <$> P.signTierLoop (emsg m sk.pk) k tried β := by
  intro k
  induction k with
  | zero => intro tried β; simp [signLoop, signTierLoop]
  | succ k ih =>
    intro tried β
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signLoop_succ sk m k tried β hc, P.signTierLoop_succ _ k tried β hc, map_bind]
      refine bind_congr fun j => ?_
      unfold loopBody tierBody
      rw [P.encQuery_emsg, map_bind]
      refine bind_congr fun w => ?_
      unfold afterHash
      exact ih _ _
    · rw [signLoop, signTierLoop, dif_neg hc, dif_neg hc, map_pure]

/-- Signing encodes the revealed words at the best trial of `signTier`. -/
theorem sign_eq_map (sk : SecretKey) (m : Message) :
    P.sign sk m = P.sigOf sk <$> P.signTier (emsg m sk.pk) := by
  rw [sign_eq]
  exact P.signLoop_eq_map sk m trials ∅ none

theorem card_pool {tried : Finset Nonce} :
    (Finset.univ \ tried).card = 2 ^ 127 - tried.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_bitVec]

theorem pool_pos {tried : Finset Nonce} (h : tried.card < trials) :
    0 < (Finset.univ \ tried).card := by
  rw [card_pool]
  unfold trials at h
  omega

theorem queryCost_enc (u : EncInput) : queryCost (.inr (P.encQuery u)) = 2 := by
  norm_num [Params.encQuery, queryCost, blockCost, blockBits]

/-! ## Cost (S0) -/

/-- Every run makes all its trials: a budget `b` for signing and the continuation leaves
`b - 2 k` to the continuation. -/
theorem signTierLoop_cost {γ : Type} (M : EMessage) (kont : Option (Nonce × Index) → OracleComp Spec γ) :
    ∀ (k : ℕ) (tried : Finset Nonce) (β : Option (Nonce × Index)) (b : ℕ),
      tried.card + k ≤ trials → CostAtMost (P.signTierLoop M k tried β >>= kont) b →
      2 * k ≤ b ∧ ∀ c, ∀ p ∈ support (run (P.signTierLoop M k tried β) c),
        CostAtMost (kont p.1) (b - 2 * k) := by
  intro k
  induction k with
  | zero =>
    intro tried β b _ hB
    refine ⟨Nat.zero_le _, fun c p hp => ?_⟩
    rw [signTierLoop, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [signTierLoop, pure_bind] at hB
    simpa using hB
  | succ k ih =>
    intro tried β b hk hB
    have hc : 0 < (Finset.univ \ tried).card := pool_pos (by omega)
    rw [P.signTierLoop_succ M k tried β hc] at hB ⊢
    have hB1 := fun j => costAtMost_inl_bind _ _ _ hB j
    have hB2 : ∀ j, queryCost (.inr (P.encQuery (M ++ nonceOf tried hc j))) ≤ b ∧
        ∀ w, CostAtMost (P.signTierLoop M k (insert (nonceOf tried hc j) tried)
          (P.upd β (nonceOf tried hc j) (indexSlice w)) >>= kont)
          (b - queryCost (.inr (P.encQuery (M ++ nonceOf tried hc j)))) := fun j =>
      costAtMost_inr_bind _ _ _ (hB1 j)
    have hins : ∀ j, (insert (nonceOf tried hc j) tried).card + k ≤ trials := fun j => by
      rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.1 (nonceOf_mem tried hc j)).2]
      omega
    have j₀ : Fin ((Finset.univ \ tried).card - 1 + 1) := ⟨0, Nat.succ_pos _⟩
    obtain ⟨hc₀, hw₀⟩ := hB2 j₀
    rw [P.queryCost_enc] at hc₀ hw₀
    have hk₀ := (ih _ _ _ (hins j₀) (hw₀ 0)).1
    refine ⟨by omega, fun c p hp => ?_⟩
    obtain ⟨j, hp⟩ := mem_support_run_inl hp
    simp only [tierBody] at hp
    obtain ⟨-, hw⟩ := hB2 j
    rw [P.queryCost_enc] at hw
    have hsub : b - 2 - 2 * k = b - 2 * (k + 1) := by omega
    rcases hdq : c (P.encQuery (M ++ nonceOf tried hc j)) with _ | w
    · obtain ⟨w, hp⟩ := mem_support_run_inr_none hdq hp
      have := (ih _ _ _ (hins j) (hw w)).2 _ p hp
      rwa [hsub] at this
    · have hp := mem_support_run_inr_some hdq hp
      have := (ih _ _ _ (hins j) (hw w)).2 _ p hp
      rwa [hsub] at this

/-! ## The states of a run (S1) -/

/-- A state of a run of row `M` from the cache `d`: tried nonces `tried`, best trial `β`,
cache `c`. -/
structure Reach (d : Cache) (M : EMessage) (tried : Finset Nonce) (β : Option (Nonce × Index))
    (c : Cache) : Prop where
  sub : Cache.Sub d c
  new : ∀ q w, d q = none → c q = some w → ∃ η ∈ tried, q = P.encQuery (M ++ η)
  best : ∀ b, β = some b → b.1 ∈ tried ∧ P.Accepted b.2 ∧
    ∃ w, c (P.encQuery (M ++ b.1)) = some w ∧ indexSlice w = b.2
  min : ∀ η ∈ tried, ∀ w, c (P.encQuery (M ++ η)) = some w → P.better (indexSlice w) β = false

variable {P}

theorem reach_init (d : Cache) (M : EMessage) : P.Reach d M ∅ none d where
  sub := Cache.Sub.refl d
  new := fun q w h1 h2 => by rw [h1] at h2; cases h2
  best := fun b h => by cases h
  min := fun η h => by simp at h

theorem Reach.cache_eq {d c : Cache} {M : EMessage} {tried : Finset Nonce}
    {β : Option (Nonce × Index)} (h : P.Reach d M tried β c) {η : Nonce} (hη : η ∉ tried) :
    c (P.encQuery (M ++ η)) = d (P.encQuery (M ++ η)) := by
  rcases hdq : d (P.encQuery (M ++ η)) with _ | w
  · rcases hcq : c (P.encQuery (M ++ η)) with _ | w'
    · rfl
    · obtain ⟨η', hη', he⟩ := h.new _ _ hdq hcq
      exact absurd (by rw [append_nonce_inj M (P.encQuery_inj he)]; exact hη') hη
  · exact h.sub _ _ hdq

theorem better_self (I : Index) (β : Option (Nonce × Index)) (η : Nonce) :
    P.better I (P.upd β η I) = false := by
  unfold upd
  split_ifs with h
  · simp [better]
  · simpa using h

theorem better_upd {I I' : Index} {β : Option (Nonce × Index)} (η : Nonce)
    (h : P.better I' β = false) : P.better I' (P.upd β η I) = false := by
  unfold upd
  split_ifs with hI
  · cases β with
    | none =>
      simp only [better, decide_eq_false_iff_not, decide_eq_true_eq] at h hI ⊢
      simp [h]
    | some b =>
      simp only [better, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
        decide_eq_false_iff_not, not_lt] at h hI ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (hI.2.le.trans h)
  · exact h

theorem upd_best {β : Option (Nonce × Index)} {η : Nonce} {I : Index} {b : Nonce × Index}
    (h : P.upd β η I = some b) : (b = (η, I) ∧ P.Accepted I) ∨ β = some b := by
  unfold upd at h
  split_ifs at h with hI
  · left
    refine ⟨(Option.some.inj h).symm, ?_⟩
    cases β with
    | none => simpa [better] using hI
    | some b' =>
      simp only [better, Bool.and_eq_true, decide_eq_true_eq] at hI
      exact hI.1
  · exact Or.inr h

theorem Reach.step {d c c' : Cache} {M : EMessage} {tried : Finset Nonce}
    {β : Option (Nonce × Index)} (h : P.Reach d M tried β c) {η : Nonce} (hη : η ∉ tried)
    {w : BitVec hashBits} (hc' : c' (P.encQuery (M ++ η)) = some w)
    (hsub : Cache.Sub c c')
    (hnew : ∀ q w', c q = none → c' q = some w' → q = P.encQuery (M ++ η)) :
    P.Reach d M (insert η tried) (P.upd β η (indexSlice w)) c' where
  sub := h.sub.trans hsub
  new := by
    intro q w' h1 h2
    rcases hcq : c q with _ | w''
    · exact ⟨η, Finset.mem_insert_self _ _, hnew q w' hcq h2⟩
    · obtain ⟨η', hη', he⟩ := h.new q w'' h1 hcq
      exact ⟨η', Finset.mem_insert_of_mem hη', he⟩
  best := by
    intro b hb
    rcases upd_best hb with ⟨rfl, hI⟩ | hb
    · exact ⟨Finset.mem_insert_self _ _, hI, w, hc', rfl⟩
    · obtain ⟨h1, h2, w', hw', hw''⟩ := h.best b hb
      exact ⟨Finset.mem_insert_of_mem h1, h2, w', hsub _ _ hw', hw''⟩
  min := by
    intro η' hη' w' hw'
    rcases Finset.mem_insert.1 hη' with rfl | hη'
    · rw [hc'] at hw'
      obtain rfl := Option.some.inj hw'
      exact better_self _ _ _
    · rcases hcq : c (P.encQuery (M ++ η')) with _ | w''
      · have := hnew _ _ hcq hw'
        exact absurd (by rw [← append_nonce_inj M (P.encQuery_inj this)]; exact hη') hη
      · rw [hsub _ _ hcq] at hw'
        obtain rfl := Option.some.inj hw'
        exact better_upd η (h.min η' hη' w'' hcq)

theorem Reach.step_cached {d c : Cache} {M : EMessage} {tried : Finset Nonce}
    {β : Option (Nonce × Index)} (h : P.Reach d M tried β c) {η : Nonce} (hη : η ∉ tried)
    {w : BitVec hashBits} (hw : c (P.encQuery (M ++ η)) = some w) :
    P.Reach d M (insert η tried) (P.upd β η (indexSlice w)) c :=
  h.step hη hw (Cache.Sub.refl c) fun q w' h1 h2 => by rw [h1] at h2; cases h2

theorem Reach.step_fresh {d c : Cache} {M : EMessage} {tried : Finset Nonce}
    {β : Option (Nonce × Index)} (h : P.Reach d M tried β c) {η : Nonce} (hη : η ∉ tried)
    (hc : c (P.encQuery (M ++ η)) = none) (w : BitVec hashBits) :
    P.Reach d M (insert η tried) (P.upd β η (indexSlice w))
      (c.cacheQuery (P.encQuery (M ++ η)) w) := by
  refine h.step hη (QueryCache.cacheQuery_self _ _ _) (Cache.sub_cacheQuery_of_none hc w) ?_
  intro q w' h1 h2
  by_contra hq
  rw [QueryCache.cacheQuery_of_ne _ _ hq, h1] at h2
  cases h2

variable (P)

/-- Every outcome of a run is a state of the run. -/
theorem signTierLoop_reach (d : Cache) (M : EMessage) :
    ∀ (k : ℕ) (tried : Finset Nonce) (β : Option (Nonce × Index)) (c : Cache),
      P.Reach d M tried β c → ∀ p ∈ support (run (P.signTierLoop M k tried β) c),
        ∃ tried', P.Reach d M tried' p.1 p.2 := by
  intro k
  induction k with
  | zero =>
    intro tried β c h p hp
    rw [signTierLoop, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨tried, h⟩
  | succ k ih =>
    intro tried β c h p hp
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signTierLoop_succ M k tried β hc] at hp
      obtain ⟨j, hp⟩ := mem_support_run_inl hp
      simp only [tierBody] at hp
      have hη := (Finset.mem_sdiff.1 (nonceOf_mem tried hc j)).2
      rcases hcq : c (P.encQuery (M ++ nonceOf tried hc j)) with _ | w
      · obtain ⟨w, hp⟩ := mem_support_run_inr_none hcq hp
        exact ih _ _ _ (h.step_fresh hη hcq w) p hp
      · exact ih _ _ _ (h.step_cached hη hcq) p (mem_support_run_inr_some hcq hp)
    · rw [signTierLoop, dif_neg hc, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨tried, h⟩

/-- `d'` extends `d` by the entries of a signing run of row `M` with outcome `r`. -/
def TierExt (M : EMessage) (d : Cache) (r : Option (Nonce × Index)) (d' : Cache) : Prop :=
  Cache.Sub d d' ∧ (∀ q w, d q = none → d' q = some w → ∃ η : Nonce, q = P.encQuery (M ++ η)) ∧
    ∀ b, r = some b → P.Accepted b.2 ∧
      ∃ w, d' (P.encQuery (M ++ b.1)) = some w ∧ indexSlice w = b.2

/-- The outcomes of signing (S1). -/
theorem signTier_ext (M : EMessage) (d : Cache) :
    ∀ p ∈ support (run (P.signTier M) d), P.TierExt M d p.1 p.2 := by
  intro p hp
  obtain ⟨tried, h⟩ := P.signTierLoop_reach d M trials ∅ none d (reach_init d M) p hp
  refine ⟨h.sub, fun q w h1 h2 => ?_, fun b hb => ?_⟩
  · obtain ⟨η, -, he⟩ := h.new q w h1 h2
    exact ⟨η, he⟩
  · obtain ⟨-, h2, h3⟩ := h.best b hb
    exact ⟨h2, h3⟩

/-! ## Non-index entries are irrelevant (S2) -/

theorem run_signTierLoop_extend (M : EMessage) (f : Cache)
    (hf : ∀ u : EncInput, f (P.encQuery u) = none) :
    ∀ (k : ℕ) (tried : Finset Nonce) (β : Option (Nonce × Index)) (d : Cache),
      run (P.signTierLoop M k tried β) (Cache.extend d f) =
        (fun p => (p.1, Cache.extend p.2 f)) <$> run (P.signTierLoop M k tried β) d := by
  intro k
  induction k with
  | zero => intro tried β d; simp [signTierLoop, run_pure]
  | succ k ih =>
    intro tried β d
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signTierLoop_succ M k tried β hc, run_query_bind, run_query_bind, oracleImpl_run_inl,
        oracleImpl_run_inl]
      simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun j => ?_
      simp only [tierBody]
      rw [run_query_bind, run_query_bind]
      rcases hdq : d (P.encQuery (M ++ nonceOf tried hc j)) with _ | w
      · have hdq' : Cache.extend d f (P.encQuery (M ++ nonceOf tried hc j)) = none := by
          rw [Cache.extend_apply_of_none hdq]; exact hf _
        rw [oracleImpl_run_inr_none hdq, oracleImpl_run_inr_none hdq']
        simp only [bind_assoc, pure_bind, map_bind]
        refine bind_congr fun w => ?_
        rw [← Cache.extend_cacheQuery]
        exact ih _ _ _
      · have hdq' : Cache.extend d f (P.encQuery (M ++ nonceOf tried hc j)) = some w :=
          Cache.extend_apply_of_some hdq
        rw [oracleImpl_run_inr_some hdq, oracleImpl_run_inr_some hdq', pure_bind, pure_bind]
        exact ih _ _ _
    · rw [signTierLoop, dif_neg hc, run_pure, run_pure, map_pure]

theorem run_signTier_extend (M : EMessage) (d f : Cache)
    (hf : ∀ u : EncInput, f (P.encQuery u) = none) :
    run (P.signTier M) (Cache.extend d f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run (P.signTier M) d :=
  P.run_signTierLoop_extend M f hf trials ∅ none d

/-! ## One trial and the value of a run (lemma V) -/

/-- The value of one trial at nonce `η`: `g η w false` at the cached answer `w`, the average of
`g η w true` over a fresh answer. -/
def trialVal (d : Cache) (M : EMessage) (g : Nonce → BitVec hashBits → Bool → ℝ≥0∞)
    (η : Nonce) : ℝ≥0∞ :=
  match d (P.encQuery (M ++ η)) with
  | some w => g η w false
  | none => ∑ w, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * g η w true

/-- The average over one trial: `η` uniform among the untried nonces. -/
def trialAvg (d : Cache) (M : EMessage) (tried : Finset Nonce)
    (g : Nonce → BitVec hashBits → Bool → ℝ≥0∞) : ℝ≥0∞ :=
  ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * ∑ η ∈ Finset.univ \ tried, P.trialVal d M g η

variable {P} in
theorem trialVal_none {d : Cache} {M : EMessage} {g : Nonce → BitVec hashBits → Bool → ℝ≥0∞}
    {η : Nonce} (hd : d (P.encQuery (M ++ η)) = none) :
    P.trialVal d M g η = ∑ w, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * g η w true := by
  unfold trialVal
  rw [hd]

variable {P} in
theorem trialVal_some {d : Cache} {M : EMessage} {g : Nonce → BitVec hashBits → Bool → ℝ≥0∞}
    {η : Nonce} {w : BitVec hashBits} (hd : d (P.encQuery (M ++ η)) = some w) :
    P.trialVal d M g η = g η w false := by
  unfold trialVal
  rw [hd]

theorem trialVal_mono {d : Cache} {M : EMessage} {g h : Nonce → BitVec hashBits → Bool → ℝ≥0∞}
    (hgh : ∀ η w fr, g η w fr ≤ h η w fr) (η : Nonce) :
    P.trialVal d M g η ≤ P.trialVal d M h η := by
  rcases hd : d (P.encQuery (M ++ η)) with _ | w
  · rw [trialVal_none hd, trialVal_none hd]
    gcongr with w
    exact hgh _ _ _
  · rw [trialVal_some hd, trialVal_some hd]
    exact hgh _ _ _

theorem trialAvg_mono {d : Cache} {M : EMessage} {tried : Finset Nonce}
    {g h : Nonce → BitVec hashBits → Bool → ℝ≥0∞} (hgh : ∀ η w fr, g η w fr ≤ h η w fr) :
    P.trialAvg d M tried g ≤ P.trialAvg d M tried h := by
  unfold trialAvg
  gcongr with η
  exact P.trialVal_mono hgh η

theorem trialAvg_add (d : Cache) (M : EMessage) (tried : Finset Nonce)
    (g h : Nonce → BitVec hashBits → Bool → ℝ≥0∞) :
    P.trialAvg d M tried (fun η w fr => g η w fr + h η w fr) =
      P.trialAvg d M tried g + P.trialAvg d M tried h := by
  unfold trialAvg
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun η _ => ?_
  rcases hd : d (P.encQuery (M ++ η)) with _ | w
  · rw [trialVal_none hd, trialVal_none hd, trialVal_none hd]
    simp only [mul_add, Finset.sum_add_distrib]
  · rw [trialVal_some hd, trialVal_some hd, trialVal_some hd]

theorem trialVal_const_mul (d : Cache) (M : EMessage) (a : ℝ≥0∞)
    (g : Nonce → BitVec hashBits → Bool → ℝ≥0∞) (η : Nonce) :
    P.trialVal d M (fun η w fr => a * g η w fr) η = a * P.trialVal d M g η := by
  rcases hd : d (P.encQuery (M ++ η)) with _ | w
  · rw [trialVal_none hd, trialVal_none hd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  · rw [trialVal_some hd, trialVal_some hd]

theorem trialAvg_const_mul (d : Cache) (M : EMessage) (tried : Finset Nonce) (a : ℝ≥0∞)
    (g : Nonce → BitVec hashBits → Bool → ℝ≥0∞) :
    P.trialAvg d M tried (fun η w fr => a * g η w fr) = a * P.trialAvg d M tried g := by
  unfold trialAvg
  simp only [P.trialVal_const_mul, ← Finset.mul_sum]
  ring

/-- The trials that a trial average sees: untried nonces, fresh exactly when not cached. -/
def TrialOK (d : Cache) (M : EMessage) (tried : Finset Nonce) (η : Nonce) (w : BitVec hashBits)
    (fr : Bool) : Prop :=
  η ∉ tried ∧ (fr = true → d (P.encQuery (M ++ η)) = none) ∧
    (fr = false → d (P.encQuery (M ++ η)) = some w)

theorem trialAvg_mono' {d : Cache} {M : EMessage} {tried : Finset Nonce}
    {g h : Nonce → BitVec hashBits → Bool → ℝ≥0∞}
    (hgh : ∀ η w fr, P.TrialOK d M tried η w fr → g η w fr ≤ h η w fr) :
    P.trialAvg d M tried g ≤ P.trialAvg d M tried h := by
  unfold trialAvg
  gcongr with η hη
  have hηt := (Finset.mem_sdiff.1 hη).2
  rcases hd : d (P.encQuery (M ++ η)) with _ | w
  · rw [trialVal_none hd, trialVal_none hd]
    gcongr with w
    exact hgh _ _ _ ⟨hηt, fun _ => hd, fun h => absurd h (by simp)⟩
  · rw [trialVal_some hd, trialVal_some hd]
    exact hgh _ _ _ ⟨hηt, fun h => absurd h (by simp), fun _ => hd⟩

/-- Bound a trial average by a combination of indicator averages. -/
theorem trialAvg_le_two {d : Cache} {M : EMessage} {tried : Finset Nonce}
    {g : Nonce → BitVec hashBits → Bool → ℝ≥0∞} (φ ψ : Nonce → BitVec hashBits → Bool → Prop)
    [∀ η w fr, Decidable (φ η w fr)] [∀ η w fr, Decidable (ψ η w fr)] (a b : ℝ≥0∞)
    (hg : ∀ η w fr, P.TrialOK d M tried η w fr →
      g η w fr ≤ (if φ η w fr then a else 0) + (if ψ η w fr then b else 0)) :
    P.trialAvg d M tried g ≤
      a * P.trialAvg d M tried (fun η w fr => if φ η w fr then 1 else 0) +
        b * P.trialAvg d M tried (fun η w fr => if ψ η w fr then 1 else 0) := by
  rw [← trialAvg_const_mul, ← trialAvg_const_mul, ← trialAvg_add]
  refine P.trialAvg_mono' fun η w fr hok => (hg η w fr hok).trans (le_of_eq ?_)
  split_ifs <;> simp

theorem E_run_tierBody_cached {M : EMessage} {k : ℕ} {tried : Finset Nonce}
    {β : Option (Nonce × Index)} {η : Nonce} {c : Cache} {w : BitVec hashBits}
    (hc : c (P.encQuery (M ++ η)) = some w) (F : Option (Nonce × Index) × Cache → ℝ≥0∞) :
    E (run (P.tierBody M k tried β η) c) F =
      E (run (P.signTierLoop M k (insert η tried) (P.upd β η (indexSlice w))) c) F := by
  unfold tierBody
  rw [run_query_bind, oracleImpl_run_inr_some hc, pure_bind]

theorem E_run_tierBody_fresh {M : EMessage} {k : ℕ} {tried : Finset Nonce}
    {β : Option (Nonce × Index)} {η : Nonce} {c : Cache}
    (hc : c (P.encQuery (M ++ η)) = none) (F : Option (Nonce × Index) × Cache → ℝ≥0∞) :
    E (run (P.tierBody M k tried β η) c) F =
      ∑ w, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        E (run (P.signTierLoop M k (insert η tried) (P.upd β η (indexSlice w)))
          (c.cacheQuery (P.encQuery (M ++ η)) w)) F := by
  unfold tierBody
  rw [run_query_bind, oracleImpl_run_inr_none hc, E_bind, E_bind, E_uniform]
  simp only [E_pure]

/-- **Lemma V.** A function `U` of the state that one trial does not increase in average bounds
the value of every run. -/
theorem loop_value (d : Cache) (M : EMessage) (F : Option (Nonce × Index) → Cache → ℝ≥0∞)
    (U : ℕ → Finset Nonce → Option (Nonce × Index) → Cache → ℝ≥0∞)
    (h0 : ∀ tried β c, P.Reach d M tried β c → F β c ≤ U 0 tried β c)
    (hstep : ∀ k tried β c, P.Reach d M tried β c → tried.card + (k + 1) ≤ trials →
      P.trialAvg d M tried (fun η w fr => U k (insert η tried) (P.upd β η (indexSlice w))
        (if fr then c.cacheQuery (P.encQuery (M ++ η)) w else c)) ≤ U (k + 1) tried β c) :
    ∀ k tried β c, P.Reach d M tried β c → tried.card + k ≤ trials →
      E (run (P.signTierLoop M k tried β) c) (fun p => F p.1 p.2) ≤ U k tried β c := by
  intro k
  induction k with
  | zero =>
    intro tried β c h _
    rw [signTierLoop, run_pure, E_pure]
    exact h0 tried β c h
  | succ k ih =>
    intro tried β c h hk
    have hc : 0 < (Finset.univ \ tried).card := pool_pos (by omega)
    refine le_trans ?_ (hstep k tried β c h hk)
    rw [P.signTierLoop_succ M k tried β hc, run_query_bind, E_bind, oracleImpl_run_inl, E_bind,
      E_query_unif]
    simp only [E_pure]
    have hcast : (Finset.univ \ tried).card - 1 + 1 = (Finset.univ \ tried).card := by omega
    have hcR : (((Finset.univ \ tried).card - 1 : ℕ) : ℝ≥0∞) + 1 =
        ((Finset.univ \ tried).card : ℝ≥0∞) := by
      rw [← Nat.cast_add_one, hcast]
    simp only [hcR]
    set g : Nonce → BitVec hashBits → Bool → ℝ≥0∞ := fun η w fr =>
      U k (insert η tried) (P.upd β η (indexSlice w))
        (if fr then c.cacheQuery (P.encQuery (M ++ η)) w else c) with hg
    have per : ∀ η ∈ Finset.univ \ tried,
        E (run (P.tierBody M k tried β η) c) (fun p => F p.1 p.2) ≤ P.trialVal d M g η := by
      intro η hη
      have hηt : η ∉ tried := (Finset.mem_sdiff.1 hη).2
      have hins : (insert η tried).card + k ≤ trials := by
        rw [Finset.card_insert_of_notMem hηt]; omega
      have hce := h.cache_eq hηt
      rcases hdq : d (P.encQuery (M ++ η)) with _ | w
      · rw [hdq] at hce
        rw [P.E_run_tierBody_fresh hce, trialVal_none hdq]
        gcongr with w
        exact ih _ _ _ (h.step_fresh hηt hce w) hins
      · rw [hdq] at hce
        rw [P.E_run_tierBody_cached hce, trialVal_some hdq]
        exact ih _ _ _ (h.step_cached hηt hce) hins
    calc ∑ j, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
          E (run (P.tierBody M k tried β (nonceOf tried hc j)) c) (fun p => F p.1 p.2)
        ≤ ∑ j, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * P.trialVal d M g (nonceOf tried hc j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_right (per _ (nonceOf_mem tried hc j)) _
      _ = ∑ η ∈ Finset.univ \ tried, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            P.trialVal d M g η :=
          sum_fin_equivFin hcast fun η => ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            P.trialVal d M g η
      _ = P.trialAvg d M tried g := by
          rw [← Finset.mul_sum]
          rfl

/-! ## One trial (T0, T1) -/

theorem card_answers : (Fintype.card (BitVec hashBits) : ℝ≥0∞) = 2 ^ 256 := by
  rw [Fintype.card_bitVec]
  unfold hashBits
  norm_num

theorem pool_card_ne_zero {tried : Finset Nonce} (h : tried.card < trials) :
    ((Finset.univ \ tried).card : ℝ≥0∞) ≠ 0 :=
  Nat.cast_ne_zero.2 (pool_pos h).ne'

theorem pool_ge {tried : Finset Nonce} (h : tried.card < trials) :
    2 ^ 127 - 2 ^ 19 ≤ (Finset.univ \ tried).card := by
  rw [card_pool]
  unfold trials at h
  omega

theorem avg_ind (φ : BitVec hashBits → Prop) [DecidablePred φ] :
    ∑ w, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (if φ w then 1 else 0) =
      (Finset.univ.filter φ).card * (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ := by
  rw [← Finset.mul_sum, Finset.sum_boole, mul_comm]

theorem two_pow_129_mul_inv : (2 : ℝ≥0∞) ^ 129 * ((2 : ℝ≥0∞) ^ 256)⁻¹ = ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
  rw [show (256 : ℕ) = 129 + 127 from rfl, pow_add,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
    ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]

/-- One trial lands on an answer satisfying `φ` (T0). -/
theorem trialAvg_ind (d : Cache) (M : EMessage) (tried : Finset Nonce)
    (φ : BitVec hashBits → Prop) [DecidablePred φ] :
    P.trialAvg d M tried (fun _ w _ => if φ w then 1 else 0) =
      ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
        ((((Finset.univ \ tried).filter fun η =>
            ∃ w, d (P.encQuery (M ++ η)) = some w ∧ φ w).card : ℝ≥0∞) +
          ((Finset.univ \ tried).filter fun η => d (P.encQuery (M ++ η)) = none).card *
            ((Finset.univ.filter φ).card * (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹)) := by
  unfold trialAvg
  congr 1
  have hx : ∀ η, P.trialVal d M (fun _ w _ => if φ w then 1 else 0) η =
      (if ∃ w, d (P.encQuery (M ++ η)) = some w ∧ φ w then 1 else 0) +
        (if d (P.encQuery (M ++ η)) = none then
          (Finset.univ.filter φ).card * (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ else 0) := by
    intro η
    rcases hd : d (P.encQuery (M ++ η)) with _ | w
    · rw [trialVal_none hd, avg_ind]
      simp
    · rw [trialVal_some hd]
      simp
  simp only [hx]
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]

/-- A fresh trial lands on an answer satisfying `φ` with probability at most the mass of `φ`. -/
theorem trialAvg_fresh_le (d : Cache) (M : EMessage) {tried : Finset Nonce}
    (htr : tried.card < trials) (φ : BitVec hashBits → Prop) [DecidablePred φ] :
    P.trialAvg d M tried (fun _ w fr => if fr = true ∧ φ w then 1 else 0) ≤
      (Finset.univ.filter φ).card * (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ := by
  unfold trialAvg
  set ρ := ((Finset.univ.filter φ).card : ℝ≥0∞) * (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹
  have hx : ∀ η, P.trialVal d M (fun _ w fr => if fr = true ∧ φ w then 1 else 0) η ≤ ρ := by
    intro η
    rcases hd : d (P.encQuery (M ++ η)) with _ | w
    · rw [trialVal_none hd]
      simp only [true_and]
      rw [avg_ind]
    · rw [trialVal_some hd]
      simp
  calc ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * ∑ η ∈ Finset.univ \ tried, _
      ≤ ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * ∑ _η ∈ Finset.univ \ tried, ρ := by
        gcongr with η
        exact hx η
    _ = ρ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (pool_card_ne_zero htr) (ENNReal.natCast_ne_top _), one_mul]

/-- A fresh trial has class `v` with probability at most `p(v)` (T1b). -/
theorem trialAvg_fresh_cls (d : Cache) (M : EMessage) {tried : Finset Nonce}
    (htr : tried.card < trials) (v : Cls) :
    P.trialAvg d M tried (fun _ w fr => if fr = true ∧ P.cls w = some v then 1 else 0) ≤
      (P.cweight v : ℝ≥0∞) / 2 ^ 127 := by
  refine (P.trialAvg_fresh_le d M htr _).trans (le_of_eq ?_)
  rw [P.card_cls, card_answers, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv,
    mul_assoc, two_pow_129_mul_inv]

/-- A trial is at a given nonce with probability at most `1 / (I - L)` (T1c). -/
theorem trialAvg_nonce (d : Cache) (M : EMessage) {tried : Finset Nonce}
    (htr : tried.card < trials) (η₀ : Nonce) :
    P.trialAvg d M tried (fun η _ _ => if η = η₀ then 1 else 0) ≤
      ((2 ^ 127 - 2 ^ 19 : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold trialAvg
  have hx : ∀ η, P.trialVal d M (fun η _ _ => if η = η₀ then 1 else 0) η =
      if η = η₀ then 1 else 0 := by
    intro η
    rcases hd : d (P.encQuery (M ++ η)) with _ | w
    · rw [trialVal_none hd, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    · rw [trialVal_some hd]
  simp only [hx]
  rw [Finset.sum_ite_eq']
  split_ifs
  · rw [mul_one]
    exact ENNReal.inv_le_inv.2 (Nat.cast_le.2 (pool_ge htr))
  · rw [mul_zero]
    exact bot_le

theorem trialAvg_le_one (d : Cache) (M : EMessage) {tried : Finset Nonce}
    (htr : tried.card < trials) {g : Nonce → BitVec hashBits → Bool → ℝ≥0∞}
    (hg : ∀ η w fr, g η w fr ≤ 1) : P.trialAvg d M tried g ≤ 1 := by
  unfold trialAvg
  have hx : ∀ η, P.trialVal d M g η ≤ 1 := by
    intro η
    rcases hd : d (P.encQuery (M ++ η)) with _ | w
    · rw [trialVal_none hd]
      calc ∑ w, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * g η w true
          ≤ ∑ _w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * 1 := by
            gcongr with w; exact hg _ _ _
        _ = 1 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
              ENNReal.mul_inv_cancel (by simp) (by simp)]
    · rw [trialVal_some hd]
      exact hg _ _ _
  calc ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * ∑ η ∈ Finset.univ \ tried, P.trialVal d M g η
      ≤ ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * ∑ _η ∈ Finset.univ \ tried, (1 : ℝ≥0∞) := by
        gcongr with η
        exact hx η
    _ = 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one,
          ENNReal.inv_mul_cancel (pool_card_ne_zero htr) (ENNReal.natCast_ne_top _)]

/-! ## The tier bound of one trial under `RowGood` (T1a) -/

theorem card_filter_eq_sum {s : Finset Nonce} (p : Nonce → Prop) [DecidablePred p] :
    ((s.filter p).card : ℝ) = ∑ η ∈ s, if p η then (1 : ℝ) else 0 := by
  rw [Finset.card_filter]
  push_cast
  rfl

theorem card_filter_split (tried : Finset Nonce) (p : Nonce → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      ((Finset.univ \ tried).filter p).card + (tried.filter p).card := by
  rw [← Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter Finset.sdiff_disjoint)]
  congr 1
  ext η
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
  tauto

theorem card_some_add_none (s : Finset Nonce) (d : Cache) (M : EMessage) :
    (s.filter fun η => (d (P.encQuery (M ++ η))).isSome).card +
      (s.filter fun η => d (P.encQuery (M ++ η)) = none).card = s.card := by
  rw [← Finset.card_filter_add_card_filter_not
    (s := s) (fun η => (d (P.encQuery (M ++ η))).isSome)]
  congr 2
  ext η
  simp only [Finset.mem_filter, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]

theorem ennreal_frac_le {n A F : ℕ} {x y : ℝ} (hn : 0 < n) (hx : 0 ≤ x)
    (h : (n : ℝ)⁻¹ * (A + F * x) ≤ y) :
    ((n : ℝ≥0∞))⁻¹ * ((A : ℝ≥0∞) + F * ENNReal.ofReal x) ≤ ENNReal.ofReal y := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_natCast A, ← ENNReal.ofReal_natCast F,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hx), ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_inv_of_pos hn', ← ENNReal.ofReal_mul (inv_nonneg.2 hn'.le)]
  exact ENNReal.ofReal_le_ofReal h

/-- The arithmetic of T1a. -/
theorem t1a_arith {A a F n rU rN r₁ r₂ r Pm eta : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hF : 0 ≤ F) (hr1 : 0 ≤ r₁) (hr2 : 0 ≤ r₂)
    (hpart : A + a + F = n) (hN : rN ≤ a + r₁) (hU : rU + F + r₂ = 2 ^ 127)
    (hr : r₁ + r₂ = r) (hn : n = 2 ^ 127 - r) (hrL : r < 2 ^ 19) (hPm0 : 0 ≤ Pm)
    (hPm1 : Pm ≤ 1) (hgood : rU * Pm ≤ rN + 2 ^ 66)
    (heta : (2 ^ 66 + 2 ^ 19) / (2 ^ 127 - 2 ^ 19) ≤ eta) :
    n⁻¹ * (A + F * (1 - Pm)) ≤ 1 - Pm + eta := by
  have hn0 : 0 < n := by rw [hn]; linarith
  rw [inv_mul_le_iff₀ hn0]
  have hne : 2 ^ 66 + 2 ^ 19 ≤ n * eta := by
    have h1 : (2 ^ 66 + 2 ^ 19 : ℝ) ≤ n * ((2 ^ 66 + 2 ^ 19) / (2 ^ 127 - 2 ^ 19)) := by
      rw [mul_div_assoc', le_div_iff₀ (by norm_num)]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left heta hn0.le)
  nlinarith [mul_le_mul_of_nonneg_right hN hPm0, mul_nonneg hF hPm0, mul_nonneg hr2 hPm0,
    mul_le_mul_of_nonneg_left hPm1 hr2]

variable {S : Tier.Sched}

/-- One trial misses the tiers below `t` with probability at most `ȳ_t` (T1a). -/
theorem trialAvg_tier_ge (hS : S.Valid) (hT : P.TierHyp S) {d : Cache} {M : EMessage}
    (hRG : P.RowGood S d M) {tried : Finset Nonce} (htr : tried.card < trials) {t : ℕ}
    (ht : t ≤ S.T) :
    P.trialAvg d M tried (fun _ w _ => if t ≤ P.tierW S w then 1 else 0) ≤ S.yb t := by
  have heta : (0 : ℝ) ≤ (Tier.eta0 : ℝ) := by norm_num [Tier.eta0]
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · refine (P.trialAvg_le_one d M htr fun _ _ _ => by split_ifs <;> simp).trans ?_
    unfold Tier.Sched.yb Tier.Sched.ybar
    rw [show S.mass 0 = 0 by simp [Tier.Sched.mass], ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hs : s < S.T := by omega
  rw [P.trialAvg_ind]
  set A := ((Finset.univ \ tried).filter fun η =>
    ∃ w, d (P.encQuery (M ++ η)) = some w ∧ s + 1 ≤ P.tierW S w).card with hA
  set a := ((Finset.univ \ tried).filter fun η =>
    ∃ w, d (P.encQuery (M ++ η)) = some w ∧ P.tierW S w ≤ s).card with ha
  set F := ((Finset.univ \ tried).filter fun η => d (P.encQuery (M ++ η)) = none).card with hF
  set Pm : ℝ := (S.mass (s + 1) : ℝ) with hPm
  set X := ∑ t ∈ Finset.range (s + 1), S.N t * S.a t with hX
  -- the answer mass
  have hmassN : Pm = (X : ℝ) / 2 ^ 127 := by
    rw [hPm]
    unfold Tier.Sched.mass
    rw [hT.K_eq, hX]
    push_cast
    rfl
  have hcardlt := card_tierW_lt hS hT (show s + 1 ≤ S.T by omega)
  rw [← hX] at hcardlt
  have hall : (Finset.univ : Finset (BitVec hashBits)).card = 2 ^ 256 := by
    rw [Finset.card_univ, Fintype.card_bitVec]; unfold hashBits; rfl
  have hXle : X * 2 ^ 129 ≤ 2 ^ 256 := by
    rw [← hcardlt, ← hall]
    exact Finset.card_filter_le _ _
  have hPm0 : 0 ≤ Pm := by rw [hmassN]; positivity
  have hPm1 : Pm ≤ 1 := by
    rw [hmassN, div_le_one (by positivity)]
    have : ((X * 2 ^ 129 : ℕ) : ℝ) ≤ ((2 ^ 256 : ℕ) : ℝ) := by exact_mod_cast hXle
    push_cast at this
    nlinarith
  have hρ : ((Finset.univ.filter fun w : BitVec hashBits => s + 1 ≤ P.tierW S w).card : ℝ≥0∞) *
      (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - Pm) := by
    have hc : (Finset.univ.filter fun w : BitVec hashBits => s + 1 ≤ P.tierW S w).card =
        2 ^ 256 - X * 2 ^ 129 := by
      have h1 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (BitVec hashBits))) (fun w => P.tierW S w < s + 1)
      rw [hcardlt, hall] at h1
      have h2 : (Finset.univ.filter fun w : BitVec hashBits => ¬ P.tierW S w < s + 1) =
          Finset.univ.filter fun w : BitVec hashBits => s + 1 ≤ P.tierW S w := by
        ext w; simp only [Finset.mem_filter, not_lt]
      rw [h2] at h1
      omega
    rw [hc, card_answers]
    rw [show ((2 ^ 256 - X * 2 ^ 129 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 ^ 256 - X * 2 ^ 129 : ℕ) : ℝ)
      from (ENNReal.ofReal_natCast _).symm,
      show (2 : ℝ≥0∞) ^ 256 = ENNReal.ofReal ((2 : ℝ) ^ 256) from (Tier.ofReal_two_pow 256).symm,
      ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.cast_sub hXle, hmassN]
    push_cast
    field_simp
    ring
  rw [hρ]
  -- counting
  have hpart : A + a + F = (Finset.univ \ tried).card := by
    have hsum : ((A + a + F : ℕ) : ℝ) = (Finset.univ \ tried).card := by
      push_cast
      rw [hA, ha, hF, card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
      push_cast
      refine Finset.sum_congr rfl fun η _ => ?_
      rcases d (P.encQuery (M ++ η)) with _ | w
      · simp
      · by_cases hw : s + 1 ≤ P.tierW S w
        · simp [show ¬ P.tierW S w ≤ s by omega]
        · simp [show P.tierW S w ≤ s by omega]
    exact_mod_cast hsum
  have hN := card_filter_split tried
    (fun η => ∃ w, d (P.encQuery (M ++ η)) = some w ∧ P.tierW S w ≤ s)
  have hFs := card_filter_split tried (fun η => d (P.encQuery (M ++ η)) = none)
  have hU := P.card_some_add_none Finset.univ d M
  have hr := P.card_some_add_none tried d M
  have hr₁ : (tried.filter fun η =>
      ∃ w, d (P.encQuery (M ++ η)) = some w ∧ P.tierW S w ≤ s).card ≤
      (tried.filter fun η => (d (P.encQuery (M ++ η))).isSome).card := by
    refine Finset.card_le_card fun η hη => ?_
    simp only [Finset.mem_filter] at hη ⊢
    obtain ⟨h, w, hw, -⟩ := hη
    exact ⟨h, by simp [hw]⟩
  have hgood := hRG s hs
  have hrowN : P.rowN S d M s = (Finset.univ.filter fun η =>
      ∃ w, d (P.encQuery (M ++ η)) = some w ∧ P.tierW S w ≤ s).card := rfl
  have hrowU : P.rowU d M = (Finset.univ.filter fun η =>
      (d (P.encQuery (M ++ η))).isSome).card := rfl
  rw [Finset.card_univ, Fintype.card_bitVec] at hU
  have hpool : (Finset.univ \ tried).card = 2 ^ 127 - tried.card := card_pool
  have htr' : tried.card < 2 ^ 19 := by unfold trials at htr; exact htr
  have heta_eq : ((Tier.eta0 : ℚ) : ℝ) = (2 ^ 66 + 2 ^ 19) / (2 ^ 127 - 2 ^ 19) := by
    norm_num [Tier.eta0]
  have hy : (((1 : ℚ) - S.mass (s + 1) + Tier.eta0 : ℚ) : ℝ) = 1 - Pm + Tier.eta0 := by
    rw [hPm]; push_cast; rfl
  unfold Tier.Sched.yb Tier.Sched.ybar
  rw [hy]
  refine ennreal_frac_le (pool_pos htr) (by linarith) ?_
  refine t1a_arith (A := A) (a := a) (F := F) (rU := P.rowU d M) (rN := P.rowN S d M s)
    (r₁ := (tried.filter fun η => (d (P.encQuery (M ++ η))).isSome).card)
    (r₂ := (tried.filter fun η => d (P.encQuery (M ++ η)) = none).card) (r := tried.card)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by exact_mod_cast hpart) ?_ ?_ (by exact_mod_cast hr) ?_ (by exact_mod_cast htr')
    hPm0 hPm1 hgood ?_
  · rw [hrowN, hN]
    exact_mod_cast Nat.add_le_add_left hr₁ _
  · have : P.rowU d M + F + (tried.filter fun η => d (P.encQuery (M ++ η)) = none).card =
        2 ^ 127 := by rw [hrowU]; omega
    exact_mod_cast this
  · rw [hpool, Nat.cast_sub (by omega)]
    push_cast
    ring
  · rw [heta_eq]

/-! ## The winner law (K1-K5) -/

theorem upd_cases (hS : S.Valid) (hT : P.TierHyp S) {β : Option (Nonce × Index)}
    (hβ : ∀ b, β = some b → P.Accepted b.2) (η : Nonce) (I : Index) :
    (P.tierI S I < P.tierB S β ∧ P.upd β η I = some (η, I)) ∨
      (P.tierB S β ≤ P.tierI S I ∧ P.upd β η I = β) := by
  by_cases h : P.better I β = true
  · left
    exact ⟨(better_iff hS hT I hβ).1 h, by unfold upd; rw [if_pos h]⟩
  · right
    exact ⟨not_lt.1 fun h' => h ((better_iff hS hT I hβ).2 h'), by unfold upd; rw [if_neg h]⟩

theorem tierW_eq (w : BitVec hashBits) : P.tierW S w = P.tierI S (indexSlice w) := rfl

variable (S) in
/-- The value function of `win_le`: open (no best trial of tier `≤ t`), hold (the best trial is
a target), dead. -/
def winU (θ : Nonce → Index → Prop) (t : ℕ) (x y q : ℝ≥0∞) (k : ℕ) :
    Option (Nonce × Index) → ℝ≥0∞
  | none => Tier.winA x y q k
  | some b => if θ b.1 b.2 then y ^ k else if t < P.tierI S b.2 then Tier.winA x y q k else 0

theorem winU_none (θ : Nonce → Index → Prop) (t : ℕ) (x y q : ℝ≥0∞) (k : ℕ) :
    P.winU S θ t x y q k none = Tier.winA x y q k := rfl

theorem winU_some (θ : Nonce → Index → Prop) (t : ℕ) (x y q : ℝ≥0∞) (k : ℕ) (b : Nonce × Index) :
    P.winU S θ t x y q k (some b) =
      if θ b.1 b.2 then y ^ k else if t < P.tierI S b.2 then Tier.winA x y q k else 0 := rfl

/-- **K1, K2.** The best trial is a target trial (a set `θ` of trials of tier `t`) with
probability at most `q w̄_t` when one trial hits `θ` with probability at most `q`. -/
theorem win_le (hS : S.Valid) (hT : P.TierHyp S) {d : Cache} {M : EMessage}
    (hRG : P.RowGood S d M) (θ : Nonce → Index → Prop) {t : ℕ} (ht : t < S.T)
    (hθ : ∀ η I, θ η I → P.tierI S I = t) {q : ℝ≥0∞}
    (hq : ∀ tried : Finset Nonce, tried.card < trials →
      P.trialAvg d M tried (fun η w _ => if θ η (indexSlice w) then 1 else 0) ≤ q) :
    E (run (P.signTier M) d) (fun p => if ∃ b, p.1 = some b ∧ θ b.1 b.2 then 1 else 0) ≤
      q * S.wbar t := by
  set x := S.yb (t + 1) with hx
  set y := S.yb t with hy
  have key := P.loop_value d M (fun β _ => if ∃ b, β = some b ∧ θ b.1 b.2 then 1 else 0)
    (fun k _ β _ => P.winU S θ t x y q k β) ?_ ?_ trials ∅ none d (reach_init d M) (by simp)
  · unfold signTier
    refine key.trans (le_of_eq ?_)
    rw [winU_none, Tier.winA_eq, Tier.Sched.wbar]
    unfold trials
    rfl
  · intro tried β c _
    cases β with
    | none => simp
    | some b =>
      rw [winU_some]
      by_cases hb : θ b.1 b.2 <;> simp [hb]
  · intro k tried β c h hk
    beta_reduce
    have htr : tried.card < trials := by omega
    have hβ : ∀ b, β = some b → P.Accepted b.2 := fun b hb => (h.best b hb).2.1
    have hA := P.trialAvg_tier_ge hS hT hRG htr (t := t + 1) (by omega)
    have hB := P.trialAvg_tier_ge hS hT hRG htr (t := t) ht.le
    rcases β with _ | b
    · -- open, no best trial yet
      rw [winU_none, Tier.winA]
      refine (P.trialAvg_le_two (fun η w _ => θ η (indexSlice w))
        (fun _ w _ => t + 1 ≤ P.tierW S w) (y ^ k) (Tier.winA x y q k) ?_).trans ?_
      · intro η w fr _
        rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2, winU_some]
          by_cases hθη : θ η (indexSlice w)
          · simp [hθη]
          · by_cases hlt : t < P.tierI S (indexSlice w)
            · simp [hθη, hlt, tierW_eq, show t + 1 ≤ P.tierI S (indexSlice w) by omega]
            · simp [hθη, hlt]
        · rw [h2, winU_none]
          have : t + 1 ≤ P.tierW S w := by
            rw [tierW_eq]; simp only [tierB] at h1; omega
          simp [this]
      · calc y ^ k * _ + Tier.winA x y q k * _ ≤ y ^ k * q + Tier.winA x y q k * x :=
            add_le_add (mul_le_mul' le_rfl (hq tried htr)) (mul_le_mul' le_rfl hA)
          _ = q * y ^ k + x * Tier.winA x y q k := by ring
    · have hbacc := hβ b rfl
      by_cases hθb : θ b.1 b.2
      · -- hold
        have htb : P.tierI S b.2 = t := hθ _ _ hθb
        rw [winU_some, if_pos hθb]
        refine (P.trialAvg_le_two (fun _ w _ => t ≤ P.tierW S w) (fun _ _ _ => False)
          (y ^ k) 0 ?_).trans ?_
        · intro η w fr _
          rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [tierB] at h1
            rw [h2, winU_some]
            have hn : ¬ θ η (indexSlice w) := fun h' => by rw [hθ _ _ h'] at h1; omega
            simp [hn, show ¬ t < P.tierI S (indexSlice w) by omega]
          · simp only [tierB] at h1
            rw [h2, winU_some, if_pos hθb]
            simp [tierW_eq, show t ≤ P.tierI S (indexSlice w) by omega]
        · calc y ^ k * _ + 0 * _ ≤ y ^ k * y := by
                rw [zero_mul, add_zero]; exact mul_le_mul' le_rfl hB
            _ = y ^ (k + 1) := (pow_succ y k).symm
      · by_cases hlt : t < P.tierI S b.2
        · -- open
          rw [winU_some, if_neg hθb, if_pos hlt, Tier.winA]
          refine (P.trialAvg_le_two (fun η w _ => θ η (indexSlice w))
            (fun _ w _ => t + 1 ≤ P.tierW S w) (y ^ k) (Tier.winA x y q k) ?_).trans ?_
          · intro η w fr _
            rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h2, winU_some]
              by_cases hθη : θ η (indexSlice w)
              · simp [hθη]
              · by_cases hlt' : t < P.tierI S (indexSlice w)
                · simp [hθη, hlt', tierW_eq, show t + 1 ≤ P.tierI S (indexSlice w) by omega]
                · simp [hθη, hlt']
            · simp only [tierB] at h1
              rw [h2, winU_some, if_neg hθb, if_pos hlt]
              simp [tierW_eq, show t + 1 ≤ P.tierI S (indexSlice w) by omega]
          · calc y ^ k * _ + Tier.winA x y q k * _ ≤ y ^ k * q + Tier.winA x y q k * x :=
                add_le_add (mul_le_mul' le_rfl (hq tried htr)) (mul_le_mul' le_rfl hA)
              _ = q * y ^ k + x * Tier.winA x y q k := by ring
        · -- dead
          rw [winU_some, if_neg hθb, if_neg hlt]
          refine (P.trialAvg_le_two (fun _ _ _ => False) (fun _ _ _ => False) 0 0 ?_).trans
            (by simp)
          intro η w fr _
          rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [tierB] at h1
            rw [h2, winU_some]
            have hn : ¬ θ η (indexSlice w) := fun h' => by rw [hθ _ _ h'] at h1; omega
            simp [hn, show ¬ t < P.tierI S (indexSlice w) by omega]
          · rw [h2, winU_some, if_neg hθb, if_neg hlt]
            simp

/-- A fresh trial of the run other than the best trial `b` holds the class of `b`. -/
def SelfCol (d : Cache) (M : EMessage) (c : Cache) (b : Nonce × Index) : Prop :=
  ∃ η, η ≠ b.1 ∧ d (P.encQuery (M ++ η)) = none ∧
    ∃ w, c (P.encQuery (M ++ η)) = some w ∧ P.cls w = some (P.digit b.2)

variable {P} in
theorem SelfCol.mono {d c c' : Cache} {M : EMessage} {b : Nonce × Index}
    (h : P.SelfCol d M c b) (hc : Cache.Sub c c') : P.SelfCol d M c' b := by
  obtain ⟨η, h1, h2, w, h3, h4⟩ := h
  exact ⟨η, h1, h2, w, hc _ _ h3, h4⟩

variable (S) in
/-- The value function of `win_sc_le`: open, hold without a self-collision, hold with one, dead. -/
def scU (d : Cache) (M : EMessage) (θ : Nonce → Index → Prop) (t : ℕ) (x y q r : ℝ≥0∞)
    (k : ℕ) (β : Option (Nonce × Index)) (c : Cache) : ℝ≥0∞ :=
  match β with
  | none => Tier.scB x y q r k
  | some b => if θ b.1 b.2 then
      (if P.SelfCol d M c b then y ^ k else (k : ℝ≥0∞) * r * y ^ (k - 1))
    else if t < P.tierI S b.2 then Tier.scB x y q r k else 0

theorem scU_none (d : Cache) (M : EMessage) (θ : Nonce → Index → Prop) (t : ℕ)
    (x y q r : ℝ≥0∞) (k : ℕ) (c : Cache) :
    P.scU S d M θ t x y q r k none c = Tier.scB x y q r k := rfl

theorem scU_some (d : Cache) (M : EMessage) (θ : Nonce → Index → Prop) (t : ℕ)
    (x y q r : ℝ≥0∞) (k : ℕ) (b : Nonce × Index) (c : Cache) :
    P.scU S d M θ t x y q r k (some b) c = if θ b.1 b.2 then
      (if P.SelfCol d M c b then y ^ k else (k : ℝ≥0∞) * r * y ^ (k - 1))
    else if t < P.tierI S b.2 then Tier.scB x y q r k else 0 := rfl

theorem sc_alg (y r : ℝ≥0∞) (k : ℕ) :
    y ^ k * r + (k : ℝ≥0∞) * r * y ^ (k - 1) * y = ((k + 1 : ℕ) : ℝ≥0∞) * r * y ^ (k + 1 - 1) := by
  rcases k with _ | k
  · simp
  · rw [Nat.add_sub_cancel, Nat.add_sub_cancel, mul_assoc _ (y ^ k), ← pow_succ]
    push_cast
    ring

/-- **K3.** The best trial is a target trial of tier `t` and class `v₀` and a fresh non-winning
trial holds `v₀`, with probability at most `q r SCK_t`. -/
theorem win_sc_le (hS : S.Valid) (hT : P.TierHyp S) {d : Cache} {M : EMessage}
    (hRG : P.RowGood S d M) (θ : Nonce → Index → Prop) {t : ℕ} (ht : t < S.T)
    (hθ : ∀ η I, θ η I → P.tierI S I = t) {v₀ : Cls} (hθv : ∀ η I, θ η I → P.digit I = v₀)
    {q r : ℝ≥0∞}
    (hq : ∀ tried : Finset Nonce, tried.card < trials →
      P.trialAvg d M tried (fun η w _ => if θ η (indexSlice w) then 1 else 0) ≤ q)
    (hr : ∀ tried : Finset Nonce, tried.card < trials →
      P.trialAvg d M tried (fun _ w fr => if fr = true ∧ P.cls w = some v₀ then 1 else 0) ≤ r) :
    E (run (P.signTier M) d)
        (fun p => if ∃ b, p.1 = some b ∧ θ b.1 b.2 ∧ P.SelfCol d M p.2 b then 1 else 0) ≤
      q * r * S.sckT t := by
  set x := S.yb (t + 1) with hx
  set y := S.yb t with hy
  have key := P.loop_value d M
    (fun β c => if ∃ b, β = some b ∧ θ b.1 b.2 ∧ P.SelfCol d M c b then 1 else 0)
    (fun k _ β c => P.scU S d M θ t x y q r k β c) ?_ ?_ trials ∅ none d (reach_init d M)
    (by simp)
  · unfold signTier
    refine key.trans (le_of_eq ?_)
    rw [scU_none, Tier.scB_eq, Tier.Sched.sckT]
    unfold trials
    rfl
  · intro tried β c _
    cases β with
    | none => simp
    | some b =>
      rw [scU_some]
      by_cases hb : θ b.1 b.2
      · by_cases hsc : P.SelfCol d M c b
        · simp [hb, hsc]
        · simp [hsc]
      · simp [hb]
  · intro k tried β c h hk
    beta_reduce
    have htr : tried.card < trials := by omega
    have hβ : ∀ b, β = some b → P.Accepted b.2 := fun b hb => (h.best b hb).2.1
    have hA := P.trialAvg_tier_ge hS hT hRG htr (t := t + 1) (by omega)
    have hB := P.trialAvg_tier_ge hS hT hRG htr (t := t) ht.le
    -- the cache after a trial extends the cache before it
    have hsub : ∀ η w fr, P.TrialOK d M tried η w fr →
        Cache.Sub c (if fr = true then c.cacheQuery (P.encQuery (M ++ η)) w else c) := by
      intro η w fr hok
      cases fr with
      | false => exact Cache.Sub.refl c
      | true =>
        have hce := h.cache_eq hok.1
        rw [hok.2.1 rfl] at hce
        exact Cache.sub_cacheQuery_of_none hce w
    -- no tried entry holds a class of tier `t` while the best trial is above `t`
    have hnosc : ∀ η w fr, P.TrialOK d M tried η w fr → t < P.tierB S β →
        θ η (indexSlice w) →
        ¬ P.SelfCol d M (if fr = true then c.cacheQuery (P.encQuery (M ++ η)) w else c)
          (η, indexSlice w) := by
      intro η w fr hok hopen hθη ⟨η', hne, hd', w'', hc'', hcls⟩
      have hc0 : c (P.encQuery (M ++ η')) = some w'' := by
        cases fr with
        | false => exact hc''
        | true =>
          simp only [if_true] at hc''
          rwa [QueryCache.cacheQuery_of_ne _ _ (fun he =>
            hne (append_nonce_inj M (P.encQuery_inj he)))] at hc''
      obtain ⟨η₂, hη₂, he⟩ := h.new _ _ hd' hc0
      have hη' : η' = η₂ := append_nonce_inj M (P.encQuery_inj he)
      subst hη'
      have hmin := h.min η' hη₂ w'' hc0
      have hacc : P.Accepted (indexSlice w) :=
        (tierI_lt_T hT).1 (by rw [hθ _ _ hθη]; exact ht)
      simp only at hcls
      have htier : P.tierI S (indexSlice w'') = t := by
        rw [← tierW_eq, tierW_eq_ctier hcls, ← tierI_eq_ctier hacc]
        exact hθ _ _ hθη
      have := (better_iff hS hT (indexSlice w'') hβ).2 (by omega)
      rw [hmin] at this
      exact Bool.false_ne_true this
    rcases β with _ | b
    · -- open, no best trial yet
      rw [scU_none, Tier.scB]
      refine (P.trialAvg_le_two (fun η w _ => θ η (indexSlice w))
        (fun _ w _ => t + 1 ≤ P.tierW S w) ((k : ℝ≥0∞) * r * y ^ (k - 1)) (Tier.scB x y q r k)
        ?_).trans ?_
      · intro η w fr hok
        rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2, scU_some]
          by_cases hθη : θ η (indexSlice w)
          · rw [if_pos hθη, if_neg (hnosc η w fr hok (by simp only [tierB]; exact ht) hθη)]
            simp [hθη]
          · by_cases hlt : t < P.tierI S (indexSlice w)
            · simp [hθη, hlt, tierW_eq, show t + 1 ≤ P.tierI S (indexSlice w) by omega]
            · simp [hθη, hlt]
        · rw [h2, scU_none]
          have : t + 1 ≤ P.tierW S w := by
            rw [tierW_eq]; simp only [tierB] at h1; omega
          simp [this]
      · calc (k : ℝ≥0∞) * r * y ^ (k - 1) * _ + Tier.scB x y q r k * _
            ≤ (k : ℝ≥0∞) * r * y ^ (k - 1) * q + Tier.scB x y q r k * x :=
            add_le_add (mul_le_mul' le_rfl (hq tried htr)) (mul_le_mul' le_rfl hA)
          _ = q * ((k : ℝ≥0∞) * r * y ^ (k - 1)) + x * Tier.scB x y q r k := by ring
    · have hbacc := hβ b rfl
      by_cases hθb : θ b.1 b.2
      · have htb : P.tierI S b.2 = t := hθ _ _ hθb
        by_cases hsc : P.SelfCol d M c b
        · -- hold with a self-collision
          rw [scU_some, if_pos hθb, if_pos hsc]
          refine (P.trialAvg_le_two (fun _ w _ => t ≤ P.tierW S w) (fun _ _ _ => False)
            (y ^ k) 0 ?_).trans ?_
          · intro η w fr hok
            rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp only [tierB] at h1
              rw [h2, scU_some]
              have hn : ¬ θ η (indexSlice w) := fun h' => by rw [hθ _ _ h'] at h1; omega
              simp [hn, show ¬ t < P.tierI S (indexSlice w) by omega]
            · simp only [tierB] at h1
              rw [h2, scU_some, if_pos hθb, if_pos (hsc.mono (hsub η w fr hok))]
              simp [tierW_eq, show t ≤ P.tierI S (indexSlice w) by omega]
          · calc y ^ k * _ + 0 * _ ≤ y ^ k * y := by
                  rw [zero_mul, add_zero]; exact mul_le_mul' le_rfl hB
              _ = y ^ (k + 1) := (pow_succ y k).symm
        · -- hold without a self-collision
          rw [scU_some, if_pos hθb, if_neg hsc]
          refine (P.trialAvg_le_two (fun _ w fr => fr = true ∧ P.cls w = some v₀)
            (fun _ w _ => t ≤ P.tierW S w) (y ^ k) ((k : ℝ≥0∞) * r * y ^ (k - 1)) ?_).trans ?_
          · intro η w fr hok
            rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp only [tierB] at h1
              rw [h2, scU_some]
              have hn : ¬ θ η (indexSlice w) := fun h' => by rw [hθ _ _ h'] at h1; omega
              simp [hn, show ¬ t < P.tierI S (indexSlice w) by omega]
            · simp only [tierB] at h1
              rw [h2, scU_some, if_pos hθb]
              have ht' : t ≤ P.tierW S w := by rw [tierW_eq]; omega
              by_cases hsc' : P.SelfCol d M
                  (if fr = true then c.cacheQuery (P.encQuery (M ++ η)) w else c) b
              · rw [if_pos hsc']
                have hdup : fr = true ∧ P.cls w = some v₀ := by
                  obtain ⟨η', hne, hd', w'', hc'', hcls⟩ := hsc'
                  cases fr with
                  | false => exact absurd ⟨η', hne, hd', w'', hc'', hcls⟩ hsc
                  | true =>
                    simp only [if_true] at hc''
                    by_cases hη : η' = η
                    · subst hη
                      rw [QueryCache.cacheQuery_self] at hc''
                      obtain rfl := Option.some.inj hc''
                      exact ⟨rfl, hcls.trans (by rw [hθv _ _ hθb])⟩
                    · rw [QueryCache.cacheQuery_of_ne _ _ (fun he =>
                        hη (append_nonce_inj M (P.encQuery_inj he)))] at hc''
                      exact absurd ⟨η', hne, hd', w'', hc'', hcls⟩ hsc
                simp [hdup, ht']
              · rw [if_neg hsc']
                simp [ht']
          · calc y ^ k * _ + (k : ℝ≥0∞) * r * y ^ (k - 1) * _
                ≤ y ^ k * r + (k : ℝ≥0∞) * r * y ^ (k - 1) * y :=
                add_le_add (mul_le_mul' le_rfl (hr tried htr)) (mul_le_mul' le_rfl hB)
              _ = _ := sc_alg y r k
      · by_cases hlt : t < P.tierI S b.2
        · -- open
          rw [scU_some, if_neg hθb, if_pos hlt, Tier.scB]
          refine (P.trialAvg_le_two (fun η w _ => θ η (indexSlice w))
            (fun _ w _ => t + 1 ≤ P.tierW S w) ((k : ℝ≥0∞) * r * y ^ (k - 1))
            (Tier.scB x y q r k) ?_).trans ?_
          · intro η w fr hok
            rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h2, scU_some]
              by_cases hθη : θ η (indexSlice w)
              · rw [if_pos hθη, if_neg (hnosc η w fr hok (by simp only [tierB]; exact hlt) hθη)]
                simp [hθη]
              · by_cases hlt' : t < P.tierI S (indexSlice w)
                · simp [hθη, hlt', tierW_eq, show t + 1 ≤ P.tierI S (indexSlice w) by omega]
                · simp [hθη, hlt']
            · simp only [tierB] at h1
              rw [h2, scU_some, if_neg hθb, if_pos hlt]
              simp [tierW_eq, show t + 1 ≤ P.tierI S (indexSlice w) by omega]
          · calc (k : ℝ≥0∞) * r * y ^ (k - 1) * _ + Tier.scB x y q r k * _
                ≤ (k : ℝ≥0∞) * r * y ^ (k - 1) * q + Tier.scB x y q r k * x :=
                add_le_add (mul_le_mul' le_rfl (hq tried htr)) (mul_le_mul' le_rfl hA)
              _ = q * ((k : ℝ≥0∞) * r * y ^ (k - 1)) + x * Tier.scB x y q r k := by ring
        · -- dead
          rw [scU_some, if_neg hθb, if_neg hlt]
          refine (P.trialAvg_le_two (fun _ _ _ => False) (fun _ _ _ => False) 0 0 ?_).trans
            (by simp)
          intro η w fr _
          rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [tierB] at h1
            rw [h2, scU_some]
            have hn : ¬ θ η (indexSlice w) := fun h' => by rw [hθ _ _ h'] at h1; omega
            simp [hn, show ¬ t < P.tierI S (indexSlice w) by omega]
          · rw [h2, scU_some, if_neg hθb, if_neg hlt]
            simp

variable (S) in
/-- The value function of `tail_le`. -/
def tailU (t : ℕ) (y : ℝ≥0∞) (k : ℕ) (β : Option (Nonce × Index)) : ℝ≥0∞ :=
  if t ≤ P.tierB S β then y ^ k else 0

/-- **K4.** No trial has tier `< t` with probability at most `ȳ_t ^ L`. -/
theorem tail_le (hS : S.Valid) (hT : P.TierHyp S) {d : Cache} {M : EMessage}
    (hRG : P.RowGood S d M) {t : ℕ} (ht : t ≤ S.T) :
    E (run (P.signTier M) d) (fun p => if t ≤ P.tierB S p.1 then 1 else 0) ≤
      S.yb t ^ trials := by
  have key := P.loop_value d M (fun β _ => if t ≤ P.tierB S β then 1 else 0)
    (fun k _ β _ => P.tailU S t (S.yb t) k β) ?_ ?_ trials ∅ none d (reach_init d M) (by simp)
  · unfold signTier
    refine key.trans (le_of_eq ?_)
    simp [tailU, tierB, ht]
  · intro tried β c _
    simp only [tailU]
    split_ifs <;> simp
  · intro k tried β c h hk
    beta_reduce
    have htr : tried.card < trials := by omega
    have hβ : ∀ b, β = some b → P.Accepted b.2 := fun b hb => (h.best b hb).2.1
    have hB := P.trialAvg_tier_ge hS hT hRG htr ht
    by_cases hle : t ≤ P.tierB S β
    · simp only [tailU, if_pos hle]
      refine (P.trialAvg_le_two (fun _ w _ => t ≤ P.tierW S w) (fun _ _ _ => False)
        (S.yb t ^ k) 0 ?_).trans ?_
      · intro η w fr _
        rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2]
          by_cases hc : t ≤ P.tierI S (indexSlice w) <;> simp [tailU, tierB, tierW_eq, hc]
        · rw [h2]
          simp only [tailU, if_pos hle, tierW_eq, show t ≤ P.tierI S (indexSlice w) by omega]
          simp
      · calc S.yb t ^ k * _ + 0 * _ ≤ S.yb t ^ k * S.yb t := by
              rw [zero_mul, add_zero]; exact mul_le_mul' le_rfl hB
          _ = S.yb t ^ (k + 1) := (pow_succ _ k).symm
    · simp only [tailU, if_neg hle]
      refine (P.trialAvg_le_two (fun _ _ _ => False) (fun _ _ _ => False) 0 0 ?_).trans
        (by simp)
      intro η w fr _
      rcases P.upd_cases hS hT hβ η (indexSlice w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        have hc : ¬ t ≤ P.tierI S (indexSlice w) := by omega
        simp [tailU, tierB, hc]
      · rw [h2]
        simp [tailU, if_neg hle]

theorem tierE_add {α : Type} (p : ProbComp α) (f g : α → ℝ≥0∞) :
    E p (fun x => f x + g x) = E p f + E p g := expectedValue_add _ _ _

theorem tierE_const_mul {α : Type} (p : ProbComp α) (a : ℝ≥0∞) (f : α → ℝ≥0∞) :
    E p (fun x => a * f x) = a * E p f := by
  rw [E, E, mul_comm, ← expectedValue_mul_const]
  exact congrArg _ (funext fun x => mul_comm _ _)

theorem tierE_sum {α J : Type} (p : ProbComp α) (s : Finset J) (f : J → α → ℝ≥0∞) :
    E p (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, E p (f j) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [E, expectedValue_def]
    simp
  | cons j s hj ih =>
    simp only [Finset.sum_cons]
    rw [tierE_add, ih]

variable (S) in
/-- The post-sign rate after the outcome `r`: `max(2^-128, p/2)`. -/
def kappaB : Option (Nonce × Index) → ℝ≥0∞
  | none => (2 ^ 128 : ℝ≥0∞)⁻¹
  | some b => (2 ^ 128 : ℝ≥0∞)⁻¹ + S.fE (P.tierI S b.2) / 2

/-- **K5.** The average post-sign rate. -/
theorem kappaB_le (hS : S.Valid) (hT : P.TierHyp S) {d : Cache} {M : EMessage}
    (hRG : P.RowGood S d M) :
    E (run (P.signTier M) d) (fun p => P.kappaB S p.1) ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ENNReal.ofReal S.Pos / 2 := by
  set Δ : ℕ → ℝ≥0∞ := fun t => S.fE t - if t = 0 then 0 else S.fE (t - 1) with hΔ
  have hpt : ∀ p ∈ support (run (P.signTier M) d), P.kappaB S p.1 ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ∑ t ∈ Finset.range S.T,
        Δ t / 2 * (if t ≤ P.tierB S p.1 then 1 else 0) := by
    intro p hp
    obtain ⟨-, -, hbest⟩ := P.signTier_ext M d p hp
    rcases hr : p.1 with _ | b
    · exact le_self_add
    · have hacc := (hbest b hr).1
      have hτ := (tierI_spec hT hacc).1
      set τ := P.tierI S b.2 with hτdef
      have hsum : ∑ t ∈ Finset.range S.T, Δ t / 2 * (if t ≤ P.tierB S (some b) then 1 else 0) =
          ∑ t ∈ Finset.range (τ + 1), Δ t / 2 := by
        rw [← Finset.sum_range_add_sum_Ico _ (show τ + 1 ≤ S.T by omega),
          Finset.sum_eq_zero (s := Finset.Ico (τ + 1) S.T), add_zero]
        · refine Finset.sum_congr rfl fun t ht => ?_
          have : t ≤ τ := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
          simp [tierB, ← hτdef, this]
        · intro t ht
          have : ¬ t ≤ τ := by
            have := (Finset.mem_Ico.1 ht).1
            omega
          simp [tierB, ← hτdef, this]
      simp only [kappaB]
      rw [hsum, S.fE_telescope hS hτ]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      exact le_rfl
  calc E (run (P.signTier M) d) (fun p => P.kappaB S p.1)
      ≤ E (run (P.signTier M) d) (fun p => (2 ^ 128 : ℝ≥0∞)⁻¹ + ∑ t ∈ Finset.range S.T,
          Δ t / 2 * (if t ≤ P.tierB S p.1 then 1 else 0)) :=
        expectedValue_mono_of_support hpt
    _ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ + ∑ t ∈ Finset.range S.T, Δ t / 2 * min 1 (S.yb t ^ 2 ^ 19) := by
        rw [tierE_add, tierE_sum]
        refine add_le_add (expectedValue_le_of_le _ fun _ => le_rfl) (Finset.sum_le_sum ?_)
        intro t ht
        rw [tierE_const_mul]
        refine mul_le_mul' le_rfl (le_min ?_ ?_)
        · exact expectedValue_le_of_le _ fun _ => by split_ifs <;> simp
        · have := P.tail_le hS hT hRG (t := t) (Finset.mem_range.1 ht).le
          unfold trials at this
          exact this
    _ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ + ENNReal.ofReal S.Pos / 2 := by
        refine add_le_add le_rfl ?_
        calc ∑ t ∈ Finset.range S.T, Δ t / 2 * min 1 (S.yb t ^ 2 ^ 19)
            = (∑ t ∈ Finset.range S.T, Δ t * min 1 (S.yb t ^ 2 ^ 19)) / 2 := by
              simp only [div_eq_mul_inv, Finset.sum_mul]
              refine Finset.sum_congr rfl fun t _ => ?_
              ring
          _ ≤ ENNReal.ofReal S.Pos / 2 := by
              gcongr
              exact S.sum_pos_le hS

end Params

end OptimalOTS.LeanIsaBaseline.Layer
