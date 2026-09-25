import Submissions.UpperLeanIsa.FusionEvents
import Submissions.UpperLeanIsa.IdxCharges
import Submissions.UpperLeanIsa.TierLoss

/-!
# The second stage

After the first stage ended with cache `d` and signing added the index entries `d' ⊇ d`
(`TierExt`), the second attacker stage and the verifier run from `extend d' (hidden₀ ξ)`.

* `stageB_none` (signing failed): the hidden points before signing are removed by
  identical-until-bad, and an accepted pair is a hidden hit or a cut target at the cut before
  signing (`events_none`); each costs `2 ^ -129` per compression.
* `stageB_fiber` (signing returned `(η₁, I₁)`, one public fiber after signing): the hidden
  points below the signed cut are removed by identical-until-bad; an accepted fresh pair is a
  hidden hit, a cut target, or a *new* index entry with the class of `I₁` (`IdxPost`), provided
  no entry of the first stage other than the signed one held that class (`IdxPreC`) and no other
  trial of the signer did (`SelfCol`); both are charged to signing. The three events are charged
  in one potential `ΦB` by query shape: a chain step or root call pays the hidden charge and one
  target charge (`2 · 2 ^ -129 = 2 ^ -128` per compression), and an index query only the
  `IdxPost` charge `p(I₁)` per query of two compressions, so the potential grows by at most any
  rate `ρ ≥ max(2 ^ -128, p(I₁) / 2)` per compression.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Layer.Params.encQuery
  publicFiber finiteFiber publicData hiddenCache exposedCache queryLocation Record.query

/-! ## Expectation helpers -/

theorem E_finset_sum {α J : Type} (p : ProbComp α) (S : Finset J) (f : J → α → ℝ≥0∞) :
    E p (fun x => ∑ j ∈ S, f j x) = ∑ j ∈ S, E p (f j) := by
  let : DecidableEq J := Classical.decEq J
  induction S using Finset.induction_on with
  | empty => simp [E, expectedValue_def]
  | @insert j S hj ih =>
    simp only [Finset.sum_insert hj, E, expectedValue_add]
    exact congrArg (fun t => E p (f j) + t) ih

theorem E_const_mul {α : Type} (p : ProbComp α) (w : ℝ≥0∞) (f : α → ℝ≥0∞) :
    E p (fun x => w * f x) = w * E p f := by
  rw [E, E, mul_comm, ← expectedValue_mul_const]
  exact congrArg _ (funext fun x => mul_comm _ _)

theorem E_weighted_sum {α J : Type} (p : ProbComp α) (S : Finset J)
    (w : ℝ≥0∞) (f : J → α → ℝ≥0∞) :
    E p (fun x => ∑ j ∈ S, w * f j x) = ∑ j ∈ S, w * E p (f j) := by
  rw [E_finset_sum]
  exact Finset.sum_congr rfl fun j _ => E_const_mul p w (f j)

theorem E_add' {α : Type} (p : ProbComp α) (f h : α → ℝ≥0∞) :
    E p (fun x => f x + h x) = E p f + E p h := expectedValue_add _ _ _

/-- The success indicator. -/
def g (p : Bool × Cache) : ℝ≥0∞ := if p.1 = true then 1 else 0

theorem g_le_one (p : Bool × Cache) : g p ≤ 1 := by
  unfold g
  split_ifs <;> simp

/-- The security rate per compression, `2 ^ -127`. -/
def κ : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 127)⁻¹

theorem κ_eq : κ = ((2 : ℝ≥0∞) ^ 127)⁻¹ := rfl

theorem two_rate_le_κ : 2 * rate ≤ κ := by
  rw [mul_comm, rate_two, κ_eq]
  exact ENNReal.inv_le_inv.mpr (by norm_num)

/-- A potential charged at every fresh query bounds every adaptive computation. -/
theorem potential_bound {α : Type} (Φ : Cache → ℝ≥0∞) (κ' : ℝ≥0∞)
    (hΦ : ∀ c q, c q = none →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) ≤
        Φ c + κ' * queryCost (.inr q))
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ) (hB : CostAtMost oa B) :
    E (run oa c) (fun p => Φ p.2) ≤ Φ c + κ' * B :=
  master_single κ' Φ (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) (fun c _ q _ hq _ => hΦ c q hq) oa (fun _ c => Φ c)
    (fun _ _ => le_rfl) c B trivial hB

theorem two_le_queryCost_896 {q : Query} (hw : q.1 = 896) : (2 : ℝ≥0∞) = queryCost (.inr q) := by
  rw [queryCost_896 hw, Nat.cast_ofNat]

namespace Params

variable (P : Params) (A : OracleAlgorithm.Adversary)

/-! ## Index entries and record caches -/

theorem record_query_ne_encQuery (hP : P.SecurityHyp) (ξ : Record P) (a : Loc P) (u : EncInput) :
    ξ.query a ≠ P.codec.encQuery u := by
  obtain ⟨M,η,rfl⟩ := exists_append u
  obtain ⟨m,pk,rfl⟩ := exists_emsg M
  rw [P.codec.encQuery_emsg]
  exact ξ.query_ne_idx hP a m η pk

theorem raw_query_ne_encQuery (hP : P.SecurityHyp) (a : RawInput P) (u : EncInput) :
    a.query ≠ P.codec.encQuery u := by
  obtain ⟨M,η,rfl⟩ := exists_append u
  obtain ⟨m,pk,rfl⟩ := exists_emsg M
  rw [P.codec.encQuery_emsg]
  exact a.query_ne_idx hP m η pk

theorem not_loc_enc (hP : P.SecurityHyp) (u : EncInput) :
    ∀ (ζ : Record P) (a : Loc P), ζ.query a ≠ P.codec.encQuery u :=
  fun ζ a => P.record_query_ne_encQuery hP ζ a u

theorem hiddenCache_enc (hP : P.SecurityHyp) (d : Cut) (ξ : Record P) (u : EncInput) :
    hiddenCache d ξ (P.codec.encQuery u) = none :=
  hiddenCache_of_not_loc hP d ξ _ (P.not_loc_enc hP u)

theorem exposedCache_enc (hP : P.SecurityHyp) (d : Cut) (ξ : Record P) (u : EncInput) :
    exposedCache d ξ (P.codec.encQuery u) = none := by
  rcases h : exposedCache d ξ (P.codec.encQuery u) with _ | w
  · rfl
  · obtain ⟨a, -, ha, -⟩ := (exposedCache_some_iff hP d ξ _ w).mp h
    exact absurd ha (P.record_query_ne_encQuery hP ξ a u)

/-- A query that is a record location is not an index query. -/
theorem not_enc_of_loc (hP : P.SecurityHyp) {q : Query} {ζ : Record P} {a : Loc P}
    (h : ζ.query a = q) : ∀ u : EncInput, q ≠ P.codec.encQuery u := by
  intro u he
  exact P.record_query_ne_encQuery hP ζ a u (h.trans he)

/-! ## Caches after signing -/

/-- The entries that a signing run adds are index entries. -/
def EncExt (d d' : Cache) : Prop :=
  Cache.Sub d d' ∧ ∀ q u, d q = none → d' q = some u → ∃ u', q = P.codec.encQuery u'

theorem encExt_of_tierExt {M : EMessage} {d d' : Cache} {r : Option (Nonce × Index)}
    (h : P.codec.TierExt M d r d') : P.EncExt d d' := by
  refine ⟨h.1, fun q u h1 h2 => ?_⟩
  obtain ⟨η, hq⟩ := h.2.1 q u h1 h2
  exact ⟨M ++ η, hq⟩

theorem EncExt.none_of {d d' : Cache} (h : P.EncExt d d') {q : Query}
    (hq : ∀ u, q ≠ P.codec.encQuery u) (hd : d q = none) : d' q = none := by
  rcases h' : d' q with _ | u
  · rfl
  · obtain ⟨u', hu'⟩ := h.2 q u hd h'
    exact absurd hu' (hq u')

theorem EncExt.not_hits {d d' : Cache} (h : P.EncExt d d') {f : Cache}
    (hf : ∀ u, f (P.codec.encQuery u) = none) (hh : ¬ Cache.Hits d f) : ¬ Cache.Hits d' f := by
  rintro ⟨q, hfq, hdq⟩
  rcases hd : d q with _ | u
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hdq
    obtain ⟨u', rfl⟩ := h.2 q v hd hv
    rw [hf u'] at hfq
    exact absurd hfq (by simp)
  · exact hh ⟨q, hfq, by simp [hd]⟩

theorem EncExt.targetHit {d d' : Cache} (h : P.EncExt d d')
    {targets : Query → Finset (BitVec hashBits)} (ht : ∀ u, targets (P.codec.encQuery u) = ∅)
    (hh : TargetHit targets d') : TargetHit targets d := by
  obtain ⟨q, u, hq, hu⟩ := hh
  rcases hd : d q with _ | v
  · obtain ⟨u', rfl⟩ := h.2 q u hd hq
    rw [ht u'] at hu
    exact absurd hu (Finset.notMem_empty _)
  · have := h.1 q v hd
    rw [hq] at this
    cases this
    exact ⟨q, u, hd, hu⟩

theorem cutTargets_enc (hP : P.SecurityHyp) (d : Cut) (ζ : Record P) (u : EncInput) :
    cutTargets P d ζ (P.codec.encQuery u) = ∅ := (targets_of_not_loc (fun a => P.raw_query_ne_encQuery hP a u) d ζ).1

theorem spr_enc (hP : P.SecurityHyp) (ζ : Record P) (u : EncInput) :
    secondPreimageTargets P ζ (P.codec.encQuery u) = ∅ :=
  (targets_of_not_loc (fun a => P.raw_query_ne_encQuery hP a u) (beforeSigning P) ζ).2

/-! ## Adaptive bounds -/

/-- Hidden hits of a subset of a public fiber: `rate · sumW (fiber)` per compression. -/
theorem hiddenHit_charge (hP : P.SecurityHyp) {d : Cut} (hd : ValidCut P d) (v : PublicData P)
    (T : Finset (Record P)) (hT : T ⊆ publicFiber d v) (c : Cache) (q : Query) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * hiddenHitPotential d T (c.cacheQuery q u) ≤
      hiddenHitPotential d T c + rate * sumW P (publicFiber d v) * queryCost (.inr q) :=
  avg_le_of_le _ _ fun u => (hiddenHitPotential_cacheQuery d T c q u).trans
    (add_le_add le_rfl (hiddenHit_increment_le hP hd v T hT q))

theorem hiddenHit_charge_enc (hP : P.SecurityHyp) (d : Cut) (T : Finset (Record P)) (c : Cache)
    (u₀ : EncInput) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        hiddenHitPotential d T (c.cacheQuery (P.codec.encQuery u₀) u) ≤ hiddenHitPotential d T c :=
  avg_le_of_le _ _ fun u => by
    have h := hiddenHitPotential_cacheQuery d T c (P.codec.encQuery u₀) u
    rw [hiddenHit_increment_zero hP d T _ (P.not_loc_enc hP u₀), add_zero] at h
    exact h

theorem hidden_hit_bound_subset {α : Type} (hP : P.SecurityHyp) {d : Cut} (hd : ValidCut P d)
    (v : PublicData P) (T : Finset (Record P)) (hT : T ⊆ publicFiber d v)
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ) (hB : CostAtMost oa B)
    (hc : ∀ ξ ∈ T, Cache.Disjoint c (hiddenCache d ξ)) :
    E (run oa c) (fun p => hiddenHitPotential d T p.2) ≤ rate * sumW P (publicFiber d v) * B := by
  have h := potential_bound (hiddenHitPotential d T) (rate * sumW P (publicFiber d v))
    (fun c q _ => P.hiddenHit_charge hP hd v T hT c q) oa c B hB
  rwa [hiddenHitPotential_zero d T c hc, zero_add] at h

theorem cutTargets_hit_bound {α : Type} (d : Cut) (ζ : Record P) (oa : OracleComp Spec α)
    (c : Cache) (B : ℕ) (hB : CostAtMost oa B) (hc : ¬ TargetHit (cutTargets P d ζ) c) :
    E (run oa c) (fun p => ind (TargetHit (cutTargets P d ζ) p.2)) ≤ rate * B := by
  have h := potential_bound (fun c => ind (TargetHit (cutTargets P d ζ) c)) rate
    (fun c q hq => (ind_target_charge _ c q hq).trans
      (add_le_add le_rfl (cutTargets_charge d ζ q))) oa c B hB
  rwa [ind_not hc, zero_add] at h

/-! ## Cache algebra -/

/-- Before signing all chain points of `ξ` are hidden; at a later cut only those below it. If
`c` holds the points exposed before signing, the difference moves into the exposed cache. -/
theorem extend_hidden_shift (hP : P.SecurityHyp) (c : Cache) (ξ : Record P) (d₁ : Cut)
    (hc : Cache.Sub (exposedCache (beforeSigning P) ξ) c) :
    Cache.extend c (hiddenCache (beforeSigning P) ξ) =
      Cache.extend (Cache.extend c (exposedCache d₁ ξ)) (hiddenCache d₁ ξ) := by
  rw [Cache.extend_assoc, exposure_partition]
  funext q
  rw [Cache.extend_apply, Cache.extend_apply]
  rcases hq : ξ.cache q with _ | u
  · have hh : hiddenCache (beforeSigning P) ξ q = none := by
      rcases hh' : hiddenCache (beforeSigning P) ξ q with _ | u
      · rfl
      · obtain ⟨a, -, haq, -⟩ := (hiddenCache_some_iff hP _ ξ q u).mp hh'
        rw [← haq, Record.cache_query hP] at hq
        exact absurd hq (Option.some_ne_none _)
    rw [hh]
  · obtain ⟨a, haq, hau⟩ := (ξ.cache_some_iff hP q u).mp hq
    cases a with
    | inl x =>
      rw [(hiddenCache_some_iff hP _ ξ q u).mpr ⟨.inl x, hiddenBefore_inl x, haq, hau⟩]
    | inr r =>
      have hdq : c q = some u :=
        hc q u ((exposedCache_some_iff hP _ ξ q u).mpr ⟨.inr r, not_hidden_inr _ r, haq, hau⟩)
      simp only [hdq, Option.some_or]

/-- A cache holding the exposed points of `ξ` before signing, extending a first-stage cache
without hidden hits by index entries only, agrees with the points of `ξ` exposed at any cut. -/
theorem sub_exposed_after (hP : P.SecurityHyp) (d d' : Cache) (ξ : Record P) (d₁ : Cut)
    (hext : P.EncExt d d') (hd : Cache.Sub (exposedCache (beforeSigning P) ξ) d)
    (hh : ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ)) :
    Cache.Sub (exposedCache d₁ ξ) (Cache.extend d' (exposedCache d₁ ξ)) := by
  intro q u hq
  obtain ⟨a, -, haq, hau⟩ := (exposedCache_some_iff hP _ ξ q u).mp hq
  cases a with
  | inl x =>
    have hdq : d q = none :=
      none_of_not_hits_hidden hP d ξ hh (.inl x) (hiddenBefore_inl x) haq
    rw [Cache.extend_apply_of_none (EncExt.none_of P hext (P.not_enc_of_loc hP haq) hdq)]
    exact hq
  | inr r =>
    exact Cache.extend_apply_of_some (hext.1 q u (hd q u
      ((exposedCache_some_iff hP _ ξ q u).mpr ⟨.inr r, not_hidden_inr _ r, haq, hau⟩)))

theorem disjoint_after (hP : P.SecurityHyp) (d d' : Cache) (ξ : Record P) (d₁ : Cut)
    (hext : P.EncExt d d') (hh : ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ)) :
    Cache.Disjoint (Cache.extend d' (exposedCache d₁ ξ)) (hiddenCache d₁ ξ) := by
  intro q hq
  obtain ⟨a, ha, haq⟩ := (hiddenCache_isSome_iff hP d₁ ξ q).mp hq
  have hdq : d q = none := none_of_not_hits_hidden hP d ξ hh a (hiddenBefore_of_hidden ha) haq
  rw [Cache.extend_apply, EncExt.none_of P hext (P.not_enc_of_loc hP haq) hdq,
    exposure_disjoint d₁ ξ q hq, Option.none_or]

theorem disjoint_before (hP : P.SecurityHyp) (d d' : Cache) (ξ : Record P)
    (hext : P.EncExt d d') (hh : ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ)) :
    Cache.Disjoint d' (hiddenCache (beforeSigning P) ξ) := by
  intro q hq
  obtain ⟨a, ha, haq⟩ := (hiddenCache_isSome_iff hP _ ξ q).mp hq
  exact EncExt.none_of P hext (P.not_enc_of_loc hP haq)
    (none_of_not_hits_hidden hP d ξ hh a ha haq)

theorem extend_of_sub {c f : Cache} (h : Cache.Sub f c) : Cache.extend c f = c := by
  funext q
  rw [Cache.extend_apply]
  rcases hf : f q with _ | u
  · simp
  · rw [h q u hf]
    rfl

theorem avg_add' (f h : BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (f u + h u) =
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f u +
        ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * h u := by
  simp only [mul_add, Finset.sum_add_distrib]

theorem avg_mul' (s : ℝ≥0∞) (f : BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (s * f u) =
      s * ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f u := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => mul_left_comm _ _ _

/-! ## Stage B after a signing failure -/

theorem stageB_none (hP : P.SecurityHyp) (pk : PublicKey) (m₁ : Message) (st : A.State)
    (v : PublicData P) (T : Finset (Record P)) (hT : T ⊆ publicFiber (beforeSigning P) v)
    (hpk : ∀ ξ ∈ T, ξ.pk = pk) (d d' : Cache) (hext : P.EncExt d d')
    (hd : ∀ ξ ∈ T, Cache.Sub (exposedCache (beforeSigning P) ξ) d ∧
      ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ) ∧
      ¬ TargetHit (secondPreimageTargets P ξ) d)
    (b' : ℕ) (hb : CostAtMost (P.stB A pk m₁ st none) b') :
    ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st none)
        (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g ≤
      2 * rate * sumW P (publicFiber (beforeSigning P) v) * b' := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨ξ₀, hξ₀⟩
  · rw [hTe, Finset.sum_empty]
    exact bot_le
  have hdata : ∀ ξ ∈ T, publicData (beforeSigning P) ξ = publicData (beforeSigning P) ξ₀ :=
    fun ξ hξ => ((mem_publicFiber _ _ _).mp (hT hξ)).trans ((mem_publicFiber _ _ _).mp (hT hξ₀)).symm
  have hcut : ∀ ξ ∈ T, cutTargets P (beforeSigning P) ξ = cutTargets P (beforeSigning P) ξ₀ :=
    fun ξ hξ => cutTargets_public beforeSigning_valid ξ ξ₀ (hdata ξ hξ)
  have hdisj : ∀ ξ ∈ T, Cache.Disjoint d' (hiddenCache (beforeSigning P) ξ) :=
    fun ξ hξ => P.disjoint_before hP d d' ξ hext (hd ξ hξ).2.1
  have hsub : ∀ ξ ∈ T, Cache.Sub (exposedCache (beforeSigning P) ξ) d' :=
    fun ξ hξ => (hd ξ hξ).1.trans hext.1
  have hct : ¬ TargetHit (cutTargets P (beforeSigning P) ξ₀) d' := by
    intro h
    have h1 := EncExt.targetHit P hext (P.cutTargets_enc hP _ ξ₀) h
    have heq : Cache.extend d (exposedCache (beforeSigning P) ξ₀) = d :=
      extend_of_sub (hd ξ₀ hξ₀).1
    exact no_cutTargets_initial hP (beforeSigning P) ξ₀ d (hd ξ₀ hξ₀).2.1 (hd ξ₀ hξ₀).2.2
      (heq.symm ▸ h1)
  have hstep : ∀ ξ ∈ T,
      E (run (P.stB A pk m₁ st none) (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g ≤
        E (run (P.stB A pk m₁ st none) d') (fun p =>
          ind (Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ)) +
            ind (TargetHit (cutTargets P (beforeSigning P) ξ₀) p.2)) := by
    intro ξ hξ
    refine (iub _ (hiddenCache (beforeSigning P) ξ) g g_le_one d' (hdisj ξ hξ)).trans ?_
    refine expectedValue_mono_of_support fun p hp => ?_
    by_cases hh : Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ)
    · rw [if_pos hh, ind_of hh]
      exact le_self_add
    · rw [if_neg hh, ind_not hh, zero_add]
      by_cases hok : p.1 = true
      · have hg : g (p.1, Cache.extend p.2 (hiddenCache (beforeSigning P) ξ)) = 1 := by
          show (if p.1 = true then (1 : ℝ≥0∞) else 0) = 1
          rw [if_pos hok]
        rw [hg]
        rcases events_none A hP pk m₁ st ξ d' (hsub ξ hξ) (hpk ξ hξ) p hp hok with h | h
        · exact absurd h hh
        · rw [hcut ξ hξ] at h
          exact (ind_of h).ge
      · have hg : g (p.1, Cache.extend p.2 (hiddenCache (beforeSigning P) ξ)) = 0 := by
          show (if p.1 = true then (1 : ℝ≥0∞) else 0) = 0
          rw [if_neg hok]
        rw [hg]
        exact bot_le
  calc ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st none)
          (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g
      ≤ ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st none) d') (fun p =>
          ind (Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ)) +
            ind (TargetHit (cutTargets P (beforeSigning P) ξ₀) p.2)) :=
        Finset.sum_le_sum fun ξ hξ => mul_le_mul' le_rfl (hstep ξ hξ)
    _ = E (run (P.stB A pk m₁ st none) d') (fun p => hiddenHitPotential (beforeSigning P) T p.2) +
          sumW P T * E (run (P.stB A pk m₁ st none) d')
            (fun p => ind (TargetHit (cutTargets P (beforeSigning P) ξ₀) p.2)) := by
        unfold hiddenHitPotential
        rw [E_weighted_sum, sumW, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [← mul_add, E_add']
    _ ≤ rate * sumW P (publicFiber (beforeSigning P) v) * b' + sumW P T * (rate * b') :=
        add_le_add (P.hidden_hit_bound_subset hP beforeSigning_valid v T hT _ d' b' hb hdisj)
          (mul_le_mul' le_rfl (P.cutTargets_hit_bound _ ξ₀ _ d' b' hb hct))
    _ ≤ rate * sumW P (publicFiber (beforeSigning P) v) * b' +
          sumW P (publicFiber (beforeSigning P) v) * (rate * b') :=
        add_le_add le_rfl (mul_le_mul' (sumW_mono hT) le_rfl)
    _ = 2 * rate * sumW P (publicFiber (beforeSigning P) v) * b' := by ring

/-! ## Stage B after signing index `I₁` -/

/-- The potential of the second stage after signing an index of class `v`: hidden hits of the
records `T`, cut targets of `ζ`, and new index entries of class `v`. -/
def ΦB (d₁ : Cut) (T : Finset (Record P)) (ζ : Record P) (d' : Cache) (v : Cls) (c : Cache) :
    ℝ≥0∞ :=
  hiddenHitPotential d₁ T c +
    sumW P T * (ind (TargetHit (cutTargets P d₁ ζ) c) + ind (P.codec.IdxPost d' c v))

theorem ΦB_charge (hP : P.SecurityHyp) {d₁ : Cut} (hd₁ : ValidCut P d₁) (v₁ : PublicData P)
    (T : Finset (Record P)) (hT : T ⊆ publicFiber d₁ v₁) (ζ : Record P) (d' : Cache) (v : Cls)
    {ρ : ℝ≥0∞} (hρ₁ : 2 * rate ≤ ρ) (hρ₂ : (P.codec.cweight v : ℝ≥0∞) / 2 ^ 127 ≤ ρ * 2)
    (c : Cache) (q : Query) (hq : c q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * P.ΦB d₁ T ζ d' v (c.cacheQuery q u) ≤
      P.ΦB d₁ T ζ d' v c + ρ * sumW P (publicFiber d₁ v₁) * queryCost (.inr q) := by
  unfold ΦB
  rw [avg_add', avg_mul', avg_add']
  by_cases henc : ∃ u₀, q = P.codec.encQuery u₀
  · obtain ⟨u₀, rfl⟩ := henc
    have h1 := P.hiddenHit_charge_enc hP d₁ T c u₀
    have h2 : ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ind (TargetHit (cutTargets P d₁ ζ) (c.cacheQuery (P.codec.encQuery u₀) u)) =
          ind (TargetHit (cutTargets P d₁ ζ) c) := by
      have he : ∀ u, ind (TargetHit (cutTargets P d₁ ζ) (c.cacheQuery (P.codec.encQuery u₀) u)) =
          ind (TargetHit (cutTargets P d₁ ζ) c) := fun u =>
        ind_congr (targetHit_cacheQuery_of_empty _ c _ u (P.cutTargets_enc hP d₁ ζ u₀))
      simp only [he]
      exact sum_inv_card_mul _
    have h3 := P.codec.idxPost_charge d' c u₀ hq v
    have hcost : (2 : ℝ≥0∞) = queryCost (.inr (P.codec.encQuery u₀)) :=
      two_le_queryCost_896 (by unfold Layer.Params.encQuery; rfl)
    have hs := sumW_mono (P := P) hT
    calc _ ≤ hiddenHitPotential d₁ T c + sumW P T *
          (ind (TargetHit (cutTargets P d₁ ζ) c) +
            ((if P.codec.IdxPost d' c v then 1 else 0) + (P.codec.cweight v : ℝ≥0∞) / 2 ^ 127)) := by
          refine add_le_add h1 (mul_le_mul' le_rfl (add_le_add (le_of_eq h2) ?_))
          exact h3
      _ = hiddenHitPotential d₁ T c + sumW P T *
            (ind (TargetHit (cutTargets P d₁ ζ) c) + ind (P.codec.IdxPost d' c v)) +
          sumW P T * ((P.codec.cweight v : ℝ≥0∞) / 2 ^ 127) := by
          unfold ind
          ring
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [← hcost]
          calc sumW P T * ((P.codec.cweight v : ℝ≥0∞) / 2 ^ 127)
              ≤ sumW P (publicFiber d₁ v₁) * (ρ * 2) := mul_le_mul' hs hρ₂
            _ = ρ * sumW P (publicFiber d₁ v₁) * 2 := by ring
  · have hne : ∀ u, q ≠ P.codec.encQuery u := fun u h => henc ⟨u, h⟩
    have h1 := P.hiddenHit_charge hP hd₁ v₁ T hT c q
    have h2 := (ind_target_charge (cutTargets P d₁ ζ) c q hq).trans
      (add_le_add le_rfl (cutTargets_charge d₁ ζ q))
    have h3 : ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ind (P.codec.IdxPost d' (c.cacheQuery q u) v) = ind (P.codec.IdxPost d' c v) := by
      have he : ∀ u, ind (P.codec.IdxPost d' (c.cacheQuery q u) v) = ind (P.codec.IdxPost d' c v) :=
        fun u => ind_congr (P.codec.idxPost_cacheQuery_of_ne_enc d' c hne u v)
      simp only [he]
      exact sum_inv_card_mul _
    have hs := sumW_mono (P := P) hT
    calc _ ≤ (hiddenHitPotential d₁ T c + rate * sumW P (publicFiber d₁ v₁) * queryCost (.inr q)) +
          sumW P T * ((ind (TargetHit (cutTargets P d₁ ζ) c) + rate * queryCost (.inr q)) +
            ind (P.codec.IdxPost d' c v)) :=
          add_le_add h1 (mul_le_mul' le_rfl (add_le_add h2 (le_of_eq h3)))
      _ = (hiddenHitPotential d₁ T c + sumW P T *
            (ind (TargetHit (cutTargets P d₁ ζ) c) + ind (P.codec.IdxPost d' c v))) +
          (rate * sumW P (publicFiber d₁ v₁) * queryCost (.inr q) +
            sumW P T * (rate * queryCost (.inr q))) := by ring
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          calc rate * sumW P (publicFiber d₁ v₁) * queryCost (.inr q) +
                sumW P T * (rate * queryCost (.inr q))
              ≤ rate * sumW P (publicFiber d₁ v₁) * queryCost (.inr q) +
                  sumW P (publicFiber d₁ v₁) * (rate * queryCost (.inr q)) :=
                add_le_add le_rfl (mul_le_mul' hs le_rfl)
            _ = 2 * rate * sumW P (publicFiber d₁ v₁) * queryCost (.inr q) := by ring
            _ ≤ ρ * sumW P (publicFiber d₁ v₁) * queryCost (.inr q) := by
                gcongr

/-- The index event of a fresh forgery after signing (E1): unless an entry of the first stage
other than the signed one held the signed class, or another trial of the signer did, it is a new
index entry of that class. -/
theorem idxPost_of_event (pk : PublicKey) (m₁ : Message) (d d' c : Cache) (η₁ : Nonce)
    (I₁ : Index) (hext : P.codec.TierExt (emsg m₁ pk) d (some (η₁, I₁)) d')
    (hpre : ¬ P.codec.IdxPreC d (emsg m₁ pk ++ η₁) (P.codec.digit I₁))
    (hsc : ¬ P.codec.SelfCol d (emsg m₁ pk) d' (η₁, I₁)) (hsub : Cache.Sub d' c)
    (m₂ : Message) (η₂ : Nonce) (hne : (m₂, η₂) ≠ (m₁, η₁)) (w : BitVec hashBits)
    (hw : c ⟨896, P.codec.idxInput m₂ η₂ pk⟩ = some w)
    (hacc : P.codec.Accepted (indexSlice w)) (hdig : P.codec.digit (indexSlice w) = P.codec.digit I₁) :
    P.codec.IdxPost d' c (P.codec.digit I₁) := by
  have hcls : P.codec.cls w = some (P.codec.digit I₁) := P.codec.cls_eq_some.2 ⟨hacc, hdig⟩
  have hwq : c (P.codec.encQuery (emsg m₂ pk ++ η₂)) = some w := by rw [P.codec.encQuery_emsg]; exact hw
  have hne' : emsg m₂ pk ++ η₂ ≠ emsg m₁ pk ++ η₁ := by
    intro h
    obtain ⟨hM, hη⟩ := append_pair_inj h
    obtain ⟨hm, -⟩ := emsg_inj hM
    exact hne (by rw [hm, hη])
  rcases hd' : d' (P.codec.encQuery (emsg m₂ pk ++ η₂)) with _ | w'
  · exact ⟨_, hd', w, hwq, hcls⟩
  · have hww : w' = w := Option.some.inj ((hsub _ _ hd').symm.trans hwq)
    subst hww
    rcases hd : d (P.codec.encQuery (emsg m₂ pk ++ η₂)) with _ | w''
    · obtain ⟨η, hq⟩ := hext.2.1 _ _ hd hd'
      obtain ⟨hM, hη⟩ := append_pair_inj (P.codec.encQuery_inj hq)
      obtain ⟨hm, -⟩ := emsg_inj hM
      subst hm
      subst hη
      refine absurd ⟨η₂, fun h => hne (by rw [h]), hd, w', hd', hcls⟩ hsc
    · have hww : w'' = w' := Option.some.inj ((hext.1 _ _ hd).symm.trans hd')
      subst hww
      exact absurd ⟨_, hne', w'', hd, hcls⟩ hpre

/-- **The second stage** on the records `T` of one public fiber after signing index `I₁`, at
any rate `ρ ≥ max(2 ^ -128, p(I₁) / 2)`. -/
theorem stageB_fiber (hP : P.SecurityHyp) (pk : PublicKey) (m₁ : Message) (st : A.State)
    (d d' : Cache) (η₁ : Nonce) (I₁ : Index)
    (hext : P.codec.TierExt (emsg m₁ pk) d (some (η₁, I₁)) d')
    (hpre : ¬ P.codec.IdxPreC d (emsg m₁ pk ++ η₁) (P.codec.digit I₁))
    (hsc : ¬ P.codec.SelfCol d (emsg m₁ pk) d' (η₁, I₁))
    {ρ : ℝ≥0∞} (hρ₁ : 2 * rate ≤ ρ) (hρ₂ : (P.codec.cweight (P.codec.digit I₁) : ℝ≥0∞) / 2 ^ 127 ≤ ρ * 2)
    (v₁ : PublicData P) (ζ₁ : Record P)
    (hζ₁ : ζ₁ ∈ publicFiber (afterSigning P I₁) v₁)
    (T : Finset (Record P)) (hT : T ⊆ publicFiber (afterSigning P I₁) v₁)
    (hpk : ∀ ξ ∈ T, ξ.pk = pk)
    (hd : ∀ ξ ∈ T, Cache.Sub (exposedCache (beforeSigning P) ξ) d ∧
      ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ) ∧
      ¬ TargetHit (secondPreimageTargets P ξ) d)
    (b' : ℕ) (hb : CostAtMost (P.stB A pk m₁ st
      (some (encode (fun k => ζ₁.word k (afterSigning P I₁ k)) η₁))) b') :
    ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st
        (some (encode (fun k => ξ.word k (afterSigning P I₁ k)) η₁)))
        (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g ≤
      ρ * sumW P (publicFiber (afterSigning P I₁) v₁) * b' := by
  set d₁ := afterSigning P I₁ with hd₁
  have hv₁ : ValidCut P d₁ := afterSigning_valid I₁
  have hI₁ : P.codec.Accepted I₁ := (hext.2.2 _ rfl).1
  have henc := P.encExt_of_tierExt hext
  rcases T.eq_empty_or_nonempty with hTe | ⟨ξ₀, hξ₀⟩
  · rw [hTe, Finset.sum_empty]
    exact bot_le
  have hdata : ∀ ξ ∈ T, publicData d₁ ξ = publicData d₁ ζ₁ :=
    fun ξ hξ => ((mem_publicFiber _ _ _).mp (hT hξ)).trans ((mem_publicFiber _ _ _).mp hζ₁).symm
  have hsig : ∀ ξ ∈ T, (fun k => ξ.word k (d₁ k)) = fun k => ζ₁.word k (d₁ k) :=
    fun ξ hξ => funext fun k => data_word_eq d₁ ξ ζ₁ (hdata ξ hξ) k (d₁ k) le_rfl
  have hexp : ∀ ξ ∈ T, exposedCache d₁ ξ = exposedCache d₁ ζ₁ :=
    fun ξ hξ => exposedCache_data_eq hP hv₁ ξ ζ₁ (hdata ξ hξ)
  set c' := Cache.extend d' (exposedCache d₁ ζ₁) with hc'
  set oa := P.stB A pk m₁ st (some (encode (fun k => ζ₁.word k (d₁ k)) η₁)) with hoa
  have hsubexp : ∀ ξ ∈ T, Cache.Sub (exposedCache d₁ ξ) c' := by
    intro ξ hξ
    rw [hc', ← hexp ξ hξ]
    exact P.sub_exposed_after hP d d' ξ d₁ henc (hd ξ hξ).1 (hd ξ hξ).2.1
  have hdisj : ∀ ξ ∈ T, Cache.Disjoint c' (hiddenCache d₁ ξ) := by
    intro ξ hξ
    rw [hc', ← hexp ξ hξ]
    exact P.disjoint_after hP d d' ξ d₁ henc (hd ξ hξ).2.1
  have hshift : ∀ ξ ∈ T, Cache.extend d' (hiddenCache (beforeSigning P) ξ) =
      Cache.extend c' (hiddenCache d₁ ξ) := by
    intro ξ hξ
    rw [P.extend_hidden_shift hP d' ξ d₁ ((hd ξ hξ).1.trans henc.1), hexp ξ hξ]
  have hcut : ∀ ξ ∈ T, cutTargets P d₁ ξ = cutTargets P d₁ ζ₁ :=
    fun ξ hξ => cutTargets_public hv₁ ξ ζ₁ (hdata ξ hξ)
  have hsd' : Cache.Sub d' c' := fun q u h => Cache.extend_apply_of_some h
  -- the step for one record
  have hstep : ∀ ξ ∈ T,
      E (run (P.stB A pk m₁ st (some (encode (fun k => ξ.word k (d₁ k)) η₁)))
          (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g ≤
        E (run oa c') (fun p => ind (Cache.Hits p.2 (hiddenCache d₁ ξ)) +
          (ind (TargetHit (cutTargets P d₁ ζ₁) p.2) + ind (P.codec.IdxPost d' p.2 (P.codec.digit I₁)))) := by
    intro ξ hξ
    rw [hshift ξ hξ, hsig ξ hξ, ← hoa]
    refine (iub oa (hiddenCache d₁ ξ) g g_le_one c' (hdisj ξ hξ)).trans ?_
    refine expectedValue_mono_of_support fun p hp => ?_
    by_cases hh : Cache.Hits p.2 (hiddenCache d₁ ξ)
    · rw [if_pos hh, ind_of hh]
      exact le_self_add
    · rw [if_neg hh, ind_not hh, zero_add]
      by_cases hok : p.1 = true
      · have hg : g (p.1, Cache.extend p.2 (hiddenCache d₁ ξ)) = 1 := by
          show (if p.1 = true then (1 : ℝ≥0∞) else 0) = 1
          rw [if_pos hok]
        rw [hg]
        have hp' : p ∈ support (run (P.stB A pk m₁ st
            (some (encode (fun k => ξ.word k (afterSigning P I₁ k)) η₁))) c') := by
          rw [hsig ξ hξ]
          exact hp
        rcases events_some A hP pk m₁ st ξ c' I₁ hI₁ η₁ (hsubexp ξ hξ) (hpk ξ hξ) p hp' hok with
          h | h | ⟨m₂, η₂, hne, w, hw, hacc, hdig⟩
        · exact absurd h hh
        · rw [hcut ξ hξ] at h
          exact le_trans (le_of_eq (ind_of h).symm) le_self_add
        · have hcp := (P.stB_support A pk m₁ st _ c' p hp).1
          have hpost := P.idxPost_of_event pk m₁ d d' p.2 η₁ I₁ hext hpre hsc (hsd'.trans hcp)
            m₂ η₂ hne w hw hacc hdig
          exact le_trans (le_of_eq (ind_of hpost).symm) le_add_self
      · have hg : g (p.1, Cache.extend p.2 (hiddenCache d₁ ξ)) = 0 := by
          show (if p.1 = true then (1 : ℝ≥0∞) else 0) = 0
          rw [if_neg hok]
        rw [hg]
        exact bot_le
  -- the potential vanishes at the start of the stage
  have hct : ¬ TargetHit (cutTargets P d₁ ζ₁) c' := by
    intro h
    have hc0 : Cache.extend d' (exposedCache d₁ ξ₀) = c' := by rw [hc', hexp ξ₀ hξ₀]
    rw [← hcut ξ₀ hξ₀, ← hc0] at h
    have h' : TargetHit (cutTargets P d₁ ξ₀) (Cache.extend d (exposedCache d₁ ξ₀)) := by
      obtain ⟨q, u, hq, hu⟩ := h
      obtain ⟨a, hl, -, -⟩ := mem_cutTargets hu
      obtain ⟨ζ, hloc, hζ⟩ := queryLocation_some hl
      have hne : ∀ e, q ≠ P.codec.encQuery e := fun e he => P.raw_query_ne_encQuery hP ζ e (hζ.trans he)
      refine ⟨q, u, ?_, hu⟩
      rw [Cache.extend_apply] at hq ⊢
      rcases hdq : d q with _ | v
      · rw [EncExt.none_of P henc hne hdq] at hq
        exact hq
      · rw [henc.1 q v hdq] at hq
        exact hq
    exact no_cutTargets_initial hP d₁ ξ₀ d (hd ξ₀ hξ₀).2.1 (hd ξ₀ hξ₀).2.2 h'
  have hpost0 : ¬ P.codec.IdxPost d' c' (P.codec.digit I₁) :=
    P.codec.not_idxPost_extend_of_enc_none d' _ (fun u => P.exposedCache_enc hP d₁ ζ₁ u) _
  have hΦ0 : P.ΦB d₁ T ζ₁ d' (P.codec.digit I₁) c' = 0 := by
    unfold ΦB
    rw [hiddenHitPotential_zero d₁ T c' hdisj, ind_not hct, ind_not hpost0]
    simp
  have hbound := potential_bound (P.ΦB d₁ T ζ₁ d' (P.codec.digit I₁)) (ρ * sumW P (publicFiber d₁ v₁))
    (fun c q hq => by
      simpa only [mul_assoc] using
        P.ΦB_charge hP hv₁ v₁ T hT ζ₁ d' (P.codec.digit I₁) hρ₁ hρ₂ c q hq) oa c' b' hb
  rw [hΦ0, zero_add] at hbound
  calc ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st
          (some (encode (fun k => ξ.word k (afterSigning P I₁ k)) η₁)))
          (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g
      ≤ ∑ ξ ∈ T, recW P * E (run oa c') (fun p => ind (Cache.Hits p.2 (hiddenCache d₁ ξ)) +
          (ind (TargetHit (cutTargets P d₁ ζ₁) p.2) + ind (P.codec.IdxPost d' p.2 (P.codec.digit I₁)))) :=
        Finset.sum_le_sum fun ξ hξ => mul_le_mul' le_rfl (hstep ξ hξ)
    _ = E (run oa c') (fun p => P.ΦB d₁ T ζ₁ d' (P.codec.digit I₁) p.2) := by
        unfold ΦB hiddenHitPotential
        rw [E_add', E_weighted_sum, E_const_mul, sumW, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [← mul_add, E_add']
    _ ≤ ρ * sumW P (publicFiber d₁ v₁) * b' := hbound

end Params

end OptimalOTS.LeanIsaBaseline.Layer.Fusion
