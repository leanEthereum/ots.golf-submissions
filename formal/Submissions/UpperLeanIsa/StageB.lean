import Submissions.UpperLeanIsa.Events
import Submissions.UpperLeanIsa.CutTargets

/-!
# The second stage

After the first stage ended with cache `d` and signing replayed the honest cache, the second
attacker stage and the verifier run from `extend d (hiddenCache beforeSigning ξ)`. For the records
`T` of one public-data fiber after signing, this is the run from the common cache
`c' = extend d (exposedCache (afterSigning m₁) ζ₁)` with the hidden points of `ξ` added
(`extend_hidden_shift`). Identical-until-bad (`iub`) removes the hidden points; on the remaining
run an accepted forgery is a hidden hit or a cut-target hit (`events_stB`). The first is bounded
by `hidden_hit_bound_subset`, the second by `cutTargets_hit_bound`, each at `2⁻¹²⁹` per
compression:

```
∑ ξ ∈ T, w · E[g | stB from extend d (hidden ξ)] ≤ κ · sumW (fiber after signing) · b'.
```
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

attribute [local irreducible] hashBits publicFiber finiteFiber hiddenCache
attribute [local irreducible] queryLocation Record.query

local instance instDecEqRecordStageB : DecidableEq Record := Classical.decEq Record

variable (A : OracleAlgorithm.Adversary)

/-! ## Cache algebra -/

/-- Before signing all chain points of `ξ` are hidden; after signing only those below the cut.
If `d` holds the points exposed before signing, the difference may be moved into the exposed
cache after signing. -/
theorem extend_hidden_shift (d : Cache) (ξ : Record) (m : Message)
    (hd : Cache.Sub (exposedCache beforeSigning ξ) d) :
    Cache.extend d (hiddenCache beforeSigning ξ) =
      Cache.extend (Cache.extend d (exposedCache (afterSigning m) ξ))
        (hiddenCache (afterSigning m) ξ) := by
  rw [Cache.extend_assoc, exposure_partition]
  funext q
  rw [Cache.extend_apply, Cache.extend_apply]
  rcases hq : ξ.cache q with _ | u
  · have hh : hiddenCache beforeSigning ξ q = none := by
      rcases hh' : hiddenCache beforeSigning ξ q with _ | u
      · rfl
      · obtain ⟨a, -, haq, -⟩ := (hiddenCache_some_iff beforeSigning ξ q u).mp hh'
        rw [← haq, Record.cache_query] at hq
        exact absurd hq (Option.some_ne_none _)
    rw [hh]
  · obtain ⟨a, haq, hau⟩ := (ξ.cache_some_iff q u).mp hq
    cases a with
    | inl x =>
      rw [(hiddenCache_some_iff beforeSigning ξ q u).mpr
        ⟨.inl x, hiddenBefore_inl x, haq, hau⟩]
    | inr i =>
      have hdq : d q = some u :=
        hd q u ((exposedCache_some_iff beforeSigning ξ q u).mpr
          ⟨.inr i, fun h => h, haq, hau⟩)
      simp only [hdq, Option.some_or]

/-- If the first stage did not hit a hidden point of `ξ`, its cache agrees with the points of
`ξ` exposed after signing. -/
theorem sub_exposed_after (d : Cache) (ξ : Record) (m : Message)
    (hd : Cache.Sub (exposedCache beforeSigning ξ) d)
    (hh : ¬ Cache.Hits d (hiddenCache beforeSigning ξ)) :
    Cache.Sub (exposedCache (afterSigning m) ξ)
      (Cache.extend d (exposedCache (afterSigning m) ξ)) := by
  intro q u hq
  obtain ⟨a, -, haq, hau⟩ := (exposedCache_some_iff _ ξ q u).mp hq
  cases a with
  | inl x =>
    rw [Cache.extend_apply_of_none
      (none_of_not_hits_hidden d ξ hh (.inl x) (hiddenBefore_inl x) haq)]
    exact hq
  | inr i =>
    exact Cache.extend_apply_of_some
      (hd q u ((exposedCache_some_iff beforeSigning ξ q u).mpr
        ⟨.inr i, fun h => h, haq, hau⟩))

/-! ## Stage B -/

/-- The second stage for the records `T` of one public-data fiber after signing `m₁`, none of
which was hit (hidden point or second-preimage target) in the first stage. -/
theorem stageB (pk : PublicKey) (m₁ : Message) (st : A.State) (d : Cache) (v₁ : PublicData)
    (ζ₁ : Record) (hζ₁ : ζ₁ ∈ publicFiber (afterSigning m₁) v₁) (T : Finset Record)
    (hT : T ⊆ publicFiber (afterSigning m₁) v₁) (hpk : ∀ ξ ∈ T, ξ.publicKey = pk)
    (hd : ∀ ξ ∈ T, Cache.Sub (exposedCache beforeSigning ξ) d ∧
      ¬ Cache.Hits d (hiddenCache beforeSigning ξ) ∧ ¬ TargetHit (secondPreimageTargets ξ) d)
    (b' : ℕ) (hb : ∀ ξ ∈ T, CostAtMost (stB A pk m₁ st (some (ξ.signature m₁))) b') :
    ∑ ξ ∈ T, w * E (run (stB A pk m₁ st (some (ξ.signature m₁)))
        (Cache.extend d (hiddenCache beforeSigning ξ))) g ≤
      κ * sumW (publicFiber (afterSigning m₁) v₁) * b' := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨ξ₀, hξ₀⟩
  · rw [hTe, Finset.sum_empty]
    exact bot_le
  obtain ⟨oa, hoa⟩ : ∃ oa : OracleComp Spec Bool,
      oa = stB A pk m₁ st (some (ζ₁.signature m₁)) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : Cache,
      c' = Cache.extend d (exposedCache (afterSigning m₁) ζ₁) := ⟨_, rfl⟩
  -- every record of `T` has the public data of `ζ₁` after signing
  have hdata : ∀ ξ ∈ T, publicData (afterSigning m₁) ξ = publicData (afterSigning m₁) ζ₁ :=
    fun ξ hξ => ((mem_publicFiber _ _ _).mp (hT hξ)).trans ((mem_publicFiber _ _ _).mp hζ₁).symm
  have hsig : ∀ ξ ∈ T, ξ.signature m₁ = ζ₁.signature m₁ :=
    fun ξ hξ => signature_data_eq m₁ ξ ζ₁ (hdata ξ hξ)
  have hexp : ∀ ξ ∈ T, exposedCache (afterSigning m₁) ξ = exposedCache (afterSigning m₁) ζ₁ :=
    fun ξ hξ => exposedCache_data_eq (afterSigning m₁) ξ ζ₁ (hdata ξ hξ)
  -- the common starting cache
  have hsub : ∀ ξ ∈ T, Cache.Sub (exposedCache (afterSigning m₁) ξ) c' := by
    intro ξ hξ
    rw [hc', ← hexp ξ hξ]
    exact sub_exposed_after d ξ m₁ (hd ξ hξ).1 (hd ξ hξ).2.1
  have hdisj : ∀ ξ ∈ T, Cache.Disjoint c' (hiddenCache (afterSigning m₁) ξ) := by
    intro ξ hξ q hq
    obtain ⟨a, ha, haq⟩ := (hiddenCache_isSome_iff (afterSigning m₁) ξ q).mp hq
    rw [hc', Cache.extend_apply, ← hexp ξ hξ, exposure_disjoint (afterSigning m₁) ξ q hq,
      none_of_not_hits_hidden d ξ (hd ξ hξ).2.1 a (hiddenBefore_of_hidden ha) haq,
      Option.none_or]
  have hct : ¬ TargetHit (cutTargets (afterSigning m₁) ζ₁) c' := by
    have h := no_cutTargets_initial m₁ ξ₀ d (hd ξ₀ hξ₀).2.1 (hd ξ₀ hξ₀).2.2
    rw [cutTargets_public (afterSigning m₁) ξ₀ ζ₁ (hdata ξ₀ hξ₀), hexp ξ₀ hξ₀, ← hc'] at h
    exact h
  have hboa : CostAtMost oa b' := by
    rw [hoa, ← hsig ξ₀ hξ₀]
    exact hb ξ₀ hξ₀
  -- identical until a hidden point is queried, then the events lemma
  have hstep : ∀ ξ ∈ T,
      E (run (stB A pk m₁ st (some (ξ.signature m₁)))
          (Cache.extend d (hiddenCache beforeSigning ξ))) g ≤
        E (run oa c') (fun p => ind (Cache.Hits p.2 (hiddenCache (afterSigning m₁) ξ)) +
          ind (TargetHit (cutTargets (afterSigning m₁) ζ₁) p.2)) := by
    intro ξ hξ
    rw [extend_hidden_shift d ξ m₁ (hd ξ hξ).1, hexp ξ hξ, ← hc', hsig ξ hξ, ← hoa]
    refine (iub oa (hiddenCache (afterSigning m₁) ξ) g g_le_one c' (hdisj ξ hξ)).trans ?_
    refine expectedValue_mono_of_support fun p hp => ?_
    by_cases hh : Cache.Hits p.2 (hiddenCache (afterSigning m₁) ξ)
    · rw [if_pos hh, ind_of hh]
      exact le_self_add
    · rw [if_neg hh, ind_not hh, zero_add]
      by_cases hok : p.1 = true
      · have hg : g (p.1, Cache.extend p.2 (hiddenCache (afterSigning m₁) ξ)) = 1 := by
          show (if p.1 = true then (1 : ℝ≥0∞) else 0) = 1
          rw [if_pos hok]
        rw [hg]
        have hp' : p ∈ support (run (stB A pk m₁ st (some (ξ.signature m₁))) c') := by
          rw [hsig ξ hξ, ← hoa]
          exact hp
        rcases events_stB A pk m₁ st ξ c' (hsub ξ hξ) (hpk ξ hξ) p hp' hok with h | h
        · exact absurd h hh
        · rw [cutTargets_public (afterSigning m₁) ξ ζ₁ (hdata ξ hξ)] at h
          exact (ind_of h).ge
      · have hg : g (p.1, Cache.extend p.2 (hiddenCache (afterSigning m₁) ξ)) = 0 := by
          show (if p.1 = true then (1 : ℝ≥0∞) else 0) = 0
          rw [if_neg hok]
        rw [hg]
        exact bot_le
  -- sum over `T`, then the two adaptive bounds
  calc ∑ ξ ∈ T, w * E (run (stB A pk m₁ st (some (ξ.signature m₁)))
          (Cache.extend d (hiddenCache beforeSigning ξ))) g
      ≤ ∑ ξ ∈ T, w * E (run oa c') (fun p =>
          ind (Cache.Hits p.2 (hiddenCache (afterSigning m₁) ξ)) +
            ind (TargetHit (cutTargets (afterSigning m₁) ζ₁) p.2)) :=
        Finset.sum_le_sum fun ξ hξ => mul_le_mul' le_rfl (hstep ξ hξ)
    _ = ∑ ξ ∈ T, (w * E (run oa c') (fun p =>
            ind (Cache.Hits p.2 (hiddenCache (afterSigning m₁) ξ))) +
          w * E (run oa c') (fun p =>
            ind (TargetHit (cutTargets (afterSigning m₁) ζ₁) p.2))) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [← mul_add]
        congr 1
        exact expectedValue_add _ _ _
    _ = E (run oa c') (fun p => ∑ ξ ∈ T,
            w * ind (Cache.Hits p.2 (hiddenCache (afterSigning m₁) ξ))) +
          sumW T * E (run oa c') (fun p =>
            ind (TargetHit (cutTargets (afterSigning m₁) ζ₁) p.2)) := by
        rw [Finset.sum_add_distrib, E_weighted_sum, sumW, Finset.sum_mul]
    _ ≤ secondPreimageRate * sumW (publicFiber (afterSigning m₁) v₁) * b' +
          sumW T * (secondPreimageRate * b') :=
        add_le_add (hidden_hit_bound_subset (afterSigning m₁) v₁ T hT oa c' b' hboa hdisj)
          (mul_le_mul' le_rfl (cutTargets_hit_bound (afterSigning m₁) ζ₁ oa c' b' hboa hct))
    _ ≤ secondPreimageRate * sumW (publicFiber (afterSigning m₁) v₁) * b' +
          sumW (publicFiber (afterSigning m₁) v₁) * (secondPreimageRate * b') :=
        add_le_add le_rfl (mul_le_mul' (Finset.sum_le_sum_of_subset hT) le_rfl)
    _ = κ * sumW (publicFiber (afterSigning m₁) v₁) * b' := by
        simp only [κ]
        ring

end OptimalOTS.LeanIsaBaseline
