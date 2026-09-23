import Submissions.UpperLeanIsa.Budget
import Submissions.UpperLeanIsa.StageB

/-!
# The first stage

The records with public data `v` before signing form the fiber `fiber₀ v`. After the first
attacker stage has ended with `(x, d)`, the quantity to bound is `FA A v x d`: for every record of
the fiber, `1` if `d` hit a hidden keygen point of the record, else the success probability of the
rest of the experiment. The potential

```
ΦA v c = ∑ ξ ∈ fiber₀ v, w · (ind (hidden hit of ξ) + ind (second-preimage hit of ξ))
```

grows by at most `κ · sumW (fiber₀ v)` per compression (`ΦA_charge`), is zero on the exposed
cache before signing (`ΦA_initial`), and bounds the continuation up to the path budget
(`stageA_cont`: signing is a replay, then `stageB` on each public-data fiber after signing). The
master lemma for a family of continuations gives

```
E[FA | first stage from the exposed cache] ≤ κ · sumW (fiber₀ v) · b      (stageA_master).
```
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

attribute [local irreducible] hashBits publicFiber finiteFiber hiddenCache
attribute [local irreducible] queryLocation Record.query

local instance instDecEqRecordStageA : DecidableEq Record := Classical.decEq Record

variable (A : OracleAlgorithm.Adversary)

/-! ## Signing is a replay -/

/-- On a cache extending the honest cache, signing and then the second stage is the second
stage with the recorded signature. -/
theorem run_rest₂_record (ξ : Record) (x : Message × A.State) (c : Cache)
    (hc : Cache.Sub ξ.cache c) :
    run (rest₂ A ξ.publicKey ξ.1 x) c =
      run (stB A ξ.publicKey x.1 x.2 (some (ξ.signature x.1))) c := by
  unfold rest₂
  rw [run_bind, run_sign_record ξ c hc x.1, pure_bind]
  try rfl

/-- A budget of signing followed by the second stage is a budget of the second stage with the
recorded signature. -/
theorem costAtMost_stB_of_rest₂ (ξ : Record) (x : Message × A.State) (b : ℕ)
    (h : CostAtMost (rest₂ A ξ.publicKey ξ.1 x) b) :
    CostAtMost (stB A ξ.publicKey x.1 x.2 (some (ξ.signature x.1))) b := by
  have hp : ((some (ξ.signature x.1), ξ.cache) : Option (List Bool) × Cache) ∈
      support (run (sign ξ.1 x.1) ξ.cache) := by
    rw [run_sign_record ξ ξ.cache (Cache.Sub.refl _) x.1, support_pure]
    exact Set.mem_singleton _
  exact costAtMost_bind_run_support (sign ξ.1 x.1) (stB A ξ.publicKey x.1 x.2) h ξ.cache _ hp

attribute [local irreducible] CostAtMost rest₂ stB

/-! ## The first-stage fiber, payoff, potential and invariant -/

/-- The records with public data `v` before signing. -/
def fiber₀ (v : PublicData) : Finset Record := publicFiber beforeSigning v

theorem fiber₀_eq (v : PublicData) : fiber₀ v = publicFiber beforeSigning v := rfl

theorem mem_fiber₀ (v : PublicData) (ξ : Record) : ξ ∈ fiber₀ v ↔ publicData beforeSigning ξ = v :=
  mem_publicFiber beforeSigning v ξ

theorem fiber₀_subset (v : PublicData) : fiber₀ v ⊆ publicFiber beforeSigning v := by
  intro ξ h
  exact h

/-- The quantity bounded after the first stage. -/
def FA (v : PublicData) (x : Message × A.State) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiber₀ v, w * (if Cache.Hits d (hiddenCache beforeSigning ξ) then 1 else
    E (run (rest₂ A ξ.publicKey ξ.1 x) (Cache.extend d (hiddenCache beforeSigning ξ))) g)

/-- The first-stage potential: hidden hits and second-preimage hits, weighted over the fiber. -/
def ΦA (v : PublicData) (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiber₀ v, w * (ind (Cache.Hits c (hiddenCache beforeSigning ξ)) +
    ind (TargetHit (secondPreimageTargets ξ) c))

/-- The first-stage invariant: the exposed keygen points of every record of the fiber are
cached. -/
def InvA (v : PublicData) (c : Cache) (_b : ℕ) : Prop :=
  ∀ ξ ∈ fiber₀ v, Cache.Sub (exposedCache beforeSigning ξ) c

theorem InvA_fresh (v : PublicData) : ∀ c b q, InvA v c b → c q = none →
    queryCost (.inr q) ≤ b → ∀ u, InvA v (c.cacheQuery q u) (b - queryCost (.inr q)) := by
  intro c b q hI hq _ u ξ hξ
  exact (hI ξ hξ).trans (Cache.sub_cacheQuery_of_none hq u)

theorem InvA_cached (v : PublicData) : ∀ c b q, InvA v c b → (c q).isSome →
    queryCost (.inr q) ≤ b → InvA v c (b - queryCost (.inr q)) := by
  intro c b q hI _ _ ξ hξ
  exact hI ξ hξ

theorem ΦA_eq (v : PublicData) (c : Cache) :
    ΦA v c = hiddenHitPotential beforeSigning (fiber₀ v) c +
      ∑ ξ ∈ fiber₀ v, w * ind (TargetHit (secondPreimageTargets ξ) c) := by
  unfold ΦA hiddenHitPotential
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [mul_add]

/-- The second-preimage part of the potential grows by `2⁻¹²⁹` per compression. -/
theorem targetPart_charge (v : PublicData) (c : Cache) (q : Query) (hq : c q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ fiber₀ v, w * ind (TargetHit (secondPreimageTargets ξ) (c.cacheQuery q u)) ≤
      ∑ ξ ∈ fiber₀ v, w * ind (TargetHit (secondPreimageTargets ξ) c) +
        sumW (fiber₀ v) * (secondPreimageRate * queryCost (.inr q)) := by
  calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          ∑ ξ ∈ fiber₀ v, w * ind (TargetHit (secondPreimageTargets ξ) (c.cacheQuery q u))
      = ∑ u, ∑ ξ ∈ fiber₀ v, w * ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          ind (TargetHit (secondPreimageTargets ξ) (c.cacheQuery q u))) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ξ _ => mul_left_comm _ _ _
    _ = ∑ ξ ∈ fiber₀ v, ∑ u, w * ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          ind (TargetHit (secondPreimageTargets ξ) (c.cacheQuery q u))) := Finset.sum_comm
    _ = ∑ ξ ∈ fiber₀ v, w * ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          targetPotential (secondPreimageTargets ξ) (c.cacheQuery q u) := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [Finset.mul_sum]
        simp only [ind_targetHit_eq]
    _ ≤ ∑ ξ ∈ fiber₀ v, w * (targetPotential (secondPreimageTargets ξ) c +
          secondPreimageRate * queryCost (.inr q)) :=
        Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl
          (target_charge (secondPreimageTargets ξ) secondPreimageRate
            (secondPreimage_charge ξ) c q hq)
    _ = ∑ ξ ∈ fiber₀ v, w * ind (TargetHit (secondPreimageTargets ξ) c) +
          sumW (fiber₀ v) * (secondPreimageRate * queryCost (.inr q)) := by
        rw [sumW, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [ind_targetHit_eq, mul_add]

/-- The potential grows by at most `κ · sumW (fiber₀ v)` per compression. -/
theorem ΦA_charge (v : PublicData) : ∀ c b q, InvA v c b → c q = none →
    queryCost (.inr q) ≤ b →
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ΦA v (c.cacheQuery q u) ≤
      ΦA v c + κ * sumW (fiber₀ v) * queryCost (.inr q) := by
  intro c _ q _ hq _
  have h1 := hiddenHitPotential_charge beforeSigning v (fiber₀ v) (fiber₀_subset v) c q
  rw [← fiber₀_eq v] at h1
  have h2 := targetPart_charge v c q hq
  calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ΦA v (c.cacheQuery q u)
      = ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
            hiddenHitPotential beforeSigning (fiber₀ v) (c.cacheQuery q u) +
          ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
            ∑ ξ ∈ fiber₀ v, w * ind (TargetHit (secondPreimageTargets ξ) (c.cacheQuery q u)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [ΦA_eq, mul_add]
    _ ≤ (hiddenHitPotential beforeSigning (fiber₀ v) c +
            secondPreimageRate * sumW (fiber₀ v) * queryCost (.inr q)) +
          (∑ ξ ∈ fiber₀ v, w * ind (TargetHit (secondPreimageTargets ξ) c) +
            sumW (fiber₀ v) * (secondPreimageRate * queryCost (.inr q))) :=
        add_le_add h1 h2
    _ = ΦA v c + κ * sumW (fiber₀ v) * queryCost (.inr q) := by
        rw [ΦA_eq]
        simp only [κ]
        ring

theorem no_secondPreimage_exposed (d : Cut) (ξ : Record) :
    ¬ TargetHit (secondPreimageTargets ξ) (exposedCache d ξ) := by
  rintro ⟨q, u, hq, hu⟩
  obtain ⟨a, -, rfl, -⟩ := (exposedCache_some_iff d ξ q u).mp hq
  rw [secondPreimageTargets_query] at hu
  exact Finset.notMem_empty _ hu

/-- The potential vanishes on the exposed cache before signing of any record of the fiber. -/
theorem ΦA_initial (v : PublicData) (ζ₀ : Record) (hζ₀ : ζ₀ ∈ fiber₀ v) :
    ΦA v (exposedCache beforeSigning ζ₀) = 0 := by
  unfold ΦA
  refine Finset.sum_eq_zero fun ξ hξ => ?_
  have hdata : publicData beforeSigning ξ = publicData beforeSigning ζ₀ :=
    ((mem_fiber₀ v ξ).mp hξ).trans ((mem_fiber₀ v ζ₀).mp hζ₀).symm
  rw [← exposedCache_data_eq beforeSigning ξ ζ₀ hdata,
    ind_not (exposure_disjoint beforeSigning ξ).not_hits,
    ind_not (no_secondPreimage_exposed beforeSigning ξ), add_zero, mul_zero]

/-! ## The continuation after the first stage -/

/-- The continuation bound: the rest of the experiment after the first stage ended with
`(x, d)`, within the path budget `b'`. -/
theorem stageA_cont (v : PublicData) (x : Message × A.State) (d : Cache) (b' : ℕ)
    (hI : InvA v d b') (hB : ∀ ξ ∈ fiber₀ v, CostAtMost (rest₂ A ξ.publicKey ξ.1 x) b') :
    FA A v x d ≤ ΦA v d + κ * sumW (fiber₀ v) * b' := by
  obtain ⟨T, hTdef⟩ : ∃ T : Finset Record, T = (fiber₀ v).filter
      (fun ξ => ¬ Cache.Hits d (hiddenCache beforeSigning ξ) ∧
        ¬ TargetHit (secondPreimageTargets ξ) d) := ⟨_, rfl⟩
  have hT : T ⊆ fiber₀ v := by
    rw [hTdef]
    exact Finset.filter_subset _ _
  have hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (hiddenCache beforeSigning ξ) ∧
      ¬ TargetHit (secondPreimageTargets ξ) d := by
    intro ξ hξ
    rw [hTdef, Finset.mem_filter] at hξ
    exact hξ.2
  -- Step 1: records hit in the first stage pay `1`; the others replay signing.
  have hsplit : FA A v x d ≤ ΦA v d + ∑ ξ ∈ T, w * E (run (stB A ξ.publicKey x.1 x.2
      (some (ξ.signature x.1))) (Cache.extend d (hiddenCache beforeSigning ξ))) g := by
    unfold FA ΦA
    rw [hTdef, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ξ hξ => ?_
    by_cases hh : Cache.Hits d (hiddenCache beforeSigning ξ)
    · refine le_trans ?_ le_self_add
      rw [if_pos hh, ind_of hh]
      exact mul_le_mul' le_rfl le_self_add
    · by_cases ht : TargetHit (secondPreimageTargets ξ) d
      · refine le_trans ?_ le_self_add
        rw [if_neg hh, ind_not hh, ind_of ht, zero_add]
        exact mul_le_mul' le_rfl (E_le_one _ g_le_one)
      · rw [if_neg hh, ind_not hh, ind_not ht, add_zero, mul_zero, zero_add,
          if_pos (And.intro hh ht)]
        exact le_of_eq (by
          rw [run_rest₂_record A ξ x _
            (record_cache_sub_extend_hidden beforeSigning ξ d (hI ξ hξ) hh)])
  -- Step 2: regroup the records of `T` by their public data after signing.
  have hmaps : ∀ ξ ∈ T,
      publicData (afterSigning x.1) ξ ∈ T.image (publicData (afterSigning x.1)) :=
    fun ξ hξ => Finset.mem_image_of_mem _ hξ
  have hregroup : ∀ f : Record → ℝ≥0∞, ∑ ξ ∈ T, f ξ =
      ∑ v₁ ∈ T.image (publicData (afterSigning x.1)),
        ∑ ξ ∈ T with publicData (afterSigning x.1) ξ = v₁, f ξ :=
    fun f => (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  -- Step 3: `stageB` on every fiber after signing.
  have hfiber : ∀ v₁ ∈ T.image (publicData (afterSigning x.1)),
      ∑ ξ ∈ T with publicData (afterSigning x.1) ξ = v₁,
          w * E (run (stB A ξ.publicKey x.1 x.2 (some (ξ.signature x.1)))
            (Cache.extend d (hiddenCache beforeSigning ξ))) g ≤
        κ * sumW (publicFiber (afterSigning x.1) v₁) * b' := by
    intro v₁ hv₁
    obtain ⟨ζ₁, hζ₁T, hζ₁⟩ := Finset.mem_image.1 hv₁
    have hζ₁F : ζ₁ ∈ publicFiber (afterSigning x.1) v₁ := (mem_publicFiber _ _ _).mpr hζ₁
    have hpkζ : ∀ ξ ∈ fiber₀ v, ξ.publicKey = ζ₁.publicKey := fun ξ hξ =>
      publicKey_data_eq beforeSigning ξ ζ₁
        (((mem_fiber₀ v ξ).mp hξ).trans ((mem_fiber₀ v ζ₁).mp (hT hζ₁T)).symm)
    have hmemT : ∀ ξ ∈ T.filter (fun ξ => publicData (afterSigning x.1) ξ = v₁), ξ ∈ T :=
      fun ξ hξ => (Finset.mem_filter.1 hξ).1
    have hsubT : T.filter (fun ξ => publicData (afterSigning x.1) ξ = v₁) ⊆
        publicFiber (afterSigning x.1) v₁ := by
      intro ξ hξ
      exact (mem_publicFiber _ _ _).mpr (Finset.mem_filter.1 hξ).2
    calc ∑ ξ ∈ T with publicData (afterSigning x.1) ξ = v₁,
          w * E (run (stB A ξ.publicKey x.1 x.2 (some (ξ.signature x.1)))
            (Cache.extend d (hiddenCache beforeSigning ξ))) g
        = ∑ ξ ∈ T with publicData (afterSigning x.1) ξ = v₁,
          w * E (run (stB A ζ₁.publicKey x.1 x.2 (some (ξ.signature x.1)))
            (Cache.extend d (hiddenCache beforeSigning ξ))) g := by
          refine Finset.sum_congr rfl fun ξ hξ => ?_
          rw [hpkζ ξ (hT (hmemT ξ hξ))]
      _ ≤ κ * sumW (publicFiber (afterSigning x.1) v₁) * b' :=
          stageB A ζ₁.publicKey x.1 x.2 d v₁ ζ₁ hζ₁F _ hsubT
            (fun ξ hξ => hpkζ ξ (hT (hmemT ξ hξ)))
            (fun ξ hξ => ⟨hI ξ (hT (hmemT ξ hξ)), (hTd ξ (hmemT ξ hξ)).1,
              (hTd ξ (hmemT ξ hξ)).2⟩)
            b' (fun ξ hξ => by
              have h := costAtMost_stB_of_rest₂ A ξ x b' (hB ξ (hT (hmemT ξ hξ)))
              rw [hpkζ ξ (hT (hmemT ξ hξ))] at h
              exact h)
  -- Step 4: the fibers after signing partition part of `fiber₀ v`.
  have hsumW : ∑ v₁ ∈ T.image (publicData (afterSigning x.1)),
      sumW (publicFiber (afterSigning x.1) v₁) ≤ sumW (fiber₀ v) := by
    have hsub : ∀ v₁ ∈ T.image (publicData (afterSigning x.1)),
        publicFiber (afterSigning x.1) v₁ ⊆
          ((fiber₀ v).filter fun ξ =>
            publicData (afterSigning x.1) ξ ∈ T.image (publicData (afterSigning x.1))).filter
              fun ξ => publicData (afterSigning x.1) ξ = v₁ := by
      intro v₁ hv₁ ξ hξ
      obtain ⟨ζ₁, hζ₁T, hζ₁⟩ := Finset.mem_image.1 hv₁
      have hξd : publicData (afterSigning x.1) ξ = v₁ := (mem_publicFiber _ _ _).mp hξ
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨?_, by rw [hξd]; exact hv₁⟩, hξd⟩
      apply (mem_fiber₀ v ξ).mpr
      rw [publicData_before_of_after x.1 ξ ζ₁ (hξd.trans hζ₁.symm)]
      exact (mem_fiber₀ v ζ₁).mp (hT hζ₁T)
    calc ∑ v₁ ∈ T.image (publicData (afterSigning x.1)),
          sumW (publicFiber (afterSigning x.1) v₁)
        ≤ ∑ v₁ ∈ T.image (publicData (afterSigning x.1)),
            ∑ ξ ∈ ((fiber₀ v).filter fun ξ => publicData (afterSigning x.1) ξ ∈
              T.image (publicData (afterSigning x.1))) with
                publicData (afterSigning x.1) ξ = v₁, w :=
          Finset.sum_le_sum fun v₁ hv₁ => Finset.sum_le_sum_of_subset (hsub v₁ hv₁)
      _ = ∑ ξ ∈ ((fiber₀ v).filter fun ξ => publicData (afterSigning x.1) ξ ∈
              T.image (publicData (afterSigning x.1))), w :=
          Finset.sum_fiberwise_of_maps_to (fun ξ hξ => (Finset.mem_filter.1 hξ).2) _
      _ ≤ sumW (fiber₀ v) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- Assemble.
  calc FA A v x d
      ≤ ΦA v d + ∑ ξ ∈ T, w * E (run (stB A ξ.publicKey x.1 x.2
          (some (ξ.signature x.1))) (Cache.extend d (hiddenCache beforeSigning ξ))) g := hsplit
    _ = ΦA v d + ∑ v₁ ∈ T.image (publicData (afterSigning x.1)),
          ∑ ξ ∈ T with publicData (afterSigning x.1) ξ = v₁,
            w * E (run (stB A ξ.publicKey x.1 x.2 (some (ξ.signature x.1)))
              (Cache.extend d (hiddenCache beforeSigning ξ))) g := by
        rw [hregroup]
    _ ≤ ΦA v d + ∑ v₁ ∈ T.image (publicData (afterSigning x.1)),
          κ * sumW (publicFiber (afterSigning x.1) v₁) * b' :=
        add_le_add le_rfl (Finset.sum_le_sum hfiber)
    _ ≤ ΦA v d + κ * sumW (fiber₀ v) * b' := by
        refine add_le_add le_rfl ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        exact mul_le_mul' (mul_le_mul' le_rfl hsumW) le_rfl

/-! ## The first stage -/

/-- **The first stage.** Run from the exposed keygen cache of any record `ζ₀` of the fiber, the
first attacker stage followed by the bounded continuation `FA` succeeds with at most
`κ · sumW (fiber₀ v) · b`. -/
theorem stageA_master (v : PublicData) (ζ₀ : Record) (hζ₀ : ζ₀ ∈ fiber₀ v) (b : ℕ)
    (hB : ∀ ξ ∈ fiber₀ v, CostAtMost (A.choose ξ.publicKey >>= rest₂ A ξ.publicKey ξ.1) b) :
    E (run (A.choose ζ₀.publicKey) (exposedCache beforeSigning ζ₀))
        (fun p => FA A v p.1 p.2) ≤ κ * sumW (fiber₀ v) * b := by
  have hne : Nonempty {ξ // ξ ∈ fiber₀ v} := ⟨⟨ζ₀, hζ₀⟩⟩
  have hdata : ∀ ξ ∈ fiber₀ v, publicData beforeSigning ξ = publicData beforeSigning ζ₀ :=
    fun ξ hξ => ((mem_fiber₀ v ξ).mp hξ).trans ((mem_fiber₀ v ζ₀).mp hζ₀).symm
  have hpk : ∀ ξ ∈ fiber₀ v, ξ.publicKey = ζ₀.publicKey :=
    fun ξ hξ => publicKey_data_eq beforeSigning ξ ζ₀ (hdata ξ hξ)
  have hF : ∀ (x : Message × A.State) (d : Cache) (b' : ℕ), InvA v d b' →
      (∀ j : {ξ // ξ ∈ fiber₀ v}, CostAtMost (rest₂ A ζ₀.publicKey j.1.1 x) b') →
      FA A v x d ≤ ΦA v d + κ * sumW (fiber₀ v) * b' := by
    intro x d b' hI hB'
    refine stageA_cont A v x d b' hI fun ξ hξ => ?_
    rw [hpk ξ hξ]
    exact hB' ⟨ξ, hξ⟩
  have hI0 : InvA v (exposedCache beforeSigning ζ₀) b := by
    intro ξ hξ
    rw [exposedCache_data_eq beforeSigning ξ ζ₀ (hdata ξ hξ)]
    exact Cache.Sub.refl _
  have hB0 : ∀ j : {ξ // ξ ∈ fiber₀ v},
      CostAtMost (A.choose ζ₀.publicKey >>= rest₂ A ζ₀.publicKey j.1.1) b := by
    intro j
    have h := hB j.1 j.2
    rw [hpk j.1 j.2] at h
    exact h
  have h := master_family (α := Message × A.State) (β := Bool) (J := {ξ // ξ ∈ fiber₀ v})
    (κ * sumW (fiber₀ v)) (ΦA v) (InvA v) (InvA_fresh v) (InvA_cached v) (ΦA_charge v)
    (A.choose ζ₀.publicKey) (fun j => rest₂ A ζ₀.publicKey j.1.1) (fun x d => FA A v x d) hF
    (exposedCache beforeSigning ζ₀) b hI0 hB0
  rw [ΦA_initial v ζ₀ hζ₀, zero_add] at h
  exact h

end OptimalOTS.LeanIsaBaseline
