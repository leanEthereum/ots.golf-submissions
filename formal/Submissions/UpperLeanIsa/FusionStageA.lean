import Submissions.UpperLeanIsa.FusionStageB
import Submissions.UpperLeanIsa.TierPsi

/-!
# The first stage and signing

The records with public data `v` before signing form the fiber `fiber₀ v`. After the first
attacker stage has ended with `(x, d)`, the quantity to bound is `FA v x d`: for every record of
the fiber, `1` if `d` hit a hidden keygen point of the record, else the success probability of
signing and the second stage. For a tier schedule `S` the potential with remaining budget `b` is

```
ΦA v c b = ∑ ξ ∈ fiber₀ v, w · (ind (hidden hit of ξ) + ind (second-preimage hit of ξ))
             + sumW (fiber₀ v) · (Pre(c, b) + Ψ(c) / θ + K(b))
```

(`Pre` the pre-sign potential, `Ψ` the RowGood supermartingale, `K` the budget term). It does
not grow in average at any fresh query (`ΦA_charge`, tier-proof.md A1): an index query moves
`Pre` by at most `(1 + (b - 2)/I) H'`, paid by `K`, and leaves `Ψ` a martingale; a chain or root
query moves the hidden and second-preimage terms by at most `2 · 2 ^ -129` per compression, paid
by the slope `κ₁` of `K`. The continuation (`stageA_cont`, A2): a row that is not good pays
through `Ψ / θ ≥ 1`; otherwise signing is one expectation over its outcomes, a lost signature
(`IdxPreC` or `SelfCol`) pays its weight (`loss_le`), and the second stage runs at the rate of
the signed class (`kappaB_le`). The budget master lemma gives `stageA_master` (A3).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion

open Layer.Params

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Layer.Params.encQuery
  publicFiber finiteFiber hiddenCache exposedCache queryLocation Record.query

namespace Params

variable (P : Params) (A : OracleAlgorithm.Adversary)

/-! ## Signing from a record -/

theorem revealed_record (hP : P.SecurityHyp) (ξ : Record P) (I : Index) (k : Fin numChains) :
    P.codec.revealed ξ.sk I k = ξ.word k (afterSigning P I k) := by
  unfold revealed afterSigning
  have := hP.codec.len_pos k
  exact P.table_getD ξ k _ (by omega)

theorem sigOf_record (hP : P.SecurityHyp) (ξ : Record P) (η : Nonce) (I : Index) :
    P.codec.sigOf ξ.sk (some (η, I)) =
      some (encode (fun k => ξ.word k (afterSigning P I k)) η) := by
  unfold sigOf
  simp only [Option.map_some]
  congr 2
  funext k
  exact P.revealed_record hP ξ _ k

theorem rest₂_eq_signTier (pk : PublicKey) (ξ : Record P) (hpk : ξ.pk = pk)
    (x : Message × A.State) :
    P.rest₂ A pk ξ.sk x =
      P.codec.signTier (emsg x.1 pk) >>= fun r => P.stB A pk x.1 x.2 (P.codec.sigOf ξ.sk r) := by
  unfold rest₂
  rw [sign_eq_map, bind_map_left]
  rw [show ξ.sk.pk = pk from hpk]

/-- The hidden keygen points are irrelevant to signing. -/
theorem E_rest₂_extend (hP : P.SecurityHyp) (pk : PublicKey) (ξ : Record P) (hpk : ξ.pk = pk)
    (x : Message × A.State) (d : Cache) :
    E (run (P.rest₂ A pk ξ.sk x) (Cache.extend d (hiddenCache (beforeSigning P) ξ))) g =
      E (run (P.codec.signTier (emsg x.1 pk)) d) (fun p =>
        E (run (P.stB A pk x.1 x.2 (P.codec.sigOf ξ.sk p.1))
          (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g) := by
  rw [P.rest₂_eq_signTier A pk ξ hpk, run_bind,
    P.codec.run_signTier_extend _ d _ (fun u => P.hiddenCache_enc hP _ ξ u), bind_map_left, E_bind]

/-! ## Public data at nested cuts -/

theorem publicData_mono {d₀ d₁ : Cut} (h : ∀ k, d₁ k ≤ d₀ k) (ξ ζ : Record P)
    (hd : publicData d₁ ξ = publicData d₁ ζ) : publicData d₀ ξ = publicData d₀ ζ := by
  apply Prod.ext
  · funext k
    by_cases hk : d₀ k = 0
    · have hk1 : d₁ k = 0 := by have := h k; omega
      simp only [publicData, hk, if_true, data_source_eq d₁ ξ ζ hd k hk1]
    · simp only [publicData, hk, if_false]
  · funext a
    rcases a with b | r
    · by_cases hb : d₀ b.1 ≤ b.2.val + 1
      · simp only [publicData, hb, if_true,
          data_chain_eq d₁ ξ ζ hd b (le_trans (h b.1) hb)]
      · simp only [publicData, hb, if_false]
    · simp only [publicData, data_root_eq d₁ ξ ζ hd r]

theorem afterSigning_le (I : Index) (k : Fin numChains) :
    afterSigning P I k ≤ beforeSigning P k := Nat.sub_le _ _

/-! ## The second stage after a successful signing, over all public fibers -/

theorem stageB_some (hP : P.SecurityHyp) (pk : PublicKey) (m₁ : Message) (st : A.State)
    (v : PublicData P) (T : Finset (Record P)) (hT : T ⊆ publicFiber (beforeSigning P) v)
    (hpk : ∀ ξ ∈ T, ξ.pk = pk) (d d' : Cache) (η₁ : Nonce) (I₁ : Index)
    (hext : P.codec.TierExt (emsg m₁ pk) d (some (η₁, I₁)) d')
    (hpre : ¬ P.codec.IdxPreC d (emsg m₁ pk ++ η₁) (P.codec.digit I₁))
    (hsc : ¬ P.codec.SelfCol d (emsg m₁ pk) d' (η₁, I₁))
    {ρ : ℝ≥0∞} (hρ₁ : 2 * rate ≤ ρ) (hρ₂ : (P.codec.cweight (P.codec.digit I₁) : ℝ≥0∞) / 2 ^ 127 ≤ ρ * 2)
    (hd : ∀ ξ ∈ T, Cache.Sub (exposedCache (beforeSigning P) ξ) d ∧
      ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ) ∧
      ¬ TargetHit (secondPreimageTargets P ξ) d)
    (b' : ℕ) (hb : ∀ ξ ∈ T, CostAtMost (P.stB A pk m₁ st
      (some (encode (fun k => ξ.word k (afterSigning P I₁ k)) η₁))) b') :
    ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st
        (some (encode (fun k => ξ.word k (afterSigning P I₁ k)) η₁)))
        (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g ≤
      ρ * sumW P (publicFiber (beforeSigning P) v) * b' := by
  set d₁ := afterSigning P I₁ with hd₁
  set D := T.image (publicData d₁) with hD
  have hmaps : ∀ ξ ∈ T, publicData d₁ ξ ∈ D := fun ξ hξ => Finset.mem_image_of_mem _ hξ
  have hregroup : ∀ f : Record P → ℝ≥0∞, ∑ ξ ∈ T, f ξ =
      ∑ v₁ ∈ D, ∑ ξ ∈ T with publicData d₁ ξ = v₁, f ξ :=
    fun f => (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  have hfiber : ∀ v₁ ∈ D,
      ∑ ξ ∈ T with publicData d₁ ξ = v₁, recW P * E (run (P.stB A pk m₁ st
        (some (encode (fun k => ξ.word k (d₁ k)) η₁)))
        (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g ≤
      ρ * sumW P (publicFiber d₁ v₁) * b' := by
    intro v₁ hv₁
    obtain ⟨ζ₁, hζ₁T, hζ₁⟩ := Finset.mem_image.1 hv₁
    have hζ₁F : ζ₁ ∈ publicFiber d₁ v₁ := (mem_publicFiber _ _ _).mpr hζ₁
    have hmemT : ∀ ξ ∈ T.filter (fun ξ => publicData d₁ ξ = v₁), ξ ∈ T :=
      fun ξ hξ => (Finset.mem_filter.1 hξ).1
    have hsubT : T.filter (fun ξ => publicData d₁ ξ = v₁) ⊆ publicFiber d₁ v₁ := by
      intro ξ hξ
      exact (mem_publicFiber _ _ _).mpr (Finset.mem_filter.1 hξ).2
    exact P.stageB_fiber A hP pk m₁ st d d' η₁ I₁ hext hpre hsc hρ₁ hρ₂ v₁ ζ₁ hζ₁F _ hsubT
      (fun ξ hξ => hpk ξ (hmemT ξ hξ)) (fun ξ hξ => hd ξ (hmemT ξ hξ)) b' (hb ζ₁ hζ₁T)
  have hsumW : ∑ v₁ ∈ D, sumW P (publicFiber d₁ v₁) ≤ sumW P (publicFiber (beforeSigning P) v) := by
    have hsub : ∀ v₁ ∈ D, publicFiber d₁ v₁ ⊆
        ((publicFiber (beforeSigning P) v).filter fun ξ => publicData d₁ ξ ∈ D).filter
          fun ξ => publicData d₁ ξ = v₁ := by
      intro v₁ hv₁ ξ hξ
      obtain ⟨ζ₁, hζ₁T, hζ₁⟩ := Finset.mem_image.1 hv₁
      have hξd : publicData d₁ ξ = v₁ := (mem_publicFiber _ _ _).mp hξ
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨?_, by rw [hξd]; exact hv₁⟩, hξd⟩
      apply (mem_publicFiber _ _ _).mpr
      rw [P.publicData_mono (fun k => P.afterSigning_le _ k) ξ ζ₁ (hξd.trans hζ₁.symm)]
      exact (mem_publicFiber _ _ _).mp (hT hζ₁T)
    calc ∑ v₁ ∈ D, sumW P (publicFiber d₁ v₁)
        ≤ ∑ v₁ ∈ D, ∑ ξ ∈ ((publicFiber (beforeSigning P) v).filter fun ξ =>
            publicData d₁ ξ ∈ D) with publicData d₁ ξ = v₁, recW P :=
          Finset.sum_le_sum fun v₁ hv₁ => Finset.sum_le_sum_of_subset (hsub v₁ hv₁)
      _ = ∑ ξ ∈ ((publicFiber (beforeSigning P) v).filter fun ξ => publicData d₁ ξ ∈ D),
            recW P :=
          Finset.sum_fiberwise_of_maps_to (fun ξ hξ => (Finset.mem_filter.1 hξ).2) _
      _ ≤ sumW P (publicFiber (beforeSigning P) v) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st
          (some (encode (fun k => ξ.word k (d₁ k)) η₁)))
          (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g
      = ∑ v₁ ∈ D, ∑ ξ ∈ T with publicData d₁ ξ = v₁, recW P * E (run (P.stB A pk m₁ st
          (some (encode (fun k => ξ.word k (d₁ k)) η₁)))
          (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g := hregroup _
    _ ≤ ∑ v₁ ∈ D, ρ * sumW P (publicFiber d₁ v₁) * b' := Finset.sum_le_sum hfiber
    _ = ρ * (∑ v₁ ∈ D, sumW P (publicFiber d₁ v₁)) * b' := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ρ * sumW P (publicFiber (beforeSigning P) v) * b' :=
        mul_le_mul' (mul_le_mul' le_rfl hsumW) le_rfl

/-! ## The first-stage potential -/

/-- The records with public data `v` before signing. -/
def fiber₀ (v : PublicData P) : Finset (Record P) := publicFiber (beforeSigning P) v

variable (S : Tier.Sched)

/-- The first-stage potential with remaining budget `b`: hidden and second-preimage hits of the
fiber, and, weighted by the fiber, the pre-sign potential `Pre`, the RowGood potential and the
budget term `K(b)`. -/
def ΦA (v : PublicData P) (c : Cache) (b : ℕ) : ℝ≥0∞ :=
  hiddenHitPotential (beforeSigning P) (P.fiber₀ v) c +
    ∑ ξ ∈ P.fiber₀ v, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
    sumW P (P.fiber₀ v) * (P.codec.Pre S c b + P.codec.PsiE S c + S.Kb b)

variable {S}

/-- The budget invariant of the index potential: every index entry was paid by an index query of
two compressions. -/
def Inv (c : Cache) (b : ℕ) : Prop := 2 * P.codec.encCount c + b ≤ 2 ^ 127

/-- The first-stage invariant. -/
def InvA (v : PublicData P) (c : Cache) (b : ℕ) : Prop :=
  (∀ ξ ∈ P.fiber₀ v, Cache.Sub (exposedCache (beforeSigning P) ξ) c) ∧ P.Inv c b

theorem Inv_fresh : ∀ c b q, P.Inv c b → c q = none → queryCost (.inr q) ≤ b →
    ∀ u, P.Inv (c.cacheQuery q u) (b - queryCost (.inr q)) := by
  intro c b q hI _ hcost u
  unfold Inv at hI ⊢
  by_cases henc : ∃ u₀, q = P.codec.encQuery u₀
  · obtain ⟨u₀, rfl⟩ := henc
    have h1 := P.codec.encCount_cacheQuery_le c (P.codec.encQuery u₀) u
    have h2 : queryCost (.inr (P.codec.encQuery u₀)) = 2 := queryCost_896 (by unfold Layer.Params.encQuery; rfl)
    omega
  · have h1 := P.codec.encCount_cacheQuery_of_ne c (fun u' h => henc ⟨u', h⟩) u
    omega

theorem Inv_cached : ∀ c b q, P.Inv c b → (c q).isSome → queryCost (.inr q) ≤ b →
    P.Inv c (b - queryCost (.inr q)) := by
  intro c b q hI _ _
  unfold Inv at hI ⊢
  omega

theorem InvA_fresh (v : PublicData P) : ∀ c b q, P.InvA v c b → c q = none →
    queryCost (.inr q) ≤ b → ∀ u, P.InvA v (c.cacheQuery q u) (b - queryCost (.inr q)) := by
  intro c b q hI hq hcost u
  exact ⟨fun ξ hξ => (hI.1 ξ hξ).trans (Cache.sub_cacheQuery_of_none hq u),
    P.Inv_fresh c b q hI.2 hq hcost u⟩

theorem InvA_cached (v : PublicData P) : ∀ c b q, P.InvA v c b → (c q).isSome →
    queryCost (.inr q) ≤ b → P.InvA v c (b - queryCost (.inr q)) := by
  intro c b q hI hq hcost
  exact ⟨hI.1, P.Inv_cached c b q hI.2 hq hcost⟩

theorem avg_finset_sum {ι : Type} (T : Finset ι) (f : ι → BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ∑ ξ ∈ T, f ξ u =
      ∑ ξ ∈ T, ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f ξ u := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem spr_part_charge (c : Cache) (q : Query) (hq : c q = none) (T : Finset (Record P)) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) (c.cacheQuery q u)) ≤
      ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
        sumW P T * (rate * queryCost (.inr q)) := by
  rw [avg_finset_sum, sumW, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [avg_mul', ← mul_add]
  exact mul_le_mul' le_rfl ((ind_target_charge _ c q hq).trans
    (add_le_add le_rfl (secondPreimage_charge ξ q)))

theorem spr_part_enc (hP : P.SecurityHyp) (c : Cache) (u₀ : EncInput) (T : Finset (Record P)) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, recW P *
          ind (TargetHit (secondPreimageTargets P ξ) (c.cacheQuery (P.codec.encQuery u₀) u)) =
      ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) := by
  have he : ∀ u, ∑ ξ ∈ T, recW P *
      ind (TargetHit (secondPreimageTargets P ξ) (c.cacheQuery (P.codec.encQuery u₀) u)) =
      ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) := fun u =>
    Finset.sum_congr rfl fun ξ _ => by
      rw [ind_congr (targetHit_cacheQuery_of_empty _ c _ u (P.spr_enc hP ξ u₀))]
  simp only [he]
  exact sum_inv_card_mul _

theorem two_rate_le_k1 (hS : S.Valid) : 2 * rate ≤ S.k1E := by
  rw [mul_comm, rate_two]
  exact S.rate_le_k1 hS

/-- The potential is charged nothing by a fresh query in average (A1). -/
theorem ΦA_charge (hP : P.SecurityHyp) (hS : S.Valid) (hT : P.codec.TierHyp S) (v : PublicData P) :
    ∀ c b q, P.InvA v c b → c q = none → queryCost (.inr q) ≤ b →
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        P.ΦA S v (c.cacheQuery q u) (b - queryCost (.inr q)) ≤ P.ΦA S v c b := by
  intro c b q _ hq hcost
  unfold ΦA
  rw [avg_add', avg_add', avg_mul', avg_add', avg_add', sum_inv_card_mul]
  by_cases henc : ∃ u₀, q = P.codec.encQuery u₀
  · obtain ⟨u₀, rfl⟩ := henc
    have hc2 : queryCost (.inr (P.codec.encQuery u₀)) = 2 := P.codec.queryCost_enc u₀
    rw [hc2] at hcost ⊢
    have h1 := P.hiddenHit_charge_enc hP (beforeSigning P) (P.fiber₀ v) c u₀
    have h2 := P.spr_part_enc hP c u₀ (P.fiber₀ v)
    have h3 := P.codec.pre_charge_enc S hS hT hq hcost
    have h4 := P.codec.PsiE_enc hS hT hq
    have h5 := S.Kb_step_enc hS hcost
    refine add_le_add (add_le_add h1 (le_of_eq h2)) (mul_le_mul' le_rfl ?_)
    rw [h4]
    calc (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
            P.codec.Pre S (c.cacheQuery (P.codec.encQuery u₀) u) (b - 2)) + P.codec.PsiE S c + S.Kb (b - 2)
        ≤ (P.codec.Pre S c b + (1 + ((b - 2 : ℕ) : ℝ≥0∞) / 2 ^ 127) * S.hpE) + P.codec.PsiE S c +
            S.Kb (b - 2) := by gcongr
      _ = P.codec.Pre S c b + P.codec.PsiE S c +
            (S.Kb (b - 2) + (1 + ((b - 2 : ℕ) : ℝ≥0∞) / 2 ^ 127) * S.hpE) := by ring
      _ ≤ P.codec.Pre S c b + P.codec.PsiE S c + S.Kb b := by gcongr
  · have hne : ∀ u, q ≠ P.codec.encQuery u := fun u h => henc ⟨u, h⟩
    have h1 := P.hiddenHit_charge hP beforeSigning_valid v (P.fiber₀ v) (fun ξ h => h) c q
    have h2 := P.spr_part_charge c q hq (P.fiber₀ v)
    have h3 : ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        P.codec.Pre S (c.cacheQuery q u) (b - queryCost (.inr q)) =
        P.codec.Pre S c (b - queryCost (.inr q)) := by
      simp only [P.codec.pre_of_ne S hne]
      exact sum_inv_card_mul _
    have h4 : ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * P.codec.PsiE S (c.cacheQuery q u) =
        P.codec.PsiE S c := by
      simp only [P.codec.PsiE_of_ne hne]
      exact sum_inv_card_mul _
    have h5 := S.Kb_step hcost
    have h6 := P.codec.pre_mono S c (Nat.sub_le b (queryCost (.inr q)))
    have h7 := two_rate_le_k1 hS
    rw [h3, h4]
    set n : ℝ≥0∞ := (queryCost (.inr q) : ℝ≥0∞)
    calc _ ≤ (hiddenHitPotential (beforeSigning P) (P.fiber₀ v) c +
            rate * sumW P (publicFiber (beforeSigning P) v) * n) +
          (∑ ξ ∈ P.fiber₀ v, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
            sumW P (P.fiber₀ v) * (rate * n)) +
          sumW P (P.fiber₀ v) * (P.codec.Pre S c (b - queryCost (.inr q)) + P.codec.PsiE S c +
            S.Kb (b - queryCost (.inr q))) := add_le_add (add_le_add h1 h2) le_rfl
      _ = hiddenHitPotential (beforeSigning P) (P.fiber₀ v) c +
          ∑ ξ ∈ P.fiber₀ v, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
          sumW P (P.fiber₀ v) * (P.codec.Pre S c (b - queryCost (.inr q)) + P.codec.PsiE S c +
            (S.Kb (b - queryCost (.inr q)) + 2 * rate * n)) := by
          unfold fiber₀
          ring
      _ ≤ hiddenHitPotential (beforeSigning P) (P.fiber₀ v) c +
          ∑ ξ ∈ P.fiber₀ v, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
          sumW P (P.fiber₀ v) * (P.codec.Pre S c b + P.codec.PsiE S c +
            (S.Kb (b - queryCost (.inr q)) + S.k1E * n)) := by
          gcongr
      _ ≤ _ := by
          gcongr

theorem ΦA_cached (v : PublicData P) : ∀ c b q, P.InvA v c b → (c q).isSome →
    queryCost (.inr q) ≤ b → P.ΦA S v c (b - queryCost (.inr q)) ≤ P.ΦA S v c b := by
  intro c b q _ _ _
  unfold ΦA
  gcongr
  · exact P.codec.pre_mono S c (Nat.sub_le _ _)
  · exact S.Kb_mono (Nat.sub_le _ _)

theorem encCount_noEnc (c : Cache) (hc : ∀ u, c (P.codec.encQuery u) = none) : P.codec.encCount c = 0 := by
  unfold encCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _
  rw [hc u]
  simp

theorem ΦA_initial (hP : P.SecurityHyp) (hS : S.Valid) (v : PublicData P) (ζ₀ : Record P)
    (hζ₀ : ζ₀ ∈ P.fiber₀ v) (b : ℕ) :
    P.ΦA S v (exposedCache (beforeSigning P) ζ₀) b ≤
      sumW P (P.fiber₀ v) * ((2 ^ 500 : ℝ≥0∞)⁻¹ + S.Kb b) := by
  have hdata : ∀ ξ ∈ P.fiber₀ v,
      publicData (beforeSigning P) ξ = publicData (beforeSigning P) ζ₀ :=
    fun ξ hξ => ((mem_publicFiber _ _ _).mp hξ).trans ((mem_publicFiber _ _ _).mp hζ₀).symm
  have hexp : ∀ ξ ∈ P.fiber₀ v,
      exposedCache (beforeSigning P) ζ₀ = exposedCache (beforeSigning P) ξ :=
    fun ξ hξ => (exposedCache_data_eq hP beforeSigning_valid ξ ζ₀ (hdata ξ hξ)).symm
  have hno : ∀ u, exposedCache (beforeSigning P) ζ₀ (P.codec.encQuery u) = none :=
    fun u => P.exposedCache_enc hP _ ζ₀ u
  have hspr : ∑ ξ ∈ P.fiber₀ v, recW P *
      ind (TargetHit (secondPreimageTargets P ξ) (exposedCache (beforeSigning P) ζ₀)) = 0 := by
    refine Finset.sum_eq_zero fun ξ hξ => ?_
    rw [hexp ξ hξ]
    have : ¬ TargetHit (secondPreimageTargets P ξ) (exposedCache (beforeSigning P) ξ) := by
      rintro ⟨q, u, hq, hu⟩
      obtain ⟨a, -, rfl, -⟩ := (exposedCache_some_iff hP _ ξ q u).mp hq
      rw [secondPreimageTargets_query hP] at hu
      exact Finset.notMem_empty _ hu
    rw [ind_not this, mul_zero]
  unfold ΦA
  rw [hiddenHitPotential_zero _ _ _ fun ξ hξ => by
      rw [hexp ξ hξ]; exact exposure_disjoint _ ξ,
    hspr, P.codec.pre_noEnc S hno, zero_add, zero_add, zero_add]
  exact mul_le_mul' le_rfl (add_le_add (P.codec.PsiE_noEnc hS hno) le_rfl)

/-! ## The continuation after the first stage -/

/-- The quantity bounded after the first stage. -/
def FA (pk : PublicKey) (v : PublicData P) (x : Message × A.State) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ P.fiber₀ v, recW P * (if Cache.Hits d (hiddenCache (beforeSigning P) ξ) then 1 else
    E (run (P.rest₂ A pk ξ.sk x) (Cache.extend d (hiddenCache (beforeSigning P) ξ))) g)

theorem rowU_le_encCount (d : Cache) (M : EMessage) : P.codec.rowU d M ≤ P.codec.encCount d := by
  unfold rowU encCount
  refine Finset.card_le_card_of_injOn (fun η => M ++ η) ?_ ?_
  · intro η hη
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hη ⊢
    exact hη
  · intro η₁ _ η₂ _ h
    exact append_nonce_inj M h

/-- The rate after signing covers the index charge of its class. -/
theorem cweight_le_kappaB (hT : P.codec.TierHyp S) {η : Nonce} {I : Index} (hI : P.codec.Accepted I) :
    (P.codec.cweight (P.codec.digit I) : ℝ≥0∞) / 2 ^ 127 ≤ P.codec.kappaB S (some (η, I)) * 2 := by
  have hc : (P.codec.cweight (P.codec.digit I) : ℝ≥0∞) / 2 ^ 127 = S.pE (P.codec.tierI S I) := by
    rw [Tier.Sched.pE, hT.K_eq, ← (tierI_spec hT hI).2]
    rfl
  rw [hc]
  simp only [kappaB, Tier.Sched.fE]
  rw [add_mul, ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
    show (2 ^ 128 : ℝ≥0∞)⁻¹ * 2 = (2 ^ 127)⁻¹ by
      rw [pow_succ, ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), mul_assoc,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]]
  exact le_add_tsub

theorem two_rate_le_kappaB (r : Option (Nonce × Index)) : 2 * rate ≤ P.codec.kappaB S r := by
  have h : 2 * rate = (2 ^ 128 : ℝ≥0∞)⁻¹ := by rw [mul_comm, rate_two]
  rw [h]
  cases r with
  | none => exact le_rfl
  | some b => exact le_self_add

/-- **The continuation after the first stage** (A2): signing as one expectation over its
outcomes, then the second stage. -/
theorem stageA_cont (hP : P.SecurityHyp) (hS : S.Valid) (hT : P.codec.TierHyp S) (pk : PublicKey)
    (v : PublicData P) (hpk : ∀ ξ ∈ P.fiber₀ v, ξ.pk = pk) (x : Message × A.State) (d : Cache)
    (b' : ℕ) (hI : P.InvA v d b') (hB : ∀ ξ ∈ P.fiber₀ v, CostAtMost (P.rest₂ A pk ξ.sk x) b') :
    P.FA A pk v x d ≤ P.ΦA S v d b' := by
  rcases (P.fiber₀ v).eq_empty_or_nonempty with hFe | ⟨ξ₀, hξ₀⟩
  · unfold FA
    rw [hFe, Finset.sum_empty]
    exact bot_le
  set M := emsg x.1 pk with hM
  set F := P.fiber₀ v with hF
  have hFA_le : P.FA A pk v x d ≤ sumW P F := by
    unfold FA sumW
    refine Finset.sum_le_sum fun ξ _ => ?_
    refine le_trans (mul_le_mul' le_rfl ?_) (le_of_eq (mul_one _))
    split_ifs
    · exact le_rfl
    · exact E_le_one _ g_le_one
  -- a row that is not good pays everything through the RowGood potential
  by_cases hRG : ¬ P.codec.RowGood S d M
  · have hu : P.codec.rowU d M ≤ 2 ^ 126 := by
      have := P.rowU_le_encCount d M
      have h2 := hI.2
      unfold Inv at h2
      omega
    have h1 := P.codec.one_le_PsiE hS hT hu hRG
    refine hFA_le.trans ?_
    unfold ΦA
    refine le_trans ?_ le_add_self
    calc sumW P F = sumW P F * 1 := (mul_one _).symm
      _ ≤ sumW P F * (P.codec.Pre S d b' + P.codec.PsiE S d + S.Kb b') := by
          gcongr
          exact h1.trans (le_add_self.trans le_self_add)
  push_neg at hRG
  set T := F.filter (fun ξ => ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ) ∧
    ¬ TargetHit (secondPreimageTargets P ξ) d) with hTdef
  have hT' : T ⊆ F := Finset.filter_subset _ _
  have hTd : ∀ ξ ∈ T, Cache.Sub (exposedCache (beforeSigning P) ξ) d ∧
      ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ) ∧
      ¬ TargetHit (secondPreimageTargets P ξ) d := by
    intro ξ hξ
    have h := (Finset.mem_filter.1 hξ).2
    exact ⟨hI.1 ξ (hT' hξ), h.1, h.2⟩
  set Fn : Option (Nonce × Index) → Cache → ℝ≥0∞ := fun r d' => ∑ ξ ∈ T, recW P *
    E (run (P.stB A pk x.1 x.2 (P.codec.sigOf ξ.sk r))
      (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g with hFn
  -- Step 1: records hit in the first stage pay their indicator; the others sign.
  have hsplit : P.FA A pk v x d ≤ hiddenHitPotential (beforeSigning P) F d +
      ∑ ξ ∈ F, recW P * ind (TargetHit (secondPreimageTargets P ξ) d) +
      E (run (P.codec.signTier M) d) (fun p => Fn p.1 p.2) := by
    rw [hFn, E_weighted_sum, hTdef, Finset.sum_filter]
    unfold FA hiddenHitPotential
    rw [← hF, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ξ hξ => ?_
    by_cases hh : Cache.Hits d (hiddenCache (beforeSigning P) ξ)
    · rw [if_pos hh, ind_of hh]
      exact le_self_add.trans le_self_add
    · by_cases ht : TargetHit (secondPreimageTargets P ξ) d
      · rw [if_neg hh, ind_not hh, ind_of ht, if_neg (fun h => h.2 ht), add_zero, mul_zero,
          zero_add]
        exact mul_le_mul' le_rfl (E_le_one _ g_le_one)
      · rw [if_neg hh, ind_not hh, ind_not ht, if_pos ⟨hh, ht⟩]
        simp only [mul_zero, zero_add]
        rw [P.E_rest₂_extend A hP pk ξ (hpk ξ hξ) x d]
  -- Step 2: the budget of the second stage after all trials.
  have hcost : ∀ ξ ∈ F, 2 * trials ≤ b' ∧ ∀ p ∈ support (run (P.codec.signTier M) d),
      CostAtMost (P.stB A pk x.1 x.2 (P.codec.sigOf ξ.sk p.1)) (b' - 2 * trials) := by
    intro ξ hξ
    have h := hB ξ hξ
    rw [P.rest₂_eq_signTier A pk ξ (hpk ξ hξ), signTier] at h
    have := P.codec.signTierLoop_cost M _ trials ∅ none b' (by simp) h
    exact ⟨this.1, fun p hp => this.2 d p hp⟩
  have hL : 2 * trials ≤ b' := (hcost ξ₀ hξ₀).1
  set b'' := b' - 2 * trials with hb''
  -- Step 3: each outcome of signing.
  have hout : ∀ p ∈ support (run (P.codec.signTier M) d), Fn p.1 p.2 ≤
      sumW P F * (if ∃ b, p.1 = some b ∧
        (P.codec.IdxPreC d (M ++ b.1) (P.codec.digit b.2) ∨ P.codec.SelfCol d M p.2 b) then 1 else 0) +
      P.codec.kappaB S p.1 * sumW P F * b'' := by
    intro p hp
    have hext := P.codec.signTier_ext M d p hp
    rcases hr : p.1 with _ | ⟨η₁, I₁⟩
    · have hb0 : CostAtMost (P.stB A pk x.1 x.2 none) b'' := by
        have := (hcost ξ₀ hξ₀).2 p hp
        rwa [hr] at this
      have h := P.stageB_none A hP pk x.1 x.2 v T hT' (fun ξ hξ => hpk ξ (hT' hξ)) d p.2
        (P.encExt_of_tierExt hext) hTd b'' hb0
      refine le_trans ?_ (le_trans (le_trans h ?_) le_add_self)
      · exact le_of_eq rfl
      · gcongr
        exact P.two_rate_le_kappaB none
        exact le_of_eq (by rw [hF]; rfl)
    · rw [hr] at hext
      by_cases hloss : P.codec.IdxPreC d (M ++ η₁) (P.codec.digit I₁) ∨ P.codec.SelfCol d M p.2 (η₁, I₁)
      · have hone : Fn (some (η₁, I₁)) p.2 ≤ sumW P F := by
          rw [hFn]
          refine le_trans (Finset.sum_le_sum fun ξ _ =>
            le_trans (mul_le_mul' le_rfl (E_le_one _ g_le_one)) (le_of_eq (mul_one _)))
            (sumW_mono hT')
        refine hone.trans (le_trans ?_ le_self_add)
        rw [if_pos ⟨(η₁, I₁), rfl, hloss⟩, mul_one]
      · push_neg at hloss
        have hacc := (hext.2.2 _ rfl).1
        have hBξ : ∀ ξ ∈ T, CostAtMost (P.stB A pk x.1 x.2
            (some (encode (fun k => ξ.word k (afterSigning P I₁ k)) η₁))) b'' := by
          intro ξ hξ
          have h := (hcost ξ (hT' hξ)).2 p hp
          rwa [hr, P.sigOf_record hP] at h
        have h := P.stageB_some A hP pk x.1 x.2 v T hT' (fun ξ hξ => hpk ξ (hT' hξ)) d p.2 η₁
          I₁ hext hloss.1 hloss.2 (P.two_rate_le_kappaB (some (η₁, I₁)))
          (P.cweight_le_kappaB hT hacc) hTd b'' hBξ
        have hFn' : Fn (some (η₁, I₁)) p.2 = ∑ ξ ∈ T, recW P * E (run (P.stB A pk x.1 x.2
            (some (encode (fun k => ξ.word k (afterSigning P I₁ k)) η₁)))
            (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g := by
          rw [hFn]
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [P.sigOf_record hP]
        rw [hFn']
        exact h.trans le_add_self
  -- Step 4: the expectation over signing.
  have hsig : E (run (P.codec.signTier M) d) (fun p => Fn p.1 p.2) ≤
      sumW P F * (P.codec.Gp S d + P.codec.Zp S d + P.codec.Yp S d +
        Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum) +
      sumW P F * b'' * ((2 ^ 128 : ℝ≥0∞)⁻¹ + ENNReal.ofReal S.Pos / 2) := by
    calc E (run (P.codec.signTier M) d) (fun p => Fn p.1 p.2)
        ≤ E (run (P.codec.signTier M) d) (fun p => sumW P F * (if ∃ b, p.1 = some b ∧
            (P.codec.IdxPreC d (M ++ b.1) (P.codec.digit b.2) ∨ P.codec.SelfCol d M p.2 b) then 1 else 0) +
            sumW P F * b'' * P.codec.kappaB S p.1) := by
          refine expectedValue_mono_of_support fun p hp => (hout p hp).trans (le_of_eq ?_)
          ring
      _ = sumW P F * E (run (P.codec.signTier M) d) (fun p => if ∃ b, p.1 = some b ∧
            (P.codec.IdxPreC d (M ++ b.1) (P.codec.digit b.2) ∨ P.codec.SelfCol d M p.2 b) then 1 else 0) +
          sumW P F * b'' * E (run (P.codec.signTier M) d) (fun p => P.codec.kappaB S p.1) := by
          rw [E_add', E_const_mul, E_const_mul]
      _ ≤ _ := by
          gcongr
          · exact P.codec.loss_le hS hT hRG
          · exact P.codec.kappaB_le hS hT hRG
  -- Step 5: assemble.
  refine hsplit.trans ?_
  unfold ΦA
  rw [← hF]
  refine add_le_add le_rfl (le_trans hsig ?_)
  have hL' : ((2 * trials : ℕ) : ℝ≥0∞) + b'' = b' := by
    rw [hb'', ← Nat.cast_add, Nat.add_sub_cancel' hL]
  have hSC := S.SCf_le hS
  have hkp := S.kpost_le hS
  have hGZY : P.codec.Gp S d + P.codec.Zp S d + P.codec.Yp S d ≤ P.codec.Pre S d b' := by
    unfold Pre
    gcongr
    exact le_mul_of_one_le_left bot_le le_self_add
  have hk1 : S.k1E * b' ≤ S.Kb b' := by
    unfold Tier.Sched.Kb
    exact le_self_add
  calc sumW P F * (P.codec.Gp S d + P.codec.Zp S d + P.codec.Yp S d +
          Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum) +
        sumW P F * b'' * ((2 ^ 128 : ℝ≥0∞)⁻¹ + ENNReal.ofReal S.Pos / 2)
      ≤ sumW P F * (P.codec.Pre S d b' + 2 * 2 ^ 19 * S.k1E) + sumW P F * b'' * S.k1E := by
        gcongr
    _ = sumW P F * (P.codec.Pre S d b' + S.k1E * (((2 * trials : ℕ) : ℝ≥0∞) + b'')) := by
        unfold trials
        push_cast
        ring
    _ ≤ sumW P F * (P.codec.Pre S d b' + P.codec.PsiE S d + S.Kb b') := by
        rw [hL']
        gcongr
        · exact le_self_add

/-! ## The first stage -/

theorem stageA_master (hP : P.SecurityHyp) (hS : S.Valid) (hT : P.codec.TierHyp S) (v : PublicData P)
    (ζ₀ : Record P) (hζ₀ : ζ₀ ∈ P.fiber₀ v) (b : ℕ) (hb : b ≤ 2 ^ 127)
    (hB : ∀ ξ ∈ P.fiber₀ v, CostAtMost (A.choose ζ₀.pk >>= P.rest₂ A ζ₀.pk ξ.sk) b) :
    E (run (A.choose ζ₀.pk) (exposedCache (beforeSigning P) ζ₀))
        (fun p => P.FA A ζ₀.pk v p.1 p.2) ≤
      sumW P (P.fiber₀ v) * ((2 ^ 500 : ℝ≥0∞)⁻¹ + S.Kb b) := by
  haveI hne : Nonempty {ξ // ξ ∈ P.fiber₀ v} := ⟨⟨ζ₀, hζ₀⟩⟩
  have hdata : ∀ ξ ∈ P.fiber₀ v,
      publicData (beforeSigning P) ξ = publicData (beforeSigning P) ζ₀ :=
    fun ξ hξ => ((mem_publicFiber _ _ _).mp hξ).trans ((mem_publicFiber _ _ _).mp hζ₀).symm
  have hpk : ∀ ξ ∈ P.fiber₀ v, ξ.pk = ζ₀.pk :=
    fun ξ hξ => data_pk_eq _ ξ ζ₀ (hdata ξ hξ)
  have hF : ∀ (x : Message × A.State) (d : Cache) (b' : ℕ), P.InvA v d b' →
      (∀ j : {ξ // ξ ∈ P.fiber₀ v}, CostAtMost (P.rest₂ A ζ₀.pk j.1.sk x) b') →
      P.FA A ζ₀.pk v x d ≤ P.ΦA S v d b' :=
    fun x d b' hI hB' => P.stageA_cont A hP hS hT ζ₀.pk v hpk x d b' hI fun ξ hξ => hB' ⟨ξ, hξ⟩
  have hI0 : P.InvA v (exposedCache (beforeSigning P) ζ₀) b := by
    refine ⟨fun ξ hξ => ?_, ?_⟩
    · rw [exposedCache_data_eq hP beforeSigning_valid ζ₀ ξ (hdata ξ hξ).symm]
      exact Cache.Sub.refl _
    · unfold Inv
      rw [P.encCount_noEnc _ fun u => P.exposedCache_enc hP _ ζ₀ u, mul_zero, zero_add]
      exact hb
  have h := master_budget_family (α := Message × A.State) (β := Bool) (J := {ξ // ξ ∈ P.fiber₀ v})
    (P.ΦA S v) (P.InvA v) (P.InvA_fresh v) (P.InvA_cached v)
    (P.ΦA_charge hP hS hT v) (P.ΦA_cached v) (A.choose ζ₀.pk) (fun j => P.rest₂ A ζ₀.pk j.1.sk)
    (fun x d => P.FA A ζ₀.pk v x d) hF (exposedCache (beforeSigning P) ζ₀) b hI0
    (fun j => hB j.1 j.2)
  exact h.trans (P.ΦA_initial hP hS v ζ₀ hζ₀ b)

end Params

end OptimalOTS.LeanIsaBaseline.Layer.Fusion
