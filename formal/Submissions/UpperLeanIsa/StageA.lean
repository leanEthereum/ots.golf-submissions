import Submissions.UpperLeanIsa.StageB
import Submissions.UpperLeanIsa.RowPotential

/-!
# The first stage and signing

The records with public data `v` before signing form the fiber `fiber₀ v`; the bound is over a
set `T` of good records of the fiber. After the first attacker stage has ended with `(x, d)`, the
quantity to bound is `FA v T x d`: for every record of `T`, `1` if `d` hit a hidden keygen point
of the record, else the success probability of signing and the second stage. The potential

```
ΦA v T c = ∑ ξ ∈ T, w · (ind (hidden hit of ξ) + ind (second-preimage hit of ξ))
           + sumW (fiber₀ v) · θ ψ(c)
```

(`ψ` the row potential of the index cache, ported from UpperRiscv) grows by at most
`κ · sumW (fiber₀ v)` per compression, split by query shape (`ΦA_charge`): an index query only
moves `θ ψ`, by at most `2 · 2 ^ -127` per query (`psi_charge`), and every other query only
the hidden and second-preimage terms, by at most `(1 + 3) · 2 ^ -129` per compression. The
continuation is bounded by signing as one disjoint case split (`signRho_bound`, with `θ ψ`
bounding the loss of a pre-held signed index, `psi_dom`), then the second stage (`stageB_none`,
`stageB_some`) (`stageA_cont`). The master lemma gives `stageA_master`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.validSet Params.encQuery
  Params.V Params.validInputs publicFiber finiteFiber hiddenCache exposedCache
  queryLocation Record.query RowPot.idxBits RowPot.nonceBits

namespace Params

variable (P : Params) (A : OracleAlgorithm.Adversary)

/-! ## Signing from a record -/

theorem table_getD (ξ : Record P) (k : Fin numChains) (j : ℕ) (hj : j < P.len k) :
    (ξ.table k).getD j 0 = ξ.word k j := by
  unfold Record.table
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem revealed_record (hP : P.Hyp) (ξ : Record P) (I : Index) (k : Fin numChains) :
    P.revealed ξ.sk I k = ξ.word k (afterSigning P I k) := by
  unfold revealed afterSigning
  have := hP.len_pos k
  exact P.table_getD ξ k _ (by omega)

theorem sigOfIdx_record (hP : P.Hyp) (ξ : Record P) (η : Nonce) (i : P.Idx) :
    P.sigOfIdx ξ.sk (some (η, i)) =
      some (encode (fun k => ξ.word k (afterSigning P (idxWord i.val) k)) η) := by
  unfold sigOfIdx
  simp only [Option.map_some]
  congr 2
  funext k
  exact P.revealed_record hP ξ _ k

theorem sigOfIdx_none (sk : SecretKey) : P.sigOfIdx sk none = none := rfl

theorem rest₂_eq_signIdx (pk : PublicKey) (ξ : Record P) (hpk : ξ.pk = pk)
    (x : Message × A.State) :
    P.rest₂ A pk ξ.sk x =
      P.signIdx (emsg x.1 pk) >>= fun r => P.stB A pk x.1 x.2 (P.sigOfIdx ξ.sk r) := by
  unfold rest₂
  rw [sign_eq_map, bind_map_left]
  rw [show ξ.sk.pk = pk from hpk]

/-- The hidden keygen points are irrelevant to signing. -/
theorem E_rest₂_extend (hP : P.Hyp) (pk : PublicKey) (ξ : Record P) (hpk : ξ.pk = pk)
    (x : Message × A.State) (d : Cache) :
    E (run (P.rest₂ A pk ξ.sk x) (Cache.extend d (hiddenCache (beforeSigning P) ξ))) g =
      E (run (P.signIdx (emsg x.1 pk)) d) (fun p =>
        E (run (P.stB A pk x.1 x.2 (P.sigOfIdx ξ.sk p.1))
          (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g) := by
  rw [P.rest₂_eq_signIdx A pk ξ hpk, run_bind,
    P.run_signIdx_extend _ d _ (fun u => P.hiddenCache_enc hP _ ξ u), bind_map_left, E_bind]

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

theorem stageB_some (hP : P.Hyp) (pk : PublicKey) (m₁ : Message) (st : A.State)
    (v : PublicData P) (T : Finset (Record P)) (hT : T ⊆ publicFiber (beforeSigning P) v)
    (hG : ∀ ξ ∈ T, ξ.Good)
    (hpk : ∀ ξ ∈ T, ξ.pk = pk) (d d' : Cache) (η₁ : Nonce) (i₁ : P.Idx)
    (hext : P.SignExt (emsg m₁ pk) d (some (η₁, i₁)) d')
    (hpre : ¬ P.IdxPre d (emsg m₁ pk ++ η₁) i₁.val)
    (hd : ∀ ξ ∈ T, Cache.Sub (exposedCache (beforeSigning P) ξ) d ∧
      ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ) ∧
      ¬ TargetHit (secondPreimageTargets P ξ) d)
    (b' : ℕ) (hb : ∀ ξ ∈ T, CostAtMost (P.stB A pk m₁ st
      (some (encode (fun k => ξ.word k (afterSigning P (idxWord i₁.val) k)) η₁))) b') :
    ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st
        (some (encode (fun k => ξ.word k (afterSigning P (idxWord i₁.val) k)) η₁)))
        (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g ≤
      κ * sumW P (publicFiber (beforeSigning P) v) * b' := by
  set d₁ := afterSigning P (idxWord i₁.val) with hd₁
  set S := T.image (publicData d₁) with hS
  have hmaps : ∀ ξ ∈ T, publicData d₁ ξ ∈ S := fun ξ hξ => Finset.mem_image_of_mem _ hξ
  have hregroup : ∀ f : Record P → ℝ≥0∞, ∑ ξ ∈ T, f ξ =
      ∑ v₁ ∈ S, ∑ ξ ∈ T with publicData d₁ ξ = v₁, f ξ :=
    fun f => (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  have hfiber : ∀ v₁ ∈ S,
      ∑ ξ ∈ T with publicData d₁ ξ = v₁, recW P * E (run (P.stB A pk m₁ st
        (some (encode (fun k => ξ.word k (d₁ k)) η₁)))
        (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g ≤
      κ * sumW P (publicFiber d₁ v₁) * b' := by
    intro v₁ hv₁
    obtain ⟨ζ₁, hζ₁T, hζ₁⟩ := Finset.mem_image.1 hv₁
    have hζ₁F : ζ₁ ∈ publicFiber d₁ v₁ := (mem_publicFiber _ _ _).mpr hζ₁
    have hmemT : ∀ ξ ∈ T.filter (fun ξ => publicData d₁ ξ = v₁), ξ ∈ T :=
      fun ξ hξ => (Finset.mem_filter.1 hξ).1
    have hsubT : T.filter (fun ξ => publicData d₁ ξ = v₁) ⊆ publicFiber d₁ v₁ := by
      intro ξ hξ
      exact (mem_publicFiber _ _ _).mpr (Finset.mem_filter.1 hξ).2
    exact P.stageB_fiber A hP pk m₁ st d d' η₁ i₁ hext hpre v₁ ζ₁ hζ₁F _ hsubT
      (fun ξ hξ => hG ξ (hmemT ξ hξ))
      (fun ξ hξ => hpk ξ (hmemT ξ hξ)) (fun ξ hξ => hd ξ (hmemT ξ hξ)) b' (hb ζ₁ hζ₁T)
  have hsumW : ∑ v₁ ∈ S, sumW P (publicFiber d₁ v₁) ≤ sumW P (publicFiber (beforeSigning P) v) := by
    have hsub : ∀ v₁ ∈ S, publicFiber d₁ v₁ ⊆
        ((publicFiber (beforeSigning P) v).filter fun ξ => publicData d₁ ξ ∈ S).filter
          fun ξ => publicData d₁ ξ = v₁ := by
      intro v₁ hv₁ ξ hξ
      obtain ⟨ζ₁, hζ₁T, hζ₁⟩ := Finset.mem_image.1 hv₁
      have hξd : publicData d₁ ξ = v₁ := (mem_publicFiber _ _ _).mp hξ
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨?_, by rw [hξd]; exact hv₁⟩, hξd⟩
      apply (mem_publicFiber _ _ _).mpr
      rw [P.publicData_mono (fun k => P.afterSigning_le _ k) ξ ζ₁ (hξd.trans hζ₁.symm)]
      exact (mem_publicFiber _ _ _).mp (hT hζ₁T)
    calc ∑ v₁ ∈ S, sumW P (publicFiber d₁ v₁)
        ≤ ∑ v₁ ∈ S, ∑ ξ ∈ ((publicFiber (beforeSigning P) v).filter fun ξ =>
            publicData d₁ ξ ∈ S) with publicData d₁ ξ = v₁, recW P :=
          Finset.sum_le_sum fun v₁ hv₁ => Finset.sum_le_sum_of_subset (hsub v₁ hv₁)
      _ = ∑ ξ ∈ ((publicFiber (beforeSigning P) v).filter fun ξ => publicData d₁ ξ ∈ S),
            recW P :=
          Finset.sum_fiberwise_of_maps_to (fun ξ hξ => (Finset.mem_filter.1 hξ).2) _
      _ ≤ sumW P (publicFiber (beforeSigning P) v) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc ∑ ξ ∈ T, recW P * E (run (P.stB A pk m₁ st
          (some (encode (fun k => ξ.word k (d₁ k)) η₁)))
          (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g
      = ∑ v₁ ∈ S, ∑ ξ ∈ T with publicData d₁ ξ = v₁, recW P * E (run (P.stB A pk m₁ st
          (some (encode (fun k => ξ.word k (d₁ k)) η₁)))
          (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g := hregroup _
    _ ≤ ∑ v₁ ∈ S, κ * sumW P (publicFiber d₁ v₁) * b' := Finset.sum_le_sum hfiber
    _ = κ * (∑ v₁ ∈ S, sumW P (publicFiber d₁ v₁)) * b' := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ κ * sumW P (publicFiber (beforeSigning P) v) * b' :=
        mul_le_mul' (mul_le_mul' le_rfl hsumW) le_rfl

/-! ## The first-stage potential -/

/-- The records with public data `v` before signing. -/
def fiber₀ (v : PublicData P) : Finset (Record P) := publicFiber (beforeSigning P) v

/-- The row-potential term, `θ ψ`. -/
def encTerm (c : Cache) : ℝ≥0∞ :=
  ENNReal.ofReal (RowPot.Row.θ * @RowPot.psi ⟨P⟩ c)

/-- The first-stage potential of the records `T`. -/
def ΦA (v : PublicData P) (T : Finset (Record P)) (c : Cache) : ℝ≥0∞ :=
  hiddenHitPotential (beforeSigning P) T c +
    ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
    sumW P (P.fiber₀ v) * P.encTerm c

/-- The budget invariant of the index potential. -/
def Inv (c : Cache) (b : ℕ) : Prop := 2 * P.encCount c + b ≤ 2 ^ 127

/-- The first-stage invariant. -/
def InvA (T : Finset (Record P)) (c : Cache) (b : ℕ) : Prop :=
  (∀ ξ ∈ T, Cache.Sub (exposedCache (beforeSigning P) ξ) c) ∧ P.Inv c b

theorem one_le_queryCost (q : Query) : 1 ≤ queryCost (.inr q) := by
  unfold queryCost blockCost
  exact le_max_left _ _

theorem Inv_fresh : ∀ c b q, P.Inv c b → c q = none → queryCost (.inr q) ≤ b →
    ∀ u, P.Inv (c.cacheQuery q u) (b - queryCost (.inr q)) := by
  intro c b q hI _ hcost u
  unfold Inv at hI ⊢
  have h1 := P.encCount_cacheQuery_le c q u
  by_cases he : ∃ v, q = P.encQuery v
  · obtain ⟨v, rfl⟩ := he
    have h2 : queryCost (.inr (P.encQuery v)) = 2 := by
      norm_num [encQuery, queryCost, blockCost, blockBits]
    omega
  · have hne : ∀ v, q ≠ P.encQuery v := fun v hv => he ⟨v, hv⟩
    rw [P.encCount_cacheQuery_of_ne c hne u]
    omega

theorem Inv_cached : ∀ c b q, P.Inv c b → (c q).isSome → queryCost (.inr q) ≤ b →
    P.Inv c (b - queryCost (.inr q)) := by
  intro c b q hI _ _
  unfold Inv at hI ⊢
  omega

theorem InvA_fresh (T : Finset (Record P)) : ∀ c b q, P.InvA T c b → c q = none →
    queryCost (.inr q) ≤ b → ∀ u, P.InvA T (c.cacheQuery q u) (b - queryCost (.inr q)) := by
  intro c b q hI hq hcost u
  exact ⟨fun ξ hξ => (hI.1 ξ hξ).trans (Cache.sub_cacheQuery_of_none hq u),
    P.Inv_fresh c b q hI.2 hq hcost u⟩

theorem InvA_cached (T : Finset (Record P)) : ∀ c b q, P.InvA T c b → (c q).isSome →
    queryCost (.inr q) ≤ b → P.InvA T c (b - queryCost (.inr q)) := by
  intro c b q hI hq hcost
  exact ⟨hI.1, P.Inv_cached c b q hI.2 hq hcost⟩

/-- The hypotheses of the row potential. -/
theorem rowHyp (hP : P.Hyp) : @RowPot.RowHyp ⟨P⟩ := by
  letI : RowPot.RowCtx := ⟨P⟩
  refine ⟨by rw [RowPot.nonceBits_eq, RowPot.idxBits_eq],
    by rw [RowPot.idxBits_eq]; unfold hashBits; omega, ?_, ?_, ?_⟩
  · show 2 ≤ P.validSet.card
    rw [P.card_validSet]
    have := hP.numValid_ge
    omega
  · show 2 * P.validSet.card ≤ 2 ^ RowPot.idxBits
    rw [P.card_validSet, RowPot.idxBits_eq]
    exact hP.numValid_le
  · show 24 * trials ≤ 2 ^ RowPot.idxBits
    rw [RowPot.idxBits_eq]
    unfold trials
    norm_num

theorem two_encCount_le {c : Cache} {b : ℕ} (h : P.Inv c b) :
    2 * P.encCount c ≤ 2 ^ RowPot.idxBits := by
  unfold Inv at h
  rw [RowPot.idxBits_eq]
  omega

theorem encTerm_cacheQuery_of_ne (c : Cache) {q : Query} (hq : ∀ u, q ≠ P.encQuery u)
    (w : BitVec hashBits) : P.encTerm (c.cacheQuery q w) = P.encTerm c := by
  letI : RowPot.RowCtx := ⟨P⟩
  unfold encTerm
  rw [RowPot.psi_of_ne hq]

theorem encTerm_charge (hP : P.Hyp) {c : Cache} {b : ℕ} (hI : P.Inv c b) (u₀ : EncInput)
    (hq : c (P.encQuery u₀) = none) :
    ∑ w, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * P.encTerm (c.cacheQuery (P.encQuery u₀) w) ≤
      P.encTerm c + κ * 2 := by
  letI : RowPot.RowCtx := ⟨P⟩
  obtain ⟨m₀, η₀, rfl⟩ := exists_append u₀
  have h := RowPot.psi_charge (P.rowHyp hP) (P.two_encCount_le hI) hq
  unfold encTerm
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [RowPot.idxBits_eq, κ_eq, mul_comm]

theorem psi_zero_of_noEnc (c : Cache) (hc : ∀ u, c (P.encQuery u) = none) :
    P.encTerm c = 0 := by
  letI : RowPot.RowCtx := ⟨P⟩
  unfold encTerm
  rw [RowPot.psi_noEnc hc, mul_zero, ENNReal.ofReal_zero]

theorem avg_finset_sum {ι : Type} (S : Finset ι) (f : ι → BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ∑ ξ ∈ S, f ξ u =
      ∑ ξ ∈ S, ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f ξ u := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem spr_part_charge (c : Cache) (q : Query) (hq : c q = none) (T : Finset (Record P)) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) (c.cacheQuery q u)) ≤
      ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
        sumW P T * (3 * (rate * queryCost (.inr q))) := by
  rw [avg_finset_sum, sumW, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [avg_mul', ← mul_add]
  exact mul_le_mul' le_rfl ((ind_target_charge _ c q hq).trans
    (add_le_add le_rfl (secondPreimage_charge ξ q)))

theorem spr_part_enc (hP : P.Hyp) (c : Cache) (u₀ : EncInput) (T : Finset (Record P)) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, recW P *
          ind (TargetHit (secondPreimageTargets P ξ) (c.cacheQuery (P.encQuery u₀) u)) =
      ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) := by
  have he : ∀ u, ∑ ξ ∈ T, recW P *
      ind (TargetHit (secondPreimageTargets P ξ) (c.cacheQuery (P.encQuery u₀) u)) =
      ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) := fun u =>
    Finset.sum_congr rfl fun ξ _ => by
      rw [ind_congr (targetHit_cacheQuery_of_empty _ c _ u (P.spr_enc hP ξ u₀))]
  simp only [he]
  exact sum_inv_card_mul _

theorem ΦA_charge (hP : P.Hyp) (v : PublicData P) (T : Finset (Record P))
    (hT : T ⊆ P.fiber₀ v) : ∀ c b q, P.InvA T c b → c q = none →
    queryCost (.inr q) ≤ b →
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * P.ΦA v T (c.cacheQuery q u) ≤
      P.ΦA v T c + κ * sumW P (P.fiber₀ v) * queryCost (.inr q) := by
  intro c b q hI hq _
  unfold ΦA
  rw [avg_add', avg_add', avg_mul']
  by_cases henc : ∃ u₀, q = P.encQuery u₀
  · obtain ⟨u₀, rfl⟩ := henc
    have h1 := P.hiddenHit_charge_enc hP (beforeSigning P) T c u₀
    have h2 := P.spr_part_enc hP c u₀ T
    have h3 := P.encTerm_charge hP hI.2 u₀ hq
    have hcost : (2 : ℝ≥0∞) = queryCost (.inr (P.encQuery u₀)) :=
      two_le_queryCost_896 (by unfold Params.encQuery; rfl)
    calc _ ≤ hiddenHitPotential (beforeSigning P) T c +
          ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
          sumW P (P.fiber₀ v) * (P.encTerm c + κ * 2) :=
          add_le_add (add_le_add h1 (le_of_eq h2)) (mul_le_mul' le_rfl h3)
      _ = _ := by rw [← hcost]; ring
  · have hne : ∀ u, q ≠ P.encQuery u := fun u h => henc ⟨u, h⟩
    have h1 := P.hiddenHit_charge hP beforeSigning_valid v T hT c q
    have h2 := P.spr_part_charge c q hq T
    have h3 : ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * P.encTerm (c.cacheQuery q u) =
        P.encTerm c := by
      simp only [P.encTerm_cacheQuery_of_ne c hne]
      exact sum_inv_card_mul _
    have hs : sumW P T ≤ sumW P (P.fiber₀ v) := sumW_mono hT
    calc _ ≤ (hiddenHitPotential (beforeSigning P) T c +
            rate * sumW P (publicFiber (beforeSigning P) v) * queryCost (.inr q)) +
          (∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
            sumW P (P.fiber₀ v) * (3 * (rate * queryCost (.inr q)))) +
          sumW P (P.fiber₀ v) * P.encTerm c :=
          add_le_add (add_le_add h1 (h2.trans (add_le_add le_rfl (mul_le_mul' hs le_rfl))))
            (mul_le_mul' le_rfl (le_of_eq h3))
      _ = (hiddenHitPotential (beforeSigning P) T c +
          ∑ ξ ∈ T, recW P * ind (TargetHit (secondPreimageTargets P ξ) c) +
          sumW P (P.fiber₀ v) * P.encTerm c) +
          (rate * sumW P (P.fiber₀ v) * queryCost (.inr q) +
            sumW P (P.fiber₀ v) * (3 * (rate * queryCost (.inr q)))) := by
          unfold fiber₀
          ring
      _ ≤ _ := add_le_add le_rfl (rate_quad_le _ _)

theorem ΦA_initial (hP : P.Hyp) (v : PublicData P) (T : Finset (Record P))
    (hT : T ⊆ P.fiber₀ v) (hG : ∀ ξ ∈ T, ξ.Good) (ζ₀ : Record P) (hζ₀ : ζ₀ ∈ P.fiber₀ v) :
    P.ΦA v T (exposedCache (beforeSigning P) ζ₀) = 0 := by
  have hdata : ∀ ξ ∈ P.fiber₀ v,
      publicData (beforeSigning P) ξ = publicData (beforeSigning P) ζ₀ :=
    fun ξ hξ => ((mem_publicFiber _ _ _).mp hξ).trans ((mem_publicFiber _ _ _).mp hζ₀).symm
  have hexp : ∀ ξ ∈ P.fiber₀ v,
      exposedCache (beforeSigning P) ζ₀ = exposedCache (beforeSigning P) ξ :=
    fun ξ hξ => (exposedCache_data_eq hP beforeSigning_valid ξ ζ₀ (hdata ξ hξ)).symm
  unfold ΦA
  rw [hiddenHitPotential_zero _ _ _ fun ξ hξ => by
      rw [hexp ξ (hT hξ)]; exact exposure_disjoint _ ξ,
    P.psi_zero_of_noEnc _ fun u => P.exposedCache_enc hP _ ζ₀ u, mul_zero, zero_add, add_zero]
  refine Finset.sum_eq_zero fun ξ hξ => ?_
  rw [hexp ξ (hT hξ)]
  have : ¬ TargetHit (secondPreimageTargets P ξ) (exposedCache (beforeSigning P) ξ) := by
    rintro ⟨q, u, hq, hu⟩
    obtain ⟨a, -, hv, rfl, rfl⟩ := (exposedCache_some_iff hP _ ξ q u).mp hq
    exact not_mem_extraTargets_honest hP (hG ξ hξ) a (secondPreimageTargets_query hP ξ a hv hu)
  rw [ind_not this, mul_zero]

theorem encCount_noEnc (c : Cache) (hc : ∀ u, c (P.encQuery u) = none) : P.encCount c = 0 := by
  unfold encCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _
  rw [hc u]
  simp

/-! ## The continuation after the first stage -/

/-- The quantity bounded after the first stage, over the records `T`. -/
def FA (pk : PublicKey) (T : Finset (Record P)) (x : Message × A.State) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ T, recW P * (if Cache.Hits d (hiddenCache (beforeSigning P) ξ) then 1 else
    E (run (P.rest₂ A pk ξ.sk x) (Cache.extend d (hiddenCache (beforeSigning P) ξ))) g)

theorem E_le_one' {α : Type} (p : ProbComp α) {f : α → ℝ≥0∞} (hf : ∀ x, f x ≤ 1) : E p f ≤ 1 :=
  E_le_one p hf

theorem psi_dom' (hP : P.Hyp) {d : Cache} {b : ℕ} (hI : P.Inv d b) (m : EMessage) (c : ℕ)
    (hc1 : (P.rowFresh d m).card ≤ c + trials) (hc2 : c ≤ (P.rowFresh d m).card) :
    ((P.rowBad d m).card : ℝ≥0∞) + c * (((P.V d).card : ℝ≥0∞) / 2 ^ 127) ≤
      P.encTerm d * ((P.rowAcc d m).card + c * ((P.numValid : ℝ≥0∞) / 2 ^ 127)) := by
  letI : RowPot.RowCtx := ⟨P⟩
  have h := RowPot.psi_dom (P.rowHyp hP) (P.two_encCount_le hI) m c hc1 hc2
  rw [RowPot.idxBits_eq, RowPot.numValid_eq] at h
  exact h

theorem stageA_cont (hP : P.Hyp) (pk : PublicKey) (v : PublicData P) (T₀ : Finset (Record P))
    (hT₀ : T₀ ⊆ P.fiber₀ v) (hG : ∀ ξ ∈ T₀, ξ.Good)
    (hpk : ∀ ξ ∈ P.fiber₀ v, ξ.pk = pk) (x : Message × A.State) (d : Cache) (b' : ℕ)
    (hI : P.InvA T₀ d b') (hB : ∀ ξ ∈ T₀, CostAtMost (P.rest₂ A pk ξ.sk x) b') :
    P.FA A pk T₀ x d ≤ P.ΦA v T₀ d + κ * sumW P (P.fiber₀ v) * b' := by
  rcases T₀.eq_empty_or_nonempty with hT0 | ⟨ξ₀, hξ₀⟩
  · unfold FA
    rw [hT0, Finset.sum_empty]
    exact bot_le
  haveI hne : Nonempty {ξ // ξ ∈ T₀} := ⟨⟨ξ₀, hξ₀⟩⟩
  set M := emsg x.1 pk with hM
  set T := T₀.filter (fun ξ => ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ) ∧
    ¬ TargetHit (secondPreimageTargets P ξ) d) with hTdef
  have hTT : T ⊆ T₀ := Finset.filter_subset _ _
  have hT : T ⊆ P.fiber₀ v := hTT.trans hT₀
  have hTG : ∀ ξ ∈ T, ξ.Good := fun ξ hξ => hG ξ (hTT hξ)
  have hTd : ∀ ξ ∈ T, Cache.Sub (exposedCache (beforeSigning P) ξ) d ∧
      ¬ Cache.Hits d (hiddenCache (beforeSigning P) ξ) ∧
      ¬ TargetHit (secondPreimageTargets P ξ) d := by
    intro ξ hξ
    have h := (Finset.mem_filter.1 hξ).2
    exact ⟨hI.1 ξ (hTT hξ), h.1, h.2⟩
  set Fn : Option (Nonce × P.Idx) → Cache → ℝ≥0∞ := fun r d' => ∑ ξ ∈ T, recW P *
    E (run (P.stB A pk x.1 x.2 (P.sigOfIdx ξ.sk r))
      (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g with hFn
  -- Step 1: records hit in the first stage pay their indicator; the others sign.
  have hsplit : P.FA A pk T₀ x d ≤ hiddenHitPotential (beforeSigning P) T₀ d +
      ∑ ξ ∈ T₀, recW P * ind (TargetHit (secondPreimageTargets P ξ) d) +
      E (run (P.signIdx M) d) (fun p => Fn p.1 p.2) := by
    rw [hFn, E_weighted_sum, hTdef, Finset.sum_filter]
    unfold FA hiddenHitPotential
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
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
        rw [P.E_rest₂_extend A hP pk ξ (hpk ξ (hT₀ hξ)) x d]
  -- Step 2: signing as one disjoint case split.
  have hB' : ∀ j : {ξ // ξ ∈ T₀},
      CostAtMost (P.signIdx M >>= fun r => P.stB A pk x.1 x.2 (P.sigOfIdx j.1.sk r)) b' := by
    intro j
    have h := hB j.1 j.2
    rw [P.rest₂_eq_signIdx A pk j.1 (hpk j.1 (hT₀ j.2))] at h
    exact h
  have hΦ : P.EncInvariant (fun _ : Cache => (0 : ℝ≥0∞)) := fun _ _ _ => rfl
  have hsig := P.signRho_bound P.numValid_le' (by unfold hashBits; omega) M d
    (fun (j : {ξ // ξ ∈ T₀}) r => P.stB A pk x.1 x.2 (P.sigOfIdx j.1.sk r)) Fn
    (fun _ => 0) hΦ (κ * sumW P (P.fiber₀ v)) (sumW P T) (P.encTerm d) P.Inv
    P.Inv_fresh P.Inv_cached ?_ (fun c hc1 hc2 => P.psi_dom' hP hI.2 M c hc1 hc2) hI.2 hB'
  · -- assemble
    refine hsplit.trans ?_
    unfold ΦA
    have hsT : sumW P T ≤ sumW P (P.fiber₀ v) := sumW_mono hT
    calc hiddenHitPotential (beforeSigning P) T₀ d +
          ∑ ξ ∈ T₀, recW P * ind (TargetHit (secondPreimageTargets P ξ) d) +
          E (run (P.signIdx M) d) (fun p => Fn p.1 p.2)
        ≤ hiddenHitPotential (beforeSigning P) T₀ d +
          ∑ ξ ∈ T₀, recW P * ind (TargetHit (secondPreimageTargets P ξ) d) +
          (0 + sumW P T * P.encTerm d + κ * sumW P (P.fiber₀ v) * b') :=
          add_le_add le_rfl hsig
      _ ≤ hiddenHitPotential (beforeSigning P) T₀ d +
          ∑ ξ ∈ T₀, recW P * ind (TargetHit (secondPreimageTargets P ξ) d) +
          (0 + sumW P (P.fiber₀ v) * P.encTerm d + κ * sumW P (P.fiber₀ v) * b') := by
          gcongr
      _ = _ := by ring
  · -- the second stage, for every outcome of signing
    intro r d' b'' hext hI' hBr
    rcases r with _ | ⟨η₁, i₁⟩
    · have hb0 : CostAtMost (P.stB A pk x.1 x.2 none) b'' := hBr ⟨ξ₀, hξ₀⟩
      have h := P.stageB_none A hP pk x.1 x.2 v T hT hTG (fun ξ hξ => hpk ξ (hT hξ)) d d'
        (P.encExt_of_signExt hext) hTd b'' hb0
      refine le_trans ?_ (le_trans h (le_add_self))
      exact le_of_eq rfl
    · by_cases hpre : P.IdxPre d (M ++ η₁) i₁.val
      · have hone : Fn (some (η₁, i₁)) d' ≤ sumW P T := by
          rw [hFn, sumW]
          exact Finset.sum_le_sum fun ξ _ =>
            le_trans (mul_le_mul' le_rfl (E_le_one _ g_le_one)) (le_of_eq (mul_one _))
        refine hone.trans ?_
        rw [if_pos ⟨η₁, i₁, rfl, hpre⟩, mul_one, zero_add]
        exact le_self_add
      · have hBξ : ∀ ξ ∈ T, CostAtMost (P.stB A pk x.1 x.2
            (some (encode (fun k => ξ.word k (afterSigning P (idxWord i₁.val) k)) η₁))) b'' := by
          intro ξ hξ
          have h := hBr ⟨ξ, hTT hξ⟩
          rwa [P.sigOfIdx_record hP] at h
        have h := P.stageB_some A hP pk x.1 x.2 v T hT hTG (fun ξ hξ => hpk ξ (hT hξ)) d d' η₁ i₁
          hext hpre hTd b'' hBξ
        have hFn' : Fn (some (η₁, i₁)) d' = ∑ ξ ∈ T, recW P * E (run (P.stB A pk x.1 x.2
            (some (encode (fun k => ξ.word k (afterSigning P (idxWord i₁.val) k)) η₁)))
            (Cache.extend d' (hiddenCache (beforeSigning P) ξ))) g := by
          rw [hFn]
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [P.sigOfIdx_record hP]
        rw [hFn']
        refine h.trans ?_
        exact le_add_self

/-! ## The first stage -/

theorem stageA_master (hP : P.Hyp) (v : PublicData P) (T : Finset (Record P))
    (hT : T ⊆ P.fiber₀ v) (hG : ∀ ξ ∈ T, ξ.Good) (ζ₀ : Record P) (hζ₀ : ζ₀ ∈ P.fiber₀ v)
    (b : ℕ) (hb : b ≤ 2 ^ 127)
    (hB : ∀ ξ ∈ T, CostAtMost (A.choose ζ₀.pk >>= P.rest₂ A ζ₀.pk ξ.sk) b) :
    E (run (A.choose ζ₀.pk) (exposedCache (beforeSigning P) ζ₀))
        (fun p => P.FA A ζ₀.pk T p.1 p.2) ≤ κ * sumW P (P.fiber₀ v) * b := by
  rcases T.eq_empty_or_nonempty with hT0 | ⟨ξ₁, hξ₁⟩
  · have h0 : (fun p : (Message × A.State) × Cache => P.FA A ζ₀.pk T p.1 p.2) = fun _ => 0 := by
      funext p
      unfold FA
      rw [hT0, Finset.sum_empty]
    rw [h0]
    refine le_trans (le_of_eq ?_) bot_le
    exact expectedValue_const (by simp) 0 |>.trans rfl
  haveI hne : Nonempty {ξ // ξ ∈ T} := ⟨⟨ξ₁, hξ₁⟩⟩
  have hdata : ∀ ξ ∈ P.fiber₀ v,
      publicData (beforeSigning P) ξ = publicData (beforeSigning P) ζ₀ :=
    fun ξ hξ => ((mem_publicFiber _ _ _).mp hξ).trans ((mem_publicFiber _ _ _).mp hζ₀).symm
  have hpk : ∀ ξ ∈ P.fiber₀ v, ξ.pk = ζ₀.pk :=
    fun ξ hξ => data_pk_eq _ ξ ζ₀ (hdata ξ hξ)
  have hF : ∀ (x : Message × A.State) (d : Cache) (b' : ℕ), P.InvA T d b' →
      (∀ j : {ξ // ξ ∈ T}, CostAtMost (P.rest₂ A ζ₀.pk j.1.sk x) b') →
      P.FA A ζ₀.pk T x d ≤ P.ΦA v T d + κ * sumW P (P.fiber₀ v) * b' :=
    fun x d b' hI hB' => P.stageA_cont A hP ζ₀.pk v T hT hG hpk x d b' hI
      fun ξ hξ => hB' ⟨ξ, hξ⟩
  have hI0 : P.InvA T (exposedCache (beforeSigning P) ζ₀) b := by
    refine ⟨fun ξ hξ => ?_, ?_⟩
    · rw [exposedCache_data_eq hP beforeSigning_valid ζ₀ ξ (hdata ξ (hT hξ)).symm]
      exact Cache.Sub.refl _
    · unfold Inv
      rw [P.encCount_noEnc _ fun u => P.exposedCache_enc hP _ ζ₀ u, mul_zero, zero_add]
      exact hb
  have h := master_family (α := Message × A.State) (β := Bool) (J := {ξ // ξ ∈ T})
    (κ * sumW P (P.fiber₀ v)) (P.ΦA v T) (P.InvA T) (P.InvA_fresh T) (P.InvA_cached T)
    (P.ΦA_charge hP v T hT) (A.choose ζ₀.pk) (fun j => P.rest₂ A ζ₀.pk j.1.sk)
    (fun x d => P.FA A ζ₀.pk T x d) hF (exposedCache (beforeSigning P) ζ₀) b hI0
    (fun j => hB j.1 j.2)
  rw [P.ΦA_initial hP v T hT hG ζ₀ hζ₀, zero_add] at h
  exact h

end Params

end OptimalOTS.LeanIsaBaseline.Layer
