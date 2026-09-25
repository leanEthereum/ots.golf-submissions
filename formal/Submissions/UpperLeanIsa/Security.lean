import Submissions.UpperLeanIsa.StageA
import Submissions.UpperLeanIsa.CostPrefix

/-!
# Strong unforgeability of a layer scheme

For every adversary `A` whose experiment costs at most `B ≤ 2 ^ 127` compressions on every path,

```
probTrue (experiment P.scheme A) ≤ 2 ^ -500 + κ (B - keygenCost) < B / 2 ^ 127,
```

where the strict inequality uses the positive key-generation cost `keygenCost`, a fixed prefix of
every experiment (`CostPrefix`); for larger budgets the bound is trivial.

The proof: key generation is a uniform record (`E_run_keygen`); the first attacker stage is
coupled to a run in which only the exposed part of the keygen cache is present (`iub`); records
are regrouped by their public data before signing (`regroup`); each group is bounded by
`stageA_master` (the first stage, rarest-cut signing, and the second stage) by
`2 ^ -500 + K(B)` for a tier schedule of the codec (`Hyp.tier`), and `K(B) ≤ κ B`
(`Kb_le`); the group weights sum to one (`sum_sumW_fiber₀`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.encQuery
  publicFiber finiteFiber hiddenCache exposedCache queryLocation Record.query

namespace Params

variable (P : Params) (A : OracleAlgorithm.Adversary)

/-! ## Key generation and the first stage -/

theorem recW_ne_zero : recW P ≠ 0 := by
  unfold recW
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

theorem sum_recW : ∑ _ξ : Record P, recW P = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold recW
  have h : (Fintype.card (Record P) : ℝ≥0∞) ≠ 0 := by
    have : Fintype.card (Record P) ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast this
  exact ENNReal.mul_inv_cancel h (ENNReal.natCast_ne_top _)

/-- Every record is a possible outcome of key generation. -/
theorem mem_support_run_keygen (hP : P.Hyp) (ξ : Record P) :
    ((ξ.pk, ξ.sk), ξ.cache) ∈ support (run P.keygen ∅) := by
  by_contra hns
  have h0 : E (run P.keygen ∅) (fun p => ind (p = ((ξ.pk, ξ.sk), ξ.cache))) = 0 := by
    refine le_antisymm (expectedValue_le_of_support fun p hp => ?_) bot_le
    have hne : p ≠ ((ξ.pk, ξ.sk), ξ.cache) := by
      intro he
      apply hns
      rw [← he]
      exact hp
    exact le_of_eq (ind_not hne)
  rw [E_run_keygen hP] at h0
  have hall := Iff.mp (Fintype.sum_eq_zero_iff_of_nonneg (fun _ => bot_le)) h0
  have h2 : recW P * ind (((ξ.pk, ξ.sk), ξ.cache) = ((ξ.pk, ξ.sk), ξ.cache)) = 0 :=
    congrFun hall ξ
  rw [ind_of rfl, mul_one] at h2
  exact P.recW_ne_zero h2

theorem costAtMost_rest (hP : P.Hyp) {B : ℕ}
    (h : CostAtMost (OracleAlgorithm.experiment P.scheme A) B) :
    ∀ ξ : Record P, CostAtMost (P.rest A (ξ.pk, ξ.sk)) (B - P.keygenCost) := by
  intro ξ
  rw [experiment_eq] at h
  exact (P.spends_keygen.run_budget (P.rest A) ∅ _ (P.mem_support_run_keygen hP ξ) h).2

theorem keygenCost_le_of_experiment (hP : P.Hyp) {B : ℕ}
    (h : CostAtMost (OracleAlgorithm.experiment P.scheme A) B) : P.keygenCost ≤ B := by
  rw [experiment_eq] at h
  exact (P.spends_keygen.run_budget (P.rest A) ∅ _
    (P.mem_support_run_keygen hP ((fun _ => 0), (fun _ => 0))) h).1

theorem E_run_experiment (hP : P.Hyp) :
    E (run (OracleAlgorithm.experiment P.scheme A) ∅) g =
      ∑ ξ : Record P, recW P * E (run (P.rest A (ξ.pk, ξ.sk)) ξ.cache) g := by
  rw [experiment_eq, run_bind, E_bind]
  exact E_run_keygen hP _

theorem stageA_iub (hP : P.Hyp) (ξ : Record P) :
    E (run (P.rest A (ξ.pk, ξ.sk)) ξ.cache) g ≤
      E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (fun p =>
        if Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ) then 1 else
          E (run (P.rest₂ A ξ.pk ξ.sk p.1)
            (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g) := by
  unfold rest
  rw [run_bind, E_bind, ← exposure_partition (beforeSigning P) ξ]
  exact iub (A.choose ξ.pk) (hiddenCache (beforeSigning P) ξ)
    (fun p => E (run (P.rest₂ A ξ.pk ξ.sk p.1) p.2) g) (fun _ => E_le_one _ g_le_one)
    (exposedCache (beforeSigning P) ξ) (exposure_disjoint (beforeSigning P) ξ)

/-! ## Regrouping by public data before signing -/

local instance instDecEqPublicData : DecidableEq (PublicData P) := Classical.decEq _

local instance instDecEqRecord : DecidableEq (Record P) := Classical.decEq _

/-- The public data before signing of all records. -/
def dataSet₀ : Finset (PublicData P) := Finset.univ.image (publicData (beforeSigning P))

theorem mem_dataSet₀ (ξ : Record P) : publicData (beforeSigning P) ξ ∈ P.dataSet₀ := by
  unfold dataSet₀
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨ξ, rfl⟩

theorem exists_of_mem_dataSet₀ {v : PublicData P} (hv : v ∈ P.dataSet₀) :
    ∃ ξ, publicData (beforeSigning P) ξ = v := by
  unfold dataSet₀ at hv
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
  exact hv

theorem fiber₀_eq_filter (v : PublicData P) :
    (Finset.univ.filter fun ξ : Record P => publicData (beforeSigning P) ξ = v) = P.fiber₀ v := by
  ext ξ
  unfold fiber₀
  rw [mem_publicFiber]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] dataSet₀

theorem nonempty_record : Nonempty (Record P) := ⟨((fun _ => 0), (fun _ => 0))⟩

/-- A representative of the records with public data `v`. -/
def rep (v : PublicData P) : Record P :=
  @Classical.epsilon (Record P) P.nonempty_record (fun ξ => ξ ∈ P.fiber₀ v)

theorem rep_mem {v : PublicData P} (hv : v ∈ P.dataSet₀) : P.rep v ∈ P.fiber₀ v := by
  obtain ⟨ξ, hξ⟩ := P.exists_of_mem_dataSet₀ hv
  have hex : ∃ ζ, ζ ∈ P.fiber₀ v := ⟨ξ, (mem_publicFiber _ v ξ).2 hξ⟩
  unfold rep
  exact Classical.epsilon_spec hex

theorem regroup (hP : P.Hyp) (G : Record P → (Message × A.State) × Cache → ℝ≥0∞) :
    ∑ ξ : Record P, recW P * E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) =
      ∑ v ∈ P.dataSet₀,
        E (run (A.choose (P.rep v).pk) (exposedCache (beforeSigning P) (P.rep v)))
          (fun p => ∑ ξ ∈ P.fiber₀ v, recW P * G ξ p) := by
  symm
  calc ∑ v ∈ P.dataSet₀,
        E (run (A.choose (P.rep v).pk) (exposedCache (beforeSigning P) (P.rep v)))
          (fun p => ∑ ξ ∈ P.fiber₀ v, recW P * G ξ p)
      = ∑ v ∈ P.dataSet₀, ∑ ξ ∈ P.fiber₀ v,
          recW P * E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [E_weighted_sum]
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        have hd : publicData (beforeSigning P) ξ = publicData (beforeSigning P) (P.rep v) :=
          ((mem_publicFiber _ _ _).1 hξ).trans ((mem_publicFiber _ _ _).1 (P.rep_mem hv)).symm
        rw [data_pk_eq _ ξ (P.rep v) hd,
          exposedCache_data_eq hP beforeSigning_valid ξ (P.rep v) hd]
    _ = ∑ v ∈ P.dataSet₀, ∑ ξ ∈ Finset.univ.filter
          (fun ξ : Record P => publicData (beforeSigning P) ξ = v),
            recW P * E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [P.fiber₀_eq_filter]
    _ = ∑ ξ : Record P, recW P *
          E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (G ξ) :=
        Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := P.dataSet₀)
          (g := publicData (beforeSigning P)) (fun ξ _ => P.mem_dataSet₀ ξ) _

theorem sum_sumW_fiber₀ : ∑ v ∈ P.dataSet₀, sumW P (P.fiber₀ v) = 1 := by
  calc ∑ v ∈ P.dataSet₀, sumW P (P.fiber₀ v)
      = ∑ v ∈ P.dataSet₀, ∑ _ξ ∈ Finset.univ.filter
          (fun ξ : Record P => publicData (beforeSigning P) ξ = v), recW P := by
        refine Finset.sum_congr rfl fun v _ => ?_
        unfold sumW
        rw [P.fiber₀_eq_filter]
    _ = ∑ _ξ : Record P, recW P :=
        Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := P.dataSet₀)
          (g := publicData (beforeSigning P)) (fun ξ _ => P.mem_dataSet₀ ξ) _
    _ = 1 := P.sum_recW

/-! ## The bound -/

attribute [local irreducible] CostAtMost OracleAlgorithm.experiment Params.rest Params.rest₂
  Params.stB Params.keygen Params.verify

theorem main_bound_rest (hP : P.Hyp) {S : Tier.Sched} (hS : S.Valid) (hT : P.TierHyp S) {B : ℕ}
    (hB' : B ≤ 2 ^ 127)
    (hrest : ∀ ξ : Record P, CostAtMost (A.choose ξ.pk >>= P.rest₂ A ξ.pk ξ.sk) B) :
    probTrue (OracleAlgorithm.experiment P.scheme A) ≤ (2 ^ 500 : ℝ≥0∞)⁻¹ + κ * B := by
  rw [probTrue_eq_E_run, show (fun p : Bool × Cache => if p.1 = true then (1 : ℝ≥0∞) else 0) = g
    from rfl, P.E_run_experiment A hP]
  calc ∑ ξ : Record P, recW P * E (run (P.rest A (ξ.pk, ξ.sk)) ξ.cache) g
      ≤ ∑ ξ : Record P, recW P *
          E (run (A.choose ξ.pk) (exposedCache (beforeSigning P) ξ)) (fun p =>
            if Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ) then 1 else
              E (run (P.rest₂ A ξ.pk ξ.sk p.1)
                (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g) :=
        Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl (P.stageA_iub A hP ξ)
    _ = ∑ v ∈ P.dataSet₀,
          E (run (A.choose (P.rep v).pk) (exposedCache (beforeSigning P) (P.rep v)))
            (fun p => ∑ ξ ∈ P.fiber₀ v, recW P *
              (if Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ) then 1 else
                E (run (P.rest₂ A ξ.pk ξ.sk p.1)
                  (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g)) :=
        P.regroup A hP (fun ξ p => if Cache.Hits p.2 (hiddenCache (beforeSigning P) ξ) then 1 else
          E (run (P.rest₂ A ξ.pk ξ.sk p.1)
            (Cache.extend p.2 (hiddenCache (beforeSigning P) ξ))) g)
    _ = ∑ v ∈ P.dataSet₀,
          E (run (A.choose (P.rep v).pk) (exposedCache (beforeSigning P) (P.rep v)))
            (fun p => P.FA A (P.rep v).pk v p.1 p.2) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        refine congrArg _ (funext fun p => ?_)
        unfold FA
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        have hd : publicData (beforeSigning P) ξ = publicData (beforeSigning P) (P.rep v) :=
          ((mem_publicFiber _ _ _).1 hξ).trans ((mem_publicFiber _ _ _).1 (P.rep_mem hv)).symm
        rw [data_pk_eq _ ξ (P.rep v) hd]
    _ ≤ ∑ v ∈ P.dataSet₀, sumW P (P.fiber₀ v) * ((2 ^ 500 : ℝ≥0∞)⁻¹ + S.Kb B) :=
        Finset.sum_le_sum fun v hv =>
          P.stageA_master A hP hS hT v (P.rep v) (P.rep_mem hv) B hB' fun ξ hξ => by
            have hd : publicData (beforeSigning P) ξ = publicData (beforeSigning P) (P.rep v) :=
              ((mem_publicFiber _ _ _).1 hξ).trans
                ((mem_publicFiber _ _ _).1 (P.rep_mem hv)).symm
            have h := hrest ξ
            rw [data_pk_eq _ ξ (P.rep v) hd] at h
            exact h
    _ = (2 ^ 500 : ℝ≥0∞)⁻¹ + S.Kb B := by
        rw [← Finset.sum_mul, P.sum_sumW_fiber₀, one_mul]
    _ ≤ (2 ^ 500 : ℝ≥0∞)⁻¹ + κ * B := by
        rw [κ_eq]
        exact add_le_add le_rfl (S.Kb_le hS hB')

theorem main_bound (hP : P.Hyp) {B : ℕ}
    (hB : CostAtMost (OracleAlgorithm.experiment P.scheme A) B) (hB' : B ≤ 2 ^ 127) :
    probTrue (OracleAlgorithm.experiment P.scheme A) ≤
      (2 ^ 500 : ℝ≥0∞)⁻¹ + κ * (B - P.keygenCost : ℕ) := by
  obtain ⟨S, hS, hT⟩ := hP.tier
  apply P.main_bound_rest A hP hS hT ((Nat.sub_le B P.keygenCost).trans hB')
  intro ξ
  simpa only [rest] using P.costAtMost_rest A hP hB ξ

/-- The positive key-generation cost supplies the strictness at the 127-bit rate: its charge
`κ · keygenCost` exceeds the RowGood slack `2 ^ -500`. -/
theorem κ_mul_sub_lt {B : ℕ} (hKB : P.keygenCost ≤ B) :
    (2 ^ 500 : ℝ≥0∞)⁻¹ + κ * (B - P.keygenCost : ℕ) < (B : ℝ≥0∞) / 2 ^ securityBits := by
  have hsec : securityBits = 127 := rfl
  have hsplit : (B : ℝ≥0∞) / 2 ^ securityBits =
      κ * (B - P.keygenCost : ℕ) + κ * (P.keygenCost : ℝ≥0∞) := by
    rw [hsec, ENNReal.div_eq_inv_mul, ← κ_eq, ← mul_add]
    congr 1
    rw [← Nat.cast_add, Nat.sub_add_cancel hKB]
  rw [hsplit, add_comm]
  refine ENNReal.add_lt_add_left
    (ENNReal.mul_ne_top (by rw [κ_eq]; simp) (ENNReal.natCast_ne_top _)) ?_
  have hK : (1 : ℝ≥0∞) ≤ P.keygenCost := by exact_mod_cast P.keygenCost_pos
  calc (2 ^ 500 : ℝ≥0∞)⁻¹ < (2 ^ 127 : ℝ≥0∞)⁻¹ :=
        ENNReal.inv_lt_inv.2 (by
          exact_mod_cast (Nat.pow_lt_pow_right (by norm_num) (by norm_num) : (2 : ℕ) ^ 127 < 2 ^ 500))
    _ = κ * 1 := by rw [κ_eq, mul_one]
    _ ≤ κ * (P.keygenCost : ℝ≥0∞) := mul_le_mul' le_rfl hK

theorem one_lt_div {B : ℕ} (h : 2 ^ 127 < B) :
    (1 : ℝ≥0∞) < (B : ℝ≥0∞) / 2 ^ securityBits := by
  have hsec : securityBits = 127 := rfl
  rw [hsec, ENNReal.lt_div_iff_mul_lt (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
  exact_mod_cast h

/-- **Strong unforgeability** of a layer scheme. -/
theorem secure (hP : P.Hyp) : P.scheme.Secure := by
  intro A B hB
  by_cases hle : B ≤ 2 ^ 127
  · exact (P.main_bound A hP hB hle).trans_lt
      (P.κ_mul_sub_lt (P.keygenCost_le_of_experiment A hP hB))
  · exact (probOutput_le_one).trans_lt (one_lt_div (not_le.1 hle))

end Params

end OptimalOTS.LeanIsaBaseline.Layer
