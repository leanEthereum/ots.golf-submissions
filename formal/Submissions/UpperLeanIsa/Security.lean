import Submissions.UpperLeanIsa.Budget
import Submissions.UpperLeanIsa.KeygenBridge
import Submissions.UpperLeanIsa.StageA

/-!
# Strong unforgeability of the leanISA Winternitz candidate

For every adversary `A` whose experiment costs at most `B` compressions on every path,

```
probTrue (experiment scheme A) ≤ κ B = B / 2 ^ 128 < B / 2 ^ 127,
```

where the strict inequality uses `2 ≤ B` (the first chain query of key generation).

The proof: key generation is a uniform record (`E_run_keygen`); the first attacker stage is
coupled to a run in which only the exposed part of the keygen cache is present (`stageA_iub`);
records are regrouped by their public data before signing (`regroup`); each group is bounded by
`stageA_master`; the group weights sum to one (`sum_sumW_fiber₀`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- The linter `whnf`s the types of binders; a membership in a concrete finset of records would be
-- evaluated.
set_option linter.constructorNameAsVariable false

attribute [local irreducible] blockBits securityBits maxSignatureBits
attribute [local irreducible] keygenBudget signBudget verifyBudget
attribute [local irreducible] publicFiber finiteFiber hiddenCache queryLocation Record.query

local instance instDecEqRecordSecurity : DecidableEq Record := Classical.decEq Record

variable (A : OracleAlgorithm.Adversary)

/-! ## Budget after key generation -/

/-- Every record is a possible outcome of key generation. -/
theorem mem_support_run_keygen (ξ : Record) :
    ((ξ.publicKey, ξ.1), ξ.cache) ∈ support (run keygen ∅) := by
  by_contra hns
  have h0 : E (run keygen ∅) (fun p => ind (p = ((ξ.publicKey, ξ.1), ξ.cache))) = 0 := by
    refine le_antisymm (expectedValue_le_of_support fun p hp => ?_) zero_le
    have hne : p ≠ ((ξ.publicKey, ξ.1), ξ.cache) := by
      intro he
      apply hns
      rw [← he]
      exact hp
    exact le_of_eq (ind_not hne)
  rw [E_run_keygen] at h0
  have hall := Iff.mp (Fintype.sum_eq_zero_iff_of_nonneg (fun _ => zero_le)) h0
  have h2 : w * ind (((ξ.publicKey, ξ.1), ξ.cache) = ((ξ.publicKey, ξ.1), ξ.cache)) = 0 :=
    congrFun hall ξ
  rw [ind_of rfl, mul_one] at h2
  exact w_ne_zero_stg h2

/-- The budget of the experiment is a budget of the continuation after key generation, at every
record. -/
theorem costAtMost_rest {B : ℕ} (h : CostAtMost (OracleAlgorithm.experiment scheme A) B) :
    ∀ ξ : Record, CostAtMost (rest A (ξ.publicKey, ξ.1)) B := by
  intro ξ
  rw [experiment_eq] at h
  exact costAtMost_bind_run_support keygen (rest A) h ∅ _ (mem_support_run_keygen ξ)

/-! ## Stage A: identical until a hidden keygen point is queried -/

theorem stageA_iub (ξ : Record) :
    E (run (rest A (ξ.publicKey, ξ.1)) ξ.cache) g ≤
      E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (fun p =>
        if Cache.Hits p.2 (hiddenCache beforeSigning ξ) then 1 else
          E (run (rest₂ A ξ.publicKey ξ.1 p.1)
            (Cache.extend p.2 (hiddenCache beforeSigning ξ))) g) := by
  unfold rest
  rw [run_bind, E_bind, ← exposure_partition beforeSigning ξ]
  exact iub (A.choose ξ.publicKey) (hiddenCache beforeSigning ξ)
    (fun p => E (run (rest₂ A ξ.publicKey ξ.1 p.1) p.2) g) (fun _ => E_le_one _ g_le_one)
    (exposedCache beforeSigning ξ) (exposure_disjoint beforeSigning ξ)

/-- The experiment as a uniform average over records of the continuation after key
generation. -/
theorem E_run_experiment (g' : Bool × Cache → ℝ≥0∞) :
    E (run (OracleAlgorithm.experiment scheme A) ∅) g' =
      ∑ ξ : Record, w * E (run (rest A (ξ.publicKey, ξ.1)) ξ.cache) g' := by
  rw [experiment_eq, run_bind keygen (rest A) ∅, E_bind]
  exact E_run_keygen _

/-! ## Regrouping by public data before signing -/

attribute [local irreducible] fiber₀

theorem mem_fiber₀_sec (v : PublicData) (ξ : Record) :
    ξ ∈ fiber₀ v ↔ publicData beforeSigning ξ = v := by
  unfold fiber₀
  exact mem_publicFiber beforeSigning v ξ

theorem fiber₀_eq_filter_sec (v : PublicData) :
    (Finset.univ.filter fun ξ : Record => publicData beforeSigning ξ = v) = fiber₀ v := by
  ext ξ
  rw [mem_fiber₀_sec]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The public data before signing of all records. Kept opaque: a membership in it would
otherwise be evaluated by `whnf`. -/
def dataSet₀ : Finset PublicData := Finset.univ.image (publicData beforeSigning)

/-- Generic form, so that no membership in the concrete `Finset.univ : Finset Record` is ever
elaborated or unfolded. -/
theorem mem_image_univ_gen {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (a : α) :
    f a ∈ Finset.univ.image f :=
  Finset.mem_image_of_mem f (Finset.mem_univ a)

theorem exists_of_mem_image_univ_gen {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    {b : β} (h : b ∈ Finset.univ.image f) : ∃ a, f a = b := by
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
  exact ⟨a, ha⟩

theorem mem_dataSet₀ (ξ : Record) : publicData beforeSigning ξ ∈ dataSet₀ := by
  unfold dataSet₀
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨ξ, rfl⟩

theorem exists_of_mem_dataSet₀ {v : PublicData} (hv : v ∈ dataSet₀) :
    ∃ ξ, publicData beforeSigning ξ = v := by
  unfold dataSet₀ at hv
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
  exact hv

attribute [local irreducible] dataSet₀

theorem nonempty_record_sec : Nonempty Record := ⟨((fun _ => 0), (fun _ => 0))⟩

/-- A representative of the records with public data `v` (any record if there is none). -/
def rep (v : PublicData) : Record :=
  @Classical.epsilon Record nonempty_record_sec (fun ξ => ξ ∈ fiber₀ v)

theorem rep_mem {v : PublicData} (hv : v ∈ dataSet₀) : rep v ∈ fiber₀ v := by
  obtain ⟨ξ, hξ⟩ := exists_of_mem_dataSet₀ hv
  have hex : ∃ ζ, ζ ∈ fiber₀ v := ⟨ξ, (mem_fiber₀_sec v ξ).2 hξ⟩
  unfold rep
  exact Classical.epsilon_spec hex

theorem regroup (G : Record → (Message × A.State) × Cache → ℝ≥0∞) :
    ∑ ξ : Record, w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (G ξ) =
      ∑ v ∈ dataSet₀,
        E (run (A.choose (rep v).publicKey) (exposedCache beforeSigning (rep v)))
          (fun p => ∑ ξ ∈ fiber₀ v, w * G ξ p) := by
  symm
  calc ∑ v ∈ dataSet₀,
        E (run (A.choose (rep v).publicKey) (exposedCache beforeSigning (rep v)))
          (fun p => ∑ ξ ∈ fiber₀ v, w * G ξ p)
      = ∑ v ∈ dataSet₀, ∑ ξ ∈ fiber₀ v,
          w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (G ξ) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [E_weighted_sum]
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        have hd : publicData beforeSigning ξ = publicData beforeSigning (rep v) :=
          ((mem_fiber₀_sec v ξ).1 hξ).trans ((mem_fiber₀_sec v (rep v)).1 (rep_mem hv)).symm
        rw [publicKey_data_eq beforeSigning ξ (rep v) hd,
          exposedCache_data_eq beforeSigning ξ (rep v) hd]
    _ = ∑ v ∈ dataSet₀,
          ∑ ξ ∈ Finset.univ.filter (fun ξ : Record => publicData beforeSigning ξ = v),
            w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (G ξ) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [fiber₀_eq_filter_sec]
    _ = ∑ ξ : Record, w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ)) (G ξ) :=
        Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := dataSet₀)
          (g := publicData beforeSigning) (fun ξ _ => mem_dataSet₀ ξ) _

theorem sum_sumW_fiber₀ : ∑ v ∈ dataSet₀, sumW (fiber₀ v) = 1 := by
  calc ∑ v ∈ dataSet₀, sumW (fiber₀ v)
      = ∑ v ∈ dataSet₀,
          ∑ _ξ ∈ Finset.univ.filter (fun ξ : Record => publicData beforeSigning ξ = v), w := by
        refine Finset.sum_congr rfl fun v _ => ?_
        unfold sumW
        rw [fiber₀_eq_filter_sec]
    _ = ∑ _ξ : Record, w :=
        Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := dataSet₀)
          (g := publicData beforeSigning) (fun ξ _ => mem_dataSet₀ ξ) _
    _ = 1 := sum_w

/-! ## The bound -/

attribute [local irreducible] CostAtMost OracleAlgorithm.experiment rest rest₂ stB
attribute [local irreducible] keygen sign verify

theorem main_bound {B : ℕ} (hB : CostAtMost (OracleAlgorithm.experiment scheme A) B) :
    probTrue (OracleAlgorithm.experiment scheme A) ≤ κ * B := by
  have hrest : ∀ ξ : Record,
      CostAtMost (A.choose ξ.publicKey >>= rest₂ A ξ.publicKey ξ.1) B := by
    intro ξ
    have h := costAtMost_rest A hB ξ
    unfold rest at h
    exact h
  rw [probTrue_eq_E_run, E_run_experiment]
  calc ∑ ξ : Record, w * E (run (rest A (ξ.publicKey, ξ.1)) ξ.cache) g
      ≤ ∑ ξ : Record, w * E (run (A.choose ξ.publicKey) (exposedCache beforeSigning ξ))
          (fun p => if Cache.Hits p.2 (hiddenCache beforeSigning ξ) then 1 else
            E (run (rest₂ A ξ.publicKey ξ.1 p.1)
              (Cache.extend p.2 (hiddenCache beforeSigning ξ))) g) :=
        Finset.sum_le_sum fun ξ _ => mul_le_mul' le_rfl (stageA_iub A ξ)
    _ = ∑ v ∈ dataSet₀,
          E (run (A.choose (rep v).publicKey) (exposedCache beforeSigning (rep v)))
            (fun p => ∑ ξ ∈ fiber₀ v, w *
              (if Cache.Hits p.2 (hiddenCache beforeSigning ξ) then 1 else
                E (run (rest₂ A ξ.publicKey ξ.1 p.1)
                  (Cache.extend p.2 (hiddenCache beforeSigning ξ))) g)) :=
        regroup A (fun ξ p => if Cache.Hits p.2 (hiddenCache beforeSigning ξ) then 1 else
          E (run (rest₂ A ξ.publicKey ξ.1 p.1)
            (Cache.extend p.2 (hiddenCache beforeSigning ξ))) g)
    _ = ∑ v ∈ dataSet₀,
          E (run (A.choose (rep v).publicKey) (exposedCache beforeSigning (rep v)))
            (fun p => FA A v p.1 p.2) := rfl
    _ ≤ ∑ v ∈ dataSet₀, κ * sumW (fiber₀ v) * B :=
        Finset.sum_le_sum fun v hv =>
          stageA_master A v (rep v) (rep_mem hv) B (fun ξ _ => hrest ξ)
    _ = κ * B := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_sumW_fiber₀, mul_one]

theorem κ_mul_lt {B : ℕ} (h2 : 2 ≤ B) : κ * (B : ℝ≥0∞) < (B : ℝ≥0∞) / 2 ^ securityBits := by
  have hsec : securityBits = 127 := by
    unfold securityBits
    rfl
  rw [κ_eq, hsec, ENNReal.div_eq_inv_mul]
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by
    have hB : B ≠ 0 := by omega
    exact_mod_cast hB
  have hlt : (2 : ℝ≥0∞) ^ 127 < 2 ^ 128 := by
    first
    | exact_mod_cast (show (2 : ℕ) ^ 127 < 2 ^ 128 by norm_num)
    | (have h := ENNReal.mul_lt_mul_right (a := (2 : ℝ≥0∞) ^ 127) (b := 1) (c := 2)
          (by simp) (by simp) ENNReal.one_lt_two
       rwa [mul_one, ← pow_succ] at h)
  exact ENNReal.mul_lt_mul_left hB0 (ENNReal.natCast_ne_top B) (ENNReal.inv_lt_inv.2 hlt)

/-- **Strong unforgeability** of the leanISA Winternitz candidate. -/
theorem secure : scheme.Secure := by
  intro A B hB
  exact (main_bound A hB).trans_lt (κ_mul_lt (two_le_of_costAtMost_experiment A hB))

end OptimalOTS.LeanIsaBaseline

end
