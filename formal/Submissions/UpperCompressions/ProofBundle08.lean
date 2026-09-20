import Submissions.UpperCompressions.ProofBundle07
import Submissions.UpperCompressions.ProofBundle06
import Submissions.UpperCompressions.ProofBundle02

/- Original module: Submissions.UpperCompressions.WeightedProgramPayoff; SHA256 7f758b13bb8b873f8015183f9a07b43c2bdf2832f7c3e4c9d45b6bc892eb01d4. -/
section

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
noncomputable section
open scoped Classical
namespace WeightedCompletion
open WeightedReplacement

/-- Exact arbitrary nonnegative payoff under the actual all-trials oracle loop,
once its shared oracle row is fixed. Failure has payoff zero. -/
theorem E_loop_fixed_row_score (n M k : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (f : Nonce n → Fin M → ℝ) (hf : ∀ a i, 0 ≤ f a i) :
    E (run (loop n decode tier m k) c)
      (fun p => ENNReal.ofReal (score p.1 (fun r => f r.1 r.2))) =
      ENNReal.ofReal (tableKernel k (decode ∘ table) tier f) := by
  rw [run_loop_fixed_row n decode tier m table c hc, E_map]
  have hn : ∀ xs : List (Nonce n),
      0 ≤ score (selected (decode ∘ table) tier xs) (fun r => f r.1 r.2) := by
    intro xs
    cases selected (decode ∘ table) tier xs with
    | none => exact le_rfl
    | some r => exact hf r.1 r.2
  have h := E_drawList_ofReal n k
    (fun xs => score (selected (decode ∘ table) tier xs) (fun r => f r.1 r.2)) hn
  rw [iid_selected_score] at h
  exact h

end WeightedCompletion
#print axioms WeightedCompletion.E_loop_fixed_row_score
end
end

/- Original module: Submissions.UpperCompressions.WeightedKernelReplay; SHA256 77dc243c5b08f87a6d60192a5fdfd5f4510b6f9475ac0766fd3889854c301abb. -/
section

/-! Integrate the exact first-minimum kernel with unconditional row completion.
This supplies replay and excess bounds from the pointwise kernel envelope, with
no conditioning on the good-table event. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {Ω D I : Type} [Fintype Ω] [Nonempty Ω] [Fintype D] [Nonempty D]
  [Fintype I] [DecidableEq D] [DecidableEq I]

theorem tableKernel_reference_le (n : ℕ) (R : Finset D)
    (table : Ω → D → Option I) (tier : I → ℕ) (p g fKnown fFresh : I → ℝ)
    (hK : ∀ i, 0 ≤ fKnown i) (hF : ∀ i, 0 ≤ fFresh i) (F : ℝ) (ω : Ω)
    (hk : ∀ i, kernel n (fraction (weakRank tier i ∘ table ω))
      (fraction (strictRank tier i ∘ table ω)) ≤ F * (g i / p i)) :
    tableKernel n (table ω) tier (fun a i => if a ∈ R then fKnown i else fFresh i) ≤
      F * referencePayoff R table p g fKnown fFresh ω := by
  unfold tableKernel referencePayoff
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro a _
  cases ht : table ω a with
  | none => simp [score, ht]
  | some i =>
    simp only [score, ht, Option.map_some, Option.getD_some]
    by_cases ha : a ∈ R
    · rw [if_pos ha, if_pos ha]
      exact (mul_le_mul_of_nonneg_right (hk i) (hK i)).trans_eq (by ring)
    · rw [if_neg ha, if_neg ha]
      exact (mul_le_mul_of_nonneg_right (hk i) (hF i)).trans_eq (by ring)

/-- Actual first-minimum replay probability, averaged over the original table
completion law, is bounded by the clipped public replay hazard plus the bad tail. -/
theorem replay_kernel_bound (w : WeightedRow.Weights I) (n : ℕ) (tier : I → ℕ)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I) (k : I → ℕ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (Good : Ω → Prop) (F δ : ℝ) (hF : 0 ≤ F)
    (hkernel : ∀ ω, Good ω → ∀ i, kernel n
      (fraction (weakRank tier i ∘ table ω)) (fraction (strictRank tier i ∘ table ω)) ≤
        F * (w.g i / w.p i))
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean (fun ω => tableKernel n (table ω) tier (fun a i =>
      if a ∈ R then (if 2 ≤ k i then 1 else 0) else (if k i = 0 then 0 else 1))) ≤
      F * w.hazard (Fintype.card D) R.card k (rowCount R fixed) + δ := by
  apply replay_bound w R fixed table k hknown hfresh Good _ F δ hF
  · intro ω hg
    exact tableKernel_reference_le n R table tier w.p w.g _ _
      (fun i => by split_ifs <;> norm_num) (fun i => by split_ifs <;> norm_num) F ω (hkernel ω hg)
  · intro ω
    apply tableKernel_le n (table ω) tier _ 1 zero_le_one
    intro a i
    split_ifs <;> norm_num
  · exact hbad

/-- Post-sign excess payoff for the same actual selector and completion law. -/
theorem excess_kernel_bound (w : WeightedRow.Weights I) (n : ℕ) (tier : I → ℕ)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (e : I → ℝ) (he : ∀ i, 0 ≤ e i) (emax : ℝ) (hemax : 0 ≤ emax) (hesc : ∀ i, e i ≤ emax)
    (Good : Ω → Prop) (F δ : ℝ) (hF : 0 ≤ F)
    (hkernel : ∀ ω, Good ω → ∀ i, kernel n
      (fraction (weakRank tier i ∘ table ω)) (fraction (strictRank tier i ∘ table ω)) ≤
        F * (w.g i / w.p i))
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean (fun ω => tableKernel n (table ω) tier (fun _ i => e i)) ≤
      F * ((1-(R.card : ℝ)/Fintype.card D) * (∑ i, w.g i * e i) +
        (∑ i, (rowCount R fixed i : ℝ) * (w.g i/w.p i * e i)) / Fintype.card D) + emax * δ := by
  apply excess_bound w R fixed table hknown hfresh e he Good _ F emax δ hF hemax
  · intro ω hg
    simpa only [ite_self] using
      tableKernel_reference_le n R table tier w.p w.g e e he he F ω (hkernel ω hg)
  · intro ω
    exact tableKernel_le n (table ω) tier (fun _ i => e i) emax hemax (fun _ i => hesc i)
  · exact hbad

end WeightedCompletion
#print axioms WeightedCompletion.replay_kernel_bound
#print axioms WeightedCompletion.excess_kernel_bound
end
end

/- Original module: Submissions.UpperCompressions.WeightedUniformCompletion; SHA256 d4230e3a35d33dd908e0c0cccdf4f3d7860423d65634b9ae3e143dced953f4d8. -/
section

/-! Literal uniform-table completion has the unconditional one-coordinate
marginals required by the replay/excess formulas. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {D W I : Type} [Fintype D] [Fintype W] [Nonempty W] [DecidableEq D] [DecidableEq I]

theorem uniformMean_coordinate (a : D) (f : W → ℝ) :
    uniformMean (fun g : D → W => f (g a)) = uniformMean f := by
  have h : uniformMean (fun g : D → W => ∏ d, (if d = a then f (g d) else 1)) =
      ∏ d : D, uniformMean (fun x : W => if d = a then f x else 1) := by
    simp only [uniformMean, Fintype.card_fun, Nat.cast_pow]
    rw [← Fintype.prod_sum (f := fun d : D => fun x : W => if d = a then f x else 1),
      Finset.prod_div_distrib]
    simp
  have hm (d : D) : uniformMean (fun x : W => if d = a then f x else 1) =
      if d = a then uniformMean f else 1 := by
    by_cases hd : d = a <;> simp only [hd, if_true, if_false, uniformMean_const]
  simpa only [hm, Finset.prod_ite_eq', Finset.mem_univ, if_true] using h

def completionTable (R : Finset D) (fixed : D → Option I) (decode : W → Option I)
    (g : D → W) (a : D) : Option I := if a ∈ R then fixed a else decode (g a)

theorem completionTable_known (R : Finset D) (fixed : D → Option I) (decode : W → Option I)
    (g : D → W) (a : D) (ha : a ∈ R) : completionTable R fixed decode g a = fixed a := by
  exact if_pos ha

theorem completionTable_fresh (R : Finset D) (fixed : D → Option I) (decode : W → Option I)
    (a : D) (ha : a ∉ R) (i : I) :
    uniformMean (fun g : D → W => if completionTable R fixed decode g a = some i then 1 else 0) =
      uniformMean (fun x : W => if decode x = some i then 1 else 0) := by
  simp only [completionTable, if_neg ha]
  exact uniformMean_coordinate (W := W) a (fun x : W => if decode x = some i then 1 else 0)

theorem uniformMean_indicator (p : W → Prop) [DecidablePred p] :
    uniformMean (fun x => if p x then 1 else 0) =
      ((Finset.univ.filter p).card : ℝ) / Fintype.card W := by
  unfold uniformMean
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end WeightedCompletion

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReplacement WeightedCompletion
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes

/-- Actual uniform256 oracle answers have the exact classProbability marginal. -/
theorem uniform_decode_probability (i : Fin M) :
    uniformMean (fun x : BitVec 256 => if decode x = some i then 1 else 0) = classProbability i := by
  rw [uniformMean_indicator]
  have hcard : (Fintype.card (BitVec 256) : ℝ) = 2^256 := by
    rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcard]
  exact class_probability_real i

/-- Unexposed coordinates retain their original marginal before applying the
joint Good indicator. Cached coordinates are overwritten by their public values. -/
theorem completion_decode_probability {D : Type} [Fintype D] [DecidableEq D]
    (R : Finset D) (fixed : D → Option (Fin M)) (a : D) (ha : a ∉ R) (i : Fin M) :
    uniformMean (fun g : D → BitVec 256 =>
      if completionTable R fixed decode g a = some i then 1 else 0) = classProbability i := by
  exact (completionTable_fresh R fixed decode a ha i).trans (uniform_decode_probability i)

end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms WeightedCompletion.uniformMean_coordinate
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.completion_decode_probability
end
end

/- Original module: Submissions.UpperCompressions.WeightedPrefix; SHA256 0cab298866d1127f52eacf188b72d87c820604e4911df0459896cf27a3028d11. -/
section

/-! Exact raw256 tier-prefix probabilities. These are the72 predicates needed
by full-table concentration, connected to both first-minimum survival endpoints. -/
noncomputable section
open scoped BigOperators Classical
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReplacement WeightedCompletion WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes

def prefixLt (j : ℕ) (x : BitVec 256) : Prop :=
  match decode x with | none => False | some i => tier i < j

def prefixLe (j : ℕ) (x : BitVec 256) : Prop :=
  match decode x with | none => False | some i => tier i ≤ j

theorem prefixLe_eq (j : ℕ) : prefixLe j = prefixLt (j+1) := by
  funext x
  apply propext
  cases decode x <;> simp [prefixLe, prefixLt, Nat.lt_succ_iff]

theorem prefix_mass_sum (j : ℕ) (hj : j ≤ 72) :
    fraction (prefixLt j) = ∑ t ∈ Finset.range j, mass t := by
  have he : (fun x : BitVec 256 => if prefixLt j x then (1:ℝ) else 0) =
      fun x => score (decode x) (fun i => if tier i < j then 1 else 0) := by
    funext x
    cases hx : decode x <;> simp [prefixLt, score, hx]
  unfold fraction
  rw [he, mean_score decode classProbability (fun i => if tier i < j then 1 else 0)
    uniform_decode_probability]
  simp only [classProbability_eq]
  rw [sum_tier (fun t => probability t * (if t < j then 1 else 0))]
  have hh : (∑ t : Tier, (population t : ℝ) * (probability t.val * (if t.val < j then 1 else 0))) =
      ∑ t : Tier, if t.val < j then mass t.val else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    rw [← mul_assoc, population_probability]
    split_ifs <;> simp
  rw [hh, Fin.sum_univ_eq_sum_range (fun t => if t < j then mass t else 0) 72]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range 72).filter (fun t => t < j) = Finset.range j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]

theorem mass_early (j : ℕ) (hj : j < 71) : mass j = q := by
  unfold mass lower
  rw [if_pos hj]
  simp only [survival, Nat.cast_add, Nat.cast_one]
  ring

theorem prefixLt_probability (j : ℕ) (hj : j ≤ 71) :
    fraction (prefixLt j) = (j:ℝ)*q := by
  rw [prefix_mass_sum j (by omega)]
  calc
    _ = ∑ _t ∈ Finset.range j, q := by
      apply Finset.sum_congr rfl
      intro t ht
      exact mass_early t (by have := Finset.mem_range.mp ht; omega)
    _ = _ := by simp

theorem prefixLe_probability (j : ℕ) (hj : j ≤ 71) :
    fraction (prefixLe j) = 1-lower j := by
  rw [prefixLe_eq]
  by_cases h : j < 71
  · rw [prefixLt_probability (j+1) (by omega)]
    simp only [lower, if_pos h, survival]
    ring
  · have hj' : j = 71 := by omega
    subst j
    rw [prefix_mass_sum 72 le_rfl, total_mass]
    norm_num [lower]

/-- Complement a predicate before or after fixing a complete table. -/
theorem fraction_not {D : Type} [Fintype D] [Nonempty D] (P : D → Prop) :
    fraction (fun x => ¬ P x) = 1-fraction P := by
  unfold fraction uniformMean
  rw [eq_sub_iff_add_eq, ← add_div]
  have hs : (∑ x : D, if ¬ P x then (1:ℝ) else 0) +
      (∑ x : D, if P x then (1:ℝ) else 0) = Fintype.card D := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x : D, (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : P x <;> simp [hx]
      _ = _ := by simp
  convert div_self (show (Fintype.card D : ℝ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero) using 1
  congr 1
  convert hs using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

theorem weakRank_prefix (i : Fin M) :
    weakRank tier i ∘ decode = fun x => ¬ prefixLt (tier i) x := by
  funext x
  apply propext
  cases hx : decode x <;> simp [Function.comp_apply, weakRank, prefixLt, hx]

theorem strictRank_prefix (i : Fin M) :
    strictRank tier i ∘ decode = fun x => ¬ prefixLe (tier i) x := by
  funext x
  apply propext
  cases hx : decode x <;> simp [Function.comp_apply, strictRank, prefixLe, hx]

theorem weakRank_probability (i : Fin M) :
    fraction (weakRank tier i ∘ decode) = survival (tier i) := by
  rw [weakRank_prefix, fraction_not, prefixLt_probability (tier i) (by have := tier_lt i; omega)]
  rfl

theorem strictRank_probability (i : Fin M) :
    fraction (strictRank tier i ∘ decode) = lower (tier i) := by
  rw [strictRank_prefix, fraction_not, prefixLe_probability (tier i) (by have := tier_lt i; omega)]
  ring

theorem prefixLt_zero : prefixLt 0 = fun _ => False := by
  funext x
  cases hx : decode x <;> simp [prefixLt, hx]

theorem prefixLt_succ (j : ℕ) : prefixLt (j+1) = prefixLe j := (prefixLe_eq j).symm

end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.prefixLe_probability
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.weakRank_probability
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.strictRank_probability
end
end

/- Original module: Submissions.UpperCompressions.ReplacementConcreteRate; SHA256 19b08d932809642bbff57d5fccf7a9155000e3984ff0fd78321bb3b8d05a8893. -/
section

/-! Actual decoder probabilities and the concrete fresh-public-input posterior
rate for the mixed72 schedule. -/
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
open OptimalOTS.WeightedConstruction.WeightedSchedule WeightedReference
attribute [local irreducible] Finset.univ Finset.filter OptimalOTS.WeightedResearch92.classes

theorem concrete_weak_mass_pos (i : Fin M) :
    0 < fraction (weakRank tier i ∘ decode) := by
  rw [weakRank_probability]
  exact lt_of_lt_of_le (by norm_num [acceptance])
    (survival_ge_reject _ (by have := tier_lt i; omega))

theorem concrete_class_fraction (i : Fin M) :
    fraction (fun y => decode y = some i) = classProbability i := by
  unfold fraction
  convert uniform_decode_probability i using 1
  congr 1
  funext y
  split_ifs <;> rfl

theorem concrete_posterior_rate (i : Fin M) :
    fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) =
      classProbability i / survival (tier i) := by
  rw [concrete_class_fraction, weakRank_probability]

theorem concrete_posterior_rate_le (i : Fin M) :
    fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) ≤
      classProbability i / (1-acceptance) := by
  rw [concrete_posterior_rate]
  exact div_le_div_of_nonneg_left (classProbability_pos i).le
    (by norm_num [acceptance]) (survival_ge_reject _ (by have := tier_lt i; omega))

theorem concrete_posterior_rate_ennreal (i : Fin M) :
    ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) ≤
      ENNReal.ofReal (classProbability i / (1-acceptance)) :=
  ENNReal.ofReal_le_ofReal (concrete_posterior_rate_le i)

theorem concrete_rate_eq_base_excess (i : Fin M) :
    classProbability i / (1-acceptance) = kappa/2 + excess i := by
  rw [excess_eq]
  ring

theorem concrete_posterior_rate_base_excess (i : Fin M) :
    fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) ≤
      kappa/2 + excess i := by
  rw [← concrete_rate_eq_base_excess]
  exact concrete_posterior_rate_le i

theorem concrete_posterior_rate_ennreal_base_excess (i : Fin M) :
    ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) ≤
      ENNReal.ofReal (kappa/2) + ENNReal.ofReal (excess i) := by
  have he : 0 ≤ excess i := le_max_right _ _
  rw [← ENNReal.ofReal_add (show 0 ≤ kappa/2 by unfold kappa; positivity) he]
  exact ENNReal.ofReal_le_ofReal (concrete_posterior_rate_base_excess i)

#print axioms concrete_posterior_rate_ennreal_base_excess
#print axioms concrete_weak_mass_pos
#print axioms concrete_posterior_rate_le
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.WidePublicForgery; SHA256 547c8e56b3955d16c707f72702eeb7f6fba7cc88f777a268cd0defde41fd14bc. -/
section

/-! The actual forged input is the verifier's first public index query. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter
namespace OptimalOTS.WeightedConstruction.WideForest
open WeightedReplacement

def verifyForgery (pk : PublicKey) (m₁ : Message) (σ : Option WeightedScheme.Signature)
    (z : Message × WeightedScheme.Signature) : OracleComp Spec ForgeryResult := do
  let ok ← forestScheme.verify pk z.1 z.2
  return (z.1,z.2,ok && decide (σ.map (fun s => (m₁,s)) ≠ some z))

theorem stBWithForgery_bind (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option WeightedScheme.Signature) :
    stBWithForgery A pk m₁ st σ = A.forge st σ >>= verifyForgery pk m₁ σ := by
  unfold stBWithForgery verifyForgery
  congr 1
  funext z
  cases z
  dsimp only [WeightedScheme.Scheme.toAlgorithm]
  congr 1
  funext ok
  congr 3
  congr 1
  exact decide_eq_decide.mpr Iff.rfl

theorem verifyForgery_queries_chosen (pk : PublicKey) (m₁ : Message)
    (σ : Option WeightedScheme.Signature) (z : Message × WeightedScheme.Signature) (c : Cache) :
    publicHit (encQuery (z.1,z.2.1)) (verifyForgery pk m₁ σ z) c = 1 := by
  unfold verifyForgery WeightedScheme.Scheme.verify
  rw [bind_assoc]
  exact publicHit_hash_target (z.1++z.2.1) _ c

theorem stBWithForgery_selected_input_union (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (allowed good : EncInput → Prop) (c : Cache) :
    E (run (A.forge st σ) c)
      (fun p => if allowed (p.1.1,p.1.2.1) ∧ good (p.1.1,p.1.2.1) then 1 else 0) ≤
    ∑ u : EncInput, if allowed u ∧ good u then
      publicHit (encQuery u) (stBWithForgery A pk m₁ st σ) c else 0 := by
  have h := selected_input_union encQuery (fun z : Message × WeightedScheme.Signature => (z.1,z.2.1))
    allowed good (A.forge st σ) (verifyForgery pk m₁ σ) c
    (verifyForgery_queries_chosen pk m₁ σ)
  exact h.trans_eq (congrArg (fun oa => ∑ u : EncInput, if allowed u ∧ good u then
    publicHit (encQuery u) oa c else 0) (stBWithForgery_bind A pk m₁ st σ).symm)

#print axioms verifyForgery_queries_chosen
#print axioms stBWithForgery_selected_input_union
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.SignedGameBridge; SHA256 38a13559201f8cf75bef236de6bb69239ac044f2029573402c5e5750a03d616a. -/
section

/-! Concrete successful-signature bridge: the retained actual forged input is
either an old public-cache replay or an eligible fresh target. The fresh target
is fed to the checked all-L posterior/public-query theorem on the same cache. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ Finset.filter

def signatureFromWinner (ξ : Rec) (s : Option (Winner 86 WeightedSchedule.M)) :
    Option WeightedScheme.Signature :=
  s.map fun r => (r.1, revealed (setsName r.2) ξ)

def forgedInput (z : Message × WeightedScheme.Signature) : EncInput := (z.1,z.2.1)

theorem fExp_indexLength_none (A? : Option (Finset Name)) (ξ : Rec)
    (q : Query) (hq : q.1 = msgBits+86) : fExp A? ξ q = none := by
  have hk : kc ξ q = none := by
    cases hc : kc ξ q with
    | none => rfl
    | some u =>
      obtain ⟨h,p,hp,he,_⟩ := (kc_apply_iff ξ q u).mp hc
      exact False.elim (len_hashParent_ne_enc hp ((congrArg Sigma.fst he).symm.trans hq))
  unfold fExp
  split_ifs
  · exact hk
  · rfl

/-- This adapter supplies the concrete forge/verify/strong-check continuation
to FreshOverlay. The actual query-prefix, graph exposure, and positive weak-rank
mass premises are all discharged. -/
theorem concrete_fresh_overlay (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (m : Message) (st : A.State) (c : Cache) (k : ℕ)
    (v : Nonce 86) (i : Fin WeightedSchedule.M) :
    E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
      signedChosen (exposeCache (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
        ((lengthSlice (msgBits+86)).preload c g)) (fExp (some (setsName i)) ξ))
        (fun s => A.forge st (signatureFromWinner ξ s)) forgedInput (some (v,i))
        (freshAlternative 86 c (m,v))
        (fun d => WeightedSchedule.decode (g (d.1++d.2)) = some i)) ≤
      ENNReal.ofReal (fraction (fun y => WeightedSchedule.decode y = some i) /
        fraction (weakRank WeightedSchedule.tier i ∘ WeightedSchedule.decode)) *
        E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits)) (fun g =>
          signedCharge (exposeCache (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
            ((lengthSlice (msgBits+86)).preload c g)) (fExp (some (setsName i)) ξ))
            (fun s => stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ s))
            (some (v,i)) (indexPaid (isIndexLength (msgBits+86)))) := by
  have h := eager_fresh_chosen_overlay_bound 86 WeightedSchedule.decode WeightedSchedule.tier m k
    c (fExp (some (setsName i)) ξ) (fExp_indexLength_none _ ξ)
    (fun s => A.forge st (signatureFromWinner ξ s))
    (fun s => verifyForgery (pkOf ξ) m (signatureFromWinner ξ s))
    forgedInput v i (concrete_weak_mass_pos i)
    (fun s z d => verifyForgery_queries_chosen (pkOf ξ) m (signatureFromWinner ξ s) z d)
  have he : (fun s => A.forge st (signatureFromWinner ξ s) >>=
      verifyForgery (pkOf ξ) m (signatureFromWinner ξ s)) =
      (fun s => stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ s)) :=
    funext fun s => (stBWithForgery_bind A (pkOf ξ) m st (signatureFromWinner ξ s)).symm
  rw [he] at h
  exact h

/-- A completed table is stable under the actual public execution. An accepted
different-input forgery therefore uses either the original public cache or a
fresh coordinate of this same completed table. -/
theorem forgery_replay_or_fresh (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin WeightedSchedule.M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d)
    (p : ForgeryResult × Cache)
    (hp : p ∈ support (run (stBWithForgery A (pkOf ξ) m st
      (some (η,revealed (setsName i) ξ))) d)) (hok : p.1.2.2 = true) :
    Cache.Hits p.2 (fHid (some (setsName i)) ξ) ∨ Spr p.2 ξ ∨
      AlternateClass c (m,η) i ∨
      (freshAlternative 86 c (m,η) (p.1.1,p.1.2.1.1) ∧
        WeightedSchedule.decode (g (p.1.1++p.1.2.1.1)) = some i) := by
  obtain ⟨u,hu,hs | hh | hi⟩ := stBWithForgery_index_witness A ξ i η m st d p hp hok
  · exact Or.inr (Or.inl hs)
  · exact Or.inl hh
  · have hmono := sub_of_mem_support_run _ d p hp
    let q : Query := encQuery (p.1.1,p.1.2.1.1)
    cases hc : c q with
    | some y =>
      have hpq := hmono q y (hsub q y ((lengthSlice (msgBits+86)).preload_some c g q y hc))
      have hy : y = u := Option.some.inj (hpq.symm.trans hu)
      exact Or.inr (Or.inr (Or.inl ⟨_,hi.2,y,hc,hy ▸ hi.1⟩))
    | none =>
      have hpre : (lengthSlice (msgBits+86)).preload c g q =
          some (g (p.1.1++p.1.2.1.1)) := by
        unfold QuerySlice.preload
        rw [Cache.extend_apply, hc, Option.none_or]
        exact lengthSlice_inside _ g _
      have hpq := hmono q _ (hsub q _ hpre)
      have hu' : g (p.1.1++p.1.2.1.1) = u := Option.some.inj (hpq.symm.trans hu)
      exact Or.inr (Or.inr (Or.inr ⟨⟨hc,hi.2⟩,hu' ▸ hi.1⟩))

def forgerySuccess (p : ForgeryResult × Cache) : ℝ≥0∞ := if p.1.2.2 = true then 1 else 0

/-- Hidden graph removal keeps the forged input, which is needed for the
posterior event. This is the existing checked IUB theorem on the actual program. -/
theorem graph_iub_forgery (oa : OracleComp Spec ForgeryResult) (ξ : Rec)
    (A? : Option (Finset Name)) (d d' : Cache)
    (hd' : IndexExtension d d') (hξ : ¬ Cache.Hits d (kc ξ)) :
    E (run oa (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run oa (Cache.extend d' (fExp A? ξ)))
        (fun p => if Cache.Hits p.2 (fHid A? ξ) then 1 else forgerySuccess p) := by
  have hkc : Cache.extend d' (kc ξ) =
      Cache.extend (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    rw [Cache.extend_assoc, extend_fExp_fHid]
  have hdisj : Cache.Disjoint (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
    intro q hq
    have hkq : (kc ξ q).isSome := by
      obtain ⟨h,p,hp,_,hqp⟩ := (fHid_isSome_iff _ ξ q).mp hq
      exact (kc_isSome_iff ξ q).mpr ⟨h,p,hp,hqp⟩
    rw [Cache.extend_apply, indexExtension_kc_none hd' hξ hkq, Option.none_or]
    exact disjoint_fExp_fHid _ ξ q hq
  rw [hkc]
  exact iub oa (fHid A? ξ) forgerySuccess
    (fun p => by unfold forgerySuccess; split_ifs <;> simp) _ hdisj

/-- Concrete game-to-events bound. Replay is measured in the original public
cache; private signer entries are part of the fresh-table term, not replay. -/
theorem signed_success_replay_fresh (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin WeightedSchedule.M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d' : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hd' : IndexExtension c d') (hξ : ¬ Cache.Hits c (kc ξ))
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d') :
    E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
      (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ)) + ind (Spr p.2 ξ) +
          ind (AlternateClass c (m,η) i) +
          ind (freshAlternative 86 c (m,η) (p.1.1,p.1.2.1.1) ∧
            WeightedSchedule.decode (g (p.1.1++p.1.2.1.1)) = some i)) := by
  refine (graph_iub_forgery _ ξ (some (setsName i)) c d' hd' hξ).trans ?_
  apply expectedValue_mono_of_support
  intro p hp
  by_cases hh : Cache.Hits p.2 (fHid (some (setsName i)) ξ)
  · rw [if_pos hh, ind_of hh]
    exact le_add_right (le_add_right le_self_add)
  · rw [if_neg hh]
    by_cases hok : p.1.2.2 = true
    · rw [forgerySuccess, if_pos hok]
      have hsub' : Cache.Sub ((lengthSlice (msgBits+86)).preload c g)
          (Cache.extend d' (fExp (some (setsName i)) ξ)) :=
        fun q u h => Cache.extend_apply_of_some (hsub q u h)
      rcases forgery_replay_or_fresh A ξ i η m st c _ g hsub' p hp hok with hh' | hs | ho | hf
      · exact absurd hh' hh
      · rw [ind_of hs]
        exact le_add_right (le_add_right le_add_self)
      · rw [ind_of ho]
        exact le_add_right le_add_self
      · rw [ind_of hf]
        exact le_add_self
    · rw [forgerySuccess, if_neg hok]
      exact zero_le

#print axioms concrete_fresh_overlay
#print axioms forgery_replay_or_fresh
#print axioms signed_success_replay_fresh
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.ReplacementSignedBudget; SHA256 14acc066f362a0435f9db5a716e172fc8d46c9ec7b0905864ce9afdd86891669. -/
section

/-! Remaining-budget accounting after an arbitrary signer distribution. The
index excess and graph base rate use one actual continuation and cache. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementSignedBudget_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem index_expectedCharge_le {α : Type} (isIndex : Spec.Domain → Prop)
    (oa : OracleComp Spec α) (c : Cache) (B : ℕ) (hB : CostAtMost oa B) :
    expectedCharge (indexPaid isIndex) oa c ≤ B := by
  have hc : ∀ t, indexPaid isIndex t ≤ (1:ℝ≥0∞)*queryCost t := by
    intro t
    unfold indexPaid
    split_ifs <;> simp
  simpa using expectedCharge_budget (indexPaid isIndex) 1 hc oa B hB c

/-- A fixed signed class's index expenditure is bounded by its joint mass times
the remaining pathwise budget. This preserves the sign event explicitly. -/
theorem signedCharge_remaining {β γ : Type} (p : ProbComp (β × Cache))
    (post : β → OracleComp Spec γ) (b : β) (isIndex : Spec.Domain → Prop)
    (B : ℕ) (hB : CostAtMost (post b) B) :
    signedCharge p post b (indexPaid isIndex) ≤
      E p (fun r => if r.1 = b then (1:ℝ≥0∞) else 0) * B := by
  unfold signedCharge
  calc
    _ ≤ E p (fun r => (if r.1 = b then (1:ℝ≥0∞) else 0) * B) := by
      apply E_mono
      intro r
      by_cases hr : r.1 = b
      · simp only [hr, if_pos, one_mul]
        exact index_expectedCharge_le isIndex (post b) r.2 B hB
      · simp [hr]
    _ = _ := expectedValue_mul_const _ _ _

theorem signed_excess_remaining {β γ : Type} (p : ProbComp (β × Cache))
    (post : β → OracleComp Spec γ) (excess : β → ℝ≥0∞) (isIndex : Spec.Domain → Prop)
    (B : ℕ) (hB : ∀ b, CostAtMost (post b) B) :
    E p (fun r => excess r.1 * expectedCharge (indexPaid isIndex) (post r.1) r.2) ≤
      E p (fun r => excess r.1) * B := by
  calc
    _ ≤ E p (fun r => excess r.1 * B) := E_mono p
      (fun r => mul_le_mul' le_rfl (index_expectedCharge_le isIndex (post r.1) r.2 B (hB r.1)))
    _ = _ := expectedValue_mul_const _ _ _

/-- The class-dependent index rate is a common base plus excess; the graph rate
uses only the common base, so the base portion pays for the total cost once. -/
theorem paid_shared_budget_excess {γ : Type} (isIndex : Spec.Domain → Prop)
    (base extra : ℝ≥0∞) (oa : OracleComp Spec γ) (c : Cache) (B : ℕ)
    (hB : CostAtMost oa B) :
    (base+extra)*expectedCharge (indexPaid isIndex) oa c +
      base*expectedCharge (otherPaid isIndex) oa c ≤ base*B + extra*B := by
  calc
    _ = (base*expectedCharge (indexPaid isIndex) oa c + base*expectedCharge (otherPaid isIndex) oa c) +
        extra*expectedCharge (indexPaid isIndex) oa c := by ring
    _ ≤ base*B + extra*B := add_le_add
      (by simpa using paid_shared_budget isIndex base base oa c B hB)
      (mul_le_mul' le_rfl (index_expectedCharge_le isIndex oa c B hB))

/-- Averaging over the actual signer keeps the expected excess class score,
rather than replacing it by the largest possible class rate. -/
theorem integrated_shared_budget {β γ : Type} (p : ProbComp (β × Cache))
    (post : β → OracleComp Spec γ) (isIndex : Spec.Domain → Prop)
    (base : ℝ≥0∞) (excess : β → ℝ≥0∞) (B : ℕ)
    (hB : ∀ b, CostAtMost (post b) B) :
    E p (fun r => (base+excess r.1)*expectedCharge (indexPaid isIndex) (post r.1) r.2 +
      base*expectedCharge (otherPaid isIndex) (post r.1) r.2) ≤
      base*B + E p (fun r => excess r.1)*B := by
  calc
    _ ≤ E p (fun r => base*B + excess r.1*B) := E_mono p
      (fun r => paid_shared_budget_excess isIndex base (excess r.1) (post r.1) r.2 B (hB r.1))
    _ = E p (fun _ => base*B) + E p (fun r => excess r.1)*B := by
      calc
        _ = E p (fun _ => base*B) + E p (fun r => excess r.1*B) := expectedValue_add p _ _
        _ = _ := congrArg (E p (fun _ => base*B) + ·) (expectedValue_mul_const p _ _)
    _ ≤ _ := add_le_add (E_const_le _ _) le_rfl

/-- A finite family of joint signed events reconstructs the weighted expected
excess without losing correlation between the returned class and its cost. -/
theorem signedCharge_weighted_sum {β γ : Type} [Fintype β] (p : ProbComp (β × Cache))
    (post : β → OracleComp Spec γ) (weight : β → ℝ≥0∞) (charge : Spec.Domain → ℝ≥0∞) :
    (∑ b, weight b * signedCharge p post b charge) =
      E p (fun r => weight r.1*expectedCharge charge (post r.1) r.2) := by
  unfold signedCharge
  have hm (b : β) : weight b * E p (fun r => if r.1 = b then expectedCharge charge (post r.1) r.2 else 0) =
      E p (fun r => weight b * (if r.1 = b then expectedCharge charge (post r.1) r.2 else 0)) := by
    simpa only [mul_comm] using (expectedValue_mul_const p
      (fun r => if r.1 = b then expectedCharge charge (post r.1) r.2 else 0) (weight b)).symm
  simp_rw [hm]
  rw [← expectedValue_finsetSum]
  congr 1
  funext r
  simp only [mul_ite, mul_zero]
  simp

#print axioms signedCharge_remaining
#print axioms signed_excess_remaining
#print axioms integrated_shared_budget
#print axioms signedCharge_weighted_sum
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.SignedGameExpectation; SHA256 71c51a513db1b4c407c29181e34060b7e475ab2380506c85f7cdb1594df77240. -/
section

/-! Actual game-to-payoff leaves and the completed-table cache invariants needed
to integrate those leaves over the real all-L signer. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ Finset.filter

theorem exists_encQuery_of_length (q : Query) (hq : q.1 = msgBits+86) :
    ∃ u : EncInput, q = encQuery u := by
  rcases q with ⟨n,x⟩
  dsimp only at hq
  subst n
  refine ⟨(x.extractLsb' 86 msgBits,x.extractLsb' 0 86), ?_⟩
  exact congrArg (fun y : BitVec (msgBits+86) => (⟨msgBits+86,y⟩ : Query))
    BitVec.extractLsb'_append_extractLsb'.symm

theorem indexExtension_trans {c d e : Cache} (hcd : IndexExtension c d)
    (hde : IndexExtension d e) : IndexExtension c e := by
  refine ⟨fun q u h => hde.1 q u (hcd.1 q u h), ?_⟩
  intro q u hc he
  cases hd : d q with
  | none => exact hde.2 q u hd he
  | some v => exact hcd.2 q v hc hd

theorem indexExtension_preload (c : Cache) (g : BitVec (msgBits+86) → BitVec hashBits) :
    IndexExtension c ((lengthSlice (msgBits+86)).preload c g) := by
  refine ⟨fun q u h => (lengthSlice (msgBits+86)).preload_some c g q u h, ?_⟩
  intro q u hc he
  by_cases hq : q.1 = msgBits+86
  · exact exists_encQuery_of_length q hq
  · unfold QuerySlice.preload at he
    rw [Cache.extend_apply, hc, Option.none_or, lengthSlice_outside _ g q hq] at he
    cases he

theorem loop_indexExtension {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (p : Option (Winner 86 M) × Cache)
    (hp : p ∈ support (run (loop 86 decode tier m k) c)) : IndexExtension c p.2 := by
  refine ⟨sub_of_mem_support_run _ c p hp, ?_⟩
  intro q u hc he
  obtain ⟨η,hη⟩ := ReplacementLocality.loop_new_cache_row 86 decode tier m k c p hp q u hc he
  exact ⟨(m,η),hη⟩

theorem preloaded_loop_indexExtension {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (p : Option (Winner 86 M) × Cache)
    (hp : p ∈ support (run (loop 86 decode tier m k) ((lengthSlice (msgBits+86)).preload c g))) :
    IndexExtension c p.2 :=
  indexExtension_trans (indexExtension_preload c g) (loop_indexExtension decode tier m k _ p hp)

theorem auth_E_add {α : Type} (p : ProbComp α) (f g : α → ℝ≥0∞) :
    E p (fun x => f x+g x) = E p f+E p g := by
  simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]

/-- Verifying a forged pair keeps its chosen input unchanged. Dropping the
verification outcome converts the terminal fresh event to the exact forge
expectation used in FreshOverlay's `signedChosen`. -/
theorem terminal_chosen_le_forge (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (c : Cache) (P : EncInput → Prop) :
    E (run (stBWithForgery A pk m st σ) c) (fun p => ind (P (p.1.1,p.1.2.1.1))) ≤
      E (run (A.forge st σ) c) (fun p => ind (P (forgedInput p.1))) := by
  rw [stBWithForgery_bind]
  dsimp only [WeightedScheme.Scheme.toAlgorithm] at A ⊢
  rw [run_bind, E_bind]
  apply E_mono
  intro p
  unfold verifyForgery
  rw [run_bind, E_bind]
  simp only [run_pure, E_pure]
  exact E_const_le _ _

/-- Pointwise actual signed-game master. Its replay and fresh payoffs are
measured before signing and before final verification respectively, and graph
costs use exactly the same reduced continuation/cache as the fresh-index cost. -/
theorem signed_game_leaf (A : forestScheme.toAlgorithm.Adversary)
    (ξ : Rec) (i : Fin WeightedSchedule.M) (η : Nonce 86) (m : Message) (st : A.State)
    (c d' : Cache) (g : BitVec (msgBits+86) → BitVec hashBits)
    (hd' : IndexExtension c d') (hξ : ¬ Cache.Hits c (kc ξ))
    (hsub : Cache.Sub ((lengthSlice (msgBits+86)).preload c g) d') :
    E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
      (Cache.extend d' (kc ξ))) forgerySuccess ≤
      E (run (stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ))+ind (Spr p.2 ξ)) +
      ind (AlternateClass c (m,η) i) +
      E (run (A.forge st (some (η,revealed (setsName i) ξ)))
        (Cache.extend d' (fExp (some (setsName i)) ξ)))
        (fun p => ind (freshAlternative 86 c (m,η) (forgedInput p.1) ∧
          WeightedSchedule.decode (g (p.1.1++p.1.2.1)) = some i)) := by
  have h := signed_success_replay_fresh A ξ i η m st c d' g hd' hξ hsub
  rw [auth_E_add, auth_E_add] at h
  refine h.trans (add_le_add (add_le_add le_rfl (E_const_le _ _)) ?_)
  exact terminal_chosen_le_forge A (pkOf ξ) m st _ _
    (fun u => freshAlternative 86 c (m,η) u ∧ WeightedSchedule.decode (g (u.1++u.2)) = some i)

theorem retained_success_eq (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (c : Cache) :
    E (run (stBWithForgery A pk m st σ) c) forgerySuccess =
      E (run (stB A pk m st σ) c) successValue := by
  rw [← stBWithForgery_map A pk m st σ, run_map, E_map]
  rfl

#print axioms exists_encQuery_of_length
#print axioms preloaded_loop_indexExtension
#print axioms signed_game_leaf
#print axioms retained_success_eq
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.SignedAverage; SHA256 568305de8e5084bdf7542cfa2344ef96328e55081294daaaed06ca4dc4f8c489. -/
section

/-! Joint averages over the actual completed-table all-L signer. These helpers
retain a specific signed nonce/class event while combining the graph and fresh
index analyses on identical public continuations and caches. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

abbrev IndexTable := BitVec (msgBits+86) → BitVec hashBits
abbrev SignedWinner := Option (Winner 86 WeightedSchedule.M)

def signedAverage (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F : IndexTable → Cache → ℝ≥0∞) : ℝ≥0∞ :=
  E ($ᵗ IndexTable) (fun g =>
    E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p => if p.1=b then F g p.2 else 0))

theorem signedAverage_mono_support (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F G : IndexTable → Cache → ℝ≥0∞)
    (h : ∀ g p, p ∈ support (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) → p.1=b → F g p.2 ≤ G g p.2) :
    signedAverage m c k b F ≤ signedAverage m c k b G := by
  apply E_mono
  intro g
  apply expectedValue_mono_of_support
  intro p hp
  split_ifs with hb
  · exact h g p hp hb
  · exact le_rfl

theorem signedAverage_add (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (F G : IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => F g d+G g d) =
      signedAverage m c k b F+signedAverage m c k b G := by
  let trial (g : IndexTable) := run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2+G g p.2 else 0)) =
    E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2 else 0)) +
    E latent (fun g => E (trial g) (fun p => if p.1=b then G g p.2 else 0))
  have hh (P : Prop) [Decidable P] (a b : ℝ≥0∞) : (if P then a+b else 0) =
      (if P then a else 0)+(if P then b else 0) := by split_ifs <;> simp
  simp_rw [hh,auth_E_add]

theorem signedAverage_const_mul (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (a : ℝ≥0∞) (F : IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => a*F g d) = a*signedAverage m c k b F := by
  let trial (g : IndexTable) := run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then a*F g p.2 else 0)) =
    a*E latent (fun g => E (trial g) (fun p => if p.1=b then F g p.2 else 0))
  have hh (P : Prop) [Decidable P] (x : ℝ≥0∞) : (if P then a*x else 0) = a*(if P then x else 0) := by
    split_ifs <;> simp
  simp_rw [hh,← E_const_mul]

theorem signedAverage_sum {ι : Type} (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (T : Finset ι) (F : ι → IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => ∑ ξ ∈ T, F ξ g d) =
      ∑ ξ ∈ T, signedAverage m c k b (F ξ) := by
  let trial (g : IndexTable) := run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change E latent (fun g => E (trial g) (fun p => if p.1=b then ∑ ξ∈T, F ξ g p.2 else 0)) =
    ∑ ξ∈T, E latent (fun g => E (trial g) (fun p => if p.1=b then F ξ g p.2 else 0))
  have hh (P : Prop) [Decidable P] (f : ι → ℝ≥0∞) : (if P then ∑ ξ ∈ T, f ξ else 0) =
      ∑ ξ ∈ T, if P then f ξ else 0 := by split_ifs <;> simp
  simp_rw [hh,E_finsetSum]

theorem signedAverage_weighted_sum (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (T : Finset Rec) (F : Rec → IndexTable → Cache → ℝ≥0∞) :
    signedAverage m c k b (fun g d => ∑ ξ ∈ T, w*F ξ g d) =
      ∑ ξ ∈ T, w*signedAverage m c k b (F ξ) := by
  rw [signedAverage_sum]
  simp_rw [signedAverage_const_mul]

def fixedPost (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M) :=
  stBWithForgery A (pkOf ξ) m st (some (η,revealed (setsName i) ξ))

def graphLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M) (d : Cache) : ℝ≥0∞ :=
  E (run (fixedPost A ξ m st η i) (Cache.extend d (fExp (some (setsName i)) ξ)))
    (fun p => ind (Cache.Hits p.2 (fHid (some (setsName i)) ξ))+ind (Spr p.2 ξ))

def freshLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M)
    (c : Cache) (g : IndexTable) (d : Cache) : ℝ≥0∞ :=
  E (run (A.forge st (some (η,revealed (setsName i) ξ)))
    (Cache.extend d (fExp (some (setsName i)) ξ)))
    (fun p => ind (freshAlternative 86 c (m,η) (forgedInput p.1) ∧
      WeightedSchedule.decode (g (p.1.1++p.1.2.1))=some i))

def postCost (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M)
    (charge : Spec.Domain → ℝ≥0∞) (d : Cache) : ℝ≥0∞ :=
  expectedCharge charge (fixedPost A ξ m st η i) (Cache.extend d (fExp (some (setsName i)) ξ))

def posteriorRate (i : Fin WeightedSchedule.M) : ℝ≥0∞ :=
  ENNReal.ofReal (fraction (fun y => WeightedSchedule.decode y=some i) /
    fraction (weakRank WeightedSchedule.tier i ∘ WeightedSchedule.decode))

private def jointInd (P Q : Prop) : ℝ≥0∞ := if P ∧ Q then 1 else 0

theorem signedAverage_fresh_bound (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) :
    signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c) ≤
      posteriorRate i * signedAverage m c k (some (η,i))
        (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d) := by
  have h := concrete_fresh_overlay A ξ m st c k η i
  unfold signedChosen signedCharge exposeCache at h
  simp only [E_map] at h
  dsimp only [WeightedScheme.Scheme.toAlgorithm] at A
  have hl : (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then E (run (A.forge st (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (fExp (some (setsName i)) ξ)))
          (fun s => jointInd (freshAlternative 86 c (m,η) (forgedInput s.1))
            (WeightedSchedule.decode (g ((forgedInput s.1).1++(forgedInput s.1).2))=some i))
        else 0)) =
      (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then freshLoss A ξ m st η i c g p.2 else 0)) := by
    funext g
    congr 1
    funext p
    split_ifs with hp
    · rw [hp]
      simp only [freshLoss, signatureFromWinner, Option.map_some, forgedInput, ind, jointInd]
      congr 1
      funext s
      split_ifs <;> rfl
    · rfl
  have hr : (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then expectedCharge (indexPaid (isIndexLength (msgBits+86)))
          (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ p.1))
          (Cache.extend p.2 (fExp (some (setsName i)) ξ)) else 0)) =
      (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) (fun p =>
        if p.1=some (η,i) then postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) p.2 else 0)) := by
    funext g
    congr 1
    funext p
    split_ifs with hp
    · rw [hp]
      rfl
    · rfl
  have hlE := congrArg (E ($ᵗ IndexTable)) hl
  have hrE := congrArg (E ($ᵗ IndexTable)) hr
  exact hlE.symm.le.trans (h.trans_eq (congrArg (posteriorRate i * ·) hrE))

theorem signedAverage_graph_bound (A : forestScheme.toAlgorithm.Adversary)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ)) :
    signedAverage m c k (some (η,i)) (fun _ d => ∑ ξ∈T, w*graphLoss A ξ m st η i d) ≤
      signedAverage m c k (some (η,i)) (fun _ d => (∑ ξ∈T, w*ind (Spr c ξ)) +
        authRate * ∑ ξ∈fiberA pk, w*postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d) := by
  apply signedAverage_mono_support
  intro g p hp _
  have hext := preloaded_loop_indexExtension WeightedSchedule.decode WeightedSchedule.tier m k c g p hp
  have h := postsign_auth_expected (isCut_setsName i) pk T hT c p.2 hext hTc
    (isIndexLength (msgBits+86)) (fun q hq => exists_encQuery_of_length q hq)
    (fun dt => stBWithForgery A dt.1 m st (some (η,dt.2.1)))
  exact h

#print axioms signedAverage_fresh_bound
#print axioms signedAverage_graph_bound
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.SignedWinnerMaster; SHA256 b0acaf49b115ab6583b992fa7527581511ea1690acd1eeeaec4e84ee2f7288b6. -/
section

/-! A concrete joint signed-winner game-to-payoff master. Query budgets are
required only at supported actual signer outcomes; impossible returned classes
never impose a continuation-budget premise. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

def signedMass (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner) : ℝ≥0∞ :=
  signedAverage m c k b (fun _ _ => 1)

theorem signedAverage_const (m : Message) (c : Cache) (k : ℕ) (b : SignedWinner)
    (a : ℝ≥0∞) : signedAverage m c k b (fun _ _ => a) = a*signedMass m c k b := by
  simpa only [mul_one,signedMass] using signedAverage_const_mul m c k b a (fun _ _ => 1)

def SupportedPostBudget (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) : Prop :=
  ∀ ξ∈fiberA pk, ∀ g p,
    p ∈ support (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g)) →
    CostAtMost (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ p.1)) B

def successLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (η : Nonce 86) (i : Fin WeightedSchedule.M) (d : Cache) : ℝ≥0∞ :=
  E (run (fixedPost A ξ m st η i) (Cache.extend d (kc ξ))) forgerySuccess

theorem signed_leaf_average (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) (hξ : ¬ Cache.Hits c (kc ξ)) :
    signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d) ≤
      signedAverage m c k (some (η,i)) (fun _ d => graphLoss A ξ m st η i d) +
      signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i)) +
      signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c) := by
  rw [← signedAverage_add, ← signedAverage_add]
  apply signedAverage_mono_support
  intro g p hp _
  exact signed_game_leaf A ξ i η m st c p.2 g
    (preloaded_loop_indexExtension WeightedSchedule.decode WeightedSchedule.tier m k c g p hp)
    hξ (sub_of_mem_support_run _ _ p hp)

theorem signed_cost_budget (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) (hB : SupportedPostBudget A pk m st c k B) :
    posteriorRate i * (∑ ξ∈fiberA pk, w*signedAverage m c k (some (η,i))
      (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d)) +
    authRate * (∑ ξ∈fiberA pk, w*signedAverage m c k (some (η,i))
      (fun _ d => postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d)) ≤
      (max (posteriorRate i) authRate * sumW (fiberA pk) * B) * signedMass m c k (some (η,i)) := by
  rw [← signedAverage_weighted_sum, ← signedAverage_weighted_sum,
    ← signedAverage_const_mul, ← signedAverage_const_mul, ← signedAverage_add,
    ← signedAverage_const]
  apply signedAverage_mono_support
  intro g p hp hb
  have hcont : ∀ ξ∈fiberA pk,
      CostAtMost (fixedPost A ξ m st η i) B := by
    intro ξ hξ
    have h := hB ξ hξ g p hp
    simpa only [hb,signatureFromWinner,Option.map_some,fixedPost] using h
  have h := record_shared_paid_budget (setsName i) pk p.2 (isIndexLength (msgBits+86))
    (posteriorRate i) authRate
    (fun dt => stBWithForgery A dt.1 m st (some (η,dt.2.1))) B hcont
  exact h

/-- Conditional successful-signature master for a fixed returned nonce/class.
It contains the actual strong-success event, concrete posterior law, graph
resampling, and one supported continuation clock. Only the pre-sign record
filter and the actual residual budget are premises. -/
theorem signed_winner_master (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ) (η : Nonce 86)
    (i : Fin WeightedSchedule.M) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    (∑ ξ∈T, w*signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d)) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
      sumW T * signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i)) +
      (max (posteriorRate i) authRate * sumW (fiberA pk) * B)*signedMass m c k (some (η,i)) := by
  let G (ξ : Rec) := signedAverage m c k (some (η,i)) (fun _ d => graphLoss A ξ m st η i d)
  let F (ξ : Rec) := signedAverage m c k (some (η,i)) (freshLoss A ξ m st η i c)
  let CI (ξ : Rec) := signedAverage m c k (some (η,i))
    (fun _ d => postCost A ξ m st η i (indexPaid (isIndexLength (msgBits+86))) d)
  let CO (ξ : Rec) := signedAverage m c k (some (η,i))
    (fun _ d => postCost A ξ m st η i (otherPaid (isIndexLength (msgBits+86))) d)
  let R := signedAverage m c k (some (η,i)) (fun _ _ => ind (AlternateClass c (m,η) i))
  have hG : (∑ ξ∈T, w*G ξ) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
        authRate*(∑ ξ∈fiberA pk, w*CO ξ) := by
    have h := signedAverage_graph_bound A pk T hT m st c k η i hTc
    rw [signedAverage_weighted_sum, signedAverage_add, signedAverage_const,
      signedAverage_const_mul, signedAverage_weighted_sum] at h
    exact h
  have hF : (∑ ξ∈T, w*F ξ) ≤ posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ) := by
    calc
      _ ≤ ∑ ξ∈T, w*(posteriorRate i*CI ξ) :=
        Finset.sum_le_sum fun ξ _ => mul_le_mul_right (signedAverage_fresh_bound A ξ m st c k η i) w
      _ = posteriorRate i*(∑ ξ∈T, w*CI ξ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := mul_le_mul_right (Finset.sum_le_sum_of_subset hT) (posteriorRate i)
  calc
    _ ≤ ∑ ξ∈T, w*(G ξ+R+F ξ) := Finset.sum_le_sum fun ξ hξ =>
      mul_le_mul_right (signed_leaf_average A ξ m st c k η i (hTc ξ hξ)) w
    _ = (∑ ξ∈T, w*G ξ)+sumW T*R+(∑ ξ∈T, w*F ξ) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_mul,sumW]
    _ ≤ ((∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
        authRate*(∑ ξ∈fiberA pk, w*CO ξ))+sumW T*R+
        posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ) := add_le_add (add_le_add hG le_rfl) hF
    _ = (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) + sumW T*R +
        (posteriorRate i*(∑ ξ∈fiberA pk, w*CI ξ)+authRate*(∑ ξ∈fiberA pk, w*CO ξ)) := by ring
    _ ≤ _ := add_le_add le_rfl (signed_cost_budget A pk m st c k B η i hB)

#print axioms signed_cost_budget
#print axioms signed_winner_master
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.SignedNoneMaster; SHA256 d811c7b2bc6877be925a7d1a5242a11251d24b3051c966f26141ec0f52bb14cd. -/
section

/-! The actual signing-failure branch of the common game master. It carries
pre-sign spurious mass once and spends only its supported public continuation. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

def nonePost (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) := stBWithForgery A (pkOf ξ) m st none

def noneSuccessLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (d : Cache) : ℝ≥0∞ :=
  E (run (nonePost A ξ m st) (Cache.extend d (kc ξ))) forgerySuccess

def noneOtherCost (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (d : Cache) : ℝ≥0∞ :=
  expectedCharge (otherPaid (isIndexLength (msgBits+86))) (nonePost A ξ m st) d

theorem retained_charge_eq (A : forestScheme.toAlgorithm.Adversary)
    (pk : PublicKey) (m : Message) (st : A.State) (σ : Option WeightedScheme.Signature)
    (charge : Spec.Domain → ℝ≥0∞) (c : Cache) :
    expectedCharge charge (stBWithForgery A pk m st σ) c =
      expectedCharge charge (stB A pk m st σ) c := by
  have h := expectedCharge_map charge (stBWithForgery A pk m st σ)
    (fun r : ForgeryResult => r.2.2) c
  rw [stBWithForgery_map] at h
  exact h.symm

theorem none_fiber_leaf (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c d' : Cache) (hd' : IndexExtension c d') (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ)) :
    (∑ ξ∈T, w*noneSuccessLoss A ξ m st d') ≤
      (∑ ξ∈T, w*ind (Spr c ξ)) + authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d') := by
  have hsum : (∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d') =
      sumW (fiberA pk)*expectedCharge (otherPaid (isIndexLength (msgBits+86)))
        (stB A pk m st none) d' := by
    calc
      _ = ∑ ξ∈fiberA pk, w*expectedCharge (otherPaid (isIndexLength (msgBits+86)))
          (stB A pk m st none) d' := by
        apply Finset.sum_congr rfl
        intro ξ hξ
        unfold noneOtherCost nonePost
        rw [retained_charge_eq, (Finset.mem_filter.mp hξ).2]
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ = ∑ ξ∈T, w*E (run (stB A (pkOf ξ) m st none) (Cache.extend d' (kc ξ))) successValue := by
      apply Finset.sum_congr rfl
      intro ξ _
      exact congrArg (w*·) (retained_success_eq A (pkOf ξ) m st none _)
    _ ≤ (∑ ξ∈T, w*ind (Spr c ξ)) + (authRate*sumW (fiberA pk))*
        expectedCharge (otherPaid (isIndexLength (msgBits+86))) (stB A pk m st none) d' :=
      failed_sign_success_expected A pk T hT m st c d' hd' hTc
        (isIndexLength (msgBits+86)) (fun q hq => exists_encQuery_of_length q hq)
    _ = _ := by rw [hsum]; ring

theorem none_cost_budget (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ)
    (hB : SupportedPostBudget A pk m st c k B) :
    signedAverage m c k none (fun _ d => authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) ≤
      (authRate*sumW (fiberA pk)*B)*signedMass m c k none := by
  rw [← signedAverage_const]
  apply signedAverage_mono_support
  intro g p hp hb
  have hcont : ∀ ξ∈fiberA pk, noneOtherCost A ξ m st p.2 ≤ B := by
    intro ξ hξ
    have h := hB ξ hξ g p hp
    have hc : CostAtMost (nonePost A ξ m st) B := by
      simpa only [hb,signatureFromWinner,Option.map_none,nonePost] using h
    have hq := expectedCharge_budget (otherPaid (isIndexLength (msgBits+86))) 1
      (fun t => by simpa only [one_mul] using otherPaid_le_queryCost (isIndexLength (msgBits+86)) t)
      (nonePost A ξ m st) B hc p.2
    simpa only [one_mul,noneOtherCost] using hq
  calc
    _ ≤ authRate*(∑ ξ∈fiberA pk, w*B) := mul_le_mul_right
      (Finset.sum_le_sum fun ξ hξ => mul_le_mul_right (hcont ξ hξ) w) authRate
    _ = _ := by rw [← Finset.sum_mul]; simp only [sumW,mul_assoc]

/-- Joint actual failed-signature success, with no posterior/index premise and
no budget obligation for unsupported signer outputs. -/
theorem signed_none_master (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (m : Message) (st : A.State) (c : Cache) (k B : ℕ)
    (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    (∑ ξ∈T, w*signedAverage m c k none (fun _ d => noneSuccessLoss A ξ m st d)) ≤
      (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k none +
      (authRate*sumW (fiberA pk)*B)*signedMass m c k none := by
  rw [← signedAverage_weighted_sum]
  calc
    _ ≤ signedAverage m c k none (fun _ d => (∑ ξ∈T, w*ind (Spr c ξ)) +
        authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) := by
      apply signedAverage_mono_support
      intro g p hp _
      exact none_fiber_leaf A pk T hT m st c p.2
        (preloaded_loop_indexExtension WeightedSchedule.decode WeightedSchedule.tier m k c g p hp) hTc
    _ = (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k none +
        signedAverage m c k none (fun _ d => authRate*(∑ ξ∈fiberA pk, w*noneOtherCost A ξ m st d)) := by
      rw [signedAverage_add,signedAverage_const]
    _ ≤ _ := add_le_add le_rfl (none_cost_budget A pk m st c k B hB)

#print axioms none_fiber_leaf
#print axioms signed_none_master
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.SignedConditionalMaster; SHA256 9db7178c8e0919b8eeac8075d6dc95ed51d51c5462ceaa704d03165b900a2bc9. -/
section

/-! The common conditional game-to-payoff master, including actual signing
failure and every supported signed outcome. Replay and excess retain the actual
completed-table signer law, ready for the concrete empirical/hazard bounds. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

def winnerReplay (c : Cache) (m : Message) : SignedWinner → ℝ≥0∞
  | none => 0
  | some (η,i) => ind (AlternateClass c (m,η) i)

def winnerExcess : SignedWinner → ℝ≥0∞
  | none => 0
  | some (_,i) => ENNReal.ofReal (WeightedSchedule.excess i)

def signerAverage (m : Message) (c : Cache) (k : ℕ) (F : SignedWinner → ℝ≥0∞) : ℝ≥0∞ :=
  E ($ᵗ IndexTable) (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)) (fun p => F p.1))

def outcomeSuccessLoss (A : forestScheme.toAlgorithm.Adversary) (ξ : Rec)
    (m : Message) (st : A.State) (b : SignedWinner) (d : Cache) : ℝ≥0∞ :=
  E (run (stBWithForgery A (pkOf ξ) m st (signatureFromWinner ξ b))
    (Cache.extend d (kc ξ))) forgerySuccess

def conditionalGame (A : forestScheme.toAlgorithm.Adversary) (T : Finset Rec)
    (m : Message) (st : A.State) (c : Cache) (k : ℕ) : ℝ≥0∞ :=
  ∑ ξ∈T, w*E ($ᵗ IndexTable) (fun g =>
    E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
      ((lengthSlice (msgBits+86)).preload c g))
      (fun p => outcomeSuccessLoss A ξ m st p.1 p.2))

theorem signedAverage_partition (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → IndexTable → Cache → ℝ≥0∞) :
    (∑ b : SignedWinner, signedAverage m c k b (F b)) =
      E ($ᵗ IndexTable) (fun g => E (run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
        ((lengthSlice (msgBits+86)).preload c g)) (fun p => F p.1 g p.2)) := by
  let trial (g : IndexTable) := run (loop 86 WeightedSchedule.decode WeightedSchedule.tier m k)
    ((lengthSlice (msgBits+86)).preload c g)
  let latent : ProbComp IndexTable := $ᵗ IndexTable
  change (∑ b : SignedWinner, E latent (fun g => E (trial g)
    (fun p => if p.1=b then F b g p.2 else 0))) =
      E latent (fun g => E (trial g) (fun p => F p.1 g p.2))
  rw [← E_finsetSum]
  congr 1
  funext g
  rw [← E_finsetSum]
  congr 1
  funext p
  simp

theorem signedMass_weighted_sum (m : Message) (c : Cache) (k : ℕ)
    (F : SignedWinner → ℝ≥0∞) :
    (∑ b : SignedWinner, F b*signedMass m c k b) = signerAverage m c k F := by
  simp_rw [← signedAverage_const]
  exact signedAverage_partition m c k (fun b _ _ => F b)

theorem signedMass_sum_le (m : Message) (c : Cache) (k : ℕ) :
    (∑ b : SignedWinner, signedMass m c k b) ≤ 1 := by
  have h := signedMass_weighted_sum m c k (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  exact (E_mono _ (fun _ => E_const_le _ 1)).trans (E_const_le _ 1)

theorem conditionalGame_partition (A : forestScheme.toAlgorithm.Adversary)
    (T : Finset Rec) (m : Message) (st : A.State) (c : Cache) (k : ℕ) :
    conditionalGame A T m st c k =
      ∑ b : SignedWinner, ∑ ξ∈T, w*signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d) := by
  unfold conditionalGame
  calc
    _ = ∑ ξ∈T, w*(∑ b : SignedWinner,
        signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d)) := by
      apply Finset.sum_congr rfl
      intro ξ _
      exact congrArg (w*·) (signedAverage_partition m c k (fun b _ d => outcomeSuccessLoss A ξ m st b d)).symm
    _ = _ := by simp only [Finset.mul_sum]; rw [Finset.sum_comm]

theorem authRate_ofReal : authRate = ENNReal.ofReal (WeightedReference.kappa/2) := by
  unfold authRate WeightedReference.kappa
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
    ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ)<2^127)]
  norm_num

theorem max_posterior_auth_le (i : Fin WeightedSchedule.M) :
    max (posteriorRate i) authRate ≤ authRate+ENNReal.ofReal (WeightedSchedule.excess i) := by
  apply max_le
  · rw [authRate_ofReal]
    exact concrete_posterior_rate_ennreal_base_excess i
  · exact le_self_add

theorem signed_outcome_master (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c : Cache) (k B : ℕ) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) (b : SignedWinner) :
    (∑ ξ∈T, w*signedAverage m c k b (fun _ d => outcomeSuccessLoss A ξ m st b d)) ≤
      ((∑ ξ∈T, w*ind (Spr c ξ)) + sumW T*winnerReplay c m b +
        (sumW (fiberA pk)*B)*(authRate+winnerExcess b))*signedMass m c k b := by
  cases b with
  | none =>
    have h := signed_none_master A pk T hT m st c k B hTc hB
    change (∑ ξ∈T, w*signedAverage m c k none (fun _ d => noneSuccessLoss A ξ m st d)) ≤ _
    refine h.trans_eq ?_
    simp only [winnerReplay,winnerExcess,mul_zero,add_zero]
    ring
  | some b =>
    rcases b with ⟨η,i⟩
    have h := signed_winner_master A pk T hT m st c k B η i hTc hB
    change (∑ ξ∈T, w*signedAverage m c k (some (η,i)) (fun _ d => successLoss A ξ m st η i d)) ≤ _
    refine h.trans ?_
    rw [signedAverage_const]
    calc
      _ ≤ (∑ ξ∈T, w*ind (Spr c ξ))*signedMass m c k (some (η,i)) +
          sumW T*(ind (AlternateClass c (m,η) i)*signedMass m c k (some (η,i))) +
          ((authRate+ENNReal.ofReal (WeightedSchedule.excess i))*sumW (fiberA pk)*B)*
            signedMass m c k (some (η,i)) := by
        gcongr
        exact max_posterior_auth_le i
      _ = _ := by simp only [winnerReplay,winnerExcess]; ring

/-- The actual conditional sign/forge/verify game, including signing failure,
is bounded by surviving pre-sign spurious mass plus replay and expected class
excess of the same all-L signer. The base graph/index cost is spent once.
Only supported remaining budgets and the pre-sign no-hit record filter remain. -/
theorem conditional_game_master (A : forestScheme.toAlgorithm.Adversary) (pk : BitVec 128)
    (T : Finset Rec) (hT : T ⊆ fiberA pk) (m : Message) (st : A.State)
    (c : Cache) (k B : ℕ) (hTc : ∀ ξ∈T, ¬ Cache.Hits c (kc ξ))
    (hB : SupportedPostBudget A pk m st c k B) :
    conditionalGame A T m st c k ≤
      (∑ ξ∈T, w*ind (Spr c ξ)) + sumW (fiberA pk) *
        (signerAverage m c k (winnerReplay c m) +
          B*(authRate+signerAverage m c k winnerExcess)) := by
  rw [conditionalGame_partition]
  let P := ∑ ξ∈T, w*ind (Spr c ξ)
  let Z := sumW (fiberA pk)*(B:ℝ≥0∞)
  calc
    _ ≤ ∑ b : SignedWinner, (P+sumW T*winnerReplay c m b+Z*(authRate+winnerExcess b))*
        signedMass m c k b := Finset.sum_le_sum fun b _ =>
      signed_outcome_master A pk T hT m st c k B hTc hB b
    _ = P*(∑ b : SignedWinner, signedMass m c k b) +
        sumW T*(∑ b : SignedWinner, winnerReplay c m b*signedMass m c k b) +
        Z*(authRate*(∑ b : SignedWinner, signedMass m c k b) +
          ∑ b : SignedWinner, winnerExcess b*signedMass m c k b) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib]
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ P*1 + sumW T*(∑ b : SignedWinner, winnerReplay c m b*signedMass m c k b) +
        Z*(authRate*1+∑ b : SignedWinner, winnerExcess b*signedMass m c k b) := by
      gcongr <;> exact signedMass_sum_le m c k
    _ = P+sumW T*signerAverage m c k (winnerReplay c m)+Z*(authRate+signerAverage m c k winnerExcess) := by
      rw [mul_one,mul_one,signedMass_weighted_sum,signedMass_weighted_sum]
    _ ≤ P+sumW (fiberA pk)*signerAverage m c k (winnerReplay c m)+
        Z*(authRate+signerAverage m c k winnerExcess) := by
      gcongr
      exact sumW_mono hT
    _ = _ := by dsimp only [P,Z]; ring

#print axioms conditionalGame_partition
#print axioms authRate_ofReal
#print axioms conditional_game_master
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.WeightedReserve; SHA256 5e3db4eff5682f305215d35087c497d99755174cab3f7e0aaff90b2c71b1fb6f. -/
section

/-! The all-trial signer reserves its entire paid query budget on every
raw answer path. These are resource statements, not probabilistic claims. -/

open OracleSpec OracleComp
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling

variable {M : ℕ}

theorem loop_step_budget {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (k : ℕ) (kont : Option (Winner n M) → OracleComp Spec β)
    (hc : blockCost (msgBits+n) = 1) {b : ℕ}
    (hB : CostAtMost (loop n decode tier m (k+1) >>= kont) b) :
    1 ≤ b ∧ ∀ η w, CostAtMost
      (loop n decode tier m k >>= fun r =>
        kont (best (fun s => tier s.2) (candidate decode η w) r)) (b-1) := by
  rw [loop,bind_assoc,sampleBits] at hB
  have hη := costAtMost_liftM_bind _ _ hB
  have hη' (η : Nonce n) := hη η (by simp)
  have hw (η : Nonce n) : 1 ≤ b ∧ ∀ w, CostAtMost
      (loop n decode tier m k >>= fun r =>
        kont (best (fun s => tier s.2) (candidate decode η w) r)) (b-1) := by
    have hx := hη' η
    rw [bind_assoc,hash,costAtMost_query_bind_iff] at hx
    change blockCost (msgBits+n) ≤ b ∧ ∀ w : BitVec hashBits,
      CostAtMost ((loop n decode tier m k >>= fun r =>
        pure (best (fun s => tier s.2) (candidate decode η w) r)) >>= kont)
        (b-blockCost (msgBits+n)) at hx
    simpa only [hc,bind_assoc,pure_bind] using hx
  exact ⟨(hw 0).1,fun η => (hw η).2⟩

/-- All L hashes are paid before any outcome-dependent continuation.
The guarantee holds for every syntactically possible output, so it also
covers outcomes of a single consistent random oracle. -/
theorem loop_reserve {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (hc : blockCost (msgBits+n) = 1) :
    ∀ k (kont : Option (Winner n M) → OracleComp Spec β) b,
      CostAtMost (loop n decode tier m k >>= kont) b →
      k ≤ b ∧ ∀ r ∈ support (loop n decode tier m k),
        CostAtMost (kont r) (b-k) := by
  intro k
  induction k with
  | zero =>
    intro kont b hB
    rw [loop,pure_bind] at hB
    refine ⟨Nat.zero_le _, ?_⟩
    intro r hr
    simp only [loop,support_pure,Set.mem_singleton_iff] at hr
    subst r
    simpa using hB
  | succ k ih =>
    intro kont b hB
    obtain ⟨hb,hs⟩ := loop_step_budget n decode tier m k kont hc hB
    have hi (η : Nonce n) (w : BitVec hashBits) := ih
      (fun r => kont (best (fun s => tier s.2) (candidate decode η w) r))
      (b-1) (hs η w)
    have hk := (hi 0 0).1
    refine ⟨by omega, ?_⟩
    intro r hr
    rw [loop,support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨η,_,hr⟩ := hr
    rw [support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨w,_,hr⟩ := hr
    rw [support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨s,hs,hr⟩ := hr
    rw [support_pure,Set.mem_singleton_iff] at hr
    subst r
    have hkont := (hi η w).2 s hs
    simpa only [Nat.sub_sub,show 1+k=k+1 by omega] using hkont

#print axioms loop_step_budget
#print axioms loop_reserve

end OptimalOTS.WeightedSampling
end
end

