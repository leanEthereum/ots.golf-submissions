import Submissions.UpperCompressions.LongChain91Codec
import Submissions.UpperCompressions.ProofBundle04

/-!
# Concrete security data for the chain-18 compact schedule

This module connects the exact full-width decoder to the finite-difference
weights certified in `CompactSchedule91`.  In particular, every probability
and score in `securityWeights` is the probability of an actual decoder fiber
or its corresponding true (unrounded) winner kernel.
-/

namespace OptimalOTS.WeightedConstruction.LongChain91Security

open scoped Classical BigOperators
noncomputable section

set_option maxRecDepth 100000

abbrev Tier := LongChain91Schedule.Tier
abbrev M : ℕ := LongChain91Schedule.M

/-- Probability of one concrete class under a uniform 256-bit answer. -/
def classProbability (i : Fin M) : ℝ := Chain18Compact.probability (LongChain91Schedule.tier i)

/-- The true reference winner weight for one concrete class. -/
def referenceWeight (i : Fin M) : ℝ := Chain18Compact.winner Chain18Compact.actualKernel (LongChain91Schedule.tier i)

theorem class_probability_real (i : Fin M) :
    ((Finset.univ.filter fun x : BitVec 256 => LongChain91Schedule.decode x = some i).card : ℝ) /
        2^256 = classProbability i := by
  exact LongChain91Schedule.class_probability_real i

/-- Reindex any real-valued class expression by the 160 compact tiers. -/
theorem sum_tier (f : Tier → ℝ) :
    (∑ i : Fin M, f (LongChain91Schedule.tier i)) =
      ∑ j : Tier, (Chain18Compact.classes j : ℝ) * f j :=
  LongChain91Schedule.sum_tier f

theorem classProbability_pos (i : Fin M) : 0 < classProbability i := by
  unfold classProbability Chain18Compact.probability
  exact div_pos (by exact_mod_cast (Chain18Compact.aliases_valid (LongChain91Schedule.tier i)).1)
    (by norm_num [Chain18Compact.R])

theorem classProbability_sum :
    (∑ i : Fin M, classProbability i) =
      (Chain18Compact.acceptedAliases : ℝ) / (Chain18Compact.R : ℝ) := by
  rw [show (∑ i : Fin M, classProbability i) =
      ∑ j : Tier, (Chain18Compact.classes j : ℝ) * Chain18Compact.probability j by
    exact sum_tier Chain18Compact.probability]
  unfold Chain18Compact.acceptedAliases Chain18Compact.probability
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem classProbability_sum_lt_one :
    (∑ i : Fin M, classProbability i) < 1 := by
  rw [classProbability_sum]
  exact (div_lt_one (by norm_num [Chain18Compact.R] : (0 : ℝ) < Chain18Compact.R)).2
    (by exact_mod_cast Chain18Compact.acceptedAliases_bounds.2)

theorem referenceWeight_eq (i : Fin M) :
    referenceWeight i = classProbability i * Chain18Compact.actualKernel (LongChain91Schedule.tier i) := rfl

theorem referenceWeight_nonneg (i : Fin M) : 0 ≤ referenceWeight i := by
  exact Chain18Compact.winner_nonneg Chain18Compact.actualKernel_bounds (LongChain91Schedule.tier i)

/-- The exact probability/score data consumed by the generic weighted-row
martingale and cache lemmas. -/
def securityWeights : WeightedRow.Weights (Fin M) where
  p := classProbability
  g := referenceWeight
  p_pos := fun i => by exact classProbability_pos i
  g_nonneg := fun i => by exact referenceWeight_nonneg i
  mass_le_one := classProbability_sum_lt_one.le

@[simp] theorem securityWeights_p (i : Fin M) :
    securityWeights.p i = classProbability i := rfl

@[simp] theorem securityWeights_g (i : Fin M) :
    securityWeights.g i = referenceWeight i := rfl

theorem weight_ratio (i : Fin M) :
    referenceWeight i / classProbability i = Chain18Compact.actualKernel (LongChain91Schedule.tier i) := by
  rw [referenceWeight_eq]
  exact mul_div_cancel_left₀ _ (classProbability_pos i).ne'

theorem weight_ratio_lt (i : Fin M) :
    referenceWeight i / classProbability i < (4 / 5) * (Chain18Compact.L : ℝ) := by
  rw [weight_ratio]
  exact Chain18Compact.actual_w_lt (LongChain91Schedule.tier i)

/-- Compatibility envelope used by the accepted weighted hazard algebra. -/
theorem weight_ratio_le (i : Fin M) :
    referenceWeight i / classProbability i ≤ (Chain18Compact.L : ℝ) := by
  exact (weight_ratio_lt i).le.trans (by norm_num [Chain18Compact.L])

theorem referenceWeight_lt (i : Fin M) :
    referenceWeight i < (17 / 40) * (Chain18Compact.L : ℝ) * Chain18Compact.kappa := by
  exact Chain18Compact.actual_g_lt (LongChain91Schedule.tier i)

/-- Compatibility envelope used by the accepted score concentration lemmas. -/
theorem referenceWeight_le (i : Fin M) :
    referenceWeight i ≤ (Chain18Compact.L : ℝ) * Chain18Compact.kappa / 2 := by
  exact (referenceWeight_lt i).le.trans (by
    norm_num [Chain18Compact.L, Chain18Compact.kappa])

/-! A common multiplicative envelope for empirical prefix deficits.  The
reference endpoints stay above `9999/10000`; this deliberately simple rational
floor leaves enough room for the same `99/98` factor as the accepted proof. -/

def minSurvival : ℝ := 9999 / 10000
def empiricalDelta : ℝ := 1 / (100 * (Chain18Compact.L : ℝ))

theorem accepted_fraction_lt :
    (Chain18Compact.acceptedAliases : ℝ) / (Chain18Compact.R : ℝ) < 1 / 10000 := by
  rw [Chain18Compact.acceptedAliases_exact]
  norm_num [Chain18Compact.R]

theorem minSurvival_le_rejection :
    minSurvival ≤
      1 - (Chain18Compact.acceptedAliases : ℝ) / (Chain18Compact.R : ℝ) := by
  unfold minSurvival
  linarith [accepted_fraction_lt]

theorem minSurvival_le_lowerEndpoint (j : Tier) :
    minSurvival ≤
      Chain18Compact.survival
        (Chain18Compact.prefixMass j + Chain18Compact.tierMass j) := by
  have hmass := Chain18Compact.prefix_add_mass_le j
  have hcast :
      ((Chain18Compact.prefixMass j + Chain18Compact.tierMass j : ℕ) : ℝ) ≤
        (Chain18Compact.acceptedAliases : ℝ) := by
    exact_mod_cast hmass
  have hR : (0 : ℝ) < Chain18Compact.R := by norm_num [Chain18Compact.R]
  have hdiv := div_le_div_of_nonneg_right hcast hR.le
  unfold Chain18Compact.survival
  linarith [minSurvival_le_rejection]

theorem minSurvival_le_upperEndpoint (j : Tier) :
    minSurvival ≤ Chain18Compact.survival (Chain18Compact.prefixMass j) := by
  have hp : Chain18Compact.prefixMass j ≤
      Chain18Compact.prefixMass j + Chain18Compact.tierMass j := Nat.le_add_right _ _
  have hcast : (Chain18Compact.prefixMass j : ℝ) ≤
      (Chain18Compact.prefixMass j + Chain18Compact.tierMass j : ℕ) := by
    exact_mod_cast hp
  have hR : (0 : ℝ) < Chain18Compact.R := by norm_num [Chain18Compact.R]
  have hdiv := div_le_div_of_nonneg_right hcast hR.le
  have hl := minSurvival_le_lowerEndpoint j
  unfold Chain18Compact.survival at hl
  unfold Chain18Compact.survival at hdiv ⊢
  linarith

theorem commonEnvelope :
    (1 + empiricalDelta / minSurvival) ^ (Chain18Compact.L - 1) ≤ 99 / 98 := by
  let x : ℝ := empiricalDelta / minSurvival
  have hx : 0 ≤ x := by
    norm_num [x, empiricalDelta, minSurvival, Chain18Compact.L]
  have h := WeightedReference.pow_times_linear_le_one x hx (Chain18Compact.L - 1)
  have hd : 0 < 1 - ((Chain18Compact.L - 1 : ℕ) : ℝ) * x := by
    norm_num [x, empiricalDelta, minSurvival, Chain18Compact.L]
  have hb : 1 / (1 - ((Chain18Compact.L - 1 : ℕ) : ℝ) * x) ≤
      (99 : ℝ) / 98 := by
    norm_num [x, empiricalDelta, minSurvival, Chain18Compact.L]
  exact ((le_div_iff₀ hd).2 h).trans hb

/-- Pointwise bridge from a `1/(100L)` empirical prefix deficit to the true
class kernel.  This is ready for `WeightedCompletion.replay_kernel_bound`. -/
theorem empirical_kernel_le (i : Fin M) (Ah Bh : ℝ)
    (ha : 0 ≤ Ah) (hb : 0 ≤ Bh)
    (hA : Ah ≤ Chain18Compact.survival
      (Chain18Compact.prefixMass (LongChain91Schedule.tier i)) + empiricalDelta)
    (hB : Bh ≤ Chain18Compact.survival
      (Chain18Compact.prefixMass (LongChain91Schedule.tier i) +
        Chain18Compact.tierMass (LongChain91Schedule.tier i)) + empiricalDelta) :
    WeightedReplacement.kernel Chain18Compact.L Ah Bh ≤
      (99 / 98) * (referenceWeight i / classProbability i) := by
  let j := LongChain91Schedule.tier i
  have h := WeightedReplacement.kernel_additive_envelope Chain18Compact.L
    ha hb (show 0 < minSurvival by norm_num [minSurvival])
    (show 0 ≤ empiricalDelta by
      norm_num [empiricalDelta, Chain18Compact.L])
    (minSurvival_le_upperEndpoint j) (minSurvival_le_lowerEndpoint j) hA hB
  calc
    WeightedReplacement.kernel Chain18Compact.L Ah Bh ≤
        (1 + empiricalDelta / minSurvival) ^ (Chain18Compact.L - 1) *
          WeightedReplacement.kernel Chain18Compact.L
            (Chain18Compact.survival (Chain18Compact.prefixMass j))
            (Chain18Compact.survival
              (Chain18Compact.prefixMass j + Chain18Compact.tierMass j)) := h
    _ ≤ (99 / 98) *
          WeightedReplacement.kernel Chain18Compact.L
            (Chain18Compact.survival (Chain18Compact.prefixMass j))
            (Chain18Compact.survival
              (Chain18Compact.prefixMass j + Chain18Compact.tierMass j)) :=
      mul_le_mul_of_nonneg_right commonEnvelope (Chain18Compact.actualKernel_nonneg j)
    _ = (99 / 98) * (referenceWeight i / classProbability i) := by
      rw [weight_ratio]
      rfl

theorem securityWeights_mean_eq :
    securityWeights.mean = Chain18Compact.hValue Chain18Compact.actualKernel := by
  change (∑ i : Fin M, classProbability i * referenceWeight i) = _
  unfold referenceWeight classProbability
  rw [sum_tier (fun j =>
    Chain18Compact.probability j *
      Chain18Compact.winner Chain18Compact.actualKernel j)]
  unfold Chain18Compact.hValue Chain18Compact.winner
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem securityWeights_mean_lt :
    securityWeights.mean < (967 / 1000) * Chain18Compact.kappa := by
  rw [securityWeights_mean_eq]
  exact Chain18Compact.actual_h_lt

theorem securityWeights_mean :
    securityWeights.mean ≤ (967 / 1000) * Chain18Compact.kappa :=
  securityWeights_mean_lt.le

theorem card_decode_none :
    (Finset.univ.filter fun b : BitVec 256 => LongChain91Schedule.decode b = none).card =
      2^256 - Chain18Compact.acceptedAliases := by
  have h := WeightedSampling.Availability.card_option_none LongChain91Schedule.decode Chain18Compact.acceptedAliases
    LongChain91Schedule.accepted_count
  have hs : (Finset.univ.filter fun b : BitVec 256 => LongChain91Schedule.decode b = none) =
      Finset.univ.filter fun b : BitVec 256 => (LongChain91Schedule.decode b).isNone := by
    apply Finset.filter_congr
    intro b hb
    cases LongChain91Schedule.decode b <;> simp
  exact (congrArg Finset.card hs).trans h

/-- Exact full decoder law, including its rejection atom. -/
theorem decoder_law (x : Option (Fin M)) :
    ((Finset.univ.filter fun b : BitVec 256 => LongChain91Schedule.decode b = x).card : ℝ) /
        Fintype.card (BitVec 256) = securityWeights.classMass x := by
  cases x with
  | none =>
      rw [card_decode_none, Fintype.card_bitVec]
      change ((2^256 - Chain18Compact.acceptedAliases : ℕ) : ℝ) / (2^256 : ℕ) =
        1 - ∑ i : Fin M, classProbability i
      rw [classProbability_sum]
      have ha : Chain18Compact.acceptedAliases ≤ 2^256 := Chain18Compact.acceptedAliases_bounds.2.le
      rw [Nat.cast_sub ha]
      norm_num [Chain18Compact.R]
      ring
  | some i =>
      change ((Finset.univ.filter fun b : BitVec 256 => LongChain91Schedule.decode b = some i).card : ℝ) /
          Fintype.card (BitVec 256) = classProbability i
      rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
      exact class_probability_real i

/-! The following natural endpoint facts are table facts, checked in the
kernel.  They let the indexed reference weights telescope without replacing
the actual kernels by their rounded certificates. -/

/-- The positive post-sign correction expressed directly on concrete classes. -/
def postSignPositive : ℝ :=
  ∑ i : Fin M, referenceWeight i *
    (Chain18Compact.positiveFactor (LongChain91Schedule.tier i) : ℝ) / (2 * (Chain18Compact.remainingAliases : ℝ))

theorem postSignPositive_eq : postSignPositive = Chain18Compact.positiveValue Chain18Compact.actualKernel := by
  unfold postSignPositive referenceWeight
  rw [sum_tier (fun j =>
    Chain18Compact.winner Chain18Compact.actualKernel j *
      (Chain18Compact.positiveFactor j : ℝ) /
        (2 * (Chain18Compact.remainingAliases : ℝ)))]
  unfold Chain18Compact.positiveValue Chain18Compact.winner Chain18Compact.probability
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem postSignPositive_lt : postSignPositive < 47 / 100 := by
  rw [postSignPositive_eq]
  exact Chain18Compact.actual_positive_lt

/-! `postSignPositive` is normalized by `kappa`.  The following definitions
recover the literal positive-part score used by the signed-prefix modules. -/

theorem remainingAliases_pos : 0 < Chain18Compact.remainingAliases := by
  unfold Chain18Compact.remainingAliases
  exact Nat.sub_pos_of_lt Chain18Compact.acceptedAliases_bounds.2

theorem remainingAliases_le_scaled (j : Tier) :
    Chain18Compact.remainingAliases ≤ Chain18Compact.aliases j * 2^128 := by
  revert j
  decide +kernel

def excess (i : Fin M) : ℝ :=
  max (classProbability i /
    (1 - ∑ j : Fin M, classProbability j) - Chain18Compact.kappa / 2) 0

theorem excess_raw_eq (i : Fin M) :
    classProbability i / (1 - ∑ j : Fin M, classProbability j) -
        Chain18Compact.kappa / 2 =
      Chain18Compact.kappa *
        (Chain18Compact.positiveFactor (LongChain91Schedule.tier i) : ℝ) /
          (2 * (Chain18Compact.remainingAliases : ℝ)) := by
  rw [classProbability_sum]
  have hacc : Chain18Compact.acceptedAliases ≤ Chain18Compact.R :=
    Chain18Compact.acceptedAliases_bounds.2.le
  have hscale := remainingAliases_le_scaled (LongChain91Schedule.tier i)
  have hrem : (Chain18Compact.remainingAliases : ℝ) ≠ 0 := by
    exact_mod_cast (remainingAliases_pos.ne')
  have hposcast :
      (Chain18Compact.positiveFactor (LongChain91Schedule.tier i) : ℝ) =
        (Chain18Compact.aliases (LongChain91Schedule.tier i) : ℝ) * 2^128 -
          (Chain18Compact.remainingAliases : ℝ) := by
    unfold Chain18Compact.positiveFactor
    rw [Nat.cast_sub hscale]
    push_cast
    norm_num
  have hremcast :
      (Chain18Compact.remainingAliases : ℝ) =
        (Chain18Compact.R : ℝ) - (Chain18Compact.acceptedAliases : ℝ) := by
    unfold Chain18Compact.remainingAliases
    rw [Nat.cast_sub hacc]
  have hrejection :
      1 - (Chain18Compact.acceptedAliases : ℝ) / (Chain18Compact.R : ℝ) =
        (Chain18Compact.remainingAliases : ℝ) / (Chain18Compact.R : ℝ) := by
    rw [hremcast]
    have hR : (Chain18Compact.R : ℝ) ≠ 0 := by
      norm_num [Chain18Compact.R]
    field_simp [hR]
  unfold classProbability Chain18Compact.probability Chain18Compact.kappa
  rw [hposcast, hrejection]
  norm_num [Chain18Compact.R] at hrem ⊢
  field_simp [hrem]
  ring

theorem excess_eq (i : Fin M) :
    excess i = Chain18Compact.kappa *
      (Chain18Compact.positiveFactor (LongChain91Schedule.tier i) : ℝ) /
        (2 * (Chain18Compact.remainingAliases : ℝ)) := by
  unfold excess
  rw [excess_raw_eq]
  apply max_eq_left
  exact div_nonneg
    (mul_nonneg (show 0 ≤ Chain18Compact.kappa by
      unfold Chain18Compact.kappa
      positivity) (Nat.cast_nonneg _))
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _))

def postSignExcess : ℝ :=
  ∑ i : Fin M, referenceWeight i * excess i

theorem postSignExcess_eq :
    postSignExcess = Chain18Compact.kappa * postSignPositive := by
  unfold postSignExcess postSignPositive
  simp_rw [excess_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem postSignExcess_lt :
    postSignExcess < (47 / 100) * Chain18Compact.kappa := by
  rw [postSignExcess_eq]
  have hk : 0 < Chain18Compact.kappa := by
    unfold Chain18Compact.kappa
    positivity
  have h := mul_lt_mul_of_pos_left postSignPositive_lt hk
  nlinarith

end
end OptimalOTS.WeightedConstruction.LongChain91Security
