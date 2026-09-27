import Submissions.UpperCompressions.LongChain91TailArithmetic
import Submissions.UpperCompressions.LongChain91CollisionCap

/-!
# Actual stopped collision bound for the cost-91 long-chain schedule

This file instantiates the equality-collision stopped-process theorem with the
concrete long-chain decoder, row domain, score envelope, and occupancy cap.
It also transfers the simultaneous completed-table occupancy tail back to an
arbitrary adaptive execution from a fresh length-342 cache.
-/

noncomputable section

set_option maxRecDepth 100000

open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal

namespace OptimalOTS.WeightedConstruction.LongChain91StoppedCollision

open LongChain91Security LongChain91Occupancy LongChain91CollisionCap

/-- The common pointwise score envelope used by the collision martingale. -/
def collisionScale : ℝ :=
  (Chain18Compact.L : ℝ) * Chain18Compact.kappa / 2

theorem collisionScale_nonneg : 0 ≤ collisionScale := by
  unfold collisionScale Chain18Compact.kappa
  positivity

/-- The stopped self-collision event on one message row. -/
def collisionHit (m : Message) (a v : ℝ) :
    ℕ → hashSpec.QueryCache → Prop :=
  fun _ cache =>
    a ≤ EqualityCollisionCache91.cacheXz securityWeights
      (WideDomains.rowDomain m) LongChain91Empirical.cacheDecode
      collisionScale cache ∧
    EqualityCollisionCache91.cacheXw (WideDomains.rowDomain m)
      collisionJumpBound collisionScale cache ≤ v

/-- Stop before a decoder class in the selected row exceeds its certified
occupancy cap. -/
def occupancyKill (m : Message) : ℕ → hashSpec.QueryCache → Prop :=
  fun _ cache =>
    ¬ EqualityCollisionCache91.OccupancyGood (WideDomains.rowDomain m)
      LongChain91Empirical.cacheDecode cap cache

/-- Concrete specialization of the actual-cache maximal Freedman theorem.
The adversarial program is otherwise arbitrary; only the length-342 part of
the initial public cache must be fresh. -/
theorem actual_stopped_collision_freedman {α : Type}
    (m : Message) (oa : OracleComp Spec α)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    Pr[fun out => out.2.status = WeightedFirstHit.Status.hit |
      (simulateQ (WeightedOracleExecution.stoppedImpl OptimalOTS.oracleImpl
        (collisionHit m a v) (occupancyKill m)) oa).run
          (WeightedFirstHit.classify (collisionHit m a v) (occupancyKill m)
            0 initial)] ≤
      ENNReal.ofReal
        (Real.exp (-a ^ 2 / (2 * (v + collisionJumpBound * a / 3)))) := by
  obtain ⟨hr0, hk0⟩ := LongChain91Empirical.row_initial m initial hfresh
  have hg : ∀ i, securityWeights.g i ≤ collisionScale := by
    intro i
    simpa only [securityWeights_g, collisionScale] using referenceWeight_le i
  have h := EqualityCollisionCache91.actual_stopped_x_freedman
    securityWeights
    (WideDomains.rowDomain m) WideDomains.indexDomain
    (WideDomains.row_subset m)
    LongChain91Empirical.cacheDecode LongChain91Empirical.cache_decoder_law
    cap collisionScale collisionJumpBound collisionScale_nonneg hg
    collisionJumpBound_nonneg collision_cap oa initial hr0 hk0 a v ha hv
  have hhit : collisionHit m a v =
      (fun (_ : ℕ) (cache : hashSpec.QueryCache) =>
        a ≤ EqualityCollisionCache91.cacheXz securityWeights
            (WideDomains.rowDomain m) LongChain91Empirical.cacheDecode
            collisionScale cache ∧
          EqualityCollisionCache91.cacheXw (WideDomains.rowDomain m)
            collisionJumpBound collisionScale cache ≤ v) := by
    funext n cache
    rfl
  have hkill : occupancyKill m =
      (fun (_ : ℕ) (cache : hashSpec.QueryCache) =>
        ¬ EqualityCollisionCache91.OccupancyGood (WideDomains.rowDomain m)
          LongChain91Empirical.cacheDecode cap cache) := by
    funext n cache
    rfl
  rw [hhit, hkill]
  exact h

/-! ## Completed-table tail and actual-cache kill adapters -/

/-- The simultaneous completed-table failure event, kept opaque so posterior
completion arguments do not elaborate the large row predicate repeatedly. -/
def anyRowOverfull
    (table : BitVec (msgBits + 86) → BitVec hashBits) : Prop :=
  ∃ s : Message × Fin LongChain91Security.M, rowOverfull s table

private theorem anyRowOverfull_iff
    (table : BitVec (msgBits + 86) → BitVec hashBits) :
    anyRowOverfull table ↔
      ∃ s : Message × Fin LongChain91Security.M, rowOverfull s table :=
  Iff.rfl

private theorem completed_failure_indicator_eq
    (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits) :
    (if ¬ CompletedOccupancyGood cache g then (1 : ℝ≥0∞) else 0) =
      (if anyRowOverfull
        (WeightedReplacement.completedTable (msgBits + 86) cache g)
        then 1 else 0) := by
  unfold CompletedOccupancyGood anyRowOverfull
  by_cases h : ∃ s : Message × Fin LongChain91Security.M,
      rowOverfull s
        (WeightedReplacement.completedTable (msgBits + 86) cache g) <;>
    simp only [h, not_true_eq_false, not_false_eq_true, if_false, if_true]

/-- A single completed table is simultaneously occupancy-good for every
message row except with the unconditional `2^-334` tail.  This remains true
after an arbitrary adaptive public computation, averaged over its posterior
completion. -/
theorem completed_occupancy_failure_probability {α : Type}
    (oa : OracleComp Spec α) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    E (run oa initial) (fun out =>
      E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
        if ¬ CompletedOccupancyGood out.2 g then 1 else 0)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  calc
    _ = E (run oa initial) (fun out =>
        E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
          if anyRowOverfull
            (WeightedReplacement.completedTable (msgBits + 86) out.2 g)
          then 1 else 0)) := by
      apply congrArg (E (run oa initial))
      funext out
      apply congrArg (E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)))
      funext g
      exact completed_failure_indicator_eq out.2 g
    _ ≤ E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
        if anyRowOverfull g then 1 else 0) :=
      WeightedReplacement.completed_bad_probability_le
        (msgBits + 86) oa initial (fun x => hfresh ⟨342, x⟩ rfl)
        anyRowOverfull
    _ ≤ E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
        if ∃ s : Message × Fin LongChain91Security.M,
          rowOverfull s g then 1 else 0) := by
      apply E_mono
      intro g
      by_cases h : anyRowOverfull g
      · rw [if_pos h, if_pos ((anyRowOverfull_iff g).mp h)]
      · rw [if_neg h, if_neg (fun hex => h ((anyRowOverfull_iff g).mpr hex))]
    _ ≤ _ := full_table_overfull_probability

/-- The real cache is occupancy-good on every message row whenever one of its
posterior completions is simultaneously good. -/
def AllRowsOccupancyGood (cache : hashSpec.QueryCache) : Prop :=
  ∀ m : Message,
    EqualityCollisionCache91.OccupancyGood (WideDomains.rowDomain m)
      LongChain91Empirical.cacheDecode cap cache

theorem completed_allRowsOccupancyGood
    (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (hgood : CompletedOccupancyGood cache g) :
    AllRowsOccupancyGood cache := by
  intro m
  exact completed_occupancyGood cache g hgood m

/-- Strong unconditional adapter: after any adaptive computation from a fresh
length-342 cache, the probability that *some* message row violates the actual
cache occupancy cap is at most `2^-334`. -/
theorem actual_allRows_occupancy_failure_probability {α : Type}
    (oa : OracleComp Spec α) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    E (run oa initial) (fun out =>
      if ¬ AllRowsOccupancyGood out.2 then 1 else 0) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  calc
    _ ≤ E (run oa initial) (fun out =>
        E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
          if ¬ CompletedOccupancyGood out.2 g then 1 else 0)) := by
      apply E_mono
      intro out
      by_cases hrows : AllRowsOccupancyGood out.2
      · simp only [hrows, not_true_eq_false, if_false]
        exact bot_le
      · have hbad : ∀ g : BitVec (msgBits + 86) → BitVec hashBits,
            ¬ CompletedOccupancyGood out.2 g := by
          intro g hcompletion
          exact hrows (completed_allRowsOccupancyGood out.2 g hcompletion)
        have hfun :
            (fun g : BitVec (msgBits + 86) → BitVec hashBits =>
              if ¬ CompletedOccupancyGood out.2 g
              then (1 : ℝ≥0∞) else 0) =
            (fun _ => (1 : ℝ≥0∞)) := by
          funext g
          rw [if_pos (hbad g)]
        rw [if_pos hrows, hfun,
          WeightedReplacement.E_uniform_constant]
    _ ≤ _ := completed_occupancy_failure_probability oa initial hfresh

end OptimalOTS.WeightedConstruction.LongChain91StoppedCollision

/-!
# Equality-collision arithmetic for the cost-91 large branch

The small stopped-payoff endpoint reaches its `65/64` factor at the split
`B <= 2^86/64`.  This file records the exact constants needed on the other
side of that split.  In particular, the finite schedule already certifies the
two square moments used by the equality-only variance clock.  With a
`kappa*B/100` deviation and a `61/20` diagonal-clock envelope, the resulting
Freedman exponent is at least `500`.

No probabilistic clock assertion is made here: the execution proof must still
establish the stated clock envelope.  The lemmas below isolate all numerical
and finite-schedule obligations from that proof.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91CollisionArithmetic

open scoped Classical BigOperators ENNReal
open LongChain91Security LongChain91CollisionCap LongChain91StoppedCollision

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev M := LongChain91Security.M
abbrev securityWeights := LongChain91Security.securityWeights
abbrev kappa : ℝ := Chain18Compact.kappa
abbrev C : ℝ := LongChain91BudgetArithmetic.C

/-- Mean drift after tightening only the reference row-score event from a
`1/100` allowance to a `1/1000` allowance. -/
def tightAlpha : ℝ := (968 / 1000) * kappa

/-- Number of nonce positions in one message row. -/
def N : ℝ := (2 : ℝ)^86

/-- Upper bound for `sum_i g_i^2`, certified by the compact schedule. -/
def diagonalRate : ℝ :=
  (8 / 25) * (Chain18Compact.L : ℝ) * kappa

/-- Upper bound for `sum_i p_i*g_i^2`, certified by the compact schedule. -/
def freshSquareRate : ℝ :=
  (1 / 4) * (Chain18Compact.L : ℝ) * kappa^2

/-- Uniform absolute jump bound for the equality replay hazard. -/
def hazardJumpBound : ℝ :=
  collisionScale + 2 * (Chain18Compact.L : ℝ) / N

/-- Deviation allocated to the large replay-hazard martingale. -/
def largeDeviation (B : ℝ) : ℝ := kappa * B / 100

/-- Variance envelope after bounding the diagonal and forward clocks by
`3/2 * diagonalRate * B` each, the self-collision excess by
`diagonalRate * B / 20`, and using `r^2 <= B*N`. -/
def hazardVariance (B : ℝ) : ℝ :=
  3 * freshSquareRate * B +
    (183 / 20) * diagonalRate * B^2 / N^2 +
    3 * collisionScale^2 * B^2 / N

theorem diagonalRate_pos : 0 < diagonalRate := by
  unfold diagonalRate
  have hL : 0 < (Chain18Compact.L : ℝ) := by
    norm_num [Chain18Compact.L]
  exact mul_pos (mul_pos (by norm_num) hL)
    LongChain91BudgetArithmetic.kappa_pos

theorem freshSquareRate_pos : 0 < freshSquareRate := by
  unfold freshSquareRate
  have hL : 0 < (Chain18Compact.L : ℝ) := by
    norm_num [Chain18Compact.L]
  exact mul_pos (mul_pos (by norm_num) hL)
    (sq_pos_of_pos LongChain91BudgetArithmetic.kappa_pos)

theorem hazardJumpBound_pos : 0 < hazardJumpBound := by
  unfold hazardJumpBound
  have hL : 0 < (Chain18Compact.L : ℝ) := by
    norm_num [Chain18Compact.L]
  have hc : 0 < collisionScale := by
    unfold collisionScale
    exact div_pos (mul_pos hL LongChain91BudgetArithmetic.kappa_pos)
      (by norm_num)
  have hN : 0 < N := by unfold N; positivity
  exact add_pos hc (div_pos (mul_pos (by norm_num) hL) hN)

theorem tightAlpha_nonneg : 0 ≤ tightAlpha := by
  unfold tightAlpha kappa Chain18Compact.kappa
  positivity

theorem tight_mean_margin_le :
    securityWeights.mean + kappa / 1000 ≤ tightAlpha := by
  calc
    securityWeights.mean + kappa / 1000 ≤
        (967 / 1000) * kappa + kappa / 1000 :=
      add_le_add LongChain91Security.securityWeights_mean le_rfl
    _ = tightAlpha := by
      unfold tightAlpha
      ring

/-! ## Exact identification of the two certified moments -/

theorem diagonalMean_eq :
    securityWeights.diagonalMean =
      Chain18Compact.cValue Chain18Compact.actualKernel := by
  unfold WeightedRow.Weights.diagonalMean Chain18Compact.cValue
  change
    (∑ i : Fin M,
      (Chain18Compact.winner Chain18Compact.actualKernel
        (LongChain91Schedule.tier i))^2) =
      ∑ j : Chain18Compact.Tier,
        (Chain18Compact.classes j : ℝ) *
          (Chain18Compact.winner Chain18Compact.actualKernel j)^2
  exact LongChain91Security.sum_tier
    (fun j => (Chain18Compact.winner Chain18Compact.actualKernel j)^2)

theorem freshSquareMass_eq :
    securityWeights.freshSquareMass =
      Chain18Compact.aValue Chain18Compact.actualKernel := by
  unfold WeightedRow.Weights.freshSquareMass
  change
    (∑ i : Fin M,
      Chain18Compact.probability (LongChain91Schedule.tier i) *
        (Chain18Compact.winner Chain18Compact.actualKernel
          (LongChain91Schedule.tier i))^2) =
      Chain18Compact.aValue Chain18Compact.actualKernel
  calc
    _ = ∑ j : Chain18Compact.Tier,
        (Chain18Compact.classes j : ℝ) *
          (Chain18Compact.probability j *
            (Chain18Compact.winner Chain18Compact.actualKernel j)^2) :=
      LongChain91Security.sum_tier
        (fun j => Chain18Compact.probability j *
          (Chain18Compact.winner Chain18Compact.actualKernel j)^2)
    _ = Chain18Compact.aValue Chain18Compact.actualKernel := by
      unfold Chain18Compact.aValue
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem diagonalMean_lt : securityWeights.diagonalMean < diagonalRate := by
  rw [diagonalMean_eq]
  exact Chain18Compact.actual_c_lt

theorem freshSquareMass_lt :
    securityWeights.freshSquareMass < freshSquareRate := by
  rw [freshSquareMass_eq]
  exact Chain18Compact.actual_a_lt

/-- A single diagonal-clock increment has the checked pointwise bound. -/
theorem collisionMass_lt (i : Fin M) :
    securityWeights.collisionMass i <
      (13 / 40) * (Chain18Compact.L : ℝ)^2 * kappa := by
  rw [LongChain91CollisionCap.security_collisionMass_eq]
  exact Chain18Compact.actual_diagonal_lt (LongChain91Schedule.tier i)

/-! ## Large-split exponent -/

theorem hazardVariance_pos {B : ℝ} (hB : 0 < B) :
    0 < hazardVariance B := by
  unfold hazardVariance
  have hN : 0 < N := by unfold N; positivity
  have hd := diagonalRate_pos
  have hf := freshSquareRate_pos
  have hg := collisionScale_nonneg
  positivity

/-- The exact rational check behind the new split.  The linear-in-`B` terms
are maximized at `B = N/64`; all remaining terms are quadratic. -/
theorem large_hazard_exponent (B : ℝ) (hB : N / 64 ≤ B) :
    (500 : ℝ) ≤
      (largeDeviation B)^2 /
        (2 * (hazardVariance B +
          hazardJumpBound * largeDeviation B / 3)) := by
  have hN : 0 < N := by unfold N; positivity
  have hBpos : 0 < B := lt_of_lt_of_le (div_pos hN (by norm_num)) hB
  have hden :
      0 < 2 * (hazardVariance B +
        hazardJumpBound * largeDeviation B / 3) := by
    have hv := hazardVariance_pos hBpos
    have hj := hazardJumpBound_pos
    have ha : 0 < largeDeviation B := by
      unfold largeDeviation kappa Chain18Compact.kappa
      positivity
    positivity
  apply (le_div_iff₀ hden).2
  have hlinear :
      500 * 2 *
        (3 * freshSquareRate +
          (183 / 20) * diagonalRate * B / N^2 +
          3 * collisionScale^2 * B / N +
          hazardJumpBound * (kappa / 100) / 3) ≤
        (kappa / 100)^2 * B := by
    norm_num [N, diagonalRate, freshSquareRate, hazardJumpBound,
      collisionScale, kappa, Chain18Compact.L, Chain18Compact.kappa] at hB ⊢
    linarith
  have hm := mul_le_mul_of_nonneg_right hlinear hBpos.le
  calc
    500 * (2 * (hazardVariance B +
        hazardJumpBound * largeDeviation B / 3)) =
        (500 * 2 *
          (3 * freshSquareRate +
            (183 / 20) * diagonalRate * B / N^2 +
            3 * collisionScale^2 * B / N +
            hazardJumpBound * (kappa / 100) / 3)) * B := by
      unfold hazardVariance largeDeviation
      ring
    _ ≤ ((kappa / 100)^2 * B) * B := hm
    _ = (largeDeviation B)^2 := by
      unfold largeDeviation
      ring

/-- Coarse dyadic form convenient for a finite union over all messages. -/
theorem exp_neg_500 :
    Real.exp (-(500 : ℝ)) ≤ ((2 : ℝ)^500)⁻¹ := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ)^500 ≤ (Real.exp 1)^500 :=
    pow_le_pow_left₀ (by norm_num) he 500
  rw [← Real.exp_nat_mul, mul_one] at hp
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hp

theorem message_union_margin :
    (2 : ℝ)^256 * Real.exp (-(500 : ℝ)) ≤ ((2 : ℝ)^244)⁻¹ := by
  have h := mul_le_mul_of_nonneg_left exp_neg_500
    (show (0 : ℝ) ≤ 2^256 by positivity)
  apply h.trans_eq
  rw [show (500 : ℕ) = 256 + 244 by omega, pow_add]
  field_simp

/-! ## Scalar and negligible-tail closure -/

/-- The relaxed large deviation still leaves a visible strict margin below
the target security rate. -/
theorem large_coefficient_tight_identity (K : ℝ) :
    C * tightAlpha * K + C * (kappa * K / 100) + kappa * K / 1000 =
      (2423 / 2450) * kappa * K := by
  unfold C tightAlpha LongChain91BudgetArithmetic.C
  ring

theorem authRate_le_C_tightAlpha : kappa / 2 ≤ C * tightAlpha := by
  unfold C tightAlpha LongChain91BudgetArithmetic.C
  have hk := LongChain91BudgetArithmetic.kappa_pos.le
  nlinarith

theorem postRate_le_C_tightAlpha :
    LongChain91BudgetArithmetic.postRate ≤ C * tightAlpha := by
  change kappa / 2 + (99 / 98) * ((471 / 1000) * kappa) ≤
    (99 / 98) * ((968 / 1000) * kappa)
  have hk := LongChain91BudgetArithmetic.kappa_pos.le
  change 0 ≤ kappa at hk
  nlinarith

/-- Four `2^-244` collision/concentration tails, the common occupancy tail,
and all row-completion failures still fit inside the existing `1/1000`
exception reserve throughout the large branch. -/
theorem large_exception_margin (B : ℝ) (hB : N / 64 ≤ B)
    (hcap : B ≤ (2 : ℝ)^127) :
    4 * ((2 : ℝ)^244)⁻¹ + ((2 : ℝ)^334)⁻¹ +
        (1 + B) * ((2 : ℝ)^760)⁻¹ ≤
      kappa * B / 1000 := by
  have hinv (n k : ℕ) (h : k ≤ n) :
      ((2 : ℝ)^n)⁻¹ ≤ ((2 : ℝ)^k)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) h
  have hcollision := hinv 244 200 (by decide)
  have hocc := hinv 334 200 (by decide)
  have htab := hinv 760 384 (by decide)
  have hp : 0 ≤ 1 + B := by
    have hN : 0 < N := by unfold N; positivity
    have : 0 < B := lt_of_lt_of_le (div_pos hN (by norm_num)) hB
    linarith
  have hb : 1 + B ≤ (2 : ℝ)^128 := by linarith
  have hterm := mul_le_mul htab hb hp
    (show (0 : ℝ) ≤ ((2 : ℝ)^384)⁻¹ by positivity)
  have he : ((2 : ℝ)^384)⁻¹ * (2 : ℝ)^128 =
      ((2 : ℝ)^256)⁻¹ := by
    rw [show (384 : ℕ) = 256 + 128 by omega, pow_add]
    field_simp
  rw [he, mul_comm _ (1 + B)] at hterm
  have hterm' :
      (1 + B) * ((2 : ℝ)^760)⁻¹ ≤ ((2 : ℝ)^200)⁻¹ :=
    hterm.trans (hinv 256 200 (by decide))
  have hsmall : 6 * ((2 : ℝ)^200)⁻¹ ≤
      kappa * (N / 64) / 1000 := by
    norm_num [N, kappa, Chain18Compact.kappa]
  have hrate := mul_le_mul_of_nonneg_left hB
    (show 0 ≤ kappa / 1000 by
      unfold kappa Chain18Compact.kappa
      positivity)
  calc
    _ ≤ 4 * ((2 : ℝ)^200)⁻¹ + ((2 : ℝ)^200)⁻¹ +
          ((2 : ℝ)^200)⁻¹ :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hcollision (by norm_num)) hocc) hterm'
    _ = 6 * ((2 : ℝ)^200)⁻¹ := by ring
    _ ≤ kappa * (N / 64) / 1000 := hsmall
    _ ≤ kappa * B / 1000 := by
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hrate

end OptimalOTS.WeightedConstruction.LongChain91CollisionArithmetic
