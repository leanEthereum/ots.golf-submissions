import Submissions.UpperCompressions.LongChain91DiagonalClock

/-!
# Large-row equality hazard for the cost-91 construction

This module carries the clipped replay hazard on the real memoized oracle
cache.  Its variance is controlled by three concrete clocks: the global
diagonal clock, the global forward clock, and the selected row's equality
self-collision clock.  The first two are dominated by `Dglobal`; the last is
the stopped process from `LongChain91StoppedCollision`.

The resulting stopped theorem has deviation `kappa * B / 100`, variance
`LongChain91CollisionArithmetic.hazardVariance B`, and the checked exponent
`500` throughout the large regime `2^86 / 64 <= B`.
-/

noncomputable section

open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal

namespace OptimalOTS.WeightedConstruction.LongChain91LargeHazard

open WeightedCacheCounts WeightedRow.Weights WeightedRealExecution
open WeightedDualCache WeightedOracleExecution WeightedFirstHit
open WeightedEmpirical
open LongChain91Security LongChain91Empirical LongChain91CollisionCap
open LongChain91StoppedCollision LongChain91CollisionArithmetic
open LongChain91DiagonalClock

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev M := LongChain91Security.M
abbrev decode := LongChain91Empirical.cacheDecode
abbrev securityWeights := LongChain91Security.securityWeights
abbrev kappa : ℝ := Chain18Compact.kappa
abbrev L : ℕ := Chain18Compact.L

/-! ## Actual-cache hazard law -/

def rowCount (m : Message) (c : hashSpec.QueryCache) : ℕ :=
  (seen (WideDomains.rowDomain m) c).card

def globalCount (c : hashSpec.QueryCache) : ℕ :=
  (seen WideDomains.indexDomain c).card

def globalCounts (c : hashSpec.QueryCache) : Fin M → ℕ :=
  classCounts WideDomains.indexDomain c decode

def rowCounts (m : Message) (c : hashSpec.QueryCache) : Fin M → ℕ :=
  classCounts (WideDomains.rowDomain m) c decode

def hazard (m : Message) (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.hazard N (rowCount m c) (globalCounts c) (rowCounts m c)

def queryPhase (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) : Phase :=
  protectedPhase (WideDomains.rowDomain m) WideDomains.indexDomain t c

def nextHazard (s : Phase) (m : Message) (c : hashSpec.QueryCache) :
    Option (Fin M) → ℝ :=
  after (securityWeights.hazard N) s (rowCount m c)
    (globalCounts c) (rowCounts m c)

def delta (s : Phase) (m : Message) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) : ℝ :=
  nextHazard s m c x - hazard m c

theorem primitive_joint_law (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache)
    (f : ℕ → (Fin M → ℕ) → (Fin M → ℕ) → ℝ) :
    realEval ((oracleImpl t).run c)
      (fun out => f (rowCount m out.2) (globalCounts out.2)
        (rowCounts m out.2)) =
      securityWeights.expect (after f (queryPhase m t c) (rowCount m c)
        (globalCounts c) (rowCounts m c)) := by
  exact WeightedDualCache.actual_query_law securityWeights
    (WideDomains.rowDomain m) WideDomains.indexDomain
    (WideDomains.row_subset m) decode cache_decoder_law t c f

theorem primitive_delta_law (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (f : ℝ → ℝ) :
    realEval ((oracleImpl t).run c)
      (fun out => f (hazard m out.2 - hazard m c)) =
      securityWeights.expect
        (fun x => f (delta (queryPhase m t c) m c x)) := by
  have h := primitive_joint_law m t c
    (fun r k row => f (securityWeights.hazard N r k row - hazard m c))
  exact h.trans (congrArg securityWeights.expect (after_comp
    (fun z => f (z - hazard m c)) (securityWeights.hazard N)
    (queryPhase m t c) (rowCount m c) (globalCounts c) (rowCounts m c)))

theorem row_le_global (m : Message) (c : hashSpec.QueryCache) (i : Fin M) :
    rowCounts m c i ≤ globalCounts c i := by
  exact classCounts_mono (WideDomains.row_subset m) c decode i

theorem rowCount_le_globalCount (m : Message) (c : hashSpec.QueryCache) :
    rowCount m c ≤ globalCount c := by
  exact Finset.card_le_card (WideDomains.seen_row_subset m c)

theorem rowCount_le (m : Message) (c : hashSpec.QueryCache) :
    (rowCount m c : ℝ) ≤ N := by
  have h : (rowCount m c : ℝ) ≤ ((2^86 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (WideDomains.seen_row_bound m c)
  exact h.trans_eq (by norm_num [N])

theorem inside_rowCount_succ_le (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (h : queryPhase m t c = .inside) :
    (rowCount m c : ℝ) + 1 ≤ N := by
  obtain ⟨q, hc, hq⟩ := WeightedDualCache.protectedPhase_inside_witness
    (WideDomains.rowDomain m) WideDomains.indexDomain t c h
  have hb : (((rowCount m c) + 1 : ℕ) : ℝ) ≤ ((2^86 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (WideDomains.fresh_row_succ_bound m c q hq hc)
  have he : (((rowCount m c) + 1 : ℕ) : ℝ) =
      (rowCount m c : ℝ) + 1 :=
    (Nat.cast_add (rowCount m c) 1).trans
      (congrArg (fun z : ℝ => (rowCount m c : ℝ) + z) Nat.cast_one)
  exact he.symm.trans_le (hb.trans_eq (by norm_num [N]))

/-! ## Increment, drift, and jump bounds -/

def gain (s : Phase) (m : Message) (c : hashSpec.QueryCache) :
    Option (Fin M) → ℝ :=
  match s with
  | .idle => fun _ => 0
  | .outside => securityWeights.positiveOutside N (rowCount m c)
      (globalCounts c) (rowCounts m c)
  | .inside => securityWeights.positiveInside N (rowCount m c)
      (globalCounts c) (rowCounts m c)

def shift (s : Phase) (c : hashSpec.QueryCache) : ℝ :=
  match s with
  | .inside => securityWeights.seen (globalCounts c) / N
  | _ => 0

def drift (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache) : ℝ :=
  realEval ((oracleImpl t).run c)
    (fun out => hazard m out.2 - hazard m c)

theorem delta_gain_shift (s : Phase) (m : Message)
    (c : hashSpec.QueryCache) (x : Option (Fin M)) :
    delta s m c x = gain s m c x - shift s c := by
  cases s with
  | idle => simp [delta, nextHazard, after, hazard, gain, shift]
  | outside =>
      have h := securityWeights.increment_outside N (rowCount m c)
        (globalCounts c) (rowCounts m c) x
      cases x <;> simpa only [delta, nextHazard, after, advance, hazard,
        gain, shift, afterOutside, sub_zero] using h
  | inside =>
      have h := securityWeights.increment_inside N (rowCount m c)
        (globalCounts c) (rowCounts m c) x
      cases x <;> simpa only [delta, nextHazard, after, advance, hazard,
        gain, shift, afterInside] using h

theorem gain_bounds (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (x : Option (Fin M)) :
    0 ≤ gain (queryPhase m t c) m c x ∧
      gain (queryPhase m t c) m c x ≤ hazardJumpBound := by
  cases hs : queryPhase m t c with
  | idle =>
      change 0 ≤ (0 : ℝ) ∧ 0 ≤ hazardJumpBound
      exact ⟨le_rfl, hazardJumpBound_pos.le⟩
  | outside =>
      change 0 ≤ securityWeights.positiveOutside N (rowCount m c)
          (globalCounts c) (rowCounts m c) x ∧
        securityWeights.positiveOutside N (rowCount m c)
          (globalCounts c) (rowCounts m c) x ≤
            (L : ℝ) * kappa / 2 + 2 * (L : ℝ) / N
      exact securityWeights.positiveOutside_bounds N (by unfold N; positivity)
        (rowCount m c) (rowCount_le m c) (globalCounts c)
        (rowCounts m c) (row_le_global m c)
        ((L : ℝ) * kappa / 2) L
        (by
          exact div_nonneg
            (mul_nonneg (Nat.cast_nonneg L)
              LongChain91BudgetArithmetic.kappa_pos.le)
            (by norm_num))
        (by positivity) referenceWeight_le weight_ratio_le x
  | inside =>
      change 0 ≤ securityWeights.positiveInside N (rowCount m c)
          (globalCounts c) (rowCounts m c) x ∧
        securityWeights.positiveInside N (rowCount m c)
          (globalCounts c) (rowCounts m c) x ≤
            (L : ℝ) * kappa / 2 + 2 * (L : ℝ) / N
      exact securityWeights.positiveInside_bounds N (by unfold N; positivity)
        (rowCount m c) (inside_rowCount_succ_le m t c hs)
        (globalCounts c) (rowCounts m c) (row_le_global m c)
        ((L : ℝ) * kappa / 2) L
        (by
          exact div_nonneg
            (mul_nonneg (Nat.cast_nonneg L)
              LongChain91BudgetArithmetic.kappa_pos.le)
            (by norm_num))
        (by positivity) referenceWeight_le weight_ratio_le x

theorem delta_drift_le (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ) * securityWeights.mean + η * kappa * N) :
    securityWeights.expect (delta (queryPhase m t c) m c) ≤
      securityWeights.mean + η * kappa := by
  cases hs : queryPhase m t c with
  | idle =>
      have hz : delta Phase.idle m c = fun _ => 0 := by
        funext x
        exact sub_self _
      rw [hz, securityWeights.expect_const]
      have hm : 0 ≤ securityWeights.mean := by
        exact Finset.sum_nonneg (fun i _ =>
          mul_nonneg (securityWeights.p_pos i).le
            (securityWeights.g_nonneg i))
      exact add_nonneg hm (mul_nonneg hη (by
        unfold kappa Chain18Compact.kappa
        positivity))
  | outside =>
      exact securityWeights.drift_outside_le N (by unfold N; positivity)
        (rowCount m c) (rowCount_le m c) (globalCounts c)
        (rowCounts m c) η kappa hscore
  | inside =>
      exact securityWeights.drift_inside_le N (by unfold N; positivity)
        (rowCount m c) (rowCount_le m c) (globalCounts c)
        (rowCounts m c) η kappa hscore

theorem drift_eq (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache) :
    drift m t c =
      securityWeights.expect (delta (queryPhase m t c) m c) := by
  exact primitive_delta_law m t c id

theorem centered_delta (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (x : Option (Fin M)) :
    delta (queryPhase m t c) m c x - drift m t c =
      gain (queryPhase m t c) m c x -
        securityWeights.expect (gain (queryPhase m t c) m c) := by
  rw [drift_eq]
  simp only [show delta (queryPhase m t c) m c =
      (fun x => gain (queryPhase m t c) m c x -
        shift (queryPhase m t c) c) from
    funext (delta_gain_shift _ _ _)]
  exact securityWeights.center_predictable_shift _ _ x

/-! ## Tight empirical drift -/

theorem good_row_hyp (m : Message) (c : hashSpec.QueryCache)
    (hc : LongChain91Empirical.Good c) :
    securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ) * securityWeights.mean +
        (1 / 1000 : ℝ) * kappa * N := by
  have h := LongChain91Empirical.good_row_score c hc m
  change securityWeights.score (rowCounts m c) ≤
    securityWeights.mean * (rowCount m c : ℝ) +
      kappa * (2 : ℝ)^86 / 1000 at h
  exact h.trans_eq (by unfold N; ring)

theorem good_delta_drift (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (hc : LongChain91Empirical.Good c) :
    securityWeights.expect (delta (queryPhase m t c) m c) ≤
      tightAlpha * (globalStep (queryPhase m t c) : ℝ) := by
  have h := (delta_drift_le m t c (1 / 1000) (by norm_num)
    (good_row_hyp m c hc)).trans
      (show securityWeights.mean + (1 / 1000 : ℝ) * kappa ≤
        tightAlpha from by
          convert tight_mean_margin_le using 1 <;> ring)
  cases hs : queryPhase m t c with
  | idle =>
      have hz : delta Phase.idle m c = fun _ => 0 := by
        funext x
        exact sub_self _
      rw [hz, securityWeights.expect_const]
      simp [globalStep]
  | outside => simpa only [hs, globalStep, Nat.cast_one, mul_one] using h
  | inside => simpa only [hs, globalStep, Nat.cast_one, mul_one] using h

/-! ## Deterministic equality-clock envelope -/

/-- Deviation assigned to the selected row's self-collision process. -/
def selfDeviation (B : ℝ) : ℝ := diagonalRate * B / 20

/-- A deterministic variance cap for that process.  It uses both physical
bounds on a nonce row: its length is at most `N`, and while the large hazard
runs its length is also at most the global count `B`. -/
def selfVariance (B : ℝ) : ℝ :=
  collisionJumpBound * collisionScale^2 * B * N

def selfHit (B : ℝ) (m : Message) :
    ℕ → hashSpec.QueryCache → Prop :=
  collisionHit m (selfDeviation B) (selfVariance B)

theorem selfDeviation_pos {B : ℝ} (hB : 0 < B) :
    0 < selfDeviation B := by
  unfold selfDeviation
  exact div_pos (mul_pos diagonalRate_pos hB) (by norm_num)

theorem selfVariance_pos {B : ℝ} (hB : 0 < B) :
    0 < selfVariance B := by
  have hL : 0 < (Chain18Compact.L : ℝ) := by
    norm_num [Chain18Compact.L]
  have hJ : 0 < collisionJumpBound := by
    unfold LongChain91CollisionCap.collisionJumpBound
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hL))
      LongChain91BudgetArithmetic.kappa_pos
  have hG : 0 < collisionScale := by
    unfold LongChain91StoppedCollision.collisionScale
    exact div_pos (mul_pos hL LongChain91BudgetArithmetic.kappa_pos)
      (by norm_num)
  have hN : 0 < N := by unfold N; positivity
  unfold selfVariance
  exact mul_pos (mul_pos (mul_pos hJ (sq_pos_of_pos hG)) hB) hN

/-- The selected-row diagonal and the global forward clock are both charged
to the global diagonal clock. -/
theorem reverse_forward_le (m : Message) (c : hashSpec.QueryCache) :
    securityWeights.Qrev (rowCounts m c) +
        securityWeights.Qfwd (globalCounts c) ≤
      2 * Dglobal c + securityWeights.X (rowCounts m c) := by
  have hD : securityWeights.D (rowCounts m c) ≤ Dglobal c := by
    simpa only [rowCounts, LongChain91DiagonalClock.Drow] using
      LongChain91DiagonalClock.Drow_le_Dglobal m c
  have hF : securityWeights.Qfwd (globalCounts c) ≤ Dglobal c := by
    simpa only [globalCounts, LongChain91DiagonalClock.globalCounts,
      LongChain91SmallMoments.counts] using
      LongChain91DiagonalClock.Qfwd_le_Dglobal c
  rw [securityWeights.Qrev_eq_D_add_X]
  linarith

theorem self_clock_le (B : ℝ) (m : Message)
    (c : hashSpec.QueryCache) (hq : (globalCount c : ℝ) ≤ B) :
    EqualityCollisionCache91.cacheXw (WideDomains.rowDomain m)
        collisionJumpBound collisionScale c ≤ selfVariance B := by
  have hrq : rowCount m c ≤ globalCount c := rowCount_le_globalCount m c
  have hrB : (rowCount m c : ℝ) ≤ B := by
    exact (by exact_mod_cast hrq : (rowCount m c : ℝ) ≤
      (globalCount c : ℝ)).trans hq
  have hrN : (rowCount m c : ℝ) ≤ N := rowCount_le m c
  have hr0 : (0 : ℝ) ≤ rowCount m c := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B := hr0.trans hrB
  have hrr : (rowCount m c : ℝ) * ((rowCount m c : ℝ) - 1) ≤
      (rowCount m c : ℝ) * (rowCount m c : ℝ) := by
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) hr0
  have hrBN : (rowCount m c : ℝ) * (rowCount m c : ℝ) ≤
      B * N := by
    exact mul_le_mul hrB hrN hr0 hB0
  have hcoef : 0 ≤ collisionJumpBound * collisionScale^2 :=
    mul_nonneg collisionJumpBound_nonneg (sq_nonneg _)
  unfold EqualityCollisionCache91.cacheXw EqualityCollisionCache91.xW
    selfVariance
  calc
    collisionJumpBound * collisionScale ^ 2 *
        ((seen (WideDomains.rowDomain m) c).card : ℝ) *
          (((seen (WideDomains.rowDomain m) c).card : ℝ) - 1) =
      collisionJumpBound * collisionScale ^ 2 *
        (((seen (WideDomains.rowDomain m) c).card : ℝ) *
          (((seen (WideDomains.rowDomain m) c).card : ℝ) - 1)) := by ring
    _ ≤
      collisionJumpBound * collisionScale ^ 2 *
        (((seen (WideDomains.rowDomain m) c).card : ℝ) *
          ((seen (WideDomains.rowDomain m) c).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hrr hcoef
    _ ≤ collisionJumpBound * collisionScale ^ 2 * (B * N) :=
        mul_le_mul_of_nonneg_left hrBN hcoef
    _ = collisionJumpBound * collisionScale ^ 2 * B * N := by ring

/-- Before the stopped self-collision event, `X` is its deterministic mean
envelope plus the allocated deviation. -/
theorem selfCollision_le (B : ℝ) (m : Message)
    (c : hashSpec.QueryCache) (hq : (globalCount c : ℝ) ≤ B)
    (hnot : ¬ selfHit B m 0 c) :
    securityWeights.X (rowCounts m c) ≤
      collisionScale^2 * (rowCount m c : ℝ) *
          ((rowCount m c : ℝ) - 1) + selfDeviation B := by
  have hw := self_clock_le B m c hq
  have hn : ¬ selfDeviation B ≤
      EqualityCollisionCache91.cacheXz securityWeights
        (WideDomains.rowDomain m) decode collisionScale c := by
    intro hz
    exact hnot ⟨hz, hw⟩
  have hz := (lt_of_not_ge hn).le
  unfold EqualityCollisionCache91.cacheXz EqualityCollisionCache91.xZ at hz
  change securityWeights.X (rowCounts m c) -
      collisionScale^2 * (rowCount m c : ℝ) *
        ((rowCount m c : ℝ) - 1) ≤ selfDeviation B at hz
  linarith

def diagonalGood (B : ℝ) (c : hashSpec.QueryCache) : Prop :=
  Dglobal c ≤ (3 / 2 : ℝ) * diagonalRate * B

/-- `Qrev = Drow + X`, `Drow <= Dglobal`, and `Qfwd <= Dglobal` give the
`61/20` envelope advertised by the numerical certificate. -/
theorem equality_clock_envelope (B : ℝ) (m : Message)
    (c : hashSpec.QueryCache) (hq : (globalCount c : ℝ) ≤ B)
    (hD : diagonalGood B c) (hX : ¬ selfHit B m 0 c) :
    securityWeights.Qrev (rowCounts m c) +
        securityWeights.Qfwd (globalCounts c) ≤
      (61 / 20 : ℝ) * diagonalRate * B +
        collisionScale^2 * B * N := by
  have hbase := reverse_forward_le m c
  have hx := selfCollision_le B m c hq hX
  have hrB : (rowCount m c : ℝ) ≤ B := by
    have hrq := rowCount_le_globalCount m c
    exact (by exact_mod_cast hrq : (rowCount m c : ℝ) ≤
      (globalCount c : ℝ)).trans hq
  have hrN := rowCount_le m c
  have hr0 : (0 : ℝ) ≤ rowCount m c := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B := hr0.trans hrB
  have hrr : (rowCount m c : ℝ) * ((rowCount m c : ℝ) - 1) ≤
      (rowCount m c : ℝ) * (rowCount m c : ℝ) := by
    exact mul_le_mul_of_nonneg_left (sub_le_self _ (by norm_num)) hr0
  have hrBN : (rowCount m c : ℝ) * (rowCount m c : ℝ) ≤
      B * N := mul_le_mul hrB hrN hr0 hB0
  have hscale := mul_le_mul_of_nonneg_left (hrr.trans hrBN)
    (sq_nonneg collisionScale)
  unfold diagonalGood at hD
  unfold selfDeviation at hx
  nlinarith

/-! ## Equality-gain second moment -/

def varianceRate (B : ℝ) : ℝ :=
  3 * freshSquareRate +
    (183 / 20) * diagonalRate * B / N^2 +
    3 * collisionScale^2 * B / N

theorem varianceRate_pos {B : ℝ} (hB : 0 < B) :
    0 < varianceRate B := by
  unfold varianceRate
  have hN : 0 < N := by unfold N; positivity
  have hf := freshSquareRate_pos
  have hd := diagonalRate_pos
  have hg := collisionScale_nonneg
  positivity

theorem hazardVariance_eq_rate (B : ℝ) :
    hazardVariance B = varianceRate B * B := by
  unfold hazardVariance varianceRate
  ring

theorem gain_square_le (B : ℝ) (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (hq : (globalCount c : ℝ) ≤ B)
    (hD : diagonalGood B c) (hX : ¬ selfHit B m 0 c) :
    securityWeights.expect
        (fun x => (gain (queryPhase m t c) m c x)^2) ≤
      varianceRate B * (globalStep (queryPhase m t c) : ℝ) := by
  have hclock := equality_clock_envelope B m c hq hD hX
  have hfresh : securityWeights.freshSquareMass ≤ freshSquareRate :=
    freshSquareMass_lt.le
  have hN : 0 < N := by unfold N; positivity
  have henvelope :
      3 * securityWeights.freshSquareMass +
          3 * (securityWeights.Qrev (rowCounts m c) +
            securityWeights.Qfwd (globalCounts c)) / N^2 ≤
        varianceRate B := by
    calc
      3 * securityWeights.freshSquareMass +
          3 * (securityWeights.Qrev (rowCounts m c) +
            securityWeights.Qfwd (globalCounts c)) / N^2 ≤
        3 * freshSquareRate +
          3 * ((61 / 20 : ℝ) * diagonalRate * B +
            collisionScale^2 * B * N) / N^2 := by
              gcongr
      _ = varianceRate B := by
        unfold varianceRate
        field_simp [hN.ne']
        <;> ring
  cases hs : queryPhase m t c with
  | idle =>
      simp only [hs, gain, securityWeights.expect_const, globalStep,
        Nat.cast_zero, mul_zero]
      norm_num
  | outside =>
      have h := securityWeights.positiveOutside_square_envelope N hN
        (rowCount m c) (rowCount_le m c) (globalCounts c) (rowCounts m c)
      simpa only [hs, gain, globalStep, Nat.cast_one, mul_one] using
        h.trans henvelope
  | inside =>
      have h := securityWeights.positiveInside_square_envelope N hN
        (rowCount m c) (inside_rowCount_succ_le m t c hs)
        (globalCounts c) (rowCounts m c)
      simpa only [hs, gain, globalStep, Nat.cast_one, mul_one] using
        h.trans henvelope

theorem centered_variance_le (B : ℝ) (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (hq : (globalCount c : ℝ) ≤ B)
    (hD : diagonalGood B c) (hX : ¬ selfHit B m 0 c) :
    securityWeights.expect (fun x =>
        (delta (queryPhase m t c) m c x -
          securityWeights.expect (delta (queryPhase m t c) m c))^2) ≤
      varianceRate B * (globalStep (queryPhase m t c) : ℝ) := by
  have heq : (fun x => delta (queryPhase m t c) m c x -
      securityWeights.expect (delta (queryPhase m t c) m c)) =
      (fun x => gain (queryPhase m t c) m c x -
        securityWeights.expect (gain (queryPhase m t c) m c)) := by
    funext x
    have h := centered_delta m t c x
    rw [drift_eq] at h
    exact h
  have heq' := congrArg
    (fun f : Option (Fin M) → ℝ => fun x => (f x)^2) heq
  rw [heq', securityWeights.centered_square]
  have hsquare := gain_square_le B m t c hq hD hX
  nlinarith [sq_nonneg
    (securityWeights.expect (gain (queryPhase m t c) m c))]

/-! ## Compensated one-query MGF -/

theorem good_delta_mgf (B : ℝ) (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (hc : LongChain91Empirical.Good c)
    (hq : (globalCount c : ℝ) ≤ B) (hD : diagonalGood B c)
    (hX : ¬ selfHit B m 0 c) (θ : ℝ) (hθ : 0 ≤ θ)
    (hθJ : θ * hazardJumpBound < 3) :
    securityWeights.expect (fun x => Real.exp
      (θ * (delta (queryPhase m t c) m c x -
        tightAlpha * (globalStep (queryPhase m t c) : ℝ)) -
      θ^2 * (varianceRate B *
        (globalStep (queryPhase m t c) : ℝ)) /
          (2 * (1 - θ * hazardJumpBound / 3)))) ≤ 1 := by
  let X : Option (Fin M) → ℝ := fun x =>
    delta (queryPhase m t c) m c x -
      securityWeights.expect (delta (queryPhase m t c) m c)
  have hcenter (x : Option (Fin M)) :
      X x = gain (queryPhase m t c) m c x -
        securityWeights.expect (gain (queryPhase m t c) m c) := by
    dsimp only [X]
    have h := centered_delta m t c x
    rw [drift_eq] at h
    exact h
  have hb (x : Option (Fin M)) : |X x| ≤ hazardJumpBound := by
    rw [hcenter]
    exact securityWeights.centered_abs_le _ _ (gain_bounds m t c) x
  have hm : expectLinear securityWeights X = 0 := by
    change securityWeights.expect X = 0
    dsimp only [X]
    rw [securityWeights.expect_sub, securityWeights.expect_const, sub_self]
  have hv : expectLinear securityWeights (fun x => (X x)^2) ≤
      varianceRate B * (globalStep (queryPhase m t c) : ℝ) := by
    change securityWeights.expect (fun x => (X x)^2) ≤ _
    exact centered_variance_le B m t c hq hD hX
  have hmgf := WeightedMGF.compensated_mgf (expectLinear securityWeights)
    securityWeights.expect_mono (securityWeights.expect_const 1) X θ
    hazardJumpBound
    (varianceRate B * (globalStep (queryPhase m t c) : ℝ))
    hθ hazardJumpBound_pos.le hθJ hb hm hv
  change securityWeights.expect (fun x => Real.exp
    (θ * X x - θ^2 * (varianceRate B *
      (globalStep (queryPhase m t c) : ℝ)) /
        (2 * (1 - θ * hazardJumpBound / 3)))) ≤ 1 at hmgf
  have hd := good_delta_drift m t c hc
  apply (securityWeights.expect_mono _ _ (fun x => ?_)).trans hmgf
  apply Real.exp_le_exp.mpr
  dsimp only [X]
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hd _) hθ) _

theorem actual_good_delta_mgf (B : ℝ) (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (hc : LongChain91Empirical.Good c)
    (hq : (globalCount c : ℝ) ≤ B) (hD : diagonalGood B c)
    (hX : ¬ selfHit B m 0 c) (θ : ℝ) (hθ : 0 ≤ θ)
    (hθJ : θ * hazardJumpBound < 3) :
    realEval ((oracleImpl t).run c) (fun out => Real.exp
      (θ * (hazard m out.2 - hazard m c -
        tightAlpha * (globalStep (queryPhase m t c) : ℝ)) -
      θ^2 * (varianceRate B *
        (globalStep (queryPhase m t c) : ℝ)) /
          (2 * (1 - θ * hazardJumpBound / 3)))) ≤ 1 := by
  exact (primitive_delta_law m t c (fun z => Real.exp
    (θ * (z - tightAlpha *
      (globalStep (queryPhase m t c) : ℝ)) -
    θ^2 * (varianceRate B *
      (globalStep (queryPhase m t c) : ℝ)) /
        (2 * (1 - θ * hazardJumpBound / 3))))).trans_le
      (good_delta_mgf B m t c hc hq hD hX θ hθ hθJ)

/-! ## Accumulated potential and stopped concentration -/

def Z (m : Message) (c : hashSpec.QueryCache) : ℝ :=
  hazard m c - tightAlpha * (globalCount c : ℝ)

def W (B : ℝ) (c : hashSpec.QueryCache) : ℝ :=
  varianceRate B * (globalCount c : ℝ)

theorem actual_count_step (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    globalCount out.2 = globalCount c + globalStep (queryPhase m t c) := by
  have hg := actual_seen_count WideDomains.indexDomain t c out hout
  have he := protected_phase_steps (WideDomains.rowDomain m)
    WideDomains.indexDomain (WideDomains.row_subset m) t c
  exact hg.trans
    (congrArg (fun n => globalCount c + n) he.1.symm)

theorem actual_ZW_steps (B : ℝ) (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    Z m out.2 = Z m c +
        (hazard m out.2 - hazard m c -
          tightAlpha * (globalStep (queryPhase m t c) : ℝ)) ∧
      W B out.2 = W B c +
        varianceRate B * (globalStep (queryPhase m t c) : ℝ) := by
  have hg := actual_count_step m t c out hout
  constructor
  · unfold Z
    rw [hg, Nat.cast_add]
    ring
  · unfold W
    rw [hg, Nat.cast_add]
    ring

theorem actual_potential_step (B : ℝ) (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (hc : LongChain91Empirical.Good c)
    (hq : (globalCount c : ℝ) ≤ B) (hD : diagonalGood B c)
    (hX : ¬ selfHit B m 0 c) (θ : ℝ) (hθ : 0 ≤ θ)
    (hθJ : θ * hazardJumpBound < 3) :
    expectedValue ((oracleImpl t).run c)
      (fun out => ENNReal.ofReal (Real.exp
        (θ * Z m out.2 - θ^2 * W B out.2 /
          (2 * (1 - θ * hazardJumpBound / 3))))) ≤
      ENNReal.ofReal (Real.exp
        (θ * Z m c - θ^2 * W B c /
          (2 * (1 - θ * hazardJumpBound / 3)))) := by
  rw [← ofReal_realEval _ _ (fun _ => Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hp := WeightedKernel.exponential_step
    (realEval ((oracleImpl t).run c)) (Z m c)
    (θ^2 * W B c / (2 * (1 - θ * hazardJumpBound / 3))) θ
    (θ^2 * (varianceRate B *
      (globalStep (queryPhase m t c) : ℝ)) /
        (2 * (1 - θ * hazardJumpBound / 3)))
    (fun out => hazard m out.2 - hazard m c -
      tightAlpha * (globalStep (queryPhase m t c) : ℝ))
    (actual_good_delta_mgf B m t c hc hq hD hX θ hθ hθJ)
  apply (realEval_mono_of_support ((oracleImpl t).run c) _ _
    (fun out hout => ?_)).trans hp
  obtain ⟨hz, hw⟩ := actual_ZW_steps B m t c out hout
  apply Real.exp_le_exp.mpr
  rw [hz, hw]
  ring_nf
  exact le_rfl

def largeHit (B : ℝ) (m : Message) :
    ℕ → hashSpec.QueryCache → Prop :=
  fun _ c => (globalCount c : ℝ) ≤ B ∧ largeDeviation B ≤ Z m c

def largeKill (B : ℝ) (m : Message) :
    ℕ → hashSpec.QueryCache → Prop :=
  fun _ c =>
    ¬ LongChain91Empirical.Good c ∨
    B < (globalCount c : ℝ) ∨
    ¬ diagonalGood B c ∨
    selfHit B m 0 c ∨
    occupancyKill m 0 c

theorem ZW_initial (B : ℝ) (m : Message) (c : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → c q = none) :
    Z m c = 0 ∧ W B c = 0 := by
  obtain ⟨hq, hk⟩ := LongChain91SmallMoments.index_initial c hfresh
  obtain ⟨hr, hrow⟩ := LongChain91Empirical.row_initial m c hfresh
  have hq' : globalCount c = 0 := by exact hq
  have hk' : globalCounts c = fun _ => 0 := by exact hk
  have hr' : rowCount m c = 0 := by exact hr
  have hrow' : rowCounts m c = fun _ => 0 := by exact hrow
  constructor
  · simp [Z, hazard, WeightedRow.Weights.hazard,
      WeightedRow.Weights.seen, WeightedRow.Weights.bad,
      hq', hk', hr', hrow']
  · simp [W, hq']

/-- Large-regime concentration for one chosen message row on the actual
memoized oracle execution.  Every stop condition has its own unconditional
tail theorem: empirical failure, global diagonal crossing, selected-row
self-collision, and occupancy failure. -/
theorem actual_stopped_large_hazard { β : Type }
    (B : ℝ) (hlarge : N / 64 ≤ B)
    (m : Message) (oa : OracleComp Spec β)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[fun out => out.2.status = Status.hit |
      (simulateQ (stoppedImpl oracleImpl (largeHit B m) (largeKill B m))
        oa).run (classify (largeHit B m) (largeKill B m) 0 initial)] ≤
      ENNReal.ofReal (Real.exp (-(500 : ℝ))) := by
  have hN : 0 < N := by unfold N; positivity
  have hB : 0 < B := lt_of_lt_of_le (div_pos hN (by norm_num)) hlarge
  have ha : 0 < largeDeviation B := by
    unfold largeDeviation
    exact div_pos (mul_pos LongChain91BudgetArithmetic.kappa_pos hB)
      (by norm_num)
  have hv : 0 < hazardVariance B := hazardVariance_pos hB
  obtain ⟨hz0, hw0⟩ := ZW_initial B m initial hfresh
  have h := actual_stopped_freedman oracleImpl oa
    (fun _ => Z m) (fun _ => W B) initial
    (largeDeviation B) (hazardVariance B) hazardJumpBound
    ha hv hazardJumpBound_pos.le hz0 hw0
    (largeHit B m) (largeKill B m)
    (by
      intro θ hθ hθJ q n c _ hnotKill
      have hs : LongChain91Empirical.Good c ∧
          (globalCount c : ℝ) ≤ B ∧ diagonalGood B c ∧
          ¬ selfHit B m 0 c ∧ ¬ occupancyKill m 0 c := by
        simpa only [largeKill, not_or, not_not, not_lt] using hnotKill
      exact actual_potential_step B m q c hs.1 hs.2.1 hs.2.2.1
        hs.2.2.2.1 θ hθ.le hθJ)
    (fun _ _ hh => hh.2)
    (by
      intro _ c hh
      unfold W
      have hr := mul_le_mul_of_nonneg_left hh.1 (varianceRate_pos hB).le
      rw [hazardVariance_eq_rate]
      exact hr)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have he := large_hazard_exponent B hlarge
  simpa only [neg_div] using neg_le_neg he

/-! ## The selected-row collision tail used by `largeKill` -/

theorem actual_stopped_self_collision { β : Type }
    (B : ℝ) (hlarge : N / 64 ≤ B)
    (m : Message) (oa : OracleComp Spec β)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[fun out => out.2.status = Status.hit |
      (simulateQ (stoppedImpl oracleImpl (selfHit B m) (occupancyKill m))
        oa).run (classify (selfHit B m) (occupancyKill m) 0 initial)] ≤
      ENNReal.ofReal (Real.exp
        (-(selfDeviation B)^2 /
          (2 * (selfVariance B +
            collisionJumpBound * selfDeviation B / 3)))) := by
  have hN : 0 < N := by unfold N; positivity
  have hB : 0 < B := lt_of_lt_of_le (div_pos hN (by norm_num)) hlarge
  exact actual_stopped_collision_freedman m oa initial hfresh
    (selfDeviation B) (selfVariance B)
    (selfDeviation_pos hB) (selfVariance_pos hB)

end OptimalOTS.WeightedConstruction.LongChain91LargeHazard
