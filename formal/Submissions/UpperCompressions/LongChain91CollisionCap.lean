import Submissions.UpperCompressions.LongChain91Occupancy
import Submissions.UpperCompressions.LongChain91SecurityData
import Submissions.UpperCompressions.EqualityCollision91
import Submissions.UpperCompressions.ProofBundle12

/-!
# Actual-cache bridge for equality replay clocks

The equality collision algebra in `EqualityCollision91` is phrased for two
multiplicity vectors: all exposed index inputs and one distinguished nonce row.
This file connects those vectors to the contract's real memoized random-oracle
cache.  A fresh row query advances both vectors with the same decoded answer; a
fresh index query outside the row advances only the global vector; every cache
hit and every private query leaves both vectors fixed.

The bridge is deliberately generic in the finite decoder.  The chain-18
schedule can instantiate it once its decoder-fiber theorem is available.
-/

noncomputable section

open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal

namespace EqualityCollisionCache91

open WeightedCacheCounts WeightedRealExecution
open WeightedRow.Weights WeightedDualCache

set_option maxHeartbeats 1600000

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! The diagonal and forward clocks also chain through complete adaptive
`OracleComp` programs.  These two lemmas use the one-domain cache kernel: `D`
is an exact martingale after subtracting its mean, while `Qfwd` is a
supermartingale after subtracting the same envelope. -/

/-! ## The stopped self-collision process -/

/-- Decoded class multiplicities cannot outnumber the finite set of inputs
from which they were obtained.  Rejected decoder outputs account for the
possible strict inequality. -/
theorem counts_sum_le_card {Q : Type} [DecidableEq Q]
    (S : Finset Q) (answer : Q → Option ι) :
    (∑ i : ι, WeightedPublicCounts.counts S answer i) ≤ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [WeightedPublicCounts.counts]
  | @insert q S hq ih =>
      rw [Finset.card_insert_of_notMem hq]
      simp_rw [WeightedPublicCounts.counts_insert_apply S answer q hq]
      rw [Finset.sum_add_distrib]
      have hone : (∑ i : ι, if answer q = some i then 1 else 0) ≤ 1 := by
        cases ha : answer q with
        | none => simp [ha]
        | some j => simp [ha]
      omega

theorem classCounts_sum_le_seen {B : Type} {D : Type} [DecidableEq D]
    (A : Finset D) (cache : D → Option B) (decode : B → Option ι) :
    (∑ i : ι, WeightedCacheCounts.classCounts A cache decode i) ≤
      (WeightedCacheCounts.seen A cache).card := by
  unfold WeightedCacheCounts.classCounts
  exact counts_sum_le_card _ _

/-- Self-collision martingale coordinate after subtracting the deterministic
envelope for the accumulated conditional means `2 r G²`. -/
def xZ (w : WeightedRow.Weights ι) (G : ℝ) (r : ℕ) (row : ι → ℕ) : ℝ :=
  w.X row - G^2 * (r : ℝ) * ((r : ℝ) - 1)

/-- Predictable variance clock paired with `xZ`. -/
def xW (J G : ℝ) (r : ℕ) : ℝ :=
  J * G^2 * (r : ℝ) * ((r : ℝ) - 1)

theorem xZ_advance (w : WeightedRow.Weights ι) (G : ℝ) (r : ℕ)
    (row : ι → ℕ) (x : Option ι) :
    xZ w G (r+1) (advance row x) =
      xZ w G r row + (w.xJump row x - 2*(r:ℝ)*G^2) := by
  unfold xZ
  rw [w.X_advance]
  push_cast
  ring

theorem xW_succ (J G : ℝ) (r : ℕ) :
    xW J G (r+1) = xW J G r + J*(2*(r:ℝ)*G^2) := by
  unfold xW
  push_cast
  ring

/-- Exponential potential used by the stopped process. -/
def xPhi (w : WeightedRow.Weights ι) (θ J G : ℝ) (r : ℕ)
    (row : ι → ℕ) : ℝ :=
  Real.exp (θ*xZ w G r row - θ^2*xW J G r /
    (2*(1-θ*J/3)))

theorem xPhi_advance (w : WeightedRow.Weights ι) (θ J G : ℝ) (r : ℕ)
    (row : ι → ℕ) (x : Option ι) :
    xPhi w θ J G (r+1) (advance row x) =
      xPhi w θ J G r row * Real.exp
        (θ*(w.xJump row x-2*(r:ℝ)*G^2) -
          θ^2*(J*(2*(r:ℝ)*G^2))/(2*(1-θ*J/3))) := by
  unfold xPhi
  rw [xZ_advance, xW_succ]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Occupancy cap for a distinguished row, expressed on the actual cache. -/
def OccupancyGood (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι) (u : ι → ℕ)
    (cache : OptimalOTS.hashSpec.QueryCache) : Prop :=
  ∀ i, WeightedCacheCounts.classCounts A cache decode i ≤ u i

/-- The compensated self-collision potential is a supermartingale for one
primitive query of the actual memoized oracle, until the occupancy cap fails. -/
theorem actual_xPhi_step (w : WeightedRow.Weights ι)
    (A Gdom : Finset OptimalOTS.Query) (hAG : A ⊆ Gdom)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (u : ι → ℕ) (G θ J : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ*J < 3)
    (hcap : ∀ i, 2*(u i:ℝ)*w.collisionMass i ≤ J)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (hgood : OccupancyGood A decode u cache) :
    realEval ((OptimalOTS.oracleImpl t).run cache) (fun out =>
      xPhi w θ J G (WeightedCacheCounts.seen A out.2).card
        (WeightedCacheCounts.classCounts A out.2 decode)) ≤
      xPhi w θ J G (WeightedCacheCounts.seen A cache).card
        (WeightedCacheCounts.classCounts A cache decode) := by
  let r := (WeightedCacheCounts.seen A cache).card
  let row := WeightedCacheCounts.classCounts A cache decode
  have hsumNat : (∑ i : ι, row i) ≤ r := by
    exact classCounts_sum_le_seen A cache decode
  have hsum : (∑ i : ι, (row i : ℝ)) ≤ (r : ℝ) := by
    exact_mod_cast hsumNat
  have hmean : w.expect (w.xJump row) ≤ 2*(r:ℝ)*G^2 :=
    w.expect_xJump_le row (r:ℝ) G hG hg hsum
  have hmgf := w.xJump_upper_compensated_mgf_of_cap row u θ J
    (2*(r:ℝ)*G^2) hθ hJ hθJ hgood hcap hmean
  have hlaw := actual_query_law w A Gdom hAG decode hfiber t cache
    (fun r _ row => xPhi w θ J G r row)
  rw [hlaw]
  cases hs : protectedPhase A Gdom t cache with
  | idle =>
      simp only [hs, after, expect_const]
      exact le_rfl
  | outside =>
      simp only [hs, after, expect_const]
      exact le_rfl
  | inside =>
      simp only [hs, after]
      change w.expect (fun x => xPhi w θ J G (r+1) (advance row x)) ≤
        xPhi w θ J G r row
      rw [show (fun x => xPhi w θ J G (r+1) (advance row x)) =
          (fun x => xPhi w θ J G r row * Real.exp
            (θ*(w.xJump row x-2*(r:ℝ)*G^2) -
              θ^2*(J*(2*(r:ℝ)*G^2))/(2*(1-θ*J/3)))) by
        funext x
        exact xPhi_advance w θ J G r row x]
      rw [w.expect_smul]
      have hm := mul_le_mul_of_nonneg_left hmgf
        (Real.exp_nonneg (θ*xZ w G r row - θ^2*xW J G r/(2*(1-θ*J/3))))
      simpa only [xPhi, mul_one] using hm

/-- Cache specialization of the two stopped-process coordinates. -/
def cacheXz (w : WeightedRow.Weights ι) (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι) (G : ℝ)
    (cache : OptimalOTS.hashSpec.QueryCache) : ℝ :=
  xZ w G (WeightedCacheCounts.seen A cache).card
    (WeightedCacheCounts.classCounts A cache decode)

def cacheXw (A : Finset OptimalOTS.Query) (J G : ℝ)
    (cache : OptimalOTS.hashSpec.QueryCache) : ℝ :=
  xW J G (WeightedCacheCounts.seen A cache).card

/-- Maximal Freedman bound for the actual oracle execution, stopped before an
occupancy-cap violation.  The theorem chains the one-query cache law through
the real `OracleComp` syntax; no independent-draw execution is substituted. -/
theorem actual_stopped_x_freedman {α : Type}
    (w : WeightedRow.Weights ι)
    (A Gdom : Finset OptimalOTS.Query) (hAG : A ⊆ Gdom)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (u : ι → ℕ) (G J : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hJ : 0 ≤ J)
    (hcap : ∀ i, 2*(u i:ℝ)*w.collisionMass i ≤ J)
    (oa : OracleComp OptimalOTS.Spec α)
    (initial : OptimalOTS.hashSpec.QueryCache)
    (hr0 : (WeightedCacheCounts.seen A initial).card = 0)
    (hk0 : WeightedCacheCounts.classCounts A initial decode = fun _ => 0)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    let hit := fun (_ : ℕ) (cache : OptimalOTS.hashSpec.QueryCache) =>
      a ≤ cacheXz w A decode G cache ∧ cacheXw A J G cache ≤ v
    let kill := fun (_ : ℕ) (cache : OptimalOTS.hashSpec.QueryCache) =>
      ¬ OccupancyGood A decode u cache
    Pr[fun out => out.2.status = WeightedFirstHit.Status.hit |
      (simulateQ (WeightedOracleExecution.stoppedImpl OptimalOTS.oracleImpl hit kill) oa).run
        (WeightedFirstHit.classify hit kill 0 initial)] ≤
      ENNReal.ofReal (Real.exp (-a^2/(2*(v+J*a/3)))) := by
  dsimp only
  let hit := fun (_ : ℕ) (cache : OptimalOTS.hashSpec.QueryCache) =>
    a ≤ cacheXz w A decode G cache ∧ cacheXw A J G cache ≤ v
  let kill := fun (_ : ℕ) (cache : OptimalOTS.hashSpec.QueryCache) =>
    ¬ OccupancyGood A decode u cache
  apply WeightedOracleExecution.actual_stopped_freedman
    OptimalOTS.oracleImpl oa
    (fun _ cache => cacheXz w A decode G cache)
    (fun _ cache => cacheXw A J G cache)
    initial a v J ha hv hJ
  · unfold cacheXz xZ
    rw [hr0, hk0]
    simp [WeightedRow.Weights.X]
  · simp [cacheXw, xW, hr0]
  · intro θ hθ hθJ t _ cache _ hnotKill
    have hgood : OccupancyGood A decode u cache := by
      exact Classical.not_not.mp hnotKill
    change expectedValue ((OptimalOTS.oracleImpl t).run cache) (fun out =>
      ENNReal.ofReal (xPhi w θ J G (WeightedCacheCounts.seen A out.2).card
        (WeightedCacheCounts.classCounts A out.2 decode))) ≤
      ENNReal.ofReal (xPhi w θ J G (WeightedCacheCounts.seen A cache).card
        (WeightedCacheCounts.classCounts A cache decode))
    calc
      _ = ENNReal.ofReal (realEval ((OptimalOTS.oracleImpl t).run cache) (fun out =>
          xPhi w θ J G (WeightedCacheCounts.seen A out.2).card
            (WeightedCacheCounts.classCounts A out.2 decode))) :=
        (WeightedRealExecution.ofReal_realEval _ _ (fun _ => by
          unfold xPhi
          exact Real.exp_nonneg _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (actual_xPhi_step w A Gdom hAG decode hfiber
        u G θ J hG hg hθ.le hJ hθJ hcap t cache hgood)
  · intro _ _ hh
    exact hh.1
  · intro _ _ hh
    exact hh.2

end EqualityCollisionCache91

/-!
# Concrete collision cap for the cost-91 long-chain schedule

The stopped self-collision theorem requires one deterministic jump bound for
all decoder classes.  This module checks that bound against the exact
160-tier table, then connects a good completed nonce table to the real-cache
occupancy predicate used by the stopped process.
-/

noncomputable section

open OracleSpec OracleComp
open scoped Classical BigOperators

namespace OptimalOTS.WeightedConstruction.LongChain91CollisionCap

open LongChain91Security LongChain91Occupancy

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A uniform upper bound for every capped self-collision increment. -/
def collisionJumpBound : ℝ :=
  332 * (Chain18Compact.L : ℝ) ^ 2 * Chain18Compact.kappa

theorem collisionJumpBound_nonneg : 0 ≤ collisionJumpBound := by
  unfold collisionJumpBound Chain18Compact.kappa
  positivity

/-- Integer cross-multiplication of the desired rational inequality.  All
160 cases reduce to the checked compact-schedule tables. -/
theorem capTier_kernel_numerator (j : Chain18Compact.Tier) :
    2 * capTier j * Chain18Compact.aliases j *
        Chain18Compact.kernelNumerator j ^ 2 * 2 ^ 127 ≤
      332 * Chain18Compact.L ^ 2 * Chain18Compact.R *
        Chain18Compact.KQ ^ 2 := by
  revert j
  decide +kernel

/-- The rounded kernel table obeys the common jump bound. -/
theorem capTier_kernelUpper_le (j : Chain18Compact.Tier) :
    2 * (capTier j : ℝ) * Chain18Compact.probability j *
        Chain18Compact.kernelUpper j ^ 2 ≤ collisionJumpBound := by
  have hnat := capTier_kernel_numerator j
  have hcast :
      ((2 * capTier j * Chain18Compact.aliases j *
          Chain18Compact.kernelNumerator j ^ 2 * 2 ^ 127 : ℕ) : ℝ) ≤
        ((332 * Chain18Compact.L ^ 2 * Chain18Compact.R *
          Chain18Compact.KQ ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hR : 0 < (Chain18Compact.R : ℝ) := by
    norm_num [Chain18Compact.R]
  have hK : 0 < (Chain18Compact.KQ : ℝ) := by
    norm_num [Chain18Compact.KQ]
  have hP : 0 < (2 : ℝ) ^ 127 := by positivity
  have hform :
      2 * (capTier j : ℝ) * Chain18Compact.probability j *
          Chain18Compact.kernelUpper j ^ 2 =
        ((2 * capTier j * Chain18Compact.aliases j *
          Chain18Compact.kernelNumerator j ^ 2 : ℕ) : ℝ) /
          ((Chain18Compact.R : ℝ) * (Chain18Compact.KQ : ℝ) ^ 2) := by
    unfold Chain18Compact.probability Chain18Compact.kernelUpper
    push_cast
    field_simp [hR.ne', hK.ne']
    <;> ring
  rw [hform]
  apply (div_le_iff₀ (mul_pos hR (sq_pos_of_pos hK))).2
  rw [show collisionJumpBound *
      ((Chain18Compact.R : ℝ) * (Chain18Compact.KQ : ℝ) ^ 2) =
      ((332 : ℝ) * (Chain18Compact.L : ℝ) ^ 2 *
        ((Chain18Compact.R : ℝ) * (Chain18Compact.KQ : ℝ) ^ 2)) /
          (2 : ℝ) ^ 127 by
    unfold collisionJumpBound Chain18Compact.kappa
    rw [div_eq_mul_inv]
    ring]
  apply (le_div_iff₀ hP).2
  push_cast at hcast ⊢
  ring_nf at hcast ⊢
  exact hcast

/-- For the concrete weights, collision mass is exactly class probability
times the square of the true finite-difference kernel. -/
theorem security_collisionMass_eq (i : Fin LongChain91Security.M) :
    securityWeights.collisionMass i =
      classProbability i *
        Chain18Compact.actualKernel (LongChain91Schedule.tier i) ^ 2 := by
  rw [WeightedRow.Weights.collisionMass_eq, securityWeights_p,
    securityWeights_g, weight_ratio]

/-- The exact cap selected by `LongChain91Occupancy` supplies the uniform
`hcap` premise of `EqualityCollisionCache91.actual_stopped_x_freedman`. -/
theorem collision_cap (i : Fin LongChain91Security.M) :
    2 * (cap i : ℝ) * securityWeights.collisionMass i ≤
      collisionJumpBound := by
  have hsquare :
      Chain18Compact.actualKernel (LongChain91Schedule.tier i) ^ 2 ≤
        Chain18Compact.kernelUpper (LongChain91Schedule.tier i) ^ 2 :=
    pow_le_pow_left₀
      (Chain18Compact.actualKernel_nonneg (LongChain91Schedule.tier i))
      (Chain18Compact.actualKernel_le (LongChain91Schedule.tier i)) 2
  calc
    2 * (cap i : ℝ) * securityWeights.collisionMass i =
        (2 * (cap i : ℝ) * classProbability i) *
          Chain18Compact.actualKernel (LongChain91Schedule.tier i) ^ 2 := by
      rw [security_collisionMass_eq]
      ring
    _ ≤ (2 * (cap i : ℝ) * classProbability i) *
          Chain18Compact.kernelUpper (LongChain91Schedule.tier i) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          (classProbability_pos i).le)
    _ = 2 * (capTier (LongChain91Schedule.tier i) : ℝ) *
          Chain18Compact.probability (LongChain91Schedule.tier i) *
          Chain18Compact.kernelUpper (LongChain91Schedule.tier i) ^ 2 := by
      rfl
    _ ≤ collisionJumpBound :=
      capTier_kernelUpper_le (LongChain91Schedule.tier i)

/-! ## Completed-table occupancy bridge -/

/-- One completed length-342 table has no overfull message/class row. -/
def CompletedOccupancyGood (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits) : Prop :=
  ¬ ∃ s : Message × Fin LongChain91Security.M,
    rowOverfull s
      (WeightedReplacement.completedTable (msgBits + 86) cache g)

private theorem classCounts_mono_cache {D B ι : Type}
    [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (A : Finset D) (cache complete : D → Option B)
    (decode : B → Option ι)
    (hsub : ∀ q y, cache q = some y → complete q = some y) (i : ι) :
    WeightedCacheCounts.classCounts A cache decode i ≤
      WeightedCacheCounts.classCounts A complete decode i := by
  unfold WeightedCacheCounts.classCounts WeightedPublicCounts.counts
    WeightedCacheCounts.seen
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hseen, hdecode⟩
  rcases Finset.mem_filter.mp hseen with ⟨hA, hsome⟩
  cases hc : cache q with
  | none => simp [hc] at hsome
  | some y =>
      have hd : complete q = some y := hsub q y hc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hA, ?_⟩, ?_⟩
      · simp [hd]
      · simpa [hc, hd] using hdecode

private theorem classCounts_preload_le
    (m : Message) (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (i : Fin LongChain91Security.M) :
    WeightedCacheCounts.classCounts (WideDomains.rowDomain m) cache
        LongChain91Empirical.cacheDecode i ≤
      WeightedCacheCounts.classCounts (WideDomains.rowDomain m)
        ((WeightedReplacement.lengthSlice (msgBits + 86)).preload cache g)
        LongChain91Empirical.cacheDecode i := by
  apply classCounts_mono_cache
  intro q y hq
  exact WeightedReplacement.QuerySlice.preload_some _ _ _ q y hq

private theorem classCounts_preload_row_eq
    (m : Message) (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (i : Fin LongChain91Security.M) :
    WeightedCacheCounts.classCounts (WideDomains.rowDomain m)
        ((WeightedReplacement.lengthSlice (msgBits + 86)).preload cache g)
        LongChain91Empirical.cacheDecode i =
      (Finset.univ.filter fun η : BitVec 86 =>
        LongChain91Empirical.cacheDecode
          (WeightedReplacement.completedTable (msgBits + 86) cache g
            (m ++ η)) = some i).card := by
  let complete :=
    (WeightedReplacement.lengthSlice (msgBits + 86)).preload cache g
  have hseen :
      WeightedCacheCounts.seen (WideDomains.rowDomain m) complete =
        WideDomains.rowDomain m := by
    unfold WeightedCacheCounts.seen
    apply Finset.filter_eq_self.mpr
    intro q hq
    obtain ⟨η, rfl⟩ := (WideDomains.mem_rowDomain m q).mp hq
    have hp := WeightedReplacement.length_preload_row 86 m cache g η
    change (complete (WideForest.encQuery (m, η))).isSome = true
    simpa [complete, WideForest.encQuery] using congrArg Option.isSome hp
  unfold WeightedCacheCounts.classCounts
  rw [hseen]
  unfold WeightedPublicCounts.counts
  have himage :
      (WideDomains.rowDomain m).filter
          (fun q => (complete q).bind LongChain91Empirical.cacheDecode = some i) =
        (Finset.univ.filter fun η : BitVec 86 =>
          LongChain91Empirical.cacheDecode
            (WeightedReplacement.completedTable (msgBits + 86) cache g
              (m ++ η)) = some i).image
            (fun η => WideForest.encQuery (m, η)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqrow, hqdecode⟩ := Finset.mem_filter.mp hq
      obtain ⟨η, he⟩ := (WideDomains.mem_rowDomain m q).mp hqrow
      subst q
      apply Finset.mem_image.mpr
      refine ⟨η, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have hp := WeightedReplacement.length_preload_row 86 m cache g η
      change complete (WideForest.encQuery (m, η)) =
        some (WeightedReplacement.cachedRow 86 m cache g η) at hp
      rw [hp] at hqdecode
      simp only [Option.bind_some] at hqdecode
      simpa [WeightedReplacement.cachedRow,
        WeightedReplacement.completedTable] using hqdecode
    · intro hq
      obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hq
      apply Finset.mem_filter.mpr
      refine ⟨(WideDomains.mem_rowDomain m _).mpr ⟨η, rfl⟩, ?_⟩
      have hp := WeightedReplacement.length_preload_row 86 m cache g η
      change complete (WideForest.encQuery (m, η)) =
        some (WeightedReplacement.cachedRow 86 m cache g η) at hp
      rw [hp]
      rw [Option.bind_some]
      have hdecode := (Finset.mem_filter.mp hη).2
      simpa [WeightedReplacement.cachedRow,
        WeightedReplacement.completedTable] using hdecode
  rw [himage, Finset.card_image_of_injective]
  intro η ζ h
  exact WeightedSampling.Availability.nonce_query_inj m h

/-- A good completed table bounds every multiplicity already present in the
actual cache on the chosen message row. -/
theorem completed_occupancyGood
    (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (hgood : CompletedOccupancyGood cache g) (m : Message) :
    EqualityCollisionCache91.OccupancyGood (WideDomains.rowDomain m)
      LongChain91Empirical.cacheDecode cap cache := by
  intro i
  calc
    WeightedCacheCounts.classCounts (WideDomains.rowDomain m) cache
        LongChain91Empirical.cacheDecode i ≤
      WeightedCacheCounts.classCounts (WideDomains.rowDomain m)
        ((WeightedReplacement.lengthSlice (msgBits + 86)).preload cache g)
        LongChain91Empirical.cacheDecode i := classCounts_preload_le m cache g i
    _ = (Finset.univ.filter fun η : BitVec 86 =>
        LongChain91Empirical.cacheDecode
          (WeightedReplacement.completedTable (msgBits + 86) cache g
            (m ++ η)) = some i).card :=
      classCounts_preload_row_eq m cache g i
    _ ≤ cap i := by
      have hrow : ¬ rowOverfull (m, i)
          (WeightedReplacement.completedTable (msgBits + 86) cache g) := by
        intro hover
        exact hgood ⟨(m, i), hover⟩
      have hnamed : ¬ cap i ≤ (Finset.univ.filter fun η : BitVec 86 =>
          decodesTo i
            (WeightedReplacement.completedTable (msgBits + 86) cache g
              (rowInput m η))).card := by
        intro hover
        exact hrow ((rowOverfull_iff (m, i) _).2 hover)
      have hn : ¬ cap i ≤ (Finset.univ.filter fun η : BitVec 86 =>
          LongChain91Empirical.cacheDecode
            (WeightedReplacement.completedTable (msgBits + 86) cache g
              (m ++ η)) = some i).card := by
        have hfilters :
            (Finset.univ.filter fun η : BitVec 86 =>
              decodesTo i
                (WeightedReplacement.completedTable (msgBits + 86) cache g
                  (rowInput m η))) =
              (Finset.univ.filter fun η : BitVec 86 =>
                LongChain91Empirical.cacheDecode
                  (WeightedReplacement.completedTable (msgBits + 86) cache g
                    (m ++ η)) = some i) := by
          apply Finset.filter_congr
          intro η hη
          rfl
        have hcards := congrArg Finset.card hfilters
        rw [hcards] at hnamed
        exact hnamed
      omega

end OptimalOTS.WeightedConstruction.LongChain91CollisionCap
