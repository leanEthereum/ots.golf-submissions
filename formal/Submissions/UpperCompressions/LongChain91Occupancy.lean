import Submissions.UpperCompressions.LongChain91SecurityData
import Submissions.UpperCompressions.ProofBundle06
import Submissions.UpperCompressions.LongChain91Empirical

/-!
# Simultaneous row-occupancy control for the cost-91 decoder

The equality-only collision clock needs a bound on repeated occurrences of
one decoded class in one complete message row.  This file proves the bound on
the eager uniform table.  The threshold is six times the exact class mean,
plus 512; a Bernstein product potential gives enough slack to union over all
`2^256` messages and every concrete class.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

-- The concrete decoder has a large, kernel-checked normal form.  Keep enough
-- elaborator depth for the three specializations below without changing any
-- proof or computation bound.
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace WeightedReplacement

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

local instance {α : Type*} : DecidableEq α := Classical.decEq α

/-- At `theta = 2`, a centered Bernoulli variable with mean `mu` pays the
exact Bernstein compensator `6*mu`. -/
theorem uniformMean_indicator_mgf_two {W : Type*} [Fintype W] [Nonempty W]
    (P : W → Prop) :
    uniformMean (fun w => Real.exp
      (2 * ((if P w then (1 : ℝ) else 0) - fraction P) - 6 * fraction P)) ≤ 1 := by
  let U : W → ℝ := fun w => if P w then 1 else 0
  have hmean : meanLinear W U = fraction P := by
    rfl
  have h := WeightedMGF.nonnegative_centered_mgf
    (meanLinear W) (fun f g hfg => uniformMean_mono f g hfg)
    (uniformMean_const 1) U 2 1 (by norm_num) (by norm_num) (by norm_num)
    (fun w => by dsimp [U]; split_ifs <;> norm_num)
    (fun w => by dsimp [U]; split_ifs <;> norm_num)
  rw [hmean] at h
  have hcomp :
      2 ^ 2 * (1 * fraction P) / (2 * (1 - 2 * 1 / 3)) = 6 * fraction P := by
    ring
  rw [hcomp] at h
  have hf : (fun w => Real.exp
      (2 * (U w - fraction P) - 6 * fraction P)) =
      (fun w => Real.exp (2 * (U w - fraction P)) *
        Real.exp (-6 * fraction P)) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    ring
  change uniformMean (fun w => Real.exp
    (2 * (U w - fraction P) - 6 * fraction P)) ≤ 1
  rw [hf, uniformMean_mul_const]
  calc
    _ ≤ Real.exp (6 * fraction P) * Real.exp (-6 * fraction P) :=
      mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

theorem fraction_eq_filter_card {W : Type*} [Fintype W]
    (P : W → Prop) :
    fraction P = ((Finset.univ.filter P).card : ℝ) / Fintype.card W := by
  unfold fraction uniformMean
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Product Bernstein bound for a rare predicate.  If the integer threshold
is at least `6*N*mu+512`, reaching it has probability at most `exp(-700)`.
The deliberately rounded exponent leaves a large exact union-bound margin. -/
theorem uniform_table_occupancy_tail {D W : Type*}
    [Fintype D] [Nonempty D] [Fintype W] [Nonempty W]
    (P : W → Prop) (u : ℕ)
    (hu : 6 * (Fintype.card D : ℝ) * fraction P + 512 ≤ (u : ℝ)) :
    uniformMean (fun g : D → W =>
      if u ≤ (Finset.univ.filter fun d => P (g d)).card then (1 : ℝ) else 0) ≤
      Real.exp (-700) := by
  let U : W → ℝ := fun w => if P w then 1 else 0
  let Z : (D → W) → ℝ := fun g =>
    ∑ d, (2 * (U (g d) - fraction P) - 6 * fraction P)
  have hmgf : uniformMean (fun g : D → W => Real.exp (Z g)) ≤ 1 := by
    have hexp : (fun g : D → W => Real.exp (Z g)) =
        (fun g => ∏ d, Real.exp
          (2 * (U (g d) - fraction P) - 6 * fraction P)) := by
      funext g
      exact Real.exp_sum _ _
    rw [hexp, uniformMean_product (fun _d : D => fun w => Real.exp
      (2 * (U w - fraction P) - 6 * fraction P))]
    calc
      (∏ _d : D, uniformMean (fun w => Real.exp
          (2 * (U w - fraction P) - 6 * fraction P))) ≤
          ∏ _d : D, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro d hd
          unfold uniformMean
          exact div_nonneg (Finset.sum_nonneg fun w _ => Real.exp_nonneg _)
            (Nat.cast_nonneg _)
        · intro d hd
          exact uniformMean_indicator_mgf_two P
      _ = 1 := by simp
  have hmu : 0 ≤ fraction P := by
    unfold fraction uniformMean
    exact div_nonneg (Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num)
      (Nat.cast_nonneg _)
  apply WeightedKernel.exponential_tail (meanLinear (D → W))
    (fun f g hfg => uniformMean_mono f g hfg)
    (fun g : D → W => u ≤ (Finset.univ.filter fun d => P (g d)).card)
    Z 700
  · intro g hg
    have hcount : (u : ℝ) ≤ ∑ d : D, U (g d) := by
      have hn : u ≤ (Finset.univ.filter fun d => P (g d)).card := hg
      have hsum : (∑ d : D, U (g d)) =
          ((Finset.univ.filter fun d => P (g d)).card : ℝ) := by
        dsimp [U]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hsum]
      exact_mod_cast hn
    have hsum_expand :
        (∑ d : D, (2 * (U (g d) - fraction P) - 6 * fraction P)) =
          2 * (∑ d : D, U (g d)) -
            8 * (Fintype.card D : ℝ) * fraction P := by
      calc
        _ = ∑ d : D, (2 * U (g d) - 8 * fraction P) := by
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = 2 * (∑ d : D, U (g d)) -
            8 * (Fintype.card D : ℝ) * fraction P := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
    dsimp [Z]
    rw [hsum_expand]
    nlinarith
  · exact hmgf

/-- Restrict a larger uniform table to an injectively embedded row and apply
the product occupancy bound. -/
theorem E_table_occupancy_tail {A B W : Type}
    [Fintype A] [Nonempty A] [Fintype B] [Fintype W] [Nonempty W]
    [SampleableType W] [SampleableType (A → W)] [SampleableType (B → W)]
    (e : A → B) (he : Function.Injective e) (P : W → Prop) (u : ℕ)
    (hu : 6 * (Fintype.card A : ℝ) * fraction P + 512 ≤ (u : ℝ)) :
    E ($ᵗ (B → W)) (fun g =>
      if u ≤ (Finset.univ.filter fun a => P (g (e a))).card then 1 else 0) ≤
      ENNReal.ofReal (Real.exp (-700)) := by
  let f : (A → W) → ℝ≥0∞ := fun g =>
    if u ≤ (Finset.univ.filter fun a => P (g a)).card then 1 else 0
  have hx := E_uniform_ofReal (fun g : A → W =>
    if u ≤ (Finset.univ.filter fun a => P (g a)).card then (1 : ℝ) else 0)
    (fun g => by split_ifs <;> norm_num)
  simp only [apply_ite, ENNReal.ofReal_one, ENNReal.ofReal_zero] at hx
  calc
    _ ≤ E ($ᵗ (B → W)) (fun g => f (g ∘ e)) := by
      apply E_mono
      intro g
      rfl
    _ = E ($ᵗ (A → W)) f := E_uniform_restrict e he f
    _ = ENNReal.ofReal (uniformMean (fun g : A → W =>
        if u ≤ (Finset.univ.filter fun a => P (g a)).card then (1 : ℝ) else 0)) := by
      exact hx
    _ ≤ ENNReal.ofReal (Real.exp (-700)) :=
      ENNReal.ofReal_le_ofReal (uniform_table_occupancy_tail P u hu)

end WeightedReplacement

namespace OptimalOTS.WeightedConstruction.LongChain91Occupancy

open WeightedReplacement
open LongChain91Security

abbrev M := LongChain91Security.M

/-- Opaque names keep the concrete 160-case decoder out of definitional
equality checks on whole random tables. -/
def decodesTo (i : Fin M) (x : BitVec hashBits) : Prop :=
  LongChain91Empirical.cacheDecode x = some i

def rowInput (m : Message) (eta : BitVec 86) : BitVec (msgBits + 86) :=
  m ++ eta

theorem rowInput_injective (m : Message) : Function.Injective (rowInput m) := by
  intro a b h
  exact WeightedReplacement.append_right_injective m h

/-- Exact integer ceiling of six full-row means, with a 512-count buffer. -/
def capTier (j : Chain18Compact.Tier) : ℕ :=
  (6 * 2^86 * Chain18Compact.aliases j + Chain18Compact.R - 1) /
      Chain18Compact.R + 512

def cap (i : Fin M) : ℕ := capTier (LongChain91Schedule.tier i)

/-- The ceiling arithmetic is certified over the emitted 160-entry table. -/
theorem capTier_numerator (j : Chain18Compact.Tier) :
    6 * 2^86 * Chain18Compact.aliases j ≤
      (capTier j - 512) * Chain18Compact.R := by
  revert j
  decide +kernel

theorem uniform_decode_probability (i : Fin M) :
    fraction (decodesTo i) =
      classProbability i := by
  rw [fraction_eq_filter_card]
  have hs : (Finset.univ.filter (decodesTo i)) =
      Finset.univ.filter (fun x : BitVec hashBits =>
        LongChain91Empirical.cacheDecode x = some i) := by
    apply Finset.filter_congr
    intro x hx
    rfl
  rw [hs]
  simpa only [WeightedRow.Weights.classMass,
    LongChain91Security.securityWeights_p] using
      LongChain91Empirical.cache_decoder_law (some i)

theorem cap_mean (i : Fin M) :
    6 * (Fintype.card (BitVec 86) : ℝ) *
        fraction (decodesTo i) + 512 ≤
      (cap i : ℝ) := by
  rw [uniform_decode_probability]
  rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  unfold classProbability Chain18Compact.probability cap
  have hn := capTier_numerator (LongChain91Schedule.tier i)
  have hR : (0 : ℝ) < Chain18Compact.R := by norm_num [Chain18Compact.R]
  have hsub : 512 ≤ capTier (LongChain91Schedule.tier i) := by
    simp [capTier]
  have hcast :
      (6 * 2^86 * Chain18Compact.aliases (LongChain91Schedule.tier i) : ℝ) ≤
        ((capTier (LongChain91Schedule.tier i) - 512 : ℕ) : ℝ) *
          (Chain18Compact.R : ℝ) := by
    exact_mod_cast hn
  have hdiv := (div_le_iff₀ hR).2 hcast
  rw [Nat.cast_sub hsub] at hdiv
  have hdiv' :
      (6 * 2^86 * Chain18Compact.aliases (LongChain91Schedule.tier i) : ℝ) /
          (Chain18Compact.R : ℝ) ≤
        (capTier (LongChain91Schedule.tier i) : ℝ) - 512 := by
    simpa only [Nat.cast_ofNat] using hdiv
  calc
    6 * (2 : ℝ) ^ 86 *
          ((Chain18Compact.aliases (LongChain91Schedule.tier i) : ℝ) /
            (Chain18Compact.R : ℝ)) + 512 =
        (6 * (2 : ℝ) ^ 86 *
          (Chain18Compact.aliases (LongChain91Schedule.tier i) : ℝ)) /
            (Chain18Compact.R : ℝ) + 512 := by ring
    _ ≤ ((capTier (LongChain91Schedule.tier i) : ℝ) - 512) + 512 :=
      by simpa only [add_comm] using add_le_add_right hdiv' 512
    _ = (capTier (LongChain91Schedule.tier i) : ℝ) := by ring

def rowOverfull (s : Message × Fin M)
    (g : BitVec (msgBits + 86) → BitVec hashBits) : Prop :=
  cap s.2 ≤ (Finset.univ.filter fun η : BitVec 86 =>
    decodesTo s.2 (g (rowInput s.1 η))).card

theorem rowOverfull_iff (s : Message × Fin M)
    (g : BitVec (msgBits + 86) → BitVec hashBits) :
    rowOverfull s g ↔
      cap s.2 ≤ (Finset.univ.filter fun η : BitVec 86 =>
        decodesTo s.2 (g (rowInput s.1 η))).card := by
  rfl

theorem rowOverfull_probability (s : Message × Fin M) :
    E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
      (fun g => if rowOverfull s g then 1 else 0) ≤
      (2 : ℝ≥0∞)⁻¹^700 := by
  have h := E_table_occupancy_tail
    (rowInput s.1)
    (rowInput_injective s.1)
    (decodesTo s.2)
    (cap s.2) (cap_mean s.2)
  have hnamed :
      E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
          (fun g => if rowOverfull s g then 1 else 0) ≤
        ENNReal.ofReal (Real.exp (-700)) := by
    calc
      _ ≤ E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
          (fun g => if cap s.2 ≤ (Finset.univ.filter fun eta : BitVec 86 =>
            decodesTo s.2 (g (rowInput s.1 eta))).card then 1 else 0) := by
        apply E_mono
        intro g
        by_cases hr : rowOverfull s g
        · have he : cap s.2 ≤ (Finset.univ.filter fun eta : BitVec 86 =>
              decodesTo s.2 (g (rowInput s.1 eta))).card :=
            (rowOverfull_iff s g).1 hr
          simp only [if_pos hr, if_pos he]
          exact le_rfl
        · have he : ¬ cap s.2 ≤ (Finset.univ.filter fun eta : BitVec 86 =>
              decodesTo s.2 (g (rowInput s.1 eta))).card :=
            fun h => hr ((rowOverfull_iff s g).2 h)
          simp only [if_neg hr, if_neg he]
          exact le_rfl
      _ ≤ _ := h
  have hexp : Real.exp (-700) ≤ (2 : ℝ)⁻¹^700 := by
    have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      Real.exp (-700) = (Real.exp 1)⁻¹^700 := by
        rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul]
        norm_num
      _ ≤ (2 : ℝ)⁻¹^700 := pow_le_pow_left₀ (by positivity)
        (inv_anti₀ (by norm_num) he) 700
  have hof : ENNReal.ofReal ((2 : ℝ)⁻¹^700) = (2 : ℝ≥0∞)⁻¹^700 := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  exact hnamed.trans (hof ▸ ENNReal.ofReal_le_ofReal hexp)

theorem class_count_lt_pow : M < 2^110 := by
  rw [show M = Chain18Compact.familyCardinality by rfl,
    Chain18Compact.familyCardinality_exact]
  norm_num

/-- One eager table simultaneously satisfies every message/class occupancy
cap except with probability at most `2^-334`. -/
theorem full_table_overfull_probability :
    E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
      (fun g => if ∃ s : Message × Fin M, rowOverfull s g then 1 else 0) ≤
      (2 : ℝ≥0∞)⁻¹^334 := by
  have hb : ∀ s : Message × Fin M,
      E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
        (fun g => if rowOverfull s g then 1 else 0) ≤
        (2 : ℝ≥0∞)⁻¹^700 := by
    intro s
    exact rowOverfull_probability s
  have h := E_finite_union ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
    rowOverfull
    ((2 : ℝ≥0∞)⁻¹^700) hb
  have hc : (Fintype.card (Message × Fin M) : ℝ≥0∞) ≤ (2 : ℝ≥0∞)^366 := by
    have hn : Fintype.card (Message × Fin M) ≤ 2^366 := by
      rw [Fintype.card_prod, Fintype.card_fin]
      have hm : M ≤ 2^110 := class_count_lt_pow.le
      have hmsg : Fintype.card Message = 2^256 := by norm_num [Message, msgBits]
      rw [hmsg]
      calc
        2^256 * M ≤ 2^256 * 2^110 := Nat.mul_le_mul_left _ hm
        _ = 2^366 := by rw [← pow_add]
    exact_mod_cast hn
  calc
    _ ≤ (Fintype.card (Message × Fin M) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹^700 := h
    _ ≤ (2 : ℝ≥0∞)^366 * (2 : ℝ≥0∞)⁻¹^700 := mul_le_mul' hc le_rfl
    _ = (2 : ℝ≥0∞)⁻¹^334 := by
      rw [show 700 = 366 + 334 by omega, pow_add, ← mul_assoc, ← mul_pow]
      have hh : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [hh, one_pow, one_mul]

end OptimalOTS.WeightedConstruction.LongChain91Occupancy
