import Submissions.UpperCompressions.LongChain91SecurityData
import Submissions.UpperCompressions.ProofBundle11

/-!
# Empirical prefix control for the chain-18, 160-tier schedule

This file specializes the generic finite-row concentration and first-minimum
kernel lemmas to the concrete 91-compression decoder.  All prefix probabilities
are probabilities in the full 256-bit output space, including the rejection
atom.
-/

namespace OptimalOTS.WeightedConstruction.LongChain91Empirical

open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
open WeightedReplacement WeightedCompletion

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

abbrev Tier := LongChain91Security.Tier
abbrev M := LongChain91Security.M

abbrev decode : BitVec 256 → Option (Fin M) := LongChain91Schedule.decode
abbrev classTier : Fin M → Tier := LongChain91Schedule.tier
def rank (i : Fin M) : ℕ := (classTier i).val

abbrev classProbability := LongChain91Security.classProbability
abbrev referenceWeight := LongChain91Security.referenceWeight
abbrev securityWeights := LongChain91Security.securityWeights
abbrev excess := LongChain91Security.excess

/-! ## Exact full-output prefix probabilities -/

def prefixLt (j : ℕ) (x : BitVec 256) : Prop :=
  match LongChain91Schedule.rawTier x with
  | none => False
  | some t => t.val < j

def prefixLe (j : ℕ) (x : BitVec 256) : Prop :=
  match LongChain91Schedule.rawTier x with
  | none => False
  | some t => t.val ≤ j

theorem rawTier_eq_decode_map (x : BitVec 256) :
    LongChain91Schedule.rawTier x = (decode x).map classTier := by
  change LongChain91Schedule.rawTier x =
    (LongChain91Schedule.decode x).map LongChain91Schedule.tier
  unfold LongChain91Schedule.rawTier LongChain91Schedule.decode
    LongChain91Schedule.rawClass LongChain91Schedule.tier
  cases h : LongChain91Schedule.rawAlias x with
  | none => simp [h]
  | some a => simp [h]

theorem prefixLt_decode (j : ℕ) (x : BitVec 256) :
    prefixLt j x ↔
      match decode x with | none => False | some i => rank i < j := by
  rw [prefixLt, rawTier_eq_decode_map]
  cases decode x <;> simp [rank]

theorem prefixLe_decode (j : ℕ) (x : BitVec 256) :
    prefixLe j x ↔
      match decode x with | none => False | some i => rank i ≤ j := by
  rw [prefixLe, rawTier_eq_decode_map]
  cases decode x <;> simp [rank]

theorem uniform_decode_probability (i : Fin M) :
    uniformMean (fun x : BitVec 256 => if decode x = some i then 1 else 0) =
      classProbability i := by
  rw [WeightedCompletion.uniformMean_indicator]
  rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  exact LongChain91Security.class_probability_real i

theorem prefix_mass_nat (j : Tier) :
    (∑ t : Tier, if t.val < j.val then Chain18Compact.tierMass t else 0) =
      Chain18Compact.prefixMass j := by
  revert j
  decide +kernel

theorem prefix_le_mass_nat (j : Tier) :
    (∑ t : Tier, if t.val ≤ j.val then Chain18Compact.tierMass t else 0) =
      Chain18Compact.prefixMass j + Chain18Compact.tierMass j := by
  revert j
  decide +kernel

private theorem prefixLt_score (j : ℕ) :
    (fun x : BitVec 256 => if prefixLt j x then (1 : ℝ) else 0) =
      fun x => WeightedCompletion.score (decode x)
        (fun i => if rank i < j then 1 else 0) := by
  funext x
  cases hx : decode x with
  | none =>
      have hr := rawTier_eq_decode_map x
      rw [hx] at hr
      simp [prefixLt, hr, WeightedCompletion.score, hx]
  | some i =>
      rw [if_congr (prefixLt_decode j x) rfl rfl]
      simp [WeightedCompletion.score, hx]

private theorem prefixLe_score (j : ℕ) :
    (fun x : BitVec 256 => if prefixLe j x then (1 : ℝ) else 0) =
      fun x => WeightedCompletion.score (decode x)
        (fun i => if rank i ≤ j then 1 else 0) := by
  funext x
  cases hx : decode x with
  | none =>
      have hr := rawTier_eq_decode_map x
      rw [hx] at hr
      simp [prefixLe, hr, WeightedCompletion.score, hx]
  | some i =>
      rw [if_congr (prefixLe_decode j x) rfl rfl]
      simp [WeightedCompletion.score, hx]

theorem prefixLt_probability (j : Tier) :
    fraction (prefixLt j.val) =
      (Chain18Compact.prefixMass j : ℝ) / (Chain18Compact.R : ℝ) := by
  unfold fraction
  rw [prefixLt_score, WeightedCompletion.mean_score decode classProbability
    (fun i => if rank i < j.val then 1 else 0) uniform_decode_probability]
  change (∑ i : Fin M, Chain18Compact.probability (LongChain91Schedule.tier i) *
    (if (LongChain91Schedule.tier i).val < j.val then 1 else 0)) = _
  rw [LongChain91Security.sum_tier
    (fun t => Chain18Compact.probability t * (if t.val < j.val then 1 else 0))]
  calc
    (∑ t : Tier, (Chain18Compact.classes t : ℝ) *
        (Chain18Compact.probability t * (if t.val < j.val then 1 else 0))) =
        ∑ t : Tier,
          (((if t.val < j.val then Chain18Compact.tierMass t else 0 : ℕ) : ℝ) /
            (Chain18Compact.R : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      unfold Chain18Compact.probability Chain18Compact.tierMass
      split_ifs <;> push_cast <;> ring
    _ = (((∑ t : Tier,
          if t.val < j.val then Chain18Compact.tierMass t else 0 : ℕ) : ℝ) /
          (Chain18Compact.R : ℝ)) := by
      push_cast
      rw [Finset.sum_div]
    _ = _ := by rw [prefix_mass_nat]

theorem prefixLe_probability (j : Tier) :
    fraction (prefixLe j.val) =
      (Chain18Compact.prefixMass j + Chain18Compact.tierMass j : ℕ) /
        (Chain18Compact.R : ℝ) := by
  unfold fraction
  rw [prefixLe_score, WeightedCompletion.mean_score decode classProbability
    (fun i => if rank i ≤ j.val then 1 else 0) uniform_decode_probability]
  change (∑ i : Fin M, Chain18Compact.probability (LongChain91Schedule.tier i) *
    (if (LongChain91Schedule.tier i).val ≤ j.val then 1 else 0)) = _
  rw [LongChain91Security.sum_tier
    (fun t => Chain18Compact.probability t * (if t.val ≤ j.val then 1 else 0))]
  calc
    (∑ t : Tier, (Chain18Compact.classes t : ℝ) *
        (Chain18Compact.probability t * (if t.val ≤ j.val then 1 else 0))) =
        ∑ t : Tier,
          (((if t.val ≤ j.val then Chain18Compact.tierMass t else 0 : ℕ) : ℝ) /
            (Chain18Compact.R : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      unfold Chain18Compact.probability Chain18Compact.tierMass
      split_ifs <;> push_cast <;> ring
    _ = (((∑ t : Tier,
          if t.val ≤ j.val then Chain18Compact.tierMass t else 0 : ℕ) : ℝ) /
          (Chain18Compact.R : ℝ)) := by
      push_cast
      rw [Finset.sum_div]
    _ = _ := by rw [prefix_le_mass_nat]

theorem prefixLe_eq (j : ℕ) : prefixLe j = prefixLt (j + 1) := by
  funext x
  apply propext
  unfold prefixLe prefixLt
  cases LongChain91Schedule.rawTier x <;> simp [Nat.lt_succ_iff]

theorem fraction_not {D : Type} [Fintype D] [Nonempty D] (P : D → Prop) :
    fraction (fun x => ¬ P x) = 1 - fraction P := by
  unfold fraction uniformMean
  rw [eq_sub_iff_add_eq, ← add_div]
  have hs : (∑ x : D, if ¬ P x then (1 : ℝ) else 0) +
      (∑ x : D, if P x then (1 : ℝ) else 0) = Fintype.card D := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x : D, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : P x <;> simp [h]
      _ = _ := by simp
  convert div_self (show (Fintype.card D : ℝ) ≠ 0 by
    exact_mod_cast Fintype.card_ne_zero) using 1
  congr 1
  convert hs using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : P x <;> simp [h]

theorem weakRank_prefix (i : Fin M) :
    WeightedReplacement.weakRank rank i ∘ decode =
      fun x => ¬ prefixLt (rank i) x := by
  funext x
  apply propext
  cases hx : decode x with
  | none =>
      have hr := rawTier_eq_decode_map x
      rw [hx] at hr
      simp [Function.comp_apply, WeightedReplacement.weakRank, prefixLt, hr, hx]
  | some a =>
      have h := prefixLt_decode (rank i) x
      rw [hx] at h
      simp only at h
      simp [Function.comp_apply, WeightedReplacement.weakRank, hx, h]

theorem strictRank_prefix (i : Fin M) :
    WeightedReplacement.strictRank rank i ∘ decode =
      fun x => ¬ prefixLe (rank i) x := by
  funext x
  apply propext
  cases hx : decode x with
  | none =>
      have hr := rawTier_eq_decode_map x
      rw [hx] at hr
      simp [Function.comp_apply, WeightedReplacement.strictRank, prefixLe, hr, hx]
  | some a =>
      have h := prefixLe_decode (rank i) x
      rw [hx] at h
      simp only at h
      simp [Function.comp_apply, WeightedReplacement.strictRank, hx, h]

theorem weakRank_probability (i : Fin M) :
    fraction (WeightedReplacement.weakRank rank i ∘ decode) =
      Chain18Compact.survival (Chain18Compact.prefixMass (classTier i)) := by
  rw [weakRank_prefix, fraction_not]
  have hp := prefixLt_probability (classTier i)
  change fraction (prefixLt (rank i)) = _ at hp
  rw [hp]
  rfl

/-! ## Empirical row envelope and the concrete kernel bridge -/

def rowGood {D : Type} [Fintype D] (table : D → Option (Fin M)) : Prop := ∀ i,
  fraction (WeightedReplacement.weakRank rank i ∘ table) ≤
      Chain18Compact.survival (Chain18Compact.prefixMass (classTier i)) +
        LongChain91Security.empiricalDelta ∧
  fraction (WeightedReplacement.strictRank rank i ∘ table) ≤
      Chain18Compact.survival
        (Chain18Compact.prefixMass (classTier i) + Chain18Compact.tierMass (classTier i)) +
        LongChain91Security.empiricalDelta

theorem rowGood_kernel {D : Type} [Fintype D] [Nonempty D]
    (table : D → Option (Fin M)) (hg : rowGood table) (i : Fin M) :
    WeightedReplacement.kernel Chain18Compact.L
      (fraction (WeightedReplacement.weakRank rank i ∘ table))
      (fraction (WeightedReplacement.strictRank rank i ∘ table)) ≤
        (99 / 98 : ℝ) * (referenceWeight i / classProbability i) := by
  apply LongChain91Security.empirical_kernel_le i _ _ _ _ (hg i).1 (hg i).2
  all_goals
    unfold fraction uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg _

def prefixPredicates (j : Tier) : BitVec 256 → Prop := prefixLe j.val

theorem empirical_eq_fraction {D : Type} [Fintype D]
    (P : BitVec 256 → Prop) (row : D → BitVec 256) :
    WeightedReplacement.empirical P row = fraction (P ∘ row) := rfl

theorem fraction_le_one {D : Type} [Fintype D] [Nonempty D] (P : D → Prop) :
    fraction P ≤ 1 := by
  unfold fraction
  exact (uniformMean_mono _ (fun _ => 1)
    (fun _ => by split_ifs <;> norm_num)).trans_eq (uniformMean_const 1)

theorem prefixMass_zero (j : Tier) (hj : j.val = 0) :
    Chain18Compact.prefixMass j = 0 := by
  have he : j = ⟨0, by omega⟩ := Fin.ext hj
  rw [he]
  rfl

theorem prefix_deficits_rowGood {D : Type} [Fintype D] [Nonempty D]
    [DecidableEq D] (row : D → BitVec 256)
    (hgood : ∀ j : Tier,
      fraction (prefixPredicates j) - LongChain91Security.empiricalDelta <
        WeightedReplacement.empirical (prefixPredicates j) row) :
    rowGood (decode ∘ row) := by
  intro i
  have hw : WeightedReplacement.weakRank rank i ∘ (decode ∘ row) =
      fun a => ¬ prefixLt (rank i) (row a) := by
    funext a
    exact congrArg (fun f => f (row a)) (weakRank_prefix i)
  have hs : WeightedReplacement.strictRank rank i ∘ (decode ∘ row) =
      fun a => ¬ prefixLe (rank i) (row a) := by
    funext a
    exact congrArg (fun f => f (row a)) (strictRank_prefix i)
  constructor
  · by_cases h0 : rank i = 0
    · have hh := fraction_le_one
          (WeightedReplacement.weakRank rank i ∘ (decode ∘ row))
      rw [prefixMass_zero (classTier i) h0]
      simp only [Chain18Compact.survival, Nat.cast_zero, zero_div, sub_zero]
      exact hh.trans (le_add_of_nonneg_right (by
        unfold LongChain91Security.empiricalDelta
        positivity))
    · let j : Tier := ⟨rank i - 1, by
          unfold rank
          have hi := (classTier i).isLt
          omega⟩
      have hp : prefixPredicates j = prefixLt (rank i) := by
        unfold prefixPredicates
        rw [prefixLe_eq]
        congr 1
        dsimp only [j]
        omega
      have hg := hgood j
      rw [hp, empirical_eq_fraction] at hg
      have hprob := prefixLt_probability (classTier i)
      change fraction (prefixLt (rank i)) = _ at hprob
      rw [hprob] at hg
      rw [hw, fraction_not]
      change 1 - fraction (prefixLt (rank i) ∘ row) ≤
        1 - (Chain18Compact.prefixMass (classTier i) : ℝ) /
          (Chain18Compact.R : ℝ) + LongChain91Security.empiricalDelta
      linarith
  · have hg := hgood (classTier i)
    change fraction (prefixLe (rank i)) - LongChain91Security.empiricalDelta <
      WeightedReplacement.empirical (prefixLe (rank i)) row at hg
    rw [empirical_eq_fraction] at hg
    have hprob := prefixLe_probability (classTier i)
    change fraction (prefixLe (rank i)) = _ at hprob
    rw [hprob] at hg
    rw [hs, fraction_not]
    change 1 - fraction (prefixLe (rank i) ∘ row) ≤
      1 - (Chain18Compact.prefixMass (classTier i) +
        Chain18Compact.tierMass (classTier i) : ℕ) /
          (Chain18Compact.R : ℝ) + LongChain91Security.empiricalDelta
    linarith

/-! ## A single 160-prefix completion event -/

/-- The same concrete decoder at the contract's named oracle width. -/
abbrev cacheDecode : BitVec hashBits → Option (Fin M) :=
  LongChain91Schedule.decode

theorem cache_decoder_law (x : Option (Fin M)) :
    ((Finset.univ.filter fun b : BitVec hashBits => cacheDecode b = x).card : ℝ) /
        Fintype.card (BitVec hashBits) = securityWeights.classMass x := by
  change ((Finset.univ.filter fun b : BitVec 256 => decode b = x).card : ℝ) /
      Fintype.card (BitVec 256) = securityWeights.classMass x
  exact LongChain91Security.decoder_law x

def cachePrefixPredicates (j : Tier) : BitVec hashBits → Prop :=
  fun x => prefixLe j.val x

def rowDeficitBad160 (P : Tier → BitVec hashBits → Prop)
    (s : Message × Tier)
    (g : BitVec (msgBits + 86) → BitVec hashBits) : Prop :=
  WeightedReplacement.empirical (P s.2)
      (fun η : BitVec 86 => g (s.1 ++ η)) ≤
    fraction (P s.2) - LongChain91Security.empiricalDelta

def fullRowBad160 (P : Tier → BitVec hashBits → Prop)
    (g : BitVec (msgBits + 86) → BitVec hashBits) : Prop :=
  ∃ s : Message × Tier, rowDeficitBad160 P s g

theorem fullRowBad160_iff (P : Tier → BitVec hashBits → Prop)
    (g : BitVec (msgBits + 86) → BitVec hashBits) :
    fullRowBad160 P g ↔
      ∃ s : Message × Tier, rowDeficitBad160 P s g := by
  unfold fullRowBad160
  rfl

theorem empiricalDelta_eq :
    LongChain91Security.empiricalDelta = 1 / (100 * (2 : ℝ)^20) := by
  norm_num [LongChain91Security.empiricalDelta, Chain18Compact.L]

theorem full_table_bad_probability160_explicit
    (P : Tier → BitVec hashBits → Prop) :
    E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
      (fun g => if ∃ s : Message × Tier, rowDeficitBad160 P s g
        then 1 else 0) ≤ (2 : ℝ≥0∞)⁻¹^760 := by
  have hb (s : Message × Tier) :
      E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
        (fun g => if rowDeficitBad160 P s g then 1 else 0) ≤
          (2 : ℝ≥0∞)⁻¹^1024 := by
    have hx := WeightedReplacement.E_table_deficit
      (fun η : BitVec 86 => s.1 ++ η)
      (WeightedReplacement.append_right_injective s.1) (P s.2)
      LongChain91Security.empiricalDelta
      (by rw [empiricalDelta_eq]; positivity)
      (by rw [empiricalDelta_eq]; norm_num)
    have he : ENNReal.ofReal ((2 : ℝ)⁻¹^1024) =
        (2 : ℝ≥0∞)⁻¹^1024 := by
      rw [ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    apply hx.trans
    rw [empiricalDelta_eq]
    exact he ▸ ENNReal.ofReal_le_ofReal
      WeightedReplacement.concrete_row_exponent
  have hu := WeightedReplacement.E_finite_union
    ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
    (rowDeficitBad160 P)
    ((2 : ℝ≥0∞)⁻¹^1024) hb
  have hc : (Fintype.card (Message × Tier) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)^264 := by
    have hn : Fintype.card (Message × Tier) ≤ 2^264 := by
      have hcard : Fintype.card (Message × Tier) = 2^256 * 160 := by
        norm_num [Message, msgBits, Tier, Fintype.card_prod,
          Fintype.card_bitVec]
      rw [hcard]
      calc
        2^256 * 160 ≤ 2^256 * 2^8 := Nat.mul_le_mul_left _ (by norm_num)
        _ = 2^264 := by rw [← pow_add]
    exact_mod_cast hn
  have hnum : (Fintype.card (Message × Tier) : ℝ≥0∞) *
      (2 : ℝ≥0∞)⁻¹^1024 ≤ (2 : ℝ≥0∞)⁻¹^760 := by
    calc
      _ ≤ (2 : ℝ≥0∞)^264 * (2 : ℝ≥0∞)⁻¹^1024 :=
        mul_le_mul' hc le_rfl
      _ = (2 : ℝ≥0∞)⁻¹^760 := by
        rw [show (1024 : ℕ) = 264 + 760 by omega, pow_add,
          ← mul_assoc, ← mul_pow]
        have hh : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [hh, one_pow, one_mul]
  exact le_trans hu hnum

theorem full_table_bad_probability160
    (P : Tier → BitVec hashBits → Prop) :
    E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
      (fun g => if fullRowBad160 P g then 1 else 0) ≤
        (2 : ℝ≥0∞)⁻¹^760 := by
  calc
    _ ≤ E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
        (fun g => if ∃ s : Message × Tier, rowDeficitBad160 P s g
          then 1 else 0) := by
      apply E_mono
      intro g
      by_cases he : ∃ s : Message × Tier, rowDeficitBad160 P s g
      · have hn : fullRowBad160 P g := (fullRowBad160_iff P g).2 he
        simp only [if_pos hn, if_pos he]
        exact le_rfl
      · have hn : ¬ fullRowBad160 P g :=
          fun h => he ((fullRowBad160_iff P g).1 h)
        simp only [if_neg hn, if_neg he]
        exact le_rfl
    _ ≤ _ := full_table_bad_probability160_explicit P

def fullTableGood (g : BitVec (msgBits + 86) → BitVec hashBits) : Prop :=
  ¬ fullRowBad160 cachePrefixPredicates g

theorem fullTableGood_row
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (hg : fullTableGood g) (m : Message) :
    rowGood (cacheDecode ∘
      (fun η : BitVec 86 => g (m ++ η))) := by
  change rowGood (decode ∘ (fun η : BitVec 86 => g (m ++ η)))
  apply prefix_deficits_rowGood
  intro j
  apply lt_of_not_ge
  intro hj
  apply hg
  exact (fullRowBad160_iff cachePrefixPredicates g).2 ⟨(m, j), hj⟩

theorem completed_full_bad_probability160 { α : Type }
    (oa : OracleComp Spec α) (c : Cache)
    (hc : ∀ x : BitVec (msgBits + 86), c ⟨msgBits + 86, x⟩ = none)
    (P : Tier → BitVec hashBits → Prop) :
    E (run oa c) (fun p =>
      E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
        (fun g => if fullRowBad160 P
          (WeightedReplacement.completedTable (msgBits + 86) p.2 g)
          then 1 else 0)) ≤ (2 : ℝ≥0∞)⁻¹^760 := by
  apply (WeightedReplacement.completed_bad_probability_le
    (msgBits + 86) oa c hc (fullRowBad160 P)).trans
  exact full_table_bad_probability160 P

/-- Average conditional failure of the actual partially cached nonce row. -/
theorem actual_rowGood_completion_failure { α : Type }
    (oa : OracleComp Spec α) (c : Cache)
    (hc : ∀ x : BitVec (msgBits + 86), c ⟨msgBits + 86, x⟩ = none)
    (message : α → Message) :
    E (run oa c) (fun p => ENNReal.ofReal (uniformMean
      (fun g : BitVec (msgBits + 86) → BitVec hashBits =>
        if rowGood (cacheDecode ∘
          WeightedReplacement.cachedRow 86 (message p.1) p.2 g)
        then (0 : ℝ) else 1))) ≤ (2 : ℝ≥0∞)⁻¹^760 := by
  apply (le_trans (b := E (run oa c) (fun p =>
    E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits))
      (fun g => if fullRowBad160 cachePrefixPredicates
        (WeightedReplacement.completedTable (msgBits + 86) p.2 g)
        then 1 else 0))))
  · apply E_mono
    intro p
    rw [← WeightedReplacement.E_uniform_ofReal
      (fun g : BitVec (msgBits + 86) → BitVec hashBits =>
        if rowGood (cacheDecode ∘
          WeightedReplacement.cachedRow 86 (message p.1) p.2 g)
        then (0 : ℝ) else 1)
      (fun g => by split_ifs <;> norm_num)]
    apply E_mono
    intro g
    by_cases hr : rowGood (cacheDecode ∘
        WeightedReplacement.cachedRow 86 (message p.1) p.2 g)
    · simp only [if_pos hr, ENNReal.ofReal_zero]
      exact bot_le
    · have hb : fullRowBad160 cachePrefixPredicates
          (WeightedReplacement.completedTable (msgBits + 86) p.2 g) := by
        by_contra hn
        apply hr
        exact fullTableGood_row _ hn (message p.1)
      simp only [if_neg hr, ENNReal.ofReal_one, if_pos hb]
      exact le_rfl
  · exact completed_full_bad_probability160 oa c hc cachePrefixPredicates

/-! ## The actual-cache family: 160 prefixes, score, and excess -/

open WeightedCacheCounts WeightedRow.Weights

def crossing { α : Type } (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (bad : hashSpec.QueryCache → Prop) : ℝ≥0∞ :=
  Pr[fun out => out.2.status = .hit |
    (simulateQ (WeightedOracleExecution.stoppedImpl oracleImpl
      (fun _ c => bad c) (fun _ _ => False)) oa).run
        (WeightedFirstHit.classify (fun _ c => bad c) (fun _ _ => False) 0 c)]

theorem row_initial (m : Message) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    (seen (WideDomains.rowDomain m) c).card = 0 ∧
      classCounts (WideDomains.rowDomain m) c cacheDecode = (fun _ => 0) := by
  have hg := WideDomains.fresh_seen_empty c hf
  have hs := WideDomains.seen_row_subset m c
  rw [hg] at hs
  have he : seen (WideDomains.rowDomain m) c = ∅ := by
    exact Finset.Subset.antisymm hs (Finset.empty_subset _)
  constructor
  · rw [he, Finset.card_empty]
  · unfold classCounts
    rw [he]
    funext i
    simp [WeightedPublicCounts.counts]

def prefixClasses (j : Tier) : Finset (Fin M) :=
  Finset.univ.filter fun i => rank i ≤ j.val

def prefixWeight (j : Tier) : WeightedRow.Weights (Fin M) :=
  securityWeights.prefixWeights (prefixClasses j)

def prefixBad (m : Message) (j : Tier) (c : hashSpec.QueryCache) : Prop :=
  (2 : ℝ)^86 / (100 * (2 : ℝ)^20) ≤
    -(prefixWeight j).M1 (seen (WideDomains.rowDomain m) c).card
      (classCounts (WideDomains.rowDomain m) c cacheDecode)

def scoreBad (m : Message) (c : hashSpec.QueryCache) : Prop :=
  Chain18Compact.kappa * (2 : ℝ)^86 / 1000 ≤
    securityWeights.M1 (seen (WideDomains.rowDomain m) c).card
      (classCounts (WideDomains.rowDomain m) c cacheDecode)

theorem excess_nonneg (i : Fin M) : 0 ≤ excess i := by
  change 0 ≤ LongChain91Security.excess i
  rw [LongChain91Security.excess_eq]
  exact div_nonneg
    (mul_nonneg (by
      unfold Chain18Compact.kappa
      positivity) (Nat.cast_nonneg _))
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _))

def excessScore (i : Fin M) : ℝ :=
  referenceWeight i * excess i / classProbability i

theorem excessScore_nonneg (i : Fin M) : 0 ≤ excessScore i := by
  exact div_nonneg
    (mul_nonneg (LongChain91Security.referenceWeight_nonneg i) (excess_nonneg i))
    (LongChain91Security.classProbability_pos i).le

theorem excess_le_probability_ratio (i : Fin M) :
    excess i ≤ classProbability i /
      (1 - ∑ j : Fin M, classProbability j) := by
  unfold excess LongChain91Security.excess
  apply max_le
  · have hk : 0 ≤ Chain18Compact.kappa / 2 := by
      unfold Chain18Compact.kappa
      positivity
    linarith
  · apply div_nonneg (LongChain91Security.classProbability_pos i).le
    have ha := LongChain91Security.classProbability_sum_lt_one
    linarith

theorem excessScore_le (i : Fin M) :
    excessScore i ≤ (Chain18Compact.L : ℝ) * Chain18Compact.kappa := by
  have ha : (∑ j : Fin M, classProbability j) < 1 / 10000 := by
    rw [LongChain91Security.classProbability_sum]
    exact LongChain91Security.accepted_fraction_lt
  have hd : 0 < 1 - ∑ j : Fin M, classProbability j := by linarith
  have hg := LongChain91Security.referenceWeight_nonneg i
  have hp := LongChain91Security.classProbability_pos i
  have hk : 0 ≤ (Chain18Compact.L : ℝ) * Chain18Compact.kappa := by
    unfold Chain18Compact.kappa
    positivity
  calc
    excessScore i ≤
        (referenceWeight i *
          (classProbability i / (1 - ∑ j : Fin M, classProbability j))) /
            classProbability i :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (excess_le_probability_ratio i) hg) hp.le
    _ = referenceWeight i / (1 - ∑ j : Fin M, classProbability j) := by
      field_simp [(LongChain91Security.classProbability_pos i).ne']
    _ ≤ (((Chain18Compact.L : ℝ) * Chain18Compact.kappa / 2) /
        (1 - ∑ j : Fin M, classProbability j)) :=
      div_le_div_of_nonneg_right (LongChain91Security.referenceWeight_le i) hd.le
    _ ≤ (Chain18Compact.L : ℝ) * Chain18Compact.kappa := by
      apply (div_le_iff₀ hd).2
      nlinarith

def excessWeights : WeightedRow.Weights (Fin M) :=
  securityWeights.withScore excessScore excessScore_nonneg

theorem excessWeights_mean :
    excessWeights.mean = ∑ i : Fin M, referenceWeight i * excess i := by
  unfold WeightedRow.Weights.mean excessWeights excessScore
  apply Finset.sum_congr rfl
  intro i hi
  change classProbability i *
      (referenceWeight i * excess i / classProbability i) = _
  field_simp [(LongChain91Security.classProbability_pos i).ne']

def excessBad (m : Message) (c : hashSpec.QueryCache) : Prop :=
  Chain18Compact.kappa * (2 : ℝ)^86 / 1000 ≤
    excessWeights.M1 (seen (WideDomains.rowDomain m) c).card
      (classCounts (WideDomains.rowDomain m) c cacheDecode)

theorem prefix_bound { α : Type } (m : Message) (j : Tier)
    (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    crossing oa c (prefixBad m j) ≤
      ENNReal.ofReal (Real.exp (-(2^30 : ℝ))) := by
  obtain ⟨hq, hk⟩ := row_initial m c hf
  have hfiber : ∀ x,
      ((Finset.univ.filter (fun b : BitVec hashBits => cacheDecode b = x)).card : ℝ) /
        Fintype.card (BitVec hashBits) = (prefixWeight j).classMass x := by
    intro x
    exact (cache_decoder_law x).trans
      (WeightedRow.Weights.withScore_classMass securityWeights
        (fun i => if i ∈ prefixClasses j then 1 else 0)
        (fun i => by split_ifs <;> norm_num) x).symm
  have h := WeightedProtectedCache.row_score (prefixWeight j)
    (WideDomains.rowDomain m) (WideDomains.row_card m).le cacheDecode
    hfiber true 1 (by norm_num)
    (securityWeights.prefix_weight_bound (prefixClasses j)) oa c hq hk
  have he : (1 : ℝ) * (2 : ℝ)^86 / (100 * (2 : ℝ)^20) =
      (2 : ℝ)^86 / (100 * (2 : ℝ)^20) := by ring
  rw [he] at h
  change crossing oa c (prefixBad m j) ≤ _ at h
  exact h

theorem score_bound { α : Type } (m : Message) (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    crossing oa c (scoreBad m) ≤
      ENNReal.ofReal (Real.exp (-(2^27 : ℝ))) := by
  obtain ⟨hq, hk⟩ := row_initial m c hf
  have hfiber : ∀ x,
      ((Finset.univ.filter (fun b : BitVec hashBits => cacheDecode b = x)).card : ℝ) /
        Fintype.card (BitVec hashBits) = securityWeights.classMass x :=
    cache_decoder_law
  let G : ℝ := (Chain18Compact.L : ℝ) * Chain18Compact.kappa / 2
  let N : ℝ := (2 : ℝ)^86
  let a : ℝ := Chain18Compact.kappa * (2 : ℝ)^86 / 1000
  have hG : 0 < G := by
    dsimp only [G]
    exact div_pos
      (mul_pos (by norm_num [Chain18Compact.L])
        (by norm_num [Chain18Compact.kappa])) (by norm_num)
  have hN : 0 < N := by dsimp only [N]; positivity
  have ha : 0 < a := by
    dsimp only [a]
    exact div_pos
      (mul_pos (by norm_num [Chain18Compact.kappa]) (by positivity))
      (by norm_num)
  have hx := WeightedActualScore.row_freedman securityWeights oracleImpl
    (fun d => (seen (WideDomains.rowDomain m) d).card)
    (fun d => classCounts (WideDomains.rowDomain m) d cacheDecode)
    (WeightedDirectCache.protectedFresh (WideDomains.rowDomain m))
    (WeightedProtectedCache.query_law securityWeights
      (WideDomains.rowDomain m) cacheDecode hfiber)
    false G N a hG LongChain91Security.referenceWeight_le hN ha oa c hq hk
  have hcap (d : hashSpec.QueryCache) :
      ((seen (WideDomains.rowDomain m) d).card : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast
      (WeightedCacheCounts.seen_card_le (WideDomains.rowDomain m) d).trans
        (WideDomains.row_card m).le
  have hhit :
      (fun (_ : ℕ) (d : hashSpec.QueryCache) =>
        ((seen (WideDomains.rowDomain m) d).card : ℝ) ≤ N ∧
          a ≤ WeightedActualScore.signedM1 securityWeights
            (fun e => (seen (WideDomains.rowDomain m) e).card)
            (fun e => classCounts (WideDomains.rowDomain m) e cacheDecode)
            false d) =
      (fun (_ : ℕ) (d : hashSpec.QueryCache) =>
        a ≤ WeightedActualScore.signedM1 securityWeights
          (fun e => (seen (WideDomains.rowDomain m) e).card)
          (fun e => classCounts (WideDomains.rowDomain m) e cacheDecode)
          false d) := by
    funext n d
    apply propext
    constructor
    · exact And.right
    · intro hd
      exact ⟨hcap d, hd⟩
  have hkill :
      (fun (_ : ℕ) (d : hashSpec.QueryCache) =>
        N < ((seen (WideDomains.rowDomain m) d).card : ℝ)) =
      (fun (_ : ℕ) (_ : hashSpec.QueryCache) => False) := by
    funext n d
    exact propext (iff_false_intro (not_lt_of_ge (hcap d)))
  dsimp only at hx
  rw [hhit, hkill] at hx
  have hexponent :
      (2^27 : ℝ) ≤ a^2 / (2 * (G^2 * N + G * a / 3)) := by
    norm_num [a, G, N, Chain18Compact.L, Chain18Compact.kappa]
  have hexp :
      Real.exp (-a^2 / (2 * (G^2 * N + G * a / 3))) ≤
        Real.exp (-(2^27 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hexponent
  have htail := hx.trans (ENNReal.ofReal_le_ofReal hexp)
  change crossing oa c (scoreBad m) ≤ _ at htail
  exact htail

theorem excess_bound { α : Type } (m : Message) (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    crossing oa c (excessBad m) ≤
      ENNReal.ofReal (Real.exp (-(2^25 : ℝ))) := by
  obtain ⟨hq, hk⟩ := row_initial m c hf
  have hfiber : ∀ x,
      ((Finset.univ.filter (fun b : BitVec hashBits => cacheDecode b = x)).card : ℝ) /
        Fintype.card (BitVec hashBits) = excessWeights.classMass x := by
    intro x
    exact (cache_decoder_law x).trans
      (WeightedRow.Weights.withScore_classMass securityWeights
        excessScore excessScore_nonneg x).symm
  let G : ℝ := (Chain18Compact.L : ℝ) * Chain18Compact.kappa
  let N : ℝ := (2 : ℝ)^86
  let a : ℝ := Chain18Compact.kappa * (2 : ℝ)^86 / 1000
  have hG : 0 < G := by
    dsimp only [G]
    exact mul_pos (by norm_num [Chain18Compact.L])
      (by norm_num [Chain18Compact.kappa])
  have hN : 0 < N := by dsimp only [N]; positivity
  have ha : 0 < a := by
    dsimp only [a]
    exact div_pos
      (mul_pos (by norm_num [Chain18Compact.kappa]) (by positivity))
      (by norm_num)
  have hx := WeightedActualScore.row_freedman excessWeights oracleImpl
    (fun d => (seen (WideDomains.rowDomain m) d).card)
    (fun d => classCounts (WideDomains.rowDomain m) d cacheDecode)
    (WeightedDirectCache.protectedFresh (WideDomains.rowDomain m))
    (WeightedProtectedCache.query_law excessWeights
      (WideDomains.rowDomain m) cacheDecode hfiber)
    false G N a hG excessScore_le hN ha oa c hq hk
  have hcap (d : hashSpec.QueryCache) :
      ((seen (WideDomains.rowDomain m) d).card : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast
      (WeightedCacheCounts.seen_card_le (WideDomains.rowDomain m) d).trans
        (WideDomains.row_card m).le
  have hhit :
      (fun (_ : ℕ) (d : hashSpec.QueryCache) =>
        ((seen (WideDomains.rowDomain m) d).card : ℝ) ≤ N ∧
          a ≤ WeightedActualScore.signedM1 excessWeights
            (fun e => (seen (WideDomains.rowDomain m) e).card)
            (fun e => classCounts (WideDomains.rowDomain m) e cacheDecode)
            false d) =
      (fun (_ : ℕ) (d : hashSpec.QueryCache) =>
        a ≤ WeightedActualScore.signedM1 excessWeights
          (fun e => (seen (WideDomains.rowDomain m) e).card)
          (fun e => classCounts (WideDomains.rowDomain m) e cacheDecode)
          false d) := by
    funext n d
    apply propext
    constructor
    · exact And.right
    · intro hd
      exact ⟨hcap d, hd⟩
  have hkill :
      (fun (_ : ℕ) (d : hashSpec.QueryCache) =>
        N < ((seen (WideDomains.rowDomain m) d).card : ℝ)) =
      (fun (_ : ℕ) (_ : hashSpec.QueryCache) => False) := by
    funext n d
    exact propext (iff_false_intro (not_lt_of_ge (hcap d)))
  dsimp only at hx
  rw [hhit, hkill] at hx
  have hexponent :
      (2^25 : ℝ) ≤ a^2 / (2 * (G^2 * N + G * a / 3)) := by
    norm_num [a, G, N, Chain18Compact.L, Chain18Compact.kappa]
  have hexp :
      Real.exp (-a^2 / (2 * (G^2 * N + G * a / 3))) ≤
        Real.exp (-(2^25 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hexponent
  have htail := hx.trans (ENNReal.ofReal_le_ofReal hexp)
  change crossing oa c (excessBad m) ≤ _ at htail
  exact htail

/-- The row-local event coordinate: 160 prefix deficits, then the reference
score and literal post-sign excess score. -/
abbrev RowEvent := Fin 162
abbrev BadIndex := Message × RowEvent

def event : BadIndex → hashSpec.QueryCache → Prop
  | (m, j) =>
      if h : j.val < 160 then prefixBad m ⟨j.val, h⟩
      else if j.val = 160 then scoreBad m else excessBad m

theorem event_bound { α : Type } (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) (i : BadIndex) :
    crossing oa c (event i) ≤ ENNReal.ofReal (Real.exp (-(2^25 : ℝ))) := by
  have h30 : Real.exp (-(2^30 : ℝ)) ≤ Real.exp (-(2^25 : ℝ)) := by
    exact Real.exp_le_exp.mpr (by norm_num)
  have h27 : Real.exp (-(2^27 : ℝ)) ≤ Real.exp (-(2^25 : ℝ)) := by
    exact Real.exp_le_exp.mpr (by norm_num)
  obtain ⟨m, j⟩ := i
  dsimp only [event]
  split_ifs with h h'
  · exact (prefix_bound m ⟨j.val, h⟩ oa c hf).trans
      (ENNReal.ofReal_le_ofReal h30)
  · exact (score_bound m oa c hf).trans
      (ENNReal.ofReal_le_ofReal h27)
  · exact excess_bound m oa c hf

def Good (c : hashSpec.QueryCache) : Prop := ∀ i : BadIndex, ¬ event i c

theorem row162_union_margin :
    (162 * (2^256 : ℝ)) * Real.exp (-(2^25 : ℝ)) ≤
      ((2 : ℝ)^512)⁻¹ := by
  have hexp : Real.exp (-(2^25 : ℝ)) ≤ ((2 : ℝ)^1024)⁻¹ := by
    have hmono : Real.exp (-(2^25 : ℝ)) ≤ Real.exp (-(1024 : ℝ)) := by
      exact Real.exp_le_exp.mpr (by norm_num)
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hp : (2 : ℝ)^1024 ≤ (Real.exp 1)^1024 :=
      pow_le_pow_left₀ (by norm_num) he 1024
    rw [← Real.exp_nat_mul, mul_one] at hp
    have htail : Real.exp (-(1024 : ℝ)) ≤ ((2 : ℝ)^1024)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hp
    exact hmono.trans htail
  have hm := mul_le_mul_of_nonneg_left hexp
    (show 0 ≤ 162 * (2^256 : ℝ) by positivity)
  have hfactor : 162 * (2^256 : ℝ) ≤ (2 : ℝ)^512 := by
    have hbase : (162 : ℝ) ≤ 2^256 := by norm_num
    calc
      162 * (2^256 : ℝ) ≤ (2^256 : ℝ) * (2^256 : ℝ) := by gcongr
      _ = (2 : ℝ)^512 := by rw [← pow_add]
  apply hm.trans
  calc
    (162 * (2^256 : ℝ)) * ((2 : ℝ)^1024)⁻¹ ≤
        (2 : ℝ)^512 * ((2 : ℝ)^1024)⁻¹ := by gcongr
    _ = ((2 : ℝ)^512)⁻¹ := by
      rw [show (1024 : ℕ) = 512 + 512 by omega, pow_add]
      field_simp

theorem all_crossings { α : Type } (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    crossing oa c (fun d => ∃ i : BadIndex, event i d) ≤
      ENNReal.ofReal (((2 : ℝ)^512)⁻¹) := by
  have hu := WeightedOracleExecution.stopped_hit_union_uniform oracleImpl
    (fun i _ c => event i c) oa 0 c
    (ENNReal.ofReal (Real.exp (-(2^25 : ℝ)))) (event_bound oa c hf)
  calc
    crossing oa c (fun d => ∃ i : BadIndex, event i d) ≤
        (Fintype.card BadIndex : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(2^25 : ℝ))) := hu
    _ = ENNReal.ofReal
        ((Fintype.card BadIndex : ℝ) * Real.exp (-(2^25 : ℝ))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal
        ((162 * (2^256 : ℝ)) * Real.exp (-(2^25 : ℝ))) := by
      congr 2
      norm_num [BadIndex, RowEvent, Message, msgBits, Fintype.card_prod,
        Fintype.card_bitVec]
    _ ≤ ENNReal.ofReal (((2 : ℝ)^512)⁻¹) :=
      ENNReal.ofReal_le_ofReal row162_union_margin

theorem terminal_bad { α : Type } (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    Pr[fun out => ¬ Good out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2 : ℝ)^512)⁻¹) := by
  have hgood (d : hashSpec.QueryCache) :
      (¬ Good d) = (∃ i : BadIndex, event i d) := by
    simp only [Good, not_forall, not_not]
  simp only [hgood]
  apply (WeightedOracleExecution.terminal_bad_le_firstHit oracleImpl
    (fun d => ∃ i : BadIndex, event i d) oa 0 c).trans
  have h := all_crossings oa c hf
  simpa only [crossing, WeightedOracleExecution.prob_stopped_hit_eq_firstHitRun] using h

theorem good_row_score (c : hashSpec.QueryCache) (hc : Good c)
    (m : Message) :
    securityWeights.score (classCounts (WideDomains.rowDomain m) c cacheDecode) ≤
      securityWeights.mean * (seen (WideDomains.rowDomain m) c).card +
        Chain18Compact.kappa * (2 : ℝ)^86 / 1000 := by
  have h := hc (m, ⟨160, by decide⟩)
  change ¬ scoreBad m c at h
  have hh := lt_of_not_ge h
  change securityWeights.score _ - securityWeights.mean *
    (seen (WideDomains.rowDomain m) c).card < _ at hh
  linarith

theorem good_row_excess (c : hashSpec.QueryCache) (hc : Good c)
    (m : Message) :
    excessWeights.score (classCounts (WideDomains.rowDomain m) c cacheDecode) ≤
      (∑ i : Fin M, referenceWeight i * excess i) *
          (seen (WideDomains.rowDomain m) c).card +
        Chain18Compact.kappa * (2 : ℝ)^86 / 1000 := by
  have h := hc (m, ⟨161, by decide⟩)
  change ¬ excessBad m c at h
  have hh := lt_of_not_ge h
  unfold excessBad WeightedRow.Weights.M1 at hh
  rw [excessWeights_mean] at hh
  linarith

end
end OptimalOTS.WeightedConstruction.LongChain91Empirical
