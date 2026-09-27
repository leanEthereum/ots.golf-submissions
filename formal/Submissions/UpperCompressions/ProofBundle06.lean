import Submissions.UpperCompressions.ProofBundle05
import Submissions.UpperCompressions.ProofBundle03
import Submissions.UpperCompressions.ProofBundle04
import Submissions.UpperCompressions.ProofBundle00

section

/-! Exact accounting across actual public/private phases of a shared-cache
OracleComp program. No pathwise budget is spent a second time at a phase split. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedReplacement
open OptimalOTS
set_option maxHeartbeats 800000

theorem expectedCharge_bind {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache) :
    expectedCharge charge (oa >>= k) c = expectedCharge charge oa c +
      E (run oa c) (fun p => expectedCharge charge (k p.1) p.2) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t next ih =>
    rw [bind_assoc, expectedCharge_query]
    simp_rw [ih]
    rw [expectedCharge_query, run_query_bind, E_bind]
    simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]
    ring

theorem expectedCharge_bind_pure {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (f : α → β) (c : Cache) :
    expectedCharge charge (oa >>= fun a => pure (f a)) c = expectedCharge charge oa c := by
  rw [expectedCharge_bind]
  simp [E, expectedValue_def]

theorem expectedCharge_map {α β : Type} (charge : Spec.Domain → ℝ≥0∞)
    (oa : OracleComp Spec α) (f : α → β) (c : Cache) :
    expectedCharge charge (f <$> oa) c = expectedCharge charge oa c := by
  rw [map_eq_bind_pure_comp]
  exact expectedCharge_bind_pure charge oa f c

end WeightedReplacement
end
end

section

/-! The concrete all-L signer spends no non-index paid cost. Combining public
phases across it preserves exactly the non-index clock used by authentication. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedReplacement
open OptimalOTS OptimalOTS.WeightedSampling
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits signBudget

theorem otherPaid_le_queryCost (isIndex : Spec.Domain → Prop) (t : Spec.Domain) :
    otherPaid isIndex t ≤ queryCost t := by
  unfold otherPaid
  split_ifs <;> simp

end WeightedReplacement
end
end

section

/-! The terminal chosen input is charged to its actual first public query.
This uses the program's query prefix, not membership in a private signer cache. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementPublicUnion_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits blockBits msgBits signBudget

theorem publicHit_le_one {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache) :
    publicHit u oa c ≤ 1 := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    rw [publicHit_query]
    split_ifs
    · exact le_rfl
    · exact E_le_one _ (fun p => ih p.1 p.2)

theorem publicHit_query_target {α : Type} (u : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) :
    publicHit u (liftM (Spec.query (.inr u)) >>= k) c = 1 := by
  rw [publicHit_query]
  simp

theorem publicHit_hash_target {α : Type} {n : ℕ} (x : BitVec n)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) :
    publicHit ⟨n,x⟩ (hash x >>= k) c = 1 := by
  unfold OptimalOTS.hash
  exact publicHit_query_target _ k c

/-- A hit during the continuation is a hit of the whole public program. Hits
that already occurred in the prefix only strengthen this inequality. -/
theorem publicHit_bind_ge {α β : Type} (u : Query) (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (c : Cache) :
    E (run oa c) (fun p => publicHit u (k p.1) p.2) ≤ publicHit u (oa >>= k) c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t next ih =>
    rw [bind_assoc, publicHit_query]
    split_ifs
    · exact E_le_one _ (fun p => publicHit_le_one u (k p.1) p.2)
    · rw [run_query_bind, E_bind]
      exact E_mono _ (fun p => ih p.1 p.2)

/-- If each selected continuation really queries its chosen input, the selected
input event is bounded by the probability of that input's first public query. -/
theorem publicHit_query_output {α β : Type} (u : Query) (chosen : α → Query)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache)
    (hquery : ∀ a, chosen a = u → ∀ d, publicHit u (k a) d = 1) :
    E (run oa c) (fun p => if chosen p.1 = u then 1 else 0) ≤ publicHit u (oa >>= k) c := by
  apply (E_mono (run oa c) (fun p => ?_)).trans (publicHit_bind_ge u oa k c)
  by_cases h : chosen p.1 = u
  · rw [if_pos h, hquery p.1 h p.2]
  · rw [if_neg h]
    exact bot_le

/-- Finite union for a forger's actual selected input, provided its continuation
queries that input. Fixed initial-public-cache and signed-input exclusions may
be put in `allowed`; target class membership is `good`. -/
theorem selected_input_union {D α β : Type} [Fintype D]
    (e : D → Query) (chosen : α → D) (allowed good : D → Prop)
    (oa : OracleComp Spec α) (k : α → OracleComp Spec β) (c : Cache)
    (hquery : ∀ a, ∀ d, publicHit (e (chosen a)) (k a) d = 1) :
    E (run oa c) (fun p => if allowed (chosen p.1) ∧ good (chosen p.1) then 1 else 0) ≤
      ∑ d, if allowed d ∧ good d then publicHit (e d) (oa >>= k) c else 0 := by
  have hpoint (p : α × Cache) :
      (if allowed (chosen p.1) ∧ good (chosen p.1) then (1:ℝ≥0∞) else 0) =
      ∑ d, if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0 := by
    have hh (d : D) :
        (if allowed d ∧ good d then (if chosen p.1 = d then (1:ℝ≥0∞) else 0) else 0) =
        if chosen p.1 = d then (if allowed d ∧ good d then 1 else 0) else 0 := by
      split_ifs <;> rfl
    simp_rw [hh]
    simp
  calc
    _ = E (run oa c) (fun p => ∑ d, if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0) := by
      congr 1
      funext p
      exact hpoint p
    _ = ∑ d, E (run oa c) (fun p => if allowed d ∧ good d then (if chosen p.1 = d then 1 else 0) else 0) :=
      expectedValue_finsetSum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : allowed d ∧ good d
      · simp only [if_pos hd]
        have hdom : E (run oa c) (fun p => if chosen p.1 = d then 1 else 0) ≤
            E (run oa c) (fun p => if e (chosen p.1) = e d then 1 else 0) := E_mono _ (fun p => by
          by_cases hp : chosen p.1 = d
          · simp [hp]
          · simp [hp])
        apply hdom.trans
        apply publicHit_query_output (e d) (e ∘ chosen) oa k c
        intro a ha d'
        exact ha ▸ hquery a d'
      · simp only [if_neg hd]
        exact E_const_le _ 0

end
end WeightedReplacement
end

section

/-! Exact single-coordinate decomposition for real table updates, followed by a
Bayes bound for the actual first-minimum sampling likelihood. No Good event is
conditioned on. Adaptive transcript/filtration integration remains separate. -/

namespace WeightedReplacement

open OptimalOTS.WeightedSampling
open scoped Classical
noncomputable section
local instance stagedLocal_ReplacementCoordinate_1 {α : Type*} : DecidableEq α := Classical.decEq α

noncomputable def fractionExcept {ι : Type} [Fintype ι] (p : ι → Prop) (u : ι) : ℝ :=
  (∑ a ∈ Finset.univ.erase u, if p a then (1 : ℝ) else 0) / Fintype.card ι

theorem fractionExcept_nonneg {ι : Type} [Fintype ι] (p : ι → Prop) (u : ι) :
    0 ≤ fractionExcept p u := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a ha
  split_ifs <;> norm_num

theorem fraction_update {ι Ω : Type} [Fintype ι] (table : ι → Ω)
    (p : Ω → Prop) (u : ι) (y : Ω) :
    fraction (p ∘ Function.update table u y) = fractionExcept (p ∘ table) u +
      if p y then 1 / (Fintype.card ι : ℝ) else 0 := by
  have hs : (∑ a, if p (Function.update table u y a) then (1 : ℝ) else 0) =
      (∑ a ∈ Finset.univ.erase u, if p (table a) then (1 : ℝ) else 0) +
        (if p y then 1 else 0) := by
    calc
      _ = (∑ a ∈ Finset.univ.erase u,
          if p (Function.update table u y a) then (1 : ℝ) else 0) +
          (if p (Function.update table u y u) then 1 else 0) :=
        (Finset.sum_erase_add Finset.univ
          (fun a => if p (Function.update table u y a) then (1 : ℝ) else 0)
          (Finset.mem_univ u)).symm
      _ = _ := by
        rw [Function.update_self]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [Function.update_of_ne (Finset.mem_erase.mp ha).1]
  unfold fraction uniformMean fractionExcept
  simp only [Function.comp_apply]
  rw [hs, add_div]
  by_cases hy : p y <;> simp [hy]

/-- The exact first-minimum target likelihood on one concrete decoded table. -/
noncomputable def tableWinnerLikelihood {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (v : ι) (i : γ) : ℝ :=
  iidMean k (fun xs => if select (fun p : ι × γ => tier p.2)
      (xs.map fun a => (fun j => (a,j)) <$> decode (table a)) = some (v,i)
    then (1 : ℝ) else 0)

theorem tableWinnerLikelihood_eq {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (v : ι) (i : γ) (hv : decode (table v) = some i) :
    tableWinnerLikelihood k table decode tier v i =
      kernel k (fraction (weakRank tier i ∘ decode ∘ table))
        (fraction (strictRank tier i ∘ decode ∘ table)) / Fintype.card ι := by
  have h := iid_tagged_table_probability (decode ∘ table) tier v i hv k
  unfold tableWinnerLikelihood
  convert h using 1
  congr 1

/-- Changing a distinct unknown nonce changes each survival endpoint only by
that coordinate's exact mass 1/N. This identifies the generic Bayes kernel with
the actual selector likelihood, not an assumed likelihood surrogate. -/
theorem tableWinnerLikelihood_update {ι Ω γ : Type} [Fintype ι]
    (k : ℕ) (table : ι → Ω) (decode : Ω → Option γ) (tier : γ → ℕ)
    (u v : ι) (i : γ) (hvu : v ≠ u) (hv : decode (table v) = some i) (y : Ω) :
    tableWinnerLikelihood k (Function.update table u y) decode tier v i =
      coordinateLikelihood k
        (fractionExcept (weakRank tier i ∘ decode ∘ table) u)
        (fractionExcept (strictRank tier i ∘ decode ∘ table) u)
        (1 / (Fintype.card ι : ℝ)) (Fintype.card ι)
        (weakRank tier i ∘ decode) (strictRank tier i ∘ decode) y := by
  rw [tableWinnerLikelihood_eq k _ decode tier v i
    (by simpa only [Function.update_of_ne hvu] using hv)]
  have hweak := fraction_update table (weakRank tier i ∘ decode) u y
  have hstrict := fraction_update table (strictRank tier i ∘ decode) u y
  simp only [Function.comp_assoc] at hweak hstrict
  rw [hweak, hstrict]
  rfl

end
end WeightedReplacement
end

section

/-! Compositional probability factorization: after fixing the returned signing
value, any adaptive public-prefix event contributes coordinate-independent
evidence. The equality is proved from actual `ProbComp` bind semantics. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementFactorization_1 {α : Type*} : DecidableEq α := Classical.decEq α

def taggedBind {β α : Type} (p : ProbComp β) (post : β → ProbComp α) : ProbComp (β × α) := do
  let b ← p
  let a ← post b
  pure (b,a)

/-- Fixing the first computation's returned value factors its probability from
the conditional continuation. No independence of the unconditioned outcomes is asserted. -/
theorem E_taggedBind_event {β α : Type} (p : ProbComp β) (post : β → ProbComp α)
    (b : β) (event : α → Prop) :
    E (taggedBind p post) (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
      E p (fun b' => if b' = b then 1 else 0) *
        E (post b) (fun a => if event a then 1 else 0) := by
  calc
    _ = E p (fun b' => (if b' = b then 1 else 0) *
        E (post b) (fun a => if event a then 1 else 0)) := by
      rw [taggedBind, E_bind]
      congr 1
      funext b'
      simp only [E_bind, E_pure]
      by_cases hb : b' = b
      · subst b'
        simp
      · simp [hb, E, expectedValue_def]
    _ = _ := expectedValue_mul_const p _ _

end
end WeightedReplacement
end

section

/-! Finite product concentration of uniform function tables. All expectations
are finite normalized sums, then connected to the actual uniform ProbComp. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementConcentration_1 {α : Type*} : DecidableEq α := Classical.decEq α

def meanLinear (α : Type*) [Fintype α] : (α → ℝ) →ₗ[ℝ] ℝ where
  toFun := uniformMean
  map_add' f g := uniformMean_add f g
  map_smul' r f := by
    change uniformMean (fun a => r*f a) = r*uniformMean f
    simp only [uniformMean, ← Finset.mul_sum]
    ring

theorem uniformMean_mono {α : Type*} [Fintype α] (f g : α → ℝ)
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, Finset.sum_const, nsmul_eq_mul]

theorem uniformMean_product {D W : Type*} [Fintype D] [Fintype W]
    (f : D → W → ℝ) :
    uniformMean (fun g : D → W => ∏ d, f d (g d)) = ∏ d, uniformMean (f d) := by
  simp only [uniformMean, Fintype.card_fun, Nat.cast_pow]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

theorem uniformMean_centered_indicator_mgf {W : Type*} [Fintype W] [Nonempty W]
    (P : W → Prop) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    uniformMean (fun w => Real.exp (θ * (fraction P - if P w then 1 else 0) - θ^2)) ≤ 1 := by
  let X : W → ℝ := fun w => fraction P - if P w then 1 else 0
  have hμ0 : 0 ≤ fraction P := by
    unfold fraction
    exact (show uniformMean (fun _ : W => (0:ℝ)) ≤ _ from
      uniformMean_mono _ _ (fun w => by split_ifs <;> norm_num)).trans_eq' (uniformMean_const 0)
  have hμ1 : fraction P ≤ 1 := by
    unfold fraction
    calc
      _ ≤ uniformMean (fun _ : W => (1:ℝ)) := uniformMean_mono _ _ (fun w => by split_ifs <;> norm_num)
      _ = _ := uniformMean_const 1
  have hb : ∀ w, |X w| ≤ 1 := by
    intro w
    dsimp [X]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hm : meanLinear W X = 0 := by
    change uniformMean X = 0
    dsimp [X]
    simp [uniformMean, fraction, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      sub_div, mul_div_cancel_left₀ _ (show (Fintype.card W:ℝ) ≠ 0 by positivity)]
  have hs : meanLinear W (fun w => (X w)^2) ≤ 1 := by
    change uniformMean _ ≤ 1
    calc
      _ ≤ uniformMean (fun _ : W => (1:ℝ)) := uniformMean_mono _ _ (fun w => (sq_le_one_iff_abs_le_one _).2 (hb w))
      _ = _ := uniformMean_const 1
  have hx := WeightedMGF.centered_mgf (meanLinear W) (fun f g h => uniformMean_mono f g h)
    (uniformMean_const 1) X θ 1 1 hθ0 (by norm_num) (by nlinarith) hb hm hs
  have hc : θ^2 * 1 / (2 * (1-θ*1/3)) ≤ θ^2 := by
    have hd : 0 < 2*(1-θ*1/3) := by linarith
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg θ]
  have hbase : uniformMean (fun w => Real.exp (θ*X w)) ≤ Real.exp (θ^2) :=
    hx.trans (Real.exp_le_exp.mpr hc)
  have hf : (fun w => Real.exp (θ*X w-θ^2)) =
      (fun w => Real.exp (θ*X w) * Real.exp (-θ^2)) := by
    funext w
    rw [sub_eq_add_neg, Real.exp_add]
  change uniformMean (fun w => Real.exp (θ*X w-θ^2)) ≤ 1
  rw [hf, uniformMean_mul_const]
  calc
    _ ≤ Real.exp (θ^2)*Real.exp (-θ^2) :=
      mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

def empirical {D W : Type*} [Fintype D] (P : W → Prop) (g : D → W) : ℝ :=
  fraction (P ∘ g)

theorem uniform_table_deficit {D W : Type*} [Fintype D] [Nonempty D]
    [Fintype W] [Nonempty W] (P : W → Prop) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    uniformMean (fun g : D → W => if empirical P g ≤ fraction P - δ then 1 else 0) ≤
      Real.exp (-((Fintype.card D : ℝ) * δ^2 / 4)) := by
  let θ := δ/2
  let X : W → ℝ := fun w => fraction P - if P w then 1 else 0
  let Z : (D → W) → ℝ := fun g => ∑ d, (θ*X (g d)-θ^2)
  have hmgf : uniformMean (fun g : D → W => Real.exp (Z g)) ≤ 1 := by
    have hf : (fun g : D → W => Real.exp (Z g)) =
        (fun g => ∏ d, Real.exp (θ*X (g d)-θ^2)) := by
      funext g
      exact Real.exp_sum _ _
    rw [hf, uniformMean_product (fun _d : D => fun w => Real.exp (θ*X w-θ^2))]
    calc
      _ ≤ ∏ _d : D, (1:ℝ) := Finset.prod_le_prod
        (fun d _ => div_nonneg (Finset.sum_nonneg (fun w _ => Real.exp_nonneg _)) (by positivity))
        (fun d _ => uniformMean_centered_indicator_mgf P θ (by dsimp [θ]; positivity) (by dsimp [θ]; linarith))
      _ = _ := by simp
  have hbad (g : D → W) (hg : empirical P g ≤ fraction P-δ) :
      (Fintype.card D:ℝ)*δ^2/4 ≤ Z g := by
    have hN : 0 < (Fintype.card D:ℝ) := by positivity
    have hsum : (∑ d, if P (g d) then (1:ℝ) else 0) ≤
        (fraction P-δ)*(Fintype.card D:ℝ) := by
      apply (div_le_iff₀ hN).mp
      exact hg
    dsimp [Z, X, θ]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    nlinarith
  exact WeightedKernel.exponential_tail (meanLinear (D → W))
    (fun f g h => uniformMean_mono f g h) _ Z ((Fintype.card D:ℝ)*δ^2/4) hbad hmgf

end
end WeightedReplacement
end

section

/-! Actual full-table concentration, using the exact uniform restriction law. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementTableGood_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem E_uniform_ofReal {A : Type} [Fintype A] [Nonempty A] [SampleableType A]
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    E ($ᵗ A) (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal (uniformMean f) := by
  rw [ofReal_uniformMean f hf, E, expectedValue_def, tsum_fintype]
  simp only [probOutput_uniformSample]

theorem E_uniform_restrict {A B W : Type} [Fintype A] [Fintype B] [Fintype W]
    [Nonempty W] [SampleableType W] [SampleableType (A → W)] [SampleableType (B → W)]
    (e : A → B) (he : Function.Injective e) (f : (A → W) → ℝ≥0∞) :
    E ($ᵗ (B → W)) (fun g => f (g ∘ e)) = E ($ᵗ (A → W)) f := by
  have hd := evalSPMF_uniformSample_map_comp_injective (R := W) he
  have h := expectedValue_congr (mx := (do let g ← $ᵗ (B → W); pure (g ∘ e)))
    (my := ($ᵗ (A → W))) (fun g => by
      simpa only [probOutput_def] using congrArg (fun p : SPMF (A → W) => p g) hd) f
  simpa only [E, expectedValue_bind, expectedValue_pure] using h

theorem E_table_deficit {A B W : Type} [Fintype A] [Nonempty A]
    [Fintype B] [Fintype W] [Nonempty W] [SampleableType W]
    [SampleableType (A → W)] [SampleableType (B → W)]
    (e : A → B) (he : Function.Injective e) (P : W → Prop)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    E ($ᵗ (B → W)) (fun g => if empirical P (g ∘ e) ≤ fraction P - δ then 1 else 0) ≤
      ENNReal.ofReal (Real.exp (-((Fintype.card A:ℝ)*δ^2/4))) := by
  rw [E_uniform_restrict e he (fun g => if empirical P g ≤ fraction P-δ then 1 else 0)]
  have hx := E_uniform_ofReal (fun g : A → W =>
    if empirical P g ≤ fraction P-δ then (1:ℝ) else 0) (fun g => by split_ifs <;> norm_num)
  simp only [apply_ite, ENNReal.ofReal_one, ENNReal.ofReal_zero] at hx
  rw [hx]
  exact ENNReal.ofReal_le_ofReal (uniform_table_deficit P δ hδ0 hδ1)

theorem E_finite_union {T I : Type} [Fintype I] (p : ProbComp T)
    (bad : I → T → Prop) (ε : ℝ≥0∞)
    (hb : ∀ i, E p (fun t => if bad i t then 1 else 0) ≤ ε) :
    E p (fun t => if ∃ i, bad i t then 1 else 0) ≤ (Fintype.card I:ℝ≥0∞)*ε := by
  calc
    _ ≤ E p (fun t => ∑ i, if bad i t then 1 else 0) := E_mono p (fun t => by
      split_ifs with h
      · obtain ⟨i, hi⟩ := h
        have hle := Finset.single_le_sum (s := Finset.univ)
          (f := fun j => if bad j t then (1:ℝ≥0∞) else 0)
          (fun _ _ => bot_le) (Finset.mem_univ i)
        simpa only [if_pos hi] using hle
      · exact bot_le)
    _ = ∑ i, E p (fun t => if bad i t then 1 else 0) := expectedValue_finsetSum p _ _
    _ ≤ ∑ _i : I, ε := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp [nsmul_eq_mul]

theorem append_right_injective (m : Message) :
    Function.Injective (fun η : BitVec 86 => m ++ η) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun x : BitVec (msgBits+86) => x.getLsbD i) h
  simpa only [BitVec.getLsbD_append, if_pos hi] using hh

theorem concrete_row_exponent :
    Real.exp (-((Fintype.card (BitVec 86):ℝ)*(1/(100*(2:ℝ)^20))^2/4)) ≤
      (2:ℝ)⁻¹^1024 := by
  have hnum : (1024:ℝ) ≤ (Fintype.card (BitVec 86):ℝ)*(1/(100*(2:ℝ)^20))^2/4 := by
    norm_num
  have hexp : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  calc
    _ ≤ Real.exp (-(1024:ℝ)) := Real.exp_le_exp.mpr (neg_le_neg hnum)
    _ = (Real.exp 1)⁻¹^1024 := by rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (inv_anti₀ (by norm_num) hexp) 1024

end
end WeightedReplacement
end

section

/-! Denominator-free first-exposure bounds. Zero-probability public prefixes
require no exceptional conditioning argument. Evidence remains joint throughout. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance stagedLocal_ReplacementJointPosterior_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem finite_likelihood_joint {Ω : Type*} [Fintype Ω]
    (weight likelihood : Ω → ℝ) (target survival : Ω → Prop) (c : ℝ)
    (hw : ∀ y, 0 ≤ weight y) (hl : ∀ y, 0 ≤ likelihood y)
    (ht : ∀ y, target y → likelihood y = c)
    (hs : ∀ y, survival y → c ≤ likelihood y)
    (hmass : 0 < weightedMass weight survival) :
    (∑ y, if target y then weight y * likelihood y else 0) ≤
      (weightedMass weight target / weightedMass weight survival) *
        (∑ y, weight y * likelihood y) := by
  have hnum : (∑ y, if target y then weight y * likelihood y else 0) =
      weightedMass weight target * c := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : target y <;> simp [hy, ht y]
  have hlow : weightedMass weight survival * c ≤ ∑ y, weight y * likelihood y := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : survival y
    · simp only [if_pos hy]
      exact mul_le_mul_of_nonneg_left (hs y hy) (hw y)
    · simp only [if_neg hy, zero_mul]
      exact mul_nonneg (hw y) (hl y)
  rw [hnum]
  have hcp : c ≤ (∑ y, weight y * likelihood y) / weightedMass weight survival := by
    apply (le_div_iff₀ hmass).2
    simpa only [mul_comm] using hlow
  calc
    _ ≤ weightedMass weight target * ((∑ y, weight y * likelihood y) / weightedMass weight survival) :=
      mul_le_mul_of_nonneg_left hcp (weightedMass_nonneg weight target hw)
    _ = _ := by ring

theorem weightedMass_uniform {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    weightedMass (fun _ : Ω => 1/(Fintype.card Ω:ℝ)) P = fraction P := by
  unfold weightedMass fraction uniformMean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

theorem coordinate_uniform_joint {Ω : Type*} [Fintype Ω]
    (L : ℕ) (A B δ N : ℝ) (target weak strict : Ω → Prop)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (ht : ∀ y, target y → weak y ∧ ¬ strict y) (hmass : 0 < fraction weak) :
    uniformMean (fun y => if target y then coordinateLikelihood L A B δ N weak strict y else 0) ≤
      (fraction target / fraction weak) * uniformMean (coordinateLikelihood L A B δ N weak strict) := by
  have h := finite_likelihood_joint (fun _ : Ω => 1/(Fintype.card Ω:ℝ))
    (coordinateLikelihood L A B δ N weak strict) target weak (kernel L (A+δ) B/N)
    (fun _ => by positivity) (coordinateLikelihood_nonneg L A B δ N weak strict hA hB hδ hN)
    (fun y hy => coordinateLikelihood_same L A B δ N weak strict y (ht y hy).1 (ht y hy).2)
    (coordinateLikelihood_survival L A B δ N weak strict hA hB hδ hN)
    (by simpa only [weightedMass_uniform] using hmass)
  simp only [weightedMass_uniform] at h
  have hn : (∑ y, if target y then (1/(Fintype.card Ω:ℝ))*coordinateLikelihood L A B δ N weak strict y else 0) =
      uniformMean (fun y => if target y then coordinateLikelihood L A B δ N weak strict y else 0) := by
    simp only [uniformMean, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  have hd : (∑ y, (1/(Fintype.card Ω:ℝ))*coordinateLikelihood L A B δ N weak strict y) =
      uniformMean (coordinateLikelihood L A B δ N weak strict) := by
    simp [uniformMean, div_eq_mul_inv, mul_comm, ← Finset.mul_sum]
  rwa [hn, hd] at h

def hybridEvidence {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) : ℝ :=
  (E (hybridPrefix u oa c []) (fun p => if event p then 1 else 0)).toReal

theorem hybridEvidence_nonneg {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) : 0 ≤ hybridEvidence u oa c event := ENNReal.toReal_nonneg

theorem ofReal_hybridEvidence {α : Type} (u : Query) (oa : OracleComp Spec α) (c : Cache)
    (event : Option α × PublicTrace → Prop) :
    ENNReal.ofReal (hybridEvidence u oa c event) =
      E (hybridPrefix u oa c []) (fun p => if event p then 1 else 0) := by
  apply ENNReal.ofReal_toReal
  exact ne_of_lt (lt_of_le_of_lt (E_le_one _ (fun _ => by split_ifs <;> simp)) (by simp))

theorem E_taggedHybridPrefix {α β : Type} (p : ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache) (y : BitVec hashBits)
    (event : Option α × PublicTrace → Prop) :
    E (taggedBind p (fun b' => hybridPrefix u (post b') (overwrite c u y) []))
      (fun r => if r.1 = b ∧ event r.2 then 1 else 0) =
        E p (fun b' => if b' = b then 1 else 0) * ENNReal.ofReal (hybridEvidence u (post b) c event) := by
  rw [E_taggedBind_event, hybridPrefix_event_overwrite, ofReal_hybridEvidence]

def resampledSignedPrefix {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (u : Query) (c : Cache) :
    ProbComp (BitVec hashBits × β × (Option α × PublicTrace)) := do
  let y ← $ᵗ BitVec hashBits
  let r ← taggedBind (p y) (fun b => hybridPrefix u (post b) (overwrite c u y) [])
  pure (y,r)

/-- Exact joint factorization under an actual uniform coordinate resampling.
The public program is fully adaptive and uses the original mixed lazy oracle. -/
theorem resampledSignedPrefix_joint {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache)
    (event : Option α × PublicTrace → Prop) (target : BitVec hashBits → Prop)
    (likelihood : BitVec hashBits → ℝ) (hl : ∀ y, 0 ≤ likelihood y)
    (hp : ∀ y, E (p y) (fun b' => if b' = b then 1 else 0) = ENNReal.ofReal (likelihood y)) :
    E (resampledSignedPrefix p post u c)
      (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0) =
      ENNReal.ofReal (uniformMean (fun y => if target y then likelihood y else 0) *
        hybridEvidence u (post b) c event) := by
  rw [resampledSignedPrefix, E_bind]
  have hpoint (y : BitVec hashBits) :
      E (taggedBind (p y) (fun b' => hybridPrefix u (post b') (overwrite c u y) []))
        (fun r => E (pure (y,r)) (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0)) =
      ENNReal.ofReal ((if target y then likelihood y else 0) * hybridEvidence u (post b) c event) := by
    simp only [E_pure]
    by_cases hy : target y
    · simp only [hy, true_and, if_true]
      rw [E_taggedHybridPrefix, hp y, ENNReal.ofReal_mul (hl y)]
    · simp [hy, E, expectedValue_def]
  simp only [E_bind, hpoint]
  rw [E_uniform_ofReal _ (fun y => mul_nonneg (by split_ifs <;> simp [hl]) (hybridEvidence_nonneg _ _ _ _)),
    uniformMean_mul_const]

theorem resampledSignedPrefix_bound {α β : Type} (p : BitVec hashBits → ProbComp β)
    (post : β → OracleComp Spec α) (b : β) (u : Query) (c : Cache)
    (event : Option α × PublicTrace → Prop) (target : BitVec hashBits → Prop)
    (likelihood : BitVec hashBits → ℝ) (rate : ℝ) (hl : ∀ y, 0 ≤ likelihood y)
    (hr : 0 ≤ rate)
    (hp : ∀ y, E (p y) (fun b' => if b' = b then 1 else 0) = ENNReal.ofReal (likelihood y))
    (hb : uniformMean (fun y => if target y then likelihood y else 0) ≤ rate*uniformMean likelihood) :
    E (resampledSignedPrefix p post u c)
      (fun r => if target r.1 ∧ r.2.1 = b ∧ event r.2.2 then 1 else 0) ≤
      ENNReal.ofReal rate * E (resampledSignedPrefix p post u c)
        (fun r => if r.2.1 = b ∧ event r.2.2 then 1 else 0) := by
  have hden := resampledSignedPrefix_joint p post b u c event (fun _ => True) likelihood hl hp
  simp only [true_and, if_true] at hden
  rw [resampledSignedPrefix_joint p post b u c event target likelihood hl hp, hden,
    ← ENNReal.ofReal_mul hr]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (rate*uniformMean likelihood)*hybridEvidence u (post b) c event :=
      mul_le_mul_of_nonneg_right hb (hybridEvidence_nonneg _ _ _ _)
    _ = _ := by ring

end
end WeightedReplacement
end

section

/-! Actual all-trial signing followed by an adaptive stopped public prefix.
The prefix keeps the original mixed lazy oracle, and the final signer cache is
passed to it. On a complete row that cache is unchanged, including private hits. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementActualPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

theorem rowQuery_injective (n : ℕ) (m : Message) :
    Function.Injective (fun η : Nonce n => (⟨msgBits+n,m++η⟩ : Query)) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hh := congrArg (fun q : Query => q.2.getLsbD j) h
  simpa only [BitVec.getLsbD_append, if_pos hj] using hh

theorem overwrite_complete_row (n : ℕ) (m : Message) (table : Nonce n → BitVec hashBits)
    (c : Cache) (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (u : Nonce n) (y : BitVec hashBits) :
    ∀ η, overwrite c ⟨msgBits+n,m++u⟩ y ⟨msgBits+n,m++η⟩ =
      some (Function.update table u y η) := by
  intro η
  by_cases hη : η = u
  · subst η
    simp [overwrite]
  · have hq : (⟨msgBits+n,m++η⟩ : Query) ≠ ⟨msgBits+n,m++u⟩ := by
      intro h
      exact hη (rowQuery_injective n m h)
    simp [overwrite, Function.update, hq, Ne.symm hq, hη, Ne.symm hη, hc]

def actualSignedPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (u : Query) (c : Cache) :
    ProbComp (Option (Winner n M) × (Option α × PublicTrace)) := do
  let r ← run (loop n decode tier m k) c
  let t ← hybridPrefix u (post r.1) r.2 []
  pure (r.1,t)

theorem actualSignedPrefix_fixed_row {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u : Query) :
    actualSignedPrefix n decode tier m k post u c =
      taggedBind (Prod.fst <$> run (loop n decode tier m k) c)
        (fun b => hybridPrefix u (post b) c []) := by
  rw [actualSignedPrefix, taggedBind, run_loop_fixed_row n decode tier m table c hc k]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

def resampledActualPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (u : Nonce n) (c : Cache) :
    ProbComp (BitVec hashBits × Option (Winner n M) × (Option α × PublicTrace)) := do
  let y ← $ᵗ BitVec hashBits
  let r ← actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
    (overwrite c ⟨msgBits+n,m++u⟩ y)
  pure (y,r)

theorem resampledActualPrefix_eq {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u : Nonce n) :
    resampledActualPrefix n decode tier m k post u c =
      resampledSignedPrefix
        (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        post ⟨msgBits+n,m++u⟩ c := by
  unfold resampledActualPrefix resampledSignedPrefix
  apply bind_congr
  intro y
  rw [actualSignedPrefix_fixed_row n decode tier m k (Function.update table u y)
    (overwrite c ⟨msgBits+n,m++u⟩ y) (overwrite_complete_row n m table c hc u y)]

theorem loop_cached_target_zero {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (v : Nonce n) (i : Fin M) (c : Cache) (w : BitVec hashBits)
    (hc : c ⟨msgBits+n,m++v⟩ = some w) (hw : decode w ≠ some i) :
    E (Prod.fst <$> run (loop n decode tier m k) c) (fun b => if b = some (v,i) then 1 else 0) = 0 := by
  rw [E_map]
  apply le_antisymm _ bot_le
  apply (expectedValue_mono_of_support (mx := run (loop n decode tier m k) c)
    (h := fun _ => (0:ℝ≥0∞)) ?_).trans (E_const_le _ 0)
  intro p hp
  by_cases hret : p.1 = some (v,i)
  · obtain ⟨hsub, hwin⟩ := loop_support n decode tier m k c p hp
    obtain ⟨w', hw', hd⟩ := hwin v i hret
    have he : w' = w := Option.some.inj (hw'.symm.trans (hsub _ _ hc))
    exact False.elim (hw (he ▸ hd))
  · simp [Function.comp_def, hret]

/-- A fresh uniform resampling of one publicly unexposed row coordinate, then
the actual all-L signer and actual adaptive mixed-oracle prefix. The joint class
and prefix probability is at most p_i/(1-F_i) times the prefix probability.
The returned nonce is fixed to v≠u; there is no Good-event conditioning and no
assumption that u is absent from the implementation cache. -/
theorem actual_prefix_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (u v : Nonce n) (i : Fin M)
    (hvu : v ≠ u) (event : Option α × PublicTrace → Prop)
    (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    E (resampledActualPrefix n decode tier m k post u c)
      (fun r => if decode r.1 = some i ∧ r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E (resampledActualPrefix n decode tier m k post u c)
          (fun r => if r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) := by
  rw [resampledActualPrefix_eq n decode tier m k table c hc post u]
  have hrate : 0 ≤ fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) := by
    apply div_nonneg _ hmass.le
    unfold fraction uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)
  by_cases hv : decode (table v) = some i
  · let A := fractionExcept (weakRank tier i ∘ decode ∘ table) u
    let B := fractionExcept (strictRank tier i ∘ decode ∘ table) u
    let lik := coordinateLikelihood k A B (1/(Fintype.card (Nonce n):ℝ)) (Fintype.card (Nonce n))
      (weakRank tier i ∘ decode) (strictRank tier i ∘ decode)
    have hl : ∀ y, 0 ≤ lik y := coordinateLikelihood_nonneg k A B _ _ _ _
      (fractionExcept_nonneg _ _) (fractionExcept_nonneg _ _) (by positivity) (by positivity)
    have hp : ∀ y, E (Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        (fun b => if b = some (v,i) then 1 else 0) = ENNReal.ofReal (lik y) := by
      intro y
      rw [E_map]
      have hv' : decode (Function.update table u y v) = some i := by
        rw [Function.update_of_ne hvu]
        exact hv
      have hh := E_loop_fixed_row_target n M k decode tier m (Function.update table u y)
        (overwrite c ⟨msgBits+n,m++u⟩ y) (overwrite_complete_row n m table c hc u y) v i hv'
      rw [← tableWinnerLikelihood_eq k (Function.update table u y) decode tier v i hv',
        tableWinnerLikelihood_update k table decode tier u v i hvu hv y] at hh
      convert hh using 1
      congr 1
      funext r
      split_ifs <;> rfl
    have hb : uniformMean (fun y => if decode y = some i then lik y else 0) ≤
        (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode))*uniformMean lik := by
      exact coordinate_uniform_joint k A B _ _ _ _ _
        (fractionExcept_nonneg _ _) (fractionExcept_nonneg _ _) (by positivity) (by positivity)
        (fun y hy => by simp [hy, weakRank, strictRank]) hmass
    have hh := resampledSignedPrefix_bound
      (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
      post (some (v,i)) ⟨msgBits+n,m++u⟩ c event (fun y => decode y = some i) lik _ hl hrate hp hb
    convert hh using 1 <;> congr 1 <;> (try funext r) <;> split_ifs <;> rfl
  · have hp : ∀ y, E (Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
        (fun b => if b = some (v,i) then 1 else 0) = ENNReal.ofReal (0:ℝ) := by
      intro y
      rw [ENNReal.ofReal_zero]
      apply loop_cached_target_zero n decode tier m k v i _ (table v) _ hv
      have hq : (⟨msgBits+n,m++v⟩ : Query) ≠ ⟨msgBits+n,m++u⟩ :=
        fun h => hvu (rowQuery_injective n m h)
      simpa [overwrite, Function.update, hq, Ne.symm hq] using hc v
    have hh := resampledSignedPrefix_bound
      (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c ⟨msgBits+n,m++u⟩ y))
      post (some (v,i)) ⟨msgBits+n,m++u⟩ c event (fun y => decode y = some i) (fun _ => 0) _
      (fun _ => le_rfl) hrate hp (by simp only [ite_self, uniformMean_const, mul_zero, le_refl])
    convert hh using 1 <;> congr 1 <;> (try funext r) <;> split_ifs <;> rfl

end
end WeightedReplacement
end

section

/-! Two-phase finite union, retaining the actual signer's terminal cache and
the signed value as a joint event. All costs refer to the same continuation. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementSignedUnion_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def signedHit {β γ : Type} (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ)
    (b : β) (q : Query) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then publicHit q (post r.1) r.2 else 0)

def signedCharge {β γ : Type} (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ)
    (b : β) (charge : Spec.Domain → ℝ≥0∞) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then expectedCharge charge (post r.1) r.2 else 0)

def signedChosen {D β α : Type} (p : ProbComp (β × Cache)) (forge : β → OracleComp Spec α)
    (chosen : α → D) (b : β) (allowed good : D → Prop) : ℝ≥0∞ :=
  E p (fun r => if r.1 = b then E (run (forge r.1) r.2)
    (fun s => if allowed (chosen s.1) ∧ good (chosen s.1) then 1 else 0) else 0)

theorem signedChosen_union {D β α γ : Type} [Fintype D]
    (p : ProbComp (β × Cache)) (forge : β → OracleComp Spec α)
    (verify : β → α → OracleComp Spec γ) (e : D → Query) (chosen : α → D)
    (b : β) (allowed good : D → Prop)
    (hquery : ∀ s a c, publicHit (e (chosen a)) (verify s a) c = 1) :
    signedChosen p forge chosen b allowed good ≤
      ∑ d, if allowed d ∧ good d then signedHit p (fun s => forge s >>= verify s) b (e d) else 0 := by
  have hpoint (r : β × Cache) :
      (if r.1 = b then E (run (forge r.1) r.2)
        (fun s => if allowed (chosen s.1) ∧ good (chosen s.1) then 1 else 0) else 0) ≤
      ∑ d, if allowed d ∧ good d then (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0 := by
    by_cases hr : r.1 = b
    · simp only [if_pos hr]
      exact selected_input_union e chosen allowed good (forge r.1) (verify r.1) r.2 (hquery r.1)
    · simp [hr]
  calc
    _ ≤ E p (fun r => ∑ d, if allowed d ∧ good d then
        (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0) := E_mono p hpoint
    _ = ∑ d, E p (fun r => if allowed d ∧ good d then
        (if r.1 = b then publicHit (e d) (forge r.1 >>= verify r.1) r.2 else 0) else 0) :=
      expectedValue_finsetSum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : allowed d ∧ good d <;> simp [hd, signedHit, E, expectedValue_def]

theorem signedHit_sum_le_indexPaid {D β γ : Type} [Fintype D] (e : D → Query)
    (he : Function.Injective e) (isIndex : Spec.Domain → Prop)
    (hi : ∀ d, isIndex (.inr (e d))) (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d)))
    (p : ProbComp (β × Cache)) (post : β → OracleComp Spec γ) (b : β) :
    (∑ d, signedHit p post b (e d)) ≤ signedCharge p post b (indexPaid isIndex) := by
  unfold signedHit signedCharge
  rw [← expectedValue_finsetSum p Finset.univ (fun d r => if r.1 = b then publicHit (e d) (post r.1) r.2 else 0)]
  apply E_mono p
  intro r
  by_cases hr : r.1 = b
  · simp only [if_pos hr]
    exact publicHit_sum_le_indexPaid e he isIndex hi hpaid (post r.1) r.2
  · simp [hr]

theorem signedHit_actual_eq {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (b : Option (Winner n M)) (u : Query) (c : Cache) :
    signedHit (run (loop n decode tier m k) c) post b u =
      E (actualSignedPrefix n decode tier m k post u c)
        (fun r => if r.1 = b ∧ r.2.1 = none then 1 else 0) := by
  unfold signedHit actualSignedPrefix
  simp only [E_bind, E_pure]
  congr 1
  funext r
  by_cases hr : r.1 = b
  · simp only [hr, true_and, if_pos]
    exact publicHit_eq_prefix u (post b) r.2 []
  · simp [hr, E, expectedValue_def]

theorem signedHit_actual_gate {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (b : Option (Winner n M))
    (u : Query) (c : Cache) (P : Prop) :
    (if P then signedHit (run (loop n decode tier m k) c) post b u else 0) =
      E (actualSignedPrefix n decode tier m k post u c)
        (fun r => if P ∧ r.1 = b ∧ r.2.1 = none then 1 else 0) := by
  by_cases hP : P
  · simp only [hP, true_and, if_true]
    exact signedHit_actual_eq n decode tier m k post b u c
  · simp [hP, E, expectedValue_def]

/-- Joint posterior estimates at each eligible coordinate combine with actual
public input selection and the shared paid-index cost. The estimates are later
instantiated with the checked same-row and cross-row sampler laws. -/
theorem integrated_signedChosen_bound {Z D β α γ : Type} [Fintype D]
    (latent : ProbComp Z) (p : Z → ProbComp (β × Cache))
    (forge : β → OracleComp Spec α) (verify : β → α → OracleComp Spec γ)
    (e : D → Query) (chosen : α → D) (b : β) (allowed : D → Prop) (good : Z → D → Prop)
    (isIndex : Spec.Domain → Prop) (rate : ℝ≥0∞)
    (he : Function.Injective e) (hi : ∀ d, isIndex (.inr (e d)))
    (hpaid : ∀ d, 1 ≤ queryCost (.inr (e d)))
    (hquery : ∀ s a c, publicHit (e (chosen a)) (verify s a) c = 1)
    (hposterior : ∀ d, allowed d →
      E latent (fun z => if good z d then signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) ≤
        rate * E latent (fun z => signedHit (p z) (fun s => forge s >>= verify s) b (e d))) :
    E latent (fun z => signedChosen (p z) forge chosen b allowed (good z)) ≤
      rate * E latent (fun z => signedCharge (p z) (fun s => forge s >>= verify s) b (indexPaid isIndex)) := by
  calc
    _ ≤ E latent (fun z => ∑ d, if allowed d ∧ good z d then
        signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) :=
      E_mono latent (fun z => signedChosen_union (p z) forge verify e chosen b allowed (good z) hquery)
    _ = ∑ d, E latent (fun z => if allowed d ∧ good z d then
        signedHit (p z) (fun s => forge s >>= verify s) b (e d) else 0) := expectedValue_finsetSum _ _ _
    _ ≤ ∑ d, rate * E latent (fun z => signedHit (p z) (fun s => forge s >>= verify s) b (e d)) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : allowed d
      · simpa only [hd, true_and] using hposterior d hd
      · simp only [hd, false_and, if_false]
        exact (E_const_le _ 0).trans bot_le
    _ = rate * E latent (fun z => ∑ d, signedHit (p z) (fun s => forge s >>= verify s) b (e d)) := by
      rw [← Finset.mul_sum]
      apply congrArg (rate * ·)
      exact (expectedValue_finsetSum latent Finset.univ
        (fun d z => signedHit (p z) (fun s => forge s >>= verify s) b (e d))).symm
    _ ≤ _ := mul_le_mul' le_rfl (E_mono latent
      (fun z => signedHit_sum_le_indexPaid e he isIndex hi hpaid (p z) (fun s => forge s >>= verify s) b))

end
end WeightedReplacement
end
