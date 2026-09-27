import Mathlib

section
namespace WeightedAvailability
attribute [local irreducible] Nat.choose

lemma quartic_binomial_lower (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 4 ≤ n) :
    1 + (n:ℝ)*x + (n.choose 2:ℝ)*x^2 + (n.choose 3:ℝ)*x^3 +
      (n.choose 4:ℝ)*x^4 ≤ (1+x)^n := by
  have hs : Finset.range 5 ⊆ Finset.range (n+1) := Finset.range_mono (by omega)
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i =>
    x^i*(1:ℝ)^(n-i)*(n.choose i:ℝ)) hs (by intro i hi hni; positivity)
  rw [← add_pow] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_pow,
    mul_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    zero_add, pow_one] at h
  simpa only [add_comm, add_left_comm, add_assoc, mul_comm] using h

lemma linear_binomial_lower (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (hn : 1 ≤ n) :
    1+(n:ℝ)*x ≤ (1+x)^n := by
  have hs : Finset.range 2 ⊆ Finset.range (n+1) := Finset.range_mono (by omega)
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i =>
    x^i*(1:ℝ)^(n-i)*(n.choose i:ℝ)) hs (by intro i hi hni; positivity)
  rw [← add_pow] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_pow,
    mul_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    zero_add, pow_one] at h
  simpa only [add_comm, mul_comm] using h

lemma choose_two : Nat.choose 8192 2 = 33550336 := by rw [Nat.choose_two_right]
lemma choose_three : Nat.choose 8192 3 = 91592417280 := by
  have h := Nat.choose_succ_right_eq 8192 2
  norm_num [choose_two] at h
  omega
lemma choose_four : Nat.choose 8192 4 = 187512576276480 := by
  have h := Nat.choose_succ_right_eq 8192 3
  norm_num [choose_three] at h
  omega

lemma reciprocal_block : (256:ℝ)/127 ≤ (1+8999/104848601)^8192 := by
  have h := quartic_binomial_lower (8999/104848601) (by norm_num) 8192 (by norm_num)
  rw [choose_two, choose_three, choose_four] at h
  have hc : (256:ℝ)/127 ≤ 1+(8192:ℝ)*(8999/104848601)+
      33550336*(8999/104848601)^2+91592417280*(8999/104848601)^3+
      187512576276480*(8999/104848601)^4 := by norm_num
  exact hc.trans h

lemma block : (1-(8999:ℝ)/104857600)^8192 ≤ 127/256 := by
  have hn : 0 ≤ (1-(8999:ℝ)/104857600)^8192 := by positivity
  have hp : (1-(8999:ℝ)/104857600)^8192*(1+8999/104848601)^8192=1 := by
    have hb : (1-(8999:ℝ)/104857600)*(1+8999/104848601)=1 := by norm_num
    rw [← mul_pow, hb, one_pow]
  have h := mul_le_mul_of_nonneg_left reciprocal_block hn
  rw [hp] at h
  have hv := (le_div_iff₀ (by norm_num : (0:ℝ) < 256/127)).2 h
  simpa only [one_div_div] using hv

lemma extra_half : ((127:ℝ)/128)^128 ≤ 1/2 := by
  have h := linear_binomial_lower ((1:ℝ)/127) (by norm_num) 128 (by norm_num)
  have hlo : (2:ℝ) ≤ (1+1/127)^128 := by linarith
  have hn : 0 ≤ ((127:ℝ)/128)^128 := by positivity
  have hp : ((127:ℝ)/128)^128*(1+1/127)^128=1 := by
    have hb : ((127:ℝ)/128)*(1+1/127)=1 := by norm_num
    rw [← mul_pow, hb, one_pow]
  have hmul := mul_le_mul_of_nonneg_left hlo hn
  rw [hp] at hmul
  linarith

/-- Complete-row empirical acceptance slack leaves half the failure budget.
This is arithmetic, not yet the actual replacement signer's availability proof. -/
theorem empirical_failure :
    (1-(8999:ℝ)/104857600)^(2^20:ℕ) ≤ ((2:ℝ)^129)⁻¹ := by
  have he : (2^20:ℕ)=8192*128 := by norm_num
  rw [he, pow_mul]
  calc
    ((1-(8999:ℝ)/104857600)^8192)^128 ≤ ((127:ℝ)/256)^128 :=
      pow_le_pow_left₀ (by positivity) block 128
    _ = ((1:ℝ)/2)^128*((127:ℝ)/128)^128 := by rw [← mul_pow]; norm_num
    _ ≤ ((1:ℝ)/2)^128*(1/2) := mul_le_mul_of_nonneg_left extra_half (by positivity)
    _ = ((2:ℝ)^129)⁻¹ := by norm_num

end WeightedAvailability
end

section

/-! Algebraic kernel for the iid-nonce, first-minimum weighted signer.
This module proves polynomial identities and bounds only. The finite random-sampling
law and the full OTS security argument remain separate obligations. -/

namespace WeightedReplacement

/-- The divided-difference polynomial, with no division or unequal-endpoint hypothesis. -/
def kernel (L : ℕ) (A B : ℝ) : ℝ :=
  ∑ k ∈ Finset.range L, A^k * B^(L-1-k)

@[simp] theorem kernel_zero (A B : ℝ) : kernel 0 A B = 0 := by simp [kernel]

theorem kernel_nonneg (L : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ kernel L A B := by
  unfold kernel
  exact Finset.sum_nonneg fun k hk => mul_nonneg (pow_nonneg hA _) (pow_nonneg hB _)

/-- Monotonicity in both survival probabilities, including equal endpoints. -/
theorem kernel_mono (L : ℕ) {A B A' B' : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAA : A ≤ A') (hBB : B ≤ B') : kernel L A B ≤ kernel L A' B' := by
  unfold kernel
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul (pow_le_pow_left₀ hA hAA k)
    (pow_le_pow_left₀ hB hBB (L-1-k)) (pow_nonneg hB _) (pow_nonneg (hA.trans hAA) _)

/-- Every term has degree L-1; the identity also covers L=0. -/
theorem kernel_scale (L : ℕ) (c A B : ℝ) :
    kernel L (c*A) (c*B) = c^(L-1)*kernel L A B := by
  unfold kernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < L := Finset.mem_range.mp hk
  have he : k+(L-1-k)=L-1 := by omega
  rw [mul_pow, mul_pow]
  calc
    (c^k*A^k)*(c^(L-1-k)*B^(L-1-k))
        = (c^k*c^(L-1-k))*(A^k*B^(L-1-k)) := by ring
    _ = c^(L-1)*(A^k*B^(L-1-k)) := by rw [← pow_add, he]

/-- Difference of powers with no positivity or strictness assumptions. -/
theorem sub_mul_kernel (L : ℕ) (A B : ℝ) :
    (A-B)*kernel L A B = A^L-B^L := by
  exact (Commute.all A B).mul_geom_sum₂ L

/-- Compare arbitrary nonnegative empirical endpoints to scaled reference endpoints. -/
theorem kernel_le_scaled (L : ℕ) {Ah Bh A B c : ℝ}
    (hAh : 0 ≤ Ah) (hBh : 0 ≤ Bh) (hA : Ah ≤ c*A) (hB : Bh ≤ c*B) :
    kernel L Ah Bh ≤ c^(L-1)*kernel L A B := by
  exact (kernel_mono L hAh hBh hA hB).trans_eq (kernel_scale L c A B)

/-- An additive prefix-deficit bound becomes one common multiplicative envelope.
Here z is a positive lower bound on both reference survival endpoints. -/
theorem kernel_additive_envelope (L : ℕ) {Ah Bh A B z delta : ℝ}
    (hAh : 0 ≤ Ah) (hBh : 0 ≤ Bh) (hz : 0 < z) (hd : 0 ≤ delta)
    (hzA : z ≤ A) (hzB : z ≤ B) (hA : Ah ≤ A+delta) (hB : Bh ≤ B+delta) :
    kernel L Ah Bh ≤ (1+delta/z)^(L-1)*kernel L A B := by
  have hdz : 0 ≤ delta/z := div_nonneg hd hz.le
  have hAz : delta ≤ (delta/z)*A := by
    have hh := mul_le_mul_of_nonneg_left hzA hdz
    have he : (delta/z)*z=delta := div_mul_cancel₀ delta hz.ne'
    linarith
  have hBz : delta ≤ (delta/z)*B := by
    have hh := mul_le_mul_of_nonneg_left hzB hdz
    have he : (delta/z)*z=delta := div_mul_cancel₀ delta hz.ne'
    linarith
  apply kernel_le_scaled L hAh hBh
  · nlinarith
  · nlinarith

end WeightedReplacement
end

section

/-! Exact finite-table iid sampling law. `iidMean` is the expectation obtained by
independently drawing one uniform element at every recursive step. A fixed target
is returned precisely when earlier draws are strictly worse and later draws are
weakly worse. Repeated nonce values are included without any distinctness premise. -/

namespace WeightedReplacement

attribute [local instance] Classical.propDecidable

noncomputable def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

noncomputable def iidMean {α : Type*} [Fintype α] : ℕ → (List α → ℝ) → ℝ
  | 0, f => f []
  | n+1, f => uniformMean fun a => iidMean n (fun xs => f (a :: xs))

noncomputable def allPass {α : Type*} (weak : α → Prop) (xs : List α) : ℝ :=
  if ∀ a ∈ xs, weak a then 1 else 0

noncomputable def targetWins {α : Type*} (v : α) (weak strict : α → Prop) : List α → ℝ
  | [] => 0
  | a :: xs => if a = v then allPass weak xs else
      if strict a then targetWins v weak strict xs else 0

noncomputable def fraction {α : Type*} [Fintype α] (p : α → Prop) : ℝ :=
  uniformMean fun a => if p a then 1 else 0

/-- A target occurrence with only strictly worse draws before it and only weakly
worse draws after it is exactly a first occurrence at the minimum accepted tier. -/
def FirstMinimumEvent {α : Type*} (v : α) (weak strict : α → Prop) (xs : List α) : Prop :=
  ∃ pre post, xs = pre ++ v :: post ∧ (∀ a ∈ pre, strict a) ∧ (∀ a ∈ post, weak a)

theorem firstMinimumEvent_nil {α : Type*} (v : α) (weak strict : α → Prop) :
    ¬ FirstMinimumEvent v weak strict [] := by
  rintro ⟨pre, post, he, _, _⟩
  have hh := congrArg List.length he
  simp at hh

theorem firstMinimumEvent_cons {α : Type*} (v a : α) (weak strict : α → Prop)
    (xs : List α) :
    FirstMinimumEvent v weak strict (a :: xs) ↔
      (a = v ∧ ∀ b ∈ xs, weak b) ∨ (strict a ∧ FirstMinimumEvent v weak strict xs) := by
  constructor
  · rintro ⟨pre, post, he, hpre, hpost⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      exact Or.inl ⟨he.1, he.2 ▸ hpost⟩
    | cons b pre =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact Or.inr ⟨hpre a (by simp), pre, post, he,
        fun c hc => hpre c (by simp [hc]), hpost⟩
  · rintro (⟨rfl, hx⟩ | ⟨ha, pre, post, he, hpre, hpost⟩)
    · exact ⟨[], xs, rfl, by simp, hx⟩
    · refine ⟨a :: pre, post, ?_, ?_, hpost⟩
      · simp [he]
      · simpa using And.intro ha hpre

theorem targetWins_indicator {α : Type*} (v : α) (weak strict : α → Prop)
    (hv : ¬ strict v) (xs : List α) :
    targetWins v weak strict xs = if FirstMinimumEvent v weak strict xs then 1 else 0 := by
  classical
  induction xs with
  | nil => simp [targetWins, firstMinimumEvent_nil]
  | cons a xs ih =>
    rw [firstMinimumEvent_cons]
    by_cases ha : a = v
    · subst a
      simp [targetWins, hv, allPass]
    · by_cases hs : strict a
      · simp [targetWins, ha, hs, ih]
      · simp [targetWins, ha, hs]

theorem uniformMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uniformMean (fun a => f a * c) = uniformMean f * c := by
  simp [uniformMean, ← Finset.sum_mul, div_mul_eq_mul_div]

theorem uniformMean_gate {α : Type*} [Fintype α] (p : α → Prop) (c : ℝ) :
    uniformMean (fun a => if p a then c else 0) = fraction p * c := by
  classical
  unfold fraction
  rw [← uniformMean_mul_const]
  congr 1
  funext a
  split_ifs <;> simp

theorem uniformMean_point {α : Type*} [Fintype α] (v : α) (c : ℝ) :
    uniformMean (fun a => if a = v then c else 0) = c / Fintype.card α := by
  classical
  simp [uniformMean]

theorem iidMean_zero {α : Type*} [Fintype α] (n : ℕ) :
    iidMean n (fun _ : List α => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iidMean, ih, uniformMean]

theorem iidMean_allPass {α : Type*} [Fintype α] (weak : α → Prop) (n : ℕ) :
    iidMean n (allPass weak) = fraction weak ^ n := by
  classical
  induction n with
  | zero => simp [iidMean, allPass]
  | succ n ih =>
    have hh (a : α) :
        iidMean n (fun xs => allPass weak (a :: xs)) =
          if weak a then fraction weak ^ n else 0 := by
      by_cases ha : weak a
      · have hf : (fun xs => allPass weak (a :: xs)) = allPass weak := by
          funext xs
          simp [allPass, ha]
        simpa only [hf, if_pos ha] using ih
      · simp [allPass, ha, iidMean_zero]
    simp only [iidMean, hh]
    rw [uniformMean_gate, pow_succ']

theorem iidMean_targetWins_succ {α : Type*} [Fintype α]
    (v : α) (weak strict : α → Prop) (hv : ¬ strict v) (n : ℕ) :
    iidMean (n+1) (targetWins v weak strict) =
      fraction weak ^ n / Fintype.card α +
        fraction strict * iidMean n (targetWins v weak strict) := by
  classical
  have hh (a : α) :
      iidMean n (fun xs => targetWins v weak strict (a :: xs)) =
        (if a = v then fraction weak ^ n else 0) +
        (if strict a then iidMean n (targetWins v weak strict) else 0) := by
    by_cases ha : a = v
    · subst a
      simp [targetWins, hv, iidMean_allPass]
    · by_cases hs : strict a
      · simp [targetWins, ha, hs]
      · simp [targetWins, ha, hs, iidMean_zero]
  simp only [iidMean, hh]
  rw [uniformMean_add, uniformMean_point, uniformMean_gate]

theorem kernel_succ (n : ℕ) (A B : ℝ) :
    kernel (n+1) A B = A^n + B * kernel n A B := by
  unfold kernel
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
  rw [Finset.mul_sum]
  have hh : (∑ k ∈ Finset.range n, A^k * B^(n-k)) =
      ∑ k ∈ Finset.range n, B * (A^k * B^(n-1-k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : n-k = (n-1-k)+1 := by omega
    rw [he, pow_succ]
    ring
  rw [hh]
  ring

/-- The exact probability that iid uniform draws return a fixed nonce under the
first-minimum rule. `weak` means no better than the target; `strict` means strictly
worse, including rejected draws. The only algebraic premise is that the target
is not strictly worse than itself. -/
theorem iid_first_minimum_probability {α : Type*} [Fintype α]
    (v : α) (weak strict : α → Prop) (hv : ¬ strict v) (n : ℕ) :
    iidMean n (targetWins v weak strict) =
      kernel n (fraction weak) (fraction strict) / Fintype.card α := by
  induction n with
  | zero => simp [iidMean, targetWins]
  | succ n ih =>
    rw [iidMean_targetWins_succ v weak strict hv, ih, kernel_succ]
    ring

theorem iid_first_minimum_event_probability {α : Type*} [Fintype α]
    (v : α) (weak strict : α → Prop) (hv : ¬ strict v) (n : ℕ) :
    iidMean n (fun xs => if FirstMinimumEvent v weak strict xs then 1 else 0) =
      kernel n (fraction weak) (fraction strict) / Fintype.card α := by
  classical
  simp_rw [← targetWins_indicator v weak strict hv]
  exact iid_first_minimum_probability v weak strict hv n

end WeightedReplacement
end

section

/-! One-coordinate Bayes bound for a signed first-minimum nonce. This module does
not condition on any global Good event. The prior weights may be arbitrary
nonnegative finite weights; the bound is invariant under their normalization.
Connecting fixed-coordinate tables to an adaptive oracle filtration is separate. -/

namespace WeightedReplacement

open scoped Classical

noncomputable def weightedMass {α : Type*} [Fintype α]
    (weight : α → ℝ) (event : α → Prop) : ℝ :=
  ∑ a, if event a then weight a else 0

theorem weightedMass_nonneg {α : Type*} [Fintype α]
    (weight : α → ℝ) (event : α → Prop) (hw : ∀ a, 0 ≤ weight a) :
    0 ≤ weightedMass weight event := by
  apply Finset.sum_nonneg
  intro a ha
  split_ifs <;> simp [hw]

/-- The unknown coordinate contributes δ to A when weakly worse and to B when
strictly worse. A and B contain only the other fixed nonce coordinates. -/
noncomputable def coordinateLikelihood {α : Type*} (L : ℕ) (A B δ N : ℝ)
    (weak strict : α → Prop) (a : α) : ℝ :=
  kernel L (A + if weak a then δ else 0) (B + if strict a then δ else 0) / N

theorem coordinateLikelihood_nonneg {α : Type*} (L : ℕ) (A B δ N : ℝ)
    (weak strict : α → Prop) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hN : 0 ≤ N) (a : α) :
    0 ≤ coordinateLikelihood L A B δ N weak strict a := by
  unfold coordinateLikelihood
  apply div_nonneg _ hN
  apply kernel_nonneg
  · split_ifs <;> linarith
  · split_ifs <;> linarith

theorem coordinateLikelihood_same {α : Type*} (L : ℕ) (A B δ N : ℝ)
    (weak strict : α → Prop) (a : α) (hw : weak a) (hs : ¬ strict a) :
    coordinateLikelihood L A B δ N weak strict a = kernel L (A+δ) B / N := by
  simp [coordinateLikelihood, hw, hs]

/-- Changing the unknown nonce from the signed tier to a higher tier or rejection
cannot reduce the signed target's likelihood. Equal-tier answers have equal likelihood. -/
theorem coordinateLikelihood_survival {α : Type*} (L : ℕ) (A B δ N : ℝ)
    (weak strict : α → Prop) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hN : 0 ≤ N) (a : α) (hw : weak a) :
    kernel L (A+δ) B / N ≤ coordinateLikelihood L A B δ N weak strict a := by
  unfold coordinateLikelihood
  rw [if_pos hw]
  apply div_le_div_of_nonneg_right _ hN
  apply kernel_mono L (add_nonneg hA hδ) hB le_rfl
  split_ifs <;> linarith

end WeightedReplacement
end

section

/-! One-step Bernstein exponential moments from explicit positive expectation.
This file does not assert a stochastic-process concentration or OTS theorem. -/

noncomputable section
namespace WeightedMGF

open scoped BigOperators

/-- The exponential tail after degree one is dominated by a geometric series
with ratio x/3. -/
theorem factorial_geometric (n : ℕ) : 2 * 3^n ≤ (n+2).factorial := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, Nat.factorial_succ, pow_succ]
    calc
      2*(3^n*3) = 3*(2*3^n) := by ring
      _ ≤ (n+2+1)*(n+2).factorial := Nat.mul_le_mul (by omega) ih

/-- Scalar Bernstein remainder bound, including negative increments. -/
theorem exp_bernstein (x b : ℝ) (hb : 0 ≤ b) (hb3 : b < 3)
    (hxb : |x| ≤ b) :
    Real.exp x ≤ 1+x+x^2/(2*(1-b/3)) := by
  have hf := Real.summable_pow_div_factorial x
  have htail : Summable (fun n : ℕ => x^(n+2)/((n+2).factorial : ℝ)) :=
    (summable_nat_add_iff 2).2 hf
  have hgeo : HasSum (fun n : ℕ => (b/3)^n) (1-b/3)⁻¹ :=
    hasSum_geometric_of_lt_one (by positivity) (by linarith)
  have hterm (n : ℕ) : x^(n+2)/((n+2).factorial : ℝ) ≤ (x^2/2)*(b/3)^n := by
    have hxp : x^n ≤ b^n :=
      (le_abs_self _).trans ((abs_pow x n).le.trans (pow_le_pow_left₀ (abs_nonneg _) hxb n))
    have hnum : x^(n+2) ≤ x^2*b^n := by
      have hp := mul_le_mul_of_nonneg_right hxp (sq_nonneg x)
      simpa only [pow_add, mul_comm] using hp
    have hfact : (2:ℝ)*3^n ≤ (n+2).factorial := by exact_mod_cast factorial_geometric n
    have hd : (0:ℝ) < 2*3^n := by positivity
    calc
      x^(n+2)/((n+2).factorial : ℝ) ≤ (x^2*b^n)/((n+2).factorial : ℝ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (x^2*b^n)/(2*3^n) :=
        div_le_div_of_nonneg_left (by positivity) hd hfact
      _ = (x^2/2)*(b/3)^n := by rw [div_pow]; ring
  have ht := htail.tsum_le_tsum hterm (hgeo.summable.mul_left (x^2/2))
  rw [tsum_mul_left, hgeo.tsum_eq] at ht
  have hid : Real.exp x = 1+x+∑' n : ℕ, x^(n+2)/((n+2).factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hp := hf.sum_add_tsum_nat_add 2
    simpa [Finset.sum_range_succ] using hp.symm
  rw [hid]
  have heq : (x^2/2)*(1-b/3)⁻¹ = x^2/(2*(1-b/3)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at ht
  linarith

variable {Ω : Type*}

@[simp] theorem expect_mul (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a : ℝ) (f : Ω → ℝ) :
    E (fun ω => a*f ω) = a*E f := by
  change E (a • f) = a • E f
  exact E.map_smul a f

@[simp] theorem expect_add (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (f g : Ω → ℝ) :
    E (fun ω => f ω+g ω) = E f+E g := E.map_add f g

@[simp] theorem expect_const (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hnorm : E (fun _ => 1) = 1) (a : ℝ) : E (fun _ => a) = a := by
  have hx := expect_mul E a (fun _ => 1)
  simpa [hnorm] using hx

/-- Exact Bernstein one-step MGF, under explicit zero-mean, second-moment,
and bounded-increment hypotheses. -/
theorem centered_mgf
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (X : Ω → ℝ) (θ J v : ℝ)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ*J < 3)
    (hbound : ∀ ω, |X ω| ≤ J)
    (hmean : E X = 0) (hsecond : E (fun ω => (X ω)^2) ≤ v) :
    E (fun ω => Real.exp (θ*X ω)) ≤
      Real.exp (θ^2*v/(2*(1-θ*J/3))) := by
  have hden : 0 < 2*(1-θ*J/3) := by linarith
  have hpoint (ω : Ω) : Real.exp (θ*X ω) ≤
      1+θ*X ω+(θ^2/(2*(1-θ*J/3)))*(X ω)^2 := by
    have hb : |θ*X ω| ≤ θ*J := by
      rw [abs_mul, abs_of_nonneg hθ]
      exact mul_le_mul_of_nonneg_left (hbound ω) hθ
    have hx := exp_bernstein (θ*X ω) (θ*J) (mul_nonneg hθ hJ) hθJ hb
    convert hx using 1 <;> ring
  have havg := hmono _ _ hpoint
  simp only [expect_add, expect_const E hnorm, expect_mul, hmean, mul_zero, add_zero] at havg
  have hvariance := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ θ^2/(2*(1-θ*J/3)) by positivity)
  have hlinear : E (fun ω => Real.exp (θ*X ω)) ≤ 1+θ^2*v/(2*(1-θ*J/3)) := by
    calc
      E (fun ω => Real.exp (θ*X ω)) ≤ 1+(θ^2/(2*(1-θ*J/3)))*v := by linarith
      _ = _ := by ring
  exact hlinear.trans (by simpa only [add_comm] using Real.add_one_le_exp (θ^2*v/(2*(1-θ*J/3))))

@[simp] theorem expect_sub (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (f g : Ω → ℝ) :
    E (fun ω => f ω-g ω) = E f-E g := E.map_sub f g

/-- The bounded nonnegative increment form used by the clipped-row hazard.
The mean and variance bounds follow from 0 ≤ U ≤ J; they are not additional
unverified probabilistic hypotheses. -/
theorem nonnegative_centered_mgf
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (U : Ω → ℝ) (θ J : ℝ)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ*J < 3)
    (hU0 : ∀ ω, 0 ≤ U ω) (hUJ : ∀ ω, U ω ≤ J) :
    E (fun ω => Real.exp (θ*(U ω-E U))) ≤
      Real.exp (θ^2*(J*E U)/(2*(1-θ*J/3))) := by
  have hμ0 : 0 ≤ E U := by
    have hx := hmono (fun _ => 0) U hU0
    simpa only [expect_const E hnorm] using hx
  have hμJ : E U ≤ J := by
    have hx := hmono U (fun _ => J) hUJ
    simpa only [expect_const E hnorm] using hx
  have hbound (ω : Ω) : |U ω-E U| ≤ J := by
    rw [abs_le]
    constructor <;> linarith [hU0 ω, hUJ ω]
  have hmean : E (fun ω => U ω-E U) = 0 := by
    rw [expect_sub, expect_const E hnorm, sub_self]
  have hsqpt (ω : Ω) : (U ω)^2 ≤ J*U ω := by
    nlinarith [hU0 ω, hUJ ω]
  have hsq := hmono _ _ hsqpt
  rw [expect_mul] at hsq
  have hid : E (fun ω => (U ω-E U)^2) =
      E (fun ω => (U ω)^2)+(-2*E U)*E U+(E U)^2 := by
    have hf : (fun ω => (U ω-E U)^2) =
        (fun ω => (U ω)^2+(-2*E U)*U ω+(E U)^2) := by funext ω; ring
    rw [hf, expect_add, expect_add, expect_mul, expect_const E hnorm]
  have hvariance : E (fun ω => (U ω-E U)^2) ≤ J*E U := by
    rw [hid]
    nlinarith [sq_nonneg (E U)]
  exact centered_mgf E hmono hnorm (fun ω => U ω-E U) θ J (J*E U)
    hθ hJ hθJ hbound hmean hvariance

/-- Exponentially compensated one-step expectation. This is the local
supermartingale inequality; chaining conditional kernels is a separate step. -/
theorem compensated_mgf
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (X : Ω → ℝ) (θ J v : ℝ)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ*J < 3)
    (hbound : ∀ ω, |X ω| ≤ J)
    (hmean : E X = 0) (hsecond : E (fun ω => (X ω)^2) ≤ v) :
    E (fun ω => Real.exp (θ*X ω-θ^2*v/(2*(1-θ*J/3)))) ≤ 1 := by
  let b := θ^2*v/(2*(1-θ*J/3))
  have hx := centered_mgf E hmono hnorm X θ J v hθ hJ hθJ hbound hmean hsecond
  have hm := mul_le_mul_of_nonneg_left hx (Real.exp_nonneg (-b))
  have hf : (fun ω => Real.exp (θ*X ω-b)) =
      (fun ω => Real.exp (-b)*Real.exp (θ*X ω)) := by
    funext ω
    rw [sub_eq_add_neg, Real.exp_add, mul_comm]
  change E (fun ω => Real.exp (θ*X ω-b)) ≤ 1
  rw [hf, expect_mul]
  calc
    Real.exp (-b)*E (fun ω => Real.exp (θ*X ω)) ≤ Real.exp (-b)*Real.exp b := hm
    _ = 1 := by rw [← Real.exp_add]; simp

end WeightedMGF
end
end

section

/-! Finite-horizon concentration algebra for explicit probability kernels.
A state may contain the complete adaptive transcript. A concrete random-oracle
experiment still has to provide these kernels and prove the step hypotheses. -/

noncomputable section
namespace WeightedKernel

variable {S : Type*}

@[simp] theorem expect_mul (E : (S → ℝ) →ₗ[ℝ] ℝ) (a : ℝ) (f : S → ℝ) :
    E (fun s => a*f s) = a*E f := by
  change E (a • f) = a • E f
  exact E.map_smul a f

/-- A local compensated-MGF bound implies drift of the exponential potential.
The compensator c is predictable in the current state. -/
theorem exponential_step
    (E : (S → ℝ) →ₗ[ℝ] ℝ) (z a θ c : ℝ) (X : S → ℝ)
    (hmgf : E (fun s => Real.exp (θ*X s-c)) ≤ 1) :
    E (fun s => Real.exp (θ*(z+X s)-(a+c))) ≤ Real.exp (θ*z-a) := by
  have hf : (fun s => Real.exp (θ*(z+X s)-(a+c))) =
      (fun s => Real.exp (θ*z-a)*Real.exp (θ*X s-c)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hf, expect_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg (θ*z-a))

/-- Exponential Markov bound from a checked terminal potential expectation.
This can be used on a first-hit absorbing state to avoid a time union bound;
the absorbing construction itself must still be supplied by the caller. -/
theorem exponential_tail
    (E : (S → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ s, f s ≤ g s) → E f ≤ E g)
    (bad : S → Prop) [DecidablePred bad]
    (Z : S → ℝ) (b : ℝ)
    (hbad : ∀ s, bad s → b ≤ Z s)
    (hmgf : E (fun s => Real.exp (Z s)) ≤ 1) :
    E (fun s => if bad s then 1 else 0) ≤ Real.exp (-b) := by
  have hpt (s : S) : Real.exp b * (if bad s then (1:ℝ) else 0) ≤ Real.exp (Z s) := by
    by_cases hs : bad s
    · simp only [if_pos hs, mul_one]
      exact Real.exp_le_exp.mpr (hbad s hs)
    · simp only [if_neg hs, mul_zero]
      exact Real.exp_nonneg _
  have hx := (hmono _ _ hpt).trans hmgf
  rw [expect_mul] at hx
  have hm := mul_le_mul_of_nonneg_left hx (Real.exp_nonneg (-b))
  have he : Real.exp (-b)*Real.exp b = 1 := by rw [← Real.exp_add]; simp
  rw [← mul_assoc, he, one_mul, mul_one] at hm
  exact hm

/-- Bernstein's optimized scalar exponent. -/
theorem optimized_exponent (a v J : ℝ) (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J) :
    let θ := a/(v+J*a/3)
    0 < θ ∧ θ*J < 3 ∧
      θ*a-θ^2*v/(2*(1-θ*J/3)) = a^2/(2*(v+J*a/3)) := by
  dsimp
  have hd : 0 < v+J*a/3 := by positivity
  have hθ : 0 < a/(v+J*a/3) := div_pos ha hd
  have hθJ : a/(v+J*a/3)*J < 3 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).2
    nlinarith
  refine ⟨hθ, hθJ, ?_⟩
  have hrem : 1-a/(v+J*a/3)*J/3 ≠ 0 := by linarith
  field_simp
  <;> ring

end WeightedKernel
end
end

section

/-! Reference probabilities and symbolic security constants for mixed72.
These are arithmetic lemmas, not a forgery-game theorem. -/
noncomputable section
namespace WeightedReference
open WeightedReplacement
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def kappa : ℝ := 1/2^127

/-- A binomial upper bound that avoids expanding a large natural exponent. -/
theorem pow_times_linear_le_one (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (1+x)^n*(1-(n:ℝ)*x) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1+x)^n := by positivity
    have hs : 0 ≤ (1+x)^n*((n:ℝ)+1)*x^2 := by positivity
    push_cast
    rw [pow_succ]
    nlinarith

end WeightedReference
end
end

section

/-! One-query algebra for the clipped row hazard of weighted index sampling.
This is a finite-distribution theorem. It does not formalize signing, the
random-oracle experiment, concentration, or any signature-security claim. -/

noncomputable section

open scoped BigOperators
namespace WeightedRow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure Weights (ι : Type*) [Fintype ι] where
  p : ι → ℝ
  g : ι → ℝ
  p_pos : ∀ i, 0 < p i
  g_nonneg : ∀ i, 0 ≤ g i
  mass_le_one : ∑ i, p i ≤ 1

namespace Weights

variable (w : Weights ι)

/-- Add one observed accepted class. Rejection changes no class count. -/
def bump (k : ι → ℕ) (i : ι) : ι → ℕ := Function.update k i (k i + 1)

def seen (k : ι → ℕ) : ℝ := ∑ i, if k i = 0 then 0 else w.g i

def bad (k row : ι → ℕ) : ℝ :=
  ∑ i, if 2 ≤ k i then (row i : ℝ) * w.g i / w.p i else 0

def score (row : ι → ℕ) : ℝ := ∑ i, (row i : ℝ) * w.g i

def singleton (k row : ι → ℕ) : ℝ :=
  ∑ i, if k i = 1 then (row i : ℝ) * w.g i else 0

def mean : ℝ := ∑ i, w.p i * w.g i

def unseenMean (k : ι → ℕ) : ℝ := ∑ i, if k i = 0 then w.p i * w.g i else 0

/-- `r` includes rejected positions in the distinguished row. -/
def hazard (N : ℝ) (r : ℕ) (k row : ι → ℕ) : ℝ :=
  (1 - (r : ℝ) / N) * w.seen k + w.bad k row / N

/-- Expectation over one oracle output, including the rejected-output atom. -/
def expect (f : Option ι → ℝ) : ℝ :=
  (1 - ∑ i, w.p i) * f none + ∑ i, w.p i * f (some i)

private theorem sum_change (f f' : ι → ℝ) (i : ι)
    (h : ∀ j, j ≠ i → f' j = f j) :
    (∑ j, f' j) = (∑ j, f j) + (f' i - f i) := by
  have he : f' = fun j => f j + if j = i then f' i - f i else 0 := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj, h j hj]
  rw [he, Finset.sum_add_distrib]
  simp

@[simp] theorem seen_bump (k : ι → ℕ) (i : ι) :
    w.seen (bump k i) = w.seen k + if k i = 0 then w.g i else 0 := by
  unfold seen
  rw [sum_change (fun j => if k j = 0 then 0 else w.g j)
    (fun j => if bump k i j = 0 then 0 else w.g j) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  simp [bump]
  split_ifs <;> ring

theorem bad_bump_outside (k row : ι → ℕ) (i : ι) :
    w.bad (bump k i) row = w.bad k row +
      if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0 := by
  unfold bad
  rw [sum_change (fun j => if 2 ≤ k j then (row j : ℝ) * w.g j / w.p j else 0)
    (fun j => if 2 ≤ bump k i j then (row j : ℝ) * w.g j / w.p j else 0) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  simp only [bump, Function.update_self]
  by_cases h0 : k i = 0
  · simp [h0]
  · by_cases h1 : k i = 1
    · simp [h1]
    · have h2 : 2 ≤ k i := by omega
      have h3 : 2 ≤ k i + 1 := by omega
      simp [h1, h2, h3]

theorem bad_bump_inside (k row : ι → ℕ) (i : ι) :
    w.bad (bump k i) (bump row i) = w.bad k row +
      (if k i = 0 then 0 else w.g i / w.p i) +
      (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0) := by
  unfold bad
  rw [sum_change (fun j => if 2 ≤ k j then (row j : ℝ) * w.g j / w.p j else 0)
    (fun j => if 2 ≤ bump k i j then (bump row i j : ℝ) * w.g j / w.p j else 0) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  simp only [bump, Function.update_self, Nat.cast_add, Nat.cast_one]
  by_cases h0 : k i = 0
  · simp [h0]
  · by_cases h1 : k i = 1
    · simp [h1]
      ring
    · have h2 : 2 ≤ k i := by omega
      have h3 : 2 ≤ k i + 1 := by omega
      simp [h0, h1, h2, h3]
      ring

private theorem avg_new (k : ι → ℕ) :
    (∑ i, w.p i * (if k i = 0 then w.g i else 0)) = w.unseenMean k := by
  unfold unseenMean
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

private theorem avg_old (k : ι → ℕ) :
    (∑ i, w.p i * (if k i = 0 then 0 else w.g i / w.p i)) = w.seen k := by
  unfold seen
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : k i = 0
  · simp [h]
  · simp only [if_neg h]
    field_simp [(w.p_pos i).ne']

private theorem avg_singleton (k row : ι → ℕ) :
    (∑ i, w.p i * (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) =
      w.singleton k row := by
  unfold singleton
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : k i = 1
  · simp only [if_pos h]
    field_simp [(w.p_pos i).ne']
  · simp [h]

/-- Exact change if the accepted query is outside the distinguished row. -/
theorem hazard_change_outside (N : ℝ) (r : ℕ) (k row : ι → ℕ) (i : ι) :
    w.hazard N r (bump k i) row - w.hazard N r k row =
      (1 - (r : ℝ) / N) * (if k i = 0 then w.g i else 0) +
      (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0) / N := by
  simp only [hazard, seen_bump, bad_bump_outside]
  ring

/-- Exact change if the accepted query is inside the distinguished row. -/
theorem hazard_change_inside (N : ℝ) (r : ℕ) (k row : ι → ℕ) (i : ι) :
    w.hazard N (r + 1) (bump k i) (bump row i) - w.hazard N r k row =
      (1 - ((r : ℝ) + 1) / N) * (if k i = 0 then w.g i else 0) +
      ((if k i = 0 then 0 else w.g i / w.p i) +
       (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) / N -
      w.seen k / N := by
  simp only [hazard, seen_bump, bad_bump_inside, Nat.cast_add, Nat.cast_one]
  ring

/-- A rejected inside-row query only removes one unknown candidate position. -/
theorem hazard_change_rejected (N : ℝ) (r : ℕ) (k row : ι → ℕ) :
    w.hazard N (r + 1) k row - w.hazard N r k row = -w.seen k / N := by
  simp only [hazard, Nat.cast_add, Nat.cast_one]
  ring

/-- Query outside the row; `none` denotes rejection. -/
def afterOutside (N : ℝ) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ
  | none => w.hazard N r k row
  | some i => w.hazard N r (bump k i) row

/-- Query inside the row; the row position count grows even on rejection. -/
def afterInside (N : ℝ) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ
  | none => w.hazard N (r + 1) k row
  | some i => w.hazard N (r + 1) (bump k i) (bump row i)

/-- Exact conditional drift for a query outside the row. -/
theorem drift_outside (N : ℝ) (r : ℕ) (k row : ι → ℕ) :
    w.expect (fun x => w.afterOutside N r k row x - w.hazard N r k row) =
      (1 - (r : ℝ) / N) * w.unseenMean k + w.singleton k row / N := by
  simp only [expect, afterOutside, sub_self, mul_zero, zero_add, hazard_change_outside]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show (∑ i, w.p i * ((1 - (r : ℝ) / N) *
      (if k i = 0 then w.g i else 0))) =
      (1 - (r : ℝ) / N) * ∑ i, w.p i * (if k i = 0 then w.g i else 0) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [avg_new]
  rw [show (∑ i, w.p i * ((if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0) / N)) =
      (∑ i, w.p i * (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) / N by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intros; ring]
  rw [avg_singleton]

/-- Exact conditional drift for a query inside the row. The rejection atom
cancels the apparent extra `seen/N` term after averaging. -/
theorem drift_inside (N : ℝ) (r : ℕ) (k row : ι → ℕ) :
    w.expect (fun x => w.afterInside N r k row x - w.hazard N r k row) =
      (1 - ((r : ℝ) + 1) / N) * w.unseenMean k + w.singleton k row / N := by
  simp only [expect, afterInside, hazard_change_rejected, hazard_change_inside]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ i, w.p i * ((1 - ((r : ℝ) + 1) / N) *
      (if k i = 0 then w.g i else 0))) =
      (1 - ((r : ℝ) + 1) / N) * ∑ i, w.p i * (if k i = 0 then w.g i else 0) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [avg_new]
  have hsum : (∑ i, w.p i *
      ((if k i = 0 then 0 else w.g i / w.p i) +
       (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) / N) =
      (w.seen k + w.singleton k row) / N := by
    rw [← Finset.sum_div]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [avg_old, avg_singleton]
  simp_rw [← mul_div_assoc]
  rw [hsum, ← Finset.sum_div, ← Finset.sum_mul]
  ring

/-- The rejected-output atom is a nonnegative probability. -/
theorem rejection_nonneg : 0 ≤ 1 - ∑ i, w.p i := sub_nonneg.mpr w.mass_le_one

theorem expect_one : w.expect (fun _ => 1) = 1 := by
  simp only [expect, mul_one]
  ring

theorem unseenMean_nonneg (k : ι → ℕ) : 0 ≤ w.unseenMean k := by
  unfold unseenMean
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg (w.p_pos i).le (w.g_nonneg i)
  · exact le_rfl

theorem unseenMean_le_mean (k : ι → ℕ) : w.unseenMean k ≤ w.mean := by
  unfold unseenMean mean
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (w.p_pos i).le (w.g_nonneg i)

theorem singleton_le_score (k row : ι → ℕ) : w.singleton k row ≤ w.score row := by
  unfold singleton score
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (w.g_nonneg i)

/-- A row-score concentration hypothesis controls either drift formula.
The exact drift identities above hold even without count-consistency hypotheses;
in an actual count matrix one also has row_i≤global_i and sum row_i≤r. -/
theorem drift_expression_le (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) (η κ extra : ℝ)
    (hextra : 0 ≤ extra)
    (hscore : w.score row ≤ (r : ℝ) * w.mean + η * κ * N) :
    (1 - ((r : ℝ) + extra) / N) * w.unseenMean k + w.singleton k row / N ≤
      w.mean + η * κ := by
  have hc : 0 ≤ 1 - (r : ℝ) / N :=
    sub_nonneg.mpr ((div_le_one hN).2 hr)
  have hc' : 1 - ((r : ℝ) + extra) / N ≤ 1 - (r : ℝ) / N := by
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_right (by linarith) hN.le
  calc
    (1 - ((r : ℝ) + extra) / N) * w.unseenMean k + w.singleton k row / N
      ≤ (1 - (r : ℝ) / N) * w.unseenMean k + w.singleton k row / N :=
        add_le_add (mul_le_mul_of_nonneg_right hc' (w.unseenMean_nonneg k)) le_rfl
    _ ≤ (1 - (r : ℝ) / N) * w.mean + w.score row / N :=
        add_le_add (mul_le_mul_of_nonneg_left (w.unseenMean_le_mean k) hc)
          (div_le_div_of_nonneg_right (w.singleton_le_score k row) hN.le)
    _ ≤ (1 - (r : ℝ) / N) * w.mean +
          ((r : ℝ) * w.mean + η * κ * N) / N :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hscore hN.le)
    _ = w.mean + η * κ := by field_simp [hN.ne']; ring

theorem drift_outside_le (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) (η κ : ℝ)
    (hscore : w.score row ≤ (r : ℝ) * w.mean + η * κ * N) :
    w.expect (fun x => w.afterOutside N r k row x - w.hazard N r k row) ≤
      w.mean + η * κ := by
  rw [drift_outside]
  simpa only [add_zero] using w.drift_expression_le N hN r hr k row η κ 0 le_rfl hscore

theorem drift_inside_le (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) (η κ : ℝ)
    (hscore : w.score row ≤ (r : ℝ) * w.mean + η * κ * N) :
    w.expect (fun x => w.afterInside N r k row x - w.hazard N r k row) ≤
      w.mean + η * κ := by
  rw [drift_inside]
  exact w.drift_expression_le N hN r hr k row η κ 1 zero_le_one hscore

/-- Nonnegative part of an outside-row increment. -/
def positiveOutside (N : ℝ) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i =>
      (1 - (r : ℝ) / N) * (if k i = 0 then w.g i else 0) +
      (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0) / N

/-- Nonnegative part of an inside-row increment; `seen/N` is predictable. -/
def positiveInside (N : ℝ) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i =>
      (1 - ((r : ℝ) + 1) / N) * (if k i = 0 then w.g i else 0) +
      ((if k i = 0 then 0 else w.g i / w.p i) +
       (if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0)) / N

theorem increment_outside (N : ℝ) (r : ℕ) (k row : ι → ℕ) (x : Option ι) :
    w.afterOutside N r k row x - w.hazard N r k row =
      w.positiveOutside N r k row x := by
  cases x <;> simp [afterOutside, positiveOutside, hazard_change_outside]

theorem increment_inside (N : ℝ) (r : ℕ) (k row : ι → ℕ) (x : Option ι) :
    w.afterInside N r k row x - w.hazard N r k row =
      w.positiveInside N r k row x - w.seen k / N := by
  cases x <;> simp [afterInside, positiveInside, hazard_change_inside,
    hazard_change_rejected, neg_div]

private theorem coeff_bounds (N : ℝ) (hN : 0 < N) (t : ℝ)
    (ht : 0 ≤ t) (htN : t ≤ N) : 0 ≤ 1 - t / N ∧ 1 - t / N ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr ((div_le_one hN).2 htN)
  · exact sub_le_self _ (div_nonneg ht hN.le)

private theorem row_ratio_bounds (k row : ι → ℕ) (hrow : ∀ i, row i ≤ k i)
    (L : ℝ) (hL : 0 ≤ L) (hratio : ∀ i, w.g i / w.p i ≤ L)
    (i : ι) (h1 : k i = 1) :
    0 ≤ (row i : ℝ) * w.g i / w.p i ∧ (row i : ℝ) * w.g i / w.p i ≤ L := by
  have hr : (row i : ℝ) ≤ 1 := by exact_mod_cast (h1 ▸ hrow i)
  have hg := div_nonneg (w.g_nonneg i) (w.p_pos i).le
  constructor
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (w.g_nonneg i)) (w.p_pos i).le
  · calc
      (row i : ℝ) * w.g i / w.p i = (row i : ℝ) * (w.g i / w.p i) := by ring
      _ ≤ 1 * L := mul_le_mul hr (hratio i) hg (by norm_num)
      _ = L := one_mul L

/-- The physical count consistency is used only here, to bound the singleton jump. -/
theorem positiveOutside_bounds (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) (hrow : ∀ i, row i ≤ k i)
    (G L : ℝ) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hg : ∀ i, w.g i ≤ G) (hratio : ∀ i, w.g i / w.p i ≤ L)
    (x : Option ι) :
    0 ≤ w.positiveOutside N r k row x ∧
      w.positiveOutside N r k row x ≤ G + 2 * L / N := by
  have hLN : 0 ≤ L / N := div_nonneg hL hN.le
  have htwo : 2 * L / N = 2 * (L / N) := by ring
  have hc := coeff_bounds N hN r (Nat.cast_nonneg _) hr
  cases x with
  | none => simp only [positiveOutside]; constructor <;> nlinarith
  | some i =>
    by_cases h0 : k i = 0
    · have h1 : k i ≠ 1 := by omega
      simp only [positiveOutside, if_pos h0, if_neg h1, zero_div, add_zero]
      have hu : (1 - (r : ℝ) / N) * w.g i ≤ G :=
        (mul_le_mul_of_nonneg_right hc.2 (w.g_nonneg i)).trans (by simpa using hg i)
      constructor
      · exact mul_nonneg hc.1 (w.g_nonneg i)
      · nlinarith
    · by_cases h1 : k i = 1
      · simp only [positiveOutside, if_neg h0, if_pos h1, mul_zero, zero_add]
        have hb := w.row_ratio_bounds k row hrow L hL hratio i h1
        have hd := div_le_div_of_nonneg_right hb.2 hN.le
        constructor
        · exact div_nonneg hb.1 hN.le
        · nlinarith
      · simp only [positiveOutside, if_neg h0, if_neg h1, mul_zero, zero_div, add_zero]
        constructor <;> nlinarith

theorem positiveInside_bounds (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) + 1 ≤ N) (k row : ι → ℕ) (hrow : ∀ i, row i ≤ k i)
    (G L : ℝ) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hg : ∀ i, w.g i ≤ G) (hratio : ∀ i, w.g i / w.p i ≤ L)
    (x : Option ι) :
    0 ≤ w.positiveInside N r k row x ∧
      w.positiveInside N r k row x ≤ G + 2 * L / N := by
  have hLN : 0 ≤ L / N := div_nonneg hL hN.le
  have htwo : 2 * L / N = 2 * (L / N) := by ring
  have hc := coeff_bounds N hN ((r : ℝ) + 1) (by positivity) hr
  cases x with
  | none => simp only [positiveInside]; constructor <;> nlinarith
  | some i =>
    by_cases h0 : k i = 0
    · have h1 : k i ≠ 1 := by omega
      simp only [positiveInside, if_pos h0, if_neg h1, add_zero, zero_div]
      have hu : (1 - ((r : ℝ) + 1) / N) * w.g i ≤ G :=
        (mul_le_mul_of_nonneg_right hc.2 (w.g_nonneg i)).trans (by simpa using hg i)
      constructor
      · exact mul_nonneg hc.1 (w.g_nonneg i)
      · nlinarith
    · have hgi : 0 ≤ w.g i / w.p i := div_nonneg (w.g_nonneg i) (w.p_pos i).le
      by_cases h1 : k i = 1
      · simp only [positiveInside, if_neg h0, if_pos h1, mul_zero, zero_add]
        have hb := w.row_ratio_bounds k row hrow L hL hratio i h1
        have hd : (w.g i / w.p i + (row i : ℝ) * w.g i / w.p i) / N ≤ 2 * L / N :=
          div_le_div_of_nonneg_right (by linarith [hratio i]) hN.le
        constructor
        · exact div_nonneg (add_nonneg hgi hb.1) hN.le
        · linarith
      · simp only [positiveInside, if_neg h0, if_neg h1, mul_zero, add_zero, zero_add]
        have hd := div_le_div_of_nonneg_right (hratio i) hN.le
        constructor
        · exact div_nonneg hgi hN.le
        · nlinarith

/-- Elementary finite-distribution expectation rules, retaining rejection. -/
theorem expect_const (a : ℝ) : w.expect (fun _ => a) = a := by
  simp only [expect, ← Finset.sum_mul]
  ring

theorem expect_add (f f' : Option ι → ℝ) :
    w.expect (fun x => f x + f' x) = w.expect f + w.expect f' := by
  simp only [expect, mul_add, Finset.sum_add_distrib]
  ring

theorem expect_sub (f f' : Option ι → ℝ) :
    w.expect (fun x => f x - f' x) = w.expect f - w.expect f' := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]
  ring

theorem expect_smul (a : ℝ) (f : Option ι → ℝ) :
    w.expect (fun x => a * f x) = a * w.expect f := by
  unfold expect
  rw [show (∑ i, w.p i * (a * f (some i))) = a * ∑ i, w.p i * f (some i) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  ring

theorem expect_mono (f f' : Option ι → ℝ) (h : ∀ x, f x ≤ f' x) :
    w.expect f ≤ w.expect f' := by
  unfold expect
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (h none) w.rejection_nonneg
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h (some i)) (w.p_pos i).le)

theorem expect_nonneg (f : Option ι → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ w.expect f := by
  simpa only [expect_const] using w.expect_mono (fun _ => 0) f hf

theorem expect_le_const (f : Option ι → ℝ) (d : ℝ) (hf : ∀ x, f x ≤ d) :
    w.expect f ≤ d := by
  simpa only [expect_const] using w.expect_mono f (fun _ => d) hf

/-- Subtracting a predictable scalar does not change the centered increment. -/
theorem center_predictable_shift (u : Option ι → ℝ) (c : ℝ) (x : Option ι) :
    (u x - c) - w.expect (fun y => u y - c) = u x - w.expect u := by
  rw [expect_sub, expect_const]
  ring

/-- Exact second centered moment for this finite distribution. -/
theorem centered_square (u : Option ι → ℝ) :
    w.expect (fun x => (u x - w.expect u)^2) =
      w.expect (fun x => (u x)^2) - (w.expect u)^2 := by
  calc
    w.expect (fun x => (u x - w.expect u)^2) =
        w.expect (fun x => (u x)^2 - (2 * w.expect u) * u x + (w.expect u)^2) := by
          congr 1; funext x; ring
    _ = w.expect (fun x => (u x)^2) - (w.expect u)^2 := by
      rw [expect_add, expect_sub, expect_smul, expect_const]
      ring

/-- A nonnegative jump in [0,d] has variance at most d times its mean. -/
theorem centered_variance_le (u : Option ι → ℝ) (d : ℝ)
    (hu : ∀ x, 0 ≤ u x ∧ u x ≤ d) :
    w.expect (fun x => (u x - w.expect u)^2) ≤ d * w.expect u := by
  have hsq : w.expect (fun x => (u x)^2) ≤ w.expect (fun x => d * u x) := by
    apply w.expect_mono
    intro x
    nlinarith [(hu x).1, (hu x).2]
  rw [expect_smul] at hsq
  rw [centered_square]
  nlinarith [sq_nonneg (w.expect u)]

/-- Its centered increment is also bounded in absolute value by d. -/
theorem centered_abs_le (u : Option ι → ℝ) (d : ℝ)
    (hu : ∀ x, 0 ≤ u x ∧ u x ≤ d) (x : Option ι) :
    |u x - w.expect u| ≤ d := by
  have hm0 := w.expect_nonneg u (fun y => (hu y).1)
  have hmd := w.expect_le_const u d (fun y => (hu y).2)
  apply abs_le.mpr
  constructor <;> linarith [(hu x).1, (hu x).2]

end Weights
end WeightedRow
end
end

section

/-! Exact class-count moments. A fresh rejected index query advances q while
leaving class counts unchanged. Cached/non-index queries leave both unchanged.
No actual random-oracle distribution is assumed from these finite identities. -/

noncomputable section
open scoped BigOperators
namespace WeightedRow.Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (w : WeightedRow.Weights ι)

/-- Weighted unordered collision-pair count. -/
def pairScore (k : ι → ℕ) : ℝ := ∑ i, (Nat.choose (k i) 2 : ℝ)*w.g i/w.p i

def advance (k : ι → ℕ) : Option ι → (ι → ℕ)
  | none => k
  | some i => bump k i

def scoreJump : Option ι → ℝ
  | none => 0
  | some i => w.g i

def pairJump (k : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i => (k i : ℝ)*w.g i/w.p i

private theorem sum_update_delta (f f' : ι → ℝ) (i : ι)
    (h : ∀ j, j ≠ i → f' j = f j) :
    (∑ j, f' j) = (∑ j, f j)+(f' i-f i) := by
  have he : f' = fun j => f j + if j=i then f' i-f i else 0 := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj, h j hj]
  rw [he, Finset.sum_add_distrib]
  simp

theorem score_bump (k : ι → ℕ) (i : ι) : w.score (bump k i) = w.score k+w.g i := by
  unfold score
  rw [sum_update_delta (fun j => (k j:ℝ)*w.g j)
    (fun j => (bump k i j:ℝ)*w.g j) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  simp only [bump, Function.update_self, Nat.cast_add, Nat.cast_one]
  ring

theorem pairScore_bump (k : ι → ℕ) (i : ι) :
    w.pairScore (bump k i) = w.pairScore k+(k i:ℝ)*w.g i/w.p i := by
  unfold pairScore
  rw [sum_update_delta (fun j => (Nat.choose (k j) 2:ℝ)*w.g j/w.p j)
    (fun j => (Nat.choose (bump k i j) 2:ℝ)*w.g j/w.p j) i
    (by intro j hj; simp [bump, Function.update_of_ne hj])]
  have hc : Nat.choose (k i+1) 2 = Nat.choose (k i) 2+k i := by
    simpa [Nat.choose_one_right, add_comm] using Nat.choose_succ_succ (k i) 1
  simp only [bump, Function.update_self, hc, Nat.cast_add]
  ring

@[simp] theorem score_advance (k : ι → ℕ) (x : Option ι) :
    w.score (advance k x) = w.score k+w.scoreJump x := by
  cases x <;> simp [advance, scoreJump, score_bump]

@[simp] theorem pairScore_advance (k : ι → ℕ) (x : Option ι) :
    w.pairScore (advance k x) = w.pairScore k+w.pairJump k x := by
  cases x <;> simp [advance, pairJump, pairScore_bump]

@[simp] theorem mean_scoreJump : w.expect w.scoreJump = w.mean := by
  simp [expect, scoreJump, mean]

@[simp] theorem mean_pairJump (k : ι → ℕ) : w.expect (w.pairJump k) = w.score k := by
  simp only [expect, pairJump, mul_zero, zero_add, score]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(w.p_pos i).ne']

theorem scoreJump_bounds (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (x : Option ι) : 0 ≤ w.scoreJump x ∧ w.scoreJump x ≤ G := by
  cases x with
  | none => exact ⟨le_rfl, hG⟩
  | some i => exact ⟨w.g_nonneg i, hg i⟩

/-- Variance-sensitive one-query bound, retaining the rejection atom. -/
theorem score_variance_le (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) :
    w.expect (fun x => (w.scoreJump x-w.mean)^2) ≤ G*w.mean := by
  simpa only [mean_scoreJump] using
    w.centered_variance_le w.scoreJump G (w.scoreJump_bounds G hG hg)

/-- Centered weighted score after q distinct fresh index queries. -/
def M1 (q : ℕ) (k : ι → ℕ) : ℝ := w.score k-w.mean*(q:ℝ)

/-- Pair-energy martingale; q counts fresh rejected index queries too. -/
def M2 (q : ℕ) (k : ι → ℕ) : ℝ :=
  w.pairScore k-(q:ℝ)*w.score k+w.mean*(q:ℝ)*((q:ℝ)+1)/2

theorem M1_increment (q : ℕ) (k : ι → ℕ) (x : Option ι) :
    w.M1 (q+1) (advance k x) = w.M1 q k+(w.scoreJump x-w.mean) := by
  simp only [M1, score_advance, Nat.cast_add, Nat.cast_one]
  ring

theorem M2_increment (q : ℕ) (k : ι → ℕ) (x : Option ι) :
    w.M2 (q+1) (advance k x) = w.M2 q k+
      (w.pairJump k x-w.score k)-((q:ℝ)+1)*(w.scoreJump x-w.mean) := by
  simp only [M2, score_advance, pairScore_advance, Nat.cast_add, Nat.cast_one]
  ring

/-- Exact conditional martingale equality for the weighted score. -/
theorem M1_mean_next (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => w.M1 (q+1) (advance k x)) = w.M1 q k := by
  simp_rw [M1_increment]
  rw [expect_add, expect_const, expect_sub, mean_scoreJump, expect_const]
  ring

/-- Exact conditional martingale equality for pair energy. -/
theorem M2_mean_next (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => w.M2 (q+1) (advance k x)) = w.M2 q k := by
  simp_rw [M2_increment]
  rw [expect_sub, expect_add, expect_const, expect_sub, mean_pairJump,
    expect_const, expect_smul, expect_sub, mean_scoreJump, expect_const]
  ring

/-- Predictable quadratic-variation bound, with no independence assumption
between the current score and the history that determined q or k. -/
theorem M1_square_next_le (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => (w.M1 (q+1) (advance k x))^2) ≤ (w.M1 q k)^2+G*w.mean := by
  have hz : w.expect (fun x => w.scoreJump x-w.mean) = 0 := by
    rw [expect_sub, mean_scoreJump, expect_const, sub_self]
  have heq : (fun x => (w.M1 (q+1) (advance k x))^2) =
      (fun x => (w.M1 q k)^2+(2*w.M1 q k)*(w.scoreJump x-w.mean)+(w.scoreJump x-w.mean)^2) := by
    funext x
    rw [M1_increment]
    ring
  rw [heq, expect_add, expect_add, expect_const, expect_smul, hz, mul_zero, add_zero]
  exact add_le_add le_rfl (w.score_variance_le G hG hg)

/-- The square minus G*h times the fresh-query counter has nonpositive drift. -/
theorem M1_compensated_square_next_le (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => (w.M1 (q+1) (advance k x))^2-G*w.mean*((q+1:ℕ):ℝ)) ≤
      (w.M1 q k)^2-G*w.mean*(q:ℝ) := by
  rw [expect_sub, expect_const]
  have hx := w.M1_square_next_le G hG hg q k
  push_cast
  linarith

/-- The rejected class carries the remaining probability mass. -/
def classMass : Option ι → ℝ
  | none => 1-∑ i, w.p i
  | some i => w.p i

/-- Exact decoder law from finite answer-fiber probabilities. This applies to
uniform 256-bit oracle answers once the concrete decoder fibers are supplied. -/
theorem uniform_decoder_expect {β : Type*} [Fintype β] [Nonempty β]
    (decode : β → Option ι)
    (hfiber : ∀ x : Option ι,
      ((Finset.univ.filter (fun b => decode b=x)).card:ℝ)/(Fintype.card β:ℝ) = w.classMass x)
    (f : Option ι → ℝ) :
    (∑ b : β, f (decode b))/(Fintype.card β:ℝ) = w.expect f := by
  have hp := Finset.sum_fiberwise' (Finset.univ : Finset β) decode f
  simp only [Finset.sum_const, nsmul_eq_mul] at hp
  calc
    (∑ b : β, f (decode b))/(Fintype.card β:ℝ) =
        (∑ x : Option ι, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ)*f x)/
          (Fintype.card β:ℝ) := by rw [hp]
    _ = ∑ x : Option ι,
        (((Finset.univ.filter (fun b => decode b=x)).card:ℝ)/(Fintype.card β:ℝ))*f x := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x : Option ι, w.classMass x*f x := by simp_rw [hfiber]
    _ = w.expect f := by rw [Fintype.sum_option]; rfl

/-- A fresh-query flag separates index observations from cached or unrelated
queries. The latter preserve all weighted statistics and the fresh counter. -/
def step (fresh : Bool) (q : ℕ) (k : ι → ℕ) (x : Option ι) : ℕ × (ι → ℕ) :=
  if fresh then (q+1, advance k x) else (q,k)

@[simp] theorem step_not_fresh (q : ℕ) (k : ι → ℕ) (x : Option ι) :
    step false q k x = (q,k) := rfl

theorem M1_step_mean (fresh : Bool) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => w.M1 (step fresh q k x).1 (step fresh q k x).2) = w.M1 q k := by
  cases fresh
  · simp only [step_not_fresh, expect_const]
  · exact w.M1_mean_next q k

theorem M2_step_mean (fresh : Bool) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => w.M2 (step fresh q k x).1 (step fresh q k x).2) = w.M2 q k := by
  cases fresh
  · simp only [step_not_fresh, expect_const]
  · exact w.M2_mean_next q k

theorem M1_step_square_compensated (fresh : Bool) (G : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x =>
      (w.M1 (step fresh q k x).1 (step fresh q k x).2)^2-G*w.mean*((step fresh q k x).1:ℝ)) ≤
        (w.M1 q k)^2-G*w.mean*(q:ℝ) := by
  cases fresh
  · simp only [step_not_fresh, expect_const, le_refl]
  · exact w.M1_compensated_square_next_le G hG hg q k

end WeightedRow.Weights

namespace WeightedPublicCounts
open WeightedRow.Weights
open scoped BigOperators
variable {Q ι : Type*} [DecidableEq Q] [Fintype ι] [DecidableEq ι]

/-- Multiplicities count distinct public index inputs, not repeated queries. -/
def counts (A : Finset Q) (answers : Q → Option ι) (i : ι) : ℕ :=
  (A.filter (fun q => answers q=some i)).card

theorem counts_insert_apply (A : Finset Q) (answers : Q → Option ι)
    (q : Q) (hq : q ∉ A) (i : ι) :
    counts (insert q A) answers i = counts A answers i + if answers q=some i then 1 else 0 := by
  by_cases hi : answers q=some i
  · simp [counts, Finset.filter_insert, hi, hq, add_comm]
  · simp [counts, Finset.filter_insert, hi]

theorem counts_insert (A : Finset Q) (answers : Q → Option ι)
    (q : Q) (hq : q ∉ A) :
    counts (insert q A) answers = advance (counts A answers) (answers q) := by
  cases he : answers q with
  | none =>
    funext i
    simp [counts_insert_apply, hq, he, advance]
  | some j =>
    funext i
    by_cases hij : i=j
    · subst i
      simp [counts_insert_apply, hq, he, advance, bump]
    · simp [counts_insert_apply, hq, he, advance, bump, Function.update_of_ne hij, hij, Ne.symm hij]

theorem counts_update_absent (A : Finset Q) (answers : Q → Option ι)
    (q : Q) (hq : q ∉ A) (x : Option ι) :
    counts A (Function.update answers q x) = counts A answers := by
  funext i
  unfold counts
  congr 1
  apply Finset.filter_congr
  intro r hr
  have hrq : r ≠ q := by intro he; subst r; exact hq hr
  simp [Function.update_of_ne hrq]

/-- The exact count update after exposing one previously absent index input. -/
theorem counts_insert_update (A : Finset Q) (answers : Q → Option ι)
    (q : Q) (hq : q ∉ A) (x : Option ι) :
    counts (insert q A) (Function.update answers q x) = advance (counts A answers) x := by
  rw [counts_insert _ _ _ hq, Function.update_self, counts_update_absent _ _ _ hq]

end WeightedPublicCounts
end
end

section
noncomputable section
open scoped Classical
namespace WeightedCacheCounts
open WeightedRow.Weights WeightedPublicCounts
variable {D B ι : Type} [DecidableEq D] [Fintype ι] [DecidableEq ι]

/-- Cached inputs inside an explicitly finite public index domain. -/
def seen (A : Finset D) (cache : D → Option B) : Finset D :=
  A.filter (fun q => (cache q).isSome)

def classCounts (A : Finset D) (cache : D → Option B) (decode : B → Option ι) : ι → ℕ :=
  counts (seen A cache) (fun q => (cache q).bind decode)

theorem not_seen_of_none (A : Finset D) (cache : D → Option B) (q : D)
    (hq : cache q = none) : q ∉ seen A cache := by simp [seen, hq]

theorem seen_update_of_mem (A : Finset D) (cache : D → Option B) (q : D) (u : B)
    (hq : q ∈ A) : seen A (Function.update cache q (some u)) = insert q (seen A cache) := by
  ext t
  by_cases ht : t = q
  · subst t; simp [seen, hq]
  · simp [seen, ht, Function.update_of_ne ht]

theorem seen_update_of_not_mem (A : Finset D) (cache : D → Option B) (q : D) (u : B)
    (hq : q ∉ A) : seen A (Function.update cache q (some u)) = seen A cache := by
  ext t
  by_cases ht : t = q
  · subst t; simp [seen, hq]
  · simp [seen, ht, Function.update_of_ne ht]

theorem decoded_update (cache : D → Option B) (decode : B → Option ι) (q : D) (u : B) :
    (fun t => (Function.update cache q (some u) t).bind decode) =
      Function.update (fun t => (cache t).bind decode) q (decode u) := by
  funext t
  by_cases ht : t = q
  · subst t; simp
  · simp [ht]

/-- A cache miss at a selected input is exactly a new decoded multiplicity. -/
theorem classCounts_update_of_mem (A : Finset D) (cache : D → Option B)
    (decode : B → Option ι) (q : D) (u : B) (hq : q ∈ A) (hfresh : cache q = none) :
    classCounts A (Function.update cache q (some u)) decode =
      advance (classCounts A cache decode) (decode u) := by
  unfold classCounts
  rw [seen_update_of_mem A cache q u hq, decoded_update]
  exact counts_insert_update _ _ q (not_seen_of_none A cache q hfresh) _

/-- Fresh queries outside the selected input domain preserve its multiplicities. -/
theorem classCounts_update_of_not_mem (A : Finset D) (cache : D → Option B)
    (decode : B → Option ι) (q : D) (u : B) (hq : q ∉ A) :
    classCounts A (Function.update cache q (some u)) decode = classCounts A cache decode := by
  unfold classCounts
  rw [seen_update_of_not_mem A cache q u hq, decoded_update]
  apply counts_update_absent
  intro h
  exact hq (Finset.mem_of_mem_filter q h)

theorem seen_card_update (A : Finset D) (cache : D → Option B) (q : D) (u : B)
    (hq : q ∈ A) (hfresh : cache q = none) :
    (seen A (Function.update cache q (some u))).card = (seen A cache).card+1 := by
  rw [seen_update_of_mem A cache q u hq,
    Finset.card_insert_of_notMem (not_seen_of_none A cache q hfresh)]

theorem seen_card_le (A : Finset D) (cache : D → Option B) : (seen A cache).card ≤ A.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

end WeightedCacheCounts
end
end

section

/-! An explicit first-hit/absorbing-state construction over adaptive kernels.
This proves a finite-time maximum without unioning over time prefixes. The
caller still supplies the actual oracle kernel and local exponential drift. -/

noncomputable section
open scoped Classical
namespace WeightedFirstHit
open WeightedKernel

variable {S : Type*}

inductive Status where
  | active
  | hit
  | killed
  deriving DecidableEq

/-- Frozen time and state preserve the exponential potential after stopping.
The hit status carries its event evidence, so no reachability assumption is
silently substituted for a theorem about all stopped states. -/
structure StoppedState (hit kill : ℕ → S → Prop) where
  clock : ℕ
  value : S
  status : Status
  valid : status = .hit → hit clock value
  safe : status = .active → ¬hit clock value ∧ ¬kill clock value

def classify (hit kill : ℕ → S → Prop) (t : ℕ) (s : S) : StoppedState hit kill :=
  if hh : hit t s then ⟨t, s, .hit, fun _ => hh, by simp⟩
  else if hk : kill t s then ⟨t, s, .killed, by simp, by simp⟩
  else ⟨t, s, .active, by simp, fun _ => ⟨hh, hk⟩⟩

@[simp] theorem classify_clock (hit kill : ℕ → S → Prop) (t : ℕ) (s : S) :
    (classify hit kill t s).clock = t := by
  unfold classify
  split_ifs <;> rfl

@[simp] theorem classify_value (hit kill : ℕ → S → Prop) (t : ℕ) (s : S) :
    (classify hit kill t s).value = s := by
  unfold classify
  split_ifs <;> rfl

@[simp] theorem classify_status_hit (hit kill : ℕ → S → Prop) (t : ℕ) (s : S)
    (hh : hit t s) : (classify hit kill t s).status = .hit := by simp [classify, hh]

@[simp] theorem classify_status_killed (hit kill : ℕ → S → Prop) (t : ℕ) (s : S)
    (hh : ¬hit t s) (hk : kill t s) : (classify hit kill t s).status = .killed := by
  simp [classify, hh, hk]

@[simp] theorem classify_status_active (hit kill : ℕ → S → Prop) (t : ℕ) (s : S)
    (hh : ¬hit t s) (hk : ¬kill t s) : (classify hit kill t s).status = .active := by
  simp [classify, hh, hk]

end WeightedFirstHit
end
end
