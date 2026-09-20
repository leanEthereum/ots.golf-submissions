import Mathlib

/- Original module: Submissions.UpperCompressions.ShallowCount; SHA256 a6142df965081e7f00f85e4f7be8aaa1fb9d6aeba757e8f71ae2adec0788bfcc. -/
section

/-!
# Counting positions for the exploratory shallow forest

`comp n s` is the number of tuples `(c_1, …, c_n) ∈ {0, …, 18}^n` with sum `s` (`card_comp`).

Concrete values are certified without `native_decide`: `comp` is evaluated through a
polynomial-size table of partial sums (`compTable`), which agrees with `comp` by induction
(`compTable_getD`) and is computed by kernel reduction.
-/

namespace OptimalOTS

namespace ShallowResearch

/-- Number of `(c : Fin n → Fin 19)` with `∑ i, (c i).val = s`. -/
def comp : ℕ → ℕ → ℕ
  | 0, s => if s = 0 then 1 else 0
  | n + 1, s => ∑ v ∈ Finset.range 19, if v ≤ s then comp n (s - v) else 0

theorem card_comp (n s : ℕ) :
    (Finset.univ.filter fun c : Fin n → Fin 19 => ∑ i, (c i).val = s).card = comp n s := by
  induction n generalizing s with
  | zero =>
    rw [comp]
    split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]
  | succ n ih =>
    rw [comp, ← Fin.sum_univ_eq_sum_range (fun v => if v ≤ s then comp n (s - v) else 0) 19]
    simp only [← ih]
    rw [Finset.card_filter, ← (Fin.consEquiv fun _ => Fin 19).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    split_ifs with hv
    · rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact if_congr (by omega) rfl rfl
    · refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      omega

/-! ### Kernel-checkable evaluation of `comp`

`comp` as written unfolds exponentially, so the concrete values are obtained from the row-by-row
dynamic programming table `compTable S n = [comp n 0, …, comp n S]`, which is computed by structural
recursion on lists and therefore reduces in the kernel in polynomial time. -/

/-- `compTable S n` is the list `[comp n 0, comp n 1, …, comp n S]`. -/
def compTable (S : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate S 0
  | n + 1 =>
    (List.range (S + 1)).map fun s =>
      ((List.range 19).map fun v => if v ≤ s then (compTable S n).getD (s - v) 0 else 0).sum

theorem sum_map_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ v ∈ Finset.range m, f v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

theorem compTable_getD (S n s : ℕ) (hs : s ≤ S) : (compTable S n).getD s 0 = comp n s := by
  induction n generalizing s with
  | zero =>
    rw [compTable, comp]
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_replicate,
        Nat.succ_ne_zero, if_false]
      split_ifs <;> rfl
  | succ n ih =>
    rw [compTable, comp, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some, sum_map_range]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · exact ih (s - v) (by omega)
    · rfl

/-- Exact coefficient for the 102-compression numerical candidate. -/
theorem comp_36_84 : comp 36 84 = 1588422833690542979003596657572 := by
  rw [← compTable_getD 84 36 84 le_rfl]
  decide +kernel

/-- Exact coefficient for 36 length-18 chains at total reconstruction cost 85. -/
theorem comp_36_85 : comp 36 85 = 2237827609476623676586919095944 := by
  rw [← compTable_getD 85 36 85 le_rfl]
  decide +kernel

/-- Number of choices: six of eighteen groups are disclosed, and the remaining
36 chains have total cost 85. Realizing these choices as a secure scheme is a
separate obligation; this file proves only the combinatorial count. -/
theorem single_shape_count :
    Nat.choose 18 6 * comp 36 85 =
      41543031742324041932159566097104416 := by
  rw [comp_36_85]
  decide +kernel

theorem single_shape_ge : 2 ^ 115 ≤ Nat.choose 18 6 * comp 36 85 := by
  rw [single_shape_count]
  norm_num

/-- The smaller cost layer admits the acceptance fraction 45 / 524288 when
indices are uniform 128-bit words. Availability and security are separate proofs. -/
theorem single_shape_102_count :
    Nat.choose 18 6 * comp 36 84 =
      29487481484631239862222768351166608 := by
  rw [comp_36_84]
  decide +kernel

theorem single_shape_102_ge : 45 * 2 ^ 109 ≤ Nat.choose 18 6 * comp 36 84 := by
  rw [single_shape_102_count]
  norm_num

#print axioms single_shape_ge
#print axioms single_shape_102_ge

end ShallowResearch

end OptimalOTS
end

/- Original module: Submissions.UpperCompressions.Count92; SHA256 fdb8fdee53b493adcf192882ac5247e50627a029418851bc256a56e4350a3fd0. -/
section

/-! Exact mixed72 class count and rank74 cut capacity. This is arithmetic for
an unproved weighted construction, not an admissibility or security export. -/
namespace OptimalOTS.WeightedResearch92
open ShallowResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def tierClasses (j : ℕ) : ℕ :=
  if j < 71 then 19 * 2 ^ (104-j) else if j = 71 then 91 * 2 ^ 33 else 0

def classes : ℕ := ∑ j ∈ Finset.range 72, tierClasses j
def acceptedAliases : ℕ := ∑ j ∈ Finset.range 72, tierClasses j * 2 ^ (j+1)

theorem classes_exact : classes = 770731564938763476110450815401984 := by
  decide +kernel

theorem aliases_exact : acceptedAliases = 45 * 2 ^ 110 := by
  decide +kernel

theorem row36 : compTable 76 36 = [1,36,666,8436,82251,658008,4496388,26978328,145008513,708930508,3190187286,13340783196,52251400851,192928249296,675248872536,2250829575120,7174519270695,21945588357420,64617565719070,183649923622584,505037289960909,1346766106541904,3489348548526084,8799226772348844,21631432465615167,51915437812458324,121801603507011954,279692568026003504,629308264282699149,1388818179893555496,3009105825002450160,6406482510816104340,13413569750053582950,27640073124131434680,56093057878466718396,112186019533969100412,221255480097237522482,430550415658610439192,827107866445940948862,1569378520206180891732,2942570331823825626210,5454484870541961587760,9999802454167283261910,18138972423171011777820,32567229708428410551738,57896234989709386484648,101945370364057577878038,177857047504597789011348,307533654960367530886758,527177933467646430672144,896156010781404704103942,1511071060381038101043792,2527950987009856504498662,4196985377626749242665152,6916543167030379911409746,11316623300211009184924752,18386956474180182575674182,29672434214856493510305372,47569459804045740237276522,75772711149244247504470824,119944823469469898626742238,188714656593605800704866868,295157330460382829410955178,458976975181272088280096448,709709303992678175027173563,1091396933579605285047406320,1669381310079376782728339220,2540122303120774647161827500,3845328815098000789598874645,5792200194804402778954401132,8682291625252691066932936512,12952497981352711317329172672,19232995069718270925816402327,28428811666219616937580398312,41834199218963804960625988326,61292342173830113592773276100,89417505832567661255943043350] := by decide +kernel

theorem coefficient_74 : comp 36 74 = 41834199218963804960625988326 := by
  rw [← compTable_getD 76 36 74 (by omega), row36]
  decide +kernel

theorem count_74 : Nat.choose 18 6 * comp 36 74 = 776610074300844075289060847283864 := by
  rw [coefficient_74]
  decide +kernel


theorem enough_classes92 : classes ≤ Nat.choose 18 6 * comp 36 74 := by
  rw [classes_exact, count_74]
  norm_num

theorem signature_bits : 42*129+86=5504 := rfl
theorem keygen_compressions : 54*18+18+5=995 := rfl
theorem verification_compressions : 74+12+5+1=92 := rfl

theorem acceptance_fraction : (acceptedAliases : ℚ) / 2^129 = 45/524288 := by
  rw [aliases_exact]
  norm_num

theorem finite_nonce_correction : (90 : ℚ) / 2^86 ≤ 1 / (100 * 2^20) := by
  norm_num

#print axioms enough_classes92
#print axioms aliases_exact
#print axioms acceptance_fraction
end OptimalOTS.WeightedResearch92
end

/- Original module: Submissions.UpperCompressions.Availability; SHA256 1164cc775158b2b3a3324dc6997b33c61732e612c874d776cb8dbcc3cbb790c6. -/
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

#print axioms empirical_failure
end WeightedAvailability
end

/- Original module: Submissions.UpperCompressions.ReplacementKernel; SHA256 69043ee39743a544b1027da73dd61e88fd09d8ee78e18aac633e0b87508873ad. -/
section

/-! Algebraic kernel for the iid-nonce, first-minimum weighted signer.
This module proves polynomial identities and bounds only. The finite random-sampling
law and the full OTS security argument remain separate obligations. -/

namespace WeightedReplacement

/-- The divided-difference polynomial, with no division or unequal-endpoint hypothesis. -/
def kernel (L : ℕ) (A B : ℝ) : ℝ :=
  ∑ k ∈ Finset.range L, A^k * B^(L-1-k)

@[simp] theorem kernel_zero (A B : ℝ) : kernel 0 A B = 0 := by simp [kernel]
@[simp] theorem kernel_one (A B : ℝ) : kernel 1 A B = 1 := by simp [kernel]

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

/-- Reversing time in the first-minimum position sum leaves the kernel unchanged. -/
theorem kernel_symm (L : ℕ) (A B : ℝ) : kernel L A B = kernel L B A := by
  exact geom_sum₂_comm A B L

/-- This is the sum of the first-minimum position probabilities after removing 1/N.
Earlier positions must have tier strictly above the winner, later positions may tie. -/
theorem first_minimum_sum (L : ℕ) (A B : ℝ) :
    (∑ t ∈ Finset.range L, B^t*A^(L-1-t)) = kernel L A B :=
  kernel_symm L B A

/-- Tier winning mass is its tier probability times the common kernel. -/
theorem tier_mass (L : ℕ) (A B Q : ℝ) (hQ : Q=A-B) :
    Q*kernel L A B = A^L-B^L := by rw [hQ]; exact sub_mul_kernel L A B

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

/-- Nonempty-tier division recovers the usual difference quotient exactly. -/
theorem kernel_eq_div (L : ℕ) {A B : ℝ} (hAB : A ≠ B) :
    kernel L A B = (A^L-B^L)/(A-B) := by
  apply (eq_div_iff (sub_ne_zero.mpr hAB)).2
  rw [mul_comm]
  exact sub_mul_kernel L A B

#print axioms kernel_mono
#print axioms kernel_scale
#print axioms sub_mul_kernel
#print axioms kernel_symm
#print axioms first_minimum_sum
#print axioms kernel_additive_envelope
#print axioms kernel_eq_div

end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementSampling; SHA256 077527aa68cb20196340759b7297a005835ef79c06b2a4959b943eea366297f4. -/
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

set_option maxHeartbeats 1000000 in
/-- Independent finite uniform sampling is exactly the uniform distribution on
all length-n vectors, with denominator N^n. The recursive definition does not hide
any random-sampling or independence premise. -/
theorem iidMean_eq_uniform_vectors {α : Type*} [Fintype α] (n : ℕ) (f : List α → ℝ) :
    iidMean n f = (∑ draws : Fin n → α, f (List.ofFn draws)) / (Fintype.card α : ℝ)^n := by
  classical
  induction n generalizing f with
  | zero => simp [iidMean]
  | succ n ih =>
    simp only [iidMean]
    simp_rw [ih]
    unfold uniformMean
    rw [← Finset.sum_div, div_div, ← pow_succ]
    congr 1
    calc
      (∑ a, ∑ draws : Fin n → α, f (a :: List.ofFn draws)) =
          ∑ p : α × (Fin n → α), f (p.1 :: List.ofFn p.2) :=
        (Fintype.sum_prod_type (fun p : α × (Fin n → α) => f (p.1 :: List.ofFn p.2))).symm
      _ = ∑ draws : Fin (n+1) → α, f (List.ofFn draws) := by
        have he := (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp
          (fun draws : Fin (n+1) → α => f (List.ofFn draws))
        change (∑ p : α × (Fin n → α), f (List.ofFn (Fin.cons p.1 p.2))) =
          ∑ draws : Fin (n+1) → α, f (List.ofFn draws) at he
        simpa only [List.ofFn_cons] using he

/-- Finite sample-space formulation of the exact first-minimum law. -/
theorem uniform_vectors_first_minimum_probability {α : Type*} [Fintype α]
    (v : α) (weak strict : α → Prop) (hv : ¬ strict v) (n : ℕ) :
    (∑ draws : Fin n → α,
      if FirstMinimumEvent v weak strict (List.ofFn draws) then (1 : ℝ) else 0) /
        (Fintype.card α : ℝ)^n =
      kernel n (fraction weak) (fraction strict) / Fintype.card α := by
  classical
  rw [← iidMean_eq_uniform_vectors n
    (fun xs => if FirstMinimumEvent v weak strict xs then (1 : ℝ) else 0)]
  exact iid_first_minimum_event_probability v weak strict hv n

#print axioms iidMean_allPass
#print axioms iid_first_minimum_probability
#print axioms iid_first_minimum_event_probability
#print axioms iidMean_eq_uniform_vectors
#print axioms uniform_vectors_first_minimum_probability

end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementPosterior; SHA256 d3b5b0c82b03acfc2672e7ac92bca9a89aeb6a503685823102ff27dcb77efe53. -/
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

/-- A constant target likelihood and a no-smaller likelihood throughout a
survival event bound the posterior by prior target mass / prior survival mass. -/
theorem finite_bayes_likelihood_bound {α : Type*} [Fintype α]
    (weight likelihood : α → ℝ) (target survival : α → Prop) (c : ℝ)
    (hw : ∀ a, 0 ≤ weight a) (hl : ∀ a, 0 ≤ likelihood a)
    (htarget : ∀ a, target a → likelihood a = c)
    (hsurvival : ∀ a, survival a → c ≤ likelihood a)
    (hmass : 0 < weightedMass weight survival)
    (hden : 0 < ∑ a, weight a * likelihood a) :
    (∑ a, if target a then weight a * likelihood a else 0) /
        (∑ a, weight a * likelihood a) ≤
      weightedMass weight target / weightedMass weight survival := by
  have hnum : (∑ a, if target a then weight a * likelihood a else 0) =
      weightedMass weight target * c := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ht : target a
    · simp [ht, htarget a ht]
    · simp [ht]
  have hlow : weightedMass weight survival * c ≤ ∑ a, weight a * likelihood a := by
    rw [weightedMass, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    by_cases hs : survival a
    · simp only [if_pos hs]
      exact mul_le_mul_of_nonneg_left (hsurvival a hs) (hw a)
    · simp only [if_neg hs, zero_mul]
      exact mul_nonneg (hw a) (hl a)
  rw [hnum]
  apply (div_le_div_iff₀ hden hmass).2
  calc
    (weightedMass weight target * c) * weightedMass weight survival =
        weightedMass weight target * (weightedMass weight survival * c) := by ring
    _ ≤ weightedMass weight target * (∑ a, weight a * likelihood a) :=
      mul_le_mul_of_nonneg_left hlow (weightedMass_nonneg weight target hw)

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

/-- Bayes posterior bound for one unknown coordinate, pointwise in all other
fixed table entries. The target event is any particular class in the signed tier.
There is no conditioning on a concentration/Good event. -/
theorem coordinate_posterior_bound {α : Type*} [Fintype α]
    (L : ℕ) (A B δ N : ℝ) (weight : α → ℝ) (target weak strict : α → Prop)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (hw : ∀ a, 0 ≤ weight a) (ht : ∀ a, target a → weak a ∧ ¬ strict a)
    (hmass : 0 < weightedMass weight weak)
    (hden : 0 < ∑ a, weight a * coordinateLikelihood L A B δ N weak strict a) :
    (∑ a, if target a then
        weight a * coordinateLikelihood L A B δ N weak strict a else 0) /
      (∑ a, weight a * coordinateLikelihood L A B δ N weak strict a) ≤
        weightedMass weight target / weightedMass weight weak := by
  apply finite_bayes_likelihood_bound weight _ target weak (kernel L (A+δ) B / N)
    hw (coordinateLikelihood_nonneg L A B δ N weak strict hA hB hδ hN)
  · intro a ha
    exact coordinateLikelihood_same L A B δ N weak strict a (ht a ha).1 (ht a ha).2
  · exact coordinateLikelihood_survival L A B δ N weak strict hA hB hδ hN
  · exact hmass
  · exact hden

#print axioms finite_bayes_likelihood_bound
#print axioms coordinateLikelihood_survival
#print axioms coordinate_posterior_bound

end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.BernsteinMGF; SHA256 c949a2f77c682b98587957a580669936759bc99db85ea2932c6ffea4958ea1e6. -/
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

#print axioms factorial_geometric
#print axioms exp_bernstein
#print axioms centered_mgf
#print axioms nonnegative_centered_mgf
#print axioms compensated_mgf

end WeightedMGF
end
end

/- Original module: Submissions.UpperCompressions.FiniteKernelConcentration; SHA256 168da6ca04563c82d6179781620bc64da7ab591126186777424d085a2828c951. -/
section

/-! Finite-horizon concentration algebra for explicit probability kernels.
A state may contain the complete adaptive transcript. A concrete random-oracle
experiment still has to provide these kernels and prove the step hypotheses. -/

noncomputable section
namespace WeightedKernel

variable {S : Type*}

/-- A sequence of normalized positive expectation functionals, one per state.
For finite S these can be ordinary finite probability sums. -/
abbrev Kernels (S : Type*) := ℕ → S → ((S → ℝ) →ₗ[ℝ] ℝ)

/-- Expected terminal payoff after n steps beginning at time t in state s. -/
def iterate (K : Kernels S) : ℕ → ℕ → S → ((S → ℝ) →ₗ[ℝ] ℝ)
  | 0, _, s => LinearMap.proj s
  | n+1, t, s => (K t s).comp (LinearMap.pi (fun s' => iterate K n (t+1) s'))

@[simp] theorem iterate_zero (K : Kernels S) (t : ℕ) (s : S) (f : S → ℝ) :
    iterate K 0 t s f = f s := rfl

@[simp] theorem iterate_succ (K : Kernels S) (n t : ℕ) (s : S) (f : S → ℝ) :
    iterate K (n+1) t s f = K t s (fun s' => iterate K n (t+1) s' f) := rfl

theorem iterate_mono (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (n t : ℕ) (s : S) (f g : S → ℝ) (hfg : ∀ s', f s' ≤ g s') :
    iterate K n t s f ≤ iterate K n t s g := by
  induction n generalizing t s with
  | zero => exact hfg s
  | succ n ih =>
    simp only [iterate_succ]
    exact hmono t s _ _ (fun s' => ih (t+1) s')

theorem iterate_one (K : Kernels S) (hnorm : ∀ t s, K t s (fun _ => 1) = 1)
    (n t : ℕ) (s : S) : iterate K n t s (fun _ => 1) = 1 := by
  induction n generalizing t s with
  | zero => rfl
  | succ n ih =>
    simp only [iterate_succ]
    have hf : (fun s' => iterate K n (t+1) s' (fun _ => 1)) = (fun _ => 1) := by
      funext s'; exact ih (t+1) s'
    rw [hf, hnorm]

/-- Local supermartingale inequalities telescope for arbitrary adaptive
state-dependent kernels. No independence of states or increments is assumed. -/
theorem iterate_supermartingale (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (Z : ℕ → S → ℝ) (hstep : ∀ t s, K t s (Z (t+1)) ≤ Z t s)
    (n t : ℕ) (s : S) : iterate K n t s (Z (t+n)) ≤ Z t s := by
  induction n generalizing t s with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ]
    have hx : K t s (fun s' => iterate K n (t+1) s' (Z (t+(n+1)))) ≤
        K t s (Z (t+1)) := by
      apply hmono t s
      intro s'
      simpa only [show t+(n+1) = (t+1)+n by omega] using ih (t+1) s'
    exact hx.trans (hstep t s)

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

/-- Terminal Bernstein/Freedman tail from the exponential potential bound.
The variance proxy W may be random; the event includes W ≤ v. -/
theorem freedman_tail
    (E : (S → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ s, f s ≤ g s) → E f ≤ E g)
    (bad : S → Prop) [DecidablePred bad]
    (Z W : S → ℝ) (a v J : ℝ) (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ : ∀ s, bad s → a ≤ Z s) (hW : ∀ s, bad s → W s ≤ v)
    (hmgf : ∀ θ, 0 < θ → θ*J < 3 →
      E (fun s => Real.exp (θ*Z s-θ^2*W s/(2*(1-θ*J/3)))) ≤ 1) :
    E (fun s => if bad s then 1 else 0) ≤ Real.exp (-a^2/(2*(v+J*a/3))) := by
  let θ := a/(v+J*a/3)
  obtain ⟨hθ, hθJ, heq⟩ := optimized_exponent a v J ha hv hJ
  change 0 < θ at hθ
  change θ*J < 3 at hθJ
  change θ*a-θ^2*v/(2*(1-θ*J/3)) = a^2/(2*(v+J*a/3)) at heq
  have hcoef : 0 ≤ θ^2/(2*(1-θ*J/3)) := by
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hbad (s : S) (hs : bad s) :
      a^2/(2*(v+J*a/3)) ≤ θ*Z s-θ^2*W s/(2*(1-θ*J/3)) := by
    have hz := mul_le_mul_of_nonneg_left (hZ s hs) hθ.le
    have hw := mul_le_mul_of_nonneg_left (hW s hs) hcoef
    calc
      _ = θ*a-θ^2*v/(2*(1-θ*J/3)) := heq.symm
      _ ≤ θ*Z s-(θ^2/(2*(1-θ*J/3)))*W s := by
        have heqv : θ^2*v/(2*(1-θ*J/3)) = (θ^2/(2*(1-θ*J/3)))*v := by ring
        rw [heqv]
        linarith
      _ = _ := by ring
  have hx := exponential_tail E hmono bad
    (fun s => θ*Z s-θ^2*W s/(2*(1-θ*J/3)))
    (a^2/(2*(v+J*a/3))) hbad (hmgf θ hθ hθJ)
  simpa only [neg_div] using hx

/-- Chaining state-dependent exponential drift gives a finite-horizon
Freedman tail. The caller supplies actual kernel drift, initialization, and the
terminal event interpretation. -/
theorem finite_kernel_freedman
    (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (Z W : ℕ → S → ℝ) (s₀ : S) (n : ℕ) (a v J : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ0 : Z 0 s₀ = 0) (hW0 : W 0 s₀ = 0)
    (hstep : ∀ θ, 0 < θ → θ*J < 3 → ∀ t s,
      K t s (fun s' => Real.exp (θ*Z (t+1) s'-θ^2*W (t+1) s'/(2*(1-θ*J/3)))) ≤
        Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))))
    (bad : S → Prop) [DecidablePred bad]
    (hZ : ∀ s, bad s → a ≤ Z n s) (hW : ∀ s, bad s → W n s ≤ v) :
    iterate K n 0 s₀ (fun s => if bad s then 1 else 0) ≤
      Real.exp (-a^2/(2*(v+J*a/3))) := by
  apply freedman_tail (iterate K n 0 s₀) (iterate_mono K hmono n 0 s₀)
    bad (Z n) (W n) a v J ha hv hJ hZ hW
  intro θ hθ hθJ
  have hx := iterate_supermartingale K hmono
    (fun t s => Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))))
    (hstep θ hθ hθJ) n 0 s₀
  simpa only [zero_add, hZ0, hW0, mul_zero, zero_div, sub_zero, Real.exp_zero] using hx

#print axioms iterate_mono
#print axioms iterate_one
#print axioms iterate_supermartingale
#print axioms exponential_step
#print axioms exponential_tail
#print axioms optimized_exponent
#print axioms freedman_tail
#print axioms finite_kernel_freedman

end WeightedKernel
end
end

/- Original module: Submissions.UpperCompressions.WeightedConstants; SHA256 80a9d9f1c6217d0af321351d2e3b85fd2f19ff46d24194e37ee88851a7e8b9b1. -/
section

/-! Symbolic constants for the mixed72 schedule, avoiding million-degree
rational evaluation. These lemmas concern the reference tier distribution. -/

noncomputable section
namespace WeightedConstants
attribute [local irreducible] Nat.choose
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def L : ℕ := 2^20
def q : ℝ := 19/(16*L)

theorem truncated_binomial (x : ℝ) (hx : 0 ≤ x) (n d : ℕ) (hd : d ≤ n+1) :
    (∑ i ∈ Finset.range d, x^i*(n.choose i : ℝ)) ≤ (1+x)^n := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hd)
    (f := fun i => x^i*(1:ℝ)^(n-i)*(n.choose i : ℝ))
    (by intro i hi hni; positivity)
  rw [← add_pow] at h
  simpa only [one_pow,mul_one,add_comm] using h

theorem reciprocal_lower : (200:ℝ)/61 ≤ (1+(19:ℝ)/16777197)^L := by
  have h := truncated_binomial ((19:ℝ)/16777197) (by norm_num) L 8 (by norm_num [L])
  have hb : (200:ℝ)/61 ≤ ∑ i ∈ Finset.range 8, ((19:ℝ)/16777197)^i*(L.choose i : ℝ) := by
    norm_num [L,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial_succ,Nat.factorial_succ]
  exact hb.trans h

theorem first_survival : (1-q)^L ≤ (61:ℝ)/200 := by
  have hnonneg : 0 ≤ (1-q)^L := by apply pow_nonneg; norm_num [q,L]
  have hid : (1-q)^L*(1+(19:ℝ)/16777197)^L = 1 := by
    rw [← mul_pow]
    have hb : (1-q)*(1+(19:ℝ)/16777197) = 1 := by norm_num [q,L]
    rw [hb,one_pow]
  have h := mul_le_mul_of_nonneg_left reciprocal_lower hnonneg
  rw [hid] at h
  linarith

theorem penultimate_reciprocal_lower : (3:ℝ) ≤ (1+(19:ℝ)/16777197)^(L-1) := by
  have h := truncated_binomial ((19:ℝ)/16777197) (by norm_num) (L-1) 4 (by norm_num [L])
  have hb : (3:ℝ) ≤ ∑ i ∈ Finset.range 4,
      ((19:ℝ)/16777197)^i*((L-1).choose i : ℝ) := by
    norm_num [L,Finset.sum_range_succ,Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial_succ,Nat.factorial_succ]
  exact hb.trans h

theorem penultimate_survival : (1-q)^(L-1) ≤ (1:ℝ)/3 := by
  have hnonneg : 0 ≤ (1-q)^(L-1) := by apply pow_nonneg; norm_num [q,L]
  have hid : (1-q)^(L-1)*(1+(19:ℝ)/16777197)^(L-1) = 1 := by
    rw [← mul_pow]
    have hb : (1-q)*(1+(19:ℝ)/16777197) = 1 := by norm_num [q,L]
    rw [hb,one_pow]
  have h := mul_le_mul_of_nonneg_left penultimate_reciprocal_lower hnonneg
  rw [hid] at h
  linarith

theorem prefix_power (t : ℕ) (r : ℝ) (hb : (1-q)^t ≤ r)
    (j : ℕ) (hj : j ≤ 71) : (1-(j:ℝ)*q)^t ≤ r^j := by
  have hjr : (j:ℝ) ≤ 71 := by exact_mod_cast hj
  have hq0 : 0 ≤ q := by norm_num [q,L]
  have hq1 : q ≤ 1 := by norm_num [q,L]
  have hbase : 0 ≤ 1-(j:ℝ)*q := by
    have hp := mul_le_mul_of_nonneg_right hjr hq0
    have hh : (71:ℝ)*q ≤ 1 := by norm_num [q,L]
    linarith
  have hbern : 1-(j:ℝ)*q ≤ (1-q)^j := by
    have h := one_add_mul_le_pow (show (-2:ℝ) ≤ -q by linarith) j
    simpa only [sub_eq_add_neg,mul_neg] using h
  calc
    _ ≤ ((1-q)^j)^t := pow_le_pow_left₀ hbase hbern t
    _ = ((1-q)^t)^j := by rw [← pow_mul,← pow_mul,Nat.mul_comm j t]
    _ ≤ r^j := pow_le_pow_left₀ (pow_nonneg (by linarith) _) hb j

theorem weighted_telescope (u : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, (2:ℝ)^j*(u j-u (j+1))) =
      u 0+(∑ j ∈ Finset.range k, (2:ℝ)^j*u (j+1))-(2:ℝ)^k*u k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.sum_range_succ,ih,pow_succ]
    ring

theorem geometric_identity (x : ℝ) (k : ℕ) :
    (1-x)*(∑ j ∈ Finset.range k, x^j) = 1-x^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,mul_add,ih,pow_succ]
    ring

theorem geometric_upper (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k, x^j) ≤ 1/(1-x) := by
  apply (le_div_iff₀ (by linarith)).2
  rw [mul_comm,geometric_identity]
  exact sub_le_self _ (pow_nonneg hx k)

/-- The last tier may contain more aliases; only its failure tail is dropped.
No equal-mass assumption is imposed on that last tier. -/
theorem weighted_mean_bound (u : ℕ → ℝ) (tail : ℝ) (ht : 0 ≤ tail)
    (h0 : u 0 ≤ 1) (hu : ∀ j, j ≤ 71 → u j ≤ ((61:ℝ)/200)^j) :
    (1:ℝ)/2*((∑ j ∈ Finset.range 71, (2:ℝ)^j*(u j-u (j+1)))+
      (2:ℝ)^71*(u 71-tail)) ≤ 139/156 := by
  rw [weighted_telescope]
  have hs : (∑ j ∈ Finset.range 71, (2:ℝ)^j*u (j+1)) ≤
      (61:ℝ)/200*(∑ j ∈ Finset.range 71, ((61:ℝ)/100)^j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hp := mul_le_mul_of_nonneg_left (hu (j+1) (by have := Finset.mem_range.mp hj; omega))
      (show (0:ℝ) ≤ 2^j by positivity)
    calc
      _ ≤ 2^j*((61:ℝ)/200)^(j+1) := hp
      _ = (61:ℝ)/200*((61:ℝ)/100)^j := by
        rw [pow_succ]
        have hh : (2:ℝ)*((61:ℝ)/200) = (61:ℝ)/100 := by norm_num
        rw [← hh,mul_pow]
        ring
  have hg := geometric_upper ((61:ℝ)/100) (by norm_num) (by norm_num) 71
  have htail : (0:ℝ) ≤ 2^71*tail := by positivity
  nlinarith

def referenceMean (failure : ℝ) : ℝ :=
  (1:ℝ)/2*((∑ j ∈ Finset.range 71,
    (2:ℝ)^j*((1-(j:ℝ)*q)^L-(1-((j+1:ℕ):ℝ)*q)^L))+
      (2:ℝ)^71*((1-(71:ℝ)*q)^L-failure))

theorem referenceMean_le (failure : ℝ) (hf : 0 ≤ failure) :
    referenceMean failure ≤ (223:ℝ)/250 := by
  have h := weighted_mean_bound (fun j => (1-(j:ℝ)*q)^L) failure hf (by simp)
    (fun j hj => prefix_power L ((61:ℝ)/200) first_survival j hj)
  exact h.trans (by norm_num)

theorem relative_peak_bound (j : ℕ) (hj : j ≤ 71) :
    (2:ℝ)^j*(1-(j:ℝ)*q)^(L-1) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left
    (prefix_power (L-1) ((1:ℝ)/3) penultimate_survival j hj)
    (show (0:ℝ) ≤ 2^j by positivity)
  calc
    _ ≤ (2:ℝ)^j*((1:ℝ)/3)^j := h
    _ = ((2:ℝ)/3)^j := by rw [← mul_pow]; congr 1; norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem small_total_margin :
    (99:ℝ)/98*(223/250)*(11/10)+2/1000 = 243337/245000 ∧
      (243337:ℝ)/245000 < 1 := by norm_num

#print axioms first_survival
#print axioms penultimate_survival
#print axioms referenceMean_le
#print axioms relative_peak_bound
end WeightedConstants
end
end

/- Original module: Submissions.UpperCompressions.WeightedReference; SHA256 6b30143f0072065fe8bbaf00d7453fad2f0e29f1c4fb67bcbe86d1f5f906f201. -/
section

/-! Reference probabilities and symbolic security constants for mixed72.
These are arithmetic lemmas, not a forgery-game theorem. -/
noncomputable section
namespace WeightedReference
open WeightedConstants WeightedReplacement
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def kappa : ℝ := 1/2^127
def acceptance : ℝ := 45/524288
def survival (j : ℕ) : ℝ := 1-(j:ℝ)*q
def lower (j : ℕ) : ℝ := if j < 71 then survival (j+1) else 1-acceptance
def mass (j : ℕ) : ℝ := survival j-lower j
def probability (j : ℕ) : ℝ := kappa/2*2^j
def weight (j : ℕ) : ℝ := probability j*kernel L (survival j) (lower j)
def failure : ℝ := (1-acceptance)^L

theorem survival_nonneg (j : ℕ) (hj : j ≤ 71) : 0 ≤ survival j := by
  have hjr : (j:ℝ) ≤ 71 := by exact_mod_cast hj
  have hh := mul_le_mul_of_nonneg_right hjr (show 0 ≤ q by norm_num [q,L])
  have hn : (71:ℝ)*q ≤ 1 := by norm_num [q,L]
  unfold survival
  linarith

theorem lower_nonneg (j : ℕ) (hj : j ≤ 71) : 0 ≤ lower j := by
  unfold lower
  split_ifs with h
  · exact survival_nonneg _ (by omega)
  · norm_num [acceptance]

theorem lower_le_survival (j : ℕ) (hj : j ≤ 71) : lower j ≤ survival j := by
  unfold lower
  split_ifs with h
  · have hq : 0 ≤ q := by norm_num [q,L]
    simp only [survival,Nat.cast_add,Nat.cast_one]
    nlinarith
  · have he : j=71 := by omega
    subst j
    norm_num [survival,acceptance,q,L]

theorem kernel_diagonal (n : ℕ) (A : ℝ) : kernel n A A = (n:ℝ)*A^(n-1) := by
  unfold kernel
  have hterm : ∀ k ∈ Finset.range n, A^k*A^(n-1-k) = A^(n-1) := by
    intro k hk
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.mp hk
    omega
  simp only [Finset.sum_congr rfl hterm,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem weight_nonneg (j : ℕ) (hj : j ≤ 71) : 0 ≤ weight j := by
  exact mul_nonneg (by unfold probability kappa; positivity)
    (kernel_nonneg L (survival_nonneg j hj) (lower_nonneg j hj))

theorem weight_le (j : ℕ) (hj : j ≤ 71) : weight j ≤ (L:ℝ)*kappa/2 := by
  have hm := kernel_mono L (survival_nonneg j hj) (lower_nonneg j hj)
    (le_refl (survival j)) (lower_le_survival j hj)
  rw [kernel_diagonal] at hm
  have hp : 0 ≤ probability j := by unfold probability kappa; positivity
  have h := mul_le_mul_of_nonneg_left hm hp
  have ht := relative_peak_bound j hj
  have hk : 0 ≤ (L:ℝ)*kappa/2 := by unfold kappa; positivity
  have ht' := mul_le_mul_of_nonneg_left ht hk
  unfold weight
  calc
    _ ≤ probability j*((L:ℝ)*survival j^(L-1)) := h
    _ = ((L:ℝ)*kappa/2)*(2^j*(1-(j:ℝ)*q)^(L-1)) := by unfold probability survival; ring
    _ ≤ (L:ℝ)*kappa/2 := by simpa only [mul_one] using ht'

theorem failure_nonneg : 0 ≤ failure := by unfold failure acceptance; positivity

theorem failure_le : failure ≤ (1:ℝ)/1000 := by
  have hm : 1-acceptance ≤ survival 71 := by norm_num [acceptance,survival,q,L]
  have h := pow_le_pow_left₀ (show 0 ≤ 1-acceptance by norm_num [acceptance]) hm L
  have hp := prefix_power L ((61:ℝ)/200) first_survival 71 (by omega)
  exact (h.trans hp).trans (by norm_num)

theorem mass_weight (j : ℕ) :
    mass j*weight j = kappa/2*(2^j*(survival j^L-lower j^L)) := by
  have h := sub_mul_kernel L (survival j) (lower j)
  unfold mass weight probability
  calc
    _ = kappa/2*2^j*((survival j-lower j)*kernel L (survival j) (lower j)) := by ring
    _ = _ := by rw [h]; ring

theorem reference_mean_identity :
    (∑ j ∈ Finset.range 72, mass j*weight j) = kappa*referenceMean failure := by
  rw [show 72=71+1 by omega,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range 71, mass j*weight j) =
      kappa/2*(∑ j ∈ Finset.range 71,2^j*(survival j^L-survival (j+1)^L)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mass_weight,lower,if_pos (Finset.mem_range.mp hj)]
  rw [hs,mass_weight]
  simp only [lower,show ¬71<71 by omega,if_false]
  unfold referenceMean failure survival
  ring

theorem reference_mean_le :
    (∑ j ∈ Finset.range 72,mass j*weight j) ≤ kappa*(223/250) := by
  rw [reference_mean_identity]
  exact mul_le_mul_of_nonneg_left (referenceMean_le failure failure_nonneg)
    (by unfold kappa; positivity)

theorem telescope (u : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,(u j-u (j+1))) = u 0-u n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

theorem total_mass : (∑ j ∈ Finset.range 72,mass j) = acceptance := by
  rw [show 72=71+1 by omega,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range 71,mass j) = survival 0-survival 71 := by
    rw [← telescope survival 71]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [mass,lower,if_pos (Finset.mem_range.mp hj)]
  rw [hs]
  norm_num [mass,lower,survival]

theorem total_winner_mass :
    (∑ j ∈ Finset.range 72,mass j*kernel L (survival j) (lower j)) = 1-failure := by
  rw [show 72=71+1 by omega,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range 71,mass j*kernel L (survival j) (lower j)) =
      survival 0^L-survival 71^L := by
    rw [← telescope (fun j => survival j^L) 71]
    apply Finset.sum_congr rfl
    intro j hj
    unfold mass
    rw [sub_mul_kernel,lower,if_pos (Finset.mem_range.mp hj)]
  rw [hs]
  unfold mass
  rw [sub_mul_kernel]
  simp only [lower,show ¬71<71 by omega,if_false]
  unfold failure
  have h0 : survival 0=1 := by simp [survival]
  rw [h0,one_pow]
  ring

theorem post_excess_le {h f : ℝ} (hh : h ≤ kappa*(223/250))
    (hf : f ≤ 1/1000) : h/(1-acceptance)-kappa/2*(1-f) ≤ kappa*(2/5) := by
  have hd : 0 < 1-acceptance := by norm_num [acceptance]
  have h1 := div_le_div_of_nonneg_right hh hd.le
  have hk : 0 ≤ kappa := by unfold kappa; positivity
  have h2 := mul_le_mul_of_nonneg_left hf (div_nonneg hk (by norm_num : (0:ℝ) ≤ 2))
  have hn : (kappa*(223/250))/(1-acceptance)-kappa/2*(1-1/1000) ≤ kappa*(2/5) := by
    norm_num [kappa,acceptance]
  linarith

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

theorem common_envelope :
    (1+(1/(100*(L:ℝ)))/(1-acceptance))^(L-1) ≤ (99:ℝ)/98 := by
  let x : ℝ := (1/(100*(L:ℝ)))/(1-acceptance)
  have hx : 0 ≤ x := by norm_num [x,L,acceptance]
  have h := pow_times_linear_le_one x hx (L-1)
  have hd : 0 < 1-((L-1:ℕ):ℝ)*x := by norm_num [x,L,acceptance]
  have hb : 1/(1-((L-1:ℕ):ℝ)*x) ≤ (99:ℝ)/98 := by norm_num [x,L,acceptance]
  exact ((le_div_iff₀ hd).2 h).trans hb

#print axioms weight_le
#print axioms reference_mean_le
#print axioms post_excess_le
#print axioms common_envelope
end WeightedReference
end
end

/- Original module: Submissions.UpperCompressions.ClippedDrift; SHA256 11fafc1385b7799976f278b952d40ee0148ed78bd3761531e1d49db97b366a01. -/
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

#print axioms drift_outside
#print axioms drift_inside
#print axioms drift_outside_le
#print axioms drift_inside_le
#print axioms expect_one
#print axioms positiveOutside_bounds
#print axioms positiveInside_bounds
#print axioms centered_variance_le
#print axioms centered_abs_le
#print axioms center_predictable_shift

end Weights
end WeightedRow
end
end

/- Original module: Submissions.UpperCompressions.WeightedMoments; SHA256 2d9dacb0c1c04a0d427e4091822ebab215ac335b64c7f82e4d612b2894d4cd20. -/
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

/-- Direct fresh-query expected score increment. -/
theorem score_drift (k : ι → ℕ) :
    w.expect (fun x => w.score (advance k x)-w.score k) = w.mean := by
  simp only [score_advance, add_sub_cancel_left]
  exact w.mean_scoreJump

/-- Direct fresh-query expected pair-energy increment. -/
theorem pair_drift (k : ι → ℕ) :
    w.expect (fun x => w.pairScore (advance k x)-w.pairScore k) = w.score k := by
  simp only [pairScore_advance, add_sub_cancel_left]
  exact w.mean_pairJump k

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

#print axioms score_bump
#print axioms pairScore_bump
#print axioms score_drift
#print axioms pair_drift
#print axioms score_variance_le
#print axioms M1_mean_next
#print axioms M2_mean_next
#print axioms M1_square_next_le
#print axioms M1_compensated_square_next_le
#print axioms uniform_decoder_expect
#print axioms M1_step_mean
#print axioms M2_step_mean
#print axioms M1_step_square_compensated

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

/-- Repeating a public query with the same cached answer changes no count. -/
theorem counts_cached (A : Finset Q) (answers : Q → Option ι) (q : Q) (hq : q ∈ A) :
    counts (insert q A) answers = counts A answers := by rw [Finset.insert_eq_of_mem hq]

#print axioms counts_insert_update
#print axioms counts_cached
end WeightedPublicCounts
end
end

/- Original module: Submissions.UpperCompressions.FiniteCacheCounts; SHA256 dcd6df82ab26b4356af7b8014b4a1ded5c1afb1a98369536372427631377e68b. -/
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

#print axioms classCounts_update_of_mem
#print axioms classCounts_update_of_not_mem
#print axioms seen_card_update
#print axioms seen_card_le
end WeightedCacheCounts
end
end

/- Original module: Submissions.UpperCompressions.FirstHitFreedman; SHA256 1b842ae043498009825189176a13d630e553b7ea5b58116699e2547cb87ad21f. -/
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

/-- Active states take one original transition and classify the result; stopped
states take a deterministic self-loop, freezing their clock and potential. -/
def stoppedKernel (K : Kernels S) (hit kill : ℕ → S → Prop) : Kernels (StoppedState hit kill) :=
  fun _ st => if st.status = .active then
    (K st.clock st.value).comp
      (LinearMap.pi (fun s' => LinearMap.proj (classify hit kill (st.clock+1) s')))
    else LinearMap.proj st

@[simp] theorem stoppedKernel_apply (K : Kernels S) (hit kill : ℕ → S → Prop)
    (t : ℕ) (st : StoppedState hit kill) (f : StoppedState hit kill → ℝ) :
    stoppedKernel K hit kill t st f =
      if st.status = .active then
        K st.clock st.value (fun s' => f (classify hit kill (st.clock+1) s'))
      else f st := by
  unfold stoppedKernel
  split_ifs <;> rfl

theorem stoppedKernel_mono (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (hit kill : ℕ → S → Prop) (t : ℕ) (st : StoppedState hit kill)
    (f g : StoppedState hit kill → ℝ) (hfg : ∀ s', f s' ≤ g s') :
    stoppedKernel K hit kill t st f ≤ stoppedKernel K hit kill t st g := by
  simp only [stoppedKernel_apply]
  split_ifs
  · exact hmono _ _ _ _ (fun s' => hfg _)
  · exact hfg st

theorem stoppedKernel_one (K : Kernels S)
    (hnorm : ∀ t s, K t s (fun _ => 1) = 1)
    (hit kill : ℕ → S → Prop) (t : ℕ) (st : StoppedState hit kill) :
    stoppedKernel K hit kill t st (fun _ => 1) = 1 := by
  simp only [stoppedKernel_apply]
  split_ifs
  · exact hnorm _ _
  · rfl

def hitIndicator (hit kill : ℕ → S → Prop) (st : StoppedState hit kill) : ℝ :=
  if st.status = .hit then 1 else 0

/-- Direct recursive event probability: hit has priority over kill. For the
usual variance/good-event stopping, the predicates should be chosen disjoint. -/
def firstHit (K : Kernels S) (hit kill : ℕ → S → Prop) : ℕ → ℕ → S → ℝ
  | 0, t, s => if hit t s then 1 else 0
  | n+1, t, s => if hit t s then 1 else if kill t s then 0
      else K t s (fun s' => firstHit K hit kill n (t+1) s')

theorem iterate_stopped (K : Kernels S) (hit kill : ℕ → S → Prop)
    (st : StoppedState hit kill) (hstop : st.status ≠ .active)
    (n t : ℕ) (f : StoppedState hit kill → ℝ) :
    iterate (stoppedKernel K hit kill) n t st f = f st := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ, stoppedKernel_apply, if_neg hstop]
    exact ih (t+1)

/-- Exact equality between the absorbing construction and the first-hit-before-
kill event, including the initial time and every time through the horizon. -/
theorem iterate_hit_eq (K : Kernels S) (hit kill : ℕ → S → Prop)
    (n t u : ℕ) (s : S) :
    iterate (stoppedKernel K hit kill) n u (classify hit kill t s) (hitIndicator hit kill) =
      firstHit K hit kill n t s := by
  induction n generalizing t u s with
  | zero =>
    simp only [iterate_zero, firstHit, hitIndicator]
    by_cases hh : hit t s
    · simp [hh]
    · by_cases hk : kill t s <;> simp [classify, hh, hk]
  | succ n ih =>
    by_cases hh : hit t s
    · rw [iterate_stopped K hit kill _ (by simp [hh])]
      simp [firstHit, hitIndicator, hh]
    · by_cases hk : kill t s
      · rw [iterate_stopped K hit kill _ (by simp [hh, hk])]
        simp [firstHit, hitIndicator, hh, hk]
      · simp only [iterate_succ, stoppedKernel_apply, classify_status_active _ _ _ _ hh hk,
          if_true, classify_clock, classify_value, firstHit, if_neg hh, if_neg hk]
        congr 1
        funext s'
        exact ih (t+1) (u+1) s'

/-- Original exponential drift is preserved by the absorbing construction.
Both score and variance proxy use the stored stopping time. -/
theorem stopped_exponential_drift
    (K : Kernels S) (hit kill : ℕ → S → Prop)
    (Z W : ℕ → S → ℝ) (θ J : ℝ)
    (hstep : ∀ t s, ¬hit t s → ¬kill t s →
      K t s (fun s' => Real.exp (θ*Z (t+1) s'-θ^2*W (t+1) s'/(2*(1-θ*J/3)))) ≤
        Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))))
    (t : ℕ) (st : StoppedState hit kill) :
    stoppedKernel K hit kill t st
      (fun st' => Real.exp (θ*Z st'.clock st'.value-θ^2*W st'.clock st'.value/(2*(1-θ*J/3)))) ≤
      Real.exp (θ*Z st.clock st.value-θ^2*W st.clock st.value/(2*(1-θ*J/3))) := by
  simp only [stoppedKernel_apply]
  split_ifs with hs
  · simpa only [classify_clock, classify_value] using
      hstep st.clock st.value (st.safe hs).1 (st.safe hs).2
  · exact le_rfl

/-- Maximal Freedman bound for a hit before an arbitrary killing condition.
There is no factor for the number of time prefixes. A hit can include W≤v;
killing can include W>v or failure of the stopped cache-good predicate. -/
theorem firstHit_freedman
    (K : Kernels S)
    (hmono : ∀ t s f g, (∀ s', f s' ≤ g s') → K t s f ≤ K t s g)
    (Z W : ℕ → S → ℝ) (s₀ : S) (n : ℕ) (a v J : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ0 : Z 0 s₀ = 0) (hW0 : W 0 s₀ = 0)
    (hit kill : ℕ → S → Prop)
    (hstep : ∀ θ, 0 < θ → θ*J < 3 → ∀ t s, ¬hit t s → ¬kill t s →
      K t s (fun s' => Real.exp (θ*Z (t+1) s'-θ^2*W (t+1) s'/(2*(1-θ*J/3)))) ≤
        Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))))
    (hZ : ∀ t s, hit t s → a ≤ Z t s) (hW : ∀ t s, hit t s → W t s ≤ v) :
    firstHit K hit kill n 0 s₀ ≤ Real.exp (-a^2/(2*(v+J*a/3))) := by
  let Ks := stoppedKernel K hit kill
  let Zs : ℕ → StoppedState hit kill → ℝ := fun _ st => Z st.clock st.value
  let Ws : ℕ → StoppedState hit kill → ℝ := fun _ st => W st.clock st.value
  have hz0 : Zs 0 (classify hit kill 0 s₀) = 0 := by simpa [Zs] using hZ0
  have hw0 : Ws 0 (classify hit kill 0 s₀) = 0 := by simpa [Ws] using hW0
  have hstepS : ∀ θ, 0 < θ → θ*J < 3 → ∀ t st,
      Ks t st (fun st' => Real.exp (θ*Zs (t+1) st'-θ^2*Ws (t+1) st'/(2*(1-θ*J/3)))) ≤
        Real.exp (θ*Zs t st-θ^2*Ws t st/(2*(1-θ*J/3))) := by
    intro θ hθ hθJ t st
    exact stopped_exponential_drift K hit kill Z W θ J (hstep θ hθ hθJ) t st
  have hx := finite_kernel_freedman Ks (stoppedKernel_mono K hmono hit kill)
    Zs Ws (classify hit kill 0 s₀) n a v J ha hv hJ hz0 hw0 hstepS
    (fun st => st.status = .hit)
    (fun st hs => hZ st.clock st.value (st.valid hs))
    (fun st hs => hW st.clock st.value (st.valid hs))
  change iterate (stoppedKernel K hit kill) n 0 (classify hit kill 0 s₀)
    (hitIndicator hit kill) ≤ _ at hx
  rw [iterate_hit_eq] at hx
  exact hx

#print axioms stoppedKernel_mono
#print axioms stoppedKernel_one
#print axioms iterate_stopped
#print axioms iterate_hit_eq
#print axioms stopped_exponential_drift
#print axioms firstHit_freedman

end WeightedFirstHit
end
end

