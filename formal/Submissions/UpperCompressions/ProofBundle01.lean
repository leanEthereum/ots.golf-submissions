import Submissions.UpperCompressions.ProofBundle00
import Mathlib

/- Original module: Submissions.UpperCompressions.WeightedScoreMGF; SHA256 83096b6d8c04aa7430bd05e7e55fce37d34560bace5f796a8eb8d0c94c2ab0a7. -/
section

noncomputable section
open scoped Classical BigOperators
namespace WeightedEmpirical
open WeightedRow.Weights
set_option maxHeartbeats 800000
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive normalized expectation for the decoder's class distribution. -/
def expectLinear (w : WeightedRow.Weights ι) : (Option ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := w.expect
  map_add' := w.expect_add
  map_smul' c f := w.expect_smul c f

/-- The per-fresh-query Bernstein compensator for a score bounded by G. -/
def rate (w : WeightedRow.Weights ι) (θ G : ℝ) : ℝ :=
  θ^2*(G*w.mean)/(2*(1-θ*G/3))

/-- Exponential drift including cached queries and private randomness. -/
theorem score_step_mgf (w : WeightedRow.Weights ι) (G θ : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G < 3)
    (fresh : Bool) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => Real.exp (θ*w.M1 (step fresh q k x).1 (step fresh q k x).2-
      rate w θ G*((step fresh q k x).1:ℝ))) ≤
      Real.exp (θ*w.M1 q k-rate w θ G*(q:ℝ)) := by
  cases fresh with
  | false => simp only [step_not_fresh, expect_const, le_refl]
  | true =>
    have hnorm : expectLinear w (fun _ => 1) = 1 := w.expect_const 1
    have hm : expectLinear w (fun x => w.scoreJump x-w.mean) = 0 := by
      change w.expect (fun x => w.scoreJump x-w.mean) = 0
      rw [expect_sub, mean_scoreJump, expect_const, sub_self]
    have hb : ∀ x, |w.scoreJump x-w.mean| ≤ G := by
      intro x
      have hh := w.centered_abs_le w.scoreJump G (w.scoreJump_bounds G hG hg) x
      simpa only [mean_scoreJump] using hh
    have hs : expectLinear w (fun x => (w.scoreJump x-w.mean)^2) ≤ G*w.mean :=
      w.score_variance_le G hG hg
    have hx := WeightedMGF.compensated_mgf (expectLinear w) w.expect_mono hnorm
      (fun x => w.scoreJump x-w.mean) θ G (G*w.mean) hθ hG hθG hb hm hs
    change w.expect (fun x => Real.exp (θ*(w.scoreJump x-w.mean)-rate w θ G)) ≤ 1 at hx
    have hf : (fun x => Real.exp (θ*w.M1 (step true q k x).1 (step true q k x).2-
        rate w θ G*((step true q k x).1:ℝ))) =
      (fun x => Real.exp (θ*w.M1 q k-rate w θ G*(q:ℝ))*
        Real.exp (θ*(w.scoreJump x-w.mean)-rate w θ G)) := by
      funext x
      simp only [step, ite_true, M1_increment, Nat.cast_add, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hf, expect_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx
      (Real.exp_nonneg (θ*w.M1 q k-rate w θ G*(q:ℝ)))

#print axioms score_step_mgf
end WeightedEmpirical
end
end

/- Original module: Submissions.UpperCompressions.WeightedLowerMGF; SHA256 0514182599438e70315dbeb5a47c3924ea60a02d458043c9bb77658d99ab778d. -/
section
noncomputable section
open scoped Classical BigOperators
namespace WeightedEmpirical
open WeightedRow.Weights
set_option maxHeartbeats 800000
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem lower_score_step_mgf (w : WeightedRow.Weights ι) (G θ : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G < 3)
    (fresh : Bool) (q : ℕ) (k : ι → ℕ) :
    w.expect (fun x => Real.exp (θ*(-w.M1 (step fresh q k x).1 (step fresh q k x).2)-
      rate w θ G*((step fresh q k x).1:ℝ))) ≤
      Real.exp (θ*(-w.M1 q k)-rate w θ G*(q:ℝ)) := by
  cases fresh with
  | false => simp only [step_not_fresh, expect_const, le_refl]
  | true =>
    have hnorm : expectLinear w (fun _ => 1) = 1 := w.expect_const 1
    have hm : expectLinear w (fun x => w.mean-w.scoreJump x) = 0 := by
      change w.expect (fun x => w.mean-w.scoreJump x) = 0
      rw [expect_sub, mean_scoreJump, expect_const, sub_self]
    have hb : ∀ x, |w.mean-w.scoreJump x| ≤ G := by
      intro x
      have hh := w.centered_abs_le w.scoreJump G (w.scoreJump_bounds G hG hg) x
      simpa only [mean_scoreJump, abs_sub_comm] using hh
    have hs : expectLinear w (fun x => (w.mean-w.scoreJump x)^2) ≤ G*w.mean := by
      have he : (fun x => (w.mean-w.scoreJump x)^2) =
          (fun x => (w.scoreJump x-w.mean)^2) := by funext x; ring
      rw [he]
      exact w.score_variance_le G hG hg
    have hx := WeightedMGF.compensated_mgf (expectLinear w) w.expect_mono hnorm
      (fun x => w.mean-w.scoreJump x) θ G (G*w.mean) hθ hG hθG hb hm hs
    change w.expect (fun x => Real.exp (θ*(w.mean-w.scoreJump x)-rate w θ G)) ≤ 1 at hx
    have hf : (fun x => Real.exp (θ*(-w.M1 (step true q k x).1 (step true q k x).2)-
        rate w θ G*((step true q k x).1:ℝ))) =
      (fun x => Real.exp (θ*(-w.M1 q k)-rate w θ G*(q:ℝ))*
        Real.exp (θ*(w.mean-w.scoreJump x)-rate w θ G)) := by
      funext x
      simp only [step, ite_true, M1_increment, Nat.cast_add, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hf, expect_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx
      (Real.exp_nonneg (θ*(-w.M1 q k)-rate w θ G*(q:ℝ)))

#print axioms lower_score_step_mgf
end WeightedEmpirical
end
end

/- Original module: Submissions.UpperCompressions.LinearBoundaryConstants; SHA256 ca2ac1bfdf7f4f9567f3e77f89f195eab94c002eb20ce8ccb4ecf45f3b1d7c8a. -/
section
noncomputable section
open scoped BigOperators
namespace WeightedEmpirical
open WeightedRow.Weights
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A convenient conservative sufficient condition for the linear boundary. -/
theorem rate_le_linear (w : WeightedRow.Weights ι) (G θ δ : ℝ)
    (hG : 0 ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G ≤ 1)
    (hsmall : θ*G*w.mean ≤ δ/2) : rate w θ G ≤ θ*δ/2 := by
  have hm : 0 ≤ w.mean := by
    unfold mean
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (w.p_pos i).le (w.g_nonneg i))
  have hn : 0 ≤ θ^2*(G*w.mean) := by positivity
  have hd : 1 ≤ 2*(1-θ*G/3) := by linarith
  calc
    rate w θ G ≤ θ^2*(G*w.mean) := div_le_self hn hd
    _ = θ*(θ*G*w.mean) := by ring
    _ ≤ θ*(δ/2) := mul_le_mul_of_nonneg_left hsmall hθ
    _ = θ*δ/2 := by ring

def mixedTheta (κ : ℝ) : ℝ := 1/(1000*(2^20:ℝ)*κ)

/-- Explicit mixed72 constants for global .01κ max(q,N/10) concentration.
This deliberately leaves enormous exponent slack. -/
theorem mixed_global_constants (w : WeightedRow.Weights ι) (κ : ℝ)
    (hκ : 0 < κ) (hm : w.mean ≤ κ) :
    0 < mixedTheta κ ∧
    mixedTheta κ*((2^20:ℝ)*κ/2) < 3 ∧
    rate w (mixedTheta κ) ((2^20:ℝ)*κ/2) ≤ mixedTheta κ*(κ/100)/2 ∧
    (2^40:ℝ) ≤ mixedTheta κ*(κ/100)*((2^86:ℝ)/10)/2 := by
  have hθ : 0 < mixedTheta κ := by unfold mixedTheta; positivity
  have hp : mixedTheta κ*((2^20:ℝ)*κ/2) = 1/2000 := by
    unfold mixedTheta
    field_simp
    <;> ring
  refine ⟨hθ, ?_, ?_, ?_⟩
  · rw [hp]
    norm_num
  · apply rate_le_linear w _ _ _ (by positivity) hθ.le
    · rw [hp]; norm_num
    · rw [hp]
      nlinarith
  · have he : mixedTheta κ*(κ/100)*((2^86:ℝ)/10)/2 = (2^66:ℝ)/2000000 := by
      unfold mixedTheta
      field_simp
      <;> ring
    rw [he]
    norm_num

#print axioms rate_le_linear
#print axioms mixed_global_constants
end WeightedEmpirical
end
end

/- Original module: Submissions.UpperCompressions.RowConcentrationConstants; SHA256 a091dbb4288175f5ffb630df3b19eadaf87aff063eb5f99cfa125bce49e35cec. -/
section
noncomputable section
namespace WeightedEmpirical

/-- The same very conservative variance bound suffices for all row statistics.
Use G=1 for prefix indicators and G=Lκ for weighted row scores. -/
theorem mixed_row_exponent (G : ℝ) (hG : 0 < G) :
    let N : ℝ := 2^86
    let L : ℝ := 2^20
    let a := G*N/(100*L)
    let v := G^2*N
    0 < a ∧ 0 < v ∧ (2^30:ℝ) ≤ a^2/(2*(v+G*a/3)) := by
  dsimp only
  refine ⟨by positivity, by positivity, ?_⟩
  apply (le_div_iff₀ (by positivity)).2
  norm_num
  nlinarith [sq_pos_of_pos hG]

/-- Turn a deliberately loose exponential margin into a binary bound. -/
theorem exp_neg_pow30_le : Real.exp (-(2^30:ℝ)) ≤ ((2:ℝ)^1024)⁻¹ := by
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp : (2:ℝ)^1024 ≤ (Real.exp 1)^1024 := pow_le_pow_left₀ (by norm_num) he 1024
  rw [← Real.exp_nat_mul, mul_one] at hp
  have hc : (1024:ℝ) ≤ 2^30 := by norm_num
  have hb := hp.trans (Real.exp_le_exp.mpr hc)
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hb

/-- A 256-bit message-row union over 72 prefix tests and two weighted scores,
plus the global-score event, still fits within 2^-512. No time-prefix factor. -/
theorem mixed_row_union_margin :
    (74*(2^256:ℝ)+1)*Real.exp (-(2^30:ℝ)) ≤ ((2:ℝ)^512)⁻¹ := by
  have hm := mul_le_mul_of_nonneg_left exp_neg_pow30_le
    (show 0 ≤ 74*(2^256:ℝ)+1 by positivity)
  have hbase : (75:ℝ) ≤ 2^256 := by norm_num
  have hfactor : 74*(2^256:ℝ)+1 ≤ (2:ℝ)^512 := by
    calc
      74*(2^256:ℝ)+1 ≤ ((2:ℝ)^256)^2 := by nlinarith
      _ = (2:ℝ)^512 := by rw [← pow_mul]
  apply hm.trans
  calc
    (74*(2^256:ℝ)+1)*((2:ℝ)^1024)⁻¹ ≤ (2:ℝ)^512*((2:ℝ)^1024)⁻¹ := by gcongr
    _ = ((2:ℝ)^512)⁻¹ := by
      rw [show (1024:ℕ) = 512+512 from rfl, pow_add]
      field_simp

#print axioms mixed_row_exponent
#print axioms exp_neg_pow30_le
#print axioms mixed_row_union_margin
end WeightedEmpirical
end
end

/- Original module: Submissions.UpperCompressions.ReweightedScores; SHA256 f145a7987959605c6f45a9b5f09b54f62cb4998e5872119e5583d5c61e698e13. -/
section
noncomputable section
open scoped Classical BigOperators
namespace WeightedRow.Weights
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Change the observed score while preserving the actual class distribution. -/
def withScore (w : WeightedRow.Weights ι) (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) :
    WeightedRow.Weights ι where
  p := w.p
  g := g
  p_pos := w.p_pos
  g_nonneg := hg
  mass_le_one := w.mass_le_one

@[simp] theorem withScore_classMass (w : WeightedRow.Weights ι)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) (x : Option ι) :
    (w.withScore g hg).classMass x = w.classMass x := by cases x <;> rfl

/-- Prefix-count score. Rejection contributes zero, as in the shared decoder. -/
def prefixWeights (w : WeightedRow.Weights ι) (C : Finset ι) : WeightedRow.Weights ι :=
  w.withScore (fun i => if i ∈ C then 1 else 0) (fun i => by split_ifs <;> norm_num)

theorem prefix_weight_bound (w : WeightedRow.Weights ι) (C : Finset ι) (i : ι) :
    (w.prefixWeights C).g i ≤ 1 := by
  change (if i ∈ C then (1:ℝ) else 0) ≤ 1
  split_ifs <;> norm_num

private theorem indicator_sum (C : Finset ι) (f : ι → ℝ) :
    (∑ i, f i*(if i ∈ C then 1 else 0)) = ∑ i ∈ C, f i := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp

theorem prefix_mean (w : WeightedRow.Weights ι) (C : Finset ι) :
    (w.prefixWeights C).mean = ∑ i ∈ C, w.p i := by
  exact indicator_sum C w.p

theorem prefix_score (w : WeightedRow.Weights ι) (C : Finset ι) (k : ι → ℕ) :
    (w.prefixWeights C).score k = ∑ i ∈ C, (k i:ℝ) := by
  exact indicator_sum C (fun i => (k i:ℝ))

/-- Lower-tail M1 is exactly the empirical accepted-prefix deficit. -/
theorem prefix_deficit (w : WeightedRow.Weights ι) (C : Finset ι) (q : ℕ) (k : ι → ℕ) :
    -(w.prefixWeights C).M1 q k = (∑ i ∈ C, w.p i)*(q:ℝ)-∑ i ∈ C, (k i:ℝ) := by
  rw [M1, prefix_score, prefix_mean]
  ring

#print axioms withScore_classMass
#print axioms prefix_deficit
end WeightedRow.Weights
end
end

/- Original module: Submissions.UpperCompressions.WeightedCacheEvidence; SHA256 bb74060f4d853b3fd9a56427e1fac7ee0e1857878a22202c75c2bde7a43f741a. -/
section
noncomputable section
namespace WeightedCacheEvidence
open WeightedCacheCounts
open scoped Classical
variable {Q W I : Type} [DecidableEq Q] [Fintype I] [DecidableEq I]

def classSet (A : Finset Q) (c : Q → Option W) (decode : W → Option I) (i : I) : Finset Q :=
  (seen A c).filter (fun q => (c q).bind decode=some i)

theorem mem (A : Finset Q) (c : Q → Option W) (decode : W → Option I) (i : I)
    (q : Q) (hq : q∈A) (y : W) (hc : c q=some y) (hi : decode y=some i) :
    q∈classSet A c decode i := by
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_filter.mpr ⟨hq,by simp only [hc,Option.isSome_some]⟩
  · simp only [hc,Option.bind_some,hi]

theorem one (A : Finset Q) (c : Q → Option W) (decode : W → Option I) (i : I)
    (q : Q) (hq : q∈A) (y : W) (hc : c q=some y) (hi : decode y=some i) :
    1≤classCounts A c decode i := by
  exact Finset.one_le_card.mpr ⟨q,mem A c decode i q hq y hc hi⟩

theorem two (A : Finset Q) (c : Q → Option W) (decode : W → Option I) (i : I)
    (q q' : Q) (hne : q≠q') (hq : q∈A) (hq' : q'∈A)
    (y y' : W) (hc : c q=some y) (hc' : c q'=some y')
    (hi : decode y=some i) (hi' : decode y'=some i) : 2≤classCounts A c decode i := by
  have hs : ({q,q'} : Finset Q) ⊆ classSet A c decode i := by
    intro z hz
    have hz' : z=q ∨ z=q' := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz
    rcases hz' with hz | hz
    · rw [hz]
      exact mem A c decode i q hq y hc hi
    · rw [hz]
      exact mem A c decode i q' hq' y' hc' hi'
  have h := Finset.card_le_card hs
  have hn : q ∉ ({q'} : Finset Q) := by simpa only [Finset.mem_singleton] using hne
  have hcard : ({q,q'} : Finset Q).card=2 := by
    rw [Finset.card_insert_of_notMem hn,Finset.card_singleton]
  rw [hcard] at h
  exact h
#print axioms one
#print axioms two
end WeightedCacheEvidence
end
end

/- Original module: Submissions.UpperCompressions.StoppingExpectation; SHA256 cfdbfca09b9fc52b05f6024401aa4eba6cdad6e00c02bec559ddb4a8c7c2f98f. -/
section

/-! Bounded-stopping expectation algebra for the weighted-index research.
The expectation is an explicitly assumed normalized positive linear functional.
Zero stopped means and the stopped second moment are hypotheses, NOT optional
stopping or oracle-filtration theorems. No signature-security claim is exported. -/

noncomputable section
namespace WeightedStopping

variable {Ω : Type*}

@[simp] theorem expect_mul (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (a : ℝ) (f : Ω → ℝ) :
    E (fun ω => a * f ω) = a * E f := by
  change E (a • f) = a • E f
  exact E.map_smul a f

@[simp] theorem expect_add (E : (Ω → ℝ) →ₗ[ℝ] ℝ) (f g : Ω → ℝ) :
    E (fun ω => f ω + g ω) = E f + E g := E.map_add f g

@[simp] theorem expect_const (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hnorm : E (fun _ => 1) = 1) (a : ℝ) : E (fun _ => a) = a := by
  have hx := expect_mul E a (fun _ => 1)
  simpa [hnorm] using hx

theorem abs_young (x T : ℝ) (hT : 0 < T) : |x| ≤ T + x^2/(4*T) := by
  have hs := sq_nonneg (|x|-2*T)
  have ha : |x|^2 = x^2 := sq_abs x
  have hp : 0 < 4*T := by positivity
  calc
    |x| ≤ (T*(4*T)+x^2)/(4*T) := (le_div_iff₀ hp).2 (by nlinarith)
    _ = T+x^2/(4*T) := by field_simp

/-- The sole covariance estimate uses positivity and the stopped second moment;
no independence of the stopping time and the observed score is assumed. -/
theorem covariance_young
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (τ M : Ω → ℝ) (K V T : ℝ) (hK : 0 ≤ K) (hT : 0 < T)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτK : ∀ ω, τ ω ≤ K)
    (hsecond : E (fun ω => M ω ^ 2) ≤ V) :
    E (fun ω => τ ω * M ω) ≤ K * (T + V/(4*T)) := by
  have hpt (ω : Ω) : τ ω * M ω ≤ K*T + (K/(4*T))*(M ω)^2 := by
    calc
      τ ω * M ω ≤ τ ω * |M ω| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (hτ0 ω)
      _ ≤ K * |M ω| := mul_le_mul_of_nonneg_right (hτK ω) (abs_nonneg _)
      _ ≤ K * (T + (M ω)^2/(4*T)) :=
        mul_le_mul_of_nonneg_left (abs_young (M ω) T hT) hK
      _ = K*T + (K/(4*T))*(M ω)^2 := by ring
  have havg := hmono _ _ hpt
  rw [expect_add, expect_const E hnorm, expect_mul] at havg
  have hc : 0 ≤ K/(4*T) := by positivity
  have hv := mul_le_mul_of_nonneg_left hsecond hc
  calc
    E (fun ω => τ ω * M ω) ≤ K*T + (K/(4*T))*V := by linarith
    _ = K*(T+V/(4*T)) := by ring

/-- Chord bound for the deterministic part, expressed as a per-budget rate. -/
theorem endpoint (h d N K q : ℝ) (hh : 0 ≤ h) (hN : 0 < N)
    (hq : 0 ≤ q) (hqK : q ≤ K) :
    h*q + h*q*(q-1)/N + d*(K-q) ≤
      K * max d (h*(1+(K-1)/N)) := by
  let c := max d (h*(1+(K-1)/N))
  have hgap : 0 ≤ h*q*(K-q)/N := by positivity
  have hchord : h*q+h*q*(q-1)/N ≤ h*(1+(K-1)/N)*q := by
    ring_nf at hgap ⊢
    linarith
  have hpre := mul_le_mul_of_nonneg_right (le_max_right d (h*(1+(K-1)/N))) hq
  have hpost := mul_le_mul_of_nonneg_right (le_max_left d (h*(1+(K-1)/N)))
    (sub_nonneg.mpr hqK)
  nlinarith

/-- Main expectation bound. Its martingale hypotheses must be supplied by the
actual adaptive oracle experiment; this theorem proves only their algebraic
consequence, with the stopping covariance retained explicitly. -/
theorem stopped_payoff
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (τ S P : Ω → ℝ) (C h d N K V T : ℝ)
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hN : 0 < N) (hK : 0 ≤ K) (hT : 0 < T)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτK : ∀ ω, τ ω ≤ K)
    (hmean1 : E (fun ω => S ω - h*τ ω) = 0)
    (hmean2 : E (fun ω => P ω - τ ω*S ω + h*τ ω*(τ ω+1)/2) = 0)
    (hsecond : E (fun ω => (S ω - h*τ ω)^2) ≤ V) :
    E (fun ω => C*(S ω+2*P ω/N)+d*(K-τ ω)) ≤
      K*max d (C*h*(1+(K-1)/N)) + (2*C*K/N)*(T+V/(4*T)) := by
  let M₁ : Ω → ℝ := fun ω => S ω - h*τ ω
  let M₂ : Ω → ℝ := fun ω => P ω - τ ω*S ω + h*τ ω*(τ ω+1)/2
  let R := K*max d (C*h*(1+(K-1)/N))
  have hpoint (ω : Ω) : C*(S ω+2*P ω/N)+d*(K-τ ω) ≤
      R + C*M₁ ω + (2*C/N)*(τ ω*M₁ ω) + (2*C/N)*M₂ ω := by
    have hend := endpoint (C*h) d N K (τ ω) (mul_nonneg hC hh) hN (hτ0 ω) (hτK ω)
    have hid : C*(S ω+2*P ω/N)+d*(K-τ ω) =
      (C*h*τ ω+C*h*τ ω*(τ ω-1)/N+d*(K-τ ω)) +
      C*M₁ ω+(2*C/N)*(τ ω*M₁ ω)+(2*C/N)*M₂ ω := by
      dsimp [M₁, M₂]
      ring
    rw [hid]
    dsimp [R]
    linarith
  have havg := hmono _ _ hpoint
  simp only [expect_add, expect_const E hnorm, expect_mul] at havg
  have hm1 : E M₁ = 0 := hmean1
  have hm2 : E M₂ = 0 := hmean2
  rw [hm1, hm2] at havg
  have hcov := covariance_young E hmono hnorm τ M₁ K V T hK hT hτ0 hτK hsecond
  have hcoef : 0 ≤ 2*C/N := by positivity
  have hc := mul_le_mul_of_nonneg_left hcov hcoef
  dsimp [R] at havg
  calc
    E (fun ω => C*(S ω+2*P ω/N)+d*(K-τ ω)) ≤
      K*max d (C*h*(1+(K-1)/N))+(2*C/N)*(K*(T+V/(4*T))) := by
        simp only [expect_add, expect_mul]
        linarith
    _ = _ := by ring

/-- Explicit mixed72 nonce constants. This scalar fact does not establish the
schedule's h or gmax bounds; those are hypotheses in its application. -/
theorem mixed72_young_coefficient :
    (2*(99/98 : ℝ)/4096 + (512*(99/98 : ℝ)/5)*((2:ℝ)^20/(2:ℝ)^86)) < 1/1000 := by
  norm_num

/-- Symbolic bound reducing the mixed72 covariance correction to its
nonce/sample-size coefficient. All moment and budget estimates are explicit. -/
theorem covariance_coefficient (C κ K N L g h : ℝ)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hK : 0 ≤ K) (hN : 0 < N)
    (hL : 0 ≤ L) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hKN : K ≤ N/10) (hgmax : g ≤ L*κ/2) (hhmean : h ≤ κ) :
    (2*C*K/N)*(κ*N/4096+(K*g*h)/(4*(κ*N/4096))) ≤
      κ*K*(2*C/4096+(512*C/5)*(L/N)) := by
  have hv : K*g*h ≤ (N/10)*(L*κ/2)*κ := by
    have hkg : K*g ≤ (N/10)*(L*κ/2) :=
      mul_le_mul hKN hgmax hg (by positivity)
    exact mul_le_mul hkg hhmean hh (by positivity)
  have hden : 0 < 4*(κ*N/4096) := by positivity
  have hvdiv := div_le_div_of_nonneg_right hv hden.le
  have hcoeff : 0 ≤ 2*C*K/N := by positivity
  have hfull := mul_le_mul_of_nonneg_left
    (add_le_add_left hvdiv (κ*N/4096)) hcoeff
  calc
    (2*C*K/N)*(κ*N/4096+(K*g*h)/(4*(κ*N/4096))) ≤
      (2*C*K/N)*(κ*N/4096+((N/10)*(L*κ/2)*κ)/(4*(κ*N/4096))) := by simpa only [add_comm] using hfull
    _ = κ*K*(2*C/4096+(512*C/5)*(L/N)) := by
      field_simp
      <;> ring

/-- The mixed72 covariance error is at most one thousandth of κ times budget.
The concrete powers are the nonce count and number of signing draws. -/
theorem mixed72_covariance (C κ K g h : ℝ)
    (hC : 0 ≤ C) (hCmax : C ≤ 99/98) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hKN : K ≤ (2:ℝ)^86/10) (hgmax : g ≤ (2:ℝ)^20*κ/2) (hhmean : h ≤ κ) :
    (2*C*K/(2:ℝ)^86)*(κ*(2:ℝ)^86/4096+
      (K*g*h)/(4*(κ*(2:ℝ)^86/4096))) ≤ κ*K/1000 := by
  have hx := covariance_coefficient C κ K ((2:ℝ)^86) ((2:ℝ)^20) g h
    hC hκ hK (by positivity) (by positivity) hg hh hKN hgmax hhmean
  have hfirst : 2*C/4096 ≤ 2*(99/98 : ℝ)/4096 := by linarith
  have hsecond : (512*C/5)*((2:ℝ)^20/(2:ℝ)^86) ≤
      (512*(99/98 : ℝ)/5)*((2:ℝ)^20/(2:ℝ)^86) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hcoeff := (add_le_add hfirst hsecond).trans mixed72_young_coefficient.le
  have htotal := mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hκ.le hK)
  calc
    _ ≤ κ*K*(2*C/4096+(512*C/5)*((2:ℝ)^20/(2:ℝ)^86)) := hx
    _ ≤ κ*K*(1/1000) := htotal
    _ = _ := by ring

/-- Endpoint plus explicit covariance error for the mixed72 budget branch.
No stopping theorem is assumed implicitly: both zero means and the second
moment inequality appear in this statement. -/
theorem stopped_mixed72_payoff
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1) = 1)
    (τ S P : Ω → ℝ) (C h d κ K g : ℝ)
    (hC : 0 ≤ C) (hCmax : C ≤ 99/98) (hh : 0 ≤ h) (hκ : 0 < κ)
    (hK : 0 ≤ K) (hg : 0 ≤ g) (hKN : K ≤ (2:ℝ)^86/10)
    (hgmax : g ≤ (2:ℝ)^20*κ/2) (hhmean : h ≤ κ)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτK : ∀ ω, τ ω ≤ K)
    (hmean1 : E (fun ω => S ω - h*τ ω) = 0)
    (hmean2 : E (fun ω => P ω - τ ω*S ω + h*τ ω*(τ ω+1)/2) = 0)
    (hsecond : E (fun ω => (S ω - h*τ ω)^2) ≤ K*g*h) :
    E (fun ω => C*(S ω+2*P ω/(2:ℝ)^86)+d*(K-τ ω)) ≤
      K*max d (11*C*h/10) + κ*K/1000 := by
  have hN : 0 < (2:ℝ)^86 := by positivity
  have hT : 0 < κ*(2:ℝ)^86/4096 := by positivity
  have hx := stopped_payoff E hmono hnorm τ S P C h d ((2:ℝ)^86) K
    (K*g*h) (κ*(2:ℝ)^86/4096) hC hh hN hK hT hτ0 hτK
    hmean1 hmean2 hsecond
  have hc := mixed72_covariance C κ K g h hC hCmax hκ hK hg hh hKN hgmax hhmean
  have hratio : (K-1)/(2:ℝ)^86 ≤ 1/10 := (div_le_iff₀ hN).2 (by linarith)
  have hpre : C*h*(1+(K-1)/(2:ℝ)^86) ≤ 11*C*h/10 := by
    have hm := mul_le_mul_of_nonneg_left hratio (mul_nonneg hC hh)
    nlinarith
  have hend := mul_le_mul_of_nonneg_left (max_le_max_left d hpre) hK
  exact hx.trans (add_le_add hend hc)

/-- A uniform pre-signing authentication charge is absorbed by the continuation
rate when alpha ≤ d. This is deterministic algebra only. -/
theorem pre_authentication_domination (α d K q u : ℝ)
    (hα : α ≤ d) (hu : 0 ≤ u) :
    α*u+d*(K-q-u) ≤ d*(K-q) := by
  have hx := mul_le_mul_of_nonneg_right hα hu
  nlinarith

#print axioms covariance_young
#print axioms endpoint
#print axioms stopped_payoff
#print axioms mixed72_young_coefficient
#print axioms covariance_coefficient
#print axioms mixed72_covariance
#print axioms stopped_mixed72_payoff
#print axioms pre_authentication_domination

end WeightedStopping
end
end

/- Original module: Submissions.UpperCompressions.WeightedHazardPair; SHA256 aa845daa836ee1faba622e815f316b2a8ff867c5ddb9706d98b732a2ec7d5d51. -/
section

/-! Deterministic domination of the cached-replay hazard by the global first
and collision-pair scores. No random-oracle or stopping hypotheses are used. -/
noncomputable section
namespace WeightedRow.Weights
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (w : Weights ι)

theorem nat_le_twice_choose_two (n : ℕ) (hn : 2 ≤ n) : n ≤ 2*n.choose 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    have he : (n+1).choose 2=n.choose 2+n := by
      simpa [Nat.choose_one_right,add_comm] using Nat.choose_succ_succ n 1
    rw [he]
    by_cases h : 2 ≤ n
    · have := ih h
      omega
    · have : n=1 := by omega
      subst n
      decide

theorem seen_nonneg (k : ι → ℕ) : 0 ≤ w.seen k := by
  unfold seen
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> first | exact le_rfl | exact w.g_nonneg i

theorem seen_le_score (k : ι → ℕ) : w.seen k ≤ w.score k := by
  unfold seen score
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : k i=0
  · simp [h]
  · rw [if_neg h]
    have hk : (1:ℝ) ≤ k i := by exact_mod_cast (show 1 ≤ k i by omega)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (w.g_nonneg i)

theorem bad_le_twice_pairScore (k row : ι → ℕ) (hr : ∀ i,row i ≤ k i) :
    w.bad k row ≤ 2*w.pairScore k := by
  unfold bad pairScore
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hk : 2 ≤ k i
  · rw [if_pos hk]
    have hkn : row i ≤ 2*(k i).choose 2 := (hr i).trans (nat_le_twice_choose_two _ hk)
    have hkr : (row i:ℝ) ≤ 2*((k i).choose 2:ℝ) := by exact_mod_cast hkn
    have hx := mul_le_mul_of_nonneg_right hkr
      (div_nonneg (w.g_nonneg i) (w.p_pos i).le)
    convert hx using 1 <;> ring
  · rw [if_neg hk]
    exact mul_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (w.g_nonneg i)) (w.p_pos i).le)

theorem hazard_le_score_pair (N : ℝ) (hN : 0 < N) (r : ℕ)
    (k row : ι → ℕ) (hr : ∀ i,row i ≤ k i) :
    w.hazard N r k row ≤ w.score k+2*w.pairScore k/N := by
  have hc : 1-(r:ℝ)/N ≤ 1 := sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hN.le)
  have hseen := mul_le_mul_of_nonneg_right hc (w.seen_nonneg k)
  have hbad := div_le_div_of_nonneg_right (w.bad_le_twice_pairScore k row hr) hN.le
  unfold hazard
  have hs := w.seen_le_score k
  nlinarith

#print axioms hazard_le_score_pair
end WeightedRow.Weights
end
end

