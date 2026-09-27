import Submissions.UpperCompressions.ProofBundle00
import Mathlib

/-!
# Equality-only replay collision algebra

For an equality compatibility relation, repeated occurrences of the same
decoded class are the only off-diagonal replay terms.  This file isolates
their deterministic and one-query algebra.  It deliberately stops before the
random-oracle completion coupling: the latter must prove the simultaneous
occupancy cap used by the stopped process.
-/

noncomputable section

open scoped Classical BigOperators

namespace WeightedRow.Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (w : WeightedRow.Weights ι)

/-- `p_i (g_i/p_i)^2`, written in the cancellation-friendly form `g_i^2/p_i`. -/
def collisionMass (i : ι) : ℝ := (w.g i)^2 / w.p i

theorem collisionMass_eq (i : ι) :
    w.collisionMass i = w.p i * (w.g i / w.p i)^2 := by
  unfold collisionMass
  field_simp [(w.p_pos i).ne']
  <;> ring

theorem collisionMass_nonneg (i : ι) : 0 ≤ w.collisionMass i :=
  div_nonneg (sq_nonneg _) (w.p_pos i).le

/-- The diagonal occurrence score in a distinguished row. -/
def D (row : ι → ℕ) : ℝ :=
  ∑ i, (row i : ℝ) * w.collisionMass i

/-- The ordered equal-class self-collision score in a distinguished row. -/
def X (row : ι → ℕ) : ℝ :=
  ∑ i, (row i : ℝ) * ((row i : ℝ) - 1) * w.collisionMass i

/-- Reverse replay square clock. -/
def Qrev (row : ι → ℕ) : ℝ :=
  ∑ i, (row i : ℝ)^2 * w.collisionMass i

/-- Forward replay square clock: a class contributes after its first global occurrence. -/
def Qfwd (k : ι → ℕ) : ℝ :=
  ∑ i, if k i = 0 then 0 else w.collisionMass i

/-- Fresh-class square mass appearing in the hazard gain. -/
def freshSquareMass : ℝ := ∑ i, w.p i * (w.g i)^2

/-- Mean diagonal-clock increment under one decoder draw. -/
def diagonalMean : ℝ := ∑ i, (w.g i)^2

/-- Mean self-collision half-increment under one decoder draw. -/
def rowSquareScore (row : ι → ℕ) : ℝ :=
  ∑ i, (row i : ℝ) * (w.g i)^2

private theorem collision_sum_change (f f' : ι → ℝ) (i : ι)
    (h : ∀ j, j ≠ i → f' j = f j) :
    (∑ j, f' j) = (∑ j, f j) + (f' i - f i) := by
  have he : f' = fun j => f j + if j = i then f' i - f i else 0 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj, h j hj]
  rw [he, Finset.sum_add_distrib]
  simp

theorem X_bump (row : ι → ℕ) (i : ι) :
    w.X (bump row i) = w.X row +
      2 * (row i : ℝ) * w.collisionMass i := by
  unfold X
  rw [collision_sum_change
    (fun j => (row j : ℝ) * ((row j : ℝ) - 1) * w.collisionMass j)
    (fun j => (bump row i j : ℝ) * ((bump row i j : ℝ) - 1) *
      w.collisionMass j) i]
  · simp only [bump, Function.update_self, Nat.cast_add, Nat.cast_one]
    ring
  · intro j hj
    simp [bump, Function.update_of_ne hj]

theorem Qrev_eq_D_add_X (row : ι → ℕ) :
    w.Qrev row = w.D row + w.X row := by
  unfold Qrev D X
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One-query ordered self-collision increment; rejection contributes zero. -/
def xJump (row : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i => 2 * (row i : ℝ) * w.collisionMass i

theorem X_advance (row : ι → ℕ) (x : Option ι) :
    w.X (advance row x) = w.X row + w.xJump row x := by
  cases x with
  | none => simp [advance, xJump]
  | some i => simpa [advance, xJump] using w.X_bump row i

theorem expect_xJump (row : ι → ℕ) :
    w.expect (w.xJump row) = 2 * w.rowSquareScore row := by
  unfold expect xJump rowSquareScore collisionMass
  simp only [mul_zero, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(w.p_pos i).ne']
  <;> ring

theorem rowSquareScore_le_total (row : ι → ℕ) (r G : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (hrow : ∑ i, (row i : ℝ) ≤ r) :
    w.rowSquareScore row ≤ r * G^2 := by
  have hpoint (i : ι) :
      (row i : ℝ) * (w.g i)^2 ≤ (row i : ℝ) * G^2 := by
    have hr : 0 ≤ (row i : ℝ) := Nat.cast_nonneg _
    have hgi : 0 ≤ w.g i := w.g_nonneg i
    have hsq : (w.g i)^2 ≤ G^2 := by nlinarith [hg i]
    exact mul_le_mul_of_nonneg_left hsq hr
  calc
    w.rowSquareScore row ≤ ∑ i, (row i : ℝ) * G^2 :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (∑ i, (row i : ℝ)) * G^2 := by rw [Finset.sum_mul]
    _ ≤ r * G^2 := mul_le_mul_of_nonneg_right hrow (sq_nonneg G)

theorem expect_xJump_le (row : ι → ℕ) (r G : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (hrow : ∑ i, (row i : ℝ) ≤ r) :
    w.expect (w.xJump row) ≤ 2 * r * G^2 := by
  rw [expect_xJump]
  nlinarith [w.rowSquareScore_le_total row r G hG hg hrow]

theorem xJump_nonneg (row : ι → ℕ) (x : Option ι) : 0 ≤ w.xJump row x := by
  cases x with
  | none => simp [xJump]
  | some i =>
      simp only [xJump]
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (w.collisionMass_nonneg i)

theorem Qfwd_nonneg (k : ι → ℕ) : 0 ≤ w.Qfwd k := by
  unfold Qfwd
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · exact w.collisionMass_nonneg i

/-- The unseen-class contribution to a positive hazard increment. -/
def freshPiece (a : ℝ) (k : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i => a * (if k i = 0 then w.g i else 0)

/-- The old-class forward contribution to an inside-row hazard increment. -/
def forwardPiece (k : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i => if k i = 0 then 0 else w.g i / w.p i

/-- The singleton reverse contribution to either positive hazard increment. -/
def reversePiece (k row : ι → ℕ) : Option ι → ℝ
  | none => 0
  | some i => if k i = 1 then (row i : ℝ) * w.g i / w.p i else 0

theorem expect_freshPiece_sq_le (a : ℝ) (k : ι → ℕ) (ha : |a| ≤ 1) :
    w.expect (fun x => (w.freshPiece a k x)^2) ≤ w.freshSquareMass := by
  have haa := abs_le.mp ha
  have ha2 : a^2 ≤ 1 := by
    have hp : 0 ≤ (1-a)*(1+a) := mul_nonneg (sub_nonneg.mpr haa.2) (by linarith)
    nlinarith
  unfold expect freshSquareMass
  simp [freshPiece]
  apply Finset.sum_le_sum
  intro i _
  by_cases h0 : k i = 0
  · simp only [if_pos h0]
    apply mul_le_mul_of_nonneg_left _ (w.p_pos i).le
    have hs := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (w.g i))
    nlinarith
  · simp only [if_neg h0, mul_zero, zero_pow]
    exact mul_nonneg (w.p_pos i).le (sq_nonneg _)

theorem expect_forwardPiece_sq (k : ι → ℕ) :
    w.expect (fun x => (w.forwardPiece k x)^2) = w.Qfwd k := by
  unfold expect Qfwd collisionMass
  simp [forwardPiece]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h0 : k i = 0
  · simp [h0]
  · simp only [if_neg h0]
    field_simp [(w.p_pos i).ne']
    <;> ring

theorem expect_reversePiece_sq_le (k row : ι → ℕ) :
    w.expect (fun x => (w.reversePiece k row x)^2) ≤ w.Qrev row := by
  unfold expect Qrev collisionMass
  simp [reversePiece]
  apply Finset.sum_le_sum
  intro i _
  by_cases h1 : k i = 1
  · simp only [if_pos h1]
    field_simp [(w.p_pos i).ne']
    exact le_rfl
  · simp only [if_neg h1, zero_pow, mul_zero]
    exact mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) (w.p_pos i).le)

private theorem three_sq_le (a b c : ℝ) :
    (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]

theorem expect_three_square_le (f₁ f₂ f₃ : Option ι → ℝ) (A₁ A₂ A₃ : ℝ)
    (h₁ : w.expect (fun x => (f₁ x)^2) ≤ A₁)
    (h₂ : w.expect (fun x => (f₂ x)^2) ≤ A₂)
    (h₃ : w.expect (fun x => (f₃ x)^2) ≤ A₃) :
    w.expect (fun x => (f₁ x + f₂ x + f₃ x)^2) ≤ 3*(A₁+A₂+A₃) := by
  have hpoint := w.expect_mono
    (fun x => (f₁ x + f₂ x + f₃ x)^2)
    (fun x => 3*((f₁ x)^2+(f₂ x)^2+(f₃ x)^2))
    (fun x => three_sq_le (f₁ x) (f₂ x) (f₃ x))
  simp only [mul_add, expect_add, expect_smul] at hpoint
  nlinarith

/-- Conditional second-moment envelope for the three positive equality-hazard pieces. -/
theorem equalityGain_square_envelope (a N : ℝ) (k row : ι → ℕ)
    (ha : |a| ≤ 1) (hN : 0 < N) :
    w.expect (fun x =>
      (w.freshPiece a k x + w.forwardPiece k x / N + w.reversePiece k row x / N)^2) ≤
      3*w.freshSquareMass + 3*(w.Qrev row+w.Qfwd k)/N^2 := by
  have hfwd : w.expect (fun x => (w.forwardPiece k x / N)^2) = w.Qfwd k/N^2 := by
    have he : (fun x => (w.forwardPiece k x / N)^2) =
        (fun x => (1/N^2) * (w.forwardPiece k x)^2) := by
      funext x
      field_simp [hN.ne']
      <;> ring
    rw [he, expect_smul, expect_forwardPiece_sq]
    ring
  have hrev : w.expect (fun x => (w.reversePiece k row x / N)^2) ≤
      w.Qrev row/N^2 := by
    have he : (fun x => (w.reversePiece k row x / N)^2) =
        (fun x => (1/N^2) * (w.reversePiece k row x)^2) := by
      funext x
      field_simp [hN.ne']
      <;> ring
    rw [he, expect_smul]
    have hm := mul_le_mul_of_nonneg_left (w.expect_reversePiece_sq_le k row)
      (by positivity : 0 ≤ (1/N^2))
    simpa only [one_div, inv_mul_eq_div] using hm
  have h := w.expect_three_square_le
    (w.freshPiece a k)
    (fun x => w.forwardPiece k x/N)
    (fun x => w.reversePiece k row x/N)
    w.freshSquareMass (w.Qfwd k/N^2) (w.Qrev row/N^2)
    (w.expect_freshPiece_sq_le a k ha) (hfwd.le) hrev
  calc
    _ ≤ 3*(w.freshSquareMass+w.Qfwd k/N^2+w.Qrev row/N^2) := h
    _ = 3*w.freshSquareMass + 3*(w.Qrev row+w.Qfwd k)/N^2 := by ring

theorem positiveInside_eq_pieces (N : ℝ) (r : ℕ) (k row : ι → ℕ)
    (x : Option ι) :
    w.positiveInside N r k row x =
      w.freshPiece (1-((r:ℝ)+1)/N) k x +
        w.forwardPiece k x/N + w.reversePiece k row x/N := by
  cases x with
  | none => simp [positiveInside, freshPiece, forwardPiece, reversePiece]
  | some i =>
      by_cases h0 : k i = 0
      · have h1 : k i ≠ 1 := by omega
        simp [positiveInside, freshPiece, forwardPiece, reversePiece, h0, h1]
      · by_cases h1 : k i = 1
        · simp [positiveInside, freshPiece, forwardPiece, reversePiece, h0, h1]
          ring
        · simp [positiveInside, freshPiece, forwardPiece, reversePiece, h0, h1]

/-- The inside-row positive hazard gain has the common equality-clock envelope. -/
theorem positiveInside_square_envelope (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ)+1 ≤ N) (k row : ι → ℕ) :
    w.expect (fun x => (w.positiveInside N r k row x)^2) ≤
      3*w.freshSquareMass + 3*(w.Qrev row+w.Qfwd k)/N^2 := by
  have ha : |1-((r:ℝ)+1)/N| ≤ 1 := by
    rw [abs_le]
    constructor
    · have hd : ((r:ℝ)+1)/N ≤ 2 := by
        calc
          ((r:ℝ)+1)/N ≤ 1 := (div_le_one hN).2 hr
          _ ≤ 2 := by norm_num
      linarith
    · exact sub_le_self _ (div_nonneg (by positivity) hN.le)
  rw [show (fun x => (w.positiveInside N r k row x)^2) =
      (fun x => (w.freshPiece (1-((r:ℝ)+1)/N) k x +
        w.forwardPiece k x/N + w.reversePiece k row x/N)^2) by
    funext x
    rw [w.positiveInside_eq_pieces N r k row x]]
  exact w.equalityGain_square_envelope (1-((r:ℝ)+1)/N) N k row ha hN

theorem positiveOutside_eq_pieces (N : ℝ) (r : ℕ) (k row : ι → ℕ)
    (x : Option ι) :
    w.positiveOutside N r k row x =
      w.freshPiece (1-(r:ℝ)/N) k x + w.reversePiece k row x/N := by
  cases x with
  | none => simp [positiveOutside, freshPiece, reversePiece]
  | some i =>
      by_cases h0 : k i = 0
      · have h1 : k i ≠ 1 := by omega
        simp [positiveOutside, freshPiece, reversePiece, h0, h1]
      · by_cases h1 : k i = 1
        · simp [positiveOutside, freshPiece, reversePiece, h0, h1]
        · simp [positiveOutside, freshPiece, reversePiece, h0, h1]

/-- The outside-row positive hazard gain obeys the same common envelope. -/
theorem positiveOutside_square_envelope (N : ℝ) (hN : 0 < N) (r : ℕ)
    (hr : (r : ℝ) ≤ N) (k row : ι → ℕ) :
    w.expect (fun x => (w.positiveOutside N r k row x)^2) ≤
      3*w.freshSquareMass + 3*(w.Qrev row+w.Qfwd k)/N^2 := by
  have ha : |1-(r:ℝ)/N| ≤ 1 := by
    rw [abs_le]
    constructor
    · have hd : (r:ℝ)/N ≤ 1 := (div_le_one hN).2 hr
      linarith
    · exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hN.le)
  have hbase := w.expect_three_square_le
    (w.freshPiece (1-(r:ℝ)/N) k)
    (fun _ => 0)
    (fun x => w.reversePiece k row x/N)
    w.freshSquareMass 0 (w.Qrev row/N^2)
    (w.expect_freshPiece_sq_le (1-(r:ℝ)/N) k ha)
    (by simp [expect_const])
    (by
      have he : (fun x => (w.reversePiece k row x / N)^2) =
          (fun x => (1/N^2) * (w.reversePiece k row x)^2) := by
        funext x
        field_simp [hN.ne']
        <;> ring
      rw [he, expect_smul]
      have hm := mul_le_mul_of_nonneg_left (w.expect_reversePiece_sq_le k row)
        (by positivity : 0 ≤ (1/N^2))
      simpa only [one_div, inv_mul_eq_div] using hm)
  rw [show (fun x => (w.positiveOutside N r k row x)^2) =
      (fun x => (w.freshPiece (1-(r:ℝ)/N) k x + 0 +
        w.reversePiece k row x/N)^2) by
    funext x
    rw [w.positiveOutside_eq_pieces N r k row x]
    ring]
  calc
    _ ≤ 3*(w.freshSquareMass+0+w.Qrev row/N^2) := hbase
    _ ≤ 3*w.freshSquareMass + 3*(w.Qrev row+w.Qfwd k)/N^2 := by
      have hq := w.Qfwd_nonneg k
      have hn2 : 0 < N^2 := sq_pos_of_pos hN
      apply le_of_sub_nonneg
      field_simp [hn2.ne']
      nlinarith

/-- An occupancy cap turns the self-collision clock into a bounded-jump process. -/
theorem xJump_le_of_cap (row u : ι → ℕ) (J : ℝ)
    (hJ : 0 ≤ J)
    (hrow : ∀ i, row i ≤ u i)
    (hcap : ∀ i, 2 * (u i : ℝ) * w.collisionMass i ≤ J)
    (x : Option ι) : w.xJump row x ≤ J := by
  cases x with
  | none => simpa [xJump] using hJ
  | some i =>
      simp only [xJump]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hrow i)) (by norm_num))
        (w.collisionMass_nonneg i)).trans (hcap i)

theorem xJump_centered_variance_le_of_cap (row u : ι → ℕ) (J : ℝ)
    (hJ : 0 ≤ J)
    (hrow : ∀ i, row i ≤ u i)
    (hcap : ∀ i, 2 * (u i : ℝ) * w.collisionMass i ≤ J) :
    w.expect (fun x => (w.xJump row x - w.expect (w.xJump row))^2) ≤
      J * w.expect (w.xJump row) := by
  apply w.centered_variance_le
  intro x
  exact ⟨w.xJump_nonneg row x, w.xJump_le_of_cap row u J hJ hrow hcap x⟩

/-- Linear-map packaging of the decoder expectation for generic MGF lemmas. -/
def collisionExpectLinear : (Option ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := w.expect
  map_add' := w.expect_add
  map_smul' c f := w.expect_smul c f

/-- The stopped-process interface: replace the exact conditional drift by any
predictable upper bound `μ`, charging the corresponding larger variance rate. -/
theorem xJump_upper_compensated_mgf_of_cap (row u : ι → ℕ) (θ J μ : ℝ)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ * J < 3)
    (hrow : ∀ i, row i ≤ u i)
    (hcap : ∀ i, 2 * (u i : ℝ) * w.collisionMass i ≤ J)
    (hmean : w.expect (w.xJump row) ≤ μ) :
    w.expect (fun x => Real.exp
      (θ * (w.xJump row x - μ) -
        θ^2 * (J * μ) / (2 * (1 - θ * J / 3)))) ≤ 1 := by
  let E := w.collisionExpectLinear
  have hnorm : E (fun _ => 1) = 1 := w.expect_one
  have hzero : E (fun x => w.xJump row x - w.expect (w.xJump row)) = 0 := by
    change w.expect (fun x => w.xJump row x - w.expect (w.xJump row)) = 0
    rw [expect_sub, expect_const, sub_self]
  have habs : ∀ x, |w.xJump row x - w.expect (w.xJump row)| ≤ J := by
    intro x
    exact w.centered_abs_le _ _
      (fun y => ⟨w.xJump_nonneg row y, w.xJump_le_of_cap row u J hJ hrow hcap y⟩) x
  have hsecond : E (fun x => (w.xJump row x - w.expect (w.xJump row))^2) ≤
      J * μ := by
    exact (w.xJump_centered_variance_le_of_cap row u J hJ hrow hcap).trans
      (mul_le_mul_of_nonneg_left hmean hJ)
  have hmgf := WeightedMGF.compensated_mgf E w.expect_mono hnorm
    (fun x => w.xJump row x - w.expect (w.xJump row)) θ J (J*μ)
    hθ hJ hθJ habs hzero hsecond
  change w.expect (fun x => Real.exp
    (θ * (w.xJump row x - w.expect (w.xJump row)) -
      θ^2 * (J*μ) / (2*(1-θ*J/3)))) ≤ 1 at hmgf
  apply (w.expect_mono _ _ ?_).trans hmgf
  intro x
  apply Real.exp_le_exp.mpr
  have hd : 0 < 2*(1-θ*J/3) := by linarith
  have hm := mul_le_mul_of_nonneg_left hmean hθ
  linarith

end WeightedRow.Weights
