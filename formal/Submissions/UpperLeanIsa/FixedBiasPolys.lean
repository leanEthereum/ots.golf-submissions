import Submissions.UpperLeanIsa.AffineFrames

/-! Two fixed stages use length and ONE; all other stages use positive powers. -/
namespace OptimalOTS.AffineFrames
open Polynomial LeanerVM.Parameters
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def isFixed (u : Nat) : Prop := 12 ≤ u
instance (u : Nat) : Decidable (isFixed u) := inferInstanceAs (Decidable (12 ≤ u))
def fixedBias (u : Nat) : K := if u = 12 then lengthK else 1
def stageBias (a : K) (u : Nat) : K := if isFixed u then fixedBias u else a^(u+1)
def stagePoly (u s : Nat) : K[X] :=
  if isFixed u then C (fixedBias u + gpow s) else framePoly (u+1) s
def stageCollision (u v s e c j : Nat) : K[X] :=
  C (gpow c) * stagePoly u s - C (gpow j) * stagePoly v e

theorem stagePoly_eval (a : K) (u s : Nat) :
    (stagePoly u s).eval a = stageBias a u + gpow s := by
  unfold stagePoly stageBias
  split_ifs <;> simp only [Polynomial.eval_C, framePoly, Polynomial.eval_add,
    Polynomial.eval_X_pow, Polynomial.eval_C]

theorem stageCollision_eval (a : K) (u v s e c j : Nat) :
    (stageCollision u v s e c j).eval a =
    gpow c * (stageBias a u + gpow s) - gpow j * (stageBias a v + gpow e) := by
  simp only [stageCollision, Polynomial.eval_sub, Polynomial.eval_C_mul, stagePoly_eval]

theorem positive_constant_collision (b : K) {u s c j : Nat} (hu : 0 < u) :
    C (gpow c) * framePoly u s - C (gpow j) * C b ≠ (0 : K[X]) := by
  intro h
  have hh := congrArg (fun p : K[X] => p.coeff u) h
  have hz : gpow c = 0 := by
    simpa only [framePoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_zero, if_pos rfl, if_neg (Nat.ne_of_gt hu),
      add_zero, mul_one, mul_zero, sub_zero, ite_true] using hh
  exact (pow_ne_zero _ g_ne_zero) hz

theorem constant_positive_collision (b : K) {u s c j : Nat} (hu : 0 < u) :
    C (gpow c) * C b - C (gpow j) * framePoly u s ≠ (0 : K[X]) := by
  intro h
  apply positive_constant_collision b (u:=u) (s:=s) (c:=j) (j:=c) hu
  exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

theorem stagePoly_degree (u s : Nat) (hu : u < 14) : (stagePoly u s).natDegree ≤ 300 := by
  unfold stagePoly
  split_ifs
  · simp
  · apply (Polynomial.natDegree_add_le _ _).trans
    simp only [framePoly, Polynomial.natDegree_X_pow, Polynomial.natDegree_C, max_zero]
    omega

theorem stageCollision_degree {u v s e c j : Nat} (hu : u < 14) (hv : v < 14) :
    (stageCollision u v s e c j).natDegree ≤ 300 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le ((Polynomial.natDegree_C_mul_le _ _).trans (stagePoly_degree u s hu))
    ((Polynomial.natDegree_C_mul_le _ _).trans (stagePoly_degree v e hv))

end
end OptimalOTS.AffineFrames
