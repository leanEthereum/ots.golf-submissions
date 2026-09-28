import Mathlib
import Submissions.UpperLeanIsa.FieldRescale

/-! Algebraic support for destination-dependent frames.

A jump to slot `s` in stage `u` uses frame `g^s + a^u`. A body beginning
at `e` in stage `v` is encoded relative to `g^e + a^v`. Incorrect landings
lead to nonzero polynomial equations in `a`. Avoiding their roots can remove
the old entry jump. These lemmas are research support, not a machine certificate.
-/

namespace OptimalOTS.AffineFrames

open Polynomial LeanerVM.Parameters
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section RootAvoidance

variable {F I : Type} [Field F] [Fintype F] [Fintype I]

/-- A finite family excludes fewer field elements than the sum of its degrees. -/
theorem exists_common_nonroot (polys : I → F[X]) (D : ℕ)
    (hne : ∀ i, polys i ≠ 0) (hdeg : ∀ i, (polys i).natDegree ≤ D)
    (hcard : Fintype.card I * D < Fintype.card F) :
    ∃ a : F, ∀ i, (polys i).eval a ≠ 0 := by
  classical
  let p : F[X] := ∏ i : I, polys i
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hb : p.natDegree ≤ Fintype.card I * D := by
    calc p.natDegree ≤ ∑ i : I, (polys i).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : I, D := Finset.sum_le_sum fun i _ => hdeg i
      _ = Fintype.card I * D := by simp
  obtain ⟨a, ha⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card p hp (by
    rw [Cardinal.mk_fintype]
    exact_mod_cast hb.trans_lt hcard)
  have he : (∏ i : I, (polys i).eval a) ≠ 0 := by
    simpa only [p, Polynomial.eval_prod] using ha
  exact ⟨a, fun i => Finset.prod_ne_zero_iff.mp he i (Finset.mem_univ _)⟩

end RootAvoidance

/-- Polynomial describing the frame at a chosen target. Stage exponents are positive. -/
def framePoly (u s : ℕ) : K[X] := X ^ u + C (gpow s)

/-- Equality between a read in the incoming frame and cell `j` of the declared frame. -/
def collisionPoly (u v s e c j : ℕ) : K[X] :=
  C (gpow c) * framePoly u s - C (gpow j) * framePoly v e

theorem collision_eval (a : K) (u v s e c j : ℕ) :
    (collisionPoly u v s e c j).eval a =
      gpow c * (a ^ u + gpow s) - gpow j * (a ^ v + gpow e) := by
  simp only [collisionPoly, framePoly, Polynomial.eval_sub, Polynomial.eval_C_mul,
    Polynomial.eval_add, Polynomial.eval_X_pow, Polynomial.eval_C]

theorem collision_degree {u v s e c j D : ℕ} (hu : u ≤ D) (hv : v ≤ D) :
    (collisionPoly u v s e c j).natDegree ≤ D := by
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  all_goals
    apply le_trans Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_C, zero_add]
    apply le_trans (Polynomial.natDegree_add_le _ _)
    simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
    exact max_le (by assumption) (Nat.zero_le _)

theorem framePoly_ne_zero {u s : ℕ} (hu : 0 < u) : framePoly u s ≠ 0 := by
  intro h
  have hc := congrArg (fun p : K[X] => p.coeff u) h
  simp only [framePoly, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.coeff_zero, if_pos rfl, if_neg (Nat.ne_of_gt hu), add_zero] at hc
  exact one_ne_zero hc

theorem collision_ne_zero {u v s e c j : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hs : s < 2 ^ 64 - 1) (he : e < 2 ^ 64 - 1)
    (hc : c < 2 ^ 64 - 1) (hj : j < 2 ^ 64 - 1)
    (hwrong : u ≠ v ∨ s ≠ e) : collisionPoly u v s e c j ≠ 0 := by
  intro h
  by_cases huv : u = v
  · subst v
    have hse : s ≠ e := hwrong.resolve_left (by simp)
    have hcoeff := congrArg (fun p : K[X] => p.coeff u) h
    have hcg : gpow c = gpow j := by
      simpa only [collisionPoly, framePoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
        Polynomial.coeff_zero, if_pos rfl, if_neg (Nat.ne_of_gt hu), add_zero, mul_one,
        sub_eq_zero, ite_true] using hcoeff
    have hcj : c = j := gpow_injOn (Set.mem_Iio.mpr hc) (Set.mem_Iio.mpr hj) hcg
    subst j
    have hzero := congrArg (fun p : K[X] => p.coeff 0) h
    have hsg : gpow c * gpow s = gpow c * gpow e := by
      simpa only [collisionPoly, framePoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
        Polynomial.coeff_zero, if_pos rfl, if_neg (Nat.ne_of_gt hu).symm, zero_add,
        sub_eq_zero, ite_true] using hzero
    have heq : gpow s = gpow e := mul_left_cancel₀ (pow_ne_zero _ g_ne_zero) hsg
    exact hse (gpow_injOn (Set.mem_Iio.mpr hs) (Set.mem_Iio.mpr he) heq)
  · have hcoeff := congrArg (fun p : K[X] => p.coeff u) h
    have hz : gpow c = 0 := by
      simpa only [collisionPoly, framePoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
        Polynomial.coeff_zero, if_pos rfl, if_neg (Nat.ne_of_gt hu), if_neg huv,
        add_zero, mul_one, mul_zero, sub_zero, ite_true] using hcoeff
    exact (pow_ne_zero _ g_ne_zero) hz

/-- The main family is small enough even with all admitted memory sizes. -/
theorem main_root_count : 14 * 2 ^ 18 * 2 ^ 32 * 14 < (2 : ℕ) ^ 64 := by norm_num

/-- The pinned signature length, as a field bit pattern (not a natural-number cast). -/
def lengthK : K := BitVec.ofNat 64 5504

theorem lengthK_ne_one : lengthK ≠ 1 := by decide

theorem lengthK_ne_zero : lengthK ≠ 0 := by decide

/-- A positive power can be separated from an already initialized constant. -/
theorem power_sub_constant_ne_zero (c : K) {n : ℕ} (hn : 0 < n) :
    (X ^ n - C c : K[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : K[X] => p.coeff n) h
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.coeff_zero, if_pos rfl, if_neg (Nat.ne_of_gt hn), sub_zero] at hc
  exact one_ne_zero hc

theorem power_sub_constant_degree (c : K) (n : ℕ) :
    (X ^ n - C c : K[X]).natDegree ≤ n := by
  exact (Polynomial.natDegree_sub_le _ _).trans (by simp)

end
end OptimalOTS.AffineFrames
