import Submissions.UpperLeanIsa.FreeLastResearch

/-! Clearing Laurent denominators for the free-last landing constraints.
The degree is the span of the two signed exponents and zero, rather than the
sum of their absolute values. This distinction makes the root budget fit. -/
namespace OptimalOTS.FreeLastPolys
open Polynomial
noncomputable section
open scoped Classical

def lower (n m : Int) : Int := min 0 (min n m)
def upper (n m : Int) : Int := max 0 (max n m)
def shift (n m : Int) : Nat := (-lower n m).toNat
def span (n m : Int) : Nat := (upper n m - lower n m).toNat
def lift (n : Int) (k : Nat) : Nat := (n + k).toNat

theorem shift_spec (n m : Int) :
    (shift n m : Int) = -lower n m ∧ 0 ≤ n + shift n m ∧ 0 ≤ m + shift n m := by
  simp only [shift, lower]
  omega

theorem lift_cast {n : Int} {k : Nat} (h : 0 ≤ n+k) :
    (lift n k : Int) = n+k := Int.toNat_of_nonneg h

theorem lift_ne {n m : Int} {k : Nat} (hn : 0 ≤ n+k) (hm : 0 ≤ m+k)
    (h : n ≠ m) : lift n k ≠ lift m k := by
  intro he
  have := congrArg (fun x : Nat => (x : Int)) he
  rw [lift_cast hn, lift_cast hm] at this
  omega

theorem lift_ne_shift {n : Int} {k : Nat} (hn : 0 ≤ n+k) (h : n ≠ 0) :
    lift n k ≠ k := by
  intro he
  have := lift_cast hn
  rw [he] at this
  omega

/-- The collision between `a^n+c` and `a^m+d`, after multiplying by the
smallest common power that clears all negative exponents. -/
def collision {F : Type} [Field F] (n m : Int) (p q c d : F) : F[X] :=
  C p * X^(lift n (shift n m)) - C q * X^(lift m (shift n m)) +
    C (p*c-q*d) * X^(shift n m)

theorem collision_degree {F : Type} [Field F] (n m : Int) (p q c d : F) :
    (collision n m p q c d).natDegree ≤ span n m := by
  have hs := shift_spec n m
  have hn : lift n (shift n m) ≤ span n m := by
    simp only [lift, span, upper, lower] at *
    omega
  have hm : lift m (shift n m) ≤ span n m := by
    simp only [lift, span, upper, lower] at *
    omega
  have hk : shift n m ≤ span n m := by
    simp only [span, upper, lower] at *
    omega
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le ((Polynomial.natDegree_C_mul_X_pow_le _ _).trans hn)
      ((Polynomial.natDegree_C_mul_X_pow_le _ _).trans hm)
  · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans hk

theorem pow_lift {F : Type} [Field F] {a : F} (ha : a ≠ 0)
    {n : Int} {k : Nat} (h : 0 ≤ n+k) : a^(lift n k) = a^n * a^k := by
  rw [← zpow_natCast, lift_cast h, zpow_add₀ ha, zpow_natCast]

theorem collision_eval {F : Type} [Field F] {a : F} (ha : a ≠ 0)
    (n m : Int) (p q c d : F) :
    (collision n m p q c d).eval a =
      (p*(a^n+c)-q*(a^m+d))*a^(shift n m) := by
  have hs := shift_spec n m
  simp only [collision, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_C_mul, Polynomial.eval_X_pow,
    pow_lift ha hs.2.1, pow_lift ha hs.2.2]
  ring

theorem collision_eval_ne_zero {F : Type} [Field F] {a : F} (ha : a ≠ 0)
    {n m : Int} {p q c d : F}
    (h : (collision n m p q c d).eval a ≠ 0) :
    p*(a^n+c) ≠ q*(a^m+d) := by
  rw [collision_eval ha] at h
  exact sub_ne_zero.mp (mul_ne_zero_iff.mp h).1

/-- Different nonconstant powers cannot have an identically zero collision.
The remaining constant/constant cases are checked by exact field arithmetic. -/
theorem collision_nonconstant {F : Type} [Field F] {n m : Int} {p q c d : F}
    (hp : p ≠ 0) (hq : q ≠ 0) (hnm : n ≠ 0 ∨ m ≠ 0)
    (hzero : collision n m p q c d = 0) : n = m ∧ p = q ∧ c = d := by
  have hs := shift_spec n m
  have heq : n = m := by
    by_contra hne
    rcases hnm with hn | hm
    · have hh := congrArg (fun f : F[X] => f.coeff (lift n (shift n m))) hzero
      have h1 := lift_ne hs.2.1 hs.2.2 hne
      have h2 := lift_ne_shift hs.2.1 hn
      simp only [collision, Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_C_mul_X_pow, ite_true, if_neg h1, if_neg h2,
        Polynomial.coeff_zero, sub_zero, add_zero] at hh
      exact hp hh
    · have hh := congrArg (fun f : F[X] => f.coeff (lift m (shift n m))) hzero
      have h1 := lift_ne hs.2.1 hs.2.2 hne
      have h2 := lift_ne_shift hs.2.2 hm
      simp only [collision, Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_C_mul_X_pow, ite_true, if_neg h1.symm, if_neg h2,
        Polynomial.coeff_zero, zero_sub, add_zero, neg_eq_zero] at hh
      exact hq hh
  subst m
  have hn : n ≠ 0 := by tauto
  have hsep := lift_ne_shift hs.2.1 hn
  have hpq : p = q := by
    have hh := congrArg (fun f : F[X] => f.coeff (lift n (shift n n))) hzero
    simpa only [collision, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul_X_pow, ite_true, if_neg hsep,
      Polynomial.coeff_zero, add_zero, sub_eq_zero] using hh
  have hcd : c = d := by
    have hh := congrArg (fun f : F[X] => f.coeff (shift n n)) hzero
    simp only [collision, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul_X_pow, if_neg hsep.symm, ite_true,
      Polynomial.coeff_zero, sub_self, zero_add, hpq, ← mul_sub] at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hq)
  exact ⟨rfl, hpq, hcd⟩

/-- Ignore identities in a root-avoidance family; all other constraints remain. -/
def guard {F : Type} [Field F] (p : F[X]) : F[X] := if p = 0 then 1 else p

theorem guard_ne_zero {F : Type} [Field F] (p : F[X]) : guard p ≠ 0 := by
  unfold guard
  split_ifs with h
  · exact one_ne_zero
  · exact h

theorem guard_degree {F : Type} [Field F] (p : F[X]) :
    (guard p).natDegree ≤ p.natDegree := by
  unfold guard
  split_ifs <;> simp

theorem of_guard_eval {F : Type} [Field F] {p : F[X]} {a : F}
    (hp : p ≠ 0) (ha : (guard p).eval a ≠ 0) : p.eval a ≠ 0 := by
  simpa only [guard, if_neg hp] using ha

end
end OptimalOTS.FreeLastPolys
