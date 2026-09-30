import Submissions.UpperLeanIsa.FreeLastPolys
import Submissions.UpperLeanIsa.AffineSelect

/-! A fixed base for signed-power landing constraints. The construction uses
the existing charged-cost bound 16, so the final product exponent ranges from
-77 through 131. The interface separates the 2079 free slots from all other
slots, which is essential to the weighted root bound. -/
namespace OptimalOTS.FreeLastSelect
open Polynomial LeanerVM.Parameters OptimalOTS.FreeLastPolys
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev GroupSlot := Fin 262144
abbrev FreeSlot := Fin 2079
abbrev TargetSlot := GroupSlot ⊕ FreeSlot
abbrev MaxCell := Fin (2^32)
abbrev Flow := Fin 13 ⊕ Fin 209 ⊕ Unit

structure Target where
  exponent : Int
  constant : K
  firstCell : Nat

structure Layout where
  group : GroupSlot → Target
  free : FreeSlot → Target
  group_bounds : ∀ s, 0 ≤ (group s).exponent ∧ (group s).exponent ≤ 12
  free_bounds : ∀ s, -63 ≤ (free s).exponent ∧ (free s).exponent ≤ 0

def Layout.target (L : Layout) : TargetSlot → Target
  | .inl s => L.group s
  | .inr s => L.free s

def address : TargetSlot → Nat
  | .inl s => s.val
  | .inr s => 260064+s.val

def exponent : Flow → Int
  | .inl u => if u.val < 11 then (u.val+1 : Nat) else 0
  | .inr (.inl n) => (n.val : Int)-77
  | .inr (.inr _) => 0

def constant (f : Flow) (s : Nat) : K := match f with
  | .inl u => if u.val = 12 then AffineFrames.lengthK+gpow s-1 else gpow s
  | .inr (.inl _) => gpow s
  | .inr (.inr _) => 0

def groupDegree (n : Int) : Nat := (max n 12 - min n 0).toNat
def freeDegree (n : Int) : Nat := (max n 0 - min n (-63)).toNat

theorem group_span {n m : Int} (hm : 0 ≤ m ∧ m ≤ 12) :
    span n m ≤ groupDegree n := by
  simp only [span, upper, lower, groupDegree]
  omega

theorem free_span {n m : Int} (hm : -63 ≤ m ∧ m ≤ 0) :
    span n m ≤ freeDegree n := by
  simp only [span, upper, lower, freeDegree]
  omega

def landing (L : Layout) (f : Flow) (s : TargetSlot) (j : MaxCell) : K[X] :=
  let d := L.target s
  collision (exponent f) d.exponent (gpow d.firstCell) (gpow j.val)
    (constant f (address s)) d.constant

def landingDegree (f : Flow) : TargetSlot → Nat
  | .inl _ => groupDegree (exponent f)
  | .inr _ => freeDegree (exponent f)

theorem landing_degree (L : Layout) (f : Flow) (s : TargetSlot) (j : MaxCell) :
    (landing L f s j).natDegree ≤ landingDegree f s := by
  apply (collision_degree _ _ _ _ _ _).trans
  cases s with
  | inl s => exact group_span (L.group_bounds s)
  | inr s => exact free_span (L.free_bounds s)

def framePoly (d : Target) : K[X] := collision d.exponent 0 1 0 d.constant 0
def haltPoly (f : Flow) : K[X] :=
  collision (exponent f) 0 1 0 (constant f 262143-1) 0

theorem target_bounds (L : Layout) (s : TargetSlot) :
    -63 ≤ (L.target s).exponent ∧ (L.target s).exponent ≤ 12 := by
  cases s with
  | inl s => dsimp only [Layout.target]; have := L.group_bounds s; exact ⟨by omega, this.2⟩
  | inr s => dsimp only [Layout.target]; have := L.free_bounds s; exact ⟨this.1, by omega⟩

theorem exponent_bounds (f : Flow) : -77 ≤ exponent f ∧ exponent f ≤ 131 := by
  rcases f with u | n | _
  · simp only [exponent]; split_ifs <;> have := u.isLt <;> constructor <;> omega
  · have := n.isLt; simp only [exponent]; constructor <;> omega
  · simp [exponent]

theorem span_zero_bound {n : Int} (hn : -300 ≤ n ∧ n ≤ 300) : span n 0 ≤ 300 := by
  simp only [span, upper, lower]
  omega

abbrev Constraint := (Flow × TargetSlot × MaxCell) ⊕ TargetSlot ⊕ Flow ⊕
  (Fin 301 × Fin 301) ⊕ Fin 14 ⊕ Unit

def constraints (L : Layout) : Constraint → K[X]
  | .inl (f,s,j) => guard (landing L f s j)
  | .inr (.inl s) => guard (framePoly (L.target s))
  | .inr (.inr (.inl f)) => guard (haltPoly f)
  | .inr (.inr (.inr (.inl (i,j)))) => AffineFrames.powerPoly i j
  | .inr (.inr (.inr (.inr (.inl i)))) => X^(i.val+1)-C AffineFrames.lengthK
  | .inr (.inr (.inr (.inr (.inr _)))) => X

def degree : Constraint → Nat
  | .inl x => landingDegree x.1 x.2.1
  | .inr _ => 300

theorem constraints_ne_zero (L : Layout) (i : Constraint) : constraints L i ≠ 0 := by
  rcases i with ⟨f,s,j⟩ | s | f | ⟨i,j⟩ | i | _
  · exact guard_ne_zero _
  · exact guard_ne_zero _
  · exact guard_ne_zero _
  · exact AffineFrames.powerPoly_ne_zero i j
  · exact AffineFrames.power_sub_constant_ne_zero _ (Nat.succ_pos _)
  · exact Polynomial.X_ne_zero

theorem constraints_degree (L : Layout) (i : Constraint) :
    (constraints L i).natDegree ≤ degree i := by
  rcases i with ⟨f,s,j⟩ | s | f | ⟨i,j⟩ | i | _
  · exact (guard_degree _).trans (landing_degree L f s j)
  · apply (guard_degree _).trans ((collision_degree _ _ _ _ _ _).trans _)
    have h := target_bounds L s
    exact span_zero_bound ⟨by omega, by omega⟩
  · apply (guard_degree _).trans ((collision_degree _ _ _ _ _ _).trans _)
    have h := exponent_bounds f
    exact span_zero_bound ⟨by omega, by omega⟩
  · exact AffineFrames.powerPoly_degree i j
  · change (X^(i.val+1)-C AffineFrames.lengthK : K[X]).natDegree ≤ 300
    exact (AffineFrames.power_sub_constant_degree _ _).trans (by have := i.isLt; omega)
  · change (X : K[X]).natDegree ≤ 300; simp

def totalDegrees : Nat :=
  (∑ f : Flow, (262144*groupDegree (exponent f)+2079*freeDegree (exponent f)))*2^32 +
    (262144+2079+223+301*301+14+1)*300

theorem address_degree_sum (f : Flow) (s : TargetSlot) :
    (∑ _j : MaxCell, landingDegree f s) = 2^32 * landingDegree f s := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

theorem flow_degree_sum (f : Flow) :
    (∑ sj : TargetSlot × MaxCell, landingDegree f sj.1) =
      (262144*groupDegree (exponent f)+2079*freeDegree (exponent f))*2^32 := by
  rw [Fintype.sum_prod_type]
  simp_rw [address_degree_sum]
  rw [Fintype.sum_sum_type]
  simp only [landingDegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  omega

theorem flow_card : Fintype.card Flow = 223 := by
  simp only [Flow, Fintype.card_sum, Fintype.card_fin]
  rw [Fintype.card_unit]

theorem remaining_card : Fintype.card
    (TargetSlot ⊕ Flow ⊕ (Fin 301 × Fin 301) ⊕ Fin 14 ⊕ Unit) = 355062 := by
  simp only [TargetSlot, GroupSlot, FreeSlot, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, flow_card]
  rw [Fintype.card_unit]

theorem degree_left : (fun x : Flow × TargetSlot × MaxCell => degree (.inl x)) =
    (fun x => landingDegree x.1 x.2.1) := by funext x; rfl

theorem degree_right :
    (fun x : TargetSlot ⊕ Flow ⊕ (Fin 301 × Fin 301) ⊕ Fin 14 ⊕ Unit => degree (.inr x)) =
      (fun _ => 300) := by funext x; rfl

theorem degree_sum : (∑ i : Constraint, degree i) = totalDegrees := by
  rw [Fintype.sum_sum_type, degree_left, degree_right]
  rw [Fintype.sum_prod_type]
  simp_rw [flow_degree_sum]
  rw [Finset.sum_const, Finset.card_univ, remaining_card, nsmul_eq_mul, Nat.cast_id,
    ← Finset.sum_mul]
  rfl

theorem totalDegrees_lt_field : totalDegrees < Fintype.card K := by
  rw [BF64.card_bf64]
  decide +kernel

theorem totalDegrees_value : totalDegrees = 14637086839355824200 := by decide +kernel

theorem exists_base (L : Layout) : ∃ a : K, ∀ i, (constraints L i).eval a ≠ 0 :=
  FreeLastResearch.exists_common_nonroot_weighted (constraints L) degree
    (constraints_ne_zero L) (constraints_degree L) (by rw [degree_sum]; exact totalDegrees_lt_field)

def base (L : Layout) : K := Classical.choose (exists_base L)

theorem avoids (L : Layout) (i : Constraint) : (constraints L i).eval (base L) ≠ 0 :=
  Classical.choose_spec (exists_base L) i

theorem base_ne_zero (L : Layout) : base L ≠ 0 := by
  simpa only [constraints, Polynomial.eval_X] using
    avoids L (.inr (.inr (.inr (.inr (.inr ())))))

theorem landing_avoids (L : Layout) (f : Flow) (s : TargetSlot) (j : MaxCell)
    (h : landing L f s j ≠ 0) : (landing L f s j).eval (base L) ≠ 0 :=
  of_guard_eval h (avoids L (.inl (f,s,j)))

/-- A cross-multiplied successful read involving a nonconstant frame forces
the exponent and both coefficients to match exactly. Constant landings require
the separate checked finite guards. -/
theorem landing_exact (L : Layout) (f : Flow) (s : TargetSlot) (j : MaxCell)
    (hn : exponent f ≠ 0 ∨ (L.target s).exponent ≠ 0)
    (hread : gpow (L.target s).firstCell *
      ((base L)^(exponent f)+constant f (address s)) =
      gpow j.val * ((base L)^((L.target s).exponent)+(L.target s).constant)) :
    exponent f = (L.target s).exponent ∧
      gpow (L.target s).firstCell = gpow j.val ∧
      constant f (address s) = (L.target s).constant := by
  have hz : landing L f s j = 0 := by
    by_contra h
    have hne := landing_avoids L f s j h
    rw [landing, collision_eval (base_ne_zero L), hread, sub_self, zero_mul] at hne
    exact hne rfl
  exact collision_nonconstant (pow_ne_zero _ g_ne_zero) (pow_ne_zero _ g_ne_zero) hn hz

theorem read_exact (L : Layout) (f : Flow) (s : TargetSlot) (j : MaxCell)
    (hn : exponent f ≠ 0 ∨ (L.target s).exponent ≠ 0)
    (hd : (base L)^((L.target s).exponent)+(L.target s).constant ≠ 0)
    (hread : ((base L)^(exponent f)+constant f (address s)) *
      (gpow (L.target s).firstCell /
        ((base L)^((L.target s).exponent)+(L.target s).constant)) = gpow j.val) :
    exponent f = (L.target s).exponent ∧
      gpow (L.target s).firstCell = gpow j.val ∧
      constant f (address s) = (L.target s).constant := by
  apply landing_exact L f s j hn
  apply (div_eq_iff hd).mp
  simpa only [mul_div_assoc, mul_comm] using hread

theorem frame_nonzero (L : Layout) (s : TargetSlot)
    (hp : framePoly (L.target s) ≠ 0) :
    (base L)^((L.target s).exponent)+(L.target s).constant ≠ 0 := by
  have h := of_guard_eval hp (avoids L (.inr (.inl s)))
  rw [framePoly, collision_eval (base_ne_zero L)] at h
  simpa only [one_mul, zero_mul, sub_zero] using (mul_ne_zero_iff.mp h).1

theorem framePoly_ne_zero (d : Target) (hd : d.exponent ≠ 0) : framePoly d ≠ 0 := by
  intro hz
  have hs := shift_spec d.exponent 0
  have hsep := lift_ne_shift hs.2.1 hd
  have hh := congrArg (fun f : K[X] => f.coeff (lift d.exponent (shift d.exponent 0))) hz
  simp only [framePoly, collision, map_zero, zero_mul, sub_zero, one_mul,
    Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,
    ite_true, if_neg hsep, Polynomial.coeff_zero, add_zero] at hh
  exact one_ne_zero hh

theorem nonconstant_frame_nonzero (L : Layout) (s : TargetSlot)
    (hd : (L.target s).exponent ≠ 0) :
    (base L)^((L.target s).exponent)+(L.target s).constant ≠ 0 :=
  frame_nonzero L s (framePoly_ne_zero _ hd)

theorem powers_injective (L : Layout) {i j : Nat} (hi : i ≤ 300) (hj : j ≤ 300)
    (h : base L ^ i = base L ^ j) : i = j := by
  by_contra hne
  have he : (⟨i, by omega⟩ : Fin 301) ≠ ⟨j, by omega⟩ := fun he => hne (Fin.mk.inj he)
  have hh := avoids L (.inr (.inr (.inr (.inl (⟨i,by omega⟩,⟨j,by omega⟩)))))
  simp only [constraints, AffineFrames.powerPoly, if_neg he, Polynomial.eval_sub,
    Polynomial.eval_X_pow, h, sub_self, ne_eq, not_true_eq_false] at hh

theorem length_ne (L : Layout) {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 14) :
    base L ^ n ≠ AffineFrames.lengthK := by
  have h := avoids L (.inr (.inr (.inr (.inr (.inl ⟨n-1,by omega⟩)))))
  have he : n-1+1 = n := by omega
  simpa only [constraints, he, Polynomial.eval_sub, Polynomial.eval_X_pow,
    Polynomial.eval_C, sub_ne_zero] using h

end
end OptimalOTS.FreeLastSelect
