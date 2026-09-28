import Submissions.UpperLeanIsa.AffineFrames

/-! Choose one field element that guards every potential jump in a fixed layout.
The selection is independent of the input, oracle and committed memory. -/

namespace OptimalOTS.AffineFrames

open Polynomial LeanerVM.Parameters
noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Stage := Fin 14
abbrev Slot := Fin (2 ^ 18)
abbrev Cell := Fin (2 ^ 16)
abbrev MaxCell := Fin (2 ^ 32)

structure BodyDescriptor where
  stage : Stage
  entry : Slot
  firstCell : Cell

inductive SlotShape
  | trap
  | initial (firstCell : Cell)
  | body (descriptor : BodyDescriptor)

abbrev Layout := Slot → SlotShape

def initialPoly (u s c j : ℕ) : K[X] :=
  C (gpow c) * framePoly u s - C (gpow j)

theorem initialPoly_ne_zero {u s c j : ℕ} (hu : 0 < u) :
    initialPoly u s c j ≠ 0 := by
  intro h
  have hh := congrArg (fun p : K[X] => p.coeff u) h
  have hz : gpow c = 0 := by
    simpa only [initialPoly, framePoly, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_zero, if_neg (Nat.ne_of_gt hu), ite_true, add_zero,
      mul_one, sub_zero] using hh
  exact (pow_ne_zero _ g_ne_zero) hz

theorem initialPoly_degree {u s c j D : ℕ} (hu : u ≤ D) :
    (initialPoly u s c j).natDegree ≤ D := by
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  · apply le_trans (Polynomial.natDegree_C_mul_le _ _)
    apply le_trans (Polynomial.natDegree_add_le _ _)
    simpa only [Polynomial.natDegree_X_pow, Polynomial.natDegree_C, max_zero] using hu
  · simpa only [Polynomial.natDegree_C] using Nat.zero_le D

def landingPoly (L : Layout) (u : Stage) (s : Slot) (j : MaxCell) : K[X] :=
  match L s with
  | .trap => 1
  | .initial c => initialPoly (u.val + 1) s.val c.val j.val
  | .body d => if u = d.stage ∧ s = d.entry then 1
      else collisionPoly (u.val + 1) (d.stage.val + 1) s.val d.entry.val d.firstCell.val j.val

theorem landingPoly_ne_zero (L : Layout) (u : Stage) (s : Slot) (j : MaxCell) :
    landingPoly L u s j ≠ 0 := by
  unfold landingPoly
  split
  · exact one_ne_zero
  · exact initialPoly_ne_zero (Nat.succ_pos _)
  · rename_i d hd
    split
    · exact one_ne_zero
    · rename_i hwrong
      apply collision_ne_zero (Nat.succ_pos _) (Nat.succ_pos _)
      · have := s.isLt; omega
      · have := d.entry.isLt; omega
      · have := d.firstCell.isLt; omega
      · have := j.isLt; omega
      · by_cases hu : u = d.stage
        · right
          intro hs
          exact hwrong ⟨hu, Fin.ext hs⟩
        · left
          intro he
          exact hu (Fin.ext (by omega))

theorem landingPoly_degree (L : Layout) (u : Stage) (s : Slot) (j : MaxCell) :
    (landingPoly L u s j).natDegree ≤ 300 := by
  unfold landingPoly
  split
  · simp
  · exact initialPoly_degree (by have := u.isLt; omega)
  · rename_i d hd
    split
    · simp
    · exact collision_degree (by have := u.isLt; omega) (by have := d.stage.isLt; omega)

def powerPoly (i j : Fin 301) : K[X] := if i = j then 1 else X ^ i.val - X ^ j.val

theorem powerPoly_ne_zero (i j : Fin 301) : powerPoly i j ≠ 0 := by
  unfold powerPoly
  split
  · exact one_ne_zero
  · rename_i hij
    intro h
    have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
    have hh := congrArg (fun p : K[X] => p.coeff i.val) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_zero,
      if_neg hv, ite_true, sub_zero] at hh
    exact one_ne_zero hh

theorem powerPoly_degree (i j : Fin 301) : (powerPoly i j).natDegree ≤ 300 := by
  unfold powerPoly
  split
  · simp
  · apply le_trans (Polynomial.natDegree_sub_le _ _)
    simp only [Polynomial.natDegree_X_pow]
    have := i.isLt
    have := j.isLt
    omega

/-- Jump guards, nonzero frames, halt guards, distinct cost powers, and nonzero base. -/
abbrev Constraint := (Stage × Slot × MaxCell) ⊕
  (Stage × Slot) ⊕ Stage ⊕ (Fin 301 × Fin 301) ⊕ Unit

def constraints (L : Layout) : Constraint → K[X]
  | .inl (u,s,j) => landingPoly L u s j
  | .inr (.inl (u,s)) => framePoly (u.val + 1) s.val
  | .inr (.inr (.inl u)) => initialPoly (u.val + 1) (2 ^ 18 - 1) 0 0
  | .inr (.inr (.inr (.inl (i,j)))) => powerPoly i j
  | .inr (.inr (.inr (.inr _))) => X

theorem constraints_ne_zero (L : Layout) (i : Constraint) : constraints L i ≠ 0 := by
  rcases i with ⟨u,s,j⟩ | ⟨u,s⟩ | u | ⟨i,j⟩ | v
  · exact landingPoly_ne_zero L u s j
  · exact framePoly_ne_zero (Nat.succ_pos _)
  · exact initialPoly_ne_zero (Nat.succ_pos _)
  · exact powerPoly_ne_zero i j
  · exact Polynomial.X_ne_zero

theorem constraints_degree (L : Layout) (i : Constraint) :
    (constraints L i).natDegree ≤ 300 := by
  rcases i with ⟨u,s,j⟩ | ⟨u,s⟩ | u | ⟨i,j⟩ | v
  · exact landingPoly_degree L u s j
  · apply le_trans (Polynomial.natDegree_add_le _ _)
    simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_C, max_zero]
    have := u.isLt
    omega
  · exact initialPoly_degree (by have := u.isLt; omega)
  · exact powerPoly_degree i j
  · simp only [constraints, Polynomial.natDegree_X]; omega

-- `Fintype.card_unit` is applied by `rw`: under `simp` its instance unification leaves the
-- kernel a defeq check that enumerates the product type.
theorem constraint_card_bound : Fintype.card Constraint * 300 < Fintype.card K := by
  simp only [Constraint, Stage, Slot, MaxCell, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, BF64.card_bf64]
  rw [Fintype.card_unit]
  decide +kernel

/-- A checksum landing inside the bytecode must be the intended halt. -/
def exitPoly (n layer : Fin 301) (s : Slot) : K[X] :=
  if n = layer ∧ s.val = 2 ^ 18 - 1 then 1
  else C (gpow (2 ^ 18 - 1)) * X ^ n.val - C (gpow s.val) * X ^ layer.val

theorem exitPoly_ne_zero (n layer : Fin 301) (s : Slot) : exitPoly n layer s ≠ 0 := by
  unfold exitPoly
  split
  · exact one_ne_zero
  · rename_i hwrong
    intro h
    have hh := congrArg (fun p : K[X] => p.coeff n.val) h
    by_cases hn : n = layer
    · subst layer
      have he : gpow (2 ^ 18 - 1) = gpow s.val := by
        simpa only [Polynomial.coeff_sub,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,
          Polynomial.coeff_zero,ite_true,mul_one,sub_eq_zero] using hh
      have hs : s.val = 2 ^ 18 - 1 := (OptimalOTS.GenFast.gpow_injOn (by norm_num)
        (by have := s.isLt; change s.val < 2 ^ 64 - 1; omega) he).symm
      exact hwrong ⟨rfl,hs⟩
    · have hv : n.val ≠ layer.val := fun h => hn (Fin.ext h)
      have hz : gpow (2 ^ 18 - 1) = 0 := by
        simpa only [Polynomial.coeff_sub,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,
          Polynomial.coeff_zero,ite_true,if_neg hv,mul_one,mul_zero,sub_zero] using hh
      exact (pow_ne_zero _ g_ne_zero) hz

theorem exitPoly_degree (n layer : Fin 301) (s : Slot) : (exitPoly n layer s).natDegree ≤ 300 := by
  unfold exitPoly
  split
  · simp
  · apply le_trans (Polynomial.natDegree_sub_le _ _)
    apply max_le
    all_goals
      apply le_trans (Polynomial.natDegree_C_mul_le _ _)
      simp only [Polynomial.natDegree_X_pow]
      have := n.isLt
      have := layer.isLt
      omega

/-- In addition to control-flow separation, reserve the existing length word as
a distinct domain label. This needs no extra machine constant. -/
abbrev AllConstraint := Constraint ⊕ (Fin 301 × Fin 301 × Slot) ⊕ Fin 14

def allConstraints (L : Layout) : AllConstraint → K[X]
  | .inl i => constraints L i
  | .inr (.inl (n,layer,s)) => exitPoly n layer s
  | .inr (.inr n) => X ^ (n.val + 1) - C lengthK

theorem allConstraints_ne_zero (L : Layout) (i : AllConstraint) : allConstraints L i ≠ 0 := by
  rcases i with i | ⟨n,layer,s⟩ | n
  · exact constraints_ne_zero L i
  · exact exitPoly_ne_zero n layer s
  · exact power_sub_constant_ne_zero lengthK (Nat.succ_pos _)

theorem allConstraints_degree (L : Layout) (i : AllConstraint) :
    (allConstraints L i).natDegree ≤ 300 := by
  rcases i with i | ⟨n,layer,s⟩ | n
  · exact constraints_degree L i
  · exact exitPoly_degree n layer s
  · exact (power_sub_constant_degree lengthK _).trans (by have := n.isLt; omega)

theorem allConstraints_card_bound : Fintype.card AllConstraint * 300 < Fintype.card K := by
  simp only [AllConstraint,Constraint,Stage,Slot,MaxCell,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,BF64.card_bf64]
  rw [Fintype.card_unit]
  decide +kernel

theorem exists_safe_base (L : Layout) : ∃ a : K, ∀ i, (allConstraints L i).eval a ≠ 0 :=
  exists_common_nonroot (allConstraints L) 300 (allConstraints_ne_zero L)
    (allConstraints_degree L) allConstraints_card_bound

def safeBase (L : Layout) : K := Classical.choose (exists_safe_base L)

theorem safeBase_avoids (L : Layout) (i : Constraint) :
    (constraints L i).eval (safeBase L) ≠ 0 := Classical.choose_spec (exists_safe_base L) (.inl i)

theorem safeBase_exit_avoids (L : Layout) (n layer : Fin 301) (s : Slot) :
    (exitPoly n layer s).eval (safeBase L) ≠ 0 :=
  Classical.choose_spec (exists_safe_base L) (.inr (.inl (n,layer,s)))

theorem safeBase_length_ne (L : Layout) {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 14) :
    safeBase L ^ n ≠ lengthK := by
  have h := Classical.choose_spec (exists_safe_base L) (.inr (.inr ⟨n - 1, by omega⟩))
  have he : n - 1 + 1 = n := by omega
  simpa only [safeBase, allConstraints, he, Polynomial.eval_sub, Polynomial.eval_X_pow,
    Polynomial.eval_C, sub_ne_zero] using h

theorem safeBase_ne_zero (L : Layout) : safeBase L ≠ 0 := by
  have h := safeBase_avoids L (.inr (.inr (.inr (.inr ()))))
  simpa only [constraints, Polynomial.eval_X] using h

theorem safeBase_powers_injective (L : Layout) {i j : ℕ} (hi : i ≤ 300) (hj : j ≤ 300)
    (h : safeBase L ^ i = safeBase L ^ j) : i = j := by
  by_contra hne
  have he : (⟨i, by omega⟩ : Fin 301) ≠ ⟨j, by omega⟩ := fun he => hne (Fin.mk.inj he)
  have hh := safeBase_avoids L (.inr (.inr (.inr (.inl (⟨i,by omega⟩,⟨j,by omega⟩)))))
  simp only [constraints, powerPoly, if_neg he, Polynomial.eval_sub,
    Polynomial.eval_X_pow, h, sub_self, ne_eq, not_true_eq_false] at hh

theorem safeBase_frame_ne_zero (L : Layout) (u : Stage) (s : Slot) :
    safeBase L ^ (u.val + 1) + gpow s.val ≠ 0 := by
  have h := safeBase_avoids L (.inr (.inl (u,s)))
  simpa only [constraints, framePoly, Polynomial.eval_add, Polynomial.eval_X_pow,
    Polynomial.eval_C] using h

end
end OptimalOTS.AffineFrames
