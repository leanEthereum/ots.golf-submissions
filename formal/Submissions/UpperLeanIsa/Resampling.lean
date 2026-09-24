import Submissions.UpperLeanIsa.SecondPreimages

/-! Finite-record resampling. The change-of-variables argument is adapted from
`UpperRiscv.Resample`, generalized to any coordinate with a replacement operation. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleComp.EvalDist OracleSpec ENNReal
open scoped Classical
noncomputable section

attribute [local irreducible] hashBits

local instance : DecidableEq Record := Classical.decEq Record

theorem sum_resample {R V : Type} [Fintype V] [Nonempty V]
    (get : R → V) (put : R → V → R)
    (hget : ∀ r v, get (put r v) = v)
    (hrestore : ∀ r v, put (put r v) (get r) = r)
    (S : Finset R) (hS : ∀ r ∈ S, ∀ v, put r v ∈ S) (f : R → ℝ≥0∞) :
    ∑ r ∈ S, f r = ∑ r ∈ S, (Fintype.card V : ℝ≥0∞)⁻¹ * ∑ v, f (put r v) := by
  have key : ∑ r ∈ S, ∑ v, f (put r v) = ∑ r ∈ S, ∑ _v : V, f r := by
    calc
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset V), f (put p.1 p.2) :=
        (Finset.sum_product' S Finset.univ (fun r v => f (put r v))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset V), f p.1 := by
        refine Finset.sum_nbij' (fun p => (put p.1 p.2, get p.1))
          (fun p => (put p.1 p.2, get p.1)) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p _
          exact Prod.ext (hrestore _ _) (hget _ _)
        · intro p _
          exact Prod.ext (hrestore _ _) (hget _ _)
        · intro p _
          rfl
      _ = _ := Finset.sum_product' S Finset.univ (fun r _ => f r)
  have hc0 : (Fintype.card V : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card V : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

def Record.putSource (ξ : Record) (i : Fin 39) (x : Word) : Record :=
  (Function.update ξ.1 i x, ξ.2)

def Record.putAnswer (ξ : Record) (a : HashLocation) (x : BitVec hashBits) : Record :=
  (ξ.1, Function.update ξ.2 a x)

theorem putSource_get (ξ : Record) (i : Fin 39) (x : Word) : (ξ.putSource i x).1 i = x :=
  Function.update_self _ _ _

theorem putAnswer_get (ξ : Record) (a : HashLocation) (x : BitVec hashBits) :
    (ξ.putAnswer a x).2 a = x := Function.update_self _ _ _

theorem putSource_restore (ξ : Record) (i : Fin 39) (x : Word) :
    (ξ.putSource i x).putSource i (ξ.1 i) = ξ := by
  apply Prod.ext
  · funext j
    by_cases h : j = i <;> simp [Record.putSource, h]
  · rfl

theorem putAnswer_restore (ξ : Record) (a : HashLocation) (x : BitVec hashBits) :
    (ξ.putAnswer a x).putAnswer a (ξ.2 a) = ξ := by
  apply Prod.ext
  · rfl
  · funext b
    by_cases h : b = a <;> simp [Record.putAnswer, h]

abbrev Cut := Fin 39 → Fin 128
abbrev PublicData := (Fin 39 → Option Word) × (HashLocation → Option (BitVec hashBits))

def beforeSigning : Cut := fun _ => 127

def afterSigning (m : Message) : Cut := fun i => ⟨digit m i, by have := digit_le m i; omega⟩

/-- The analysis exposes at least the signature and all information needed to
recompute its suffixes. Extra revealed data only strengthens the adversary. -/
def publicData (d : Cut) (ξ : Record) : PublicData :=
  (fun i => if (d i).val = 0 then some (ξ.1 i) else none,
   fun a => match a with
     | .inl (i, j) => if (d i).val ≤ j.val + 1 then some (ξ.2 a) else none
     | .inr _ => some (ξ.2 a))

def finiteFiber {R V : Type} [Fintype R] (f : R → V) (v : V) : Finset R :=
  @Finset.filter R (fun r => f r = v) (fun _ => Classical.propDecidable _) Finset.univ

theorem mem_finiteFiber {R V : Type} [Fintype R] (f : R → V) (v : V) (r : R) :
    r ∈ finiteFiber f v ↔ f r = v := by
  simp only [finiteFiber, Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] finiteFiber

def publicFiber (d : Cut) (v : PublicData) : Finset Record := finiteFiber (publicData d) v

theorem publicData_putSource (d : Cut) (ξ : Record) (i : Fin 39) (x : Word)
    (hi : 0 < (d i).val) : publicData d (ξ.putSource i x) = publicData d ξ := by
  apply Prod.ext
  · funext j
    by_cases h : j = i
    · subst j
      simp only [publicData, if_neg (Nat.ne_of_gt hi)]
    · simp [publicData, Record.putSource, Function.update_of_ne h]
  · rfl

theorem publicData_putAnswer (d : Cut) (ξ : Record) (i : Fin 39) (j : Fin 127)
    (x : BitVec hashBits) (hj : j.val + 1 < (d i).val) :
    publicData d (ξ.putAnswer (.inl (i, j)) x) = publicData d ξ := by
  apply Prod.ext
  · rfl
  · funext a
    by_cases h : a = .inl (i, j)
    · subst a
      simp [publicData, not_le_of_gt hj]
    · cases a with
      | inl b => simp [publicData, Record.putAnswer, Function.update_of_ne h]
      | inr b => simp [publicData, Record.putAnswer]

attribute [local irreducible] publicData

theorem mem_publicFiber (d : Cut) (v : PublicData) (ξ : Record) :
    ξ ∈ publicFiber d v ↔ publicData d ξ = v :=
  mem_finiteFiber (publicData d) v ξ

attribute [local irreducible] publicFiber

theorem fiber_closed_source (d : Cut) (v : PublicData) (i : Fin 39) (hi : 0 < (d i).val) :
    ∀ ξ ∈ publicFiber d v, ∀ x, ξ.putSource i x ∈ publicFiber d v := by
  intro ξ h x
  apply (mem_publicFiber _ _ _).mpr
  rw [publicData_putSource d ξ i x hi]
  exact (mem_publicFiber _ _ _).mp h

theorem fiber_closed_answer (d : Cut) (v : PublicData) (i : Fin 39) (j : Fin 127)
    (hj : j.val + 1 < (d i).val) :
    ∀ ξ ∈ publicFiber d v, ∀ x, ξ.putAnswer (.inl (i, j)) x ∈ publicFiber d v := by
  intro ξ h x
  apply (mem_publicFiber _ _ _).mpr
  rw [publicData_putAnswer d ξ i j x hj]
  exact (mem_publicFiber _ _ _).mp h

end
end OptimalOTS.LeanIsaBaseline
