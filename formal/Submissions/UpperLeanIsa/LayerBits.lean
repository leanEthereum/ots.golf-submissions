import OptimalOTS.LeanIsaMachine
import Submissions.UpperLeanIsa.IUB

/-!
# Bit-string and query-layout lemmas for layer schemes

Copies of the record's `Wire` / `QueryLayout` round-trip lemmas that do not depend on the old
Winternitz scheme, and an expectation bound over the support.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

theorem length_bits {n : ℕ} (x : BitVec n) : (toBits x).length = n :=
  List.length_ofFn

private theorem fold_bits_testBit (xs : List Bool) (i : ℕ) :
    (xs.foldr (fun (b : Bool) (a : ℕ) => b.toNat + 2 * a) 0).testBit i = xs.getD i false := by
  induction xs generalizing i with
  | nil => simp
  | cons b xs ih =>
    cases i with
    | zero => cases b <;> simp [Nat.testBit_zero]
    | succ i =>
      rw [List.foldr_cons, Nat.testBit_succ, List.getD_cons_succ, ← ih]
      congr 1
      cases b <;> simp
      omega

theorem ofBits_bits {n : ℕ} (x : BitVec n) : ofBits n (toBits x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, toBits]
  rw [fold_bits_testBit]
  simp [hi, List.getD_eq_getElem?_getD]

theorem bits_ofBits {n : ℕ} (xs : List Bool) (h : xs.length = n) :
    toBits (ofBits n xs) = xs := by
  apply List.ext_getElem
  · rw [length_bits, h]
  · intro i h₁ h₂
    rw [length_bits] at h₁
    simp only [toBits, List.getElem_ofFn, ofBits, BitVec.getLsbD_ofNat]
    rw [fold_bits_testBit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
    simp [h₁]

theorem bits_injective {n : ℕ} : Function.Injective (@toBits n) := by
  intro x y h
  exact (ofBits_bits x).symm.trans ((congrArg (ofBits n) h).trans (ofBits_bits y))

theorem hashInput_bits (cv : BitVec 256) (block : BitVec 512) (md : BitVec 128) :
    toBits (LeanIsa.hashInput cv block md) = toBits cv ++ toBits block ++ toBits md := by
  apply bits_ofBits
  simp only [List.length_append, length_bits]

theorem hashInput_eq_iff (cv cv' : BitVec 256) (block block' : BitVec 512)
    (md md' : BitVec 128) :
    LeanIsa.hashInput cv block md = LeanIsa.hashInput cv' block' md' ↔
      cv = cv' ∧ block = block' ∧ md = md' := by
  constructor
  · intro h
    have hb := congrArg toBits h
    rw [hashInput_bits, hashInput_bits] at hb
    obtain ⟨hab, hc⟩ := List.append_inj hb (by simp only [List.length_append, length_bits])
    obtain ⟨ha, hb⟩ := List.append_inj hab (by simp only [length_bits])
    exact ⟨bits_injective ha, bits_injective hb, bits_injective hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Queries with different metadata are different. -/
theorem hashInput_ne_of_md_ne {cv cv' : BitVec 256} {block block' : BitVec 512}
    {md md' : BitVec 128} (h : md ≠ md') :
    (⟨896, LeanIsa.hashInput cv block md⟩ : Query) ≠ ⟨896, LeanIsa.hashInput cv' block' md'⟩ := by
  intro hq
  have := ((hashInput_eq_iff _ _ _ _ _ _).mp (eq_of_heq (Sigma.mk.inj hq).2)).2.2
  exact h this

/-- An expectation is bounded by a bound on its support. -/
theorem E_le_of_support {α : Type} (p : ProbComp α) {g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x ∈ support p, g x ≤ c) : E p g ≤ c := by
  calc E p g ≤ E p (fun _ => c) := by
        rw [E, E, expectedValue_def, expectedValue_def]
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support p
        · exact mul_le_mul_right (h x hx) _
        · rw [probOutput_eq_zero_of_not_mem_support hx]; simp
    _ ≤ c := E_const_le p c

end OptimalOTS.LeanIsaBaseline.Layer
