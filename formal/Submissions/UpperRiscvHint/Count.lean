import Mathlib

/-!
# Counting digit tuples of mixed widths

`compW w n s` is the number of tuples `(c_0, …, c_{n-1})` with `c_k < 2 ^ w k` and sum `s`
(`card_compW`). Concrete values are certified without `native_decide`: `compW` is evaluated
through a polynomial-size table of partial sums (`compTableW`), which agrees with `compW` by
induction (`compTableW_getD`) and is computed by kernel reduction.
-/

namespace OptimalOTS

namespace Forest

variable (w : ℕ → ℕ)

/-- Number of `(c : (k : Fin n) → Fin (2 ^ w k))` with `∑ k, (c k).val = s`; the last digit is
peeled first. -/
def compW : ℕ → ℕ → ℕ
  | 0, s => if s = 0 then 1 else 0
  | n + 1, s => ∑ v ∈ Finset.range (2 ^ w n), if v ≤ s then compW n (s - v) else 0

theorem card_compW (n s : ℕ) :
    (Finset.univ.filter fun c : (k : Fin n) → Fin (2 ^ w k) => ∑ k, (c k).val = s).card =
      compW w n s := by
  induction n generalizing s with
  | zero =>
    rw [compW]
    split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]
  | succ n ih =>
    rw [compW, ← Fin.sum_univ_eq_sum_range (fun v => if v ≤ s then compW w n (s - v) else 0)]
    simp only [← ih]
    rw [Finset.card_filter, ← (Fin.snocEquiv fun k : Fin (n + 1) => Fin (2 ^ w k)).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Fin.snocEquiv_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    split_ifs with hv
    · rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact if_congr (by simp only [Fin.val_last]; omega) rfl rfl
    · refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      simp only [Fin.val_last]
      omega

/-- `compTableW w S n` is the list `[compW w n 0, …, compW w n S]`. -/
def compTableW (S : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate S 0
  | n + 1 =>
    (List.range (S + 1)).map fun s =>
      ((List.range (2 ^ w n)).map fun v => if v ≤ s then (compTableW S n).getD (s - v) 0 else 0).sum

theorem sum_map_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ v ∈ Finset.range m, f v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

theorem compTableW_getD (S n s : ℕ) (hs : s ≤ S) : (compTableW w S n).getD s 0 = compW w n s := by
  induction n generalizing s with
  | zero =>
    rw [compTableW, compW]
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_replicate,
        Nat.succ_ne_zero, if_false]
      split_ifs <;> rfl
  | succ n ih =>
    rw [compTableW, compW, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some, sum_map_range]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · exact ih (s - v) (by omega)
    · rfl

end Forest

end OptimalOTS
