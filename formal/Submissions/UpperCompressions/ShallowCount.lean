import Mathlib

/-!
# Counting positions for the exploratory shallow forest

`comp n s` is the number of tuples `(c_1, …, c_n) ∈ {0, …, 18}^n` with sum `s` (`card_comp`).

Concrete values are certified without `native_decide`: `comp` is evaluated through a
polynomial-size table of partial sums (`compTable`), which agrees with `comp` by induction
(`compTable_getD`) and is computed by kernel reduction.
-/

namespace OptimalOTS

namespace ShallowResearch

/-- Number of `(c : Fin n → Fin 19)` with `∑ i, (c i).val = s`. -/
def comp : ℕ → ℕ → ℕ
  | 0, s => if s = 0 then 1 else 0
  | n + 1, s => ∑ v ∈ Finset.range 19, if v ≤ s then comp n (s - v) else 0

theorem card_comp (n s : ℕ) :
    (Finset.univ.filter fun c : Fin n → Fin 19 => ∑ i, (c i).val = s).card = comp n s := by
  induction n generalizing s with
  | zero =>
    rw [comp]
    split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]
  | succ n ih =>
    rw [comp, ← Fin.sum_univ_eq_sum_range (fun v => if v ≤ s then comp n (s - v) else 0) 19]
    simp only [← ih]
    rw [Finset.card_filter, ← (Fin.consEquiv fun _ => Fin 19).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    split_ifs with hv
    · rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact if_congr (by omega) rfl rfl
    · refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      omega

/-! ### Kernel-checkable evaluation of `comp`

`comp` as written unfolds exponentially, so the concrete values are obtained from the row-by-row
dynamic programming table `compTable S n = [comp n 0, …, comp n S]`, which is computed by structural
recursion on lists and therefore reduces in the kernel in polynomial time. -/

/-- `compTable S n` is the list `[comp n 0, comp n 1, …, comp n S]`. -/
def compTable (S : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate S 0
  | n + 1 =>
    (List.range (S + 1)).map fun s =>
      ((List.range 19).map fun v => if v ≤ s then (compTable S n).getD (s - v) 0 else 0).sum

theorem sum_map_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ v ∈ Finset.range m, f v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

theorem compTable_getD (S n s : ℕ) (hs : s ≤ S) : (compTable S n).getD s 0 = comp n s := by
  induction n generalizing s with
  | zero =>
    rw [compTable, comp]
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_replicate,
        Nat.succ_ne_zero, if_false]
      split_ifs <;> rfl
  | succ n ih =>
    rw [compTable, comp, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some, sum_map_range]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with h
    · exact ih (s - v) (by omega)
    · rfl

/-- Exact coefficient for the 102-compression numerical candidate. -/
theorem comp_36_84 : comp 36 84 = 1588422833690542979003596657572 := by
  rw [← compTable_getD 84 36 84 le_rfl]
  decide +kernel

/-- Exact coefficient for 36 length-18 chains at total reconstruction cost 85. -/
theorem comp_36_85 : comp 36 85 = 2237827609476623676586919095944 := by
  rw [← compTable_getD 85 36 85 le_rfl]
  decide +kernel

/-- Number of choices: six of eighteen groups are disclosed, and the remaining
36 chains have total cost 85. Realizing these choices as a secure scheme is a
separate obligation; this file proves only the combinatorial count. -/
theorem single_shape_count :
    Nat.choose 18 6 * comp 36 85 =
      41543031742324041932159566097104416 := by
  rw [comp_36_85]
  decide +kernel

theorem single_shape_ge : 2 ^ 115 ≤ Nat.choose 18 6 * comp 36 85 := by
  rw [single_shape_count]
  norm_num

/-- The smaller cost layer admits the acceptance fraction 45 / 524288 when
indices are uniform 128-bit words. Availability and security are separate proofs. -/
theorem single_shape_102_count :
    Nat.choose 18 6 * comp 36 84 =
      29487481484631239862222768351166608 := by
  rw [comp_36_84]
  decide +kernel

theorem single_shape_102_ge : 45 * 2 ^ 109 ≤ Nat.choose 18 6 * comp 36 84 := by
  rw [single_shape_102_count]
  norm_num

#print axioms single_shape_ge
#print axioms single_shape_102_ge

end ShallowResearch

end OptimalOTS
