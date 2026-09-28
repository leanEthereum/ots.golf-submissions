import Submissions.UpperLeanIsa.SplitWindow

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitWindow

open SplitDP

theorem list_sum_finset (ms : List ℕ) (hn : ms.Nodup) (F : ℕ → ℕ) :
    (ms.map F).sum = ∑ m ∈ ms.toFinset, F m := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.nodup_cons] at hn
    simp [hn.1, ih hn.2]

theorem dot_range (row : List ℕ) (F : ℕ → ℕ) (n : ℕ) (hl : row.length ≤ n) :
    (row.zipWith (· * ·) ((List.range n).map F)).sum =
      ∑ s ∈ Finset.range n, row.getD s 0 * F s := by
  induction n generalizing row F with
  | zero =>
    have : row = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst row
    simp
  | succ n ih =>
    cases row with
    | nil => simp
    | cons x xs =>
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.zipWith_cons_cons, List.sum_cons]
      rw [ih xs (F ∘ Nat.succ) (by simpa using Nat.le_of_succ_le_succ hl),
        Finset.sum_range_succ']
      simp [Nat.add_comm]

theorem window_range (row : List ℕ) (n : ℕ) (hl : row.length ≤ n) (a b c : ℕ) :
    window row (a - c) (b - c) =
      ∑ s ∈ Finset.range n, if a ≤ s + c ∧ s + c < b then row.getD s 0 else 0 := by
  rw [window_eq]
  calc
    _ = ∑ s ∈ Finset.Ico (a - c) (b - c),
        if s < n then row.getD s 0 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
    _ = _ := by
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      congr 1
      ext s
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
      omega

theorem stepWindow_transpose (p : List MProfile) (ms : List ℕ) (hn : ms.Nodup)
    (hm : ∀ x ∈ p, x.2.1 ∈ ms) (keys : List ℕ) (rows : List (List ℕ))
    (S : ℕ) (hl : ∀ v, (rowM keys rows v).length ≤ S + 1) (a b w : ℕ) :
    stepWindow p keys rows a b w =
      (ms.map fun m => if m ∣ w then
        ((rowM keys rows (w / m)).zipWith (· * ·)
          ((List.range (S + 1)).map fun s =>
            (p.map fun x => if x.2.1 = m ∧ a ≤ s + x.1 ∧ s + x.1 < b
              then x.2.2 * x.2.1 else 0).sum)).sum else 0).sum := by
  let term := fun (x : MProfile) (m s : ℕ) =>
    if x.2.1 = m ∧ m ∣ w ∧ a ≤ s + x.1 ∧ s + x.1 < b
      then (rowM keys rows (w / m)).getD s 0 * (x.2.2 * x.2.1) else 0
  have hx (x : MProfile) (hxp : x ∈ p) :
      (if x.2.1 ∣ w then (x.2.2 * x.2.1) *
        window (rowM keys rows (w / x.2.1)) (a - x.1) (b - x.1) else 0) =
      ∑ m ∈ ms.toFinset, ∑ s ∈ Finset.range (S + 1), term x m s := by
    have he (m : ℕ) : (∑ s ∈ Finset.range (S + 1), term x m s) =
        if x.2.1 = m then ∑ s ∈ Finset.range (S + 1), term x m s else 0 := by
      split_ifs with h
      · rfl
      · simp [term, h]
    have hcollect : (∑ m ∈ ms.toFinset, ∑ s ∈ Finset.range (S + 1), term x m s) =
        ∑ m ∈ ms.toFinset, if x.2.1 = m then
          ∑ s ∈ Finset.range (S + 1), term x m s else 0 :=
      Finset.sum_congr rfl fun m _ => he m
    rw [hcollect]
    rw [Finset.sum_ite_eq_of_mem _ _ _ (by simpa using hm x hxp)]
    by_cases hd : x.2.1 ∣ w
    · simp only [hd, if_true]
      rw [window_range _ _ (hl _) a b x.1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [term, hd, true_and]
      split_ifs <;> simp_all [Nat.mul_comm]
    · simp [term, hd]
  calc
    stepWindow p keys rows a b w =
        (p.map fun x => ∑ m ∈ ms.toFinset, ∑ s ∈ Finset.range (S + 1), term x m s).sum := by
      unfold stepWindow
      congr 1
      exact List.map_congr_left hx
    _ = ∑ m ∈ ms.toFinset, (p.map fun x =>
        ∑ s ∈ Finset.range (S + 1), term x m s).sum :=
      (sum_list_comm p ms.toFinset (fun m x => ∑ s ∈ Finset.range (S + 1), term x m s)).symm
    _ = ∑ m ∈ ms.toFinset, ∑ s ∈ Finset.range (S + 1),
        (p.map fun x => term x m s).sum := by
      apply Finset.sum_congr rfl
      intro m hmem
      exact (sum_list_comm p (Finset.range (S + 1)) (fun s x => term x m s)).symm
    _ = _ := by
      rw [list_sum_finset ms hn]
      apply Finset.sum_congr rfl
      intro m hmem
      by_cases hd : m ∣ w
      · simp only [hd, if_true]
        rw [dot_range _ _ _ (hl _)]
        apply Finset.sum_congr rfl
        intro s hs
        rw [← List.sum_map_mul_left]
        congr 1
        apply List.map_congr_left
        intro x hx
        simp only [term, hd]
        split_ifs <;> simp_all
      · simp [term, hd]

theorem rowM_length_le (keys : List ℕ) (rows : List (List ℕ)) (S : ℕ)
    (hl : ∀ row ∈ rows, row.length ≤ S) (w : ℕ) :
    (rowM keys rows w).length ≤ S := by
  rw [rowM, List.getD_eq_getElem?_getD]
  cases he : rows[keys.idxOf w]? with
  | none => simp
  | some row => exact hl row (List.mem_of_getElem? he)


end OptimalOTS.LeanIsaBaseline.Layer.SplitWindow
