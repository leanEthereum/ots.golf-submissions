import Submissions.UpperLeanIsa.SplitDPStage0

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitWindow

open SplitDP

theorem sum_list_comm {α : Type} (p : List α) (I : Finset ℕ) (F : ℕ → α → ℕ) :
    ∑ s ∈ I, (p.map (F s)).sum = (p.map fun x => ∑ s ∈ I, F s x).sum := by
  induction p with
  | nil => simp
  | cons x xs ih => simp [Finset.sum_add_distrib, ih]

theorem shift_window (F : ℕ → ℕ) (a b c : ℕ) :
    ∑ s ∈ Finset.Ico a b, (if c ≤ s then F (s - c) else 0) =
      ∑ s ∈ Finset.Ico (a - c) (b - c), F s := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun s _ => s - c)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_Ico] at hs ⊢
    omega
  · intro s hs t ht he
    simp only [Finset.mem_filter, Finset.mem_Ico] at hs ht
    omega
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    refine ⟨t + c, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  · intro s hs
    rfl

def window (row : List ℕ) (a b : ℕ) : ℕ := ((row.drop a).take (b - a)).sum

theorem window_eq (row : List ℕ) (a b : ℕ) :
    window row a b = ∑ s ∈ Finset.Ico a b, row.getD s 0 := by
  rw [window, take_sum_getD, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

def stepWindow (p : List MProfile) (keys : List ℕ) (rows : List (List ℕ))
    (a b w : ℕ) : ℕ :=
  (p.map fun x => if x.2.1 ∣ w then
    (x.2.2 * x.2.1) * window (rowM keys rows (w / x.2.1)) (a - x.1) (b - x.1)
    else 0).sum

theorem stepWindow_correct (N : ℕ → ℕ) (f g : ℕ → ℕ → ℕ)
    (p : List MProfile) (S n : ℕ) (keys : List ℕ) (rows : List (List ℕ))
    (hrec : ∀ s w, compM N f g (n + 1) s w =
      (p.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum)
    (hprev : ∀ w s, s ≤ S → (rowM keys rows w).getD s 0 = compM N f g n s w)
    (a b w : ℕ) (hb : b ≤ S + 1) :
    ∑ s ∈ Finset.Ico a b, compM N f g (n + 1) s w = stepWindow p keys rows a b w := by
  simp only [hrec]
  rw [sum_list_comm, stepWindow]
  congr 1
  apply List.map_congr_left
  intro x hx
  by_cases hd : x.2.1 ∣ w
  · simp only [hd, and_true, if_true]
    rw [window_eq, Finset.mul_sum]
    calc
      _ = ∑ s ∈ Finset.Ico a b, if x.1 ≤ s then
          (x.2.2 * x.2.1) * (rowM keys rows (w / x.2.1)).getD (s - x.1) 0 else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        split_ifs with hc
        · rw [hprev _ _ (by have := (Finset.mem_Ico.mp hs).2; omega)]
        · rfl
      _ = _ := shift_window (fun s =>
        (x.2.2 * x.2.1) * (rowM keys rows (w / x.2.1)).getD s 0) a b x.1
  · simp [hd]


theorem stepWindow_not_mem (p : List MProfile) (keys next : List ℕ)
    (rows : List (List ℕ)) (hlen : rows.length ≤ keys.length)
    (hclosed : ∀ x ∈ p, ∀ w ∈ keys, w * x.2.1 ∈ next)
    (a b w : ℕ) (hw : w ∉ next) : stepWindow p keys rows a b w = 0 := by
  unfold stepWindow
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  split_ifs with hd
  · have hn : w / x.2.1 ∉ keys := by
      intro hm
      have hc := hclosed x hx _ hm
      rw [Nat.div_mul_cancel hd] at hc
      exact hw hc
    rw [rowM_not_mem hlen hn]
    simp [window]
  · rfl

theorem map_idxOf (keys : List ℕ) (F : ℕ → ℕ) {w : ℕ} (hw : w ∈ keys) :
    (keys.map F).getD (keys.idxOf w) 0 = F w := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf hw, Option.map_some, Option.getD_some]

theorem map_nat_append_eq (f : ℕ → ℕ) (a b ra rb : List ℕ)
    (ha : a.map f = ra) (hb : b.map f = rb) : (a ++ b).map f = ra ++ rb := by
  rw [List.map_append]
  exact congrArg₂ List.append ha hb

end OptimalOTS.LeanIsaBaseline.Layer.SplitWindow
