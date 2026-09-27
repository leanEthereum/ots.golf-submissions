import Submissions.UpperRiscvHint.Count

/-! Exact counting for the pair alphabet with every pair sum at most 24. -/
namespace OptimalOTS.PairCode

def cap (_q : ℕ) : ℕ := 24

abbrev Pair := Fin 16 × Fin 16

def weight (p : Pair) : ℕ := p.1.val + p.2.val

def multiplicity (s : ℕ) : ℕ := if s < 16 then s + 1 else 31 - s

theorem weight_lt (p : Pair) : weight p < 31 := by
  have ha := p.1.isLt
  have hb := p.2.isLt
  unfold weight
  omega

theorem multiplicity_eq : ∀ s : Fin 31,
    ((Finset.univ : Finset Pair).filter (fun p => weight p = s.val)).card =
      multiplicity s.val := by
  decide +kernel

theorem sum_weight (f : ℕ → ℕ) :
    (∑ p : Pair, f (weight p)) = ∑ s ∈ Finset.range 31, multiplicity s * f s := by
  have regroup := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset Pair)) (t := Finset.range 31)
    (g := weight) (f := fun p => f (weight p))
    (fun p _ => Finset.mem_range.mpr (weight_lt p))
  rw [← regroup]
  refine Finset.sum_congr rfl fun s hs => ?_
  have eqf : ∀ p ∈ Finset.univ.filter (fun p : Pair => weight p = s),
      f (weight p) = f s := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl eqf, Finset.sum_const, nsmul_eq_mul,
    multiplicity_eq ⟨s, Finset.mem_range.mp hs⟩]
  rfl

def Allowed {n : ℕ} (c : Fin n → Pair) : Prop := ∀ q, weight (c q) ≤ cap q.val

instance {n : ℕ} : DecidablePred (@Allowed n) := fun _ => by unfold Allowed; infer_instance

def tuples (n s : ℕ) : Finset (Fin n → Pair) :=
  Finset.univ.filter fun c => Allowed c ∧ ∑ q, weight (c q) = s

def count : ℕ → ℕ → ℕ
  | 0, s => if s = 0 then 1 else 0
  | n+1, s => ∑ v ∈ Finset.range 31,
      multiplicity v * if v ≤ cap n ∧ v ≤ s then count n (s-v) else 0

theorem allowed_snoc {n : ℕ} (c : Fin n → Pair) (p : Pair) :
    Allowed (Fin.snoc c p) ↔ Allowed c ∧ weight p ≤ cap n := by
  simp only [Allowed, Fin.forall_fin_succ', Fin.snoc_last, Fin.snoc_castSucc,
    Fin.val_last, Fin.val_castSucc]

theorem tuples_card (n s : ℕ) : (tuples n s).card = count n s := by
  induction n generalizing s with
  | zero =>
    by_cases hs : s = 0
    · subst s; simp [tuples, Allowed, count]
    · simp [tuples, Allowed, count, hs, Ne.symm hs]
  | succ n ih =>
    rw [count, ← sum_weight]
    simp only [tuples, Finset.card_filter] at ih ⊢
    rw [← (Fin.snocEquiv fun _ : Fin (n+1) => Pair).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Fin.snocEquiv_apply, Allowed, Fin.forall_fin_succ', Fin.sum_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last]
    split_ifs with hp
    · rw [← ih]
      refine Finset.sum_congr rfl fun c _ => ?_
      apply if_congr _ rfl rfl
      constructor
      · rintro ⟨⟨hc, _⟩, hs⟩
        exact ⟨hc, by omega⟩
      · rintro ⟨hc, hs⟩
        exact ⟨⟨hc, hp.1⟩, by omega⟩
    · refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      rintro ⟨⟨_, hcap⟩, hsum⟩
      apply hp
      exact ⟨hcap, by omega⟩

def table (S : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate S 0
  | n+1 => (List.range (S+1)).map fun s =>
      ((List.range 31).map fun v => multiplicity v *
        if v ≤ cap n ∧ v ≤ s then (table S n).getD (s-v) 0 else 0).sum

theorem table_getD (S n s : ℕ) (hs : s ≤ S) : (table S n).getD s 0 = count n s := by
  induction n generalizing s with
  | zero =>
    rw [table, count]
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_replicate, Nat.succ_ne_zero, if_false]
      split_ifs <;> rfl
  | succ n ih =>
    rw [table, count, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some,
      Forest.sum_map_range]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with hv
    · rw [ih (s-v) (by omega)]
    · rfl

set_option maxRecDepth 100000 in
/-- The digit sums `130, …, 145` of sixteen capped pairs. -/
theorem window_count :
    ∑ s ∈ Finset.range 16, count 16 (130 + s) = 32887768277521427631995290068220650 := by
  rw [Finset.sum_congr rfl fun s hs =>
    (table_getD 145 16 (130 + s) (by rw [Finset.mem_range] at hs; omega)).symm,
    ← Forest.sum_map_range]
  decide +kernel

theorem window_lower : 89 * 2^108 ≤ ∑ s ∈ Finset.range 16, count 16 (130 + s) := by
  rw [window_count]
  norm_num

theorem window_le_half : ∑ s ∈ Finset.range 16, count 16 (130 + s) ≤ 2 ^ 127 := by
  rw [window_count]
  norm_num

end OptimalOTS.PairCode
