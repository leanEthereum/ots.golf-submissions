import Submissions.UpperLeanIsa.LayerProfile

/-! Exact tuple counting with an additive cost and an arbitrary positive
multiplicative weight. Sparse checkpoint tables avoid any prime-factor encoding. -/

namespace OptimalOTS.LeanIsaBaseline.Layer

variable (N : ℕ → ℕ) (f g : ℕ → ℕ → ℕ)

/-- Raw field tuples by sum of costs and product of multiplicities. -/
def compM : ℕ → ℕ → ℕ → ℕ
  | 0, s, w => if s = 0 ∧ w = 1 then 1 else 0
  | n + 1, s, w => ∑ v ∈ Finset.range (N n),
      if f n v ≤ s ∧ g n v ∣ w then compM n (s - f n v) (w / g n v) else 0

theorem card_compM (hg : ∀ n v, v < N n → 0 < g n v) (n s w : ℕ) :
    (Finset.univ.filter fun c : (k : Fin n) → Fin (N k) =>
        ∑ k : Fin n, f k (c k).val = s ∧ ∏ k : Fin n, g k (c k).val = w).card =
      compM N f g n s w := by
  induction n generalizing s w with
  | zero =>
    rw [compM]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Finset.filter_false_of_mem, Finset.card_empty]
      intro c _ hc
      simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty] at hc
      exact h ⟨hc.1.symm, hc.2.symm⟩
  | succ n ih =>
    rw [compM, ← Fin.sum_univ_eq_sum_range
      (fun v => if f n v ≤ s ∧ g n v ∣ w then compM N f g n (s - f n v) (w / g n v) else 0)]
    simp only [← ih]
    rw [Finset.card_filter, ← (Fin.snocEquiv fun k : Fin (n + 1) => Fin (N k)).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Fin.snocEquiv_apply, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    have hvpos := hg n v v.isLt
    split_ifs with hv
    · rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      apply if_congr _ rfl rfl
      constructor
      · intro h
        refine ⟨by omega, ?_⟩
        rw [← h.2, Nat.mul_div_cancel _ hvpos]
      · intro h
        refine ⟨by omega, ?_⟩
        rw [h.2, Nat.div_mul_cancel hv.2]
    · refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      intro h
      apply hv
      refine ⟨by omega, ?_⟩
      rw [← h.2]
      exact dvd_mul_left _ _

/-- Cost windows retain arbitrary multiplicative weights. -/
theorem card_windowM (hg : ∀ n v, v < N n → 0 < g n v) (n a b w : ℕ) :
    (Finset.univ.filter fun c : (k : Fin n) → Fin (N k) =>
        a ≤ ∑ k : Fin n, f k (c k).val ∧ ∑ k : Fin n, f k (c k).val < b ∧
          ∏ k : Fin n, g k (c k).val = w).card =
      ∑ s ∈ Finset.Ico a b, compM N f g n s w := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun c : (k : Fin n) → Fin (N k) =>
      ∑ k : Fin n, f k (c k).val) (t := Finset.Ico a b)]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [← card_compM N f g hg, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun c _ => ?_
    rw [Finset.mem_Ico] at hs
    constructor
    · exact fun h => ⟨h.2, h.1.2.2⟩
    · intro h
      exact ⟨⟨h.1 ▸ hs.1, h.1 ▸ hs.2, h.2⟩, h.1⟩
  · intro c hc
    have := (Finset.mem_filter.mp hc).2
    exact Finset.mem_Ico.mpr ⟨this.1, this.2.1⟩

/-- `(cost, multiplicity, number of tuples)`. The raw profile coefficient is
`multiplicity * number of tuples`, so aliases are counted rather than erased. -/
abbrev MProfile := ℕ × ℕ × ℕ

def profileSumM (p : List MProfile) (F : ℕ → ℕ → ℕ) : ℕ :=
  (p.map fun x => (x.2.2 * x.2.1) * F x.1 x.2.1).sum

theorem compM_succ_profile (p : List MProfile) (n : ℕ)
    (hp : ∀ F : ℕ → ℕ → ℕ,
      ∑ v ∈ Finset.range (N n), F (f n v) (g n v) = profileSumM p F) (s w : ℕ) :
    compM N f g (n + 1) s w =
      (p.map fun x => if x.1 ≤ s ∧ x.2.1 ∣ w then
        (x.2.2 * x.2.1) * compM N f g n (s - x.1) (w / x.2.1) else 0).sum := by
  rw [compM, hp (fun c m => if c ≤ s ∧ m ∣ w then compM N f g n (s - c) (w / m) else 0),
    profileSumM]
  congr 1
  apply List.map_congr_left
  intro x _
  split_ifs <;> simp

end OptimalOTS.LeanIsaBaseline.Layer
