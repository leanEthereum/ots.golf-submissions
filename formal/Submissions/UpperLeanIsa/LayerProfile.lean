import Submissions.UpperLeanIsa.LayerCount

/-!
# Counting tuples by a per-coordinate cost

A generalisation of `LayerCount` from digit sums to *cost* sums. Coordinate `k` of a tuple
ranges over `Fin (N k)` and costs `f k v`; `compP N f n s` counts the tuples of length `n` of
total cost `s` (`card_compP`), and `card_window` counts a window of total costs.

When the cost of coordinate `n` is a *band* function, i.e. constant `c` on the interval
`[A c, A (c + 1))` of a monotone threshold sequence `A`, the sum over the `N n = A M` values
collapses to a sum over the `M` costs weighted by the band sizes `A (c + 1) - A c` (`sum_band`).
`compTableP` evaluates `compP` through these profiles by kernel reduction (`compTableP_getD`),
so concrete counts are certified without enumerating any coordinate range.
-/

namespace OptimalOTS.LeanIsaBaseline.Layer

variable (N : ℕ → ℕ) (f : ℕ → ℕ → ℕ)

/-- Number of `c : (k : Fin n) → Fin (N k)` with `∑ k, f k (c k) = s`; the last coordinate is
peeled first. -/
def compP : ℕ → ℕ → ℕ
  | 0, s => if s = 0 then 1 else 0
  | n + 1, s => ∑ v ∈ Finset.range (N n), if f n v ≤ s then compP n (s - f n v) else 0

theorem card_compP (n s : ℕ) :
    (Finset.univ.filter fun c : (k : Fin n) → Fin (N k) => ∑ k : Fin n, f k (c k).val = s).card =
      compP N f n s := by
  induction n generalizing s with
  | zero =>
    rw [compP]
    split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]
  | succ n ih =>
    rw [compP, ← Fin.sum_univ_eq_sum_range
      (fun v => if f n v ≤ s then compP N f n (s - f n v) else 0)]
    simp only [← ih]
    rw [Finset.card_filter, ← (Fin.snocEquiv fun k : Fin (n + 1) => Fin (N k)).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Fin.snocEquiv_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_last]
    split_ifs with hv
    · rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact if_congr (by omega) rfl rfl
    · refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]
      omega

/-- Tuples whose total cost lies in the window `[a, b)`. -/
theorem card_window (n a b : ℕ) :
    (Finset.univ.filter fun c : (k : Fin n) → Fin (N k) =>
        a ≤ ∑ k : Fin n, f k (c k).val ∧ ∑ k : Fin n, f k (c k).val < b).card =
      ∑ s ∈ Finset.Ico a b, compP N f n s := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun c : (k : Fin n) → Fin (N k) =>
      ∑ k : Fin n, f k (c k).val) (t := Finset.Ico a b)]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [← card_compP, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun c _ => ?_
    rw [Finset.mem_Ico] at hs
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨h ▸ hs.1, h ▸ hs.2⟩, h⟩
  · intro c hc
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hc).2

/-- **Band sums.** If `b` takes the value `c` exactly on `[A c, A (c + 1))`, a sum of `G ∘ b`
over `[0, A M)` is the band-size-weighted sum of `G` over the costs `c < M`. -/
theorem sum_band (A : ℕ → ℕ) (hA : Monotone A) (hA0 : A 0 = 0) (b G : ℕ → ℕ) :
    ∀ M, (∀ v < A M, A (b v) ≤ v ∧ v < A (b v + 1)) →
      ∑ v ∈ Finset.range (A M), G (b v) = ∑ c ∈ Finset.range M, (A (c + 1) - A c) * G c := by
  intro M
  induction M with
  | zero => intro _; simp [hA0]
  | succ M ih =>
    intro hb
    have hle : A M ≤ A (M + 1) := hA (Nat.le_succ M)
    rw [← Finset.sum_range_add_sum_Ico _ hle, Finset.sum_range_succ,
      ih fun v hv => hb v (lt_of_lt_of_le hv hle)]
    congr 1
    have hc : ∀ v ∈ Finset.Ico (A M) (A (M + 1)), G (b v) = G M := by
      intro v hv
      rw [Finset.mem_Ico] at hv
      obtain ⟨h1, h2⟩ := hb v hv.2
      have hbv : b v = M := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := hA (show b v + 1 ≤ M by omega)
          omega
        · have := hA (show M + 1 ≤ b v by omega)
          omega
      rw [hbv]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Ico, smul_eq_mul]

/-- `compTableP p M S n` is `[compP n 0, …, compP n S]` when `p n c` is the number of values of
coordinate `n` of cost `c < M` (`compTableP_getD`). -/
def compTableP (p : ℕ → ℕ → ℕ) (M S : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate S 0
  | n + 1 =>
    (List.range (S + 1)).map fun s =>
      ((List.range M).map fun c =>
        if c ≤ s then p n c * (compTableP p M S n).getD (s - c) 0 else 0).sum

theorem compTableP_getD (p : ℕ → ℕ → ℕ) (M S n₀ : ℕ)
    (hrec : ∀ n < n₀, ∀ s, compP N f (n + 1) s =
      ∑ c ∈ Finset.range M, if c ≤ s then p n c * compP N f n (s - c) else 0) :
    ∀ n ≤ n₀, ∀ s ≤ S, (compTableP p M S n).getD s 0 = compP N f n s := by
  intro n
  induction n with
  | zero =>
    intro _ s hs
    rw [compTableP, compP]
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_replicate,
        Nat.succ_ne_zero, if_false]
      split_ifs <;> rfl
  | succ n ih =>
    intro hn s hs
    rw [compTableP, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some, sum_map_range,
      hrec n (by omega) s]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with h
    · rw [ih (by omega) (s - c) (by omega)]
    · rfl

/-- The profile recursion of `compP` for a band-cost coordinate. -/
theorem compP_succ_band (A : ℕ → ℕ) (hA : Monotone A) (hA0 : A 0 = 0) (M n : ℕ)
    (hN : N n = A M) (hb : ∀ v < A M, A (f n v) ≤ v ∧ v < A (f n v + 1)) (s : ℕ) :
    compP N f (n + 1) s =
      ∑ c ∈ Finset.range M, if c ≤ s then (A (c + 1) - A c) * compP N f n (s - c) else 0 := by
  rw [compP, hN, sum_band A hA hA0 (f n) (fun c => if c ≤ s then compP N f n (s - c) else 0)
    M hb]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

end OptimalOTS.LeanIsaBaseline.Layer
