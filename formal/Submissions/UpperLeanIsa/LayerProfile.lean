import Submissions.UpperLeanIsa.LayerCount

/-!
# Counting tuples by a per-coordinate cost and code

Coordinate `k` of a tuple ranges over `Fin (N k)`, costs `f k v` and has code `g k v`;
`compQ N f g n s e` counts the tuples of length `n` of total cost `s` and total code `e`
(`card_compQ`), and `card_windowQ` counts a window of total costs.

When the cost of coordinate `n` is a *band* function, i.e. constant `c` on the interval
`[A c, A (c + 1))` of a monotone threshold sequence `A`, the sum over the `N n = A M` values
collapses to a sum over the `M` costs weighted by the band sizes `A (c + 1) - A c` (`sum_band`).
`compTableQ` evaluates `compQ` through these profiles by kernel reduction (`compTableQ_getD`),
one coordinate per `stepQ`, so concrete counts are certified without enumerating any coordinate
range.
-/

namespace OptimalOTS.LeanIsaBaseline.Layer

variable (N : ℕ → ℕ) (f : ℕ → ℕ → ℕ)

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

/-! ## Two additive statistics

`compTableQ` evaluates `compQ` row by row (one row per code), with shifted, scaled list sums
instead of indexed lookups, so the kernel evaluates it in time linear in the table size. -/

variable (g : ℕ → ℕ → ℕ)

/-- Number of `c : (k : Fin n) → Fin (N k)` with `∑ k, f k (c k) = s` and
`∑ k, g k (c k) = e`. -/
def compQ : ℕ → ℕ → ℕ → ℕ
  | 0, s, e => if s = 0 ∧ e = 0 then 1 else 0
  | n + 1, s, e => ∑ v ∈ Finset.range (N n),
      if f n v ≤ s ∧ g n v ≤ e then compQ n (s - f n v) (e - g n v) else 0

theorem card_compQ (n s e : ℕ) :
    (Finset.univ.filter fun c : (k : Fin n) → Fin (N k) =>
        ∑ k : Fin n, f k (c k).val = s ∧ ∑ k : Fin n, g k (c k).val = e).card =
      compQ N f g n s e := by
  induction n generalizing s e with
  | zero =>
    rw [compQ]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Finset.filter_false_of_mem, Finset.card_empty]
      intro c _ hc
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hc
      exact h ⟨hc.1.symm, hc.2.symm⟩
  | succ n ih =>
    rw [compQ, ← Fin.sum_univ_eq_sum_range
      (fun v => if f n v ≤ s ∧ g n v ≤ e then compQ N f g n (s - f n v) (e - g n v) else 0)]
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

/-- Tuples whose total cost lies in `[a, b)` and whose total code is `e`. -/
theorem card_windowQ (n a b e : ℕ) :
    (Finset.univ.filter fun c : (k : Fin n) → Fin (N k) =>
        a ≤ ∑ k : Fin n, f k (c k).val ∧ ∑ k : Fin n, f k (c k).val < b ∧
          ∑ k : Fin n, g k (c k).val = e).card =
      ∑ s ∈ Finset.Ico a b, compQ N f g n s e := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun c : (k : Fin n) → Fin (N k) =>
      ∑ k : Fin n, f k (c k).val) (t := Finset.Ico a b)]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [← card_compQ, Finset.filter_filter]
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

/-- The profile recursion of `compQ` for a band-cost coordinate whose code depends only on the
cost. -/
theorem compQ_succ_band (A : ℕ → ℕ) (hA : Monotone A) (hA0 : A 0 = 0) (γ : ℕ → ℕ) (M n : ℕ)
    (hN : N n = A M) (hb : ∀ v < A M, A (f n v) ≤ v ∧ v < A (f n v + 1))
    (hg : ∀ v < A M, g n v = γ (f n v)) (s e : ℕ) :
    compQ N f g (n + 1) s e =
      ∑ c ∈ Finset.range M, if c ≤ s ∧ γ c ≤ e then
        (A (c + 1) - A c) * compQ N f g n (s - c) (e - γ c) else 0 := by
  rw [compQ, hN]
  rw [Finset.sum_congr rfl fun v hv => by rw [hg v (Finset.mem_range.mp hv)]]
  rw [sum_band A hA hA0 (f n)
    (fun c => if c ≤ s ∧ γ c ≤ e then compQ N f g n (s - c) (e - γ c) else 0) M hb]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/-- Entrywise sum of two lists (the shorter padded by zeros). -/
def addL : List ℕ → List ℕ → List ℕ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

theorem getD_addL : ∀ (l m : List ℕ) (s : ℕ), (addL l m).getD s 0 = l.getD s 0 + m.getD s 0
  | [], m, s => by simp [addL]
  | a :: l, [], s => by simp [addL]
  | a :: l, b :: m, 0 => by simp [addL]
  | a :: l, b :: m, s + 1 => by
    rw [addL, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, getD_addL l m s]

theorem getD_foldr_addL (L : List (List ℕ)) (s : ℕ) :
    (L.foldr addL []).getD s 0 = (L.map fun l => l.getD s 0).sum := by
  induction L with
  | nil => simp
  | cons l L ih => rw [List.foldr_cons, getD_addL, ih, List.map_cons, List.sum_cons]

theorem getD_shift (c : ℕ) (l : List ℕ) (s : ℕ) :
    (List.replicate c 0 ++ l).getD s 0 = if c ≤ s then l.getD (s - c) 0 else 0 := by
  induction c generalizing s with
  | zero => simp
  | succ c ih =>
    cases s with
    | zero => simp [List.replicate_succ]
    | succ s =>
      rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih]
      exact if_congr (by omega) (by congr 1; omega) rfl

theorem getD_map_mul (p : ℕ) : ∀ (l : List ℕ) (s : ℕ), (l.map (p * ·)).getD s 0 = p * l.getD s 0
  | [], s => by simp
  | a :: l, 0 => by simp
  | a :: l, s + 1 => by
    rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ, getD_map_mul p l s]

theorem getD_take : ∀ (l : List ℕ) (k s : ℕ), s < k → (l.take k).getD s 0 = l.getD s 0
  | [], k, s, _ => by simp
  | a :: l, 0, s, h => absurd h (Nat.not_lt_zero s)
  | a :: l, k + 1, 0, _ => by simp
  | a :: l, k + 1, s + 1, h => by
    rw [List.take_succ_cons, List.getD_cons_succ, List.getD_cons_succ, getD_take l k s (by omega)]

theorem getD_map_range {α : Type} (F : ℕ → α) {m e : ℕ} (d : α) (he : e < m) :
    ((List.range m).map F).getD e d = F e := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range he, Option.map_some,
    Option.getD_some]

/-- One coordinate of the table: rows `e ≤ E` of `compQ (n + 1) · e` from the rows `prev` of
`compQ n`, when `p n c` values of coordinate `n` have cost `c < M` and code `γ n c`. -/
def stepQ (p γ : ℕ → ℕ → ℕ) (M S E n : ℕ) (prev : List (List ℕ)) : List (List ℕ) :=
  (List.range (E + 1)).map fun e =>
    (((List.range M).map fun c => if γ n c ≤ e then
        List.replicate c 0 ++ (prev.getD (e - γ n c) []).map (p n c * ·)
      else []).foldr addL []).take (S + 1)

/-- Rows `e ≤ E` of the table of `compQ n · e`, entries `s ≤ S`. -/
def compTableQ (p γ : ℕ → ℕ → ℕ) (M S E : ℕ) : ℕ → List (List ℕ)
  | 0 => (List.range (E + 1)).map fun e => if e = 0 then [1] else []
  | n + 1 => stepQ p γ M S E n (compTableQ p γ M S E n)

theorem compTableQ_getD (p γ : ℕ → ℕ → ℕ) (M S E n₀ : ℕ)
    (hrec : ∀ n < n₀, ∀ s e, compQ N f g (n + 1) s e =
      ∑ c ∈ Finset.range M, if c ≤ s ∧ γ n c ≤ e then
        p n c * compQ N f g n (s - c) (e - γ n c) else 0) :
    ∀ n ≤ n₀, ∀ e ≤ E, ∀ s ≤ S,
      ((compTableQ p γ M S E n).getD e []).getD s 0 = compQ N f g n s e := by
  intro n
  induction n with
  | zero =>
    intro _ e he s _
    rw [compTableQ, getD_map_range _ _ (by omega), compQ]
    by_cases h0 : e = 0
    · subst h0
      cases s <;> simp
    · rw [if_neg h0, if_neg (by omega)]
      simp
  | succ n ih =>
    intro hn e he s hs
    rw [compTableQ, stepQ, getD_map_range _ _ (by omega), getD_take _ _ _ (by omega),
      getD_foldr_addL, List.map_map, sum_map_range, hrec n (by omega) s e]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Function.comp]
    by_cases hγ : γ n c ≤ e
    · rw [if_pos hγ, getD_shift]
      by_cases hc : c ≤ s
      · rw [if_pos hc, if_pos ⟨hc, hγ⟩, getD_map_mul, ih (by omega) _ (by omega) _ (by omega)]
      · rw [if_neg hc, if_neg (fun h => hc h.1)]
    · rw [if_neg hγ, if_neg (fun h => hγ h.2)]
      simp

end OptimalOTS.LeanIsaBaseline.Layer
