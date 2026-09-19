import Submissions.UpperCompressions.Tree
import Submissions.UpperCompressions.Count

/-!
# The disclosure sets of the concrete scheme

A disclosure set is described by a *choice* `(E, G, t)`: the revealed subtree digests `E`, the
revealed group digests `G` (under evaluated subtrees), and for every chain `k` the position
`t k ∈ {0, …, 14}` of the revealed chain value (`0` reveals the source `z_k`, `p ≥ 1` reveals
`c_{k,p} = cv k (p-1)`); only *active* chains (under evaluated groups and subtrees) reveal a
value, and inactive chains have `t k = 14` so that the choice is determined by the set.

The three shapes `(|E|, |G|, chain cost)` `(1, 2, 83)`, `(0, 6, 83)`, `(1, 3, 84)` all give cuts of
reconstruction cost `103` with at most `42` revealed values, and there are more than `2 ^ 115` of
them (`card_family`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

/-- The subtree of a group. -/
def subtreeOf (j : Fin 18) : Fin 6 := ⟨j / 3, by omega⟩

/-- The group of a chain. -/
def groupOfChain (k : Fin 54) : Fin 18 := ⟨k / 3, by omega⟩

/-- The subtree of a chain. -/
def subtreeOfChain (k : Fin 54) : Fin 6 := ⟨k / 9, by omega⟩

/-- Groups under evaluated subtrees. -/
def allowed (E : Finset (Fin 6)) : Finset (Fin 18) := Finset.univ.filter fun j => subtreeOf j ∉ E

/-- Chains under evaluated groups and subtrees. -/
def active (E : Finset (Fin 6)) (G : Finset (Fin 18)) : Finset (Fin 54) :=
  Finset.univ.filter fun k => subtreeOfChain k ∉ E ∧ groupOfChain k ∉ G

/-- The revealed node of chain `k` at position `p`. -/
def chainNode (k : Fin 54) (p : Fin 15) : Name :=
  if h : p.val = 0 then src k else cv k ⟨p.val - 1, by omega⟩

/-- Chain positions with total chain cost `s` on the chains of `S`; other chains are at `14`.

Irreducible: the elaborator must never unfold `Finset.univ` of the function type `Fin 54 → Fin 15`
(it would try to enumerate it); use `positions_def` and `mem_positions`. -/
irreducible_def positions (S : Finset (Fin 54)) (s : ℕ) : Finset (Fin 54 → Fin 15) :=
  Finset.univ.filter fun t => (∀ k ∉ S, t k = 14) ∧ ∑ k ∈ S, (14 - (t k).val) = s

theorem mem_positions (S : Finset (Fin 54)) (s : ℕ) (t : Fin 54 → Fin 15) :
    t ∈ positions S s ↔ (∀ k ∉ S, t k = 14) ∧ ∑ k ∈ S, (14 - (t k).val) = s := by
  rw [positions_def, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- A choice of disclosure set. -/
abbrev Choice := Finset (Fin 6) × Finset (Fin 18) × (Fin 54 → Fin 15)

/-- The choices of a shape. -/
@[irreducible] def shape (a b s : ℕ) : Finset Choice :=
  ((Finset.powersetCard a (Finset.univ : Finset (Fin 6))).sigma fun E =>
    (Finset.powersetCard b (allowed E)).sigma fun G => positions (active E G) s).image
      fun x => (x.1, x.2.1, x.2.2)

/-- The disclosure set of a choice. -/
def cutOf (c : Choice) : Finset Name :=
  c.1.image ev ∪ c.2.1.image gv ∪ (active c.1 c.2.1).image fun k => chainNode k (c.2.2 k)

/-- The three shapes. -/
@[irreducible] def shapes : Finset Choice := shape 1 2 83 ∪ shape 0 6 83 ∪ shape 1 3 84

theorem mem_shapes_iff (c : Choice) :
    c ∈ shapes ↔ c ∈ shape 1 2 83 ∨ c ∈ shape 0 6 83 ∨ c ∈ shape 1 3 84 := by
  unfold shapes
  simp [Finset.mem_union]

/-- The family of disclosure sets. -/
@[irreducible] def family : Finset (Finset Name) := shapes.image cutOf

theorem mem_shape_iff (a b s : ℕ) (c : Choice) :
    c ∈ shape a b s ↔ c.1.card = a ∧ c.2.1 ⊆ allowed c.1 ∧ c.2.1.card = b ∧
      c.2.2 ∈ positions (active c.1 c.2.1) s := by
  unfold shape
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨E, G, t⟩, hx, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powersetCard] at hx
    exact ⟨hx.1.2, hx.2.1.1, hx.2.1.2, hx.2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨c.1, c.2.1, c.2.2⟩, ?_, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, h1⟩, ⟨h2, h3⟩, h4⟩

/-! ### Cardinalities of the index sets -/

theorem subtreeOf_groupOf (l : Fin 6) (a : Fin 3) : subtreeOf (groupOf l a) = l := by
  apply Fin.ext
  simp only [subtreeOf, groupOf]
  omega

theorem groupOf_injective : Function.Injective fun p : Fin 6 × Fin 3 => groupOf p.1 p.2 := by
  rintro ⟨l, a⟩ ⟨l', a'⟩ h
  simp only [groupOf, Fin.mk.injEq] at h
  have hl : l = l' := Fin.ext (by omega)
  have ha : a = a' := Fin.ext (by omega)
  rw [hl, ha]

theorem allowed_eq_image (E : Finset (Fin 6)) :
    allowed E = (Eᶜ ×ˢ (Finset.univ : Finset (Fin 3))).image fun p => groupOf p.1 p.2 := by
  ext j
  simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product, Finset.mem_compl, and_true, Prod.exists]
  constructor
  · intro h
    refine ⟨subtreeOf j, ⟨j % 3, by omega⟩, h, ?_⟩
    apply Fin.ext
    simp only [groupOf, subtreeOf]
    omega
  · rintro ⟨l, a, hl, rfl⟩
    rwa [subtreeOf_groupOf]

theorem card_allowed (E : Finset (Fin 6)) : (allowed E).card = 18 - 3 * E.card := by
  rw [allowed_eq_image, Finset.card_image_of_injective _ groupOf_injective, Finset.card_product,
    Finset.card_compl, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  have := Finset.card_le_univ E
  rw [Fintype.card_fin] at this
  omega

theorem groupOfChain_chainOf (j : Fin 18) (a : Fin 3) : groupOfChain (chainOf j a) = j := by
  apply Fin.ext
  simp only [groupOfChain, chainOf]
  omega

theorem subtreeOfChain_eq (k : Fin 54) : subtreeOfChain k = subtreeOf (groupOfChain k) := by
  apply Fin.ext
  simp only [subtreeOfChain, subtreeOf, groupOfChain]
  omega

theorem chainOf_injective : Function.Injective fun p : Fin 18 × Fin 3 => chainOf p.1 p.2 := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  simp only [chainOf, Fin.mk.injEq] at h
  have hj : j = j' := Fin.ext (by omega)
  have ha : a = a' := Fin.ext (by omega)
  rw [hj, ha]

theorem mem_active_iff (E : Finset (Fin 6)) (G : Finset (Fin 18)) (k : Fin 54) :
    k ∈ active E G ↔ subtreeOfChain k ∉ E ∧ groupOfChain k ∉ G := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]

theorem active_eq_image (E : Finset (Fin 6)) (G : Finset (Fin 18)) :
    active E G =
      ((allowed E \ G) ×ˢ (Finset.univ : Finset (Fin 3))).image fun p => chainOf p.1 p.2 := by
  ext k
  simp only [active, allowed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product, Finset.mem_sdiff, and_true, Prod.exists]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨groupOfChain k, ⟨k % 3, by omega⟩, ⟨?_, h2⟩, ?_⟩
    · rwa [← subtreeOfChain_eq]
    · apply Fin.ext
      simp only [chainOf, groupOfChain]
      omega
  · rintro ⟨j, a, ⟨h1, h2⟩, rfl⟩
    rw [subtreeOfChain_eq, groupOfChain_chainOf]
    exact ⟨h1, h2⟩

theorem card_active (E : Finset (Fin 6)) (G : Finset (Fin 18)) (hG : G ⊆ allowed E) :
    (active E G).card = 3 * (18 - 3 * E.card - G.card) := by
  rw [active_eq_image, Finset.card_image_of_injective _ chainOf_injective, Finset.card_product,
    Finset.card_sdiff_of_subset hG, card_allowed, Finset.card_univ, Fintype.card_fin]
  omega

theorem card_positions (S : Finset (Fin 54)) (s : ℕ) : (positions S s).card = comp S.card s := by
  rw [← card_comp]
  refine Finset.card_nbij' (fun t i => Fin.rev (t (S.equivFin.symm i)))
    (fun c k => if h : k ∈ S then Fin.rev (c (S.equivFin ⟨k, h⟩)) else 14) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, mem_positions] at ht
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← ht.2, ← Finset.sum_coe_sort S, ← Equiv.sum_comp S.equivFin.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_rev]
    omega
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter] at hc
    rw [Finset.mem_coe, mem_positions]
    refine ⟨fun k hk => dif_neg hk, ?_⟩
    rw [← hc.2, ← Finset.sum_coe_sort S, ← Equiv.sum_comp S.equivFin (fun i => (c i).val)]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [dif_pos x.2]
    simp only [Fin.val_rev, Subtype.coe_eta]
    omega
  · intro t ht
    rw [Finset.mem_coe, mem_positions] at ht
    funext k
    dsimp only
    by_cases hk : k ∈ S
    · simp only [dif_pos hk, Equiv.symm_apply_apply, Fin.rev_rev]
    · rw [dif_neg hk, ht.1 k hk]
  · intro c _
    funext i
    dsimp only
    have h := (S.equivFin.symm i).2
    simp only [dif_pos h, Subtype.coe_eta, Equiv.apply_symm_apply, Fin.rev_rev]

theorem choice_mk_injective :
    Function.Injective fun x : (_ : Finset (Fin 6)) × (_ : Finset (Fin 18)) × (Fin 54 → Fin 15) =>
      ((x.1, x.2.1, x.2.2) : Choice) := by
  rintro ⟨E, G, t⟩ ⟨E', G', t'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem card_shape (a b s : ℕ) :
    (shape a b s).card = Nat.choose 6 a * Nat.choose (18 - 3 * a) b * comp (3 * (18 - 3 * a - b)) s := by
  unfold shape
  rw [Finset.card_image_of_injective _ choice_mk_injective, Finset.card_sigma]
  have h2 : ∀ E ∈ Finset.powersetCard a (Finset.univ : Finset (Fin 6)),
      ((Finset.powersetCard b (allowed E)).sigma fun G => positions (active E G) s).card =
        Nat.choose (18 - 3 * a) b * comp (3 * (18 - 3 * a - b)) s := by
    intro E hE
    rw [Finset.mem_powersetCard] at hE
    rw [Finset.card_sigma]
    have h1 : ∀ G ∈ Finset.powersetCard b (allowed E),
        (positions (active E G) s).card = comp (3 * (18 - 3 * a - b)) s := by
      intro G hG
      rw [Finset.mem_powersetCard] at hG
      rw [card_positions, card_active E G hG.1, hG.2, hE.2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_powersetCard, card_allowed, hE.2,
      smul_eq_mul]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_assoc]

/-! ### Membership in a disclosure set -/

theorem chainNode_eq_src_iff (k k' : Fin 54) (p : Fin 15) :
    chainNode k p = src k' ↔ k = k' ∧ p = 0 := by
  unfold chainNode
  split_ifs with h
  · simp only [Name.src.injEq, Fin.ext_iff, Fin.val_zero, h, and_true]
  · simp only [false_iff, not_and, Fin.ext_iff, Fin.val_zero]
    intro _ hp
    exact h hp

theorem chainNode_eq_cv_iff (k k' : Fin 54) (p : Fin 15) (t : Fin 14) :
    chainNode k p = cv k' t ↔ k = k' ∧ p.val = t.val + 1 := by
  unfold chainNode
  split_ifs with h
  · simp only [false_iff, not_and]
    intro _
    omega
  · simp only [Name.cv.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨hk, hp⟩
      exact ⟨hk, by omega⟩
    · rintro ⟨hk, hp⟩
      exact ⟨hk, by omega⟩

theorem chainNode_ne_ev (k : Fin 54) (p : Fin 15) (l : Fin 6) : chainNode k p ≠ ev l := by
  unfold chainNode
  split_ifs <;> simp

theorem chainNode_ne_gv (k : Fin 54) (p : Fin 15) (j : Fin 18) : chainNode k p ≠ gv j := by
  unfold chainNode
  split_ifs <;> simp

theorem chainNode_len (k : Fin 54) (p : Fin 15) : (chainNode k p).len = 128 := by
  unfold chainNode
  split_ifs <;> rfl

theorem mem_cutOf_iff (c : Choice) (n : Name) :
    n ∈ cutOf c ↔ (∃ l ∈ c.1, ev l = n) ∨ (∃ j ∈ c.2.1, gv j = n) ∨
      ∃ k ∈ active c.1 c.2.1, chainNode k (c.2.2 k) = n := by
  unfold cutOf
  simp only [Finset.mem_union, Finset.mem_image, or_assoc]

theorem ev_mem_cutOf_iff' (c : Choice) (l : Fin 6) : ev l ∈ cutOf c ↔ l ∈ c.1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨l', hl', h⟩ | ⟨j, _, h⟩ | ⟨k, _, h⟩)
    · rw [Name.ev.injEq] at h
      exact h ▸ hl'
    · exact absurd h (by simp)
    · exact absurd h (chainNode_ne_ev _ _ _)
  · intro h
    exact Or.inl ⟨l, h, rfl⟩

theorem gv_mem_cutOf_iff' (c : Choice) (j : Fin 18) : gv j ∈ cutOf c ↔ j ∈ c.2.1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨l, _, h⟩ | ⟨j', hj', h⟩ | ⟨k, _, h⟩)
    · exact absurd h (by simp)
    · rw [Name.gv.injEq] at h
      exact h ▸ hj'
    · exact absurd h (chainNode_ne_gv _ _ _)
  · intro h
    exact Or.inr (Or.inl ⟨j, h, rfl⟩)

theorem src_mem_cutOf_iff' (c : Choice) (k : Fin 54) :
    src k ∈ cutOf c ↔ k ∈ active c.1 c.2.1 ∧ c.2.2 k = 0 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨l, _, h⟩ | ⟨j, _, h⟩ | ⟨k', hk', h⟩)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · rw [chainNode_eq_src_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨hk', h⟩
  · rintro ⟨hk, h⟩
    exact Or.inr (Or.inr ⟨k, hk, (chainNode_eq_src_iff _ _ _).mpr ⟨rfl, h⟩⟩)

theorem cv_mem_cutOf_iff' (c : Choice) (k : Fin 54) (t : Fin 14) :
    cv k t ∈ cutOf c ↔ k ∈ active c.1 c.2.1 ∧ (c.2.2 k).val = t.val + 1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨l, _, h⟩ | ⟨j, _, h⟩ | ⟨k', hk', h⟩)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · rw [chainNode_eq_cv_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨hk', h⟩
  · rintro ⟨hk, h⟩
    exact Or.inr (Or.inr ⟨k, hk, (chainNode_eq_cv_iff _ _ _ _).mpr ⟨rfl, h⟩⟩)

theorem not_mem_cutOf_of_len {c : Choice} {n : Name} (hn : n.len ≠ 128) : n ∉ cutOf c := by
  intro h
  rw [mem_cutOf_iff] at h
  rcases h with ⟨l, _, rfl⟩ | ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
  · exact hn rfl
  · exact hn rfl
  · exact hn (chainNode_len _ _)

theorem mem_cutOf_len' {c : Choice} {n : Name} (hn : n ∈ cutOf c) : n.len = 128 := by
  by_contra h
  exact not_mem_cutOf_of_len h hn

theorem ci_not_mem_cutOf (c : Choice) (k : Fin 54) (t : Fin 14) : ci k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem ch_not_mem_cutOf (c : Choice) (k : Fin 54) (t : Fin 14) : ch k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem gc_not_mem_cutOf (c : Choice) (j : Fin 18) : gc j ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem gh_not_mem_cutOf (c : Choice) (j : Fin 18) : gh j ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem ec_not_mem_cutOf (c : Choice) (l : Fin 6) : ec l ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem eh_not_mem_cutOf (c : Choice) (l : Fin 6) : eh l ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

/-! ### The choices of `shapes` -/

theorem exists_of_mem_shapes {c : Choice} (hc : c ∈ shapes) :
    ∃ a b s : ℕ, ((a = 1 ∧ b = 2 ∧ s = 83) ∨ (a = 0 ∧ b = 6 ∧ s = 83) ∨ (a = 1 ∧ b = 3 ∧ s = 84)) ∧
      c.1.card = a ∧ c.2.1 ⊆ allowed c.1 ∧ c.2.1.card = b ∧
      c.2.2 ∈ positions (active c.1 c.2.1) s := by
  rw [mem_shapes_iff] at hc
  rcases hc with hc | hc | hc <;> rw [mem_shape_iff] at hc
  · exact ⟨1, 2, 83, Or.inl ⟨rfl, rfl, rfl⟩, hc⟩
  · exact ⟨0, 6, 83, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hc⟩
  · exact ⟨1, 3, 84, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), hc⟩

theorem subset_allowed_of_mem_shapes {c : Choice} (hc : c ∈ shapes) : c.2.1 ⊆ allowed c.1 := by
  obtain ⟨_, _, _, -, -, h, -, -⟩ := exists_of_mem_shapes hc
  exact h

theorem pos_of_mem_shapes {c : Choice} (hc : c ∈ shapes) :
    ∀ k ∉ active c.1 c.2.1, c.2.2 k = 14 := by
  obtain ⟨_, _, _, -, -, -, -, h⟩ := exists_of_mem_shapes hc
  exact ((mem_positions _ _ _).mp h).1

/-- The choice is determined by its disclosure set. -/
theorem cutOf_injective : Set.InjOn cutOf shapes := by
  intro c hc c' hc' h
  rw [Finset.mem_coe] at hc hc'
  have hE : c.1 = c'.1 := by
    ext l
    rw [← ev_mem_cutOf_iff' c l, ← ev_mem_cutOf_iff' c' l, h]
  have hG : c.2.1 = c'.2.1 := by
    ext j
    rw [← gv_mem_cutOf_iff' c j, ← gv_mem_cutOf_iff' c' j, h]
  have ht : c.2.2 = c'.2.2 := by
    funext k
    by_cases hk : k ∈ active c.1 c.2.1
    · have hmem : chainNode k (c.2.2 k) ∈ cutOf c' := by
        rw [← h, mem_cutOf_iff]
        exact Or.inr (Or.inr ⟨k, hk, rfl⟩)
      unfold chainNode at hmem
      split_ifs at hmem with h0
      · rw [src_mem_cutOf_iff'] at hmem
        rw [hmem.2]
        exact Fin.ext h0
      · rw [cv_mem_cutOf_iff'] at hmem
        apply Fin.ext
        rw [hmem.2]
        dsimp only
        omega
    · rw [pos_of_mem_shapes hc k hk, pos_of_mem_shapes hc' k (by rwa [← hE, ← hG])]
  exact Prod.ext hE (Prod.ext hG ht)

theorem comp_39_83 : comp 39 83 = 35822450422664223521084479933335 := by
  rw [← compTable_getD 83 39 83 le_rfl]
  decide +kernel

theorem comp_36_83 : comp 36 83 = 1012546233179703066212339579496 := by
  rw [← compTable_getD 83 36 83 le_rfl]
  decide +kernel

theorem comp_36_84 : comp 36 84 = 1422449004829698659936386602786 := by
  rw [← compTable_getD 84 36 84 le_rfl]
  decide +kernel

/-- The number of choices of the three shapes, from the exact values of `comp`
(`C(6,1) = 6`, `C(15,2) = 105`, `C(6,0) = 1`, `C(18,6) = 18564`, `C(15,3) = 455`). -/
theorem shapes_ge :
    2 ^ 115 ≤ 6 * 105 * comp 39 83 + 1 * 18564 * comp 36 83 + 6 * 455 * comp 36 84 := by
  rw [comp_39_83, comp_36_83, comp_36_84]
  norm_num

theorem card_family : 2 ^ 115 ≤ family.card := by
  unfold family
  rw [Finset.card_image_of_injOn cutOf_injective]
  unfold shapes
  have d1 : Disjoint (shape 1 2 83) (shape 0 6 83) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    rw [mem_shape_iff] at h1 h2
    omega
  have d2 : Disjoint (shape 1 2 83) (shape 1 3 84) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    rw [mem_shape_iff] at h1 h2
    omega
  have d3 : Disjoint (shape 0 6 83) (shape 1 3 84) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    rw [mem_shape_iff] at h1 h2
    omega
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d2, d3⟩),
    Finset.card_union_of_disjoint d1, card_shape, card_shape, card_shape]
  have c1 : 6 * 105 = Nat.choose 6 1 * Nat.choose (18 - 3 * 1) 2 := by decide
  have c2 : 1 * 18564 = Nat.choose 6 0 * Nat.choose (18 - 3 * 0) 6 := by decide
  have c3 : 6 * 455 = Nat.choose 6 1 * Nat.choose (18 - 3 * 1) 3 := by decide
  have e1 : comp 39 83 = comp (3 * (18 - 3 * 1 - 2)) 83 := congrArg (fun x => comp x 83) (by norm_num)
  have e2 : comp 36 83 = comp (3 * (18 - 3 * 0 - 6)) 83 := congrArg (fun x => comp x 83) (by norm_num)
  have e3 : comp 36 84 = comp (3 * (18 - 3 * 1 - 3)) 84 := congrArg (fun x => comp x 84) (by norm_num)
  refine le_trans shapes_ge (le_of_eq ?_)
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· * ·) c1 e1) (congrArg₂ (· * ·) c2 e2))
    (congrArg₂ (· * ·) c3 e3)

/-! ### Evaluated nodes -/

theorem forall_above_of_child {A : Finset Name} {n p : Name} (hp : child n = some p)
    (he : Evaluated A p) : ∀ m, Above m n → m ∉ A := by
  intro m hm
  rw [above_of_child hp] at hm
  rcases hm with rfl | hm
  · exact he.1
  · exact he.2 m hm

theorem evaluated_of_child {A : Finset Name} {n p : Name} (hp : child n = some p) (hn : n ∉ A)
    (he : Evaluated A p) : Evaluated A n :=
  ⟨hn, forall_above_of_child hp he⟩

theorem evaluated_rh' (c : Choice) : Evaluated (cutOf c) rh :=
  ⟨rh_not_mem_cutOf c, fun m hm => absurd hm (not_above_rh m)⟩

theorem evaluated_rc' (c : Choice) : Evaluated (cutOf c) rc :=
  evaluated_of_child rfl (rc_not_mem_cutOf c) (evaluated_rh' c)

theorem evaluated_eh_iff' (c : Choice) (l : Fin 6) : Evaluated (cutOf c) (eh l) ↔ l ∉ c.1 := by
  constructor
  · intro h
    rw [← ev_mem_cutOf_iff' c l]
    exact h.2 (ev l) (Above.child rfl)
  · intro hl
    refine evaluated_of_child rfl (eh_not_mem_cutOf c l) ?_
    refine evaluated_of_child rfl ?_ (evaluated_rc' c)
    rw [ev_mem_cutOf_iff']
    exact hl

theorem evaluated_gh_iff' (c : Choice) (j : Fin 18) :
    Evaluated (cutOf c) (gh j) ↔ subtreeOf j ∉ c.1 ∧ j ∉ c.2.1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← ev_mem_cutOf_iff' c]
      refine h.2 (ev (subtreeOf j)) ((above_iff_mem_ancSet _ _).mpr ?_)
      simp [ancSet, subtreeOf]
    · rw [← gv_mem_cutOf_iff' c j]
      exact h.2 (gv j) (Above.child rfl)
  · rintro ⟨h1, h2⟩
    refine evaluated_of_child rfl (gh_not_mem_cutOf c j) ?_
    refine evaluated_of_child rfl ?_ ?_
    · rw [gv_mem_cutOf_iff']
      exact h2
    · refine evaluated_of_child rfl (ec_not_mem_cutOf c _) ?_
      rw [evaluated_eh_iff']
      exact h1

theorem evaluated_ch_iff' (c : Choice) (k : Fin 54) (t : Fin 14) :
    Evaluated (cutOf c) (ch k t) ↔ k ∈ active c.1 c.2.1 ∧ (c.2.2 k).val ≤ t.val := by
  unfold Evaluated
  simp only [above_iff_mem_ancSet, ancSet, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert, Finset.mem_singleton,
    forall_eq, ci_not_mem_cutOf, ch_not_mem_cutOf, cv_mem_cutOf_iff', gc_not_mem_cutOf,
    gh_not_mem_cutOf,
    gv_mem_cutOf_iff', ec_not_mem_cutOf, eh_not_mem_cutOf, ev_mem_cutOf_iff', rc_not_mem_cutOf,
    rh_not_mem_cutOf, not_false_eq_true, true_and, and_true, implies_true, mem_active_iff,
    subtreeOfChain, groupOfChain]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h3, h2⟩, ?_⟩
    by_contra hlt
    have hv := (c.2.2 k).isLt
    exact @h1 ⟨(c.2.2 k).val - 1, by omega⟩ (by rw [Fin.le_def]; dsimp only; omega)
      ⟨⟨h3, h2⟩, by dsimp only; omega⟩
  · rintro ⟨⟨h3, h2⟩, hle⟩
    refine ⟨fun x hx h => ?_, h2, h3⟩
    rw [Fin.le_def] at hx
    omega

/-- The input of a chain hash is evaluated exactly when the chain hash is. -/
theorem evaluated_ci_iff' (c : Choice) (k : Fin 54) (t : Fin 14) :
    Evaluated (cutOf c) (ci k t) ↔ k ∈ active c.1 c.2.1 ∧ (c.2.2 k).val ≤ t.val := by
  rw [← evaluated_ch_iff']
  constructor
  · intro h
    exact ⟨ch_not_mem_cutOf c k t, fun m hm => h.2 m (Above.step rfl hm)⟩
  · intro h
    exact evaluated_of_child rfl (ci_not_mem_cutOf c k t) h

theorem child_cv_of_lt (k : Fin 54) (t : Fin 14) (ht : t.val < 13) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]

theorem child_cv_of_eq (k : Fin 54) (t : Fin 14) (ht : t.val = 13) :
    child (cv k t) = some (gc (groupOfChain k)) := by
  simp only [Name.child]
  rw [dif_pos ht]
  rfl

theorem isCut_cutOf' {c : Choice} (hc : c ∈ shapes) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_len' hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    rcases hn with ⟨l, hl, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
    · exact forall_above_of_child rfl (evaluated_rc' c)
    · refine forall_above_of_child rfl (evaluated_of_child rfl (ec_not_mem_cutOf c _)
        ((evaluated_eh_iff' c _).mpr ?_))
      have := subset_allowed_of_mem_shapes hc hj
      simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    · have hk' := (mem_active_iff _ _ _).mp hk
      unfold chainNode
      split_ifs with h0
      · exact forall_above_of_child rfl
          ((evaluated_ci_iff' c k 0).mpr ⟨hk, by rw [h0]; exact Nat.zero_le _⟩)
      · by_cases h13 : (c.2.2 k).val = 14
        · refine forall_above_of_child (child_cv_of_eq k _ (by dsimp only; omega))
            (evaluated_of_child rfl (gc_not_mem_cutOf c _) ((evaluated_gh_iff' c _).mpr ?_))
          rw [← subtreeOfChain_eq]
          exact hk'
        · have hlt := (c.2.2 k).isLt
          refine forall_above_of_child (child_cv_of_lt k _ (by dsimp only; omega))
            ((evaluated_ci_iff' c k _).mpr ⟨hk, ?_⟩)
          dsimp only
          omega
  covers := by
    intro k
    by_cases hk : k ∈ active c.1 c.2.1
    · by_cases h0 : (c.2.2 k).val = 0
      · exact Or.inl ((src_mem_cutOf_iff' c k).mpr ⟨hk, Fin.ext h0⟩)
      · have hlt := (c.2.2 k).isLt
        refine Or.inr ⟨cv k ⟨(c.2.2 k).val - 1, by omega⟩,
          (cv_mem_cutOf_iff' c k _).mpr ⟨hk, by dsimp only; omega⟩, ?_⟩
        rw [above_iff_mem_ancSet]
        simp [ancSet]
    · rw [mem_active_iff, not_and_or, not_not, not_not] at hk
      rcases hk with hk | hk
      · refine Or.inr ⟨ev (subtreeOfChain k), (ev_mem_cutOf_iff' c _).mpr hk, ?_⟩
        rw [above_iff_mem_ancSet]
        simp [ancSet, subtreeOfChain]
      · refine Or.inr ⟨gv (groupOfChain k), (gv_mem_cutOf_iff' c _).mpr hk, ?_⟩
        rw [above_iff_mem_ancSet]
        simp [ancSet, groupOfChain]

theorem card_cutOf_le' {c : Choice} (hc : c ∈ shapes) : (cutOf c).card ≤ 42 := by
  obtain ⟨a, b, s, habs, ha, hG, hb, -⟩ := exists_of_mem_shapes hc
  have h1 := Finset.card_union_le (c.1.image ev ∪ c.2.1.image gv)
    ((active c.1 c.2.1).image fun k => chainNode k (c.2.2 k))
  have h2 := Finset.card_union_le (c.1.image ev) (c.2.1.image gv)
  have h3 : (c.1.image ev).card ≤ c.1.card := Finset.card_image_le
  have h4 : (c.2.1.image gv).card ≤ c.2.1.card := Finset.card_image_le
  have h5 : ((active c.1 c.2.1).image fun k => chainNode k (c.2.2 k)).card ≤
      (active c.1 c.2.1).card := Finset.card_image_le
  rw [card_active c.1 c.2.1 hG, ha, hb] at h5
  unfold cutOf
  rcases habs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega

theorem sum_fin14_ge (v : ℕ) : ∑ t : Fin 14, (if v ≤ t.val then 1 else 0) = 14 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 14, ← Finset.card_filter]
  have : (Finset.range 14).filter (fun t => v ≤ t) = Finset.Ico v 14 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

theorem cost_cutOf' {c : Choice} (hc : c ∈ shapes) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost = 103 := by
  obtain ⟨a, b, s, habs, ha, hG, hb, ht⟩ := exists_of_mem_shapes hc
  have h_eh : ∑ l, (if Evaluated (cutOf c) (eh l) then 1 else 0) = 6 - a := by
    simp only [evaluated_eh_iff']
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun l => l ∉ c.1) = c.1ᶜ := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    rw [this, Finset.card_compl, Fintype.card_fin, ha]
  have h_gh : ∑ j, (if Evaluated (cutOf c) (gh j) then 1 else 0) = 18 - 3 * a - b := by
    simp only [evaluated_gh_iff']
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun j => subtreeOf j ∉ c.1 ∧ j ∉ c.2.1) = allowed c.1 \ c.2.1 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, allowed]
    rw [this, Finset.card_sdiff_of_subset hG, card_allowed, ha, hb]
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) = s := by
    simp only [evaluated_ch_iff']
    have hin : ∀ k, ∑ t : Fin 14, (if k ∈ active c.1 c.2.1 ∧ (c.2.2 k).val ≤ t.val then 1 else 0) =
        if k ∈ active c.1 c.2.1 then 14 - (c.2.2 k).val else 0 := by
      intro k
      by_cases hk : k ∈ active c.1 c.2.1
      · simp only [hk, true_and, if_true]
        exact sum_fin14_ge _
      · simp only [hk, false_and, if_false, Finset.sum_const_zero]
    simp only [hin]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact ((mem_positions _ _ _).mp ht).2
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh' c), h_ch, h_gh, h_eh]
  rcases habs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num

/-! ## Membership in a disclosure set -/

section props

variable {c : Choice} (hc : c ∈ shapes)
include hc

-- the statements below take `hc` for uniformity; some proofs do not need it
set_option linter.unusedSectionVars false

theorem isCut_cutOf : IsCut (cutOf c) :=
  isCut_cutOf' hc

theorem card_cutOf_le : (cutOf c).card ≤ 42 :=
  card_cutOf_le' hc

theorem cost_cutOf : ∑ n ∈ evaluatedSet (cutOf c), n.cost = 103 :=
  cost_cutOf' hc

end props

theorem isCut_of_mem_family {A : Finset Name} (h : A ∈ family) : IsCut A := by
  unfold family at h
  rw [Finset.mem_image] at h
  obtain ⟨c, hc, hA⟩ := h
  rw [← hA]
  exact isCut_cutOf hc

theorem card_le_of_mem_family {A : Finset Name} (h : A ∈ family) : A.card ≤ 42 := by
  unfold family at h
  rw [Finset.mem_image] at h
  obtain ⟨c, hc, hA⟩ := h
  rw [← hA]
  exact card_cutOf_le hc

theorem cost_of_mem_family {A : Finset Name} (h : A ∈ family) :
    ∑ n ∈ evaluatedSet A, n.cost = 103 := by
  unfold family at h
  rw [Finset.mem_image] at h
  obtain ⟨c, hc, hA⟩ := h
  rw [← hA]
  exact cost_cutOf hc

end Forest

end OptimalOTS
