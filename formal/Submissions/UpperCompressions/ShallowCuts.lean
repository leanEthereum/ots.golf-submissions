import Submissions.UpperCompressions.ShallowTree
import Submissions.UpperCompressions.ShallowCount

/-!
# A single shallow-forest disclosure family

Six of eighteen group digests are disclosed; each of the remaining 36 chains
contributes one word. Chain reconstruction costs sum to 84, twelve group hashes
cost twelve, and the root costs five. This file connects the exact counted
family to the protected graph and proves its 101-compression reconstruction cost.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical
set_option linter.constructorNameAsVariable false
namespace OptimalOTS
open OptimalOTS.Dag
namespace ShallowForest
open Name ShallowResearch

attribute [local irreducible] ShallowResearch.comp Finset.univ Finset.filter

/-- The group containing a chain. -/
def groupOfChain (k : Fin 54) : Fin 18 := ⟨k / 3, by omega⟩

/-- Chains whose group digest is not disclosed. -/
def active (G : Finset (Fin 18)) : Finset (Fin 54) :=
  Finset.univ.filter fun k => groupOfChain k ∉ G

/-- Position zero reveals a source; positive positions reveal chain outputs. -/
def chainNode (k : Fin 54) (p : Fin 19) : Name :=
  if h : p.val = 0 then src k else cv k ⟨p.val - 1, by omega⟩

/-- Positions of total cost s; inactive positions are fixed to make choices canonical. -/
irreducible_def positions (S : Finset (Fin 54)) (s : ℕ) : Finset (Fin 54 → Fin 19) :=
  Finset.univ.filter fun t => (∀ k ∉ S, t k = 18) ∧ ∑ k ∈ S, (18 - (t k).val) = s

theorem mem_positions (S : Finset (Fin 54)) (s : ℕ) (t : Fin 54 → Fin 19) :
    t ∈ positions S s ↔ (∀ k ∉ S, t k = 18) ∧ ∑ k ∈ S, (18 - (t k).val) = s := by
  rw [positions_def, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

abbrev Choice := Finset (Fin 18) × (Fin 54 → Fin 19)

@[irreducible] def shape (b s : ℕ) : Finset Choice :=
  ((Finset.powersetCard b (Finset.univ : Finset (Fin 18))).sigma fun G =>
    positions (active G) s).image fun x => (x.1, x.2)

@[irreducible] def shapes : Finset Choice := shape 6 84

def cutOf (c : Choice) : Finset Name :=
  c.1.image gv ∪ (active c.1).image fun k => chainNode k (c.2 k)

@[irreducible] def family : Finset (Finset Name) := shapes.image cutOf

theorem mem_shape_iff (b s : ℕ) (c : Choice) :
    c ∈ shape b s ↔ c.1.card = b ∧ c.2 ∈ positions (active c.1) s := by
  unfold shape
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨G, t⟩, hx, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_powersetCard] at hx
    exact ⟨hx.1.2, hx.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨c.1, c.2⟩, ?_, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, h1⟩, h2⟩

theorem mem_shapes_iff (c : Choice) :
    c ∈ shapes ↔ c.1.card = 6 ∧ c.2 ∈ positions (active c.1) 84 := by
  rw [shapes, mem_shape_iff]

theorem groupOfChain_chainOf (j : Fin 18) (a : Fin 3) : groupOfChain (chainOf j a) = j := by
  apply Fin.ext
  simp only [groupOfChain, chainOf]
  omega

theorem chainOf_injective : Function.Injective fun p : Fin 18 × Fin 3 => chainOf p.1 p.2 := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  simp only [chainOf, Fin.mk.injEq] at h
  have hj : j = j' := Fin.ext (by omega)
  have ha : a = a' := Fin.ext (by omega)
  rw [hj, ha]

theorem mem_active_iff (G : Finset (Fin 18)) (k : Fin 54) :
    k ∈ active G ↔ groupOfChain k ∉ G := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]

theorem active_eq_image (G : Finset (Fin 18)) :
    active G = (Gᶜ ×ˢ (Finset.univ : Finset (Fin 3))).image fun p => chainOf p.1 p.2 := by
  ext k
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product, Finset.mem_compl, and_true, Prod.exists]
  constructor
  · intro h
    refine ⟨groupOfChain k, ⟨k % 3, by omega⟩, h, ?_⟩
    apply Fin.ext
    simp only [chainOf, groupOfChain]
    omega
  · rintro ⟨j, a, hj, rfl⟩
    rwa [groupOfChain_chainOf]

theorem card_active (G : Finset (Fin 18)) : (active G).card = 3 * (18 - G.card) := by
  rw [active_eq_image, Finset.card_image_of_injective _ chainOf_injective,
    Finset.card_product, Finset.card_compl, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  omega

theorem card_positions (S : Finset (Fin 54)) (s : ℕ) : (positions S s).card = comp S.card s := by
  rw [← card_comp]
  refine Finset.card_nbij' (fun t i => Fin.rev (t (S.equivFin.symm i)))
    (fun c k => if h : k ∈ S then Fin.rev (c (S.equivFin ⟨k, h⟩)) else 18) ?_ ?_ ?_ ?_
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
    Function.Injective fun x : (_ : Finset (Fin 18)) × (Fin 54 → Fin 19) =>
      ((x.1, x.2) : Choice) := by
  rintro ⟨G, t⟩ ⟨G', t'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem card_shape (b s : ℕ) :
    (shape b s).card = Nat.choose 18 b * comp (3 * (18 - b)) s := by
  unfold shape
  rw [Finset.card_image_of_injective _ choice_mk_injective, Finset.card_sigma]
  have h : ∀ G ∈ Finset.powersetCard b (Finset.univ : Finset (Fin 18)),
      (positions (active G) s).card = comp (3 * (18 - b)) s := by
    intro G hG
    rw [Finset.mem_powersetCard] at hG
    rw [card_positions, card_active, hG.2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem chainNode_eq_src_iff (k k' : Fin 54) (p : Fin 19) :
    chainNode k p = src k' ↔ k = k' ∧ p = 0 := by
  unfold chainNode
  split_ifs with h
  · simp only [Name.src.injEq, Fin.ext_iff, Fin.val_zero, h, and_true]
  · simp only [false_iff, not_and, Fin.ext_iff, Fin.val_zero]
    intro _ hp
    exact h hp

theorem chainNode_eq_cv_iff (k k' : Fin 54) (p : Fin 19) (t : Fin 18) :
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

theorem chainNode_ne_gv (k : Fin 54) (p : Fin 19) (j : Fin 18) : chainNode k p ≠ gv j := by
  unfold chainNode
  split_ifs <;> simp

theorem chainNode_len (k : Fin 54) (p : Fin 19) : (chainNode k p).len = 128 := by
  unfold chainNode
  split_ifs <;> rfl

theorem chainNode_injective (t : Fin 54 → Fin 19) :
    Function.Injective fun k => chainNode k (t k) := by
  intro k k' h
  unfold chainNode at h
  dsimp only at h
  split_ifs at h <;> simp only [Name.src.injEq, Name.cv.injEq] at h <;> tauto

theorem mem_cutOf_iff (c : Choice) (n : Name) :
    n ∈ cutOf c ↔ (∃ j ∈ c.1, gv j = n) ∨
      ∃ k ∈ active c.1, chainNode k (c.2 k) = n := by
  unfold cutOf
  simp only [Finset.mem_union, Finset.mem_image]

theorem gv_mem_cutOf_iff' (c : Choice) (j : Fin 18) : gv j ∈ cutOf c ↔ j ∈ c.1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨j', hj', h⟩ | ⟨k, _, h⟩)
    · rw [Name.gv.injEq] at h
      exact h ▸ hj'
    · exact absurd h (chainNode_ne_gv _ _ _)
  · intro h
    exact Or.inl ⟨j, h, rfl⟩

theorem src_mem_cutOf_iff' (c : Choice) (k : Fin 54) :
    src k ∈ cutOf c ↔ k ∈ active c.1 ∧ c.2 k = 0 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨j, _, h⟩ | ⟨k', hk', h⟩)
    · exact absurd h (by simp)
    · rw [chainNode_eq_src_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨hk', h⟩
  · rintro ⟨hk, h⟩
    exact Or.inr ⟨k, hk, (chainNode_eq_src_iff _ _ _).mpr ⟨rfl, h⟩⟩

theorem cv_mem_cutOf_iff' (c : Choice) (k : Fin 54) (t : Fin 18) :
    cv k t ∈ cutOf c ↔ k ∈ active c.1 ∧ (c.2 k).val = t.val + 1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨j, _, h⟩ | ⟨k', hk', h⟩)
    · exact absurd h (by simp)
    · rw [chainNode_eq_cv_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨hk', h⟩
  · rintro ⟨hk, h⟩
    exact Or.inr ⟨k, hk, (chainNode_eq_cv_iff _ _ _ _).mpr ⟨rfl, h⟩⟩

theorem not_mem_cutOf_of_len {c : Choice} {n : Name} (hn : n.len ≠ 128) : n ∉ cutOf c := by
  intro h
  rw [mem_cutOf_iff] at h
  rcases h with ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
  · exact hn rfl
  · exact hn (chainNode_len _ _)

theorem mem_cutOf_len' {c : Choice} {n : Name} (hn : n ∈ cutOf c) : n.len = 128 := by
  by_contra h
  exact not_mem_cutOf_of_len h hn

theorem ci_not_mem_cutOf (c : Choice) (k : Fin 54) (t : Fin 18) : ci k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem ch_not_mem_cutOf (c : Choice) (k : Fin 54) (t : Fin 18) : ch k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem gc_not_mem_cutOf (c : Choice) (j : Fin 18) : gc j ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem gh_not_mem_cutOf (c : Choice) (j : Fin 18) : gh j ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem pos_of_mem_shapes {c : Choice} (hc : c ∈ shapes) :
    ∀ k ∉ active c.1, c.2 k = 18 :=
  ((mem_positions _ _ _).mp ((mem_shapes_iff c).mp hc).2).1

/-- The canonical choice is determined by its disclosure set. -/
theorem cutOf_injective : Set.InjOn cutOf shapes := by
  intro c hc c' hc' h
  rw [Finset.mem_coe] at hc hc'
  have hG : c.1 = c'.1 := by
    ext j
    rw [← gv_mem_cutOf_iff' c j, ← gv_mem_cutOf_iff' c' j, h]
  have ht : c.2 = c'.2 := by
    funext k
    by_cases hk : k ∈ active c.1
    · have hmem : chainNode k (c.2 k) ∈ cutOf c' := by
        rw [← h, mem_cutOf_iff]
        exact Or.inr ⟨k, hk, rfl⟩
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
    · rw [pos_of_mem_shapes hc k hk, pos_of_mem_shapes hc' k (by rwa [← hG])]
  exact Prod.ext hG ht

/-- The graph cut family realizes the previously certified coefficient exactly. -/
theorem card_family_eq : family.card = Nat.choose 18 6 * comp 36 84 := by
  have hn : 3 * (18 - 6) = 36 := by norm_num
  have he : comp (3 * (18 - 6)) 84 = comp 36 84 := congrArg (fun n => comp n 84) hn
  calc
    family.card = shapes.card := by
      unfold family
      exact Finset.card_image_of_injOn cutOf_injective
    _ = Nat.choose 18 6 * comp (3 * (18 - 6)) 84 := by
      unfold shapes
      exact card_shape 6 84
    _ = Nat.choose 18 6 * comp 36 84 := congrArg (fun v => Nat.choose 18 6 * v) he

theorem card_family : 45 * 2 ^ 109 ≤ family.card :=
  single_shape_102_ge.trans_eq card_family_eq.symm

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

theorem evaluated_gh_iff' (c : Choice) (j : Fin 18) :
    Evaluated (cutOf c) (gh j) ↔ j ∉ c.1 := by
  constructor
  · intro h
    rw [← gv_mem_cutOf_iff' c j]
    exact h.2 (gv j) (Above.child rfl)
  · intro hj
    refine evaluated_of_child rfl (gh_not_mem_cutOf c j) ?_
    refine evaluated_of_child rfl ?_ (evaluated_rc' c)
    rw [gv_mem_cutOf_iff']
    exact hj

theorem evaluated_ch_iff' (c : Choice) (k : Fin 54) (t : Fin 18) :
    Evaluated (cutOf c) (ch k t) ↔ k ∈ active c.1 ∧ (c.2 k).val ≤ t.val := by
  unfold Evaluated
  simp only [above_iff_mem_ancSet, ancSet, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert, Finset.mem_singleton,
    forall_eq, ci_not_mem_cutOf, ch_not_mem_cutOf, cv_mem_cutOf_iff', gc_not_mem_cutOf,
    gh_not_mem_cutOf, gv_mem_cutOf_iff', rc_not_mem_cutOf, rh_not_mem_cutOf,
    not_false_eq_true, true_and, and_true, implies_true, mem_active_iff, groupOfChain]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    by_contra hlt
    have hv := (c.2 k).isLt
    exact @h1 ⟨(c.2 k).val - 1, by omega⟩ (by rw [Fin.le_def]; dsimp only; omega)
      ⟨h2, by dsimp only; omega⟩
  · rintro ⟨h2, hle⟩
    refine ⟨fun x hx h => ?_, h2⟩
    rw [Fin.le_def] at hx
    omega

/-- The input of a chain hash is evaluated exactly when the chain hash is. -/
theorem evaluated_ci_iff' (c : Choice) (k : Fin 54) (t : Fin 18) :
    Evaluated (cutOf c) (ci k t) ↔ k ∈ active c.1 ∧ (c.2 k).val ≤ t.val := by
  rw [← evaluated_ch_iff']
  constructor
  · intro h
    exact ⟨ch_not_mem_cutOf c k t, fun m hm => h.2 m (Above.step rfl hm)⟩
  · intro h
    exact evaluated_of_child rfl (ci_not_mem_cutOf c k t) h

theorem child_cv_of_lt (k : Fin 54) (t : Fin 18) (ht : t.val < 17) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]

theorem child_cv_of_eq (k : Fin 54) (t : Fin 18) (ht : t.val = 17) :
    child (cv k t) = some (gc (groupOfChain k)) := by
  simp only [Name.child]
  rw [dif_pos ht]
  rfl

theorem isCut_cutOf (c : Choice) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_len' hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    rcases hn with ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
    · exact forall_above_of_child rfl (evaluated_rc' c)
    · have hk' := (mem_active_iff _ _).mp hk
      unfold chainNode
      split_ifs with h0
      · exact forall_above_of_child rfl
          ((evaluated_ci_iff' c k 0).mpr ⟨hk, by rw [h0]; exact Nat.zero_le _⟩)
      · by_cases h18 : (c.2 k).val = 18
        · refine forall_above_of_child (child_cv_of_eq k _ (by dsimp only; omega))
            (evaluated_of_child rfl (gc_not_mem_cutOf c _) ((evaluated_gh_iff' c _).mpr hk'))
        · have hlt := (c.2 k).isLt
          refine forall_above_of_child (child_cv_of_lt k _ (by dsimp only; omega))
            ((evaluated_ci_iff' c k _).mpr ⟨hk, ?_⟩)
          dsimp only
          omega
  covers := by
    intro k
    by_cases hk : k ∈ active c.1
    · by_cases h0 : (c.2 k).val = 0
      · exact Or.inl ((src_mem_cutOf_iff' c k).mpr ⟨hk, Fin.ext h0⟩)
      · have hlt := (c.2 k).isLt
        refine Or.inr ⟨cv k ⟨(c.2 k).val - 1, by omega⟩,
          (cv_mem_cutOf_iff' c k _).mpr ⟨hk, by dsimp only; omega⟩, ?_⟩
        rw [above_iff_mem_ancSet]
        simp [ancSet]
    · rw [mem_active_iff, not_not] at hk
      refine Or.inr ⟨gv (groupOfChain k), (gv_mem_cutOf_iff' c _).mpr hk, ?_⟩
      rw [above_iff_mem_ancSet]
      simp [ancSet, groupOfChain]

theorem cutOf_disjoint (c : Choice) :
    Disjoint (c.1.image gv) ((active c.1).image fun k => chainNode k (c.2 k)) := by
  apply Finset.disjoint_left.mpr
  intro n hnG hnC
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hnG
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hnC
  exact chainNode_ne_gv k (c.2 k) j hk

theorem card_cutOf {c : Choice} (hc : c ∈ shapes) : (cutOf c).card = 42 := by
  rw [cutOf, Finset.card_union_of_disjoint (cutOf_disjoint c),
    Finset.card_image_of_injective _ (fun _ _ h => Name.gv.inj h),
    Finset.card_image_of_injective _ (chainNode_injective c.2), card_active,
    ((mem_shapes_iff c).mp hc).1]

theorem revealBits_cutOf {c : Choice} (hc : c ∈ shapes) :
    graph.revealBits (fins (cutOf c)) = 42 * 128 := by
  rw [revealBits_eq]
  calc
    ∑ n ∈ cutOf c, n.len = ∑ _n ∈ cutOf c, 128 :=
      Finset.sum_congr rfl fun _ hn => mem_cutOf_len' hn
    _ = 42 * 128 := by rw [Finset.sum_const, smul_eq_mul, card_cutOf hc]

theorem sum_fin18_ge (v : ℕ) : ∑ t : Fin 18, (if v ≤ t.val then 1 else 0) = 18 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 18, ← Finset.card_filter]
  have : (Finset.range 18).filter (fun t => v ≤ t) = Finset.Ico v 18 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

theorem cost_cutOf {c : Choice} (hc : c ∈ shapes) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost = 101 := by
  obtain ⟨hG, ht⟩ := (mem_shapes_iff c).mp hc
  have h_gh : ∑ j, (if Evaluated (cutOf c) (gh j) then 1 else 0) = 12 := by
    simp only [evaluated_gh_iff']
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun j => j ∉ c.1) = c.1ᶜ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    rw [this, Finset.card_compl, Fintype.card_fin, hG]
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) = 84 := by
    simp only [evaluated_ch_iff']
    have hin : ∀ k, ∑ t : Fin 18, (if k ∈ active c.1 ∧ (c.2 k).val ≤ t.val then 1 else 0) =
        if k ∈ active c.1 then 18 - (c.2 k).val else 0 := by
      intro k
      by_cases hk : k ∈ active c.1
      · simp only [hk, true_and, if_true]
        exact sum_fin18_ge _
      · simp only [hk, false_and, if_false, Finset.sum_const_zero]
    simp only [hin]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact ((mem_positions _ _ _).mp ht).2
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh' c), h_ch, h_gh]

theorem reconstructCost_cutOf {c : Choice} (hc : c ∈ shapes) :
    graph.reconstructCost (fins (cutOf c)) = 101 := by
  rw [reconstructCost_eq, cost_cutOf hc]

theorem isCut_of_mem_family {A : Finset Name} (h : A ∈ family) : IsCut A := by
  rw [family, Finset.mem_image] at h
  obtain ⟨c, _, rfl⟩ := h
  exact isCut_cutOf c

theorem card_of_mem_family {A : Finset Name} (h : A ∈ family) : A.card = 42 := by
  rw [family, Finset.mem_image] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact card_cutOf hc

theorem cost_of_mem_family {A : Finset Name} (h : A ∈ family) :
    ∑ n ∈ evaluatedSet A, n.cost = 101 := by
  rw [family, Finset.mem_image] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact cost_cutOf hc

#print axioms card_family
#print axioms isCut_of_mem_family
#print axioms card_of_mem_family
#print axioms cost_of_mem_family
#print axioms reconstructCost_cutOf
#print axioms revealBits_cutOf
end ShallowForest
end OptimalOTS
