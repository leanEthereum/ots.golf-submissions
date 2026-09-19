import Submissions.UpperRiscv.Tree
import Submissions.UpperRiscv.Count

/-!
# Disclosure sets of the flat forest

A disclosure set is described by a *choice* `c : Fin 32 → Fin 16`: for every chain `k` the
position `c k ∈ {0, …, 15}` of the revealed chain value (`0` reveals the source `z_k`, `p ≥ 1`
reveals `c_{k,p} = cv k (p-1)`). `cutOf c` is always a cut (`isCut_cutOf`), the choice is
determined by the set (`cutOf_injective`), and its reconstruction cost is `Σ (15 - c k) + 12`
(`cost_cutOf`). `FixedChoice.lean` instantiates this with the nibbles of the index.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

/-- The revealed node of chain `k` at position `p`. -/
def chainNode (k : Fin 32) (p : Fin 16) : Name :=
  if h : p.val = 0 then src k else cv k ⟨p.val - 1, by omega⟩

/-- A choice of disclosure set: one position per chain. -/
abbrev Choice := Fin 32 → Fin 16

/-- The disclosure set of a choice. -/
def cutOf (c : Choice) : Finset Name := Finset.univ.image fun k => chainNode k (c k)

/-! ### Membership in a disclosure set -/

theorem chainNode_eq_src_iff (k k' : Fin 32) (p : Fin 16) :
    chainNode k p = src k' ↔ k = k' ∧ p = 0 := by
  unfold chainNode
  split_ifs with h
  · simp only [Name.src.injEq, Fin.ext_iff, Fin.val_zero, h, and_true]
  · simp only [false_iff, not_and, Fin.ext_iff, Fin.val_zero]
    intro _ hp
    exact h hp

theorem chainNode_eq_cv_iff (k k' : Fin 32) (p : Fin 16) (t : Fin 15) :
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

theorem chainNode_len (k : Fin 32) (p : Fin 16) : (chainNode k p).len = 128 := by
  unfold chainNode
  split_ifs <;> rfl

theorem chainNode_injective (c : Choice) : Function.Injective (fun k => chainNode k (c k)) := by
  intro k l equal
  unfold chainNode at equal
  dsimp only at equal
  split_ifs at equal <;> simp only [Name.src.injEq, Name.cv.injEq, reduceCtorEq] at equal
  · exact equal
  · exact equal.1

theorem mem_cutOf_iff (c : Choice) (n : Name) :
    n ∈ cutOf c ↔ ∃ k, chainNode k (c k) = n := by
  unfold cutOf
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem src_mem_cutOf_iff (c : Choice) (k : Fin 32) : src k ∈ cutOf c ↔ c k = 0 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    rw [chainNode_eq_src_iff] at h
    obtain ⟨rfl, h⟩ := h
    exact h
  · intro h
    exact ⟨k, (chainNode_eq_src_iff _ _ _).mpr ⟨rfl, h⟩⟩

theorem cv_mem_cutOf_iff (c : Choice) (k : Fin 32) (t : Fin 15) :
    cv k t ∈ cutOf c ↔ (c k).val = t.val + 1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    rw [chainNode_eq_cv_iff] at h
    obtain ⟨rfl, h⟩ := h
    exact h
  · intro h
    exact ⟨k, (chainNode_eq_cv_iff _ _ _ _).mpr ⟨rfl, h⟩⟩

theorem not_mem_cutOf_of_len {c : Choice} {n : Name} (hn : n.len ≠ 128) : n ∉ cutOf c := by
  intro h
  rw [mem_cutOf_iff] at h
  obtain ⟨k, rfl⟩ := h
  exact hn (chainNode_len _ _)

theorem mem_cutOf_len {c : Choice} {n : Name} (hn : n ∈ cutOf c) : n.len = 128 := by
  by_contra h
  exact not_mem_cutOf_of_len h hn

theorem ci_not_mem_cutOf (c : Choice) (k : Fin 32) (t : Fin 15) : ci k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem ch_not_mem_cutOf (c : Choice) (k : Fin 32) (t : Fin 15) : ch k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem card_cutOf (c : Choice) : (cutOf c).card = 32 := by
  unfold cutOf
  rw [Finset.card_image_of_injective _ (chainNode_injective c), Finset.card_univ,
    Fintype.card_fin]

/-! ### Injectivity -/

/-- The choice is determined by its disclosure set. -/
theorem cutOf_injective {c c' : Choice} (h : cutOf c = cutOf c') : c = c' := by
  funext k
  have hmem : chainNode k (c k) ∈ cutOf c' := by
    rw [← h, mem_cutOf_iff]
    exact ⟨k, rfl⟩
  unfold chainNode at hmem
  split_ifs at hmem with h0
  · rw [src_mem_cutOf_iff] at hmem
    rw [hmem]
    exact Fin.ext h0
  · rw [cv_mem_cutOf_iff] at hmem
    apply Fin.ext
    rw [hmem]
    dsimp only
    omega

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

theorem evaluated_rh (c : Choice) : Evaluated (cutOf c) rh :=
  ⟨rh_not_mem_cutOf c, fun m hm => absurd hm (not_above_rh m)⟩

theorem evaluated_rc (c : Choice) : Evaluated (cutOf c) rc :=
  evaluated_of_child rfl (rc_not_mem_cutOf c) (evaluated_rh c)

theorem evaluated_ch_iff (c : Choice) (k : Fin 32) (t : Fin 15) :
    Evaluated (cutOf c) (ch k t) ↔ (c k).val ≤ t.val := by
  unfold Evaluated
  simp only [above_iff_mem_ancSet, ancSet, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert, Finset.mem_singleton,
    forall_eq, ci_not_mem_cutOf, ch_not_mem_cutOf, cv_mem_cutOf_iff, rc_not_mem_cutOf,
    rh_not_mem_cutOf, not_false_eq_true, true_and, and_true, implies_true]
  constructor
  · intro h1
    by_contra hlt
    have hv := (c k).isLt
    exact @h1 ⟨(c k).val - 1, by omega⟩ (by rw [Fin.le_def]; dsimp only; omega)
      (by dsimp only; omega)
  · intro hle x hx h
    rw [Fin.le_def] at hx
    omega

/-- The input of a chain hash is evaluated exactly when the chain hash is. -/
theorem evaluated_ci_iff (c : Choice) (k : Fin 32) (t : Fin 15) :
    Evaluated (cutOf c) (ci k t) ↔ (c k).val ≤ t.val := by
  rw [← evaluated_ch_iff]
  constructor
  · intro h
    exact ⟨ch_not_mem_cutOf c k t, fun m hm => h.2 m (Above.step rfl hm)⟩
  · intro h
    exact evaluated_of_child rfl (ci_not_mem_cutOf c k t) h

theorem child_cv_of_lt (k : Fin 32) (t : Fin 15) (ht : t.val < 14) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]

theorem child_cv_of_eq (k : Fin 32) (t : Fin 15) (ht : t.val = 14) :
    child (cv k t) = some rc := by
  simp only [Name.child]
  rw [dif_pos ht]

theorem isCut_cutOf (c : Choice) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_len hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    obtain ⟨k, rfl⟩ := hn
    unfold chainNode
    split_ifs with h0
    · exact forall_above_of_child rfl
        ((evaluated_ci_iff c k 0).mpr (by rw [h0]; exact Nat.zero_le _))
    · by_cases h15 : (c k).val = 15
      · exact forall_above_of_child (child_cv_of_eq k _ (by dsimp only; omega)) (evaluated_rc c)
      · have hlt := (c k).isLt
        refine forall_above_of_child (child_cv_of_lt k _ (by dsimp only; omega))
          ((evaluated_ci_iff c k _).mpr ?_)
        dsimp only
        omega
  covers := by
    intro k
    by_cases h0 : (c k).val = 0
    · exact Or.inl ((src_mem_cutOf_iff c k).mpr (Fin.ext h0))
    · have hlt := (c k).isLt
      refine Or.inr ⟨cv k ⟨(c k).val - 1, by omega⟩,
        (cv_mem_cutOf_iff c k _).mpr (by dsimp only; omega), ?_⟩
      rw [above_iff_mem_ancSet]
      simp [ancSet]

theorem sum_fin15_ge (v : ℕ) : ∑ t : Fin 15, (if v ≤ t.val then 1 else 0) = 15 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 15, ← Finset.card_filter]
  have : (Finset.range 15).filter (fun t => v ≤ t) = Finset.Ico v 15 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

/-- The reconstruction cost of a disclosure set: the chain steps and the 12-block root. -/
theorem cost_cutOf (c : Choice) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost = (∑ k, (15 - (c k).val)) + 12 := by
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) =
      ∑ k, (15 - (c k).val) := by
    simp only [evaluated_ch_iff]
    exact Finset.sum_congr rfl fun k _ => sum_fin15_ge _
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh c), h_ch]

end Forest

end OptimalOTS
