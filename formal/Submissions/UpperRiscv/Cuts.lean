import Submissions.UpperRiscv.Tree
import Submissions.UpperRiscv.Count

/-!
# Disclosure sets of the bare-chain forest

A disclosure set is described by a *choice* `c : Fin 32 → Fin 32`: for every chain `k` the
position `c k ∈ {0, …, 31}` of the revealed chain input `ci k (c k)` (`0` reveals the input
`ci k 0`, whose value is the source `z_k`). `cutOf c` is always a cut (`isCut_cutOf`), the choice
is determined by the set (`cutOf_injective`), and its reconstruction cost is
`Σ (32 - c k) + 15` (`cost_cutOf`). `FixedChoice.lean` instantiates this with the digits of the
index.
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
def chainNode (k : Fin 32) (p : Fin 32) : Name := ci k p

/-- A choice of disclosure set: one position per chain. -/
abbrev Choice := Fin 32 → Fin 32

/-- The disclosure set of a choice. -/
def cutOf (c : Choice) : Finset Name := Finset.univ.image fun k => chainNode k (c k)

/-! ### Membership in a disclosure set -/

theorem chainNode_len (k : Fin 32) (p : Fin 32) : (chainNode k p).len = chainBits k := rfl

theorem chainNode_injective (c : Choice) : Function.Injective (fun k => chainNode k (c k)) := by
  intro k l equal
  simp only [chainNode, Name.ci.injEq] at equal
  exact equal.1

theorem mem_cutOf_iff (c : Choice) (n : Name) :
    n ∈ cutOf c ↔ ∃ k, chainNode k (c k) = n := by
  unfold cutOf
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem ci_mem_cutOf_iff (c : Choice) (k : Fin 32) (t : Fin 32) :
    ci k t ∈ cutOf c ↔ c k = t := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    simp only [chainNode, Name.ci.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact h
  · intro h
    exact ⟨k, by simp [chainNode, h]⟩

theorem mem_cutOf_ci {c : Choice} {n : Name} (hn : n ∈ cutOf c) : ∃ k t, n = ci k t := by
  rw [mem_cutOf_iff] at hn
  obtain ⟨k, rfl⟩ := hn
  exact ⟨k, c k, rfl⟩

theorem src_not_mem_cutOf (c : Choice) (k : Fin 32) : src k ∉ cutOf c := by
  intro h; obtain ⟨_, _, h'⟩ := mem_cutOf_ci h; cases h'

theorem ch_not_mem_cutOf (c : Choice) (k : Fin 32) (t : Fin 32) : ch k t ∉ cutOf c := by
  intro h; obtain ⟨_, _, h'⟩ := mem_cutOf_ci h; cases h'

theorem cv_not_mem_cutOf (c : Choice) (k : Fin 32) (t : Fin 32) : cv k t ∉ cutOf c := by
  intro h; obtain ⟨_, _, h'⟩ := mem_cutOf_ci h; cases h'

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c := by
  intro h; obtain ⟨_, _, h'⟩ := mem_cutOf_ci h; cases h'

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c := by
  intro h; obtain ⟨_, _, h'⟩ := mem_cutOf_ci h; cases h'

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
  exact ((ci_mem_cutOf_iff c' k (c k)).mp hmem).symm

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

theorem evaluated_ch_iff (c : Choice) (k : Fin 32) (t : Fin 32) :
    Evaluated (cutOf c) (ch k t) ↔ (c k).val ≤ t.val := by
  unfold Evaluated
  simp only [above_iff_mem_ancSet, ancSet, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert, Finset.mem_singleton,
    forall_eq, ci_mem_cutOf_iff, ch_not_mem_cutOf, cv_not_mem_cutOf, rc_not_mem_cutOf,
    rh_not_mem_cutOf, not_false_eq_true, true_and, and_true, implies_true]
  constructor
  · intro h1
    by_contra hlt
    exact h1 (show t < c k from Fin.lt_def.mpr (by omega)) rfl
  · intro hle x hx h
    rw [Fin.lt_def] at hx
    rw [h] at hle
    omega

/-- The input of a chain hash is evaluated exactly when it lies strictly above the revealed
position. -/
theorem evaluated_ci_iff (c : Choice) (k : Fin 32) (t : Fin 32) :
    Evaluated (cutOf c) (ci k t) ↔ (c k).val < t.val := by
  constructor
  · intro h
    have hne : c k ≠ t := fun e => h.1 ((ci_mem_cutOf_iff c k t).mpr e)
    have hle := (evaluated_ch_iff c k t).mp ⟨ch_not_mem_cutOf c k t, fun m hm => h.2 m (Above.step rfl hm)⟩
    have : (c k).val ≠ t.val := fun e => hne (Fin.ext e)
    omega
  · intro h
    refine evaluated_of_child rfl (fun e => ?_) ((evaluated_ch_iff c k t).mpr h.le)
    have := (ci_mem_cutOf_iff c k t).mp e
    rw [this] at h
    exact lt_irrefl _ h

theorem child_cv_of_lt (k : Fin 32) (t : Fin 32) (ht : t.val < 31) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]

theorem child_cv_of_eq (k : Fin 32) (t : Fin 32) (ht : t.val = 31) :
    child (cv k t) = some rc := by
  simp only [Name.child]
  rw [dif_pos ht]

theorem isCut_cutOf (c : Choice) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_ci hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    obtain ⟨k, rfl⟩ := hn
    exact forall_above_of_child rfl ((evaluated_ch_iff c k (c k)).mpr le_rfl)
  covers := by
    intro k
    refine Or.inr ⟨ci k (c k), (ci_mem_cutOf_iff c k _).mpr rfl, ?_⟩
    rw [above_iff_mem_ancSet]
    simp [ancSet]

theorem sum_fin32_ge (v : ℕ) : ∑ t : Fin 32, (if v ≤ t.val then 1 else 0) = 32 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 32, ← Finset.card_filter]
  have : (Finset.range 32).filter (fun t => v ≤ t) = Finset.Ico v 32 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

/-- Every cut reveals twenty-four 160-bit and eight 192-bit states. -/
theorem reveal_cutOf (c : Choice) : ∑ n ∈ cutOf c, n.len = 5376 := by
  unfold cutOf
  rw [Finset.sum_image]
  · change ∑ k : Fin 32, chainBits k = 5376
    decide +kernel
  · intro a _ b _ h
    exact chainNode_injective c h

/-- The reconstruction cost of a disclosure set: the chain steps and the 15-block root. -/
theorem cost_cutOf (c : Choice) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost = (∑ k, (32 - (c k).val)) + 15 := by
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) =
      ∑ k, (32 - (c k).val) := by
    simp only [evaluated_ch_iff]
    exact Finset.sum_congr rfl fun k _ => sum_fin32_ge _
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh c), h_ch]

end Forest

end OptimalOTS
