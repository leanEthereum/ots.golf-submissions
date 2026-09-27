import Submissions.UpperRiscv.Tree
import Submissions.UpperRiscv.Count

/-!
# Disclosure sets of the bare-chain forest

A disclosure set is described by a *choice* `c : Fin 33 → Fin 33`: for every chain `k` the
position `c k ∈ {0, …, 32}` of its revealed node, the chain input `ci k (c k)` for `c k < 32`
(`0` reveals the input `ci k 0`, whose value is the source `z_k`) and the top `tp k` for
`c k = 32`. `cutOf c` is always a cut (`isCut_cutOf`), the choice is determined by the set
(`cutOf_injective`), and its reconstruction cost is `Σ (32 - c k) + 13` (`cost_cutOf`).
`FixedChoice.lean` instantiates this with the digits of the index.
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
def chainNode (k : Fin 33) (p : Fin 33) : Name :=
  if h : p.val < 32 then ci k ⟨p.val, h⟩ else tp k

/-- A choice of disclosure set: one position per chain. -/
abbrev Choice := Fin 33 → Fin 33

/-- The disclosure set of a choice. -/
def cutOf (c : Choice) : Finset Name := Finset.univ.image fun k => chainNode k (c k)

/-! ### Membership in a disclosure set -/

theorem chainNode_len (k : Fin 33) (p : Fin 33) :
    (chainNode k p).len = if p.val < 32 then chainBits k else topBits k := by
  unfold chainNode; split_ifs <;> rfl

theorem chainNode_injective (c : Choice) : Function.Injective (fun k => chainNode k (c k)) := by
  intro k l equal
  simp only [chainNode] at equal
  split_ifs at equal <;> simp_all

theorem mem_cutOf_iff (c : Choice) (n : Name) :
    n ∈ cutOf c ↔ ∃ k, chainNode k (c k) = n := by
  unfold cutOf
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem ci_mem_cutOf_iff (c : Choice) (k : Fin 33) (t : Fin 32) :
    ci k t ∈ cutOf c ↔ (c k).val = t.val := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    unfold chainNode at h
    split_ifs at h with hp
    all_goals first
      | (simp only [Name.ci.injEq] at h; obtain ⟨rfl, rfl⟩ := h; try rfl)
      | cases h
  · intro h
    refine ⟨k, ?_⟩
    simp only [chainNode, h, t.isLt, dif_pos]

theorem tp_mem_cutOf_iff (c : Choice) (k : Fin 33) :
    tp k ∈ cutOf c ↔ (c k).val = 32 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    unfold chainNode at h
    split_ifs at h with hp
    all_goals first
      | (simp only [Name.tp.injEq] at h; subst h; have := (c k').isLt; omega)
      | cases h
  · intro h
    refine ⟨k, ?_⟩
    simp only [chainNode, h, lt_irrefl, dif_neg, not_false_eq_true]

theorem mem_cutOf_values {c : Choice} {n : Name} (hn : n ∈ cutOf c) :
    (∃ k t, n = ci k t) ∨ ∃ k, n = tp k := by
  rw [mem_cutOf_iff] at hn
  obtain ⟨k, rfl⟩ := hn
  unfold chainNode
  split_ifs
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

theorem src_not_mem_cutOf (c : Choice) (k : Fin 33) : src k ∉ cutOf c := by
  intro h; rcases mem_cutOf_values h with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> cases h'

theorem ch_not_mem_cutOf (c : Choice) (k : Fin 33) (t : Fin 32) : ch k t ∉ cutOf c := by
  intro h; rcases mem_cutOf_values h with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> cases h'

theorem cv_not_mem_cutOf (c : Choice) (k : Fin 33) (t : Fin 32) : cv k t ∉ cutOf c := by
  intro h; rcases mem_cutOf_values h with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> cases h'

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c := by
  intro h; rcases mem_cutOf_values h with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> cases h'

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c := by
  intro h; rcases mem_cutOf_values h with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> cases h'

theorem card_cutOf (c : Choice) : (cutOf c).card = 33 := by
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
  apply Fin.ext
  unfold chainNode at hmem
  split_ifs at hmem with hp
  · exact ((ci_mem_cutOf_iff c' k _).mp hmem).symm
  · have := (tp_mem_cutOf_iff c' k).mp hmem
    have := (c k).isLt
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

/-- A top is evaluated exactly when the chain reveals an input. -/
theorem evaluated_tp_iff (c : Choice) (k : Fin 33) :
    Evaluated (cutOf c) (tp k) ↔ (c k).val < 32 := by
  constructor
  · intro h
    have hne := h.1
    rw [tp_mem_cutOf_iff] at hne
    have := (c k).isLt
    omega
  · intro h
    refine evaluated_of_child rfl (fun e => ?_) (evaluated_rc c)
    rw [tp_mem_cutOf_iff] at e
    omega

theorem evaluated_ch_iff (c : Choice) (k : Fin 33) (t : Fin 32) :
    Evaluated (cutOf c) (ch k t) ↔ (c k).val ≤ t.val := by
  have hk := (c k).isLt
  constructor
  · intro h
    by_contra hlt
    by_cases h32 : (c k).val = 32
    · refine h.2 (tp k) ?_ ((tp_mem_cutOf_iff c k).mpr h32)
      rw [above_iff_mem_ancSet]
      simp [ancSet]
    · let t' : Fin 32 := ⟨(c k).val, by omega⟩
      refine h.2 (ci k t') ?_ ((ci_mem_cutOf_iff c k t').mpr rfl)
      rw [above_iff_mem_ancSet]
      simp only [ancSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inl (Or.inl (Or.inl ⟨t', Fin.lt_def.mpr (by simp only [t']; omega), rfl⟩))
  · intro hle
    refine ⟨ch_not_mem_cutOf c k t, fun m hm hmA => ?_⟩
    rw [above_iff_mem_ancSet] at hm
    rcases mem_cutOf_values hmA with ⟨k', t', rfl⟩ | ⟨k', rfl⟩
    · have e := (ci_mem_cutOf_iff c k' t').mp hmA
      simp only [ancSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_false,
        Name.ci.injEq, and_false, exists_false, false_or] at hm
      obtain ⟨t'', ht'', rfl, rfl⟩ := hm
      rw [Fin.lt_def] at ht''
      omega
    · have e := (tp_mem_cutOf_iff c k').mp hmA
      simp only [ancSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_false,
        Name.tp.injEq, false_or, exists_false, and_false] at hm
      subst hm
      have := t.isLt
      omega

/-- The input of a chain hash is evaluated exactly when it lies strictly above the revealed
position. -/
theorem evaluated_ci_iff (c : Choice) (k : Fin 33) (t : Fin 32) :
    Evaluated (cutOf c) (ci k t) ↔ (c k).val < t.val := by
  constructor
  · intro h
    have hne : (c k).val ≠ t.val := fun e => h.1 ((ci_mem_cutOf_iff c k t).mpr e)
    have hle := (evaluated_ch_iff c k t).mp ⟨ch_not_mem_cutOf c k t, fun m hm => h.2 m (Above.step rfl hm)⟩
    omega
  · intro h
    refine evaluated_of_child rfl (fun e => ?_) ((evaluated_ch_iff c k t).mpr h.le)
    have := (ci_mem_cutOf_iff c k t).mp e
    omega

theorem child_cv_of_lt (k : Fin 33) (t : Fin 32) (ht : t.val < 31) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]

theorem child_cv_of_eq (k : Fin 33) (t : Fin 32) (ht : t.val = 31) :
    child (cv k t) = some (tp k) := by
  simp only [Name.child]
  rw [dif_pos ht]

theorem isCut_cutOf (c : Choice) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_values hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    obtain ⟨k, rfl⟩ := hn
    unfold chainNode
    split_ifs with hp
    · exact forall_above_of_child rfl ((evaluated_ch_iff c k _).mpr le_rfl)
    · exact forall_above_of_child rfl (evaluated_rc c)
  covers := by
    intro k
    refine Or.inr ⟨chainNode k (c k), (mem_cutOf_iff c _).mpr ⟨k, rfl⟩, ?_⟩
    rw [above_iff_mem_ancSet]
    unfold chainNode
    split_ifs <;> simp [ancSet]

theorem sum_fin32_ge (v : ℕ) : ∑ t : Fin 32, (if v ≤ t.val then 1 else 0) = 32 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 32, ← Finset.card_filter]
  have : (Finset.range 32).filter (fun t => v ≤ t) = Finset.Ico v 32 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

/-- A choice reveals a top only on the cap chains. -/
def CapChoice (c : Choice) : Prop := ∀ k, (c k).val = 32 → isCap k

/-- A cap choice reveals twenty-one 144-bit and twelve 192-bit states. -/
theorem reveal_cutOf (c : Choice) (hc : CapChoice c) : ∑ n ∈ cutOf c, n.len = 5328 := by
  unfold cutOf
  rw [Finset.sum_image]
  · have e : ∀ k : Fin 33, (chainNode k (c k)).len = chainBits k := by
      intro k
      rw [chainNode_len]
      split_ifs with h
      · rfl
      · exact topBits_cap (hc k (by have := (c k).isLt; omega))
    simp only [e]
    change ∑ k : Fin 33, chainBits k = 5328
    decide +kernel
  · intro a _ b _ h
    exact chainNode_injective c h

/-- The reconstruction cost of a disclosure set: the chain steps and the 13-block root. -/
theorem cost_cutOf (c : Choice) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost = (∑ k, (32 - (c k).val)) + 13 := by
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) =
      ∑ k, (32 - (c k).val) := by
    simp only [evaluated_ch_iff]
    exact Finset.sum_congr rfl fun k _ => sum_fin32_ge _
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh c), h_ch]

end Forest

end OptimalOTS
