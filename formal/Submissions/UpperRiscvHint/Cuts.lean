import Submissions.UpperRiscvHint.Tree

/-!
# Disclosure sets of the chain forest

A disclosure set is described by a *choice* `c : Chain → Fin 32`: for every chain `k` a
position `c k ∈ {0, …, 31}`. A normal chain reveals the input `ci k (c k)`; a cap reveals one
level higher, `ci k (c k + 1)`, and position 31 of a cap reveals its top. `firstEval k (c k)` is
the first level the verifier hashes. `cutOf c` is always a cut (`isCut_cutOf`), the choice is
determined by the set (`cutOf_injective`), and its reconstruction cost is
`Σ (32 - firstEval k (c k)) + 14` (`cost_cutOf`). `FixedChoice.lean` instantiates this with the
digits of the index.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

open OptimalOTS.Dag

namespace Forest

open Name

/-- The first level of chain `k` the verifier hashes when the chain is revealed at position `p`;
`32` means none. -/
def firstEval (k : Chain) (p : Fin 32) : ℕ := if k.val < 14 ∨ 31 ≤ k.val then p.val + 1 else p.val

theorem firstEval_le (k : Chain) (p : Fin 32) : firstEval k p ≤ 32 := by
  unfold firstEval; split_ifs <;> omega

theorem firstEval_injective (k : Chain) : Function.Injective (firstEval k) := by
  intro p p' h
  unfold firstEval at h
  split_ifs at h <;> exact Fin.ext (by omega)

/-- The revealed node of chain `k` at position `p`. -/
def chainNode (k : Chain) (p : Fin 32) : Name :=
  if h : firstEval k p < 32 then ci k ⟨firstEval k p, h⟩ else top k

/-- A choice of disclosure set: one position per chain. -/
abbrev Choice := Chain → Fin 32

/-- The disclosure set of a choice. -/
def cutOf (c : Choice) : Finset Name := Finset.univ.image fun k => chainNode k (c k)

/-! ### Membership in a disclosure set -/

theorem cap_of_firstEval {k : Chain} {p : Fin 32} (h : ¬ firstEval k p < 32) :
    k.val < 14 ∨ 31 ≤ k.val := by
  unfold firstEval at h; split_ifs at h with hk <;> omega

def revealWidth (k : Chain) (p : Fin 32) : ℕ :=
  if k.val = 32 ∧ p.val = 31 then 144 else chainBits k

theorem chainNode_len (k : Chain) (p : Fin 32) : (chainNode k p).len = revealWidth k p := by
  have hp := p.isLt
  have hk := k.isLt
  unfold chainNode revealWidth firstEval
  split_ifs <;> simp only [Name.len, topBits, chainBits] <;> split_ifs <;> omega

theorem chainNode_len_le (k : Chain) (p : Fin 32) :
    (chainNode k p).len ≤ chainBits k + if k.val = 32 then 3 else 0 := by
  rw [chainNode_len]
  unfold revealWidth chainBits
  split_ifs <;> omega

theorem revealWidth_eq (k : Chain) (p : Fin 32) :
    revealWidth k p = chainBits k + if k.val = 32 ∧ p.val = 31 then 3 else 0 := by
  unfold revealWidth chainBits
  split_ifs <;> omega

theorem revealable_chainNode (k : Chain) (p : Fin 32) : Revealable (chainNode k p) := by
  unfold chainNode
  split_ifs with h
  · trivial
  · exact cap_of_firstEval h

/-- The chain of a node. -/
def chainOf : Name → Chain
  | src k | ci k _ | ch k _ | cv k _ | top k => k
  | rc | rh => 0

/-- The level of a revealable node: its input level, `32` for a top. -/
def levelOf : Name → ℕ
  | ci _ t => t.val
  | top _ => 32
  | _ => 0

theorem chainOf_chainNode (k : Chain) (p : Fin 32) : chainOf (chainNode k p) = k := by
  unfold chainNode; split_ifs <;> rfl

theorem levelOf_chainNode (k : Chain) (p : Fin 32) : levelOf (chainNode k p) = firstEval k p := by
  unfold chainNode
  split_ifs with h
  · rfl
  · show 32 = _
    have := firstEval_le k p
    omega

theorem chainNode_injective (c : Choice) : Function.Injective (fun k => chainNode k (c k)) := by
  intro k l equal
  simpa only [chainOf_chainNode] using congrArg chainOf equal

theorem mem_cutOf_iff (c : Choice) (n : Name) :
    n ∈ cutOf c ↔ ∃ k, chainNode k (c k) = n := by
  unfold cutOf
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem mem_cutOf_revealable {c : Choice} {n : Name} (hn : n ∈ cutOf c) : Revealable n := by
  rw [mem_cutOf_iff] at hn
  obtain ⟨k, rfl⟩ := hn
  exact revealable_chainNode k (c k)

theorem ci_mem_cutOf_iff (c : Choice) (k : Chain) (t : Fin 32) :
    ci k t ∈ cutOf c ↔ firstEval k (c k) = t.val := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    obtain rfl : k' = k := by have e := congrArg chainOf h; rw [chainOf_chainNode] at e; exact e
    have e := congrArg levelOf h; rw [levelOf_chainNode] at e; exact e
  · intro h
    refine ⟨k, ?_⟩
    unfold chainNode
    rw [dif_pos (by rw [h]; exact t.isLt)]
    exact congrArg (ci k) (Fin.ext h)

theorem top_mem_cutOf_iff (c : Choice) (k : Chain) :
    top k ∈ cutOf c ↔ 32 ≤ firstEval k (c k) := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    obtain rfl : k' = k := by have e := congrArg chainOf h; rw [chainOf_chainNode] at e; exact e
    have := congrArg levelOf h
    rw [levelOf_chainNode] at this
    exact this.ge
  · intro h
    refine ⟨k, ?_⟩
    unfold chainNode
    rw [dif_neg (by omega)]

theorem src_not_mem_cutOf (c : Choice) (k : Chain) : src k ∉ cutOf c :=
  fun h => mem_cutOf_revealable h

theorem ch_not_mem_cutOf (c : Choice) (k : Chain) (t : Fin 32) : ch k t ∉ cutOf c :=
  fun h => mem_cutOf_revealable h

theorem cv_not_mem_cutOf (c : Choice) (k : Chain) (t : Fin 32) : cv k t ∉ cutOf c :=
  fun h => mem_cutOf_revealable h

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c :=
  fun h => mem_cutOf_revealable h

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c :=
  fun h => mem_cutOf_revealable h

/-! ### Injectivity -/

/-- The choice is determined by its disclosure set. -/
theorem cutOf_injective {c c' : Choice} (h : cutOf c = cutOf c') : c = c' := by
  funext k
  have hmem : chainNode k (c k) ∈ cutOf c' := by
    rw [← h, mem_cutOf_iff]
    exact ⟨k, rfl⟩
  rw [mem_cutOf_iff] at hmem
  obtain ⟨k', e⟩ := hmem
  have hk : k' = k := by simpa only [chainOf_chainNode] using congrArg chainOf e
  rw [hk] at e
  have := congrArg levelOf e
  rw [levelOf_chainNode, levelOf_chainNode] at this
  exact (firstEval_injective k this).symm

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

theorem evaluated_top_iff (c : Choice) (k : Chain) :
    Evaluated (cutOf c) (top k) ↔ firstEval k (c k) < 32 := by
  constructor
  · intro h
    by_contra hge
    exact h.1 ((top_mem_cutOf_iff c k).mpr (by omega))
  · intro h
    exact evaluated_of_child rfl (fun e => by have := (top_mem_cutOf_iff c k).mp e; omega)
      (evaluated_rc c)

theorem evaluated_ch_iff (c : Choice) (k : Chain) (t : Fin 32) :
    Evaluated (cutOf c) (ch k t) ↔ firstEval k (c k) ≤ t.val := by
  unfold Evaluated
  simp only [above_iff_mem_ancSet, ancSet, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert, Finset.mem_singleton,
    forall_eq, ci_mem_cutOf_iff, top_mem_cutOf_iff, ch_not_mem_cutOf, cv_not_mem_cutOf,
    rc_not_mem_cutOf, rh_not_mem_cutOf, not_false_eq_true, true_and, and_true, implies_true]
  have hle := firstEval_le k (c k)
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hlt
    exact h1 (show t < ⟨firstEval k (c k), by omega⟩ from Fin.lt_def.mpr (by simp only; omega)) rfl
  · intro hle' 
    refine ⟨fun x hx h => ?_, by omega⟩
    rw [Fin.lt_def] at hx
    omega

/-- The input of a chain hash is evaluated exactly when it lies strictly above the revealed
position. -/
theorem evaluated_ci_iff (c : Choice) (k : Chain) (t : Fin 32) :
    Evaluated (cutOf c) (ci k t) ↔ firstEval k (c k) < t.val := by
  constructor
  · intro h
    have hne : firstEval k (c k) ≠ t.val := fun e => h.1 ((ci_mem_cutOf_iff c k t).mpr e)
    have hle := (evaluated_ch_iff c k t).mp
      ⟨ch_not_mem_cutOf c k t, fun m hm => h.2 m (Above.step rfl hm)⟩
    omega
  · intro h
    refine evaluated_of_child rfl (fun e => ?_) ((evaluated_ch_iff c k t).mpr h.le)
    have := (ci_mem_cutOf_iff c k t).mp e
    omega

theorem isCut_cutOf (c : Choice) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_revealable hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    obtain ⟨k, rfl⟩ := hn
    unfold chainNode
    split_ifs with h
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

/-- Fourteen wide chains, nineteen narrow chains, and at most three extra top bits. -/
theorem reveal_cutOf (c : Choice) : ∑ n ∈ cutOf c, n.len ≤ 5370 := by
  unfold cutOf
  rw [Finset.sum_image]
  · calc
      ∑ k : Chain, (chainNode k (c k)).len
          ≤ ∑ k : Chain, (chainBits k + if k.val = 32 then 3 else 0) :=
        Finset.sum_le_sum (fun k _ => chainNode_len_le k (c k))
      _ = 5370 := by decide +kernel
  · intro a _ b _ h
    exact chainNode_injective c h

set_option maxHeartbeats 2000000 in
/-- Only a zero-step bottom chain reveals the three additional top bits. -/
theorem reveal_cutOf_exact (c : Choice) :
    ∑ n ∈ cutOf c, n.len = 5367 + if (c 32).val = 31 then 3 else 0 := by
  unfold cutOf
  rw [Finset.sum_image]
  · simp only [chainNode_len, revealWidth_eq, Finset.sum_add_distrib]
    have fixed : (∑ k : Chain, chainBits k) = 5367 := by decide +kernel
    rw [fixed]
    apply congrArg (fun n : ℕ => 5367 + n)
    have pointwise (k : Chain) :
        (if k.val = 32 ∧ (c k).val = 31 then 3 else 0) =
          if k = 32 then (if (c 32).val = 31 then 3 else 0) else 0 := by
      by_cases hk : k = 32
      · subst k; simp
      · have hval : k.val ≠ 32 := fun h => hk (Fin.ext h)
        simp [hk, hval]
    simp_rw [pointwise]
    simp
  · intro a _ b _ h
    exact chainNode_injective c h

/-- The reconstruction cost of a disclosure set: the chain steps and the 14-block root. -/
theorem cost_cutOf (c : Choice) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost = (∑ k, (32 - firstEval k (c k))) + 14 := by
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) =
      ∑ k, (32 - firstEval k (c k)) := by
    simp only [evaluated_ch_iff]
    exact Finset.sum_congr rfl fun k _ => sum_fin32_ge _
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh c), h_ch]

end Forest

end OptimalOTS
