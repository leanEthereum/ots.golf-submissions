import Submissions.UpperRiscv.Names

/-!
# The tree structure of the concrete graph

Every node other than the root feeds exactly one other node (`Name.child`), so the graph is a
tree.  This file relates the generic notions of `OptimalOTS.Dag` (`Graph.Visited`,
`Graph.evaluated`, `Graph.reconstructCost`, `Graph.revealBits`) to the tree:

* `Above m n`: `m` is a strict ancestor of `n` (reached by following `child` at least once);
  `ancSet n` is the explicit finite set of strict ancestors;
* `visited_iff`: a node is visited when reconstructing from the (names of the) set `A` exactly
  when none of its strict ancestors lies in `A`;
* `Evaluated A n`: `n ∉ A` and no strict ancestor of `n` lies in `A`;
* `reconstructCost_eq`, `revealBits_eq`, `no_hidden_source_iff`: the scheme's quantities in
  tree terms;
* cuts (`IsCut`): antichains of 128-bit nodes meeting every source path; distinct cuts of equal
  cost are incomparable (`exists_mem_evaluated_of_ne`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

/-- Strict ancestors: `m` is reached from `n` by following `child` at least once. -/
inductive Above : Name → Name → Prop
  | child {m n : Name} : child n = some m → Above m n
  | step {m n p : Name} : child n = some p → Above m p → Above m n

/-- Distance to the root. -/
def height : Name → ℕ
  | src _ => 47
  | ci _ t => 46 - 3 * t
  | ch _ t => 45 - 3 * t
  | cv _ t => 44 - 3 * t
  | rc => 1
  | rh => 0

theorem height_child {m n : Name} (h : child n = some m) : height m + 1 = height n := by
  cases n <;> simp only [Name.child, Option.some.injEq, reduceCtorEq] at h
  all_goals try (subst h; simp [height]; try omega)
  split_ifs at h with ht <;> (simp only [Option.some.injEq] at h; subst h; simp [height]; omega)

theorem Above.trans {a b c : Name} (h₁ : Above a b) (h₂ : Above b c) : Above a c := by
  revert h₁
  induction h₂ with
  | child h => intro h₁; exact Above.step h h₁
  | step h _ ih => intro h₁; exact Above.step h (ih h₁)

theorem above_of_child {m n p : Name} (h : child n = some p) : Above m n ↔ m = p ∨ Above m p := by
  constructor
  · intro ha
    cases ha with
    | child h' => rw [h, Option.some.injEq] at h'; exact Or.inl h'.symm
    | step h' ha' => rw [h, Option.some.injEq] at h'; subst h'; exact Or.inr ha'
  · rintro (rfl | ha)
    · exact Above.child h
    · exact Above.step h ha

theorem not_above_rh (m : Name) : ¬ Above m rh := by
  intro h
  cases h with
  | child h' => simp [Name.child] at h'
  | step h' _ => simp [Name.child] at h'

/-- The strict ancestors of a node, explicitly. -/
def ancSet : Name → Finset Name
  | rh => ∅
  | rc => {rh}
  | cv k t => (Finset.univ.filter fun t' : Fin 15 => t < t').image (ci k) ∪
      (Finset.univ.filter fun t' : Fin 15 => t < t').image (ch k) ∪
      (Finset.univ.filter fun t' : Fin 15 => t < t').image (cv k) ∪ {rc, rh}
  | ch k t => (Finset.univ.filter fun t' : Fin 15 => t < t').image (ci k) ∪
      (Finset.univ.filter fun t' : Fin 15 => t < t').image (ch k) ∪
      (Finset.univ.filter fun t' : Fin 15 => t ≤ t').image (cv k) ∪ {rc, rh}
  | ci k t => (Finset.univ.filter fun t' : Fin 15 => t < t').image (ci k) ∪
      (Finset.univ.filter fun t' : Fin 15 => t ≤ t').image (ch k) ∪
      (Finset.univ.filter fun t' : Fin 15 => t ≤ t').image (cv k) ∪ {rc, rh}
  | src k => Finset.univ.image (ci k) ∪ Finset.univ.image (ch k) ∪ Finset.univ.image (cv k) ∪
      {rc, rh}

theorem child_eq_none {n : Name} (h : child n = none) : n = rh := by
  cases n <;> simp only [Name.child, reduceCtorEq] at h <;> try rfl
  split_ifs at h

theorem filter_lt_succ (t : Fin 15) (ht : t.val < 14) :
    Finset.univ.filter (fun t' : Fin 15 => t < t') =
      insert (⟨t.val + 1, by omega⟩ : Fin 15)
        (Finset.univ.filter (fun t' : Fin 15 => (⟨t.val + 1, by omega⟩ : Fin 15) < t')) := by
  ext t'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
    Fin.ext_iff]
  omega

theorem filter_lt_eq_filter_le (t : Fin 15) (ht : t.val < 14) :
    Finset.univ.filter (fun t' : Fin 15 => t < t') =
      Finset.univ.filter (fun t' : Fin 15 => (⟨t.val + 1, by omega⟩ : Fin 15) ≤ t') := by
  ext t'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]
  omega

theorem filter_le_eq_insert (t : Fin 15) :
    Finset.univ.filter (fun t' : Fin 15 => t ≤ t') =
      insert t (Finset.univ.filter (fun t' : Fin 15 => t < t')) := by
  ext t'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.le_def,
    Fin.lt_def, Fin.ext_iff]
  omega

theorem filter_lt_14 : Finset.univ.filter (fun t' : Fin 15 => (14 : Fin 15) < t') = ∅ :=
  Finset.filter_eq_empty_iff.mpr fun t' _ => not_lt.mpr (Fin.le_last t')

theorem univ_eq_insert_zero :
    (Finset.univ : Finset (Fin 15)) =
      insert 0 (Finset.univ.filter (fun t' : Fin 15 => 0 < t')) := by
  ext t'
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff, Fin.lt_def,
    Fin.ext_iff, Fin.val_zero]
  omega

theorem filter_zero_le :
    Finset.univ.filter (fun t' : Fin 15 => (0 : Fin 15) ≤ t') = Finset.univ := by
  simp

theorem ancSet_child {n p : Name} (h : child n = some p) : ancSet n = insert p (ancSet p) := by
  cases n with
  | src k =>
    simp only [Name.child, Option.some.injEq] at h; subst h
    simp only [ancSet]
    rw [show Finset.univ.image (cv k) =
        (Finset.univ.filter (fun t' : Fin 15 => (0 : Fin 15) ≤ t')).image (cv k) from by
      rw [filter_zero_le]]
    rw [show Finset.univ.image (ch k) =
        (Finset.univ.filter (fun t' : Fin 15 => (0 : Fin 15) ≤ t')).image (ch k) from by
      rw [filter_zero_le]]
    rw [show Finset.univ.image (ci k) =
        insert (ci k 0) ((Finset.univ.filter (fun t' : Fin 15 => 0 < t')).image (ci k)) from by
      rw [← Finset.image_insert, ← univ_eq_insert_zero]]
    rw [Finset.insert_union, Finset.insert_union, Finset.insert_union]
  | ci k t =>
    simp only [Name.child, Option.some.injEq] at h; subst h
    simp only [ancSet]
    have hB : (Finset.univ.filter (fun t' : Fin 15 => t ≤ t')).image (ch k) =
        insert (ch k t) ((Finset.univ.filter (fun t' : Fin 15 => t < t')).image (ch k)) := by
      rw [filter_le_eq_insert t, Finset.image_insert]
    rw [hB, Finset.union_insert (ch k t), Finset.insert_union (ch k t),
      Finset.insert_union (ch k t)]
  | ch k t =>
    simp only [Name.child, Option.some.injEq] at h; subst h
    simp only [ancSet]
    have hC : (Finset.univ.filter (fun t' : Fin 15 => t ≤ t')).image (cv k) =
        insert (cv k t) ((Finset.univ.filter (fun t' : Fin 15 => t < t')).image (cv k)) := by
      rw [filter_le_eq_insert t, Finset.image_insert]
    rw [hC, Finset.union_insert (cv k t), Finset.insert_union (cv k t)]
  | cv k t =>
    simp only [Name.child] at h
    split_ifs at h with ht
    · simp only [Option.some.injEq] at h; subst h
      have ht' : t = 14 := Fin.ext ht
      subst ht'
      simp only [ancSet, filter_lt_14, Finset.image_empty, Finset.empty_union]
    · simp only [Option.some.injEq] at h; subst h
      simp only [ancSet]
      rw [show (Finset.univ.filter (fun t' : Fin 15 => t < t')).image (cv k) =
          (Finset.univ.filter
            (fun t' : Fin 15 => (⟨t.val + 1, by omega⟩ : Fin 15) ≤ t')).image (cv k) from by
        rw [filter_lt_eq_filter_le t (by omega)]]
      rw [show (Finset.univ.filter (fun t' : Fin 15 => t < t')).image (ch k) =
          (Finset.univ.filter
            (fun t' : Fin 15 => (⟨t.val + 1, by omega⟩ : Fin 15) ≤ t')).image (ch k) from by
        rw [filter_lt_eq_filter_le t (by omega)]]
      rw [filter_lt_succ t (by omega), Finset.image_insert, Finset.insert_union,
        Finset.insert_union, Finset.insert_union]
  | rc => simp only [Name.child, Option.some.injEq] at h; subst h; simp [ancSet]
  | rh => simp [Name.child] at h

theorem above_iff_mem_ancSet (m n : Name) : Above m n ↔ m ∈ ancSet n := by
  suffices ∀ k, ∀ n, height n = k → (Above m n ↔ m ∈ ancSet n) from this _ n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hn
    rcases hc : child n with _ | p
    · rw [child_eq_none hc]; simp [ancSet, not_above_rh]
    · rw [above_of_child hc, ancSet_child hc, Finset.mem_insert,
        ih (height p) (by rw [← hn, ← height_child hc]; omega) p rfl]

/-- Indices of a set of names. -/
def fins (A : Finset Name) : Finset (Fin N) := A.map nameEquiv.toEmbedding

@[simp] theorem mem_fins (A : Finset Name) (n : Name) : n.fin ∈ fins A ↔ n ∈ A :=
  Finset.mem_map' _

/-- Membership in the parents of a node, in the graph, in terms of `child`. -/
theorem mem_graph_parents_iff (m n : Name) :
    m.fin ∈ (graph.kind n.fin).parents ↔ child m = some n := by
  rw [graph_parents_fin]
  exact (Finset.mem_map' _).trans (Name.mem_parents_iff m n)

/-- Visited nodes are those with no strict ancestor in `A`. -/
theorem visited_iff (A : Finset Name) (n : Name) :
    graph.Visited (fins A) n.fin ↔ ∀ m, Above m n → m ∉ A := by
  constructor
  · intro hv
    have key : ∀ v, graph.Visited (fins A) v → ∀ n : Name, n.fin = v → ∀ m, Above m n → m ∉ A := by
      intro v hv
      induction hv with
      | root =>
        intro n hn m hm
        have hr : n = rh := Name.fin_injective hn
        subst hr
        exact absurd hm (not_above_rh m)
      | parent hw hwA hv ih =>
        rename_i w v
        intro n hn m hm hmA
        subst hn
        obtain ⟨w', rfl⟩ : ∃ w' : Name, w'.fin = w := ⟨ofFin w, fin_ofFin w⟩
        have hc : child n = some w' := (mem_graph_parents_iff n w').mp hv
        rw [above_of_child hc] at hm
        rcases hm with rfl | hm
        · exact hwA ((mem_fins A _).mpr hmA)
        · exact ih w' rfl m hm hmA
    exact key _ hv n rfl
  · suffices ∀ k, ∀ n, height n = k → (∀ m, Above m n → m ∉ A) →
        graph.Visited (fins A) n.fin from this _ n rfl
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n hn hA
      rcases hc : child n with _ | p
      · rw [child_eq_none hc]; exact Graph.Visited.root
      · have hp : p ∉ A := hA p (Above.child hc)
        have hvp : graph.Visited (fins A) p.fin :=
          ih (height p) (by rw [← hn, ← height_child hc]; omega) p rfl
            (fun m hm => hA m ((above_of_child hc).mpr (Or.inr hm)))
        exact Graph.Visited.parent hvp (fun h => hp ((mem_fins A p).mp h))
          ((mem_graph_parents_iff n p).mpr hc)

/-- The nodes evaluated when reconstructing from `A`. -/
def Evaluated (A : Finset Name) (n : Name) : Prop := n ∉ A ∧ ∀ m, Above m n → m ∉ A

theorem mem_evaluated_iff (A : Finset Name) (n : Name) :
    n.fin ∈ graph.evaluated (fins A) ↔ Evaluated A n := by
  have h : ∀ (B : Finset (Fin graph.size)) (v : Fin graph.size),
      v ∈ graph.evaluated B ↔ graph.Visited B v ∧ v ∉ B := by
    intro B v
    unfold Graph.evaluated
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine (h (fins A) n.fin).trans ?_
  constructor
  · rintro ⟨hv, hnA⟩
    exact ⟨fun h => hnA ((mem_fins A n).mpr h), (visited_iff A n).mp hv⟩
  · rintro ⟨hnA, hanc⟩
    exact ⟨(visited_iff A n).mpr hanc, fun h => hnA ((mem_fins A n).mp h)⟩

/-- The evaluated set as a finset of names. -/
def evaluatedSet (A : Finset Name) : Finset Name := Finset.univ.filter (Evaluated A)

theorem evaluated_eq_fins (A : Finset Name) : graph.evaluated (fins A) = fins (evaluatedSet A) := by
  ext v
  obtain ⟨n, rfl⟩ : ∃ n : Name, n.fin = v := ⟨ofFin v, fin_ofFin v⟩
  refine (mem_evaluated_iff A n).trans (Iff.trans ?_ (mem_fins (evaluatedSet A) n).symm)
  simp [evaluatedSet]

/-- Reconstruction cost in tree terms. -/
theorem reconstructCost_eq (A : Finset Name) :
    graph.reconstructCost (fins A) = ∑ n ∈ evaluatedSet A, n.cost := by
  unfold Graph.reconstructCost
  rw [evaluated_eq_fins]
  refine (Finset.sum_map (evaluatedSet A) nameEquiv.toEmbedding graph.nodeCost).trans ?_
  exact Finset.sum_congr rfl fun n _ => graph_nodeCost_fin n

/-- Revealed bits in tree terms. -/
theorem revealBits_eq (A : Finset Name) : graph.revealBits (fins A) = ∑ n ∈ A, n.len := by
  unfold Graph.revealBits
  refine (Finset.sum_map A nameEquiv.toEmbedding graph.len).trans ?_
  exact Finset.sum_congr rfl fun n _ => graph_len_fin n

/-- The condition `Scheme.no_hidden_source` in tree terms: every source path meets `A`. -/
theorem no_hidden_source_iff (A : Finset Name) :
    (∀ v, graph.Visited (fins A) v → v ∉ fins A → ¬ (graph.kind v).IsSource) ↔
      ∀ k, src k ∈ A ∨ ∃ m ∈ A, Above m (src k) := by
  constructor
  · intro h k
    by_contra hk
    push Not at hk
    apply h (src k).fin
    · exact (visited_iff A _).mpr fun m hm hmA => hk.2 m hmA hm
    · exact fun h' => hk.1 ((mem_fins A _).mp h')
    · exact (graph_isSource_fin _).mpr ⟨k, rfl⟩
  · intro h v hv hvA hs
    obtain ⟨n, rfl⟩ : ∃ n : Name, n.fin = v := ⟨ofFin v, fin_ofFin v⟩
    obtain ⟨k, rfl⟩ := (graph_isSource_fin n).mp hs
    have hv' := (visited_iff A _).mp hv
    have hvA' : src k ∉ A := fun h' => hvA ((mem_fins A _).mpr h')
    rcases h k with h1 | ⟨m, hmA, hm⟩
    · exact hvA' h1
    · exact hv' m hm hmA

/-- The hash node whose output is the value of a 128-bit node (none for sources). -/
def hashOf : Name → Option Name
  | cv k t => some (ch k t)
  | _ => none

theorem child_hashOf {a h : Name} (hh : hashOf a = some h) : child h = some a := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh <;> rfl

theorem hashOf_isSome_iff (a : Name) : (hashOf a).isSome ↔ a.len = 128 ∧ ∀ k, a ≠ src k := by
  cases a <;> simp [hashOf, Name.len]

theorem len_of_hashOf {a p : Name} (hp : hashOf a = some p) : p.len = 256 := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;> rfl

theorem one_le_cost_of_hashOf {a p : Name} (hp : hashOf a = some p) : 1 ≤ p.cost := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp [Name.cost]

/-- A cut: an antichain of 128-bit nodes, other than the root, meeting every source path. -/
structure IsCut (A : Finset Name) : Prop where
  values : ∀ n ∈ A, n.len = 128
  antichain : ∀ n ∈ A, ∀ m, Above m n → m ∉ A
  covers : ∀ k, src k ∈ A ∨ ∃ m ∈ A, Above m (src k)

theorem IsCut.rh_not_mem {A : Finset Name} (h : IsCut A) : rh ∉ A := by
  intro hm
  have := h.values rh hm
  simp [Name.len] at this

/-- The parent hash node of a cut node is not evaluated. -/
theorem IsCut.not_evaluated_hashOf {A : Finset Name} (hA : IsCut A) {a h : Name} (ha : a ∈ A)
    (hh : hashOf a = some h) : ¬ Evaluated A h :=
  fun he => he.2 a (Above.child (child_hashOf hh)) ha

section

/- Unifying or normalising a hypothesis of the form `p ∈ evaluatedSet A` makes Lean unfold
`Finset.univ : Finset Name` through the `Fintype` instance (1474 elements), which exhausts the
recursion depth; `evaluatedSet` is therefore kept opaque in this section. -/
attribute [local irreducible] evaluatedSet

/-- Distinct cuts of equal cost are incomparable: some node revealed by the first is evaluated
by the second. -/
theorem exists_mem_evaluated_of_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hcost : ∑ n ∈ evaluatedSet A, n.cost = ∑ n ∈ evaluatedSet A', n.cost) (hne : A ≠ A') :
    ∃ v ∈ A, Evaluated A' v := by
  by_contra hcon
  push Not at hcon
  -- every node of `A` is in `A'` or has a strict ancestor in `A'`
  have key : ∀ v ∈ A, v ∈ A' ∨ ∃ m ∈ A', Above m v := by
    intro v hv
    by_contra h
    push Not at h
    exact hcon v hv ⟨h.1, fun m hm hmA' => h.2 m hmA' hm⟩
  -- (i) the evaluated set of `A'` is contained in that of `A`
  have hsub : evaluatedSet A' ⊆ evaluatedSet A := by
    intro n hn
    simp only [evaluatedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
    obtain ⟨hnA', hanc'⟩ := hn
    refine ⟨fun hnA => ?_, fun m hm hmA => ?_⟩
    · rcases key n hnA with h | ⟨m, hmA', hm⟩
      · exact hnA' h
      · exact hanc' m hm hmA'
    · rcases key m hmA with h | ⟨m', hm'A', hm'⟩
      · exact hanc' m hm h
      · exact hanc' m' (hm'.trans hm) hm'A'
  -- (ii) a node of `A'` evaluated at `A`
  have hex : ∃ a ∈ A', Evaluated A a := by
    by_cases hAA' : A ⊆ A'
    · have : ∃ v' ∈ A', v' ∉ A := by
        by_contra h
        push Not at h
        exact hne (Finset.Subset.antisymm hAA' h)
      obtain ⟨v', hv'A', hv'A⟩ := this
      exact ⟨v', hv'A', hv'A, fun m hm hmA => hA'.antichain v' hv'A' m hm (hAA' hmA)⟩
    · rw [Finset.not_subset] at hAA'
      obtain ⟨v, hvA, hvA'⟩ := hAA'
      rcases key v hvA with h | ⟨a', ha'A', ha'⟩
      · exact absurd h hvA'
      · exact ⟨a', ha'A', hA.antichain v hvA a' ha',
          fun m hm hmA => hA.antichain v hvA m (hm.trans ha') hmA⟩
  obtain ⟨a, haA', haE⟩ := hex
  -- `a` is not a source, so it has a hash node `p` above it
  have hns : ∀ k, a ≠ src k := by
    intro k hk
    subst hk
    rcases hA.covers k with h | ⟨m, hmA, hm⟩
    · exact haE.1 h
    · exact haE.2 m hm hmA
  have hsome : (hashOf a).isSome := (hashOf_isSome_iff a).mpr ⟨hA'.values a haA', hns⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hchild : child p = some a := child_hashOf hp
  have hpA : p ∉ A := fun h => by have := hA.values p h; rw [len_of_hashOf hp] at this; omega
  have hpE : Evaluated A p := by
    refine ⟨hpA, fun m hm => ?_⟩
    rw [above_of_child hchild] at hm
    rcases hm with rfl | hm
    · exact haE.1
    · exact haE.2 m hm
  have hpE' : ¬ Evaluated A' p := fun h => h.2 a (Above.child hchild) haA'
  -- (iii) compare the costs
  have hpcost : 1 ≤ p.cost := one_le_cost_of_hashOf hp
  have hpmem : p ∈ evaluatedSet A := by simp [evaluatedSet, hpE]
  have hpnmem : p ∉ evaluatedSet A' := by simp [evaluatedSet, hpE']
  have hsub' : evaluatedSet A' ⊆ (evaluatedSet A).erase p :=
    Finset.subset_erase.mpr ⟨hsub, hpnmem⟩
  have h1 := Finset.sum_le_sum_of_subset (f := fun n : Name => n.cost) hsub'
  have h2 := Finset.sum_erase_add (evaluatedSet A) (fun n : Name => n.cost) hpmem
  omega

end

end Forest

end OptimalOTS
