import Submissions.UpperLeanIsa.MachineWalk

/-!
# The shape of every walk

Chain-level and whole-program path lemmas (design `NOTES.md` §6 step 3, §9.2), for any
slot predicate `R` implying the hash-free relation, on an image with `Lx L oneCell = oneV`:

* `walk_rice_chain`, `walk_hi`: a walk from a chain's base visits its dispatch, exactly one
  leaf `e` and the body steps after it, and continues at the next segment;
* `walk_full`: every walk from slot 0 is determined by a leaf vector `E` with `Valid E`: its
  steps are `totalSteps E`, its cost `totalCost E`, and `R` holds on the constants, the leaves,
  the bodies, the root and the pk check (`PathFacts`);
* `walk_full_mk`: conversely `PathFacts` and the dispatch facts selecting `E`
  (`DispatchFacts`) make a walk of `totalSteps E` steps and cost `totalCost E` from slot 0.
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters LeanerVM.Semantics

noncomputable section

/-! ## Path predicates -/

/-- A leaf vector: a leaf `< nLeaves k` for each Rice chain, and `≤ 36` for `c_hi`. -/
def Valid (E : ℕ → ℕ) : Prop := (∀ k, (k < 37 ∨ k = 38) → E k < nLeaves k) ∧ E 37 ≤ 36

/-- `R` on the leaf ops of leaf `e` of Rice chain `k` and on the body steps after it. -/
def ChainFacts (R : ℕ → Prop) (k e : ℕ) : Prop :=
  (∀ i < leafLen k e, R (leafSlot k e + i)) ∧ (∀ j, e < j → j ≤ 126 → R (s0 k + j))

/-- The dispatch facts of Rice chain `k` selecting leaf `e`. -/
def ChainDispatch (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (k e : ℕ) : Prop :=
  UnaryFacts R L (rBase k) 18 (nU k) (zuCell k) (e / 2) ∧ GroupFacts R L k (e / 2) (e % 2)

/-- `R` on the ops of leaf `c` of chain 37 and on the body steps after it. -/
def HiFacts (R : ℕ → Prop) (c : ℕ) : Prop :=
  (∀ i < 5, R (leafSlotHi c + i)) ∧ (∀ j, c < j → j ≤ 126 → R (s0 37 + j))

/-- The dispatch facts of chain 37 selecting leaf `c`. -/
def HiDispatch (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (c : ℕ) : Prop :=
  UnaryFacts R L (rBase 37) 7 36 (zuCell 37) (36 - c)

/-- `R` on every non-dispatch slot of the walk with leaf vector `E`. -/
structure PathFacts (R : ℕ → Prop) (E : ℕ → ℕ) : Prop where
  const : ∀ s < 129, R s
  leaf : ∀ k, (k < 37 ∨ k = 38) → ∀ i < leafLen k (E k), R (leafSlot k (E k) + i)
  leafHi : ∀ i < 5, R (leafSlotHi (E 37) + i)
  body : ∀ k < 39, ∀ j, E k < j → j ≤ 126 → R (s0 k + j)
  root : ∀ t < 39, R (rootBase + t)
  pk : R pkSlot

/-- `R` on the dispatch nodes of the walk with leaf vector `E`, whose condition cells select `E`. -/
structure DispatchFacts (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (E : ℕ → ℕ) : Prop where
  rice : ∀ k, (k < 37 ∨ k = 38) → ChainDispatch R L k (E k)
  hi : HiDispatch R L (E 37)

theorem const_shape {s : ℕ} (hs : s < 129) :
    (cinstrAt s).isJump = false ∧ (cinstrAt s).cost = 1 := by
  rw [cinstrAt_const_seg hs]; unfold constInstr; split_ifs <;> exact ⟨rfl, rfl⟩

theorem root_shape {t : ℕ} (ht : t < 40) :
    (cinstrAt (rootBase + t)).isJump = false ∧ (cinstrAt (rootBase + t)).cost = if t < 39 then 10 else 1 := by
  rcases Nat.lt_or_ge t 39 with h | h
  · rw [cinstrAt_root h, if_pos h]; exact ⟨rfl, rfl⟩
  · rw [show t = 39 by omega, rootBase_add_39, cinstrAt_pk, if_neg (by omega)]; exact ⟨rfl, rfl⟩

theorem const_cost : ∑ i ∈ Finset.range 129, (cinstrAt (0 + i)).cost = 129 :=
  seg_cost (w := 1) fun i hi => (const_shape (by omega)).2

theorem root_cost : ∑ i ∈ Finset.range 40, (cinstrAt (rootBase + i)).cost = 391 := by
  rw [Finset.sum_range_succ, seg_cost (w := 10) fun i hi => by
    rw [(root_shape (by omega)).2, if_pos hi], (root_shape (by omega)).2, if_neg (by omega)]

section Chains

variable {κ : ℕ} {R : ℕ → Prop} {L : MemImage κ}

/-- **Rice chain.** From `rBase k`, a walk runs chain `k`'s dispatch to one leaf `e`, the leaf,
and the body steps after it, and continues at `s0 k + 127`. -/
theorem walk_rice_chain (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {k n c : ℕ}
    (hk : k < 37 ∨ k = 38) (h : Walk R L n (rBase k) c) :
    ∃ e, e < nLeaves k ∧ ChainFacts R k e ∧ ChainDispatch R L k e ∧ ∃ n' c',
      n = chainSteps k e + n' ∧ c = chainCost k e + c' ∧ Walk R L n' (s0 k + 127) c' := by
  obtain ⟨x, hx, hU, n1, c1, rfl, rfl, hw1⟩ := walk_unary hR (riceShape hk) h
  rw [unaryExit_rice k hx] at hw1
  obtain ⟨b, hb, hG, n2, c2, rfl, rfl, hw2⟩ := walk_group hR hk hx hw1
  have he : 2 * x + b < nLeaves k := by rw [nLeaves_eq]; omega
  have he' := nLeaves_le k
  obtain ⟨hl, n3, c3, rfl, rfl, hw3⟩ := walk_leaf hR hone hk he hw2
  obtain ⟨hbd, n4, c4, rfl, rfl, hw4⟩ := walk_body (k := k) (j0 := min (2 * x + b) 126 + 1)
    (by omega) (by omega) (by omega) (hw3.cast rfl (by omega) rfl)
  have hq : (2 * x + b) / 2 = x := by omega
  have hr : (2 * x + b) % 2 = b := by omega
  refine ⟨2 * x + b, he, ⟨hl, fun j hj hj' => hbd j (by omega) hj'⟩,
    ⟨by rw [hq]; exact hU, by rw [hq, hr]; exact hG⟩, n4, c4, ?_, ?_, hw4⟩
  · unfold chainSteps riceDepth bodyLen; rw [hq]; split_ifs <;> omega
  · unfold chainCost riceDepth bodyLen; rw [hq]; split_ifs <;> omega

theorem walk_rice_chain_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV)
    {k e n c : ℕ} (hk : k < 37 ∨ k = 38) (he : e < nLeaves k) (hF : ChainFacts R k e)
    (hD : ChainDispatch R L k e) (h : Walk R L n (s0 k + 127) c) :
    Walk R L (chainSteps k e + n) (rBase k) (chainCost k e + c) := by
  have he' := nLeaves_le k
  have heU : e / 2 ≤ nU k := by rw [nLeaves_eq] at he; omega
  have hw4 := walk_body_mk (k := k) (j0 := min e 126 + 1) (by omega) (by omega) (by omega)
    (fun j hj hj' => hF.2 j (by omega) hj') h
  have hw3 := walk_leaf_mk hR hone hk he hF.1 (hw4.cast rfl (by omega) rfl)
  have hw2 := walk_group_mk hR hk (q := e / 2) (b := e % 2) heU (by omega) hD.2
    (hw3.cast rfl (by rw [show 2 * (e / 2) + e % 2 = e by omega]) rfl)
  have hw1 := walk_unary_mk hR (riceShape hk) (x := e / 2) heU hD.1
    (hw2.cast rfl (unaryExit_rice k heU).symm rfl)
  refine hw1.cast ?_ rfl ?_
  · unfold chainSteps riceDepth bodyLen; split_ifs <;> omega
  · unfold chainCost riceDepth bodyLen; split_ifs <;> omega

/-- **Chain 37.** From `rBase 37`, a walk runs the unary dispatch to one leaf `c ≤ 36`, the
leaf, and the body steps after it, and continues at `s0 37 + 127`. -/
theorem walk_hi (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {n cost : ℕ}
    (h : Walk R L n (rBase 37) cost) :
    ∃ c, c ≤ 36 ∧ HiFacts R c ∧ HiDispatch R L c ∧ ∃ n' c',
      n = hiSteps c + n' ∧ cost = hiCost c + c' ∧ Walk R L n' (s0 37 + 127) c' := by
  obtain ⟨x, hx, hU, n1, c1, rfl, rfl, hw1⟩ := walk_unary hR hiShape h
  obtain ⟨c, hc, rfl⟩ : ∃ c, c ≤ 36 ∧ x = 36 - c := ⟨36 - x, by omega, by omega⟩
  rw [unaryExit_hi hc] at hw1
  obtain ⟨hl, n3, c3, rfl, rfl, hw3⟩ := walk_leafHi hR hone hc hw1
  obtain ⟨hbd, n4, c4, rfl, rfl, hw4⟩ := walk_body (k := 37) (j0 := c + 1)
    (by omega) (by omega) (by omega) (hw3.cast rfl (by omega) rfl)
  refine ⟨c, hc, ⟨hl, fun j hj hj' => hbd j (by omega) hj'⟩, hU, n4, c4, ?_, ?_, hw4⟩
  · unfold hiSteps hiDepth; split_ifs <;> omega
  · unfold hiCost hiDepth; split_ifs <;> omega

theorem walk_hi_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {c n cost : ℕ}
    (hc : c ≤ 36) (hF : HiFacts R c) (hD : HiDispatch R L c) (h : Walk R L n (s0 37 + 127) cost) :
    Walk R L (hiSteps c + n) (rBase 37) (hiCost c + cost) := by
  have hw4 := walk_body_mk (k := 37) (j0 := c + 1) (by omega) (by omega) (by omega)
    (fun j hj hj' => hF.2 j (by omega) hj') h
  have hw3 := walk_leafHi_mk hR hone hc hF.1 (hw4.cast rfl (by omega) rfl)
  have hw1 := walk_unary_mk hR hiShape (x := 36 - c) (by omega) hD
    (hw3.cast rfl (unaryExit_hi hc).symm rfl)
  refine hw1.cast ?_ rfl ?_
  · unfold hiSteps hiDepth; split_ifs <;> omega
  · unfold hiCost hiDepth; split_ifs <;> omega

/-- The 37 message chains in sequence, from `rBase 0`. -/
theorem walk_chains (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) :
    ∀ j, j ≤ 37 → ∀ {n c : ℕ}, Walk R L n (rBase 0) c →
      ∃ E : ℕ → ℕ, (∀ k < j, E k < nLeaves k ∧ ChainFacts R k (E k) ∧ ChainDispatch R L k (E k)) ∧
        ∃ n' c', n = (∑ k ∈ Finset.range j, chainSteps k (E k)) + n' ∧
          c = (∑ k ∈ Finset.range j, chainCost k (E k)) + c' ∧ Walk R L n' (rBase j) c' := by
  intro j
  induction j with
  | zero =>
    intro _ n c h
    exact ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero _), n, c, by simp, by simp, h⟩
  | succ j ih =>
    intro hj n c h
    obtain ⟨E, hE, n1, c1, rfl, rfl, hw1⟩ := ih (by omega) h
    obtain ⟨e, he, hF, hD, n2, c2, rfl, rfl, hw2⟩ :=
      walk_rice_chain hR hone (k := j) (Or.inl (by omega)) hw1
    rw [s0_add_127 (by omega)] at hw2
    have hE' : ∀ k < j, (if k = j then e else E k) = E k := fun k hk => if_neg (by omega)
    have hsum : ∀ F : ℕ → ℕ → ℕ, ∑ k ∈ Finset.range (j + 1), F k (if k = j then e else E k) =
        (∑ k ∈ Finset.range j, F k (E k)) + F j e := fun F => by
      rw [Finset.sum_range_succ, if_pos rfl,
        Finset.sum_congr rfl fun k hk => by rw [hE' k (Finset.mem_range.mp hk)]]
    refine ⟨fun k => if k = j then e else E k, fun k hk => ?_, n2, c2, ?_, ?_, hw2⟩
    · rcases (show k < j ∨ k = j by omega) with hk' | rfl
      · simp only [hE' k hk']; exact hE k hk'
      · simp only; exact ⟨he, hF, hD⟩
    · rw [hsum chainSteps]; omega
    · rw [hsum chainCost]; omega

theorem walk_chains_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) (E : ℕ → ℕ) :
    ∀ j, j ≤ 37 →
      (∀ k < j, E k < nLeaves k ∧ ChainFacts R k (E k) ∧ ChainDispatch R L k (E k)) →
      ∀ {n c : ℕ}, Walk R L n (rBase j) c →
        Walk R L ((∑ k ∈ Finset.range j, chainSteps k (E k)) + n) (rBase 0)
          ((∑ k ∈ Finset.range j, chainCost k (E k)) + c) := by
  intro j
  induction j with
  | zero => intro _ _ n c h; exact h.cast (by simp) rfl (by simp)
  | succ j ih =>
    intro hj hE n c h
    obtain ⟨he, hF, hD⟩ := hE j (by omega)
    have hw := walk_rice_chain_mk hR hone (Or.inl (by omega)) he hF hD
      (h.cast rfl (s0_add_127 (by omega)).symm rfl)
    have hw' := ih (by omega) (fun k hk => hE k (by omega)) hw
    refine hw'.cast ?_ rfl ?_
    · rw [Finset.sum_range_succ]; omega
    · rw [Finset.sum_range_succ]; omega

/-- **Shape of every walk.** A walk from slot 0 is the walk of a leaf vector `E`: it has
`totalSteps E` steps and cost `totalCost E`, and `R` holds on every non-dispatch slot of it. -/
theorem walk_full (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {n c : ℕ}
    (h : Walk R L n 0 c) :
    ∃ E, Valid E ∧ n = totalSteps E ∧ c = totalCost E ∧ PathFacts R E := by
  obtain ⟨hr0, n1, c1, rfl, hc1, hw1⟩ := walk_seg (a := 129) (s := 0)
    (fun i hi => (const_shape (by omega)).1) (by rw [sentinel]; omega) h
  rw [const_cost] at hc1
  subst hc1
  obtain ⟨E1, hE1, n2, c2, rfl, rfl, hw2⟩ :=
    walk_chains hR hone 37 le_rfl (hw1.cast rfl rBase_zero.symm rfl)
  obtain ⟨cHi, hcHi, hFHi, -, n3, c3, rfl, rfl, hw3⟩ := walk_hi hR hone hw2
  rw [s0_add_127 le_rfl] at hw3
  obtain ⟨e38, he38, hF38, -, n4, c4, rfl, rfl, hw4⟩ :=
    walk_rice_chain hR hone (Or.inr rfl) hw3
  rw [s0_38_add_127] at hw4
  obtain ⟨hrt, n5, c5, rfl, hc5, hw5⟩ := walk_seg (a := 40) (s := rootBase)
    (fun i hi => (root_shape hi).1) (by rw [sentinel, rootBase]) hw4
  rw [root_cost] at hc5
  subst hc5
  obtain ⟨rfl, rfl⟩ := (hw5.cast rfl (show rootBase + 40 = sentinel from rfl) rfl).at_sentinel
  let E : ℕ → ℕ := fun k => if k < 37 then E1 k else if k = 37 then cHi else e38
  have hElt : ∀ k < 37, E k = E1 k := fun k hk => if_pos hk
  have hE37 : E 37 = cHi := rfl
  have hE38 : E 38 = e38 := rfl
  have hsum : ∀ F : ℕ → ℕ → ℕ, ∑ k ∈ Finset.range 37, F k (E k) =
      ∑ k ∈ Finset.range 37, F k (E1 k) := fun F =>
    Finset.sum_congr rfl fun k hk => by rw [hElt k (Finset.mem_range.mp hk)]
  refine ⟨E, ⟨fun k hk => ?_, hcHi⟩, ?_, ?_, ⟨fun s hs => rcast (hr0 s hs) (by omega),
    fun k hk i hi => ?_, hFHi.1, fun k hk j hj hj' => ?_,
    fun t ht => hrt t (by omega), rcast (hrt 39 (by omega)) rootBase_add_39⟩⟩
  · rcases hk with hk | rfl
    · rw [hElt k hk]; exact (hE1 k hk).1
    · exact he38
  · unfold totalSteps; rw [hsum chainSteps, hE37, hE38]; omega
  · unfold totalCost; rw [hsum chainCost, hE37, hE38]; omega
  · rcases hk with hk | rfl
    · rw [hElt k hk] at hi ⊢; exact (hE1 k hk).2.1.1 i hi
    · exact hF38.1 i hi
  · rcases (show k < 37 ∨ k = 37 ∨ k = 38 by omega) with hk' | rfl | rfl
    · rw [hElt k hk'] at hj; exact (hE1 k hk').2.1.2 j hj hj'
    · exact hFHi.2 j hj hj'
    · exact hF38.2 j hj hj'

/-- **Walk of a leaf vector.** The path facts and the dispatch facts selecting `E` make a walk
from slot 0 of `totalSteps E` steps and cost `totalCost E`. -/
theorem walk_full_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {E : ℕ → ℕ}
    (hE : Valid E) (hP : PathFacts R E) (hD : DispatchFacts R L E) :
    Walk R L (totalSteps E) 0 (totalCost E) := by
  have hw5 := walk_seg_mk (L := L) (a := 40) (fun i hi => (root_shape hi).1)
    (by rw [sentinel, rootBase])
    (fun i hi => by
      rcases Nat.lt_or_ge i 39 with h | h
      · exact hP.root i h
      · exact rcast hP.pk (by rw [show i = 39 by omega, rootBase_add_39]))
    ((Walk.done (R := R) (L := L)).cast rfl (show sentinel = rootBase + 40 from rfl) rfl)
  rw [root_cost] at hw5
  have hw4 := walk_rice_chain_mk hR hone (k := 38) (Or.inr rfl) (hE.1 38 (Or.inr rfl))
    ⟨hP.leaf 38 (Or.inr rfl), hP.body 38 (by omega)⟩ (hD.rice 38 (Or.inr rfl))
    (hw5.cast rfl s0_38_add_127.symm rfl)
  have hw3 := walk_hi_mk hR hone hE.2 ⟨hP.leafHi, hP.body 37 (by omega)⟩ hD.hi
    (hw4.cast rfl (s0_add_127 le_rfl).symm rfl)
  have hw2 := walk_chains_mk hR hone E 37 le_rfl
    (fun k hk => ⟨hE.1 k (Or.inl hk), ⟨hP.leaf k (Or.inl hk), hP.body k (by omega)⟩,
      hD.rice k (Or.inl hk)⟩) hw3
  have hw1 := walk_seg_mk (a := 129) (s := 0) (fun i hi => (const_shape (by omega)).1)
    (by rw [sentinel]; omega) (fun i hi => rcast (hP.const i hi) (by omega))
    (hw2.cast rfl rBase_zero rfl)
  rw [const_cost] at hw1
  refine hw1.cast ?_ rfl ?_
  · unfold totalSteps; omega
  · unfold totalCost; omega

end Chains

end

end OptimalOTS.LeanIsaBaseline.Machine
