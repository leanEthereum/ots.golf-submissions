import Submissions.UpperLeanIsa.MachineWalk

/-!
# The shape of every walk

Chain-level and whole-program path lemmas (design `NOTES.md` §6 step 3, §9.2), for any
slot predicate `R` implying the hash-free relation, on an image with `Lx L oneCell = oneV`:

* `walk_rice_chain`, `walk_c32`: a walk from a chain's base visits its dispatch, exactly one
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

/-! ## Closed forms and path predicates -/

/-- Steps of the walk with leaf vector `E`: constants, the 32 message chains, `c_hi`, `c_lo`, and
the 34 absorptions plus the pk check. -/
def totalSteps (E : ℕ → ℕ) : ℕ :=
  257 + (∑ k ∈ Finset.range 32, chainSteps k (E k)) + c32Steps (E 32) + chainSteps 33 (E 33) + 35

/-- Cost of the walk with leaf vector `E`. -/
def totalCost (E : ℕ → ℕ) : ℕ :=
  257 + (∑ k ∈ Finset.range 32, chainCost k (E k)) + c32Cost (E 32) + chainCost 33 (E 33) + 341

/-- A leaf vector: a leaf `< 256` for each Rice chain, and `< 32` for `c_hi`. -/
def Valid (E : ℕ → ℕ) : Prop := (∀ k, (k < 32 ∨ k = 33) → E k < 256) ∧ E 32 < 32

/-- `R` on the leaf ops of leaf `e` of Rice chain `k` and on the body steps after it. -/
def ChainFacts (R : ℕ → Prop) (k e : ℕ) : Prop :=
  (∀ i < leafLen k e, R (leafSlot k e + i)) ∧ (∀ j, e < j → j ≤ 254 → R (s0 k + j))

/-- The dispatch facts of Rice chain `k` selecting leaf `e`. -/
def ChainDispatch (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (k e : ℕ) : Prop :=
  UnaryFacts R L (rBase k) 46 63 (zuCell k) (e / 4) ∧ GroupFacts R L k (e / 4) (e % 4)

/-- `R` on the ops of leaf `c` of chain 32 and on the body steps after it. -/
def C32Facts (R : ℕ → Prop) (c : ℕ) : Prop :=
  (∀ i < 5, R (leafSlot32 c + i)) ∧ (∀ j, c < j → j ≤ 254 → R (s0 32 + j))

/-- The dispatch facts of chain 32 selecting leaf `c`. -/
def C32Dispatch (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (c : ℕ) : Prop :=
  UnaryFacts R L (rBase 32) 7 31 (zuCell 32) (31 - c)

/-- `R` on every non-dispatch slot of the walk with leaf vector `E`. -/
structure PathFacts (R : ℕ → Prop) (E : ℕ → ℕ) : Prop where
  const : ∀ s < 257, R s
  leaf : ∀ k, (k < 32 ∨ k = 33) → ∀ i < leafLen k (E k), R (leafSlot k (E k) + i)
  leaf32 : ∀ i < 5, R (leafSlot32 (E 32) + i)
  body : ∀ k < 34, ∀ j, E k < j → j ≤ 254 → R (s0 k + j)
  root : ∀ t < 34, R (rootBase + t)
  pk : R pkSlot

/-- `R` on the dispatch nodes of the walk with leaf vector `E`, whose condition cells select `E`. -/
structure DispatchFacts (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (E : ℕ → ℕ) : Prop where
  rice : ∀ k, (k < 32 ∨ k = 33) → ChainDispatch R L k (E k)
  c32 : C32Dispatch R L (E 32)

theorem const_shape {s : ℕ} (hs : s < 257) :
    (cinstrAt s).isJump = false ∧ (cinstrAt s).cost = 1 := by
  rw [cinstrAt_const_seg hs]; unfold constInstr; split_ifs <;> exact ⟨rfl, rfl⟩

theorem root_shape {t : ℕ} (ht : t < 35) :
    (cinstrAt (rootBase + t)).isJump = false ∧ (cinstrAt (rootBase + t)).cost = if t < 34 then 10 else 1 := by
  rcases Nat.lt_or_ge t 34 with h | h
  · rw [cinstrAt_root h, if_pos h]; exact ⟨rfl, rfl⟩
  · rw [show t = 34 by omega, rootBase_add_34, cinstrAt_pk, if_neg (by omega)]; exact ⟨rfl, rfl⟩

theorem const_cost : ∑ i ∈ Finset.range 257, (cinstrAt (0 + i)).cost = 257 :=
  seg_cost (w := 1) fun i hi => (const_shape (by omega)).2

theorem root_cost : ∑ i ∈ Finset.range 35, (cinstrAt (rootBase + i)).cost = 341 := by
  rw [Finset.sum_range_succ, seg_cost (w := 10) fun i hi => by
    rw [(root_shape (by omega)).2, if_pos hi], (root_shape (by omega)).2, if_neg (by omega)]

section Chains

variable {κ : ℕ} {R : ℕ → Prop} {L : MemImage κ}

/-- **Rice chain.** From `rBase k`, a walk runs chain `k`'s dispatch to one leaf `e`, the leaf,
and the body steps after it, and continues at `s0 k + 255`. -/
theorem walk_rice_chain (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {k n c : ℕ}
    (hk : k < 32 ∨ k = 33) (h : Walk R L n (rBase k) c) :
    ∃ e, e < 256 ∧ ChainFacts R k e ∧ ChainDispatch R L k e ∧ ∃ n' c',
      n = chainSteps k e + n' ∧ c = chainCost k e + c' ∧ Walk R L n' (s0 k + 255) c' := by
  obtain ⟨x, hx, hU, n1, c1, rfl, rfl, hw1⟩ := walk_unary hR (riceShape hk) h
  rw [unaryExit_rice k hx] at hw1
  obtain ⟨b, hb, hG, n2, c2, rfl, rfl, hw2⟩ := walk_group hR hk (by omega) hw1
  have he : 4 * x + b < 256 := by omega
  obtain ⟨hl, n3, c3, rfl, rfl, hw3⟩ := walk_leaf hR hone hk he hw2
  obtain ⟨hbd, n4, c4, rfl, rfl, hw4⟩ := walk_body (k := k) (j0 := min (4 * x + b) 254 + 1)
    (by omega) (by omega) (by omega) (hw3.cast rfl (by omega) rfl)
  have hq : (4 * x + b) / 4 = x := by omega
  have hr : (4 * x + b) % 4 = b := by omega
  refine ⟨4 * x + b, he, ⟨hl, fun j hj hj' => hbd j (by omega) hj'⟩,
    ⟨by rw [hq]; exact hU, by rw [hq, hr]; exact hG⟩, n4, c4, ?_, ?_, hw4⟩
  · unfold chainSteps riceDepth bodyLen; rw [hq]; split_ifs <;> omega
  · unfold chainCost riceDepth bodyLen; rw [hq]; split_ifs <;> omega

theorem walk_rice_chain_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV)
    {k e n c : ℕ} (hk : k < 32 ∨ k = 33) (he : e < 256) (hF : ChainFacts R k e)
    (hD : ChainDispatch R L k e) (h : Walk R L n (s0 k + 255) c) :
    Walk R L (chainSteps k e + n) (rBase k) (chainCost k e + c) := by
  have hw4 := walk_body_mk (k := k) (j0 := min e 254 + 1) (by omega) (by omega) (by omega)
    (fun j hj hj' => hF.2 j (by omega) hj') h
  have hw3 := walk_leaf_mk hR hone hk he hF.1 (hw4.cast rfl (by omega) rfl)
  have hw2 := walk_group_mk hR hk (q := e / 4) (b := e % 4) (by omega) (by omega) hD.2
    (hw3.cast rfl (by rw [show 4 * (e / 4) + e % 4 = e by omega]) rfl)
  have hw1 := walk_unary_mk hR (riceShape hk) (x := e / 4) (by omega) hD.1
    (hw2.cast rfl (unaryExit_rice k (by omega)).symm rfl)
  refine hw1.cast ?_ rfl ?_
  · unfold chainSteps riceDepth bodyLen; split_ifs <;> omega
  · unfold chainCost riceDepth bodyLen; split_ifs <;> omega

/-- **Chain 32.** From `rBase 32`, a walk runs the unary dispatch to one leaf `c < 32`, the
leaf, and the body steps after it, and continues at `s0 32 + 255`. -/
theorem walk_c32 (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {n cost : ℕ}
    (h : Walk R L n (rBase 32) cost) :
    ∃ c, c < 32 ∧ C32Facts R c ∧ C32Dispatch R L c ∧ ∃ n' c',
      n = c32Steps c + n' ∧ cost = c32Cost c + c' ∧ Walk R L n' (s0 32 + 255) c' := by
  obtain ⟨x, hx, hU, n1, c1, rfl, rfl, hw1⟩ := walk_unary hR c32Shape h
  obtain ⟨c, hc, rfl⟩ : ∃ c, c < 32 ∧ x = 31 - c := ⟨31 - x, by omega, by omega⟩
  rw [unaryExit_c32 hc] at hw1
  obtain ⟨hl, n3, c3, rfl, rfl, hw3⟩ := walk_leaf32 hR hone hc hw1
  obtain ⟨hbd, n4, c4, rfl, rfl, hw4⟩ := walk_body (k := 32) (j0 := c + 1)
    (by omega) (by omega) (by omega) (hw3.cast rfl (by omega) rfl)
  refine ⟨c, hc, ⟨hl, fun j hj hj' => hbd j (by omega) hj'⟩, hU, n4, c4, ?_, ?_, hw4⟩
  · unfold c32Steps u32Depth; split_ifs <;> omega
  · unfold c32Cost u32Depth; split_ifs <;> omega

theorem walk_c32_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {c n cost : ℕ}
    (hc : c < 32) (hF : C32Facts R c) (hD : C32Dispatch R L c) (h : Walk R L n (s0 32 + 255) cost) :
    Walk R L (c32Steps c + n) (rBase 32) (c32Cost c + cost) := by
  have hw4 := walk_body_mk (k := 32) (j0 := c + 1) (by omega) (by omega) (by omega)
    (fun j hj hj' => hF.2 j (by omega) hj') h
  have hw3 := walk_leaf32_mk hR hone hc hF.1 (hw4.cast rfl (by omega) rfl)
  have hw1 := walk_unary_mk hR c32Shape (x := 31 - c) (by omega) hD
    (hw3.cast rfl (unaryExit_c32 hc).symm rfl)
  refine hw1.cast ?_ rfl ?_
  · unfold c32Steps u32Depth; split_ifs <;> omega
  · unfold c32Cost u32Depth; split_ifs <;> omega

/-- The 32 message chains in sequence, from `rBase 0`. -/
theorem walk_chains (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) :
    ∀ j, j ≤ 32 → ∀ {n c : ℕ}, Walk R L n (rBase 0) c →
      ∃ E : ℕ → ℕ, (∀ k < j, E k < 256 ∧ ChainFacts R k (E k) ∧ ChainDispatch R L k (E k)) ∧
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
    rw [s0_add_255 (by omega)] at hw2
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
    ∀ j, j ≤ 32 → (∀ k < j, E k < 256 ∧ ChainFacts R k (E k) ∧ ChainDispatch R L k (E k)) →
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
      (h.cast rfl (s0_add_255 (by omega)).symm rfl)
    have hw' := ih (by omega) (fun k hk => hE k (by omega)) hw
    refine hw'.cast ?_ rfl ?_
    · rw [Finset.sum_range_succ]; omega
    · rw [Finset.sum_range_succ]; omega

/-- **Shape of every walk.** A walk from slot 0 is the walk of a leaf vector `E`: it has
`totalSteps E` steps and cost `totalCost E`, and `R` holds on every non-dispatch slot of it. -/
theorem walk_full (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {n c : ℕ}
    (h : Walk R L n 0 c) :
    ∃ E, Valid E ∧ n = totalSteps E ∧ c = totalCost E ∧ PathFacts R E := by
  obtain ⟨hr0, n1, c1, rfl, hc1, hw1⟩ := walk_seg (a := 257) (s := 0)
    (fun i hi => (const_shape (by omega)).1) (by rw [sentinel]; omega) h
  rw [const_cost] at hc1
  subst hc1
  obtain ⟨E1, hE1, n2, c2, rfl, rfl, hw2⟩ :=
    walk_chains hR hone 32 le_rfl (hw1.cast rfl (by rw [rBase_of_le (by omega)]) rfl)
  obtain ⟨c32, hc32, hF32, -, n3, c3, rfl, rfl, hw3⟩ := walk_c32 hR hone hw2
  rw [s0_add_255 le_rfl] at hw3
  obtain ⟨e33, he33, hF33, -, n4, c4, rfl, rfl, hw4⟩ :=
    walk_rice_chain hR hone (Or.inr rfl) hw3
  rw [s0_33_add_255] at hw4
  obtain ⟨hrt, n5, c5, rfl, hc5, hw5⟩ := walk_seg (a := 35) (s := rootBase)
    (fun i hi => (root_shape hi).1) (by rw [sentinel, rootBase]) hw4
  rw [root_cost] at hc5
  subst hc5
  obtain ⟨rfl, rfl⟩ := (hw5.cast rfl (show rootBase + 35 = sentinel from rfl) rfl).at_sentinel
  let E : ℕ → ℕ := fun k => if k < 32 then E1 k else if k = 32 then c32 else e33
  have hElt : ∀ k < 32, E k = E1 k := fun k hk => if_pos hk
  have hE32 : E 32 = c32 := rfl
  have hE33 : E 33 = e33 := rfl
  have hsum : ∀ F : ℕ → ℕ → ℕ, ∑ k ∈ Finset.range 32, F k (E k) =
      ∑ k ∈ Finset.range 32, F k (E1 k) := fun F =>
    Finset.sum_congr rfl fun k hk => by rw [hElt k (Finset.mem_range.mp hk)]
  refine ⟨E, ⟨fun k hk => ?_, hc32⟩, ?_, ?_, ⟨fun s hs => rcast (hr0 s hs) (by omega),
    fun k hk i hi => ?_, hF32.1, fun k hk j hj hj' => ?_,
    fun t ht => hrt t (by omega), rcast (hrt 34 (by omega)) rootBase_add_34⟩⟩
  · rcases hk with hk | rfl
    · rw [hElt k hk]; exact (hE1 k hk).1
    · exact he33
  · unfold totalSteps; rw [hsum chainSteps, hE32, hE33]; omega
  · unfold totalCost; rw [hsum chainCost, hE32, hE33]; omega
  · rcases hk with hk | rfl
    · rw [hElt k hk] at hi ⊢; exact (hE1 k hk).2.1.1 i hi
    · exact hF33.1 i hi
  · rcases (show k < 32 ∨ k = 32 ∨ k = 33 by omega) with hk' | rfl | rfl
    · rw [hElt k hk'] at hj; exact (hE1 k hk').2.1.2 j hj hj'
    · exact hF32.2 j hj hj'
    · exact hF33.2 j hj hj'

/-- **Walk of a leaf vector.** The path facts and the dispatch facts selecting `E` make a walk
from slot 0 of `totalSteps E` steps and cost `totalCost E`. -/
theorem walk_full_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {E : ℕ → ℕ}
    (hE : Valid E) (hP : PathFacts R E) (hD : DispatchFacts R L E) :
    Walk R L (totalSteps E) 0 (totalCost E) := by
  have hw5 := walk_seg_mk (L := L) (a := 35) (fun i hi => (root_shape hi).1)
    (by rw [sentinel, rootBase])
    (fun i hi => by
      rcases Nat.lt_or_ge i 34 with h | h
      · exact hP.root i h
      · exact rcast hP.pk (by rw [show i = 34 by omega, rootBase_add_34]))
    ((Walk.done (R := R) (L := L)).cast rfl (show sentinel = rootBase + 35 from rfl) rfl)
  rw [root_cost] at hw5
  have hw4 := walk_rice_chain_mk hR hone (k := 33) (Or.inr rfl) (hE.1 33 (Or.inr rfl))
    ⟨hP.leaf 33 (Or.inr rfl), hP.body 33 (by omega)⟩ (hD.rice 33 (Or.inr rfl))
    (hw5.cast rfl s0_33_add_255.symm rfl)
  have hw3 := walk_c32_mk hR hone hE.2 ⟨hP.leaf32, hP.body 32 (by omega)⟩ hD.c32
    (hw4.cast rfl (s0_add_255 le_rfl).symm rfl)
  have hw2 := walk_chains_mk hR hone E 32 le_rfl
    (fun k hk => ⟨hE.1 k (Or.inl hk), ⟨hP.leaf k (Or.inl hk), hP.body k (by omega)⟩,
      hD.rice k (Or.inl hk)⟩) hw3
  have hw1 := walk_seg_mk (a := 257) (s := 0) (fun i hi => (const_shape (by omega)).1)
    (by rw [sentinel]; omega) (fun i hi => rcast (hP.const i hi) (by omega))
    (hw2.cast rfl (by rw [rBase_of_le (by omega)]) rfl)
  rw [const_cost] at hw1
  refine hw1.cast ?_ rfl ?_
  · unfold totalSteps; omega
  · unfold totalCost; omega

end Chains

end

end OptimalOTS.LeanIsaBaseline.Machine
