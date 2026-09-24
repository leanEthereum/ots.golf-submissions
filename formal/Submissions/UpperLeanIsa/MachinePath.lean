import Submissions.UpperLeanIsa.MachineWalk

/-!
# The shape of every walk

Chain-level and whole-program path lemmas (design `NOTES.md` §6 step 3, §9.2), for any
slot predicate `R` implying the hash-free relation, on an image with `Lx L oneCell = oneV`:

* `walk_rice_chain`, `walk_hi`: a walk from a chain's base visits its dispatch, exactly one
  leaf `e` and the body steps after it, and continues at the next segment;
* `walk_full`: every walk from slot 0 is determined by a leaf vector `E` of chain digits with
  `Valid E`: its
  steps are `totalSteps E`, its cost `totalCost E`, and `R` holds on the constants, the leaves,
  the bodies, the root and the pk check (`PathFacts`);
* `walk_full_mk`: conversely `PathFacts` and the dispatch facts selecting `E`
  (`DispatchFacts`) make a walk of `totalSteps E` steps and cost `totalCost E` from slot 0.
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters LeanerVM.Semantics

noncomputable section

/-! ## Path predicates -/

/-- A leaf vector of chain digits: `off k ≤ E k < off k + nLeaves k` for each Rice chain, and
`64 ≤ E 41 ≤ 114` for `c_hi`. -/
def Valid (E : ℕ → ℕ) : Prop :=
  (∀ k, (k < 41 ∨ k = 42) → off k ≤ E k ∧ E k < off k + nLeaves k) ∧ 64 ≤ E 41 ∧ E 41 ≤ 114

/-- `R` on the leaf ops of chain digit `e` of Rice chain `k` and on the body steps after it. -/
def ChainFacts (R : ℕ → Prop) (k e : ℕ) : Prop :=
  (∀ i < leafLen k e, R (leafSlot k e + i)) ∧ (∀ j, e < j → j ≤ 126 → R (s0 k + j))

/-- The dispatch facts of Rice chain `k` selecting chain digit `e` (leaf `e - off k`). -/
def ChainDispatch (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (k e : ℕ) : Prop :=
  UnaryFacts R L (rBase k) 18 (nU k) (zuCell k) ((e - off k) / 2) ∧
    GroupFacts R L k ((e - off k) / 2) ((e - off k) % 2)

/-- `R` on the ops of leaf `dh` of chain 41 and on the body steps after it. -/
def HiFacts (R : ℕ → Prop) (dh : ℕ) : Prop :=
  (∀ i < 5, R (leafSlotHi dh + i)) ∧ (∀ j, 64 + dh < j → j ≤ 126 → R (s0 41 + j))

/-- The dispatch facts of chain 41 selecting leaf `dh`. -/
def HiDispatch (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (dh : ℕ) : Prop :=
  UnaryFacts R L (rBase 41) 7 50 (zuCell 41) (50 - dh)

/-- `R` on every non-dispatch slot of the walk with leaf vector `E`. -/
structure PathFacts (R : ℕ → Prop) (E : ℕ → ℕ) : Prop where
  const : ∀ s < 131, R s
  leaf : ∀ k, (k < 41 ∨ k = 42) → ∀ i < leafLen k (E k), R (leafSlot k (E k) + i)
  leafHi : ∀ i < 5, R (leafSlotHi (E 41 - 64) + i)
  body : ∀ k < 43, ∀ j, E k < j → j ≤ 126 → R (s0 k + j)
  root : ∀ t < 43, R (rootBase + t)
  pk : R pkSlot

/-- `R` on the dispatch nodes of the walk with leaf vector `E`, whose condition cells select `E`. -/
structure DispatchFacts (R : ℕ → Prop) {κ : ℕ} (L : MemImage κ) (E : ℕ → ℕ) : Prop where
  rice : ∀ k, (k < 41 ∨ k = 42) → ChainDispatch R L k (E k)
  hi : HiDispatch R L (E 41 - 64)

theorem const_shape {s : ℕ} (hs : s < 131) :
    (cinstrAt s).isJump = false ∧ (cinstrAt s).cost = 1 := by
  rw [cinstrAt_const_seg hs]; unfold constInstr; split_ifs <;> exact ⟨rfl, rfl⟩

theorem root_shape {t : ℕ} (ht : t < 44) :
    (cinstrAt (rootBase + t)).isJump = false ∧ (cinstrAt (rootBase + t)).cost = if t < 43 then 10 else 1 := by
  rcases Nat.lt_or_ge t 43 with h | h
  · rw [cinstrAt_root h, if_pos h]; exact ⟨rfl, rfl⟩
  · rw [show t = 43 by omega, rootBase_add_43, cinstrAt_pk, if_neg (by omega)]; exact ⟨rfl, rfl⟩

theorem const_cost : ∑ i ∈ Finset.range 131, (cinstrAt (0 + i)).cost = 131 :=
  seg_cost (w := 1) fun i hi => (const_shape (by omega)).2

theorem root_cost : ∑ i ∈ Finset.range 44, (cinstrAt (rootBase + i)).cost = 431 := by
  rw [Finset.sum_range_succ, seg_cost (w := 10) fun i hi => by
    rw [(root_shape (by omega)).2, if_pos hi], (root_shape (by omega)).2, if_neg (by omega)]

section Chains

variable {κ : ℕ} {R : ℕ → Prop} {L : MemImage κ}

/-- **Rice chain.** From `rBase k`, a walk runs chain `k`'s dispatch to one chain digit `e`,
the leaf, and the body steps after it, and continues at `s0 k + 127`. -/
theorem walk_rice_chain (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {k n c : ℕ}
    (hk : k < 41 ∨ k = 42) (h : Walk R L n (rBase k) c) :
    ∃ e, off k ≤ e ∧ e < off k + nLeaves k ∧ ChainFacts R k e ∧ ChainDispatch R L k e ∧
      ∃ n' c', n = chainSteps k e + n' ∧ c = chainCost k e + c' ∧
        Walk R L n' (s0 k + 127) c' := by
  obtain ⟨x, hx, hU, n1, c1, rfl, rfl, hw1⟩ := walk_unary hR (riceShape hk) h
  rw [unaryExit_rice k hx] at hw1
  obtain ⟨b, hb, hG, n2, c2, rfl, rfl, hw2⟩ := walk_group hR hk hx hw1
  have he : off k + 2 * x + b < off k + nLeaves k := by rw [nLeaves_eq]; omega
  have he' := off_add_nLeaves k
  have hoff := off_le k
  obtain ⟨hl, n3, c3, rfl, rfl, hw3⟩ := walk_leaf hR hone hk (by omega) he hw2
  obtain ⟨hbd, n4, c4, rfl, rfl, hw4⟩ :=
    walk_body (k := k) (j0 := min (off k + 2 * x + b) 126 + 1) (by omega)
      (by unfold bodyFirst; omega) (by omega) (hw3.cast rfl (by omega) rfl)
  have hd : off k + 2 * x + b - off k = 2 * x + b := by omega
  have hq : (2 * x + b) / 2 = x := by omega
  have hr : (2 * x + b) % 2 = b := by omega
  refine ⟨off k + 2 * x + b, by omega, he, ⟨hl, fun j hj hj' => hbd j (by omega) hj'⟩,
    ⟨by rw [hd, hq]; exact hU, by rw [hd, hq, hr]; exact hG⟩, n4, c4, ?_, ?_, hw4⟩
  · unfold chainSteps riceDepth bodyLen; rw [hd, hq]; split_ifs <;> omega
  · unfold chainCost riceDepth bodyLen; rw [hd, hq]; split_ifs <;> omega

theorem walk_rice_chain_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV)
    {k e n c : ℕ} (hk : k < 41 ∨ k = 42) (he1 : off k ≤ e) (he2 : e < off k + nLeaves k)
    (hF : ChainFacts R k e) (hD : ChainDispatch R L k e) (h : Walk R L n (s0 k + 127) c) :
    Walk R L (chainSteps k e + n) (rBase k) (chainCost k e + c) := by
  have he' := off_add_nLeaves k
  have hoff := off_le k
  have heU : (e - off k) / 2 ≤ nU k := by rw [nLeaves_eq] at he2; omega
  have hw4 := walk_body_mk (k := k) (j0 := min e 126 + 1) (by omega) (by unfold bodyFirst; omega)
    (by omega) (fun j hj hj' => hF.2 j (by omega) hj') h
  have hw3 := walk_leaf_mk hR hone hk he1 he2 hF.1 (hw4.cast rfl (by omega) rfl)
  have hw2 := walk_group_mk hR hk (q := (e - off k) / 2) (b := (e - off k) % 2) heU (by omega) hD.2
    (hw3.cast rfl (by rw [show off k + 2 * ((e - off k) / 2) + (e - off k) % 2 = e by omega]) rfl)
  have hw1 := walk_unary_mk hR (riceShape hk) (x := (e - off k) / 2) heU hD.1
    (hw2.cast rfl (unaryExit_rice k heU).symm rfl)
  refine hw1.cast ?_ rfl ?_
  · unfold chainSteps riceDepth bodyLen; split_ifs <;> omega
  · unfold chainCost riceDepth bodyLen; split_ifs <;> omega

/-- **Chain 41.** From `rBase 41`, a walk runs the unary dispatch to one leaf `dh ≤ 50` (chain
digit `64 + dh`), the leaf, and the body steps after it, and continues at `s0 41 + 127`. -/
theorem walk_hi (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {n cost : ℕ}
    (h : Walk R L n (rBase 41) cost) :
    ∃ dh, dh ≤ 50 ∧ HiFacts R dh ∧ HiDispatch R L dh ∧ ∃ n' c',
      n = hiSteps dh + n' ∧ cost = hiCost dh + c' ∧ Walk R L n' (s0 41 + 127) c' := by
  obtain ⟨x, hx, hU, n1, c1, rfl, rfl, hw1⟩ := walk_unary hR hiShape h
  obtain ⟨dh, hdh, rfl⟩ : ∃ dh, dh ≤ 50 ∧ x = 50 - dh := ⟨50 - x, by omega, by omega⟩
  rw [unaryExit_hi hdh] at hw1
  obtain ⟨hl, n3, c3, rfl, rfl, hw3⟩ := walk_leafHi hR hone hdh hw1
  obtain ⟨hbd, n4, c4, rfl, rfl, hw4⟩ := walk_body (k := 41) (j0 := 64 + dh + 1)
    (by omega) (by rw [show bodyFirst 41 = 65 from rfl]; omega) (by omega)
    (hw3.cast rfl (by omega) rfl)
  refine ⟨dh, hdh, ⟨hl, fun j hj hj' => hbd j (by omega) hj'⟩, hU, n4, c4, ?_, ?_, hw4⟩
  · unfold hiSteps hiDepth; split_ifs <;> omega
  · unfold hiCost hiDepth; split_ifs <;> omega

theorem walk_hi_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {dh n cost : ℕ}
    (hdh : dh ≤ 50) (hF : HiFacts R dh) (hD : HiDispatch R L dh)
    (h : Walk R L n (s0 41 + 127) cost) :
    Walk R L (hiSteps dh + n) (rBase 41) (hiCost dh + cost) := by
  have hw4 := walk_body_mk (k := 41) (j0 := 64 + dh + 1) (by omega)
    (by rw [show bodyFirst 41 = 65 from rfl]; omega) (by omega)
    (fun j hj hj' => hF.2 j (by omega) hj') h
  have hw3 := walk_leafHi_mk hR hone hdh hF.1 (hw4.cast rfl (by omega) rfl)
  have hw1 := walk_unary_mk hR hiShape (x := 50 - dh) (by omega) hD
    (hw3.cast rfl (unaryExit_hi hdh).symm rfl)
  refine hw1.cast ?_ rfl ?_
  · unfold hiSteps hiDepth; split_ifs <;> omega
  · unfold hiCost hiDepth; split_ifs <;> omega

/-- The 41 message chains in sequence, from `rBase 0`. -/
theorem walk_chains (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) :
    ∀ j, j ≤ 41 → ∀ {n c : ℕ}, Walk R L n (rBase 0) c →
      ∃ E : ℕ → ℕ, (∀ k < j, off k ≤ E k ∧ E k < off k + nLeaves k ∧ ChainFacts R k (E k) ∧
          ChainDispatch R L k (E k)) ∧
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
    obtain ⟨e, he1, he2, hF, hD, n2, c2, rfl, rfl, hw2⟩ :=
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
      · simp only; exact ⟨he1, he2, hF, hD⟩
    · rw [hsum chainSteps]; omega
    · rw [hsum chainCost]; omega

theorem walk_chains_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) (E : ℕ → ℕ) :
    ∀ j, j ≤ 41 →
      (∀ k < j, off k ≤ E k ∧ E k < off k + nLeaves k ∧ ChainFacts R k (E k) ∧
        ChainDispatch R L k (E k)) →
      ∀ {n c : ℕ}, Walk R L n (rBase j) c →
        Walk R L ((∑ k ∈ Finset.range j, chainSteps k (E k)) + n) (rBase 0)
          ((∑ k ∈ Finset.range j, chainCost k (E k)) + c) := by
  intro j
  induction j with
  | zero => intro _ _ n c h; exact h.cast (by simp) rfl (by simp)
  | succ j ih =>
    intro hj hE n c h
    obtain ⟨he1, he2, hF, hD⟩ := hE j (by omega)
    have hw := walk_rice_chain_mk hR hone (Or.inl (by omega)) he1 he2 hF hD
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
  obtain ⟨hr0, n1, c1, rfl, hc1, hw1⟩ := walk_seg (a := 131) (s := 0)
    (fun i hi => (const_shape (by omega)).1) (by rw [sentinel]; omega) h
  rw [const_cost] at hc1
  subst hc1
  obtain ⟨E1, hE1, n2, c2, rfl, rfl, hw2⟩ :=
    walk_chains hR hone 41 le_rfl (hw1.cast rfl rBase_zero.symm rfl)
  obtain ⟨dh, hdh, hFHi, -, n3, c3, rfl, rfl, hw3⟩ := walk_hi hR hone hw2
  rw [s0_add_127 le_rfl] at hw3
  obtain ⟨e42, he42, he42', hF42, -, n4, c4, rfl, rfl, hw4⟩ :=
    walk_rice_chain hR hone (Or.inr rfl) hw3
  rw [s0_42_add_127] at hw4
  obtain ⟨hrt, n5, c5, rfl, hc5, hw5⟩ := walk_seg (a := 44) (s := rootBase)
    (fun i hi => (root_shape hi).1) (by rw [sentinel, rootBase]) hw4
  rw [root_cost] at hc5
  subst hc5
  obtain ⟨rfl, rfl⟩ := (hw5.cast rfl (show rootBase + 44 = sentinel from rfl) rfl).at_sentinel
  let E : ℕ → ℕ := fun k => if k < 41 then E1 k else if k = 41 then 64 + dh else e42
  have hElt : ∀ k < 41, E k = E1 k := fun k hk => if_pos hk
  have hE41 : E 41 - 64 = dh := by show 64 + dh - 64 = dh; omega
  have hE41' : E 41 = 64 + dh := rfl
  have hE42 : E 42 = e42 := rfl
  have hsum : ∀ F : ℕ → ℕ → ℕ, ∑ k ∈ Finset.range 41, F k (E k) =
      ∑ k ∈ Finset.range 41, F k (E1 k) := fun F =>
    Finset.sum_congr rfl fun k hk => by rw [hElt k (Finset.mem_range.mp hk)]
  refine ⟨E, ⟨fun k hk => ?_, by rw [hE41']; omega, by rw [hE41']; omega⟩, ?_, ?_,
    ⟨fun s hs => rcast (hr0 s hs) (by omega), fun k hk i hi => ?_, by rw [hE41]; exact hFHi.1,
    fun k hk j hj hj' => ?_, fun t ht => hrt t (by omega),
    rcast (hrt 43 (by omega)) rootBase_add_43⟩⟩
  · rcases hk with hk | rfl
    · rw [hElt k hk]; exact ⟨(hE1 k hk).1, (hE1 k hk).2.1⟩
    · exact ⟨he42, he42'⟩
  · unfold totalSteps; rw [hsum chainSteps, hE41, hE42]; omega
  · unfold totalCost; rw [hsum chainCost, hE41, hE42]; omega
  · rcases hk with hk | rfl
    · rw [hElt k hk] at hi ⊢; exact (hE1 k hk).2.2.1.1 i hi
    · exact hF42.1 i hi
  · rcases (show k < 41 ∨ k = 41 ∨ k = 42 by omega) with hk' | rfl | rfl
    · rw [hElt k hk'] at hj; exact (hE1 k hk').2.2.1.2 j hj hj'
    · exact hFHi.2 j hj hj'
    · exact hF42.2 j hj hj'

/-- **Walk of a leaf vector.** The path facts and the dispatch facts selecting `E` make a walk
from slot 0 of `totalSteps E` steps and cost `totalCost E`. -/
theorem walk_full_mk (hR : ∀ s, R s → HoldsNH L s) (hone : Lx L oneCell = oneV) {E : ℕ → ℕ}
    (hE : Valid E) (hP : PathFacts R E) (hD : DispatchFacts R L E) :
    Walk R L (totalSteps E) 0 (totalCost E) := by
  have hw5 := walk_seg_mk (L := L) (a := 44) (fun i hi => (root_shape hi).1)
    (by rw [sentinel, rootBase])
    (fun i hi => by
      rcases Nat.lt_or_ge i 43 with h | h
      · exact hP.root i h
      · exact rcast hP.pk (by rw [show i = 43 by omega, rootBase_add_43]))
    ((Walk.done (R := R) (L := L)).cast rfl (show sentinel = rootBase + 44 from rfl) rfl)
  rw [root_cost] at hw5
  obtain ⟨h42a, h42b⟩ := hE.1 42 (Or.inr rfl)
  have hw4 := walk_rice_chain_mk hR hone (k := 42) (Or.inr rfl) h42a h42b
    ⟨hP.leaf 42 (Or.inr rfl), hP.body 42 (by omega)⟩ (hD.rice 42 (Or.inr rfl))
    (hw5.cast rfl s0_42_add_127.symm rfl)
  have hE41a := hE.2.1
  have hE41b := hE.2.2
  have hw3 := walk_hi_mk hR hone (dh := E 41 - 64) (by omega)
    ⟨hP.leafHi, fun j hj hj' => hP.body 41 (by omega) j (by omega) hj'⟩ hD.hi
    (hw4.cast rfl (s0_add_127 le_rfl).symm rfl)
  have hw2 := walk_chains_mk hR hone E 41 le_rfl
    (fun k hk => ⟨(hE.1 k (Or.inl hk)).1, (hE.1 k (Or.inl hk)).2,
      ⟨hP.leaf k (Or.inl hk), hP.body k (by omega)⟩, hD.rice k (Or.inl hk)⟩) hw3
  have hw1 := walk_seg_mk (a := 131) (s := 0) (fun i hi => (const_shape (by omega)).1)
    (by rw [sentinel]; omega) (fun i hi => rcast (hP.const i hi) (by omega))
    (hw2.cast rfl rBase_zero rfl)
  rw [const_cost] at hw1
  refine hw1.cast ?_ rfl ?_
  · unfold totalSteps; omega
  · unfold totalCost; omega

end Chains

end

end OptimalOTS.LeanIsaBaseline.Machine
