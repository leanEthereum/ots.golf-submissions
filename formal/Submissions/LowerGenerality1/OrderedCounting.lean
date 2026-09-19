import Mathlib

/-! Count finite set families using the largest element of each directed difference. -/
noncomputable section
open scoped Classical
namespace OptimalOTS.DisclosureCounting
variable {ι α : Type*} [DecidableEq ι] [LinearOrder α]

/-- The largest element of `A i \ A j`, when it exists, belongs to `B j`. -/
def Witnesses (F : Finset ι) (A B : ι → Finset α) : Prop :=
  ∀ i ∈ F, ∀ j ∈ F, ∀ v ∈ A i \ A j,
    (∀ w ∈ A i \ A j, w ≤ v) → v ∈ B j

private theorem zero_left (F : Finset ι) (A : ι → Finset α)
    (hinj : Set.InjOn A F) (ha : ∀ i ∈ F, (A i).card ≤ 0) : F.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply hinj hi hj
  rw [Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (ha i hi)),
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (ha j hj))]

private theorem zero_right (F : Finset ι) (A B : ι → Finset α)
    (hinj : Set.InjOn A F) (hb : ∀ i ∈ F, (B i).card ≤ 0)
    (hw : Witnesses F A B) : F.card ≤ 1 := by
  have hsub : ∀ i ∈ F, ∀ j ∈ F, A i ⊆ A j := by
    intro i hi j hj
    by_contra hn
    have hn' : (A i \ A j).Nonempty := Finset.sdiff_nonempty.mpr hn
    have hv := hw i hi j hj ((A i \ A j).max' hn')
      (Finset.max'_mem _ _) (fun w hw => Finset.le_max' _ w hw)
    have he := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hb j hj))
    simpa only [he, Finset.notMem_empty] using hv
  exact Finset.card_le_one.mpr fun i hi j hj => hinj hi hj
    (Finset.Subset.antisymm (hsub i hi j hj) (hsub j hj i hi))

/-- Pascal's recurrence bounds a family by its element and boundary budgets. -/
theorem card_le_choose (r s : ℕ) (F : Finset ι) (A B : ι → Finset α)
    (hinj : Set.InjOn A F)
    (ha : ∀ i ∈ F, (A i).card ≤ r) (hb : ∀ i ∈ F, (B i).card ≤ s)
    (hw : Witnesses F A B) : F.card ≤ (r + s).choose r := by
  induction r generalizing s F A B with
  | zero => simpa using zero_left F A hinj ha
  | succ r ihr =>
    induction s generalizing F A B with
    | zero => simpa using zero_right F A B hinj hb hw
    | succ s ihs =>
      let U := F.biUnion A
      by_cases hU : U.Nonempty
      · let v := U.max' hU
        have hvU : v ∈ U := Finset.max'_mem _ _
        obtain ⟨i₀, hi₀, hv₀⟩ := Finset.mem_biUnion.mp hvU
        have hmax : ∀ i ∈ F, ∀ w ∈ A i, w ≤ v := by
          intro i hi w hw
          exact Finset.le_max' U w (Finset.mem_biUnion.mpr ⟨i, hi, hw⟩)
        let F₁ := F.filter fun i => v ∈ A i
        let F₀ := F.filter fun i => v ∉ A i
        have h₁ : ∀ i ∈ F₁, i ∈ F ∧ v ∈ A i := fun i hi => Finset.mem_filter.mp hi
        have h₀ : ∀ i ∈ F₀, i ∈ F ∧ v ∉ A i := fun i hi => Finset.mem_filter.mp hi
        have hvB : ∀ i ∈ F₀, v ∈ B i := by
          intro i hi
          exact hw i₀ hi₀ i (h₀ i hi).1 v
            (Finset.mem_sdiff.mpr ⟨hv₀, (h₀ i hi).2⟩)
            (fun w hw => hmax i₀ hi₀ w (Finset.mem_sdiff.mp hw).1)
        have hinj₁ : Set.InjOn (fun i => (A i).erase v) F₁ := by
          intro i hi j hj he
          apply hinj (h₁ i hi).1 (h₁ j hj).1
          have hh := congrArg (insert v) he
          simpa only [Finset.insert_erase (h₁ i hi).2, Finset.insert_erase (h₁ j hj).2] using hh
        have ha₁ : ∀ i ∈ F₁, ((A i).erase v).card ≤ r := by
          intro i hi
          rw [Finset.card_erase_of_mem (h₁ i hi).2]
          have hh := ha i (h₁ i hi).1
          omega
        have hw₁ : Witnesses F₁ (fun i => (A i).erase v) B := by
          intro i hi j hj w hw' hwm
          have hwne : w ≠ v := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hw').1).1
          have hwi : w ∈ A i := Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hw').1
          have hwj : w ∉ A j := by
            intro hj'
            exact (Finset.mem_sdiff.mp hw').2 (Finset.mem_erase.mpr ⟨hwne, hj'⟩)
          apply hw i (h₁ i hi).1 j (h₁ j hj).1 w (Finset.mem_sdiff.mpr ⟨hwi, hwj⟩)
          intro u hu
          have hune : u ≠ v := fun e => (Finset.mem_sdiff.mp hu).2 (e ▸ (h₁ j hj).2)
          apply hwm u
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_erase.mpr ⟨hune, (Finset.mem_sdiff.mp hu).1⟩,
              fun he => (Finset.mem_sdiff.mp hu).2 (Finset.mem_of_mem_erase he)⟩
        have hb₀ : ∀ i ∈ F₀, ((B i).erase v).card ≤ s := by
          intro i hi
          rw [Finset.card_erase_of_mem (hvB i hi)]
          have hh := hb i (h₀ i hi).1
          omega
        have hw₀ : Witnesses F₀ A (fun i => (B i).erase v) := by
          intro i hi j hj w hw' hwm
          refine Finset.mem_erase.mpr ⟨?_, hw i (h₀ i hi).1 j (h₀ j hj).1 w hw' hwm⟩
          intro he
          exact (h₀ i hi).2 (he ▸ (Finset.mem_sdiff.mp hw').1)
        have hc₁ := ihr (s + 1) F₁ (fun i => (A i).erase v) B hinj₁ ha₁
          (fun i hi => hb i (h₁ i hi).1) hw₁
        have hc₀ := ihs F₀ A (fun i => (B i).erase v)
          (fun i hi j hj he => hinj (h₀ i hi).1 (h₀ j hj).1 he)
          (fun i hi => ha i (h₀ i hi).1) hb₀ hw₀
        have hsum : F₁.card + F₀.card = F.card :=
          Finset.card_filter_add_card_filter_not (s := F) (p := fun i => v ∈ A i)
        calc F.card = F₁.card + F₀.card := hsum.symm
          _ ≤ (r + (s + 1)).choose r + (r + 1 + s).choose (r + 1) := Nat.add_le_add hc₁ hc₀
          _ = (r + 1 + (s + 1)).choose (r + 1) := by
            rw [show r + 1 + (s + 1) = (r + (s + 1)) + 1 by omega, Nat.choose_succ_succ]
            congr 2 <;> omega
      · have hz : ∀ i ∈ F, (A i).card ≤ 0 := by
          intro i hi
          have he : A i = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro w hw
            exact hU ⟨w, Finset.mem_biUnion.mpr ⟨i, hi, hw⟩⟩
          simp only [he, Finset.card_empty, le_refl]
        exact (zero_left F A hinj hz).trans (Nat.succ_le_of_lt (Nat.choose_pos (by omega)))
end OptimalOTS.DisclosureCounting
