import Submissions.UpperLeanIsa.FusionScheme
import Submissions.UpperLeanIsa.FusionConcrete

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open scoped Classical
noncomputable section
variable {P : Params}

theorem earlier_asymm (a b : Loc P) (h : Earlier a b) : ¬ Earlier b a := by
  rcases a with ⟨k,j⟩ | r <;> rcases b with ⟨k',j'⟩ | s
  · change _ ∨ _ at h
    change ¬ (_ ∨ _)
    rintro (hr | ⟨hk,hj⟩)
    · rcases h with hl | ⟨rfl,hl⟩ <;> omega
    · subst k'
      rcases h with hl | ⟨_,hl⟩ <;> omega
  · exact id
  · exact h.elim
  · change r.val < s.val at h
    change ¬ s.val < r.val
    omega

/-- Future updates preserve every earlier query and answer. -/
theorem Params.evalLocationsValue_preserves (P : Params) (f : HashTable) (seeds : Fin 42 → Word)
    (l : List (Loc P)) (y : Tbl P) (a : Loc P)
    (h : ∀ b ∈ l, b ≠ a ∧ ¬ Earlier b a) :
    (P.evalLocationsValue f seeds l y) a = y a ∧
      Record.input (seeds,P.evalLocationsValue f seeds l y) a = Record.input (seeds,y) a := by
  induction l generalizing y with
  | nil => exact ⟨rfl,rfl⟩
  | cons b l ih =>
    have hb := h b (by simp)
    have hl : ∀ c ∈ l, c ≠ a ∧ ¬ Earlier c a := fun c hc => h c (by simp [hc])
    rw [Params.evalLocationsValue]
    obtain ⟨hv,hq⟩ := ih (Function.update y b (f ⟨896,Record.input (seeds,y) b⟩)) hl
    exact ⟨hv.trans (Function.update_of_ne hb.1.symm _ y),
      hq.trans (Record.input_update seeds y a b _ hb.2)⟩

/-- Every query in a correctly ordered DAG agrees with the final record. -/
theorem Params.evalLocationsValue_coherent (P : Params) (f : HashTable) (seeds : Fin 42 → Word)
    (l : List (Loc P)) (hl : l.Pairwise Earlier) (y : Tbl P) :
    ∀ a ∈ l, (P.evalLocationsValue f seeds l y) a =
      f ⟨896,Record.input (seeds,P.evalLocationsValue f seeds l y) a⟩ := by
  induction l generalizing y with
  | nil => simp
  | cons b l ih =>
    obtain ⟨hb,ht⟩ := List.pairwise_cons.mp hl
    let v := f ⟨896,Record.input (seeds,y) b⟩
    let y' := Function.update y b v
    have hpres : ∀ c ∈ l, c ≠ b ∧ ¬ Earlier c b := by
      intro c hc
      have hbc := hb c hc
      refine ⟨?_,earlier_asymm b c hbc⟩
      intro he
      subst c
      exact earlier_irrefl b hbc
    have hp := P.evalLocationsValue_preserves f seeds l y' b hpres
    intro a ha
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      change (P.evalLocationsValue f seeds l y') b = _
      rw [hp.1]
      have hq : Record.input (seeds,P.evalLocationsValue f seeds l y') b = Record.input (seeds,y) b :=
        hp.2.trans (Record.input_update seeds y b b v (earlier_irrefl b))
      change y' b = f ⟨896,Record.input (seeds,P.evalLocationsValue f seeds l y') b⟩
      rw [hq]
      exact Function.update_self b v y
    · exact ih ht y' a ha

theorem Params.locationOrder_mem (P : Params) (a : Loc P) : a ∈ P.locationOrder := by
  cases a with
  | inl a =>
    rcases a with ⟨k,j⟩
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨k,?_,?_⟩
    · exact chainOrder_permutation.mem_iff.mpr (List.mem_finRange k)
    · exact List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩
  | inr r =>
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨r,List.mem_finRange r,rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem concrete_ordered : params.locationOrder.Pairwise Earlier := by decide +kernel

theorem concrete_location_count : params.locationOrder.length = 628 := by decide +kernel

/-- Coherence of every key-generation output for any fixed oracle, with no good-event assumption. -/
theorem concrete_coherent (f : HashTable) (seeds : Fin 42 → Word) :
    let y := params.evalLocationsValue f seeds params.locationOrder (fun _ => 0)
    ∀ a : Loc params, y a = f ⟨896,Record.input (seeds,y) a⟩ := by
  intro y a
  exact params.evalLocationsValue_coherent f seeds _ concrete_ordered _ a (params.locationOrder_mem a)

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
