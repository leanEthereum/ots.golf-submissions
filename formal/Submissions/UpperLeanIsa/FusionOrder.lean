import Submissions.UpperLeanIsa.FusionRecords

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open scoped Classical
noncomputable section
variable {P : Params}

/-- The dependency order, including the ordinary within-chain order. -/
def Earlier (a b : Loc P) : Prop :=
  match a,b with
  | .inl ⟨k,j⟩, .inl ⟨k',j'⟩ => evaluationRank k.val < evaluationRank k'.val ∨ k = k' ∧ j.val < j'.val
  | .inl _, .inr _ => True
  | .inr r, .inr s => r.val < s.val
  | .inr _, .inl _ => False

instance (a b : Loc P) : Decidable (Earlier a b) := by
  rcases a with ⟨k,j⟩ | r <;> rcases b with ⟨k',j'⟩ | s <;> unfold Earlier <;> infer_instance

theorem earlier_irrefl (a : Loc P) : ¬ Earlier a a := by
  cases a <;> simp [Earlier]

theorem children_getD_mem : ∀ u : Fin 6, ∀ i : Fin 5, (children u).getD i.val 0 ∈ children u := by decide

theorem children_bounded : ∀ u : Fin 6, ∀ d ∈ children u, d < 42 := by decide

theorem Params.active_owner {k : Fin 42} {j : ℕ} {u : Fin 6} (h : P.active k j = some u) :
    owner k = some u := by
  unfold Params.active at h
  split_ifs at h
  exact h

theorem Params.chainInput_congr (t t' : Tops) (k : Fin 42) (j : ℕ) (x : Word)
    (ht : ∀ u : Fin 6, owner k = some u → ∀ d ∈ children u, t d = t' d) :
    P.chainInput t k j x = P.chainInput t' k j x := by
  unfold Params.chainInput
  cases ha : P.active k j with
  | none => rfl
  | some u =>
    have hh (i : Fin 5) := ht u (Params.active_owner ha) _ (children_getD_mem u i)
    have h0 : t ((children u).getD 0 0) = t' ((children u).getD 0 0) := hh 0
    have h1 : t ((children u).getD 1 0) = t' ((children u).getD 1 0) := hh 1
    have h2 : t ((children u).getD 2 0) = t' ((children u).getD 2 0) := hh 2
    have h3 : t ((children u).getD 3 0) = t' ((children u).getD 3 0) := hh 3
    have h4 : t ((children u).getD 4 0) = t' ((children u).getD 4 0) := hh 4
    simp only [fusionWords, h0, h1, h2, h3, h4]

theorem Record.word_agree (ξ ζ : Record P) (k : Fin 42) (j : ℕ)
    (hs : ξ.1 k = ζ.1 k)
    (hy : ∀ l : Fin (P.codec.len k - 1), l.val + 1 = j → ξ.2 (.inl ⟨k,l⟩) = ζ.2 (.inl ⟨k,l⟩)) :
    ξ.word k j = ζ.word k j := by
  cases j with
  | zero => exact hs
  | succ j =>
    by_cases hj : j < P.codec.len k - 1
    · rw [Record.word_succ _ _ _ hj, Record.word_succ _ _ _ hj, hy ⟨j,hj⟩ rfl]
    · simp only [Record.word, dif_neg hj]

theorem Record.input_agree (ξ ζ : Record P) (a : Loc P) (hs : ξ.1 = ζ.1)
    (hy : ∀ b, Earlier b a → ξ.2 b = ζ.2 b) : ξ.input a = ζ.input a := by
  cases a with
  | inl a =>
    rcases a with ⟨k,j⟩
    change P.chainInput ξ.tops k j (ξ.word k j) = P.chainInput ζ.tops k j (ζ.word k j)
    have hw : ξ.word k j = ζ.word k j := Record.word_agree ξ ζ k j (congrFun hs k) (by
      intro l hl
      exact hy _ (Or.inr ⟨rfl,by omega⟩))
    rw [hw]
    apply Params.chainInput_congr
    intro u hu d hd
    have hdlt := children_bounded u d hd
    change Layer.Params.topAt ξ.top d = Layer.Params.topAt ζ.top d
    rw [Layer.Params.topAt, Layer.Params.topAt, dif_pos hdlt, dif_pos hdlt]
    apply Record.word_agree ξ ζ ⟨d,hdlt⟩ _ (congrFun hs _)
    intro l _
    apply hy
    exact Or.inl (dependency_precedes u u.isLt k.val ((owner_mem k u).mp hu) d hd)
  | inr r =>
    have ht : ξ.tops = ζ.tops := by
      funext d
      unfold Record.tops Layer.Params.topAt
      split_ifs with hd
      · apply Record.word_agree ξ ζ ⟨d,hd⟩ _ (congrFun hs _)
        intro l _
        exact hy _ trivial
      · rfl
    have hr : ξ.rootState r = ζ.rootState r := by
      rcases r with ⟨r,hr⟩
      cases r with
      | zero => rfl
      | succ r =>
        have hrl : r < 3 := by omega
        change ξ.rootState (r+1) = ζ.rootState (r+1)
        rw [Record.rootState_succ ξ ⟨r,hrl⟩, Record.rootState_succ ζ ⟨r,hrl⟩]
        exact hy (.inr ⟨r,hrl⟩) (by change r < r+1; omega)
    change P.rootInput ξ.tops r (ξ.rootState r) = P.rootInput ζ.tops r (ζ.rootState r)
    rw [ht,hr]

theorem Record.input_update (seeds : Fin 42 → Word) (y : Loc P → BitVec hashBits)
    (a b : Loc P) (v : BitVec hashBits) (hb : ¬ Earlier b a) :
    Record.input (seeds,Function.update y b v) a = Record.input (seeds,y) a := by
  apply Record.input_agree (seeds,Function.update y b v) (seeds,y) a rfl
  intro c hc
  have hcb : c ≠ b := by
    intro h
    subst c
    exact hb hc
  exact Function.update_of_ne hcb v y

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
