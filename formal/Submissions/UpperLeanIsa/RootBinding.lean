import Submissions.UpperLeanIsa.ForgeryStructure

/-! Extraction of the root-hash failure event, without assuming root injectivity.
Probability bounds for these events remain separate obligations. -/

namespace OptimalOTS.LeanIsaBaseline

def absorbValue (f : HashTable) (remaining : ℕ) (cv : BitVec 256) (x : Word) : BitVec 256 :=
  f ⟨896, LeanIsa.hashInput cv (x.setWidth 512) (BitVec.ofNat 128 (2 + remaining))⟩

/-- A mismatching absorption input with the same output as the honest path.
Only the last absorption compares truncated outputs; internal ones compare all 256 bits.
The right-hand path is the honest endpoint vector, not an arbitrary collision target. -/
def RootSecondPreimage (f : HashTable) :
    List Word → BitVec 256 → List Word → BitVec 256 → Prop
  | [x], cv, [y], dv =>
      (cv ≠ dv ∨ x ≠ y) ∧
        (absorbValue f 0 cv x).extractLsb' 0 128 = (absorbValue f 0 dv y).extractLsb' 0 128
  | x :: xs, cv, y :: ys, dv =>
      ((cv ≠ dv ∨ x ≠ y) ∧ absorbValue f xs.length cv x = absorbValue f ys.length dv y) ∨
        RootSecondPreimage f xs (absorbValue f xs.length cv x) ys (absorbValue f ys.length dv y)
  | _, _, _, _ => False

/-- Matching roots for different nonempty inputs force a concrete second-preimage
event on the two evaluated paths. It makes no injectivity assumption about a random hash. -/
theorem root_match (f : HashTable) (xs ys : List Word) (cv dv : BitVec 256)
    (hlen : xs.length = ys.length) (hne : xs ≠ [])
    (h : (rootValueFold f xs cv).extractLsb' 0 128 =
      (rootValueFold f ys dv).extractLsb' 0 128) :
    (cv = dv ∧ xs = ys) ∨ RootSecondPreimage f xs cv ys dv := by
  induction xs generalizing ys cv dv with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := Nat.succ.inj hlen
      by_cases he : cv = dv ∧ x = y ∧ xs = ys
      · exact Or.inl ⟨he.1, by rw [he.2.1, he.2.2]⟩
      · right
        cases xs with
        | nil =>
          have hy : ys = [] := List.length_eq_zero_iff.mp ht.symm
          subst ys
          refine ⟨?_, h⟩
          tauto
        | cons z zs =>
          change ((cv ≠ dv ∨ x ≠ y) ∧ absorbValue f (z :: zs).length cv x = absorbValue f ys.length dv y) ∨
            RootSecondPreimage f (z :: zs) (absorbValue f (z :: zs).length cv x) ys (absorbValue f ys.length dv y)
          rcases ih ys (absorbValue f (z :: zs).length cv x) (absorbValue f ys.length dv y) ht (by simp) h with
            ⟨hcv, hxs⟩ | hc
          · left
            exact ⟨by tauto, hcv⟩
          · exact Or.inr hc

theorem root_value_match (f : HashTable) (xs ys : Words) (h : rootValue f xs = rootValue f ys) :
    xs = ys ∨ RootSecondPreimage f (List.ofFn xs) 0 (List.ofFn ys) 0 := by
  rcases root_match f (List.ofFn xs) (List.ofFn ys) 0 0
      (by rw [List.length_ofFn, List.length_ofFn]) (by simp) h with ⟨_, he⟩ | hc
  · exact Or.inl (List.ofFn_injective he)
  · exact Or.inr hc

/-- The deterministic forgery alternatives. This is a structural reduction, not the
random-oracle probability bound required by `scheme.Secure`. -/
def ForgeryEvent (f : HashTable) (sk : Words) (signedMessage forgedMessage : Message)
    (bits : List Bool) : Prop :=
  RootSecondPreimage f (List.ofFn (reconstructedWords f forgedMessage bits)) 0
      (List.ofFn (endpoints f sk)) 0 ∨
    ChainForgeryEvent f sk forgedMessage bits ∨
    (∃ i : Fin 34, digit forgedMessage i < digit signedMessage i ∧
      decode bits i = honestWord f sk i (digit forgedMessage i))

theorem accepted_forgery_event (f : HashTable) (sk : Words) (m₁ m₂ : Message) (bits : List Bool)
    (hlen : bits.length = 4352)
    (hroot : rootValue f (reconstructedWords f m₂ bits) = rootValue f (endpoints f sk))
    (hfresh : (m₁, encode (signedWords f sk m₁)) ≠ (m₂, bits)) :
    ForgeryEvent f sk m₁ m₂ bits := by
  rcases root_value_match f _ _ hroot with he | hc
  · by_cases hm : m₁ = m₂
    · subst m₂
      exact Or.inr (Or.inl (same_message_forgery f sk m₁ bits hlen
        (fun hb => hfresh (by rw [hb])) he))
    · rcases different_message_forgery f sk m₁ m₂ bits hm he with hw | hs
      · exact Or.inr (Or.inr hw)
      · exact Or.inr (Or.inl hs)
  · exact Or.inl hc

end OptimalOTS.LeanIsaBaseline
