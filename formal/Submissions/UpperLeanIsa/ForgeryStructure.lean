import Submissions.UpperLeanIsa.Correctness

/-! Deterministic extraction facts for a future security reduction.

These are not probability bounds. In particular, a witness to a hash second preimage is
not itself a proof of the contract's `Secure` property. The adaptive random-oracle
reduction must still bound the probability of obtaining these witnesses.
-/

namespace OptimalOTS.LeanIsaBaseline

def stepValue (f : HashTable) (i j : ℕ) (x : Word) : Word :=
  (f ⟨896, chainInput i j x⟩).extractLsb' 0 128

/-- Distinct checksum encodings require moving backwards in at least one chain. -/
theorem exists_lower_digit {m₁ m₂ : Message} (h : m₁ ≠ m₂) :
    ∃ i : Fin 43, digit m₂ i < digit m₁ i := by
  by_contra hn
  push Not at hn
  apply (digits_incomparable h).1
  apply List.forall₂_of_length_eq_of_get (by rw [digits_length, digits_length])
  intro i hi hj
  exact hn ⟨i, by simpa only [digits_length] using hi⟩

/-- If two continuations merge, either they began at the same word or the compared
paths exhibit a second preimage for one of the honest path's step outputs. -/
theorem chain_merge (f : HashTable) (i j n : ℕ) (x y : Word)
    (h : chainValue f i j n x = chainValue f i j n y) :
    x = y ∨ ∃ k, k < n ∧
      chainValue f i j k x ≠ chainValue f i j k y ∧
      stepValue f i (j + k) (chainValue f i j k x) =
        stepValue f i (j + k) (chainValue f i j k y) := by
  induction n generalizing j x y with
  | zero => exact Or.inl h
  | succ n ih =>
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      rcases ih (j + 1) (stepValue f i j x) (stepValue f i j y) h with heq | ⟨k, hk, hne, heq⟩
      · exact ⟨0, by omega, hxy, heq⟩
      · refine ⟨k + 1, by omega, hne, ?_⟩
        change stepValue f i (j + (k + 1)) (chainValue f i (j + 1) k (stepValue f i j x)) =
          stepValue f i (j + (k + 1)) (chainValue f i (j + 1) k (stepValue f i j y))
        rw [show j + (k + 1) = (j + 1) + k by omega]
        exact heq

def honestWord (f : HashTable) (sk : Words) (i : Fin 43) (j : ℕ) : Word :=
  chainValue f i.val 0 j (sk i)

/-- A second preimage for one particular step of the honest chain. -/
def ChainSecondPreimage (f : HashTable) (sk : Words) (i : Fin 43) (j : ℕ) (y : Word) : Prop :=
  j < 127 ∧ y ≠ honestWord f sk i j ∧
    stepValue f i.val j y = stepValue f i.val j (honestWord f sk i j)

theorem honest_continuation (f : HashTable) (sk : Words) (i : Fin 43) (j n : ℕ) :
    chainValue f i.val j n (honestWord f sk i j) = honestWord f sk i (j + n) := by
  simpa only [Nat.zero_add, honestWord] using chainValue_add f i.val 0 j n (sk i)

/-- Reaching an honest endpoint from a candidate signature word either discloses the
actual word at that position or gives a second preimage on the traversed path. -/
theorem endpoint_match (f : HashTable) (sk : Words) (i : Fin 43) (j : ℕ) (hj : j ≤ 127)
    (x : Word) (h : chainValue f i.val j (127 - j) x = endpoints f sk i) :
    x = honestWord f sk i j ∨ ∃ k, j ≤ k ∧
      ChainSecondPreimage f sk i k (chainValue f i.val j (k - j) x) := by
  have href : chainValue f i.val j (127 - j) (honestWord f sk i j) = endpoints f sk i := by
    rw [honest_continuation, Nat.add_sub_of_le hj]
    rfl
  rcases chain_merge f i.val j (127 - j) x (honestWord f sk i j) (h.trans href.symm) with
    heq | ⟨k, hk, hne, heq⟩
  · exact Or.inl heq
  · right
    refine ⟨j + k, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    refine ⟨by omega, ?_, ?_⟩
    · simpa only [honest_continuation] using hne
    · simpa only [honest_continuation] using heq

/-- The second-preimage input must occur on the candidate's verification path.
Existence somewhere in the entire oracle table would not be a useful security event. -/
def ChainForgeryEvent (f : HashTable) (sk : Words) (m : Message) (bits : List Bool) : Prop :=
  ∃ (i : Fin 43) (k : ℕ), digit m i ≤ k ∧
    ChainSecondPreimage f sk i k
      (chainValue f i.val (digit m i) (k - digit m i) (decode bits i))

/-- A different signed message with the same reconstructed endpoints either reveals
an honest word strictly before the disclosed cut, or yields a chain second preimage.
Root binding is deliberately an explicit hypothesis, not an assumed theorem. -/
theorem different_message_forgery (f : HashTable) (sk : Words) (m₁ m₂ : Message)
    (bits : List Bool) (hm : m₁ ≠ m₂)
    (he : reconstructedWords f m₂ bits = endpoints f sk) :
    (∃ i : Fin 43, digit m₂ i < digit m₁ i ∧
      decode bits i = honestWord f sk i (digit m₂ i)) ∨
    ChainForgeryEvent f sk m₂ bits := by
  obtain ⟨i, hi⟩ := exists_lower_digit hm
  have h := congrFun he i
  rcases endpoint_match f sk i (digit m₂ i) (digit_le m₂ i) (decode bits i) h with
    heq | ⟨k, hk, hs⟩
  · exact Or.inl ⟨i, hi, heq⟩
  · exact Or.inr ⟨i, k, hk, hs⟩

/-- Changing only the signature at the same message also needs a second preimage,
provided the reconstructed endpoint vector is unchanged. Canonical wire encoding
rules out a different bit string that decodes to the same vector. -/
theorem same_message_forgery (f : HashTable) (sk : Words) (m : Message) (bits : List Bool)
    (hlen : bits.length = 5504) (hne : bits ≠ encode (signedWords f sk m))
    (he : reconstructedWords f m bits = endpoints f sk) :
    ChainForgeryEvent f sk m bits := by
  have hd : decode bits ≠ signedWords f sk m := by
    intro h
    apply hne
    rw [← encode_decode bits hlen, h]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hd
  rcases endpoint_match f sk i (digit m i) (digit_le m i) (decode bits i) (congrFun he i) with
    heq | ⟨k, hk, hs⟩
  · exact (hi heq).elim
  · exact ⟨i, k, hk, hs⟩

end OptimalOTS.LeanIsaBaseline
