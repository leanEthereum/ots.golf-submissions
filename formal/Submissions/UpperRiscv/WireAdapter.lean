import Submissions.UpperRiscv.AlgorithmCosts

/-! Transfer a typed-signature admissibility certificate to the contract's scheme on the encoded
bit strings. Signing outputs the encoding; verification parses a bit string with `decode`. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WireAdapter

variable (S : TypedScheme) (decode : List Bool → S.Signature)

/-- The scheme on bit strings. -/
abbrev scheme : OracleAlgorithm.Scheme where
  SecretKey := S.SecretKey
  keygen := S.keygen
  sign := fun sk m => Option.map S.encodeSignature <$> S.sign sk m
  verify := fun pk m bits => S.verify pk m (decode bits)

variable (inverse : ∀ σ, decode (S.encodeSignature σ) = σ)
  (canonical : ∀ pk m bits, true ∈ support (S.verify pk m (decode bits)) →
    S.encodeSignature (decode bits) = bits)

include inverse in
theorem correct (h : S.Correct) : (scheme S decode).Correct := by
  unfold TypedScheme.Correct at h
  unfold OracleAlgorithm.Scheme.Correct
  intro message
  rw [← h message]
  congr 1
  simp only [scheme, bind_map_left]
  apply bind_congr
  intro keys
  apply bind_congr
  intro signed
  cases signed <;> simp only [Option.map_none, Option.map_some, inverse]

theorem signingFailure (ε : ℝ≥0∞) (h : S.SigningFailureAtMost ε) :
    (scheme S decode).SigningFailureAtMost ε := by
  intro message
  have original := h message
  simpa only [OracleAlgorithm.Scheme.SigningFailureAtMost, scheme, bind_map_left,
    Option.isNone_map] using original

theorem signatureSize (n : ℕ) (h : S.SignatureSizeAtMost n) :
    (scheme S decode).SignatureSizeAtMost n := by
  intro sk m bits hb
  change some bits ∈ support (Option.map S.encodeSignature <$> S.sign sk m) at hb
  rw [support_map] at hb
  obtain ⟨signed, hs, he⟩ := hb
  cases signed with
  | none => cases he
  | some σ =>
    have equal : S.encodeSignature σ = bits := Option.some.inj he
    rw [← equal]
    exact h sk m σ hs

include canonical in
theorem rejectsOversized (n : ℕ) (h : S.RejectsOversized n) :
    (scheme S decode).RejectsOversized n := by
  intro pk m bits hsize accepted
  have hc := canonical pk m bits accepted
  exact h pk m (decode bits) (by simpa only [hc] using hsize) accepted

theorem verifyCost (c : ℕ) (h : S.VerifyCostAtMost c) : (scheme S decode).VerifyCostAtMost c :=
  fun pk m bits => h pk m (decode bits)

include inverse canonical in
/-- Admissibility transfers; the verification budget (a core requirement since the cap on
`verifyBudget`) comes from the typed scheme's own verification-cost bound. -/
theorem admissible (h : S.Admissible (1 / 2 ^ signingFailureBits)) (c : ℕ)
    (hc : S.VerifyCostAtMost c) (hle : c ≤ verifyBudget) :
    (scheme S decode).Admissible where
  correct := correct S decode inverse h.correct
  verifyDeterministic := fun pk m bits => h.verifyDeterministic pk m (decode bits)
  signingFailure := signingFailure S decode _ h.signingFailure
  signatureSize := signatureSize S decode maxSignatureBits h.signatureSize
  rejectsOversized := rejectsOversized S decode canonical maxSignatureBits h.rejectsOversized
  keygenCost := h.keygenCost
  signCost := fun sk m => AlgorithmCosts.CostAtMost.map (h.signCost sk m) _
  verifyCost := OracleAlgorithm.Scheme.VerifyCostAtMost.mono _ (verifyCost S decode c hc) hle

end OptimalOTS.WireAdapter
