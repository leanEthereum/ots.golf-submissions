import Submissions.UpperCompressions.AlgorithmCosts

/-! Transfer a typed-signature certificate to the contract's scheme on the encoded bit strings.
Signing outputs the encoding; verification parses a bit string with `decode`. -/

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

def adversary (A : OracleAlgorithm.Adversary) : S.Adversary where
  State := A.State
  choose := A.choose
  forge := fun state signed =>
    (fun pair => (pair.1, decode pair.2)) <$> A.forge state (signed.map S.encodeSignature)

variable (inverse : ∀ σ, decode (S.encodeSignature σ) = σ)
  (canonical : ∀ pk m bits, true ∈ support (S.verify pk m (decode bits)) →
    S.encodeSignature (decode bits) = bits)

include inverse canonical in
theorem experiment_eq (A : OracleAlgorithm.Adversary) :
    OracleAlgorithm.experiment (scheme S decode) A = S.experiment (adversary S decode A) := by
  simp only [OracleAlgorithm.experiment, TypedScheme.experiment, scheme, adversary,
    bind_map_left]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr_of_forall_mem_support
  intro ok hok
  cases ok with
  | false => rfl
  | true =>
    have hc := canonical keys.1 forged.1 forged.2 hok
    congr 1
    cases signed with
    | none => simp
    | some σ =>
      simp only [Option.map_some, Bool.true_and]
      have he : S.encodeSignature σ = forged.2 ↔ σ = decode forged.2 := by
        constructor
        · intro h
          have hd := congrArg decode h
          simpa only [inverse] using hd
        · intro h
          simpa only [h] using hc
      simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, he]

include inverse canonical in
theorem secure (h : S.Secure) : (scheme S decode).Secure := by
  intro A B hB
  rw [experiment_eq S decode inverse canonical A] at hB ⊢
  exact h (adversary S decode A) B hB

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

include inverse canonical in
theorem admissible (h : S.Admissible (1 / 2 ^ signingFailureBits)) :
    (scheme S decode).Admissible where
  correct := correct S decode inverse h.correct
  verifyDeterministic := fun pk m bits => h.verifyDeterministic pk m (decode bits)
  signingFailure := signingFailure S decode _ h.signingFailure
  signatureSize := signatureSize S decode maxSignatureBits h.signatureSize
  rejectsOversized := rejectsOversized S decode canonical maxSignatureBits h.rejectsOversized
  keygenCost := h.keygenCost
  signCost := fun sk m => AlgorithmCosts.CostAtMost.map (h.signCost sk m) _

theorem verifyCost (c : ℕ) (h : S.VerifyCostAtMost c) : (scheme S decode).VerifyCostAtMost c :=
  fun pk m bits => h pk m (decode bits)

end OptimalOTS.WireAdapter
