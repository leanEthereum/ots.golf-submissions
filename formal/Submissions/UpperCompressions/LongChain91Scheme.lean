import Submissions.UpperCompressions.LongChain91CutBridge
import Submissions.UpperCompressions.LongChain91Codec
import Submissions.UpperCompressions.ProofBundle04

/-!
# The concrete cost-87 long-chain scheme

This module selects the schedule's classes injectively from the certified
cost-86 cut family, instantiates the generic 86-bit weighted signer, and
discharges the honest-party resource and availability obligations.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open WeightedSampling.Availability

abbrev M : ℕ := LongChain91Schedule.M

theorem schedule_capacity : M ≤ family.card := by
  change Chain18Compact.familyCardinality ≤ family.card
  rw [Chain18Compact.familyCardinality_exact, card_family_exact]

/-- The first `M` members of the certified family.  `selectCut` uses the
finite family's canonical equivalence, so distinct schedule classes disclose
distinct cuts. -/
def setsName (i : Fin M) : Finset Name := selectCut schedule_capacity i

theorem setsName_mem (i : Fin M) : setsName i ∈ family :=
  selectCut_mem schedule_capacity i

theorem setsName_injective : Function.Injective setsName :=
  selectCut_injective schedule_capacity

/-- The concrete weighted DAG scheme. -/
def scheme : WeightedScheme.Scheme M where
  graph := graph
  sets i := fins (setsName i)
  decode := LongChain91Schedule.decode
  tier i := (LongChain91Schedule.tier i).val
  root_not_mem i := family_root_not_mem (setsName_mem i)
  no_hidden_source i := family_no_hidden_source (setsName_mem i)
  reveal_le i := family_disclosure_and_nonce (setsName_mem i)
  keygen_le := by
    rw [graph_keygenCost]
    norm_num [keygenBudget]

theorem scheme_reconstructCost (i : Fin M) :
    scheme.graph.reconstructCost (scheme.sets i) ≤ 86 :=
  family_reconstructCost (setsName_mem i)

theorem scheme_keygenCost : scheme.graph.keygenCost = 865 := graph_keygenCost

abbrev typed : TypedScheme := scheme.toAlgorithm

theorem typed_cost : typed.VerifyCostAtMost 87 :=
  scheme.verifyCost scheme_reconstructCost

theorem typed_correct : typed.Correct := scheme.correct

theorem typed_signatureSize : typed.SignatureSizeAtMost maxSignatureBits :=
  scheme.signatureSize

theorem typed_rejectsOversized : typed.RejectsOversized maxSignatureBits :=
  scheme.rejectsOversized

theorem typed_keygenCost : typed.KeygenCostAtMost keygenBudget := scheme.keygenCost

theorem typed_signCost : typed.SignCostAtMost signBudget := scheme.signCost

theorem typed_verifyDeterministic : typed.VerifyDeterministic :=
  scheme.verifyDeterministic

/-! ## The 86-bit wire adapter -/

def decodeWire (bits : List Bool) : WeightedScheme.Signature :=
  NonceCodec.decode 86 bits

theorem decodeWire_encode (s : WeightedScheme.Signature) :
    decodeWire (typed.encodeSignature s) = s :=
  NonceCodec.decode_encode s

theorem accepted_payload_positive (pk : PublicKey) (m : Message)
    (s : WeightedScheme.Signature)
    (h : true ∈ support (scheme.verify pk m s)) : 0 < s.2.length := by
  rw [WeightedScheme.Scheme.verify, support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨w, _, h⟩ := h
  cases hd : scheme.decode w with
  | none => simp [hd] at h
  | some i =>
      simp only [hd] at h
      by_cases hlen : s.2.length = scheme.graph.revealBits (scheme.sets i)
      · rw [hlen]
        exact family_revealBits_pos (setsName_mem i)
      · simp [hlen] at h

theorem wire_canonical (pk : PublicKey) (m : Message) (bits : List Bool)
    (h : true ∈ support (typed.verify pk m (decodeWire bits))) :
    typed.encodeSignature (decodeWire bits) = bits := by
  exact NonceCodec.canonical_of_payload_positive
    (accepted_payload_positive pk m (decodeWire bits) h)

def wireScheme : OracleAlgorithm.Scheme := WireAdapter.scheme typed decodeWire

theorem wire_cost : wireScheme.VerifyCostAtMost 87 :=
  WireAdapter.verifyCost typed decodeWire 87 typed_cost

/-! ## Honest signing availability

The decoder accepts exactly `acceptedAliases` of the `2^256` oracle words.
The signer samples with replacement, so an occupied 86-bit nonce contributes
the cache-collision term `L / 2^86` inside every trial's miss probability.
-/

def honestMiss : ℝ≥0∞ :=
  ((2^256 - Chain18Compact.acceptedAliases : ℕ) : ℝ≥0∞) /
    (2 : ℝ≥0∞)^256

theorem uniform_miss (a : ℝ≥0∞) :
    E ($ᵗ BitVec hashBits)
      (fun w => if (scheme.decode w).isNone then a else 0) = honestMiss * a := by
  change E ($ᵗ BitVec 256)
    (fun w => if (LongChain91Schedule.decode w).isNone then a else 0) = _
  rw [uniform_option_miss LongChain91Schedule.decode
    Chain18Compact.acceptedAliases LongChain91Schedule.accepted_count a]
  rfl

theorem honestMiss_ne_top : honestMiss ≠ ⊤ := by
  unfold honestMiss
  finiteness

theorem honestBase_ne_top :
    honestMiss + (Chain18Compact.L : ℝ≥0∞) / (2 : ℝ≥0∞)^86 ≠ ⊤ := by
  exact ENNReal.add_ne_top.mpr ⟨honestMiss_ne_top, by finiteness⟩

theorem honestBase_toReal :
    (honestMiss + (Chain18Compact.L : ℝ≥0∞) / (2 : ℝ≥0∞)^86).toReal =
      Chain18Compact.replacementBase := by
  rw [ENNReal.toReal_add honestMiss_ne_top (by finiteness)]
  unfold honestMiss Chain18Compact.replacementBase
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]
  unfold Chain18Compact.R
  have hA : Chain18Compact.acceptedAliases ≤ 2^256 := by
    simpa [Chain18Compact.R] using Chain18Compact.acceptedAliases_bounds.2.le
  rw [Nat.cast_sub hA]
  norm_num
  ring

theorem honestBase_eq_ofReal :
    honestMiss + (Chain18Compact.L : ℝ≥0∞) / (2 : ℝ≥0∞)^86 =
      ENNReal.ofReal Chain18Compact.replacementBase := by
  rw [← honestBase_toReal]
  exact (ENNReal.ofReal_toReal honestBase_ne_top).symm

/-- The real fixed-point certificate from `CompactSchedule91` is exactly the
failure envelope needed by the memoized with-replacement signer. -/
theorem honest_replacement_envelope :
    (honestMiss + (Chain18Compact.L : ℝ≥0∞) / (2 : ℝ≥0∞)^86) ^
        Chain18Compact.L ≤
      1 / (2 : ℝ≥0∞)^129 := by
  have h := ENNReal.ofReal_le_ofReal Chain18Compact.collisionAwareAvailability.le
  rw [ENNReal.ofReal_pow Chain18Compact.replacementBase_nonneg] at h
  have ht : ENNReal.ofReal (((2 : ℝ)^129)⁻¹) =
      1 / (2 : ℝ≥0∞)^129 := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [ht] at h
  rwa [honestBase_eq_ofReal]

theorem sign_failure_fresh (x : scheme.graph.Assignment) (m : Message)
    (c : Cache) (hf : ∀ η : BitVec 86, c ⟨msgBits + 86, m ++ η⟩ = none) :
    E (run (scheme.sign x m) c) (fun p => if p.1.isNone then 1 else 0) ≤
      1 / (2 : ℝ≥0∞)^129 := by
  rw [WeightedScheme.Scheme.sign, run_map, E_map]
  simp only [Option.isNone_map]
  have h := WeightedSampling.Availability.loop_failure 86 scheme.decode scheme.tier
    m signBudget honestMiss (fun a => (uniform_miss a).le)
    signBudget ∅ c (by simp) (fun η _ => hf η)
  have he :
      (honestMiss + (signBudget : ℝ≥0∞) / (2 : ℝ≥0∞)^86)^signBudget ≤
        1 / (2 : ℝ≥0∞)^129 := by
    simpa only [signBudget, Chain18Compact.L, Nat.cast_pow, Nat.cast_ofNat] using
      honest_replacement_envelope
  exact h.trans he

theorem graph_hashInputsAvoid :
    WeightedFreshness.HashInputsAvoid graph (msgBits + 86) := by
  intro v
  obtain ⟨n, rfl⟩ := Name.nameEquiv.surjective v
  erw [graph_kind_fin]
  cases n <;> simp [kindOf, graph_len_fin, Name.len, msgBits]

theorem keygen_fresh
    (p : (PublicKey × scheme.graph.Assignment) × Cache)
    (hp : p ∈ support (run scheme.keygen ∅)) (q : Query)
    (hq : q.1 = msgBits + 86) : p.2 q = none := by
  have h : WeightedFreshness.PreservesLength (msgBits + 86) scheme.keygen :=
    WeightedFreshness.PreservesLength.bind
      (WeightedFreshness.graph_keygen_preservesLength graph graph_hashInputsAvoid)
      (fun _ => WeightedFreshness.PreservesLength.of_pure _)
  simpa using h ∅ p hp q hq

theorem typed_signingFailureHalf :
    typed.SigningFailureAtMost (1 / (2 : ℝ≥0∞)^129) := by
  intro message
  change probTrue (do
    let kg ← scheme.keygen
    let s ← scheme.sign kg.2 (message kg.1)
    pure s.isNone) ≤ _
  rw [WeightedFreshness.probTrue_eq_E_run, run_bind, E_bind]
  simp only [run_bind, E_bind, run_pure, E_pure]
  calc
    _ ≤ E (run scheme.keygen ∅) (fun _ => (1 / (2 : ℝ≥0∞)^129)) := by
      refine expectedValue_mono_of_support fun p hp => ?_
      apply sign_failure_fresh p.1.2 (message p.1.1) p.2
      intro η
      exact keygen_fresh p hp ⟨msgBits + 86, message p.1.1 ++ η⟩ rfl
    _ ≤ _ := E_const_le _ _

theorem typed_signingFailure :
    typed.SigningFailureAtMost (1 / (2 : ℝ≥0∞)^128) := by
  intro message
  exact (typed_signingFailureHalf message).trans (by
    rw [one_div, one_div]
    apply ENNReal.inv_le_inv.mpr
    norm_num)

theorem typed_admissible :
    typed.Admissible (1 / (2 : ℝ≥0∞)^128) where
  failure_lt_one := by norm_num
  correct := typed_correct
  verifyDeterministic := typed_verifyDeterministic
  signingFailure := typed_signingFailure
  signatureSize := typed_signatureSize
  rejectsOversized := typed_rejectsOversized
  keygenCost := typed_keygenCost
  signCost := typed_signCost

theorem wire_admissible : wireScheme.Admissible :=
  WireAdapter.admissible typed decodeWire decodeWire_encode wire_canonical typed_admissible
    typed_cost (by norm_num [verifyBudget])

end OptimalOTS.WeightedConstruction.LongChain91
