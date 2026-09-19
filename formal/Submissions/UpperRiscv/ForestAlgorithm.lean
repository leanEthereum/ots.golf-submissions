import Submissions.UpperRiscv.Resources
import Submissions.UpperRiscv.Main
import Submissions.UpperRiscv.Correctness
import Submissions.UpperRiscv.Availability
import Submissions.UpperRiscv.Deterministic

/-!
# The verified forest under the generic algorithm interface

The forest satisfies the generic challenge: perfect correctness, signing failure at most
`2⁻¹²⁸`, 127-bit strong security, and verification within 173 compressions on every path.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.RiscvUpperForest

open OptimalOTS.Dag


attribute [local irreducible] Forest.forestScheme
attribute [local irreducible] GScheme.sign GScheme.signLoop
attribute [local irreducible] TypedScheme.Secure TypedScheme.VerifyCostAtMost
  TypedScheme.KeygenCostAtMost TypedScheme.SignCostAtMost
  TypedScheme.SignatureSizeAtMost TypedScheme.RejectsOversized

def scheme : TypedScheme := Forest.forestScheme.toAlgorithm

theorem secure : scheme.Secure :=
  (AlgorithmAdapter.secure_iff Forest.forestScheme).2 Forest.forestScheme_secure

/-- This bound covers all public keys, messages and signatures, including rejecting inputs. -/
theorem cost : scheme.VerifyCostAtMost 173 := by
  apply AlgorithmAdapter.verifyCost Forest.forestScheme (v := 172) (by decide)
  intro i
  have h := Forest.forestScheme_verifyCost i
  change 1 + Forest.forestScheme.graph.reconstructCost (Forest.forestScheme.sets i) = 173 at h
  omega

theorem keygen_cost : scheme.KeygenCostAtMost keygenBudget :=
  AlgorithmAdapter.keygenCost Forest.forestScheme

theorem sign_cost : scheme.SignCostAtMost signBudget :=
  AlgorithmAdapter.signCost Forest.forestScheme (by decide)

theorem signature_size : scheme.SignatureSizeAtMost maxSignatureBits :=
  AlgorithmAdapter.signatureSize Forest.forestScheme

theorem rejects_oversized : scheme.RejectsOversized maxSignatureBits :=
  AlgorithmAdapter.rejectsOversized Forest.forestScheme

/-- Every honestly returned signature verifies under the same oracle. -/
theorem correct : scheme.Correct := GenericCorrectness.correct Forest.forestScheme

/-- Signing succeeds except with probability at most `2⁻¹²⁸` for every public-key-dependent message. -/
theorem signing_failure : scheme.SigningFailureAtMost (1 / 2 ^ 128) :=
  GenericAvailability.signingFailure

/-- All generic admission requirements, with the challenge's fixed failure allowance. -/
theorem admissible : scheme.Admissible (1 / 2 ^ 128) where
  failure_lt_one := by norm_num
  correct := correct
  verifyDeterministic := GScheme.verifyDeterministic Forest.forestScheme
  signingFailure := signing_failure
  signatureSize := signature_size
  rejectsOversized := rejects_oversized
  keygenCost := keygen_cost
  signCost := sign_cost

/-- A complete admissible, strongly secure, 173-compression construction. -/
theorem certificate :
    scheme.Admissible (1 / 2 ^ 128) ∧
    scheme.Secure ∧ scheme.VerifyCostAtMost 173 :=
  ⟨admissible, secure, cost⟩

/--
info: 'OptimalOTS.RiscvUpperForest.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certificate

end OptimalOTS.RiscvUpperForest
