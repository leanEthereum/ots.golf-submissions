import Submissions.UpperCompressions.ShallowScheme
import Submissions.UpperCompressions.IndexedResources
import Submissions.UpperCompressions.IndexedCorrectness
import Submissions.UpperCompressions.IndexedFreshness

/-!
# Admissibility and 102-compression cost of the shallow typed scheme

The candidate is perfectly correct, deterministic in verification, within every
honest-party size/cost budget, and meets the signing-failure target even for
public-key-dependent messages. Verification costs at most 102 on every input.
This module does not prove strong unforgeability or export a challenge solution.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.ShallowForest

/-- The shallow graph hashes only 144-, 400-, and 2320-bit inputs. -/
theorem graph_hashInputsAvoid :
    IndexedFreshness.HashInputsAvoid graph (msgBits + Dag.nonceBits) := by
  intro v
  obtain ⟨n, rfl⟩ := nameEquiv.surjective v
  erw [graph_kind_fin]
  cases n <;> simp [kindOf, graph_len_fin, Name.len, msgBits, Dag.nonceBits]

end OptimalOTS.ShallowForest

namespace OptimalOTS.ShallowUpperForest

attribute [local irreducible] ShallowForest.forestScheme
attribute [local irreducible] IndexedDag.Scheme.sign IndexedDag.Scheme.signLoop

def scheme : TypedScheme := ShallowForest.forestScheme.toAlgorithm

/-- Every public key, message and typed signature, including rejecting inputs. -/
theorem cost : scheme.VerifyCostAtMost 102 :=
  IndexedDag.AlgorithmAdapter.verifyCostBound ShallowForest.forestScheme
    (v := 101) (fun i => (ShallowForest.forestScheme_reconstructCost i).le)

theorem keygen_cost : scheme.KeygenCostAtMost keygenBudget :=
  IndexedDag.AlgorithmAdapter.keygenCost ShallowForest.forestScheme

theorem keygen_cost_exact : scheme.KeygenCostAtMost 995 := by
  have h := IndexedDag.AlgorithmAdapter.keygenCost_exact ShallowForest.forestScheme
  rwa [ShallowForest.forestScheme_keygenCost] at h

theorem sign_cost : scheme.SignCostAtMost signBudget :=
  IndexedDag.AlgorithmAdapter.signCostAtBudget ShallowForest.forestScheme

theorem signature_size : scheme.SignatureSizeAtMost maxSignatureBits :=
  IndexedDag.AlgorithmAdapter.signatureSize ShallowForest.forestScheme

theorem rejects_oversized : scheme.RejectsOversized maxSignatureBits :=
  IndexedDag.AlgorithmAdapter.rejectsOversized ShallowForest.forestScheme

theorem verify_deterministic : scheme.VerifyDeterministic :=
  IndexedDag.AlgorithmAdapter.verifyDeterministic ShallowForest.forestScheme

theorem correct : scheme.Correct :=
  IndexedAnalysis.Correctness.correct ShallowForest.forestScheme

theorem signing_failure : scheme.SigningFailureAtMost (1 / 2 ^ 128) :=
  IndexedFreshness.signingFailure ShallowForest.forestScheme
    (by simpa only [ShallowForest.forestScheme] using ShallowForest.graph_hashInputsAvoid)

/-- Every typed admissibility requirement; security remains a separate theorem. -/
theorem admissible : scheme.Admissible (1 / 2 ^ 128) where
  failure_lt_one := by norm_num
  correct := correct
  verifyDeterministic := verify_deterministic
  signingFailure := signing_failure
  signatureSize := signature_size
  rejectsOversized := rejects_oversized
  keygenCost := keygen_cost
  signCost := sign_cost

end OptimalOTS.ShallowUpperForest
