import OptimalOTS.WholeWords
import Submissions.LowerGenerality1.WholeWordOrigins
import Submissions.LowerGenerality1.AveragedAssembly

/-!
# Verification lower bound for whole-word DAGs

A 5376-bit payload contains at most 42 whole 128-bit words and therefore represents at most
42 hash origins. If every verification cost were at most 89, its pattern would have at most
87 non-root hashes. There are at most choose(129,42) distinct patterns. The averaged
signature-conversion attack succeeds with probability at least 9801/280000, exceeding its
complete experiment budget divided by 2^127. Its forgery uses a different message.
-/

namespace OptimalOTS

open OptimalOTS.Dag


/-- Whole-word operations force a verification costing at least 90. -/
theorem wholeWordVerificationLowerBound_paper :
    LowerBoundGenerality1 90 := by
  intro S hwords hS
  have hdis := S.disclosureBound42_of_wholeWords hwords
  by_contra hn
  push Not at hn
  have hcost : ∀ i, S.verifyCost i ≤ 89 := fun i => Nat.lt_succ_iff.mp (hn i)
  have hrecon : ∀ i, S.graph.reconstructCost (S.sets i) ≤ 88 := by
    intro i
    have h := hcost i
    change 1 + S.graph.reconstructCost (S.sets i) ≤ 89 at h
    omega
  have hb := PatternAttack.cost_experiment S (2 ^ 122) 88 (by decide) hrecon
  have hsec := hS.weaklySecure _ _ hb
  have hsuccess := AveragedAssembly.success_ge_count S
    (S.card_hashPattern_image_le_disclosure hdis hcost)
  exact (not_lt_of_ge hsuccess) (hsec.trans AveragedAssembly.budget_lt)

/-- The exported restricted lower-track certificate. -/
theorem Challenge.LowerGenerality1.candidate :
    LowerBoundGenerality1 90 :=
  wholeWordVerificationLowerBound_paper

end OptimalOTS

/--
info: 'OptimalOTS.Challenge.LowerGenerality1.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.LowerGenerality1.candidate
