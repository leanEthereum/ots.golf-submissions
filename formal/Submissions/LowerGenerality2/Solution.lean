import OptimalOTS.Dag
import Submissions.LowerGenerality2.PatternAssembly

/-!
# The bare single-oracle verification lower bound

A scheme whose every verification costs at most 17 has too few distinct sets of recomputed
hash nodes. The pattern attack converts an observed disclosure to another index with the same
set, and forges on a different message. Its success is at least 9/200, while its total query
cost divided by 2^127 is smaller. No separation or tagging hypothesis is imposed on the scheme.
-/

namespace OptimalOTS

open OptimalOTS.Dag


/-- Every secure scheme in the bare model has a verification costing at least 18. -/
theorem verificationLowerBound_paper : LowerBoundGenerality2 18 := by
  intro S hS
  by_contra hn
  push Not at hn
  have hcost : ∀ i, S.verifyCost i ≤ 17 := fun i => Nat.lt_succ_iff.mp (hn i)
  have hrecon : ∀ i, S.graph.reconstructCost (S.sets i) ≤ 16 := by
    intro i
    have h := hcost i
    change 1 + S.graph.reconstructCost (S.sets i) ≤ 17 at h
    omega
  have hb := PatternAttack.cost_experiment S (2 ^ 122) 16 (by decide) hrecon
  have hsec := hS.weaklySecure _ _ hb
  have hsuccess := PatternAttack.success_ge S hcost
  exact (not_lt_of_ge hsuccess) (hsec.trans PatternAttack.budget_lt)

/-- The exported lower-track certificate, with exactly the rendered challenge statement. -/
theorem Challenge.LowerGenerality2.candidate : LowerBoundGenerality2 18 :=
  verificationLowerBound_paper

end OptimalOTS

/--
info: 'OptimalOTS.Challenge.LowerGenerality2.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.LowerGenerality2.candidate
