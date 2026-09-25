import OptimalOTS.Dag

/-! Scheme-local signature parameters. A 128-bit nonce preserves the nonce/index
space equality used by the adaptive chosen-message security proof. -/

namespace OptimalOTS

open OracleSpec OracleComp
open OptimalOTS.Dag

def nonceBits : ℕ := 128
abbrev Nonce := BitVec nonceBits
abbrev Signature := Nonce × List Bool

def idxCost : ℕ := blockCost (pkBits + msgBits + nonceBits)
def trials : ℕ := signBudget / idxCost

/-- The same unrestricted two-stage attacker interface, with this scheme's signature type. -/
structure Adversary where
  State : Type
  choose : PublicKey → OracleComp Spec (Message × State)
  forge : State → Option Signature → OracleComp Spec (Message × Signature)

theorem index_cost_one : idxCost = 1 := by decide
theorem signing_trials : trials = 2 ^ 20 := by decide
theorem nonce_space_sufficient : trials < 2 ^ nonceBits := by decide

end OptimalOTS
