import Submissions.UpperRiscv.MixedChainFrame
import Submissions.UpperRiscv.MixedCode

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

def earlyHash (k : ℕ) : ℕ := if expands k then 1 else 0

theorem earlyHash_cases (k : ℕ) : earlyHash k = 0 ∨ earlyHash k = 1 := by
  unfold earlyHash; split_ifs <;> simp

/-- Hash steps of chain `k`: its digit, plus one unless it is a cap. -/
theorem steps_eq_digit (index : RawIdx) (v : ℕ) (k : Fin 33) (hv : v < 16) :
    32 - RiscvUpperForest.ForestVerifier.pos index v k =
      digitV index v k + (if isCap k then 0 else 1) := by
  have hd : digitV index v k < 16 := by
    unfold digitV; split_ifs
    · exact hv
    · exact digit_lt_16 _ _
  show 32 - (posV index v k).val = _
  rw [posV_val]
  unfold topPos
  split_ifs <;> omega

theorem fineDigit_lt (index : RawIdx) (q : ℕ) : digit index.val (2*q) < 16 := digit_lt_16 _ _

/-- The packed subtraction selects the coarse copy and the fine table entry. -/
theorem pair_landing (index : RawIdx) (q : ℕ) :
    landing0 q-dispatch index q = copyStart q (coarseDigit index q) +
      4*(15-digit index.val (2*q)) := by
  have hc := coarseDigit_lt index q
  have hf := fineDigit_lt index q
  have e : copyStart q 0 = copyStart q (coarseDigit index q)+1024*coarseDigit index q := by
    unfold copyStart bodyAt
    omega
  unfold landing0 dispatch
  rw [e]
  omega

end OptimalOTS.RiscvMixedProgram
