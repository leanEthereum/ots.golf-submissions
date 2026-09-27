import Submissions.UpperRiscvHint.MixedChainFrame
import Submissions.UpperRiscvHint.MixedCode

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

/-- The hashes of chain `k`: its digit for the free chain and a cap, its digit plus one for a
normal chain. -/
def remaining (index : RawIdx) (k : Chain) : ℕ := 32-firstAt index k

theorem steps_eq_digit (index : RawIdx) (k : Chain) :
    remaining index k = chainDigit index.val k + 1 - if k.val < 13 then 1 else 0 := by
  have h := chainDigit_lt_32 index.val k
  unfold remaining firstAt firstEval
  rw [fixedPositions_val]
  split_ifs <;> omega

theorem lead_pair (q : ℕ) (j : ℕ) (hj : j < 2) :
    (if 2*q+1+j < 13 then 1 else 0) = lead q := by
  unfold lead; split_ifs <;> omega

theorem fineDigit_lt (index : RawIdx) (q : ℕ) (hq : q < 16) :
    digit index.val (2*q) < 2^fineWidth q := by
  have h := digit_lt index.val (2*q)
  have he : wid (2*q) = fineWidth q := by
    simp [wid, fineWidth, show 2*q < 32 by omega]
  rw [he] at h; exact h

theorem coarseDigit_lt_copies (index : RawIdx) (q : ℕ) (hq : q < 16) :
    coarseDigit index q < copies q := by
  have h := digit_lt index.val (2*q+1)
  have he : 2^wid (2*q+1) = copies q := by
    simp [wid, copies, show 2*q+1 < 32 by omega]
  rw [he] at h; exact h

/-- The packed subtraction selects the coarse copy and the fine table entry, one row later for a
cap pair. -/
theorem pair_landing (index : RawIdx) (q : ℕ) (hq : q < 16) :
    landing0 q+4*lead q-dispatch index q = copyStart q (coarseDigit index q) +
      4*(2^fineWidth q-1-digit index.val (2*q)+lead q) := by
  have hc := coarseDigit_lt_copies index q hq
  have hf := fineDigit_lt index q hq
  have e : copyStart q 0 = copyStart q (coarseDigit index q)+1024*coarseDigit index q := by
    unfold copyStart
    omega
  unfold landing0 dispatch
  rw [e]
  omega

end OptimalOTS.RiscvMixedProgram
