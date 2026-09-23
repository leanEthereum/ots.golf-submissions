import Submissions.UpperRiscv.MixedChainFrame
import Submissions.UpperRiscv.MixedCode

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open Riscv2Program

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

def earlyHash (k : ℕ) : ℕ := if expands k then 1 else 0

theorem earlyHash_cases (k : ℕ) : earlyHash k = 0 ∨ earlyHash k = 1 := by
  unfold earlyHash; split_ifs <;> simp

theorem steps_eq_digit (index : Idx) (k : Fin 32) :
    32-RiscvUpperForest.ForestVerifier.pos index k = digit index.val k + 1 := by
  have h := digit_lt_32' index.val k
  rw [RiscvUpperForest.ForestVerifier.pos, fixedPositions_val]
  omega

theorem fineDigit_lt (index : Idx) (q : ℕ) (hq : q < 16) :
    digit index.val (2*q) < 2^fineWidth q := by
  have h := digit_lt index.val (2*q)
  have he : wid (2*q) = fineWidth q := by
    simp [wid, fineWidth, show 2*q < 32 by omega]
  rw [he] at h; exact h

theorem coarseDigit_lt_copies (index : Idx) (q : ℕ) (hq : q < 16) :
    coarseDigit index q < copies q := by
  have h := digit_lt index.val (2*q+1)
  have he : 2^wid (2*q+1) = copies q := by
    simp [wid, copies, show 2*q+1 < 32 by omega]
  rw [he] at h; exact h

/-- The packed subtraction selects the coarse copy and the fine table entry. -/
theorem pair_landing (index : Idx) (q : ℕ) (hq : q < 16) :
    landing0 q-dispatch index q = copyStart q (coarseDigit index q) +
      4*(2^fineWidth q-1-digit index.val (2*q)) := by
  have hc := coarseDigit_lt_copies index q hq
  have hf := fineDigit_lt index q hq
  have e : copyStart q 0 = copyStart q (coarseDigit index q)+512*coarseDigit index q := by
    unfold copyStart
    omega
  unfold landing0 dispatch
  rw [e]
  omega

/-- Hash work is fixed by the accepted digit sum. -/
theorem all_chain_hashes (index : Idx) :
    ∑ k : Fin 32, (32-RiscvUpperForest.ForestVerifier.pos index k) = 189 := by
  exact fixedPositions_sum index

/-- Chain work plus all pointer updates, dispatches, redirects, and the two length changes. -/
def chainsCost (index : Idx) : ℕ :=
  (∑ k : Fin 32, (32-RiscvUpperForest.ForestVerifier.pos index k)) +
    2*32 + 2*16 + (∑ k : Fin 32, earlyHash k) + 2

theorem chainsCost_eq (index : Idx) : chainsCost index = 299 := by
  have he : ∑ k : Fin 32, earlyHash k = 12 := by decide +kernel
  rw [chainsCost, all_chain_hashes, he]

theorem totalCost (index : Idx) : 40+chainsCost index+21 = 360 := by
  rw [chainsCost_eq]

end OptimalOTS.RiscvMixedProgram
