import Submissions.UpperRiscvHint.Cuts
import Submissions.UpperRiscvHint.Valid

/-!
# The digit layout

Reveal one node from each of the 33 chains: chain `k` is revealed at position `31 - d_k`, where
`d_0` is the free count `target - S` and `d_{k+1}` is digit `k` of the accepted index, so that
the verifier makes `d_k + 1` hash steps on a normal chain and `d_k` on a cap (digit 0 reveals the
cap's top). The digits and the free count sum to `target` and the caps are fixed, so every
disclosure set is a cut of the same cost, and distinct indices give distinct cuts.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.Forest

open OptimalOTS.Dag

/-- On an accepted index the free count completes the digit sum to `target`. -/
theorem freeDigit_add {i : ℕ} (hi : Accepted i) : freeDigit i + digitSum i = target := by
  obtain ⟨⟨lo, hi⟩, _⟩ := hi
  unfold freeDigit
  unfold target at hi ⊢
  omega

theorem digit_lt_32 (i : ℕ) (k : ℕ) : digit i k < 32 := by
  have h := digit_lt i k
  have : 2 ^ wid k ≤ 32 := by unfold wid; split_ifs <;> norm_num
  omega

/-- The digit of chain `k`: the free count for chain 0, index digit `k - 1` otherwise. -/
def chainDigit (i k : ℕ) : ℕ := if k = 0 then min (freeDigit i) 31 else digit i (k - 1)

theorem chainDigit_lt_32 (i k : ℕ) : chainDigit i k < 32 := by
  unfold chainDigit
  split_ifs
  · omega
  · exact digit_lt_32 i _

theorem chainDigit_succ (i k : ℕ) : chainDigit i (k + 1) = digit i k := by
  simp [chainDigit]

/-- The chain digits of an index. -/
def fixedDigits (i : RawIdx) (k : Chain) : Fin 32 := ⟨chainDigit i.val k.val, chainDigit_lt_32 _ _⟩

theorem fixedDigits_sum (i : Idx) : ∑ k, (fixedDigits i k).val = target := by
  have hacc := mem_validSet_accepted i.2
  rw [Fin.sum_univ_succ]
  simp only [fixedDigits, Fin.val_succ, Fin.val_zero, Idx.toRaw_val, chainDigit_succ]
  have hlow : ∑ k : Fin 32, digit i.val k.val = digitSum i.val := by
    rw [digitSum, ← Fin.sum_univ_eq_sum_range]
  have hfree : chainDigit i.val 0 = freeDigit i.val := by
    have sum := freeDigit_add hacc
    have lo := hacc.1.1
    unfold chainDigit
    rw [if_pos rfl]
    unfold target at sum
    omega
  rw [hlow, hfree]
  exact freeDigit_add hacc

theorem fixedDigits_injective : Function.Injective fixedDigits := by
  intro i j h
  apply Fin.ext
  have hi : i.val < 2 ^ pos 32 := by rw [← idxBits_eq]; exact i.isLt
  have hj : j.val < 2 ^ pos 32 := by rw [← idxBits_eq]; exact j.isLt
  rw [← ofDigits_digit i.val 32 hi, ← ofDigits_digit j.val 32 hj]
  unfold ofDigits
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have e := congrArg (fun d : Chain → Fin 32 => (d ⟨k + 1, by omega⟩).val) h
  simp only [fixedDigits, chainDigit_succ] at e
  rw [e]

/-- The revealed positions: chain `k` at `31 - d_k`. -/
def fixedPositions (i : RawIdx) (k : Chain) : Fin 32 := Fin.rev (fixedDigits i k)

theorem fixedPositions_val (i : RawIdx) (k : Chain) :
    (fixedPositions i k).val = 31 - chainDigit i.val k.val := by
  simp [fixedPositions, fixedDigits, Fin.val_rev]

theorem fixedPositions_sum (i : Idx) :
    ∑ k, (32 - firstEval k (fixedPositions i k)) = target + 20 := by
  have : ∑ k : Chain, (32 - firstEval k (fixedPositions i k)) =
      ∑ k : Chain, ((fixedDigits i k).val + if k.val < 13 then 0 else 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [firstEval, fixedPositions, Fin.val_rev]
    have := (fixedDigits i k).isLt
    split_ifs <;> omega
  rw [this, Finset.sum_add_distrib, fixedDigits_sum]
  congr 1

/-- The disclosure set of an index. -/
def fixedChoice (i : RawIdx) : Choice := fixedPositions i

attribute [local irreducible] fixedDigits

theorem fixedCut_injective : Function.Injective (fun i : Idx => cutOf (fixedChoice i)) := by
  intro i j h
  have hc := cutOf_injective h
  apply Idx.toRaw_injective
  apply fixedDigits_injective
  funext k
  have hp := congrFun hc k
  simp only [fixedChoice, fixedPositions] at hp
  exact Fin.rev_injective hp

theorem fixedCut_isCut (i : RawIdx) : IsCut (cutOf (fixedChoice i)) := isCut_cutOf _

/-- Every disclosure set costs `target + 20 + 14 = 179` compressions to reconstruct. -/
theorem fixedCut_cost (i : Idx) :
    ∑ n ∈ evaluatedSet (cutOf (fixedChoice i)), n.cost = 179 := by
  rw [cost_cutOf]
  change ∑ k, (32 - firstEval k (fixedPositions i k)) + 14 = 179
  rw [fixedPositions_sum]
  rfl

end OptimalOTS.Forest
