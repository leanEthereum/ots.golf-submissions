import Submissions.UpperRiscv.Cuts
import Submissions.UpperRiscv.Valid

/-!
# The digit layout

Reveal one input from each of the 32 chains: chain `k` is revealed at position `31 - d_k`, where
`d_k` is digit `k` of the accepted index, so that the verifier makes `d_k + 1` hash steps on
chain `k`. The digits sum to `target`, so every disclosure set is a cut of the same cost, and
distinct indices give distinct cuts.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.Forest

open OptimalOTS.Dag

theorem digit_sum (i : Idx) : ∑ k ∈ Finset.range 32, digit i.val k = target :=
  mem_validSet_accepted i.2

theorem digit_lt_32 (i : ℕ) (k : ℕ) : digit i k < 32 := by
  have h := digit_lt i k
  have : 2 ^ wid k ≤ 32 := by unfold wid; split_ifs <;> norm_num
  omega

/-- The chain digits of an accepted index. -/
def fixedDigits (i : Idx) (k : Fin 32) : Fin 32 := ⟨digit i.val k, digit_lt_32 _ _⟩

theorem fixedDigits_sum (i : Idx) : ∑ k, (fixedDigits i k).val = target := by
  rw [← digit_sum i, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem fixedDigits_injective : Function.Injective fixedDigits := by
  intro i j h
  apply Subtype.ext
  have hi : i.val < 2 ^ pos 32 := by rw [← idxBits_eq]; exact Idx.isLt i
  have hj : j.val < 2 ^ pos 32 := by rw [← idxBits_eq]; exact Idx.isLt j
  rw [← ofDigits_digit i.val 32 hi, ← ofDigits_digit j.val 32 hj]
  unfold ofDigits
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have e := congrArg (fun d : Fin 32 → Fin 32 => (d ⟨k, hk'⟩).val) h
  simp only [fixedDigits] at e
  rw [e]

/-- The revealed positions: chain `k` at `31 - d_k`. -/
def fixedPositions (i : Idx) (k : Fin 32) : Fin 32 := Fin.rev (fixedDigits i k)

theorem fixedPositions_val (i : Idx) (k : Fin 32) :
    (fixedPositions i k).val = 31 - digit i.val k := by
  simp [fixedPositions, fixedDigits, Fin.val_rev]

theorem fixedPositions_sum (i : Idx) : ∑ k, (32 - (fixedPositions i k).val) = target + 32 := by
  have : ∑ k : Fin 32, (32 - (fixedPositions i k).val) = ∑ k : Fin 32, ((fixedDigits i k).val + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [fixedPositions, Fin.val_rev]
    have := (fixedDigits i k).isLt
    omega
  rw [this, Finset.sum_add_distrib, fixedDigits_sum]
  simp

/-- The disclosure set of an accepted index. -/
def fixedChoice (i : Idx) : Choice := fixedPositions i

attribute [local irreducible] fixedDigits

theorem fixedCut_injective : Function.Injective (fun i => cutOf (fixedChoice i)) := by
  intro i j h
  have hc := cutOf_injective h
  apply fixedDigits_injective
  funext k
  have hp := congrFun hc k
  simp only [fixedChoice, fixedPositions] at hp
  exact Fin.rev_injective hp

theorem fixedCut_isCut (i : Idx) : IsCut (cutOf (fixedChoice i)) := isCut_cutOf _

theorem fixedCut_card (i : Idx) : (cutOf (fixedChoice i)).card = 32 := card_cutOf _

/-- Every disclosure set costs `target + 32 + 15 = 204` compressions to reconstruct. -/
theorem fixedCut_cost (i : Idx) :
    ∑ n ∈ evaluatedSet (cutOf (fixedChoice i)), n.cost = 204 := by
  rw [cost_cutOf]
  change ∑ k, (32 - (fixedPositions i k).val) + 15 = 204
  rw [fixedPositions_sum]
  rfl

end OptimalOTS.Forest
