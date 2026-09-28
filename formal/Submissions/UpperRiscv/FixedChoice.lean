import Submissions.UpperRiscv.Cuts
import Submissions.UpperRiscv.Valid

/-!
# The digit layout

Reveal one node from each of the 33 chains. Chain `0` takes the free digit `146 - sum`, chain
`k ≥ 1` digit `k - 1` of the index. A chain with digit `d` is revealed at position `31 - d`, so
that the verifier makes `d + 1` hash steps on it; a cap chain at `32 - d`, so that the verifier
makes `d` steps and a zero digit reveals its top. The 33 digits sum to `target`, so every
disclosure set is a cut of the same cost, and distinct indices give distinct cuts.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.Forest

open OptimalOTS.Dag

/-- The digit of chain `k` for the free digit `v`: `v` for chain `0`, index digit `k - 1`
otherwise. -/
def digitV (i : RawIdx) (v : ℕ) (k : Fin 33) : ℕ :=
  if k.val = 0 then v else digit i.val (k.val - 1)

/-- The position of a zero digit: the last input of a chain, the top of a cap chain. -/
def topPos (k : Fin 33) : ℕ := if isCap k then 32 else 31

theorem topPos_le (k : Fin 33) : topPos k ≤ 32 := by
  unfold topPos; split_ifs <;> omega

/-- The revealed positions for the free digit `v`: chain `k` at `topPos k - d_k`. -/
def posV (i : RawIdx) (v : ℕ) (k : Fin 33) : Fin 33 :=
  ⟨topPos k - digitV i v k, by have := topPos_le k; omega⟩

/-- The digit of chain `k`: the free digit for chain `0`, index digit `k - 1` otherwise. -/
def fixedDigits (i : RawIdx) (k : Fin 33) : ℕ := digitV i (freeDigit i.val) k

/-- The revealed positions of an index. -/
def fixedPositions (i : RawIdx) (k : Fin 33) : Fin 33 := posV i (freeDigit i.val) k

theorem fixedPositions_val (i : RawIdx) (k : Fin 33) :
    (fixedPositions i k).val = topPos k - fixedDigits i k := rfl

theorem posV_val (i : RawIdx) (v : ℕ) (k : Fin 33) :
    (posV i v k).val = topPos k - digitV i v k := rfl

theorem digitSum_bounds (i : Idx) : freeLow ≤ digitSum i.val ∧ digitSum i.val ≤ target :=
  (mem_validSet_accepted i.2).1

theorem fixedDigits_lt (i : Idx) (k : Fin 33) : fixedDigits i k < 16 := by
  unfold fixedDigits digitV
  split_ifs
  · have := digitSum_bounds i
    unfold freeDigit
    simp only [freeLow, target] at this ⊢
    change 146 - digitSum i.val < 16
    omega
  · exact digit_lt_16 _ _

theorem sum_fin33_succ (f : ℕ → ℕ) : ∑ k : Fin 33, f k.val = f 0 + ∑ k ∈ Finset.range 32, f (k + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f k) 33, Finset.sum_range_succ']
  ring

/-- The 33 digits of an accepted index sum to `target`. -/
theorem fixedDigits_sum (i : Idx) : ∑ k, fixedDigits i k = target := by
  have h := sum_fin33_succ (fun k => if k = 0 then freeDigit i.val else digit i.val (k - 1))
  have e : ∑ k : Fin 33, fixedDigits i k =
      ∑ k : Fin 33, (fun k => if k = 0 then freeDigit i.val else digit i.val (k - 1)) k.val := by
    unfold fixedDigits digitV; rfl
  rw [e, h]
  simp only [if_pos, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
  change freeDigit i.val + digitSum i.val = target
  have := digitSum_bounds i
  unfold freeDigit
  omega

theorem topPos_sub_add (i : Idx) (k : Fin 33) :
    32 - (fixedPositions i k).val = fixedDigits i k + (if isCap k then 0 else 1) := by
  rw [fixedPositions_val]
  have := fixedDigits_lt i k
  unfold topPos
  split_ifs <;> omega

theorem card_nonCap : ∑ k : Fin 33, (if isCap k then 0 else 1) = 32 := by decide +kernel

theorem fixedPositions_sum (i : Idx) : ∑ k, (32 - (fixedPositions i k).val) = target + 32 := by
  simp only [topPos_sub_add, Finset.sum_add_distrib, fixedDigits_sum, card_nonCap]

theorem fixedDigits_injective : Function.Injective (fun (i : Idx) => fixedDigits i) := by
  intro i j h
  apply Subtype.ext
  have hi : i.val < 2 ^ pos 32 := by rw [← idxBits_eq]; exact i.isLt
  have hj : j.val < 2 ^ pos 32 := by rw [← idxBits_eq]; exact j.isLt
  rw [← ofDigits_digit i.val 32 hi, ← ofDigits_digit j.val 32 hj]
  unfold ofDigits ofDigitsW
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have e := congrFun h ⟨k + 1, by omega⟩
  simp only [fixedDigits, digitV, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
    Nat.add_sub_cancel] at e
  change digit i.val k = digit j.val k at e
  rw [e]

/-- The disclosure set of an accepted index. -/
def fixedChoice (i : RawIdx) : Choice := fixedPositions i

attribute [local irreducible] fixedDigits digitV

theorem fixedCut_injective : Function.Injective (fun i : Idx => cutOf (fixedChoice i)) := by
  intro i j h
  have hc := cutOf_injective h
  apply fixedDigits_injective
  funext k
  show fixedDigits i k = fixedDigits j k
  have hp := congrArg Fin.val (congrFun hc k)
  simp only [fixedChoice, fixedPositions_val] at hp
  have := fixedDigits_lt i k
  have := fixedDigits_lt j k
  have := topPos_le k
  have : 31 ≤ topPos k := by unfold topPos; split_ifs <;> omega
  omega

theorem fixedChoice_capChoice (i : RawIdx) : CapChoice (fixedChoice i) := by
  intro k hk
  simp only [fixedChoice, fixedPositions_val] at hk
  by_contra h
  unfold topPos at hk
  rw [if_neg h] at hk
  omega

theorem fixedCut_isCut (i : RawIdx) : IsCut (cutOf (fixedChoice i)) := isCut_cutOf _

theorem fixedCut_card (i : RawIdx) : (cutOf (fixedChoice i)).card = 33 := card_cutOf _

/-- Every disclosure set costs `target + 32 + 13 = 191` compressions to reconstruct. -/
theorem fixedCut_cost (i : Idx) :
    ∑ n ∈ evaluatedSet (cutOf (fixedChoice i)), n.cost = 191 := by
  rw [cost_cutOf]
  change ∑ k, (32 - (fixedPositions i k).val) + 13 = 191
  rw [fixedPositions_sum]
  rfl

end OptimalOTS.Forest
