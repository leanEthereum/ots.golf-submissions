import Submissions.UpperRiscv.Cuts
import Submissions.UpperRiscv.Valid

/-!
# The nibble layout

Reveal one value from each of the 32 chains: chain `k` is revealed at position `15 - d_k`, where
`d_k` is nibble `k` of the accepted index. The chain steps sum to `target`, so every disclosure
set is a cut of the same cost, and distinct indices give distinct cuts.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.Forest

open OptimalOTS.Dag

theorem nibble_sum (i : Idx) : ∑ k ∈ Finset.range 32, nibble i.val k = target :=
  mem_validSet_accepted i.2

/-- The chain digits of an accepted index: its 32 nibbles. -/
def fixedDigits (i : Idx) (k : Fin 32) : Fin 16 := ⟨nibble i.val k, nibble_lt _ _⟩

theorem fixedDigits_sum (i : Idx) : ∑ k, (fixedDigits i k).val = target := by
  rw [← nibble_sum i, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem fixedDigits_injective : Function.Injective fixedDigits := by
  intro i j h
  apply Subtype.ext
  have hi : i.val < 16 ^ 32 := by rw [← idxBits_eq]; exact Idx.isLt i
  have hj : j.val < 16 ^ 32 := by rw [← idxBits_eq]; exact Idx.isLt j
  rw [← ofNibbles_nibble i.val 32 hi, ← ofNibbles_nibble j.val 32 hj]
  unfold ofNibbles
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have e := congrArg (fun d : Fin 32 → Fin 16 => (d ⟨k, hk'⟩).val) h
  simp only [fixedDigits] at e
  rw [e]

/-- The revealed positions: chain `k` at `15 - d_k`. -/
def fixedPositions (i : Idx) (k : Fin 32) : Fin 16 := Fin.rev (fixedDigits i k)

theorem fixedPositions_val (i : Idx) (k : Fin 32) :
    (fixedPositions i k).val = 15 - nibble i.val k := by
  simp [fixedPositions, fixedDigits, Fin.val_rev]

theorem fixedPositions_sum (i : Idx) : ∑ k, (15 - (fixedPositions i k).val) = target := by
  rw [← fixedDigits_sum i]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [fixedPositions, Fin.val_rev]
  have := (fixedDigits i k).isLt
  omega

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

/-- Every disclosure set costs `target + 12 = 172` compressions to reconstruct. -/
theorem fixedCut_cost (i : Idx) :
    ∑ n ∈ evaluatedSet (cutOf (fixedChoice i)), n.cost = 172 := by
  rw [cost_cutOf]
  change ∑ k, (15 - (fixedPositions i k).val) + 12 = 172
  rw [fixedPositions_sum]
  rfl

end OptimalOTS.Forest
