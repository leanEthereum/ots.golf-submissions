import Submissions.UpperRiscvHint.Cuts
import Submissions.UpperRiscvHint.Valid

/-!
# The digit layout

Reveal one node from each of the 33 chains: chain `k` is revealed at position `31 - d_k`, where
`d_0` is the free count `target - S` and `d_{k+1}` is digit `k` of the accepted index, so that
the verifier makes `d_k + 1` hash steps on a normal chain and `d_k` on a cap (digit 0 reveals the
cap's top). The pair weights and the free count sum to `target`. Pair weights strictly
increasing in each coordinate give incomparable cuts; actual hash costs may differ.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.Forest

open OptimalOTS.Dag

/-- On an accepted index the free count completes the digit sum to `target`. -/
theorem freeDigit_add {i : ℕ} (hi : Accepted i) : freeDigit i + digitSum i = target := by
  obtain ⟨⟨lo, hi⟩, _⟩ := hi
  have hle := digitSum_le i
  unfold freeDigit
  unfold target at hi ⊢
  omega

theorem digit_lt_32 (i : ℕ) (k : ℕ) : digit i k < 32 := by
  have h := digit_lt i k
  have : 2 ^ wid k ≤ 32 := by unfold wid; split_ifs <;> norm_num
  omega

/-- The digit of chain `k`: the free count for chain 0, interpreted digit `k - 1` otherwise. -/
def chainDigit (i : ChainIndex) (k : ℕ) : ℕ := if k = 0 then i.free.val else stepDigit i.val (k - 1)

theorem chainDigit_lt_32 (i : ChainIndex) (k : ℕ) : chainDigit i k < 32 := by
  unfold chainDigit
  split_ifs
  · exact i.free.isLt
  · have := stepDigit_le i.val (k-1)
    omega

theorem chainDigit_succ (i : ChainIndex) (k : ℕ) : chainDigit i (k + 1) = stepDigit i.val k := by
  simp [chainDigit]

/-- The chain digits of an index. -/
def fixedDigits (i : ChainIndex) (k : Chain) : Fin 32 := ⟨chainDigit i k.val, chainDigit_lt_32 _ _⟩

theorem free_chainDigit (i : Idx) : chainDigit i 0 = freeDigit i.val := by
  have hacc := mem_validSet_accepted i.2
  have hsum := freeDigit_add hacc
  have hlo := hacc.1.1
  clear hacc
  rw [chainDigit, if_pos rfl, Idx.toChain_free]
  unfold target at hsum
  exact Nat.min_eq_left (by omega)

theorem chainDigit_pair (i : ChainIndex) (q : ℕ) :
    chainDigit i (2*q+1) = stepDigit i.val (2*q) ∧ chainDigit i (2*q+2) = stepDigit i.val (2*q+1) :=
  ⟨chainDigit_succ i (2*q), chainDigit_succ i (2*q+1)⟩

theorem fixedDigits_rank (i : Idx) :
    WeightedPairs.rank (fun k => (fixedDigits i k).val) = target := by
  rw [WeightedPairs.rank]
  simp only [fixedDigits, Fin.val_zero]
  rw [free_chainDigit]
  simp only [fun q : Fin 16 => (chainDigit_pair (i : ChainIndex) q.val).1,
    fun q : Fin 16 => (chainDigit_pair (i : ChainIndex) q.val).2, Idx.toChain_val]
  rw [← digitSum_eq_weights]
  exact freeDigit_add (mem_validSet_accepted i.property)

theorem fixedDigits_cost (i : Idx) :
    (∑ k, (fixedDigits i k).val) + 2*helperCount i.val + 6 = target + skipCount i.val := by
  rw [Fin.sum_univ_succ]
  simp only [fixedDigits, Fin.val_succ, Fin.val_zero, Idx.toChain_val, chainDigit_succ]
  rw [free_chainDigit]
  have hc := digitSum_cost i.val
  rw [← Fin.sum_univ_eq_sum_range] at hc
  have hf := freeDigit_add (mem_validSet_accepted i.property)
  omega

theorem fixedDigits_sum_le (i : Idx) : ∑ k, (fixedDigits i k).val ≤ target := by
  have := fixedDigits_cost i
  have := skipCount_le i.val
  omega

theorem fixedDigits_injective : Function.Injective fixedDigits := by
  intro i j h
  apply ChainIndex.ext
  · have hi : i.val < 2 ^ pos 32 := by rw [← idxBits_eq]; exact i.isLt
    have hj : j.val < 2 ^ pos 32 := by rw [← idxBits_eq]; exact j.isLt
    rw [← ofDigits_digit i.val 32 hi, ← ofDigits_digit j.val 32 hj]
    unfold ofDigits
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have e := congrArg (fun d : Chain → Fin 32 => (d ⟨k + 1, by omega⟩).val) h
    simp only [fixedDigits, chainDigit_succ] at e
    have hp : rawPair i.val (k/2) = rawPair j.val (k/2) := by
      apply PairCode.recode_injective (k/2)
      apply Prod.ext
      · have he := congrArg (fun d : Chain → Fin 32 =>
            (d ⟨2*(k/2)+1, by omega⟩).val) h
        simpa only [fixedDigits, chainDigit_succ, stepDigit_even] using he
      · have he := congrArg (fun d : Chain → Fin 32 =>
            (d ⟨(2*(k/2)+1)+1, by omega⟩).val) h
        simpa only [fixedDigits, chainDigit_succ, stepDigit_odd] using he
    have hd : digit i.val k = digit j.val k := by
      by_cases he : k%2=0
      · have heq : 2*(k/2)=k := by omega
        have e := congrArg (fun p : PairCode.Pair => p.1.val) hp
        simpa only [rawPair, heq] using e
      · have heq : 2*(k/2)+1=k := by omega
        have e := congrArg (fun p : PairCode.Pair => p.2.val) hp
        simpa only [rawPair, heq] using e
    rw [hd]
  · apply Fin.ext
    have e := congrArg (fun d : Chain → Fin 32 => (d 0).val) h
    simpa only [fixedDigits, chainDigit, Fin.val_zero, if_true] using e

/-- The revealed positions: chain `k` at `31 - d_k`. -/
def fixedPositions (i : ChainIndex) (k : Chain) : Fin 32 := Fin.rev (fixedDigits i k)

theorem fixedPositions_val (i : ChainIndex) (k : Chain) :
    (fixedPositions i k).val = 31 - chainDigit i k.val := by
  simp [fixedPositions, fixedDigits, Fin.val_rev]

theorem fixedPositions_sum (i : Idx) :
    ∑ k, (32 - firstEval k (fixedPositions i k)) ≤ target + 18 := by
  have : ∑ k : Chain, (32 - firstEval k (fixedPositions i k)) =
      ∑ k : Chain, ((fixedDigits i k).val + if k.val < 13 ∨ 31 ≤ k.val then 0 else 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [firstEval, fixedPositions, Fin.val_rev]
    have := (fixedDigits i k).isLt
    split_ifs <;> omega
  rw [this, Finset.sum_add_distrib]
  have hn : (∑ k : Chain, if k.val < 13 ∨ 31 ≤ k.val then 0 else 1) = 18 := by
    decide +kernel
  rw [hn]
  exact Nat.add_le_add_right (fixedDigits_sum_le i) 18

/-- The disclosure set of an index. -/
def fixedChoice (i : ChainIndex) : Choice := fixedPositions i

attribute [local irreducible] fixedDigits

theorem fixedCut_injective : Function.Injective (fun i : Idx => cutOf (fixedChoice i)) := by
  intro i j h
  have hc := cutOf_injective h
  apply Subtype.ext
  change (i : ChainIndex).val = (j : ChainIndex).val
  apply congrArg ChainIndex.val
  apply fixedDigits_injective
  funext k
  have hp := congrFun hc k
  simp only [fixedChoice, fixedPositions] at hp
  exact Fin.rev_injective hp

theorem fixedCut_isCut (i : ChainIndex) : IsCut (cutOf (fixedChoice i)) := isCut_cutOf _

/-- Preserve the original verifier budget; weighted decoding only decreases hash work. -/
theorem fixedCut_cost (i : Idx) :
    ∑ n ∈ evaluatedSet (cutOf (fixedChoice i)), n.cost ≤ 179 := by
  rw [cost_cutOf]
  change ∑ k, (32 - firstEval k (fixedPositions i k)) + 14 ≤ 179
  have h := fixedPositions_sum i
  unfold target at h
  omega

/-- Weighted rank provides the cross-cut witness without equal hash cost. -/
theorem fixedCut_witness (i j : Idx) (hne : i ≠ j) :
    ∃ v ∈ cutOf (fixedChoice i), Evaluated (cutOf (fixedChoice j)) v := by
  have hd : (fun k => (fixedDigits i k).val) ≠ (fun k => (fixedDigits j k).val) := by
    intro h
    apply hne
    apply Subtype.ext
    change (i : ChainIndex).val = (j : ChainIndex).val
    apply congrArg ChainIndex.val
    apply fixedDigits_injective
    funext k
    exact Fin.ext (congrFun h k)
  obtain ⟨k, hk⟩ := WeightedPairs.equal_rank_crossing
    ((fixedDigits_rank i).trans (fixedDigits_rank j).symm) hd
  have hfe : firstEval k (fixedChoice j k) < firstEval k (fixedChoice i k) := by
    have hi := (fixedDigits i k).isLt
    have hj := (fixedDigits j k).isLt
    unfold firstEval fixedChoice fixedPositions
    simp only [Fin.val_rev]
    split_ifs <;> omega
  refine ⟨chainNode k (fixedChoice i k), (mem_cutOf_iff _ _).mpr ⟨k, rfl⟩, ?_⟩
  unfold chainNode
  split_ifs with h
  · exact (evaluated_ci_iff _ _ _).mpr hfe
  · apply (evaluated_top_iff _ _).mpr
    have := firstEval_le k (fixedChoice i k)
    omega

end OptimalOTS.Forest
