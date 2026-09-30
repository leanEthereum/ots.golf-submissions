import Submissions.UpperRiscvHint.WeightedPairs

/-! The raw nibble-pair alphabet, with the coarse nibble complemented before
 the weighted recoding. Counting is transported through that involution. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace OptimalOTS.PairCode

abbrev Pair := WeightedPairs.Pair

def complement (p : Pair) : Pair := (p.1, Fin.rev p.2)

@[simp] theorem complement_complement (p : Pair) : complement (complement p) = p := by
  simp [complement]

theorem complement_injective : Function.Injective complement := by
  intro p q h
  simpa only [complement_complement] using congrArg complement h

def kind (q : ℕ) : Bool := WeightedPairs.capPos q
def recode (q : ℕ) (p : Pair) : ℕ × ℕ := WeightedPairs.recode (kind q) (complement p)
def weight (q : ℕ) (p : Pair) : ℕ := WeightedPairs.weight (kind q) (complement p)
def helper (q : ℕ) (p : Pair) : ℕ := WeightedPairs.helper (kind q) (complement p)
def skip (q : ℕ) (p : Pair) : ℕ := WeightedPairs.skip (kind q) (complement p)
def skipSave (q : ℕ) (p : Pair) : ℕ := WeightedPairs.skipSave (kind q) (complement p)
def cap (_q : ℕ) : ℕ := 24

theorem recode_injective (q : ℕ) : Function.Injective (recode q) :=
  (WeightedPairs.recode_injective _).comp complement_injective

theorem recode_bounds (q : ℕ) (p : Pair) : (recode q p).1 ≤ 22 ∧ (recode q p).2 ≤ 20 :=
  WeightedPairs.recode_bounds _ (complement p)

theorem weight_le (q : ℕ) (p : Pair) : weight q p ≤ 24 := WeightedPairs.weight_le _ (complement p)

theorem weight_recode (q : ℕ) (p : Pair) : weight q p =
    WeightedPairs.pairWeight (kind q) (recode q p).1 (recode q p).2 := rfl

theorem decoder_cost_exact (q : ℕ) (p : Pair) :
    weight q p + skipSave q p =
      (recode q p).1 + (recode q p).2 + 2 * helper q p + (if kind q then 1 else 0) :=
  WeightedPairs.decoder_cost_exact _ (complement p)

theorem skipSave_le (q : ℕ) (p : Pair) :
    skipSave q p ≤ (if kind q then 1 else 0) + helper q p :=
  WeightedPairs.skipSave_le _ (complement p)

def tuples (n s : ℕ) : Finset (Fin n → Pair) :=
  Finset.univ.filter fun c => ∑ q, weight q.val (c q) = s

abbrev count := WeightedPairs.count

theorem tuples_card (n s : ℕ) : (tuples n s).card = count n s := by
  change (tuples n s).card = WeightedPairs.count n s
  rw [← WeightedPairs.tuples_card]
  refine Finset.card_bij' (fun c _ q => complement (c q))
    (fun c _ q => complement (c q)) ?_ ?_ ?_ ?_
  · intro c hc
    have h : (∑ q, weight q.val (c q)) = s := (Finset.mem_filter.mp hc).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  · intro c hc
    have h : (∑ q, WeightedPairs.weight (WeightedPairs.capPos q.val) (c q)) = s :=
      (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [weight, kind, complement_complement] using h
  · intro c _; funext q; exact complement_complement (c q)
  · intro c _; funext q; exact complement_complement (c q)

theorem window_exact : ∑ s ∈ Finset.range 19, count 16 (129+s) =
    29392495299674139897463880312407816 := WeightedPairs.window_count

theorem window_lower : 89*2^108 ≤ ∑ s ∈ Finset.range 19, count 16 (129+s) := by
  rw [window_exact]
  norm_num

theorem window_le_half : (∑ s ∈ Finset.range 19, count 16 (129+s)) ≤ 2^127 := by
  rw [window_exact]
  norm_num

end OptimalOTS.PairCode
