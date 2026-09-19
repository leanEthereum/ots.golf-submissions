import Submissions.LowerGenerality1.PatternSearch

/-! Search probabilities retain the size of every reconstruction-pattern class. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.AveragedSearch

open OptimalOTS.Dag


/-- A lower bound on hitting one of `k` indices in `2^122` fresh 128-bit index trials. -/
def hitRate (k : ℕ) : ℝ≥0∞ := (k : ℝ≥0∞) / (64 + k)

theorem paper_success_ge (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ 128)
    (m : Message) (c : Cache)
    (hc : BareLower.FreshMessage c m) :
    hitRate G.card ≤
      E (run (PatternSearch.search G m (2 ^ 122) 0) c)
        (fun p => if p.1.isSome then 1 else 0) := by
  rw [PatternSearch.success_eq (by decide) G hG m (2 ^ 122) 0 c
    (by norm_num [nonceBits, idxBits, numCuts, trials, idxCost, blockCost, signBudget, msgBits, blockBits]) (PatternSearch.freshRange_of_freshMessage hc _ _)]
  change hitRate G.card ≤ 1 - (1 - (G.card : ℝ≥0∞) / 2 ^ 128) ^ (2 ^ 122)
  have hcard : G.card ≤ 2 ^ 128 := by
    calc G.card ≤ (Finset.range (2 ^ 128)).card :=
        Finset.card_le_card (fun j hj => Finset.mem_range.mpr (hG j hj))
      _ = _ := Finset.card_range _
  have hp0 : (0 : ℝ) ≤ (G.card : ℝ) / 2 ^ 128 := by positivity
  have hp1 : (G.card : ℝ) / 2 ^ 128 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hcard
  have hbase : (0 : ℝ) ≤ 1 - (G.card : ℝ) / 2 ^ 128 := sub_nonneg.mpr hp1
  have hb := FreshSign.one_sub_pow_le_reciprocal hp0 hp1 (2 ^ 122)
  have he : (1 : ℝ) - 1 / (1 + ((2 ^ 122 : ℕ) : ℝ) * (G.card : ℝ) / 2 ^ 128) =
      (G.card : ℝ) / (64 + G.card) := by
    have hk : (0 : ℝ) < 64 + G.card := by positivity
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
    ring
  have hr : (G.card : ℝ) / (64 + G.card) ≤
      1 - (1 - (G.card : ℝ) / 2 ^ 128) ^ (2 ^ 122) := by
    rw [← he]
    apply sub_le_sub_left
    simpa only [mul_div_assoc] using hb
  have h := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_sub _ (pow_nonneg hbase _), ENNReal.ofReal_pow hbase,
    ENNReal.ofReal_sub _ hp0] at h
  simpa only [hitRate, ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 64 + G.card),
    ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 64) (Nat.cast_nonneg G.card),
    ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, ENNReal.ofReal_one,
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 128),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)] using h

end OptimalOTS.AveragedSearch
