import Submissions.UpperCompressions.IndexedSampling
import Submissions.UpperCompressions.ShallowAvailability

/-!
# Availability of the submitted index sampler

Exact failure probability for the custom acceptance count, conditional on a fresh
index-query cache. This does not yet establish freshness after a concrete keygen.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.IndexedAnalysis.Availability

open OptimalOTS.Dag


attribute [local irreducible] Finset.univ Finset.filter

/-- Failure probability of one fresh index query. -/
def miss : ℝ≥0∞ := 524243 / 524288

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- Stated for any width, so that the kernel never enumerates the 256-bit strings. -/
private theorem card_filter_not_bitVec {n k : ℕ} (p : BitVec n → Prop) [DecidablePred p]
    (hv : (Finset.univ.filter p).card = k) :
    (Finset.univ.filter fun w => ¬ p w).card = 2 ^ n - k := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BitVec n))) (p := p)
  rw [hv, Finset.card_univ, Fintype.card_bitVec] at h
  omega

private theorem uniform_miss_count (hidx : idxBits ≤ hashBits)
    (hM : numCuts ≤ 2 ^ idxBits) (a : ℝ≥0∞) :
    E ($ᵗ BitVec hashBits) (fun w => if idxOf w < numCuts then 0 else a) =
      ((2 ^ hashBits - numCuts * 2 ^ (hashBits - idxBits) : ℕ) : ℝ≥0∞) *
        (((2 ^ hashBits : ℕ) : ℝ≥0∞)⁻¹ * a) := by
  have hv : (Finset.univ.filter fun w : BitVec hashBits => idxOf w < numCuts).card =
      numCuts * 2 ^ (hashBits - idxBits) := by
    have h := Analysis.card_idxOfOut_mem hidx (Finset.range numCuts)
      (fun n hn => (Finset.mem_range.mp hn).trans_le hM)
    convert h using 1 <;> simp [Analysis.idxOfOut, idxOf]
  have hn : (Finset.univ.filter fun w : BitVec hashBits => ¬ idxOf w < numCuts).card =
      2 ^ hashBits - numCuts * 2 ^ (hashBits - idxBits) :=
    card_filter_not_bitVec _ hv
  rw [E_uniform]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    nsmul_eq_mul, hn, Fintype.card_bitVec]

attribute [local semireducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

private theorem uniform_miss (a : ℝ≥0∞) :
    E ($ᵗ BitVec hashBits)
      (fun w => if idxOf w < numCuts then 0 else a) = miss * a := by
  rw [uniform_miss_count (by decide) (by norm_num [nonceBits, idxBits, numCuts, trials, idxCost, blockCost, signBudget, msgBits, blockBits])]
  rw [← mul_assoc]
  congr 1
  rw [← div_eq_mul_inv]
  apply (ENNReal.div_eq_div_iff (by norm_num [hashBits, blockBits, pkBits, msgBits, securityBits, maxSignatureBits, keygenBudget, signBudget]) (by finiteness)
    (by norm_num) (by finiteness)).2
  norm_num [miss, hashBits, blockBits, pkBits, msgBits, securityBits, maxSignatureBits, keygenBudget, signBudget, nonceBits, idxBits, numCuts, trials, idxCost, blockCost, signBudget, msgBits, blockBits]

/-- Exact failure probability while enough untried nonces remain and their queries are fresh. -/
theorem loop_failure (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (c : Cache),
      tried.card + k ≤ 2 ^ nonceBits →
      (∀ η ∉ tried, c (encQuery (m ++ η)) = none) →
      E (run (signIdxLoop m k tried) c)
        (fun p => if p.1.isNone then 1 else 0) = miss ^ k := by
  intro k
  induction k with
  | zero =>
    intro tried c _ _
    simp [signIdxLoop, run_pure]
  | succ k ih =>
    intro tried c hbudget hfresh
    have hc : 0 < (Finset.univ \ tried).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_bitVec]
      omega
    rw [signIdxLoop_succ m k tried hc, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, E_bind]
    have hbody : ∀ j,
        E (run (loopBody m k tried (nonceOf tried hc j)) c)
          (fun p => if p.1.isNone then 1 else 0) = miss ^ (k + 1) := by
      intro j
      let η := nonceOf tried hc j
      have hη : η ∉ tried := (Finset.mem_sdiff.mp (nonceOf_mem tried hc j)).2
      rw [loopBody, run_query_bind, oracleImpl_run_inr_none (hfresh η hη)]
      simp only [bind_assoc, pure_bind, E_bind]
      have hkont : ∀ w : BitVec hashBits,
          E (run (afterHash m k tried η w)
            (c.cacheQuery (encQuery (m ++ η)) w))
            (fun p => if p.1.isNone then 1 else 0) =
          if idxOf w < numCuts then 0 else miss ^ k := by
        intro w
        unfold afterHash
        by_cases hw : idxOf w < numCuts
        · rw [dif_pos hw, if_pos hw, run_pure, E_pure]
          rfl
        · rw [dif_neg hw, if_neg hw]
          apply ih
          · rw [Finset.card_insert_of_notMem hη]
            omega
          · intro η' hη'
            have hne : encQuery (m ++ η') ≠ encQuery (m ++ η) := by
              intro heq
              have he := append_nonce_inj m (encQuery_inj heq)
              exact hη' (he ▸ Finset.mem_insert_self η tried)
            rw [QueryCache.cacheQuery_of_ne _ _ hne]
            exact hfresh η' (fun h => hη' (Finset.mem_insert_of_mem h))
      calc
        _ = E ($ᵗ BitVec hashBits)
            (fun w => if idxOf w < numCuts then 0 else miss ^ k) := by
          congr 1
          funext w
          exact hkont w
        _ = _ := by rw [uniform_miss, pow_succ, mul_comm]
    simp_rw [hbody]
    exact expectedValue_const (by simp) _

/-- The arithmetic helper transferred from real probabilities to ENNReal. -/
private theorem miss_block : miss ^ 8192 ≤ 1 / 2 := by
  have h := AvailabilityCubic.block_bound
  have hbase : (1 : ℝ) - 45 / 524288 = 524243 / 524288 := by norm_num
  rw [hbase] at h
  have h' := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_pow (by norm_num)] at h'
  have hb : ENNReal.ofReal ((524243 : ℝ) / 524288) = miss := by
    norm_num [miss, ENNReal.ofReal_div_of_pos]
  have hh : ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rwa [hb, hh] at h'

/-- The full signing budget contains 128 blocks of 8192 fresh trials. -/
theorem miss_trials_le : miss ^ trials ≤ 1 / 2 ^ 128 := by
  change miss ^ (8192 * 128) ≤ 1 / 2 ^ 128
  rw [pow_mul]
  calc
    (miss ^ 8192) ^ 128 ≤ (1 / 2 : ℝ≥0∞) ^ 128 := pow_le_pow_left' miss_block _
    _ = 1 / 2 ^ 128 := by simp only [one_div, ENNReal.inv_pow]

/-- Exact signing failure for any graph using these indices and a fresh cache. -/
theorem sign_failure (S : IndexedDag.Scheme numCuts) (x : S.graph.Assignment)
    (m : Message) (c : Cache)
    (hfresh : ∀ η : Nonce, c (encQuery (m ++ η)) = none) :
    E (run (S.sign x m) c)
      (fun p => if p.1.isNone then 1 else 0) = miss ^ trials := by
  rw [sign_eq_map, run_map, E_map]
  simp only [Option.isNone_map]
  exact loop_failure m _ ∅ c
    (by norm_num [nonceBits, idxBits, numCuts, trials, idxCost, blockCost,
      signBudget, msgBits, blockBits]) (fun η _ => hfresh η)

/-- The contract's numerical signing-failure target, conditional on cache freshness. -/
theorem sign_failure_le (S : IndexedDag.Scheme numCuts) (x : S.graph.Assignment)
    (m : Message) (c : Cache)
    (hfresh : ∀ η : Nonce, c (encQuery (m ++ η)) = none) :
    E (run (S.sign x m) c)
      (fun p => if p.1.isNone then 1 else 0) ≤ 1 / 2 ^ 128 := by
  rw [sign_failure S x m c hfresh]
  exact miss_trials_le

#print axioms loop_failure
#print axioms sign_failure_le

end OptimalOTS.IndexedAnalysis.Availability
