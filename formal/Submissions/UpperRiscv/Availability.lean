import Submissions.UpperRiscv.Assembly
import Submissions.UpperRiscv.Scheme
import Submissions.UpperRiscv.Adapter
import Submissions.UpperRiscv.FreshKeygen

/-!
# Signing availability of the forest algorithm

Key generation makes no 512-bit index query. For any message chosen from the public key,
the signer therefore tries fresh, distinct nonce queries. Each trial fails with probability
`miss = 1 - numValid / 2 ^ 128 ≤ 1048487 / 1048576`, and the `2^20` trials give failure at most
`2^-128`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.Forest.Availability

open OptimalOTS.Dag


attribute [local irreducible] Finset.univ Finset.filter validSet numValid

/-- Failure probability of one fresh index query. -/
def miss : ℝ≥0∞ :=
  ((2 ^ 256 - numValid * 2 ^ 128 : ℕ) : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹

theorem miss_eq : miss = ((2 ^ 256 - numValid * 2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [miss, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]

/-- At least `89 * 2 ^ 108` of the `2 ^ 128` indices are accepted. -/
theorem miss_le : miss ≤ 1048487 / 1048576 := by
  have hN : 89 * 2 ^ 236 ≤ numValid * 2 ^ 128 :=
    calc 89 * 2 ^ 236 = (89 * 2 ^ 108) * 2 ^ 128 := by norm_num
      _ ≤ _ := Nat.mul_le_mul_right _ numValid_avail
  have ha : 2 ^ 256 - numValid * 2 ^ 128 ≤ 1048487 * 2 ^ 236 := by
    have h := Nat.sub_le_sub_left hN (2 ^ 256)
    have e : 2 ^ 256 - 89 * 2 ^ 236 = 1048487 * 2 ^ 236 := by norm_num
    omega
  calc miss = ((2 ^ 256 - numValid * 2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := miss_eq
    _ ≤ ((1048487 * 2 ^ 236 : ℕ) : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (Nat.cast_le.mpr ha) _
    _ = 1048487 / 1048576 := by
      rw [ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)]
      norm_num

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- Stated for any width, so that the kernel never enumerates the 256-bit strings. -/
private theorem card_filter_not_bitVec {n k : ℕ} (p : BitVec n → Prop) [DecidablePred p]
    (hv : (Finset.univ.filter p).card = k) :
    (Finset.univ.filter fun w => ¬ p w).card = 2 ^ n - k := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (BitVec n))) (p := p)
  rw [hv, Finset.card_univ, Fintype.card_bitVec] at h
  omega

private theorem uniform_miss_count (hidx : idxBits ≤ hashBits)
    (hM : numValid ≤ 2 ^ idxBits) (a : ℝ≥0∞) :
    E ($ᵗ BitVec hashBits) (fun w => if idxOf w ∈ validSet then 0 else a) =
      ((2 ^ hashBits - numValid * 2 ^ (hashBits - idxBits) : ℕ) : ℝ≥0∞) *
        (((2 ^ hashBits : ℕ) : ℝ≥0∞)⁻¹ * a) := by
  have hv : (Finset.univ.filter fun w : BitVec hashBits => idxOf w ∈ validSet).card =
      numValid * 2 ^ (hashBits - idxBits) := by
    have h := Analysis.card_idxOfOut_mem hidx (validSet) (fun n hn => mem_validSet_lt hn)
    convert h using 2
    · exact Finset.filter_congr_decidable _ _ _
    · rw [numValid]
  have hn : (Finset.univ.filter fun w : BitVec hashBits => ¬ idxOf w ∈ validSet).card =
      2 ^ hashBits - numValid * 2 ^ (hashBits - idxBits) :=
    card_filter_not_bitVec _ hv
  rw [E_uniform]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    nsmul_eq_mul, hn, Fintype.card_bitVec]

attribute [local semireducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

private theorem uniform_miss (a : ℝ≥0∞) :
    E ($ᵗ BitVec hashBits)
      (fun w => if idxOf w ∈ validSet then 0 else a) = miss * a := by
  rw [uniform_miss_count (by decide) (numValid_le), ← mul_assoc]
  have h1 : hashBits = 256 := rfl
  have h2 : hashBits - idxBits = 128 := rfl
  rw [h2, h1]
  rfl

/-- Exact failure probability while enough untried nonces remain and their queries are fresh. -/
theorem loop_failure (m : EMessage) :
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
          if idxOf w ∈ validSet then 0 else miss ^ k := by
        intro w
        unfold afterHash
        by_cases hw : idxOf w ∈ validSet
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
            (fun w => if idxOf w ∈ validSet then 0 else miss ^ k) := by
          congr 1
          funext w
          exact hkont w
        _ = _ := by rw [uniform_miss, pow_succ, mul_comm]
    simp_rw [hbody]
    exact expectedValue_const (by simp) _

/-- A rational bound on repeated failure; it avoids real exponentials. -/
private theorem bernoulli_reciprocal {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (1 - p) ^ k ≤ 1 / (1 + (k : ℝ) * p) := by
  have hr : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hprod : ∀ n : ℕ, (1 + (n : ℝ) * p) * (1 - p) ^ n ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add_one, pow_succ]
      have hc : (1 + ((n : ℝ) + 1) * p) * (1 - p) ≤ 1 + (n : ℝ) * p := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith [sq_nonneg p]
      have hh := mul_le_mul_of_nonneg_right hc (pow_nonneg hr n)
      nlinarith
  have hd : 0 < 1 + (k : ℝ) * p := by positivity
  rw [le_div_iff₀ hd]
  simpa only [mul_comm] using hprod k

/-- Grouping the rational reciprocal bound into 32-trial blocks proves that
8192 trials fail with probability at most one half, without real exponentials. -/
private theorem miss_block : miss ^ 8192 ≤ 1 / 2 := by
  refine (pow_le_pow_left' miss_le 8192).trans ?_
  have h32 := bernoulli_reciprocal (p := (89 : ℝ) / 1048576) (by norm_num) (by norm_num) 32
  have hbase : (1 : ℝ) - 89 / 1048576 = 1048487 / 1048576 := by norm_num
  have hden : 1 + ((32 : ℕ) : ℝ) * (89 / 1048576) = 1051424 / 1048576 := by norm_num
  rw [hbase, hden, one_div_div] at h32
  have hnn : (0 : ℝ) ≤ ((1048487 : ℝ) / 1048576) ^ 32 := by positivity
  have h : ((1048487 : ℝ) / 1048576) ^ 8192 ≤ 1 / 2 := by
    calc ((1048487 : ℝ) / 1048576) ^ 8192
        = (((1048487 : ℝ) / 1048576) ^ 32) ^ 256 := by rw [← pow_mul]
      _ ≤ ((1048576 : ℝ) / 1051424) ^ 256 := pow_le_pow_left₀ hnn h32 256
      _ ≤ 1 / 2 := by
          rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
          norm_num
  have h' := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_pow (by norm_num)] at h'
  have hb : ENNReal.ofReal ((1048487 : ℝ) / 1048576) = (1048487 / 1048576 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  have hh : ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rwa [hb, hh] at h'

/-- The full signing budget contains 128 blocks. -/
theorem miss_trials_le : miss ^ trials ≤ (1 : ℝ≥0∞) / 2 ^ 128 := by
  change miss ^ (8192 * 128) ≤ (1 : ℝ≥0∞) / 2 ^ 128
  rw [pow_mul]
  refine (pow_le_pow_left' miss_block 128).trans ?_
  simp only [one_div, ENNReal.inv_pow, le_refl]

/-- Signing has the same failure probability for every message and every fresh index cache. -/
theorem sign_failure (x : forestScheme.graph.Assignment) (m : Message)
    (c : Cache)
    (hfresh : ∀ η : Nonce, c (encQuery (emsg m (forestScheme.publicKey x) ++ η)) = none) :
    E (run (forestScheme.sign x m) c)
      (fun p => if p.1.isNone then 1 else 0) = miss ^ trials := by
  rw [sign_eq_map, run_map, E_map]
  simp only [Option.isNone_map]
  exact loop_failure (emsg m (forestScheme.publicKey x)) _ ∅ c (by norm_num [nonceBits, idxBits, numCuts, trials, idxCost, blockCost, signBudget, msgBits, pkBits, blockBits]) (fun η _ => hfresh η)

attribute [local irreducible] graph

/-- Exact failure probability, including keygen runs with repeated oracle inputs.
Length separation makes the ideal-record collision penalty unnecessary. -/
theorem signingFailure_exact (message : PublicKey → Message) :
    probTrue (do
      let kg ← forestScheme.keygen
      let σ ← forestScheme.sign kg.2 (message kg.1)
      pure σ.isNone) = miss ^ trials := by
  rw [probTrue_eq_E_run, run_bind, E_bind, E_run_keygen_real]
  simp only [run_bind, E_bind, run_pure, E_pure]
  calc
    _ = ∑ _ξ : forestScheme.graph.Rec,
        (Fintype.card forestScheme.graph.Rec : ℝ≥0∞)⁻¹ * miss ^ trials := by
      refine Finset.sum_congr rfl fun ξ _ => congrArg _ ?_
      exact sign_failure _ _ _ (fun η => realRun_enc_fresh ξ _)
    _ = miss ^ trials := sum_inv_card_mul' _

/-- Failure remains bounded even when the message is chosen after seeing the public key. -/
theorem signingFailure_strong :
    forestScheme.toAlgorithm.SigningFailureAtMost (1 / 2 ^ 128 : ℝ≥0∞) := by
  intro message
  change probTrue (do
    let kg ← forestScheme.keygen
    let σ ← forestScheme.sign kg.2 (message kg.1)
    pure σ.isNone) ≤ _
  rw [signingFailure_exact]
  exact miss_trials_le

end OptimalOTS.Forest.Availability

namespace OptimalOTS.GenericAvailability

open OptimalOTS.Dag


/-- The forest algorithm meets the generic upper challenge's signing-failure allowance. -/
theorem signingFailure :
    Forest.forestScheme.toAlgorithm.SigningFailureAtMost (1 / 2 ^ 128 : ℝ≥0∞) := by
  intro message
  exact (Forest.Availability.signingFailure_strong message).trans (by norm_num)

end OptimalOTS.GenericAvailability
