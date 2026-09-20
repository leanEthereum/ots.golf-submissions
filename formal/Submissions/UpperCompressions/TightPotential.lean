import Submissions.UpperCompressions.RepeatedFibers
import Submissions.UpperCompressions.TightRow
import Submissions.UpperCompressions.TightDrift

/-! Accepted-count/exponential cache potential for a127-bit index and128-bit
nonce. The initial potential is paid by the reserved signing-query budget. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.IndexedAnalysis.Tight

open OptimalOTS.Dag

attribute [local irreducible] hashBits msgBits nonceBits IndexedAnalysis.idxBits
  IndexedAnalysis.numCuts trials signBudget idxCost blockBits

/-- Index universe, accepted classes, acceptance rate, and trial cap. -/
def I : ℝ := 2 ^ IndexedAnalysis.idxBits
def M : ℝ := numCuts
def p : ℝ := M / I
def L : ℝ := trials
/-- Accepted and total cached encoding-entry counts. -/
def A (d : Cache) : ℝ := (validSet d).card
def q (d : Cache) : ℝ := encCount d

def rhoReal (d : Cache) : ℝ := TightIndex.cachePotential p M L (A d) (q d)
def rho (d : Cache) : ℝ≥0∞ := ENNReal.ofReal (rhoReal d)

theorem I_pos : 0 < I := by unfold I; positivity
theorem M_pos : 0 < M := by norm_num [M, numCuts]
theorem p_nonneg : 0 ≤ p := div_nonneg M_pos.le I_pos.le
theorem L_nonneg : 0 ≤ L := Nat.cast_nonneg _
theorem A_nonneg (d : Cache) : 0 ≤ A d := Nat.cast_nonneg _
theorem q_nonneg (d : Cache) : 0 ≤ q d := Nat.cast_nonneg _
theorem rhoReal_nonneg (d : Cache) : 0 ≤ rhoReal d :=
  TightIndex.cachePotential_nonneg p M L (A d) (q d)
    (A_nonneg d) (mul_nonneg p_nonneg L_nonneg) M_pos.le

/-- Pointwise lookup at an encoding query. -/
theorem cache_enc_apply (d : Cache) (u v : EncInput) (w : BitVec hashBits) :
    (d.cacheQuery (encQuery u) w) (encQuery v) =
      if v = u then some w else d (encQuery v) := by
  by_cases hv : v = u
  · subst v; simp
  · rw [if_neg hv]
    exact QueryCache.cacheQuery_of_ne _ _ (fun he => hv (encQuery_inj he))

/-- Fresh accepted entries enter the accepted set once; rejected entries do not. -/
theorem validSet_cacheQuery (d : Cache) (u : EncInput) (w : BitVec hashBits)
    (hfresh : d (encQuery u) = none) :
    validSet (d.cacheQuery (encQuery u) w) =
      if idxOf w < numCuts then insert u (validSet d) else validSet d := by
  ext v
  by_cases hi : idxOf w < numCuts <;> by_cases hv : v = u
  · subst v
    simp [validSet, cache_enc_apply, hfresh, hi]
  · simp [validSet, cache_enc_apply, hv, hi]
  · subst v
    simp [validSet, cache_enc_apply, hfresh, hi]
  · simp [validSet, cache_enc_apply, hv, hi]

theorem A_cacheQuery (d : Cache) (u : EncInput) (w : BitVec hashBits)
    (hfresh : d (encQuery u) = none) :
    A (d.cacheQuery (encQuery u) w) = A d + if idxOf w < numCuts then 1 else 0 := by
  have hu : u ∉ validSet d := by simp [validSet, hfresh]
  unfold A
  rw [validSet_cacheQuery d u w hfresh]
  split_ifs with hi
  · rw [Finset.card_insert_of_notMem hu]
    push_cast
    rfl
  · simp

theorem encCount_cacheQuery_fresh (d : Cache) (u : EncInput) (w : BitVec hashBits)
    (hfresh : d (encQuery u) = none) :
    encCount (d.cacheQuery (encQuery u) w) = encCount d + 1 := by
  have hset : (Finset.univ.filter fun v : EncInput =>
      ((d.cacheQuery (encQuery u) w) (encQuery v)).isSome) =
      insert u (Finset.univ.filter fun v : EncInput => (d (encQuery v)).isSome) := by
    ext v
    by_cases hv : v = u
    · subst v; simp [cache_enc_apply]
    · simp [cache_enc_apply, hv]
  unfold encCount
  rw [hset, Finset.card_insert_of_notMem]
  simp [hfresh]

theorem q_cacheQuery (d : Cache) (u : EncInput) (w : BitVec hashBits)
    (hfresh : d (encQuery u) = none) :
    q (d.cacheQuery (encQuery u) w) = q d + 1 := by
  unfold q
  rw [encCount_cacheQuery_fresh d u w hfresh]
  push_cast
  rfl

theorem A_of_ne (d : Cache) {x : Query} (hx : ∀ u : EncInput, x ≠ encQuery u)
    (w : BitVec hashBits) : A (d.cacheQuery x w) = A d := by
  have he : validSet (d.cacheQuery x w) = validSet d := by
    apply Finset.filter_congr
    intro u _
    rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm (hx u))]
  unfold A
  rw [he]

theorem q_of_ne (d : Cache) {x : Query} (hx : ∀ u : EncInput, x ≠ encQuery u)
    (w : BitVec hashBits) : q (d.cacheQuery x w) = q d := by
  unfold q encCount
  congr 2
  apply Finset.filter_congr
  intro u _
  rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm (hx u))]

theorem rho_of_ne (d : Cache) {x : Query} (hx : ∀ u : EncInput, x ≠ encQuery u)
    (w : BitVec hashBits) : rho (d.cacheQuery x w) = rho d := by
  simp only [rho, rhoReal, A_of_ne d hx w, q_of_ne d hx w]

theorem A_empty : A ∅ = 0 := by simp [A, validSet]
theorem q_empty : q ∅ = 0 := by simp [q, encCount_empty]

theorem rhoReal_empty : rhoReal ∅ = L / (2 * I) + 1 / M := by
  unfold rhoReal
  rw [A_empty, q_empty]
  exact TightIndex.cachePotential_zero I M p L I_pos.ne' M_pos.ne' rfl

theorem rho_empty : rho ∅ = ENNReal.ofReal (L / (2 * I) + 1 / M) := by
  rw [rho, rhoReal_empty]

#print axioms A_cacheQuery
#print axioms encCount_cacheQuery_fresh
#print axioms rho_of_ne
#print axioms rho_empty


/-- Exact accepted-answer fraction, expressed over the reals. -/
theorem accepted_mean :
    (∑ w : BitVec hashBits, if idxOf w < numCuts then (1 : ℝ) else 0) /
      (2 : ℝ) ^ hashBits = p := by
  have hidx : IndexedAnalysis.idxBits ≤ hashBits := by norm_num [IndexedAnalysis.idxBits, hashBits]
  have hMle : numCuts ≤ 2 ^ IndexedAnalysis.idxBits := by norm_num [numCuts, IndexedAnalysis.idxBits]
  have hcount := card_idxOf_mem hidx (Finset.range numCuts)
    (fun n hn => lt_of_lt_of_le (Finset.mem_range.mp hn) hMle)
  simp only [Finset.mem_range, Finset.card_range] at hcount
  rw [Finset.sum_boole, hcount]
  have hH : (2 : ℝ) ^ hashBits =
      2 ^ IndexedAnalysis.idxBits * 2 ^ (hashBits - IndexedAnalysis.idxBits) := by
    rw [← pow_add, Nat.add_sub_cancel' hidx]
  push_cast
  rw [hH]
  unfold p M I
  have hpow : (2 : ℝ) ^ (hashBits - IndexedAnalysis.idxBits) ≠ 0 := by positivity
  field_simp

/-- The real uniform-oracle average charge is one inverse class universe. -/
theorem rhoReal_avg (d : Cache) (u : EncInput) (hfresh : d (encQuery u) = none) :
    (∑ w : BitVec hashBits, rhoReal (d.cacheQuery (encQuery u) w)) /
      (2 : ℝ) ^ hashBits ≤ rhoReal d + 1 / I := by
  let F0 := TightIndex.cachePotential p M L (A d) (q d + 1)
  let F1 := TightIndex.cachePotential p M L (A d + 1) (q d + 1)
  let z (w : BitVec hashBits) : ℝ := if idxOf w < numCuts then 1 else 0
  have hpoint (w : BitVec hashBits) :
      rhoReal (d.cacheQuery (encQuery u) w) = F0 + z w * (F1 - F0) := by
    unfold rhoReal
    rw [A_cacheQuery d u w hfresh, q_cacheQuery d u w hfresh]
    by_cases hi : idxOf w < numCuts <;> simp [hi, F0, F1, z]
  have havg : (∑ w : BitVec hashBits, rhoReal (d.cacheQuery (encQuery u) w)) /
      (2 : ℝ) ^ hashBits = (1 - p) * F0 + p * F1 := by
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_bitVec,
      nsmul_eq_mul, ← Finset.sum_mul]
    have hz : (∑ w : BitVec hashBits, z w) / (2 : ℝ) ^ hashBits = p := accepted_mean
    have hH : (2 : ℝ) ^ hashBits ≠ 0 := by positivity
    push_cast
    rw [add_div, mul_div_cancel_left₀ F0 hH]
    rw [mul_div_right_comm, hz]
    ring
  rw [havg]
  have hstep := TightIndex.cachePotential_step p M L (A d) (q d) p_nonneg M_pos
  have hpM : p / M = 1 / I := by
    unfold p
    field_simp [M_pos.ne', I_pos.ne']
  simpa only [F0, F1, rhoReal, hpM] using hstep

theorem ofReal_two_pow (k : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ k) = (2 : ℝ≥0∞) ^ k := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem natCast_div_two_pow (n k : ℕ) :
    ((n : ℝ≥0∞) / 2 ^ k) = ENNReal.ofReal ((n : ℝ) / 2 ^ k) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ofReal_two_pow]

/-- Uniform-oracle expected charge in the ENNReal interface used by Master. -/
theorem rho_charge (d : Cache) (u : EncInput) (hfresh : d (encQuery u) = none) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      rho (d.cacheQuery (encQuery u) w) ≤
        rho d + ((2 : ℝ≥0∞) ^ IndexedAnalysis.idxBits)⁻¹ := by
  have hH : (0 : ℝ) < 2 ^ hashBits := by positivity
  have hcard : (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal ((2 : ℝ) ^ hashBits)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hH, ofReal_two_pow, Fintype.card_bitVec]
    push_cast
    rfl
  have hi : ((2 : ℝ≥0∞) ^ IndexedAnalysis.idxBits)⁻¹ = ENNReal.ofReal (1 / I) := by
    rw [ENNReal.ofReal_div_of_pos I_pos, ENNReal.ofReal_one, I, ofReal_two_pow, one_div]
  rw [hcard, hi]
  unfold rho
  simp_rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hH.le)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ =>
      mul_nonneg (inv_nonneg.mpr hH.le) (rhoReal_nonneg _)),
    ← ENNReal.ofReal_add (rhoReal_nonneg d) (div_nonneg zero_le_one I_pos.le)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum, ← div_eq_inv_mul]
  exact rhoReal_avg d u hfresh

/-- The128-bit nonce space is twice the127-bit class universe. -/
theorem nonce_card : (2 : ℝ) ^ nonceBits = 2 * I := by
  norm_num [nonceBits, I, IndexedAnalysis.idxBits]

theorem V_le_A (d : Cache) : ((V d).card : ℝ) ≤ A d := by
  have h : (V d).card ≤ (validSet d).card := Finset.card_image_le
  unfold A
  exact_mod_cast h

theorem rowCached_le_encCount (d : Cache) (m : Message) :
    (rowCached d m).card ≤ encCount d := by
  exact (Finset.single_le_sum (fun m _ => Nat.zero_le (rowCached d m).card)
    (Finset.mem_univ m)).trans (sum_rowCached_le d)

theorem fresh_row_lower (d : Cache) (m : Message) (c : ℕ)
    (hc : (rowFresh d m).card ≤ c + trials) : 2 * I - q d - L ≤ c := by
  have he : rowFresh d m = Finset.univ \ rowCached d m := by
    ext η
    simp [rowFresh, rowCached]
  have hcard : (rowFresh d m).card + (rowCached d m).card = 2 ^ nonceBits := by
    rw [he, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_bitVec]
  have hlow : 2 ^ nonceBits ≤ c + trials + encCount d := by
    have := rowCached_le_encCount d m
    omega
  have hlowR : (2 : ℝ) ^ nonceBits ≤ c + L + q d := by
    unfold L q
    exact_mod_cast hlow
  rw [nonce_card] at hlowR
  linarith

/-- Real form of the signing-hazard bound. -/
theorem rhoReal_dom (d : Cache) (hbudget : encCount d + trials ≤ 2 ^ nonceBits)
    (m : Message) (c : ℕ) (hc : (rowFresh d m).card ≤ c + trials) :
    ((rowBad d m).card : ℝ) + c * (((V d).card : ℝ) / I) ≤
      rhoReal d * ((rowAcc d m).card + c * p) := by
  have hvM : ((V d).card : ℝ) ≤ M := by
    unfold M
    exact_mod_cast card_V_le_numCuts d
  have hba : ((rowBad d m).card : ℝ) ≤ (rowAcc d m).card := by
    exact_mod_cast Finset.card_le_card (rowBad_subset d m)
  have hsub : (V d).card ≤ (validSet d).card := Finset.card_image_le
  have hrepNat := TightIndex.rowBad_card_le_twice_excess d m
  have hrep : ((rowBad d m).card : ℝ) ≤ 2 * (A d - ((V d).card : ℝ)) := by
    have hs : (((validSet d).card - (V d).card : ℕ) : ℝ) =
        A d - ((V d).card : ℝ) := by rw [Nat.cast_sub hsub]; rfl
    have hh : ((rowBad d m).card : ℝ) ≤
        2 * (((validSet d).card - (V d).card : ℕ) : ℝ) := by exact_mod_cast hrepNat
    rwa [hs] at hh
  have hbudgetR : q d + L ≤ 2 * I := by
    rw [← nonce_card]
    unfold q L
    exact_mod_cast hbudget
  have hrow := TightIndex.row_bound I M p (q d) L (A d) ((V d).card)
    ((rowAcc d m).card) ((rowBad d m).card) c I_pos M_pos rfl
    (Nat.cast_nonneg _) hvM (V_le_A d) hba (Nat.cast_nonneg _) hrep
    hbudgetR (fresh_row_lower d m c hc)
  have hcap := TightIndex.row_cap_le_exp p (q d) L (A d)
    (mul_nonneg p_nonneg L_nonneg)
  have hden : 0 ≤ ((rowAcc d m).card : ℝ) + p * c :=
    add_nonneg (Nat.cast_nonneg _) (mul_nonneg p_nonneg (Nat.cast_nonneg _))
  have hmul := mul_le_mul_of_nonneg_right hcap hden
  unfold rhoReal TightIndex.cachePotential
  rw [div_mul_eq_mul_div, le_div_iff₀ M_pos]
  convert hrow.trans hmul using 1 <;> ring

/-- Exact hρ interface required by signRho_bound. -/
theorem rho_dom (d : Cache) (hbudget : encCount d + trials ≤ 2 ^ nonceBits)
    (m : Message) (c : ℕ) (hc1 : (rowFresh d m).card ≤ c + trials)
    (_hc2 : c ≤ (rowFresh d m).card) :
    ((rowBad d m).card : ℝ≥0∞) + c * (((V d).card : ℝ≥0∞) / 2 ^ IndexedAnalysis.idxBits) ≤
      rho d * ((rowAcc d m).card + c * ((numCuts : ℝ≥0∞) / 2 ^ IndexedAnalysis.idxBits)) := by
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hleft : ((rowBad d m).card : ℝ≥0∞) + c * (((V d).card : ℝ≥0∞) / 2 ^ IndexedAnalysis.idxBits) =
      ENNReal.ofReal (((rowBad d m).card : ℝ) + c * (((V d).card : ℝ) / I)) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg hc0 (div_nonneg (Nat.cast_nonneg _) I_pos.le)),
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    unfold I
    rw [natCast_div_two_pow]
  have hright : rho d * ((rowAcc d m).card + c * ((numCuts : ℝ≥0∞) / 2 ^ IndexedAnalysis.idxBits)) =
      ENNReal.ofReal (rhoReal d * (((rowAcc d m).card : ℝ) + c * p)) := by
    rw [ENNReal.ofReal_mul (rhoReal_nonneg d),
      ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg hc0 p_nonneg),
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    unfold rho p M I
    rw [natCast_div_two_pow]
  rw [hleft, hright]
  exact ENNReal.ofReal_le_ofReal (rhoReal_dom d hbudget m c hc1)

#print axioms rho_charge
#print axioms rho_dom

end OptimalOTS.IndexedAnalysis.Tight
