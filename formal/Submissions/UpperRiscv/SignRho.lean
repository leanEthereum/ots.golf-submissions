import Submissions.UpperRiscv.EncCharges

/-!
# The signing loop as one disjoint case split

Fix the signed message `m` and the cache `d` before signing. At every trial the signer draws an
untried nonce `η`:

* if `m ++ η` is cached with an accepted index it stops, and loses exactly when another cached entry
  shares that index (`rowBad`);
* if it is cached with a rejected index it tries again;
* if it is fresh, the answer is accepted with probability `numValid / 2 ^ idxBits` and then loses
  exactly when its index is already held (`V`), with probability `|V| / 2 ^ idxBits`.

So the losing mass of a trial is `|rowBad| + NF · |V| / 2 ^ idxBits` and its stopping mass is
`|rowAcc| + NF · numValid / 2 ^ idxBits`, where `NF` is the number of untried fresh nonces. Any `ρ`
bounding their ratio for every `NF ∈ [|rowFresh| − trials, |rowFresh|]` bounds the probability
of losing (`signRho_bound`), with no union over the trials.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials


/-- Nonces of row `m` cached with an accepted index. -/
def rowAcc (d : Cache) (m : Message) : Finset Nonce :=
  Finset.univ.filter fun η => ∃ w, d (encQuery (m ++ η)) = some w ∧ idxOf w ∈ validSet

/-- Nonces of row `m` cached with an accepted index that another cached entry shares. -/
def rowBad (d : Cache) (m : Message) : Finset Nonce :=
  Finset.univ.filter fun η => ∃ w, d (encQuery (m ++ η)) = some w ∧ idxOf w ∈ validSet ∧
    IdxPre d (m ++ η) (idxOf w)

/-- Uncached nonces of row `m`. -/
def rowFresh (d : Cache) (m : Message) : Finset Nonce :=
  Finset.univ.filter fun η => d (encQuery (m ++ η)) = none

/-- Nonces of row `m` cached with a rejected index. -/
def rowRej (d : Cache) (m : Message) : Finset Nonce :=
  Finset.univ.filter fun η => ∃ w, d (encQuery (m ++ η)) = some w ∧ idxOf w ∉ validSet

theorem rowBad_subset (d : Cache) (m : Message) : rowBad d m ⊆ rowAcc d m := by
  intro η hη
  simp only [rowBad, rowAcc, Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
  obtain ⟨w, hw, hi, -⟩ := hη
  exact ⟨w, hw, hi⟩

/-- The three statuses of a nonce partition every set of nonces. -/
theorem card_status (d : Cache) (m : Message) (U : Finset Nonce) :
    U.card = (U ∩ rowAcc d m).card + (U ∩ rowRej d m).card + (U ∩ rowFresh d m).card := by
  have h1 : Disjoint (U ∩ rowAcc d m) (U ∩ rowRej d m) := by
    rw [Finset.disjoint_left]
    intro η h1 h2
    simp only [Finset.mem_inter, rowAcc, rowRej, Finset.mem_filter, Finset.mem_univ, true_and]
      at h1 h2
    obtain ⟨-, w, hw, hi⟩ := h1
    obtain ⟨-, w', hw', hi'⟩ := h2
    rw [hw] at hw'
    cases hw'
    exact hi' hi
  have h2 : Disjoint (U ∩ rowAcc d m ∪ U ∩ rowRej d m) (U ∩ rowFresh d m) := by
    rw [Finset.disjoint_left]
    intro η h1 h2
    simp only [Finset.mem_union, Finset.mem_inter, rowAcc, rowRej, rowFresh, Finset.mem_filter,
      Finset.mem_univ, true_and] at h1 h2
    rcases h1 with ⟨-, w, hw, -⟩ | ⟨-, w, hw, -⟩ <;> rw [hw] at h2 <;> cases h2.2
  rw [← Finset.card_union_of_disjoint h1, ← Finset.card_union_of_disjoint h2]
  congr 1
  ext η
  simp only [Finset.mem_union, Finset.mem_inter, rowAcc, rowRej, rowFresh, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hη
    rcases hd : d (encQuery (m ++ η)) with _ | w
    · exact Or.inr ⟨hη, rfl⟩
    · by_cases hi : idxOf w ∈ validSet
      · exact Or.inl (Or.inl ⟨hη, w, rfl, hi⟩)
      · exact Or.inl (Or.inr ⟨hη, w, rfl, hi⟩)
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h

/-- The mass of the accepted and of the rejected answers. -/
theorem frac_acc (hidx : idxBits ≤ hashBits) (hM : numValid ≤ 2 ^ idxBits) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      (if idxOf w ∈ validSet then (1 : ℝ≥0∞) else 0) = (numValid : ℝ≥0∞) / 2 ^ idxBits := by
  rw [← Finset.mul_sum, Finset.sum_boole, card_idxOf_mem hidx _ (fun n hn => mem_validSet_lt hn),
    Nat.cast_mul, inv_card_mul_pow hidx]
  rfl

theorem frac_split (w : BitVec hashBits) :
    (if idxOf w ∈ validSet then (1 : ℝ≥0∞) else 0) +
      (if idxOf w ∈ validSet then (0 : ℝ≥0∞) else 1) = 1 := by
  split_ifs <;> simp

/-- The mass of the answers whose index is held. -/
theorem frac_V (hidx : idxBits ≤ hashBits) (d : Cache) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      (if idxOf w ∈ V d then (1 : ℝ≥0∞) else 0) = ((V d).card : ℝ≥0∞) / 2 ^ idxBits := by
  rw [← Finset.mul_sum, Finset.sum_boole, card_idxOf_mem hidx _ (V_lt d), Nat.cast_mul,
    inv_card_mul_pow hidx]

/-- The bound for a single trial: losing mass at most `ρ` times the trial's mass. -/
theorem trial_mass (d : Cache) (m : Message) (U : Finset Nonce) (ρ vf af rf : ℝ≥0∞)
    (hsplit : af + rf = 1) (hacc : rowAcc d m ⊆ U)
    (hρ : ((rowBad d m).card : ℝ≥0∞) + (U ∩ rowFresh d m).card * vf ≤
      ρ * ((rowAcc d m).card + (U ∩ rowFresh d m).card * af)) :
    ((rowBad d m).card : ℝ≥0∞) + (U ∩ rowRej d m).card * ρ +
        (U ∩ rowFresh d m).card * (vf + ρ * rf) ≤ ρ * U.card := by
  have hU : (U.card : ℝ≥0∞) = (rowAcc d m).card + (U ∩ rowRej d m).card +
      (U ∩ rowFresh d m).card := by
    rw [card_status d m U, Finset.inter_eq_right.2 hacc]
    push_cast; ring
  rw [hU]
  calc ((rowBad d m).card : ℝ≥0∞) + (U ∩ rowRej d m).card * ρ +
        (U ∩ rowFresh d m).card * (vf + ρ * rf)
      = (((rowBad d m).card : ℝ≥0∞) + (U ∩ rowFresh d m).card * vf) +
          (U ∩ rowRej d m).card * ρ + (U ∩ rowFresh d m).card * (ρ * rf) := by ring
    _ ≤ ρ * ((rowAcc d m).card + (U ∩ rowFresh d m).card * af) +
          (U ∩ rowRej d m).card * ρ + (U ∩ rowFresh d m).card * (ρ * rf) := by gcongr
    _ = ρ * ((rowAcc d m).card + (U ∩ rowRej d m).card +
          (U ∩ rowFresh d m).card * (af + rf)) := by ring
    _ = _ := by rw [hsplit, mul_one]

theorem ind_le_rowBad {d : Cache} {m : Message} {η : Nonce} {w : BitVec hashBits}
    (hi : idxOf w ∈ validSet) (hw : d (encQuery (m ++ η)) = some w) :
    (if ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × Idx)) = some (η', i) ∧
        IdxPre d (m ++ η') i.val then (1 : ℝ≥0∞) else 0) ≤
      if η ∈ rowBad d m then 1 else 0 := by
  by_cases h1 : ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × Idx)) =
      some (η', i) ∧ IdxPre d (m ++ η') i.val
  · rw [if_pos h1]
    obtain ⟨η', i, he, hpre⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [if_pos]
    simp only [rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, hi, hpre⟩
  · rw [if_neg h1]; exact zero_le

set_option maxHeartbeats 4000000 in
/-- The signing loop as one disjoint case split: `k` further trials, nonces `tried` already
used, current cache `d'` differing from `d` only by rejected entries at tried nonces. The loop's
value, plus `λ ρ` when it fails, is at most `Φ d + κ b + λ ρ`. -/
theorem signRhoLoop_bound (hM' : numValid ≤ 2 ^ idxBits) (hidx : idxBits ≤ hashBits)
    (m : Message) (d : Cache) {β J : Type} [Nonempty J]
    (kont : J → Option (Nonce × Idx) → OracleComp Spec β)
    (Fn : Option (Nonce × Idx) → Cache → ℝ≥0∞)
    (Φ : Cache → ℝ≥0∞) (hΦ : EncInvariant Φ) (κ lam ρ : ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hF : ∀ r d' b', SignExt m d r d' → I d' b' → (∀ j, CostAtMost (kont j r) b') →
      Fn r d' ≤ Φ d' + lam * (if ∃ η i, r = some (η, i) ∧ IdxPre d (m ++ η) i.val then 1 else 0) +
        κ * b')
    (hρ : ∀ c : ℕ, (rowFresh d m).card ≤ c + trials → c ≤ (rowFresh d m).card →
      ((rowBad d m).card : ℝ≥0∞) + c * (((V d).card : ℝ≥0∞) / 2 ^ idxBits) ≤
        ρ * ((rowAcc d m).card + c * ((numValid : ℝ≥0∞) / 2 ^ idxBits))) :
    ∀ (k : ℕ) (tried : Finset Nonce) (d' : Cache) (b : ℕ),
      Cache.Sub d d' →
      (∀ q w, d q = none → d' q = some w →
        ∃ η ∈ tried, q = encQuery (m ++ η) ∧ idxOf w ∉ validSet) →
      (∀ η ∈ tried, η ∉ rowAcc d m) →
      Φ d' = Φ d →
      tried.card + k ≤ trials →
      I d' b →
      (∀ j, CostAtMost (signIdxLoop m k tried >>= kont j) b) →
      E (run (signIdxLoop m k tried) d')
        (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0)) ≤
        Φ d + κ * b + lam * ρ := by
  -- the failing run
  have hnone : ∀ (d' : Cache) (b : ℕ) (tried : Finset Nonce), Cache.Sub d d' →
      (∀ q w, d q = none → d' q = some w →
        ∃ η ∈ tried, q = encQuery (m ++ η) ∧ idxOf w ∉ validSet) →
      Φ d' = Φ d → I d' b → (∀ j, CostAtMost (kont j none) b) →
      Fn none d' + (if (none : Option (Nonce × Idx)) = none then lam * ρ else 0) ≤
        Φ d + κ * b + lam * ρ := by
    intro d' b tried hSub hNew hΦd hI hB
    have h := hF none d' b (signExt_none hSub hNew) hI hB
    rw [hΦd, if_neg (not_exists_none), mul_zero, add_zero] at h
    rw [if_pos rfl]
    gcongr
  intro k
  induction k with
  | zero =>
    intro tried d' b hSub hNew hTried hΦd hcard hI hB
    rw [signIdxLoop, run_pure, E_pure]
    simp only [signIdxLoop, pure_bind] at hB
    exact hnone d' b tried hSub hNew hΦd hI hB
  | succ k ih =>
    intro tried d' b hSub hNew hTried hΦd hcard hI hB
    by_cases hc : 0 < (Finset.univ \ tried).card
    · simp only [signIdxLoop_succ m k tried hc] at hB ⊢
      have hB' : ∀ j i, CostAtMost (loopBody m k tried (nonceOf tried hc i) >>= kont j) b :=
        fun j => costAtMost_inl_bind _ _ _ (hB j)
      rw [run_query_bind, E_bind, oracleImpl_run_inl, E_bind, E_query_unif]
      simp only [E_pure]
      have hcast : (Finset.univ \ tried).card - 1 + 1 = (Finset.univ \ tried).card := by omega
      have hcR : (((Finset.univ \ tried).card - 1 : ℕ) : ℝ≥0∞) + 1 =
          ((Finset.univ \ tried).card : ℝ≥0∞) := by
        rw [← Nat.cast_add_one, hcast]
      simp only [hcR]
      have hc0 : ((Finset.univ \ tried).card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
      have hct : ((Finset.univ \ tried).card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      set vf : ℝ≥0∞ := ((V d).card : ℝ≥0∞) / 2 ^ idxBits with hvf
      set af : ℝ≥0∞ := (numValid : ℝ≥0∞) / 2 ^ idxBits with haf
      set rf : ℝ≥0∞ := ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (if idxOf w ∈ validSet then (0 : ℝ≥0∞) else 1) with hrf
      have hsplit : af + rf = 1 := by
        rw [haf, ← frac_acc hidx hM', hrf, ← Finset.sum_add_distrib]
        simp_rw [← mul_add, frac_split]
        exact sum_inv_card_mul 1
      -- the value of one trial at an untried nonce
      let x : Nonce → ℝ≥0∞ := fun η =>
        (if η ∈ rowBad d m then 1 else 0) + (if η ∈ rowRej d m then ρ else 0) +
          (if η ∈ rowFresh d m then vf + ρ * rf else 0)
      have per : ∀ η ∈ Finset.univ \ tried,
          (∀ j, CostAtMost (loopBody m k tried η >>= kont j) b) →
          E (run (loopBody m k tried η) d')
            (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0)) ≤
            Φ d + κ * b + lam * x η := by
        intro η hη hBη
        have hηt : η ∉ tried := (Finset.mem_sdiff.1 hη).2
        have hins : (insert η tried).card + k ≤ trials := by
          rw [Finset.card_insert_of_notMem hηt]; omega
        have hBw : ∀ j w, CostAtMost (afterHash m k tried η w >>= kont j)
            (b - queryCost (.inr (encQuery (m ++ η)))) :=
          fun j => (costAtMost_inr_bind _ _ _ (hBη j)).2
        have hcost : queryCost (.inr (encQuery (m ++ η))) ≤ b :=
          (costAtMost_inr_bind _ _ _ (hBη (Classical.arbitrary J))).1
        have hb₁ : ((b - queryCost (.inr (encQuery (m ++ η))) : ℕ) : ℝ≥0∞) ≤ b :=
          Nat.cast_le.2 (Nat.sub_le _ _)
        have hq : d' (encQuery (m ++ η)) = d (encQuery (m ++ η)) :=
          cache_eq_of_notMem hSub hNew hηt
        simp only [loopBody]
        rw [run_query_bind, E_bind]
        rcases hdq : d (encQuery (m ++ η)) with _ | w
        · -- fresh encoding query
          rw [hdq] at hq
          have hxη : x η = vf + ρ * rf := by
            have h1 : η ∉ rowBad d m := by
              simp only [rowBad, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
            have h2 : η ∉ rowRej d m := by
              simp only [rowRej, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
            have h3 : η ∈ rowFresh d m := by
              simp only [rowFresh, Finset.mem_filter, Finset.mem_univ, true_and, hdq]
            simp only [x, if_neg h1, if_neg h2, if_pos h3, zero_add]
          rw [hxη, oracleImpl_run_inr_none hq, E_bind, E_uniform]
          simp only [E_pure]
          have hΦ' : ∀ w, Φ (d'.cacheQuery (encQuery (m ++ η)) w) = Φ d := fun w =>
            (hΦ d' (m ++ η) w).trans hΦd
          have hSub' : ∀ w, Cache.Sub d (d'.cacheQuery (encQuery (m ++ η)) w) := fun w =>
            hSub.trans (Cache.sub_cacheQuery_of_none hq w)
          have hηacc : η ∉ rowAcc d m := by
            simp only [rowAcc, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
          have hTried' : ∀ η' ∈ insert η tried, η' ∉ rowAcc d m := by
            intro η' h'
            rcases Finset.mem_insert.1 h' with rfl | h'
            · exact hηacc
            · exact hTried η' h'
          have perw : ∀ w : BitVec hashBits,
              E (run (afterHash m k tried η w) (d'.cacheQuery (encQuery (m ++ η)) w))
                (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0)) ≤
              Φ d + κ * b + lam * ((if idxOf w ∈ V d then 1 else 0) +
                (if idxOf w ∈ validSet then 0 else ρ)) := by
            intro w
            by_cases hi : idxOf w ∈ validSet
            · rw [afterHash, dif_pos hi, run_pure, E_pure, if_pos hi, add_zero]
              simp only [reduceCtorEq, if_false, add_zero]
              have hBk : ∀ j, CostAtMost (kont j (some (η, ⟨idxOf w, hi⟩)))
                  (b - queryCost (.inr (encQuery (m ++ η)))) := fun j => by
                have := hBw j w
                rwa [afterHash, dif_pos hi, pure_bind] at this
              refine (hF _ _ _ (signExt_fresh hSub hNew hi hq)
                (hI_fresh d' b _ hI hq hcost w) hBk).trans ?_
              rw [hΦ' w]
              calc _ ≤ Φ d + lam * (if idxOf w ∈ V d then 1 else 0) + κ * b := by
                    gcongr
                    · exact ind_le_V hi
                _ = _ := by ring
            · rw [afterHash, dif_neg hi, if_neg hi]
              have hBk : ∀ j, CostAtMost (signIdxLoop m k (insert η tried) >>= kont j)
                  (b - queryCost (.inr (encQuery (m ++ η)))) := fun j => by
                have := hBw j w
                rwa [afterHash, dif_neg hi] at this
              refine (ih (insert η tried) _ _ (hSub' w) (new_cacheQuery hNew η hi) hTried'
                (hΦ' w) hins (hI_fresh d' b _ hI hq hcost w) hBk).trans ?_
              calc _ ≤ Φ d + κ * b + lam * ρ := by gcongr
                _ ≤ _ := by gcongr; exact le_add_self
          calc ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                E (run (afterHash m k tried η w) (d'.cacheQuery (encQuery (m ++ η)) w))
                  (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0))
              ≤ ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                  (Φ d + κ * b + lam * ((if idxOf w ∈ V d then 1 else 0) +
                    (if idxOf w ∈ validSet then 0 else ρ))) :=
                Finset.sum_le_sum fun w _ => mul_le_mul_right (perw w) _
            _ = Φ d + κ * b + lam * (vf + ρ * rf) := by
                have hρw : ∀ w : BitVec hashBits, (if idxOf w ∈ validSet then 0 else ρ) =
                    ρ * (if idxOf w ∈ validSet then (0 : ℝ≥0∞) else 1) := fun w => by
                  split_ifs <;> simp
                simp_rw [hρw, mul_add, Finset.sum_add_distrib, sum_inv_card_mul]
                rw [hvf, ← frac_V hidx d, hrf]
                simp only [mul_add, Finset.mul_sum]
                congr 2 <;> exact Finset.sum_congr rfl fun w _ => by ring
        · -- cached encoding query
          rw [hdq] at hq
          rw [oracleImpl_run_inr_some hq, E_pure]
          by_cases hi : idxOf w ∈ validSet
          · have hxη : x η = if η ∈ rowBad d m then 1 else 0 := by
              have h2 : η ∉ rowRej d m := by
                simp only [rowRej, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simpa using hi
              have h3 : η ∉ rowFresh d m := by
                simp only [rowFresh, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
              simp only [x, if_neg h2, if_neg h3, add_zero]
            rw [hxη, afterHash, dif_pos hi, run_pure, E_pure]
            simp only [reduceCtorEq, if_false, add_zero]
            have hBk : ∀ j, CostAtMost (kont j (some (η, ⟨idxOf w, hi⟩)))
                (b - queryCost (.inr (encQuery (m ++ η)))) := fun j => by
              have := hBw j w
              rwa [afterHash, dif_pos hi, pure_bind] at this
            refine (hF _ _ _ (signExt_cached hSub hNew hi hq)
              (hI_cached d' b _ hI (by simp [hq]) hcost) hBk).trans ?_
            rw [hΦd]
            calc _ ≤ Φ d + lam * (if η ∈ rowBad d m then 1 else 0) + κ * b := by
                  gcongr
                  · exact ind_le_rowBad hi hdq
              _ = _ := by ring
          · have hxη : x η = ρ := by
              have h1 : η ∉ rowBad d m := by
                simp only [rowBad, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simpa using
                  fun h => absurd h hi
              have h2 : η ∈ rowRej d m := by
                simp only [rowRej, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simpa using hi
              have h3 : η ∉ rowFresh d m := by
                simp only [rowFresh, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
              simp only [x, if_neg h1, if_pos h2, if_neg h3, zero_add, add_zero]
            rw [hxη, afterHash, dif_neg hi]
            have hBk : ∀ j, CostAtMost (signIdxLoop m k (insert η tried) >>= kont j)
                (b - queryCost (.inr (encQuery (m ++ η)))) := fun j => by
              have := hBw j w
              rwa [afterHash, dif_neg hi] at this
            have hηacc : η ∉ rowAcc d m := by
              simp only [rowAcc, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simpa using hi
            have hTried' : ∀ η' ∈ insert η tried, η' ∉ rowAcc d m := by
              intro η' h'
              rcases Finset.mem_insert.1 h' with rfl | h'
              · exact hηacc
              · exact hTried η' h'
            refine (ih (insert η tried) d' _ hSub (new_insert hNew η) hTried' hΦd hins
              (hI_cached d' b _ hI (by simp [hq]) hcost) hBk).trans ?_
            gcongr
      -- average over the nonce
      have hacc : rowAcc d m ⊆ Finset.univ \ tried := by
        intro η hη
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => hTried η h hη⟩
      have hbad : (Finset.univ \ tried) ∩ rowBad d m = rowBad d m :=
        Finset.inter_eq_right.2 ((rowBad_subset d m).trans hacc)
      have hsum : ∑ η ∈ Finset.univ \ tried, x η =
          ((rowBad d m).card : ℝ≥0∞) + ((Finset.univ \ tried) ∩ rowRej d m).card * ρ +
            ((Finset.univ \ tried) ∩ rowFresh d m).card * (vf + ρ * rf) := by
        simp only [x]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.sum_ite_mem, Finset.sum_const, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
          nsmul_eq_mul, nsmul_eq_mul, mul_one, hbad]
      have hfreshcard : (rowFresh d m).card ≤
          ((Finset.univ \ tried) ∩ rowFresh d m).card + trials := by
        have h1 : rowFresh d m ⊆ ((Finset.univ \ tried) ∩ rowFresh d m) ∪ tried := by
          intro η hη
          by_cases ht : η ∈ tried
          · exact Finset.mem_union_right _ ht
          · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨Finset.mem_sdiff.2
              ⟨Finset.mem_univ _, ht⟩, hη⟩)
        have := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
        omega
      have hmass := trial_mass d m (Finset.univ \ tried) ρ vf af rf hsplit hacc
        (hρ _ hfreshcard (Finset.card_le_card Finset.inter_subset_right))
      rw [← hsum] at hmass
      have hstep1 : ∀ j : Fin ((Finset.univ \ tried).card - 1 + 1),
          ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            E (run (loopBody m k tried (nonceOf tried hc j)) d')
              (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0)) ≤
          ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            (Φ d + κ * b + lam * x (nonceOf tried hc j)) :=
        fun j => mul_le_mul_right (per _ (nonceOf_mem tried hc j) (fun i => hB' i j)) _
      have hstep2 := Analysis.sum_fin_equivFin hcast fun η =>
        ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * (Φ d + κ * b + lam * x η)
      calc ∑ j, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            E (run (loopBody m k tried (nonceOf tried hc j)) d')
              (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0))
          ≤ ∑ j, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
              (Φ d + κ * b + lam * x (nonceOf tried hc j)) :=
            Finset.sum_le_sum fun j _ => hstep1 j
        _ = ∑ η ∈ Finset.univ \ tried, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
              (Φ d + κ * b + lam * x η) := hstep2
        _ = (Φ d + κ * b) + ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
              (lam * ∑ η ∈ Finset.univ \ tried, x η) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
              ← Finset.mul_sum, mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
        _ ≤ (Φ d + κ * b) + ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
              (lam * (ρ * (Finset.univ \ tried).card)) := by gcongr
        _ = Φ d + κ * b + lam * ρ := by
            have : ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
                (lam * (ρ * (Finset.univ \ tried).card)) =
                lam * ρ * (((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * (Finset.univ \ tried).card) := by
              ring
            rw [this, ENNReal.inv_mul_cancel hc0 hct, mul_one]
    · rw [signIdxLoop, dif_neg hc, run_pure, E_pure]
      simp only [signIdxLoop, dif_neg hc, pure_bind] at hB
      exact hnone d' b tried hSub hNew hΦd hI hB

/-- **The signing bound, as one disjoint case split.** -/
theorem signRho_bound (hM' : numValid ≤ 2 ^ idxBits) (hidx : idxBits ≤ hashBits)
    (m : Message) (d : Cache) {β J : Type} [Nonempty J]
    (k : J → Option (Nonce × Idx) → OracleComp Spec β)
    (Fn : Option (Nonce × Idx) → Cache → ℝ≥0∞)
    (Φ : Cache → ℝ≥0∞) (hΦ : EncInvariant Φ) (κ lam ρ : ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hF : ∀ r d' b', SignExt m d r d' → I d' b' → (∀ j, CostAtMost (k j r) b') →
      Fn r d' ≤ Φ d' + lam * (if ∃ η i, r = some (η, i) ∧ IdxPre d (m ++ η) i.val then 1 else 0) +
        κ * b')
    (hρ : ∀ c : ℕ, (rowFresh d m).card ≤ c + trials → c ≤ (rowFresh d m).card →
      ((rowBad d m).card : ℝ≥0∞) + c * (((V d).card : ℝ≥0∞) / 2 ^ idxBits) ≤
        ρ * ((rowAcc d m).card + c * ((numValid : ℝ≥0∞) / 2 ^ idxBits)))
    {b : ℕ} (hI : I d b) (hB : ∀ j, CostAtMost (signIdx m >>= k j) b) :
    E (run (signIdx m) d) (fun p => Fn p.1 p.2) ≤ Φ d + lam * ρ + κ * b := by
  have h := signRhoLoop_bound hM' hidx m d k Fn Φ hΦ κ lam ρ I hI_fresh hI_cached hF hρ
    trials ∅ d b (Cache.Sub.refl d) (fun q w h1 h2 => by rw [h1] at h2; cases h2)
    (fun η h => by simp at h) rfl (by simp) hI hB
  refine (E_mono _ fun p => le_self_add).trans (h.trans (le_of_eq ?_))
  ring

end OptimalOTS
