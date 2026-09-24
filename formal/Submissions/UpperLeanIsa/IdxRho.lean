import Submissions.UpperLeanIsa.IdxCharges

/-!
# The signing loop as one disjoint case split

Ported from UpperRiscv `SignRho.lean`. Fix the extended message `m` of the signed message and
the cache `d` before signing. At every trial the signer draws an untried nonce `η`:

* if `m ++ η` is cached with an accepted index it stops, and loses exactly when another cached
  entry shares that index (`rowBad`);
* if it is cached with a rejected index it tries again;
* if it is fresh, the answer is accepted with probability `numValid / 2 ^ 127` and then loses
  exactly when its index is already held (`V`), with probability `|V| / 2 ^ 127`.

Any `ρ` bounding the ratio of the losing to the stopping mass bounds the probability of losing
(`signRho_bound`), with no union over the trials.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.validSet Params.encQuery Params.V
  Params.validInputs

namespace Params

variable (P : Params)






/-- Nonces of row `m` cached with an accepted index. -/
def rowAcc (d : Cache) (m : EMessage) : Finset Nonce :=
  Finset.univ.filter fun η => ∃ w, d (P.encQuery (m ++ η)) = some w ∧ idxOf w ∈ P.validSet

/-- Nonces of row `m` cached with an accepted index that another cached entry shares. -/
def rowBad (d : Cache) (m : EMessage) : Finset Nonce :=
  Finset.univ.filter fun η => ∃ w, d (P.encQuery (m ++ η)) = some w ∧ idxOf w ∈ P.validSet ∧
    P.IdxPre d (m ++ η) (idxOf w)

/-- Uncached nonces of row `m`. -/
def rowFresh (d : Cache) (m : EMessage) : Finset Nonce :=
  Finset.univ.filter fun η => d (P.encQuery (m ++ η)) = none

/-- Nonces of row `m` cached with a rejected index. -/
def rowRej (d : Cache) (m : EMessage) : Finset Nonce :=
  Finset.univ.filter fun η => ∃ w, d (P.encQuery (m ++ η)) = some w ∧ idxOf w ∉ P.validSet

theorem rowBad_subset (d : Cache) (m : EMessage) : P.rowBad d m ⊆ P.rowAcc d m := by
  intro η hη
  simp only [Params.rowBad, Params.rowAcc, Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
  obtain ⟨w, hw, hi, -⟩ := hη
  exact ⟨w, hw, hi⟩

/-- The three statuses of a nonce partition every set of nonces. -/
theorem card_status (d : Cache) (m : EMessage) (U : Finset Nonce) :
    U.card = (U ∩ P.rowAcc d m).card + (U ∩ P.rowRej d m).card + (U ∩ P.rowFresh d m).card := by
  have h1 : Disjoint (U ∩ P.rowAcc d m) (U ∩ P.rowRej d m) := by
    rw [Finset.disjoint_left]
    intro η h1 h2
    simp only [Finset.mem_inter, Params.rowAcc, Params.rowRej, Finset.mem_filter, Finset.mem_univ, true_and]
      at h1 h2
    obtain ⟨-, w, hw, hi⟩ := h1
    obtain ⟨-, w', hw', hi'⟩ := h2
    rw [hw] at hw'
    cases hw'
    exact hi' hi
  have h2 : Disjoint (U ∩ P.rowAcc d m ∪ U ∩ P.rowRej d m) (U ∩ P.rowFresh d m) := by
    rw [Finset.disjoint_left]
    intro η h1 h2
    simp only [Finset.mem_union, Finset.mem_inter, Params.rowAcc, Params.rowRej, Params.rowFresh, Finset.mem_filter,
      Finset.mem_univ, true_and] at h1 h2
    rcases h1 with ⟨-, w, hw, -⟩ | ⟨-, w, hw, -⟩ <;> rw [hw] at h2 <;> cases h2.2
  rw [← Finset.card_union_of_disjoint h1, ← Finset.card_union_of_disjoint h2]
  congr 1
  ext η
  simp only [Finset.mem_union, Finset.mem_inter, Params.rowAcc, Params.rowRej, Params.rowFresh, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hη
    rcases hd : d (P.encQuery (m ++ η)) with _ | w
    · exact Or.inr ⟨hη, rfl⟩
    · by_cases hi : idxOf w ∈ P.validSet
      · exact Or.inl (Or.inl ⟨hη, w, rfl, hi⟩)
      · exact Or.inl (Or.inr ⟨hη, w, rfl, hi⟩)
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h

/-- The mass of the accepted and of the rejected answers. -/
theorem frac_acc (hidx : 127 ≤ hashBits) (hM : P.numValid ≤ 2 ^ 127) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      (if idxOf w ∈ P.validSet then (1 : ℝ≥0∞) else 0) = (P.numValid : ℝ≥0∞) / 2 ^ 127 := by
  rw [← Finset.mul_sum, Finset.sum_boole, card_idxOf_mem _ (fun n hn => P.mem_validSet_lt hn),
    Nat.cast_mul, inv_card_mul_pow hidx, P.card_validSet]

theorem frac_split (w : BitVec hashBits) :
    (if idxOf w ∈ P.validSet then (1 : ℝ≥0∞) else 0) +
      (if idxOf w ∈ P.validSet then (0 : ℝ≥0∞) else 1) = 1 := by
  split_ifs <;> simp

/-- The mass of the answers whose index is held. -/
theorem frac_V (hidx : 127 ≤ hashBits) (d : Cache) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      (if idxOf w ∈ P.V d then (1 : ℝ≥0∞) else 0) = ((P.V d).card : ℝ≥0∞) / 2 ^ 127 := by
  rw [← Finset.mul_sum, Finset.sum_boole, card_idxOf_mem _ (P.V_lt d), Nat.cast_mul,
    inv_card_mul_pow hidx]

/-- The bound for a single trial: losing mass at most `ρ` times the trial's mass. -/
theorem trial_mass (d : Cache) (m : EMessage) (U : Finset Nonce) (ρ vf af rf : ℝ≥0∞)
    (hsplit : af + rf = 1) (hacc : P.rowAcc d m ⊆ U)
    (hρ : ((P.rowBad d m).card : ℝ≥0∞) + (U ∩ P.rowFresh d m).card * vf ≤
      ρ * ((P.rowAcc d m).card + (U ∩ P.rowFresh d m).card * af)) :
    ((P.rowBad d m).card : ℝ≥0∞) + (U ∩ P.rowRej d m).card * ρ +
        (U ∩ P.rowFresh d m).card * (vf + ρ * rf) ≤ ρ * U.card := by
  have hU : (U.card : ℝ≥0∞) = (P.rowAcc d m).card + (U ∩ P.rowRej d m).card +
      (U ∩ P.rowFresh d m).card := by
    rw [P.card_status d m U, Finset.inter_eq_right.2 hacc]
    push_cast; ring
  rw [hU]
  calc ((P.rowBad d m).card : ℝ≥0∞) + (U ∩ P.rowRej d m).card * ρ +
        (U ∩ P.rowFresh d m).card * (vf + ρ * rf)
      = (((P.rowBad d m).card : ℝ≥0∞) + (U ∩ P.rowFresh d m).card * vf) +
          (U ∩ P.rowRej d m).card * ρ + (U ∩ P.rowFresh d m).card * (ρ * rf) := by ring
    _ ≤ ρ * ((P.rowAcc d m).card + (U ∩ P.rowFresh d m).card * af) +
          (U ∩ P.rowRej d m).card * ρ + (U ∩ P.rowFresh d m).card * (ρ * rf) := by gcongr
    _ = ρ * ((P.rowAcc d m).card + (U ∩ P.rowRej d m).card +
          (U ∩ P.rowFresh d m).card * (af + rf)) := by ring
    _ = _ := by rw [hsplit, mul_one]

theorem ind_le_rowBad {d : Cache} {m : EMessage} {η : Nonce} {w : BitVec hashBits}
    (hi : idxOf w ∈ P.validSet) (hw : d (P.encQuery (m ++ η)) = some w) :
    (if ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × P.Idx)) = some (η', i) ∧
        P.IdxPre d (m ++ η') i.val then (1 : ℝ≥0∞) else 0) ≤
      if η ∈ P.rowBad d m then 1 else 0 := by
  by_cases h1 : ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × P.Idx)) =
      some (η', i) ∧ P.IdxPre d (m ++ η') i.val
  · rw [if_pos h1]
    obtain ⟨η', i, he, hpre⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [if_pos]
    simp only [Params.rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, hi, hpre⟩
  · rw [if_neg h1]; exact zero_le

set_option maxHeartbeats 4000000 in
/-- The signing loop as one disjoint case split: `k` further trials, nonces `tried` already
used, current cache `d'` differing from `d` only by rejected entries at tried nonces. The loop's
value, plus `λ ρ` when it fails, is at most `Φ d + κ b + λ ρ`. -/
theorem signRhoLoop_bound (hM' : P.numValid ≤ 2 ^ 127) (hidx : 127 ≤ hashBits)
    (m : EMessage) (d : Cache) {β J : Type} [Nonempty J]
    (kont : J → Option (Nonce × P.Idx) → OracleComp Spec β)
    (Fn : Option (Nonce × P.Idx) → Cache → ℝ≥0∞)
    (Φ : Cache → ℝ≥0∞) (hΦ : P.EncInvariant Φ) (κ lam ρ : ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hF : ∀ r d' b', P.SignExt m d r d' → I d' b' → (∀ j, CostAtMost (kont j r) b') →
      Fn r d' ≤ Φ d' + lam * (if ∃ η i, r = some (η, i) ∧ P.IdxPre d (m ++ η) i.val then 1 else 0) +
        κ * b')
    (hρ : ∀ c : ℕ, (P.rowFresh d m).card ≤ c + trials → c ≤ (P.rowFresh d m).card →
      ((P.rowBad d m).card : ℝ≥0∞) + c * (((P.V d).card : ℝ≥0∞) / 2 ^ 127) ≤
        ρ * ((P.rowAcc d m).card + c * ((P.numValid : ℝ≥0∞) / 2 ^ 127))) :
    ∀ (k : ℕ) (tried : Finset Nonce) (d' : Cache) (b : ℕ),
      Cache.Sub d d' →
      (∀ q w, d q = none → d' q = some w →
        ∃ η ∈ tried, q = P.encQuery (m ++ η) ∧ idxOf w ∉ P.validSet) →
      (∀ η ∈ tried, η ∉ P.rowAcc d m) →
      Φ d' = Φ d →
      tried.card + k ≤ trials →
      I d' b →
      (∀ j, CostAtMost (P.signIdxLoop m k tried >>= kont j) b) →
      E (run (P.signIdxLoop m k tried) d')
        (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0)) ≤
        Φ d + κ * b + lam * ρ := by
  -- the failing run
  have hnone : ∀ (d' : Cache) (b : ℕ) (tried : Finset Nonce), Cache.Sub d d' →
      (∀ q w, d q = none → d' q = some w →
        ∃ η ∈ tried, q = P.encQuery (m ++ η) ∧ idxOf w ∉ P.validSet) →
      Φ d' = Φ d → I d' b → (∀ j, CostAtMost (kont j none) b) →
      Fn none d' + (if (none : Option (Nonce × P.Idx)) = none then lam * ρ else 0) ≤
        Φ d + κ * b + lam * ρ := by
    intro d' b tried hSub hNew hΦd hI hB
    have h := hF none d' b (P.signExt_none hSub hNew) hI hB
    rw [hΦd, if_neg (P.not_exists_none), mul_zero, add_zero] at h
    rw [if_pos rfl]
    gcongr
  intro k
  induction k with
  | zero =>
    intro tried d' b hSub hNew hTried hΦd hcard hI hB
    rw [Params.signIdxLoop, run_pure, E_pure]
    simp only [Params.signIdxLoop, pure_bind] at hB
    exact hnone d' b tried hSub hNew hΦd hI hB
  | succ k ih =>
    intro tried d' b hSub hNew hTried hΦd hcard hI hB
    by_cases hc : 0 < (Finset.univ \ tried).card
    · simp only [P.signIdxLoop_succ m k tried hc] at hB ⊢
      have hB' : ∀ j i, CostAtMost (P.idxLoopBody m k tried (nonceOf tried hc i) >>= kont j) b :=
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
      set vf : ℝ≥0∞ := ((P.V d).card : ℝ≥0∞) / 2 ^ 127 with hvf
      set af : ℝ≥0∞ := (P.numValid : ℝ≥0∞) / 2 ^ 127 with haf
      set rf : ℝ≥0∞ := ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (if idxOf w ∈ P.validSet then (0 : ℝ≥0∞) else 1) with hrf
      have hsplit : af + rf = 1 := by
        rw [haf, ← P.frac_acc hidx hM', hrf, ← Finset.sum_add_distrib]
        simp_rw [← mul_add, frac_split]
        exact sum_inv_card_mul 1
      -- the value of one trial at an untried nonce
      let x : Nonce → ℝ≥0∞ := fun η =>
        (if η ∈ P.rowBad d m then 1 else 0) + (if η ∈ P.rowRej d m then ρ else 0) +
          (if η ∈ P.rowFresh d m then vf + ρ * rf else 0)
      have per : ∀ η ∈ Finset.univ \ tried,
          (∀ j, CostAtMost (P.idxLoopBody m k tried η >>= kont j) b) →
          E (run (P.idxLoopBody m k tried η) d')
            (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0)) ≤
            Φ d + κ * b + lam * x η := by
        intro η hη hBη
        have hηt : η ∉ tried := (Finset.mem_sdiff.1 hη).2
        have hins : (insert η tried).card + k ≤ trials := by
          rw [Finset.card_insert_of_notMem hηt]; omega
        have hBw : ∀ j w, CostAtMost (P.idxAfterHash m k tried η w >>= kont j)
            (b - queryCost (.inr (P.encQuery (m ++ η)))) :=
          fun j => (costAtMost_inr_bind _ _ _ (hBη j)).2
        have hcost : queryCost (.inr (P.encQuery (m ++ η))) ≤ b :=
          (costAtMost_inr_bind _ _ _ (hBη (Classical.arbitrary J))).1
        have hb₁ : ((b - queryCost (.inr (P.encQuery (m ++ η))) : ℕ) : ℝ≥0∞) ≤ b :=
          Nat.cast_le.2 (Nat.sub_le _ _)
        have hq : d' (P.encQuery (m ++ η)) = d (P.encQuery (m ++ η)) :=
          P.cache_eq_of_notMem hSub hNew hηt
        simp only [Params.idxLoopBody]
        rw [run_query_bind, E_bind]
        rcases hdq : d (P.encQuery (m ++ η)) with _ | w
        · -- fresh encoding query
          rw [hdq] at hq
          have hxη : x η = vf + ρ * rf := by
            have h1 : η ∉ P.rowBad d m := by
              simp only [Params.rowBad, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
            have h2 : η ∉ P.rowRej d m := by
              simp only [Params.rowRej, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
            have h3 : η ∈ P.rowFresh d m := by
              simp only [Params.rowFresh, Finset.mem_filter, Finset.mem_univ, true_and, hdq]
            simp only [x, if_neg h1, if_neg h2, if_pos h3, zero_add]
          rw [hxη, oracleImpl_run_inr_none hq, E_bind, E_uniform]
          simp only [E_pure]
          have hΦ' : ∀ w, Φ (d'.cacheQuery (P.encQuery (m ++ η)) w) = Φ d := fun w =>
            (hΦ d' (m ++ η) w).trans hΦd
          have hSub' : ∀ w, Cache.Sub d (d'.cacheQuery (P.encQuery (m ++ η)) w) := fun w =>
            hSub.trans (Cache.sub_cacheQuery_of_none hq w)
          have hηacc : η ∉ P.rowAcc d m := by
            simp only [Params.rowAcc, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
          have hTried' : ∀ η' ∈ insert η tried, η' ∉ P.rowAcc d m := by
            intro η' h'
            rcases Finset.mem_insert.1 h' with rfl | h'
            · exact hηacc
            · exact hTried η' h'
          have perw : ∀ w : BitVec hashBits,
              E (run (P.idxAfterHash m k tried η w) (d'.cacheQuery (P.encQuery (m ++ η)) w))
                (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0)) ≤
              Φ d + κ * b + lam * ((if idxOf w ∈ P.V d then 1 else 0) +
                (if idxOf w ∈ P.validSet then 0 else ρ)) := by
            intro w
            by_cases hi : idxOf w ∈ P.validSet
            · rw [Params.idxAfterHash, dif_pos hi, run_pure, E_pure, if_pos hi, add_zero]
              simp only [reduceCtorEq, if_false, add_zero]
              have hBk : ∀ j, CostAtMost (kont j (some (η, ⟨idxOf w, hi⟩)))
                  (b - queryCost (.inr (P.encQuery (m ++ η)))) := fun j => by
                have := hBw j w
                rwa [Params.idxAfterHash, dif_pos hi, pure_bind] at this
              refine (hF _ _ _ (P.signExt_fresh hSub hNew hi hq)
                (hI_fresh d' b _ hI hq hcost w) hBk).trans ?_
              rw [hΦ' w]
              calc _ ≤ Φ d + lam * (if idxOf w ∈ P.V d then 1 else 0) + κ * b := by
                    gcongr
                    · exact P.ind_le_V hi
                _ = _ := by ring
            · rw [Params.idxAfterHash, dif_neg hi, if_neg hi]
              have hBk : ∀ j, CostAtMost (P.signIdxLoop m k (insert η tried) >>= kont j)
                  (b - queryCost (.inr (P.encQuery (m ++ η)))) := fun j => by
                have := hBw j w
                rwa [Params.idxAfterHash, dif_neg hi] at this
              refine (ih (insert η tried) _ _ (hSub' w) (P.new_cacheQuery hNew η hi) hTried'
                (hΦ' w) hins (hI_fresh d' b _ hI hq hcost w) hBk).trans ?_
              calc _ ≤ Φ d + κ * b + lam * ρ := by gcongr
                _ ≤ _ := by gcongr; exact le_add_self
          calc ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                E (run (P.idxAfterHash m k tried η w) (d'.cacheQuery (P.encQuery (m ++ η)) w))
                  (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0))
              ≤ ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                  (Φ d + κ * b + lam * ((if idxOf w ∈ P.V d then 1 else 0) +
                    (if idxOf w ∈ P.validSet then 0 else ρ))) :=
                Finset.sum_le_sum fun w _ => mul_le_mul_right (perw w) _
            _ = Φ d + κ * b + lam * (vf + ρ * rf) := by
                have hρw : ∀ w : BitVec hashBits, (if idxOf w ∈ P.validSet then 0 else ρ) =
                    ρ * (if idxOf w ∈ P.validSet then (0 : ℝ≥0∞) else 1) := fun w => by
                  split_ifs <;> simp
                simp_rw [hρw, mul_add, Finset.sum_add_distrib, sum_inv_card_mul]
                rw [hvf, ← P.frac_V hidx d, hrf]
                simp only [Finset.mul_sum]
                refine congrArg (Φ d + κ * ↑b + ·) (congrArg₂ (· + ·) ?_ ?_) <;>
                  exact Finset.sum_congr rfl fun w _ => by ring
        · -- cached encoding query
          rw [hdq] at hq
          rw [oracleImpl_run_inr_some hq, E_pure]
          by_cases hi : idxOf w ∈ P.validSet
          · have hxη : x η = if η ∈ P.rowBad d m then 1 else 0 := by
              have h2 : η ∉ P.rowRej d m := by
                simp only [Params.rowRej, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simpa using hi
              have h3 : η ∉ P.rowFresh d m := by
                simp only [Params.rowFresh, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
              simp only [x, if_neg h2, if_neg h3, add_zero]
            rw [hxη, Params.idxAfterHash, dif_pos hi, run_pure, E_pure]
            simp only [reduceCtorEq, if_false, add_zero]
            have hBk : ∀ j, CostAtMost (kont j (some (η, ⟨idxOf w, hi⟩)))
                (b - queryCost (.inr (P.encQuery (m ++ η)))) := fun j => by
              have := hBw j w
              rwa [Params.idxAfterHash, dif_pos hi, pure_bind] at this
            refine (hF _ _ _ (P.signExt_cached hSub hNew hi hq)
              (hI_cached d' b _ hI (by simp [hq]) hcost) hBk).trans ?_
            rw [hΦd]
            calc _ ≤ Φ d + lam * (if η ∈ P.rowBad d m then 1 else 0) + κ * b := by
                  gcongr
                  · exact P.ind_le_rowBad hi hdq
              _ = _ := by ring
          · have hxη : x η = ρ := by
              have h1 : η ∉ P.rowBad d m := by
                simp only [Params.rowBad, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simpa using
                  fun h => absurd h hi
              have h2 : η ∈ P.rowRej d m := by
                simp only [Params.rowRej, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simpa using hi
              have h3 : η ∉ P.rowFresh d m := by
                simp only [Params.rowFresh, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simp
              simp only [x, if_neg h1, if_pos h2, if_neg h3, zero_add, add_zero]
            rw [hxη, Params.idxAfterHash, dif_neg hi]
            have hBk : ∀ j, CostAtMost (P.signIdxLoop m k (insert η tried) >>= kont j)
                (b - queryCost (.inr (P.encQuery (m ++ η)))) := fun j => by
              have := hBw j w
              rwa [Params.idxAfterHash, dif_neg hi] at this
            have hηacc : η ∉ P.rowAcc d m := by
              simp only [Params.rowAcc, Finset.mem_filter, Finset.mem_univ, true_and, hdq]; simpa using hi
            have hTried' : ∀ η' ∈ insert η tried, η' ∉ P.rowAcc d m := by
              intro η' h'
              rcases Finset.mem_insert.1 h' with rfl | h'
              · exact hηacc
              · exact hTried η' h'
            refine (ih (insert η tried) d' _ hSub (P.new_insert hNew η) hTried' hΦd hins
              (hI_cached d' b _ hI (by simp [hq]) hcost) hBk).trans ?_
            gcongr
      -- average over the nonce
      have hacc : P.rowAcc d m ⊆ Finset.univ \ tried := by
        intro η hη
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => hTried η h hη⟩
      have hbad : (Finset.univ \ tried) ∩ P.rowBad d m = P.rowBad d m :=
        Finset.inter_eq_right.2 ((P.rowBad_subset d m).trans hacc)
      have hsum : ∑ η ∈ Finset.univ \ tried, x η =
          ((P.rowBad d m).card : ℝ≥0∞) + ((Finset.univ \ tried) ∩ P.rowRej d m).card * ρ +
            ((Finset.univ \ tried) ∩ P.rowFresh d m).card * (vf + ρ * rf) := by
        simp only [x]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.sum_ite_mem, Finset.sum_const, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
          nsmul_eq_mul, nsmul_eq_mul, mul_one, hbad]
      have hfreshcard : (P.rowFresh d m).card ≤
          ((Finset.univ \ tried) ∩ P.rowFresh d m).card + trials := by
        have h1 : P.rowFresh d m ⊆ ((Finset.univ \ tried) ∩ P.rowFresh d m) ∪ tried := by
          intro η hη
          by_cases ht : η ∈ tried
          · exact Finset.mem_union_right _ ht
          · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨Finset.mem_sdiff.2
              ⟨Finset.mem_univ _, ht⟩, hη⟩)
        have := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
        omega
      have hmass := P.trial_mass d m (Finset.univ \ tried) ρ vf af rf hsplit hacc
        (hρ _ hfreshcard (Finset.card_le_card Finset.inter_subset_right))
      rw [← hsum] at hmass
      have hstep1 : ∀ j : Fin ((Finset.univ \ tried).card - 1 + 1),
          ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            E (run (P.idxLoopBody m k tried (nonceOf tried hc j)) d')
              (fun p => Fn p.1 p.2 + (if p.1 = none then lam * ρ else 0)) ≤
          ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            (Φ d + κ * b + lam * x (nonceOf tried hc j)) :=
        fun j => mul_le_mul_right (per _ (nonceOf_mem tried hc j) (fun i => hB' i j)) _
      have hstep2 := sum_fin_equivFin hcast fun η =>
        ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * (Φ d + κ * b + lam * x η)
      calc ∑ j, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            E (run (P.idxLoopBody m k tried (nonceOf tried hc j)) d')
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
    · rw [Params.signIdxLoop, dif_neg hc, run_pure, E_pure]
      simp only [Params.signIdxLoop, dif_neg hc, pure_bind] at hB
      exact hnone d' b tried hSub hNew hΦd hI hB

/-- **The signing bound, as one disjoint case split.** -/
theorem signRho_bound (hM' : P.numValid ≤ 2 ^ 127) (hidx : 127 ≤ hashBits)
    (m : EMessage) (d : Cache) {β J : Type} [Nonempty J]
    (k : J → Option (Nonce × P.Idx) → OracleComp Spec β)
    (Fn : Option (Nonce × P.Idx) → Cache → ℝ≥0∞)
    (Φ : Cache → ℝ≥0∞) (hΦ : P.EncInvariant Φ) (κ lam ρ : ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hF : ∀ r d' b', P.SignExt m d r d' → I d' b' → (∀ j, CostAtMost (k j r) b') →
      Fn r d' ≤ Φ d' + lam * (if ∃ η i, r = some (η, i) ∧ P.IdxPre d (m ++ η) i.val then 1 else 0) +
        κ * b')
    (hρ : ∀ c : ℕ, (P.rowFresh d m).card ≤ c + trials → c ≤ (P.rowFresh d m).card →
      ((P.rowBad d m).card : ℝ≥0∞) + c * (((P.V d).card : ℝ≥0∞) / 2 ^ 127) ≤
        ρ * ((P.rowAcc d m).card + c * ((P.numValid : ℝ≥0∞) / 2 ^ 127)))
    {b : ℕ} (hI : I d b) (hB : ∀ j, CostAtMost (P.signIdx m >>= k j) b) :
    E (run (P.signIdx m) d) (fun p => Fn p.1 p.2) ≤ Φ d + lam * ρ + κ * b := by
  have h := P.signRhoLoop_bound hM' hidx m d k Fn Φ hΦ κ lam ρ I hI_fresh hI_cached hF hρ
    trials ∅ d b (Cache.Sub.refl d) (fun q w h1 h2 => by rw [h1] at h2; cases h2)
    (fun η h => by simp at h) rfl (by simp) hI hB
  refine (E_mono _ fun p => le_self_add).trans (h.trans (le_of_eq ?_))
  ring


end Params

end OptimalOTS.LeanIsaBaseline.Layer
