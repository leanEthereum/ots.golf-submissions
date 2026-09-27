import Submissions.UpperCompressions.LongChain91LargeHazard
import Submissions.UpperCompressions.ProofBundle13

/-!
# Terminal large-hazard event for the cost-91 construction

The row hazard theorem stops on a row-dependent collision event.  This file
contains the missing varying-kill union argument: a terminal union is charged
to each row's hit-before-its-own-kill probability and to one crossing of the
union of all kills.  The latter is split into the common empirical, budget,
and diagonal events and one joint self-collision/occupancy event.
-/

noncomputable section

open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal

namespace WeightedOracleExecution

variable { ι S α I : Type } {spec : OracleSpec ι} [spec.Inhabited]

/-- A larger killing predicate stops earlier and therefore has no larger
hit-before-kill probability. -/
theorem firstHitRun_kill_antitone
    (impl : QueryImpl spec (StateT S ProbComp)) (hit : ℕ → S → Prop)
    (kill₁ kill₂ : ℕ → S → Prop)
    (hsub : ∀ n s, kill₁ n s → kill₂ n s)
    (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[= true | firstHitRun impl hit kill₂ oa t s] ≤
      Pr[= true | firstHitRun impl hit kill₁ oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure a => simp
  | query_bind q k ih =>
      by_cases hh : hit t s
      · simp [firstHitRun_query_bind, hh]
      · by_cases hk₂ : kill₂ t s
        · simp [firstHitRun_query_bind, hh, hk₂]
        · have hk₁ : ¬ kill₁ t s := fun h => hk₂ (hsub t s h)
          simp only [firstHitRun_query_bind, hh, hk₁, hk₂, if_false,
            probOutput_bind_eq_expectedValue]
          apply expectedValue_mono
          intro out
          exact ih out.1 (t + 1) out.2

/-- A crossing of `(some target) or common kill` is bounded by the target
hits before that common kill plus one crossing of the kill itself. -/
theorem firstHitRun_union_or_kill_le [Fintype I]
    (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (kill : ℕ → S → Prop)
    (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[= true | firstHitRun impl
        (fun n s => (∃ i, hit i n s) ∨ kill n s)
        (fun _ _ => False) oa t s] ≤
      (∑ i, Pr[= true | firstHitRun impl (hit i) kill oa t s]) +
      Pr[= true | firstHitRun impl kill (fun _ _ => False) oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure a =>
      by_cases hh : ∃ i, hit i t s
      · obtain ⟨i, hi⟩ := hh
        have hone : Pr[= true | firstHitRun impl (hit i) kill
            (pure a) t s] = 1 := by simp [hi]
        have hsum := Finset.single_le_sum (s := Finset.univ)
          (f := fun j : I =>
            Pr[= true | firstHitRun impl (hit j) kill (pure a) t s])
          (fun j _ => zero_le) (Finset.mem_univ i)
        rw [hone] at hsum
        have hall : Pr[= true | firstHitRun impl
            (fun n s => (∃ i, hit i n s) ∨ kill n s)
            (fun _ _ => False) (pure a) t s] = 1 := by
          simp [show ∃ j, hit j t s from ⟨i, hi⟩]
        rw [hall]
        exact hsum.trans le_self_add
      · by_cases hk : kill t s
        · have hone : Pr[= true | firstHitRun impl kill
              (fun _ _ => False) (pure a) t s] = 1 := by simp [hk]
          have hall : Pr[= true | firstHitRun impl
              (fun n s => (∃ i, hit i n s) ∨ kill n s)
              (fun _ _ => False) (pure a) t s] = 1 := by simp [hh, hk]
          rw [hall, hone]
          exact le_add_self
        · simp [hh, hk]
  | query_bind q k ih =>
      by_cases hh : ∃ i, hit i t s
      · obtain ⟨i, hi⟩ := hh
        have hone : Pr[= true | firstHitRun impl (hit i) kill
            ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k)
            t s] = 1 := by
          rw [firstHitRun_of_hit _ _ _ _ _ _ hi]
          simp
        have hsum := Finset.single_le_sum (s := Finset.univ)
          (f := fun j : I => Pr[= true | firstHitRun impl (hit j) kill
            ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k)
            t s]) (fun j _ => zero_le) (Finset.mem_univ i)
        rw [hone] at hsum
        exact (probOutput_le_one).trans (hsum.trans le_self_add)
      · have hnone : ∀ i, ¬ hit i t s := fun i hi => hh ⟨i, hi⟩
        by_cases hk : kill t s
        · have hone : Pr[= true | firstHitRun impl kill
              (fun _ _ => False)
              ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k)
              t s] = 1 := by
            rw [firstHitRun_of_hit _ _ _ _ _ _ hk]
            simp
          rw [hone]
          exact (probOutput_le_one).trans le_add_self
        · simp only [firstHitRun_query_bind, hh, hk, hnone, exists_false,
            or_false, if_false, probOutput_bind_eq_expectedValue]
          rw [← expectedValue_finsetSum, ← expectedValue_add]
          apply expectedValue_mono
          intro out
          exact ih out.1 (t + 1) out.2

end WeightedOracleExecution

namespace OptimalOTS.WeightedConstruction.LongChain91LargeTerminal

open WeightedCacheCounts WeightedOracleExecution
open LongChain91Security LongChain91Empirical LongChain91StoppedCollision
open LongChain91CollisionArithmetic LongChain91DiagonalClock
open LongChain91LargeHazard

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem sum_bool_values {α : Type} [AddCommMonoid α] (f : Bool → α) :
    (∑ b : Bool, f b) = f false + f true := by
  classical
  change Finset.univ.sum f = _
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  simp

/-! ## Terminal predicate and kill cover -/

def LargeBad (B : ℕ) (c : hashSpec.QueryCache) : Prop :=
  ∃ m : Message,
    tightAlpha * (LongChain91LargeHazard.globalCount c : ℝ) +
      largeDeviation (B : ℝ) ≤
      hazard m c

def occupancyBad (c : hashSpec.QueryCache) : Prop :=
  ¬ AllRowsOccupancyGood c

def sharedBad (B : ℕ) (c : hashSpec.QueryCache) : Prop :=
  ¬ LongChain91Empirical.Good c ∨
  B < LongChain91LargeHazard.globalCount c ∨
  diagonalBoundary (B : ℝ) c

def selfOrOccupancyBad (B : ℕ) (c : hashSpec.QueryCache) : Prop :=
  (∃ m : Message, selfHit (B : ℝ) m 0 c) ∨ occupancyBad c

def killCover (B : ℕ) (c : hashSpec.QueryCache) : Prop :=
  sharedBad B c ∨ selfOrOccupancyBad B c

theorem diagonal_failure_covered (B : ℕ) (c : hashSpec.QueryCache)
    (h : ¬ diagonalGood (B : ℝ) c) :
    B < LongChain91LargeHazard.globalCount c ∨
      diagonalBoundary (B : ℝ) c := by
  by_cases hqNat : B < LongChain91LargeHazard.globalCount c
  · exact Or.inl hqNat
  · right
    have hq : (LongChain91LargeHazard.globalCount c : ℝ) ≤ (B : ℝ) := by
      exact Nat.cast_le.mpr (Nat.le_of_not_gt hqNat)
    change (LongChain91DiagonalClock.globalCount c : ℝ) ≤ (B : ℝ) at hq
    have hmean := mul_le_mul collisionWeights_mean_le hq
      (Nat.cast_nonneg _) diagonalRate_pos.le
    have hD : (3 / 2 : ℝ) * diagonalRate * (B : ℝ) < Dglobal c := by
      exact lt_of_not_ge h
    unfold diagonalBoundary
    rw [max_eq_right hq, collisionWeights_M1]
    unfold diagonalDelta
    nlinarith

theorem occupancyKill_implies_bad (m : Message) (c : hashSpec.QueryCache)
    (h : occupancyKill m 0 c) : occupancyBad c := by
  intro hall
  exact h (hall m)

theorem largeKill_union_covered (B : ℕ) (c : hashSpec.QueryCache)
    (h : ∃ m : Message, largeKill (B : ℝ) m 0 c) :
    killCover B c := by
  obtain ⟨m, hm⟩ := h
  rcases hm with he | hq | hD | hX | hO
  · exact Or.inl (Or.inl he)
  · exact Or.inl (Or.inr (Or.inl (Nat.cast_lt.mp hq)))
  · rcases diagonal_failure_covered B c hD with hc | hc
    · exact Or.inl (Or.inr (Or.inl hc))
    · exact Or.inl (Or.inr (Or.inr hc))
  · exact Or.inr (Or.inl ⟨m, hX⟩)
  · exact Or.inr (Or.inr (occupancyKill_implies_bad m c hO))

/-! ## Occupancy is persistent on a growing lazy-oracle cache -/

theorem classCounts_le_of_sub (A : Finset Query)
    (c d : hashSpec.QueryCache) (hcd : Cache.Sub c d)
    (decode : BitVec hashBits → Option (Fin LongChain91Security.M))
    (i : Fin LongChain91Security.M) :
    classCounts A c decode i ≤ classCounts A d decode i := by
  unfold classCounts WeightedPublicCounts.counts
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqSeen, hdecode⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqA, hcSome⟩ := Finset.mem_filter.mp hqSeen
  cases hcq : c q with
  | none => simp [hcq] at hcSome
  | some u =>
      have hdq : d q = some u := hcd q u hcq
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_filter.mpr ⟨hqA, by simp [hdq]⟩
      · simpa only [hcq, hdq, Option.bind_some] using hdecode

theorem occupancyBad_mono {c d : hashSpec.QueryCache}
    (hcd : Cache.Sub c d) : occupancyBad c → occupancyBad d := by
  intro hc hd
  apply hc
  intro m i
  exact (classCounts_le_of_sub (WideDomains.rowDomain m) c d hcd
    LongChain91Empirical.cacheDecode i).trans (hd m i)

/-- A persistent state predicate has crossing probability at most its terminal
probability. -/
theorem firstHitRun_persistent_le_terminal
    {S β : Type} (impl : QueryImpl OptimalOTS.Spec (StateT S ProbComp))
    (bad : S → Prop)
    (hpersist : ∀ (oa : OracleComp OptimalOTS.Spec β) s out,
      out ∈ support ((simulateQ impl oa).run s) → bad s → bad out.2)
    (oa : OracleComp OptimalOTS.Spec β) (t : ℕ) (s : S) :
    Pr[= true | firstHitRun impl (fun _ s => bad s)
        (fun _ _ => False) oa t s] ≤
      Pr[fun out => bad out.2 | (simulateQ impl oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure a => by_cases h : bad s <;> simp [h]
  | query_bind q k ih =>
      by_cases h : bad s
      · apply (probOutput_le_one).trans
        have hone : (1 : ℝ≥0∞) ≤
            Pr[fun out => bad out.2 |
              (simulateQ impl
                ((liftM (OptimalOTS.Spec.query q) :
                  OracleComp OptimalOTS.Spec (OptimalOTS.Spec.Range q)) >>= k)).run s] := by
          simpa using (probEvent_mono (mx := (simulateQ impl
            ((liftM (OptimalOTS.Spec.query q) :
              OracleComp OptimalOTS.Spec (OptimalOTS.Spec.Range q)) >>= k)).run s)
            (fun out hout (_ : True) => hpersist _ s out hout h))
        exact hone
      · simp only [firstHitRun_query_bind, h, if_false, simulateQ_bind,
          simulateQ_spec_query, StateT.run_bind, probOutput_bind_eq_expectedValue,
          probEvent_bind_eq_expectedValue]
        apply expectedValue_mono
        intro out
        exact ih out.1 (t + 1) out.2

theorem occupancy_crossing_le_terminal { β : Type }
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache) :
    Pr[= true | firstHitRun oracleImpl (fun _ c => occupancyBad c)
        (fun _ _ => False) oa 0 initial] ≤
      Pr[fun out => occupancyBad out.2 |
        (simulateQ oracleImpl oa).run initial] := by
  apply firstHitRun_persistent_le_terminal
  intro ob c out hout hbad
  exact occupancyBad_mono (OptimalOTS.sub_of_mem_support_run ob c out hout) hbad

theorem occupancy_terminal_bound { β : Type }
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[fun out => occupancyBad out.2 |
        (simulateQ oracleImpl oa).run initial] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  have h := actual_allRows_occupancy_failure_probability oa initial hfresh
  rw [← expectedValue_ite_one]
  have h' : expectedValue ((simulateQ oracleImpl oa).run initial)
      (fun out => if ¬ AllRowsOccupancyGood out.2 then (1 : ℝ≥0∞) else 0) ≤
        (2 : ℝ≥0∞)⁻¹ ^ 334 := by
    simpa only [OptimalOTS.run, OptimalOTS.E] using h
  have hfun :
      (fun out : β × hashSpec.QueryCache =>
        if occupancyBad out.2 then (1 : ℝ≥0∞) else 0) =
      (fun out : β × hashSpec.QueryCache =>
        if ¬ AllRowsOccupancyGood out.2 then (1 : ℝ≥0∞) else 0) := by
    funext out
    by_cases hg : AllRowsOccupancyGood out.2 <;> simp [occupancyBad, hg]
  rw [hfun]
  exact h'

theorem occupancy_crossing_bound { β : Type }
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl (fun _ c => occupancyBad c)
        (fun _ _ => False) oa 0 initial] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 334 :=
  (occupancy_crossing_le_terminal oa initial).trans
    (occupancy_terminal_bound oa initial hfresh)

/-! ## Shared empirical, count, and diagonal crossings -/

def eps244 : ℝ≥0∞ := ENNReal.ofReal (((2 : ℝ)^244)⁻¹)

theorem inverse_pow_mono (n : ℕ) (hn : 244 ≤ n) :
    ENNReal.ofReal (((2 : ℝ)^n)⁻¹) ≤ eps244 := by
  unfold eps244
  apply ENNReal.ofReal_le_ofReal
  apply (inv_le_inv₀ (by positivity) (by positivity)).2
  exact pow_le_pow_right₀ (by norm_num) hn

theorem empirical_crossing_bound { β : Type }
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl
        (fun _ c => ¬ LongChain91Empirical.Good c)
        (fun _ _ => False) oa 0 initial] ≤ eps244 := by
  have h := LongChain91Empirical.all_crossings oa initial hfresh
  unfold LongChain91Empirical.crossing at h
  rw [prob_stopped_hit_eq_firstHitRun] at h
  have he : (fun (_ : ℕ) c => ¬ LongChain91Empirical.Good c) =
      (fun _ c => ∃ i : LongChain91Empirical.BadIndex,
        LongChain91Empirical.event i c) := by
    funext n c
    simp only [LongChain91Empirical.Good, not_forall, not_not]
  rw [he]
  exact h.trans (inverse_pow_mono 512 (by omega))

theorem seen_card_le_of_sub (A : Finset Query)
    (c d : hashSpec.QueryCache) (hcd : Cache.Sub c d) :
    (seen A c).card ≤ (seen A d).card := by
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqA, hc⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hqA, hcd.isSome hc⟩

theorem countBad_mono (B : ℕ) {c d : hashSpec.QueryCache}
    (hcd : Cache.Sub c d) :
    B < LongChain91LargeHazard.globalCount c →
      B < LongChain91LargeHazard.globalCount d := by
  intro h
  exact h.trans_le (seen_card_le_of_sub WideDomains.indexDomain c d hcd)

theorem count_crossing_zero { β : Type }
    (B : ℕ) (oa : OracleComp Spec β) (hbudget : CostAtMost oa B)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl
        (fun _ c => B < LongChain91LargeHazard.globalCount c)
        (fun _ _ => False)
        oa 0 initial] = 0 := by
  apply le_antisymm
  · refine (firstHitRun_persistent_le_terminal oracleImpl
      (fun c => B < LongChain91LargeHazard.globalCount c)
        (fun ob c out hout hbad =>
          countBad_mono B (OptimalOTS.sub_of_mem_support_run ob c out hout)
            hbad)
      oa 0 initial).trans ?_
    calc
      Pr[fun out => B < LongChain91LargeHazard.globalCount out.2 |
          (simulateQ oracleImpl oa).run initial] ≤
        Pr[fun _ => False | (simulateQ oracleImpl oa).run initial] := by
          apply probEvent_mono
          intro out hout hbad
          have hb := LongChain91SmallMoments.queryCount_le_budget_on_support
            oa B hbudget initial hfresh out hout
          have hb' : LongChain91LargeHazard.globalCount out.2 ≤ B := by
            simpa only [LongChain91LargeHazard.globalCount,
              LongChain91SmallMoments.queryCount] using hb
          exact (not_lt_of_ge hb') hbad
      _ = 0 := by simp
  · exact bot_le

theorem diagonal_crossing_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl
        (fun _ c => diagonalBoundary (B : ℝ) c)
        (fun _ _ => False) oa 0 initial] ≤ eps244 := by
  have h := global_diagonal_crossing_dyadic oa (B : ℝ) hlarge
    initial hfresh
  unfold LongChain91Empirical.crossing at h
  rw [prob_stopped_hit_eq_firstHitRun] at h
  apply h.trans
  have he1024 : (2 : ℝ≥0∞)⁻¹ ^ 1024 =
      ENNReal.ofReal (((2 : ℝ)^1024)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos
        (by positivity : (0 : ℝ) < (2 : ℝ)^1024),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  rw [he1024]
  exact inverse_pow_mono 1024 (by omega)

def concentrationEvent (B : ℕ) : Bool → ℕ → hashSpec.QueryCache → Prop
  | false => fun _ c => ¬ LongChain91Empirical.Good c
  | true => fun _ c => diagonalBoundary (B : ℝ) c

theorem concentration_union_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl
        (fun n c => ∃ i : Bool, concentrationEvent B i n c)
        (fun _ _ => False) oa 0 initial] ≤ 2 * eps244 := by
  apply (firstHitRun_union_le oracleImpl (concentrationEvent B)
    oa 0 initial).trans
  rw [sum_bool_values]
  calc
    _ ≤ eps244 + eps244 := by
      simpa only [concentrationEvent] using add_le_add
        (empirical_crossing_bound oa initial hfresh)
        (diagonal_crossing_bound B hlarge oa initial hfresh)
    _ = 2 * eps244 := by ring

def sharedEvent (B : ℕ) : Bool → ℕ → hashSpec.QueryCache → Prop
  | false => fun _ c => B < LongChain91LargeHazard.globalCount c
  | true => fun n c => ∃ i : Bool, concentrationEvent B i n c

theorem shared_event_eq (B : ℕ) (n : ℕ) (c : hashSpec.QueryCache) :
    (∃ i : Bool, sharedEvent B i n c) ↔ sharedBad B c := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | false => exact Or.inr (Or.inl hi)
    | true =>
        obtain ⟨j, hj⟩ := hi
        cases j with
        | false => exact Or.inl hj
        | true => exact Or.inr (Or.inr hj)
  · rintro (he | hq | hD)
    · exact ⟨true, false, he⟩
    · exact ⟨false, hq⟩
    · exact ⟨true, true, hD⟩

theorem shared_crossing_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (hbudget : CostAtMost oa B)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl (fun _ c => sharedBad B c)
        (fun _ _ => False) oa 0 initial] ≤ 2 * eps244 := by
  have hu := firstHitRun_union_le oracleImpl (sharedEvent B) oa 0 initial
  have he : (fun n c => ∃ i : Bool, sharedEvent B i n c) =
      (fun _ c => sharedBad B c) := by
    funext n c
    exact propext (shared_event_eq B n c)
  rw [he] at hu
  apply hu.trans
  rw [sum_bool_values]
  simp only [sharedEvent]
  rw [count_crossing_zero B oa hbudget initial hfresh, zero_add]
  exact concentration_union_bound B hlarge oa initial hfresh

/-! ## Selected-row self-collision and occupancy -/

theorem self_collision_exponent (B : ℝ) (hlarge : N / 64 ≤ B) :
    (500 : ℝ) ≤
      (selfDeviation B)^2 /
        (2 * (selfVariance B +
          LongChain91CollisionCap.collisionJumpBound *
            selfDeviation B / 3)) := by
  have hN : 0 < N := by unfold N; positivity
  have hB : 0 < B := lt_of_lt_of_le (div_pos hN (by norm_num)) hlarge
  have hden : 0 < 2 * (selfVariance B +
      LongChain91CollisionCap.collisionJumpBound *
        selfDeviation B / 3) := by
    have hv := selfVariance_pos hB
    have hJ := LongChain91CollisionCap.collisionJumpBound_nonneg
    have ha := selfDeviation_pos hB
    positivity
  apply (le_div_iff₀ hden).2
  norm_num [selfDeviation, selfVariance, diagonalRate,
    LongChain91CollisionCap.collisionJumpBound,
    collisionScale, N, Chain18Compact.L, Chain18Compact.kappa]
    at hlarge ⊢
  nlinarith

theorem self_row_crossing_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (m : Message) (oa : OracleComp Spec β)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl (selfHit (B : ℝ) m)
        (occupancyKill m) oa 0 initial] ≤
      ENNReal.ofReal (Real.exp (-(500 : ℝ))) := by
  have h := actual_stopped_self_collision (B : ℝ) hlarge m oa
    initial hfresh
  rw [prob_stopped_hit_eq_firstHitRun] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using
    neg_le_neg (self_collision_exponent (B : ℝ) hlarge)

theorem self_message_union_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    (∑ m : Message,
      Pr[= true | firstHitRun oracleImpl (selfHit (B : ℝ) m)
        (occupancyKill m) oa 0 initial]) ≤ eps244 := by
  calc
    _ ≤ ∑ _m : Message, ENNReal.ofReal (Real.exp (-(500 : ℝ))) :=
      Finset.sum_le_sum (fun m _ =>
        self_row_crossing_bound B hlarge m oa initial hfresh)
    _ = (Fintype.card Message : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(500 : ℝ))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ENNReal.ofReal
        ((2 : ℝ)^256 * Real.exp (-(500 : ℝ))) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num [Message, msgBits, Fintype.card_bitVec]
    _ ≤ eps244 := by
      unfold eps244
      exact ENNReal.ofReal_le_ofReal message_union_margin

theorem row_occupancyKill_implies_allRowsBad (m : Message)
    (n : ℕ) (c : hashSpec.QueryCache) :
    occupancyKill m n c → occupancyBad c := by
  intro h hall
  exact h (hall m)

theorem self_before_common_occupancy_le { β : Type }
    (B : ℕ) (m : Message) (oa : OracleComp Spec β)
    (initial : hashSpec.QueryCache) :
    Pr[= true | firstHitRun oracleImpl (selfHit (B : ℝ) m)
        (fun _ c => occupancyBad c) oa 0 initial] ≤
      Pr[= true | firstHitRun oracleImpl (selfHit (B : ℝ) m)
        (occupancyKill m) oa 0 initial] := by
  exact firstHitRun_kill_antitone oracleImpl (selfHit (B : ℝ) m)
    (occupancyKill m) (fun _ c => occupancyBad c)
    (row_occupancyKill_implies_allRowsBad m) oa 0 initial

theorem self_occupancy_crossing_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl
        (fun _ c => selfOrOccupancyBad B c)
        (fun _ _ => False) oa 0 initial] ≤
      eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  have h := firstHitRun_union_or_kill_le oracleImpl
    (fun m : Message => selfHit (B : ℝ) m)
    (fun _ c => occupancyBad c) oa 0 initial
  have hfun :
      (fun n c => (∃ m : Message, selfHit (B : ℝ) m n c) ∨
        occupancyBad c) = (fun _ c => selfOrOccupancyBad B c) := by
    funext n c
    rfl
  rw [hfun] at h
  apply h.trans
  calc
    (∑ m : Message, Pr[= true | firstHitRun oracleImpl
          (selfHit (B : ℝ) m) (fun _ c => occupancyBad c)
          oa 0 initial]) +
        Pr[= true | firstHitRun oracleImpl (fun _ c => occupancyBad c)
          (fun _ _ => False) oa 0 initial] ≤
      (∑ m : Message, Pr[= true | firstHitRun oracleImpl
          (selfHit (B : ℝ) m) (occupancyKill m)
          oa 0 initial]) +
        Pr[= true | firstHitRun oracleImpl (fun _ c => occupancyBad c)
          (fun _ _ => False) oa 0 initial] := by
            exact add_le_add
              (Finset.sum_le_sum (fun m _ =>
                self_before_common_occupancy_le B m oa initial)) le_rfl
    _ ≤ eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334 :=
      add_le_add (self_message_union_bound B hlarge oa initial hfresh)
        (occupancy_crossing_bound oa initial hfresh)

def coverEvent (B : ℕ) : Bool → ℕ → hashSpec.QueryCache → Prop
  | false => fun _ c => sharedBad B c
  | true => fun _ c => selfOrOccupancyBad B c

theorem cover_event_eq (B : ℕ) (n : ℕ) (c : hashSpec.QueryCache) :
    (∃ i : Bool, coverEvent B i n c) ↔ killCover B c := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩

theorem killCover_crossing_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (hbudget : CostAtMost oa B)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl (fun _ c => killCover B c)
        (fun _ _ => False) oa 0 initial] ≤
      3 * eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  have hu := firstHitRun_union_le oracleImpl (coverEvent B) oa 0 initial
  have he : (fun n c => ∃ i : Bool, coverEvent B i n c) =
      (fun _ c => killCover B c) := by
    funext n c
    exact propext (cover_event_eq B n c)
  rw [he] at hu
  apply hu.trans
  rw [sum_bool_values]
  have hs := shared_crossing_bound B hlarge oa hbudget initial hfresh
  have hx := self_occupancy_crossing_bound B hlarge oa initial hfresh
  calc
    _ ≤ 2 * eps244 +
        (eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334) := add_le_add hs hx
    _ = 3 * eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334 := by ring

/-! ## Terminal all-message hazard -/

theorem main_row_crossing_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (m : Message) (oa : OracleComp Spec β)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[= true | firstHitRun oracleImpl (largeHit (B : ℝ) m)
        (largeKill (B : ℝ) m) oa 0 initial] ≤
      ENNReal.ofReal (Real.exp (-(500 : ℝ))) := by
  have h := actual_stopped_large_hazard (B : ℝ) hlarge m oa
    initial hfresh
  rw [prob_stopped_hit_eq_firstHitRun] at h
  exact h

theorem main_message_union_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    (∑ m : Message,
      Pr[= true | firstHitRun oracleImpl (largeHit (B : ℝ) m)
        (largeKill (B : ℝ) m) oa 0 initial]) ≤ eps244 := by
  calc
    _ ≤ ∑ _m : Message, ENNReal.ofReal (Real.exp (-(500 : ℝ))) :=
      Finset.sum_le_sum (fun m _ =>
        main_row_crossing_bound B hlarge m oa initial hfresh)
    _ = (Fintype.card Message : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(500 : ℝ))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ENNReal.ofReal
        ((2 : ℝ)^256 * Real.exp (-(500 : ℝ))) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num [Message, msgBits, Fintype.card_bitVec]
    _ ≤ eps244 := by
      unfold eps244
      exact ENNReal.ofReal_le_ofReal message_union_margin

theorem row_largeKill_implies_cover (B : ℕ) (m : Message)
    (n : ℕ) (c : hashSpec.QueryCache) :
    largeKill (B : ℝ) m n c → killCover B c := by
  intro h
  exact largeKill_union_covered B c ⟨m, by simpa only [largeKill] using h⟩

theorem main_before_cover_le { β : Type }
    (B : ℕ) (m : Message) (oa : OracleComp Spec β)
    (initial : hashSpec.QueryCache) :
    Pr[= true | firstHitRun oracleImpl
        (fun _ c => largeHit (B : ℝ) m 0 c)
        (fun _ c => killCover B c) oa 0 initial] ≤
      Pr[= true | firstHitRun oracleImpl
        (largeHit (B : ℝ) m) (largeKill (B : ℝ) m)
        oa 0 initial] := by
  have h := firstHitRun_kill_antitone oracleImpl
    (largeHit (B : ℝ) m) (largeKill (B : ℝ) m)
    (fun _ c => killCover B c) (row_largeKill_implies_cover B m)
    oa 0 initial
  have hhit : (fun _ c => largeHit (B : ℝ) m 0 c) =
      largeHit (B : ℝ) m := by
    funext n c
    rfl
  rw [hhit]
  exact h

theorem terminal_hits_or_cover_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (hbudget : CostAtMost oa B)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[fun out =>
        (∃ m : Message, largeHit (B : ℝ) m 0 out.2) ∨
          killCover B out.2 |
        (simulateQ oracleImpl oa).run initial] ≤
      4 * eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  have h := terminal_union_or_kill_le_stopped oracleImpl
    (fun m : Message => largeHit (B : ℝ) m 0)
    (killCover B) oa 0 initial
  apply h.trans
  have hm :
      (∑ m : Message, Pr[= true | firstHitRun oracleImpl
        (fun _ c => largeHit (B : ℝ) m 0 c)
        (fun _ c => killCover B c) oa 0 initial]) ≤ eps244 := by
    calc
      _ ≤ ∑ m : Message, Pr[= true | firstHitRun oracleImpl
          (largeHit (B : ℝ) m) (largeKill (B : ℝ) m)
          oa 0 initial] := Finset.sum_le_sum (fun m _ =>
            main_before_cover_le B m oa initial)
      _ ≤ eps244 := main_message_union_bound B hlarge oa initial hfresh
  have hk := killCover_crossing_bound B hlarge oa hbudget initial hfresh
  calc
    _ ≤ eps244 +
        (3 * eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334) :=
      add_le_add hm hk
    _ = 4 * eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334 := by ring

theorem largeBad_implies_hit_of_support { β : Type }
    (B : ℕ) (oa : OracleComp Spec β) (hbudget : CostAtMost oa B)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none)
    (out : β × hashSpec.QueryCache)
    (hout : out ∈ support ((simulateQ oracleImpl oa).run initial))
    (hbad : LargeBad B out.2) :
    ∃ m : Message, largeHit (B : ℝ) m 0 out.2 := by
  obtain ⟨m, hm⟩ := hbad
  have hqNat := LongChain91SmallMoments.queryCount_le_budget_on_support
    oa B hbudget initial hfresh out hout
  have hq : (LongChain91LargeHazard.globalCount out.2 : ℝ) ≤
      (B : ℝ) := by
    exact Nat.cast_le.mpr hqNat
  refine ⟨m, hq, ?_⟩
  unfold Z
  linarith

def LargeGood (B : ℕ) (c : hashSpec.QueryCache) : Prop :=
  LongChain91Empirical.Good c ∧ ¬ LargeBad B c

/-- Failure bound in the exact shape used by the large weighted-clock gate.
The empirical event is already one of the common kills, so it is charged only
once in the `4 * 2^-244` budget. -/
theorem actual_large_good_failure_bound { β : Type }
    (B : ℕ) (hlarge : N / 64 ≤ (B : ℝ))
    (oa : OracleComp Spec β) (hbudget : CostAtMost oa B)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    Pr[fun out => ¬ LargeGood B out.2 |
        (simulateQ oracleImpl oa).run initial] ≤
      4 * eps244 + (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  apply (probEvent_mono (fun out hout hbad => ?_)).trans
    (terminal_hits_or_cover_bound B hlarge oa hbudget initial hfresh)
  rw [LargeGood, not_and_or, not_not] at hbad
  rcases hbad with he | hL
  · exact Or.inr (Or.inl (Or.inl he))
  · exact Or.inl (largeBad_implies_hit_of_support B oa hbudget initial
      hfresh out hout hL)

end OptimalOTS.WeightedConstruction.LongChain91LargeTerminal
