import Submissions.LowerGenerality1.CacheFresh
import Submissions.LowerGenerality1.Index
import Submissions.LowerGenerality1.CostCore
import Submissions.LowerGenerality1.SignFresh

/-! Consecutive nonce trials, with exact success bounds when the nonce does not wrap. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.PatternSearch

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- Try `k` consecutive nonces from `start`, modulo the nonce space, until a target is hit. -/
def search (G : Finset ℕ) (m : Message) :
    ℕ → ℕ → OracleComp Spec (Option (Nonce × ℕ))
  | 0, _ => pure none
  | k + 1, start =>
    (liftM (Spec.query (.inr (encQuery (m ++ BitVec.ofNat nonceBits start)))) :
      OracleComp Spec (BitVec hashBits)) >>= fun w =>
        if idxOf w ∈ G then pure (some (BitVec.ofNat nonceBits start, idxOf w))
        else search G m k (start + 1)

/-- Each trial costs one index query, even if the cache already has its answer. -/
theorem cost_search (hidx : idxCost = 1) (G : Finset ℕ) (m : Message) :
    ∀ k start, CostAtMost (search G m k start) k
  | 0, _ => costAtMost_pure _ _
  | k + 1, start => by
    rw [search, costAtMost_query_bind_iff]
    have hq : queryCost (.inr (encQuery (m ++ BitVec.ofNat nonceBits start))) = 1 := hidx
    rw [hq, Nat.add_sub_cancel]
    refine ⟨by omega, fun w => ?_⟩
    split_ifs
    · exact costAtMost_pure _ _
    · exact cost_search hidx G m k (start + 1)

/-- A successful output names a target and a cached answer for its nonce query. -/
theorem search_support (G : Finset ℕ) (m : Message) :
    ∀ k start c p, p ∈ support (run (search G m k start) c) →
      ∀ η j, p.1 = some (η, j) → j ∈ G ∧
        ∃ w, p.2 (encQuery (m ++ η)) = some w ∧ idxOf w = j := by
  intro k
  induction k with
  | zero =>
    intro start c p hp η j hout
    rw [search, run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    simp at hout
  | succ k ih =>
    intro start c p hp η j hout
    rw [search] at hp
    rcases hc : c (encQuery (m ++ BitVec.ofNat nonceBits start)) with _ | w
    · obtain ⟨w, hp⟩ := mem_support_run_inr_none hc hp
      by_cases hw : idxOf w ∈ G
      · rw [if_pos hw, run_pure, support_pure] at hp
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        exact ⟨hw, w, QueryCache.cacheQuery_self _ _ _, rfl⟩
      · rw [if_neg hw] at hp
        exact ih _ _ _ hp η j hout
    · have hp := mem_support_run_inr_some hc hp
      by_cases hw : idxOf w ∈ G
      · rw [if_pos hw, run_pure, support_pure] at hp
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        exact ⟨hw, w, hc, rfl⟩
      · rw [if_neg hw] at hp
        exact ih _ _ _ hp η j hout

/-- All nonce queries in the remaining trial interval are absent from the cache. -/
def FreshRange (c : Cache) (m : Message) (start k : ℕ) : Prop :=
  ∀ n, start ≤ n → n < start + k →
    c (encQuery (m ++ BitVec.ofNat nonceBits n)) = none

theorem freshRange_of_freshMessage {c : Cache} {m : Message}
    (h : BareLower.FreshMessage c m) (start k : ℕ) : FreshRange c m start k :=
  fun _ _ _ => h _

theorem FreshRange.step {c : Cache} {m : Message} {start k : ℕ}
    (hc : FreshRange c m start (k + 1)) (hbound : start + (k + 1) ≤ 2 ^ nonceBits)
    (w : BitVec hashBits) :
    FreshRange (c.cacheQuery (encQuery (m ++ BitVec.ofNat nonceBits start)) w)
      m (start + 1) k := by
  intro n hn hn'
  have hne : encQuery (m ++ BitVec.ofNat nonceBits n) ≠
      encQuery (m ++ BitVec.ofNat nonceBits start) := by
    intro heq
    have heq := append_nonce_inj m (encQuery_inj heq)
    have heq := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ nonceBits by omega),
      Nat.mod_eq_of_lt (show start < 2 ^ nonceBits by omega)] at heq
    omega
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hc n (by omega) (by omega)

/-- A uniform oracle output hits `G` with the expected index fraction. -/
theorem uniform_target (hidx : idxBits ≤ hashBits)
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ idxBits) :
    E ($ᵗ BitVec hashBits) (fun w => if idxOf w ∈ G then 1 else 0) =
      (G.card : ℝ≥0∞) / 2 ^ idxBits := by
  have heq : E ($ᵗ BitVec hashBits) (fun w => if idxOf w ∈ G then 1 else 0) =
      ((Finset.univ.filter fun w : BitVec hashBits => idxOf w ∈ G).card : ℝ≥0∞) /
        2 ^ hashBits := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      BareLower.uniform_indicator hashBits (Finset.univ.filter fun w => idxOf w ∈ G)
  rw [heq, show (Finset.univ.filter fun w : BitVec hashBits => idxOf w ∈ G).card =
      G.card * 2 ^ (hashBits - idxBits) from Analysis.card_idxOfOut_mem hidx G hG]
  push_cast
  rw [show (2 : ℝ≥0∞) ^ hashBits =
      2 ^ idxBits * 2 ^ (hashBits - idxBits) by
        rw [← pow_add, Nat.add_sub_cancel' hidx]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)

/-- The complementary single-trial probability. -/
theorem uniform_miss (hidx : idxBits ≤ hashBits)
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ idxBits) :
    E ($ᵗ BitVec hashBits) (fun w => if idxOf w ∈ G then 0 else 1) =
      1 - (G.card : ℝ≥0∞) / 2 ^ idxBits := by
  apply ENNReal.eq_sub_of_add_eq' (by simp)
  rw [← uniform_target hidx G hG, E, E, ← expectedValue_add]
  have heq : (fun w : BitVec hashBits =>
      (if idxOf w ∈ G then (0 : ℝ≥0∞) else 1) +
      (if idxOf w ∈ G then (1 : ℝ≥0∞) else 0)) = fun _ => (1 : ℝ≥0∞) := by
    funext w
    by_cases hw : idxOf w ∈ G <;> simp only [hw, if_true, if_false, zero_add, add_zero]
  rw [heq, expectedValue_const (by simp)]

/-- Exact all-trials-fail probability for fresh, distinct nonce queries. -/
theorem failure_eq (hidx : idxBits ≤ hashBits)
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ idxBits) (m : Message) :
    ∀ k start c, start + k ≤ 2 ^ nonceBits → FreshRange c m start k →
      E (run (search G m k start) c) (fun p => if p.1.isSome then 0 else 1) =
        (1 - (G.card : ℝ≥0∞) / 2 ^ idxBits) ^ k := by
  intro k
  induction k with
  | zero =>
    intro start c hb hc
    rw [search, run_pure, E_pure]
    simp
  | succ k ih =>
    intro start c hb hc
    have hc0 := hc start le_rfl (by omega)
    rw [search, run_query_bind, oracleImpl_run_inr_none hc0, E_bind]
    simp only [E_bind, E_pure]
    have heq : (fun w : BitVec hashBits =>
        E (run (if idxOf w ∈ G then pure (some (BitVec.ofNat nonceBits start, idxOf w))
          else search G m k (start + 1))
          (c.cacheQuery (encQuery (m ++ BitVec.ofNat nonceBits start)) w))
          (fun p => if p.1.isSome then 0 else 1)) =
        (fun w => (if idxOf w ∈ G then (0 : ℝ≥0∞) else 1) *
          (1 - (G.card : ℝ≥0∞) / 2 ^ idxBits) ^ k) := by
      funext w
      by_cases hw : idxOf w ∈ G
      · rw [if_pos hw, run_pure, E_pure, if_pos hw]
        simp
      · rw [if_neg hw, if_neg hw, one_mul]
        exact ih (start + 1) _ (by omega) (hc.step hb w)
    rw [heq, E, expectedValue_mul_const]
    have hu := uniform_miss hidx G hG
    simp only [E] at hu
    rw [hu, pow_succ, mul_comm]

/-- Exact search success probability. -/
theorem success_eq (hidx : idxBits ≤ hashBits)
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ idxBits) (m : Message)
    (k start : ℕ) (c : Cache) (hb : start + k ≤ 2 ^ nonceBits)
    (hc : FreshRange c m start k) :
    E (run (search G m k start) c) (fun p => if p.1.isSome then 1 else 0) =
      1 - (1 - (G.card : ℝ≥0∞) / 2 ^ idxBits) ^ k := by
  apply ENNReal.eq_sub_of_add_eq' (by simp)
  rw [← failure_eq hidx G hG m k start c hb hc, E, E, ← expectedValue_add]
  have heq : (fun p : Option (Nonce × ℕ) × Cache =>
      (if p.1.isSome then (1 : ℝ≥0∞) else 0) +
      (if p.1.isSome then (0 : ℝ≥0∞) else 1)) = fun _ => (1 : ℝ≥0∞) := by
    funext p
    cases p.1 <;> simp
  rw [heq, expectedValue_const (by simp)]

attribute [irreducible] search

end OptimalOTS.PatternSearch
