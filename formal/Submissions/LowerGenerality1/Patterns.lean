import Submissions.LowerGenerality1.Semantics

/-! Finite counting of reconstruction patterns, with no oracle independence assumption. -/

open scoped Classical

noncomputable section

namespace OptimalOTS

open OptimalOTS.Dag


namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- A hash node costs at least one compression. -/
theorem one_le_nodeCost_of_isHash (v : Fin G.size) (hv : (G.kind v).IsHash) : 1 ≤ G.nodeCost v := by
  unfold Graph.nodeCost
  cases h : G.kind v with
  | source => simp [h, NodeKind.IsHash] at hv
  | det ps hp f hf => simp [h, NodeKind.IsHash] at hv
  | hash p hp hl => exact le_max_left _ _

def hashNodes : Finset (Fin G.size) := Finset.univ.filter fun v => (G.kind v).IsHash

theorem card_hashNodes_le_keygenCost : G.hashNodes.card ≤ G.keygenCost := by
  calc G.hashNodes.card = ∑ _v ∈ G.hashNodes, 1 := by simp
    _ ≤ ∑ v ∈ G.hashNodes, G.nodeCost v := by
      exact Finset.sum_le_sum fun v hv =>
        G.one_le_nodeCost_of_isHash v (Finset.mem_filter.mp hv).2
    _ ≤ G.keygenCost := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem card_evalHash_le_reconstructCost (A : Finset (Fin G.size)) :
    (G.evalHash A).card ≤ G.reconstructCost A := by
  calc (G.evalHash A).card = ∑ _v ∈ G.evalHash A, 1 := by simp
    _ ≤ ∑ v ∈ G.evalHash A, G.nodeCost v := by
      exact Finset.sum_le_sum fun v hv =>
        G.one_le_nodeCost_of_isHash v (Finset.mem_filter.mp hv).2
    _ ≤ G.reconstructCost A := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end Dag.Graph

namespace Dag.Scheme

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (S : Scheme)

/-- Hash nodes reconstructed at index `i`, excluding the root common to every pattern. -/
def hashPattern (i : Fin numCuts) : Finset (Fin S.graph.size) :=
  (S.graph.evalHash (S.sets i)).erase S.graph.root

/-- All indices with the same reconstruction pattern as `i`, including `i` itself. -/
def samePattern (i : Fin numCuts) : Finset (Fin numCuts) :=
  Finset.univ.filter fun j => S.hashPattern j = S.hashPattern i

theorem root_mem_evalHash (i : Fin numCuts) :
    S.graph.root ∈ S.graph.evalHash (S.sets i) := by
  simp only [Graph.evalHash, Graph.evaluated, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨Graph.Visited.root, S.root_not_mem i⟩, S.graph.root_isHash⟩

theorem hashPattern_subset (i : Fin numCuts) :
    S.hashPattern i ⊆ S.graph.hashNodes.erase S.graph.root := by
  intro v hv
  obtain ⟨hne, hv⟩ := Finset.mem_erase.mp hv
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩⟩

theorem card_hashPattern_le (i : Fin numCuts) :
    (S.hashPattern i).card + 1 ≤ S.graph.reconstructCost (S.sets i) := by
  have h := S.graph.card_evalHash_le_reconstructCost (S.sets i)
  have hr := S.root_mem_evalHash i
  have hp := Finset.card_pos.mpr ⟨_, hr⟩
  unfold hashPattern
  rw [Finset.card_erase_of_mem hr]
  omega

theorem hashPattern_eq_iff (i j : Fin numCuts) :
    S.hashPattern i = S.hashPattern j ↔
      S.graph.evalHash (S.sets i) = S.graph.evalHash (S.sets j) := by
  constructor
  · intro h
    have := congrArg (insert S.graph.root) h
    simpa only [hashPattern, Finset.insert_erase (S.root_mem_evalHash i),
      Finset.insert_erase (S.root_mem_evalHash j)] using this
  · intro h
    exact congrArg (fun t => t.erase S.graph.root) h

end Dag.Scheme

namespace PatternCounting

/-- All sets of size at most `a` from an `n`-element universe have at most this many patterns. -/
theorem card_image_le_choose_sum {ι α : Type*} [Fintype ι] [DecidableEq α]
    (f : ι → Finset α) (U : Finset α) (a n : ℕ)
    (hU : U.card ≤ n) (hsub : ∀ i, f i ⊆ U) (hsize : ∀ i, (f i).card ≤ a) :
    (Finset.univ.image f).card ≤ ∑ k ∈ Finset.range (a + 1), n.choose k := by
  classical
  have hs : Finset.univ.image f ⊆
      (Finset.range (a + 1)).biUnion (fun k => U.powersetCard k) := by
    intro A hA
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_biUnion.mpr ⟨(f i).card, Finset.mem_range.mpr (Nat.lt_succ_of_le (hsize i)),
      Finset.mem_powersetCard.mpr ⟨hsub i, rfl⟩⟩
  calc (Finset.univ.image f).card
      ≤ ((Finset.range (a + 1)).biUnion (fun k => U.powersetCard k)).card :=
        Finset.card_le_card hs
    _ ≤ ∑ k ∈ Finset.range (a + 1), (U.powersetCard k).card := Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range (a + 1), U.card.choose k := by simp only [Finset.card_powersetCard]
    _ ≤ _ := Finset.sum_le_sum fun k _ => Nat.choose_le_choose k hU

/-- Small fibers contain at most `k` elements for each value in the image. -/
theorem card_small_fibers_le {ι α : Type*} [Fintype ι] [DecidableEq α]
    (f : ι → α) (k : ℕ) :
    (Finset.univ.filter fun i => (Finset.univ.filter fun j => f j = f i).card < k).card ≤
      k * (Finset.univ.image f).card := by
  classical
  let bad := Finset.univ.filter fun i =>
    (Finset.univ.filter fun j => f j = f i).card < k
  have himage : bad.image f ⊆ Finset.univ.image f := Finset.image_subset_image (Finset.filter_subset _ _)
  calc bad.card = ∑ y ∈ bad.image f, (bad.filter fun i => f i = y).card :=
      Finset.card_eq_sum_card_image f bad
    _ ≤ ∑ _y ∈ bad.image f, k := by
      refine Finset.sum_le_sum fun y hy => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hsmall := (Finset.mem_filter.mp hi).2
      have hsub : (bad.filter fun j => f j = f i) ⊆
          Finset.univ.filter fun j => f j = f i := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      exact (Finset.card_le_card hsub).trans hsmall.le
    _ = k * (bad.image f).card := by simp [Nat.mul_comm]
    _ ≤ k * (Finset.univ.image f).card := Nat.mul_le_mul_left k (Finset.card_le_card himage)

theorem choose_sum_1023_15_lt :
    (∑ k ∈ Finset.range 16, Nat.choose 1023 k) < 2 ^ 110 := by
  norm_num [Finset.sum_range_succ, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]

end PatternCounting

namespace Dag.Scheme

theorem card_hashPattern_image_le (S : Scheme)
    (hcost : ∀ i, S.verifyCost i ≤ 17) :
    (Finset.univ.image S.hashPattern).card ≤ 2 ^ 110 := by
  have hroot : S.graph.root ∈ S.graph.hashNodes :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.graph.root_isHash⟩
  have hn : (S.graph.hashNodes.erase S.graph.root).card ≤ 1023 := by
    rw [Finset.card_erase_of_mem hroot]
    have h := S.graph.card_hashNodes_le_keygenCost.trans S.keygen_le
    change S.graph.hashNodes.card ≤ 1024 at h
    omega
  have hs : ∀ i, (S.hashPattern i).card ≤ 15 := by
    intro i
    have hc := hcost i
    have hp := S.card_hashPattern_le i
    change 1 + S.graph.reconstructCost (S.sets i) ≤ 17 at hc
    omega
  exact (PatternCounting.card_image_le_choose_sum S.hashPattern
    (S.graph.hashNodes.erase S.graph.root) 15 1023 hn S.hashPattern_subset hs).trans
      PatternCounting.choose_sum_1023_15_lt.le

/-- At most one quarter of the indices have fewer than eight equal reconstruction patterns. -/
theorem card_small_samePattern_mul_four_le (S : Scheme)
    (hcost : ∀ i, S.verifyCost i ≤ 17) :
    (Finset.univ.filter fun i => (S.samePattern i).card < 8).card * 4 ≤
      numCuts := by
  have h := PatternCounting.card_small_fibers_le S.hashPattern 8
  have hn := S.card_hashPattern_image_le hcost
  change (Finset.univ.filter fun i => (S.samePattern i).card < 8).card ≤
    8 * (Finset.univ.image S.hashPattern).card at h
  have hb := h.trans (Nat.mul_le_mul_left 8 hn)
  change _ ≤ 2 ^ 115
  have hnumeral : 8 * 2 ^ 110 * 4 = (2 : ℕ) ^ 115 := by norm_num
  simpa only [hnumeral] using Nat.mul_le_mul_right 4 hb

end Dag.Scheme
end OptimalOTS
