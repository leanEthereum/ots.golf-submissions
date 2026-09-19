import Submissions.LowerGenerality1.Patterns
import Submissions.LowerGenerality1.OrderedCounting

/-! Hash origins of disclosed values: the hash nodes reached from a node by following parent edges
backwards, stopping at each hash node. The largest hash node in a directed pattern difference is a
disclosed origin. -/
noncomputable section
open scoped Classical
namespace OptimalOTS

open OptimalOTS.Dag

namespace Dag.Graph
attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

/-- `HashOrigin h v` reaches hash node `h` from `v` without passing another hash. -/
inductive HashOrigin : Fin G.size → Fin G.size → Prop
  | hash {h} : (G.kind h).IsHash → HashOrigin h h
  | step {h v w} : ¬ (G.kind v).IsHash → w ∈ (G.kind v).parents →
      HashOrigin h w → HashOrigin h v

/-- The hash origins of one node. -/
def hashOrigins (v : Fin G.size) : Finset (Fin G.size) :=
  Finset.univ.filter fun h => G.HashOrigin h v

/-- The union of a payload's hash origins, counting each node once. -/
def disclosureOrigins (A : Finset (Fin G.size)) : Finset (Fin G.size) :=
  A.biUnion G.hashOrigins

/-- Every disclosure set has at most `b` distinct hash origins. -/
def _root_.OptimalOTS.Dag.Scheme.DisclosureBound (S : Scheme) (b : ℕ) : Prop :=
  ∀ i, (S.graph.disclosureOrigins (S.sets i)).card ≤ b

@[simp] theorem mem_hashOrigins {h v : Fin G.size} :
    h ∈ G.hashOrigins v ↔ G.HashOrigin h v := by
  simp only [hashOrigins, Finset.mem_filter, Finset.mem_univ, true_and]

theorem HashOrigin.le {h v : Fin G.size} (ho : G.HashOrigin h v) : h ≤ v := by
  induction ho with
  | hash _ => exact le_rfl
  | step _ hp _ ih => exact ih.trans ((G.kind _).lt_of_mem_parents hp).le

theorem HashOrigin.eq_of_hash {h v : Fin G.size} (ho : G.HashOrigin h v)
    (hv : (G.kind v).IsHash) : h = v := by
  cases ho with
  | hash _ => rfl
  | step hn _ _ => exact (hn hv).elim

theorem origin_mem_disclosure {A : Finset (Fin G.size)} {h v : Fin G.size}
    (hv : v ∈ A) (ho : G.HashOrigin h v) : h ∈ G.disclosureOrigins A :=
  Finset.mem_biUnion.mpr ⟨v, hv, (G.mem_hashOrigins).mpr ho⟩

/-- Reaching an uncomputed origin through a visited node entails disclosing that origin. -/
theorem origin_disclosed_of_visited {A : Finset (Fin G.size)} {h v : Fin G.size}
    (ho : G.HashOrigin h v) (hv : G.Visited A v) (hn : h ∉ G.evalHash A) :
    h ∈ G.disclosureOrigins A := by
  induction ho with
  | hash hh =>
    apply G.origin_mem_disclosure (v := h) _ (HashOrigin.hash hh)
    by_contra ha
    exact hn (by simp only [evalHash, evaluated, Finset.mem_filter, Finset.mem_univ,
      true_and]; exact ⟨⟨hv, ha⟩, hh⟩)
  | @step v w hnh hp ho ih =>
    by_cases ha : v ∈ A
    · exact G.origin_mem_disclosure ha (HashOrigin.step hnh hp ho)
    · exact ih (Visited.parent hv ha hp)

end Dag.Graph
namespace Dag.Scheme
attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (S : Scheme)

/-- Along a visited path, an undisclosed missing origin has a strictly later missing hash. -/
theorem origin_disclosed_or_later (i j : Fin numCuts) {v : Fin S.graph.size}
    (hv : S.graph.Visited (S.sets i) v) :
    ∀ h, S.graph.HashOrigin h v → h ∉ S.graph.evalHash (S.sets j) →
      h ∈ S.graph.disclosureOrigins (S.sets j) ∨
      ∃ g ∈ S.graph.evalHash (S.sets i), g ∉ S.graph.evalHash (S.sets j) ∧ h < g := by
  induction hv with
  | root =>
    intro h ho hn
    have he := Graph.HashOrigin.eq_of_hash S.graph ho S.graph.root_isHash
    subst h
    exact (hn (S.root_mem_evalHash j)).elim
  | @parent w v hw hwa hp ih =>
    intro h ho hn
    by_cases hwh : (S.graph.kind w).IsHash
    · by_cases hwj : w ∈ S.graph.evalHash (S.sets j)
      · left
        have hh := (Finset.mem_filter.mp hwj).1
        have hh := Finset.mem_filter.mp hh
        exact S.graph.origin_disclosed_of_visited ho
          (Graph.Visited.parent hh.2.1 hh.2.2 hp) hn
      · right
        refine ⟨w, ?_, hwj, ?_⟩
        · simp only [Graph.evalHash, Graph.evaluated, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨⟨hw, hwa⟩, hwh⟩
        · exact (Graph.HashOrigin.le S.graph ho).trans_lt ((S.graph.kind w).lt_of_mem_parents hp)
    · exact ih h (Graph.HashOrigin.step hwh hp ho) hn

/-- The maximal difference of two reconstruction patterns is an origin of the second payload. -/
theorem max_difference_disclosed (i j : Fin numCuts) (v : Fin S.graph.size)
    (hv : v ∈ S.hashPattern i \ S.hashPattern j)
    (hmax : ∀ w ∈ S.hashPattern i \ S.hashPattern j, w ≤ v) :
    v ∈ S.graph.disclosureOrigins (S.sets j) := by
  obtain ⟨hvi, hvj⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hvr, hvi⟩ := Finset.mem_erase.mp hvi
  have hvj' : v ∉ S.graph.evalHash (S.sets j) :=
    fun h => hvj (Finset.mem_erase.mpr ⟨hvr, h⟩)
  have hh := Finset.mem_filter.mp hvi
  have hvisit := (Finset.mem_filter.mp hh.1).2.1
  rcases S.origin_disclosed_or_later i j hvisit v (Graph.HashOrigin.hash hh.2) hvj' with hd | ⟨g,hgi,hgj,hvg⟩
  · exact hd
  · have hgr : g ≠ S.graph.root := fun e => hgj (e ▸ S.root_mem_evalHash j)
    have hgp : g ∈ S.hashPattern i \ S.hashPattern j :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hgr, hgi⟩,
        fun h => hgj (Finset.mem_of_mem_erase h)⟩
    exact (not_lt_of_ge (hmax g hgp) hvg).elim

attribute [local semireducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

/-- At most 42 disclosed origins and cost at most 89 give at most `choose 129 42` patterns. -/
theorem card_hashPattern_image_le_disclosure (S : Scheme)
    (hdis : S.DisclosureBound 42) (hcost : ∀ i, S.verifyCost i ≤ 89) :
    (Finset.univ.image S.hashPattern).card ≤ Nat.choose 129 42 := by
  let Fn := Finset.univ.image S.hashPattern
  let idx (a : Finset (Fin S.graph.size)) : Fin numCuts :=
    if h : ∃ i, S.hashPattern i = a then Classical.choose h else ⟨0, by decide⟩
  have hidx : ∀ a ∈ Fn, S.hashPattern (idx a) = a := by
    intro a ha
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
    have he : ∃ i, S.hashPattern i = a := ⟨i, hi⟩
    simp only [idx, dif_pos he]
    exact Classical.choose_spec he
  have hA : ∀ a ∈ Fn, a.card ≤ 87 := by
    intro a ha
    rw [← hidx a ha]
    have hc := hcost (idx a)
    have hp := S.card_hashPattern_le (idx a)
    change 1 + S.graph.reconstructCost (S.sets (idx a)) ≤ 89 at hc
    omega
  have h := DisclosureCounting.card_le_choose 87 42 Fn id
    (fun a => S.graph.disclosureOrigins (S.sets (idx a)))
    (fun _ _ _ _ he => he) hA (fun a _ => hdis (idx a)) (by
      intro a ha b hb v hv hm
      apply S.max_difference_disclosed (idx a) (idx b) v
      · simpa only [hidx a ha, hidx b hb, id_eq] using hv
      · simpa only [hidx a ha, hidx b hb, id_eq] using hm)
  have he : Nat.choose 129 87 = Nat.choose 129 42 := by
    rw [Nat.choose_symm (show 87 ≤ 129 by omega)]
  exact h.trans_eq he

end Dag.Scheme
end OptimalOTS
