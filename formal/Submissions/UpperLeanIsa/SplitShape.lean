import Submissions.UpperLeanIsa.FusionShape

/-! Research graph for the eight-binding-group 1096 arithmetic candidate.
Four packets have five children and four have four children. These are graph
and packet lemmas only, not a codec, security, or machine certificate.
The concrete domain constants and their machine initialization still need a port.
-/

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion.SplitRoot

open OptimalOTS
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Table order: 5, 6, 0, 8, 9, 10, 11, 12. Table 7 is ordinary. -/
def parentList (u : ℕ) : List ℕ :=
  ([[3,4,5,6],[8,9],[1,2,7],[19,20,21],[24,25,26],[29,30,31],[34,35],[39,40]]).getD u []
def parents (u : ℕ) : Finset ℕ := (parentList u).toFinset
def children (u : ℕ) : List ℕ :=
  ([[1,2,7,24],[19,20,10,11,21],[25,26,29,30,31],[34,35,39,40],
    [12,13,14,15],[16,17,18,22],[23,27,36,28,32],[33,37,41,38,0]]).getD u []
def rootSet : Finset ℕ := {3,4,5,6,8,9}
def five (u : ℕ) : Bool := u == 1 || u == 2 || u == 6 || u == 7
def closure : ℕ → Finset ℕ
  | 0 => rootSet
  | n+1 => closure n ∪ (children n).toFinset

theorem schedule : ∀ n < 8, parents n ⊆ closure n := by decide
theorem full_coverage : Finset.range 42 ⊆ closure 8 := by decide
theorem packet_lengths : ∀ u < 8, (children u).length = if five u then 5 else 4 := by decide
theorem five_parent_count : ((List.range 8).filter five |>.map fun u => (parentList u).length).sum = 9 := by decide
theorem four_parent_count : ((List.range 8).filter (fun u => !five u) |>.map fun u => (parentList u).length).sum = 13 := by decide

theorem internal_positions : (children 1).getD 2 0 = 10 ∧
    (children 1).getD 3 0 = 11 ∧ (children 6).getD 2 0 = 36 ∧
    (children 7).getD 2 0 = 41 := by decide
theorem internal_not_parents : ∀ u < 8,
    10 ∉ parents u ∧ 11 ∉ parents u ∧ 36 ∉ parents u ∧ 41 ∉ parents u := by decide
theorem internal_private : (∀ u < 8, 10 ∈ children u ↔ u = 1) ∧
    (∀ u < 8, 11 ∈ children u ↔ u = 1) ∧
    (∀ u < 8, 36 ∈ children u ↔ u = 6) ∧
    (∀ u < 8, 41 ∈ children u ↔ u = 7) := by decide

def evaluationOrder : List ℕ :=
  [0,10,11,12,13,14,15,16,17,18,22,23,27,28,32,33,36,37,38,41,
   34,35,39,40,24,25,26,29,30,31,19,20,21,1,2,7,8,9,3,4,5,6]
def evaluationRank (k : ℕ) : ℕ := evaluationOrder.idxOf k
theorem evaluationOrder_permutation : evaluationOrder.Perm (List.range 42) := by decide
theorem dependency_precedes : ∀ u < 8, ∀ k ∈ parents u, ∀ d ∈ children u,
    evaluationRank d < evaluationRank k := by decide

/-- Abstract labels: 0 is ordinary, 4 is root, 16 is index, and 17 is the
already pinned signature length. Label 17 still needs its concrete field
separation proof; these finite facts do not assume that proof has been done. -/
def metadataLabel (u i : ℕ) : ℕ :=
  if u = 1 then [1,2].getD i 0 else if u = 2 then [3,5,6].getD i 0
  else if u = 6 then [7,8].getD i 0 else if u = 7 then [9,10].getD i 0 else 17
def messageLabel (u i : ℕ) : ℕ :=
  if u = 0 then i+1 else if u = 3 then i+5
  else if u = 4 then i+8 else if u = 5 then i+11 else 0

theorem labels_bounded : ∀ u < 8, ∀ i < (parentList u).length,
    (metadataLabel u i = 17 ∨ 1 ≤ metadataLabel u i ∧ metadataLabel u i ≤ 13) ∧
    messageLabel u i ≤ 13 := by decide
theorem labels_reserved : ∀ u < 8, ∀ i < (parentList u).length,
    metadataLabel u i ≠ 0 ∧ metadataLabel u i ≠ 4 ∧ metadataLabel u i ≠ 16 := by decide
theorem label_pairs_unique : ∀ (u v : Fin 8) (i j : Fin 4),
    i.val < (parentList u).length → j.val < (parentList v).length →
    metadataLabel u i = metadataLabel v j → messageLabel u i = messageLabel v j →
    u = v ∧ i = j := by decide +kernel

/-- `md` and `tag` must be independently domain-separated in a concrete port.
The four-child format uses `tag` in word 5; the five-child format uses it for a child. -/
def words (t : ℕ → Word) (u : Fin 8) (x tag md : Word) : Fin 7 → Word :=
  ![t ((children u).getD 0 0),t ((children u).getD 1 0),x,
    t ((children u).getD 2 0),t ((children u).getD 3 0),
    if five u then t ((children u).getD 4 0) else tag,md]

theorem packet_current {t t' : ℕ → Word} {u v : Fin 8} {x x' tag tag' md md' : Word}
    (h : packet (words t u x tag md) = packet (words t' v x' tag' md')) : x = x' :=
  congrFun (packet_injective h) 2

theorem packet_binds {t t' : ℕ → Word} {u : Fin 8} {x x' tag tag' md md' : Word}
    (h : packet (words t u x tag md) = packet (words t' u x' tag' md')) :
    ∀ k ∈ children u, t k = t' k := by
  have he := packet_injective h
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 3
  have h3 := congrFun he 4
  have h4 := congrFun he 5
  intro k hk
  fin_cases u <;> simp [children,words,five] at hk h0 h1 h2 h3 h4
  all_goals rcases hk with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- The combinatorial induction used by the later security proof. -/
theorem reconstruction_binding (t t' : ℕ → Word) (d : ℕ → ℕ) (Bad : Prop)
    (hr : ∀ k ∈ rootSet, t k = t' k)
    (ha : ∀ u < 8, 0 < ∑ k ∈ parents u, d k)
    (hf : ∀ u < 8, ∀ k ∈ parents u, 0 < d k → t k = t' k →
      Bad ∨ ∀ j ∈ children u, t j = t' j) :
    Bad ∨ ∀ k < 42, t k = t' k := by
  classical
  by_cases hb : Bad
  · exact Or.inl hb
  right
  have active : ∀ u < 8, ∃ k ∈ parents u, 0 < d k := by
    intro u hu
    by_contra hn
    have hz : ∑ k ∈ parents u, d k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have : ¬ 0 < d k := fun hd => hn ⟨k,hk,hd⟩
      omega
    have := ha u hu
    omega
  have hc : ∀ n ≤ 8, ∀ k ∈ closure n, t k = t' k := by
    intro n
    induction n with
    | zero => intro _; exact hr
    | succ n ih =>
      intro hn k hk
      rcases Finset.mem_union.mp hk with hp | hn'
      · exact ih (by omega) k hp
      · obtain ⟨b,hm,hpos⟩ := active n (by omega)
        have he := ih (by omega) b (schedule n (by omega) hm)
        rcases hf n (by omega) b hm hpos he with hbad | hgroup
        · exact (hb hbad).elim
        · exact hgroup k (List.mem_toFinset.mp hn')
  intro k hk
  exact hc 8 le_rfl k (full_coverage (Finset.mem_range.mpr hk))

end OptimalOTS.LeanIsaBaseline.Layer.Fusion.SplitRoot
