import Submissions.UpperLeanIsa.SplitShape

/-! The concrete one-root graph, with packet lemmas parameterized by domain words. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.FourFusion
open OptimalOTS
set_option maxRecDepth 100000

abbrev packet := Fusion.packet
abbrev packet_injective := Fusion.packet_injective
abbrev parentList := Fusion.SplitRoot.parentList
abbrev parents := Fusion.SplitRoot.parents
abbrev children := Fusion.SplitRoot.children
abbrev rootSet := Fusion.SplitRoot.rootSet
abbrev evaluationOrder := Fusion.SplitRoot.evaluationOrder
abbrev evaluationRank := Fusion.SplitRoot.evaluationRank
abbrev evaluationOrder_permutation := Fusion.SplitRoot.evaluationOrder_permutation
abbrev dependency_precedes := Fusion.SplitRoot.dependency_precedes

def bindOrder : List ℕ := [0,1,2,3,4,5,6,7]
def closure : ℕ → Finset ℕ
  | 0 => rootSet
  | n+1 => closure n ∪ (children (bindOrder.getD n 0)).toFinset

theorem bindOrder_lt : ∀ n < 8, bindOrder.getD n 0 < 8 := by decide
theorem schedule : ∀ n < 8, parents (bindOrder.getD n 0) ⊆ closure n := by decide
theorem full_coverage : Finset.range 42 ⊆ closure 8 := by decide

def rootWords (t : ℕ → Word) (md : Word) : Fin 7 → Word :=
  ![t 8,t 9,t 3,t 4,t 5,t 6,md]

abbrev five := Fusion.SplitRoot.five

def fusionWords (t : ℕ → Word) (u : ℕ) (x tag md : Word) : Fin 7 → Word :=
  ![t ((children u).getD 0 0),t ((children u).getD 1 0),x,
    t ((children u).getD 2 0),t ((children u).getD 3 0),
    if five u then t ((children u).getD 4 0) else tag,md]

theorem fusion_binds_children (t t' : ℕ → Word) {u : ℕ} (hu : u < 8)
    (x x' a a' md md' : Word)
    (h : packet (fusionWords t u x a md) = packet (fusionWords t' u x' a' md')) :
    ∀ k ∈ children u, t k = t' k := by
  exact Fusion.SplitRoot.packet_binds (u := ⟨u,hu⟩) h

theorem fusion_current_injective (t t' : ℕ → Word) (u : ℕ) (x x' a a' md md' : Word)
    (h : packet (fusionWords t u x a md) = packet (fusionWords t' u x' a' md')) : x = x' :=
  congrFun (packet_injective h) 2

theorem root_binds (t t' : ℕ → Word) (md md' : Word)
    (h : packet (rootWords t md) = packet (rootWords t' md')) :
    ∀ k ∈ rootSet, t k = t' k := by
  have he := packet_injective h
  have h0 : t 8 = t' 8 := congrFun he 0
  have h1 : t 9 = t' 9 := congrFun he 1
  have h2 : t 3 = t' 3 := congrFun he 2
  have h3 : t 4 = t' 4 := congrFun he 3
  have h4 : t 5 = t' 5 := congrFun he 4
  have h5 : t 6 = t' 6 := congrFun he 5
  intro k hk
  simp [rootSet, Fusion.SplitRoot.rootSet] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

def GroupBinds (t t' : ℕ → Word) (u : ℕ) : Prop := ∀ k ∈ children u, t k = t' k

end OptimalOTS.LeanIsaBaseline.Layer.FourFusion
