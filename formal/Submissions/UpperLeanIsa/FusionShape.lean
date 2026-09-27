import Submissions.UpperLeanIsa.Records

/-! The fixed one-root dependency graph of the 1115-cycle construction.
The closure theorem is conditional on actual query equalities or a charged bad event.
It is not a complete security or machine certificate. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OptimalOTS
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packet (w : Fin 7 → Word) : BitVec 896 :=
  LeanIsa.hashInput (w 1 ++ w 0) (w 5 ++ w 4 ++ w 3 ++ w 2) (w 6)

theorem packet_injective : Function.Injective packet := by
  intro w w' h
  obtain ⟨hc, hm, ht⟩ := (hashInput_eq_iff _ _ _ _ _ _).mp h
  obtain ⟨h1, h0⟩ := append_inj hc
  obtain ⟨h543, h2⟩ := append_inj hm
  obtain ⟨h54, h3⟩ := append_inj h543
  obtain ⟨h5, h4⟩ := append_inj h54
  funext i
  fin_cases i <;> assumption

def rootSet : Finset ℕ := {1,2,3,4,5,6}
/-- Groups `0 … 4` fuse five dependency tops into a parent's final step; the three-dep groups
`5 … 8` bind three tops through the message of their parents' final steps. -/
def parents (u : ℕ) : Finset ℕ :=
  if u=0 then {3,4,5,6} else if u=1 then {1,2,7}
  else if u=2 then {14,15,16} else if u=3 then {19,20,21}
  else if u=4 then {24,25,26} else if u=5 then {8,9,10,11}
  else if u=6 then {29,30,31} else if u=7 then {34,35,36} else {39,40,41}
/-- Group `8` has two children; its third message word repeats top 38. -/
def children (u : ℕ) : List ℕ :=
  if u=0 then [7,8,9,10,11] else if u=1 then [14,15,16,19,20]
  else if u=2 then [26,29,30,31,34] else if u=3 then [35,36,39,40,41]
  else if u=4 then [12,13,0,17,18] else if u=5 then [21,24,25]
  else if u=6 then [22,23,27] else if u=7 then [28,32,33] else [37,38,38]
/-- The order in which the groups bind their children. -/
def bindOrder : List ℕ := [0,1,5,2,3,4,6,7,8]
def closure : ℕ → Finset ℕ
  | 0 => rootSet
  | n+1 => closure n ∪ (children (bindOrder.getD n 0)).toFinset

theorem bindOrder_lt : ∀ n < 9, bindOrder.getD n 0 < 9 := by decide
theorem schedule : ∀ n < 9, parents (bindOrder.getD n 0) ⊆ closure n := by decide
theorem full_coverage : Finset.range 42 ⊆ closure 9 := by decide

/-- The single root call: cv `(t 1, t 2)`, message `t 3 … t 6`. -/
def rootWords (t : ℕ → Word) (tag : Word) : Fin 7 → Word := ![t 1,t 2,t 3,t 4,t 5,t 6,tag]

def fusionWords (t : ℕ → Word) (u : ℕ) (x tag : Word) : Fin 7 → Word :=
  ![t ((children u).getD 0 0),t ((children u).getD 1 0),x,
    t ((children u).getD 2 0),t ((children u).getD 3 0),t ((children u).getD 4 0),tag]

/-- The final step of a three-dep parent: message `[x, d0, d1, d2]` of the group's children. -/
def triplePacket (cv : BitVec 256) (t : ℕ → Word) (u : ℕ) (x md : Word) : BitVec 896 :=
  LeanIsa.hashInput cv
    (t ((children u).getD 2 0) ++ t ((children u).getD 1 0) ++ t ((children u).getD 0 0) ++ x) md

theorem triplePacket_eq {cv cv' : BitVec 256} {x x' md md' : Word} {t t' : ℕ → Word} {u u' : ℕ}
    (h : triplePacket cv t u x md = triplePacket cv' t' u' x' md') :
    cv = cv' ∧ (∀ i < 3, t ((children u).getD i 0) = t' ((children u').getD i 0)) ∧ x = x' ∧
      md = md' := by
  obtain ⟨hc, hm, ht⟩ := (hashInput_eq_iff _ _ _ _ _ _).mp h
  obtain ⟨h3, hx⟩ := append_inj hm
  obtain ⟨h2, h0⟩ := append_inj h3
  obtain ⟨h22, h1⟩ := append_inj h2
  refine ⟨hc, fun i hi => ?_, hx, ht⟩
  interval_cases i <;> assumption

theorem triple_binds {cv cv' : BitVec 256} {x x' md md' : Word} {t t' : ℕ → Word} {u : ℕ}
    (hu : 5 ≤ u) (hu9 : u < 9) (h : triplePacket cv t u x md = triplePacket cv' t' u x' md') :
    ∀ k ∈ children u, t k = t' k := by
  have he := (triplePacket_eq h).2.1
  have h0 := he 0 (by omega)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  intro k hk
  interval_cases u <;> simp [children] at hk h0 h1 h2
  all_goals rcases hk with rfl | rfl | rfl <;> assumption

theorem triple_current {cv cv' : BitVec 256} {x x' md md' : Word} {t t' : ℕ → Word} {u : ℕ}
    (h : triplePacket cv t u x md = triplePacket cv' t' u x' md') : x = x' :=
  (triplePacket_eq h).2.2.1

theorem root_binds (t t' : ℕ → Word) (tag tag' : Word)
    (h : packet (rootWords t tag) = packet (rootWords t' tag')) :
    ∀ k ∈ rootSet, t k = t' k := by
  have eq0 (i : Fin 7) := congrFun (packet_injective h) i
  simp [rootWords] at eq0
  intro k hk
  simp [rootSet] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact eq0 0 | exact eq0 1 | exact eq0 2 | exact eq0 3 | exact eq0 4 | exact eq0 5

theorem fusion_binds_children (t t' : ℕ → Word) {u : ℕ} (hu : u < 5) (x x' tag tag' : Word)
    (h : packet (fusionWords t u x tag) = packet (fusionWords t' u x' tag')) :
    ∀ k ∈ children u, t k = t' k := by
  have he := packet_injective h
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 3
  have h3 := congrFun he 4
  have h4 := congrFun he 5
  simp only [fusionWords, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_three] at h0 h1 h2 h3 h4
  intro k hk
  interval_cases u <;> simp [children] at hk h0 h1 h2 h3 h4
  all_goals rcases hk with rfl | rfl | rfl | rfl | rfl
  all_goals assumption

/-- The children of group `u` agree under two top assignments. -/
def GroupBinds (t t' : ℕ → Word) (u : ℕ) : Prop := ∀ k ∈ children u, t k = t' k

/-- Key generation computes every dependency before its consumers. -/
def evaluationOrder : List ℕ := [0, 12, 13, 17, 18, 22, 23, 27, 28, 32, 33, 37, 38, 24, 25, 26, 29, 30, 31, 34, 35, 36, 39, 40, 41, 14, 15, 16, 19, 20, 21, 1, 2, 7, 8, 9, 10, 11, 3, 4, 5, 6]

def evaluationRank (k : ℕ) : ℕ := evaluationOrder.idxOf k

theorem dependency_precedes : ∀ u < 9, ∀ k ∈ parents u, ∀ d ∈ children u,
    evaluationRank d < evaluationRank k := by decide

end OptimalOTS.LeanIsaBaseline.Layer.Fusion
