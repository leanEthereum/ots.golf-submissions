import Submissions.UpperLeanIsa.Records

/-! The fixed three-root dependency graph of the 1149-cycle research candidate.
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

def rootSet : Finset ℕ := {1,2,3,4,5,6,7,26,8,9,10,11}
def parents (u : ℕ) : Finset ℕ :=
  if u=0 then {1,2,7} else if u=1 then {3,4,5,6}
  else if u=2 then {8,9,10,11} else if u=3 then {14,15,16}
  else if u=4 then {19,20,21} else {24,25,26}
def children (u : ℕ) : List ℕ :=
  if u=0 then [14,15,16,19,20] else if u=1 then [21,24,25,31,34]
  else if u=2 then [35,36,39,40,41] else if u=3 then [12,13,0,17,18]
  else if u=4 then [22,23,27,28,32] else [33,37,38,29,30]
def closure : ℕ → Finset ℕ
  | 0 => rootSet
  | n+1 => closure n ∪ (children n).toFinset

theorem schedule : ∀ u < 6, parents u ⊆ closure u := by decide
theorem full_coverage : Finset.range 42 ⊆ closure 6 := by decide

def rootWords (t st tag : ℕ → Word) (r : ℕ) : Fin 7 → Word :=
  if r=0 then ![t 1,t 2,t 3,t 4,t 5,t 6,tag 0]
  else if r=1 then ![t 26,st 0,t 8,t 9,t 10,t 11,tag 1]
  else ![t 7,st 1,1,1,1,1,tag 2]

def fusionWords (t : ℕ → Word) (u : ℕ) (x tag : Word) : Fin 7 → Word :=
  ![t ((children u).getD 0 0),t ((children u).getD 1 0),x,
    t ((children u).getD 2 0),t ((children u).getD 3 0),t ((children u).getD 4 0),tag]

theorem root_binds (t t' : ℕ → Word) (st st' tag tag' : ℕ → Word)
    (h : ∀ r < 3, packet (rootWords t st tag r) = packet (rootWords t' st' tag' r)) :
    ∀ k ∈ rootSet, t k = t' k := by
  have h0 := packet_injective (h 0 (by omega))
  have h1 := packet_injective (h 1 (by omega))
  have h2 := packet_injective (h 2 (by omega))
  have eq2 (i : Fin 7) := congrFun h2 i
  have eq0 (i : Fin 7) := congrFun h0 i
  have eq1 (i : Fin 7) := congrFun h1 i
  simp [rootWords] at eq0 eq1 eq2
  intro k hk
  simp [rootSet] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact eq0 0 | exact eq0 1 | exact eq0 2 | exact eq0 3 | exact eq0 4 | exact eq0 5
    | exact eq1 0 | exact eq1 2 | exact eq1 3 | exact eq1 4 | exact eq1 5 | exact eq2 0

theorem fusion_binds_children (t t' : ℕ → Word) {u : ℕ} (hu : u < 6) (x x' tag tag' : Word)
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

/-- Query equalities at an active, already-bound parent propagate through both
levels. The probability of failing those equalities is deliberately a hypothesis. -/
theorem reconstruction_binding (t t' : ℕ → Word) (st st' tag tag' : ℕ → Word)
    (d : ℕ → ℕ) (Bad : Prop)
    (hr : ∀ r < 3, packet (rootWords t st tag r) = packet (rootWords t' st' tag' r))
    (ha : ∀ u < 6, 0 < ∑ k ∈ parents u, d k)
    (hf : ∀ u < 6, ∀ k ∈ parents u, 0 < d k → t k = t' k → Bad ∨
      ∃ x x' a a', packet (fusionWords t u x a) = packet (fusionWords t' u x' a')) :
    Bad ∨ ∀ k < 42, t k = t' k := by
  classical
  by_cases hb : Bad
  · exact Or.inl hb
  right
  have active : ∀ u < 6, ∃ k ∈ parents u, 0 < d k := by
    intro u hu
    by_contra hn
    have hz : ∑ k ∈ parents u, d k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have : ¬ 0 < d k := fun hd => hn ⟨k,hk,hd⟩
      omega
    have := ha u hu
    omega
  have hclosed : ∀ n ≤ 6, ∀ k ∈ closure n, t k = t' k := by
    intro n
    induction n with
    | zero => intro _; exact root_binds t t' st st' tag tag' hr
    | succ n ih =>
      intro hn k hk
      rcases Finset.mem_union.mp hk with hprev | hnew
      · exact ih (by omega) k hprev
      · obtain ⟨b,hmem,hpos⟩ := active n (by omega)
        have hbnd := ih (by omega) b (schedule n (by omega) hmem)
        rcases hf n (by omega) b hmem hpos hbnd with hbad | ⟨x,x',a,a',he⟩
        · exact (hb hbad).elim
        · exact fusion_binds_children t t' (by omega) x x' a a' he k
            (List.mem_toFinset.mp hnew)
  intro k hk
  exact hclosed 6 le_rfl k (full_coverage (Finset.mem_range.mpr hk))

/-- Key generation computes every dependency before its consumers. -/
def evaluationOrder : List ℕ := [0, 12, 13, 17, 18, 22, 23, 27, 28, 32, 33, 37, 38, 29, 30, 31, 34, 35, 36, 39, 40, 41, 14, 15, 16, 19, 20, 21, 24, 25, 26, 1, 2, 7, 3, 4, 5, 6, 8, 9, 10, 11]

def evaluationRank (k : ℕ) : ℕ := evaluationOrder.idxOf k

theorem evaluationOrder_permutation : evaluationOrder.Perm (List.range 42) := by decide

theorem dependency_precedes : ∀ u < 6, ∀ k ∈ parents u, ∀ d ∈ children u,
    evaluationRank d < evaluationRank k := by decide

/-- Every special input has exactly five dependency words and its current chain word. -/
theorem fusion_current_injective (t t' : ℕ → Word) (u : ℕ) (x x' a a' : Word)
    (h : packet (fusionWords t u x a) = packet (fusionWords t' u x' a')) : x = x' := by
  exact congrFun (packet_injective h) 2

end OptimalOTS.LeanIsaBaseline.Layer.Fusion
