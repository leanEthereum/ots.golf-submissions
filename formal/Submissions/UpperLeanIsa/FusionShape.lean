import Submissions.UpperLeanIsa.Records

/-! The fixed two-root dependency graph of the 1139-cycle research candidate.
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

def rootSet : Finset ℕ := {1,2,3,4,5,6,26,8,9,10,11}
/-- Groups `0 … 5` fuse five dependency tops into a parent's final step; the light group `6`
binds top 7 through the final steps of chains 39, 40, 41. -/
def parents (u : ℕ) : Finset ℕ :=
  if u=0 then {1,2,7} else if u=1 then {3,4,5,6}
  else if u=2 then {8,9,10,11} else if u=3 then {14,15,16}
  else if u=4 then {19,20,21} else if u=5 then {24,25,26} else {39,40,41}
def children (u : ℕ) : List ℕ :=
  if u=0 then [14,15,16,19,20] else if u=1 then [21,24,25,31,34]
  else if u=2 then [35,36,39,40,41] else if u=3 then [12,13,0,17,18]
  else if u=4 then [22,23,27,28,32] else if u=5 then [33,37,38,29,30] else [7]
/-- The order in which the groups bind their children. -/
def bindOrder : List ℕ := [1,2,5,6,0,3,4]
def closure : ℕ → Finset ℕ
  | 0 => rootSet
  | n+1 => closure n ∪ (children (bindOrder.getD n 0)).toFinset

theorem bindOrder_lt : ∀ n < 7, bindOrder.getD n 0 < 7 := by decide
theorem schedule : ∀ n < 7, parents (bindOrder.getD n 0) ⊆ closure n := by decide
theorem full_coverage : Finset.range 42 ⊆ closure 7 := by decide

def rootWords (t st tag : ℕ → Word) (r : ℕ) : Fin 7 → Word :=
  if r=0 then ![t 1,t 2,t 3,t 4,t 5,t 6,tag 0]
  else ![t 26,st 0,t 8,t 9,t 10,t 11,tag 1]

def fusionWords (t : ℕ → Word) (u : ℕ) (x tag : Word) : Fin 7 → Word :=
  ![t ((children u).getD 0 0),t ((children u).getD 1 0),x,
    t ((children u).getD 2 0),t ((children u).getD 3 0),t ((children u).getD 4 0),tag]

/-- The final step of a light parent: message `[x, t 7, B, C]`. -/
def lightPacket (cv : BitVec 256) (b c : Word) (t : ℕ → Word) (x md : Word) : BitVec 896 :=
  LeanIsa.hashInput cv (c ++ b ++ t 7 ++ x) md

theorem lightPacket_eq {cv cv' : BitVec 256} {b b' c c' x x' md md' : Word} {t t' : ℕ → Word}
    (h : lightPacket cv b c t x md = lightPacket cv' b' c' t' x' md') :
    cv = cv' ∧ b = b' ∧ c = c' ∧ t 7 = t' 7 ∧ x = x' ∧ md = md' := by
  obtain ⟨hc, hm, ht⟩ := (hashInput_eq_iff _ _ _ _ _ _).mp h
  obtain ⟨h3, hx⟩ := append_inj hm
  obtain ⟨h2, h7⟩ := append_inj h3
  obtain ⟨hcc, hb⟩ := append_inj h2
  exact ⟨hc, hb, hcc, h7, hx, ht⟩

theorem light_binds {cv cv' : BitVec 256} {b b' c c' x x' md md' : Word} {t t' : ℕ → Word}
    (h : lightPacket cv b c t x md = lightPacket cv' b' c' t' x' md') :
    ∀ k ∈ children 6, t k = t' k := by
  intro k hk
  simp [children] at hk
  subst hk
  exact (lightPacket_eq h).2.2.2.1

theorem light_current {cv cv' : BitVec 256} {b b' c c' x x' md md' : Word} {t t' : ℕ → Word}
    (h : lightPacket cv b c t x md = lightPacket cv' b' c' t' x' md') : x = x' :=
  (lightPacket_eq h).2.2.2.2.1

theorem root_binds (t t' : ℕ → Word) (st st' tag tag' : ℕ → Word)
    (h : ∀ r < 2, packet (rootWords t st tag r) = packet (rootWords t' st' tag' r)) :
    ∀ k ∈ rootSet, t k = t' k := by
  have h0 := packet_injective (h 0 (by omega))
  have h1 := packet_injective (h 1 (by omega))
  have eq0 (i : Fin 7) := congrFun h0 i
  have eq1 (i : Fin 7) := congrFun h1 i
  simp [rootWords] at eq0 eq1
  intro k hk
  simp [rootSet] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact eq0 0 | exact eq0 1 | exact eq0 2 | exact eq0 3 | exact eq0 4 | exact eq0 5
    | exact eq1 0 | exact eq1 2 | exact eq1 3 | exact eq1 4 | exact eq1 5

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

/-- The children of group `u` agree under two top assignments. -/
def GroupBinds (t t' : ℕ → Word) (u : ℕ) : Prop := ∀ k ∈ children u, t k = t' k

/-- Group bindings at active, already-bound parents propagate through the binding order.
The probability of failing those bindings is deliberately a hypothesis. -/
theorem reconstruction_binding (t t' : ℕ → Word) (st st' tag tag' : ℕ → Word)
    (d : ℕ → ℕ) (Bad : Prop)
    (hr : ∀ r < 2, packet (rootWords t st tag r) = packet (rootWords t' st' tag' r))
    (ha : ∀ u < 7, 0 < ∑ k ∈ parents u, d k)
    (hf : ∀ u < 7, ∀ k ∈ parents u, 0 < d k → t k = t' k → Bad ∨ GroupBinds t t' u) :
    Bad ∨ ∀ k < 42, t k = t' k := by
  classical
  by_cases hb : Bad
  · exact Or.inl hb
  right
  have active : ∀ u < 7, ∃ k ∈ parents u, 0 < d k := by
    intro u hu
    by_contra hn
    have hz : ∑ k ∈ parents u, d k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have : ¬ 0 < d k := fun hd => hn ⟨k,hk,hd⟩
      omega
    have := ha u hu
    omega
  have hclosed : ∀ n ≤ 7, ∀ k ∈ closure n, t k = t' k := by
    intro n
    induction n with
    | zero => intro _; exact root_binds t t' st st' tag tag' hr
    | succ n ih =>
      intro hn k hk
      rcases Finset.mem_union.mp hk with hprev | hnew
      · exact ih (by omega) k hprev
      · have hu := bindOrder_lt n (by omega)
        obtain ⟨b,hmem,hpos⟩ := active _ hu
        have hbnd := ih (by omega) b (schedule n (by omega) hmem)
        rcases hf _ hu b hmem hpos hbnd with hbad | hg
        · exact (hb hbad).elim
        · exact hg k (List.mem_toFinset.mp hnew)
  intro k hk
  exact hclosed 7 le_rfl k (full_coverage (Finset.mem_range.mpr hk))

/-- Key generation computes every dependency before its consumers. -/
def evaluationOrder : List ℕ := [0, 12, 13, 17, 18, 22, 23, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 14, 15, 16, 19, 20, 21, 24, 25, 26, 1, 2, 3, 4, 5, 6, 7, 39, 40, 41, 8, 9, 10, 11]

def evaluationRank (k : ℕ) : ℕ := evaluationOrder.idxOf k

theorem evaluationOrder_permutation : evaluationOrder.Perm (List.range 42) := by decide

theorem dependency_precedes : ∀ u < 7, ∀ k ∈ parents u, ∀ d ∈ children u,
    evaluationRank d < evaluationRank k := by decide

/-- Every special input has exactly five dependency words and its current chain word. -/
theorem fusion_current_injective (t t' : ℕ → Word) (u : ℕ) (x x' a a' : Word)
    (h : packet (fusionWords t u x a) = packet (fusionWords t' u x' a')) : x = x' := by
  exact congrFun (packet_injective h) 2

end OptimalOTS.LeanIsaBaseline.Layer.Fusion
