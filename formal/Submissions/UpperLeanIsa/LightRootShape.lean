import Submissions.UpperLeanIsa.FusionShape
import Submissions.UpperLeanIsa.FusionConcrete

/-! Research lemmas for a single-root dependency graph. These establish the packet
primitive, domain separation, acyclic evaluation, and conditional reconstruction.
They do not assert a signing-failure bound, security certificate, or machine score. -/

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion.LightRoot

open OptimalOTS

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Logical binding groups, in the order in which their parents become bound. -/
def parentList (u : ℕ) : List ℕ :=
  ([[3,4,5,6], [8,9,10,11], [1,2,7], [12,13,17], [18,22,23], [27,28,32],
    [33,37,38], [14,15,16], [19,20,21], [24,25,26], [29,30,31], [34,35,36]]).getD u []

def parents (u : ℕ) : Finset ℕ := (parentList u).toFinset

def children (u : ℕ) : List ℕ :=
  ([[10,11,1], [2,7,12], [13,17,18], [22,23,27], [28,32,33], [37,38,14],
    [15,16,19], [20,21,24], [25,26,29], [30,31,34], [35,36,39], [40,41,0]]).getD u []

def rootSet : Finset ℕ := {3,4,5,6,8,9}

def closure : ℕ → Finset ℕ
  | 0 => rootSet
  | n + 1 => closure n ∪ (children n).toFinset

theorem schedule : ∀ n < 12, parents n ⊆ closure n := by decide

theorem full_coverage : Finset.range 42 ⊆ closure 12 := by decide

theorem children_length : ∀ u < 12, (children u).length = 3 := by decide

theorem parent_lengths : ∀ u < 12, (parentList u).length ≤ 4 := by decide

def evaluationOrder : List ℕ :=
  [0,39,40,41,34,35,36,29,30,31,24,25,26,19,20,21,14,15,16,33,37,38,
    27,28,32,18,22,23,12,13,17,1,2,7,8,9,10,11,3,4,5,6]

def evaluationRank (k : ℕ) : ℕ := evaluationOrder.idxOf k

theorem evaluationOrder_permutation : evaluationOrder.Perm (List.range 42) := by decide

theorem dependency_precedes : ∀ u < 12, ∀ k ∈ parents u, ∀ d ∈ children u,
    evaluationRank d < evaluationRank k := by decide

/-- All these constants already occur among cost/frame constants C_1,...,C_16. -/
def domain (u : Fin 12) : Word := tagWord ⟨u.val + 1, by omega⟩
def cvLo (i : Fin 4) : Word := tagWord ⟨i.val + 1, by omega⟩
def cvHi (i : Fin 4) : Word := tagWord ⟨i.val + 2, by omega⟩
def rootDomain : Word := tagWord 15

theorem domain_injective : Function.Injective domain := by
  intro u v h
  have hv := congrArg Fin.val (tagWord_injective h)
  exact Fin.ext (by simpa using hv)

theorem cvLo_injective : Function.Injective cvLo := by
  intro i j h
  have hv := congrArg Fin.val (tagWord_injective h)
  exact Fin.ext (by simpa using hv)

theorem domain_separated (u : Fin 12) :
    domain u ≠ tagWord 0 ∧ domain u ≠ tagWord 16 ∧ domain u ≠ rootDomain := by
  have hu := u.isLt
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;>
    have he := congrArg Fin.val (tagWord_injective h) <;> simp only at he <;> omega

/-- A parent coordinate and its binding group select a unique constant CV/metadata
combination. Four message words remain for the current value and three children. -/
def words (t : ℕ → Word) (u : Fin 12) (i : Fin 4) (x : Word) : Fin 7 → Word :=
  ![cvLo i, cvHi i, x, t ((children u).getD 0 0),
    t ((children u).getD 1 0), t ((children u).getD 2 0), domain u]

def input (t : ℕ → Word) (u : Fin 12) (i : Fin 4) (x : Word) : BitVec 896 :=
  packet (words t u i x)

theorem input_location {t t' : ℕ → Word} {u v : Fin 12} {i j : Fin 4} {x x' : Word}
    (h : input t u i x = input t' v j x') : u = v ∧ i = j ∧ x = x' := by
  have he := packet_injective h
  have hd : domain u = domain v := congrFun he 6
  have hi : cvLo i = cvLo j := congrFun he 0
  have hx : x = x' := congrFun he 2
  exact ⟨domain_injective hd, cvLo_injective hi, hx⟩

theorem input_binds {t t' : ℕ → Word} {u : Fin 12} {i : Fin 4} {x x' : Word}
    (h : input t u i x = input t' u i x') : ∀ k ∈ children u, t k = t' k := by
  have he := packet_injective h
  have h0 : t ((children u).getD 0 0) = t' ((children u).getD 0 0) := congrFun he 3
  have h1 : t ((children u).getD 1 0) = t' ((children u).getD 1 0) := congrFun he 4
  have h2 : t ((children u).getD 2 0) = t' ((children u).getD 2 0) := congrFun he 5
  intro k hk
  fin_cases u <;> simp [children] at hk h0 h1 h2
  all_goals rcases hk with rfl | rfl | rfl
  all_goals assumption

def rootWords (t : ℕ → Word) : Fin 7 → Word :=
  ![t 8, t 9, t 3, t 4, t 5, t 6, rootDomain]

def rootInput (t : ℕ → Word) : BitVec 896 := packet (rootWords t)

theorem root_binds {t t' : ℕ → Word} (h : rootInput t = rootInput t') :
    ∀ k ∈ rootSet, t k = t' k := by
  have he := packet_injective h
  have h0 : t 8 = t' 8 := congrFun he 0
  have h1 : t 9 = t' 9 := congrFun he 1
  have h2 : t 3 = t' 3 := congrFun he 2
  have h3 : t 4 = t' 4 := congrFun he 3
  have h4 : t 5 = t' 5 := congrFun he 4
  have h5 : t 6 = t' 6 := congrFun he 5
  intro k hk
  simp [rootSet] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem input_ne_root (t t' : ℕ → Word) (u : Fin 12) (i : Fin 4) (x : Word) :
    input t u i x ≠ rootInput t' := by
  intro h
  have hd : domain u = rootDomain := congrFun (packet_injective h) 6
  exact (domain_separated u).2.2 hd

/-- Coverage only uses a positive parent in each binding group. A full security
proof must still bound the bad event and exclude inactive binding groups. -/
theorem reconstruction_binding (t t' : ℕ → Word) (d : ℕ → ℕ) (Bad : Prop)
    (hr : rootInput t = rootInput t')
    (ha : ∀ u < 12, 0 < ∑ k ∈ parents u, d k)
    (hf : ∀ u < 12, ∀ k ∈ parents u, 0 < d k → t k = t' k →
      Bad ∨ ∀ j ∈ children u, t j = t' j) :
    Bad ∨ ∀ k < 42, t k = t' k := by
  classical
  by_cases hb : Bad
  · exact Or.inl hb
  right
  have active : ∀ u < 12, ∃ k ∈ parents u, 0 < d k := by
    intro u hu
    by_contra hn
    have hz : ∑ k ∈ parents u, d k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have : ¬ 0 < d k := fun hd => hn ⟨k, hk, hd⟩
      omega
    have := ha u hu
    omega
  have hclosed : ∀ n ≤ 12, ∀ k ∈ closure n, t k = t' k := by
    intro n
    induction n with
    | zero => intro _; exact root_binds hr
    | succ n ih =>
      intro hn k hk
      rcases Finset.mem_union.mp hk with hprev | hnew
      · exact ih (by omega) k hprev
      · obtain ⟨b, hmem, hpos⟩ := active n (by omega)
        have hbound := ih (by omega) b (schedule n (by omega) hmem)
        rcases hf n (by omega) b hmem hpos hbound with hbad | hgroup
        · exact (hb hbad).elim
        · exact hgroup k (List.mem_toFinset.mp hnew)
  intro k hk
  exact hclosed 12 le_rfl k (full_coverage (Finset.mem_range.mpr hk))

end OptimalOTS.LeanIsaBaseline.Layer.Fusion.LightRoot
