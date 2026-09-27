import Submissions.UpperLeanIsa.FusionShape
import Submissions.UpperLeanIsa.FusionConcrete

/-! Research lemmas for a single-root, nine-group dependency graph with four-child packets. These establish the packet
primitive, domain separation, acyclic evaluation, and conditional reconstruction.
They do not assert a signing-failure bound, security certificate, or machine score. -/

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion.FourChildRoot

open OptimalOTS

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Logical binding groups, in the order in which their parents become bound. -/
def parentList (u : ℕ) : List ℕ :=
  ([[3,4,5,6],[8,9,10,11],[1,2,7],[14,15,16],[19,20,21],[24,25,26],[29,30,31],[34,35,36],[39,40,41]]).getD u []

def parents (u : ℕ) : Finset ℕ := (parentList u).toFinset

def children (u : ℕ) : List ℕ :=
  ([[10,11,1,2],[7,14,15,16],[19,20,21,24],[25,26,29,30],[31,34,35,36],[39,40,41,12],[13,17,18,22],[23,27,28,32],[33,37,38,0]]).getD u []

def rootSet : Finset ℕ := {3,4,5,6,8,9}

def closure : ℕ → Finset ℕ
  | 0 => rootSet
  | n + 1 => closure n ∪ (children n).toFinset

theorem schedule : ∀ n < 9, parents n ⊆ closure n := by decide

theorem full_coverage : Finset.range 42 ⊆ closure 9 := by decide

theorem children_length : ∀ u < 9, (children u).length = 4 := by decide

theorem parent_lengths : ∀ u < 9, (parentList u).length ≤ 4 := by decide

def evaluationOrder : List ℕ :=
  [0,12,13,17,18,22,23,27,28,32,33,37,38,29,30,31,34,35,36,39,40,41,19,20,21,24,25,26,1,2,7,14,15,16,8,9,10,11,3,4,5,6]

def evaluationRank (k : ℕ) : ℕ := evaluationOrder.idxOf k

theorem evaluationOrder_permutation : evaluationOrder.Perm (List.range 42) := by decide

theorem dependency_precedes : ∀ u < 9, ∀ k ∈ parents u, ∀ d ∈ children u,
    evaluationRank d < evaluationRank k := by decide

/-- Two constant fields encode 36 parent slots using only C1,...,C13.
Metadata C1,C2,C3 separates these packets from ordinary (C0), index (C16),
and root (C4) calls. The second tag selects one of thirteen slots. -/
def slot (u : Fin 9) (i : Fin 4) : ℕ := 4 * u.val + i.val

def domain (u : Fin 9) (i : Fin 4) : Word :=
  tagWord ⟨slot u i / 13 + 1, by have := u.isLt; have := i.isLt; unfold slot; omega⟩

def tag (u : Fin 9) (i : Fin 4) : Word :=
  tagWord ⟨slot u i % 13 + 1, by have := Nat.mod_lt (slot u i) (by omega : 0 < 13); omega⟩

def rootDomain : Word := tagWord 4

theorem tags_injective {u v : Fin 9} {i j : Fin 4}
    (hd : domain u i = domain v j) (ht : tag u i = tag v j) : u = v ∧ i = j := by
  have hd' := congrArg Fin.val (tagWord_injective hd)
  have ht' := congrArg Fin.val (tagWord_injective ht)
  dsimp only at hd' ht'
  have hs : slot u i = slot v j := by omega
  have hu := u.isLt
  have hv := v.isLt
  have hi := i.isLt
  have hj := j.isLt
  unfold slot at hs
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem domain_separated (u : Fin 9) (i : Fin 4) :
    domain u i ≠ tagWord 0 ∧ domain u i ≠ tagWord 16 ∧ domain u i ≠ rootDomain := by
  have hu := u.isLt
  have hi := i.isLt
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;>
    have he := congrArg Fin.val (tagWord_injective h) <;>
    simp only [slot] at he <;> omega

/-- A constant in the fourth message word and a metadata constant identify the
parent. The CV and two message words carry four children. -/
def words (t : ℕ → Word) (u : Fin 9) (i : Fin 4) (x : Word) : Fin 7 → Word :=
  ![t ((children u).getD 0 0), t ((children u).getD 1 0), x,
    t ((children u).getD 2 0), t ((children u).getD 3 0), tag u i, domain u i]

def input (t : ℕ → Word) (u : Fin 9) (i : Fin 4) (x : Word) : BitVec 896 :=
  packet (words t u i x)

theorem input_location {t t' : ℕ → Word} {u v : Fin 9} {i j : Fin 4} {x x' : Word}
    (h : input t u i x = input t' v j x') : u = v ∧ i = j ∧ x = x' := by
  have he := packet_injective h
  have hd : domain u i = domain v j := congrFun he 6
  have ht : tag u i = tag v j := congrFun he 5
  have hx : x = x' := congrFun he 2
  exact ⟨(tags_injective hd ht).1, (tags_injective hd ht).2, hx⟩

theorem input_binds {t t' : ℕ → Word} {u : Fin 9} {i : Fin 4} {x x' : Word}
    (h : input t u i x = input t' u i x') : ∀ k ∈ children u, t k = t' k := by
  have he := packet_injective h
  have h0 : t ((children u).getD 0 0) = t' ((children u).getD 0 0) := congrFun he 0
  have h1 : t ((children u).getD 1 0) = t' ((children u).getD 1 0) := congrFun he 1
  have h2 : t ((children u).getD 2 0) = t' ((children u).getD 2 0) := congrFun he 3
  have h3 : t ((children u).getD 3 0) = t' ((children u).getD 3 0) := congrFun he 4
  intro k hk
  fin_cases u <;> simp [children] at hk h0 h1 h2 h3
  all_goals rcases hk with rfl | rfl | rfl | rfl
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

theorem input_ne_root (t t' : ℕ → Word) (u : Fin 9) (i : Fin 4) (x : Word) :
    input t u i x ≠ rootInput t' := by
  intro h
  have hd : domain u i = rootDomain := congrFun (packet_injective h) 6
  exact (domain_separated u i).2.2 hd

/-- Coverage only uses a positive parent in each binding group. A full security
proof must still bound the bad event and exclude inactive binding groups. -/
theorem reconstruction_binding (t t' : ℕ → Word) (d : ℕ → ℕ) (Bad : Prop)
    (hr : rootInput t = rootInput t')
    (ha : ∀ u < 9, 0 < ∑ k ∈ parents u, d k)
    (hf : ∀ u < 9, ∀ k ∈ parents u, 0 < d k → t k = t' k →
      Bad ∨ ∀ j ∈ children u, t j = t' j) :
    Bad ∨ ∀ k < 42, t k = t' k := by
  classical
  by_cases hb : Bad
  · exact Or.inl hb
  right
  have active : ∀ u < 9, ∃ k ∈ parents u, 0 < d k := by
    intro u hu
    by_contra hn
    have hz : ∑ k ∈ parents u, d k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have : ¬ 0 < d k := fun hd => hn ⟨k, hk, hd⟩
      omega
    have := ha u hu
    omega
  have hclosed : ∀ n ≤ 9, ∀ k ∈ closure n, t k = t' k := by
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
  exact hclosed 9 le_rfl k (full_coverage (Finset.mem_range.mpr hk))

end OptimalOTS.LeanIsaBaseline.Layer.Fusion.FourChildRoot
