import Submissions.UpperCompressions.LongChain91Scheme
import Submissions.UpperCompressions.ProofBundle05

/-!
# Authentication bridge for the cost-90 shared-DAG construction

This module identifies the concrete key-generation oracle points of the
shared-DAG graph, splits them into exposed and hidden points after signing,
and defines the spurious-output authentication event used by the accepted
weighted-game proof.  The final section proves the fresh-query charge for
that event, including the 128-bit public root.
-/

open OracleSpec OracleComp ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Index queries -/

abbrev EncInput := Message × BitVec 86

def encQuery (u : EncInput) : Query := ⟨msgBits + 86, u.1 ++ u.2⟩

theorem encQuery_length (u : EncInput) : (encQuery u).1 = 342 := rfl

theorem ne_encQuery_of_length_ne {q : Query} (hq : q.1 ≠ msgBits + 86)
    (u : EncInput) : q ≠ encQuery u := by
  intro h
  exact hq (congrArg Sigma.fst h)


/-! ## Bit-vector helpers -/

theorem lowWord_cast {n m : ℕ} (h : n = m) (x : BitVec n) :
    lowWord (x.cast h) = lowWord x := by
  subst h
  rfl

theorem lowWord_lowWord {n : ℕ} (x : BitVec n) :
    lowWord (lowWord x) = lowWord x := BitVec.setWidth_eq _

theorem cast_cast_eq {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x := by
  subst h₁
  rfl

theorem lowWord_eq_self (x : BitVec 129) : lowWord x = x := BitVec.setWidth_eq _

theorem cast_injective {n m : ℕ} (h : n = m) {x y : BitVec n}
    (e : x.cast h = y.cast h) : x = y := by
  subst h
  simpa using e

theorem eq_of_lowWord_eq {n : ℕ} (hn : n = 129) {x y : BitVec n}
    (h : lowWord x = lowWord y) : x = y := by
  subst n
  simpa only [lowWord_eq_self] using h

theorem bv_append_inj {n m : ℕ} {x x' : BitVec n} {y y' : BitVec m}
    (h : x ++ y = x' ++ y') : x = x' ∧ y = y' := by
  have key : ∀ i, (x ++ y).getLsbD i = (x' ++ y').getLsbD i :=
    fun i => by rw [h]
  simp only [BitVec.getLsbD_append] at key
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := key (i + m)
    simp only [show ¬ (i + m < m) by omega, if_false,
      Nat.add_sub_cancel] at hh
    exact hh
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := key i
    simpa [hi] using hh

theorem cat3_inj {a b c a' b' c' : BitVec 129}
    (h : cat3 a b c = cat3 a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  unfold cat3 at h
  obtain ⟨h12, h3⟩ := bv_append_inj (cast_injective _ h)
  obtain ⟨h1, h2⟩ := bv_append_inj h12
  exact ⟨h1, h2, h3⟩

theorem cat7_inj {a b : Fin 7 → BitVec 129} (h : cat7 a = cat7 b) : a = b := by
  unfold cat7 at h
  obtain ⟨hprefix5, h6⟩ := bv_append_inj (cast_injective _ h)
  obtain ⟨hprefix4, h5⟩ := bv_append_inj hprefix5
  obtain ⟨hprefix3, h4⟩ := bv_append_inj hprefix4
  obtain ⟨hprefix2, h3⟩ := bv_append_inj hprefix3
  obtain ⟨hprefix1, h2⟩ := bv_append_inj hprefix2
  obtain ⟨h0, h1⟩ := bv_append_inj hprefix1
  funext u
  fin_cases u <;> assumption

theorem lowWord_tw_append {n : ℕ} (hn : 129 ≤ n) (a : BitVec 16) (x : BitVec n) :
    lowWord (a ++ x) = lowWord x := by
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos hn]

theorem lowWord_cat3 (x y z : BitVec 129) : lowWord (cat3 x y z) = z := by
  unfold cat3
  rw [lowWord_cast]
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

theorem lowWord_cat7 (a : Fin 7 → BitVec 129) : lowWord (cat7 a) = a 6 := by
  unfold cat7
  rw [lowWord_cast]
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

/-! ## Node roles

Every node is a source, a hash node, the input of exactly one hash node (a
compression input), or a 129-bit value node reading exactly one hash node. -/

/-- The input of a hash node. -/
def hashParent : Name → Option Name
  | .ch b k t => some (.ci b k t)
  | .hh b j => some (.hc b j)
  | .rh => some .rc
  | _ => none

/-- The hash node read by a non-source 129-bit value node. -/
def hashOf : Name → Option Name
  | .cv b k t => some (.ch b k t)
  | .hv b j => some (.hh b j)
  | _ => none

/-- The hash node behind a kid's 129-bit value in block `b`. -/
def Kid.coord (b : Fin 7) : Kid → Name
  | .c k => .ch b k 17
  | .h j => .hh b j

/-- The exclusive kid of a hash node: the 129-bit value in the low slot of
its input, read by no other node. -/
def exclOf : Name → Name
  | .ch b k t => prev b k t
  | .hh b j => (kid j 2).name b
  | .rh => .hv 6 10
  | n => n

/-- The independent record coordinate behind the exclusive kid. -/
def coordOf : Name → Name
  | .ch b k t => if h : t.val = 0 then .src b k else .ch b k ⟨t.val - 1, by omega⟩
  | .hh b j => (kid j 2).coord b
  | .rh => .hh 6 10
  | n => n

theorem hashParent_isSome_iff (h : Name) :
    (hashParent h).isSome ↔ h.cost ≠ 0 := by
  cases h <;> simp [hashParent, Name.cost]

theorem cost_ne_zero_of_hashParent {h p : Name} (hp : hashParent h = some p) :
    h.cost ≠ 0 :=
  (hashParent_isSome_iff h).1 (by rw [hp]; rfl)

/-- The hash node reading a compression input. -/
def hashOfInput : Name → Option Name
  | .ci b k t => some (.ch b k t)
  | .hc b j => some (.hh b j)
  | .rc => some .rh
  | _ => none

/-- The value node reading a hash node. -/
def valueOfHash : Name → Option Name
  | .ch b k t => some (.cv b k t)
  | .hh b j => some (.hv b j)
  | _ => none

theorem hashOfInput_of_hashParent {h p : Name} (hp : hashParent h = some p) :
    hashOfInput p = some h := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> rfl

theorem valueOfHash_of_hashOf {v h : Name} (hh : hashOf v = some h) :
    valueOfHash h = some v := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst hh <;> rfl

theorem hashParent_injective {h h' p : Name} (hp : hashParent h = some p)
    (hp' : hashParent h' = some p) : h = h' :=
  Option.some.inj ((hashOfInput_of_hashParent hp).symm.trans
    (hashOfInput_of_hashParent hp'))

theorem hashOf_injective {v v' h : Name} (hh : hashOf v = some h)
    (hh' : hashOf v' = some h) : v = v' :=
  Option.some.inj ((valueOfHash_of_hashOf hh).symm.trans (valueOfHash_of_hashOf hh'))

theorem len_of_hashParent {h p : Name} (hp : hashParent h = some p) :
    h.len = 256 := by
  cases h <;> simp_all [hashParent, Name.len]

theorem len_hashParent_cases {h p : Name} (hp : hashParent h = some p) :
    p.len = 145 ∨ p.len = 403 ∨ p.len = 919 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> simp [Name.len]

theorem len_hashParent_ne_129 {h p : Name} (hp : hashParent h = some p) :
    p.len ≠ 129 := by
  rcases len_hashParent_cases hp with e | e | e <;> omega

theorem len_hashParent_ne_enc {h p : Name} (hp : hashParent h = some p) :
    p.len ≠ msgBits + 86 := by
  have he : msgBits + 86 = 342 := rfl
  rw [he]
  rcases len_hashParent_cases hp with h | h | h <;> omega

theorem cost_hashParent {h p : Name} (hp : hashParent h = some p) :
    p.cost = 0 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> rfl

theorem hashParent_ne_src {h p : Name} (hp : hashParent h = some p)
    (b : Fin 7) (k : Fin 8) : p ≠ .src b k := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> intro e <;> nomatch e

theorem hashParent_hashParent {h p : Name} (hp : hashParent h = some p) :
    hashParent p = none := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> rfl

theorem hashOf_hashParent {h p : Name} (hp : hashParent h = some p) :
    hashOf p = none := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> rfl

theorem hashOf_of_hashParent {h p : Name} (hp : hashParent h = some p) :
    hashOf h = none := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> rfl

theorem len_of_hashOf {v h : Name} (hh : hashOf v = some h) : h.len = 256 := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst hh <;> rfl

theorem len_value_of_hashOf {v h : Name} (hh : hashOf v = some h) :
    v.len = 129 := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> rfl

theorem cost_of_hashOf {v h : Name} (hh : hashOf v = some h) : v.cost = 0 := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> rfl

theorem hashParent_of_hashOf {v h : Name} (hh : hashOf v = some h) :
    ∃ p, hashParent h = some p := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst hh <;> exact ⟨_, rfl⟩

theorem hashParent_value {v h : Name} (hh : hashOf v = some h) :
    hashParent v = none := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> rfl

theorem ne_rh_of_hashOf {v h : Name} (hh : hashOf v = some h) : h ≠ .rh := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst hh <;> intro e <;> nomatch e

theorem hashOf_rh : hashOf .rh = none := rfl

theorem one_le_cost_of_hashParent {h p : Name} (hp : hashParent h = some p) :
    1 ≤ h.cost := Nat.one_le_iff_ne_zero.2 (cost_ne_zero_of_hashParent hp)

/-- The four node roles. -/
theorem role_cases (n : Name) :
    (∃ b k, n = .src b k) ∨ (∃ p, hashParent n = some p) ∨
      (∃ h, hashParent h = some n) ∨ ∃ h, hashOf n = some h := by
  cases n with
  | src b k => exact Or.inl ⟨b, k, rfl⟩
  | ci b k t => exact Or.inr (Or.inr (Or.inl ⟨.ch b k t, rfl⟩))
  | ch b k t => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | cv b k t => exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
  | hc b j => exact Or.inr (Or.inr (Or.inl ⟨.hh b j, rfl⟩))
  | hh b j => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | hv b j => exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
  | rc => exact Or.inr (Or.inr (Or.inl ⟨.rh, rfl⟩))
  | rh => exact Or.inr (Or.inl ⟨_, rfl⟩)

theorem len_eq_129_cases {n : Name} (hn : n.len = 129) :
    (∃ b k, n = .src b k) ∨ ∃ h, hashOf n = some h := by
  rcases role_cases n with hs | ⟨p, hp⟩ | ⟨h, hp⟩ | hv
  · exact Or.inl hs
  · rw [len_of_hashParent hp] at hn
    omega
  · exact absurd hn (len_hashParent_ne_129 hp)
  · exact Or.inr hv

theorem hashOf_kidName (κ : Kid) (b : Fin 7) :
    hashOf (κ.name b) = some (κ.coord b) := by
  cases κ <;> rfl

theorem hashOf_prev (b : Fin 7) (k : Fin 8) (t : Fin 18) (ht : t.val ≠ 0) :
    hashOf (prev b k t) = some (.ch b k ⟨t.val - 1, by omega⟩) := by
  simp [prev, ht, hashOf]

/-! ### Parents by role -/

theorem mem_parents_hash {h p n : Name} (hp : hashParent h = some p) :
    n ∈ parents h ↔ n = p := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> simp [parents]

theorem mem_parents_value {v h n : Name} (hh : hashOf v = some h) :
    n ∈ parents v ↔ n = h := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst hh <;> simp [parents]

theorem not_mem_parents_src (b : Fin 7) (k : Fin 8) (n : Name) :
    n ∉ parents (.src b k) := by
  simp [parents]

/-- The inputs of a compression node are sources or value nodes. -/
theorem mem_parents_compress {h p n : Name} (hp : hashParent h = some p)
    (hn : n ∈ parents p) : (∃ b k, n = .src b k) ∨ ∃ s, hashOf n = some s := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> simp only [parents, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and] at hn
  · rename_i b k t
    subst hn
    by_cases ht : t.val = 0
    · exact Or.inl ⟨b, k, by simp [prev, ht]⟩
    · exact Or.inr ⟨_, hashOf_prev b k t ht⟩
  · obtain ⟨a, rfl⟩ := hn
    exact Or.inr ⟨_, hashOf_kidName _ _⟩
  · obtain ⟨b, rfl⟩ := hn
    exact Or.inr ⟨_, rfl⟩

theorem len_of_mem_parents_compress {h p n : Name} (hp : hashParent h = some p)
    (hn : n ∈ parents p) : n.len = 129 := by
  rcases mem_parents_compress hp hn with ⟨b, k, rfl⟩ | ⟨s, hs⟩
  · rfl
  · exact len_value_of_hashOf hs

/-- A parent of any node, classified by the role of the node. -/
theorem mem_parents_cases {m n : Name} (hn : n ∈ parents m) :
    (∃ p, hashParent m = some p ∧ n = p) ∨ hashOf m = some n ∨
      ∃ h, hashParent h = some m ∧
        ((∃ b k, n = .src b k) ∨ ∃ s, hashOf n = some s) := by
  rcases role_cases m with ⟨b, k, rfl⟩ | ⟨p, hp⟩ | ⟨h, hp⟩ | ⟨s, hs⟩
  · exact absurd hn (not_mem_parents_src b k n)
  · exact Or.inl ⟨p, hp, (mem_parents_hash hp).1 hn⟩
  · exact Or.inr (Or.inr ⟨h, hp, mem_parents_compress hp hn⟩)
  · exact Or.inr (Or.inl (by rw [(mem_parents_value hs).1 hn] ; exact hs))

theorem mem_parents_hashParent {h p : Name} (hp : hashParent h = some p) :
    p ∈ parents h := (mem_parents_hash hp).2 rfl

theorem mem_parents_hashOf {v h : Name} (hh : hashOf v = some h) :
    h ∈ parents v := (mem_parents_value hh).2 rfl

/-- A compression input is read only by its hash node. -/
theorem consumer_of_hashParent {h p m : Name} (hp : hashParent h = some p)
    (hm : p ∈ parents m) : m = h := by
  rcases mem_parents_cases hm with ⟨p', hp', rfl⟩ | hv | ⟨h', -, ⟨b, k, rfl⟩ | ⟨s, hs⟩⟩
  · exact hashParent_injective hp' hp
  · obtain ⟨q, hq⟩ := hashParent_of_hashOf hv
    rw [hashParent_hashParent hp] at hq
    exact absurd hq (by simp)
  · exact absurd rfl (hashParent_ne_src hp b k)
  · rw [hashOf_hashParent hp] at hs
    exact absurd hs (by simp)

/-- A hash node is read only by its value node. -/
theorem consumer_of_hashOf {v h m : Name} (hh : hashOf v = some h)
    (hm : h ∈ parents m) : m = v := by
  obtain ⟨p, hp⟩ := hashParent_of_hashOf hh
  rcases mem_parents_cases hm with ⟨p', hp', rfl⟩ | hv | ⟨h', -, ⟨b, k, rfl⟩ | ⟨s, hs⟩⟩
  · rw [hashParent_hashParent hp'] at hp
    exact absurd hp (by simp)
  · exact hashOf_injective hv hh
  · simp [hashParent] at hp
  · rw [hashOf_of_hashParent hp] at hs
    exact absurd hs (by simp)

theorem exclOf_mem {h p : Name} (hp : hashParent h = some p) :
    exclOf h ∈ parents p := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> simp [exclOf, parents]

theorem kid_ne_top (j : Fin 11) (a : Fin 3) : kid j a ≠ Kid.h 10 := by
  revert j a
  decide

theorem prev_ne_chainEnd (b b' : Fin 7) (k k' : Fin 8) (t : Fin 18) :
    prev b k t ≠ .cv b' k' 17 := by
  unfold prev
  split_ifs with ht
  · intro e
    nomatch e
  · intro e
    simp only [Name.cv.injEq] at e
    have := congrArg Fin.val e.2.2
    simp at this
    omega

theorem prev_injective {b b' : Fin 7} {k k' : Fin 8} {t t' : Fin 18}
    (e : prev b k t = prev b' k' t') : b = b' ∧ k = k' ∧ t = t' := by
  unfold prev at e
  split_ifs at e with ht ht' <;>
    simp only [Name.src.injEq, Name.cv.injEq, Fin.mk.injEq] at e
  · exact ⟨e.1, e.2, Fin.ext (by omega)⟩
  · exact ⟨e.1, e.2.1, Fin.ext (by omega)⟩

theorem kidName_injective {κ κ' : Kid} {b b' : Fin 7}
    (e : κ.name b = κ'.name b') : b = b' ∧ κ = κ' := by
  cases κ <;> cases κ' <;>
    simp only [Kid.name, Name.cv.injEq, Name.hv.injEq, reduceCtorEq] at e
  · exact ⟨e.1, by rw [e.2.1]⟩
  · exact ⟨e.1, by rw [e.2]⟩

theorem prev_ne_kidName (b b' : Fin 7) (k : Fin 8) (t : Fin 18) (κ : Kid) :
    prev b k t ≠ κ.name b' := by
  cases κ with
  | c k' => exact prev_ne_chainEnd b b' k k' t
  | h j =>
      unfold prev
      split_ifs <;> intro e <;> nomatch e

/-- A compression node reading the exclusive kid of `h` is the input of `h`. -/
theorem compress_reader_of_exclOf {h p h' m : Name} (hp : hashParent h = some p)
    (hm' : hashParent h' = some m) (hm : exclOf h ∈ parents m) : m = p := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;>
    cases h' <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hm' <;>
    subst hm' <;> simp only [exclOf] at hm
  · simp only [parents, Finset.mem_singleton] at hm
    obtain ⟨rfl, rfl, rfl⟩ := prev_injective hm
    rfl
  · obtain ⟨a, ha⟩ := (mem_parents_hc _ _ _).1 hm
    exact absurd ha.symm (prev_ne_kidName _ _ _ _ _)
  · obtain ⟨b', hb'⟩ := (mem_parents_rc _).1 hm
    exact absurd hb'.symm (prev_ne_kidName _ _ _ _ (Kid.h 10))
  · simp only [parents, Finset.mem_singleton] at hm
    exact absurd hm.symm (prev_ne_kidName _ _ _ _ _)
  · obtain ⟨a, ha⟩ := (mem_parents_hc _ _ _).1 hm
    obtain ⟨rfl, hk⟩ := kidName_injective ha
    rw [((kid_eq_kid_two_iff _ _ a).1 hk).1]
  · obtain ⟨b', hb'⟩ := (mem_parents_rc _).1 hm
    exact absurd (kidName_injective (κ := Kid.h 10) hb').2.symm (kid_ne_top _ 2)
  · simp only [parents, Finset.mem_singleton] at hm
    exact absurd hm.symm (prev_ne_kidName _ _ _ _ (Kid.h 10))
  · obtain ⟨a, ha⟩ := (mem_parents_hc _ _ _).1 hm
    exact absurd (kidName_injective (κ' := Kid.h 10) ha).2 (kid_ne_top _ a)
  · rfl

/-- The exclusive kid is read only by the input of its hash node. -/
theorem consumer_of_exclOf {h p m : Name} (hp : hashParent h = some p)
    (hm : exclOf h ∈ parents m) : m = p := by
  have hlen := len_of_mem_parents_compress hp (exclOf_mem hp)
  rcases mem_parents_cases hm with ⟨p', hp', e⟩ | hv | ⟨h', hp', -⟩
  · rw [e] at hlen
    exact absurd hlen (len_hashParent_ne_129 hp')
  · rw [len_of_hashOf hv] at hlen
    omega
  · exact compress_reader_of_exclOf hp hp' hm

/-- The low 129 input bits of a hash node are its exclusive kid. -/
theorem lowWord_detVal_compress {h p : Name} (hp : hashParent h = some p)
    (x : Asg) : lowWord (detVal p x) = lowWord (x (exclOf h).fin) := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp
  · show lowWord (tw _ ++ lowWord (x _)) = _
    rw [lowWord_tw_append le_rfl, lowWord_lowWord]
    rfl
  · show lowWord (tw _ ++ cat3 _ _ _) = _
    rw [lowWord_tw_append (by norm_num), lowWord_cat3]
    rfl
  · show lowWord (tw _ ++ cat7 _) = _
    rw [lowWord_tw_append (by norm_num), lowWord_cat7]
    rfl

/-- A compression input determines the low 129 bits of each of its inputs. -/
theorem compress_inj {h p : Name} (hp : hashParent h = some p) {x x' : Asg}
    (e : detVal p x = detVal p x') {n : Name} (hn : n ∈ parents p) :
    lowWord (x n.fin) = lowWord (x' n.fin) := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> simp only [parents, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and] at hn
  · subst hn
    exact (bv_append_inj e).2
  · rename_i b j
    obtain ⟨a, rfl⟩ := hn
    obtain ⟨h0, h1, h2⟩ := cat3_inj (bv_append_inj e).2
    fin_cases a
    · exact h0
    · exact h1
    · exact h2
  · obtain ⟨b, rfl⟩ := hn
    exact congrFun (cat7_inj (bv_append_inj e).2) b

/-! ## Concrete record values -/

abbrev Rec := graph.Rec

def val (ξ : Rec) (n : Name) : BitVec n.len :=
  (graph.evalRec ξ n.fin).cast (graph_len_fin n)

theorem evalRec_apply_fin (ξ : Rec) (n : Name) :
    graph.evalRec ξ n.fin =
      (kindOf n.fin n (Name.ofFin_fin n)).value
        (graph.evalRec ξ) (ξ.1 n.fin) (ξ.2 n.fin) := by
  have h := Graph.evalRec_apply graph ξ n.fin
  rwa [graph_kind_fin] at h

theorem lowWord_evalRec (ξ : Rec) (n : Name) :
    lowWord (graph.evalRec ξ n.fin) = lowWord (val ξ n) := by
  unfold val
  exact (lowWord_cast _ _).symm

theorem val_src (ξ : Rec) (b : Fin 7) (k : Fin 8) :
    val ξ (.src b k) = (ξ.1 (Name.src b k).fin).cast (graph_len_fin _) := by
  unfold val
  rw [evalRec_apply_fin]
  rfl

/-- A deterministic node evaluates its public function on the record values. -/
theorem val_det {n : Name} (hc : n.cost = 0) (hs : ∀ b k, n ≠ .src b k)
    (ξ : Rec) : val ξ n = detVal n (graph.evalRec ξ) := by
  unfold val
  rw [evalRec_apply_fin]
  cases n
  all_goals first
    | exact (hs _ _ rfl).elim
    | (simp only [kindOf, NodeKind.value]; exact cast_cast_eq _ _ _)
    | (exfalso; simp [Name.cost] at hc)

theorem lowWord_val_hash {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    lowWord (val ξ h) = lowWord (ξ.2 h.fin) := by
  unfold val
  rw [lowWord_cast, evalRec_apply_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    simp only [kindOf, NodeKind.value] <;> exact lowWord_cast _ _

theorem val_rh (ξ : Rec) : val ξ .rh = ξ.2 Name.rh.fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem lowWord_detVal_value {v h : Name} (hh : hashOf v = some h) (x : Asg) :
    lowWord (detVal v x) = lowWord (x h.fin) := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst hh <;> exact lowWord_lowWord _

theorem not_src_of_hashOf {v h : Name} (hh : hashOf v = some h) :
    ∀ b k, v ≠ .src b k := by
  intro b k e
  subst e
  simp [hashOf] at hh

/-- A value node is the low word of the hash output it reads. -/
theorem lowWord_val_value {v h : Name} (hh : hashOf v = some h) (ξ : Rec) :
    lowWord (val ξ v) = lowWord (ξ.2 h.fin) := by
  obtain ⟨p, hp⟩ := hashParent_of_hashOf hh
  rw [val_det (cost_of_hashOf hh) (not_src_of_hashOf hh)]
  refine (lowWord_detVal_value hh (graph.evalRec ξ)).trans ?_
  exact (lowWord_evalRec ξ h).trans (lowWord_val_hash hp ξ)

def pkOf (ξ : Rec) : BitVec 128 := lowPk (ξ.2 Name.rh.fin)
/-! ## Hash inputs and graph tagging -/

def pointOf (ξ : Rec) (_h p : Name) : Query := ⟨p.len, val ξ p⟩

def tagNat (q : Query) : ℕ := WideForest.tagNat q

theorem tagNat_append {n : ℕ} (a : BitVec 16) (u : BitVec n) :
    tagNat ⟨16 + n, a ++ u⟩ = a.toNat :=
  WideForest.tagNat_append a u

theorem tagNat_tw_append {n : ℕ} (h : Name) (u : BitVec n) :
    tagNat ⟨16 + n, tw h ++ u⟩ = h.idx := by
  rw [tagNat_append, tw_toNat]

theorem tagNat_cast {n m : ℕ} (e : n = m) (u : BitVec n) :
    tagNat ⟨m, u.cast e⟩ = tagNat ⟨n, u⟩ :=
  WideForest.tagNat_cast e u

theorem tagNat_detVal_of_hashParent {h p : Name}
    (hp : hashParent h = some p) (x : Asg) :
    tagNat ⟨p.len, detVal p x⟩ = h.idx := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> exact tagNat_tw_append _ _

theorem tagNat_cast_detVal_of_hashParent {h p : Name}
    (hp : hashParent h = some p) (x : Asg) {m : ℕ} (e : p.len = m) :
    tagNat ⟨m, (detVal p x).cast e⟩ = h.idx := by
  rw [tagNat_cast, tagNat_detVal_of_hashParent hp]

theorem val_hashParent {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    val ξ p = detVal p (graph.evalRec ξ) :=
  val_det (cost_hashParent hp) (hashParent_ne_src hp) ξ

theorem tagNat_val {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    tagNat ⟨p.len, val ξ p⟩ = h.idx := by
  rw [val_hashParent hp]
  exact tagNat_detVal_of_hashParent hp _

theorem tagNat_pointOf {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    tagNat (pointOf ξ h p) = h.idx := tagNat_val hp ξ

theorem pointOf_inj_left {ξ ξ' : Rec} {h h' p p' : Name}
    (hp : hashParent h = some p) (hp' : hashParent h' = some p')
    (e : pointOf ξ h p = pointOf ξ' h' p') : h = h' := by
  apply Name.idx_injective
  rw [← tagNat_pointOf hp ξ, ← tagNat_pointOf hp' ξ', e]

theorem pointOf_inj_input {ξ ξ' : Rec} {h p : Name}
    (e : pointOf ξ h p = pointOf ξ' h p) : val ξ p = val ξ' p := by
  simp only [pointOf, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
  exact e

theorem pointOf_ne_encQuery {h p : Name} (hp : hashParent h = some p)
    (ξ : Rec) (u : EncInput) : pointOf ξ h p ≠ encQuery u :=
  ne_encQuery_of_length_ne (len_hashParent_ne_enc hp) u

theorem mk_ne_encQuery {h p : Name} (hp : hashParent h = some p)
    (u' : BitVec p.len) (u : EncInput) :
    (⟨p.len, u'⟩ : Query) ≠ encQuery u :=
  ne_encQuery_of_length_ne (len_hashParent_ne_enc hp) u

theorem sigma_mk_cast_eq {n m : ℕ} (h : n = m) (x : BitVec n) :
    (⟨n, x⟩ : Σ k, BitVec k) = ⟨m, x.cast h⟩ := by
  subst h
  rfl

theorem sigma_val (ξ : Rec) (p : Name) :
    (⟨graph.len p.fin, graph.evalRec ξ p.fin⟩ : Σ k, BitVec k) =
      ⟨p.len, val ξ p⟩ := by
  unfold val
  generalize graph.evalRec ξ p.fin = x
  exact sigma_mk_cast_eq (graph_len_fin p) x

theorem graph_point_fin (ξ : Rec) (h : Name) :
    graph.point (graph.evalRec ξ) h.fin =
      (hashParent h).map fun p => pointOf ξ h p := by
  unfold Graph.point
  rw [graph_kind_fin]
  cases h <;> simp only [kindOf, hashParent, Option.map_some, Option.map_none, pointOf]
  all_goals exact congrArg some (sigma_val ξ _)

def tagOf (q : Query) : Option (Fin N) :=
  if h : tagNat q < N then some ⟨tagNat q, h⟩ else none

theorem tagOf_eq_some_of_tagNat {q : Query} {h : Name}
    (e : tagNat q = h.idx) : tagOf q = some h.fin := by
  unfold tagOf
  rw [dif_pos (by rw [e]; exact h.idx_lt)]
  exact congrArg some (Fin.ext e)

theorem graph_kind_hashParent {h p : Name} (hp : hashParent h = some p) :
    ∃ ps hps hf, graph.kind p.fin =
      .det ps hps (fun x => (detVal p x).cast (graph_len_fin p).symm) hf := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> exact ⟨_, _, _, rfl⟩

theorem graph_kind_eq_hash {h : Name} {q : Fin N} {hq : q < h.fin}
    {hl : lenF h.fin = 256} (hk : graph.kind h.fin = .hash q hq hl) :
    ∃ p, hashParent h = some p ∧ q = p.fin := by
  rw [graph_kind_fin] at hk
  cases h <;> simp only [kindOf, reduceCtorEq] at hk
  all_goals exact ⟨_, rfl, (NodeKind.hash.inj hk).symm⟩

def tagging : graph.Tagging where
  tag q := if h : tagNat q < N then some ⟨tagNat q, h⟩ else none
  tag_parent := by
    intro v q hq hl hk
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨Name.ofFin v, Name.fin_ofFin v⟩
    obtain ⟨p, hp, rfl⟩ := graph_kind_eq_hash hk
    obtain ⟨ps, hps, hf, hkp⟩ := graph_kind_hashParent hp
    refine ⟨ps, hps, _, hf, hkp, fun x => ?_⟩
    exact tagOf_eq_some_of_tagNat
      (tagNat_cast_detVal_of_hashParent hp x (graph_len_fin p).symm)

/-! ## Key-generation cache split -/

def kc (ξ : Rec) : Cache := graph.keygenCache ξ

theorem kc_apply_iff (ξ : Rec) (q : Query) (w : BitVec 256) :
    kc ξ q = some w ↔
      ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p ∧ w = ξ.2 h.fin := by
  refine (Graph.keygenCache_apply_iff graph tagging ξ q w).trans ?_
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨Name.ofFin v, Name.fin_ofFin v⟩
    rw [graph_point_fin, Option.map_eq_some_iff] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact ⟨h, p, hp, rfl, rfl⟩
  · rintro ⟨h, p, hp, rfl, rfl⟩
    exact ⟨h.fin, by rw [graph_point_fin, hp]; rfl, rfl⟩

theorem kc_isSome_iff (ξ : Rec) (q : Query) :
    (kc ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hw
    exact ⟨h, p, hp, hq⟩
  · rintro ⟨h, p, hp, hq⟩
    exact ⟨_, (kc_apply_iff ξ q _).2 ⟨h, p, hp, hq, rfl⟩⟩

theorem kc_enc (ξ : Rec) (u : EncInput) : kc ξ (encQuery u) = none := by
  rcases hk : kc ξ (encQuery u) with _ | w
  · rfl
  · obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ _ w).1 hk
    exact absurd hq.symm (pointOf_ne_encQuery hp ξ u)

def Exposed (A? : Option (Finset Name)) (h : Name) : Prop :=
  ∃ A, A? = some A ∧ Evaluated A h

theorem exposed_some_iff_evaluated (A : Finset Name) (h : Name) :
    Exposed (some A) h ↔ Evaluated A h := by simp [Exposed]

theorem not_exposed_none (h : Name) : ¬ Exposed none h := by
  rintro ⟨A, hA, -⟩
  cases hA

def fExp (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  then kc ξ q else none

def fHid (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p
  then kc ξ q else none

theorem extend_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.extend (fExp A? ξ) (fHid A? ξ) = kc ξ := by
  funext q
  simp only [Cache.extend_apply, fExp, fHid]
  by_cases h1 : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rw [if_pos h1]
    obtain ⟨h, p, hp, -, hq⟩ := h1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
      ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩)
    rw [hw]
    rfl
  · rw [if_neg h1, Option.none_or]
    by_cases h2 : ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p
    · rw [if_pos h2]
    · rw [if_neg h2]
      rcases hk : kc ξ q with _ | w
      · rfl
      · exfalso
        obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
        by_cases he : Exposed A? h
        · exact h1 ⟨h, p, hp, he, hq⟩
        · exact h2 ⟨h, p, hp, he, hq⟩

theorem disjoint_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.Disjoint (fExp A? ξ) (fHid A? ξ) := by
  intro q hq
  simp only [fHid] at hq
  split_ifs at hq with h2
  · obtain ⟨h, p, hp, he, hq⟩ := h2
    simp only [fExp]
    rw [if_neg]
    rintro ⟨h', p', hp', he', hq'⟩
    rw [hq] at hq'
    obtain rfl := pointOf_inj_left hp hp' hq'
    exact he he'
  · simp at hq

theorem fHid_isSome_iff (A? : Option (Finset Name)) (ξ : Rec) (q : Query) :
    (fHid A? ξ q).isSome ↔
      ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p := by
  simp only [fHid]
  split_ifs with hc
  · obtain ⟨h, p, hp, -, hq⟩ := id hc
    exact iff_of_true ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩) hc
  · exact iff_of_false (by simp) hc

theorem fHid_none (ξ : Rec) : fHid none ξ = kc ξ := by
  funext q
  simp only [fHid]
  split_ifs with hc
  · rfl
  · rcases hk : kc ξ q with _ | w
    · rfl
    · exfalso
      obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
      exact hc ⟨h, p, hp, not_exposed_none h, hq⟩

theorem fExp_none (ξ : Rec) : fExp none ξ = ∅ := by
  funext q
  simp only [fExp]
  rw [if_neg]
  · rfl
  · rintro ⟨h, -, -, he, -⟩
    exact not_exposed_none h he

theorem fExp_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fExp A? ξ (encQuery u) = none := by
  simp only [fExp]
  rw [if_neg]
  rintro ⟨h, p, hp, -, hq⟩
  exact pointOf_ne_encQuery hp ξ u hq.symm

theorem fHid_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fHid A? ξ (encQuery u) = none := by
  simp only [fHid]
  rw [if_neg]
  rintro ⟨h, p, hp, -, hq⟩
  exact pointOf_ne_encQuery hp ξ u hq.symm

theorem fHid_isSome_some_iff (A : Finset Name) (ξ : Rec) (q : Query) :
    (fHid (some A) ξ q).isSome ↔
      ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧ q = pointOf ξ h p := by
  simp only [fHid_isSome_iff, exposed_some_iff_evaluated]

/-! ## Spurious authentication and its exact fresh-query charge -/

def bindingWidth (h : Name) : ℕ := if h = Name.rh then 128 else 129

def bindingValue (h : Name) (w : BitVec 256) : BitVec (bindingWidth h) :=
  w.setWidth (bindingWidth h)

def Spr (c : Cache) (ξ : Rec) : Prop :=
  ∃ h p, hashParent h = some p ∧
    ∃ u : BitVec p.len, u ≠ val ξ p ∧ tagNat ⟨p.len, u⟩ = h.idx ∧
      ∃ w, c ⟨p.len, u⟩ = some w ∧
        bindingValue h w = bindingValue h (ξ.2 h.fin)

theorem Spr.mono {c c' : Cache} (h : Cache.Sub c c') {ξ : Rec}
    (hs : Spr c ξ) : Spr c' ξ := by
  obtain ⟨hn, p, hp, u, hu, htag, w, hw, ht⟩ := hs
  exact ⟨hn, p, hp, u, hu, htag, w, h _ _ hw, ht⟩

theorem spr_cacheQuery_enc (c : Cache) (ξ : Rec) (u : EncInput)
    (w : BitVec 256) : Spr (c.cacheQuery (encQuery u) w) ξ ↔ Spr c ξ := by
  have key : ∀ (h p : Name), hashParent h = some p → ∀ u' : BitVec p.len,
      c.cacheQuery (encQuery u) w ⟨p.len, u'⟩ = c ⟨p.len, u'⟩ :=
    fun h p hp u' => QueryCache.cacheQuery_of_ne _ _ (mk_ne_encQuery hp u' u)
  constructor
  · rintro ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
    rw [key h p hp] at hw
    exact ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
  · rintro ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
    refine ⟨h, p, hp, u', hu, htag, w', ?_, ht⟩
    rw [key h p hp]
    exact hw

theorem spr_of_extend {c f : Cache} {ξ : Rec}
    (hs : Spr (Cache.extend c f) ξ) : Spr c ξ ∨ Spr f ξ := by
  obtain ⟨h, p, hp, u, hu, htag, w, hw, ht⟩ := hs
  rw [Cache.extend_apply, Option.or_eq_some_iff] at hw
  rcases hw with hw | ⟨-, hw⟩
  · exact Or.inl ⟨h, p, hp, u, hu, htag, w, hw, ht⟩
  · exact Or.inr ⟨h, p, hp, u, hu, htag, w, hw, ht⟩

theorem not_spr_kc (ξ : Rec) : ¬ Spr (kc ξ) ξ := by
  rintro ⟨h, p, hp, u, hu, htag, w, hw, -⟩
  obtain ⟨h', p', hp', hq, -⟩ := (kc_apply_iff ξ _ w).1 hw
  have hh : h = h' := by
    apply Name.idx_injective
    rw [← htag, hq, tagNat_pointOf hp' ξ]
  subst hh
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  exact hu (eq_of_heq (Sigma.mk.inj_iff.1 hq).2)

theorem sub_fExp_kc (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.Sub (fExp A? ξ) (kc ξ) := by
  intro q w hw
  simp only [fExp] at hw
  by_cases hc : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rwa [if_pos hc] at hw
  · rw [if_neg hc] at hw
    cases hw

theorem not_spr_fExp (A? : Option (Finset Name)) (ξ : Rec) :
    ¬ Spr (fExp A? ξ) ξ :=
  fun hs => not_spr_kc ξ (hs.mono (sub_fExp_kc A? ξ))

theorem not_spr_empty (ξ : Rec) : ¬ Spr ∅ ξ := by
  rintro ⟨h, p, hp, u, hu, -, w, hw, -⟩
  simp at hw

def ε : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 129)⁻¹

theorem inv_card_bitVec_mul_two_pow :
    (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      ((2 ^ 127 : ℕ) : ℝ≥0∞) = ε := by
  have h0 : (2 : ℝ≥0∞) ^ 127 ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ 127 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : (2 : ℝ≥0∞) ^ 129 * 2 ^ 127 = 2 ^ 256 := by rw [← pow_add]
  rw [Fintype.card_bitVec, ε]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← e, ENNReal.mul_inv (Or.inr ht) (Or.inr h0), mul_assoc,
    ENNReal.inv_mul_cancel h0 ht, mul_one]

def sprRate (h : Name) : ℝ≥0∞ := if h = Name.rh then ε + ε else ε

theorem bindingWidth_le (h : Name) : bindingWidth h ≤ 256 := by
  simp only [bindingWidth]
  split_ifs <;> omega

theorem binding_fiber (h : Name) (a : BitVec (bindingWidth h)) :
    (Finset.univ.filter fun b : BitVec 256 => bindingValue h b = a).card =
      2 ^ (256 - bindingWidth h) :=
  TruncFiber.card_filter_setWidth (bindingWidth_le h) a

theorem inv_card_binding (h : Name) :
    (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      ((2 ^ (256 - bindingWidth h) : ℕ) : ℝ≥0∞) = sprRate h := by
  by_cases hh : h = Name.rh
  · simp only [bindingWidth, sprRate, if_pos hh]
    change (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      ((2 ^ 128 : ℕ) : ℝ≥0∞) = ε + ε
    have he : (2 : ℕ)^128 = 2^127 + 2^127 := by
      rw [show (128 : ℕ) = 127 + 1 from rfl, pow_succ, mul_two]
    rw [he, Nat.cast_add, mul_add, inv_card_bitVec_mul_two_pow]
  · simp only [bindingWidth, sprRate, if_neg hh]
    exact inv_card_bitVec_mul_two_pow

theorem epsilon_le_query_cost (q : Query) :
    ε ≤ ε * (blockCost q.1 : ℝ≥0∞) := by
  have hc : (1 : ℝ≥0∞) ≤ (blockCost q.1 : ℝ≥0∞) := by
    exact_mod_cast Nat.le_max_left 1 ((q.1 + blockBits - 1) / blockBits)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc
    (show (0 : ℝ≥0∞) ≤ ε from zero_le)

theorem sprRate_le_query_cost {h p : Name} (hp : hashParent h = some p)
    (q : Query) (hlen : q.1 = p.len) :
    sprRate h ≤ ε * (blockCost q.1 : ℝ≥0∞) := by
  by_cases hh : h = Name.rh
  · subst h
    simp only [hashParent, Option.some.injEq] at hp
    subst p
    rw [sprRate, if_pos rfl, hlen]
    change ε + ε ≤ ε * (blockCost 919 : ℝ≥0∞)
    have hc : blockCost 919 = 2 := by norm_num [blockCost, blockBits]
    rw [hc, Nat.cast_ofNat, mul_two]
  · rw [sprRate, if_neg hh]
    exact epsilon_le_query_cost q

theorem spr_charge (c : Cache) (ξ : Rec) (q : Query) (_hq : c q = none) :
    ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      (if Spr (c.cacheQuery q b) ξ then 1 else 0) ≤
        (if Spr c ξ then 1 else 0) + ε * (blockCost q.1 : ℝ≥0∞) := by
  by_cases hs : Spr c ξ
  · rw [if_pos hs]
    calc
      ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (if Spr (c.cacheQuery q b) ξ then 1 else 0)
          ≤ ∑ _b : BitVec 256,
              (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 1 := by
            refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ zero_le
            split_ifs <;> simp
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)]
      _ ≤ _ := le_self_add
  · rw [if_neg hs, zero_add]
    have key : ∀ b, Spr (c.cacheQuery q b) ξ →
        ∃ h p, hashParent h = some p ∧ q.1 = p.len ∧ tagNat q = h.idx ∧
          bindingValue h b = bindingValue h (ξ.2 h.fin) := by
      rintro b ⟨h, p, hp, u, hu, htag, b', hb', ht⟩
      by_cases hqq : (⟨p.len, u⟩ : Query) = q
      · subst hqq
        rw [QueryCache.cacheQuery_self] at hb'
        obtain rfl := Option.some.inj hb'
        exact ⟨h, p, hp, rfl, htag, ht⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hb'
        exact (hs ⟨h, p, hp, u, hu, htag, b', hb', ht⟩).elim
    by_cases hex : ∃ h₀ p₀, hashParent h₀ = some p₀ ∧
        q.1 = p₀.len ∧ tagNat q = h₀.idx
    · obtain ⟨h₀, p₀, hp₀, hlen₀, hq₀⟩ := hex
      have key' : ∀ b, Spr (c.cacheQuery q b) ξ →
          bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin) := by
        intro b hb
        obtain ⟨h, p, hp, hlen, hq', ht⟩ := key b hb
        have he : h₀ = h := Name.idx_injective (hq₀.symm.trans hq')
        subst he
        exact ht
      calc
        ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if Spr (c.cacheQuery q b) ξ then 1 else 0)
            ≤ ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
              (if bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin) then 1 else 0) := by
              refine Finset.sum_le_sum fun b _ =>
                mul_le_mul_of_nonneg_left ?_ zero_le
              split_ifs with h1 h2
              · exact le_rfl
              · exact absurd (key' b h1) h2
              · exact zero_le_one
              · exact le_rfl
        _ = (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun b : BitVec 256 =>
              bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin)).card : ℝ≥0∞) := by
              rw [← Finset.mul_sum, Finset.sum_boole]
        _ = sprRate h₀ := by rw [binding_fiber, inv_card_binding]
        _ ≤ _ := sprRate_le_query_cost hp₀ q hlen₀
    · have hno : ∀ b, ¬ Spr (c.cacheQuery q b) ξ := fun b hb => by
        obtain ⟨h, p, hp, hlen, htag, _⟩ := key b hb
        exact hex ⟨h, p, hp, hlen, htag⟩
      rw [Finset.sum_eq_zero fun b _ => by rw [if_neg (hno b), mul_zero]]
      exact zero_le

theorem two_epsilon_eq_half_kappa :
    ε + ε = (((2 : ℝ≥0∞)^127)⁻¹) / 2 := by
  have hstep (n : ℕ) :
      ((2 : ℝ≥0∞)^(n+1))⁻¹ = ((2 : ℝ≥0∞)^n)⁻¹ / 2 := by
    rw [pow_succ, ENNReal.mul_inv
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      (Or.inr two_ne_zero), div_eq_mul_inv]
  calc
    ε + ε = ((2 : ℝ≥0∞)^128)⁻¹ / 2 +
        ((2 : ℝ≥0∞)^128)⁻¹ / 2 := by
      rw [ε, show (129 : ℕ) = 128 + 1 from rfl, hstep]
    _ = ((2 : ℝ≥0∞)^128)⁻¹ := ENNReal.add_halves _
    _ = _ := hstep 127

def authRate : ℝ≥0∞ := (((2 : ℝ≥0∞)^127)⁻¹) / 2

theorem authentication_charge_budget (q : Query) :
    ε + ε * (blockCost q.1 : ℝ≥0∞) ≤
      authRate * (blockCost q.1 : ℝ≥0∞) := by
  calc
    ε + ε * (blockCost q.1 : ℝ≥0∞)
        ≤ ε * (blockCost q.1 : ℝ≥0∞) +
          ε * (blockCost q.1 : ℝ≥0∞) :=
      add_le_add (epsilon_le_query_cost q) le_rfl
    _ = (ε + ε) * (blockCost q.1 : ℝ≥0∞) := (add_mul ..).symm
    _ = _ := by rw [two_epsilon_eq_half_kappa]; rfl

/-! ## Authentication potential and free index queries -/

/-- Uniform mass of one complete key-generation record. -/
def w : ℝ≥0∞ := (Fintype.card Rec : ℝ≥0∞)⁻¹

theorem sum_w : ∑ _ξ : Rec, w = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, w]
  exact ENNReal.mul_inv_cancel
    (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

def sumW (T : Finset Rec) : ℝ≥0∞ := ∑ ξ ∈ T, w

def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

def authPotential (T : Finset Rec) (A? : Option (Finset Name))
    (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ T, w *
    (ind (Cache.Hits c (fHid A? ξ)) + ind (Spr c ξ))

theorem avg_sum_comm (T : Finset Rec)
    (f : Rec → BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * f ξ u =
      ∑ ξ ∈ T, w *
        ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f ξ u := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ξ _ =>
    Finset.sum_congr rfl fun u _ => ?_
  ring

theorem avg_const (X : ℝ≥0∞) :
    ∑ _u : BitVec hashBits,
      (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * X = X :=
  WideForest.avg_const X

theorem ind_congr {p r : Prop} (h : p ↔ r) : ind p = ind r := by
  unfold ind
  simp only [h]

theorem hits_avg_eq (T : Finset Rec) (f : Rec → Cache)
    (c : Cache) (q : Query) (hf : ∀ ξ, f ξ q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f ξ)) =
      ∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  simp only [Cache.hits_cacheQuery, hf, Option.isSome_none,
    Bool.false_eq_true, or_false]

theorem spr_avg_eq (T : Finset Rec) (c : Cache) (u₀ : EncInput) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Spr (c.cacheQuery (encQuery u₀) u) ξ) =
      ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Spr c ξ))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  exact spr_cacheQuery_enc c ξ u₀ u

theorem authPotential_eq (T : Finset Rec) (A? : Option (Finset Name))
    (c : Cache) :
    authPotential T A? c =
      (∑ ξ ∈ T, w * ind (Cache.Hits c (fHid A? ξ))) +
        ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  simp only [authPotential, mul_add, Finset.sum_add_distrib]

/-- Index queries cannot affect graph authentication: their length differs
from every graph hash input, and hidden keygen caches are empty there. -/
theorem authPotential_index (T : Finset Rec)
    (A? : Option (Finset Name)) (c : Cache) (u₀ : EncInput) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T A? (c.cacheQuery (encQuery u₀) u)) =
        authPotential T A? c := by
  simp only [authPotential_eq, mul_add, Finset.sum_add_distrib]
  rw [hits_avg_eq _ _ _ _ (fun ξ => fHid_enc A? ξ u₀), spr_avg_eq]

/-! The two record partitions used by the actual security game.  Their
resampling closure and hidden-input charge are the next graph-specific layer. -/

def fiberA (pk : BitVec 128) : Finset Rec :=
  Finset.univ.filter fun ξ => pkOf ξ = pk

abbrev Data := BitVec 128 × List Bool × Cache

def revealed (A : Finset Name) (ξ : Rec) : List Bool :=
  graph.encode (fins A) (graph.evalRec ξ)

def dataOf (A : Finset Name) (ξ : Rec) : Data :=
  (pkOf ξ, revealed A ξ, fExp (some A) ξ)

def fiberB (A : Finset Name) (d : Data) : Finset Rec :=
  Finset.univ.filter fun ξ => dataOf A ξ = d

/-! ## Signing locality

The generic replacement signer only inserts message/nonce index queries.  The
following interface records exactly that fact and shows that such an extension
neither hits a hidden graph point nor changes `Spr`.
-/

def IndexExtension (d d' : Cache) : Prop := Cache.Sub d d' ∧
  ∀ q v, d q = none → d' q = some v → ∃ u : EncInput, q = encQuery u

theorem sub_extend_left (c f : Cache) : Cache.Sub c (Cache.extend c f) :=
  fun _ _ h => Cache.extend_apply_of_some h

theorem indexExtension_kc_none {d d' : Cache} (hd' : IndexExtension d d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) {q : Query}
    (hq : (kc ξ q).isSome) : d' q = none := by
  rcases hq' : d' q with _ | v
  · rfl
  · exfalso
    rcases hdq : d q with _ | u
    · obtain ⟨u₀, hqe⟩ := hd'.2 q v hdq hq'
      rw [hqe, kc_enc] at hq
      simp at hq
    · exact hξ ⟨q, hq, by rw [hdq]; rfl⟩

theorem not_hits_fHid_of_indexExtension {d d' : Cache}
    (hd' : IndexExtension d d') {ξ : Rec}
    (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits d' (fHid A? ξ) := by
  rintro ⟨q, hq, hq'⟩
  have hkq : (kc ξ q).isSome := by
    obtain ⟨h, p, hp, -, hqp⟩ := (fHid_isSome_iff A? ξ q).1 hq
    exact (kc_isSome_iff ξ q).2 ⟨h, p, hp, hqp⟩
  rw [indexExtension_kc_none hd' hξ hkq] at hq'
  simp at hq'

theorem not_hits_extend_fExp_fHid {d d' : Cache}
    (hd' : IndexExtension d d') {ξ : Rec}
    (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
  rw [Cache.hits_extend]
  rintro (h | h)
  · exact not_hits_fHid_of_indexExtension hd' hξ A? h
  · exact (disjoint_fExp_fHid A? ξ).not_hits h

theorem spr_indexExtension_iff {d d' : Cache}
    (hd' : IndexExtension d d') (ξ : Rec) : Spr d' ξ ↔ Spr d ξ := by
  constructor
  · rintro ⟨h, p, hp, u, hu, htag, w', hw, htr⟩
    refine ⟨h, p, hp, u, hu, htag, w', ?_, htr⟩
    rcases hdq : d ⟨p.len, u⟩ with _ | v
    · exfalso
      obtain ⟨u₀, hqe⟩ := hd'.2 _ w' hdq hw
      exact mk_ne_encQuery hp u _ hqe
    · rw [hd'.1 _ _ hdq] at hw
      exact hw
  · exact Spr.mono hd'.1

theorem spr_extend_fExp_iff {d d' : Cache}
    (hd' : IndexExtension d d') (ξ : Rec)
    (A? : Option (Finset Name)) :
    Spr (Cache.extend d' (fExp A? ξ)) ξ ↔ Spr d ξ := by
  constructor
  · intro hs
    rcases spr_of_extend hs with hs | hs
    · exact (spr_indexExtension_iff hd' ξ).1 hs
    · exact absurd hs (not_spr_fExp A? ξ)
  · intro hs
    exact Spr.mono (sub_extend_left d' _)
      ((spr_indexExtension_iff hd' ξ).2 hs)

theorem authPotential_after_sign {d d' : Cache}
    (hd' : IndexExtension d d') (T : Finset Rec)
    (A? : Option (Finset Name))
    (hT : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (fe : Cache) (he : ∀ ξ ∈ T, fExp A? ξ = fe) :
    authPotential T A? (Cache.extend d' fe) =
      ∑ ξ ∈ T, w * ind (Spr d ξ) := by
  unfold authPotential
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [← he ξ hξ]
  have hh := not_hits_extend_fExp_fHid hd' (hT ξ hξ) A?
  have hs := spr_extend_fExp_iff hd' ξ A?
  simp only [ind, if_neg hh, hs, zero_add]

theorem sign_indexExtension {M' : ℕ} (S : WeightedScheme.Scheme M')
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) c)) : IndexExtension c p.2 := by
  refine ⟨sub_of_mem_support_run _ c p hp, ?_⟩
  intro q v hc he
  obtain ⟨η, hη⟩ :=
    ReplacementLocality.sign_new_cache_row S x m c p hp q v hc he
  exact ⟨(m, η), hη⟩

theorem authPotential_after_actual_sign {M' : ℕ}
    (S : WeightedScheme.Scheme M') (x : S.graph.Assignment)
    (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) c))
    (T : Finset Rec) (A? : Option (Finset Name))
    (hT : ∀ ξ ∈ T, ¬ Cache.Hits c (kc ξ))
    (fe : Cache) (he : ∀ ξ ∈ T, fExp A? ξ = fe) :
    authPotential T A? (Cache.extend p.2 fe) =
      ∑ ξ ∈ T, w * ind (Spr c ξ) :=
  authPotential_after_sign (sign_indexExtension S x m c p hp)
    T A? hT fe he

#print axioms spr_charge
#print axioms authentication_charge_budget
#print axioms not_spr_kc
#print axioms authPotential_index
#print axioms authPotential_after_actual_sign

end OptimalOTS.WeightedConstruction.LongChain91
