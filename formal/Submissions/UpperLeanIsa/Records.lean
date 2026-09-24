import Submissions.UpperLeanIsa.QueryLayout
import Submissions.UpperLeanIsa.Cache

/-! Independent source/output records and their programmed oracle points.
The position tags make distinct locations disjoint for every record, without a
probabilistic collision exception. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleSpec
open scoped Classical

abbrev ChainLocation := Fin 43 × Fin 127
abbrev HashLocation := ChainLocation ⊕ Fin 43
abbrev Record := Words × (HashLocation → BitVec hashBits)

def Record.word (ξ : Record) (i : Fin 43) (j : Fin 128) : Word :=
  if h : j.val = 0 then ξ.1 i
  else (ξ.2 (.inl (i, ⟨j.val - 1, by have := j.isLt; omega⟩))).extractLsb' 0 128

def Record.endpoint (ξ : Record) (i : Fin 43) : Word := ξ.word i 127

def Record.rootBefore (ξ : Record) (i : Fin 43) : BitVec 256 :=
  if h : i.val = 0 then 0
  else ξ.2 (.inr ⟨i.val - 1, by have := i.isLt; omega⟩)

def rootTag (i : Fin 43) : Fin 43 := ⟨42 - i.val, by omega⟩

theorem rootTag_injective : Function.Injective rootTag := by
  intro i j h
  have hn := congrArg Fin.val h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  change 42 - i.val = 42 - j.val at hn
  omega

def Record.input (ξ : Record) : HashLocation → BitVec 896
  | .inl (i, j) => chainInput i.val j.val (ξ.word i j.castSucc)
  | .inr i => rootInput (rootTag i) (ξ.rootBefore i) (ξ.endpoint i)

def Record.query (ξ : Record) (a : HashLocation) : Query := ⟨896, ξ.input a⟩

/-- Even different records cannot place different locations at the same oracle input. -/
theorem location_eq_of_input_eq (ξ ζ : Record) (a b : HashLocation)
    (h : ξ.input a = ζ.input b) : a = b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hs := (chainInput_eq_iff a.1 b.1 a.2 b.2 _ _).mp h
      exact congrArg Sum.inl (Prod.ext hs.1 hs.2.1)
    | inr b => exact (chainInput_ne_rootInput _ _ _ _ _ _ h).elim
  | inr a =>
    cases b with
    | inl b => exact (chainInput_ne_rootInput _ _ _ _ _ _ h.symm).elim
    | inr b =>
      have hs := (rootInput_eq_iff _ _ _ _ _ _).mp h
      exact congrArg Sum.inr (rootTag_injective hs.1)

theorem location_eq_of_query_eq (ξ ζ : Record) (a b : HashLocation)
    (h : ξ.query a = ζ.query b) : a = b := by
  apply location_eq_of_input_eq ξ ζ a b
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

theorem Record.query_injective (ξ : Record) : Function.Injective ξ.query :=
  fun a b h => location_eq_of_query_eq ξ ξ a b h

/-- The domain decoder depends only on the query, never on a particular sampled record. -/
noncomputable def queryLocation (q : Query) : Option HashLocation :=
  @dite (Option HashLocation) (∃ p : Record × HashLocation, p.1.query p.2 = q)
    (Classical.propDecidable _)
    (fun h => some (Classical.choose h).2) (fun _ => none)

theorem queryLocation_query (ξ : Record) (a : HashLocation) : queryLocation (ξ.query a) = some a := by
  unfold queryLocation
  have hex : ∃ p : Record × HashLocation, p.1.query p.2 = ξ.query a := ⟨(ξ, a), rfl⟩
  rw [dif_pos hex]
  exact congrArg some (location_eq_of_query_eq _ _ _ _ (Classical.choose_spec hex))

theorem queryLocation_some_width {q : Query} {a : HashLocation}
    (h : queryLocation q = some a) : q.1 = 896 := by
  unfold queryLocation at h
  split at h
  · rename_i hex
    have he := congrArg Sigma.fst (Classical.choose_spec hex)
    exact he.symm
  · simp at h

attribute [local irreducible] Record.query queryLocation

noncomputable def Record.cache (ξ : Record) : Cache :=
  letI : DecidableEq Query := Classical.decEq Query
  fun q => match queryLocation q with
    | none => none
    | some a => if ξ.query a = q then some (ξ.2 a) else none

theorem Record.cache_query (ξ : Record) (a : HashLocation) :
    ξ.cache (ξ.query a) = some (ξ.2 a) := by
  unfold Record.cache
  rw [queryLocation_query]
  exact if_pos rfl

theorem Record.cache_some_iff (ξ : Record) (q : Query) (u : BitVec hashBits) :
    ξ.cache q = some u ↔ ∃ a, ξ.query a = q ∧ ξ.2 a = u := by
  constructor
  · intro h
    cases hl : queryLocation q with
    | none => simp only [Record.cache, hl, reduceCtorEq] at h
    | some a =>
      by_cases ha : ξ.query a = q
      · exact ⟨a, ha, Option.some.inj (by simpa only [Record.cache, hl, if_pos ha] using h)⟩
      · simp only [Record.cache, hl, if_neg ha, reduceCtorEq] at h
  · rintro ⟨a, rfl, rfl⟩
    exact ξ.cache_query a

def Record.publicKey (ξ : Record) : PublicKey := (ξ.2 (.inr 42)).extractLsb' 0 128

end OptimalOTS.LeanIsaBaseline
