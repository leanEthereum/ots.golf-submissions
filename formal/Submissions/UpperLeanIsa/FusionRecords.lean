import Submissions.UpperLeanIsa.FusionInputs

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OptimalOTS
open scoped Classical
noncomputable section

abbrev ChainLoc (P : Params) := (k : Fin 42) × Fin (P.codec.len k - 1)
abbrev Loc (P : Params) := ChainLoc P ⊕ Fin 3
abbrev Record (P : Params) := (Fin 42 → Word) × (Loc P → BitVec hashBits)
variable {P : Params}

/-- Raw query data used by the location decoder; no consistency with a record is required. -/
structure RawInput (P : Params) where
  loc : Loc P
  tops : Tops
  word : Word
  state : BitVec 256

def RawInput.input (a : RawInput P) : BitVec 896 :=
  match a.loc with
  | .inl ⟨k,j⟩ => P.chainInput a.tops k j.val a.word
  | .inr r => P.rootInput a.tops r a.state

def RawInput.query (a : RawInput P) : Query := ⟨896, a.input⟩

theorem raw_location_eq (hP : P.Hyp) (a b : RawInput P) (h : a.query = b.query) : a.loc = b.loc := by
  have h' := query_inj h
  rcases a with ⟨a,t,x,st⟩
  rcases b with ⟨b,t',x',st'⟩
  cases a with
  | inl a =>
    rcases a with ⟨k,j⟩
    cases b with
    | inl b =>
      rcases b with ⟨k',j'⟩
      obtain ⟨hk,hj,-⟩ := Params.chainInput_location hP
        (by have := j.isLt; omega) (by have := j'.isLt; omega) t t' x x' h'
      subst k'
      have hj' : j = j' := Fin.ext hj
      subst j'
      rfl
    | inr r => exact (Params.chainInput_ne_rootInput hP t t' k j x r st' h').elim
  | inr r =>
    cases b with
    | inl b => exact (Params.chainInput_ne_rootInput hP t' t b.1 b.2 x' r st h'.symm).elim
    | inr s => exact congrArg Sum.inr (Params.rootInput_location hP t t' r s st st' h')

def queryLocation (P : Params) (q : Query) : Option (Loc P) :=
  if h : ∃ a : RawInput P, a.query = q then some (Classical.choose h).loc else none

theorem queryLocation_raw (hP : P.Hyp) (a : RawInput P) : queryLocation P a.query = some a.loc := by
  unfold queryLocation
  have hex : ∃ b : RawInput P, b.query = a.query := ⟨a,rfl⟩
  rw [dif_pos hex]
  exact congrArg some (raw_location_eq hP _ a (Classical.choose_spec hex))

theorem queryLocation_some {q : Query} {a : Loc P} (h : queryLocation P q = some a) :
    ∃ b : RawInput P, b.loc = a ∧ b.query = q := by
  unfold queryLocation at h
  split at h
  · rename_i hex
    exact ⟨Classical.choose hex, Option.some.inj h, Classical.choose_spec hex⟩
  · contradiction

theorem queryLocation_some_width {q : Query} {a : Loc P} (h : queryLocation P q = some a) : q.1 = 896 := by
  obtain ⟨b,-,rfl⟩ := queryLocation_some h
  rfl

theorem queryLocation_chainInput (hP : P.Hyp) (t : Tops) (k : Fin 42)
    (j : Fin (P.codec.len k - 1)) (x : Word) :
    queryLocation P ⟨896, P.chainInput t k j x⟩ = some (.inl ⟨k,j⟩) :=
  queryLocation_raw hP ⟨.inl ⟨k,j⟩,t,x,0⟩

theorem queryLocation_rootInput (hP : P.Hyp) (t : Tops) (r : Fin 3) (st : BitVec 256) :
    queryLocation P ⟨896, P.rootInput t r st⟩ = some (.inr r) :=
  queryLocation_raw hP ⟨.inr r,t,0,st⟩

theorem queryLocation_eq_none {q : Query} (h : ∀ a : RawInput P, a.query ≠ q) :
    queryLocation P q = none := by
  unfold queryLocation
  rw [dif_neg]
  rintro ⟨a,ha⟩
  exact h a ha

theorem RawInput.query_ne_idx (hP : P.Hyp) (a : RawInput P) (m : Message) (η : Nonce)
    (pk : PublicKey) : a.query ≠ ⟨896,P.codec.idxInput m η pk⟩ := by
  intro h
  have h' := query_inj h
  rcases a with ⟨a,t,x,st⟩
  cases a with
  | inl a => exact Params.chainInput_ne_idxInput hP t a.1 a.2 x m η pk h'
  | inr r => exact Params.rootInput_ne_idxInput hP t r st m η pk h'

def Record.word (ξ : Record P) (k : Fin 42) : ℕ → Word
  | 0 => ξ.1 k
  | j + 1 => if h : j < P.codec.len k - 1 then P.codec.slice k j (ξ.2 (.inl ⟨k,⟨j,h⟩⟩)) else 0

theorem Record.word_zero (ξ : Record P) (k : Fin 42) : ξ.word k 0 = ξ.1 k := rfl

theorem Record.word_succ (ξ : Record P) (k : Fin 42) (j : ℕ) (h : j < P.codec.len k - 1) :
    ξ.word k (j+1) = P.codec.slice k j (ξ.2 (.inl ⟨k,⟨j,h⟩⟩)) := dif_pos h

def Record.top (ξ : Record P) (k : Fin 42) : Word := ξ.word k (P.codec.len k - 1)
def Record.tops (ξ : Record P) : Tops := Layer.Params.topAt ξ.top

def Record.rootState (ξ : Record P) : ℕ → BitVec 256
  | 0 => 0
  | r+1 => if h : r < 3 then ξ.2 (.inr ⟨r,h⟩) else 0

theorem Record.rootState_zero (ξ : Record P) : ξ.rootState 0 = 0 := rfl

theorem Record.rootState_succ (ξ : Record P) (r : Fin 3) : ξ.rootState (r.val+1) = ξ.2 (.inr r) :=
  dif_pos r.isLt

theorem Record.rootState_succ_lt (ξ : Record P) (r : ℕ) (hr : r < 3) :
    ξ.rootState (r+1) = ξ.2 (.inr ⟨r,hr⟩) := dif_pos hr

theorem Record.rootState_succ_ge (ξ : Record P) (r : ℕ) (hr : ¬ r < 3) :
    ξ.rootState (r+1) = 0 := dif_neg hr

def Record.rawInput (ξ : Record P) (a : Loc P) : RawInput P :=
  match a with
  | .inl ⟨k,j⟩ => ⟨a,ξ.tops,ξ.word k j,0⟩
  | .inr r => ⟨a,ξ.tops,0,ξ.rootState r⟩

theorem Record.rawInput_loc (ξ : Record P) (a : Loc P) : (ξ.rawInput a).loc = a := by
  cases a <;> rfl

def Record.input (ξ : Record P) (a : Loc P) : BitVec 896 := (ξ.rawInput a).input
def Record.query (ξ : Record P) (a : Loc P) : Query := ⟨896,ξ.input a⟩

theorem Record.query_inl (ξ : Record P) (k : Fin 42) (j : Fin (P.codec.len k - 1)) :
    ξ.query (.inl ⟨k,j⟩) = ⟨896,P.chainInput ξ.tops k j (ξ.word k j)⟩ := rfl

theorem Record.query_inr (ξ : Record P) (r : Fin 3) :
    ξ.query (.inr r) = ⟨896,P.rootInput ξ.tops r (ξ.rootState r)⟩ := rfl

def Record.pk (ξ : Record P) : PublicKey := (ξ.2 (.inr 2)).extractLsb' 0 128

def Record.table (ξ : Record P) (k : Fin 42) : List Word := (List.range (P.codec.len k)).map (ξ.word k)
def Record.sk (ξ : Record P) : SecretKey := ⟨ξ.table,ξ.pk⟩

theorem queryLocation_query (hP : P.Hyp) (ξ : Record P) (a : Loc P) :
    queryLocation P (ξ.query a) = some a := by
  change queryLocation P (ξ.rawInput a).query = some a
  rw [queryLocation_raw hP, Record.rawInput_loc]

theorem location_eq_of_query_eq (hP : P.Hyp) (ξ ζ : Record P) (a b : Loc P)
    (h : ξ.query a = ζ.query b) : a = b := by
  have he := congrArg (queryLocation P) h
  rw [queryLocation_query hP, queryLocation_query hP] at he
  exact Option.some.inj he

attribute [local irreducible] Record.query queryLocation
/-- The programmed cache of a record: every keygen query with its recorded answer. -/
def Record.cache (ξ : Record P) : Cache := fun q =>
  match queryLocation P q with
  | none => none
  | some a => if ξ.query a = q then some (ξ.2 a) else none

theorem Record.cache_query (hP : P.Hyp) (ξ : Record P) (a : Loc P) :
    ξ.cache (ξ.query a) = some (ξ.2 a) := by
  unfold Record.cache
  rw [queryLocation_query hP]
  exact if_pos rfl

theorem Record.cache_some_iff (hP : P.Hyp) (ξ : Record P) (q : Query) (u : BitVec hashBits) :
    ξ.cache q = some u ↔ ∃ a, ξ.query a = q ∧ ξ.2 a = u := by
  constructor
  · intro h
    cases hl : queryLocation P q with
    | none => simp only [Record.cache, hl, reduceCtorEq] at h
    | some a =>
      by_cases ha : ξ.query a = q
      · exact ⟨a, ha, Option.some.inj (by simpa only [Record.cache, hl, if_pos ha] using h)⟩
      · simp only [Record.cache, hl, if_neg ha, reduceCtorEq] at h
  · rintro ⟨a, rfl, rfl⟩
    exact ξ.cache_query hP a

theorem Record.cache_isSome_iff (hP : P.Hyp) (ξ : Record P) (q : Query) :
    (ξ.cache q).isSome ↔ ∃ a, ξ.query a = q := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨a, ha, -⟩ := (ξ.cache_some_iff hP q u).mp hu
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨ξ.2 a, (ξ.cache_some_iff hP q _).mpr ⟨a, ha, rfl⟩⟩

/-- All programmed points are separated from every signing-index query. -/
theorem Record.query_ne_idx (hP : P.Hyp) (ξ : Record P) (a : Loc P) (m : Message) (η : Nonce)
    (pk : PublicKey) : ξ.query a ≠ ⟨896, P.codec.idxInput m η pk⟩ := by
  intro h
  unfold Record.query at h
  have h' := query_inj h
  cases a with
  | inl a => exact Params.chainInput_ne_idxInput hP ξ.tops a.1 a.2 _ m η pk h'
  | inr r => exact Params.rootInput_ne_idxInput hP ξ.tops r _ m η pk h'

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
