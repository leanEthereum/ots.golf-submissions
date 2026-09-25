import Submissions.UpperLeanIsa.LayerWire
import Submissions.UpperLeanIsa.Cache

/-!
# Records of a layer scheme and their oracle points

A *record* is the randomness of key generation laid out by location: the 42 seeds and the full
256-bit answer at every keygen query. Chain step `(k, j)` (`j + 1 < len k`) and root call `r < 8`
are the locations. The chain steps and root calls `r < 7` carry constant metadata (`Params.Hyp`);
the last root call carries the low half of the state before it. A record is *separated*
(`Record.Sep`) when that word is none of the nine constant tags. A location of a record is
*valid* (`Record.ValidAt`) unless it is the last call of a record that is not separated; valid
locations have distinct inputs in every pair of records (`location_eq_of_input_eq`).

`Params.Hyp` collects the facts about the parameters used by the security proof.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Params

variable (P : Params)

/-- The standing hypotheses of the security proof. -/
structure Hyp : Prop where
  len_pos : ∀ k, 1 ≤ P.len k
  digit_lt : ∀ I k, P.digit I k < P.len k
  digit_inj : ∀ I I' : Index, (∀ k, P.digit I k = P.digit I' k) → I = I'
  layer_pos : 1 ≤ P.layer
  tag_inj : ∀ (k k' : Fin numChains) (j j' : ℕ), j + 1 < P.len k → j' + 1 < P.len k' →
    P.tag k j 0 = P.tag k' j' 0 → P.tag k j 1 = P.tag k' j' 1 → P.tag k j 2 = P.tag k' j' 2 →
    k = k' ∧ j = j'
  chain_idx : P.chainMd ≠ P.idxMd
  chain_root : ∀ r < 7, P.chainMd ≠ P.rootMd r
  root_idx : ∀ r < 7, P.rootMd r ≠ P.idxMd
  root_inj : ∀ r s, r < 7 → s < 7 → P.rootMd r = P.rootMd s → r = s
  numValid_ge : 188 * 2 ^ 107 ≤ P.numValid
  numValid_le : 2 * P.numValid ≤ 2 ^ 127
  keygen_le : 2 * (∑ k, (P.len k - 1)) + 16 ≤ 2 ^ 20
  verify_le : 18 + 2 * P.layer ≤ 2 ^ 20
  len_zero : 2 ≤ P.len 0

/-- The nine constant metadata words: chain steps, the index query, and root calls `r < 7`. -/
def IsTag (w : Word) : Prop := w = P.chainMd ∨ w = P.idxMd ∨ ∃ r < 7, w = P.rootMd r

end Params

/-! ## Injectivity of the query layouts -/

theorem append_inj {a b : ℕ} {x x' : BitVec a} {y y' : BitVec b}
    (h : x ++ y = x' ++ y') : x = x' ∧ y = y' := by
  constructor
  · simpa only [BitVec.extractLsb'_append_eq_left] using
      congrArg (fun z : BitVec (a + b) => z.extractLsb' b a) h
  · simpa only [BitVec.extractLsb'_append_eq_right] using
      congrArg (fun z : BitVec (a + b) => z.extractLsb' 0 b) h

theorem query_inj {a b : BitVec 896} (h : (⟨896, a⟩ : Query) = ⟨896, b⟩) : a = b :=
  eq_of_heq (Sigma.mk.inj_iff.mp h).2

namespace Params

variable {P : Params}

theorem chainInput_eq_iff (hP : P.Hyp) {k k' : Fin numChains} {j j' : ℕ}
    (hj : j + 1 < P.len k) (hj' : j' + 1 < P.len k') (x y : Word) :
    P.chainInput k j x = P.chainInput k' j' y ↔ k = k' ∧ j = j' ∧ x = y := by
  constructor
  · intro h
    have hb := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.1
    obtain ⟨h1, hx⟩ := append_inj hb
    obtain ⟨h2, h0⟩ := append_inj h1
    obtain ⟨h3, h1'⟩ := append_inj h2
    obtain ⟨hk, hjj⟩ := hP.tag_inj k k' j j' hj hj' h0 h1' h3
    exact ⟨hk, hjj, hx⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem chainInput_same_iff (k : Fin numChains) (j : ℕ) (x y : Word) :
    P.chainInput k j x = P.chainInput k j y ↔ x = y := by
  constructor
  · intro h
    have hb := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.1
    exact (append_inj hb).2
  · rintro rfl
    rfl

theorem rootInput_eq_iff (hP : P.Hyp) {r s : ℕ} (hr : r < 7) (hs : s < 7)
    (t t' : Fin numChains → Word) (st st' : BitVec 256) :
    P.rootInput t r st = P.rootInput t' s st' ↔
      r = s ∧ Params.rootCv t r st = Params.rootCv t' s st' ∧
        Params.rootBlock t r st = Params.rootBlock t' s st' := by
  unfold rootInput
  rw [hashInput_eq_iff, rootTag_lt hr, rootTag_lt hs]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hP.root_inj r s hr hs h3, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨h1, h2, rfl⟩

/-- Equal inputs at the last root call: equal cv, block and metadata. -/
theorem rootInput_seven_iff (t t' : Fin numChains → Word) (st st' : BitVec 256) :
    P.rootInput t 7 st = P.rootInput t' 7 st' ↔
      Params.rootCv t 7 st = Params.rootCv t' 7 st' ∧
        Params.rootBlock t 7 st = Params.rootBlock t' 7 st' ∧
          st.extractLsb' 0 128 = st'.extractLsb' 0 128 := by
  unfold rootInput
  rw [hashInput_eq_iff, rootTag_seven, rootTag_seven]

theorem chainInput_ne_rootInput (hP : P.Hyp) {r : ℕ} (hr : r < 7) (k : Fin numChains) (j : ℕ)
    (x : Word) (t : Fin numChains → Word) (st : BitVec 256) :
    P.chainInput k j x ≠ P.rootInput t r st := by
  intro h
  have h' := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
  rw [rootTag_lt hr] at h'
  exact hP.chain_root r hr h'

theorem chainInput_ne_rootInput_seven (k : Fin numChains) (j : ℕ) (x : Word)
    (t : Fin numChains → Word) (st : BitVec 256) (hst : ¬ P.IsTag (st.extractLsb' 0 128)) :
    P.chainInput k j x ≠ P.rootInput t 7 st := by
  intro h
  have h' := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
  rw [rootTag_seven] at h'
  exact hst (Or.inl h'.symm)

theorem rootInput_ne_rootInput_seven {r : ℕ} (hr : r < 7) (t t' : Fin numChains → Word)
    (st st' : BitVec 256) (hst : ¬ P.IsTag (st'.extractLsb' 0 128)) :
    P.rootInput t r st ≠ P.rootInput t' 7 st' := by
  intro h
  have h' := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
  rw [rootTag_lt hr, rootTag_seven] at h'
  exact hst (Or.inr (Or.inr ⟨r, hr, h'.symm⟩))

theorem chainInput_ne_idxInput (hP : P.Hyp) (k : Fin numChains) (j : ℕ) (x : Word)
    (m : Message) (η : Nonce) (pk : PublicKey) : P.chainInput k j x ≠ P.idxInput m η pk := by
  intro h
  exact hP.chain_idx ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem rootInput_ne_idxInput (hP : P.Hyp) {r : ℕ} (hr : r < 7) (t : Fin numChains → Word)
    (st : BitVec 256) (m : Message) (η : Nonce) (pk : PublicKey) :
    P.rootInput t r st ≠ P.idxInput m η pk := by
  intro h
  have h' := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
  rw [rootTag_lt hr] at h'
  exact hP.root_idx r hr h'

theorem rootInput_seven_ne_idxInput (t : Fin numChains → Word) (st : BitVec 256)
    (hst : st.extractLsb' 0 128 ≠ P.idxMd) (m : Message) (η : Nonce) (pk : PublicKey) :
    P.rootInput t 7 st ≠ P.idxInput m η pk := by
  intro h
  have h' := ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2
  rw [rootTag_seven] at h'
  exact hst h'

end Params

/-! ## Locations and records -/

/-- Chain step `(k, j)`: the query at position `j < len k - 1` of chain `k`. -/
abbrev ChainLoc (P : Params) := (k : Fin numChains) × Fin (P.len k - 1)

/-- The keygen locations: chain steps and the 8 root calls. -/
abbrev Loc (P : Params) := ChainLoc P ⊕ Fin 8

/-- The seeds and the full answer at every keygen location. -/
abbrev Record (P : Params) := (Fin numChains → Word) × (Loc P → BitVec hashBits)

variable {P : Params}

/-- The word of chain `k` at position `j` (zero past the end). -/
def Record.word (ξ : Record P) (k : Fin numChains) : ℕ → Word
  | 0 => ξ.1 k
  | j + 1 => if h : j < P.len k - 1 then P.slice k j (ξ.2 (.inl ⟨k, ⟨j, h⟩⟩)) else 0

theorem Record.word_zero (ξ : Record P) (k : Fin numChains) : ξ.word k 0 = ξ.1 k := rfl

theorem Record.word_succ (ξ : Record P) (k : Fin numChains) (j : ℕ) (h : j < P.len k - 1) :
    ξ.word k (j + 1) = P.slice k j (ξ.2 (.inl ⟨k, ⟨j, h⟩⟩)) := by
  simp only [Record.word, dif_pos h]

/-- The tops: the last word of every chain. -/
def Record.top (ξ : Record P) (k : Fin numChains) : Word := ξ.word k (P.len k - 1)

/-- The root state before call `r`. -/
def Record.rootState (ξ : Record P) : ℕ → BitVec 256
  | 0 => Params.rootInit ξ.top
  | r + 1 => if h : r < 8 then ξ.2 (.inr ⟨r, h⟩) else 0

theorem Record.rootState_succ (ξ : Record P) (r : Fin 8) :
    ξ.rootState (r.val + 1) = ξ.2 (.inr r) := by
  unfold Record.rootState
  exact dif_pos r.isLt

theorem Record.rootState_zero (ξ : Record P) : ξ.rootState 0 = Params.rootInit ξ.top := rfl

theorem Record.rootState_succ_lt (ξ : Record P) (r : ℕ) (hr : r < 8) :
    ξ.rootState (r + 1) = ξ.2 (.inr ⟨r, hr⟩) := by
  unfold Record.rootState
  exact dif_pos hr

theorem Record.rootState_succ_ge (ξ : Record P) (r : ℕ) (hr : ¬ r < 8) :
    ξ.rootState (r + 1) = 0 := by
  unfold Record.rootState
  exact dif_neg hr

/-- The input of the keygen query at a location. -/
def Record.input (ξ : Record P) : Loc P → BitVec 896
  | .inl ⟨k, j⟩ => P.chainInput k j.val (ξ.word k j.val)
  | .inr r => P.rootInput ξ.top r.val (ξ.rootState r.val)

/-- The keygen query at a location. -/
def Record.query (ξ : Record P) (a : Loc P) : Query := ⟨896, ξ.input a⟩

theorem Record.query_inl (ξ : Record P) (k : Fin numChains) (j : Fin (P.len k - 1)) :
    ξ.query (.inl ⟨k, j⟩) = ⟨896, P.chainInput k j.val (ξ.word k j.val)⟩ := rfl

theorem Record.query_inr (ξ : Record P) (r : Fin 8) :
    ξ.query (.inr r) = ⟨896, P.rootInput ξ.top r.val (ξ.rootState r.val)⟩ := rfl

/-- The public key: the low half of the last root answer. -/
def Record.pk (ξ : Record P) : PublicKey := (ξ.2 (.inr 7)).extractLsb' 0 128

/-- The chain table of chain `k`: its words at positions `0, …, len k - 1`. -/
def Record.table (ξ : Record P) (k : Fin numChains) : List Word :=
  (List.range (P.len k)).map (ξ.word k)

/-- The secret key of the record. -/
def Record.sk (ξ : Record P) : SecretKey := ⟨ξ.table, ξ.pk⟩

/-- The metadata word of the last root call: the low half of the state after call 6. -/
def Record.lastTag (ξ : Record P) : Word := (ξ.2 (.inr 6)).extractLsb' 0 128

/-- A separated record: the metadata of its last root call is not a constant tag. -/
def Record.Sep (ξ : Record P) : Prop := ¬ P.IsTag ξ.lastTag

/-- A valid location: any location but the last call of a record that is not separated. -/
def Record.ValidAt (ξ : Record P) (a : Loc P) : Prop := a = .inr 7 → ξ.Sep

theorem Record.validAt_inl (ξ : Record P) (a : ChainLoc P) : ξ.ValidAt (.inl a) :=
  fun h => absurd h Sum.inl_ne_inr

theorem Record.validAt_inr_lt (ξ : Record P) {r : Fin 8} (hr : r.val < 7) : ξ.ValidAt (.inr r) :=
  fun h => by
    have h7 : r.val = 7 := congrArg Fin.val (Sum.inr.inj h)
    omega

theorem Record.validAt_of_sep {ξ : Record P} (h : ξ.Sep) (a : Loc P) : ξ.ValidAt a := fun _ => h

theorem Record.validAt_of_ne {ξ : Record P} {a : Loc P} (h : a ≠ .inr 7) : ξ.ValidAt a :=
  fun h' => absurd h' h

theorem Record.rootState_seven (ξ : Record P) : (ξ.rootState 7).extractLsb' 0 128 = ξ.lastTag := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, Record.rootState_succ_lt _ 6 (by norm_num)]
  rfl

theorem Record.rootState_seven' (ξ : Record P) :
    (ξ.rootState ((7 : Fin 8) : ℕ)).extractLsb' 0 128 = ξ.lastTag := ξ.rootState_seven

theorem ChainLoc.ext' {a b : ChainLoc P} (hk : a.1 = b.1) (hj : a.2.val = b.2.val) : a = b := by
  rcases a with ⟨k, j⟩
  rcases b with ⟨k', j'⟩
  dsimp only at hk hj
  subst hk
  exact congrArg (Sigma.mk k) (Fin.ext hj)

theorem fin8_cases (r : Fin 8) : r.val < 7 ∨ r = 7 := by
  rcases Nat.lt_or_ge r.val 7 with h | h
  · exact Or.inl h
  · exact Or.inr (Fin.ext (show r.val = 7 by have := r.isLt; omega))

theorem Record.input_seven (ξ : Record P) :
    ξ.input (.inr 7) = P.rootInput ξ.top 7 (ξ.rootState 7) := rfl

/-- Valid locations of any two records at the same oracle input are the same location. -/
theorem location_eq_of_input_eq (hP : P.Hyp) (ξ ζ : Record P) (a b : Loc P)
    (ha : ξ.ValidAt a) (hb : ζ.ValidAt b) (h : ξ.input a = ζ.input b) : a = b := by
  cases a with
  | inl a =>
    rcases a with ⟨k, j⟩
    cases b with
    | inl b =>
      rcases b with ⟨k', j'⟩
      have hs := (Params.chainInput_eq_iff hP (by have := j.isLt; omega)
        (by have := j'.isLt; omega) _ _).mp h
      exact congrArg Sum.inl (ChainLoc.ext' hs.1 hs.2.1)
    | inr r =>
      rcases fin8_cases r with hr | rfl
      · exact (Params.chainInput_ne_rootInput hP hr _ _ _ _ _ h).elim
      · refine (Params.chainInput_ne_rootInput_seven _ _ _ _ _ ?_ h).elim
        rw [Record.rootState_seven']; exact hb rfl
  | inr r =>
    cases b with
    | inl b =>
      rcases b with ⟨k', j'⟩
      rcases fin8_cases r with hr | rfl
      · exact (Params.chainInput_ne_rootInput hP hr _ _ _ _ _ h.symm).elim
      · refine (Params.chainInput_ne_rootInput_seven _ _ _ _ _ ?_ h.symm).elim
        rw [Record.rootState_seven']; exact ha rfl
    | inr s =>
      rcases fin8_cases r with hr | rfl
      · rcases fin8_cases s with hs | rfl
        · have hs' := (Params.rootInput_eq_iff hP hr hs _ _ _ _).mp h
          exact congrArg Sum.inr (Fin.ext hs'.1)
        · refine (Params.rootInput_ne_rootInput_seven hr _ _ _ _ ?_ h).elim
          rw [Record.rootState_seven']; exact hb rfl
      · rcases fin8_cases s with hs | rfl
        · refine (Params.rootInput_ne_rootInput_seven hs _ _ _ _ ?_ h.symm).elim
          rw [Record.rootState_seven']; exact ha rfl
        · rfl

theorem location_eq_of_query_eq (hP : P.Hyp) (ξ ζ : Record P) (a b : Loc P)
    (ha : ξ.ValidAt a) (hb : ζ.ValidAt b) (h : ξ.query a = ζ.query b) : a = b :=
  location_eq_of_input_eq hP ξ ζ a b ha hb (query_inj h)

/-- Records with the same query at the last call are separated together. -/
theorem Record.sep_of_query_seven {ξ ζ : Record P} (h : ξ.query (.inr 7) = ζ.query (.inr 7))
    (hζ : ζ.Sep) : ξ.Sep := by
  have h' := (Params.rootInput_seven_iff _ _ _ _).mp (query_inj h)
  unfold Record.Sep
  rw [← Record.rootState_seven', h'.2.2, Record.rootState_seven']
  exact hζ

theorem Record.validAt_of_query_eq {ξ ζ : Record P} {a : Loc P} (h : ξ.query a = ζ.query a)
    (hζ : ζ.ValidAt a) : ξ.ValidAt a := by
  rintro rfl
  exact Record.sep_of_query_seven h (hζ rfl)

/-- The location decoder: it depends only on the query, never on a particular record. -/
def queryLocation (P : Params) (q : Query) : Option (Loc P) :=
  @dite (Option (Loc P)) (∃ p : Record P × Loc P, p.1.query p.2 = q ∧ p.1.ValidAt p.2)
    (Classical.propDecidable _)
    (fun h => some (Classical.choose h).2) (fun _ => none)

theorem queryLocation_query (hP : P.Hyp) (ξ : Record P) (a : Loc P) (ha : ξ.ValidAt a) :
    queryLocation P (ξ.query a) = some a := by
  unfold queryLocation
  have hex : ∃ p : Record P × Loc P, p.1.query p.2 = ξ.query a ∧ p.1.ValidAt p.2 :=
    ⟨(ξ, a), rfl, ha⟩
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  exact congrArg some (location_eq_of_query_eq hP _ _ _ _ hs.2 ha hs.1)

theorem queryLocation_some {q : Query} {a : Loc P} (h : queryLocation P q = some a) :
    ∃ ζ : Record P, ζ.query a = q ∧ ζ.ValidAt a := by
  unfold queryLocation at h
  split at h
  · rename_i hex
    refine ⟨(Classical.choose hex).1, ?_⟩
    have ha := Option.some.inj h
    rw [← ha]
    exact Classical.choose_spec hex
  · simp at h

theorem queryLocation_some_width {q : Query} {a : Loc P}
    (h : queryLocation P q = some a) : q.1 = 896 := by
  obtain ⟨ζ, rfl, -⟩ := queryLocation_some h
  rfl

theorem queryLocation_eq_none {q : Query}
    (h : ∀ (ζ : Record P) (a : Loc P), ζ.ValidAt a → ζ.query a ≠ q) :
    queryLocation P q = none := by
  unfold queryLocation
  rw [dif_neg]
  rintro ⟨p, hp, hv⟩
  exact h p.1 p.2 hv hp

/-- A record realising the decoded location of a query is valid there. -/
theorem Record.validAt_of_queryLocation {ξ : Record P} {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (hq : ξ.query a = q) : ξ.ValidAt a := by
  obtain ⟨ζ, hζ, hv⟩ := queryLocation_some hl
  exact Record.validAt_of_query_eq (hq.trans hζ.symm) hv

attribute [local irreducible] Record.query queryLocation

/-- The programmed cache of a record: every keygen query with its recorded answer. -/
def Record.cache (ξ : Record P) : Cache := fun q =>
  match queryLocation P q with
  | none => none
  | some a => if ξ.query a = q then some (ξ.2 a) else none

theorem Record.cache_query (hP : P.Hyp) (ξ : Record P) (a : Loc P) (ha : ξ.ValidAt a) :
    ξ.cache (ξ.query a) = some (ξ.2 a) := by
  unfold Record.cache
  rw [queryLocation_query hP ξ a ha]
  exact if_pos rfl

theorem Record.cache_some_iff (hP : P.Hyp) (ξ : Record P) (q : Query) (u : BitVec hashBits) :
    ξ.cache q = some u ↔ ∃ a, ξ.ValidAt a ∧ ξ.query a = q ∧ ξ.2 a = u := by
  constructor
  · intro h
    cases hl : queryLocation P q with
    | none => simp only [Record.cache, hl, reduceCtorEq] at h
    | some a =>
      by_cases ha : ξ.query a = q
      · exact ⟨a, Record.validAt_of_queryLocation hl ha, ha,
          Option.some.inj (by simpa only [Record.cache, hl, if_pos ha] using h)⟩
      · simp only [Record.cache, hl, if_neg ha, reduceCtorEq] at h
  · rintro ⟨a, hv, rfl, rfl⟩
    exact ξ.cache_query hP a hv

theorem Record.cache_isSome_iff (hP : P.Hyp) (ξ : Record P) (q : Query) :
    (ξ.cache q).isSome ↔ ∃ a, ξ.ValidAt a ∧ ξ.query a = q := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨a, hv, ha, -⟩ := (ξ.cache_some_iff hP q u).mp hu
    exact ⟨a, hv, ha⟩
  · rintro ⟨a, hv, ha⟩
    exact ⟨ξ.2 a, (ξ.cache_some_iff hP q _).mpr ⟨a, hv, ha, rfl⟩⟩

/-- A valid record location is not an index query. -/
theorem Record.query_ne_idx (hP : P.Hyp) (ξ : Record P) (a : Loc P) (ha : ξ.ValidAt a)
    (m : Message) (η : Nonce) (pk : PublicKey) : ξ.query a ≠ ⟨896, P.idxInput m η pk⟩ := by
  intro h
  unfold Record.query at h
  have h' := query_inj h
  cases a with
  | inl a => exact Params.chainInput_ne_idxInput hP _ _ _ _ _ _ h'
  | inr r =>
    rcases fin8_cases r with hr | rfl
    · exact Params.rootInput_ne_idxInput hP hr _ _ _ _ _ h'
    · refine Params.rootInput_seven_ne_idxInput _ _ ?_ _ _ _ h'
      rw [Record.rootState_seven']
      exact fun he => ha rfl (Or.inr (Or.inl he))

variable (P) in
/-- An index query (of any message, nonce and public key). -/
def IsIdxQuery (q : Query) : Prop := ∃ m η pk, q = ⟨896, P.idxInput m η pk⟩

/-- A decoded query is not an index query. -/
theorem not_idx_of_queryLocation (hP : P.Hyp) {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (m : Message) (η : Nonce) (pk : PublicKey) :
    q ≠ ⟨896, P.idxInput m η pk⟩ := by
  obtain ⟨ζ, rfl, hv⟩ := queryLocation_some hl
  exact ζ.query_ne_idx hP a hv m η pk

end OptimalOTS.LeanIsaBaseline.Layer
