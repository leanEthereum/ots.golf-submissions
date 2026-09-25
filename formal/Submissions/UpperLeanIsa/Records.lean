import Submissions.UpperLeanIsa.LayerWire
import Submissions.UpperLeanIsa.Cache
import Submissions.UpperLeanIsa.TierCodec

/-!
# Records of a layer scheme and their oracle points

A *record* is the randomness of key generation laid out by location: the 42 seeds and the full
256-bit answer at every keygen query. Chain step `(k, j)` (`j + 1 < len k`) and root call `r < 9`
are the locations. Distinct locations have distinct inputs in every pair of records
(`location_eq_of_input_eq`), because the three tag cells and the metadata separate them
syntactically (`Params.Hyp`); no probabilistic collision exception is needed.

`Params.Hyp` collects the facts about the parameters used by the security proof, including a
tier schedule of the codec (`tier`) whose numeric conditions hold.
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
  layer_pos : 1 ≤ P.layer
  tag_inj : ∀ (k k' : Fin numChains) (j j' : ℕ), j + 1 < P.len k → j' + 1 < P.len k' →
    P.tag k j 0 = P.tag k' j' 0 → P.tag k j 1 = P.tag k' j' 1 → P.tag k j 2 = P.tag k' j' 2 →
    k = k' ∧ j = j'
  chain_idx : P.chainMd ≠ P.idxMd
  chain_root : ∀ r < 9, P.chainMd ≠ P.rootMd r
  root_idx : ∀ r < 9, P.rootMd r ≠ P.idxMd
  root_inj : ∀ r s, r < 9 → s < 9 → P.rootMd r = P.rootMd s → r = s
  tier : ∃ S : Tier.Sched, S.Valid ∧ P.TierHyp S
  keygen_le : 2 * (∑ k, (P.len k - 1)) + 18 ≤ 2 ^ 20
  verify_le : 20 + 2 * P.layer ≤ 2 ^ 20
  len_zero : 2 ≤ P.len 0

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

theorem rootInput_eq_iff (hP : P.Hyp) {r s : ℕ} (hr : r < 9) (hs : s < 9)
    (t t' : Fin numChains → Word) (st st' : BitVec 256) :
    P.rootInput t r st = P.rootInput t' s st' ↔
      r = s ∧ Params.rootCv t r st = Params.rootCv t' s st' ∧
        Params.rootBlock t r st = Params.rootBlock t' s st' := by
  unfold rootInput
  rw [hashInput_eq_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hP.root_inj r s hr hs h3, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨h1, h2, rfl⟩

theorem chainInput_ne_rootInput (hP : P.Hyp) {r : ℕ} (hr : r < 9) (k : Fin numChains) (j : ℕ)
    (x : Word) (t : Fin numChains → Word) (st : BitVec 256) :
    P.chainInput k j x ≠ P.rootInput t r st := by
  intro h
  exact hP.chain_root r hr ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem chainInput_ne_idxInput (hP : P.Hyp) (k : Fin numChains) (j : ℕ) (x : Word)
    (m : Message) (η : Nonce) (pk : PublicKey) : P.chainInput k j x ≠ P.idxInput m η pk := by
  intro h
  exact hP.chain_idx ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

theorem rootInput_ne_idxInput (hP : P.Hyp) {r : ℕ} (hr : r < 9) (t : Fin numChains → Word)
    (st : BitVec 256) (m : Message) (η : Nonce) (pk : PublicKey) :
    P.rootInput t r st ≠ P.idxInput m η pk := by
  intro h
  exact hP.root_idx r hr ((hashInput_eq_iff _ _ _ _ _ _).mp h).2.2

end Params

/-! ## Locations and records -/

/-- Chain step `(k, j)`: the query at position `j < len k - 1` of chain `k`. -/
abbrev ChainLoc (P : Params) := (k : Fin numChains) × Fin (P.len k - 1)

/-- The keygen locations: chain steps and the 9 root calls. -/
abbrev Loc (P : Params) := ChainLoc P ⊕ Fin 9

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
  | r + 1 => if h : r < 9 then ξ.2 (.inr ⟨r, h⟩) else 0

theorem Record.rootState_succ (ξ : Record P) (r : Fin 9) :
    ξ.rootState (r.val + 1) = ξ.2 (.inr r) := by
  unfold Record.rootState
  exact dif_pos r.isLt

theorem Record.rootState_zero (ξ : Record P) : ξ.rootState 0 = Params.rootInit ξ.top := rfl

theorem Record.rootState_succ_lt (ξ : Record P) (r : ℕ) (hr : r < 9) :
    ξ.rootState (r + 1) = ξ.2 (.inr ⟨r, hr⟩) := by
  unfold Record.rootState
  exact dif_pos hr

theorem Record.rootState_succ_ge (ξ : Record P) (r : ℕ) (hr : ¬ r < 9) :
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

theorem Record.query_inr (ξ : Record P) (r : Fin 9) :
    ξ.query (.inr r) = ⟨896, P.rootInput ξ.top r.val (ξ.rootState r.val)⟩ := rfl

/-- The public key: the low half of the last root answer. -/
def Record.pk (ξ : Record P) : PublicKey := (ξ.2 (.inr 8)).extractLsb' 0 128

/-- The chain table of chain `k`: its words at positions `0, …, len k - 1`. -/
def Record.table (ξ : Record P) (k : Fin numChains) : List Word :=
  (List.range (P.len k)).map (ξ.word k)

/-- The secret key of the record. -/
def Record.sk (ξ : Record P) : SecretKey := ⟨ξ.table, ξ.pk⟩

theorem ChainLoc.ext' {a b : ChainLoc P} (hk : a.1 = b.1) (hj : a.2.val = b.2.val) : a = b := by
  rcases a with ⟨k, j⟩
  rcases b with ⟨k', j'⟩
  dsimp only at hk hj
  subst hk
  exact congrArg (Sigma.mk k) (Fin.ext hj)

/-- Even different records cannot place different locations at the same oracle input. -/
theorem location_eq_of_input_eq (hP : P.Hyp) (ξ ζ : Record P) (a b : Loc P)
    (h : ξ.input a = ζ.input b) : a = b := by
  cases a with
  | inl a =>
    rcases a with ⟨k, j⟩
    cases b with
    | inl b =>
      rcases b with ⟨k', j'⟩
      have hs := (Params.chainInput_eq_iff hP (by have := j.isLt; omega)
        (by have := j'.isLt; omega) _ _).mp h
      exact congrArg Sum.inl (ChainLoc.ext' hs.1 hs.2.1)
    | inr r => exact (Params.chainInput_ne_rootInput hP r.isLt _ _ _ _ _ h).elim
  | inr r =>
    cases b with
    | inl b =>
      rcases b with ⟨k', j'⟩
      exact (Params.chainInput_ne_rootInput hP r.isLt _ _ _ _ _ h.symm).elim
    | inr s =>
      have hs := (Params.rootInput_eq_iff hP r.isLt s.isLt _ _ _ _).mp h
      exact congrArg Sum.inr (Fin.ext hs.1)

theorem location_eq_of_query_eq (hP : P.Hyp) (ξ ζ : Record P) (a b : Loc P)
    (h : ξ.query a = ζ.query b) : a = b :=
  location_eq_of_input_eq hP ξ ζ a b (query_inj h)

/-- The location decoder: it depends only on the query, never on a particular record. -/
def queryLocation (P : Params) (q : Query) : Option (Loc P) :=
  @dite (Option (Loc P)) (∃ p : Record P × Loc P, p.1.query p.2 = q)
    (Classical.propDecidable _)
    (fun h => some (Classical.choose h).2) (fun _ => none)

theorem queryLocation_query (hP : P.Hyp) (ξ : Record P) (a : Loc P) :
    queryLocation P (ξ.query a) = some a := by
  unfold queryLocation
  have hex : ∃ p : Record P × Loc P, p.1.query p.2 = ξ.query a := ⟨(ξ, a), rfl⟩
  rw [dif_pos hex]
  exact congrArg some (location_eq_of_query_eq hP _ _ _ _ (Classical.choose_spec hex))

theorem queryLocation_some {q : Query} {a : Loc P} (h : queryLocation P q = some a) :
    ∃ ζ : Record P, ζ.query a = q := by
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
  obtain ⟨ζ, rfl⟩ := queryLocation_some h
  rfl

theorem queryLocation_eq_none {q : Query} (h : ∀ (ζ : Record P) (a : Loc P), ζ.query a ≠ q) :
    queryLocation P q = none := by
  unfold queryLocation
  rw [dif_neg]
  rintro ⟨p, hp⟩
  exact h p.1 p.2 hp

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

/-- Record caches hold no index entry. -/
theorem Record.query_ne_idx (hP : P.Hyp) (ξ : Record P) (a : Loc P) (m : Message) (η : Nonce)
    (pk : PublicKey) : ξ.query a ≠ ⟨896, P.idxInput m η pk⟩ := by
  intro h
  unfold Record.query at h
  have h' := query_inj h
  cases a with
  | inl a => exact Params.chainInput_ne_idxInput hP _ _ _ _ _ _ h'
  | inr r => exact Params.rootInput_ne_idxInput hP r.isLt _ _ _ _ _ h'

end OptimalOTS.LeanIsaBaseline.Layer
