import Submissions.UpperLeanIsa.Transcript
import Submissions.UpperLeanIsa.BasicProperties

/-!
# The forgery structure

Deterministic extraction on the verifier's cached paths. Let `c` contain the points of `ζ`
exposed at a cut `d` (`RespectsExposed`), and let the verifier accept `(m₂, σ₂)` in `c` with
index `I₂`. Then, unless `c` hits a hidden point of `ζ` or a cut target of `ζ`:

* the reconstructed tops are the honest tops (`root_binding`: the tagged 10-call root has no
  second preimage on the verifier's cached calls, the internal calls comparing all 256 bits);
* no chain starts strictly below the cut, and a chain that starts at the cut starts at the
  honest word there (`accept_core`).

After signing index `I₁` (cut `afterSigning I₁`), the accepted layer is an antichain: a
different accepted index moves some chain below the cut, so the forged index is `I₁`, the words
are the revealed ones, and a fresh pair must use a different message or nonce whose cached
index answer is `I₁` (`events_some`). If signing failed (cut `beforeSigning`), every accepted
index has a nonzero digit, which moves that chain below the tops (`events_none`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

variable {P : Params}

/-! ## Tables respecting the exposed points -/

/-- The table respects `ζ` at every location exposed at cut `d`. -/
def RespectsExposed (f : HashTable) (d : Cut) (ζ : Record P) : Prop :=
  ∀ a, ¬ Hidden d a → f (ζ.query a) = ζ.2 a

theorem respectsExposed_of_sub (hP : P.Hyp) (d : Cut) (ζ : Record P) {c : Cache}
    (h : Cache.Sub (exposedCache d ζ) c) : RespectsExposed (table c) d ζ := by
  intro a ha
  have h1 : exposedCache d ζ (ζ.query a) = some (ζ.2 a) :=
    (exposedCache_some_iff hP d ζ _ _).2 ⟨a, ha, rfl, rfl⟩
  exact table_eq_of_some (h _ _ h1)

theorem chainValue_exposed (f : HashTable) (d : Cut) (ζ : Record P)
    (hf : RespectsExposed f d ζ) (k : Fin numChains) :
    ∀ (n j : ℕ), d k ≤ j → j + n ≤ P.len k - 1 →
      P.chainValue f k j n (ζ.word k j) = ζ.word k (j + n) := by
  intro n
  induction n with
  | zero => intro j _ _; rfl
  | succ n ih =>
    intro j hj hjn
    have hl : j < P.len k - 1 := by omega
    rw [Params.chainValue_succ]
    have hq : f ⟨896, P.chainInput k j (ζ.word k j)⟩ = ζ.2 (.inl ⟨k, ⟨j, hl⟩⟩) :=
      hf (.inl ⟨k, ⟨j, hl⟩⟩) (by show ¬ j < d k; omega)
    have hw : P.stepValue f k j (ζ.word k j) = ζ.word k (j + 1) := by
      unfold Params.stepValue
      rw [hq, Record.word_succ _ k j hl]
    rw [hw, ih (j + 1) (by omega) (by omega), show j + 1 + n = j + (n + 1) by omega]

/-- If two continuations merge, either they began at the same word or there is a step whose
inputs differ and whose outputs agree. -/
theorem chain_merge (f : HashTable) (k : Fin numChains) :
    ∀ (n j : ℕ) (x y : Word), P.chainValue f k j n x = P.chainValue f k j n y →
      x = y ∨ ∃ i, i < n ∧ P.chainValue f k j i x ≠ P.chainValue f k j i y ∧
        P.stepValue f k (j + i) (P.chainValue f k j i x) =
          P.stepValue f k (j + i) (P.chainValue f k j i y) := by
  intro n
  induction n with
  | zero => intro j x y h; exact Or.inl h
  | succ n ih =>
    intro j x y h
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      rcases ih (j + 1) (P.stepValue f k j x) (P.stepValue f k j y) h with
        heq | ⟨i, hi, hne, heq⟩
      · exact ⟨0, by omega, hxy, heq⟩
      · refine ⟨i + 1, by omega, hne, ?_⟩
        rw [Params.chainValue_succ, Params.chainValue_succ, show j + (i + 1) = j + 1 + i by omega]
        exact heq

/-- Reaching the honest top from a word at an exposed position: the honest word, or a second
preimage of an honest step at or after that position. -/
theorem endpoint_match_exposed (f : HashTable) (d : Cut) (ζ : Record P)
    (hf : RespectsExposed f d ζ) (k : Fin numChains) (j : ℕ) (hj : d k ≤ j)
    (hj' : j ≤ P.len k - 1) (x : Word)
    (h : P.chainValue f k j (P.len k - 1 - j) x = ζ.top k) :
    x = ζ.word k j ∨ ∃ i, j ≤ i ∧ i < P.len k - 1 ∧
      P.chainValue f k j (i - j) x ≠ ζ.word k i ∧
      P.stepValue f k i (P.chainValue f k j (i - j) x) = P.stepValue f k i (ζ.word k i) := by
  have hhon : P.chainValue f k j (P.len k - 1 - j) (ζ.word k j) = ζ.top k := by
    rw [chainValue_exposed f d ζ hf k _ j hj (by omega)]
    unfold Record.top
    congr 1
    omega
  rcases chain_merge f k _ j x (ζ.word k j) (h.trans hhon.symm) with heq | ⟨i, hi, hne, hstep⟩
  · exact Or.inl heq
  · right
    have hw := chainValue_exposed f d ζ hf k i j hj (by omega)
    refine ⟨j + i, by omega, by omega, ?_, ?_⟩
    · rw [Nat.add_sub_cancel_left]
      rw [hw] at hne
      exact hne
    · rw [Nat.add_sub_cancel_left]
      rw [hw] at hstep
      exact hstep

/-! ## Records realising a query -/

/-- A word placed in the low half of an answer. -/
def padWord (y : Word) : BitVec hashBits := (0 : BitVec 128) ++ y

theorem padWord_low (y : Word) : (padWord y).extractLsb' 0 128 = y :=
  BitVec.extractLsb'_append_eq_right (a := (0 : BitVec 128)) (b := y)

/-- The record whose chain `k` is constantly `t k` and whose root answers are all `st`. -/
def constRecord (t : Fin numChains → Word) (st : BitVec 256) : Record P :=
  (t, Sum.elim (fun a => padWord (t a.1)) (fun _ => st))

theorem constRecord_word (t : Fin numChains → Word) (st : BitVec 256) (k : Fin numChains)
    (j : ℕ) (hj : j ≤ P.len k - 1) : (constRecord (P := P) t st).word k j = t k := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [Record.word_succ _ k j (by omega)]
    exact padWord_low _

theorem constRecord_top (t : Fin numChains → Word) (st : BitVec 256) :
    (constRecord (P := P) t st).top = t :=
  funext fun k => constRecord_word t st k _ le_rfl

theorem queryLocation_chainInput (hP : P.Hyp) (k : Fin numChains) (j : Fin (P.len k - 1))
    (y : Word) : queryLocation P ⟨896, P.chainInput k j.val y⟩ = some (.inl ⟨k, j⟩) := by
  have hq : (constRecord (P := P) (fun _ => y) 0).query (.inl ⟨k, j⟩) =
      ⟨896, P.chainInput k j.val y⟩ := by
    rw [Record.query_inl, constRecord_word _ _ k j.val (by have := j.isLt; omega)]
  rw [← hq]
  exact queryLocation_query hP _ _

theorem queryLocation_rootInput (hP : P.Hyp) (r : Fin 10) (t : Fin numChains → Word)
    (st : BitVec 256) (h0 : r.val = 0 → st = Params.rootInit t) :
    queryLocation P ⟨896, P.rootInput t r.val st⟩ = some (.inr r) := by
  have hq : (constRecord (P := P) t st).query (.inr r) = ⟨896, P.rootInput t r.val st⟩ := by
    rw [Record.query_inr, constRecord_top]
    congr 3
    rcases r with ⟨r, hr⟩
    cases r with
    | zero => rw [Record.rootState_zero, constRecord_top]; exact (h0 rfl).symm
    | succ r => rw [Record.rootState_succ_lt _ r (by omega)]; rfl
  rw [← hq]
  exact queryLocation_query hP _ _

/-! ## Chain events -/

/-- A chain second preimage at an exposed step, on a cached verifier step, is a cut-target hit. -/
theorem chain_spi_targetHit (hP : P.Hyp) (d : Cut) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (i : ℕ)
    (hi : i < P.len k - 1) (hexp : d k ≤ i) (y : Word) (hy : y ≠ ζ.word k i)
    (hcached : (c ⟨896, P.chainInput k i y⟩).isSome)
    (hmatch : P.stepValue (table c) k i y = P.stepValue (table c) k i (ζ.word k i)) :
    TargetHit (cutTargets P d ζ) c := by
  have hf := respectsExposed_of_sub hP d ζ hc
  have hnh : ¬ Hidden d (.inl ⟨k, ⟨i, hi⟩⟩) := by
    show ¬ i < d k
    omega
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcached
  refine ⟨⟨896, P.chainInput k i y⟩, u, hu, ?_⟩
  have hne : ζ.query (.inl ⟨k, ⟨i, hi⟩⟩) ≠ ⟨896, P.chainInput k i y⟩ := by
    intro h
    rw [Record.query_inl] at h
    exact hy ((Params.chainInput_same_iff k i _ _).mp (query_inj h)).symm
  have h1 : P.stepValue (table c) k i y = u.extractLsb' 0 128 :=
    congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_eq_of_some hu)
  have h2 : P.stepValue (table c) k i (ζ.word k i) =
      (ζ.2 (.inl ⟨k, ⟨i, hi⟩⟩)).extractLsb' 0 128 :=
    congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (hf (.inl ⟨k, ⟨i, hi⟩⟩) hnh)
  refine mem_cutTargets_exposed (queryLocation_chainInput hP k ⟨i, hi⟩ y) hnh hne ?_
  rw [matchingAnswers_inl]
  exact mem_lowAnswers.mpr (h1.symm.trans (hmatch.trans h2))

/-- A cached verifier step just below the cut whose output is the public word at the cut: the
honest hidden input was queried, or the boundary target was hit. -/
theorem boundary_hit (hP : P.Hyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (hpos : 0 < d k)
    (y : Word) (hcached : (c ⟨896, P.chainInput k (d k - 1) y⟩).isSome)
    (hmatch : P.stepValue (table c) k (d k - 1) y = ζ.word k (d k)) :
    Cache.Hits c (hiddenCache d ζ) ∨ TargetHit (cutTargets P d ζ) c := by
  have hdk := hd k
  have he : d k - 1 < P.len k - 1 := by omega
  have hhid : Hidden d (.inl ⟨k, ⟨d k - 1, he⟩⟩) := by
    show d k - 1 < d k
    omega
  by_cases hy : y = ζ.word k (d k - 1)
  · left
    refine ⟨⟨896, P.chainInput k (d k - 1) y⟩, ?_, hcached⟩
    refine (hiddenCache_isSome_iff hP d ζ _).2 ⟨.inl ⟨k, ⟨d k - 1, he⟩⟩, hhid, ?_⟩
    rw [Record.query_inl, hy]
  · right
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcached
    refine ⟨⟨896, P.chainInput k (d k - 1) y⟩, u, hu, ?_⟩
    have hbd : Boundary d (.inl ⟨k, ⟨d k - 1, he⟩⟩) := by
      show d k - 1 + 1 = d k
      omega
    have h1 : P.stepValue (table c) k (d k - 1) y = u.extractLsb' 0 128 :=
      congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_eq_of_some hu)
    have h2 : ζ.word k (d k) = (ζ.2 (.inl ⟨k, ⟨d k - 1, he⟩⟩)).extractLsb' 0 128 := by
      rw [← Record.word_succ _ k (d k - 1) he, Nat.sub_add_cancel hpos]
    refine mem_cutTargets_boundary (queryLocation_chainInput hP k ⟨d k - 1, he⟩ y) hhid hbd ?_
    rw [matchingAnswers_inl]
    exact mem_lowAnswers.mpr (h1.symm.trans (hmatch.trans h2))

/-- A chain that starts strictly below the cut and reaches the honest top passes the boundary
(hidden or boundary hit) or merges later (exposed chain target). -/
theorem lower_chain (hP : P.Hyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (e : ℕ) (he : e < d k)
    (y : Word) (hpath : P.ChainPath c k e (P.len k - 1 - e) y)
    (hend : P.chainValue (table c) k e (P.len k - 1 - e) y = ζ.top k) :
    Cache.Hits c (hiddenCache d ζ) ∨ TargetHit (cutTargets P d ζ) c := by
  have hdk := hd k
  have hf := respectsExposed_of_sub hP d ζ hc
  have hmid : P.chainValue (table c) k (d k) (P.len k - 1 - d k)
      (P.chainValue (table c) k e (d k - e) y) = ζ.top k := by
    have h := P.chainValue_add (table c) k e (d k - e) (P.len k - 1 - d k) y
    rw [show e + (d k - e) = d k by omega,
      show d k - e + (P.len k - 1 - d k) = P.len k - 1 - e by omega] at h
    exact h.trans hend
  rcases endpoint_match_exposed (table c) d ζ hf k (d k) le_rfl hdk _ hmid with
    heq | ⟨i, hji, hi, hne, hstep⟩
  · have hpos : 0 < d k := by omega
    have hcached' : (c ⟨896, P.chainInput k (d k - 1)
        (P.chainValue (table c) k e (d k - 1 - e) y)⟩).isSome :=
      Params.ChainPath.cached P hpath (by omega) (by omega)
    have hmatch' : P.stepValue (table c) k (d k - 1)
        (P.chainValue (table c) k e (d k - 1 - e) y) = ζ.word k (d k) := by
      have h := P.chainValue_snoc (table c) k e (d k - 1 - e) y
      rw [show d k - 1 - e + 1 = d k - e by omega,
        show e + (d k - 1 - e) = d k - 1 by omega] at h
      exact h.symm.trans heq
    exact boundary_hit hP d hd ζ c hc k hpos _ hcached' hmatch'
  · right
    have hY : P.chainValue (table c) k (d k) (i - d k)
        (P.chainValue (table c) k e (d k - e) y) = P.chainValue (table c) k e (i - e) y := by
      have h := P.chainValue_add (table c) k e (d k - e) (i - d k) y
      rw [show e + (d k - e) = d k by omega,
        show d k - e + (i - d k) = i - e by omega] at h
      exact h
    have hcached := Params.ChainPath.cached P hpath (i := i) (by omega) (by omega)
    rw [← hY] at hcached
    exact chain_spi_targetHit hP d ζ c hc k i hi hji _ hne hcached hstep

/-- A chain that starts at or above the cut and reaches the honest top starts at the honest
word, or hits an exposed chain target. -/
theorem upper_chain (hP : P.Hyp) (d : Cut) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (e : ℕ) (he : d k ≤ e)
    (he' : e ≤ P.len k - 1) (y : Word) (hpath : P.ChainPath c k e (P.len k - 1 - e) y)
    (hend : P.chainValue (table c) k e (P.len k - 1 - e) y = ζ.top k) :
    y = ζ.word k e ∨ TargetHit (cutTargets P d ζ) c := by
  have hf := respectsExposed_of_sub hP d ζ hc
  rcases endpoint_match_exposed (table c) d ζ hf k e he he' y hend with
    heq | ⟨i, hji, hi, hne, hstep⟩
  · exact Or.inl heq
  · right
    have hcached := Params.ChainPath.cached P hpath (i := i) hji (by omega)
    exact chain_spi_targetHit hP d ζ c hc k i hi (by omega) _ hne hcached hstep

/-! ## Root events -/

/-- The block of root call `r`. -/
def rootBlock (t : Fin numChains → Word) (r : ℕ) : BitVec 512 :=
  Params.topAt t (4 * r + 5) ++ Params.topAt t (4 * r + 4) ++ Params.topAt t (4 * r + 3) ++
    Params.topAt t (4 * r + 2)

theorem rootInput_eq_iff' (hP : P.Hyp) {r : ℕ} (hr : r < 10) (t t' : Fin numChains → Word)
    (st st' : BitVec 256) :
    P.rootInput t r st = P.rootInput t' r st' ↔ st = st' ∧ rootBlock t r = rootBlock t' r := by
  rw [Params.rootInput_eq_iff hP hr hr]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨rfl, h.1, h.2⟩⟩

theorem tops_eq_of_blocks (t t' : Fin numChains → Word)
    (h0 : Params.rootInit t = Params.rootInit t')
    (hb : ∀ r < 10, rootBlock t r = rootBlock t' r) : t = t' := by
  have htop : ∀ i, Params.topAt t i = Params.topAt t' i := by
    intro i
    by_cases hi : i < 42
    · by_cases h2 : i < 2
      · obtain ⟨h1, h0'⟩ := append_inj h0
        interval_cases i
        · exact h0'
        · exact h1
      · have hr : (i - 2) / 4 < 10 := by omega
        have e := hb _ hr
        unfold rootBlock at e
        obtain ⟨e1, e2⟩ := append_inj e
        obtain ⟨e3, e4⟩ := append_inj e1
        obtain ⟨e5, e6⟩ := append_inj e3
        have hmod : (i - 2) % 4 < 4 := Nat.mod_lt _ (by norm_num)
        have hdecomp : i = 4 * ((i - 2) / 4) + 2 + (i - 2) % 4 := by omega
        rcases (by omega : (i - 2) % 4 = 0 ∨ (i - 2) % 4 = 1 ∨ (i - 2) % 4 = 2 ∨
            (i - 2) % 4 = 3) with h | h | h | h
        · rw [show i = 4 * ((i - 2) / 4) + 2 by omega]; exact e2
        · rw [show i = 4 * ((i - 2) / 4) + 3 by omega]; exact e4
        · rw [show i = 4 * ((i - 2) / 4) + 4 by omega]; exact e6
        · rw [show i = 4 * ((i - 2) / 4) + 5 by omega]; exact e5
    · unfold Params.topAt
      rw [dif_neg hi, dif_neg hi]
  funext k
  have := htop k.val
  unfold Params.topAt at this
  rwa [dif_pos k.isLt, dif_pos k.isLt] at this

/-- The honest root states are reproduced by any table that respects the (always exposed) root
answers. -/
theorem rootFromValue_honest (f : HashTable) (d : Cut) (ζ : Record P)
    (hf : RespectsExposed f d ζ) :
    ∀ r, r ≤ 10 → P.rootFromValue f ζ.top 0 r (Params.rootInit ζ.top) = ζ.rootState r := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih =>
    intro hr
    rw [Params.rootFromValue_snoc, Nat.zero_add, ih (by omega)]
    have h := hf (.inr ⟨r, by omega⟩) (not_hidden_inr d _)
    rw [Record.query_inr] at h
    rw [h, Record.rootState_succ_lt _ r (by omega)]

theorem rootValue_honest (f : HashTable) (d : Cut) (ζ : Record P)
    (hf : RespectsExposed f d ζ) : P.rootValue f ζ.top = ζ.pk := by
  unfold Params.rootValue
  rw [rootFromValue_honest f d ζ hf 10 le_rfl, Record.rootState_succ_lt _ 9 (by norm_num)]
  rfl

/-- **Root binding.** A cached tagged root path of the verifier that reaches the public key
has the honest tops, or some call on it hits an exposed root target. -/
theorem root_binding (hP : P.Hyp) (d : Cut) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (t : Fin numChains → Word)
    (hpath : P.RootPath c t 0 10 (Params.rootInit t))
    (hroot : P.rootValue (table c) t = ζ.pk)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) : t = ζ.top := by
  have hf := respectsExposed_of_sub hP d ζ hc
  set S : ℕ → BitVec 256 := fun r => P.rootFromValue (table c) t 0 r (Params.rootInit t) with hS
  have hhon := rootFromValue_honest (table c) d ζ hf
  -- the step at call `r`: a mismatching input with a matching answer is a target hit
  have step : ∀ r (hr : r < 10),
      (if r = 9 then (S (r + 1)).extractLsb' 0 128 = (ζ.rootState (r + 1)).extractLsb' 0 128
        else S (r + 1) = ζ.rootState (r + 1)) →
      S r = ζ.rootState r ∧ rootBlock t r = rootBlock ζ.top r := by
    intro r hr hm
    have hcached := hpath r hr
    rw [Nat.zero_add] at hcached
    by_cases hX : P.rootInput t r (S r) = P.rootInput ζ.top r (ζ.rootState r)
    · exact (rootInput_eq_iff' hP hr _ _ _ _).mp hX
    · exfalso
      apply hno
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcached
      refine ⟨⟨896, P.rootInput t r (S r)⟩, u, hu, ?_⟩
      have hSu : S (r + 1) = u := by
        show P.rootFromValue (table c) t 0 (r + 1) (Params.rootInit t) = u
        rw [Params.rootFromValue_snoc, Nat.zero_add]
        exact table_eq_of_some hu
      have hloc := queryLocation_rootInput hP ⟨r, hr⟩ t (S r) (fun h0 => by
        simp only at h0
        subst h0
        rfl)
      have hne : ζ.query (.inr ⟨r, hr⟩) ≠ ⟨896, P.rootInput t r (S r)⟩ := by
        intro h
        rw [Record.query_inr] at h
        exact hX (query_inj h).symm
      refine mem_cutTargets_exposed hloc (not_hidden_inr d _) hne ?_
      rw [matchingAnswers_inr, ← Record.rootState_succ_lt _ r hr, ← hSu]
      by_cases h9 : r = 9
      · rw [if_pos (show (⟨r, hr⟩ : Fin 10).val = 9 from h9)]
        rw [if_pos h9] at hm
        exact mem_lowAnswers.mpr hm
      · rw [if_neg (show ¬ (⟨r, hr⟩ : Fin 10).val = 9 from h9)]
        rw [if_neg h9] at hm
        rw [hm]
        exact Finset.mem_singleton_self _
  -- walk down from the last call
  have key : ∀ n, n ≤ 10 → ∀ s, 10 - n ≤ s → s < 10 →
      S s = ζ.rootState s ∧ rootBlock t s = rootBlock ζ.top s := by
    intro n
    induction n with
    | zero => intro _ s hs hs'; omega
    | succ n ih =>
      intro hn s hs hs'
      have hr : 9 - n < 10 := by omega
      have hm : (if 9 - n = 9 then (S (9 - n + 1)).extractLsb' 0 128 =
            (ζ.rootState (9 - n + 1)).extractLsb' 0 128
          else S (9 - n + 1) = ζ.rootState (9 - n + 1)) := by
        by_cases h9 : 9 - n = 9
        · rw [if_pos h9, show 9 - n + 1 = 10 by omega]
          have hr' : (S 10).extractLsb' 0 128 = ζ.pk := hroot
          rw [hr', ← rootValue_honest (table c) d ζ hf]
          unfold Params.rootValue
          rw [hhon 10 le_rfl]
        · rw [if_neg h9]
          exact (ih (by omega) (9 - n + 1) (by omega) (by omega)).1
      by_cases hs0 : s = 9 - n
      · rw [hs0]
        exact step (9 - n) hr hm
      · exact ih (by omega) s (by omega) hs'
  have h0 := key 10 le_rfl
  apply tops_eq_of_blocks t ζ.top
  · have := (h0 0 (by norm_num) (by norm_num)).1
    exact this
  · intro r hr
    exact (h0 r (by omega) hr).2

/-! ## The events lemma -/

/-- The deterministic core: an accepted pair in a cache holding the exposed points of `ζ` and
missing every hidden point and cut target of `ζ` has no chain starting below the cut, and the
chains starting at the cut start at the honest words. -/
theorem accept_core (hP : P.Hyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (pk : PublicKey) (hpk : ζ.pk = pk)
    (m₂ : Message) (σ₂ : List Bool) (hacc : P.Accepts c pk m₂ σ₂)
    (hh : ¬ Cache.Hits c (hiddenCache d ζ)) (ht : ¬ TargetHit (cutTargets P d ζ) c) :
    (∀ k, d k ≤ P.len k - 1 - P.digit (P.idxValue (table c) m₂ (decodeNonce σ₂) pk) k) ∧
    (∀ k, P.len k - 1 - P.digit (P.idxValue (table c) m₂ (decodeNonce σ₂) pk) k = d k →
      decodeWord σ₂ k = ζ.word k (d k)) := by
  set I₂ := P.idxValue (table c) m₂ (decodeNonce σ₂) pk with hI₂
  have hrec : P.reconWords (table c) I₂ σ₂ = ζ.top :=
    root_binding hP d ζ c hc _ hacc.rootPath (hacc.root.trans hpk.symm) ht
  have hchain : ∀ k, P.chainValue (table c) k (P.len k - 1 - P.digit I₂ k)
      (P.len k - 1 - (P.len k - 1 - P.digit I₂ k)) (decodeWord σ₂ k) = ζ.top k ∧
      P.ChainPath c k (P.len k - 1 - P.digit I₂ k)
        (P.len k - 1 - (P.len k - 1 - P.digit I₂ k)) (decodeWord σ₂ k) := by
    intro k
    have hdl := hP.digit_lt I₂ k
    have hn : P.len k - 1 - (P.len k - 1 - P.digit I₂ k) = P.digit I₂ k := by omega
    rw [hn]
    exact ⟨congrFun hrec k, hacc.chains k⟩
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · by_contra hlt
    rcases lower_chain hP d hd ζ c hc k _ (by omega) _ (hchain k).2 (hchain k).1 with h | h
    · exact hh h
    · exact ht h
  · have hdk := hd k
    rcases upper_chain hP d ζ c hc k _ (by omega) (Nat.sub_le _ _) _ (hchain k).2
        (hchain k).1 with h | h
    · rw [h, hk]
    · exact absurd h ht

theorem digits_eq_of_le (hP : P.Hyp) {I J : Word} (hI : P.Accepted I) (hJ : P.Accepted J)
    (h : ∀ k, P.digit J k ≤ P.digit I k) : J = I := by
  apply hP.digit_inj
  have hs : ∑ k, P.digit J k = ∑ k, P.digit I k := by
    have h1 : ∑ k, P.digit J k = P.layer := hJ
    have h2 : ∑ k, P.digit I k = P.layer := hI
    rw [h1, h2]
  intro k
  exact (Finset.sum_eq_sum_iff_of_le (fun k _ => h k)).mp hs k (Finset.mem_univ k)

variable (A : OracleAlgorithm.Adversary)

/-- **Forgery events after signing index `I₁`.** On the second-stage run from a cache holding the
points of `ζ` exposed by the signature, an accepted fresh pair yields a hidden hit, a cut-target
hit, or a different message or nonce whose cached index answer is `I₁`. -/
theorem events_some (hP : P.Hyp) (pk : PublicKey) (m₁ : Message) (st : A.State) (ζ : Record P)
    (c : Cache) (I₁ : Word) (hI₁ : P.Accepted I₁) (η₁ : Nonce)
    (hc : Cache.Sub (exposedCache (afterSigning P I₁) ζ) c) (hpk : ζ.pk = pk)
    (p : Bool × Cache)
    (hp : p ∈ support (run (P.stB A pk m₁ st
      (some (encode (fun k => ζ.word k (afterSigning P I₁ k)) η₁))) c))
    (hok : p.1 = true) :
    Cache.Hits p.2 (hiddenCache (afterSigning P I₁) ζ) ∨
      TargetHit (cutTargets P (afterSigning P I₁) ζ) p.2 ∨
      ∃ (m₂ : Message) (η₂ : Nonce), (m₂, η₂) ≠ (m₁, η₁) ∧
        ∃ w, p.2 ⟨896, P.idxInput m₂ η₂ pk⟩ = some w ∧ w.extractLsb' 0 128 = I₁ := by
  obtain ⟨hcp, h⟩ := P.stB_support A pk m₁ st _ c p hp
  obtain ⟨m₂, σ₂, hne, hacc⟩ := h hok
  have hsub := hc.trans hcp
  by_cases hh : Cache.Hits p.2 (hiddenCache (afterSigning P I₁) ζ)
  · exact Or.inl hh
  by_cases ht : TargetHit (cutTargets P (afterSigning P I₁) ζ) p.2
  · exact Or.inr (Or.inl ht)
  right; right
  obtain ⟨h1, h2⟩ := accept_core hP _ (afterSigning_valid I₁) ζ p.2 hsub pk hpk m₂ σ₂ hacc hh ht
  set I₂ := P.idxValue (table p.2) m₂ (decodeNonce σ₂) pk with hI₂
  have hle : ∀ k, P.digit I₂ k ≤ P.digit I₁ k := by
    intro k
    have := h1 k
    have hd1 := hP.digit_lt I₁ k
    have hd2 := hP.digit_lt I₂ k
    unfold afterSigning at this
    omega
  have hII : I₂ = I₁ := digits_eq_of_le hP hI₁ hacc.accepted hle
  have hwords : decodeWord σ₂ = fun k => ζ.word k (afterSigning P I₁ k) := by
    funext k
    exact h2 k (by rw [hII]; rfl)
  refine ⟨m₂, decodeNonce σ₂, fun he => ?_, ?_⟩
  · apply hne
    obtain ⟨hm, hη⟩ := Prod.mk.inj he
    have hσ : σ₂ = encode (fun k => ζ.word k (afterSigning P I₁ k)) η₁ :=
      eq_of_decode_eq hacc.length (encode_length _ _)
        (by rw [hwords]; funext k; rw [decodeWord_encode]) (by rw [hη, decodeNonce_encode])
    rw [hm, hσ]
    rfl
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hacc.idx_cached
    refine ⟨w, hw, ?_⟩
    rw [← hII, hI₂]
    exact congrArg (fun z : BitVec hashBits => z.extractLsb' 0 128) (table_eq_of_some hw).symm

/-- **Forgery events after a signing failure.** Every accepted pair yields a hidden hit or a
cut-target hit at the cut before signing. -/
theorem events_none (hP : P.Hyp) (pk : PublicKey) (m₁ : Message) (st : A.State) (ζ : Record P)
    (c : Cache) (hc : Cache.Sub (exposedCache (beforeSigning P) ζ) c) (hpk : ζ.pk = pk)
    (p : Bool × Cache) (hp : p ∈ support (run (P.stB A pk m₁ st none) c))
    (hok : p.1 = true) :
    Cache.Hits p.2 (hiddenCache (beforeSigning P) ζ) ∨
      TargetHit (cutTargets P (beforeSigning P) ζ) p.2 := by
  obtain ⟨hcp, h⟩ := P.stB_support A pk m₁ st _ c p hp
  obtain ⟨m₂, σ₂, -, hacc⟩ := h hok
  have hsub := hc.trans hcp
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨h1, -⟩ := accept_core hP _ beforeSigning_valid ζ p.2 hsub pk hpk m₂ σ₂ hacc hno.1 hno.2
  set I₂ := P.idxValue (table p.2) m₂ (decodeNonce σ₂) pk
  have hz : ∀ k, P.digit I₂ k = 0 := by
    intro k
    have := h1 k
    have hd2 := hP.digit_lt I₂ k
    unfold beforeSigning at this
    omega
  have hsum : ∑ k, P.digit I₂ k = P.layer := hacc.accepted
  simp only [hz, Finset.sum_const_zero] at hsum
  have := hP.layer_pos
  omega

end OptimalOTS.LeanIsaBaseline.Layer
