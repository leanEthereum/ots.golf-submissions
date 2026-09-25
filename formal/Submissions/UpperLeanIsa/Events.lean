import Submissions.UpperLeanIsa.Transcript
import Submissions.UpperLeanIsa.BasicProperties

/-!
# The forgery structure

Deterministic extraction on the verifier's cached paths. Let `c` contain the points of `ζ`
exposed at a cut `d` (`RespectsExposed`), and let the verifier accept `(m₂, σ₂)` in `c` with
index `I₂`. Then, unless `c` hits a hidden point of `ζ` or a cut target of `ζ`:

* the reconstructed tops are the honest tops (`root_binding`: the tagged 9-call root has no
  second preimage on the verifier's cached calls, each call comparing the low half of its answer,
  the part the next call or the public key reads);
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

/-- A word placed in both halves of an answer, so that every step slice reads it. -/
def padWord (y : Word) : BitVec hashBits := y ++ y

theorem padWord_slice (k : Fin numChains) (j : ℕ) (y : Word) : P.slice k j (padWord y) = y := by
  unfold Params.slice Params.stepOff
  split
  · exact BitVec.extractLsb'_append_eq_left (a := y) (b := y)
  · exact BitVec.extractLsb'_append_eq_right (a := y) (b := y)

/-- The record whose chain `k` is constantly `t k` and whose root answers are all `st`. -/
def constRecord (t : Fin numChains → Word) (st : BitVec 256) : Record P :=
  (t, Sum.elim (fun a => padWord (t a.1)) (fun _ => st))

theorem constRecord_word (t : Fin numChains → Word) (st : BitVec 256) (k : Fin numChains)
    (j : ℕ) (hj : j ≤ P.len k - 1) : (constRecord (P := P) t st).word k j = t k := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [Record.word_succ _ k j (by omega)]
    exact padWord_slice k j _

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

theorem queryLocation_rootInput (hP : P.Hyp) (r : Fin 9) (t : Fin numChains → Word)
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
  have h1 : P.stepValue (table c) k i y = P.slice k i u :=
    congrArg (P.slice k i) (table_eq_of_some hu)
  have h2 : P.stepValue (table c) k i (ζ.word k i) = P.slice k i (ζ.2 (.inl ⟨k, ⟨i, hi⟩⟩)) :=
    congrArg (P.slice k i) (hf (.inl ⟨k, ⟨i, hi⟩⟩) hnh)
  refine mem_cutTargets_exposed (queryLocation_chainInput hP k ⟨i, hi⟩ y) hnh hne ?_
  rw [matchingAnswers_inl]
  exact mem_sliceAnswers.mpr (h1.symm.trans (hmatch.trans h2))

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
    have h1 : P.stepValue (table c) k (d k - 1) y = P.slice k (d k - 1) u :=
      congrArg (P.slice k (d k - 1)) (table_eq_of_some hu)
    have h2 : ζ.word k (d k) = P.slice k (d k - 1) (ζ.2 (.inl ⟨k, ⟨d k - 1, he⟩⟩)) := by
      rw [← Record.word_succ _ k (d k - 1) he, Nat.sub_add_cancel hpos]
    refine mem_cutTargets_boundary (queryLocation_chainInput hP k ⟨d k - 1, he⟩ y) hhid hbd ?_
    rw [matchingAnswers_inl]
    exact mem_sliceAnswers.mpr (h1.symm.trans (hmatch.trans h2))

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

/-- Equal inputs at all nine root calls (from the initial states `rootInit t`, `rootInit t'`)
force equal tops: every top is a cv or block word of exactly one call. Tops 37 and 38 are call 0's
cv, 3..6 its block; 0, 1, 2, 7 are call 1's block, 8..11 call 7's, 39..41 call 8's; and tops
`5r+2 … 5r+6` the cv and block of call `r = 2 … 6`. -/
theorem tops_eq_of_rootInputs (hP : P.Hyp) (t t' : Fin numChains → Word)
    (S S' : ℕ → BitVec 256) (h0 : S 0 = Params.rootInit t) (h0' : S' 0 = Params.rootInit t')
    (h : ∀ r < 9, P.rootInput t r (S r) = P.rootInput t' r (S' r)) : t = t' := by
  have hcb : ∀ r < 9, Params.rootCv t r (S r) = Params.rootCv t' r (S' r) ∧
      Params.rootBlock t r (S r) = Params.rootBlock t' r (S' r) := fun r hr =>
    ((Params.rootInput_eq_iff hP hr hr _ _ _ _).mp (h r hr)).2
  have htop : ∀ i, i < 42 → Params.topAt t i = Params.topAt t' i := by
    intro i hi
    by_cases h0i : i = 37 ∨ i = 38
    · have e := (hcb 0 (by norm_num)).1
      have hc0 : (0 = 0 ∨ 0 = 1 ∨ 7 ≤ 0) := Or.inl rfl
      unfold Params.rootCv at e
      rw [if_pos hc0, if_pos hc0, h0, h0'] at e
      unfold Params.rootInit at e
      obtain ⟨e37, e38⟩ := append_inj e
      rcases h0i with rfl | rfl
      · exact e37
      · exact e38
    by_cases h3 : 3 ≤ i ∧ i ≤ 6
    · have e := (hcb 0 (by norm_num)).2
      unfold Params.rootBlock at e
      rw [if_pos rfl, if_pos rfl] at e
      obtain ⟨e1, e2⟩ := append_inj e
      obtain ⟨e3, e4⟩ := append_inj e1
      obtain ⟨e5, e6⟩ := append_inj e3
      rcases (by omega : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl
      · exact e2
      · exact e4
      · exact e6
      · exact e5
    by_cases h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 7
    · have e := (hcb 1 (by norm_num)).2
      have h10 : ¬ (1 = 0) := by norm_num
      unfold Params.rootBlock at e
      rw [if_neg h10, if_pos rfl, if_neg h10, if_pos rfl] at e
      obtain ⟨e1, e0⟩ := append_inj e
      obtain ⟨e2, e3⟩ := append_inj e1
      obtain ⟨e5, e4⟩ := append_inj e2
      rcases h1 with rfl | rfl | rfl | rfl
      · exact e0
      · exact e3
      · exact e4
      · exact e5
    by_cases h8 : 8 ≤ i ∧ i ≤ 11
    · have e := (hcb 7 (by norm_num)).2
      have h70 : ¬ (7 = 0) := by norm_num
      have h71 : ¬ (7 = 1) := by norm_num
      have h77 : ¬ (7 < 7) := by norm_num
      unfold Params.rootBlock at e
      simp only [h70, h71, h77, ↓reduceIte] at e
      obtain ⟨e1, e8⟩ := append_inj e
      obtain ⟨e2, e9⟩ := append_inj e1
      obtain ⟨e11, e10⟩ := append_inj e2
      rcases (by omega : i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with rfl | rfl | rfl | rfl
      · exact e8
      · exact e9
      · exact e10
      · exact e11
    by_cases h39 : 39 ≤ i
    · have e := (hcb 8 (by norm_num)).2
      have h80 : ¬ (8 = 0) := by norm_num
      have h81 : ¬ (8 = 1) := by norm_num
      have h87 : ¬ (8 < 7) := by norm_num
      have h88 : ¬ (8 = 7) := by norm_num
      unfold Params.rootBlock at e
      simp only [h80, h81, h87, h88, ↓reduceIte] at e
      obtain ⟨e1, -⟩ := append_inj e
      obtain ⟨e2, e39⟩ := append_inj e1
      obtain ⟨e41, e40⟩ := append_inj e2
      rcases (by omega : i = 39 ∨ i = 40 ∨ i = 41) with rfl | rfl | rfl
      · exact e39
      · exact e40
      · exact e41
    · set r := (i - 2) / 5 with hr
      have hr0 : ¬ r = 0 := by omega
      have hr1 : ¬ r = 1 := by omega
      have hr7 : r < 7 := by omega
      have hc : ¬ (r = 0 ∨ r = 1 ∨ 7 ≤ r) := by omega
      obtain ⟨ec, eb⟩ := hcb r (by omega)
      unfold Params.rootCv at ec
      rw [if_neg hc, if_neg hc] at ec
      unfold Params.rootBlock at eb
      rw [if_neg hr0, if_neg hr1, if_pos hr7, if_neg hr0, if_neg hr1, if_pos hr7] at eb
      obtain ⟨c3, c2⟩ := append_inj ec
      obtain ⟨b1, -⟩ := append_inj eb
      obtain ⟨b2, b4⟩ := append_inj b1
      obtain ⟨b6, b5⟩ := append_inj b2
      rcases (by omega : i = 5 * r + 2 ∨ i = 5 * r + 3 ∨ i = 5 * r + 4 ∨ i = 5 * r + 5 ∨
          i = 5 * r + 6) with e | e | e | e | e <;> rw [e]
      · exact c2
      · exact c3
      · exact b4
      · exact b5
      · exact b6
  funext k
  have := htop k.val k.isLt
  unfold Params.topAt at this
  rwa [dif_pos k.isLt, dif_pos k.isLt] at this

/-- Equal inputs at a root call `r ≥ 1` read the low half of the state before it: calls `1`, `7`
and `8` carry the whole state as their cv, calls `2, …, 6` its low half in the block. -/
theorem lo_eq_of_rootInput (hP : P.Hyp) {r : ℕ} (hr : r < 9) (h1 : 1 ≤ r)
    (t t' : Fin numChains → Word) (st st' : BitVec 256)
    (h : P.rootInput t r st = P.rootInput t' r st') :
    st.extractLsb' 0 128 = st'.extractLsb' 0 128 := by
  obtain ⟨-, ec, eb⟩ := (Params.rootInput_eq_iff hP hr hr _ _ _ _).mp h
  by_cases hc : r = 0 ∨ r = 1 ∨ 7 ≤ r
  · unfold Params.rootCv at ec
    rw [if_pos hc, if_pos hc] at ec
    rw [ec]
  · have hr0 : ¬ r = 0 := by omega
    have hr1 : ¬ r = 1 := by omega
    have hr7 : r < 7 := by omega
    unfold Params.rootBlock at eb
    rw [if_neg hr0, if_neg hr1, if_pos hr7, if_neg hr0, if_neg hr1, if_pos hr7] at eb
    exact (append_inj eb).2

/-- The honest root states are reproduced by any table that respects the (always exposed) root
answers. -/
theorem rootFromValue_honest (f : HashTable) (d : Cut) (ζ : Record P)
    (hf : RespectsExposed f d ζ) :
    ∀ r, r ≤ 9 → P.rootFromValue f ζ.top 0 r (Params.rootInit ζ.top) = ζ.rootState r := by
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
  rw [rootFromValue_honest f d ζ hf 9 le_rfl, Record.rootState_succ_lt _ 8 (by norm_num)]
  rfl

/-- **Root binding.** A cached tagged root path of the verifier that reaches the public key
has the honest tops, or some call on it hits an exposed root target. -/
theorem root_binding (hP : P.Hyp) (d : Cut) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (t : Fin numChains → Word)
    (hpath : P.RootPath c t 0 9 (Params.rootInit t))
    (hroot : P.rootValue (table c) t = ζ.pk)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) : t = ζ.top := by
  have hf := respectsExposed_of_sub hP d ζ hc
  set S : ℕ → BitVec 256 := fun r => P.rootFromValue (table c) t 0 r (Params.rootInit t) with hS
  have hhon := rootFromValue_honest (table c) d ζ hf
  -- the step at call `r`: a mismatching input with a matching low half is a target hit
  have step : ∀ r (hr : r < 9),
      (S (r + 1)).extractLsb' 0 128 = (ζ.rootState (r + 1)).extractLsb' 0 128 →
      P.rootInput t r (S r) = P.rootInput ζ.top r (ζ.rootState r) := by
    intro r hr hm
    have hcached := hpath r hr
    rw [Nat.zero_add] at hcached
    by_contra hX
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
    exact mem_lowAnswers.mpr hm
  -- walk down from the last call
  have key : ∀ n, n ≤ 9 → ∀ s, 9 - n ≤ s → s < 9 →
      P.rootInput t s (S s) = P.rootInput ζ.top s (ζ.rootState s) := by
    intro n
    induction n with
    | zero => intro _ s hs hs'; omega
    | succ n ih =>
      intro hn s hs hs'
      have hr : 8 - n < 9 := by omega
      have hm : (S (8 - n + 1)).extractLsb' 0 128 =
          (ζ.rootState (8 - n + 1)).extractLsb' 0 128 := by
        by_cases h8 : n = 0
        · subst h8
          have hr' : (S 9).extractLsb' 0 128 = ζ.pk := hroot
          show (S 9).extractLsb' 0 128 = (ζ.rootState 9).extractLsb' 0 128
          rw [hr', ← rootValue_honest (table c) d ζ hf]
          unfold Params.rootValue
          rw [hhon 9 le_rfl]
        · exact lo_eq_of_rootInput hP (by omega) (by omega) _ _ _ _
            (ih (by omega) (8 - n + 1) (by omega) (by omega))
      by_cases hs0 : s = 8 - n
      · rw [hs0]
        exact step (8 - n) hr hm
      · exact ih (by omega) s (by omega) hs'
  exact tops_eq_of_rootInputs hP t ζ.top S ζ.rootState rfl rfl
    (fun r hr => key 9 le_rfl r (by omega) hr)

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

theorem digits_eq_of_le {I J : Index} (hI : P.Accepted I) (hJ : P.Accepted J)
    (h : ∀ k, P.digit J k ≤ P.digit I k) : P.digit J = P.digit I := by
  have hs : ∑ k, P.digit J k = ∑ k, P.digit I k := by
    have h1 : ∑ k, P.digit J k = P.layer := hJ
    have h2 : ∑ k, P.digit I k = P.layer := hI
    rw [h1, h2]
  funext k
  exact (Finset.sum_eq_sum_iff_of_le (fun k _ => h k)).mp hs k (Finset.mem_univ k)

variable (A : OracleAlgorithm.Adversary)

/-- **Forgery events after signing index `I₁`.** On the second-stage run from a cache holding the
points of `ζ` exposed by the signature, an accepted fresh pair yields a hidden hit, a cut-target
hit, or a different message or nonce whose cached index answer is accepted with the digits of
`I₁`. -/
theorem events_some (hP : P.Hyp) (pk : PublicKey) (m₁ : Message) (st : A.State) (ζ : Record P)
    (c : Cache) (I₁ : Index) (hI₁ : P.Accepted I₁) (η₁ : Nonce)
    (hc : Cache.Sub (exposedCache (afterSigning P I₁) ζ) c) (hpk : ζ.pk = pk)
    (p : Bool × Cache)
    (hp : p ∈ support (run (P.stB A pk m₁ st
      (some (encode (fun k => ζ.word k (afterSigning P I₁ k)) η₁))) c))
    (hok : p.1 = true) :
    Cache.Hits p.2 (hiddenCache (afterSigning P I₁) ζ) ∨
      TargetHit (cutTargets P (afterSigning P I₁) ζ) p.2 ∨
      ∃ (m₂ : Message) (η₂ : Nonce), (m₂, η₂) ≠ (m₁, η₁) ∧
        ∃ w, p.2 ⟨896, P.idxInput m₂ η₂ pk⟩ = some w ∧ P.Accepted (indexSlice w) ∧
          P.digit (indexSlice w) = P.digit I₁ := by
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
  have hII : P.digit I₂ = P.digit I₁ := digits_eq_of_le hI₁ hacc.accepted hle
  have hwords : decodeWord σ₂ = fun k => ζ.word k (afterSigning P I₁ k) := by
    funext k
    exact h2 k (by unfold afterSigning; rw [hII])
  refine ⟨m₂, decodeNonce σ₂, fun he => ?_, ?_⟩
  · apply hne
    obtain ⟨hm, hη⟩ := Prod.mk.inj he
    have hσ : σ₂ = encode (fun k => ζ.word k (afterSigning P I₁ k)) η₁ :=
      eq_of_decode_eq hacc.length (encode_length _ _)
        (by rw [hwords]; funext k; rw [decodeWord_encode]) (by rw [hη, decodeNonce_encode])
    rw [hm, hσ]
    rfl
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hacc.idx_cached
    have hwI : indexSlice w = I₂ := by
      rw [hI₂]
      exact congrArg indexSlice (table_eq_of_some hw).symm
    refine ⟨w, hw, ?_, ?_⟩
    · rw [hwI]; exact hacc.accepted
    · rw [hwI, hII]

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
