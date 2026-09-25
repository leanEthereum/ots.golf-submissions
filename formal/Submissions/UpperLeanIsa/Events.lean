import Submissions.UpperLeanIsa.Transcript
import Submissions.UpperLeanIsa.BasicProperties

/-!
# The forgery structure

Deterministic extraction on the verifier's cached paths. Let `c` contain the points of `ζ`
exposed at a cut `d` (`RespectsExposed`), and let the verifier accept `(m₂, σ₂)` in `c` with
index `I₂`. Then, unless `c` hits a hidden point of `ζ` or a cut target of `ζ`:

* the reconstructed tops are the honest tops (`root_binding`: the 8-call root has no second
  preimage on the verifier's cached calls, each call comparing the low half of its answer, the
  part the next call or the public key reads; the last call is caught by the public-key target,
  or, when its metadata is the index metadata, by the index target at call 6);
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

theorem respectsExposed_of_sub (hP : P.Hyp) (d : Cut) (ζ : Record P) (hζ : ζ.Sep) {c : Cache}
    (h : Cache.Sub (exposedCache d ζ) c) : RespectsExposed (table c) d ζ := by
  intro a ha
  have h1 : exposedCache d ζ (ζ.query a) = some (ζ.2 a) :=
    (exposedCache_some_iff hP d ζ _ _).2 ⟨a, ha, Record.validAt_of_sep hζ a, rfl, rfl⟩
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
  exact queryLocation_query hP _ _ (Record.validAt_inl _ _)

theorem queryLocation_rootInput (hP : P.Hyp) (r : Fin 8) (hr : r.val < 7)
    (t : Fin numChains → Word)
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
  exact queryLocation_query hP _ _ (Record.validAt_inr_lt _ hr)

/-! ## Chain events -/

/-- A chain second preimage at an exposed step, on a cached verifier step, is a cut-target hit. -/
theorem chain_spi_targetHit (hP : P.Hyp) (d : Cut) (ζ : Record P) (hζ : ζ.Sep) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (i : ℕ)
    (hi : i < P.len k - 1) (hexp : d k ≤ i) (y : Word) (hy : y ≠ ζ.word k i)
    (hcached : (c ⟨896, P.chainInput k i y⟩).isSome)
    (hmatch : P.stepValue (table c) k i y = P.stepValue (table c) k i (ζ.word k i)) :
    TargetHit (cutTargets P d ζ) c := by
  have hf := respectsExposed_of_sub hP d ζ hζ hc
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
theorem lower_chain (hP : P.Hyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P) (hζ : ζ.Sep)
    (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (e : ℕ) (he : e < d k)
    (y : Word) (hpath : P.ChainPath c k e (P.len k - 1 - e) y)
    (hend : P.chainValue (table c) k e (P.len k - 1 - e) y = ζ.top k) :
    Cache.Hits c (hiddenCache d ζ) ∨ TargetHit (cutTargets P d ζ) c := by
  have hdk := hd k
  have hf := respectsExposed_of_sub hP d ζ hζ hc
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
    exact chain_spi_targetHit hP d ζ hζ c hc k i hi hji _ hne hcached hstep

/-- A chain that starts at or above the cut and reaches the honest top starts at the honest
word, or hits an exposed chain target. -/
theorem upper_chain (hP : P.Hyp) (d : Cut) (ζ : Record P) (hζ : ζ.Sep) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (e : ℕ) (he : d k ≤ e)
    (he' : e ≤ P.len k - 1) (y : Word) (hpath : P.ChainPath c k e (P.len k - 1 - e) y)
    (hend : P.chainValue (table c) k e (P.len k - 1 - e) y = ζ.top k) :
    y = ζ.word k e ∨ TargetHit (cutTargets P d ζ) c := by
  have hf := respectsExposed_of_sub hP d ζ hζ hc
  rcases endpoint_match_exposed (table c) d ζ hf k e he he' y hend with
    heq | ⟨i, hji, hi, hne, hstep⟩
  · exact Or.inl heq
  · right
    have hcached := Params.ChainPath.cached P hpath (i := i) hji (by omega)
    exact chain_spi_targetHit hP d ζ hζ c hc k i hi (by omega) _ hne hcached hstep

/-! ## Root events -/

theorem cv_block_of_rootInput (hP : P.Hyp) {r : ℕ} (hr : r < 8) (t t' : Fin numChains → Word)
    (st st' : BitVec 256) (h : P.rootInput t r st = P.rootInput t' r st') :
    Params.rootCv t r st = Params.rootCv t' r st' ∧
      Params.rootBlock t r st = Params.rootBlock t' r st' := by
  by_cases h7 : r < 7
  · exact ((Params.rootInput_eq_iff hP h7 h7 _ _ _ _).mp h).2
  · obtain rfl : r = 7 := by omega
    have := (Params.rootInput_seven_iff _ _ _ _).mp h
    exact ⟨this.1, this.2.1⟩

/-- Equal inputs at all eight root calls (from the initial states `rootInit t`, `rootInit t'`)
force equal tops: every top is a cv or block word of exactly one call. Tops 38 and 41 are call 0's
cv, 3..6 its block; 37 is call 1's first cv word, 0, 1, 2, 7 its block; 39, 40 call 7's cv, 8..11
its block; and tops `5r+2 … 5r+6` the cv and block of call `r = 2 … 6`. -/
theorem tops_eq_of_rootInputs (hP : P.Hyp) (t t' : Fin numChains → Word)
    (S S' : ℕ → BitVec 256) (h0 : S 0 = Params.rootInit t) (h0' : S' 0 = Params.rootInit t')
    (h : ∀ r < 8, P.rootInput t r (S r) = P.rootInput t' r (S' r)) : t = t' := by
  have hcb : ∀ r < 8, Params.rootCv t r (S r) = Params.rootCv t' r (S' r) ∧
      Params.rootBlock t r (S r) = Params.rootBlock t' r (S' r) := fun r hr =>
    cv_block_of_rootInput hP hr _ _ _ _ (h r hr)
  have htop : ∀ i, i < 42 → Params.topAt t i = Params.topAt t' i := by
    intro i hi
    by_cases h0i : i = 38 ∨ i = 41
    · have e := (hcb 0 (by norm_num)).1
      unfold Params.rootCv at e
      rw [if_pos rfl, if_pos rfl, h0, h0'] at e
      unfold Params.rootInit at e
      obtain ⟨e41, e38⟩ := append_inj e
      rcases h0i with rfl | rfl
      · exact e38
      · exact e41
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
    by_cases h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 7 ∨ i = 37
    · obtain ⟨ec, eb⟩ := hcb 1 (by norm_num)
      have h10 : ¬ (1 = 0) := by norm_num
      unfold Params.rootCv at ec
      rw [if_neg h10, if_pos rfl] at ec
      unfold Params.rootBlock at eb
      rw [if_neg h10, if_pos rfl] at eb
      obtain ⟨-, c37⟩ := append_inj ec
      obtain ⟨b1, b0⟩ := append_inj eb
      obtain ⟨b2, b3⟩ := append_inj b1
      obtain ⟨b5, b4⟩ := append_inj b2
      rcases h1 with rfl | rfl | rfl | rfl | rfl
      · exact b0
      · exact b3
      · exact b4
      · exact b5
      · exact c37
    by_cases h7 : (8 ≤ i ∧ i ≤ 11) ∨ i = 39 ∨ i = 40
    · obtain ⟨ec, eb⟩ := hcb 7 (by norm_num)
      have h70 : ¬ (7 = 0) := by norm_num
      have h71 : ¬ (7 = 1) := by norm_num
      have h77 : ¬ (7 < 7) := by norm_num
      unfold Params.rootCv Params.rootCvTop at ec
      rw [if_neg h70, if_neg h71, if_pos rfl] at ec
      unfold Params.rootBlock at eb
      rw [if_neg h70, if_neg h71, if_neg h77] at eb
      obtain ⟨c40, c39⟩ := append_inj ec
      obtain ⟨b1, b8⟩ := append_inj eb
      obtain ⟨b2, b9⟩ := append_inj b1
      obtain ⟨b11, b10⟩ := append_inj b2
      rcases h7 with h8 | rfl | rfl
      · rcases (by omega : i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11) with rfl | rfl | rfl | rfl
        · exact b8
        · exact b9
        · exact b10
        · exact b11
      · exact c39
      · exact c40
    · set r := (i - 2) / 5 with hr
      have hr0 : ¬ r = 0 := by omega
      have hr1 : ¬ r = 1 := by omega
      have hr7 : ¬ r = 7 := by omega
      have hr7' : r < 7 := by omega
      obtain ⟨ec, eb⟩ := hcb r (by omega)
      unfold Params.rootCv Params.rootCvTop at ec
      simp only [hr0, hr1, hr7, ↓reduceIte] at ec
      unfold Params.rootBlock at eb
      simp only [hr0, hr1, hr7', ↓reduceIte] at eb
      obtain ⟨c2, c1⟩ := append_inj ec
      obtain ⟨b1, -⟩ := append_inj eb
      obtain ⟨b2, b3⟩ := append_inj b1
      obtain ⟨b5, b4⟩ := append_inj b2
      rcases (by omega : i = 5 * r + 2 ∨ i = 5 * r + 2 + 1 ∨ i = 5 * r + 4 ∨ i = 5 * r + 5 ∨
          i = 5 * r + 6) with e | e | e | e | e <;> rw [e]
      · exact c1
      · exact c2
      · exact b3
      · exact b4
      · exact b5
  funext k
  have := htop k.val k.isLt
  unfold Params.topAt at this
  rwa [dif_pos k.isLt, dif_pos k.isLt] at this

/-- Equal inputs at a root call `r ≥ 1` read the low half of the state before it: call 1 carries
it in its cv, calls `2, …, 6` in the block, call 7 as its metadata. -/
theorem lo_eq_of_rootInput (hP : P.Hyp) {r : ℕ} (hr : r < 8) (h1 : 1 ≤ r)
    (t t' : Fin numChains → Word) (st st' : BitVec 256)
    (h : P.rootInput t r st = P.rootInput t' r st') :
    st.extractLsb' 0 128 = st'.extractLsb' 0 128 := by
  by_cases h7 : r < 7
  · obtain ⟨-, ec, eb⟩ := (Params.rootInput_eq_iff hP h7 h7 _ _ _ _).mp h
    have hr0 : ¬ r = 0 := by omega
    by_cases hr1 : r = 1
    · unfold Params.rootCv at ec
      rw [if_neg hr0, if_pos hr1, if_neg hr0, if_pos hr1] at ec
      exact (append_inj ec).1
    · unfold Params.rootBlock at eb
      rw [if_neg hr0, if_neg hr1, if_pos h7, if_neg hr0, if_neg hr1, if_pos h7] at eb
      exact (append_inj eb).2
  · obtain rfl : r = 7 := by omega
    exact ((Params.rootInput_seven_iff _ _ _ _).mp h).2.2

/-- The honest root states are reproduced by any table that respects the (always exposed) root
answers. -/
theorem rootFromValue_honest (f : HashTable) (d : Cut) (ζ : Record P)
    (hf : RespectsExposed f d ζ) :
    ∀ r, r ≤ 8 → P.rootFromValue f ζ.top 0 r (Params.rootInit ζ.top) = ζ.rootState r := by
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
  rw [rootFromValue_honest f d ζ hf 8 le_rfl, Record.rootState_succ_lt _ 7 (by norm_num)]
  rfl

/-- **Root binding.** A cached root path of the verifier that reaches the public key of a
separated record has the honest tops, or some call on it hits a target. -/
theorem root_binding (hP : P.Hyp) (d : Cut) (ζ : Record P) (hζ : ζ.Sep) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (t : Fin numChains → Word)
    (hpath : P.RootPath c t 0 8 (Params.rootInit t))
    (hroot : P.rootValue (table c) t = ζ.pk)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) : t = ζ.top := by
  have hf := respectsExposed_of_sub hP d ζ hζ hc
  set S : ℕ → BitVec 256 := fun r => P.rootFromValue (table c) t 0 r (Params.rootInit t) with hS
  have hhon := rootFromValue_honest (table c) d ζ hf
  have hcached : ∀ r < 8, ∃ u, c ⟨896, P.rootInput t r (S r)⟩ = some u ∧ S (r + 1) = u := by
    intro r hr
    have h := hpath r hr
    rw [Nat.zero_add] at h
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h
    refine ⟨u, hu, ?_⟩
    show P.rootFromValue (table c) t 0 (r + 1) (Params.rootInit t) = u
    rw [Params.rootFromValue_snoc, Nat.zero_add]
    exact table_eq_of_some hu
  have hloc : ∀ (r : ℕ) (hr : r < 7),
      queryLocation P ⟨896, P.rootInput t r (S r)⟩ = some (.inr ⟨r, by omega⟩) := by
    intro r hr
    exact queryLocation_rootInput hP ⟨r, by omega⟩ hr t (S r) (fun h0 => by
      simp only at h0
      subst h0
      rfl)
  -- a constant-tag call: a mismatching input with a matching low half is a target hit
  have step : ∀ r (hr : r < 7),
      (S (r + 1)).extractLsb' 0 128 = (ζ.rootState (r + 1)).extractLsb' 0 128 →
      P.rootInput t r (S r) = P.rootInput ζ.top r (ζ.rootState r) := by
    intro r hr hm
    by_contra hX
    apply hno
    obtain ⟨u, hu, hSu⟩ := hcached r (by omega)
    refine ⟨⟨896, P.rootInput t r (S r)⟩, u, hu, ?_⟩
    have hne : ζ.query (.inr ⟨r, by omega⟩) ≠ ⟨896, P.rootInput t r (S r)⟩ := by
      intro h
      rw [Record.query_inr] at h
      exact hX (query_inj h).symm
    refine mem_cutTargets_exposed (hloc r hr) (not_hidden_inr d _) hne ?_
    rw [matchingAnswers_inr, ← Record.rootState_succ_lt _ r (by omega), ← hSu]
    exact mem_lowAnswers.mpr hm
  -- the last call: the public-key target, or the index target at call 6
  have step7 : P.rootInput t 7 (S 7) = P.rootInput ζ.top 7 (ζ.rootState 7) := by
    by_contra hX
    apply hno
    obtain ⟨u, hu, hSu⟩ := hcached 7 (by norm_num)
    by_cases hidx : (S 7).extractLsb' 0 128 = P.idxMd
    · obtain ⟨v, hv, hSv⟩ := hcached 6 (by norm_num)
      refine ⟨⟨896, P.rootInput t 6 (S 6)⟩, v, hv, mem_cutTargets_extra ?_⟩
      refine mem_extraTargets_idx (hloc 6 (by norm_num)) ?_
      rw [← hSv]
      exact hidx
    · refine ⟨⟨896, P.rootInput t 7 (S 7)⟩, u, hu, mem_cutTargets_extra ?_⟩
      refine mem_extraTargets_pk ⟨rfl, ?_, ?_⟩ ?_
      · rintro ⟨m, η, pk, he⟩
        exact Params.rootInput_seven_ne_idxInput _ _ hidx m η pk (query_inj he)
      · intro h
        rw [Record.query_inr] at h
        exact hX (query_inj h)
      · rw [← hSu]
        exact hroot
  -- walk down from the last call
  have key : ∀ n, n ≤ 8 → ∀ s, 8 - n ≤ s → s < 8 →
      P.rootInput t s (S s) = P.rootInput ζ.top s (ζ.rootState s) := by
    intro n
    induction n with
    | zero => intro _ s hs hs'; omega
    | succ n ih =>
      intro hn s hs hs'
      by_cases hs0 : s = 7 - n
      · by_cases h0 : n = 0
        · subst h0
          rw [hs0]
          exact step7
        · have hm : (S (7 - n + 1)).extractLsb' 0 128 =
              (ζ.rootState (7 - n + 1)).extractLsb' 0 128 :=
            lo_eq_of_rootInput hP (by omega) (by omega) _ _ _ _
              (ih (by omega) (7 - n + 1) (by omega) (by omega))
          rw [hs0]
          exact step (7 - n) (by omega) hm
      · exact ih (by omega) s (by omega) hs'
  exact tops_eq_of_rootInputs hP t ζ.top S ζ.rootState rfl rfl
    (fun r hr => key 8 le_rfl r (by omega) hr)

/-! ## The events lemma -/

/-- The deterministic core: an accepted pair in a cache holding the exposed points of `ζ` and
missing every hidden point and cut target of `ζ` has no chain starting below the cut, and the
chains starting at the cut start at the honest words. -/
theorem accept_core (hP : P.Hyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P) (hζ : ζ.Sep)
    (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (pk : PublicKey) (hpk : ζ.pk = pk)
    (m₂ : Message) (σ₂ : List Bool) (hacc : P.Accepts c pk m₂ σ₂)
    (hh : ¬ Cache.Hits c (hiddenCache d ζ)) (ht : ¬ TargetHit (cutTargets P d ζ) c) :
    (∀ k, d k ≤ P.len k - 1 - P.digit (P.idxValue (table c) m₂ (decodeNonce σ₂) pk) k) ∧
    (∀ k, P.len k - 1 - P.digit (P.idxValue (table c) m₂ (decodeNonce σ₂) pk) k = d k →
      decodeWord σ₂ k = ζ.word k (d k)) := by
  set I₂ := P.idxValue (table c) m₂ (decodeNonce σ₂) pk with hI₂
  have hrec : P.reconWords (table c) I₂ σ₂ = ζ.top :=
    root_binding hP d ζ hζ c hc _ hacc.rootPath (hacc.root.trans hpk.symm) ht
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
    rcases lower_chain hP d hd ζ hζ c hc k _ (by omega) _ (hchain k).2 (hchain k).1 with h | h
    · exact hh h
    · exact ht h
  · have hdk := hd k
    rcases upper_chain hP d ζ hζ c hc k _ (by omega) (Nat.sub_le _ _) _ (hchain k).2
        (hchain k).1 with h | h
    · rw [h, hk]
    · exact absurd h ht

theorem digits_eq_of_le (hP : P.Hyp) {I J : Index} (hI : P.Accepted I) (hJ : P.Accepted J)
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
    (hζ : ζ.Sep) (c : Cache) (I₁ : Index) (hI₁ : P.Accepted I₁) (η₁ : Nonce)
    (hc : Cache.Sub (exposedCache (afterSigning P I₁) ζ) c) (hpk : ζ.pk = pk)
    (p : Bool × Cache)
    (hp : p ∈ support (run (P.stB A pk m₁ st
      (some (encode (fun k => ζ.word k (afterSigning P I₁ k)) η₁))) c))
    (hok : p.1 = true) :
    Cache.Hits p.2 (hiddenCache (afterSigning P I₁) ζ) ∨
      TargetHit (cutTargets P (afterSigning P I₁) ζ) p.2 ∨
      ∃ (m₂ : Message) (η₂ : Nonce), (m₂, η₂) ≠ (m₁, η₁) ∧
        ∃ w, p.2 ⟨896, P.idxInput m₂ η₂ pk⟩ = some w ∧ indexSlice w = I₁ := by
  obtain ⟨hcp, h⟩ := P.stB_support A pk m₁ st _ c p hp
  obtain ⟨m₂, σ₂, hne, hacc⟩ := h hok
  have hsub := hc.trans hcp
  by_cases hh : Cache.Hits p.2 (hiddenCache (afterSigning P I₁) ζ)
  · exact Or.inl hh
  by_cases ht : TargetHit (cutTargets P (afterSigning P I₁) ζ) p.2
  · exact Or.inr (Or.inl ht)
  right; right
  obtain ⟨h1, h2⟩ := accept_core hP _ (afterSigning_valid I₁) ζ hζ p.2 hsub pk hpk m₂ σ₂ hacc hh ht
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
    exact congrArg indexSlice (table_eq_of_some hw).symm

/-- **Forgery events after a signing failure.** Every accepted pair yields a hidden hit or a
cut-target hit at the cut before signing. -/
theorem events_none (hP : P.Hyp) (pk : PublicKey) (m₁ : Message) (st : A.State) (ζ : Record P)
    (hζ : ζ.Sep) (c : Cache) (hc : Cache.Sub (exposedCache (beforeSigning P) ζ) c) (hpk : ζ.pk = pk)
    (p : Bool × Cache) (hp : p ∈ support (run (P.stB A pk m₁ st none) c))
    (hok : p.1 = true) :
    Cache.Hits p.2 (hiddenCache (beforeSigning P) ζ) ∨
      TargetHit (cutTargets P (beforeSigning P) ζ) p.2 := by
  obtain ⟨hcp, h⟩ := P.stB_support A pk m₁ st _ c p hp
  obtain ⟨m₂, σ₂, -, hacc⟩ := h hok
  have hsub := hc.trans hcp
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨h1, -⟩ := accept_core hP _ beforeSigning_valid ζ hζ p.2 hsub pk hpk m₂ σ₂ hacc hno.1 hno.2
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
