import Submissions.UpperLeanIsa.FusionTranscript
import Submissions.UpperLeanIsa.FusionActive

/-! Deterministic extraction of the forgery events for dependency-aware chains. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
variable {P : Params}

/-- The table respects `ζ` at every location exposed at cut `d`. -/
def RespectsExposed (f : HashTable) (d : Cut) (ζ : Record P) : Prop :=
  ∀ a, ¬ Hidden d a → f (ζ.query a) = ζ.2 a

theorem respectsExposed_of_sub (hP : P.SecurityHyp) (d : Cut) (ζ : Record P) {c : Cache}
    (h : Cache.Sub (exposedCache d ζ) c) : RespectsExposed (table c) d ζ := by
  intro a ha
  have h1 : exposedCache d ζ (ζ.query a) = some (ζ.2 a) :=
    (exposedCache_some_iff hP d ζ _ _).2 ⟨a, ha, rfl, rfl⟩
  exact table_eq_of_some (h _ _ h1)

theorem chainValue_exposed (f : HashTable) (d : Cut) (ζ : Record P)
    (hf : RespectsExposed f d ζ) (k : Fin numChains) :
    ∀ (n j : ℕ), d k ≤ j → j + n ≤ P.codec.len k - 1 →
      P.chainValue f ζ.tops k j n (ζ.word k j) = ζ.word k (j + n) := by
  intro n
  induction n with
  | zero => intro j _ _; rfl
  | succ n ih =>
    intro j hj hjn
    have hl : j < P.codec.len k - 1 := by omega
    rw [Params.chainValue_succ]
    have hq : f ⟨896, P.chainInput ζ.tops k j (ζ.word k j)⟩ = ζ.2 (.inl ⟨k, ⟨j, hl⟩⟩) :=
      hf (.inl ⟨k, ⟨j, hl⟩⟩) (by show ¬ j < d k; omega)
    have hw : P.stepValue f ζ.tops k j (ζ.word k j) = ζ.word k (j + 1) := by
      unfold Params.stepValue
      rw [hq, Record.word_succ _ k j hl]
    rw [hw, ih (j + 1) (by omega) (by omega), show j + 1 + n = j + (n + 1) by omega]

/-- If two continuations merge, either they began at the same word or there is a step whose
inputs differ and whose outputs agree. -/
theorem chain_merge (f : HashTable) (t : Tops) (k : Fin numChains) :
    ∀ (n j : ℕ) (x y : Word), P.chainValue f t k j n x = P.chainValue f t k j n y →
      x = y ∨ ∃ i, i < n ∧ P.chainValue f t k j i x ≠ P.chainValue f t k j i y ∧
        P.stepValue f t k (j + i) (P.chainValue f t k j i x) =
          P.stepValue f t k (j + i) (P.chainValue f t k j i y) := by
  intro n
  induction n with
  | zero => intro j x y h; exact Or.inl h
  | succ n ih =>
    intro j x y h
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      rcases ih (j + 1) (P.stepValue f t k j x) (P.stepValue f t k j y) h with
        heq | ⟨i, hi, hne, heq⟩
      · exact ⟨0, by omega, hxy, heq⟩
      · refine ⟨i + 1, by omega, hne, ?_⟩
        rw [Params.chainValue_succ, Params.chainValue_succ, show j + (i + 1) = j + 1 + i by omega]
        exact heq

/-- Reaching the honest top from a word at an exposed position: the honest word, or a second
preimage of an honest step at or after that position. -/
theorem endpoint_match_exposed (f : HashTable) (d : Cut) (ζ : Record P)
    (hf : RespectsExposed f d ζ) (k : Fin numChains) (j : ℕ) (hj : d k ≤ j)
    (hj' : j ≤ P.codec.len k - 1) (x : Word)
    (h : P.chainValue f ζ.tops k j (P.codec.len k - 1 - j) x = ζ.top k) :
    x = ζ.word k j ∨ ∃ i, j ≤ i ∧ i < P.codec.len k - 1 ∧
      P.chainValue f ζ.tops k j (i - j) x ≠ ζ.word k i ∧
      P.stepValue f ζ.tops k i (P.chainValue f ζ.tops k j (i - j) x) = P.stepValue f ζ.tops k i (ζ.word k i) := by
  have hhon : P.chainValue f ζ.tops k j (P.codec.len k - 1 - j) (ζ.word k j) = ζ.top k := by
    rw [chainValue_exposed f d ζ hf k _ j hj (by omega)]
    unfold Record.top
    congr 1
    omega
  rcases chain_merge f ζ.tops k _ j x (ζ.word k j) (h.trans hhon.symm) with heq | ⟨i, hi, hne, hstep⟩
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

/-! ## Chain events -/

/-- A chain second preimage at an exposed step, on a cached verifier step, is a cut-target hit. -/
theorem chain_spi_targetHit (hP : P.SecurityHyp) (d : Cut) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (i : ℕ)
    (hi : i < P.codec.len k - 1) (hexp : d k ≤ i) (y : Word) (hy : y ≠ ζ.word k i)
    (hcached : (c ⟨896, P.chainInput ζ.tops k i y⟩).isSome)
    (hmatch : P.stepValue (table c) ζ.tops k i y = P.stepValue (table c) ζ.tops k i (ζ.word k i)) :
    TargetHit (cutTargets P d ζ) c := by
  have hf := respectsExposed_of_sub hP d ζ hc
  have hnh : ¬ Hidden d (.inl ⟨k, ⟨i, hi⟩⟩) := by
    show ¬ i < d k
    omega
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcached
  refine ⟨⟨896, P.chainInput ζ.tops k i y⟩, u, hu, ?_⟩
  have hne : ζ.query (.inl ⟨k, ⟨i, hi⟩⟩) ≠ ⟨896, P.chainInput ζ.tops k i y⟩ := by
    intro h
    rw [Record.query_inl] at h
    exact hy (Params.chainInput_current ζ.tops ζ.tops _ _ (query_inj h)).symm
  have h1 : P.stepValue (table c) ζ.tops k i y = P.codec.slice k i u :=
    congrArg (P.codec.slice k i) (table_eq_of_some hu)
  have h2 : P.stepValue (table c) ζ.tops k i (ζ.word k i) = P.codec.slice k i (ζ.2 (.inl ⟨k, ⟨i, hi⟩⟩)) :=
    congrArg (P.codec.slice k i) (hf (.inl ⟨k, ⟨i, hi⟩⟩) hnh)
  refine mem_cutTargets_exposed (queryLocation_chainInput hP ζ.tops k ⟨i, hi⟩ y) hnh hne ?_
  rw [matchingAnswers_inl]
  exact mem_sliceAnswers.mpr (h1.symm.trans (hmatch.trans h2))

/-- A cached verifier step just below the cut whose output is the public word at the cut: the
honest hidden input was queried, or the boundary target was hit. -/
theorem boundary_hit (hP : P.SecurityHyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (hpos : 0 < d k)
    (y : Word) (hcached : (c ⟨896, P.chainInput ζ.tops k (d k - 1) y⟩).isSome)
    (hmatch : P.stepValue (table c) ζ.tops k (d k - 1) y = ζ.word k (d k)) :
    Cache.Hits c (hiddenCache d ζ) ∨ TargetHit (cutTargets P d ζ) c := by
  have hdk := hd k
  have he : d k - 1 < P.codec.len k - 1 := by omega
  have hhid : Hidden d (.inl ⟨k, ⟨d k - 1, he⟩⟩) := by
    show d k - 1 < d k
    omega
  by_cases hy : y = ζ.word k (d k - 1)
  · left
    refine ⟨⟨896, P.chainInput ζ.tops k (d k - 1) y⟩, ?_, hcached⟩
    refine (hiddenCache_isSome_iff hP d ζ _).2 ⟨.inl ⟨k, ⟨d k - 1, he⟩⟩, hhid, ?_⟩
    rw [Record.query_inl, hy]
  · right
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hcached
    refine ⟨⟨896, P.chainInput ζ.tops k (d k - 1) y⟩, u, hu, ?_⟩
    have hbd : Boundary d (.inl ⟨k, ⟨d k - 1, he⟩⟩) := by
      show d k - 1 + 1 = d k
      omega
    have h1 : P.stepValue (table c) ζ.tops k (d k - 1) y = P.codec.slice k (d k - 1) u :=
      congrArg (P.codec.slice k (d k - 1)) (table_eq_of_some hu)
    have h2 : ζ.word k (d k) = P.codec.slice k (d k - 1) (ζ.2 (.inl ⟨k, ⟨d k - 1, he⟩⟩)) := by
      rw [← Record.word_succ _ k (d k - 1) he, Nat.sub_add_cancel hpos]
    refine mem_cutTargets_boundary (queryLocation_chainInput hP ζ.tops k ⟨d k - 1, he⟩ y) hhid hbd ?_
    rw [matchingAnswers_inl]
    exact mem_sliceAnswers.mpr (h1.symm.trans (hmatch.trans h2))

/-- A chain that starts strictly below the cut and reaches the honest top passes the boundary
(hidden or boundary hit) or merges later (exposed chain target). -/
theorem lower_chain (hP : P.SecurityHyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (e : ℕ) (he : e < d k)
    (y : Word) (hpath : P.ChainPath c ζ.tops k e (P.codec.len k - 1 - e) y)
    (hend : P.chainValue (table c) ζ.tops k e (P.codec.len k - 1 - e) y = ζ.top k) :
    Cache.Hits c (hiddenCache d ζ) ∨ TargetHit (cutTargets P d ζ) c := by
  have hdk := hd k
  have hf := respectsExposed_of_sub hP d ζ hc
  have hmid : P.chainValue (table c) ζ.tops k (d k) (P.codec.len k - 1 - d k)
      (P.chainValue (table c) ζ.tops k e (d k - e) y) = ζ.top k := by
    have h := P.chainValue_add (table c) ζ.tops k e (d k - e) (P.codec.len k - 1 - d k) y
    rw [show e + (d k - e) = d k by omega,
      show d k - e + (P.codec.len k - 1 - d k) = P.codec.len k - 1 - e by omega] at h
    exact h.trans hend
  rcases endpoint_match_exposed (table c) d ζ hf k (d k) le_rfl hdk _ hmid with
    heq | ⟨i, hji, hi, hne, hstep⟩
  · have hpos : 0 < d k := by omega
    have hcached' : (c ⟨896, P.chainInput ζ.tops k (d k - 1)
        (P.chainValue (table c) ζ.tops k e (d k - 1 - e) y)⟩).isSome :=
      Params.ChainPath.cached P hpath (by omega) (by omega)
    have hmatch' : P.stepValue (table c) ζ.tops k (d k - 1)
        (P.chainValue (table c) ζ.tops k e (d k - 1 - e) y) = ζ.word k (d k) := by
      have h := P.chainValue_snoc (table c) ζ.tops k e (d k - 1 - e) y
      rw [show d k - 1 - e + 1 = d k - e by omega,
        show e + (d k - 1 - e) = d k - 1 by omega] at h
      exact h.symm.trans heq
    exact boundary_hit hP d hd ζ c hc k hpos _ hcached' hmatch'
  · right
    have hY : P.chainValue (table c) ζ.tops k (d k) (i - d k)
        (P.chainValue (table c) ζ.tops k e (d k - e) y) = P.chainValue (table c) ζ.tops k e (i - e) y := by
      have h := P.chainValue_add (table c) ζ.tops k e (d k - e) (i - d k) y
      rw [show e + (d k - e) = d k by omega,
        show d k - e + (i - d k) = i - e by omega] at h
      exact h
    have hcached := Params.ChainPath.cached P hpath (i := i) (by omega) (by omega)
    rw [← hY] at hcached
    exact chain_spi_targetHit hP d ζ c hc k i hi hji _ hne hcached hstep

/-- A chain that starts at or above the cut and reaches the honest top starts at the honest
word, or hits an exposed chain target. -/
theorem upper_chain (hP : P.SecurityHyp) (d : Cut) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (k : Fin numChains) (e : ℕ) (he : d k ≤ e)
    (he' : e ≤ P.codec.len k - 1) (y : Word) (hpath : P.ChainPath c ζ.tops k e (P.codec.len k - 1 - e) y)
    (hend : P.chainValue (table c) ζ.tops k e (P.codec.len k - 1 - e) y = ζ.top k) :
    y = ζ.word k e ∨ TargetHit (cutTargets P d ζ) c := by
  have hf := respectsExposed_of_sub hP d ζ hc
  rcases endpoint_match_exposed (table c) d ζ hf k e he he' y hend with
    heq | ⟨i, hji, hi, hne, hstep⟩
  · exact Or.inl heq
  · right
    have hcached := Params.ChainPath.cached P hpath (i := i) hji (by omega)
    exact chain_spi_targetHit hP d ζ c hc k i hi (by omega) _ hne hcached hstep


namespace Params
variable (P : Params)

def rootStates (f : HashTable) (t : Tops) (n : ℕ) : BitVec 256 :=
  P.rootFromValue f t ([0,1,2].take n) 0

theorem cached_table {c : Cache} {q : Query} (h : (c q).isSome) : c q = some (table c q) := by
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp h
  rw [table_eq_of_some hv]
  exact hv

theorem rootPath_cached (c : Cache) (t : Tops) (hp : P.RootPath c t [0,1,2] 0) :
    ∀ r : Fin 3, c ⟨896,P.rootInput t r (P.rootStates (table c) t r.val)⟩ =
      some (P.rootStates (table c) t (r.val+1)) := by
  obtain ⟨h0,h1,h2,-⟩ := hp
  intro r
  fin_cases r
  · exact cached_table h0
  · exact cached_table h1
  · exact cached_table h2

theorem accepts_chains {c : Cache} {pk : PublicKey} {m : Message} {bits : List Bool}
    (ha : P.Accepts c pk m bits) (k : Fin 42) :
    let I := P.codec.idxValue (table c) m (decodeNonce bits) pk
    let t := P.reconWords (table c) I bits
    P.ChainPath c t k (P.codec.len k - 1 - P.codec.digit I k) (P.codec.digit I k) (decodeWord bits k) ∧
      P.chainValue (table c) t k (P.codec.len k - 1 - P.codec.digit I k)
        (P.codec.digit I k) (decodeWord bits k) = t k.val :=
  P.reconFrom_normalized c _ bits chainOrder chainOrder_ranked _ ha.reconstruction k
    (chainOrder_permutation.mem_iff.mpr (List.mem_finRange k))

theorem reconWords_zero_ge (f : HashTable) (I : Index) (bits : List Bool) (n : ℕ) (hn : ¬ n < 42) :
    P.reconWords f I bits n = 0 := by
  apply P.reconFromValue_preserves f I bits chainOrder (fun _ => 0) n
  rintro hmem
  obtain ⟨k,-,he⟩ := List.mem_map.mp hmem
  exact hn (he ▸ k.isLt)

theorem accepts_final (hP : P.Hyp) {c : Cache} {pk : PublicKey} {m : Message} {bits : List Bool}
    (ha : P.Accepts c pk m bits) (k : Fin 42)
    (hpos : 0 < P.codec.digit (P.codec.idxValue (table c) m (decodeNonce bits) pk) k) :
    let I := P.codec.idxValue (table c) m (decodeNonce bits) pk
    let t := P.reconWords (table c) I bits
    ∃ x v, c ⟨896,P.chainInput t k (P.codec.len k - 2) x⟩ = some v ∧
      P.codec.slice k (P.codec.len k - 2) v = t k.val := by
  intro I t
  change 0 < P.codec.digit I k at hpos
  obtain ⟨hpath,hval⟩ := P.accepts_chains ha k
  have hd := hP.codec.digit_lt I k
  let j := P.codec.len k - 1 - P.codec.digit I k
  have hj : j ≤ P.codec.len k - 2 := by dsimp only [j]; omega
  have hjn : P.codec.len k - 2 < j + P.codec.digit I k := by dsimp only [j]; omega
  have hc := ChainPath.cached P hpath hj hjn
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hc
  refine ⟨P.chainValue (table c) t k j (P.codec.len k - 2 - j) (decodeWord bits k),v,hv,?_⟩
  have hn : P.codec.len k - 2 - j + 1 = P.codec.digit I k := by dsimp only [j]; omega
  have hi : j + (P.codec.len k - 2 - j) = P.codec.len k - 2 := by omega
  have he := P.chainValue_snoc (table c) t k j (P.codec.len k - 2 - j) (decodeWord bits k)
  rw [hn,hi,stepValue,table_eq_of_some hv] at he
  exact he.symm.trans hval

/-- Every accepted cached reconstruction has honest tops unless it hits a cut target. -/
theorem accepts_tops (hP : P.SecurityHyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P)
    (c : Cache) (m : Message) (bits : List Bool) (ha : P.Accepts c ζ.pk m bits)
    (hno : ¬ TargetHit (cutTargets P d ζ) c) :
    P.reconWords (table c) (P.codec.idxValue (table c) m (decodeNonce bits) ζ.pk) bits = ζ.tops := by
  let I := P.codec.idxValue (table c) m (decodeNonce bits) ζ.pk
  let t := P.reconWords (table c) I bits
  have hbound := all_tops_bound hP d hd ζ c I t (P.rootStates (table c) t)
    (P.rootPath_cached c t ha.rootPath) ha.root (hP.binding I ha.accepted)
    (fun k hk => P.accepts_final hP ha k hk) hno
  funext n
  by_cases hn : n < 42
  · exact hbound n hn
  · rw [P.reconWords_zero_ge _ _ _ n hn]
    simp only [Record.tops,Layer.Params.topAt,dif_neg hn]

end Params

/-- Cached acceptance leaves every disclosed position at or above the signed cut. -/
theorem accept_core (hP : P.SecurityHyp) (d : Cut) (hd : ValidCut P d) (ζ : Record P) (c : Cache)
    (hc : Cache.Sub (exposedCache d ζ) c) (pk : PublicKey) (hpk : ζ.pk = pk)
    (m₂ : Message) (σ₂ : List Bool) (hacc : P.Accepts c pk m₂ σ₂)
    (hh : ¬ Cache.Hits c (hiddenCache d ζ)) (ht : ¬ TargetHit (cutTargets P d ζ) c) :
    (∀ k, d k ≤ P.codec.len k - 1 - P.codec.digit (P.codec.idxValue (table c) m₂ (decodeNonce σ₂) pk) k) ∧
    (∀ k, P.codec.len k - 1 - P.codec.digit (P.codec.idxValue (table c) m₂ (decodeNonce σ₂) pk) k = d k →
      decodeWord σ₂ k = ζ.word k (d k)) := by
  subst pk
  set I₂ := P.codec.idxValue (table c) m₂ (decodeNonce σ₂) ζ.pk with hI₂
  have hrec : P.reconWords (table c) I₂ σ₂ = ζ.tops := P.accepts_tops hP d hd ζ c m₂ σ₂ hacc ht
  have hchain : ∀ k, P.chainValue (table c) ζ.tops k (P.codec.len k - 1 - P.codec.digit I₂ k)
      (P.codec.len k - 1 - (P.codec.len k - 1 - P.codec.digit I₂ k)) (decodeWord σ₂ k) = ζ.top k ∧
      P.ChainPath c ζ.tops k (P.codec.len k - 1 - P.codec.digit I₂ k)
        (P.codec.len k - 1 - (P.codec.len k - 1 - P.codec.digit I₂ k)) (decodeWord σ₂ k) := by
    intro k
    have hdl := hP.codec.digit_lt I₂ k
    have hn : P.codec.len k - 1 - (P.codec.len k - 1 - P.codec.digit I₂ k) = P.codec.digit I₂ k := by omega
    rw [hn]
    obtain ⟨hp,hv⟩ := P.accepts_chains hacc k
    change P.ChainPath c (P.reconWords (table c) I₂ σ₂) k _ _ _ at hp
    change P.chainValue (table c) (P.reconWords (table c) I₂ σ₂) k _ _ _ =
      P.reconWords (table c) I₂ σ₂ k.val at hv
    rw [hrec] at hp hv
    have hk : ζ.tops k.val = ζ.top k := by simp only [Record.tops,Layer.Params.topAt,dif_pos k.isLt]
    exact ⟨hv.trans hk,hp⟩
  refine ⟨fun k => ?_,fun k hk => ?_⟩
  · by_contra hlt
    rcases lower_chain hP d hd ζ c hc k _ (by omega) _ (hchain k).2 (hchain k).1 with h | h
    · exact hh h
    · exact ht h
  · rcases upper_chain hP d ζ c hc k _ (by omega) (Nat.sub_le _ _) _ (hchain k).2
      (hchain k).1 with h | h
    · rw [h,hk]
    · exact absurd h ht

theorem digits_eq_of_le {I J : Index} (hI : P.codec.Accepted I) (hJ : P.codec.Accepted J)
    (h : ∀ k, P.codec.digit J k ≤ P.codec.digit I k) : P.codec.digit J = P.codec.digit I := by
  have hs : ∑ k, P.codec.digit J k = ∑ k, P.codec.digit I k := by
    have h1 : ∑ k, P.codec.digit J k = P.codec.layer := hJ
    have h2 : ∑ k, P.codec.digit I k = P.codec.layer := hI
    rw [h1, h2]
  funext k
  exact (Finset.sum_eq_sum_iff_of_le (fun k _ => h k)).mp hs k (Finset.mem_univ k)

variable (A : OracleAlgorithm.Adversary)

/-- **Forgery events after signing index `I₁`.** On the second-stage run from a cache holding the
points of `ζ` exposed by the signature, an accepted fresh pair yields a hidden hit, a cut-target
hit, or a different message or nonce whose cached index answer is accepted with the digits of
`I₁`. -/
theorem events_some (hP : P.SecurityHyp) (pk : PublicKey) (m₁ : Message) (st : A.State) (ζ : Record P)
    (c : Cache) (I₁ : Index) (hI₁ : P.codec.Accepted I₁) (η₁ : Nonce)
    (hc : Cache.Sub (exposedCache (afterSigning P I₁) ζ) c) (hpk : ζ.pk = pk)
    (p : Bool × Cache)
    (hp : p ∈ support (run (P.stB A pk m₁ st
      (some (encode (fun k => ζ.word k (afterSigning P I₁ k)) η₁))) c))
    (hok : p.1 = true) :
    Cache.Hits p.2 (hiddenCache (afterSigning P I₁) ζ) ∨
      TargetHit (cutTargets P (afterSigning P I₁) ζ) p.2 ∨
      ∃ (m₂ : Message) (η₂ : Nonce), (m₂, η₂) ≠ (m₁, η₁) ∧
        ∃ w, p.2 ⟨896, P.codec.idxInput m₂ η₂ pk⟩ = some w ∧ P.codec.Accepted (indexSlice w) ∧
          P.codec.digit (indexSlice w) = P.codec.digit I₁ := by
  obtain ⟨hcp, h⟩ := P.stB_support A pk m₁ st _ c p hp
  obtain ⟨m₂, σ₂, hne, hacc⟩ := h hok
  have hsub := hc.trans hcp
  by_cases hh : Cache.Hits p.2 (hiddenCache (afterSigning P I₁) ζ)
  · exact Or.inl hh
  by_cases ht : TargetHit (cutTargets P (afterSigning P I₁) ζ) p.2
  · exact Or.inr (Or.inl ht)
  right; right
  obtain ⟨h1, h2⟩ := accept_core hP _ (afterSigning_valid I₁) ζ p.2 hsub pk hpk m₂ σ₂ hacc hh ht
  set I₂ := P.codec.idxValue (table p.2) m₂ (decodeNonce σ₂) pk with hI₂
  have hle : ∀ k, P.codec.digit I₂ k ≤ P.codec.digit I₁ k := by
    intro k
    have := h1 k
    have hd1 := hP.codec.digit_lt I₁ k
    have hd2 := hP.codec.digit_lt I₂ k
    unfold afterSigning at this
    omega
  have hII : P.codec.digit I₂ = P.codec.digit I₁ := digits_eq_of_le hI₁ hacc.accepted hle
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
theorem events_none (hP : P.SecurityHyp) (pk : PublicKey) (m₁ : Message) (st : A.State) (ζ : Record P)
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
  set I₂ := P.codec.idxValue (table p.2) m₂ (decodeNonce σ₂) pk
  have hz : ∀ k, P.codec.digit I₂ k = 0 := by
    intro k
    have := h1 k
    have hd2 := hP.codec.digit_lt I₂ k
    unfold beforeSigning at this
    omega
  have hsum : ∑ k, P.codec.digit I₂ k = P.codec.layer := hacc.accepted
  simp only [hz, Finset.sum_const_zero] at hsum
  have := hP.codec.layer_pos
  omega

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
