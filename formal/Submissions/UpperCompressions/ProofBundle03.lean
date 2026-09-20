import Submissions.UpperCompressions.ProofBundle02
import OptimalOTS.Dag
import Submissions.UpperCompressions.ProofBundle00
import OptimalOTS.Model

/- Original module: Submissions.UpperCompressions.Deterministic; SHA256 35f21f2e4d77c9326a9023cf9d44e776177a86f424e62709315bc5ccb6ebb4d5. -/
section

/-! Verification never uses private randomness: every query of `Scheme.verify` is a hash query. -/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Deterministic

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable {α β : Type}

theorem of_pure (x : α) : Deterministic (pure x : OracleComp Spec α) := trivial

theorem bind {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    (h₁ : Deterministic oa) (h₂ : ∀ x, Deterministic (ob x)) :
    Deterministic (oa >>= ob) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using h₂ x
  | query_bind t mx ih =>
    unfold Deterministic at h₁ ⊢
    rw [isQueryBound_query_bind_iff] at h₁
    rw [bind_assoc, isQueryBound_query_bind_iff]
    exact ⟨h₁.1, fun u => ih u (h₁.2 u)⟩

theorem map {oa : OracleComp Spec α} (h : Deterministic oa) (f : α → β) :
    Deterministic (f <$> oa) :=
  (isQueryBound_map_iff oa f _ _ _).2 h

theorem hash {k : ℕ} (u : BitVec k) : Deterministic (OptimalOTS.hash u) := by
  unfold Deterministic OptimalOTS.hash
  rw [isQueryBound_query_iff]
  rfl

theorem foldlM {γ δ : Type} (f : γ → δ → OracleComp Spec γ)
    (hf : ∀ x a, Deterministic (f x a)) :
    ∀ (l : List δ) (init : γ), Deterministic (l.foldlM f init)
  | [], _ => Deterministic.of_pure _
  | a :: l, init => by
      rw [List.foldlM_cons]
      exact Deterministic.bind (hf init a) fun y => Deterministic.foldlM f hf l y

end Deterministic

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

theorem deterministic_evalNode (x : G.Assignment) (v : Fin G.size)
    (s : OracleComp Spec (BitVec (G.len v))) (hs : Deterministic s) :
    Deterministic (G.evalNode x v s) := by
  unfold Graph.evalNode
  cases G.kind v with
  | source => exact hs
  | det => exact Deterministic.of_pure _
  | hash p _ h => exact Deterministic.map (Deterministic.hash _) _

theorem deterministic_reconstruct (A : Finset (Fin G.size)) (given : G.Assignment) :
    Deterministic (G.reconstruct A given) := by
  unfold Graph.reconstruct
  refine Deterministic.foldlM _ (fun x v => ?_) (List.finRange G.size) (fun _ => 0)
  split_ifs
  · exact Deterministic.of_pure _
  · exact Deterministic.map (G.deterministic_evalNode x v _ (Deterministic.of_pure _)) _
  · exact Deterministic.of_pure _

end Dag.Graph

namespace Dag.Scheme

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (S : Scheme)

theorem deterministic_verify (pk : PublicKey) (m : Message) (σ : Signature) :
    Deterministic (S.verify pk m σ) := by
  unfold Scheme.verify index
  refine Deterministic.bind (Deterministic.map (Deterministic.hash _) _) fun i => ?_
  split_ifs
  · dsimp only
    split_ifs
    · exact Deterministic.bind (S.graph.deterministic_reconstruct _ _)
        fun _ => Deterministic.of_pure _
    · exact Deterministic.of_pure _
  · exact Deterministic.of_pure _

/-- The adapter's verifier is deterministic. -/
theorem verifyDeterministic : S.toAlgorithm.VerifyDeterministic :=
  fun pk m σ => S.deterministic_verify pk m σ

end Dag.Scheme

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.SignIdx; SHA256 e3cd0c80b5a6391056e43206be6fea83a12ba11463df78178d5df59bde27da07. -/
section

/-!
# The signing loop

`signIdx m` is the signing loop returning the selected nonce and index instead of the
signature; `Scheme.sign` is its image under encoding the revealed values.

The analysis of the loop, started from a cache `d`:

* `run_signIdx_extend`: cache entries of other lengths are irrelevant to the loop;
* `signIdx_support`: every new cache entry is an encoding entry at an input `m ++ η`; a new
  entry with a valid index is the one that ended the loop;
* the signing bound's vocabulary, used by the disjoint signing lemma of `SignRho.lean`:
  `IdxPre d u₁ i` (a pre-existing encoding entry `u ≠ u₁` has index `i`), `SignExt` (the
  entries added by a run with a given outcome), the valid indices `V d` of the cache, and the
  one-trial facts `signExt_none`, `signExt_cached`, `signExt_fresh`, `ind_le_V`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


/-! ## Lemmas shared with the lower-bound proof (copied: submissions may not import each other) -/

namespace Analysis

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

lemma setWidth_append_nonce (m : Message) (η : Nonce) :
    (m ++ η).setWidth nonceBits = η := by
  ext j hj
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_append, hj]

lemma sum_fin_equivFin {α : Type*} {s : Finset α} {n : ℕ} (h : n = s.card) (G : α → ℝ≥0∞) :
    ∑ j : Fin n, G (s.equivFin.symm (Fin.cast h j)).1 = ∑ η ∈ s, G η := by
  rw [← Finset.sum_coe_sort s]
  exact Equiv.sum_comp ((finCongr h).trans s.equivFin.symm) (fun x => G x.1)

/-- The index read from an oracle output. -/
def idxOfOut (y : BitVec hashBits) : ℕ := (y.setWidth idxBits).toNat

/-- Number of oracle outputs whose index lies in a set of index values. -/
theorem card_idxOfOut_mem (hidx : idxBits ≤ hashBits) (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < 2 ^ idxBits) :
    (Finset.univ.filter fun y : BitVec hashBits => idxOfOut y ∈ A).card =
      A.card * 2 ^ (hashBits - idxBits) := by
  have hH : 2 ^ hashBits = 2 ^ idxBits * 2 ^ (hashBits - idxBits) := by
    rw [← pow_add, Nat.add_sub_cancel' hidx]
  have hNpos : 0 < 2 ^ idxBits := by positivity
  rw [← Finset.card_range (2 ^ (hashBits - idxBits)), ← Finset.card_product]
  refine Finset.card_nbij' (fun y => (y.toNat % 2 ^ idxBits, y.toNat / 2 ^ idxBits))
    (fun x => BitVec.ofNat hashBits (x.1 + 2 ^ idxBits * x.2)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · simpa [idxOfOut, BitVec.toNat_setWidth] using hy
    · rw [Nat.div_lt_iff_lt_mul hNpos]
      have := y.isLt
      rw [hH] at this
      linarith
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    have h1 : x.1 + 2 ^ idxBits * x.2 < 2 ^ hashBits := by
      rw [hH]
      have := hA _ hx.1
      nlinarith
    simp only [idxOfOut, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hA _ hx.1)]
    exact hx.1
  · intro y _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_add_div, Nat.mod_eq_of_lt y.isLt]
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    have hx1 := hA _ hx.1
    have h1 : x.1 + 2 ^ idxBits * x.2 < 2 ^ hashBits := by
      rw [hH]
      nlinarith
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hx1, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hx1, zero_add]

end Analysis


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials


/-- An encoding input. -/
abbrev EncInput := BitVec (msgBits + nonceBits)

/-- The encoding query at input `u`: the query of length `msgBits + nonceBits` with bits `u`. The
oracle has no labels, so an encoding query is told apart from every other query by its length. -/
def encQuery (u : EncInput) : Query := ⟨msgBits + nonceBits, u⟩

/-- The index read from an oracle answer. -/
def idxOf (w : BitVec hashBits) : ℕ := (w.setWidth idxBits).toNat

/-- The signing loop, returning the nonce and the index. -/
def signIdxLoop (m : Message) :
    ℕ → Finset Nonce → OracleComp Spec (Option (Nonce × Fin numCuts))
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp Spec (Fin (fresh.card - 1 + 1)))
      let η : Nonce := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let i ← index m η
      if hi : i < numCuts then
        return some (η, ⟨i, hi⟩)
      else
        signIdxLoop m k (insert η tried)
    else
      pure none

/-- Signing, returning the nonce and the index. -/
def signIdx (m : Message) : OracleComp Spec (Option (Nonce × Fin numCuts)) :=
  signIdxLoop m trials ∅

/-! ### Basic facts on encoding inputs -/

theorem encQuery_inj {u u' : EncInput} (h : encQuery u = encQuery u') : u = u' := by
  simp only [encQuery, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  exact h

/-- A query of another length is not an encoding query. -/
theorem ne_encQuery_of_length_ne {q : Query} (hq : q.1 ≠ msgBits + nonceBits)
    (u : EncInput) : q ≠ encQuery u := by
  rintro rfl
  exact hq rfl

/-- The queries of encoding length are exactly the encoding queries. -/
theorem exists_eq_encQuery_of_length_eq {q : Query} (hq : q.1 = msgBits + nonceBits) :
    ∃ u : EncInput, q = encQuery u := by
  obtain ⟨k, v⟩ := q
  change k = msgBits + nonceBits at hq
  subst hq
  exact ⟨v, rfl⟩

theorem append_nonce_inj (m : Message) {η η' : Nonce} (h : m ++ η = m ++ η') : η = η' := by
  have := congrArg (fun u : EncInput => u.setWidth nonceBits) h
  simpa only [Analysis.setWidth_append_nonce] using this

/-! ### The loop in query normal form -/

theorem liftM_uniformFin_eq (n : ℕ) :
    (liftM ($[0..n]) : OracleComp Spec (Fin (n + 1))) =
      liftM (Spec.query (.inl n)) := by
  change liftComp ($[0..n]) Spec = _
  simp [liftComp, ProbComp.uniformFin]
  rfl

/-- The continuation of the loop after the encoding answer `w` at nonce `η`. -/
def afterHash (m : Message) (k : ℕ) (tried : Finset Nonce) (η : Nonce)
    (w : BitVec hashBits) : OracleComp Spec (Option (Nonce × Fin numCuts)) :=
  if hi : idxOf w < numCuts then pure (some (η, ⟨idxOf w, hi⟩))
  else signIdxLoop m k (insert η tried)

/-- The body of the loop at nonce `η`: one encoding query, then stop or recurse. -/
def loopBody (m : Message) (k : ℕ) (tried : Finset Nonce) (η : Nonce) :
    OracleComp Spec (Option (Nonce × Fin numCuts)) :=
  (liftM (Spec.query (.inr (encQuery (m ++ η)))) :
      OracleComp Spec (BitVec hashBits)) >>= afterHash m k tried η

/-- The nonce selected by the sample `j`. -/
def nonceOf (tried : Finset Nonce) (hc : 0 < (Finset.univ \ tried).card)
    (j : Fin ((Finset.univ \ tried).card - 1 + 1)) : Nonce :=
  ((Finset.univ \ tried).equivFin.symm (Fin.cast (by omega) j)).1

theorem nonceOf_mem (tried : Finset Nonce) (hc : 0 < (Finset.univ \ tried).card)
    (j : Fin ((Finset.univ \ tried).card - 1 + 1)) :
    nonceOf tried hc j ∈ Finset.univ \ tried :=
  ((Finset.univ \ tried).equivFin.symm (Fin.cast (by omega) j)).2

theorem signIdxLoop_succ (m : Message) (k : ℕ) (tried : Finset Nonce)
    (hc : 0 < (Finset.univ \ tried).card) :
    signIdxLoop m (k + 1) tried =
      (liftM (Spec.query (.inl ((Finset.univ \ tried).card - 1))) :
          OracleComp Spec (Fin ((Finset.univ \ tried).card - 1 + 1))) >>= fun j =>
        loopBody m k tried (nonceOf tried hc j) := by
  rw [signIdxLoop, dif_pos hc, liftM_uniformFin_eq]
  refine bind_congr fun j => ?_
  simp only [loopBody, nonceOf, index, hash, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  rfl

/-! ### One-step lemmas -/

theorem costAtMost_inl_bind {α β : Type} (t : ℕ)
    (body : Fin (t + 1) → OracleComp Spec α) (kont : α → OracleComp Spec β) {b : ℕ}
    (h : CostAtMost (((liftM (Spec.query (.inl t)) : OracleComp Spec (Fin (t + 1)))
      >>= body) >>= kont) b) :
    ∀ j, CostAtMost (body j >>= kont) b := by
  rw [bind_assoc, costAtMost_query_bind_iff] at h
  intro j
  have := h.2 j
  rwa [show queryCost (.inl t) = 0 from rfl, Nat.sub_zero] at this

theorem costAtMost_inr_bind {α β : Type} (q : Query)
    (body : BitVec hashBits → OracleComp Spec α) (kont : α → OracleComp Spec β)
    {b : ℕ}
    (h : CostAtMost (((liftM (Spec.query (.inr q)) : OracleComp Spec (BitVec hashBits))
      >>= body) >>= kont) b) :
    queryCost (.inr q) ≤ b ∧
      ∀ w, CostAtMost (body w >>= kont) (b - queryCost (.inr q)) := by
  rw [bind_assoc, costAtMost_query_bind_iff] at h
  exact h

theorem mem_support_run_inl {α : Type} {t : ℕ} {body : Fin (t + 1) → OracleComp Spec α}
    {c : Cache} {p : α × Cache}
    (hp : p ∈ support (run ((liftM (Spec.query (.inl t)) :
      OracleComp Spec (Fin (t + 1))) >>= body) c)) :
    ∃ j, p ∈ support (run (body j) c) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inl, support_bind] at hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨w, -, hw⟩ := hu
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨u, hp⟩

theorem mem_support_run_inr_none {α : Type} {q : Query}
    {body : BitVec hashBits → OracleComp Spec α} {c : Cache} {p : α × Cache}
    (hc : c q = none)
    (hp : p ∈ support (run ((liftM (Spec.query (.inr q)) :
      OracleComp Spec (BitVec hashBits)) >>= body) c)) :
    ∃ w, p ∈ support (run (body w) (c.cacheQuery q w)) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inr_none hc, support_bind] at hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨w, -, hw⟩ := hu
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨u, hp⟩

theorem mem_support_run_inr_some {α : Type} {q : Query} {u : BitVec hashBits}
    {body : BitVec hashBits → OracleComp Spec α} {c : Cache} {p : α × Cache}
    (hc : c q = some u)
    (hp : p ∈ support (run ((liftM (Spec.query (.inr q)) :
      OracleComp Spec (BitVec hashBits)) >>= body) c)) :
    p ∈ support (run (body u) c) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u', c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inr_some hc, support_pure] at hu
  simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  exact hp

/-! ### `Scheme.sign` as the image of `signIdx` -/

theorem signLoop_eq_map (S : Scheme) (x : S.graph.Assignment) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce),
      S.signLoop x m k tried =
        (Option.map fun r : Nonce × Fin numCuts => (r.1, S.graph.encode (S.sets r.2) x)) <$>
          signIdxLoop m k tried := by
  intro k
  induction k with
  | zero => intro tried; simp [Scheme.signLoop, signIdxLoop]
  | succ k ih =>
    intro tried
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [Scheme.signLoop, signIdxLoop, dif_pos hc, dif_pos hc]
      simp only [map_bind]
      refine bind_congr fun j => ?_
      refine bind_congr fun i => ?_
      split_ifs with hi
      · simp
      · exact ih _
    · rw [Scheme.signLoop, signIdxLoop, dif_neg hc, dif_neg hc]
      simp

/-- `Scheme.sign` encodes the revealed values of the index found by `signIdx`. -/
theorem sign_eq_map (S : Scheme) (x : S.graph.Assignment) (m : Message) :
    S.sign x m =
      (Option.map fun r : Nonce × Fin numCuts => (r.1, S.graph.encode (S.sets r.2) x)) <$>
        signIdx m :=
  signLoop_eq_map S x m trials ∅

/-! ### Non-encoding entries are irrelevant -/

theorem run_signIdxLoop_extend (m : Message) (f : Cache)
    (hf : ∀ u : EncInput, f (encQuery u) = none) :
    ∀ (k : ℕ) (tried : Finset Nonce) (d : Cache),
      run (signIdxLoop m k tried) (Cache.extend d f) =
        (fun p => (p.1, Cache.extend p.2 f)) <$> run (signIdxLoop m k tried) d := by
  intro k
  induction k with
  | zero => intro tried d; simp [signIdxLoop, run_pure]
  | succ k ih =>
    intro tried d
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [signIdxLoop_succ m k tried hc, run_query_bind, run_query_bind, oracleImpl_run_inl,
        oracleImpl_run_inl]
      simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun j => ?_
      simp only [loopBody]
      rw [run_query_bind, run_query_bind]
      rcases hdq : d (encQuery (m ++ nonceOf tried hc j)) with _ | w
      · have hdq' : Cache.extend d f (encQuery (m ++ nonceOf tried hc j)) = none := by
          rw [Cache.extend_apply_of_none hdq]; exact hf _
        rw [oracleImpl_run_inr_none hdq, oracleImpl_run_inr_none hdq']
        simp only [bind_assoc, pure_bind, map_bind]
        refine bind_congr fun w => ?_
        rw [← Cache.extend_cacheQuery]
        simp only [afterHash]
        split_ifs with hi
        · simp [run_pure]
        · exact ih _ _
      · have hdq' : Cache.extend d f (encQuery (m ++ nonceOf tried hc j)) = some w :=
          Cache.extend_apply_of_some hdq
        rw [oracleImpl_run_inr_some hdq, oracleImpl_run_inr_some hdq', pure_bind, pure_bind]
        simp only [afterHash]
        split_ifs with hi
        · simp [run_pure]
        · exact ih _ _
    · rw [signIdxLoop, dif_neg hc]
      simp [run_pure]

/-- Entries at non-encoding points (queries of another length) are irrelevant to the loop. -/
theorem run_signIdx_extend (m : Message) (d f : Cache)
    (hf : ∀ u : EncInput, f (encQuery u) = none) :
    run (signIdx m) (Cache.extend d f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run (signIdx m) d :=
  run_signIdxLoop_extend m f hf trials ∅ d

/-! ### The new cache entries -/

theorem signIdxLoop_support (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (d : Cache),
      ∀ p ∈ support (run (signIdxLoop m k tried) d),
        Cache.Sub d p.2 ∧
        (∀ q w, d q = none → p.2 q = some w →
          ∃ η : Nonce, q = encQuery (m ++ η) ∧
            ∀ hi : idxOf w < numCuts, p.1 = some (η, ⟨idxOf w, hi⟩)) ∧
        (∀ η i, p.1 = some (η, i) →
          ∃ w, p.2 (encQuery (m ++ η)) = some w ∧ idxOf w = i.val) := by
  intro k
  induction k with
  | zero =>
    intro tried d p hp
    rw [signIdxLoop, run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl d, fun q w h1 h2 => ?_, fun η i h => by simp at h⟩
    change d q = some w at h2
    rw [h1] at h2; cases h2
  | succ k ih =>
    intro tried d p hp
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [signIdxLoop_succ m k tried hc] at hp
      obtain ⟨j, hp⟩ := mem_support_run_inl hp
      simp only [loopBody] at hp
      generalize nonceOf tried hc j = η at hp
      rcases hdq : d (encQuery (m ++ η)) with _ | w
      · obtain ⟨w, hp⟩ := mem_support_run_inr_none hdq hp
        rw [afterHash] at hp
        by_cases hi : idxOf w < numCuts
        · rw [dif_pos hi, run_pure, support_pure] at hp
          simp only [Set.mem_singleton_iff] at hp
          subst hp
          refine ⟨Cache.sub_cacheQuery_of_none hdq w, ?_, ?_⟩
          · intro q w' h1 h2
            change (d.cacheQuery (encQuery (m ++ η)) w) q = some w' at h2
            by_cases hq : q = encQuery (m ++ η)
            · subst hq
              rw [QueryCache.cacheQuery_self] at h2
              obtain rfl := Option.some.inj h2
              exact ⟨η, rfl, fun _ => rfl⟩
            · rw [QueryCache.cacheQuery_of_ne _ _ hq, h1] at h2
              cases h2
          · intro η' i h
            change some (η, ⟨idxOf w, hi⟩) = some (η', i) at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨w, QueryCache.cacheQuery_self _ _ _, rfl⟩
        · rw [dif_neg hi] at hp
          obtain ⟨h1, h2, h3⟩ := ih (insert η tried) (d.cacheQuery _ w) p hp
          refine ⟨(Cache.sub_cacheQuery_of_none hdq w).trans h1, ?_, h3⟩
          intro q w' hq1 hq2
          by_cases hq : q = encQuery (m ++ η)
          · subst hq
            have : p.2 (encQuery (m ++ η)) = some w :=
              h1 _ _ (QueryCache.cacheQuery_self _ _ _)
            rw [this] at hq2
            obtain rfl := Option.some.inj hq2
            exact ⟨η, rfl, fun hi' => absurd hi' hi⟩
          · exact h2 q w' (by rw [QueryCache.cacheQuery_of_ne _ _ hq]; exact hq1) hq2
      · have hp := mem_support_run_inr_some hdq hp
        rw [afterHash] at hp
        by_cases hi : idxOf w < numCuts
        · rw [dif_pos hi, run_pure, support_pure] at hp
          simp only [Set.mem_singleton_iff] at hp
          subst hp
          refine ⟨Cache.Sub.refl d, fun q w' h1 h2 => ?_, ?_⟩
          · change d q = some w' at h2
            rw [h1] at h2; cases h2
          · intro η' i h
            change some (η, ⟨idxOf w, hi⟩) = some (η', i) at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨w, hdq, rfl⟩
        · rw [dif_neg hi] at hp
          exact ih (insert η tried) d p hp
    · rw [signIdxLoop, dif_neg hc, run_pure, support_pure] at hp
      simp only [Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨Cache.Sub.refl d, fun q w h1 h2 => ?_, fun η i h => by simp at h⟩
      change d q = some w at h2
      rw [h1] at h2; cases h2

/-- The new cache entries of the loop. -/
theorem signIdx_support (m : Message) (d : Cache) :
    ∀ p ∈ support (run (signIdx m) d),
      Cache.Sub d p.2 ∧
      (∀ q w, d q = none → p.2 q = some w →
        ∃ η : Nonce, q = encQuery (m ++ η) ∧
          ∀ hi : idxOf w < numCuts, p.1 = some (η, ⟨idxOf w, hi⟩)) ∧
      (∀ η i, p.1 = some (η, i) → ∃ w, p.2 (encQuery (m ++ η)) = some w ∧ idxOf w = i.val) :=
  signIdxLoop_support m trials ∅ d

/-! ### The signing bound -/

/-- A pre-existing encoding entry other than `u₁` has index `i`. -/
def IdxPre (d : Cache) (u₁ : EncInput) (i : ℕ) : Prop :=
  ∃ u, u ≠ u₁ ∧ ∃ w, d (encQuery u) = some w ∧ idxOf w = i

/-- `Φ` does not see encoding entries: the entries at queries of length `msgBits + nonceBits`. -/
def EncInvariant (Φ : Cache → ℝ≥0∞) : Prop :=
  ∀ (c : Cache) (u : EncInput) (w : BitVec hashBits),
    Φ (c.cacheQuery (encQuery u) w) = Φ c

/-- `d'` extends `d` by the entries of a signing run with outcome `r`. -/
def SignExt (m : Message) (d : Cache) (r : Option (Nonce × Fin numCuts)) (d' : Cache) :
    Prop :=
  Cache.Sub d d' ∧
  (∀ q w, d q = none → d' q = some w →
    ∃ η : Nonce, q = encQuery (m ++ η) ∧
      ∀ hi : idxOf w < numCuts, r = some (η, ⟨idxOf w, hi⟩)) ∧
  (∀ η i, r = some (η, i) → ∃ w, d' (encQuery (m ++ η)) = some w ∧ idxOf w = i.val)

/-- The encoding inputs cached with a valid index. -/
def validSet (d : Cache) : Finset (EncInput) :=
  Finset.univ.filter fun u : EncInput => ∃ w, d (encQuery u) = some w ∧ idxOf w < numCuts

/-- The valid indices of the entries of `d`. -/
def V (d : Cache) : Finset ℕ :=
  (validSet d).image fun u => ((d (encQuery u)).map (idxOf)).getD 0

theorem mem_V {d : Cache} {u : EncInput} {w : BitVec hashBits}
    (hu : d (encQuery u) = some w) (hw : idxOf w < numCuts) : idxOf w ∈ V d := by
  refine Finset.mem_image.2 ⟨u, ?_, ?_⟩
  · simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hu, hw⟩
  · simp [hu]

theorem V_lt (d : Cache) : ∀ n ∈ V d, n < 2 ^ idxBits := by
  intro n hn
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hn
  simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨w, hw, -⟩ := hu
  simp only [hw, Option.map_some, Option.getD_some]
  exact (w.setWidth idxBits).isLt

theorem card_idxOf_mem (hidx : idxBits ≤ hashBits) (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < 2 ^ idxBits) :
    (Finset.univ.filter fun y : BitVec hashBits => idxOf y ∈ A).card =
      A.card * 2 ^ (hashBits - idxBits) :=
  Analysis.card_idxOfOut_mem hidx A hA

theorem E_query_unif (n : ℕ) (g : Fin (n + 1) → ℝ≥0∞) :
    E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) g =
      ∑ j, ((n : ℝ≥0∞) + 1)⁻¹ * g j := by
  rw [E, expectedValue_def, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact ProbComp.probOutput_uniformFin n j

theorem cache_eq_of_notMem {d d' : Cache} {m : Message} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w < numCuts)
    {η : Nonce} (hη : η ∉ tried) :
    d' (encQuery (m ++ η)) = d (encQuery (m ++ η)) := by
  rcases hdq : d (encQuery (m ++ η)) with _ | w
  · rcases hd'q : d' (encQuery (m ++ η)) with _ | w'
    · rfl
    · obtain ⟨η', hη', he, -⟩ := hNew _ _ hdq hd'q
      exact absurd (by rw [append_nonce_inj m (encQuery_inj he)]; exact hη') hη
  · exact hSub _ _ hdq

theorem new_cacheQuery {d d' : Cache} {m : Message} {tried : Finset Nonce}
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w < numCuts)
    (η : Nonce) {w : BitVec hashBits} (hw : ¬ idxOf w < numCuts) :
    ∀ q w', d q = none → (d'.cacheQuery (encQuery (m ++ η)) w) q = some w' →
      ∃ η' ∈ insert η tried, q = encQuery (m ++ η') ∧ ¬ idxOf w' < numCuts := by
  intro q w' h1 h2
  by_cases hq : q = encQuery (m ++ η)
  · subst hq
    rw [QueryCache.cacheQuery_self] at h2
    obtain rfl := Option.some.inj h2
    exact ⟨η, Finset.mem_insert_self _ _, rfl, hw⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hq] at h2
    obtain ⟨η', hη', he, hi⟩ := hNew q w' h1 h2
    exact ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem new_insert {d d' : Cache} {m : Message} {tried : Finset Nonce}
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w < numCuts)
    (η : Nonce) :
    ∀ q w, d q = none → d' q = some w →
      ∃ η' ∈ insert η tried, q = encQuery (m ++ η') ∧ ¬ idxOf w < numCuts :=
  fun q w h1 h2 =>
    let ⟨η', hη', he, hi⟩ := hNew q w h1 h2
    ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem signExt_none {d d' : Cache} {m : Message} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w < numCuts) :
    SignExt m d none d' := by
  unfold SignExt
  refine ⟨hSub, fun q w h1 h2 => ?_, fun η i h => by cases h⟩
  obtain ⟨η, -, he, hi⟩ := hNew q w h1 h2
  exact ⟨η, he, fun hi' => absurd hi' hi⟩

theorem signExt_cached {d d' : Cache} {m : Message} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w < numCuts)
    {η : Nonce} {w : BitVec hashBits} (hi : idxOf w < numCuts)
    (hq : d' (encQuery (m ++ η)) = some w) :
    SignExt m d (some (η, ⟨idxOf w, hi⟩)) d' := by
  unfold SignExt
  refine ⟨hSub, fun q w' h1 h2 => ?_, fun η' i h => ?_⟩
  · obtain ⟨η', -, he, hi'⟩ := hNew q w' h1 h2
    exact ⟨η', he, fun h => absurd h hi'⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, hq, rfl⟩

theorem signExt_fresh {d d' : Cache} {m : Message} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w < numCuts)
    {η : Nonce} {w : BitVec hashBits} (hi : idxOf w < numCuts)
    (hq : d' (encQuery (m ++ η)) = none) :
    SignExt m d (some (η, ⟨idxOf w, hi⟩)) (d'.cacheQuery (encQuery (m ++ η)) w) := by
  unfold SignExt
  refine ⟨hSub.trans (Cache.sub_cacheQuery_of_none hq w), fun q w' h1 h2 => ?_,
    fun η' i h => ?_⟩
  · by_cases hqe : q = encQuery (m ++ η)
    · subst hqe
      rw [QueryCache.cacheQuery_self] at h2
      obtain rfl := Option.some.inj h2
      exact ⟨η, rfl, fun _ => rfl⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hqe] at h2
      obtain ⟨η', -, he, hi'⟩ := hNew q w' h1 h2
      exact ⟨η', he, fun h => absurd h hi'⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, QueryCache.cacheQuery_self _ _ _, rfl⟩

theorem ind_le_V {d : Cache} {m : Message} {η : Nonce} {w : BitVec hashBits}
    (hi : idxOf w < numCuts) :
    (if ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × Fin numCuts)) = some (η', i) ∧
        IdxPre d (m ++ η') i.val then (1 : ℝ≥0∞) else 0) ≤
      if idxOf w ∈ V d then 1 else 0 := by
  by_cases h1 : ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × Fin numCuts)) =
      some (η', i) ∧ IdxPre d (m ++ η') i.val
  · rw [if_pos h1]
    obtain ⟨η', i, he, hpre⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨u, -, w', hu, hw'⟩ := hpre
    have hw'' : idxOf w' = idxOf w := hw'
    have := mem_V hu (by rw [hw'']; exact hi)
    rw [hw''] at this
    rw [if_pos this]
  · rw [if_neg h1]; exact zero_le

theorem not_exists_none {d : Cache} {m : Message} :
    ¬ ∃ (η : Nonce) (i : Fin numCuts),
      (none : Option (Nonce × Fin numCuts)) = some (η, i) ∧ IdxPre d (m ++ η) i.val := by
  rintro ⟨_, _, h, _⟩
  cases h

end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.Correctness; SHA256 f96b83042f130650b73f7329ef5fa50a17718dc97cc3e07feac934bccb16bcc0. -/
section

/-!
Perfect correctness of the DAG adapter. The shared cache preserves the key-generation equations
and the signing index. Reconstructing an honestly encoded cut therefore recovers the public key,
even when oracle inputs repeat. The message may be any function of the public key.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.GenericCorrectness

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials


/-- A reconstruction satisfying the cached equations agrees with the original on visited nodes. -/
theorem reconstruct_eq (G : Graph) (A : Finset (Fin G.size)) (x y : G.Assignment)
    (c : Cache) (hc : G.CacheConsistent x c)
    (hsrc : ∀ v, G.Visited A v → v ∉ A → ¬ (G.kind v).IsSource)
    (hy : G.ReconEqs c A (G.decode A (G.encode A x)) y)
    (v : Fin G.size) (hv : G.Visited A v) : y v = x v := by
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    by_cases hA : v ∈ A
    · exact (hy v).1 hA |>.trans (G.decode_encode A x hA)
    · have hn := (hy v).2.2 hA hv
      have hx := hc v
      have hp : ∀ w ∈ (G.kind v).parents, y w = x w := fun w hw =>
        ih w ((G.kind v).lt_of_mem_parents hw) (Graph.Visited.parent hv hA hw)
      cases hk : G.kind v with
      | source => exact (hsrc v hv hA (by simp [hk, NodeKind.IsSource])).elim
      | det ps hps f hf =>
        have hx' : x v = f x := by simpa [Graph.CacheEqAt, hk] using hx
        exact (hn.2.1 ps hps f hf hk).trans ((hf y x (by simpa [hk, NodeKind.parents] using hp)).trans hx'.symm)
      | hash p hlt hl =>
        obtain ⟨w, hw, hyw⟩ := hn.1 p hlt hl hk
        have hpx : y p = x p := hp p (by simp [hk, NodeKind.parents])
        have hx' : c ⟨G.len p, x p⟩ = some ((x v).cast hl) := by
          simpa [Graph.CacheEqAt, hk] using hx
        rw [hpx, hx'] at hw
        have hw' := Option.some.inj hw
        rw [hyw, ← hw']
        simp

/-- Successful signing records its selected index and returns that cut's complete encoding. -/
theorem sign_result (S : Scheme) (x : S.graph.Assignment) (m : Message)
    (σ : Signature) (c d : Cache)
    (h : (some σ, d) ∈ support (run (S.sign x m) c)) :
    ∃ i : Fin numCuts, ∃ w : BitVec hashBits,
      σ.2 = S.graph.encode (S.sets i) x ∧
      d ⟨msgBits + nonceBits, m ++ σ.1⟩ = some w ∧
      (w.setWidth idxBits).toNat = i.val := by
  rw [sign_eq_map, run_map, support_map, Set.mem_image] at h
  obtain ⟨⟨r, d'⟩, hr, he⟩ := h
  cases r with
  | none => simp at he
  | some r =>
    obtain ⟨η, i⟩ := r
    simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at he
    rcases he with ⟨he, rfl⟩
    obtain ⟨w, hw, hi⟩ := (signIdx_support m c _ hr).2.2 η i rfl
    cases he
    exact ⟨i, w, rfl, hw, hi⟩

/-- A signature from a consistent assignment verifies under any extension of its signing cache. -/
theorem verify_accepts (S : Scheme) (x : S.graph.Assignment) (m : Message)
    (σ : Signature) (c : Cache) (hc : S.graph.CacheConsistent x c)
    (i : Fin numCuts) (w : BitVec hashBits)
    (hσ : σ.2 = S.graph.encode (S.sets i) x)
    (hw : c ⟨msgBits + nonceBits, m ++ σ.1⟩ = some w)
    (hi : (w.setWidth idxBits).toNat = i.val) :
    ∀ p ∈ support (run (S.verify (S.publicKey x) m σ) c), p.1 = true := by
  intro p hp
  unfold Scheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨j, d⟩, hj, hp⟩ := hp
  obtain ⟨hcd, w', hw', hj⟩ := index_support m σ.1 c ⟨j, d⟩ hj
  have hww : w' = w := Option.some.inj (hw'.symm.trans (hcd _ _ hw))
  rw [hww] at hj
  have hji : j = i.val := hj.trans hi
  subst j
  rw [dif_pos i.isLt] at hp
  have hlen : σ.2.length = S.graph.revealBits (S.sets i) := by
    rw [hσ, S.graph.length_encode]
  rw [if_pos hlen, run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨y, e⟩, hy, hp⟩ := hp
  obtain ⟨hde, he⟩ := S.graph.reconstruct_support _ _ d ⟨y, e⟩ hy
  rw [hσ] at he
  have hec := Graph.CacheConsistent.mono S.graph (hcd.trans hde) hc
  have hr := reconstruct_eq S.graph (S.sets i) x y e hec (S.no_hidden_source i)
    he S.graph.root Graph.Visited.root
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  simp only [Scheme.publicKey, hr, decide_true]

/-- Every DAG scheme's generic adapter is perfectly correct, including for messages selected
as an arbitrary function of the public key. Signing failure is handled by the availability bound. -/
theorem correct (S : Scheme) : S.toAlgorithm.Correct := by
  intro message
  dsimp only [Scheme.toAlgorithm]
  unfold probTrue
  rw [StateT.run'_eq, probOutput_eq_zero_iff, support_map]
  rintro ⟨⟨b, e⟩, h, hb⟩
  change (b, e) ∈ support (run _ ∅) at h
  rw [run_bind, support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨⟨pk, sk⟩, c⟩, hk, h⟩ := h
  rw [run_bind, support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨σ, d⟩, hs, h⟩ := h
  obtain ⟨hpk, hkc⟩ := S.keygen_cacheConsistent ∅ _ hk
  dsimp only at hpk hkc
  subst pk
  change b = true at hb
  cases σ with
  | none =>
    simp only [run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
    cases h.1.symm.trans hb
  | some σ =>
    obtain ⟨i, w, hσ, hw, hi⟩ := sign_result S sk (message (S.publicKey sk)) σ c d hs
    have hcd := sub_of_mem_support_run (S.sign sk (message (S.publicKey sk))) c _ hs
    have hdc := Graph.CacheConsistent.mono S.graph hcd hkc
    rw [run_bind, support_bind] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨⟨ok, f⟩, hv, h⟩ := h
    have hok : ok = true :=
      verify_accepts S sk (message (S.publicKey sk)) σ d hdc i w hσ hw hi _ hv
    simp only [hok, Bool.not_true, run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    cases h.1.symm.trans hb

/--
info: 'OptimalOTS.GenericCorrectness.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correct

end OptimalOTS.GenericCorrectness
end
end

/- Original module: Submissions.UpperCompressions.WeightedScheme; SHA256 34018178e72f1739b7133165cfab79170f6cf2a5919939ac78777451d53c714d. -/
section

/-! Generic graph scheme with an86-bit nonce and weighted all-trial signer.
The decoder and tier function are explicit parameters. These resource and
correctness lemmas do not establish availability or strong security. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedScheme

open WeightedConstruction
abbrev Signature := NonceCodec.Signature86

structure Scheme (M : ℕ) where
  graph : Dag.Graph
  sets : Fin M → Finset (Fin graph.size)
  decode : BitVec hashBits → Option (Fin M)
  tier : Fin M → ℕ
  root_not_mem : ∀ i, graph.root ∉ sets i
  no_hidden_source :
    ∀ i v, graph.Visited (sets i) v → v ∉ sets i → ¬ (graph.kind v).IsSource
  reveal_le : ∀ i, graph.revealBits (sets i) + 86 ≤ maxSignatureBits
  keygen_le : graph.keygenCost ≤ keygenBudget

namespace Scheme
variable {M : ℕ} (S : Scheme M)

def publicKey (x : S.graph.Assignment) : PublicKey := (x S.graph.root).setWidth pkBits

def keygen : OracleComp Spec (PublicKey × S.graph.Assignment) :=
  GraphKeygenBridge.keygen S.graph S.publicKey

def sign (x : S.graph.Assignment) (m : Message) : OracleComp Spec (Option Signature) :=
  (Option.map fun r : WeightedSampling.Winner 86 M =>
    (r.1, S.graph.encode (S.sets r.2) x)) <$>
      WeightedSampling.loop 86 S.decode S.tier m signBudget

def verify (pk : PublicKey) (m : Message) (σ : Signature) : OracleComp Spec Bool := do
  let w ← hash (m ++ σ.1)
  match S.decode w with
  | none => return false
  | some i =>
      if σ.2.length = S.graph.revealBits (S.sets i) then
        let y ← S.graph.reconstruct (S.sets i) (S.graph.decode (S.sets i) σ.2)
        return decide (S.publicKey y = pk)
      else
        return false

def toAlgorithm : TypedScheme where
  SecretKey := S.graph.Assignment
  Signature := Signature
  encodeSignature := NonceCodec.encode
  encodeSignature_injective := NonceCodec.encode_injective
  keygen := S.keygen
  sign := S.sign
  verify := S.verify

open AlgorithmCosts

theorem costAtMost_keygen_exact : CostAtMost S.keygen S.graph.keygenCost :=
  CostAtMost.bind_le (AlgorithmCosts.Dag.Graph.costAtMost_keygen S.graph)
    (fun _ => costAtMost_pure _ 0) (by simp)

theorem keygenCost : S.toAlgorithm.KeygenCostAtMost keygenBudget :=
  CostAtMost.mono S.costAtMost_keygen_exact S.keygen_le

theorem signCost : S.toAlgorithm.SignCostAtMost signBudget := fun _x m =>
  CostAtMost.map (WeightedSampling.costAtMost_loop86 S.decode S.tier m) _

theorem verifyCost {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    S.toAlgorithm.VerifyCostAtMost (1+v) := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    CostAtMost (S.verify pk m σ) (1+v)
  intro pk m σ
  unfold verify
  refine CostAtMost.bind_le (costAtMost_hash _ WeightedSampling.index86_cost.le)
    (b₂ := v) (fun w => ?_) le_rfl
  cases S.decode w with
  | none => exact costAtMost_pure _ _
  | some i =>
    dsimp only
    split_ifs
    · exact CostAtMost.bind_le
        (CostAtMost.mono
          (AlgorithmCosts.Dag.Graph.costAtMost_reconstruct S.graph (S.sets i) _) (hv i))
        (fun _ => costAtMost_pure _ 0) (by simp)
    · exact costAtMost_pure _ _

theorem verifyDeterministic : S.toAlgorithm.VerifyDeterministic := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    Deterministic (S.verify pk m σ)
  intro pk m σ
  unfold verify
  refine Deterministic.bind (Deterministic.hash _) fun w => ?_
  cases S.decode w with
  | none => exact Deterministic.of_pure _
  | some i =>
    dsimp only
    split_ifs
    · exact Deterministic.bind (S.graph.deterministic_reconstruct _ _)
        fun _ => Deterministic.of_pure _
    · exact Deterministic.of_pure _

theorem signatureSize : S.toAlgorithm.SignatureSizeAtMost maxSignatureBits := by
  change ∀ (x : S.graph.Assignment) (m : Message) (σ : Signature),
    some σ ∈ support (S.sign x m) → (NonceCodec.encode σ).length ≤ maxSignatureBits
  intro x m σ h
  change some σ ∈ support (S.sign x m) at h
  rw [sign, support_map, Set.mem_image] at h
  obtain ⟨r, _, hr⟩ := h
  cases r with
  | none => simp at hr
  | some r =>
    simp only [Option.map_some, Option.some.injEq] at hr
    subst σ
    rw [NonceCodec.length_encode, S.graph.length_encode]
    have := S.reveal_le r.2
    omega

theorem rejectsOversized : S.toAlgorithm.RejectsOversized maxSignatureBits := by
  change ∀ (pk : PublicKey) (m : Message) (σ : Signature),
    maxSignatureBits < (NonceCodec.encode σ).length → true ∉ support (S.verify pk m σ)
  intro pk m σ hlen hmem
  change maxSignatureBits < (NonceCodec.encode σ).length at hlen
  rw [NonceCodec.length_encode] at hlen
  change true ∈ support (S.verify pk m σ) at hmem
  rw [verify, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨w, _, hmem⟩ := hmem
  cases hd : S.decode w with
  | none => simp [hd] at hmem
  | some i =>
    have hwrong : σ.2.length ≠ S.graph.revealBits (S.sets i) := by
      have := S.reveal_le i
      omega
    simp [hd, hwrong] at hmem

theorem keygen_cacheConsistent (c : Cache) :
    ∀ p ∈ support (run S.keygen c),
      p.1.1 = S.publicKey p.1.2 ∧ S.graph.CacheConsistent p.1.2 p.2 := by
  intro p hp
  simp only [keygen, GraphKeygenBridge.keygen, Dag.Graph.keygen,
    run_bind, support_bind, Set.mem_iUnion] at hp
  obtain ⟨⟨x,d⟩, ⟨⟨z,d'⟩, _, hx⟩, hp⟩ := hp
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst p
  exact ⟨rfl, S.graph.evaluate_cacheConsistent z d' _ hx⟩

theorem sign_result (x : S.graph.Assignment) (m : Message) (σ : Signature) (c d : Cache)
    (h : (some σ,d) ∈ support (run (S.sign x m) c)) :
    ∃ i : Fin M, ∃ w : BitVec hashBits,
      σ.2 = S.graph.encode (S.sets i) x ∧
      d ⟨msgBits+86,m++σ.1⟩ = some w ∧ S.decode w = some i := by
  rw [sign, run_map, support_map, Set.mem_image] at h
  obtain ⟨⟨r,d'⟩, hr, he⟩ := h
  cases r with
  | none => simp at he
  | some r =>
    obtain ⟨η,i⟩ := r
    simp only [Option.map_some, Prod.mk.injEq, Option.some.injEq] at he
    rcases he with ⟨he,rfl⟩
    obtain ⟨w,hw,hi⟩ :=
      (WeightedSampling.loop_support 86 S.decode S.tier m signBudget c _ hr).2 η i rfl
    cases he
    exact ⟨i,w,rfl,hw,hi⟩

theorem verify_accepts (x : S.graph.Assignment) (m : Message) (σ : Signature)
    (c : Cache) (hc : S.graph.CacheConsistent x c) (i : Fin M) (w : BitVec hashBits)
    (hσ : σ.2 = S.graph.encode (S.sets i) x)
    (hw : c ⟨msgBits+86,m++σ.1⟩ = some w) (hi : S.decode w = some i) :
    ∀ p ∈ support (run (S.verify (S.publicKey x) m σ) c), p.1 = true := by
  intro p hp
  unfold verify at hp
  rw [run_bind, WeightedSampling.run_hash_cached _ c w hw, pure_bind, hi] at hp
  dsimp only at hp
  have hlen : σ.2.length = S.graph.revealBits (S.sets i) := by
    rw [hσ,S.graph.length_encode]
  rw [if_pos hlen,run_bind,support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨y,e⟩,hy,hp⟩ := hp
  obtain ⟨hce,he⟩ := S.graph.reconstruct_support _ _ c (y,e) hy
  rw [hσ] at he
  have hec := Dag.Graph.CacheConsistent.mono S.graph hce hc
  have hr := GenericCorrectness.reconstruct_eq S.graph (S.sets i) x y e hec
    (S.no_hidden_source i) he S.graph.root Dag.Graph.Visited.root
  rw [run_pure,support_pure,Set.mem_singleton_iff] at hp
  subst p
  simp only [publicKey,hr,decide_true]

/-- Perfect correctness, including public-key-dependent message choices. -/
theorem correct : S.toAlgorithm.Correct := by
  intro message
  dsimp only [toAlgorithm]
  unfold probTrue
  rw [StateT.run'_eq,probOutput_eq_zero_iff,support_map]
  rintro ⟨⟨b,e⟩,h,hb⟩
  change (b,e) ∈ support (run _ ∅) at h
  rw [run_bind,support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨⟨pk,sk⟩,c⟩,hk,h⟩ := h
  rw [run_bind,support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨⟨σ,d⟩,hs,h⟩ := h
  obtain ⟨hpk,hkc⟩ := S.keygen_cacheConsistent ∅ _ hk
  dsimp only at hpk hkc
  subst pk
  change b = true at hb
  cases σ with
  | none =>
    simp only [run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq] at h
    cases h.1.symm.trans hb
  | some σ =>
    obtain ⟨i,w,hσ,hw,hi⟩ := S.sign_result sk (message (S.publicKey sk)) σ c d hs
    have hcd := sub_of_mem_support_run (S.sign sk (message (S.publicKey sk))) c _ hs
    have hdc := Dag.Graph.CacheConsistent.mono S.graph hcd hkc
    rw [run_bind,support_bind] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨⟨ok,f⟩,hv,h⟩ := h
    have hok : ok = true := S.verify_accepts sk (message (S.publicKey sk)) σ d hdc
      i w hσ hw hi _ hv
    simp only [hok,Bool.not_true,run_pure,support_pure,Set.mem_singleton_iff,
      Prod.mk.injEq] at h
    cases h.1.symm.trans hb

#print axioms correct

#print axioms keygenCost
#print axioms signCost
#print axioms verifyCost
#print axioms verifyDeterministic
#print axioms signatureSize
#print axioms rejectsOversized

end Scheme
end OptimalOTS.WeightedScheme
end
end

/- Original module: Submissions.UpperCompressions.WideNames; SHA256 8b0a5c8d5b9ae6f44d6189f7ab49ec0326f268e71b8cf8792240ba2e5f823f4f. -/
section

/-!
# Names and graph for the wide weighted candidate

54 tagged hash chains of length 18 feed 18 ternary group hashes directly into
one root. Inputs have lengths 145, 403, and 2338 bits. The root costs five
compressions, so key generation costs 54 * 18 + 18 + 5 = 995.

This file defines the graph and certifies its topology and key-generation cost.
It does not establish a disclosure family, signing availability, or security.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace WeightedConstruction.WideForest

/-- Node names. -/
inductive Name where
  | src (k : Fin 54)
  | ci (k : Fin 54) (t : Fin 18)
  | ch (k : Fin 54) (t : Fin 18)
  | cv (k : Fin 54) (t : Fin 18)
  | gc (j : Fin 18)
  | gh (j : Fin 18)
  | gv (j : Fin 18)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 3026

namespace Name

/-- Topological index. -/
def idx : Name → ℕ
  | src k => k
  | ci k t => 54 + 162 * t + k
  | ch k t => 108 + 162 * t + k
  | cv k t => 162 + 162 * t + k
  | gc j => 2970 + j
  | gh j => 2988 + j
  | gv j => 3006 + j
  | rc => 3024
  | rh => 3025

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

/-- The index as an element of `Fin N`. -/
def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src _ => 129
  | ci _ _ => 145
  | ch _ _ => 256
  | cv _ _ => 129
  | gc _ => 403
  | gh _ => 256
  | gv _ => 129
  | rc => 2338
  | rh => 256

/-- Query cost of a node: one compression for every hash node except the root, which costs five. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | gh _ => 1
  | rh => 5
  | _ => 0

/-- The value node feeding the chain hash `ch k t` (through its input `ci k t`): the source for
`t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 54) (t : Fin 18) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The `a`-th chain of group `j`. -/
def chainOf (j : Fin 18) (a : Fin 3) : Fin 54 := ⟨3 * j + a, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ci k 0)
  | ci k t => some (ch k t)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 17 then some (gc ⟨k / 3, by omega⟩) else some (ci k ⟨t + 1, by omega⟩)
  | gc j => some (gh j)
  | gh j => some (gv j)
  | gv _ => some rc
  | rc => some rh
  | rh => none

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ci k t => {prev k t}
  | ch k t => {ci k t}
  | cv k t => {ch k t}
  | gc j => {cv (chainOf j 0) 17, cv (chainOf j 1) 17, cv (chainOf j 2) 17}
  | gh j => {gc j}
  | gv j => {gh j}
  | rc => Finset.univ.image gv
  | rh => {rc}

theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  cases n <;> cases m <;>
    simp only [parents, child, prev, chainOf, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.notMem_empty, Option.some.injEq,
      reduceCtorEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.gc.injEq, Name.gh.injEq,
      Name.gv.injEq, Fin.ext_iff,
      Fin.val_zero, iff_true, iff_false, false_iff, or_false, exists_false] <;>
    (try split_ifs) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Name.src.injEq, Name.ci.injEq,
      Name.cv.injEq, Name.gc.injEq, Fin.ext_iff, iff_false, false_iff, not_false_eq_true]) <;>
    first | omega | exact ⟨_, rfl⟩

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  rw [mem_parents_iff] at h
  cases m <;> simp only [child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;> (try simp only [Option.some.injEq] at h) <;> subst h <;>
    simp only [idx, Fin.val_zero] <;> omega

end Name

/-- The inverse of `Name.fin`. -/
def ofFin (v : Fin N) : Name :=
  if h₁ : v.val < 54 then .src ⟨v.val, h₁⟩
  else if h₂ : v.val < 2970 then
    let m := v.val - 54
    let t : Fin 18 := ⟨m / 162, by omega⟩
    let r := m % 162
    if h₃ : r < 54 then .ci ⟨r, h₃⟩ t
    else if h₃' : r < 108 then .ch ⟨r - 54, by omega⟩ t
    else .cv ⟨r - 108, by omega⟩ t
  else if h₄ : v.val < 2988 then .gc ⟨v.val - 2970, by omega⟩
  else if h₅ : v.val < 3006 then .gh ⟨v.val - 2988, by omega⟩
  else if h₆ : v.val < 3024 then .gv ⟨v.val - 3006, by omega⟩
  else if h₇ : v.val < 3025 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.gc.injEq,
      Name.gh.injEq, Name.gv.injEq, Fin.ext_iff,
      reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 3026 := v.isLt
  rw [Fin.ext_iff]
  simp only [ofFin]
  split_ifs <;> simp only [Name.fin, Name.idx] <;> omega

theorem ofFin_fin (n : Name) : ofFin n.fin = n :=
  Name.idx_injective (congrArg Fin.val (fin_ofFin_aux n.fin))

theorem fin_ofFin (v : Fin N) : (ofFin v).fin = v := fin_ofFin_aux v

/-- Names and indices. -/
def nameEquiv : Name ≃ Fin N where
  toFun := Name.fin
  invFun := ofFin
  left_inv := ofFin_fin
  right_inv := fin_ofFin

theorem Name.fin_injective : Function.Injective Name.fin := nameEquiv.injective

/-- The finite sum type behind `Name`. -/
abbrev NameSum := Fin 54 ⊕ (Fin 54 × Fin 18) ⊕ (Fin 54 × Fin 18) ⊕ (Fin 54 × Fin 18) ⊕ Fin 18 ⊕ Fin 18 ⊕ Fin 18 ⊕ Unit ⊕ Unit

/-- `Name` as a sum type. -/
def Name.toSum : Name → NameSum
  | src k => .inl k
  | ci k t => .inr (.inl (k, t))
  | ch k t => .inr (.inr (.inl (k, t)))
  | cv k t => .inr (.inr (.inr (.inl (k, t))))
  | gc j => .inr (.inr (.inr (.inr (.inl j))))
  | gh j => .inr (.inr (.inr (.inr (.inr (.inl j)))))
  | gv j => .inr (.inr (.inr (.inr (.inr (.inr (.inl j))))))
  | rc => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
  | rh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (()))))))))

def Name.ofSum : NameSum → Name
  | .inl k => src k
  | .inr (.inl (k, t)) => ci k t
  | .inr (.inr (.inl (k, t))) => ch k t
  | .inr (.inr (.inr (.inl (k, t)))) => cv k t
  | .inr (.inr (.inr (.inr (.inl j)))) => gc j
  | .inr (.inr (.inr (.inr (.inr (.inl j))))) => gh j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl j)))))) => gv j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))) => rc
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (())))))))) => rh

/-- The node names are equivalent to their constructor sum. -/
def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | ⟨k, t⟩ | j | j | j | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

/-- Sums over names split by constructor. -/
theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ci k t)) + (∑ k, ∑ t, f (ch k t)) +
      (∑ k, ∑ t, f (cv k t)) + (∑ j, f (gc j)) + (∑ j, f (gh j)) +
      (∑ j, f (gv j)) + f rc + f rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## Tweaks

The random oracle has no labels: a hash node queries it on its parent's value alone.  The scheme
keeps its hash nodes apart by starting every hash input with a 16-bit tweak naming the hash node.
Convention: the tweak occupies the HIGH bits, i.e. the input of the hash node `h` is
`tw h ++ payload` (`BitVec.append`, whose left argument is the most significant one).  The
payload is recovered by `setWidth`/`extractLsb' 0`, the tweak by `extractLsb' n 16` or
`tagNat`. -/

/-- The tweak of the hash node `h`: its topological index, on 16 bits. -/
def tw (h : Name) : BitVec 16 := BitVec.ofNat 16 h.idx

theorem tw_toNat (h : Name) : (tw h).toNat = h.idx := by
  have := h.idx_lt
  unfold N at this
  rw [tw, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem tw_injective : Function.Injective tw := by
  intro h h' e
  apply Name.idx_injective
  rw [← tw_toNat h, ← tw_toNat h', e]

/-- A hash input determines its tweak and its payload. -/
theorem append_inj {n : ℕ} {a a' : BitVec 16} {u u' : BitVec n} (e : a ++ u = a' ++ u') :
    a = a' ∧ u = u' := by
  constructor
  · have := congrArg (fun z => z.extractLsb' n 16) e
    simpa only [BitVec.extractLsb'_append_eq_left] using this
  · have := congrArg (fun z => z.extractLsb' 0 n) e
    simpa only [BitVec.extractLsb'_append_eq_right] using this

/-- Equal hash inputs (of one length) belong to the same hash node and have the same payload. -/
theorem tw_append_inj {n : ℕ} {h h' : Name} {u u' : BitVec n} (e : tw h ++ u = tw h' ++ u') :
    h = h' ∧ u = u' :=
  ⟨tw_injective (append_inj e).1, (append_inj e).2⟩

/-- The number written in the 16 high bits of a query. -/
def tagNat (q : Query) : ℕ := q.2.toNat / 2 ^ (q.1 - 16)

theorem tagNat_append {n : ℕ} (a : BitVec 16) (u : BitVec n) :
    tagNat ⟨16 + n, a ++ u⟩ = a.toNat := by
  unfold tagNat
  simp only [BitVec.toNat_append, Nat.add_sub_cancel_left]
  rw [← Nat.shiftLeft_add_eq_or_of_lt u.isLt, Nat.shiftLeft_eq, Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt u.isLt, Nat.zero_add]

/-- The tweak is read back from a hash input. -/
theorem tagNat_tw_append {n : ℕ} (h : Name) (u : BitVec n) :
    tagNat ⟨16 + n, tw h ++ u⟩ = h.idx := by
  rw [tagNat_append, tw_toNat]

/-- `tagNat` ignores casts. -/
theorem tagNat_cast {n m : ℕ} (e : n = m) (u : BitVec n) :
    tagNat ⟨m, u.cast e⟩ = tagNat ⟨n, u⟩ := by
  subst e; rfl

/-! ## The graph -/

/-- Output lengths, indexed by `Fin N`. -/
def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- Concatenation of three 129-bit values. -/
def cat3 (a b c : BitVec 129) : BitVec 387 := (a ++ b ++ c).cast (by norm_num)

/-- Concatenation of eighteen 129-bit values. -/
def cat18 (a : Fin 18 → BitVec 129) : BitVec 2322 :=
  (a 0 ++ a 1 ++ a 2 ++ a 3 ++ a 4 ++ a 5 ++
    a 6 ++ a 7 ++ a 8 ++ a 9 ++ a 10 ++ a 11 ++
    a 12 ++ a 13 ++ a 14 ++ a 15 ++ a 16 ++ a 17).cast (by norm_num)

/-- The 129-bit truncation. -/
def lowWord {w : ℕ} (x : BitVec w) : BitVec 129 := x.setWidth 129

/-- The public key uses 128 low bits, independently of the internal word width. -/
def lowPk {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

/-- Assignments of the concrete graph. -/
abbrev Asg := (v : Fin N) → BitVec (lenF v)

/-- The deterministic value of a node, as a function of the assignment (only used for the
deterministic nodes; the function is defined on all names for convenience).  The hash inputs
`ci`, `gc`, `rc` start with the tweak of their hash node, in the high bits. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .ci k t => tw (Name.ch k t) ++ lowWord (x (Name.prev k t).fin)
  | .cv k t => lowWord (x (Name.ch k t).fin)
  | .gc j => tw (Name.gh j) ++ cat3 (lowWord (x (Name.cv (Name.chainOf j 0) 17).fin))
      (lowWord (x (Name.cv (Name.chainOf j 1) 17).fin)) (lowWord (x (Name.cv (Name.chainOf j 2) 17).fin))
  | .gv j => lowWord (x (Name.gh j).fin)
  | .rc => tw Name.rh ++ cat18 fun l => lowWord (x (Name.gv l).fin)
  | _ => 0

/-- The value of the parent `p` of a hash node `h` carries the tweak of `h`. -/
theorem tagNat_detVal {p h : Name} (hc : Name.child p = some h) (hh : h.cost ≠ 0) (x : Asg) :
    tagNat ⟨p.len, detVal p x⟩ = h.idx := by
  cases p with
  | ci k t =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_tw_append (n := 129) _ _
  | gc j =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_tw_append (n := 387) _ _
  | rc =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    exact tagNat_tw_append (n := 2322) _ _
  | cv k t =>
    simp only [Name.child] at hc
    split_ifs at hc <;>
      (simp only [Option.some.injEq] at hc; subst hc; exact absurd rfl hh)
  | rh => simp only [Name.child, reduceCtorEq] at hc
  | src k => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | ch k t => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | gh j => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | gv j => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh


/-- The same, for the value as stored in the graph (cast to the length `graph.len p.fin`). -/
theorem tagNat_cast_detVal {p h : Name} (hc : Name.child p = some h) (hh : h.cost ≠ 0) (x : Asg)
    {m : ℕ} (e : p.len = m) : tagNat ⟨m, (detVal p x).cast e⟩ = h.idx := by
  rw [tagNat_cast, tagNat_detVal hc hh]

theorem eq_fin_of_ofFin_eq {v : Fin N} {n : Name} (h : ofFin v = n) : v = n.fin := by
  rw [← h, fin_ofFin]

theorem Name.fin_lt_fin_of_mem_parents {m n : Name} (h : m ∈ Name.parents n) : m.fin < n.fin :=
  Name.idx_lt_of_mem_parents h

theorem hash_parent_lt {v : Fin N} {n m : Name} (h : ofFin v = n) (hm : m ∈ Name.parents n) :
    m.fin < v := by
  rw [eq_fin_of_ofFin_eq h]
  exact Name.fin_lt_fin_of_mem_parents hm

theorem det_parents_lt {v : Fin N} {n : Name} (h : ofFin v = n) :
    ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, w < v := by
  intro w hw
  rw [Finset.mem_map] at hw
  obtain ⟨m, hm, rfl⟩ := hw
  exact hash_parent_lt h hm

theorem detVal_local (n : Name) (x y : Asg)
    (hxy : ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, x w = y w) :
    detVal n x = detVal n y := by
  have key : ∀ m ∈ Name.parents n, x m.fin = y m.fin := fun m hm =>
    hxy m.fin (Finset.mem_map_of_mem _ hm)
  cases n with
  | ci k t =>
    show tw (Name.ch k t) ++ lowWord (x (Name.prev k t).fin) =
      tw (Name.ch k t) ++ lowWord (y (Name.prev k t).fin)
    rw [key (Name.prev k t) (by simp [Name.parents])]
  | cv k t =>
    show lowWord (x (Name.ch k t).fin) = lowWord (y (Name.ch k t).fin)
    rw [key (Name.ch k t) (by simp [Name.parents])]
  | gc j =>
    show tw (Name.gh j) ++ cat3 (lowWord (x (Name.cv (Name.chainOf j 0) 17).fin))
        (lowWord (x (Name.cv (Name.chainOf j 1) 17).fin))
        (lowWord (x (Name.cv (Name.chainOf j 2) 17).fin)) =
      tw (Name.gh j) ++ cat3 (lowWord (y (Name.cv (Name.chainOf j 0) 17).fin))
        (lowWord (y (Name.cv (Name.chainOf j 1) 17).fin))
        (lowWord (y (Name.cv (Name.chainOf j 2) 17).fin))
    rw [key (Name.cv (Name.chainOf j 0) 17) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 1) 17) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 2) 17) (by simp [Name.parents])]
  | gv j =>
    show lowWord (x (Name.gh j).fin) = lowWord (y (Name.gh j).fin)
    rw [key (Name.gh j) (by simp [Name.parents])]
  | rc =>
    show tw Name.rh ++ cat18 (fun l => lowWord (x (Name.gv l).fin)) =
      tw Name.rh ++ cat18 (fun l => lowWord (y (Name.gv l).fin))
    have e : (fun l => lowWord (x (Name.gv l).fin)) = fun l => lowWord (y (Name.gv l).fin) := by
      funext l
      rw [key (Name.gv l) (Finset.mem_image_of_mem _ (Finset.mem_univ _))]
    rw [e]
  | src _ => rfl
  | ch _ _ => rfl
  | gh _ => rfl
  | rh => rfl

/-- The kind of the node `v = n.fin`. -/
def kindOf (v : Fin N) : (n : Name) → ofFin v = n → NodeKind N lenF v
  | .src _, _ => .source
  | .ci k t, h => .det ((Name.parents (.ci k t)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.ci k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .ch k t, h => .hash (Name.ci k t).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .cv k t, h => .det ((Name.parents (.cv k t)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.cv k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .gc j, h => .det ((Name.parents (.gc j)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.gc j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .gh j, h => .hash (Name.gc j).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .gv j, h => .det ((Name.parents (.gv j)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.gv j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .rc, h => .det ((Name.parents .rc).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal .rc x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .rh, h => .hash Name.rc.fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)

theorem kindOf_isHash (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsHash ↔ n.cost ≠ 0 := by
  cases n <;> simp [kindOf, NodeKind.IsHash, Name.cost]

theorem kindOf_isSource (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsSource ↔ ∃ k, n = .src k := by
  cases n <;> simp [kindOf, NodeKind.IsSource]

theorem kindOf_parents (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  cases n <;> simp [kindOf, NodeKind.parents, Name.parents, nameEquiv]

/-- The computation graph of the scheme. -/
def graph : Graph where
  size := N
  len := lenF
  kind v := kindOf v (ofFin v) rfl
  root := Name.rh.fin
  root_isHash := (kindOf_isHash _ _ rfl).2 (by rw [ofFin_fin]; decide)

/-- The public-key projection is the only truncation to 128 bits in this graph interface. -/
def publicKey (x : graph.Assignment) : PublicKey := lowPk (x graph.root)

theorem graph_kind_eq (v : Fin N) (n : Name) (h : ofFin v = n) : graph.kind v = kindOf v n h := by
  subst h; rfl

theorem graph_kind_fin (n : Name) : graph.kind n.fin = kindOf n.fin n (ofFin_fin n) :=
  graph_kind_eq _ _ _

theorem graph_len_fin (n : Name) : graph.len n.fin = n.len := lenF_fin n

/-- The parents of a node, in the graph. -/
theorem graph_parents_fin (n : Name) :
    (graph.kind n.fin).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  rw [graph_kind_fin]; exact kindOf_parents _ _ _

theorem graph_isHash_fin (n : Name) :
    (graph.kind n.fin).IsHash ↔ n.cost ≠ 0 := by
  rw [graph_kind_fin]; exact kindOf_isHash _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ k, n = .src k := by
  rw [graph_kind_fin]; exact kindOf_isSource _ _ _

theorem Name.len_prev (k : Fin 54) (t : Fin 18) : (Name.prev k t).len = 129 := by
  unfold Name.prev; split_ifs <;> rfl

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits]

theorem graph_keygenCost : graph.keygenCost = 995 := by
  show ∑ v : Fin N, graph.nodeCost v = 995
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

/-- Every actual hash node still produces all 256 oracle output bits. -/
theorem hash_output_width (n : Name) (hn : n.cost ≠ 0) : n.len = 256 := by
  cases n <;> simp [Name.cost] at hn <;> rfl

/-- Internal hash inputs remain disjoint in length from the 256+86-bit index input. -/
theorem hash_input_length_ne_index {p h : Name}
    (hp : Name.child p = some h) (hh : h.cost ≠ 0) : p.len ≠ 342 := by
  cases p <;> simp only [Name.len] <;> omega

theorem input_lengths (k : Fin 54) (t : Fin 18) (j : Fin 18) :
    (Name.ci k t).len = 145 ∧ (Name.gc j).len = 403 ∧ Name.rc.len = 2338 := by
  exact ⟨rfl, rfl, rfl⟩

theorem input_costs : blockCost 145 = 1 ∧ blockCost 403 = 1 ∧ blockCost 2338 = 5 := by
  norm_num [blockCost, blockBits]

end WeightedConstruction.WideForest

end OptimalOTS

#print axioms OptimalOTS.WeightedConstruction.WideForest.graph_keygenCost

#print axioms OptimalOTS.WeightedConstruction.WideForest.hash_output_width
#print axioms OptimalOTS.WeightedConstruction.WideForest.input_costs
end
end

/- Original module: Submissions.UpperCompressions.WideTree; SHA256 f4a83dfa2e5b0a4b209607528604ee2f22d2ab55ef1c719a03565e121fae54af. -/
section

/-!
# The tree structure of the concrete graph

Every node other than the root feeds exactly one other node (`Name.child`), so the graph is a
tree.  This file relates the generic notions of `OptimalOTS.Dag` (`Graph.Visited`,
`Graph.evaluated`, `Graph.reconstructCost`, `Graph.revealBits`) to the tree:

* `Above m n`: `m` is a strict ancestor of `n` (reached by following `child` at least once);
  `ancSet n` is the explicit finite set of strict ancestors;
* `visited_iff`: a node is visited when reconstructing from the (names of the) set `A` exactly
  when none of its strict ancestors lies in `A`;
* `Evaluated A n`: `n ∉ A` and no strict ancestor of `n` lies in `A`;
* `reconstructCost_eq`, `revealBits_eq`, `no_hidden_source_iff`: the scheme's quantities in
  tree terms;
* cuts (`IsCut`): antichains of 129-bit nodes meeting every source path; distinct cuts of equal
  cost are incomparable (`exists_mem_evaluated_of_ne`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace WeightedConstruction.WideForest

open Name

/-- Strict ancestors: `m` is reached from `n` by following `child` at least once. -/
inductive Above : Name → Name → Prop
  | child {m n : Name} : child n = some m → Above m n
  | step {m n p : Name} : child n = some p → Above m p → Above m n

/-- Distance to the root. -/
def height : Name → ℕ
  | src _ => 59
  | ci _ t => 58 - 3 * t
  | ch _ t => 57 - 3 * t
  | cv _ t => 56 - 3 * t
  | gc _ => 4
  | gh _ => 3
  | gv _ => 2
  | rc => 1
  | rh => 0

theorem height_child {m n : Name} (h : child n = some m) : height m + 1 = height n := by
  cases n <;> simp only [Name.child, Option.some.injEq, reduceCtorEq] at h
  all_goals try (subst h; simp [height]; try omega)
  split_ifs at h with ht <;> (simp only [Option.some.injEq] at h; subst h; simp [height]; omega)

theorem Above.trans {a b c : Name} (h₁ : Above a b) (h₂ : Above b c) : Above a c := by
  revert h₁
  induction h₂ with
  | child h => intro h₁; exact Above.step h h₁
  | step h _ ih => intro h₁; exact Above.step h (ih h₁)

theorem above_of_child {m n p : Name} (h : child n = some p) : Above m n ↔ m = p ∨ Above m p := by
  constructor
  · intro ha
    cases ha with
    | child h' => rw [h, Option.some.injEq] at h'; exact Or.inl h'.symm
    | step h' ha' => rw [h, Option.some.injEq] at h'; subst h'; exact Or.inr ha'
  · rintro (rfl | ha)
    · exact Above.child h
    · exact Above.step h ha

theorem not_above_rh (m : Name) : ¬ Above m rh := by
  intro h
  cases h with
  | child h' => simp [Name.child] at h'
  | step h' _ => simp [Name.child] at h'

/-- The strict ancestors of a node, explicitly. -/
def ancSet : Name → Finset Name
  | rh => ∅
  | rc => {rh}
  | gv j => {rc, rh}
  | gh j => {gv j, rc, rh}
  | gc j => {gh j, gv j, rc, rh}
  | cv k t => (Finset.univ.filter fun t' : Fin 18 => t < t').image (ci k) ∪
      (Finset.univ.filter fun t' : Fin 18 => t < t').image (ch k) ∪
      (Finset.univ.filter fun t' : Fin 18 => t < t').image (cv k) ∪
      {gc ⟨k / 3, by omega⟩, gh ⟨k / 3, by omega⟩, gv ⟨k / 3, by omega⟩,
        rc, rh}
  | ch k t => (Finset.univ.filter fun t' : Fin 18 => t < t').image (ci k) ∪
      (Finset.univ.filter fun t' : Fin 18 => t < t').image (ch k) ∪
      (Finset.univ.filter fun t' : Fin 18 => t ≤ t').image (cv k) ∪
      {gc ⟨k / 3, by omega⟩, gh ⟨k / 3, by omega⟩, gv ⟨k / 3, by omega⟩,
        rc, rh}
  | ci k t => (Finset.univ.filter fun t' : Fin 18 => t < t').image (ci k) ∪
      (Finset.univ.filter fun t' : Fin 18 => t ≤ t').image (ch k) ∪
      (Finset.univ.filter fun t' : Fin 18 => t ≤ t').image (cv k) ∪
      {gc ⟨k / 3, by omega⟩, gh ⟨k / 3, by omega⟩, gv ⟨k / 3, by omega⟩,
        rc, rh}
  | src k => Finset.univ.image (ci k) ∪ Finset.univ.image (ch k) ∪ Finset.univ.image (cv k) ∪
      {gc ⟨k / 3, by omega⟩, gh ⟨k / 3, by omega⟩, gv ⟨k / 3, by omega⟩,
        rc, rh}

theorem child_eq_none {n : Name} (h : child n = none) : n = rh := by
  cases n <;> simp only [Name.child, reduceCtorEq] at h <;> try rfl
  split_ifs at h

theorem filter_lt_succ (t : Fin 18) (ht : t.val < 17) :
    Finset.univ.filter (fun t' : Fin 18 => t < t') =
      insert (⟨t.val + 1, by omega⟩ : Fin 18)
        (Finset.univ.filter (fun t' : Fin 18 => (⟨t.val + 1, by omega⟩ : Fin 18) < t')) := by
  ext t'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
    Fin.ext_iff]
  omega

theorem filter_lt_eq_filter_le (t : Fin 18) (ht : t.val < 17) :
    Finset.univ.filter (fun t' : Fin 18 => t < t') =
      Finset.univ.filter (fun t' : Fin 18 => (⟨t.val + 1, by omega⟩ : Fin 18) ≤ t') := by
  ext t'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]
  omega

theorem filter_le_eq_insert (t : Fin 18) :
    Finset.univ.filter (fun t' : Fin 18 => t ≤ t') =
      insert t (Finset.univ.filter (fun t' : Fin 18 => t < t')) := by
  ext t'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.le_def,
    Fin.lt_def, Fin.ext_iff]
  omega

theorem filter_lt_17 : Finset.univ.filter (fun t' : Fin 18 => (17 : Fin 18) < t') = ∅ :=
  Finset.filter_eq_empty_iff.mpr fun t' _ => not_lt.mpr (Fin.le_last t')

theorem univ_eq_insert_zero :
    (Finset.univ : Finset (Fin 18)) =
      insert 0 (Finset.univ.filter (fun t' : Fin 18 => 0 < t')) := by
  ext t'
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff, Fin.lt_def,
    Fin.ext_iff, Fin.val_zero]
  omega

theorem filter_zero_le :
    Finset.univ.filter (fun t' : Fin 18 => (0 : Fin 18) ≤ t') = Finset.univ := by
  simp

theorem ancSet_child {n p : Name} (h : child n = some p) : ancSet n = insert p (ancSet p) := by
  cases n with
  | src k =>
    simp only [Name.child, Option.some.injEq] at h; subst h
    simp only [ancSet]
    rw [show Finset.univ.image (cv k) =
        (Finset.univ.filter (fun t' : Fin 18 => (0 : Fin 18) ≤ t')).image (cv k) from by
      rw [filter_zero_le]]
    rw [show Finset.univ.image (ch k) =
        (Finset.univ.filter (fun t' : Fin 18 => (0 : Fin 18) ≤ t')).image (ch k) from by
      rw [filter_zero_le]]
    rw [show Finset.univ.image (ci k) =
        insert (ci k 0) ((Finset.univ.filter (fun t' : Fin 18 => 0 < t')).image (ci k)) from by
      rw [← Finset.image_insert, ← univ_eq_insert_zero]]
    rw [Finset.insert_union, Finset.insert_union, Finset.insert_union]
  | ci k t =>
    simp only [Name.child, Option.some.injEq] at h; subst h
    simp only [ancSet]
    have hB : (Finset.univ.filter (fun t' : Fin 18 => t ≤ t')).image (ch k) =
        insert (ch k t) ((Finset.univ.filter (fun t' : Fin 18 => t < t')).image (ch k)) := by
      rw [filter_le_eq_insert t, Finset.image_insert]
    rw [hB, Finset.union_insert (ch k t), Finset.insert_union (ch k t),
      Finset.insert_union (ch k t)]
  | ch k t =>
    simp only [Name.child, Option.some.injEq] at h; subst h
    simp only [ancSet]
    have hC : (Finset.univ.filter (fun t' : Fin 18 => t ≤ t')).image (cv k) =
        insert (cv k t) ((Finset.univ.filter (fun t' : Fin 18 => t < t')).image (cv k)) := by
      rw [filter_le_eq_insert t, Finset.image_insert]
    rw [hC, Finset.union_insert (cv k t), Finset.insert_union (cv k t)]
  | cv k t =>
    simp only [Name.child] at h
    split_ifs at h with ht
    · simp only [Option.some.injEq] at h; subst h
      have ht' : t = 17 := Fin.ext ht
      subst ht'
      simp only [ancSet, filter_lt_17, Finset.image_empty, Finset.empty_union]
    · simp only [Option.some.injEq] at h; subst h
      simp only [ancSet]
      rw [show (Finset.univ.filter (fun t' : Fin 18 => t < t')).image (cv k) =
          (Finset.univ.filter
            (fun t' : Fin 18 => (⟨t.val + 1, by omega⟩ : Fin 18) ≤ t')).image (cv k) from by
        rw [filter_lt_eq_filter_le t (by omega)]]
      rw [show (Finset.univ.filter (fun t' : Fin 18 => t < t')).image (ch k) =
          (Finset.univ.filter
            (fun t' : Fin 18 => (⟨t.val + 1, by omega⟩ : Fin 18) ≤ t')).image (ch k) from by
        rw [filter_lt_eq_filter_le t (by omega)]]
      rw [filter_lt_succ t (by omega), Finset.image_insert, Finset.insert_union,
        Finset.insert_union, Finset.insert_union]
  | gc j => simp only [Name.child, Option.some.injEq] at h; subst h; rfl
  | gh j => simp only [Name.child, Option.some.injEq] at h; subst h; rfl
  | gv j => simp only [Name.child, Option.some.injEq] at h; subst h; rfl
  | rc => simp only [Name.child, Option.some.injEq] at h; subst h; simp [ancSet]
  | rh => simp [Name.child] at h

theorem above_iff_mem_ancSet (m n : Name) : Above m n ↔ m ∈ ancSet n := by
  suffices ∀ k, ∀ n, height n = k → (Above m n ↔ m ∈ ancSet n) from this _ n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hn
    rcases hc : child n with _ | p
    · rw [child_eq_none hc]; simp [ancSet, not_above_rh]
    · rw [above_of_child hc, ancSet_child hc, Finset.mem_insert,
        ih (height p) (by rw [← hn, ← height_child hc]; omega) p rfl]

/-- Indices of a set of names. -/
def fins (A : Finset Name) : Finset (Fin N) := A.map nameEquiv.toEmbedding

@[simp] theorem mem_fins (A : Finset Name) (n : Name) : n.fin ∈ fins A ↔ n ∈ A :=
  Finset.mem_map' _

/-- Membership in the parents of a node, in the graph, in terms of `child`. -/
theorem mem_graph_parents_iff (m n : Name) :
    m.fin ∈ (graph.kind n.fin).parents ↔ child m = some n := by
  rw [graph_parents_fin]
  exact (Finset.mem_map' _).trans (Name.mem_parents_iff m n)

/-- Visited nodes are those with no strict ancestor in `A`. -/
theorem visited_iff (A : Finset Name) (n : Name) :
    graph.Visited (fins A) n.fin ↔ ∀ m, Above m n → m ∉ A := by
  constructor
  · intro hv
    have key : ∀ v, graph.Visited (fins A) v → ∀ n : Name, n.fin = v → ∀ m, Above m n → m ∉ A := by
      intro v hv
      induction hv with
      | root =>
        intro n hn m hm
        have hr : n = rh := Name.fin_injective hn
        subst hr
        exact absurd hm (not_above_rh m)
      | parent hw hwA hv ih =>
        rename_i w v
        intro n hn m hm hmA
        subst hn
        obtain ⟨w', rfl⟩ : ∃ w' : Name, w'.fin = w := ⟨ofFin w, fin_ofFin w⟩
        have hc : child n = some w' := (mem_graph_parents_iff n w').mp hv
        rw [above_of_child hc] at hm
        rcases hm with rfl | hm
        · exact hwA ((mem_fins A _).mpr hmA)
        · exact ih w' rfl m hm hmA
    exact key _ hv n rfl
  · suffices ∀ k, ∀ n, height n = k → (∀ m, Above m n → m ∉ A) →
        graph.Visited (fins A) n.fin from this _ n rfl
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n hn hA
      rcases hc : child n with _ | p
      · rw [child_eq_none hc]; exact Graph.Visited.root
      · have hp : p ∉ A := hA p (Above.child hc)
        have hvp : graph.Visited (fins A) p.fin :=
          ih (height p) (by rw [← hn, ← height_child hc]; omega) p rfl
            (fun m hm => hA m ((above_of_child hc).mpr (Or.inr hm)))
        exact Graph.Visited.parent hvp (fun h => hp ((mem_fins A p).mp h))
          ((mem_graph_parents_iff n p).mpr hc)

/-- The nodes evaluated when reconstructing from `A`. -/
def Evaluated (A : Finset Name) (n : Name) : Prop := n ∉ A ∧ ∀ m, Above m n → m ∉ A

theorem mem_evaluated_iff (A : Finset Name) (n : Name) :
    n.fin ∈ graph.evaluated (fins A) ↔ Evaluated A n := by
  have h : ∀ (B : Finset (Fin graph.size)) (v : Fin graph.size),
      v ∈ graph.evaluated B ↔ graph.Visited B v ∧ v ∉ B := by
    intro B v
    unfold Graph.evaluated
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine (h (fins A) n.fin).trans ?_
  constructor
  · rintro ⟨hv, hnA⟩
    exact ⟨fun h => hnA ((mem_fins A n).mpr h), (visited_iff A n).mp hv⟩
  · rintro ⟨hnA, hanc⟩
    exact ⟨(visited_iff A n).mpr hanc, fun h => hnA ((mem_fins A n).mp h)⟩

/-- The evaluated set as a finset of names. -/
def evaluatedSet (A : Finset Name) : Finset Name := Finset.univ.filter (Evaluated A)

theorem evaluated_eq_fins (A : Finset Name) : graph.evaluated (fins A) = fins (evaluatedSet A) := by
  ext v
  obtain ⟨n, rfl⟩ : ∃ n : Name, n.fin = v := ⟨ofFin v, fin_ofFin v⟩
  refine (mem_evaluated_iff A n).trans (Iff.trans ?_ (mem_fins (evaluatedSet A) n).symm)
  simp [evaluatedSet]

/-- Reconstruction cost in tree terms. -/
theorem reconstructCost_eq (A : Finset Name) :
    graph.reconstructCost (fins A) = ∑ n ∈ evaluatedSet A, n.cost := by
  unfold Graph.reconstructCost
  rw [evaluated_eq_fins]
  refine (Finset.sum_map (evaluatedSet A) nameEquiv.toEmbedding graph.nodeCost).trans ?_
  exact Finset.sum_congr rfl fun n _ => graph_nodeCost_fin n

/-- Revealed bits in tree terms. -/
theorem revealBits_eq (A : Finset Name) : graph.revealBits (fins A) = ∑ n ∈ A, n.len := by
  unfold Graph.revealBits
  refine (Finset.sum_map A nameEquiv.toEmbedding graph.len).trans ?_
  exact Finset.sum_congr rfl fun n _ => graph_len_fin n

/-- The condition `Scheme.no_hidden_source` in tree terms: every source path meets `A`. -/
theorem no_hidden_source_iff (A : Finset Name) :
    (∀ v, graph.Visited (fins A) v → v ∉ fins A → ¬ (graph.kind v).IsSource) ↔
      ∀ k, src k ∈ A ∨ ∃ m ∈ A, Above m (src k) := by
  constructor
  · intro h k
    by_contra hk
    push Not at hk
    apply h (src k).fin
    · exact (visited_iff A _).mpr fun m hm hmA => hk.2 m hmA hm
    · exact fun h' => hk.1 ((mem_fins A _).mp h')
    · exact (graph_isSource_fin _).mpr ⟨k, rfl⟩
  · intro h v hv hvA hs
    obtain ⟨n, rfl⟩ : ∃ n : Name, n.fin = v := ⟨ofFin v, fin_ofFin v⟩
    obtain ⟨k, rfl⟩ := (graph_isSource_fin n).mp hs
    have hv' := (visited_iff A _).mp hv
    have hvA' : src k ∉ A := fun h' => hvA ((mem_fins A _).mpr h')
    rcases h k with h1 | ⟨m, hmA, hm⟩
    · exact hvA' h1
    · exact hv' m hm hmA

/-- The hash node whose output is the value of a 129-bit node (none for sources). -/
def hashOf : Name → Option Name
  | cv k t => some (ch k t)
  | gv j => some (gh j)
  | _ => none

theorem child_hashOf {a h : Name} (hh : hashOf a = some h) : child h = some a := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh <;> rfl

theorem hashOf_isSome_iff (a : Name) : (hashOf a).isSome ↔ a.len = 129 ∧ ∀ k, a ≠ src k := by
  cases a <;> simp [hashOf, Name.len]

theorem len_of_hashOf {a p : Name} (hp : hashOf a = some p) : p.len = 256 := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;> rfl

theorem one_le_cost_of_hashOf {a p : Name} (hp : hashOf a = some p) : 1 ≤ p.cost := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp [Name.cost]

/-- A cut: an antichain of 129-bit nodes, other than the root, meeting every source path. -/
structure IsCut (A : Finset Name) : Prop where
  values : ∀ n ∈ A, n.len = 129
  antichain : ∀ n ∈ A, ∀ m, Above m n → m ∉ A
  covers : ∀ k, src k ∈ A ∨ ∃ m ∈ A, Above m (src k)

theorem IsCut.rh_not_mem {A : Finset Name} (h : IsCut A) : rh ∉ A := by
  intro hm
  have := h.values rh hm
  simp [Name.len] at this

/-- The parent hash node of a cut node is not evaluated. -/
theorem IsCut.not_evaluated_hashOf {A : Finset Name} (_hA : IsCut A) {a h : Name} (ha : a ∈ A)
    (hh : hashOf a = some h) : ¬ Evaluated A h :=
  fun he => he.2 a (Above.child (child_hashOf hh)) ha

section

/- Unifying or normalising a hypothesis of the form `p ∈ evaluatedSet A` makes Lean unfold
`Finset.univ : Finset Name` through the `Fintype` instance (3026 elements), which exhausts the
recursion depth; `evaluatedSet` is therefore kept opaque in this section. -/
attribute [local irreducible] evaluatedSet

/-- Distinct cuts of equal cost are incomparable: some node revealed by the first is evaluated
by the second. -/
theorem exists_mem_evaluated_of_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hcost : ∑ n ∈ evaluatedSet A, n.cost = ∑ n ∈ evaluatedSet A', n.cost) (hne : A ≠ A') :
    ∃ v ∈ A, Evaluated A' v := by
  by_contra hcon
  push Not at hcon
  -- every node of `A` is in `A'` or has a strict ancestor in `A'`
  have key : ∀ v ∈ A, v ∈ A' ∨ ∃ m ∈ A', Above m v := by
    intro v hv
    by_contra h
    push Not at h
    exact hcon v hv ⟨h.1, fun m hm hmA' => h.2 m hmA' hm⟩
  -- (i) the evaluated set of `A'` is contained in that of `A`
  have hsub : evaluatedSet A' ⊆ evaluatedSet A := by
    intro n hn
    simp only [evaluatedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hn ⊢
    obtain ⟨hnA', hanc'⟩ := hn
    refine ⟨fun hnA => ?_, fun m hm hmA => ?_⟩
    · rcases key n hnA with h | ⟨m, hmA', hm⟩
      · exact hnA' h
      · exact hanc' m hm hmA'
    · rcases key m hmA with h | ⟨m', hm'A', hm'⟩
      · exact hanc' m hm h
      · exact hanc' m' (hm'.trans hm) hm'A'
  -- (ii) a node of `A'` evaluated at `A`
  have hex : ∃ a ∈ A', Evaluated A a := by
    by_cases hAA' : A ⊆ A'
    · have : ∃ v' ∈ A', v' ∉ A := by
        by_contra h
        push Not at h
        exact hne (Finset.Subset.antisymm hAA' h)
      obtain ⟨v', hv'A', hv'A⟩ := this
      exact ⟨v', hv'A', hv'A, fun m hm hmA => hA'.antichain v' hv'A' m hm (hAA' hmA)⟩
    · rw [Finset.not_subset] at hAA'
      obtain ⟨v, hvA, hvA'⟩ := hAA'
      rcases key v hvA with h | ⟨a', ha'A', ha'⟩
      · exact absurd h hvA'
      · exact ⟨a', ha'A', hA.antichain v hvA a' ha',
          fun m hm hmA => hA.antichain v hvA m (hm.trans ha') hmA⟩
  obtain ⟨a, haA', haE⟩ := hex
  -- `a` is not a source, so it has a hash node `p` above it
  have hns : ∀ k, a ≠ src k := by
    intro k hk
    subst hk
    rcases hA.covers k with h | ⟨m, hmA, hm⟩
    · exact haE.1 h
    · exact haE.2 m hm hmA
  have hsome : (hashOf a).isSome := (hashOf_isSome_iff a).mpr ⟨hA'.values a haA', hns⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hchild : child p = some a := child_hashOf hp
  have hpA : p ∉ A := fun h => by have := hA.values p h; rw [len_of_hashOf hp] at this; omega
  have hpE : Evaluated A p := by
    refine ⟨hpA, fun m hm => ?_⟩
    rw [above_of_child hchild] at hm
    rcases hm with rfl | hm
    · exact haE.1
    · exact haE.2 m hm
  have hpE' : ¬ Evaluated A' p := fun h => h.2 a (Above.child hchild) haA'
  -- (iii) compare the costs
  have hpcost : 1 ≤ p.cost := one_le_cost_of_hashOf hp
  have hpmem : p ∈ evaluatedSet A := by simp [evaluatedSet, hpE]
  have hpnmem : p ∉ evaluatedSet A' := by simp [evaluatedSet, hpE']
  have hsub' : evaluatedSet A' ⊆ (evaluatedSet A).erase p :=
    Finset.subset_erase.mpr ⟨hsub, hpnmem⟩
  have h1 := Finset.sum_le_sum_of_subset (f := fun n : Name => n.cost) hsub'
  have h2 := Finset.sum_erase_add (evaluatedSet A) (fun n : Name => n.cost) hpmem
  omega

end

end WeightedConstruction.WideForest

end OptimalOTS

#print axioms OptimalOTS.WeightedConstruction.WideForest.exists_mem_evaluated_of_ne
#print axioms OptimalOTS.WeightedConstruction.WideForest.reconstructCost_eq
end
end

/- Original module: Submissions.UpperCompressions.WideCuts; SHA256 a2c33ee92ce26e3d08d7d880ebafd44f43ff356d2345d0b60b535a14b250c827. -/
section

/-!
# A single shallow-forest disclosure family

Six of eighteen group digests are disclosed; each of the remaining 36 chains
contributes one word. Chain reconstruction costs sum to 74, twelve group hashes
cost twelve, and the root costs five. This file connects the exact counted
family to the protected graph and proves its 91-compression reconstruction cost.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical
set_option linter.constructorNameAsVariable false
namespace OptimalOTS
open OptimalOTS.Dag
namespace WeightedConstruction.WideForest
open Name ShallowResearch

attribute [local irreducible] ShallowResearch.comp Finset.univ Finset.filter

/-- The group containing a chain. -/
def groupOfChain (k : Fin 54) : Fin 18 := ⟨k / 3, by omega⟩

/-- Chains whose group digest is not disclosed. -/
def active (G : Finset (Fin 18)) : Finset (Fin 54) :=
  Finset.univ.filter fun k => groupOfChain k ∉ G

/-- Position zero reveals a source; positive positions reveal chain outputs. -/
def chainNode (k : Fin 54) (p : Fin 19) : Name :=
  if h : p.val = 0 then src k else cv k ⟨p.val - 1, by omega⟩

/-- Positions of total cost s; inactive positions are fixed to make choices canonical. -/
irreducible_def positions (S : Finset (Fin 54)) (s : ℕ) : Finset (Fin 54 → Fin 19) :=
  Finset.univ.filter fun t => (∀ k ∉ S, t k = 18) ∧ ∑ k ∈ S, (18 - (t k).val) = s

theorem mem_positions (S : Finset (Fin 54)) (s : ℕ) (t : Fin 54 → Fin 19) :
    t ∈ positions S s ↔ (∀ k ∉ S, t k = 18) ∧ ∑ k ∈ S, (18 - (t k).val) = s := by
  rw [positions_def, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

abbrev Choice := Finset (Fin 18) × (Fin 54 → Fin 19)

@[irreducible] def shape (b s : ℕ) : Finset Choice :=
  ((Finset.powersetCard b (Finset.univ : Finset (Fin 18))).sigma fun G =>
    positions (active G) s).image fun x => (x.1, x.2)

@[irreducible] def shapes : Finset Choice := shape 6 74

def cutOf (c : Choice) : Finset Name :=
  c.1.image gv ∪ (active c.1).image fun k => chainNode k (c.2 k)

@[irreducible] def family : Finset (Finset Name) := shapes.image cutOf

theorem mem_shape_iff (b s : ℕ) (c : Choice) :
    c ∈ shape b s ↔ c.1.card = b ∧ c.2 ∈ positions (active c.1) s := by
  unfold shape
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨G, t⟩, hx, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_powersetCard] at hx
    exact ⟨hx.1.2, hx.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨c.1, c.2⟩, ?_, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, h1⟩, h2⟩

theorem mem_shapes_iff (c : Choice) :
    c ∈ shapes ↔ c.1.card = 6 ∧ c.2 ∈ positions (active c.1) 74 := by
  rw [shapes, mem_shape_iff]

theorem groupOfChain_chainOf (j : Fin 18) (a : Fin 3) : groupOfChain (chainOf j a) = j := by
  apply Fin.ext
  simp only [groupOfChain, chainOf]
  omega

theorem chainOf_injective : Function.Injective fun p : Fin 18 × Fin 3 => chainOf p.1 p.2 := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  simp only [chainOf, Fin.mk.injEq] at h
  have hj : j = j' := Fin.ext (by omega)
  have ha : a = a' := Fin.ext (by omega)
  rw [hj, ha]

theorem mem_active_iff (G : Finset (Fin 18)) (k : Fin 54) :
    k ∈ active G ↔ groupOfChain k ∉ G := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]

theorem active_eq_image (G : Finset (Fin 18)) :
    active G = (Gᶜ ×ˢ (Finset.univ : Finset (Fin 3))).image fun p => chainOf p.1 p.2 := by
  ext k
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product, Finset.mem_compl, and_true, Prod.exists]
  constructor
  · intro h
    refine ⟨groupOfChain k, ⟨k % 3, by omega⟩, h, ?_⟩
    apply Fin.ext
    simp only [chainOf, groupOfChain]
    omega
  · rintro ⟨j, a, hj, rfl⟩
    rwa [groupOfChain_chainOf]

theorem card_active (G : Finset (Fin 18)) : (active G).card = 3 * (18 - G.card) := by
  rw [active_eq_image, Finset.card_image_of_injective _ chainOf_injective,
    Finset.card_product, Finset.card_compl, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  omega

theorem card_positions (S : Finset (Fin 54)) (s : ℕ) : (positions S s).card = comp S.card s := by
  rw [← card_comp]
  refine Finset.card_nbij' (fun t i => Fin.rev (t (S.equivFin.symm i)))
    (fun c k => if h : k ∈ S then Fin.rev (c (S.equivFin ⟨k, h⟩)) else 18) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, mem_positions] at ht
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← ht.2, ← Finset.sum_coe_sort S, ← Equiv.sum_comp S.equivFin.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_rev]
    omega
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter] at hc
    rw [Finset.mem_coe, mem_positions]
    refine ⟨fun k hk => dif_neg hk, ?_⟩
    rw [← hc.2, ← Finset.sum_coe_sort S, ← Equiv.sum_comp S.equivFin (fun i => (c i).val)]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [dif_pos x.2]
    simp only [Fin.val_rev, Subtype.coe_eta]
    omega
  · intro t ht
    rw [Finset.mem_coe, mem_positions] at ht
    funext k
    dsimp only
    by_cases hk : k ∈ S
    · simp only [dif_pos hk, Equiv.symm_apply_apply, Fin.rev_rev]
    · rw [dif_neg hk, ht.1 k hk]
  · intro c _
    funext i
    dsimp only
    have h := (S.equivFin.symm i).2
    simp only [dif_pos h, Subtype.coe_eta, Equiv.apply_symm_apply, Fin.rev_rev]

theorem choice_mk_injective :
    Function.Injective fun x : (_ : Finset (Fin 18)) × (Fin 54 → Fin 19) =>
      ((x.1, x.2) : Choice) := by
  rintro ⟨G, t⟩ ⟨G', t'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem card_shape (b s : ℕ) :
    (shape b s).card = Nat.choose 18 b * comp (3 * (18 - b)) s := by
  unfold shape
  rw [Finset.card_image_of_injective _ choice_mk_injective, Finset.card_sigma]
  have h : ∀ G ∈ Finset.powersetCard b (Finset.univ : Finset (Fin 18)),
      (positions (active G) s).card = comp (3 * (18 - b)) s := by
    intro G hG
    rw [Finset.mem_powersetCard] at hG
    rw [card_positions, card_active, hG.2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem chainNode_eq_src_iff (k k' : Fin 54) (p : Fin 19) :
    chainNode k p = src k' ↔ k = k' ∧ p = 0 := by
  unfold chainNode
  split_ifs with h
  · simp only [Name.src.injEq, Fin.ext_iff, Fin.val_zero, h, and_true]
  · simp only [false_iff, not_and, Fin.ext_iff, Fin.val_zero]
    intro _ hp
    exact h hp

theorem chainNode_eq_cv_iff (k k' : Fin 54) (p : Fin 19) (t : Fin 18) :
    chainNode k p = cv k' t ↔ k = k' ∧ p.val = t.val + 1 := by
  unfold chainNode
  split_ifs with h
  · simp only [false_iff, not_and]
    intro _
    omega
  · simp only [Name.cv.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨hk, hp⟩
      exact ⟨hk, by omega⟩
    · rintro ⟨hk, hp⟩
      exact ⟨hk, by omega⟩

theorem chainNode_ne_gv (k : Fin 54) (p : Fin 19) (j : Fin 18) : chainNode k p ≠ gv j := by
  unfold chainNode
  split_ifs <;> simp

theorem chainNode_len (k : Fin 54) (p : Fin 19) : (chainNode k p).len = 129 := by
  unfold chainNode
  split_ifs <;> rfl

theorem chainNode_injective (t : Fin 54 → Fin 19) :
    Function.Injective fun k => chainNode k (t k) := by
  intro k k' h
  unfold chainNode at h
  dsimp only at h
  split_ifs at h <;> simp only [Name.src.injEq, Name.cv.injEq] at h <;> tauto

theorem mem_cutOf_iff (c : Choice) (n : Name) :
    n ∈ cutOf c ↔ (∃ j ∈ c.1, gv j = n) ∨
      ∃ k ∈ active c.1, chainNode k (c.2 k) = n := by
  unfold cutOf
  simp only [Finset.mem_union, Finset.mem_image]

theorem gv_mem_cutOf_iff' (c : Choice) (j : Fin 18) : gv j ∈ cutOf c ↔ j ∈ c.1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨j', hj', h⟩ | ⟨k, _, h⟩)
    · rw [Name.gv.injEq] at h
      exact h ▸ hj'
    · exact absurd h (chainNode_ne_gv _ _ _)
  · intro h
    exact Or.inl ⟨j, h, rfl⟩

theorem src_mem_cutOf_iff' (c : Choice) (k : Fin 54) :
    src k ∈ cutOf c ↔ k ∈ active c.1 ∧ c.2 k = 0 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨j, _, h⟩ | ⟨k', hk', h⟩)
    · exact absurd h (by simp)
    · rw [chainNode_eq_src_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨hk', h⟩
  · rintro ⟨hk, h⟩
    exact Or.inr ⟨k, hk, (chainNode_eq_src_iff _ _ _).mpr ⟨rfl, h⟩⟩

theorem cv_mem_cutOf_iff' (c : Choice) (k : Fin 54) (t : Fin 18) :
    cv k t ∈ cutOf c ↔ k ∈ active c.1 ∧ (c.2 k).val = t.val + 1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨j, _, h⟩ | ⟨k', hk', h⟩)
    · exact absurd h (by simp)
    · rw [chainNode_eq_cv_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨hk', h⟩
  · rintro ⟨hk, h⟩
    exact Or.inr ⟨k, hk, (chainNode_eq_cv_iff _ _ _ _).mpr ⟨rfl, h⟩⟩

theorem not_mem_cutOf_of_len {c : Choice} {n : Name} (hn : n.len ≠ 129) : n ∉ cutOf c := by
  intro h
  rw [mem_cutOf_iff] at h
  rcases h with ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
  · exact hn rfl
  · exact hn (chainNode_len _ _)

theorem mem_cutOf_len' {c : Choice} {n : Name} (hn : n ∈ cutOf c) : n.len = 129 := by
  by_contra h
  exact not_mem_cutOf_of_len h hn

theorem ci_not_mem_cutOf (c : Choice) (k : Fin 54) (t : Fin 18) : ci k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem ch_not_mem_cutOf (c : Choice) (k : Fin 54) (t : Fin 18) : ch k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem gc_not_mem_cutOf (c : Choice) (j : Fin 18) : gc j ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem gh_not_mem_cutOf (c : Choice) (j : Fin 18) : gh j ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem pos_of_mem_shapes {c : Choice} (hc : c ∈ shapes) :
    ∀ k ∉ active c.1, c.2 k = 18 :=
  ((mem_positions _ _ _).mp ((mem_shapes_iff c).mp hc).2).1

/-- The canonical choice is determined by its disclosure set. -/
theorem cutOf_injective : Set.InjOn cutOf shapes := by
  intro c hc c' hc' h
  rw [Finset.mem_coe] at hc hc'
  have hG : c.1 = c'.1 := by
    ext j
    rw [← gv_mem_cutOf_iff' c j, ← gv_mem_cutOf_iff' c' j, h]
  have ht : c.2 = c'.2 := by
    funext k
    by_cases hk : k ∈ active c.1
    · have hmem : chainNode k (c.2 k) ∈ cutOf c' := by
        rw [← h, mem_cutOf_iff]
        exact Or.inr ⟨k, hk, rfl⟩
      unfold chainNode at hmem
      split_ifs at hmem with h0
      · rw [src_mem_cutOf_iff'] at hmem
        rw [hmem.2]
        exact Fin.ext h0
      · rw [cv_mem_cutOf_iff'] at hmem
        apply Fin.ext
        rw [hmem.2]
        dsimp only
        omega
    · rw [pos_of_mem_shapes hc k hk, pos_of_mem_shapes hc' k (by rwa [← hG])]
  exact Prod.ext hG ht

/-- The graph cut family realizes the previously certified coefficient exactly. -/
theorem card_family_eq : family.card = Nat.choose 18 6 * comp 36 74 := by
  have hn : 3 * (18 - 6) = 36 := by norm_num
  have he : comp (3 * (18 - 6)) 74 = comp 36 74 := congrArg (fun n => comp n 74) hn
  calc
    family.card = shapes.card := by
      unfold family
      exact Finset.card_image_of_injOn cutOf_injective
    _ = Nat.choose 18 6 * comp (3 * (18 - 6)) 74 := by
      unfold shapes
      exact card_shape 6 74
    _ = Nat.choose 18 6 * comp 36 74 := congrArg (fun v => Nat.choose 18 6 * v) he

/-- Capacity is separated from the expensive exact coefficient certificate. -/
theorem card_family_of_bound {m : ℕ} (hm : m ≤ Nat.choose 18 6 * comp 36 74) :
    m ≤ family.card := hm.trans_eq card_family_eq.symm

theorem forall_above_of_child {A : Finset Name} {n p : Name} (hp : child n = some p)
    (he : Evaluated A p) : ∀ m, Above m n → m ∉ A := by
  intro m hm
  rw [above_of_child hp] at hm
  rcases hm with rfl | hm
  · exact he.1
  · exact he.2 m hm

theorem evaluated_of_child {A : Finset Name} {n p : Name} (hp : child n = some p) (hn : n ∉ A)
    (he : Evaluated A p) : Evaluated A n :=
  ⟨hn, forall_above_of_child hp he⟩

theorem evaluated_rh' (c : Choice) : Evaluated (cutOf c) rh :=
  ⟨rh_not_mem_cutOf c, fun m hm => absurd hm (not_above_rh m)⟩

theorem evaluated_rc' (c : Choice) : Evaluated (cutOf c) rc :=
  evaluated_of_child rfl (rc_not_mem_cutOf c) (evaluated_rh' c)

theorem evaluated_gh_iff' (c : Choice) (j : Fin 18) :
    Evaluated (cutOf c) (gh j) ↔ j ∉ c.1 := by
  constructor
  · intro h
    rw [← gv_mem_cutOf_iff' c j]
    exact h.2 (gv j) (Above.child rfl)
  · intro hj
    refine evaluated_of_child rfl (gh_not_mem_cutOf c j) ?_
    refine evaluated_of_child rfl ?_ (evaluated_rc' c)
    rw [gv_mem_cutOf_iff']
    exact hj

theorem evaluated_ch_iff' (c : Choice) (k : Fin 54) (t : Fin 18) :
    Evaluated (cutOf c) (ch k t) ↔ k ∈ active c.1 ∧ (c.2 k).val ≤ t.val := by
  unfold Evaluated
  simp only [above_iff_mem_ancSet, ancSet, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert, Finset.mem_singleton,
    forall_eq, ci_not_mem_cutOf, ch_not_mem_cutOf, cv_mem_cutOf_iff', gc_not_mem_cutOf,
    gh_not_mem_cutOf, gv_mem_cutOf_iff', rc_not_mem_cutOf, rh_not_mem_cutOf,
    not_false_eq_true, true_and, and_true, implies_true, mem_active_iff, groupOfChain]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    by_contra hlt
    have hv := (c.2 k).isLt
    exact @h1 ⟨(c.2 k).val - 1, by omega⟩ (by rw [Fin.le_def]; dsimp only; omega)
      ⟨h2, by dsimp only; omega⟩
  · rintro ⟨h2, hle⟩
    refine ⟨fun x hx h => ?_, h2⟩
    rw [Fin.le_def] at hx
    omega

/-- The input of a chain hash is evaluated exactly when the chain hash is. -/
theorem evaluated_ci_iff' (c : Choice) (k : Fin 54) (t : Fin 18) :
    Evaluated (cutOf c) (ci k t) ↔ k ∈ active c.1 ∧ (c.2 k).val ≤ t.val := by
  rw [← evaluated_ch_iff']
  constructor
  · intro h
    exact ⟨ch_not_mem_cutOf c k t, fun m hm => h.2 m (Above.step rfl hm)⟩
  · intro h
    exact evaluated_of_child rfl (ci_not_mem_cutOf c k t) h

theorem child_cv_of_lt (k : Fin 54) (t : Fin 18) (ht : t.val < 17) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]

theorem child_cv_of_eq (k : Fin 54) (t : Fin 18) (ht : t.val = 17) :
    child (cv k t) = some (gc (groupOfChain k)) := by
  simp only [Name.child]
  rw [dif_pos ht]
  rfl

theorem isCut_cutOf (c : Choice) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_len' hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    rcases hn with ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
    · exact forall_above_of_child rfl (evaluated_rc' c)
    · have hk' := (mem_active_iff _ _).mp hk
      unfold chainNode
      split_ifs with h0
      · exact forall_above_of_child rfl
          ((evaluated_ci_iff' c k 0).mpr ⟨hk, by rw [h0]; exact Nat.zero_le _⟩)
      · by_cases h18 : (c.2 k).val = 18
        · refine forall_above_of_child (child_cv_of_eq k _ (by dsimp only; omega))
            (evaluated_of_child rfl (gc_not_mem_cutOf c _) ((evaluated_gh_iff' c _).mpr hk'))
        · have hlt := (c.2 k).isLt
          refine forall_above_of_child (child_cv_of_lt k _ (by dsimp only; omega))
            ((evaluated_ci_iff' c k _).mpr ⟨hk, ?_⟩)
          dsimp only
          omega
  covers := by
    intro k
    by_cases hk : k ∈ active c.1
    · by_cases h0 : (c.2 k).val = 0
      · exact Or.inl ((src_mem_cutOf_iff' c k).mpr ⟨hk, Fin.ext h0⟩)
      · have hlt := (c.2 k).isLt
        refine Or.inr ⟨cv k ⟨(c.2 k).val - 1, by omega⟩,
          (cv_mem_cutOf_iff' c k _).mpr ⟨hk, by dsimp only; omega⟩, ?_⟩
        rw [above_iff_mem_ancSet]
        simp [ancSet]
    · rw [mem_active_iff, not_not] at hk
      refine Or.inr ⟨gv (groupOfChain k), (gv_mem_cutOf_iff' c _).mpr hk, ?_⟩
      rw [above_iff_mem_ancSet]
      simp [ancSet, groupOfChain]

theorem cutOf_disjoint (c : Choice) :
    Disjoint (c.1.image gv) ((active c.1).image fun k => chainNode k (c.2 k)) := by
  apply Finset.disjoint_left.mpr
  intro n hnG hnC
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hnG
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hnC
  exact chainNode_ne_gv k (c.2 k) j hk

theorem card_cutOf {c : Choice} (hc : c ∈ shapes) : (cutOf c).card = 42 := by
  rw [cutOf, Finset.card_union_of_disjoint (cutOf_disjoint c),
    Finset.card_image_of_injective _ (fun _ _ h => Name.gv.inj h),
    Finset.card_image_of_injective _ (chainNode_injective c.2), card_active,
    ((mem_shapes_iff c).mp hc).1]

theorem revealBits_cutOf {c : Choice} (hc : c ∈ shapes) :
    graph.revealBits (fins (cutOf c)) = 42 * 129 := by
  rw [revealBits_eq]
  calc
    ∑ n ∈ cutOf c, n.len = ∑ _n ∈ cutOf c, 129 :=
      Finset.sum_congr rfl fun _ hn => mem_cutOf_len' hn
    _ = 42 * 129 := by rw [Finset.sum_const, smul_eq_mul, card_cutOf hc]

theorem sum_fin18_ge (v : ℕ) : ∑ t : Fin 18, (if v ≤ t.val then 1 else 0) = 18 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 18, ← Finset.card_filter]
  have : (Finset.range 18).filter (fun t => v ≤ t) = Finset.Ico v 18 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

theorem cost_cutOf {c : Choice} (hc : c ∈ shapes) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost = 91 := by
  obtain ⟨hG, ht⟩ := (mem_shapes_iff c).mp hc
  have h_gh : ∑ j, (if Evaluated (cutOf c) (gh j) then 1 else 0) = 12 := by
    simp only [evaluated_gh_iff']
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun j => j ∉ c.1) = c.1ᶜ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    rw [this, Finset.card_compl, Fintype.card_fin, hG]
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) = 74 := by
    simp only [evaluated_ch_iff']
    have hin : ∀ k, ∑ t : Fin 18, (if k ∈ active c.1 ∧ (c.2 k).val ≤ t.val then 1 else 0) =
        if k ∈ active c.1 then 18 - (c.2 k).val else 0 := by
      intro k
      by_cases hk : k ∈ active c.1
      · simp only [hk, true_and, if_true]
        exact sum_fin18_ge _
      · simp only [hk, false_and, if_false, Finset.sum_const_zero]
    simp only [hin]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact ((mem_positions _ _ _).mp ht).2
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh' c), h_ch, h_gh]

theorem reconstructCost_cutOf {c : Choice} (hc : c ∈ shapes) :
    graph.reconstructCost (fins (cutOf c)) = 91 := by
  rw [reconstructCost_eq, cost_cutOf hc]

theorem isCut_of_mem_family {A : Finset Name} (h : A ∈ family) : IsCut A := by
  rw [family, Finset.mem_image] at h
  obtain ⟨c, _, rfl⟩ := h
  exact isCut_cutOf c

theorem card_of_mem_family {A : Finset Name} (h : A ∈ family) : A.card = 42 := by
  rw [family, Finset.mem_image] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact card_cutOf hc

theorem cost_of_mem_family {A : Finset Name} (h : A ∈ family) :
    ∑ n ∈ evaluatedSet A, n.cost = 91 := by
  rw [family, Finset.mem_image] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact cost_cutOf hc

#print axioms card_family_of_bound
#print axioms isCut_of_mem_family
#print axioms card_of_mem_family
#print axioms cost_of_mem_family
#print axioms reconstructCost_cutOf
#print axioms revealBits_cutOf
theorem revealBits_of_mem_family {A : Finset Name} (h : A ∈ family) :
    graph.revealBits (fins A) = 5418 := by
  rw [family, Finset.mem_image] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact revealBits_cutOf hc

theorem reconstruction_of_mem_family {A : Finset Name} (h : A ∈ family) :
    graph.reconstructCost (fins A) = 91 := by
  rw [reconstructCost_eq, cost_of_mem_family h]

theorem disclosure_and_nonce_bits {A : Finset Name} (h : A ∈ family) :
    graph.revealBits (fins A) + 86 = 5504 := by
  rw [revealBits_of_mem_family h]

#print axioms revealBits_of_mem_family
#print axioms reconstruction_of_mem_family
#print axioms disclosure_and_nonce_bits
end WeightedConstruction.WideForest
end OptimalOTS
end
end

/- Original module: Submissions.UpperCompressions.WideCapacity; SHA256 dbf1666e5225db56b631e96ca738b6b8e0ee7a6d80fda81b24b3ae41e5668671. -/
section

namespace OptimalOTS.WeightedConstruction.WideForest

theorem card_family : WeightedResearch92.classes ≤ family.card :=
  card_family_of_bound WeightedResearch92.enough_classes92

theorem card_family_numeric : 770731564938763476110450815401984 ≤ family.card := by
  rw [← WeightedResearch92.classes_exact]
  exact card_family

end OptimalOTS.WeightedConstruction.WideForest

#print axioms OptimalOTS.WeightedConstruction.WideForest.card_family
#print axioms OptimalOTS.WeightedConstruction.WideForest.card_family_numeric
end

/- Original module: Submissions.UpperCompressions.TruncFiber; SHA256 0e52d7786b57cb9e4a090eab935ee502b82ed7d4d74ae27331ff74af95a60434. -/
section

/-! Exact fibers of low-bit truncation, generic in both widths. These finite
bijections support different internal and public-key binding widths. -/

namespace OptimalOTS.WeightedConstruction.TruncFiber

noncomputable section
open scoped Classical

/-- Join fixed low bits with free high bits. -/
def join {n w : ℕ} (hw : w ≤ n) (a : BitVec w) (b : BitVec (n - w)) : BitVec n :=
  (b ++ a).cast (Nat.sub_add_cancel hw)

@[simp] theorem low_join {n w : ℕ} (hw : w ≤ n) (a : BitVec w)
    (b : BitVec (n - w)) : (join hw a b).setWidth w = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [join, BitVec.getLsbD_append, hi]

@[simp] theorem high_join {n w : ℕ} (hw : w ≤ n) (a : BitVec w)
    (b : BitVec (n - w)) : ((join hw a b) >>> w).setWidth (n - w) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hn : ¬ w + i < w := by omega
  simp [join, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hi, hn]

theorem join_high {n w : ℕ} (hw : w ≤ n) {a : BitVec w} (x : BitVec n)
    (hx : x.setWidth w = a) : join hw a ((x >>> w).setWidth (n - w)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hl : i < w
  · have h := congrArg (fun t : BitVec w => t.getLsbD i) hx
    simpa [join, BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hl] using h.symm
  · have hh : i - w < n - w := by omega
    have he : w + (i - w) = i := by omega
    simp [join, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, hl, hh, he]

/-- Truncation leaves exactly the high `n-w` bits free. -/
def fiberEquiv {n w : ℕ} (hw : w ≤ n) (a : BitVec w) :
    {x : BitVec n // x.setWidth w = a} ≃ BitVec (n - w) where
  toFun x := (x.val >>> w).setWidth (n - w)
  invFun b := ⟨join hw a b, low_join hw a b⟩
  left_inv x := Subtype.ext (join_high hw x.val x.property)
  right_inv b := high_join hw a b

theorem card_filter_setWidth {n w : ℕ} (hw : w ≤ n) (a : BitVec w) :
    (Finset.univ.filter fun x : BitVec n => x.setWidth w = a).card = 2 ^ (n - w) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberEquiv hw a), Fintype.card_bitVec]

theorem card_filter_setWidth_le {n w : ℕ} (hw : w ≤ n) (a : BitVec w) :
    (Finset.univ.filter fun x : BitVec n => x.setWidth w = a).card ≤ 2 ^ (n - w) :=
  le_of_eq (card_filter_setWidth hw a)

theorem card_256_128 (a : BitVec 128) :
    (Finset.univ.filter fun x : BitVec 256 => x.setWidth 128 = a).card = 2 ^ 128 :=
  card_filter_setWidth (by omega) a

theorem card_256_129 (a : BitVec 129) :
    (Finset.univ.filter fun x : BitVec 256 => x.setWidth 129 = a).card = 2 ^ 127 :=
  card_filter_setWidth (by omega) a

end
end OptimalOTS.WeightedConstruction.TruncFiber

#print axioms OptimalOTS.WeightedConstruction.TruncFiber.fiberEquiv
#print axioms OptimalOTS.WeightedConstruction.TruncFiber.card_filter_setWidth
#print axioms OptimalOTS.WeightedConstruction.TruncFiber.card_256_128
#print axioms OptimalOTS.WeightedConstruction.TruncFiber.card_256_129
end

/- Original module: Submissions.UpperCompressions.WeightedSchedule; SHA256 f8b83f2f3b34e9975ac95455e2d760af13730b1cc971c6cc93368837d2a6d7e5. -/
section

/-! The concrete mixed72 schedule. Finite equivalences are fixed deterministic
pure computation; only the random oracle supplies the distribution. -/

namespace OptimalOTS.WeightedConstruction.WeightedSchedule

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

abbrev Tier := Fin 72
abbrev population (j : Tier) := WeightedResearch92.tierClasses j.val
abbrev Class := (j : Tier) × Fin (population j)
abbrev multiplicity (c : Class) : ℕ := 2 ^ (c.1.val + 1)
abbrev Alias := (c : Class) × Fin (multiplicity c)
abbrev M := WeightedResearch92.classes
abbrev A := WeightedResearch92.acceptedAliases

theorem card_class : Fintype.card Class = M := by
  simp only [Class, Fintype.card_sigma, Fintype.card_fin]
  unfold M WeightedResearch92.classes
  exact Fin.sum_univ_eq_sum_range _ 72

theorem card_alias : Fintype.card Alias = A := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ c : Class, 2 ^ (c.1.val+1)) = A
  rw [Fintype.sum_sigma]
  have hsum (j : Tier) : (∑ _k : Fin (population j), 2 ^ (j.val+1)) =
      population j * 2 ^ (j.val+1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [hsum]
  unfold A WeightedResearch92.acceptedAliases
  exact Fin.sum_univ_eq_sum_range (fun j => WeightedResearch92.tierClasses j * 2 ^ (j+1)) 72

def classEquiv : Class ≃ Fin M := Fintype.equivFinOfCardEq card_class
def aliasEquiv : Alias ≃ Fin A := Fintype.equivFinOfCardEq card_alias

def tier (i : Fin M) : ℕ := (classEquiv.symm i).1.val

theorem tier_lt (i : Fin M) : tier i < 72 := (classEquiv.symm i).1.isLt

theorem aliases_lt : A < 2 ^ 129 := by
  change WeightedResearch92.acceptedAliases < 2 ^ 129
  rw [WeightedResearch92.aliases_exact]
  norm_num

/-- The accepted prefix is in fixed bijection with aliases. -/
def rawAlias (x : BitVec 129) : Option Alias :=
  if h : x.toNat < A then some (aliasEquiv.symm ⟨x.toNat, h⟩) else none

def rawClass (x : BitVec 129) : Option Class := (rawAlias x).map Sigma.fst

def decodeRaw (x : BitVec 129) : Option (Fin M) := (rawClass x).map classEquiv

def decode (x : BitVec 256) : Option (Fin M) := decodeRaw (x.setWidth 129)

def aliasRaw (a : Alias) : BitVec 129 := BitVec.ofNat 129 (aliasEquiv a).val

theorem aliasRaw_toNat (a : Alias) : (aliasRaw a).toNat = (aliasEquiv a).val := by
  rw [aliasRaw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans (aliasEquiv a).isLt aliases_lt

@[simp] theorem rawAlias_aliasRaw (a : Alias) : rawAlias (aliasRaw a) = some a := by
  simp only [rawAlias, aliasRaw_toNat, dif_pos (aliasEquiv a).isLt]
  rw [Equiv.symm_apply_apply]

theorem aliasRaw_of_rawAlias {x : BitVec 129} {a : Alias} (h : rawAlias x = some a) :
    aliasRaw a = x := by
  unfold rawAlias at h
  split_ifs at h with hx
  · simp only [Option.some.injEq] at h
    rw [← h]
    apply BitVec.eq_of_toNat_eq
    rw [aliasRaw_toNat, Equiv.apply_symm_apply]

/-- The class fiber inside the alias type is its multiplicity coordinate. -/
def aliasFiberEquiv (c : Class) : {a : Alias // a.1 = c} ≃ Fin (multiplicity c) where
  toFun a := a.property ▸ a.val.2
  invFun b := ⟨⟨c, b⟩, rfl⟩
  left_inv := by rintro ⟨⟨d, b⟩, h⟩; cases h; rfl
  right_inv _ := rfl

/-- Decoding preserves exactly the alias fiber of each class. -/
def rawFiberEquiv (c : Class) :
    {x : BitVec 129 // rawClass x = some c} ≃ {a : Alias // a.1 = c} :=
  (Equiv.ofBijective
    (fun a : {a : Alias // a.1 = c} =>
      (⟨aliasRaw a.val, by simp [rawClass, a.property]⟩ :
        {x : BitVec 129 // rawClass x = some c}))
    (by
      constructor
      · intro a b h
        apply Subtype.ext
        have he := congrArg (fun x : {x : BitVec 129 // rawClass x = some c} =>
          rawAlias x.val) h
        simpa using he
      · intro x
        have hx := x.property
        rw [rawClass, Option.map_eq_some_iff] at hx
        obtain ⟨a, ha, hc⟩ := hx
        exact ⟨⟨a, hc⟩, Subtype.ext (aliasRaw_of_rawAlias ha)⟩)).symm

/-- Exact raw129 per-class fiber. -/
theorem rawClass_fiber (c : Class) :
    (Finset.univ.filter fun x : BitVec 129 => rawClass x = some c).card = multiplicity c := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rawFiberEquiv c),
    Fintype.card_congr (aliasFiberEquiv c), Fintype.card_fin]

end
end OptimalOTS.WeightedConstruction.WeightedSchedule

#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.card_class
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.card_alias
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.rawClass_fiber
end

/- Original module: Submissions.UpperCompressions.WideScheme; SHA256 95e4b7098861d2f02a00e05d11a90a0714b3d53ef826f612228fd27c455e1fff. -/
section

/-! Concrete weighted rank74/word129 construction. Correctness and resources
are certified here; signing availability and strong security remain unproved. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000

namespace OptimalOTS.WeightedConstruction.WideForest

open OptimalOTS.Dag
open Name

/-- Select distinct cuts from the certified shallow family. -/
def setsName (i : Fin WeightedSchedule.M) : Finset Name :=
  (family.equivFin.symm (Fin.castLE card_family i)).1

theorem setsName_mem (i : Fin WeightedSchedule.M) : setsName i ∈ family :=
  (family.equivFin.symm (Fin.castLE card_family i)).2

theorem setsName_injective : Function.Injective setsName := by
  intro i j h
  unfold setsName at h
  exact Fin.castLE_injective _ (family.equivFin.symm.injective (Subtype.ext h))

def forestScheme : WeightedScheme.Scheme WeightedSchedule.M where
  graph := graph
  decode := WeightedSchedule.decode
  tier := WeightedSchedule.tier
  sets := fun i => fins (setsName i)
  root_not_mem := by
    intro i
    show rh.fin ∉ fins (setsName i)
    rw [mem_fins]
    exact (isCut_of_mem_family (setsName_mem i)).rh_not_mem
  no_hidden_source := by
    intro i
    exact (no_hidden_source_iff (setsName i)).mpr
      (isCut_of_mem_family (setsName_mem i)).covers
  reveal_le := by
    intro i
    show graph.revealBits (fins (setsName i)) + 86 ≤ 5504
    rw [revealBits_eq, Finset.sum_const_nat
      fun n hn => (isCut_of_mem_family (setsName_mem i)).values n hn]
    have := card_of_mem_family (setsName_mem i)
    omega
  keygen_le := by
    show graph.keygenCost ≤ 1024
    rw [graph_keygenCost]
    norm_num

theorem isCut_setsName (i : Fin WeightedSchedule.M) : IsCut (setsName i) :=
  isCut_of_mem_family (setsName_mem i)

theorem card_setsName (i : Fin WeightedSchedule.M) : (setsName i).card = 42 :=
  card_of_mem_family (setsName_mem i)

theorem cost_setsName (i : Fin WeightedSchedule.M) :
    ∑ n ∈ evaluatedSet (setsName i), n.cost = 91 :=
  cost_of_mem_family (setsName_mem i)

theorem forestScheme_reconstructCost (i : Fin WeightedSchedule.M) :
    forestScheme.graph.reconstructCost (forestScheme.sets i) = 91 := by
  change graph.reconstructCost (fins (setsName i)) = 91
  rw [reconstructCost_eq, cost_setsName]

theorem forestScheme_revealBits (i : Fin WeightedSchedule.M) :
    forestScheme.graph.revealBits (forestScheme.sets i) = 42 * 129 := by
  change graph.revealBits (fins (setsName i)) = 42 * 129
  rw [revealBits_eq, Finset.sum_const_nat fun n hn => (isCut_setsName i).values n hn,
    card_setsName]

theorem forestScheme_keygenCost : forestScheme.graph.keygenCost = 995 :=
  graph_keygenCost

theorem typed_cost : forestScheme.toAlgorithm.VerifyCostAtMost 92 :=
  forestScheme.verifyCost (fun i => (forestScheme_reconstructCost i).le)

theorem typed_correct : forestScheme.toAlgorithm.Correct := forestScheme.correct

theorem typed_signatureSize : forestScheme.toAlgorithm.SignatureSizeAtMost maxSignatureBits :=
  forestScheme.signatureSize

theorem typed_rejectsOversized : forestScheme.toAlgorithm.RejectsOversized maxSignatureBits :=
  forestScheme.rejectsOversized

theorem typed_keygenCost : forestScheme.toAlgorithm.KeygenCostAtMost keygenBudget :=
  forestScheme.keygenCost

theorem typed_signCost : forestScheme.toAlgorithm.SignCostAtMost signBudget :=
  forestScheme.signCost

theorem typed_verifyDeterministic : forestScheme.toAlgorithm.VerifyDeterministic :=
  forestScheme.verifyDeterministic

#print axioms typed_cost
#print axioms typed_correct
#print axioms typed_signatureSize
#print axioms typed_rejectsOversized
#print axioms typed_keygenCost
#print axioms typed_signCost
#print axioms typed_verifyDeterministic

end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.WireAdapter; SHA256 5f8571edee2cc10b011b2380c37ac7cb51f8494551e7de5d24ac7b87aa162626. -/
section

/-! Transfer a typed-signature certificate to the contract's scheme on the encoded bit strings.
Signing outputs the encoding; verification parses a bit string with `decode`. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WireAdapter

variable (S : TypedScheme) (decode : List Bool → S.Signature)

/-- The scheme on bit strings. -/
abbrev scheme : OracleAlgorithm.Scheme where
  SecretKey := S.SecretKey
  keygen := S.keygen
  sign := fun sk m => Option.map S.encodeSignature <$> S.sign sk m
  verify := fun pk m bits => S.verify pk m (decode bits)

def adversary (A : OracleAlgorithm.Adversary) : S.Adversary where
  State := A.State
  choose := A.choose
  forge := fun state signed =>
    (fun pair => (pair.1, decode pair.2)) <$> A.forge state (signed.map S.encodeSignature)

variable (inverse : ∀ σ, decode (S.encodeSignature σ) = σ)
  (canonical : ∀ pk m bits, true ∈ support (S.verify pk m (decode bits)) →
    S.encodeSignature (decode bits) = bits)

include inverse canonical in
theorem experiment_eq (A : OracleAlgorithm.Adversary) :
    OracleAlgorithm.experiment (scheme S decode) A = S.experiment (adversary S decode A) := by
  simp only [OracleAlgorithm.experiment, TypedScheme.experiment, scheme, adversary,
    bind_map_left]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr_of_forall_mem_support
  intro ok hok
  cases ok with
  | false => rfl
  | true =>
    have hc := canonical keys.1 forged.1 forged.2 hok
    congr 1
    cases signed with
    | none => simp
    | some σ =>
      simp only [Option.map_some, Bool.true_and]
      have he : S.encodeSignature σ = forged.2 ↔ σ = decode forged.2 := by
        constructor
        · intro h
          have hd := congrArg decode h
          simpa only [inverse] using hd
        · intro h
          simpa only [h] using hc
      simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, he]

include inverse canonical in
theorem secure (h : S.Secure) : (scheme S decode).Secure := by
  intro A B hB
  rw [experiment_eq S decode inverse canonical A] at hB ⊢
  exact h (adversary S decode A) B hB

include inverse in
theorem correct (h : S.Correct) : (scheme S decode).Correct := by
  unfold TypedScheme.Correct at h
  unfold OracleAlgorithm.Scheme.Correct
  intro message
  rw [← h message]
  congr 1
  simp only [scheme, bind_map_left]
  apply bind_congr
  intro keys
  apply bind_congr
  intro signed
  cases signed <;> simp only [Option.map_none, Option.map_some, inverse]

theorem signingFailure (ε : ℝ≥0∞) (h : S.SigningFailureAtMost ε) :
    (scheme S decode).SigningFailureAtMost ε := by
  intro message
  have original := h message
  simpa only [OracleAlgorithm.Scheme.SigningFailureAtMost, scheme, bind_map_left,
    Option.isNone_map] using original

theorem signatureSize (n : ℕ) (h : S.SignatureSizeAtMost n) :
    (scheme S decode).SignatureSizeAtMost n := by
  intro sk m bits hb
  change some bits ∈ support (Option.map S.encodeSignature <$> S.sign sk m) at hb
  rw [support_map] at hb
  obtain ⟨signed, hs, he⟩ := hb
  cases signed with
  | none => cases he
  | some σ =>
    have equal : S.encodeSignature σ = bits := Option.some.inj he
    rw [← equal]
    exact h sk m σ hs

include canonical in
theorem rejectsOversized (n : ℕ) (h : S.RejectsOversized n) :
    (scheme S decode).RejectsOversized n := by
  intro pk m bits hsize accepted
  have hc := canonical pk m bits accepted
  exact h pk m (decode bits) (by simpa only [hc] using hsize) accepted

include inverse canonical in
theorem admissible (h : S.Admissible (1 / 2 ^ signingFailureBits)) :
    (scheme S decode).Admissible where
  correct := correct S decode inverse h.correct
  verifyDeterministic := fun pk m bits => h.verifyDeterministic pk m (decode bits)
  signingFailure := signingFailure S decode _ h.signingFailure
  signatureSize := signatureSize S decode maxSignatureBits h.signatureSize
  rejectsOversized := rejectsOversized S decode canonical maxSignatureBits h.rejectsOversized
  keygenCost := h.keygenCost
  signCost := fun sk m => AlgorithmCosts.CostAtMost.map (h.signCost sk m) _

theorem verifyCost (c : ℕ) (h : S.VerifyCostAtMost c) : (scheme S decode).VerifyCostAtMost c :=
  fun pk m bits => h pk m (decode bits)

end OptimalOTS.WireAdapter
end
end

/- Original module: Submissions.UpperCompressions.WideWire; SHA256 dcc6c8b5e2a4832efdbe17a441e1ef7b3b7b1f5bd7a335952d78a18fde30c50a. -/
section

/-! The concrete92 research construction on raw bit-string signatures.
All resources and perfect correctness are checked. Signing availability and
strong unforgeability are deliberately absent until their proofs are complete. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000

namespace OptimalOTS.WeightedConstruction.WideWire
open WideForest

abbrev typed := forestScheme.toAlgorithm

def decode (bits : List Bool) : WeightedScheme.Signature := NonceCodec.decode 86 bits

theorem decode_encode (σ : WeightedScheme.Signature) :
    decode (typed.encodeSignature σ) = σ := NonceCodec.decode_encode σ

theorem accepted_payload_positive (pk : PublicKey) (m : Message) (σ : WeightedScheme.Signature)
    (h : true ∈ support (forestScheme.verify pk m σ)) : 0 < σ.2.length := by
  rw [WeightedScheme.Scheme.verify,support_bind] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨w,_,h⟩ := h
  cases hd : forestScheme.decode w with
  | none => simp [hd] at h
  | some i =>
    simp only [hd] at h
    by_cases hlen : σ.2.length = forestScheme.graph.revealBits (forestScheme.sets i)
    · rw [hlen,forestScheme_revealBits]
      norm_num
    · simp [hlen] at h

theorem canonical (pk : PublicKey) (m : Message) (bits : List Bool)
    (h : true ∈ support (typed.verify pk m (decode bits))) :
    typed.encodeSignature (decode bits) = bits := by
  exact NonceCodec.canonical_of_payload_positive
    (accepted_payload_positive pk m (decode bits) h)

def scheme : OracleAlgorithm.Scheme := WireAdapter.scheme typed decode

theorem cost : scheme.VerifyCostAtMost 92 :=
  WireAdapter.verifyCost typed decode 92 typed_cost

theorem correct : scheme.Correct := WireAdapter.correct typed decode decode_encode typed_correct

theorem signatureSize : scheme.SignatureSizeAtMost maxSignatureBits :=
  WireAdapter.signatureSize typed decode maxSignatureBits typed_signatureSize

theorem rejectsOversized : scheme.RejectsOversized maxSignatureBits :=
  WireAdapter.rejectsOversized typed decode canonical maxSignatureBits typed_rejectsOversized

theorem keygenCost : scheme.KeygenCostAtMost keygenBudget := typed_keygenCost

theorem signCost : scheme.SignCostAtMost signBudget :=
  fun sk m => AlgorithmCosts.CostAtMost.map (typed_signCost sk m) _

theorem verifyDeterministic : scheme.VerifyDeterministic :=
  fun pk m bits => typed_verifyDeterministic pk m (decode bits)

#print axioms cost
#print axioms correct
#print axioms signatureSize
#print axioms rejectsOversized
#print axioms keygenCost
#print axioms signCost
#print axioms verifyDeterministic

end OptimalOTS.WeightedConstruction.WideWire
end
end

/- Original module: Submissions.UpperCompressions.WeightedAvailability; SHA256 06bc942965f9e876d8207fa7b16795d09914c293f828eb1f44ba6478824bd6ed. -/
section

/-! Availability of the actual with-replacement loop, retaining shared-oracle
memoization. Cached nonce probability is paid inside the per-trial failure
factor; no additive nonce-collision error is used. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling.Availability

variable {M n : ℕ} {α : Type}

theorem nonce_suffix (m : Message) (η : Nonce n) : (m++η).setWidth n = η := by
  ext j hj
  simp [BitVec.getElem_setWidth,BitVec.getLsbD_append,hj]

theorem nonce_query_inj (m : Message) {η ζ : Nonce n}
    (h : (⟨msgBits+n,m++η⟩ : Query) = ⟨msgBits+n,m++ζ⟩) : η = ζ := by
  have hh := congrArg (fun q : Query => q.2.setWidth n) h
  simpa only [nonce_suffix] using hh

theorem fresh_insert (m : Message) (c : Cache) (tried : Finset (Nonce n))
    (hf : ∀ η ∉ tried, c ⟨msgBits+n,m++η⟩ = none) (η : Nonce n) (w : BitVec hashBits) :
    ∀ ζ ∉ insert η tried, (c.cacheQuery ⟨msgBits+n,m++η⟩ w) ⟨msgBits+n,m++ζ⟩ = none := by
  intro ζ hζ
  have hne : (⟨msgBits+n,m++ζ⟩ : Query) ≠ ⟨msgBits+n,m++η⟩ := by
    intro h
    have he := nonce_query_inj m h
    exact hζ (he ▸ Finset.mem_insert_self η tried)
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hf ζ (fun h => hζ (Finset.mem_insert_of_mem h))

theorem run_hash_fresh {b : ℕ} (u : BitVec b) (c : Cache)
    (h : c ⟨b,u⟩ = none) : run (hash u) c =
      ($ᵗ BitVec hashBits) >>= fun w => pure (w,c.cacheQuery ⟨b,u⟩ w) := by
  unfold hash run
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_none h

theorem uniform_tried (n : ℕ) (tried : Finset (Nonce n)) (a : ℝ≥0∞) :
    E ($ᵗ BitVec n) (fun η => if η ∈ tried then a else 0) =
      (tried.card : ℝ≥0∞) / 2^n * a := by
  rw [E_uniform]
  simp only [mul_ite,mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,
    nsmul_eq_mul,Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat]
  rw [div_eq_mul_inv,mul_assoc]

theorem uniform_miss_plus (n : ℕ) (tried : Finset (Nonce n)) (miss a : ℝ≥0∞) :
    E ($ᵗ BitVec n) (fun η => miss*a + (if η ∈ tried then a else 0)) =
      (miss + (tried.card : ℝ≥0∞)/2^n)*a := by
  rw [E_uniform]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [sum_inv_card_mul]
  have hh := uniform_tried n tried a
  rw [E_uniform] at hh
  rw [hh,add_mul]

theorem none_best (rank : α → ℕ) (a b : Option α) :
    (if (best rank a b).isNone then (1 : ℝ≥0∞) else 0) =
      if a.isNone then (if b.isNone then 1 else 0) else 0 := by
  cases a <;> cases b <;> simp [best]
  split_ifs <;> simp

theorem after_bound (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (k : ℕ) (c : Cache) (η : Nonce n)
    (w : BitVec hashBits) (a : ℝ≥0∞)
    (h : E (run (loop n decode tier m k) c) (fun p => if p.1.isNone then 1 else 0) ≤ a) :
    E (run (loop n decode tier m k) c)
      (fun p => if (best (fun s => tier s.2) (candidate decode η w) p.1).isNone
        then 1 else 0) ≤ if (decode w).isNone then a else 0 := by
  simp_rw [none_best]
  cases hd : decode w with
  | none => simpa [candidate,hd] using h
  | some i => simpa [candidate,hd] using E_const_le (run (loop n decode tier m k) c) 0

/-- A cache with at mosttried.card possibly occupied row slots. -/
theorem loop_failure (n : ℕ) (decode : BitVec hashBits → Option (Fin M))
    (tier : Fin M → ℕ) (m : Message) (L : ℕ) (miss : ℝ≥0∞)
    (hmiss : ∀ a : ℝ≥0∞, E ($ᵗ BitVec hashBits)
      (fun w => if (decode w).isNone then a else 0) ≤ miss*a) :
    ∀ k (tried : Finset (Nonce n)) (c : Cache), tried.card+k ≤ L →
      (∀ η ∉ tried, c ⟨msgBits+n,m++η⟩ = none) →
      E (run (loop n decode tier m k) c) (fun p => if p.1.isNone then 1 else 0) ≤
        (miss + (L : ℝ≥0∞)/2^n)^k := by
  intro k
  induction k with
  | zero => intro tried c _ _; simp [loop,run_pure]
  | succ k ih =>
    intro tried c hL hf
    let a : ℝ≥0∞ := (miss+(L : ℝ≥0∞)/2^n)^k
    have hcard (η : Nonce n) : (insert η tried).card+k ≤ L := by
      have := Finset.card_insert_le η tried
      omega
    have hstep (η : Nonce n) :
        E (run (hash (m++η)) c) (fun q =>
          E (run (loop n decode tier m k) q.2) (fun p =>
            if (best (fun s => tier s.2) (candidate decode η q.1) p.1).isNone then 1 else 0)) ≤
          miss*a + (if η ∈ tried then a else 0) := by
      cases hc : c ⟨msgBits+n,m++η⟩ with
      | none =>
        rw [run_hash_fresh _ c hc,E_bind]
        simp only [E_pure]
        have hpt (w : BitVec hashBits) := after_bound n decode tier m k
          (c.cacheQuery ⟨msgBits+n,m++η⟩ w) η w a
          (ih (insert η tried) _ (hcard η) (fresh_insert m c tried hf η w))
        exact ((E_mono _ hpt).trans (hmiss a)).trans (le_add_right le_rfl)
      | some w =>
        rw [run_hash_cached _ c w hc,E_pure]
        have hη : η ∈ tried := by
          by_contra h
          rw [hf η h] at hc
          cases hc
        have hprev : E (run (loop n decode tier m k) c)
            (fun p => if p.1.isNone then 1 else 0) ≤ a :=
          ih (insert η tried) c (hcard η)
            (fun ζ hζ => hf ζ (fun h => hζ (Finset.mem_insert_of_mem h)))
        have ha := after_bound n decode tier m k c η w a hprev
        have ha' : (if (decode w).isNone then a else 0) ≤ a := by split_ifs <;> simp
        exact (ha.trans ha').trans (by rw [if_pos hη]; exact le_add_left le_rfl)
    rw [run_loop_succ,E_bind]
    simp only [E_bind,E_pure]
    calc
      _ ≤ E ($ᵗ BitVec n) (fun η => miss*a+(if η ∈ tried then a else 0)) := E_mono _ hstep
      _ = (miss+(tried.card : ℝ≥0∞)/2^n)*a := uniform_miss_plus n tried miss a
      _ ≤ (miss+(L : ℝ≥0∞)/2^n)*a := by
        apply mul_le_mul' _ le_rfl
        apply add_le_add le_rfl
        exact ENNReal.div_le_div_right (by exact_mod_cast (show tried.card ≤ L by omega)) _
      _ = _ := by dsimp [a]; rw [pow_succ,mul_comm]

#print axioms loop_failure
end OptimalOTS.WeightedSampling.Availability
end
end

