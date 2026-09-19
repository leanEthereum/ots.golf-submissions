import Submissions.UpperRiscv.Master
import Submissions.UpperRiscv.GScheme

/-!
# The signing loop

`signIdx m` is the signing loop returning the selected nonce and index instead of the
signature; `GScheme.sign` is its image under encoding the revealed values.

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
    ℕ → Finset Nonce → OracleComp Spec (Option (Nonce × Idx))
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp Spec (Fin (fresh.card - 1 + 1)))
      let η : Nonce := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let i ← index m η
      if hi : i ∈ validSet then
        return some (η, ⟨i, hi⟩)
      else
        signIdxLoop m k (insert η tried)
    else
      pure none

/-- Signing, returning the nonce and the index. -/
def signIdx (m : Message) : OracleComp Spec (Option (Nonce × Idx)) :=
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
    (w : BitVec hashBits) : OracleComp Spec (Option (Nonce × Idx)) :=
  if hi : idxOf w ∈ validSet then pure (some (η, ⟨idxOf w, hi⟩))
  else signIdxLoop m k (insert η tried)

/-- The body of the loop at nonce `η`: one encoding query, then stop or recurse. -/
def loopBody (m : Message) (k : ℕ) (tried : Finset Nonce) (η : Nonce) :
    OracleComp Spec (Option (Nonce × Idx)) :=
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

/-! ### `GScheme.sign` as the image of `signIdx` -/

theorem signLoop_eq_map (S : GScheme) (x : S.graph.Assignment) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce),
      S.signLoop x m k tried =
        (Option.map fun r : Nonce × Idx => (r.1, S.graph.encode (S.sets r.2) x)) <$>
          signIdxLoop m k tried := by
  intro k
  induction k with
  | zero => intro tried; simp [GScheme.signLoop, signIdxLoop]
  | succ k ih =>
    intro tried
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [GScheme.signLoop, signIdxLoop, dif_pos hc, dif_pos hc]
      simp only [map_bind]
      refine bind_congr fun j => ?_
      refine bind_congr fun i => ?_
      split_ifs with hi
      · simp
      · exact ih _
    · rw [GScheme.signLoop, signIdxLoop, dif_neg hc, dif_neg hc]
      simp

/-- `GScheme.sign` encodes the revealed values of the index found by `signIdx`. -/
theorem sign_eq_map (S : GScheme) (x : S.graph.Assignment) (m : Message) :
    S.sign x m =
      (Option.map fun r : Nonce × Idx => (r.1, S.graph.encode (S.sets r.2) x)) <$>
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
            ∀ hi : idxOf w ∈ validSet, p.1 = some (η, ⟨idxOf w, hi⟩)) ∧
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
        by_cases hi : idxOf w ∈ validSet
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
        by_cases hi : idxOf w ∈ validSet
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
          ∀ hi : idxOf w ∈ validSet, p.1 = some (η, ⟨idxOf w, hi⟩)) ∧
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
def SignExt (m : Message) (d : Cache) (r : Option (Nonce × Idx)) (d' : Cache) :
    Prop :=
  Cache.Sub d d' ∧
  (∀ q w, d q = none → d' q = some w →
    ∃ η : Nonce, q = encQuery (m ++ η) ∧
      ∀ hi : idxOf w ∈ validSet, r = some (η, ⟨idxOf w, hi⟩)) ∧
  (∀ η i, r = some (η, i) → ∃ w, d' (encQuery (m ++ η)) = some w ∧ idxOf w = i.val)

/-- The encoding inputs cached with a valid index. -/
def validInputs (d : Cache) : Finset (EncInput) :=
  Finset.univ.filter fun u : EncInput => ∃ w, d (encQuery u) = some w ∧ idxOf w ∈ validSet

/-- The valid indices of the entries of `d`. -/
def V (d : Cache) : Finset ℕ :=
  (validInputs d).image fun u => ((d (encQuery u)).map (idxOf)).getD 0

theorem mem_V {d : Cache} {u : EncInput} {w : BitVec hashBits}
    (hu : d (encQuery u) = some w) (hw : idxOf w ∈ validSet) : idxOf w ∈ V d := by
  refine Finset.mem_image.2 ⟨u, ?_, ?_⟩
  · simp only [validInputs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hu, hw⟩
  · simp [hu]

theorem V_lt (d : Cache) : ∀ n ∈ V d, n < 2 ^ idxBits := by
  intro n hn
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hn
  simp only [validInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
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
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w ∈ validSet)
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
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w ∈ validSet)
    (η : Nonce) {w : BitVec hashBits} (hw : ¬ idxOf w ∈ validSet) :
    ∀ q w', d q = none → (d'.cacheQuery (encQuery (m ++ η)) w) q = some w' →
      ∃ η' ∈ insert η tried, q = encQuery (m ++ η') ∧ ¬ idxOf w' ∈ validSet := by
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
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w ∈ validSet)
    (η : Nonce) :
    ∀ q w, d q = none → d' q = some w →
      ∃ η' ∈ insert η tried, q = encQuery (m ++ η') ∧ ¬ idxOf w ∈ validSet :=
  fun q w h1 h2 =>
    let ⟨η', hη', he, hi⟩ := hNew q w h1 h2
    ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem signExt_none {d d' : Cache} {m : Message} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w ∈ validSet) :
    SignExt m d none d' := by
  unfold SignExt
  refine ⟨hSub, fun q w h1 h2 => ?_, fun η i h => by cases h⟩
  obtain ⟨η, -, he, hi⟩ := hNew q w h1 h2
  exact ⟨η, he, fun hi' => absurd hi' hi⟩

theorem signExt_cached {d d' : Cache} {m : Message} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w ∈ validSet)
    {η : Nonce} {w : BitVec hashBits} (hi : idxOf w ∈ validSet)
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
      ∃ η ∈ tried, q = encQuery (m ++ η) ∧ ¬ idxOf w ∈ validSet)
    {η : Nonce} {w : BitVec hashBits} (hi : idxOf w ∈ validSet)
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
    (hi : idxOf w ∈ validSet) :
    (if ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × Idx)) = some (η', i) ∧
        IdxPre d (m ++ η') i.val then (1 : ℝ≥0∞) else 0) ≤
      if idxOf w ∈ V d then 1 else 0 := by
  by_cases h1 : ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × Idx)) =
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
    ¬ ∃ (η : Nonce) (i : Idx),
      (none : Option (Nonce × Idx)) = some (η, i) ∧ IdxPre d (m ++ η) i.val := by
  rintro ⟨_, _, h, _⟩
  cases h

end OptimalOTS
