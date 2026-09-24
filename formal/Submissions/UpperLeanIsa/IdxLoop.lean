import Submissions.UpperLeanIsa.IdxBase

/-!
# The signing loop in index form

Ported from UpperRiscv `SignIdx.lean`. `signIdx M` is the signing loop of the extended message
`M` returning the selected nonce and index instead of the signature; `sign` is its image under
encoding the revealed words (`sign_eq_map`).

The analysis of the loop, started from a cache `d`:

* `run_signIdx_extend`: cache entries at non-index points are irrelevant to the loop;
* `signIdx_support`: every new cache entry is an index entry at an input `M ++ η`; a new
  entry with a valid index is the one that ended the loop;
* the signing bound's vocabulary: `IdxPre d u₁ i` (a pre-existing index entry `u ≠ u₁` has
  index `i`), `SignExt` (the entries added by a run with a given outcome), the valid indices
  `V d` of the cache, and the one-trial facts `signExt_none`, `signExt_cached`, `signExt_fresh`,
  `ind_le_V`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.validSet Params.encQuery

namespace Params

variable (P : Params)

/-- The signing loop, returning the nonce and the index. -/
def signIdxLoop (m : EMessage) : ℕ → Finset Nonce → OracleComp Spec (Option (Nonce × P.Idx))
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp Spec (Fin (fresh.card - 1 + 1)))
      let η : Nonce := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let w ← (liftM (Spec.query (.inr (P.encQuery (m ++ η)))) :
        OracleComp Spec (BitVec hashBits))
      if hi : idxOf w ∈ P.validSet then
        return some (η, ⟨idxOf w, hi⟩)
      else
        signIdxLoop m k (insert η tried)
    else
      pure none

/-- Signing, returning the nonce and the index. -/
def signIdx (m : EMessage) : OracleComp Spec (Option (Nonce × P.Idx)) :=
  P.signIdxLoop m trials ∅

/-- The continuation of the loop after the index answer `w` at nonce `η`. -/
def idxAfterHash (m : EMessage) (k : ℕ) (tried : Finset Nonce) (η : Nonce)
    (w : BitVec hashBits) : OracleComp Spec (Option (Nonce × P.Idx)) :=
  if hi : idxOf w ∈ P.validSet then pure (some (η, ⟨idxOf w, hi⟩))
  else P.signIdxLoop m k (insert η tried)

/-- The body of the loop at nonce `η`: one index query, then stop or recurse. -/
def idxLoopBody (m : EMessage) (k : ℕ) (tried : Finset Nonce) (η : Nonce) :
    OracleComp Spec (Option (Nonce × P.Idx)) :=
  (liftM (Spec.query (.inr (P.encQuery (m ++ η)))) :
      OracleComp Spec (BitVec hashBits)) >>= P.idxAfterHash m k tried η

theorem signIdxLoop_succ (m : EMessage) (k : ℕ) (tried : Finset Nonce)
    (hc : 0 < (Finset.univ \ tried).card) :
    P.signIdxLoop m (k + 1) tried =
      (liftM (Spec.query (.inl ((Finset.univ \ tried).card - 1))) :
          OracleComp Spec (Fin ((Finset.univ \ tried).card - 1 + 1))) >>= fun j =>
        P.idxLoopBody m k tried (nonceOf tried hc j) := by
  rw [signIdxLoop, dif_pos hc, liftM_uniformFin_eq]
  rfl

/-- The signature of the outcome of the loop. -/
def sigOfIdx (sk : SecretKey) (r : Option (Nonce × P.Idx)) : Option (List Bool) :=
  r.map fun r => encode (P.revealed sk (idxWord r.2.val)) r.1

theorem signLoop_eq_map (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce),
      P.signLoop sk m k tried = P.sigOfIdx sk <$> P.signIdxLoop (emsg m sk.pk) k tried := by
  intro k
  induction k with
  | zero => intro tried; simp [signLoop, signIdxLoop, sigOfIdx]
  | succ k ih =>
    intro tried
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signLoop_succ sk m k tried hc, P.signIdxLoop_succ _ k tried hc, map_bind]
      refine bind_congr fun j => ?_
      unfold loopBody idxLoopBody
      rw [P.encQuery_emsg, map_bind]
      refine bind_congr fun w => ?_
      unfold afterHash idxAfterHash
      by_cases hi : idxOf w ∈ P.validSet
      · have ha : P.Accepted (idxAns w) := (P.mem_validSet_iff w).mp hi
        rw [if_pos ha, dif_pos hi, map_pure]
        simp only [sigOfIdx, Option.map_some, idxWord_idxOf]
      · have ha : ¬ P.Accepted (idxAns w) := fun h => hi ((P.mem_validSet_iff w).mpr h)
        rw [if_neg ha, dif_neg hi]
        exact ih _
    · rw [signLoop, signIdxLoop, dif_neg hc, dif_neg hc, map_pure]
      rfl

/-- Signing encodes the revealed words at the index found by `signIdx`. -/
theorem sign_eq_map (sk : SecretKey) (m : Message) :
    P.sign sk m = P.sigOfIdx sk <$> P.signIdx (emsg m sk.pk) := by
  rw [sign_eq]
  exact P.signLoop_eq_map sk m trials ∅

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

/-! ### Non-encoding entries are irrelevant -/

theorem run_signIdxLoop_extend (m : EMessage) (f : Cache)
    (hf : ∀ u : EncInput, f (P.encQuery u) = none) :
    ∀ (k : ℕ) (tried : Finset Nonce) (d : Cache),
      run (P.signIdxLoop m k tried) (Cache.extend d f) =
        (fun p => (p.1, Cache.extend p.2 f)) <$> run (P.signIdxLoop m k tried) d := by
  intro k
  induction k with
  | zero => intro tried d; simp [Params.signIdxLoop, run_pure]
  | succ k ih =>
    intro tried d
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signIdxLoop_succ m k tried hc, run_query_bind, run_query_bind, oracleImpl_run_inl,
        oracleImpl_run_inl]
      simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun j => ?_
      simp only [Params.idxLoopBody]
      rw [run_query_bind, run_query_bind]
      rcases hdq : d (P.encQuery (m ++ nonceOf tried hc j)) with _ | w
      · have hdq' : Cache.extend d f (P.encQuery (m ++ nonceOf tried hc j)) = none := by
          rw [Cache.extend_apply_of_none hdq]; exact hf _
        rw [oracleImpl_run_inr_none hdq, oracleImpl_run_inr_none hdq']
        simp only [bind_assoc, pure_bind, map_bind]
        refine bind_congr fun w => ?_
        rw [← Cache.extend_cacheQuery]
        simp only [Params.idxAfterHash]
        split_ifs with hi
        · simp [run_pure]
        · exact ih _ _
      · have hdq' : Cache.extend d f (P.encQuery (m ++ nonceOf tried hc j)) = some w :=
          Cache.extend_apply_of_some hdq
        rw [oracleImpl_run_inr_some hdq, oracleImpl_run_inr_some hdq', pure_bind, pure_bind]
        simp only [Params.idxAfterHash]
        split_ifs with hi
        · simp [run_pure]
        · exact ih _ _
    · rw [Params.signIdxLoop, dif_neg hc]
      simp [run_pure]

/-- Entries at non-encoding points (queries of another length) are irrelevant to the loop. -/
theorem run_signIdx_extend (m : EMessage) (d f : Cache)
    (hf : ∀ u : EncInput, f (P.encQuery u) = none) :
    run (P.signIdx m) (Cache.extend d f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run (P.signIdx m) d :=
  P.run_signIdxLoop_extend m f hf trials ∅ d

/-! ### The new cache entries -/

theorem signIdxLoop_support (m : EMessage) :
    ∀ (k : ℕ) (tried : Finset Nonce) (d : Cache),
      ∀ p ∈ support (run (P.signIdxLoop m k tried) d),
        Cache.Sub d p.2 ∧
        (∀ q w, d q = none → p.2 q = some w →
          ∃ η : Nonce, q = P.encQuery (m ++ η) ∧
            ∀ hi : idxOf w ∈ P.validSet, p.1 = some (η, ⟨idxOf w, hi⟩)) ∧
        (∀ η i, p.1 = some (η, i) →
          ∃ w, p.2 (P.encQuery (m ++ η)) = some w ∧ idxOf w = i.val) := by
  intro k
  induction k with
  | zero =>
    intro tried d p hp
    rw [Params.signIdxLoop, run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl d, fun q w h1 h2 => ?_, fun η i h => by simp at h⟩
    change d q = some w at h2
    rw [h1] at h2; cases h2
  | succ k ih =>
    intro tried d p hp
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [P.signIdxLoop_succ m k tried hc] at hp
      obtain ⟨j, hp⟩ := mem_support_run_inl hp
      simp only [Params.idxLoopBody] at hp
      generalize nonceOf tried hc j = η at hp
      rcases hdq : d (P.encQuery (m ++ η)) with _ | w
      · obtain ⟨w, hp⟩ := mem_support_run_inr_none hdq hp
        rw [Params.idxAfterHash] at hp
        by_cases hi : idxOf w ∈ P.validSet
        · rw [dif_pos hi, run_pure, support_pure] at hp
          simp only [Set.mem_singleton_iff] at hp
          subst hp
          refine ⟨Cache.sub_cacheQuery_of_none hdq w, ?_, ?_⟩
          · intro q w' h1 h2
            change (d.cacheQuery (P.encQuery (m ++ η)) w) q = some w' at h2
            by_cases hq : q = P.encQuery (m ++ η)
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
          obtain ⟨h1, h2, h3⟩ := ih (insert η tried) (d.cacheQuery (P.encQuery (m ++ η)) w) p hp
          refine ⟨(Cache.sub_cacheQuery_of_none hdq w).trans h1, ?_, h3⟩
          intro q w' hq1 hq2
          by_cases hq : q = P.encQuery (m ++ η)
          · subst hq
            have : p.2 (P.encQuery (m ++ η)) = some w :=
              h1 _ _ (QueryCache.cacheQuery_self _ _ _)
            rw [this] at hq2
            obtain rfl := Option.some.inj hq2
            exact ⟨η, rfl, fun hi' => absurd hi' hi⟩
          · exact h2 q w' (by rw [QueryCache.cacheQuery_of_ne _ _ hq]; exact hq1) hq2
      · have hp := mem_support_run_inr_some hdq hp
        rw [Params.idxAfterHash] at hp
        by_cases hi : idxOf w ∈ P.validSet
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
    · rw [Params.signIdxLoop, dif_neg hc, run_pure, support_pure] at hp
      simp only [Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨Cache.Sub.refl d, fun q w h1 h2 => ?_, fun η i h => by simp at h⟩
      change d q = some w at h2
      rw [h1] at h2; cases h2

/-- The new cache entries of the loop. -/
theorem signIdx_support (m : EMessage) (d : Cache) :
    ∀ p ∈ support (run (P.signIdx m) d),
      Cache.Sub d p.2 ∧
      (∀ q w, d q = none → p.2 q = some w →
        ∃ η : Nonce, q = P.encQuery (m ++ η) ∧
          ∀ hi : idxOf w ∈ P.validSet, p.1 = some (η, ⟨idxOf w, hi⟩)) ∧
      (∀ η i, p.1 = some (η, i) → ∃ w, p.2 (P.encQuery (m ++ η)) = some w ∧ idxOf w = i.val) :=
  P.signIdxLoop_support m trials ∅ d

/-! ### The signing bound -/

/-- A pre-existing encoding entry other than `u₁` has index `i`. -/
def IdxPre (d : Cache) (u₁ : EncInput) (i : ℕ) : Prop :=
  ∃ u, u ≠ u₁ ∧ ∃ w, d (P.encQuery u) = some w ∧ idxOf w = i

/-- `Φ` does not see encoding entries: the entries at queries of length `emsgBits + 128`. -/
def EncInvariant (Φ : Cache → ℝ≥0∞) : Prop :=
  ∀ (c : Cache) (u : EncInput) (w : BitVec hashBits),
    Φ (c.cacheQuery (P.encQuery u) w) = Φ c

/-- `d'` extends `d` by the entries of a signing run with outcome `r`. -/
def SignExt (m : EMessage) (d : Cache) (r : Option (Nonce × P.Idx)) (d' : Cache) :
    Prop :=
  Cache.Sub d d' ∧
  (∀ q w, d q = none → d' q = some w →
    ∃ η : Nonce, q = P.encQuery (m ++ η) ∧
      ∀ hi : idxOf w ∈ P.validSet, r = some (η, ⟨idxOf w, hi⟩)) ∧
  (∀ η i, r = some (η, i) → ∃ w, d' (P.encQuery (m ++ η)) = some w ∧ idxOf w = i.val)

/-- The encoding inputs cached with a valid index. -/
def validInputs (d : Cache) : Finset (EncInput) :=
  Finset.univ.filter fun u : EncInput => ∃ w, d (P.encQuery u) = some w ∧ idxOf w ∈ P.validSet

/-- The index of an optional answer (`0` for none). Defined by pattern matching so that the
kernel reduces it before unfolding `idxOf`. -/
def idxOfOpt : Option (BitVec hashBits) → ℕ
  | some w => idxOf w
  | none => 0

theorem idxOfOpt_some (w : BitVec hashBits) : idxOfOpt (some w) = idxOf w := rfl

/-- The valid indices of the entries of `d`. -/
def V (d : Cache) : Finset ℕ :=
  (P.validInputs d).image fun u => idxOfOpt (d (P.encQuery u))

theorem mem_validInputs {d : Cache} {u : EncInput} :
    u ∈ P.validInputs d ↔ ∃ w, d (P.encQuery u) = some w ∧ idxOf w ∈ P.validSet := by
  unfold Params.validInputs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_V {d : Cache} {u : EncInput} {w : BitVec hashBits}
    (hu : d (P.encQuery u) = some w) (hw : idxOf w ∈ P.validSet) : idxOf w ∈ P.V d := by
  refine Finset.mem_image.2 ⟨u, ?_, ?_⟩
  · exact P.mem_validInputs.2 ⟨w, hu, hw⟩
  · rw [hu, idxOfOpt_some]

theorem V_lt (d : Cache) : ∀ n ∈ P.V d, n < 2 ^ 127 := by
  intro n hn
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hn
  obtain ⟨w, hw, -⟩ := (P.mem_validInputs).1 hu
  rw [hw, idxOfOpt_some]
  exact idxOf_lt w

theorem E_query_unif (n : ℕ) (g : Fin (n + 1) → ℝ≥0∞) :
    E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) g =
      ∑ j, ((n : ℝ≥0∞) + 1)⁻¹ * g j := by
  rw [E, expectedValue_def, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact ProbComp.probOutput_uniformFin n j

theorem cache_eq_of_notMem {d d' : Cache} {m : EMessage} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = P.encQuery (m ++ η) ∧ ¬ idxOf w ∈ P.validSet)
    {η : Nonce} (hη : η ∉ tried) :
    d' (P.encQuery (m ++ η)) = d (P.encQuery (m ++ η)) := by
  rcases hdq : d (P.encQuery (m ++ η)) with _ | w
  · rcases hd'q : d' (P.encQuery (m ++ η)) with _ | w'
    · rfl
    · obtain ⟨η', hη', he, -⟩ := hNew _ _ hdq hd'q
      exact absurd (by rw [append_nonce_inj m (P.encQuery_inj he)]; exact hη') hη
  · exact hSub _ _ hdq

theorem new_cacheQuery {d d' : Cache} {m : EMessage} {tried : Finset Nonce}
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = P.encQuery (m ++ η) ∧ ¬ idxOf w ∈ P.validSet)
    (η : Nonce) {w : BitVec hashBits} (hw : ¬ idxOf w ∈ P.validSet) :
    ∀ q w', d q = none → (d'.cacheQuery (P.encQuery (m ++ η)) w) q = some w' →
      ∃ η' ∈ insert η tried, q = P.encQuery (m ++ η') ∧ ¬ idxOf w' ∈ P.validSet := by
  intro q w' h1 h2
  by_cases hq : q = P.encQuery (m ++ η)
  · subst hq
    rw [QueryCache.cacheQuery_self] at h2
    obtain rfl := Option.some.inj h2
    exact ⟨η, Finset.mem_insert_self _ _, rfl, hw⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hq] at h2
    obtain ⟨η', hη', he, hi⟩ := hNew q w' h1 h2
    exact ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem new_insert {d d' : Cache} {m : EMessage} {tried : Finset Nonce}
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = P.encQuery (m ++ η) ∧ ¬ idxOf w ∈ P.validSet)
    (η : Nonce) :
    ∀ q w, d q = none → d' q = some w →
      ∃ η' ∈ insert η tried, q = P.encQuery (m ++ η') ∧ ¬ idxOf w ∈ P.validSet :=
  fun q w h1 h2 =>
    let ⟨η', hη', he, hi⟩ := hNew q w h1 h2
    ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem signExt_none {d d' : Cache} {m : EMessage} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = P.encQuery (m ++ η) ∧ ¬ idxOf w ∈ P.validSet) :
    P.SignExt m d none d' := by
  unfold Params.SignExt
  refine ⟨hSub, fun q w h1 h2 => ?_, fun η i h => by cases h⟩
  obtain ⟨η, -, he, hi⟩ := hNew q w h1 h2
  exact ⟨η, he, fun hi' => absurd hi' hi⟩

theorem signExt_cached {d d' : Cache} {m : EMessage} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = P.encQuery (m ++ η) ∧ ¬ idxOf w ∈ P.validSet)
    {η : Nonce} {w : BitVec hashBits} (hi : idxOf w ∈ P.validSet)
    (hq : d' (P.encQuery (m ++ η)) = some w) :
    P.SignExt m d (some (η, ⟨idxOf w, hi⟩)) d' := by
  unfold Params.SignExt
  refine ⟨hSub, fun q w' h1 h2 => ?_, fun η' i h => ?_⟩
  · obtain ⟨η', -, he, hi'⟩ := hNew q w' h1 h2
    exact ⟨η', he, fun h => absurd h hi'⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, hq, rfl⟩

theorem signExt_fresh {d d' : Cache} {m : EMessage} {tried : Finset Nonce}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = P.encQuery (m ++ η) ∧ ¬ idxOf w ∈ P.validSet)
    {η : Nonce} {w : BitVec hashBits} (hi : idxOf w ∈ P.validSet)
    (hq : d' (P.encQuery (m ++ η)) = none) :
    P.SignExt m d (some (η, ⟨idxOf w, hi⟩)) (d'.cacheQuery (P.encQuery (m ++ η)) w) := by
  unfold Params.SignExt
  refine ⟨hSub.trans (Cache.sub_cacheQuery_of_none hq w), fun q w' h1 h2 => ?_,
    fun η' i h => ?_⟩
  · by_cases hqe : q = P.encQuery (m ++ η)
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

theorem ind_le_V {d : Cache} {m : EMessage} {η : Nonce} {w : BitVec hashBits}
    (hi : idxOf w ∈ P.validSet) :
    (if ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × P.Idx)) = some (η', i) ∧
        P.IdxPre d (m ++ η') i.val then (1 : ℝ≥0∞) else 0) ≤
      if idxOf w ∈ P.V d then 1 else 0 := by
  by_cases h1 : ∃ η' i, (some (η, ⟨idxOf w, hi⟩) : Option (Nonce × P.Idx)) =
      some (η', i) ∧ P.IdxPre d (m ++ η') i.val
  · rw [if_pos h1]
    obtain ⟨η', i, he, hpre⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨u, -, w', hu, hw'⟩ := hpre
    have hw'' : idxOf w' = idxOf w := hw'
    have := P.mem_V hu (by rw [hw'']; exact hi)
    rw [hw''] at this
    rw [if_pos this]
  · rw [if_neg h1]; exact zero_le

theorem not_exists_none {d : Cache} {m : EMessage} :
    ¬ ∃ (η : Nonce) (i : P.Idx),
      (none : Option (Nonce × P.Idx)) = some (η, i) ∧ P.IdxPre d (m ++ η) i.val := by
  rintro ⟨_, _, h, _⟩
  cases h


end Params

end OptimalOTS.LeanIsaBaseline.Layer
