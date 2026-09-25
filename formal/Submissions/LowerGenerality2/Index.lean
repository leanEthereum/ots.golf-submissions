import Submissions.LowerGenerality2.Expectation

/-! The signing loop, its returned index and the cache entries it creates.
All queries use the bare oracle; freshness is a property of the cache. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem costAtMost_query_bind_iff {α : Type} (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (b : ℕ) :
    CostAtMost (liftM (Spec.query t) >>= k) b ↔
      queryCost t ≤ b ∧ ∀ u, CostAtMost (k u) (b - queryCost t) := by
  unfold CostAtMost
  rw [isQueryBound_query_bind_iff]


/-! ## Index extraction and finite sums -/

namespace Analysis

lemma setWidth_append_nonce (m : Message) (η : Nonce) :
    (m ++ η).setWidth nonceBits = η := by
  ext j hj
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_append, hj]

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



/-- An encoding input. -/
abbrev EncInput := BitVec (msgBits + nonceBits)

/-- The encoding query at input `u`, represented by its length and bits. A node query may
use exactly the same string; freshness must be proved from the cache. -/
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

end OptimalOTS
