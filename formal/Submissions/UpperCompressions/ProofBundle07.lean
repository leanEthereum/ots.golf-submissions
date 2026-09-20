import Submissions.UpperCompressions.ProofBundle04
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import Submissions.UpperCompressions.ProofBundle06
import Submissions.UpperCompressions.ProofBundle00

/- Original module: Submissions.UpperCompressions.ReplacementPreload; SHA256 1cfc3861eb6e1698b5efcaaa8688010680d6000c941c0878bc5fc96801fc0238. -/
section

/-! Exact finite-subset eager preloading for the protected shared-cache oracle.
All executions still use `OptimalOTS.run` and its original `oracleImpl`; inputs
outside the distinguished subset are neither split off nor resampled separately. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementPreload_1 {α : Type*} : DecidableEq α := Classical.decEq α

/-- A finite set of distinguished query coordinates. Distinct queries cannot
name the same coordinate; unused coordinates are harmless. -/
structure QuerySlice (D : Type) where
  locate : Query → Option D
  unique : ∀ {q q' : Query} {d : D}, locate q = some d → locate q' = some d → q = q'

namespace QuerySlice

def tableCache {D : Type} (S : QuerySlice D) (g : D → BitVec hashBits) : Cache :=
  fun q => g <$> S.locate q

def preload {D : Type} (S : QuerySlice D) (c : Cache) (g : D → BitVec hashBits) : Cache :=
  Cache.extend c (S.tableCache g)

theorem preload_some {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (y : BitVec hashBits) (hc : c q = some y) :
    S.preload c g q = some y := by simp [preload, Cache.extend, hc]

theorem preload_outside {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (hq : S.locate q = none) :
    S.preload c g q = c q := by simp [preload, Cache.extend, tableCache, hq]

theorem preload_fresh_inside {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (d : D)
    (hc : c q = none) (hq : S.locate q = some d) :
    S.preload c g q = some (g d) := by simp [preload, Cache.extend, tableCache, hc, hq]

theorem preload_cacheQuery {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (y : BitVec hashBits) :
    S.preload (c.cacheQuery q y) g = (S.preload c g).cacheQuery q y :=
  Cache.extend_cacheQuery c (S.tableCache g) q y

theorem preload_update_of_none {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (d : D) (y : BitVec hashBits)
    (hc : c q = none) (hq : S.locate q = some d) :
    S.preload (c.cacheQuery q y) g = S.preload c (Function.update g d y) := by
  funext q'
  by_cases hqq : q' = q
  · subst q'
    simp [preload, Cache.extend, tableCache, hc, hq]
  · simp only [preload, Cache.extend, QueryCache.cacheQuery_of_ne _ _ hqq]
    apply congrArg (fun x => (c q').or x)
    cases hx : S.locate q' with
    | none => simp [tableCache, hx]
    | some d' =>
      have hdd : d' ≠ d := by
        intro hd
        subst d'
        exact hqq (S.unique hx hq)
      simp [tableCache, hx, Function.update_of_ne hdd]

end QuerySlice

theorem E_independent_swap {α β : Type} (p : ProbComp α) (q : ProbComp β)
    (f : α → β → ℝ≥0∞) :
    E p (fun a => E q (fun b => f a b)) = E q (fun b => E p (fun a => f a b)) := by
  simp only [E, expectedValue_def, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

theorem E_uniform_constant (α : Type) [SampleableType α] (c : ℝ≥0∞) :
    E ($ᵗ α) (fun _ => c) = c :=
  expectedValue_const (by simp) c

/-- Eager-table marginalization from the existing VCVio theorem, expressed as an
expectation identity usable with arbitrary probabilistic continuations. -/
theorem E_uniform_update {D : Type} [Fintype D] [SampleableType (D → BitVec hashBits)]
    (d : D) (f : (D → BitVec hashBits) → ℝ≥0∞) :
    E ($ᵗ BitVec hashBits) (fun y => E ($ᵗ (D → BitVec hashBits))
      (fun g => f (Function.update g d y))) = E ($ᵗ (D → BitVec hashBits)) f := by
  have hd := OracleComp.evalSPMF_uniformSample_bind_update_map
    (R := BitVec hashBits) d (fun g : D → BitVec hashBits => g)
  have he : E (do
      let y ← $ᵗ BitVec hashBits
      let g ← $ᵗ (D → BitVec hashBits)
      pure (Function.update g d y)) f = E ($ᵗ (D → BitVec hashBits)) f := by
    apply expectedValue_congr
    intro g
    simp only [probOutput_def]
    simpa only [bind_pure] using congrArg (fun p : SPMF (D → BitVec hashBits) => p g) hd
  simpa only [E_bind, E_pure] using he

abbrev outE {α : Type} (oa : OracleComp Spec α) (c : Cache) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  E (run oa c) (fun p => f p.1)

theorem outE_pure {α : Type} (a : α) (c : Cache) (f : α → ℝ≥0∞) :
    outE (pure a) c f = f a := by rw [outE, run_pure, E_pure]

theorem outE_unif {α : Type} (n : ℕ) (k : Spec.Range (.inl n) → OracleComp Spec α)
    (c : Cache) (f : α → ℝ≥0∞) :
    outE (liftM (Spec.query (.inl n)) >>= k) c f =
      E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) (fun a => outE (k a) c f) := by
  simp only [outE, run_query_bind, oracleImpl_run_inl, E_bind, E_pure]

theorem outE_hash_none {α : Type} (q : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (f : α → ℝ≥0∞)
    (hc : c q = none) :
    outE (liftM (Spec.query (.inr q)) >>= k) c f =
      E ($ᵗ BitVec hashBits) (fun y => outE (k y) (c.cacheQuery q y) f) := by
  simp only [outE, run_query_bind, oracleImpl_run_inr_none hc, E_bind, E_pure]

theorem outE_hash_some {α : Type} (q : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (f : α → ℝ≥0∞)
    (y : BitVec hashBits) (hc : c q = some y) :
    outE (liftM (Spec.query (.inr q)) >>= k) c f = outE (k y) c f := by
  simp only [outE, run_query_bind, oracleImpl_run_inr_some hc, pure_bind]

/-- Exact hybrid lazy/eager equivalence for any distinguished finite query subset.
Only the subset is preloaded. The computation and every other query still run
through the original protected shared-cache interpreter. The final cache is
hidden; this theorem equates every payoff of the actual program's output. -/
theorem outE_finite_preload {D α : Type} [Fintype D]
    [SampleableType (D → BitVec hashBits)] (S : QuerySlice D)
    (oa : OracleComp Spec α) (c : Cache) (f : α → ℝ≥0∞) :
    outE oa c f = E ($ᵗ (D → BitVec hashBits)) (fun g => outE oa (S.preload c g) f) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [outE_pure]
    exact (E_uniform_constant _ _).symm
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [outE_unif]
      calc
        _ = E (HasQuery.query (spec := unifSpec) (m := ProbComp) n)
            (fun a => E ($ᵗ (D → BitVec hashBits))
              (fun g => outE (k a) (S.preload c g) f)) := by
          congr 1
          funext a
          exact ih a c
        _ = E ($ᵗ (D → BitVec hashBits))
            (fun g => E (HasQuery.query (spec := unifSpec) (m := ProbComp) n)
              (fun a => outE (k a) (S.preload c g) f)) := E_independent_swap _ _ _
        _ = _ := by
          congr 1
          funext g
          rw [outE_unif]
    | inr q =>
      cases hc : c q with
      | some y =>
        rw [outE_hash_some q k c f y hc]
        calc
          _ = E ($ᵗ (D → BitVec hashBits)) (fun g => outE (k y) (S.preload c g) f) := ih y c
          _ = _ := by
            congr 1
            funext g
            rw [outE_hash_some q k (S.preload c g) f y (S.preload_some c g q y hc)]
      | none =>
        rw [outE_hash_none q k c f hc]
        cases hq : S.locate q with
        | none =>
          calc
            _ = E ($ᵗ BitVec hashBits) (fun y => E ($ᵗ (D → BitVec hashBits))
                (fun g => outE (k y) (S.preload (c.cacheQuery q y) g) f)) := by
              congr 1
              funext y
              exact ih y (c.cacheQuery q y)
            _ = E ($ᵗ (D → BitVec hashBits)) (fun g => E ($ᵗ BitVec hashBits)
                (fun y => outE (k y) (S.preload (c.cacheQuery q y) g) f)) :=
              E_independent_swap _ _ _
            _ = _ := by
              congr 1
              funext g
              have hg : S.preload c g q = none := (S.preload_outside c g q hq).trans hc
              rw [outE_hash_none q k (S.preload c g) f hg]
              congr 1
              funext y
              rw [S.preload_cacheQuery]
        | some d =>
          let ψ : (D → BitVec hashBits) → ℝ≥0∞ :=
            fun g => outE (k (g d)) (S.preload c g) f
          have he (y : BitVec hashBits) (g : D → BitVec hashBits) :
              outE (k y) (S.preload (c.cacheQuery q y) g) f = ψ (Function.update g d y) := by
            dsimp only [ψ]
            rw [Function.update_self, S.preload_update_of_none c g q d y hc hq]
          calc
            _ = E ($ᵗ BitVec hashBits) (fun y => E ($ᵗ (D → BitVec hashBits))
                (fun g => ψ (Function.update g d y))) := by
              congr 1
              funext y
              rw [ih y (c.cacheQuery q y)]
              congr 1
              funext g
              exact he y g
            _ = E ($ᵗ (D → BitVec hashBits)) ψ := E_uniform_update d ψ
            _ = _ := by
              congr 1
              funext g
              exact (outE_hash_some q k (S.preload c g) f (g d)
                (S.preload_fresh_inside c g q d hc hq)).symm

#print axioms QuerySlice.preload_update_of_none
#print axioms E_uniform_update
#print axioms outE_finite_preload

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementLengthSlice; SHA256 b6525a01a927467c2466c020541118b60c42e6f8c45927bae38b809579dfa433. -/
section

/-! Concrete eager preloading of exactly one hash-input length. Length 342 is the
256-bit message plus 86-bit nonce domain. Other lengths keep the original cache. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS

namespace WeightedReplacement

noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementLengthSlice_1 {α : Type*} : DecidableEq α := Classical.decEq α

def queryAtLength (b : ℕ) (q : Query) : Option (BitVec b) :=
  if h : q.1 = b then some (h ▸ q.2) else none

theorem queryAtLength_mk (b : ℕ) (x : BitVec b) :
    queryAtLength b ⟨b,x⟩ = some x := by simp [queryAtLength]

theorem queryAtLength_eq_some_iff (b : ℕ) (q : Query) (x : BitVec b) :
    queryAtLength b q = some x ↔ q = ⟨b,x⟩ := by
  constructor
  · intro hq
    rcases q with ⟨n,y⟩
    by_cases hn : n = b
    · subst n
      have hy : y = x := by simpa [queryAtLength] using hq
      subst y
      rfl
    · simp [queryAtLength, hn] at hq
  · rintro rfl
    exact queryAtLength_mk b x

def lengthSlice (b : ℕ) : QuerySlice (BitVec b) where
  locate := queryAtLength b
  unique := by
    intro q q' x hq hq'
    exact ((queryAtLength_eq_some_iff b q x).mp hq).trans
      ((queryAtLength_eq_some_iff b q' x).mp hq').symm

theorem lengthSlice_outside (b : ℕ) (g : BitVec b → BitVec hashBits)
    (q : Query) (hq : q.1 ≠ b) : (lengthSlice b).tableCache g q = none := by
  simp [QuerySlice.tableCache, lengthSlice, queryAtLength, hq]

theorem lengthSlice_inside (b : ℕ) (g : BitVec b → BitVec hashBits) (x : BitVec b) :
    (lengthSlice b).tableCache g ⟨b,x⟩ = some (g x) := by
  simp [QuerySlice.tableCache, lengthSlice, queryAtLength]

theorem outE_length_preload {α : Type} (b : ℕ) (oa : OracleComp Spec α)
    (c : Cache) (f : α → ℝ≥0∞) :
    outE oa c f = E ($ᵗ (BitVec b → BitVec hashBits))
      (fun g => outE oa ((lengthSlice b).preload c g) f) :=
  outE_finite_preload (lengthSlice b) oa c f

/-- Exact full 342-bit index-table averaging in the original shared random oracle. -/
theorem outE_index342_preload {α : Type} (oa : OracleComp Spec α)
    (c : Cache) (f : α → ℝ≥0∞) :
    outE oa c f = E ($ᵗ (BitVec 342 → BitVec hashBits))
      (fun g => outE oa ((lengthSlice 342).preload c g) f) :=
  outE_length_preload 342 oa c f

/-- Even after eager preloading, all other input lengths keep their exact cache entries. -/
theorem preload_index342_outside (c : Cache) (g : BitVec 342 → BitVec hashBits)
    (q : Query) (hq : q.1 ≠ 342) : (lengthSlice 342).preload c g q = c q := by
  apply QuerySlice.preload_outside
  simp [lengthSlice, queryAtLength, hq]

#print axioms outE_length_preload
#print axioms outE_index342_preload
#print axioms preload_index342_outside

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementEagerPrefix; SHA256 06607df8dfa372d74ba37b0e9ecc526cb479b845880c70c5caf4f3db507d1828. -/
section

/-! Averaging the actual first-exposure bound over the finite eager index table.
Initial cache entries retain priority. The distinguished input is required to
be absent before signing; signer-private visits are then handled by preloading. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance (priority := 100000) stagedLocal_ReplacementEagerPrefix_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

theorem E_left_mul {α : Type} (p : ProbComp α) (a : ℝ≥0∞) (f : α → ℝ≥0∞) :
    E p (fun x => a*f x) = a*E p f := by
  simpa only [mul_comm] using expectedValue_mul_const p f a

theorem preload_update_overwrite {D : Type} (S : QuerySlice D) (c : Cache)
    (g : D → BitVec hashBits) (q : Query) (d : D) (y : BitVec hashBits)
    (hc : c q = none) (hq : S.locate q = some d) :
    S.preload c (Function.update g d y) = overwrite (S.preload c g) q y := by
  funext r
  by_cases hr : r = q
  · subst r
    simp [overwrite, Function.update, QuerySlice.preload, Cache.extend, QuerySlice.tableCache, hc, hq]
  · have ho : overwrite (S.preload c g) q y r = S.preload c g r := by
      simp [overwrite, Function.update, hr, Ne.symm hr]
    rw [ho]
    unfold QuerySlice.preload Cache.extend QuerySlice.tableCache
    cases hrd : S.locate r with
    | none => simp [hrd]
    | some d' =>
      have hdd : d' ≠ d := by
        intro hd
        subst d'
        exact hr (S.unique hrd hq)
      simp [hrd, Function.update, hdd, Ne.symm hdd]

theorem E_preload_resampling {D : Type} [Fintype D] [SampleableType (D → BitVec hashBits)]
    (S : QuerySlice D) (c : Cache) (q : Query) (d : D)
    (hc : c q = none) (hq : S.locate q = some d)
    (F : BitVec hashBits → Cache → ℝ≥0∞) :
    E ($ᵗ (D → BitVec hashBits)) (fun g => E ($ᵗ BitVec hashBits)
      (fun y => F y (overwrite (S.preload c g) q y))) =
    E ($ᵗ (D → BitVec hashBits)) (fun g => F (g d) (S.preload c g)) := by
  rw [E_independent_swap]
  let ψ : (D → BitVec hashBits) → ℝ≥0∞ := fun g => F (g d) (S.preload c g)
  have he (y : BitVec hashBits) (g : D → BitVec hashBits) :
      F y (overwrite (S.preload c g) q y) = ψ (Function.update g d y) := by
    dsimp only [ψ]
    rw [Function.update_self, preload_update_overwrite S c g q d y hc hq]
  simp_rw [he]
  exact E_uniform_update d ψ

def cachedRow (n : ℕ) (m : Message) (c : Cache)
    (g : BitVec (msgBits+n) → BitVec hashBits) : Nonce n → BitVec hashBits :=
  fun η => (c ⟨msgBits+n,m++η⟩).getD (g (m++η))

theorem length_preload_row (n : ℕ) (m : Message) (c : Cache)
    (g : BitVec (msgBits+n) → BitVec hashBits) :
    ∀ η, (lengthSlice (msgBits+n)).preload c g ⟨msgBits+n,m++η⟩ =
      some (cachedRow n m c g η) := by
  intro η
  unfold QuerySlice.preload
  rw [Cache.extend_apply, lengthSlice_inside]
  cases hc : c ⟨msgBits+n,m++η⟩ <;> simp [cachedRow, hc]

theorem E_resampledActualPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (u : Nonce n) (c : Cache)
    (hc : c ⟨msgBits+n,m++u⟩ = none)
    (F : BitVec hashBits → (Option (Winner n M) × (Option α × PublicTrace)) → ℝ≥0∞) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (resampledActualPrefix n decode tier m k post u ((lengthSlice (msgBits+n)).preload c g))
        (fun r => F r.1 r.2)) =
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
        ((lengthSlice (msgBits+n)).preload c g)) (F (g (m++u)))) := by
  simp only [resampledActualPrefix, E_bind, E_pure]
  exact E_preload_resampling (lengthSlice (msgBits+n)) c ⟨msgBits+n,m++u⟩ (m++u) hc
    (queryAtLength_mk _ _) (fun y d => E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩ d) (F y))

/-- The class posterior inequality under the actual uniformly preloaded finite
table, for every fixed pre-sign cache and adaptive public continuation. Input u
may be visited privately by signing, but has no pre-sign public cache entry. -/
theorem eager_prefix_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c : Cache) (post : Option (Winner n M) → OracleComp Spec α)
    (u v : Nonce n) (i : Fin M) (hvu : v ≠ u) (hc : c ⟨msgBits+n,m++u⟩ = none)
    (event : Option α × PublicTrace → Prop) (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
        ((lengthSlice (msgBits+n)).preload c g))
        (fun r => if decode (g (m++u)) = some i ∧ r.1 = some (v,i) ∧ event r.2 then 1 else 0)) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m++u⟩
            ((lengthSlice (msgBits+n)).preload c g))
            (fun r => if r.1 = some (v,i) ∧ event r.2 then 1 else 0)) := by
  have hpoint (g : BitVec (msgBits+n) → BitVec hashBits) :=
    actual_prefix_class_bound n decode tier m k (cachedRow n m c g)
      ((lengthSlice (msgBits+n)).preload c g) (length_preload_row n m c g)
      post u v i hvu event hmass
  have h := E_mono ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) hpoint
  rw [E_left_mul] at h
  have hn := E_resampledActualPrefix n decode tier m k post u c hc
    (fun y r => if decode y = some i ∧ r.1 = some (v,i) ∧ event r.2 then 1 else 0)
  have hd := E_resampledActualPrefix n decode tier m k post u c hc
    (fun _ r => if r.1 = some (v,i) ∧ event r.2 then 1 else 0)
  rw [hn, hd] at h
  exact h

#print axioms E_preload_resampling
#print axioms eager_prefix_class_bound

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementCrossRow; SHA256 f03bc86007c4c98fcde93bb4fae93053dcaedb280ef2487f6e7553fad510ef07. -/
section

/-! A publicly unexposed coordinate in another message row is unaffected by
the signing likelihood. Its joint post-sign class rate is the original prior. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance (priority := 100000) stagedLocal_ReplacementCrossRow_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def resampledQueryPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (q : Query) (c : Cache) :
    ProbComp (BitVec hashBits × Option (Winner n M) × (Option α × PublicTrace)) := do
  let y ← $ᵗ BitVec hashBits
  let r ← actualSignedPrefix n decode tier m k post q (overwrite c q y)
  pure (y,r)

theorem overwrite_other_row (n : ℕ) (m : Message) (table : Nonce n → BitVec hashBits)
    (c : Cache) (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (q : Query) (hq : ∀ η : Nonce n, (⟨msgBits+n,m++η⟩ : Query) ≠ q) (y : BitVec hashBits) :
    ∀ η, overwrite c q y ⟨msgBits+n,m++η⟩ = some (table η) := by
  intro η
  simpa [overwrite, Function.update, hq η] using hc η

theorem other_row_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (post : Option (Winner n M) → OracleComp Spec α) (q : Query)
    (hq : ∀ η : Nonce n, (⟨msgBits+n,m++η⟩ : Query) ≠ q)
    (v : Nonce n) (i : Fin M) (event : Option α × PublicTrace → Prop) :
    E (resampledQueryPrefix n decode tier m k post q c)
      (fun r => if decode r.1 = some i ∧ r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i)) *
        E (resampledQueryPrefix n decode tier m k post q c)
          (fun r => if r.2.1 = some (v,i) ∧ event r.2.2 then 1 else 0) := by
  have heq : resampledQueryPrefix n decode tier m k post q c =
      resampledSignedPrefix (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c q y)) post q c := by
    unfold resampledQueryPrefix resampledSignedPrefix
    apply bind_congr
    intro y
    rw [actualSignedPrefix_fixed_row n decode tier m k table (overwrite c q y)
      (overwrite_other_row n m table c hc q hq y)]
  rw [heq]
  let base := E (Prod.fst <$> run (loop n decode tier m k) c) (fun b => if b = some (v,i) then 1 else 0)
  let μ := base.toReal
  have hμ : 0 ≤ μ := ENNReal.toReal_nonneg
  have hbase : ENNReal.ofReal μ = base := by
    apply ENNReal.ofReal_toReal
    exact ne_of_lt (lt_of_le_of_lt (E_le_one _ (fun _ => by split_ifs <;> simp)) (by simp))
  have hp : ∀ y, E (Prod.fst <$> run (loop n decode tier m k) (overwrite c q y))
      (fun b => if b = some (v,i) then 1 else 0) = ENNReal.ofReal μ := by
    intro y
    rw [hbase]
    dsimp only [base]
    rw [run_loop_fixed_row n decode tier m table (overwrite c q y)
      (overwrite_other_row n m table c hc q hq y) k, run_loop_fixed_row n decode tier m table c hc k]
    simp only [E_map]
  have hrate : 0 ≤ fraction (fun y => decode y = some i) := by
    unfold fraction uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)
  have hb : uniformMean (fun y => if decode y = some i then μ else 0) ≤
      fraction (fun y => decode y = some i)*uniformMean (fun _ : BitVec hashBits => μ) := by
    rw [uniformMean_gate, uniformMean_const]
  have hh := resampledSignedPrefix_bound
    (fun y => Prod.fst <$> run (loop n decode tier m k) (overwrite c q y))
    post (some (v,i)) q c event (fun y => decode y = some i) (fun _ => μ) _
    (fun _ => hμ) hrate hp hb
  convert hh using 1

theorem different_message_rows (n : ℕ) (m m' : Message) (hne : m ≠ m') (u : Nonce n) :
    ∀ η : Nonce n, (⟨msgBits+n,m++η⟩ : Query) ≠ ⟨msgBits+n,m'++u⟩ := by
  intro η h
  apply hne
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hh := congrArg (fun q : Query => q.2.getLsbD (j+n)) h
  simpa only [BitVec.getLsbD_append, Nat.not_lt.mpr (Nat.le_add_left n j), if_false, Nat.add_sub_cancel] using hh

theorem E_resampledQueryPrefix {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (post : Option (Winner n M) → OracleComp Spec α) (x : BitVec (msgBits+n)) (c : Cache)
    (hc : c ⟨msgBits+n,x⟩ = none)
    (F : BitVec hashBits → (Option (Winner n M) × (Option α × PublicTrace)) → ℝ≥0∞) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (resampledQueryPrefix n decode tier m k post ⟨msgBits+n,x⟩ ((lengthSlice (msgBits+n)).preload c g))
        (fun r => F r.1 r.2)) =
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,x⟩
        ((lengthSlice (msgBits+n)).preload c g)) (F (g x))) := by
  simp only [resampledQueryPrefix, E_bind, E_pure]
  exact E_preload_resampling (lengthSlice (msgBits+n)) c ⟨msgBits+n,x⟩ x hc
    (queryAtLength_mk _ _) (fun y d => E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,x⟩ d) (F y))

/-- Different message rows have the ordinary prior class rate. No nonce
inequality is imposed: the two messages already distinguish the hash inputs. -/
theorem eager_cross_row_class_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m m' : Message) (k : ℕ)
    (c : Cache) (post : Option (Winner n M) → OracleComp Spec α)
    (u v : Nonce n) (i : Fin M) (hmm : m ≠ m') (hc : c ⟨msgBits+n,m'++u⟩ = none)
    (event : Option α × PublicTrace → Prop) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m'++u⟩
        ((lengthSlice (msgBits+n)).preload c g))
        (fun r => if decode (g (m'++u)) = some i ∧ r.1 = some (v,i) ∧ event r.2 then 1 else 0)) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          E (actualSignedPrefix n decode tier m k post ⟨msgBits+n,m'++u⟩
            ((lengthSlice (msgBits+n)).preload c g))
            (fun r => if r.1 = some (v,i) ∧ event r.2 then 1 else 0)) := by
  have hpoint (g : BitVec (msgBits+n) → BitVec hashBits) :=
    other_row_class_bound n decode tier m k (cachedRow n m c g)
      ((lengthSlice (msgBits+n)).preload c g) (length_preload_row n m c g)
      post ⟨msgBits+n,m'++u⟩ (different_message_rows n m m' hmm u) v i event
  have h := E_mono ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) hpoint
  rw [E_left_mul] at h
  have hn := E_resampledQueryPrefix n decode tier m k post (m'++u) c hc
    (fun y r => if decode y = some i ∧ r.1 = some (v,i) ∧ event r.2 then 1 else 0)
  have hd := E_resampledQueryPrefix n decode tier m k post (m'++u) c hc
    (fun _ r => if r.1 = some (v,i) ∧ event r.2 then 1 else 0)
  rw [hn, hd] at h
  exact h

#print axioms other_row_class_bound
#print axioms eager_cross_row_class_bound

end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementFreshIndex; SHA256 557de86208c99fa9e9c3b64e757103e316b6cd3ddf2133b397aa7271c2d247c1. -/
section

/-! The actual all-L signer and adaptive forge/verify continuation satisfy a
joint fresh-index bound. Public freshness is measured before signing, so private
signing queries, including accepted nonwinners, do not invalidate the theorem. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementFreshIndex_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def indexInput (n : ℕ) (d : Message × Nonce n) : Query := ⟨msgBits+n,d.1++d.2⟩

def freshAlternative (n : ℕ) (c : Cache) (signed d : Message × Nonce n) : Prop :=
  c (indexInput n d) = none ∧ d ≠ signed

def isIndexLength (b : ℕ) : Spec.Domain → Prop
  | .inl _ => False
  | .inr q => q.1 = b

theorem indexInput_injective (n : ℕ) : Function.Injective (indexInput n) := by
  rintro ⟨m,u⟩ ⟨m',u'⟩ h
  have hmm : m = m' := by
    by_contra hne
    exact different_message_rows n m m' hne u' u h
  subst m'
  have huu : u = u' := rowQuery_injective n m h
  subst u'
  rfl

theorem indexInput_paid (n : ℕ) (d : Message × Nonce n) :
    1 ≤ queryCost (.inr (indexInput n d)) := le_max_left _ _

theorem class_prior_le_posterior {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (i : Fin M)
    (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    fraction (fun y => decode y = some i) ≤
      fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode) := by
  have hp : 0 ≤ fraction (fun y => decode y = some i) := by
    unfold fraction uniformMean
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Nat.cast_nonneg _)
  have hw : fraction (weakRank tier i ∘ decode) ≤ 1 := by
    unfold fraction
    calc
      _ ≤ uniformMean (fun _ : BitVec hashBits => (1:ℝ)) :=
        uniformMean_mono _ _ (fun _ => by split_ifs <;> norm_num)
      _ = _ := uniformMean_const 1
  exact (le_div_iff₀ hmass).2 ((mul_le_mul_of_nonneg_left hw hp).trans_eq (mul_one _))

/-- Every eligible public target, in the signing row or any other message row,
has the required joint first-exposure rate under the actual finite full table. -/
theorem eager_fresh_hit_bound {M : ℕ} {α : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c : Cache) (post : Option (Winner n M) → OracleComp Spec α)
    (v : Nonce n) (i : Fin M) (d : Message × Nonce n)
    (hd : freshAlternative n c (m,v) d)
    (hmass : 0 < fraction (weakRank tier i ∘ decode)) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      if decode (g (d.1++d.2)) = some i then
        signedHit (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
          post (some (v,i)) (indexInput n d) else 0) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          signedHit (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
            post (some (v,i)) (indexInput n d)) := by
  simp_rw [signedHit_actual_gate, signedHit_actual_eq]
  obtain ⟨m',u⟩ := d
  by_cases hmm : m = m'
  · subst m'
    have hvu : v ≠ u := by
      intro h
      exact hd.2 (by simp [h])
    exact eager_prefix_class_bound n decode tier m k c post u v i hvu hd.1
      (fun r => r.1 = none) hmass
  · have hh := eager_cross_row_class_bound n decode tier m m' k c post u v i hmm hd.1
      (fun r => r.1 = none)
    exact hh.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (class_prior_le_posterior decode tier i hmass)) le_rfl)

/-- The fresh accepted class of the actual forged input is charged to the actual
paid index queries of the same forge/verify execution. Signing and its private
cache are kept intact, and the signed value remains a joint event throughout. -/
theorem eager_fresh_chosen_bound {M : ℕ} {α γ : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c : Cache) (forge : Option (Winner n M) → OracleComp Spec α)
    (verify : Option (Winner n M) → α → OracleComp Spec γ)
    (chosen : α → Message × Nonce n) (v : Nonce n) (i : Fin M)
    (hmass : 0 < fraction (weakRank tier i ∘ decode))
    (hquery : ∀ s a d, publicHit (indexInput n (chosen a)) (verify s a) d = 1) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      signedChosen (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
        forge chosen (some (v,i)) (freshAlternative n c (m,v))
        (fun d => decode (g (d.1++d.2)) = some i)) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          signedCharge (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
            (fun s => forge s >>= verify s) (some (v,i)) (indexPaid (isIndexLength (msgBits+n)))) := by
  apply integrated_signedChosen_bound
    ($ᵗ (BitVec (msgBits+n) → BitVec hashBits))
    (fun g => run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g))
    forge verify (indexInput n) chosen (some (v,i)) (freshAlternative n c (m,v))
    (fun g d => decode (g (d.1++d.2)) = some i) (isIndexLength (msgBits+n)) _
    (indexInput_injective n) (fun _ => rfl) (indexInput_paid n) hquery
  intro d hd
  exact eager_fresh_hit_bound n decode tier m k c (fun s => forge s >>= verify s) v i d hd hmass

#print axioms eager_fresh_hit_bound
#print axioms eager_fresh_chosen_bound
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.ReplacementFreshOverlay; SHA256 63ad1e643bed96165e270635748dc4dd07ddf6e156516aceedb280098d08cf05. -/
section

/-! Aligning the fresh-index cost with the reduced graph-authentication
execution: a fixed graph cache can be exposed after the actual signer. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical BigOperators
local instance (priority := 100000) stagedLocal_ReplacementFreshOverlay_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

theorem preload_extend_commute (b : ℕ) (c f : Cache)
    (hf : ∀ q : Query, q.1 = b → f q = none)
    (g : BitVec b → BitVec hashBits) :
    (lengthSlice b).preload (Cache.extend c f) g =
      Cache.extend ((lengthSlice b).preload c g) f := by
  funext q
  unfold QuerySlice.preload
  by_cases hq : q.1 = b
  · simp [Cache.extend_apply, hf q hq]
  · simp [Cache.extend_apply, lengthSlice_outside b g q hq]

theorem freshAlternative_extend (n : ℕ) (c f : Cache)
    (hf : ∀ d : Message × Nonce n, f (indexInput n d) = none)
    (s d : Message × Nonce n) :
    freshAlternative n (Cache.extend c f) s d ↔ freshAlternative n c s d := by
  simp [freshAlternative, Cache.extend_apply, hf d]

def exposeCache {β : Type} (p : ProbComp (β × Cache)) (f : Cache) : ProbComp (β × Cache) :=
  (fun r => (r.1,Cache.extend r.2 f)) <$> p

theorem loop_preload_extend (n : ℕ) {M : ℕ}
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c f : Cache) (hf : ∀ q : Query, q.1 = msgBits+n → f q = none)
    (g : BitVec (msgBits+n) → BitVec hashBits) :
    run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload (Cache.extend c f) g) =
      exposeCache (run (loop n decode tier m k) ((lengthSlice (msgBits+n)).preload c g)) f := by
  rw [preload_extend_commute (msgBits+n) c f hf]
  exact run_loop_extend n decode tier m f (fun η => hf _ rfl) k _

/-- The index charge uses exactly the signer terminal cache extended by the
fixed exposed graph cache, as in the recordwise graph authentication bound. -/
theorem eager_fresh_chosen_overlay_bound {M : ℕ} {α γ : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) (k : ℕ)
    (c f : Cache) (hf : ∀ q : Query, q.1 = msgBits+n → f q = none)
    (forge : Option (Winner n M) → OracleComp Spec α)
    (verify : Option (Winner n M) → α → OracleComp Spec γ)
    (chosen : α → Message × Nonce n) (v : Nonce n) (i : Fin M)
    (hmass : 0 < fraction (weakRank tier i ∘ decode))
    (hquery : ∀ s a d, publicHit (indexInput n (chosen a)) (verify s a) d = 1) :
    E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
      signedChosen (exposeCache (run (loop n decode tier m k)
        ((lengthSlice (msgBits+n)).preload c g)) f)
        forge chosen (some (v,i)) (freshAlternative n c (m,v))
        (fun d => decode (g (d.1++d.2)) = some i)) ≤
      ENNReal.ofReal (fraction (fun y => decode y = some i) / fraction (weakRank tier i ∘ decode)) *
        E ($ᵗ (BitVec (msgBits+n) → BitVec hashBits)) (fun g =>
          signedCharge (exposeCache (run (loop n decode tier m k)
            ((lengthSlice (msgBits+n)).preload c g)) f)
            (fun s => forge s >>= verify s) (some (v,i)) (indexPaid (isIndexLength (msgBits+n)))) := by
  have h := eager_fresh_chosen_bound n decode tier m k (Cache.extend c f)
    forge verify chosen v i hmass hquery
  simp_rw [loop_preload_extend n decode tier m k c f hf] at h
  have he : freshAlternative n (Cache.extend c f) (m,v) = freshAlternative n c (m,v) := by
    funext d
    exact propext (freshAlternative_extend n c f (fun d => hf _ rfl) (m,v) d)
  rw [he] at h
  exact h

#print axioms loop_preload_extend
#print axioms eager_fresh_chosen_overlay_bound
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.WeightedTier; SHA256 28bf4fcc731eb1280c2f4d28222ff44866e3fcd27463edca1dc0651dc15a0d1b. -/
section

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

theorem rawTier_eq_decodeTier (x : BitVec 129) (j : Tier) :
    (decodeRaw x).map tier = some j.val ↔ rawTier x = some j := by
  cases h : rawAlias x with
  | none => simp only [decodeRaw, rawClass, rawTier, h, Option.map_none, reduceCtorEq]
  | some a =>
    simp only [decodeRaw, rawClass, rawTier, h, Option.map_some, Option.some.injEq]
    change (classEquiv.symm (classEquiv a.1)).1.val = j.val ↔ a.1.1 = j
    rw [classEquiv.symm_apply_apply, Fin.ext_iff]

theorem decodeTier_fiber (j : Tier) :
    (Finset.univ.filter fun x : BitVec 256 => (decode x).map tier = some j.val).card =
      population j * 2^(j.val+1) * 2^127 := by
  have he : (Finset.univ.filter fun x : BitVec 256 => (decode x).map tier = some j.val) =
      Finset.univ.filter fun x : BitVec 256 => rawTier (x.setWidth 129) = some j := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decode, rawTier_eq_decodeTier]
  have h := card_truncPredicate (n := 256) (w := 129) (by omega)
    (fun x => rawTier x = some j)
  exact (congrArg Finset.card he).trans
    (h.trans (congrArg (fun k : ℕ => k * 2^(256-129)) (rawTier_fiber j)))


end
end OptimalOTS.WeightedConstruction.WeightedSchedule

#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.rawTier_eq_decodeTier
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.decodeTier_fiber
end

/- Original module: Submissions.UpperCompressions.WeightedProbabilities; SHA256 e907e6f39c3eea0035526d77893ccae06fc095924d80caacfdbaadbc76b22397. -/
section
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter tier WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases
theorem decode_probability (i : Fin M) :
    ((Finset.univ.filter fun x : BitVec 256 => decode x = some i).card : ℚ) / 2^256 =
      (2 : ℚ)^(tier i+1) / 2^129 := by
  have h (a : ℚ) : a * 2^127 / 2^256 = a / 2^129 := by norm_num; ring
  rw [decode_fiber]
  push_cast
  exact h _

theorem acceptance_probability :
    ((Finset.univ.filter fun x : BitVec 256 => (decode x).isSome).card : ℚ) / 2^256 =
      45/524288 := by
  rw [accepted_decode_count]
  change ((WeightedResearch92.acceptedAliases * 2^127 : ℕ) : ℚ) / 2^256 = _
  rw [WeightedResearch92.aliases_exact]
  norm_num


end
end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.decode_probability
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.acceptance_probability
end

/- Original module: Submissions.UpperCompressions.WeightedGrouping; SHA256 03c3afa0ff8608ed07ee94d9d4de81bbbe9ce96a1c99f2a851b1e1b74a2f71a3. -/
section

/-! Exact grouping and real-number masses for the actual mixed72 decoder.
These identities connect construction fibers to the reference distribution;
they do not assert an adaptive game bound. -/

namespace OptimalOTS.WeightedConstruction.WeightedSchedule
noncomputable section
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes WeightedResearch92.acceptedAliases

/-- Reindex any real-valued tier function by the exact class populations. -/
theorem sum_tier (f : ℕ → ℝ) :
    (∑ i : Fin M, f (tier i)) = ∑ j : Tier, (population j : ℝ) * f j.val := by
  calc
    _ = ∑ c : Class, f c.1.val := by
      apply Fintype.sum_equiv classEquiv.symm
      intro i
      rfl
    _ = ∑ j : Tier, (population j : ℝ) * f j.val := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

def classProbability (i : Fin M) : ℝ := (2:ℝ)^(tier i+1) / 2^129

def tierProbability (j : Tier) : ℝ :=
    ((Finset.univ.filter fun x : BitVec 256 => (decode x).map tier = some j.val).card : ℝ) / 2^256

theorem class_probability_real (i : Fin M) :
    ((Finset.univ.filter fun x : BitVec 256 => decode x = some i).card : ℝ) / 2^256 =
      classProbability i := by
  have h (a : ℝ) : a * 2^127 / 2^256 = a / 2^129 := by norm_num; ring
  unfold classProbability
  rw [decode_fiber]
  push_cast
  convert h ((2:ℝ)^(tier i+1)) using 1 <;> norm_num

theorem tier_probability_eq (j : Tier) :
    tierProbability j = (if j.val < 71 then 19 else 91 : ℝ) / 2^24 := by
  unfold tierProbability
  rw [decodeTier_fiber, tier_alias_count]
  push_cast
  split_ifs <;> norm_num

theorem early_tier_probability (j : Tier) (hj : j.val < 71) :
    tierProbability j = WeightedConstants.q := by
  rw [tier_probability_eq, if_pos hj]
  norm_num [WeightedConstants.q, WeightedConstants.L]

theorem last_tier_probability :
    tierProbability ⟨71, by decide⟩ = (91:ℝ)/2^24 := by
  rw [tier_probability_eq]
  norm_num

/-- The exact early-tier mass accumulated before tier j. -/
theorem early_prefix_probability (j : ℕ) (hj : j ≤ 71) :
    (∑ t ∈ Finset.range j,
      (if t < 71 then (19:ℝ) else 91) / 2^24) = (j:ℝ) * WeightedConstants.q := by
  calc
    _ = ∑ _t ∈ Finset.range j, WeightedConstants.q := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [if_pos (by have := Finset.mem_range.mp ht; omega)]
      norm_num [WeightedConstants.q, WeightedConstants.L]
    _ = _ := by simp

/-- Class mass divided by kappa=2^-127 is half of its tier's power of two. -/
theorem relative_class_probability (i : Fin M) :
    classProbability i / ((2:ℝ)^127)⁻¹ = (1:ℝ)/2 * 2^(tier i) := by
  unfold classProbability
  rw [pow_succ]
  have h (a : ℝ) : (a*2/2^129) / ((2:ℝ)^127)⁻¹ = (1:ℝ)/2*a := by norm_num; ring
  exact h _

end
end OptimalOTS.WeightedConstruction.WeightedSchedule

#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.sum_tier
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.tier_probability_eq
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.relative_class_probability
end

/- Original module: Submissions.UpperCompressions.WideReference; SHA256 c5cfd1d69a2410992582eb1cd8f88d7848be3b0409d8804559887b21656cb1dd. -/
section

/-! Concrete class-average coefficients for the mixed72 decoder. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReference
attribute [local irreducible] WeightedResearch92.tierClasses WeightedResearch92.classes
set_option maxHeartbeats 1000000

theorem classProbability_eq (i : Fin M) : classProbability i = probability (tier i) := by
  unfold classProbability probability kappa
  rw [pow_succ]
  norm_num
  ring

theorem population_probability (j : Tier) :
    (population j : ℝ)*probability j.val = mass j.val := by
  have hh := congrArg (fun n : ℕ => (n : ℝ)) (tier_alias_count j)
  push_cast at hh
  have ha : (population j : ℝ)*probability j.val =
      (if j.val < 71 then 19 else 91 : ℝ)/2^24 := by
    unfold probability kappa
    rw [pow_succ] at hh
    split_ifs at hh ⊢ <;> norm_num at hh ⊢ <;> nlinarith [hh]
  rw [ha]
  unfold mass lower
  split_ifs with h
  · norm_num [survival,WeightedConstants.q,WeightedConstants.L]
    ring
  · have hj : j.val=71 := by have := j.isLt; omega
    norm_num [hj,survival,acceptance,WeightedConstants.q,WeightedConstants.L]

def referenceWeight (i : Fin M) : ℝ := weight (tier i)
def mean : ℝ := ∑ i : Fin M,classProbability i*referenceWeight i

theorem mean_eq : mean = kappa*WeightedConstants.referenceMean failure := by
  unfold mean referenceWeight
  simp only [classProbability_eq]
  rw [sum_tier (fun j => probability j*weight j)]
  have he : (∑ j : Tier,(population j:ℝ)*(probability j.val*weight j.val)) =
      ∑ j : Tier,mass j.val*weight j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc,population_probability]
  rw [he]
  change (∑ j : Fin 72,mass j.val*weight j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => mass j*weight j) 72]
  exact reference_mean_identity

theorem mean_le : mean ≤ kappa*(223/250) := by
  rw [mean_eq]
  exact mul_le_mul_of_nonneg_left (WeightedConstants.referenceMean_le failure failure_nonneg)
    (by unfold kappa; positivity)

theorem referenceWeight_nonneg (i : Fin M) : 0 ≤ referenceWeight i :=
  weight_nonneg _ (by have := tier_lt i; omega)

theorem referenceWeight_le (i : Fin M) : referenceWeight i ≤ (WeightedConstants.L:ℝ)*kappa/2 :=
  weight_le _ (by have := tier_lt i; omega)

theorem classProbability_pos (i : Fin M) : 0 < classProbability i := by
  unfold classProbability
  positivity

theorem classProbability_sum : (∑ i : Fin M,classProbability i) = acceptance := by
  simp only [classProbability_eq]
  rw [sum_tier probability]
  simp only [population_probability]
  rw [Fin.sum_univ_eq_sum_range mass 72]
  exact total_mass

theorem referenceWeight_sum : (∑ i : Fin M,referenceWeight i) = 1-failure := by
  unfold referenceWeight
  rw [sum_tier weight]
  have he : (∑ j : Tier,(population j:ℝ)*weight j.val) =
      ∑ j : Tier,mass j.val*WeightedReplacement.kernel WeightedConstants.L
        (survival j.val) (lower j.val) := by
    apply Finset.sum_congr rfl
    intro j hj
    unfold weight
    rw [← mul_assoc,population_probability]
  rw [he]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => mass j*WeightedReplacement.kernel WeightedConstants.L (survival j) (lower j)) 72]
  exact total_winner_mass

def excess (i : Fin M) : ℝ := max (classProbability i/(1-acceptance)-kappa/2) 0

theorem excess_eq (i : Fin M) : excess i = classProbability i/(1-acceptance)-kappa/2 := by
  apply max_eq_left
  have hp : kappa/2 ≤ classProbability i := by
    rw [classProbability_eq]
    have h : (1:ℝ) ≤ 2^(tier i) := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ kappa/2 by unfold kappa; positivity)
    simpa only [mul_one,probability] using hh
  have hd : 0 < 1-acceptance := by norm_num [acceptance]
  have hp' : classProbability i ≤ classProbability i/(1-acceptance) := by
    apply (le_div_iff₀ hd).2
    have h := mul_le_mul_of_nonneg_left
      (show 1-acceptance ≤ 1 by norm_num [acceptance]) (classProbability_pos i).le
    simpa only [mul_one] using h
  linarith

theorem excess_mean_eq :
    (∑ i : Fin M,referenceWeight i*excess i) = mean/(1-acceptance)-kappa/2*(1-failure) := by
  simp only [excess_eq,mul_sub,← mul_div_assoc,Finset.sum_sub_distrib,← Finset.sum_div,
    ← Finset.sum_mul]
  rw [referenceWeight_sum]
  have hm : (∑ i : Fin M,referenceWeight i*classProbability i) = mean := by
    unfold mean
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hm]
  ring

theorem excess_mean_le : (∑ i : Fin M,referenceWeight i*excess i) ≤ kappa*(2/5) := by
  rw [excess_mean_eq]
  exact post_excess_le mean_le failure_le

#print axioms mean_eq
#print axioms mean_le
#print axioms referenceWeight_le
#print axioms classProbability_sum
#print axioms referenceWeight_sum
#print axioms excess_mean_le
end OptimalOTS.WeightedConstruction.WeightedSchedule
end
end

/- Original module: Submissions.UpperCompressions.WideSecurityData; SHA256 45b47703a5027a3262aa332dcbb5f12a885c5be10e02f813c06f2939dbcf4af3. -/
section

/-! Concrete distribution and bounded score data for the stochastic lemmas.
No security theorem is assumed by this interface. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReference WeightedConstants WeightedReplacement
set_option maxHeartbeats 1000000

def securityWeights : WeightedRow.Weights (Fin M) where
  p := classProbability
  g := referenceWeight
  p_pos := classProbability_pos
  g_nonneg := referenceWeight_nonneg
  mass_le_one := by rw [classProbability_sum]; norm_num [acceptance]

theorem securityWeights_mean : securityWeights.mean ≤ kappa*(223/250) := mean_le

theorem survival_le_one (j : ℕ) : survival j ≤ 1 := by
  have h : 0 ≤ (j:ℝ)*q := mul_nonneg (Nat.cast_nonneg _) (by norm_num [q,L])
  unfold survival
  linarith

theorem survival_ge_reject (j : ℕ) (hj : j ≤ 71) : 1-acceptance ≤ survival j := by
  have hjr : (j:ℝ) ≤ 71 := by exact_mod_cast hj
  have hh := mul_le_mul_of_nonneg_right hjr (show 0 ≤ q by norm_num [q,L])
  have hn : (71:ℝ)*q ≤ acceptance := by norm_num [q,L,acceptance]
  unfold survival
  linarith

theorem lower_ge_reject (j : ℕ) (hj : j ≤ 71) : 1-acceptance ≤ lower j := by
  unfold lower
  split_ifs with h
  · exact survival_ge_reject _ (by omega)
  · exact le_refl _

theorem weight_ratio (i : Fin M) : referenceWeight i/classProbability i =
    kernel L (survival (tier i)) (lower (tier i)) := by
  unfold referenceWeight weight
  rw [← classProbability_eq]
  exact mul_div_cancel_left₀ _ (classProbability_pos i).ne'

theorem weight_ratio_le (i : Fin M) : referenceWeight i/classProbability i ≤ (L:ℝ) := by
  rw [weight_ratio]
  have hj : tier i ≤ 71 := by have := tier_lt i; omega
  have hm := kernel_mono L (survival_nonneg _ hj) (lower_nonneg _ hj)
    (survival_le_one _) ((lower_le_survival _ hj).trans (survival_le_one _))
  rw [kernel_diagonal,one_pow,mul_one] at hm
  exact hm

theorem excessScore_nonneg (i : Fin M) : 0 ≤ referenceWeight i*excess i/classProbability i := by
  apply div_nonneg
  · exact mul_nonneg (referenceWeight_nonneg i) (le_max_right _ _)
  · exact (classProbability_pos i).le

theorem excessScore_le (i : Fin M) :
    referenceWeight i*excess i/classProbability i ≤ (L:ℝ)*kappa := by
  have hd : 0 < 1-acceptance := by norm_num [acceptance]
  have hp := classProbability_pos i
  have hg := referenceWeight_nonneg i
  have he : excess i ≤ classProbability i/(1-acceptance) := by
    rw [excess_eq]
    have hk : 0 ≤ kappa/2 := by unfold kappa; positivity
    linarith
  calc
    _ ≤ (referenceWeight i*(classProbability i/(1-acceptance)))/classProbability i :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hg) hp.le
    _ = referenceWeight i/(1-acceptance) := by field_simp
    _ ≤ ((L:ℝ)*kappa/2)/(1-acceptance) :=
      div_le_div_of_nonneg_right (referenceWeight_le i) hd.le
    _ ≤ (L:ℝ)*kappa := by
      norm_num [L,kappa,acceptance]

/-- A complete-row prefix deficit implies the common multiplicative kernel
envelope; this is a pointwise implication, never a conditioning operation. -/
theorem empirical_kernel_le (i : Fin M) (Ah Bh : ℝ)
    (ha : 0 ≤ Ah) (hb : 0 ≤ Bh)
    (hA : Ah ≤ survival (tier i)+1/(100*(L:ℝ)))
    (hB : Bh ≤ lower (tier i)+1/(100*(L:ℝ))) :
    kernel L Ah Bh ≤ (99:ℝ)/98*(referenceWeight i/classProbability i) := by
  have hj : tier i ≤ 71 := by have := tier_lt i; omega
  have h := kernel_additive_envelope L ha hb
    (show 0 < 1-acceptance by norm_num [acceptance])
    (show 0 ≤ 1/(100*(L:ℝ)) by norm_num [L])
    (survival_ge_reject _ hj) (lower_ge_reject _ hj) hA hB
  rw [weight_ratio]
  exact h.trans (mul_le_mul_of_nonneg_right common_envelope
    (kernel_nonneg L (survival_nonneg _ hj) (lower_nonneg _ hj)))

#print axioms securityWeights
#print axioms weight_ratio_le
#print axioms excessScore_le
#print axioms empirical_kernel_le
end OptimalOTS.WeightedConstruction.WeightedSchedule
end
end

/- Original module: Submissions.UpperCompressions.WeightedCompletion; SHA256 08909465abfb618138711a9a6d5332357414e8c46c82aa11d20fc819178a2c27. -/
section

/-! Averaging a partially exposed row under its original completion law.
Only unconditional fresh-coordinate marginals are used; no Good conditioning. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {Ω D I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype D] [Nonempty D]
  [Fintype I] [DecidableEq D] [DecidableEq I]

def score (x : Option I) (f : I → ℝ) : ℝ := (x.map f).getD 0

theorem score_expand (x : Option I) (f : I → ℝ) :
    score x f = ∑ i, if x = some i then f i else 0 := by
  cases x with
  | none => simp [score]
  | some i => simp [score, eq_comm]

theorem mean_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    uniformMean (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_mul (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun ω => a * f ω) = a * uniformMean f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

theorem mean_score (x : Ω → Option I) (p f : I → ℝ)
    (hm : ∀ i, uniformMean (fun ω => if x ω = some i then 1 else 0) = p i) :
    uniformMean (fun ω => score (x ω) f) = ∑ i, p i * f i := by
  simp only [score_expand]
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun ω => if x ω = some i then f i else 0) =
      fun ω => (if x ω = some i then 1 else 0) * f i := by
    funext ω
    split_ifs <;> simp
  rw [he, uniformMean_mul_const, hm]

def rowCount (R : Finset D) (fixed : D → Option I) (i : I) : ℕ :=
  (R.filter fun a => fixed a = some i).card

theorem known_score (R : Finset D) (fixed : D → Option I) (f : I → ℝ) :
    (∑ a ∈ R, score (fixed a) f) = ∑ i, (rowCount R fixed i : ℝ) * f i := by
  simp only [score_expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp only [rowCount, Finset.sum_const, nsmul_eq_mul]

/-- Keep the good-table indicator joint with the payoff, then discard it only
from a nonnegative reference term. The bad-table tail is charged separately. -/
theorem joint_good_bound (Good : Ω → Prop) (X Y : Ω → ℝ) (F C δ : ℝ)
    (hF : 0 ≤ F) (hC : 0 ≤ C) (hY : ∀ ω, 0 ≤ Y ω)
    (hgood : ∀ ω, Good ω → X ω ≤ F * Y ω)
    (hmax : ∀ ω, X ω ≤ C)
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean X ≤ F * uniformMean Y + C * δ := by
  have hpoint : ∀ ω, X ω ≤ F * Y ω + C * (if Good ω then 0 else 1) := by
    intro ω
    by_cases hg : Good ω
    · simpa only [if_pos hg, mul_zero, add_zero] using hgood ω hg
    · rw [if_neg hg, mul_one]
      exact (hmax ω).trans (le_add_of_nonneg_left (mul_nonneg hF (hY ω)))
  have h := uniformMean_mono X _ hpoint
  rw [uniformMean_add, mean_mul, mean_mul] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad hC))

/-- Exact row expectation: exposed coordinates keep their values, while every
unexposed coordinate has its original one-coordinate marginal. Correlations
between unexposed coordinates are not excluded or conditioned away. -/
theorem completion_score (R : Finset D) (fixed : D → Option I)
    (table : Ω → D → Option I) (p fKnown fFresh : I → ℝ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = p i) :
    uniformMean (fun ω => ∑ a : D,
      if a ∈ R then score (table ω a) fKnown else score (table ω a) fFresh) =
      (∑ i, (rowCount R fixed i : ℝ) * fKnown i) +
        ((Fintype.card D : ℝ) - R.card) * ∑ i, p i * fFresh i := by
  rw [mean_sum]
  have he : ∀ a : D, uniformMean (fun ω =>
      if a ∈ R then score (table ω a) fKnown else score (table ω a) fFresh) =
      if a ∈ R then score (fixed a) fKnown else ∑ i, p i * fFresh i := by
    intro a
    by_cases ha : a ∈ R
    · simp only [if_pos ha, hknown _ a ha, uniformMean_const]
    · simp only [if_neg ha]
      exact mean_score (fun ω => table ω a) p fFresh (hfresh a ha)
  simp only [he]
  rw [← Finset.sum_add_sum_compl R]
  have hR : (∑ a ∈ R, if a ∈ R then score (fixed a) fKnown else ∑ i, p i * fFresh i) =
      ∑ a ∈ R, score (fixed a) fKnown :=
    Finset.sum_congr rfl fun a ha => if_pos ha
  have hc : (∑ a ∈ Rᶜ, if a ∈ R then score (fixed a) fKnown else ∑ i, p i * fFresh i) =
      ((Fintype.card D : ℝ)-R.card) * ∑ i, p i * fFresh i := by
    have he' : (∑ a ∈ Rᶜ, if a ∈ R then score (fixed a) fKnown else ∑ i, p i * fFresh i) =
        ∑ _a ∈ Rᶜ, ∑ i, p i * fFresh i :=
      Finset.sum_congr rfl fun a ha => if_neg (Finset.mem_compl.mp ha)
    rw [he', Finset.sum_const, nsmul_eq_mul, Finset.card_compl]
    rw [Nat.cast_sub (Finset.card_le_univ R)]
  rw [hR, known_score, hc]

end WeightedCompletion
#print axioms WeightedCompletion.joint_good_bound
#print axioms WeightedCompletion.completion_score
end
end

/- Original module: Submissions.UpperCompressions.WeightedReplay; SHA256 50674301aeefb2b4d064540f5a8f100eff47e436aa55108853fa7ef12c349c35. -/
section

/-! Exact finite-completion formulas for replay and the post-sign excess payoff.
Good remains a joint event; fresh-coordinate marginals are unconditional. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {Ω D I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype D] [Nonempty D]
  [Fintype I] [DecidableEq D] [DecidableEq I]

/-- Kernel-envelope reference payoff, with different scores at exposed and
unexposed candidate nonces. Failure contributes zero. -/
def referencePayoff (R : Finset D) (table : Ω → D → Option I)
    (p g fKnown fFresh : I → ℝ) (ω : Ω) : ℝ :=
  (∑ a : D, if a ∈ R then score (table ω a) (fun i => g i / p i * fKnown i)
    else score (table ω a) (fun i => g i / p i * fFresh i)) / Fintype.card D

theorem referencePayoff_nonneg (R : Finset D) (table : Ω → D → Option I)
    (p g fKnown fFresh : I → ℝ) (hp : ∀ i, 0 < p i) (hg : ∀ i, 0 ≤ g i)
    (hK : ∀ i, 0 ≤ fKnown i) (hF : ∀ i, 0 ≤ fFresh i) (ω : Ω) :
    0 ≤ referencePayoff R table p g fKnown fFresh ω := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro a _
  cases ht : table ω a with
  | none => simp [score, ht]
  | some i =>
    simp only [score, ht, Option.map_some, Option.getD_some]
    split_ifs
    · exact mul_nonneg (div_nonneg (hg i) (hp i).le) (hK i)
    · exact mul_nonneg (div_nonneg (hg i) (hp i).le) (hF i)

theorem referencePayoff_mean (R : Finset D) (fixed : D → Option I)
    (table : Ω → D → Option I) (p g fKnown fFresh : I → ℝ) (hp : ∀ i, 0 < p i)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = p i) :
    uniformMean (referencePayoff R table p g fKnown fFresh) =
      (1-(R.card : ℝ)/Fintype.card D) * (∑ i, g i * fFresh i) +
        (∑ i, (rowCount R fixed i : ℝ) * (g i / p i * fKnown i)) / Fintype.card D := by
  have hN : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc := completion_score R fixed table p (fun i => g i / p i * fKnown i)
    (fun i => g i / p i * fFresh i) hknown hfresh
  have hs : (∑ i, p i * (g i / p i * fFresh i)) = ∑ i, g i * fFresh i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hp i).ne']
  rw [hs] at hc
  have hdiv (f : Ω → ℝ) (n : ℝ) : uniformMean (fun ω => f ω / n) = uniformMean f / n := by
    unfold uniformMean
    rw [← Finset.sum_div]
    ring
  unfold referencePayoff
  rw [hdiv, hc]
  field_simp
  ring

/-- Exact expected public replay reference, excluding the chosen cached entry
itself: fresh candidates require k_i>0, cached candidates require k_i≥2. -/
theorem replay_reference_mean (w : WeightedRow.Weights I)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I) (k : I → ℕ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i) :
    uniformMean (referencePayoff R table w.p w.g
      (fun i => if 2 ≤ k i then 1 else 0) (fun i => if k i = 0 then 0 else 1)) =
      w.hazard (Fintype.card D) R.card k (rowCount R fixed) := by
  rw [referencePayoff_mean R fixed table w.p w.g _ _ w.p_pos hknown hfresh]
  unfold WeightedRow.Weights.hazard WeightedRow.Weights.seen WeightedRow.Weights.bad
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp <;> ring

/-- Replay bound using the pointwise good-table kernel envelope. This theorem
retains an explicit exact sampler-payoff premise until the program adapter is supplied. -/
theorem replay_bound (w : WeightedRow.Weights I)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I) (k : I → ℕ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (Good : Ω → Prop) (replay : Ω → ℝ) (F δ : ℝ) (hF : 0 ≤ F)
    (hkernel : ∀ ω, Good ω → replay ω ≤ F * referencePayoff R table w.p w.g
      (fun i => if 2 ≤ k i then 1 else 0) (fun i => if k i = 0 then 0 else 1) ω)
    (hmax : ∀ ω, replay ω ≤ 1)
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean replay ≤ F * w.hazard (Fintype.card D) R.card k (rowCount R fixed) + δ := by
  have h := joint_good_bound Good replay _ F 1 δ hF zero_le_one
    (referencePayoff_nonneg R table w.p w.g _ _ w.p_pos w.g_nonneg
      (fun i => by split_ifs <;> norm_num) (fun i => by split_ifs <;> norm_num))
    hkernel hmax hbad
  rw [replay_reference_mean w R fixed table k hknown hfresh, one_mul] at h
  exact h

/-- Excess-payoff bound, with the same unconditional fresh-coordinate averaging. -/
theorem excess_bound (w : WeightedRow.Weights I)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (e : I → ℝ) (he : ∀ i, 0 ≤ e i) (Good : Ω → Prop)
    (payoff : Ω → ℝ) (F emax δ : ℝ) (hF : 0 ≤ F) (hemax : 0 ≤ emax)
    (hkernel : ∀ ω, Good ω → payoff ω ≤ F * referencePayoff R table w.p w.g e e ω)
    (hmax : ∀ ω, payoff ω ≤ emax)
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean payoff ≤ F * ((1-(R.card : ℝ)/Fintype.card D) * (∑ i, w.g i * e i) +
      (∑ i, (rowCount R fixed i : ℝ) * (w.g i/w.p i * e i)) / Fintype.card D) + emax * δ := by
  have h := joint_good_bound Good payoff _ F emax δ hF hemax
    (referencePayoff_nonneg R table w.p w.g e e w.p_pos w.g_nonneg he he)
    hkernel hmax hbad
  rw [referencePayoff_mean R fixed table w.p w.g e e w.p_pos hknown hfresh] at h
  exact h

end WeightedCompletion
#print axioms WeightedCompletion.replay_reference_mean
#print axioms WeightedCompletion.replay_bound
#print axioms WeightedCompletion.excess_bound
end
end

/- Original module: Submissions.UpperCompressions.WeightedSelectorPayoff; SHA256 0026168cec577e75caa88b4c373af330ca213cdba830ac4bfe0a08794cb973a9. -/
section

/-! Exact weighted-payoff law for the actual first-minimum selector.
The whole nonce list is processed, ties retain the first occurrence. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement OptimalOTS.WeightedSampling
variable {D I : Type} [Fintype D] [Nonempty D] [DecidableEq D] [DecidableEq I]

def selected (table : D → Option I) (tier : I → ℕ) (xs : List D) : Option (D × I) :=
  select (fun p => tier p.2) (xs.map fun a => (fun i => (a,i)) <$> table a)

theorem selected_consistent (table : D → Option I) (tier : I → ℕ) (xs : List D)
    (a : D) (i : I) (h : selected table tier xs = some (a,i)) : table a = some i := by
  have hm := select_source (fun p : D × I => tier p.2) _ (a,i) h
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hm
  change (table b).map (fun i => (b,i)) = some (a,i) at hb
  rw [Option.map_eq_some_iff] at hb
  obtain ⟨j, hj, hji⟩ := hb
  obtain ⟨hab, hij⟩ := Prod.mk.inj hji
  cases hab
  cases hij
  exact hj

theorem selected_score_expand (table : D → Option I) (tier : I → ℕ)
    (f : D → I → ℝ) (xs : List D) :
    score (selected table tier xs) (fun p => f p.1 p.2) =
      ∑ a : D, score (table a) (fun i => if selected table tier xs = some (a,i) then f a i else 0) := by
  cases hs : selected table tier xs with
  | none =>
    simp only [score, Option.map_none, Option.getD_none]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro a _
    cases table a <;> simp [score, hs]
  | some r =>
    obtain ⟨a,i⟩ := r
    have ht := selected_consistent table tier xs a i hs
    rw [Finset.sum_eq_single a]
    · simp [score, ht, hs]
    · intro b _ hba
      cases table b with
      | none => simp [score]
      | some j =>
        have hn : (a,i) ≠ (b,j) := fun he => hba (congrArg Prod.fst he).symm
        simp [score, hs, hn, Ne.symm hba]
    · simp

theorem iidMean_sum {ι : Type} (s : Finset ι) (f : ι → List D → ℝ) (n : ℕ) :
    iidMean n (fun xs => ∑ i ∈ s, f i xs) = ∑ i ∈ s, iidMean n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change uniformMean (fun a => iidMean n (fun xs => ∑ i ∈ s, f i (a::xs))) = _
    simp only [ih]
    rw [mean_sum]
    rfl

theorem iidMean_mul_const (f : List D → ℝ) (c : ℝ) (n : ℕ) :
    iidMean n (fun xs => f xs*c) = iidMean n f*c := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change uniformMean (fun a => iidMean n (fun xs => f (a::xs)*c)) = _
    simp only [ih]
    rw [uniformMean_mul_const]
    rfl

theorem iidMean_const (c : ℝ) (n : ℕ) : iidMean n (fun _ : List D => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change uniformMean (fun _ : D => iidMean n (fun _ : List D => c)) = c
    rw [ih, uniformMean_const]

theorem iidMean_mono (f g : List D → ℝ) (h : ∀ xs, f xs ≤ g xs) (n : ℕ) :
    iidMean n f ≤ iidMean n g := by
  induction n generalizing f g with
  | zero => exact h []
  | succ n ih =>
    apply uniformMean_mono
    intro a
    exact ih _ _ (fun xs => h (a::xs))

def tableKernel (n : ℕ) (table : D → Option I) (tier : I → ℕ) (f : D → I → ℝ) : ℝ :=
  (∑ a : D, score (table a) (fun i => kernel n
    (fraction (weakRank tier i ∘ table)) (fraction (strictRank tier i ∘ table)) * f a i)) /
      Fintype.card D

/-- Exact expectation, for arbitrary real scores, under iid nonce draws. -/
theorem iid_selected_score (n : ℕ) (table : D → Option I) (tier : I → ℕ)
    (f : D → I → ℝ) :
    iidMean n (fun xs => score (selected table tier xs) (fun p => f p.1 p.2)) =
      tableKernel n table tier f := by
  simp only [selected_score_expand]
  rw [iidMean_sum]
  unfold tableKernel
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  cases ht : table a with
  | none => simp [score, ht, iidMean_const]
  | some i =>
    simp only [score, ht, Option.map_some, Option.getD_some]
    have he : (fun xs => if selected table tier xs = some (a,i) then f a i else 0) =
        fun xs => (if selected table tier xs = some (a,i) then 1 else 0)*f a i := by
      funext xs
      split_ifs <;> simp
    rw [he, iidMean_mul_const]
    have hp := iid_tagged_table_probability table tier a i ht n
    have hp' : iidMean n (fun xs => if selected table tier xs = some (a,i) then 1 else 0) =
        kernel n (fraction (weakRank tier i ∘ table))
          (fraction (strictRank tier i ∘ table)) / Fintype.card D := by
      convert hp using 1
      congr 1
      funext xs
      unfold selected
      split_ifs <;> rfl
    rw [hp']
    ring

theorem tableKernel_le (n : ℕ) (table : D → Option I) (tier : I → ℕ)
    (f : D → I → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ a i, f a i ≤ C) :
    tableKernel n table tier f ≤ C := by
  rw [← iid_selected_score]
  apply le_trans (iidMean_mono _ (fun _ => C) ?_ n) (iidMean_const C n).le
  intro xs
  cases selected table tier xs with
  | none => exact hC
  | some r => exact hf r.1 r.2

end WeightedCompletion
#print axioms WeightedCompletion.iid_selected_score
#print axioms WeightedCompletion.tableKernel_le
end
end

