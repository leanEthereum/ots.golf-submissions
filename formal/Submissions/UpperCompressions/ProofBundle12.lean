import Submissions.UpperCompressions.ProofBundle09
import Submissions.UpperCompressions.ProofBundle10
import Submissions.UpperCompressions.ProofBundle05
import Submissions.UpperCompressions.ProofBundle07
import Submissions.UpperCompressions.ProofBundle11
import Submissions.UpperCompressions.ProofBundle01

/- Original module: Submissions.UpperCompressions.DualCacheLaw; SHA256 ed895065ba6c7ea5a52dc106d11398b9c6a475e14c379529f66bdbfd90dcc5de. -/
section

/-! Joint row/global statistics use a single actual decoded oracle answer. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedDualCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
set_option maxHeartbeats 800000
variable {D B ι : Type} [DecidableEq D] [Fintype B] [SampleableType B]
  [Fintype ι] [DecidableEq ι]

inductive Phase where
  | idle | outside | inside
  deriving DecidableEq

def phase (A G : Finset D) (q : D) (cache : D → Option B) : Phase :=
  if (cache q).isSome then .idle else
  if q ∈ A then .inside else if q ∈ G then .outside else .idle

def protectedPhase (A G : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (cache : (D →ₒ B).QueryCache) : Phase :=
  match t with
  | .inl _ => .idle
  | .inr q => phase A G q cache

def after (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (s : Phase) (r : ℕ) (k row : ι → ℕ) : Option ι → ℝ :=
  match s with
  | .idle => fun _ => f r k row
  | .outside => fun x => f r (advance k x) row
  | .inside => fun x => f (r+1) (advance k x) (advance row x)

theorem after_comp (f : ℝ → ℝ) (g : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (s : Phase) (r : ℕ) (k row : ι → ℕ) :
    after (fun r k row => f (g r k row)) s r k row =
      fun x => f (after g s r k row x) := by
  cases s <;> rfl

theorem hash_query_law (w : WeightedRow.Weights ι)
    (A G : Finset D) (hAG : A ⊆ G) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (q : D) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ) :
    realEval (((D →ₒ B).randomOracle q).run cache)
      (fun out => f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode)) =
    w.expect (after f (phase A G q cache) (seen A cache).card
      (classCounts G cache decode) (classCounts A cache decode)) := by
  rw [randomOracle.run_eq]
  cases hc : cache q with
  | some u => simp [hc, phase, after, expect_const]
  | none =>
    simp only [realEval_bind, realEval_pure]
    by_cases hqA : q ∈ A
    · have hqG := hAG hqA
      have hr (u : B) : (seen A (cache.cacheQuery q u)).card =
          (seen A cache).card+1 := seen_card_update A cache q u hqA hc
      have hk (u : B) : classCounts G (cache.cacheQuery q u) decode =
          advance (classCounts G cache decode) (decode u) :=
        classCounts_update_of_mem G cache decode q u hqG hc
      have hrow (u : B) : classCounts A (cache.cacheQuery q u) decode =
          advance (classCounts A cache decode) (decode u) :=
        classCounts_update_of_mem A cache decode q u hqA hc
      simp only [hr, hk, hrow, phase, hc, Option.isSome_none, Bool.false_eq_true,
        ite_false, hqA, ite_true, after]
      exact realEval_decoded_uniform w decode hfiber (fun x =>
        f ((seen A cache).card+1) (advance (classCounts G cache decode) x)
          (advance (classCounts A cache decode) x))
    · have hr (u : B) : seen A (cache.cacheQuery q u) = seen A cache :=
        seen_update_of_not_mem A cache q u hqA
      have hrow (u : B) : classCounts A (cache.cacheQuery q u) decode =
          classCounts A cache decode := classCounts_update_of_not_mem A cache decode q u hqA
      by_cases hqG : q ∈ G
      · have hk (u : B) : classCounts G (cache.cacheQuery q u) decode =
            advance (classCounts G cache decode) (decode u) :=
          classCounts_update_of_mem G cache decode q u hqG hc
        simp only [hr, hk, hrow, phase, hc, Option.isSome_none, Bool.false_eq_true,
          ite_false, hqA, hqG, ite_true, after]
        exact realEval_decoded_uniform w decode hfiber (fun x =>
          f (seen A cache).card (advance (classCounts G cache decode) x)
            (classCounts A cache decode))
      · have hk (u : B) : classCounts G (cache.cacheQuery q u) decode =
            classCounts G cache decode := classCounts_update_of_not_mem G cache decode q u hqG
        simp only [hr, hk, hrow, phase, hc, Option.isSome_none, Bool.false_eq_true,
          ite_false, hqA, hqG, after, realEval_const, expect_const]

theorem protected_query_law (w : WeightedRow.Weights ι)
    (A G : Finset D) (hAG : A ⊆ G) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (t : (unifSpec+(D →ₒ B)).Domain) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ) :
    realEval ((WeightedDirectCache.protectedImpl (D := D) (B := B) t).run cache)
      (fun out => f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode)) =
    w.expect (after f (protectedPhase A G t cache) (seen A cache).card
      (classCounts G cache decode) (classCounts A cache decode)) := by
  cases t with
  | inl t =>
    simp only [WeightedDirectCache.protectedImpl, protectedPhase, after, expect_const]
    change realEval ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) (fun out => f (seen A out.2).card
        (classCounts G out.2 decode) (classCounts A out.2 decode)) = _
    rw [realEval_bind]
    simp only [realEval_pure, realEval_const]
  | inr q => exact hash_query_law w A G hAG decode hfiber q cache f

#print axioms protected_query_law
end WeightedDualCache
end
end

/- Original module: Submissions.UpperCompressions.DualCacheSupport; SHA256 a2f3e8a818b653a753cc522791bc3d32328bb1a988abbfe89f91b27e8fb3c2f7. -/
section

/-! Supported actual oracle outputs obey the same joint transition as its law. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedDualCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
variable {D B ι : Type} [DecidableEq D] [Fintype B] [SampleableType B]
  [Fintype ι] [DecidableEq ι]

theorem hash_payoff_support (A G : Finset D) (hAG : A ⊆ G) (decode : B → Option ι)
    (q : D) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (out : B × (D →ₒ B).QueryCache)
    (hout : out ∈ support (((D →ₒ B).randomOracle q).run cache)) :
    ∃ x : Option ι, f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode) =
      after f (phase A G q cache) (seen A cache).card
        (classCounts G cache decode) (classCounts A cache decode) x := by
  rw [randomOracle.run_eq] at hout
  cases hc : cache q with
  | some u =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact ⟨none,by simp [phase,hc,after]⟩
  | none =>
    simp only [hc,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hout
    obtain ⟨u,hu,rfl⟩ := hout
    refine ⟨decode u,?_⟩
    by_cases hqA : q ∈ A
    · have hqG := hAG hqA
      rw [show (seen A (cache.cacheQuery q u)).card=(seen A cache).card+1 from
        seen_card_update A cache q u hqA hc]
      rw [show classCounts G (cache.cacheQuery q u) decode=
        advance (classCounts G cache decode) (decode u) from
        classCounts_update_of_mem G cache decode q u hqG hc]
      rw [show classCounts A (cache.cacheQuery q u) decode=
        advance (classCounts A cache decode) (decode u) from
        classCounts_update_of_mem A cache decode q u hqA hc]
      simp [phase,hc,hqA,after]
    · rw [show seen A (cache.cacheQuery q u)=seen A cache from
        seen_update_of_not_mem A cache q u hqA]
      rw [show classCounts A (cache.cacheQuery q u) decode=classCounts A cache decode from
        classCounts_update_of_not_mem A cache decode q u hqA]
      by_cases hqG : q ∈ G
      · rw [show classCounts G (cache.cacheQuery q u) decode=
          advance (classCounts G cache decode) (decode u) from
          classCounts_update_of_mem G cache decode q u hqG hc]
        simp [phase,hc,hqA,hqG,after]
      · rw [show classCounts G (cache.cacheQuery q u) decode=classCounts G cache decode from
          classCounts_update_of_not_mem G cache decode q u hqG]
        simp [phase,hc,hqA,hqG,after]

theorem protected_payoff_support (A G : Finset D) (hAG : A ⊆ G) (decode : B → Option ι)
    (t : (unifSpec+(D →ₒ B)).Domain) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (out : (unifSpec+(D →ₒ B)).Range t × (D →ₒ B).QueryCache)
    (hout : out ∈ support ((WeightedDirectCache.protectedImpl (D := D) (B := B) t).run cache)) :
    ∃ x : Option ι, f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode) =
      after f (protectedPhase A G t cache) (seen A cache).card
        (classCounts G cache decode) (classCounts A cache decode) x := by
  cases t with
  | inl t =>
    change out ∈ support ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) at hout
    obtain ⟨u,hu,hp⟩ := (mem_support_bind_iff _ _ _).1 hout
    simp only [support_pure,Set.mem_singleton_iff] at hp
    subst out
    exact ⟨none,rfl⟩
  | inr q => exact hash_payoff_support A G hAG decode q cache f out hout

#print axioms protected_payoff_support
end WeightedDualCache
end
end

/- Original module: Submissions.UpperCompressions.DualProtectedLaw; SHA256 6dd063436b93744e9970fac13cb91c1405f27741d590ab12ea4c0607f1e4b3cc. -/
section

noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedDualCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actual_query_law (w : WeightedRow.Weights ι)
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ) :
    realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode)) =
    w.expect (after f (protectedPhase A G t cache) (seen A cache).card
      (classCounts G cache decode) (classCounts A cache decode)) := by
  have h := protected_query_law w A G hAG decode hfiber t cache f
  rw [WeightedProtectedCache.protectedImpl_eq] at h
  exact h

theorem actual_payoff_support
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (f : ℕ → (ι → ℕ) → (ι → ℕ) → ℝ)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run cache)) :
    ∃ x : Option ι, f (seen A out.2).card (classCounts G out.2 decode)
        (classCounts A out.2 decode) =
      after f (protectedPhase A G t cache) (seen A cache).card
        (classCounts G cache decode) (classCounts A cache decode) x := by
  have h := protected_payoff_support A G hAG decode t cache f out
  rw [WeightedProtectedCache.protectedImpl_eq] at h
  exact h hout

#print axioms actual_query_law
#print axioms actual_payoff_support
end WeightedDualCache
end
end

/- Original module: Submissions.UpperCompressions.DualCountSteps; SHA256 5b85c2e6e33374c2c2850c6998197a49f714f69ea5e6c2c7b9344d97d4207fcd. -/
section

/-! Exact deterministic count increments for every supported primitive answer. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedDualCache
open WeightedCacheCounts WeightedDirectCache
variable {D B : Type} [DecidableEq D] [SampleableType B]

def globalStep : Phase → ℕ | .idle => 0 | _ => 1
def rowStep : Phase → ℕ | .inside => 1 | _ => 0

theorem phase_steps (A G : Finset D) (hAG : A ⊆ G) (q : D)
    (c : (D →ₒ B).QueryCache) :
    globalStep (phase A G q c) = (if fresh G q c then 1 else 0) ∧
      rowStep (phase A G q c) = (if fresh A q c then 1 else 0) := by
  cases hc : c q with
  | some u => simp [phase,fresh,hc,globalStep,rowStep]
  | none =>
    by_cases hA : q∈A
    · simp [phase,fresh,hc,hA,hAG hA,globalStep,rowStep]
    · by_cases hG : q∈G <;> simp [phase,fresh,hc,hA,hG,globalStep,rowStep]

theorem protected_phase_steps (A G : Finset D) (hAG : A ⊆ G)
    (t : (unifSpec+(D →ₒ B)).Domain) (c : (D →ₒ B).QueryCache) :
    globalStep (protectedPhase A G t c) = (if protectedFresh G t c then 1 else 0) ∧
      rowStep (protectedPhase A G t c) = (if protectedFresh A t c then 1 else 0) := by
  cases t with
  | inl t => simp [protectedPhase,protectedFresh,globalStep,rowStep]
  | inr q => exact phase_steps A G hAG q c

theorem hash_seen_count (A : Finset D) (q : D) (c : (D →ₒ B).QueryCache)
    (out : B × (D →ₒ B).QueryCache)
    (hout : out ∈ support (((D →ₒ B).randomOracle q).run c)) :
    (seen A out.2).card = (seen A c).card+(if fresh A q c then 1 else 0) := by
  rw [randomOracle.run_eq] at hout
  cases hc : c q with
  | some u =>
    simp only [hc,support_pure,Set.mem_singleton_iff] at hout
    subst out
    simp [fresh,hc]
  | none =>
    simp only [hc,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hout
    obtain ⟨u,hu,rfl⟩ := hout
    by_cases hq : q∈A
    · have hcount : (seen A (c.cacheQuery q u)).card=(seen A c).card+1 :=
        seen_card_update A c q u hq hc
      simpa only [fresh,hq,decide_true,hc,Option.isNone_none,Bool.and_self,ite_true] using hcount
    · rw [show seen A (c.cacheQuery q u)=seen A c from seen_update_of_not_mem A c q u hq]
      simp [fresh,hq]

theorem protected_seen_count (A : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (c : (D →ₒ B).QueryCache) (out : (unifSpec+(D →ₒ B)).Range t × (D →ₒ B).QueryCache)
    (hout : out ∈ support ((protectedImpl (D := D) (B := B) t).run c)) :
    (seen A out.2).card = (seen A c).card+(if protectedFresh A t c then 1 else 0) := by
  cases t with
  | inl t =>
    change out ∈ support ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,c)) at hout
    obtain ⟨u,hu,hp⟩ := (mem_support_bind_iff _ _ _).1 hout
    simp only [support_pure,Set.mem_singleton_iff] at hp
    subst out
    simp [protectedFresh]
  | inr q => exact hash_seen_count A q c out hout

theorem actual_seen_count (A : Finset OptimalOTS.Query) (t : OptimalOTS.Spec.Domain)
    (c : OptimalOTS.hashSpec.QueryCache)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run c)) :
    (seen A out.2).card = (seen A c).card+(if protectedFresh A t c then 1 else 0) := by
  have h := protected_seen_count A t c out
  rw [WeightedProtectedCache.protectedImpl_eq] at h
  exact h hout

#print axioms actual_seen_count
end WeightedDualCache
end
end

/- Original module: Submissions.UpperCompressions.WideDistinctCharge; SHA256 fa52ab5aa023ea80bb26a1dc97b4f18cf7b546698294de0ba62ef88f930e9ec7. -/
section

/-! Distinct public inputs are charged to the same actual query stream.
The initial cache contribution is explicit; private sampling queries add no
public input. Repeated hash queries remain paid but cannot increase the count. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
namespace WeightedDualCache
open OptimalOTS WeightedCacheCounts WeightedDirectCache WeightedReplacement
set_option maxHeartbeats 800000
attribute [local irreducible] Finset.univ Finset.filter

theorem expected_seen_le_charge {β : Type} (A : Finset Query)
    (charge : Spec.Domain → ℝ≥0∞)
    (hcharge : ∀ t c, ((if protectedFresh A t c then 1 else 0 : ℕ) : ℝ≥0∞) ≤ charge t)
    (oa : OracleComp Spec β) (c : Cache) :
    E (run oa c) (fun p => ((seen A p.2).card : ℝ≥0∞)) ≤
      ((seen A c).card : ℝ≥0∞) + expectedCharge charge oa c := by
  have hstep (t : Spec.Domain) (d : Cache) :
      E ((oracleImpl t).run d) (fun p => ((seen A p.2).card : ℝ≥0∞)) ≤
        ((seen A d).card : ℝ≥0∞) + 1*charge t := by
    apply (expectedValue_mono_of_support (h := fun _ =>
      ((seen A d).card : ℝ≥0∞) + 1*charge t) ?_).trans (E_const_le _ _)
    intro p hp
    rw [actual_seen_count A t d p hp, Nat.cast_add, one_mul]
    exact add_le_add le_rfl (hcharge t d)
  simpa only [one_mul] using WeightedExpectedCharge.master_expected
    (fun d => ((seen A d).card : ℝ≥0∞)) charge 1 hstep oa c

theorem expected_seen_le_indexPaid {β : Type} (A : Finset Query)
    (isIndex : Spec.Domain → Prop) (hindex : ∀ q∈A, isIndex (.inr q))
    (oa : OracleComp Spec β) (c : Cache) :
    E (run oa c) (fun p => ((seen A p.2).card : ℝ≥0∞)) ≤
      ((seen A c).card : ℝ≥0∞) + expectedCharge (indexPaid isIndex) oa c := by
  apply expected_seen_le_charge A (indexPaid isIndex) _ oa c
  intro t d
  cases t with
  | inl n => simp [protectedFresh]
  | inr q =>
    by_cases h : protectedFresh A (.inr q) d
    · have hq : q∈A := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
      rw [if_pos h, Nat.cast_one, indexPaid, if_pos (hindex q hq)]
      exact_mod_cast (show 1≤queryCost (.inr q) from le_max_left _ _)
    · simp only [if_neg h, Nat.cast_zero]
      exact bot_le

#print axioms expected_seen_le_indexPaid
end WeightedDualCache

namespace OptimalOTS.WeightedConstruction.WideDomains
open WeightedCacheCounts WeightedReplacement
attribute [local irreducible] Finset.univ Finset.filter

theorem distinct_index_le_expected_paid {β : Type} (oa : OracleComp Spec β)
    (c : Cache) (hf : ∀ q : Query, q.1=342 → c q=none) :
    E (run oa c) (fun p => ((seen indexDomain p.2).card : ℝ≥0∞)) ≤
      expectedCharge (indexPaid (isIndexLength 342)) oa c := by
  have h := WeightedDualCache.expected_seen_le_indexPaid indexDomain (isIndexLength 342)
    (fun q hq => (mem_indexDomain q).mp hq) oa c
  rw [fresh_seen_empty c hf, Finset.card_empty, Nat.cast_zero, zero_add] at h
  exact h

theorem distinct_other_le_expected_paid {β : Type} (oa : OracleComp Spec β)
    (c : Cache) (hf : ∀ q : Query, q.1=342 → c q=none) :
    E (run oa c) (fun p => ((seen indexDomain p.2).card : ℝ≥0∞)) +
      expectedCharge (otherPaid (isIndexLength 342)) oa c ≤
      expectedCharge (fun t => queryCost t) oa c := by
  exact (add_le_add (distinct_index_le_expected_paid oa c hf) le_rfl).trans_eq
    (paid_split (isIndexLength 342) oa c)

theorem distinct_other_remaining_le {β : Type} (oa : OracleComp Spec β)
    (c : Cache) (hf : ∀ q : Query, q.1=342 → c q=none)
    (remaining : β × Cache → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : expectedCharge (fun t => queryCost t) oa c + E (run oa c) remaining ≤ B) :
    E (run oa c) (fun p => ((seen indexDomain p.2).card : ℝ≥0∞)) +
      expectedCharge (otherPaid (isIndexLength 342)) oa c + E (run oa c) remaining ≤ B :=
  (add_le_add (distinct_other_le_expected_paid oa c hf) le_rfl).trans hB

#print axioms distinct_index_le_expected_paid
#print axioms distinct_other_remaining_le
end OptimalOTS.WeightedConstruction.WideDomains
end
end

/- Original module: Submissions.UpperCompressions.WideHazardConstants; SHA256 82a4dba25e01371ee648aeae5ab63f4977292de45d8fbe1b26c14bdefc6e255e. -/
section

/-! Numerical closure for the predictable large-budget hazard variance. -/
noncomputable section
namespace WeightedHazardConstants
open WeightedReference WeightedConstants

def d : ℝ := (L:ℝ)*kappa/2+2*(L:ℝ)/(2:ℝ)^86

theorem d_pos : 0<d := by norm_num [d,L,kappa]

theorem large_exponent (B : ℝ) (hB : (2:ℝ)^86/10 ≤ B) :
    let a := (7:ℝ)/100*kappa*B
    let v := (182:ℝ)/100*d*kappa*B
    (2048:ℝ) ≤ a^2/(2*(v+d*a/3)) := by
  dsimp only
  have hBpos : 0<B := lt_of_lt_of_le (by norm_num) hB
  have hden : 0<2*((182:ℝ)/100*d*kappa*B+d*((7:ℝ)/100*kappa*B)/3) := by
    have := d_pos
    have : 0<kappa := by norm_num [kappa]
    positivity
  apply (le_div_iff₀ hden).2
  have hlinear : 2048*(2*((182:ℝ)/100*d*kappa+d*((7:ℝ)/100*kappa)/3)) ≤
      ((7:ℝ)/100*kappa)^2*B := by
    norm_num [d,L,kappa] at *
    linarith
  have h := mul_le_mul_of_nonneg_right hlinear hBpos.le
  nlinarith

theorem exp_neg_2048 : Real.exp (-(2048:ℝ)) ≤ ((2:ℝ)^2048)⁻¹ := by
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp : (2:ℝ)^2048 ≤ (Real.exp 1)^2048 := pow_le_pow_left₀ (by norm_num) he 2048
  rw [← Real.exp_nat_mul,mul_one] at hp
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hp

theorem message_union_margin :
    (2:ℝ)^256*Real.exp (-(2048:ℝ)) ≤ ((2:ℝ)^1792)⁻¹ := by
  have h := mul_le_mul_of_nonneg_left exp_neg_2048 (show (0:ℝ)≤2^256 by positivity)
  apply h.trans_eq
  rw [show (2048:ℕ)=256+1792 from rfl,pow_add]
  field_simp

/-- Both actual adaptive-state and hazard-union exceptions remain negligible. -/
theorem all_exception_margin (B : ℝ) (hB : 995 ≤ B) (hcap : B ≤ (2:ℝ)^127) :
    ((2:ℝ)^512)⁻¹+((2:ℝ)^1792)⁻¹+(1+B)*((2:ℝ)^761)⁻¹ ≤ kappa*B/1000 := by
  have hinv (n k : ℕ) (h : k ≤ n) : ((2:ℝ)^n)⁻¹ ≤ ((2:ℝ)^k)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) h
  have h1 := hinv 512 256 (by decide)
  have h2 := hinv 1792 256 (by decide)
  have h3 := hinv 761 384 (by decide)
  have hp : 0≤1+B := by linarith
  have hb : 1+B ≤ (2:ℝ)^128 := by linarith
  have hterm := mul_le_mul h3 hb hp (show (0:ℝ)≤((2:ℝ)^384)⁻¹ by positivity)
  have he : ((2:ℝ)^384)⁻¹*(2:ℝ)^128=((2:ℝ)^256)⁻¹ := by
    rw [show (384:ℕ)=256+128 from rfl,pow_add]
    field_simp
  rw [he,mul_comm _ (1+B)] at hterm
  have hsmall : 3*((2:ℝ)^256)⁻¹ ≤ kappa*995/1000 := by norm_num [kappa]
  have hfinal := mul_le_mul_of_nonneg_left hB (show 0≤kappa/1000 by norm_num [kappa])
  linarith


#print axioms large_exponent
#print axioms message_union_margin
#print axioms all_exception_margin
end WeightedHazardConstants
end
end

/- Original module: Submissions.UpperCompressions.WideLargeScalar; SHA256 021a27ff8929c08b1ac490302d6595a4e9fd1738fd57b45d4a06a4529c88f5d6. -/
section

/-! ENNReal closure of the shared large-budget clock. -/
noncomputable section
open ENNReal
namespace WeightedBudgetClosure
open WeightedReference WeightedConstants

theorem large_shared_ennreal (B : ℕ) (q a t r e : ℝ≥0∞)
    (hclock : q+a+t ≤ B)
    (hr : r ≤ ENNReal.ofReal (C*(91/100)*kappa)*q +
      ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)))
    (he : e ≤ ENNReal.ofReal (kappa*(B:ℝ)/1000)) :
    ENNReal.ofReal (kappa/2)*a+r+ENNReal.ofReal postRate*t+e ≤
      ENNReal.ofReal ((991:ℝ)/1000*kappa*(B:ℝ)) := by
  have hk : 0 ≤ kappa := by norm_num [kappa]
  have hc : 0 ≤ C := by norm_num [C]
  have hrate : 0 ≤ C*(91/100)*kappa := by positivity
  have hshift : 0 ≤ C*(7/100)*kappa*(B:ℝ) := by positivity
  have herr : 0 ≤ kappa*(B:ℝ)/1000 := by positivity
  have ha : ENNReal.ofReal (kappa/2) ≤ ENNReal.ofReal (C*(91/100)*kappa) :=
    ofReal_le_ofReal (by norm_num [C,kappa])
  have ht : ENNReal.ofReal postRate ≤ ENNReal.ofReal (C*(91/100)*kappa) :=
    ofReal_le_ofReal postRate_le_large
  calc
    _ ≤ ENNReal.ofReal (C*(91/100)*kappa)*a+
        (ENNReal.ofReal (C*(91/100)*kappa)*q+ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ)))+
        ENNReal.ofReal (C*(91/100)*kappa)*t+ENNReal.ofReal (kappa*(B:ℝ)/1000) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul' ha le_rfl) hr)
        (mul_le_mul' ht le_rfl)) he
    _ = ENNReal.ofReal (C*(91/100)*kappa)*(q+a+t)+
        ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ))+ENNReal.ofReal (kappa*(B:ℝ)/1000) := by ring
    _ ≤ ENNReal.ofReal (C*(91/100)*kappa)*B+
        ENNReal.ofReal (C*(7/100)*kappa*(B:ℝ))+ENNReal.ofReal (kappa*(B:ℝ)/1000) :=
      add_le_add (add_le_add (mul_le_mul' le_rfl hclock) le_rfl) le_rfl
    _ = _ := by
      rw [← ofReal_natCast B, ← ofReal_mul hrate,
        ← ofReal_add (mul_nonneg hrate (Nat.cast_nonneg B)) hshift,
        ← ofReal_add (add_nonneg (mul_nonneg hrate (Nat.cast_nonneg B)) hshift) herr]
      congr 1
      unfold C
      ring

theorem all_exception_margin_ennreal (B : ℕ) (hB : 995 ≤ B)
    (hcap : (B:ℝ) ≤ (2:ℝ)^127) :
    ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹)+
      (1+(B:ℝ≥0∞))*(2:ℝ≥0∞)⁻¹^761 ≤ ENNReal.ofReal (kappa*(B:ℝ)/1000) := by
  have h := ofReal_le_ofReal (WeightedHazardConstants.all_exception_margin (B:ℝ)
    (by exact_mod_cast hB) hcap)
  rw [ofReal_add (by positivity) (by positivity),
    ofReal_add (by positivity) (by positivity),
    ofReal_mul (by positivity), ofReal_add (by positivity) (by positivity)] at h
  norm_num only [ofReal_one, ofReal_natCast, ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),
    ofReal_inv_of_pos (by positivity : (0:ℝ)<2^761),
    ofReal_pow (by norm_num : (0:ℝ)≤2), ofReal_ofNat, inv_pow] at h
  simpa only [ENNReal.inv_pow,
    add_comm (ENNReal.ofReal (((2:ℝ)^512)⁻¹)) (ENNReal.ofReal (((2:ℝ)^1792)⁻¹))] using h

#print axioms large_shared_ennreal
#print axioms all_exception_margin_ennreal
end WeightedBudgetClosure
end
end

/- Original module: Submissions.UpperCompressions.ActualSmallSecurity; SHA256 9b6c14616ed8d0778850a7e41868397f4b01283f5bfcdc55ab1b47d65ce655e5. -/
section

/-! Small-budget numerical closure of the actual strong-forgery experiment. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
namespace OptimalOTS.WeightedConstruction.WideSmallSecurity
open WideForest WideInitialGame WeightedReplacement WeightedReference WeightedBudgetClosure
open WideStoppedPayoff WideDomains WeightedCacheCounts
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter

variable (A : forestScheme.toAlgorithm.Adversary)

def smallGood (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : Prop :=
  WideEmpirical.Good r.2.1

def pairPayoff (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C*pairEnvelope r.2.1)

theorem choose_budget {B : ℕ} (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (pk : PublicKey) : CostAtMost (A.choose pk) B :=
  OptimalOTS.AlgorithmCosts.CostAtMost.mono (choose_reserved_budget A hB pk).2 ((Nat.sub_le _ _).trans (Nat.sub_le _ _))

theorem choose_shared_clock {B : ℕ} (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (pk : PublicKey) :
    E (run (A.choose pk) ∅) (fun p => (queryCount p.2:ℝ≥0∞))+
      expectedCharge (otherPaid (isIndexLength 342)) (A.choose pk) ∅+
      E (runRemaining (A.choose pk) ∅ (B-995)) (postRemaining A pk) ≤ B := by
  have h := (add_le_add (distinct_other_le_expected_paid (A.choose pk) ∅ (fun _ _ => rfl))
    (le_refl (E (runRemaining (A.choose pk) ∅ (B-995)) (postRemaining A pk)))).trans
      (choose_spent_post_remaining_le A hB pk)
  exact h.trans (by exact_mod_cast ((Nat.sub_le (B-995) signBudget).trans (Nat.sub_le B 995)))

theorem hazard_le_pair (B : ℕ) :
    weightedClock A B (gatedHazard A (smallGood A)) ≤ weightedClock A B (pairPayoff A) := by
  apply Finset.sum_le_sum
  intro pk hpk
  apply mul_le_mul_right
  apply E_mono
  intro r
  by_cases hg : smallGood A pk r
  · rw [gatedHazard,if_pos hg,pairPayoff]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (hazard_le_pairEnvelope r.1.1 r.2.1) (by norm_num [C])
  · rw [gatedHazard,if_neg hg]
    exact bot_le

theorem bad_gate_bound (B : ℕ) :
    weightedClock A B (badGate A (smallGood A)) ≤ ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have ht (pk : PublicKey) :
      E (runRemaining (A.choose pk) ∅ (B-995)) (badGate A (smallGood A) pk) ≤
        ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
    have h := WideEmpirical.terminal_bad (A.choose pk) ∅ (fun _ _ => rfl)
    change Pr[fun out => ¬WideEmpirical.Good out.2 | run (A.choose pk) ∅] ≤ _ at h
    rw [← expectedValue_ite_one] at h
    change E (run (A.choose pk) ∅) _ ≤ _ at h
    rw [← runRemaining_project (A.choose pk) ∅ (B-995),E_map] at h
    convert h using 1
    congr 1
    funext r
    unfold badGate smallGood
    by_cases hg : WideEmpirical.Good r.2.1 <;> simp only [hg,not_true_eq_false,not_false_eq_true,if_true,if_false]
  calc
    _ ≤ ∑ pk : PublicKey,sumW (fiberA pk)*ENNReal.ofReal (((2:ℝ)^512)⁻¹) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul_right (ht pk) _
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

theorem small_core_bound {B : ℕ} (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (hBN : (B:ℝ) ≤ (2:ℝ)^86/10) :
    preAuth A+weightedClock A B (pairPayoff A)+
      ENNReal.ofReal postRate*weightedClock A B (postRemaining A)+
      ENNReal.ofReal (kappa*(B:ℝ)/1000) ≤
        ENNReal.ofReal ((243337:ℝ)/245000*kappa*(B:ℝ)) := by
  have hp (pk : PublicKey) := actual_small_shared_ennreal (A.choose pk) B
    (choose_budget A hB pk) hBN ∅ (fun _ _ => rfl)
    (expectedCharge (otherPaid (isIndexLength 342)) (A.choose pk) ∅)
    (E (runRemaining (A.choose pk) ∅ (B-995)) (postRemaining A pk))
    (choose_shared_clock A hB pk)
  have hpair (pk : PublicKey) :
      E (runRemaining (A.choose pk) ∅ (B-995)) (pairPayoff A pk)=
        ENNReal.ofReal C*E (run (A.choose pk) ∅) (fun p => ENNReal.ofReal (pairEnvelope p.2)) := by
    rw [E_const_mul]
    have h := runRemaining_project (A.choose pk) ∅ (B-995)
    rw [← h,E_map]
    congr 1
    funext r
    exact ENNReal.ofReal_mul (by norm_num [C])
  have hs : (∑ pk : PublicKey,sumW (fiberA pk)*
      (E (runRemaining (A.choose pk) ∅ (B-995)) (pairPayoff A pk)+
        ENNReal.ofReal (kappa/2)*expectedCharge (otherPaid (isIndexLength 342)) (A.choose pk) ∅+
        ENNReal.ofReal postRate*E (runRemaining (A.choose pk) ∅ (B-995)) (postRemaining A pk)+
        ENNReal.ofReal (kappa*(B:ℝ)/1000))) ≤
      ENNReal.ofReal ((243337:ℝ)/245000*kappa*(B:ℝ)) := by
    calc
      _ ≤ ∑ pk : PublicKey,sumW (fiberA pk)*
          ENNReal.ofReal ((243337:ℝ)/245000*kappa*(B:ℝ)) := by
        apply Finset.sum_le_sum
        intro pk hpk
        apply mul_le_mul_right
        rw [hpair]
        exact hp pk
      _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]
  convert hs using 1
  unfold preAuth weightedClock
  rw [authRate_ofReal]
  simp only [mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,sum_fiber_weights,one_mul,Finset.mul_sum]
  congr 2
  · rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro pk hpk
    rw [show msgBits+86=342 from rfl]
    ring
  · apply Finset.sum_congr rfl
    intro pk hpk
    ring

/-- Actual strong-success bound with every probabilistic premise discharged. -/
theorem actual_small_security {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (hBN : (B:ℝ) ≤ (2:ℝ)^86/10) (hcap : (B:ℝ) ≤ (2:ℝ)^127) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      ENNReal.ofReal ((243337:ℝ)/245000*kappa*(B:ℝ)) := by
  have hex := global_actual_payoff_expanded A hB (smallGood A) (fun _ _ h => h)
  have hbad := bad_gate_bound A B
  have hh := hazard_le_pair A B
  have he := all_exception_margin_ennreal B (keygen_remaining A hB).1 hcap
  have herr : weightedClock A B (badGate A (smallGood A))+
      (1+(B:ℝ≥0∞))*(2:ℝ≥0∞)⁻¹^761 ≤ ENNReal.ofReal (kappa*(B:ℝ)/1000) := by
    apply (add_le_add hbad le_rfl).trans
    apply le_trans _ he
    exact add_le_add (le_add_self : ENNReal.ofReal (((2:ℝ)^512)⁻¹) ≤
      ENNReal.ofReal (((2:ℝ)^1792)⁻¹)+ENNReal.ofReal (((2:ℝ)^512)⁻¹)) le_rfl
  have hm := add_le_add
    (add_le_add (add_le_add (le_refl (preAuth A)) hh)
      (le_refl (ENNReal.ofReal postRate*weightedClock A B (postRemaining A)))) herr
  have hc := small_core_bound A hB hBN
  rw [add_assoc (preAuth A + weightedClock A B (gatedHazard A (smallGood A)) +
    ENNReal.ofReal postRate*weightedClock A B (postRemaining A))] at hex
  exact hex.trans (hm.trans hc)

#print axioms actual_small_security
#print axioms choose_shared_clock
#print axioms bad_gate_bound
#print axioms small_core_bound
end OptimalOTS.WeightedConstruction.WideSmallSecurity
end
end

/- Original module: Submissions.UpperCompressions.WideHazardLaw; SHA256 6fc05f30d40e8484d318e6ee16ceee106b07b55c20d8596452888f7a5c9976b0. -/
section

/-! The concrete row hazard is a function of the actual shared oracle cache.
This file identifies its complete primitive-query distribution. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical

namespace WeightedDualCache
theorem protectedPhase_inside_witness {D B : Type} [DecidableEq D]
    (A G : Finset D) (t : (unifSpec+(D →ₒ B)).Domain) (c : (D →ₒ B).QueryCache)
    (h : protectedPhase A G t c = .inside) :
    ∃ q : D, c q=none ∧ q∈A := by
  cases t with
  | inl t => simp [protectedPhase] at h
  | inr q =>
    cases hc : c q with
    | some u => simp [protectedPhase,phase,hc] at h
    | none =>
      refine ⟨q,hc,?_⟩
      by_contra hn
      simp only [protectedPhase,phase,hc,Option.isSome_none,Bool.false_eq_true,ite_false,hn] at h
      split_ifs at h
end WeightedDualCache

namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedCacheCounts WeightedRow.Weights
open WeightedRealExecution WeightedDualCache WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter

def N : ℝ := 2^86
def rowCount (m : Message) (c : hashSpec.QueryCache) : ℕ :=
  (WeightedCacheCounts.seen (rowDomain m) c).card
def globalCounts (c : hashSpec.QueryCache) : Fin M → ℕ :=
  classCounts indexDomain c decode
def rowCounts (m : Message) (c : hashSpec.QueryCache) : Fin M → ℕ :=
  classCounts (rowDomain m) c decode
def hazard (m : Message) (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.hazard N (rowCount m c) (globalCounts c) (rowCounts m c)
def queryPhase (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache) : Phase :=
  protectedPhase (rowDomain m) indexDomain t c
def nextHazard (s : Phase) (m : Message) (c : hashSpec.QueryCache) : Option (Fin M) → ℝ :=
  after (securityWeights.hazard N) s (rowCount m c) (globalCounts c) (rowCounts m c)
def delta (s : Phase) (m : Message) (c : hashSpec.QueryCache) (x : Option (Fin M)) : ℝ :=
  nextHazard s m c x-hazard m c

theorem primitive_joint_law (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (f : ℕ → (Fin M → ℕ) → (Fin M → ℕ) → ℝ) :
    realEval ((oracleImpl t).run c)
      (fun out => f (rowCount m out.2) (globalCounts out.2) (rowCounts m out.2)) =
    securityWeights.expect (after f (queryPhase m t c) (rowCount m c)
      (globalCounts c) (rowCounts m c)) :=
  WeightedDualCache.actual_query_law securityWeights (rowDomain m) indexDomain
    (row_subset m) decode decoder_law t c f


theorem primitive_delta_law (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (f : ℝ → ℝ) :
    realEval ((oracleImpl t).run c) (fun out => f (hazard m out.2-hazard m c)) =
    securityWeights.expect (fun x => f (delta (queryPhase m t c) m c x)) := by
  have h := primitive_joint_law m t c
    (fun r k row => f (securityWeights.hazard N r k row-hazard m c))
  exact h.trans (congrArg securityWeights.expect (after_comp
    (fun z => f (z-hazard m c)) (securityWeights.hazard N)
    (queryPhase m t c) (rowCount m c) (globalCounts c) (rowCounts m c)))


theorem row_le_global (m : Message) (c : hashSpec.QueryCache) (i : Fin M) :
    rowCounts m c i ≤ globalCounts c i := row_class_le_global m c i

theorem rowCount_le (m : Message) (c : hashSpec.QueryCache) : (rowCount m c : ℝ) ≤ N := by
  have h : (rowCount m c : ℝ) ≤ ((2^86 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (seen_row_bound m c)
  exact h.trans_eq (by norm_num [N])


theorem inside_rowCount_succ_le (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (h : queryPhase m t c = .inside) :
    (rowCount m c : ℝ)+1 ≤ N := by
  obtain ⟨q,hc,hq⟩ := protectedPhase_inside_witness (rowDomain m) indexDomain t c h
  have hb : (((rowCount m c)+1 : ℕ) : ℝ) ≤ ((2^86 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (fresh_row_succ_bound m c q hq hc)
  have he : (((rowCount m c)+1 : ℕ) : ℝ) = (rowCount m c : ℝ)+1 :=
    (Nat.cast_add (rowCount m c) 1).trans
      (congrArg (fun z : ℝ => (rowCount m c : ℝ)+z) Nat.cast_one)
  exact he.symm.trans_le (hb.trans_eq (by norm_num [N]))

theorem primitive_delta_support (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    ∃ x : Option (Fin M), hazard m out.2-hazard m c = delta (queryPhase m t c) m c x := by
  obtain ⟨x,hx⟩ := actual_payoff_support (rowDomain m) indexDomain (row_subset m)
    decode t c (securityWeights.hazard N) out hout
  exact ⟨x,congrArg (fun z => z-hazard m c) hx⟩

#print axioms primitive_delta_law
#print axioms inside_rowCount_succ_le
#print axioms primitive_delta_support
end OptimalOTS.WeightedConstruction.WideHazard
end
end

/- Original module: Submissions.UpperCompressions.WideHazardMoments; SHA256 400052f4bc0f3b60c08b20fbbe6137ebeb1f99befe1f3f6e9c76cf454bcba892. -/
section

/-! Actual primitive-query drift and variance of the clipped row hazard.
The row-score premise is explicit; no complete-game security statement is made. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedRow.Weights
open WeightedRealExecution WeightedDualCache WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter queryPhase rowCount globalCounts rowCounts

def gain (s : Phase) (m : Message) (c : hashSpec.QueryCache) : Option (Fin M) → ℝ :=
  match s with
  | .idle => fun _ => 0
  | .outside => securityWeights.positiveOutside N (rowCount m c) (globalCounts c) (rowCounts m c)
  | .inside => securityWeights.positiveInside N (rowCount m c) (globalCounts c) (rowCounts m c)

def shift (s : Phase) (c : hashSpec.QueryCache) : ℝ :=
  match s with
  | .inside => securityWeights.seen (globalCounts c)/N
  | _ => 0

def jumpBound : ℝ := (L:ℝ)*kappa/2+2*(L:ℝ)/N

def drift (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache) : ℝ :=
  realEval ((oracleImpl t).run c) (fun out => hazard m out.2-hazard m c)

theorem delta_gain_shift (s : Phase) (m : Message) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) : delta s m c x = gain s m c x-shift s c := by
  cases s with
  | idle => simp [delta,nextHazard,after,hazard,gain,shift]
  | outside =>
    have h := securityWeights.increment_outside N (rowCount m c) (globalCounts c) (rowCounts m c) x
    cases x <;> simpa only [delta,nextHazard,after,advance,hazard,gain,shift,
      afterOutside,sub_zero] using h
  | inside =>
    have h := securityWeights.increment_inside N (rowCount m c) (globalCounts c) (rowCounts m c) x
    cases x <;> simpa only [delta,nextHazard,after,advance,hazard,gain,shift,
      afterInside] using h

theorem seen_le_one (c : hashSpec.QueryCache) : securityWeights.seen (globalCounts c) ≤ 1 := by
  calc
    securityWeights.seen (globalCounts c) ≤ ∑ i : Fin M,referenceWeight i := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact referenceWeight_nonneg i
      · exact le_rfl
    _ = 1-failure := referenceWeight_sum
    _ ≤ 1 := sub_le_self _ failure_nonneg

theorem shift_le (s : Phase) (c : hashSpec.QueryCache) : shift s c ≤ 1/N := by
  cases s with
  | idle => exact le_of_lt (by norm_num [shift,N])
  | outside => exact le_of_lt (by norm_num [shift,N])
  | inside => exact div_le_div_of_nonneg_right (seen_le_one c) (by norm_num [N])

theorem gain_bounds (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) :
    0 ≤ gain (queryPhase m t c) m c x ∧ gain (queryPhase m t c) m c x ≤ jumpBound := by
  cases hs : queryPhase m t c with
  | idle => constructor <;> norm_num [gain,jumpBound,L,kappa,N]
  | outside =>
    exact securityWeights.positiveOutside_bounds N (by norm_num [N]) (rowCount m c)
      (rowCount_le m c) (globalCounts c) (rowCounts m c) (row_le_global m c)
      ((L:ℝ)*kappa/2) L (by norm_num [L,kappa]) (by norm_num [L])
      referenceWeight_le weight_ratio_le x
  | inside =>
    exact securityWeights.positiveInside_bounds N (by norm_num [N]) (rowCount m c)
      (inside_rowCount_succ_le m t c hs) (globalCounts c) (rowCounts m c) (row_le_global m c)
      ((L:ℝ)*kappa/2) L (by norm_num [L,kappa]) (by norm_num [L])
      referenceWeight_le weight_ratio_le x

theorem delta_drift_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+η*kappa*N) :
    securityWeights.expect (delta (queryPhase m t c) m c) ≤ securityWeights.mean+η*kappa := by
  cases hs : queryPhase m t c with
  | idle =>
    have hz : delta Phase.idle m c = fun _ => 0 := by
      funext x
      exact sub_self _
    rw [hz,expect_const]
    have hm : 0 ≤ securityWeights.mean := by
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (securityWeights.p_pos i).le
        (securityWeights.g_nonneg i))
    exact add_nonneg hm (mul_nonneg hη (by norm_num [kappa]))
  | outside =>
    exact securityWeights.drift_outside_le N (by norm_num [N]) (rowCount m c)
      (rowCount_le m c) (globalCounts c) (rowCounts m c) η kappa hscore
  | inside =>
    exact securityWeights.drift_inside_le N (by norm_num [N]) (rowCount m c)
      (rowCount_le m c) (globalCounts c) (rowCounts m c) η kappa hscore

theorem drift_eq (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache) :
    drift m t c = securityWeights.expect (delta (queryPhase m t c) m c) :=
  primitive_delta_law m t c id

theorem actual_drift_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+η*kappa*N) :
    drift m t c ≤ securityWeights.mean+η*kappa := by
  rw [drift_eq]
  exact delta_drift_le m t c η hη hscore

theorem gain_mean_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+η*kappa*N) :
    securityWeights.expect (gain (queryPhase m t c) m c) ≤
      securityWeights.mean+η*kappa+1/N := by
  have h := delta_drift_le m t c η hη hscore
  simp only [show delta (queryPhase m t c) m c =
      (fun x => gain (queryPhase m t c) m c x-shift (queryPhase m t c) c) from
    funext (delta_gain_shift _ _ _),expect_sub,expect_const] at h
  linarith [shift_le (queryPhase m t c) c]

theorem centered_delta (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) :
    delta (queryPhase m t c) m c x-drift m t c =
      gain (queryPhase m t c) m c x-securityWeights.expect (gain (queryPhase m t c) m c) := by
  rw [drift_eq]
  simp only [show delta (queryPhase m t c) m c =
      (fun x => gain (queryPhase m t c) m c x-shift (queryPhase m t c) c) from
    funext (delta_gain_shift _ _ _)]
  exact securityWeights.center_predictable_shift _ _ x

theorem centered_delta_abs_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (x : Option (Fin M)) : |delta (queryPhase m t c) m c x-drift m t c| ≤ jumpBound := by
  rw [centered_delta]
  exact securityWeights.centered_abs_le _ _ (gain_bounds m t c) x

theorem actual_variance_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (η : ℝ) (hη : 0 ≤ η)
    (hscore : securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+η*kappa*N) :
    realEval ((oracleImpl t).run c)
      (fun out => (hazard m out.2-hazard m c-drift m t c)^2) ≤
    jumpBound*(securityWeights.mean+η*kappa+1/N) := by
  rw [primitive_delta_law m t c (fun z => (z-drift m t c)^2)]
  simp only [centered_delta]
  exact (securityWeights.centered_variance_le _ _ (gain_bounds m t c)).trans
    (mul_le_mul_of_nonneg_left (gain_mean_le m t c η hη hscore)
      (by norm_num [jumpBound,L,kappa,N]))

theorem actual_centered_abs_le (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    |hazard m out.2-hazard m c-drift m t c| ≤ jumpBound := by
  obtain ⟨x,hx⟩ := primitive_delta_support m t c out hout
  rw [hx]
  exact centered_delta_abs_le m t c x

#print axioms actual_drift_le
#print axioms gain_bounds
#print axioms actual_variance_le
#print axioms centered_delta_abs_le
#print axioms actual_centered_abs_le
end OptimalOTS.WeightedConstruction.WideHazard
end
end

/- Original module: Submissions.UpperCompressions.WideHazardGood; SHA256 3355d9b97a14c3cf0cfdf60bf7d7d25ffb8dac96ae9512d1b8d8c700d2de1e1c. -/
section

/-! The actual common empirical Good event bounds the clipped-hazard drift
and its cumulative inside-row variance contribution. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedRow.Weights
open WeightedRealExecution WeightedDualCache WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter queryPhase

def globalCount (c : hashSpec.QueryCache) : ℕ :=
  (WeightedCacheCounts.seen indexDomain c).card
def alpha : ℝ := (91/100)*kappa
def gainRate (B : ℝ) (s : Phase) : ℝ :=
  alpha*(globalStep s : ℝ)+alpha*B/N*(rowStep s : ℝ)

theorem mean_margin_le : securityWeights.mean+kappa/100 ≤ alpha := by
  have h := securityWeights_mean
  unfold alpha
  linarith [show (0:ℝ)≤kappa by norm_num [kappa]]

theorem good_row_hyp (m : Message) (c : hashSpec.QueryCache) (hc : WideEmpirical.Good c) :
    securityWeights.score (rowCounts m c) ≤
      (rowCount m c : ℝ)*securityWeights.mean+(1/100)*kappa*N := by
  have h := WideEmpirical.good_row_score c hc m
  change securityWeights.score (rowCounts m c) ≤
    securityWeights.mean*(rowCount m c : ℝ)+kappa*(2:ℝ)^86/100 at h
  exact h.trans_eq (by unfold N; ring)

theorem good_global_seen (B : ℝ) (c : hashSpec.QueryCache) (hc : WideEmpirical.Good c)
    (hB : N/10 ≤ B) (hq : (globalCount c : ℝ) ≤ B) :
    securityWeights.seen (globalCounts c) ≤ alpha*B := by
  have hs := WideEmpirical.good_global c hc
  change securityWeights.score (globalCounts c) ≤
    securityWeights.mean*(globalCount c : ℝ)+(kappa/100)*max (globalCount c : ℝ) (N/10) at hs
  have hm0 : 0 ≤ securityWeights.mean :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (securityWeights.p_pos i).le
      (securityWeights.g_nonneg i))
  have hmax : max (globalCount c : ℝ) (N/10) ≤ B := max_le hq hB
  have h1 := mul_le_mul_of_nonneg_left hq hm0
  have h2 := mul_le_mul_of_nonneg_left hmax (show 0≤kappa/100 by norm_num [kappa])
  have h3 := mul_le_mul_of_nonneg_right mean_margin_le ((Nat.cast_nonneg (globalCount c) : (0:ℝ)≤globalCount c).trans hq)
  exact (securityWeights.seen_le_score (globalCounts c)).trans (by nlinarith)

theorem good_delta_drift (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (hc : WideEmpirical.Good c) :
    securityWeights.expect (delta (queryPhase m t c) m c) ≤
      alpha*(globalStep (queryPhase m t c) : ℝ) := by
  have h := (delta_drift_le m t c (1/100) (by norm_num) (good_row_hyp m c hc)).trans
    (show securityWeights.mean+(1/100)*kappa ≤ alpha from
      (by calc
        _ = securityWeights.mean+kappa/100 := by ring
        _ ≤ alpha := mean_margin_le))
  cases hs : queryPhase m t c with
  | idle =>
    have hz : delta Phase.idle m c = fun _ => 0 := by funext x; exact sub_self _
    rw [hz,expect_const]
    simp [globalStep]
  | outside => simpa only [hs,globalStep,Nat.cast_one,mul_one] using h
  | inside => simpa only [hs,globalStep,Nat.cast_one,mul_one] using h

theorem good_gain_mean (B : ℝ) (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (hc : WideEmpirical.Good c) (hB : N/10 ≤ B) (hq : (globalCount c : ℝ) ≤ B) :
    securityWeights.expect (gain (queryPhase m t c) m c) ≤ gainRate B (queryPhase m t c) := by
  have hd := good_delta_drift m t c hc
  have he : securityWeights.expect (delta (queryPhase m t c) m c) =
      securityWeights.expect (gain (queryPhase m t c) m c)-shift (queryPhase m t c) c := by
    simp only [show delta (queryPhase m t c) m c =
      (fun x => gain (queryPhase m t c) m c x-shift (queryPhase m t c) c) from
      funext (delta_gain_shift _ _ _),expect_sub,expect_const]
  have hs := div_le_div_of_nonneg_right (good_global_seen B c hc hB hq)
    (show 0≤N by norm_num [N])
  cases hp : queryPhase m t c with
  | idle =>
    simp only [gain,expect_const,gainRate,globalStep,rowStep,Nat.cast_zero,mul_zero,add_zero]
    exact le_rfl
  | outside =>
    simp only [hp,shift,globalStep,Nat.cast_one,mul_one,sub_zero] at he hd
    simpa only [gainRate,globalStep,rowStep,Nat.cast_one,Nat.cast_zero,mul_one,mul_zero,add_zero]
      using he.symm.trans_le hd
  | inside =>
    simp only [hp,shift,globalStep,Nat.cast_one,mul_one] at he hd
    simp only [gainRate,globalStep,rowStep,Nat.cast_one,mul_one]
    linarith

#print axioms good_global_seen
#print axioms good_delta_drift
#print axioms good_gain_mean
end OptimalOTS.WeightedConstruction.WideHazard
end
end

/- Original module: Submissions.UpperCompressions.WideHazardMGF; SHA256 5162f17e32a272361cdd64cbb4aae50b57ea043f0f42b71d185eb6b3202afea2. -/
section

/-! Compensated exponential drift under the concrete common Good event. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WeightedRow.Weights WeightedRealExecution WeightedDualCache
open WeightedReference WeightedConstants WeightedEmpirical
attribute [local irreducible] Finset.univ Finset.filter queryPhase

theorem good_delta_mgf (B : ℝ) (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (hc : WideEmpirical.Good c) (hB : N/10 ≤ B) (hq : (globalCount c : ℝ) ≤ B)
    (θ : ℝ) (hθ : 0≤θ) (hθJ : θ*jumpBound<3) :
    securityWeights.expect (fun x => Real.exp
      (θ*(delta (queryPhase m t c) m c x-alpha*(globalStep (queryPhase m t c):ℝ))-
        θ^2*(jumpBound*gainRate B (queryPhase m t c))/(2*(1-θ*jumpBound/3)))) ≤ 1 := by
  let X : Option (Fin M) → ℝ := fun x => delta (queryPhase m t c) m c x-
    securityWeights.expect (delta (queryPhase m t c) m c)
  have hX (x : Option (Fin M)) : X x = gain (queryPhase m t c) m c x-
      securityWeights.expect (gain (queryPhase m t c) m c) := by
    dsimp only [X]
    rw [←drift_eq]
    exact centered_delta m t c x
  have hb (x : Option (Fin M)) : |X x|≤jumpBound := by
    rw [hX]
    exact securityWeights.centered_abs_le _ _ (gain_bounds m t c) x
  have hm : expectLinear securityWeights X=0 := by
    change securityWeights.expect X=0
    dsimp only [X]
    rw [expect_sub,expect_const,sub_self]
  have hJ : 0≤jumpBound := by norm_num [jumpBound,L,kappa,N]
  have hv : expectLinear securityWeights (fun x => (X x)^2) ≤
      jumpBound*gainRate B (queryPhase m t c) := by
    change securityWeights.expect (fun x => (X x)^2) ≤ _
    simp only [hX]
    exact (securityWeights.centered_variance_le _ _ (gain_bounds m t c)).trans
      (mul_le_mul_of_nonneg_left (good_gain_mean B m t c hc hB hq) hJ)
  have hmgf := WeightedMGF.compensated_mgf (expectLinear securityWeights)
    securityWeights.expect_mono (securityWeights.expect_const 1) X θ jumpBound
    (jumpBound*gainRate B (queryPhase m t c)) hθ hJ hθJ hb hm hv
  change securityWeights.expect (fun x => Real.exp (θ*X x-
    θ^2*(jumpBound*gainRate B (queryPhase m t c))/(2*(1-θ*jumpBound/3)))) ≤ 1 at hmgf
  have hd := good_delta_drift m t c hc
  apply (securityWeights.expect_mono _ _ (fun x => ?_)).trans hmgf
  apply Real.exp_le_exp.mpr
  dsimp only [X]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (sub_le_sub_left hd _) hθ) _

theorem actual_good_delta_mgf (B : ℝ) (m : Message) (t : Spec.Domain)
    (c : hashSpec.QueryCache) (hc : WideEmpirical.Good c)
    (hB : N/10 ≤ B) (hq : (globalCount c : ℝ) ≤ B)
    (θ : ℝ) (hθ : 0≤θ) (hθJ : θ*jumpBound<3) :
    realEval ((oracleImpl t).run c) (fun out => Real.exp
      (θ*(hazard m out.2-hazard m c-alpha*(globalStep (queryPhase m t c):ℝ))-
        θ^2*(jumpBound*gainRate B (queryPhase m t c))/(2*(1-θ*jumpBound/3)))) ≤ 1 :=
  (primitive_delta_law m t c (fun z => Real.exp
    (θ*(z-alpha*(globalStep (queryPhase m t c):ℝ))-
      θ^2*(jumpBound*gainRate B (queryPhase m t c))/(2*(1-θ*jumpBound/3))))).trans_le
        (good_delta_mgf B m t c hc hB hq θ hθ hθJ)

#print axioms good_delta_mgf
#print axioms actual_good_delta_mgf
end OptimalOTS.WeightedConstruction.WideHazard
end
end

/- Original module: Submissions.UpperCompressions.WideHazardClock; SHA256 5bdf9af4953237387b4bb6e64ad0baff6e646000d37df69789567f1ca551153c. -/
section

/-! The variance clock counts actual fresh global inputs and actual nonce-row
positions. Private draws, repeated cache hits, and nonindex hashes do not move it. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedRow.Weights WeightedRealExecution WeightedDualCache
open WeightedReference WeightedConstants WeightedOracleExecution
attribute [local irreducible] Finset.univ Finset.filter

def Z (m : Message) (c : hashSpec.QueryCache) : ℝ := hazard m c-alpha*(globalCount c:ℝ)
def cap (c : hashSpec.QueryCache) : ℝ := max (globalCount c:ℝ) (N/10)
def W (m : Message) (c : hashSpec.QueryCache) : ℝ :=
  jumpBound*alpha*((globalCount c:ℝ)+cap c*(rowCount m c:ℝ)/N)

theorem clock_growth (q r u v : ℝ) (hr : 0≤r) (hu : 0≤u) (hv : 0≤v) :
    jumpBound*alpha*(q+max q (N/10)*r/N)+
      jumpBound*(alpha*u+alpha*max q (N/10)/N*v) ≤
    jumpBound*alpha*((q+u)+max (q+u) (N/10)*(r+v)/N) := by
  have hm : max q (N/10) ≤ max (q+u) (N/10) := max_le_max_right _ (by linarith)
  have hp := mul_le_mul_of_nonneg_right hm (add_nonneg hr hv)
  have hd := div_le_div_of_nonneg_right hp (show 0≤N by norm_num [N])
  have hj : 0≤jumpBound*alpha := by norm_num [jumpBound,alpha,L,kappa,N]
  have h := mul_le_mul_of_nonneg_left (add_le_add_left hd (q+u)) hj
  calc
    _ = jumpBound*alpha*((q+u)+max q (N/10)*(r+v)/N) := by ring
    _ ≤ _ := by simpa only [add_comm] using h

theorem actual_count_steps (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    globalCount out.2 = globalCount c+globalStep (queryPhase m t c) ∧
    rowCount m out.2 = rowCount m c+rowStep (queryPhase m t c) := by
  have hg := actual_seen_count indexDomain t c out hout
  have hr := actual_seen_count (rowDomain m) t c out hout
  have he := protected_phase_steps (rowDomain m) indexDomain (row_subset m) t c
  exact ⟨hg.trans (congrArg (fun n => globalCount c+n) he.1.symm),
    hr.trans (congrArg (fun n => rowCount m c+n) he.2.symm)⟩

theorem actual_ZW_steps (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (out : Spec.Range t × hashSpec.QueryCache)
    (hout : out ∈ support ((oracleImpl t).run c)) :
    Z m out.2 = Z m c+(hazard m out.2-hazard m c-alpha*(globalStep (queryPhase m t c):ℝ)) ∧
    W m c+jumpBound*gainRate (cap c) (queryPhase m t c) ≤ W m out.2 := by
  obtain ⟨hg,hr⟩ := actual_count_steps m t c out hout
  constructor
  · unfold Z
    rw [hg,Nat.cast_add]
    ring
  · unfold W cap gainRate
    rw [hg,hr,Nat.cast_add,Nat.cast_add]
    exact clock_growth _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem actual_potential_step (m : Message) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (hc : WideEmpirical.Good c)
    (θ : ℝ) (hθ : 0≤θ) (hθJ : θ*jumpBound<3) :
    expectedValue ((oracleImpl t).run c)
      (fun out => ENNReal.ofReal (Real.exp
        (θ*Z m out.2-θ^2*W m out.2/(2*(1-θ*jumpBound/3))))) ≤
      ENNReal.ofReal (Real.exp (θ*Z m c-θ^2*W m c/(2*(1-θ*jumpBound/3)))) := by
  rw [←ofReal_realEval _ _ (fun _ => Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hp := WeightedKernel.exponential_step (realEval ((oracleImpl t).run c)) (Z m c)
    (θ^2*W m c/(2*(1-θ*jumpBound/3))) θ
    (θ^2*(jumpBound*gainRate (cap c) (queryPhase m t c))/(2*(1-θ*jumpBound/3)))
    (fun out => hazard m out.2-hazard m c-alpha*(globalStep (queryPhase m t c):ℝ))
    (actual_good_delta_mgf (cap c) m t c hc (le_max_right _ _) (le_max_left _ _) θ hθ hθJ)
  apply (realEval_mono_of_support ((oracleImpl t).run c) _ _ (fun out hout => ?_)).trans hp
  obtain ⟨hz,hw⟩ := actual_ZW_steps m t c out hout
  apply Real.exp_le_exp.mpr
  rw [hz]
  have hden : 0<2*(1-θ*jumpBound/3) := by linarith
  have hv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (sq_nonneg θ)) hden.le
  rw [mul_add,add_div] at hv
  exact sub_le_sub_left hv _

theorem W_budget_bound (B : ℝ) (m : Message) (c : hashSpec.QueryCache)
    (hB : N/10≤B) (hq : (globalCount c:ℝ)≤B) :
    W m c ≤ (182/100)*jumpBound*kappa*B := by
  have hr := rowCount_le m c
  have hn : (0:ℝ)<N := by norm_num [N]
  have hcap : cap c≤B := max_le hq hB
  have hc0 : 0≤cap c := (Nat.cast_nonneg (globalCount c) : (0:ℝ)≤globalCount c).trans (le_max_left _ _)
  have hbr := mul_le_mul_of_nonneg_left ((div_le_one hn).mpr hr) hc0
  have hj : 0≤jumpBound*alpha := by norm_num [jumpBound,alpha,L,kappa,N]
  have hs : (globalCount c:ℝ)+cap c*(rowCount m c:ℝ)/N ≤ 2*B := by
    rw [←mul_div_assoc] at hbr
    linarith
  have h := mul_le_mul_of_nonneg_left hs hj
  unfold W
  exact h.trans_eq (by unfold alpha; ring)

#print axioms actual_potential_step
#print axioms W_budget_bound
end OptimalOTS.WeightedConstruction.WideHazard
end
end

/- Original module: Submissions.UpperCompressions.WideHazardFreedman; SHA256 5abf52cb1b93c9eea204542425e8ebbc6a2d85aa7fbe63ff6e0ed68519e0a12d. -/
section

/-! Actual stopped clipped-hazard concentration for one message row. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
namespace OptimalOTS.WeightedConstruction.WideHazard
open WeightedSchedule WideDomains WeightedRow.Weights WeightedRealExecution WeightedDualCache
open WeightedReference WeightedConstants WeightedOracleExecution WeightedFirstHit
attribute [local irreducible] Finset.univ Finset.filter queryPhase

def hit (B : ℕ) (m : Message) : ℕ → hashSpec.QueryCache → Prop := fun _ c =>
  (globalCount c:ℝ)≤B ∧ (7/100)*kappa*(B:ℝ)≤Z m c
def kill : ℕ → hashSpec.QueryCache → Prop := fun _ c => ¬WideEmpirical.Good c

theorem ZW_initial (m : Message) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) : Z m c=0 ∧ W m c=0 := by
  obtain ⟨hq,hk⟩ := WidePreSign.index_initial c hf
  obtain ⟨hr,hrow⟩ := WideConcentration.row_initial m c hf
  have hq' : globalCount c=0 := hq
  have hr' : rowCount m c=0 := hr
  have hk' : globalCounts c=fun _=>0 := hk
  constructor
  · simp [Z,hazard,WeightedRow.Weights.hazard,WeightedRow.Weights.seen,
      WeightedRow.Weights.bad,hq',hk']
  · simp [W,hq',hr']

theorem stopped_large_bound {β : Type} (B : ℕ) (hB : N/10≤(B:ℝ))
    (m : Message) (oa : OracleComp Spec β) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => out.2.status=.hit |
      (simulateQ (stoppedImpl oracleImpl (hit B m) kill) oa).run
        (classify (hit B m) kill 0 c)] ≤ ENNReal.ofReal (Real.exp (-(2048:ℝ))) := by
  have hb : (0:ℝ)<B := lt_of_lt_of_le (by norm_num [N]) hB
  have hk : (0:ℝ)<kappa := by norm_num [kappa]
  have hd : (0:ℝ)<jumpBound := by norm_num [jumpBound,L,kappa,N]
  obtain ⟨hz0,hw0⟩ := ZW_initial m c hf
  have h := actual_stopped_freedman oracleImpl oa (fun _ => Z m) (fun _ => W m) c
    ((7/100)*kappa*(B:ℝ)) ((182/100)*jumpBound*kappa*(B:ℝ)) jumpBound
    (by positivity) (by positivity) hd.le hz0 hw0 (hit B m) kill
    (by
      intro θ hθ hθJ t n d _ hgood
      exact actual_potential_step m t d (by simpa only [kill,not_not] using hgood)
        θ hθ.le hθJ)
    (fun _ _ hs => hs.2)
    (fun _ d hs => W_budget_bound B m d hB hs.1)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have he := WeightedHazardConstants.large_exponent (B:ℝ) hB
  change (2048:ℝ) ≤
    ((7/100)*kappa*(B:ℝ))^2/(2*((182/100)*jumpBound*kappa*(B:ℝ)+
      jumpBound*((7/100)*kappa*(B:ℝ))/3)) at he
  simpa only [neg_div] using neg_le_neg he

#print axioms ZW_initial
#print axioms stopped_large_bound
end OptimalOTS.WeightedConstruction.WideHazard
end
end

