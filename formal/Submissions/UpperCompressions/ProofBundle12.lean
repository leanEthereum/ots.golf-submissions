import Submissions.UpperCompressions.ProofBundle09
import Submissions.UpperCompressions.ProofBundle10
import Submissions.UpperCompressions.ProofBundle05
import Submissions.UpperCompressions.ProofBundle07
import Submissions.UpperCompressions.ProofBundle11
import Submissions.UpperCompressions.ProofBundle01

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

end WeightedDualCache
end
end

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

end WeightedDualCache
end
end

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

end WeightedDualCache
end
end

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

end OptimalOTS.WeightedConstruction.WideDomains
end
end

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

end
end
