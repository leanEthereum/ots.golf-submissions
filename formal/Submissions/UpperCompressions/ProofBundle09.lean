import Submissions.UpperCompressions.ProofBundle08
import Submissions.UpperCompressions.ProofBundle04
import Submissions.UpperCompressions.ProofBundle02
import Submissions.UpperCompressions.ProofBundle07
import Submissions.UpperCompressions.ProofBundle00
import Submissions.UpperCompressions.ProofBundle03
import Mathlib
import OptimalOTS.Model
import VCVio.EvalDist.Expectation

section

/-! Retain the actual pathwise remaining budget alongside the original shared
cache interpreter, without requiring a finite adversary state space. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical

def runRemaining {α : Type} (oa : OracleComp Spec α) : Cache → ℕ → ProbComp (α × Cache × ℕ) :=
  OracleComp.construct (fun a c b => pure (a,c,b))
    (fun t _ rec c b => do
      let r ← (oracleImpl t).run c
      rec r.1 r.2 (b-queryCost t)) oa

@[simp] theorem runRemaining_pure {α : Type} (a : α) (c : Cache) (b : ℕ) :
    runRemaining (pure a) c b = pure (a,c,b) := by simp [runRemaining]

theorem runRemaining_query {α : Type} (t : Spec.Domain)
    (k : Spec.Range t → OracleComp Spec α) (c : Cache) (b : ℕ) :
    runRemaining (liftM (Spec.query t) >>= k) c b =
      (oracleImpl t).run c >>= fun r => runRemaining (k r.1) r.2 (b-queryCost t) := by
  simp [runRemaining]

theorem runRemaining_project {α : Type} (oa : OracleComp Spec α) (c : Cache) (b : ℕ) :
    (fun r : α × Cache × ℕ => (r.1,r.2.1)) <$> runRemaining oa c b = run oa c := by
  induction oa using OracleComp.inductionOn generalizing c b with
  | pure a => simp [run_pure]
  | query_bind t k ih =>
    rw [runRemaining_query,run_query_bind,map_bind]
    exact bind_congr fun r => ih r.1 r.2 _

/-- All members of the continuation family inherit the same pathwise remaining
budget after every supported actual first-stage execution. -/
theorem runRemaining_family_support {α β J : Type} [Nonempty J]
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β) :
    ∀ c b, (∀ j, CostAtMost (oa >>= k j) b) →
      ∀ r ∈ support (runRemaining oa c b),
        r.2.2 ≤ b ∧ ∀ j, CostAtMost (k j r.1) r.2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c b hB r hr
    rw [runRemaining_pure,support_pure,Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl,fun j => by simpa only [pure_bind] using hB j⟩
  | query_bind t f ih =>
    intro c b hB r hr
    have hB' : ∀ a j, CostAtMost (f a >>= k j) (b-queryCost t) := by
      intro a j
      have h := hB j
      rw [bind_assoc,costAtMost_query_bind_iff] at h
      exact h.2 a
    rw [runRemaining_query,support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨p,_,hr⟩ := hr
    obtain ⟨hle,hk⟩ := ih p.1 p.2 _ (hB' p.1) r hr
    exact ⟨hle.trans (Nat.sub_le _ _),hk⟩

end
end WeightedReplacement
end

section

/-! The all-L syntactic reserve applies to every supported outcome of the
actual shared-cache signer, without a full-support assumption on that cache. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem run_output_mem_support {α : Type} (oa : OracleComp Spec α) :
    ∀ c p, p ∈ support (run oa c) → p.1 ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c p hp
    rw [run_pure,support_pure,Set.mem_singleton_iff] at hp
    subst p
    simp
  | query_bind t k ih =>
    intro c p hp
    rw [run_query_bind,support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨r,_,hp⟩ := hp
    rw [support_bind]
    simp only [Set.mem_iUnion]
    exact ⟨r.1,by simp,ih r.1 r.2 p hp⟩

theorem actual_loop_reserve {M : ℕ} {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (hc : blockCost (msgBits+n) = 1)
    (k : ℕ) (kont : Option (Winner n M) → OracleComp Spec β) (b : ℕ)
    (hB : CostAtMost (loop n decode tier m k >>= kont) b) :
    k ≤ b ∧ ∀ c p, p ∈ support (run (loop n decode tier m k) c) →
      CostAtMost (kont p.1) (b-k) := by
  obtain ⟨hk,hr⟩ := loop_reserve n decode tier m hc k kont b hB
  exact ⟨hk,fun c p hp => hr p.1 (run_output_mem_support _ c p hp)⟩

end
end WeightedReplacement
end

section

/-! The concrete finite public index domain and its nonce rows. Counts are
computed from the real cache, so each row has at most2^86 distinct inputs. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideDomains
open scoped Classical
open WeightedCacheCounts WideForest
attribute [local irreducible] Finset.univ Finset.filter

def indexDomain : Finset Query := Finset.univ.image (fun x : BitVec 342 => (⟨342,x⟩ : Query))
def rowDomain (m : Message) : Finset Query :=
  Finset.univ.image (fun η : BitVec 86 => WideForest.encQuery (m,η))

theorem mem_indexDomain (q : Query) : q ∈ indexDomain ↔ q.1=342 := by
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
    exact (congrArg Sigma.fst he).symm
  · rcases q with ⟨n,x⟩
    intro hn
    dsimp at hn
    subst n
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩

theorem mem_rowDomain (m : Message) (q : Query) :
    q ∈ rowDomain m ↔ ∃ η : BitVec 86,WideForest.encQuery (m,η)=q := by
  simp only [rowDomain,Finset.mem_image,Finset.mem_univ,true_and]

theorem row_subset (m : Message) : rowDomain m ⊆ indexDomain := by
  intro q hq
  obtain ⟨η,rfl⟩ := (mem_rowDomain m q).mp hq
  exact (mem_indexDomain _).mpr rfl

theorem row_card (m : Message) : (rowDomain m).card=2^86 := by
  unfold rowDomain
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ,Fintype.card_bitVec]
  · intro η ζ h
    exact WeightedSampling.Availability.nonce_query_inj m h

theorem seen_row_bound (m : Message) (c : hashSpec.QueryCache) :
    (seen (rowDomain m) c).card ≤ 2^86 :=
  (seen_card_le _ _).trans_eq (row_card m)

theorem seen_row_subset (m : Message) (c : hashSpec.QueryCache) :
    seen (rowDomain m) c ⊆ seen indexDomain c := by
  intro q hq
  exact Finset.mem_filter.mpr ⟨row_subset m (Finset.mem_filter.mp hq).1,
    (Finset.mem_filter.mp hq).2⟩

theorem fresh_seen_empty (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) : seen indexDomain c=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := Finset.mem_filter.mp hq
  have hc := hf q ((mem_indexDomain q).mp h.1)
  simpa only [hc,Option.isSome_none,Bool.false_eq_true] using h.2

end OptimalOTS.WeightedConstruction.WideDomains
end
end

section

/-! Signed finite expectation for actual ProbComp programs. Defined by their
uniform-query syntax, with exact bind laws and a proved ENNReal semantic bridge.
No integrability or execution-law equality is supplied as a hypothesis. -/

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal BigOperators
namespace WeightedRealExecution

set_option maxHeartbeats 800000
variable {α β : Type}

/-- The real expectation functional of a finite private-randomness program. -/
def realEval (oa : ProbComp α) : (α → ℝ) →ₗ[ℝ] ℝ :=
  OracleComp.construct (fun a => LinearMap.proj a)
    (fun q _ rec => (Fintype.card (unifSpec.Range q):ℝ)⁻¹ • ∑ u, rec u) oa

@[simp] theorem realEval_pure (a : α) (f : α → ℝ) : realEval (pure a) f = f a := by
  simp [realEval]

@[simp] theorem realEval_query_bind (q : unifSpec.Domain)
    (k : unifSpec.Range q → ProbComp α) (f : α → ℝ) :
    realEval ((liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) >>= k) f =
      (Fintype.card (unifSpec.Range q):ℝ)⁻¹ * ∑ u, realEval (k u) f := by
  simp [realEval, LinearMap.sum_apply]

/-- The real tower property follows from actual ProbComp syntax. -/
theorem realEval_bind (oa : ProbComp α) (k : α → ProbComp β) (f : β → ℝ) :
    realEval (oa >>= k) f = realEval oa (fun a => realEval (k a) f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [bind_assoc, realEval_query_bind, realEval_query_bind]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    exact ih u

/-- Positivity may be restricted to outputs in the actual computation support. -/
theorem realEval_mono_of_support (oa : ProbComp α) (f g : α → ℝ)
    (hfg : ∀ a ∈ support oa, f a ≤ g a) : realEval oa f ≤ realEval oa g := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using hfg a (by simp)
  | query_bind q next ih =>
    rw [realEval_query_bind, realEval_query_bind]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro u _
    apply ih u
    intro a ha
    apply hfg a
    exact (mem_support_bind_iff _ _ _).2 ⟨u, by simp, ha⟩

theorem realEval_mono (oa : ProbComp α) (f g : α → ℝ)
    (hfg : ∀ a, f a ≤ g a) : realEval oa f ≤ realEval oa g :=
  realEval_mono_of_support oa f g (fun a _ => hfg a)

theorem realEval_nonneg (oa : ProbComp α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ realEval oa f := by
  have hx := realEval_mono oa (fun _ => 0) f hf
  change realEval oa (0 : α → ℝ) ≤ realEval oa f at hx
  rw [(realEval oa).map_zero] at hx
  exact hx

@[simp] theorem realEval_const (oa : ProbComp α) (c : ℝ) : realEval oa (fun _ => c) = c := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [realEval_query_bind]
    simp only [ih, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (unifSpec.Range q):ℝ) ≠ 0 := by positivity
    field_simp

@[simp] theorem realEval_add (oa : ProbComp α) (f g : α → ℝ) :
    realEval oa (fun a => f a+g a) = realEval oa f+realEval oa g := (realEval oa).map_add _ _

@[simp] theorem realEval_sub (oa : ProbComp α) (f g : α → ℝ) :
    realEval oa (fun a => f a-g a) = realEval oa f-realEval oa g := (realEval oa).map_sub _ _

@[simp] theorem realEval_mul (oa : ProbComp α) (c : ℝ) (f : α → ℝ) :
    realEval oa (fun a => c*f a) = c*realEval oa f := by
  change realEval oa (c • f) = c • realEval oa f
  exact (realEval oa).map_smul c f

theorem realEval_le_const_of_support (oa : ProbComp α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ a ∈ support oa, f a ≤ c) : realEval oa f ≤ c := by
  simpa using realEval_mono_of_support oa f (fun _ => c) hf

/-- Exact agreement with VCVio's ENNReal expectation for nonnegative payoffs. -/
theorem ofReal_realEval (oa : ProbComp α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (realEval oa f) = expectedValue oa (fun a => ENNReal.ofReal (f a)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    rw [realEval_query_bind, expectedValue_bind]
    have hc : 0 < (Fintype.card (unifSpec.Range q):ℝ) := by positivity
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hc]
    rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => realEval_nonneg (next u) f hf)]
    simp_rw [ih]
    rw [expectedValue_def, tsum_fintype]
    simp only [probOutput_query, ENNReal.ofReal_natCast, Finset.mul_sum]

variable {ι : Type} {spec : OracleSpec ι} {S : Type}

/-- Signed local drift lifts directly through actual stateful OracleComp execution. -/
theorem realEval_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ)
    (hstep : ∀ q s, realEval ((impl q).run s) (fun out => Φ out.2) ≤ Φ s)
    (oa : OracleComp spec α) (s : S) :
    realEval ((simulateQ impl oa).run s) (fun out => Φ out.2) ≤ Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [realEval_bind]
    have hc : ∀ out : spec.Range q × S,
        realEval ((simulateQ impl (next out.1)).run out.2) (fun out => Φ out.2) ≤ Φ out.2 :=
      fun out => ih out.1 out.2
    exact (realEval_mono ((impl q).run s) _ _ hc).trans (hstep q s)

/-- Exact signed martingale expectation, requiring only primitive-query drift. -/
theorem realEval_simulate_eq
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ)
    (hstep : ∀ q s, realEval ((impl q).run s) (fun out => Φ out.2) = Φ s)
    (oa : OracleComp spec α) (s : S) :
    realEval ((simulateQ impl oa).run s) (fun out => Φ out.2) = Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [realEval_bind]
    have hf : (fun out : spec.Range q × S =>
        realEval ((simulateQ impl (next out.1)).run out.2) (fun out => Φ out.2)) =
        (fun out => Φ out.2) := by
      funext out
      exact ih out.1 out.2
    rw [hf, hstep]

end WeightedRealExecution
end
end

section

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal BigOperators
namespace WeightedRealExecution

set_option maxHeartbeats 800000
variable {α : Type} [Fintype α] [SampleableType α]

private theorem realEval_uniform_nonneg (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    realEval ($ᵗ α) f = (∑ a, f a) / Fintype.card α := by
  have hl := ofReal_realEval ($ᵗ α) f hf
  rw [expectedValue_def, tsum_fintype] at hl
  simp only [probOutput_uniformSample] at hl
  rw [← Finset.mul_sum] at hl
  have hc : 0 < (Fintype.card α:ℝ) := by positivity
  have hs : 0 ≤ ∑ a, f a := Finset.sum_nonneg (fun a _ => hf a)
  have he : ENNReal.ofReal (realEval ($ᵗ α) f) =
      ENNReal.ofReal ((∑ a, f a) / Fintype.card α) := by
    rw [hl, div_eq_mul_inv, ENNReal.ofReal_mul hs,
      ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a), mul_comm]
  have hx := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (realEval_nonneg _ _ hf),
    ENNReal.toReal_ofReal (div_nonneg hs hc.le)] using hx

/-- The exact signed average for the library's actual uniform-sampling computation. -/
theorem realEval_uniform (f : α → ℝ) :
    realEval ($ᵗ α) f = (∑ a, f a) / Fintype.card α := by
  have hf : f = fun a => max (f a) 0 - max (-f a) 0 := by
    funext a
    rcases le_total (f a) 0 with h | h
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  rw [hf, realEval_sub,
    realEval_uniform_nonneg _ (fun a => le_max_right _ _),
    realEval_uniform_nonneg _ (fun a => le_max_right _ _),
    Finset.sum_sub_distrib, sub_div]

theorem realEval_decoded_uniform {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : WeightedRow.Weights ι) (decode : α → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card α = w.classMass x) (f : Option ι → ℝ) :
    realEval ($ᵗ α) (fun b => f (decode b)) = w.expect f :=
  (realEval_uniform _).trans (w.uniform_decoder_expect decode hfiber f)

end WeightedRealExecution
end
end

section

/-! Statistics computed directly from the actual cache, over a finite selected
domain. Unlike an auxiliary counter, their finite-domain bound is immediate. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace WeightedDirectCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts
set_option maxHeartbeats 800000
variable {D B ι : Type} [DecidableEq D] [Fintype B] [SampleableType B]
  [Fintype ι] [DecidableEq ι]

def fresh (A : Finset D) (q : D) (cache : D → Option B) : Bool :=
  decide (q ∈ A) && (cache q).isNone

/-- Exact one-query class law for the library's actual memoized uniform oracle.
The output alphabet remains generic here to avoid expanding a concrete giant sampler. -/
theorem hash_query_law (w : WeightedRow.Weights ι)
    (A : Finset D) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (q : D) (cache : (D →ₒ B).QueryCache) (f : ℕ → (ι → ℕ) → ℝ) :
    realEval (((D →ₒ B).randomOracle q).run cache)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    w.expect (fun x => f (step (fresh A q cache) (seen A cache).card (classCounts A cache decode) x).1
      (step (fresh A q cache) (seen A cache).card (classCounts A cache decode) x).2) := by
  rw [randomOracle.run_eq]
  cases hc : cache q with
  | some u => simp [hc, fresh, step, expect_const]
  | none =>
    simp only [realEval_bind, realEval_pure]
    by_cases hq : q ∈ A
    · have hcard (u : B) : (seen A (cache.cacheQuery q u)).card = (seen A cache).card+1 :=
        seen_card_update A cache q u hq hc
      have hcounts (u : B) : classCounts A (cache.cacheQuery q u) decode =
          advance (classCounts A cache decode) (decode u) :=
        classCounts_update_of_mem A cache decode q u hq hc
      simp only [hcard, hcounts, fresh, hq, decide_true, hc, Option.isNone_none,
        Bool.and_self, step, ite_true]
      exact realEval_decoded_uniform w decode hfiber (fun x =>
        f ((seen A cache).card+1) (advance (classCounts A cache decode) x))
    · have hseen (u : B) : seen A (cache.cacheQuery q u) = seen A cache :=
        seen_update_of_not_mem A cache q u hq
      have hcounts (u : B) : classCounts A (cache.cacheQuery q u) decode = classCounts A cache decode :=
        classCounts_update_of_not_mem A cache decode q u hq
      simp only [hseen, hcounts, fresh, hq, decide_false, Bool.false_and,
        step_not_fresh, realEval_const, expect_const]

/-- Generic protected oracle, with free private randomness and the shared cache. -/
def protectedImpl : QueryImpl (unifSpec+(D →ₒ B)) (StateT (D →ₒ B).QueryCache ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (D →ₒ B).QueryCache ProbComp) + (D →ₒ B).randomOracle

def protectedFresh (A : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (cache : (D →ₒ B).QueryCache) : Bool :=
  match t with
  | .inl _ => false
  | .inr q => fresh A q cache

theorem protected_query_law (w : WeightedRow.Weights ι)
    (A : Finset D) (decode : B → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card B = w.classMass x)
    (t : (unifSpec+(D →ₒ B)).Domain) (cache : (D →ₒ B).QueryCache)
    (f : ℕ → (ι → ℕ) → ℝ) :
    realEval ((protectedImpl (D := D) (B := B) t).run cache)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    w.expect (fun x => f
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).1
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).2) := by
  cases t with
  | inl t =>
    simp only [protectedImpl, protectedFresh, step_not_fresh, expect_const]
    change realEval ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) (fun out => f (seen A out.2).card (classCounts A out.2 decode)) = _
    rw [realEval_bind]
    simp only [realEval_pure, realEval_const]
  | inr q => exact hash_query_law w A decode hfiber q cache f

/-- A hash query adds at most one selected cache entry on every supported outcome. -/
theorem hash_count_le_one (A : Finset D) (q : D) (cache : (D →ₒ B).QueryCache)
    (out : B × (D →ₒ B).QueryCache)
    (hout : out ∈ support (((D →ₒ B).randomOracle q).run cache)) :
    (seen A out.2).card ≤ (seen A cache).card+1 := by
  rw [randomOracle.run_eq] at hout
  cases hc : cache q with
  | some u =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact Nat.le_succ _
  | none =>
    simp only [hc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨u, hu, rfl⟩ := hout
    by_cases hq : q ∈ A
    · exact (seen_card_update A cache q u hq hc).le
    · rw [show seen A (cache.cacheQuery q u) = seen A cache from seen_update_of_not_mem A cache q u hq]
      exact Nat.le_succ _

/-- Free private queries preserve the selected cache count; hashes add at most one. -/
theorem protected_count_le (A : Finset D) (t : (unifSpec+(D →ₒ B)).Domain)
    (cache : (D →ₒ B).QueryCache) (out : (unifSpec+(D →ₒ B)).Range t × (D →ₒ B).QueryCache)
    (hout : out ∈ support ((protectedImpl (D := D) (B := B) t).run cache)) :
    (seen A out.2).card ≤ (seen A cache).card+(if t.isRight then 1 else 0) := by
  cases t with
  | inl t =>
    change out ∈ support ((liftM (unifSpec.query t) : ProbComp (unifSpec.Range t)) >>=
      fun u => pure (u,cache)) at hout
    obtain ⟨u, hu, hp⟩ := (mem_support_bind_iff _ _ _).1 hout
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst out
    simp
  | inr q => exact hash_count_le_one A q cache out hout

end WeightedDirectCache
end
end

section

/-! Concentration induction over actual OracleComp stateful simulation.
The expectedValue and probability are VCVio's genuine distribution semantics,
not a newly assumed execution law. Concrete one-query drift is still required. -/

noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
namespace WeightedOracleExecution

set_option maxHeartbeats 800000

variable {ι : Type} {spec : OracleSpec ι} {S α : Type}

/-- An actual stateful oracle implementation preserves a nonnegative potential
in expectation through any OracleComp program if each primitive query does so.
Free private queries need no budget or count assumption. -/
theorem expected_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (Φ : S → ℝ≥0∞)
    (hstep : ∀ q s, expectedValue ((impl q).run s) (fun out => Φ out.2) ≤ Φ s)
    (oa : OracleComp spec α) (s : S) :
    expectedValue ((simulateQ impl oa).run s) (fun out => Φ out.2) ≤ Φ s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [expectedValue_bind]
    have hcont : ∀ out : spec.Range q × S,
        expectedValue ((simulateQ impl (k out.1)).run out.2) (fun out => Φ out.2) ≤ Φ out.2 :=
      fun out => ih out.1 out.2
    exact (expectedValue_mono ((impl q).run s) hcont).trans (hstep q s)

open WeightedFirstHit

variable [spec.Inhabited]

/-- Instrument the actual implementation with the checked first-hit classifier.
After stopping, dummy answers let the finite program finish while the recorded
state and clock remain fixed. No original oracle query is executed after stop. -/
def stoppedImpl (impl : QueryImpl spec (StateT S ProbComp))
    (hit kill : ℕ → S → Prop) : QueryImpl spec (StateT (StoppedState hit kill) ProbComp) :=
  fun q st => if st.status = .active then do
    let (answer, s') ← (impl q).run st.value
    return (answer, classify hit kill (st.clock+1) s')
  else pure (default, st)

@[simp] theorem stoppedImpl_run
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (q : spec.Domain) (st : StoppedState hit kill) :
    ((stoppedImpl impl hit kill) q).run st =
      if st.status = .active then (do
        let (answer, s') ← (impl q).run st.value
        return (answer, classify hit kill (st.clock+1) s'))
      else pure (default, st) := rfl

/-- Local drift is needed only on active states; stopping freezes the potential. -/
theorem expected_stopped_step_le
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (Φ : ℕ → S → ℝ≥0∞)
    (hstep : ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s) (fun out => Φ (t+1) out.2) ≤ Φ t s)
    (q : spec.Domain) (st : StoppedState hit kill) :
    expectedValue (((stoppedImpl impl hit kill) q).run st)
      (fun out => Φ out.2.clock out.2.value) ≤ Φ st.clock st.value := by
  change expectedValue (if st.status = .active then _ else _) _ ≤ _
  split_ifs with hs
  · rw [expectedValue_bind]
    simpa only [expectedValue_pure, classify_clock, classify_value] using
      hstep q st.clock st.value (st.safe hs).1 (st.safe hs).2
  · simp

/-- The stopped potential bound is now about the actual VCVio simulation law. -/
theorem expected_stopped_simulate_le
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (Φ : ℕ → S → ℝ≥0∞)
    (hstep : ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s) (fun out => Φ (t+1) out.2) ≤ Φ t s)
    (oa : OracleComp spec α) (s : S) :
    expectedValue ((simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s))
      (fun out => Φ out.2.clock out.2.value) ≤ Φ 0 s := by
  have hx := expected_simulate_le (stoppedImpl impl hit kill)
    (fun st => Φ st.clock st.value)
    (expected_stopped_step_le impl hit kill Φ hstep) oa (classify hit kill 0 s)
  simpa only [classify_clock, classify_value] using hx

/-- Exponential Markov for the actual finite probability semantics. -/
theorem actual_exponential_tail (oa : ProbComp α) (bad : α → Prop)
    (Z : α → ℝ) (b : ℝ) (hbad : ∀ x, bad x → b ≤ Z x)
    (hmgf : expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x))) ≤ 1) :
    Pr[bad | oa] ≤ ENNReal.ofReal (Real.exp (-b)) := by
  let c := ENNReal.ofReal (Real.exp (-b))
  have hcost (x : α) (hx : bad x) :
      1 ≤ ENNReal.ofReal (Real.exp (Z x)) * c := by
    dsimp [c]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    have he : (1:ℝ) ≤ Real.exp (Z x + -b) := by
      rw [Real.one_le_exp_iff]
      linarith [hbad x hx]
    exact_mod_cast ENNReal.ofReal_le_ofReal he
  have hp := probEvent_le_tsum_probOutput_mul_cost oa bad
    (fun x => ENNReal.ofReal (Real.exp (Z x))*c) hcost
  change Pr[bad | oa] ≤ expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x))*c) at hp
  rw [expectedValue_mul_const] at hp
  apply hp.trans
  calc
    expectedValue oa (fun x => ENNReal.ofReal (Real.exp (Z x)))*c ≤ 1*c := by gcongr
    _ = c := one_mul c

/-- Actual OracleComp maximal Freedman bound under primitive-query drift.
The probability is that the instrumented concrete simulation ever records a
hit before killing. Free and paid queries are both part of the syntax; only the
caller-supplied variance proxy is charged to the paid-query budget. -/
theorem actual_stopped_freedman
    (impl : QueryImpl spec (StateT S ProbComp)) (oa : OracleComp spec α)
    (Z W : ℕ → S → ℝ) (s₀ : S) (a v J : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hJ : 0 ≤ J)
    (hZ0 : Z 0 s₀ = 0) (hW0 : W 0 s₀ = 0)
    (hit kill : ℕ → S → Prop)
    (hstep : ∀ θ, 0 < θ → θ*J < 3 → ∀ q t s, ¬hit t s → ¬kill t s →
      expectedValue ((impl q).run s)
        (fun out => ENNReal.ofReal (Real.exp (θ*Z (t+1) out.2-θ^2*W (t+1) out.2/(2*(1-θ*J/3))))) ≤
        ENNReal.ofReal (Real.exp (θ*Z t s-θ^2*W t s/(2*(1-θ*J/3)))))
    (hZ : ∀ t s, hit t s → a ≤ Z t s) (hW : ∀ t s, hit t s → W t s ≤ v) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
        ENNReal.ofReal (Real.exp (-a^2/(2*(v+J*a/3)))) := by
  let θ := a/(v+J*a/3)
  obtain ⟨hθ, hθJ, heq⟩ := WeightedKernel.optimized_exponent a v J ha hv hJ
  change 0 < θ at hθ
  change θ*J < 3 at hθJ
  change θ*a-θ^2*v/(2*(1-θ*J/3)) = a^2/(2*(v+J*a/3)) at heq
  let F : ℕ → S → ℝ := fun t s => θ*Z t s-θ^2*W t s/(2*(1-θ*J/3))
  have hmgf := expected_stopped_simulate_le impl hit kill
    (fun t s => ENNReal.ofReal (Real.exp (F t s))) (hstep θ hθ hθJ) oa s₀
  have hinit : ENNReal.ofReal (Real.exp (F 0 s₀)) = 1 := by simp [F, hZ0, hW0]
  rw [hinit] at hmgf
  have hcoef : 0 ≤ θ^2/(2*(1-θ*J/3)) := by
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hbad (out : α × StoppedState hit kill) (hs : out.2.status = .hit) :
      a^2/(2*(v+J*a/3)) ≤ F out.2.clock out.2.value := by
    have hh := out.2.valid hs
    have hz := mul_le_mul_of_nonneg_left (hZ _ _ hh) hθ.le
    have hw := mul_le_mul_of_nonneg_left (hW _ _ hh) hcoef
    have heqv : θ^2*v/(2*(1-θ*J/3)) = (θ^2/(2*(1-θ*J/3)))*v := by ring
    have heqw : θ^2*W out.2.clock out.2.value/(2*(1-θ*J/3)) =
        (θ^2/(2*(1-θ*J/3)))*W out.2.clock out.2.value := by ring
    dsimp [F]
    rw [← heq, heqv, heqw]
    linarith
  have hx := actual_exponential_tail
    ((simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀))
    (fun out => out.2.status = .hit) (fun out => F out.2.clock out.2.value)
    (a^2/(2*(v+J*a/3))) hbad hmgf
  simpa only [neg_div] using hx

/-- A real-valued state quantity whose per-query increase is charged to `cost`
is bounded pathwise by the program's structural query budget. -/
theorem state_bound_of_query_budget
    (impl : QueryImpl spec (StateT S ProbComp)) (V : S → ℝ)
    (cost : spec.Domain → ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ q s out, out ∈ support ((impl q).run s) →
      V out.2 ≤ V s+c*(cost q : ℝ))
    (oa : OracleComp spec α) (B : ℕ)
    (hbudget : oa.IsQueryBound B (fun q b => cost q ≤ b) (fun q b => b-cost q))
    (s : S) (out : α × S) (hout : out ∈ support ((simulateQ impl oa).run s)) :
    V out.2 ≤ V s+c*(B:ℝ) := by
  induction oa using OracleComp.inductionOn generalizing B s out with
  | pure x =>
    have he : out = (x,s) := by simpa using hout
    subst out
    have hnonneg : 0 ≤ c*(B:ℝ) := by positivity
    exact le_add_of_nonneg_right hnonneg
  | query_bind q k ih =>
    obtain ⟨hcost, hrest⟩ := hbudget
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hout
    obtain ⟨mid, hmid, hout⟩ := hout
    have hnext := ih mid.1 (B-cost q) (hrest mid.1) mid.2 out hout
    have hlocal := hstep q s mid hmid
    have hsum : ((B-cost q : ℕ):ℝ)+(cost q:ℝ) = (B:ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hcost
    nlinarith

/-- Specialization to the protected cost model: private sampling has cost zero,
while every hash, including a cache hit, keeps its complete compression cost. -/
theorem state_bound_of_protected_budget
    {S α : Type} (impl : QueryImpl OptimalOTS.Spec (StateT S ProbComp))
    (V : S → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ q s out, out ∈ support ((impl q).run s) →
      V out.2 ≤ V s+c*(OptimalOTS.queryCost q : ℝ))
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (s : S) (out : α × S) (hout : out ∈ support ((simulateQ impl oa).run s)) :
    V out.2 ≤ V s+c*(B:ℝ) :=
  state_bound_of_query_budget impl V OptimalOTS.queryCost c hc hstep oa B hbudget s out hout

/-- An explicit early-stopping interpreter using the actual query
implementation. Its Boolean result records a hit before kill, including the
initial state and the state after the last primitive query. -/
def firstHitRun (impl : QueryImpl spec (StateT S ProbComp))
    (hit kill : ℕ → S → Prop) (oa : OracleComp spec α) : ℕ → S → ProbComp Bool :=
  OracleComp.construct
    (fun _ t s => pure (decide (hit t s)))
    (fun q _ rec t s => if hit t s then pure true else if kill t s then pure false else do
      let (answer, s') ← (impl q).run s
      rec answer (t+1) s') oa

@[simp] theorem firstHitRun_pure
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (x : α) (t : ℕ) (s : S) :
    firstHitRun impl hit kill (pure x) t s = pure (decide (hit t s)) := by
  simp [firstHitRun]

@[simp] theorem firstHitRun_query_bind
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (q : spec.Domain) (k : spec.Range q → OracleComp spec α) (t : ℕ) (s : S) :
    firstHitRun impl hit kill ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s =
      if hit t s then pure true else if kill t s then pure false else (do
        let (answer, s') ← (impl q).run s
        firstHitRun impl hit kill (k answer) (t+1) s') := by
  simp [firstHitRun]

/-- Once stopped, the remaining real OracleComp syntax is interpreted with
deterministic dummy answers, and its recorded state is exactly unchanged. -/
theorem stopped_simulate_of_stop
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (oa : OracleComp spec α) (st : StoppedState hit kill) (hstop : st.status ≠ .active) :
    (simulateQ (stoppedImpl impl hit kill) oa).run st =
      pure (evalWithAnswerFn (fun _ => default) oa, st) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change ((if st.status = .active then _ else pure (default, st)) >>= _) = _
    rw [if_neg hstop]
    simp only [pure_bind]
    rw [ih]
    congr 1

/-- The instrumented simulation's hit flag has exactly the early-interpreter
probability. This removes any assumed link between stopping and execution. -/
theorem prob_stopped_hit_eq_firstHitRun
    (impl : QueryImpl spec (StateT S ProbComp)) (hit kill : ℕ → S → Prop)
    (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill t s)] =
      Pr[= true | firstHitRun impl hit kill oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure x =>
    by_cases hh : hit t s
    · simp [hh]
    · by_cases hk : kill t s <;> simp [classify, hh, hk]
  | query_bind q k ih =>
    by_cases hh : hit t s
    · rw [stopped_simulate_of_stop _ _ _ _ _ (by simp [hh])]
      simp [hh]
    · by_cases hk : kill t s
      · rw [stopped_simulate_of_stop _ _ _ _ _ (by simp [hh, hk])]
        simp [hh, hk]
      · rw [firstHitRun_query_bind, if_neg hh, if_neg hk]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp only [stoppedImpl_run, classify_status_active _ _ _ _ hh hk, if_true,
          classify_clock, classify_value]
        simp only [classify_clock, classify_value, bind_assoc, pure_bind]
        rw [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
        apply tsum_congr
        intro out
        congr 1
        exact ih out.1 (t+1) out.2

end WeightedOracleExecution
end
end
