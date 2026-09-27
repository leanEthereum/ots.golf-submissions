import Submissions.UpperCompressions.ProofBundle09
import Submissions.UpperCompressions.ProofBundle00
import Submissions.UpperCompressions.ProofBundle01
import Submissions.UpperCompressions.ProofBundle08
import Submissions.UpperCompressions.ProofBundle07

section

/-! Stopped moments in actual OracleComp execution from an explicit one-query
observable law. The law must still be instantiated for the shared cache and
concrete decoder; no stopped means or second moments are assumed. -/

noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace WeightedActualMoments
open WeightedRealExecution WeightedRow.Weights WeightedOracleExecution

set_option maxHeartbeats 800000

variable {ι S α : Type} [Fintype ι] [DecidableEq ι]

/-- All three moment hypotheses needed by the small-budget proof, derived from
actual execution and the fresh-class query law. The terminal fresh-query count
may depend arbitrarily on prior observations and private randomness. -/
theorem actual_stopped_moments
    (w : WeightedRow.Weights ι)
    (impl : QueryImpl OptimalOTS.Spec (StateT S ProbComp))
    (qCount : S → ℕ) (counts : S → (ι → ℕ))
    (fresh : OptimalOTS.Spec.Domain → S → Bool)
    (hlaw : ∀ t s (f : ℕ → (ι → ℕ) → ℝ),
      realEval ((impl t).run s) (fun out => f (qCount out.2) (counts out.2)) =
        w.expect (fun x => f (step (fresh t s) (qCount s) (counts s) x).1
          (step (fresh t s) (qCount s) (counts s) x).2))
    (hcount : ∀ t s out, out ∈ support ((impl t).run s) →
      qCount out.2 ≤ qCount s+OptimalOTS.queryCost t)
    (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (s₀ : S) (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    realEval ((simulateQ impl oa).run s₀) (fun out => w.M1 (qCount out.2) (counts out.2)) = 0 ∧
    realEval ((simulateQ impl oa).run s₀) (fun out => w.M2 (qCount out.2) (counts out.2)) = 0 ∧
    realEval ((simulateQ impl oa).run s₀) (fun out => (w.M1 (qCount out.2) (counts out.2))^2) ≤
      (B:ℝ)*G*w.mean := by
  have hM10 : w.M1 (qCount s₀) (counts s₀) = 0 := by simp [M1, score, hq0, hk0]
  have hM20 : w.M2 (qCount s₀) (counts s₀) = 0 := by simp [M2, score, pairScore, hq0, hk0]
  have hmean1 : ∀ t s,
      realEval ((impl t).run s) (fun out => w.M1 (qCount out.2) (counts out.2)) =
        w.M1 (qCount s) (counts s) := by
    intro t s
    rw [hlaw]
    exact w.M1_step_mean (fresh t s) (qCount s) (counts s)
  have hmean2 : ∀ t s,
      realEval ((impl t).run s) (fun out => w.M2 (qCount out.2) (counts out.2)) =
        w.M2 (qCount s) (counts s) := by
    intro t s
    rw [hlaw]
    exact w.M2_step_mean (fresh t s) (qCount s) (counts s)
  have hfirst := realEval_simulate_eq impl (fun s => w.M1 (qCount s) (counts s)) hmean1 oa s₀
  have hsecond := realEval_simulate_eq impl (fun s => w.M2 (qCount s) (counts s)) hmean2 oa s₀
  rw [hM10] at hfirst
  rw [hM20] at hsecond
  refine ⟨hfirst, hsecond, ?_⟩
  have hcompstep : ∀ t s,
      realEval ((impl t).run s)
        (fun out => (w.M1 (qCount out.2) (counts out.2))^2-G*w.mean*(qCount out.2:ℝ)) ≤
          (w.M1 (qCount s) (counts s))^2-G*w.mean*(qCount s:ℝ) := by
    intro t s
    rw [hlaw t s (fun q k => (w.M1 q k)^2-G*w.mean*(q:ℝ))]
    exact w.M1_step_square_compensated (fresh t s) G hG hg (qCount s) (counts s)
  have hcomp := realEval_simulate_le impl
    (fun s => (w.M1 (qCount s) (counts s))^2-G*w.mean*(qCount s:ℝ)) hcompstep oa s₀
  rw [hM10, hq0] at hcomp
  simp only [Nat.cast_zero, mul_zero, zero_pow, sub_zero] at hcomp
  rw [realEval_sub, realEval_mul] at hcomp
  have hcountR : ∀ t s out, out ∈ support ((impl t).run s) →
      (qCount out.2:ℝ) ≤ (qCount s:ℝ)+1*(OptimalOTS.queryCost t:ℝ) := by
    intro t s out hout
    norm_num only [one_mul]
    exact_mod_cast hcount t s out hout
  have hpath : ∀ out ∈ support ((simulateQ impl oa).run s₀), (qCount out.2:ℝ) ≤ (B:ℝ) := by
    intro out hout
    have hx := state_bound_of_protected_budget impl (fun s => (qCount s:ℝ)) 1
      zero_le_one hcountR oa B hbudget s₀ out hout
    simpa only [hq0, Nat.cast_zero, zero_add, one_mul] using hx
  have hqmean := realEval_le_const_of_support ((simulateQ impl oa).run s₀)
    (fun out => (qCount out.2:ℝ)) B hpath
  have hh : 0 ≤ w.mean := by
    unfold mean
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (w.p_pos i).le (w.g_nonneg i))
  have hb := mul_le_mul_of_nonneg_left hqmean (mul_nonneg hG hh)
  nlinarith

end WeightedActualMoments
end
end

section

/-! Time-uniform linear-boundary concentration for actual OracleComp execution.
The counter may ignore private queries and cache hits. No union over time is used. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
namespace WeightedOracleExecution
open WeightedFirstHit

set_option maxHeartbeats 800000
variable {ι S α : Type} {spec : OracleSpec ι} [spec.Inhabited]

theorem actual_linear_boundary
    (impl : QueryImpl spec (StateT S ProbComp)) (counter : S → ℕ) (Z : S → ℝ)
    (θ c δ Q : ℝ) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ) (hc : c ≤ θ*δ/2)
    (hstep : ∀ t s, expectedValue ((impl t).run s)
      (fun out => ENNReal.ofReal (Real.exp (θ*Z out.2-c*(counter out.2:ℝ)))) ≤
        ENNReal.ofReal (Real.exp (θ*Z s-c*(counter s:ℝ))))
    (oa : OracleComp spec α) (s₀ : S) (hq0 : counter s₀ = 0) (hZ0 : Z s₀ = 0) :
    let hit := fun (_ : ℕ) (s : S) => δ*max (counter s:ℝ) Q ≤ Z s
    let kill := fun (_ : ℕ) (_ : S) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-(θ*δ*Q/2))) := by
  dsimp only
  let hit := fun (_ : ℕ) (s : S) => δ*max (counter s:ℝ) Q ≤ Z s
  let kill := fun (_ : ℕ) (_ : S) => False
  let F : ℕ → S → ℝ := fun _ s => θ*Z s-c*(counter s:ℝ)
  have hlocal : ∀ t n s, ¬hit n s → ¬kill n s →
      expectedValue ((impl t).run s) (fun out => ENNReal.ofReal (Real.exp (F (n+1) out.2))) ≤
        ENNReal.ofReal (Real.exp (F n s)) := fun t _ s _ _ => hstep t s
  have hmgf := expected_stopped_simulate_le impl hit kill
    (fun n s => ENNReal.ofReal (Real.exp (F n s))) hlocal oa s₀
  have hinit : ENNReal.ofReal (Real.exp (F 0 s₀)) = 1 := by simp [F, hq0, hZ0]
  rw [hinit] at hmgf
  apply actual_exponential_tail
    ((simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀))
    (fun out => out.2.status = .hit)
    (fun out => F out.2.clock out.2.value) (θ*δ*Q/2) _ hmgf
  intro out hout
  have hh := out.2.valid hout
  change δ*max (counter out.2.value:ℝ) Q ≤ Z out.2.value at hh
  have hθδ : 0 ≤ θ*δ := mul_nonneg hθ hδ
  have hsum : (counter out.2.value:ℝ)+Q ≤ 2*max (counter out.2.value:ℝ) Q := by
    linarith [le_max_left (counter out.2.value:ℝ) Q, le_max_right (counter out.2.value:ℝ) Q]
  have hx := mul_le_mul_of_nonneg_left hsum hθδ
  have hy := mul_le_mul_of_nonneg_left hh hθ
  have hz := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (counter out.2.value) : (0:ℝ) ≤ _)
  dsimp only [F]
  nlinarith

end WeightedOracleExecution
end
end

section

/-! Concentration of actual fresh-query score statistics. The only oracle-law
hypothesis is the exact primitive-query class law, discharged separately by the
concrete shared-cache implementation. No terminal concentration is assumed. -/
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
namespace WeightedActualScore
open WeightedRealExecution WeightedRow.Weights WeightedOracleExecution WeightedFirstHit WeightedEmpirical

set_option maxHeartbeats 800000
variable {ι S α : Type} [Fintype ι] [DecidableEq ι]
variable (w : WeightedRow.Weights ι)
    (impl : QueryImpl OptimalOTS.Spec (StateT S ProbComp))
    (qCount : S → ℕ) (counts : S → (ι → ℕ))
    (fresh : OptimalOTS.Spec.Domain → S → Bool)
    (hlaw : ∀ t s (f : ℕ → (ι → ℕ) → ℝ),
      realEval ((impl t).run s) (fun out => f (qCount out.2) (counts out.2)) =
        w.expect (fun x => f (step (fresh t s) (qCount s) (counts s) x).1
          (step (fresh t s) (qCount s) (counts s) x).2))

def signedM1 (lower : Bool) (s : S) : ℝ :=
  if lower then -w.M1 (qCount s) (counts s) else w.M1 (qCount s) (counts s)

include fresh hlaw

/-- Both upper and lower exponential drift follow from the same exact fresh-query law. -/
theorem query_mgf (lower : Bool) (G θ : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G < 3)
    (t : OptimalOTS.Spec.Domain) (s : S) :
    expectedValue ((impl t).run s)
      (fun out => ENNReal.ofReal (Real.exp (θ*signedM1 w qCount counts lower out.2-
        rate w θ G*(qCount out.2:ℝ)))) ≤
      ENNReal.ofReal (Real.exp (θ*signedM1 w qCount counts lower s-rate w θ G*(qCount s:ℝ))) := by
  rw [← ofReal_realEval _ _ (fun _ => Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  cases lower with
  | false =>
    change realEval ((impl t).run s)
      (fun out => Real.exp (θ*w.M1 (qCount out.2) (counts out.2)-rate w θ G*(qCount out.2:ℝ))) ≤ _
    rw [hlaw t s (fun q k => Real.exp (θ*w.M1 q k-rate w θ G*(q:ℝ)))]
    exact score_step_mgf w G θ hG hg hθ hθG (fresh t s) (qCount s) (counts s)
  | true =>
    change realEval ((impl t).run s)
      (fun out => Real.exp (θ*(-w.M1 (qCount out.2) (counts out.2))-rate w θ G*(qCount out.2:ℝ))) ≤ _
    rw [hlaw t s (fun q k => Real.exp (θ*(-w.M1 q k)-rate w θ G*(q:ℝ)))]
    exact lower_score_step_mgf w G θ hG hg hθ hθG (fresh t s) (qCount s) (counts s)

theorem global_boundary (lower : Bool) (G θ δ Q : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hθ : 0 ≤ θ) (hθG : θ*G < 3)
    (hδ : 0 ≤ δ) (hrate : rate w θ G ≤ θ*δ/2)
    (oa : OracleComp OptimalOTS.Spec α) (s₀ : S)
    (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    let hit := fun (_ : ℕ) (s : S) =>
      δ*max (qCount s:ℝ) Q ≤ signedM1 w qCount counts lower s
    let kill := fun (_ : ℕ) (_ : S) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-(θ*δ*Q/2))) := by
  exact actual_linear_boundary impl qCount (signedM1 w qCount counts lower)
    θ (rate w θ G) δ Q hθ hδ hrate
    (query_mgf w impl qCount counts fresh hlaw lower G θ hG hg hθ hθG)
    oa s₀ hq0 (by cases lower <;> simp [signedM1, M1, score, hq0, hk0])

/-- The row hit is explicitly restricted to at most N fresh row inputs.
Connecting that restriction to the finite nonce domain is a separate counting invariant. -/
theorem row_freedman (lower : Bool) (G N a : ℝ)
    (hG : 0 < G) (hg : ∀ i, w.g i ≤ G) (hN : 0 < N) (ha : 0 < a)
    (oa : OracleComp OptimalOTS.Spec α) (s₀ : S)
    (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    let hit := fun (_ : ℕ) (s : S) =>
      (qCount s:ℝ) ≤ N ∧ a ≤ signedM1 w qCount counts lower s
    let kill := fun (_ : ℕ) (s : S) => N < (qCount s:ℝ)
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-a^2/(2*(G^2*N+G*a/3)))) := by
  dsimp only
  let hit := fun (_ : ℕ) (s : S) =>
    (qCount s:ℝ) ≤ N ∧ a ≤ signedM1 w qCount counts lower s
  let kill := fun (_ : ℕ) (s : S) => N < (qCount s:ℝ)
  have hm0 : 0 ≤ w.mean := by
    simpa only [mean_scoreJump] using w.expect_nonneg w.scoreJump
      (fun x => (w.scoreJump_bounds G hG.le hg x).1)
  have hmG : w.mean ≤ G := by
    simpa only [mean_scoreJump] using w.expect_le_const w.scoreJump G
      (fun x => (w.scoreJump_bounds G hG.le hg x).2)
  apply actual_stopped_freedman impl oa
    (fun _ s => signedM1 w qCount counts lower s)
    (fun _ s => G*w.mean*(qCount s:ℝ)) s₀ a (G^2*N) G ha (by positivity) hG.le
    (by cases lower <;> simp [signedM1, M1, score, hq0, hk0])
    (by simp [hq0]) hit kill
  · intro θ hθ hθG t n s _ _
    have he (r : ℝ) : θ^2*(G*w.mean*r)/(2*(1-θ*G/3)) = rate w θ G*r := by
      unfold rate
      ring
    simp only [he]
    exact query_mgf w impl qCount counts fresh hlaw lower G θ hG.le hg hθ.le hθG t s
  · intro n s hs
    exact hs.2
  · intro n s hs
    change G*w.mean*(qCount s:ℝ) ≤ G^2*N
    calc
      G*w.mean*(qCount s:ℝ) ≤ G*w.mean*N := mul_le_mul_of_nonneg_left hs.1 (mul_nonneg hG.le hm0)
      _ ≤ G*G*N := by gcongr
      _ = G^2*N := by ring

/-- Concrete row margin for either tail. Set G=1 for prefix indicators and
G=Lκ for rowS or rowU. The counted finite-domain restriction is explicit. -/
theorem mixed_row (lower : Bool) (G : ℝ) (hG : 0 < G) (hg : ∀ i, w.g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (s₀ : S)
    (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    let a := G*(2^86:ℝ)/(100*(2^20:ℝ))
    let hit := fun (_ : ℕ) (s : S) =>
      (qCount s:ℝ) ≤ 2^86 ∧ a ≤ signedM1 w qCount counts lower s
    let kill := fun (_ : ℕ) (s : S) => (2^86:ℝ) < (qCount s:ℝ)
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  obtain ⟨ha, hv, he⟩ := mixed_row_exponent G hG
  have hx := row_freedman w impl qCount counts fresh hlaw lower G (2^86:ℝ)
    (G*(2^86:ℝ)/(100*(2^20:ℝ))) hG hg (by positivity) ha oa s₀ hq0 hk0
  apply hx.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg he

end WeightedActualScore
end
end

section

/-! The actual protected shared-oracle implementation, with statistics defined
from its cache rather than from an auxiliary execution law. A finite selected
input domain A provides the fresh-count cap by definition. All initial selected
entries must be absent when these counts represent a pre-sign public transcript.
Private signing entries invalidate a post-sign public-fresh interpretation. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators
namespace WeightedProtectedCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts WeightedDirectCache
set_option maxHeartbeats 800000
variable {ι α : Type} [Fintype ι] [DecidableEq ι]

/-- The generic protected implementation specializes exactly to the contract. -/
theorem protectedImpl_eq :
    protectedImpl (D := OptimalOTS.Query) (B := BitVec OptimalOTS.hashBits) = OptimalOTS.oracleImpl := rfl

/-- Exact primitive-query class law for the contract's actual shared oracle. -/
theorem query_law (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (f : ℕ → (ι → ℕ) → ℝ) :
    realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    w.expect (fun x => f
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).1
      (step (protectedFresh A t cache) (seen A cache).card (classCounts A cache decode) x).2) := by
  have h := protected_query_law w A decode hfiber t cache f
  rw [protectedImpl_eq] at h
  exact h

/-- Each newly cached selected hash is charged to a paid primitive query. -/
theorem count_le_cost (A : Finset OptimalOTS.Query) (t : OptimalOTS.Spec.Domain)
    (cache : OptimalOTS.hashSpec.QueryCache)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run cache)) :
    (seen A out.2).card ≤ (seen A cache).card+OptimalOTS.queryCost t := by
  have h := protected_count_le A t cache out
  rw [protectedImpl_eq] at h
  have hc : (if t.isRight then 1 else 0) ≤ OptimalOTS.queryCost t := by
    cases t with
    | inl n => simp [OptimalOTS.queryCost]
    | inr q => exact Nat.le_max_left 1 _
  exact (h hout).trans (Nat.add_le_add_left hc _)

/-- Actual execution respects both the finite domain and the paid budget,
including arbitrary initial selected-cache contents and free private randomness. -/
theorem count_bound (A : Finset OptimalOTS.Query)
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (cache : OptimalOTS.hashSpec.QueryCache) (out : α × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((simulateQ OptimalOTS.oracleImpl oa).run cache)) :
    (seen A out.2).card ≤ min A.card ((seen A cache).card+B) := by
  apply le_min (seen_card_le A out.2)
  have hstep : ∀ t c z, z ∈ support ((OptimalOTS.oracleImpl t).run c) →
      ((seen A z.2).card:ℝ) ≤ ((seen A c).card:ℝ)+1*(OptimalOTS.queryCost t:ℝ) := by
    intro t c z hz
    norm_num only [one_mul]
    exact_mod_cast count_le_cost A t c z hz
  have h := WeightedOracleExecution.state_bound_of_protected_budget OptimalOTS.oracleImpl
    (fun c => ((seen A c).card:ℝ)) 1 zero_le_one hstep oa B hbudget cache out hout
  norm_num only [one_mul] at h
  exact_mod_cast h

/-- All stopped moment hypotheses follow from actual shared-oracle execution. -/
theorem stopped_moments (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (G : ℝ) (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (B : ℕ) (hbudget : OptimalOTS.CostAtMost oa B)
    (cache : OptimalOTS.hashSpec.QueryCache)
    (hq0 : (seen A cache).card = 0) (hk0 : classCounts A cache decode = fun _ => 0) :
    let run := (simulateQ OptimalOTS.oracleImpl oa).run cache
    realEval run (fun out => w.M1 (seen A out.2).card (classCounts A out.2 decode)) = 0 ∧
    realEval run (fun out => w.M2 (seen A out.2).card (classCounts A out.2 decode)) = 0 ∧
    realEval run (fun out => (w.M1 (seen A out.2).card (classCounts A out.2 decode))^2) ≤
      (B:ℝ)*G*w.mean := by
  exact WeightedActualMoments.actual_stopped_moments w OptimalOTS.oracleImpl
    (fun c => (seen A c).card) (fun c => classCounts A c decode)
    (protectedFresh A) (query_law w A decode hfiber) (count_le_cost A)
    G hG hg oa B hbudget cache hq0 hk0

end WeightedProtectedCache
end
end

section

/-! Concentration for statistics read directly from the actual protected cache.
The row finite-domain restriction is discharged pathwise for every cache. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical BigOperators ENNReal
namespace WeightedProtectedCache
open WeightedRealExecution WeightedRow.Weights WeightedCacheCounts WeightedDirectCache
open WeightedOracleExecution WeightedFirstHit WeightedActualScore
set_option maxHeartbeats 800000
variable {ι α : Type} [Fintype ι] [DecidableEq ι]

/-- Row concentration for either score tail, with the finite nonce-domain cap
proved automatically from A.card≤2^86. The execution is never killed by a count cap. -/
theorem row_score (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (hcard : A.card ≤ 2^86)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (lower : Bool) (G : ℝ) (hG : 0 < G) (hg : ∀ i, w.g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (cache : OptimalOTS.hashSpec.QueryCache)
    (hq0 : (seen A cache).card = 0) (hk0 : classCounts A cache decode = fun _ => 0) :
    let hit := fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      G*(2^86:ℝ)/(100*(2^20:ℝ)) ≤
        signedM1 w (fun c => (seen A c).card) (fun c => classCounts A c decode) lower c
    let kill := fun (_ : ℕ) (_ : OptimalOTS.hashSpec.QueryCache) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl OptimalOTS.oracleImpl hit kill) oa).run (classify hit kill 0 cache)] ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  have hx := WeightedActualScore.mixed_row w OptimalOTS.oracleImpl
    (fun c => (seen A c).card) (fun c => classCounts A c decode)
    (protectedFresh A) (query_law w A decode hfiber) lower G hG hg oa cache hq0 hk0
  have hcap (c : OptimalOTS.hashSpec.QueryCache) : ((seen A c).card:ℝ) ≤ 2^86 := by
    exact_mod_cast (seen_card_le A c).trans hcard
  have hhit : (fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      ((seen A c).card:ℝ) ≤ 2^86 ∧ G*(2^86:ℝ)/(100*(2^20:ℝ)) ≤
        signedM1 w (fun c => (seen A c).card) (fun c => classCounts A c decode) lower c) =
      (fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
        G*(2^86:ℝ)/(100*(2^20:ℝ)) ≤
          signedM1 w (fun c => (seen A c).card) (fun c => classCounts A c decode) lower c) := by
    funext n c
    apply propext
    constructor
    · exact And.right
    · intro h; exact ⟨hcap c,h⟩
  have hkill : (fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      (2^86:ℝ) < ((seen A c).card:ℝ)) =
      (fun (_ : ℕ) (_ : OptimalOTS.hashSpec.QueryCache) => False) := by
    funext n c
    exact propext (iff_false_intro (not_lt_of_ge (hcap c)))
  dsimp only at hx
  rw [hhit, hkill] at hx
  exact hx

end WeightedProtectedCache
end
end

section

/-! Physical relations between row and global multiplicities in the actual cache. -/
noncomputable section
open scoped Classical

namespace WeightedCacheCounts
variable {D B ι : Type} [DecidableEq D] [Fintype ι] [DecidableEq ι]

theorem classCounts_mono {A G : Finset D} (hAG : A ⊆ G)
    (cache : D → Option B) (decode : B → Option ι) (i : ι) :
    classCounts A cache decode i ≤ classCounts G cache decode i := by
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqA, hi⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqA, hc⟩ := Finset.mem_filter.mp hqA
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hAG hqA, hc⟩, hi⟩

theorem fresh_seen_succ_le (A : Finset D) (cache : D → Option B)
    (q : D) (u : B) (hq : q ∈ A) (hc : cache q = none) :
    (seen A cache).card + 1 ≤ A.card := by
  rw [← seen_card_update A cache q u hq hc]
  exact seen_card_le _ _

end WeightedCacheCounts

namespace OptimalOTS.WeightedConstruction.WideDomains
open WeightedCacheCounts

theorem fresh_row_succ_bound (m : Message) (c : hashSpec.QueryCache)
    (q : Query) (hq : q ∈ rowDomain m) (hc : c q = none) :
    (seen (rowDomain m) c).card + 1 ≤ 2^86 :=
  (fresh_seen_succ_le (rowDomain m) c q (0 : BitVec hashBits) hq hc).trans_eq
    (row_card m)

end OptimalOTS.WeightedConstruction.WideDomains
end
end

section
noncomputable section
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal
namespace WeightedOracleExecution
open WeightedFirstHit
set_option maxHeartbeats 800000
variable {ι S α I : Type} {spec : OracleSpec ι} [spec.Inhabited] [Fintype I]

theorem firstHitRun_of_hit (impl : QueryImpl spec (StateT S ProbComp))
    (hit kill : ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S)
    (hh : hit t s) : firstHitRun impl hit kill oa t s = pure true := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [hh]
  | query_bind q k ih => simp only [firstHitRun_query_bind, if_pos hh]

/-- Finite union of maximal events in actual execution. The differently stopped
programs are related by structural induction, so no common-law assumption or
time-prefix union factor is needed. -/
theorem firstHitRun_union_le (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[= true | firstHitRun impl (fun n s => ∃ i, hit i n s) (fun _ _ => False) oa t s] ≤
      ∑ i, Pr[= true | firstHitRun impl (hit i) (fun _ _ => False) oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure a =>
    by_cases hh : ∃ i, hit i t s
    · obtain ⟨i,hi⟩ := hh
      have hall : Pr[= true | firstHitRun impl (fun n s => ∃ i, hit i n s)
          (fun _ _ => False) (pure a) t s] = 1 := by simp [show ∃ i, hit i t s from ⟨i,hi⟩]
      have hone : Pr[= true | firstHitRun impl (hit i) (fun _ _ => False) (pure a) t s] = 1 := by simp [hi]
      rw [hall, ← hone]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : I => Pr[= true | firstHitRun impl (hit j) (fun _ _ => False) (pure a) t s])
        (fun j _ => zero_le) (Finset.mem_univ i)
    · simp [hh]
  | query_bind q k ih =>
    by_cases hh : ∃ i, hit i t s
    · obtain ⟨i,hi⟩ := hh
      have hall : Pr[= true | firstHitRun impl (fun n s => ∃ i, hit i n s)
          (fun _ _ => False) ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s] = 1 := by
        rw [firstHitRun_of_hit _ _ _ _ _ _ ⟨i,hi⟩]
        simp
      have hone : Pr[= true | firstHitRun impl (hit i) (fun _ _ => False)
          ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s] = 1 := by
        rw [firstHitRun_of_hit _ _ _ _ _ _ hi]
        simp
      rw [hall, ← hone]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : I => Pr[= true | firstHitRun impl (hit j) (fun _ _ => False)
          ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k) t s])
        (fun j _ => zero_le) (Finset.mem_univ i)
    · have hnone : ∀ i, ¬hit i t s := fun i hi => hh ⟨i,hi⟩
      rw [firstHitRun_query_bind, if_neg hh, if_false]
      simp only [firstHitRun_query_bind, hnone, if_false, probOutput_bind_eq_expectedValue]
      rw [← expectedValue_finsetSum]
      apply expectedValue_mono
      intro out
      exact ih out.1 (t+1) out.2

/-- Finite union bound stated in the stopped-flag API used by concentration. -/
theorem stopped_hit_union_le (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (fun n s => ∃ i, hit i n s) (fun _ _ => False)) oa).run
        (classify (fun n s => ∃ i, hit i n s) (fun _ _ => False) t s)] ≤
      ∑ i, Pr[fun out => out.2.status = .hit |
        (simulateQ (stoppedImpl impl (hit i) (fun _ _ => False)) oa).run
          (classify (hit i) (fun _ _ => False) t s)] := by
  simp only [prob_stopped_hit_eq_firstHitRun]
  exact firstHitRun_union_le impl hit oa t s

theorem stopped_hit_union_uniform (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S)
    (ε : ℝ≥0∞)
    (hbound : ∀ i, Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (hit i) (fun _ _ => False)) oa).run
        (classify (hit i) (fun _ _ => False) t s)] ≤ ε) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (fun n s => ∃ i, hit i n s) (fun _ _ => False)) oa).run
        (classify (fun n s => ∃ i, hit i n s) (fun _ _ => False) t s)] ≤
      (Fintype.card I:ℝ≥0∞)*ε := by
  apply (stopped_hit_union_le impl hit oa t s).trans
  calc
    (∑ i, Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (hit i) (fun _ _ => False)) oa).run
        (classify (hit i) (fun _ _ => False) t s)]) ≤ ∑ _i : I, ε :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Fintype.card I:ℝ≥0∞)*ε := by simp [nsmul_eq_mul]

/-- A terminal violation in the actual unmodified execution is included in a
first hit of the same state predicate. No transcript or stopping coupling is assumed. -/
theorem terminal_bad_le_firstHit (impl : QueryImpl spec (StateT S ProbComp))
    (bad : S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S) :
    Pr[fun out => bad out.2 | (simulateQ impl oa).run s] ≤
      Pr[= true | firstHitRun impl (fun _ s => bad s) (fun _ _ => False) oa t s] := by
  induction oa using OracleComp.inductionOn generalizing t s with
  | pure a =>
    by_cases hh : bad s <;> simp [hh]
  | query_bind q k ih =>
    by_cases hh : bad s
    · rw [firstHitRun_of_hit _ _ _ _ _ _ hh]
      simpa using (probEvent_le_one (mx := (simulateQ impl
        ((liftM (spec.query q) : OracleComp spec (spec.Range q)) >>= k)).run s)
        (p := fun out => bad out.2))
    · rw [firstHitRun_query_bind, if_neg hh, if_false]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        probEvent_bind_eq_expectedValue, probOutput_bind_eq_expectedValue]
      apply expectedValue_mono
      intro out
      exact ih out.1 (t+1) out.2

end WeightedOracleExecution
end
end

section

/-! The actual pre-sign cache, viewed as a partially exposed nonce row. -/
noncomputable section
namespace WeightedCacheCounts
open scoped Classical
variable {D Q W I : Type} [Fintype D] [DecidableEq D] [DecidableEq Q]
  [Fintype I] [DecidableEq I]

theorem seen_image (e : D → Q) (c : Q → Option W) :
    seen (Finset.univ.image e) c = (Finset.univ.filter (fun a => (c (e a)).isSome)).image e := by
  ext q
  simp only [seen,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨a,rfl⟩,ha⟩
    exact ⟨a,ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,rfl⟩,ha⟩

theorem seen_image_card (e : D → Q) (he : Function.Injective e) (c : Q → Option W) :
    (seen (Finset.univ.image e) c).card=(Finset.univ.filter (fun a => (c (e a)).isSome)).card := by
  rw [seen_image,Finset.card_image_of_injective _ he]

theorem counts_image (e : D → Q) (he : Function.Injective e) (c : Q → Option W)
    (decode : W → Option I) :
    classCounts (Finset.univ.image e) c decode =
      WeightedCompletion.rowCount (Finset.univ.filter (fun a => (c (e a)).isSome))
        (fun a => (c (e a)).bind decode) := by
  funext i
  unfold classCounts WeightedPublicCounts.counts WeightedCompletion.rowCount
  rw [seen_image,Finset.filter_image,Finset.card_image_of_injective _ he]
end WeightedCacheCounts

end
end

section

/-! Exact conditional-completion tower for cache-sensitive terminal payoffs.
The lazy side retains the actual observed cache, then completes its unqueried
finite coordinates uniformly. The eager side samples once before execution. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance stagedLocal_ReplacementCompletion_1 {α : Type*} : DecidableEq α := Classical.decEq α

abbrev cacheE {α : Type} (oa : OracleComp Spec α) (c : Cache)
    (f : α → Cache → ℝ≥0∞) : ℝ≥0∞ := E (run oa c) (fun p => f p.1 p.2)

def completePayoff {D α : Type} [Fintype D] [SampleableType (D → BitVec hashBits)]
    (S : QuerySlice D) (f : α → Cache → ℝ≥0∞) (a : α) (c : Cache) : ℝ≥0∞ :=
  E ($ᵗ (D → BitVec hashBits)) (fun g => f a (S.preload c g))

theorem cacheE_pure {α : Type} (a : α) (c : Cache) (f : α → Cache → ℝ≥0∞) :
    cacheE (pure a) c f = f a c := by rw [cacheE, run_pure, E_pure]

theorem cacheE_unif {α : Type} (n : ℕ) (k : Spec.Range (.inl n) → OracleComp Spec α)
    (c : Cache) (f : α → Cache → ℝ≥0∞) :
    cacheE (liftM (Spec.query (.inl n)) >>= k) c f =
      E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) (fun a => cacheE (k a) c f) := by
  simp only [cacheE, run_query_bind, oracleImpl_run_inl, E_bind, E_pure]

theorem cacheE_hash_none {α : Type} (q : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (f : α → Cache → ℝ≥0∞)
    (hc : c q = none) :
    cacheE (liftM (Spec.query (.inr q)) >>= k) c f =
      E ($ᵗ BitVec hashBits) (fun y => cacheE (k y) (c.cacheQuery q y) f) := by
  simp only [cacheE, run_query_bind, oracleImpl_run_inr_none hc, E_bind, E_pure]

theorem cacheE_hash_some {α : Type} (q : Query)
    (k : BitVec hashBits → OracleComp Spec α) (c : Cache) (f : α → Cache → ℝ≥0∞)
    (y : BitVec hashBits) (hc : c q = some y) :
    cacheE (liftM (Spec.query (.inr q)) >>= k) c f = cacheE (k y) c f := by
  simp only [cacheE, run_query_bind, oracleImpl_run_inr_some hc, pure_bind]

/-- Uniform completion after the actual lazy execution equals sampling the
same finite table before execution, for arbitrary output-and-cache payoffs. -/
theorem cacheE_finite_completion {D α : Type} [Fintype D]
    [SampleableType (D → BitVec hashBits)] (S : QuerySlice D)
    (oa : OracleComp Spec α) (c : Cache) (f : α → Cache → ℝ≥0∞) :
    cacheE oa c (completePayoff S f) =
      E ($ᵗ (D → BitVec hashBits)) (fun g => cacheE oa (S.preload c g) f) := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [cacheE_pure]
    rfl
  | query_bind t k ih =>
    cases t with
    | inl n =>
      rw [cacheE_unif]
      calc
        _ = E (HasQuery.query (spec := unifSpec) (m := ProbComp) n)
            (fun a => E ($ᵗ (D → BitVec hashBits))
              (fun g => cacheE (k a) (S.preload c g) f)) := by
          congr 1
          funext a
          exact ih a c
        _ = E ($ᵗ (D → BitVec hashBits))
            (fun g => E (HasQuery.query (spec := unifSpec) (m := ProbComp) n)
              (fun a => cacheE (k a) (S.preload c g) f)) := E_independent_swap _ _ _
        _ = _ := by
          congr 1
          funext g
          rw [cacheE_unif]
    | inr q =>
      cases hc : c q with
      | some y =>
        rw [cacheE_hash_some q k c (completePayoff S f) y hc]
        calc
          _ = E ($ᵗ (D → BitVec hashBits)) (fun g => cacheE (k y) (S.preload c g) f) := ih y c
          _ = _ := by
            congr 1
            funext g
            rw [cacheE_hash_some q k (S.preload c g) f y (S.preload_some c g q y hc)]
      | none =>
        rw [cacheE_hash_none q k c (completePayoff S f) hc]
        cases hq : S.locate q with
        | none =>
          calc
            _ = E ($ᵗ BitVec hashBits) (fun y => E ($ᵗ (D → BitVec hashBits))
                (fun g => cacheE (k y) (S.preload (c.cacheQuery q y) g) f)) := by
              congr 1
              funext y
              exact ih y (c.cacheQuery q y)
            _ = E ($ᵗ (D → BitVec hashBits)) (fun g => E ($ᵗ BitVec hashBits)
                (fun y => cacheE (k y) (S.preload (c.cacheQuery q y) g) f)) :=
              E_independent_swap _ _ _
            _ = _ := by
              congr 1
              funext g
              have hg : S.preload c g q = none := (S.preload_outside c g q hq).trans hc
              rw [cacheE_hash_none q k (S.preload c g) f hg]
              congr 1
              funext y
              rw [S.preload_cacheQuery]
        | some d =>
          let ψ : (D → BitVec hashBits) → ℝ≥0∞ :=
            fun g => cacheE (k (g d)) (S.preload c g) f
          have he (y : BitVec hashBits) (g : D → BitVec hashBits) :
              cacheE (k y) (S.preload (c.cacheQuery q y) g) f = ψ (Function.update g d y) := by
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
              exact (cacheE_hash_some q k (S.preload c g) f (g d)
                (S.preload_fresh_inside c g q d hc hq)).symm

end
end WeightedReplacement
end
