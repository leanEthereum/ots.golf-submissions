import Submissions.UpperCompressions.ProofBundle09
import Submissions.UpperCompressions.ProofBundle00
import Submissions.UpperCompressions.ProofBundle01
import Submissions.UpperCompressions.ProofBundle08
import Submissions.UpperCompressions.ProofBundle07

/- Original module: Submissions.UpperCompressions.ActualWeightedMoments; SHA256 724214e81b746c932938cc14bb12cf49f4e8a70d1b433f83155c4ad8b74dd79c. -/
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

#print axioms actual_stopped_moments

end WeightedActualMoments
end
end

/- Original module: Submissions.UpperCompressions.ActualLinearBoundary; SHA256 38baf3df0738f2f6087b134984ee88e34d3201abfb472ca94469e9092a51276e. -/
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

#print axioms actual_linear_boundary
end WeightedOracleExecution
end
end

/- Original module: Submissions.UpperCompressions.ActualScoreConcentration; SHA256 1d0eff2f3d473a56b2371a71d6de5a5981affa20a3f19d3849cf7859d19f998a. -/
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

/-- Concrete global mixed72 margin, uniform in the program length and paid budget. -/
theorem mixed_global (κ : ℝ) (hκ : 0 < κ) (hm : w.mean ≤ κ)
    (hg : ∀ i, w.g i ≤ (2^20:ℝ)*κ/2)
    (oa : OracleComp OptimalOTS.Spec α) (s₀ : S)
    (hq0 : qCount s₀ = 0) (hk0 : counts s₀ = fun _ => 0) :
    let hit := fun (_ : ℕ) (s : S) =>
      (κ/100)*max (qCount s:ℝ) ((2^86:ℝ)/10) ≤ signedM1 w qCount counts false s
    let kill := fun (_ : ℕ) (_ : S) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl hit kill) oa).run (classify hit kill 0 s₀)] ≤
      ENNReal.ofReal (Real.exp (-(2^40:ℝ))) := by
  obtain ⟨hθ, hθG, hc, he⟩ := mixed_global_constants w κ hκ hm
  have hx := global_boundary w impl qCount counts fresh hlaw false
    ((2^20:ℝ)*κ/2) (mixedTheta κ) (κ/100) ((2^86:ℝ)/10)
    (by positivity) hg hθ.le hθG (by positivity) hc oa s₀ hq0 hk0
  apply hx.trans
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (neg_le_neg he)

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

#print axioms mixed_global
#print axioms mixed_row

#print axioms query_mgf
#print axioms global_boundary
#print axioms row_freedman
end WeightedActualScore
end
end

/- Original module: Submissions.UpperCompressions.ProtectedCacheStatistics; SHA256 53fcef296f9370dda8f4ed38b6acf00a7d909921b599d95465af7162af0c312e. -/
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

#print axioms count_le_cost
#print axioms count_bound
#print axioms stopped_moments

#print axioms protectedImpl_eq
#print axioms query_law
end WeightedProtectedCache
end
end

/- Original module: Submissions.UpperCompressions.WidePreSign; SHA256 9d4dae7495da2edcfa37a8bb350948937956dc0c1a7f6de7e4913ffe920aebb3. -/
section

/-! The exact primitive-query law for the concrete weighted92 decoder under
the contract's actual shared random oracle. This applies before signing. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WidePreSign
open OracleSpec OracleComp
open WeightedSchedule WideDomains WeightedCacheCounts WeightedRow.Weights
open WeightedRealExecution WeightedDirectCache
open scoped Classical

theorem primitive_law (A : Finset Query) (t : Spec.Domain) (c : hashSpec.QueryCache)
    (f : ℕ → (Fin M → ℕ) → ℝ) :
    realEval ((oracleImpl t).run c)
      (fun out => f (seen A out.2).card (classCounts A out.2 decode)) =
    securityWeights.expect (fun x => f
      (step (protectedFresh A t c) (seen A c).card (classCounts A c decode) x).1
      (step (protectedFresh A t c) (seen A c).card (classCounts A c decode) x).2) := by
  exact WeightedProtectedCache.query_law securityWeights A decode decoder_law t c f

theorem index_initial (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    (seen indexDomain c).card=0 ∧ classCounts indexDomain c decode=(fun _ => 0) := by
  constructor
  · rw [fresh_seen_empty c hf,Finset.card_empty]
  · exact fresh_counts_zero c hf

theorem row_count_bound (m : Message) (c : hashSpec.QueryCache) :
    (seen (rowDomain m) c).card ≤ 2^86 := seen_row_bound m c

#print axioms primitive_law
#print axioms index_initial
end OptimalOTS.WeightedConstruction.WidePreSign
end
end

/- Original module: Submissions.UpperCompressions.ProtectedConcentration; SHA256 5e8ef6309635368ee6575d81d04f6a8ba952f299ec11c84671250a9498ef6e37. -/
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

/-- Every prefix of actual shared-oracle execution obeys the global boundary,
except with probability exp(-2^40); no fixed paid budget or time union is used. -/
theorem global_score (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (κ : ℝ) (hκ : 0 < κ) (hm : w.mean ≤ κ) (hg : ∀ i, w.g i ≤ (2^20:ℝ)*κ/2)
    (oa : OracleComp OptimalOTS.Spec α) (cache : OptimalOTS.hashSpec.QueryCache)
    (hq0 : (seen A cache).card = 0) (hk0 : classCounts A cache decode = fun _ => 0) :
    let hit := fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      (κ/100)*max ((seen A c).card:ℝ) ((2^86:ℝ)/10) ≤ w.M1 (seen A c).card (classCounts A c decode)
    let kill := fun (_ : ℕ) (_ : OptimalOTS.hashSpec.QueryCache) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl OptimalOTS.oracleImpl hit kill) oa).run (classify hit kill 0 cache)] ≤
      ENNReal.ofReal (Real.exp (-(2^40:ℝ))) := by
  exact WeightedActualScore.mixed_global w OptimalOTS.oracleImpl
    (fun c => (seen A c).card) (fun c => classCounts A c decode)
    (protectedFresh A) (query_law w A decode hfiber) κ hκ hm hg oa cache hq0 hk0

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

#print axioms global_score
#print axioms row_score
end WeightedProtectedCache
end
end

/- Original module: Submissions.UpperCompressions.WideCountRelations; SHA256 bc7e9db5b0cf68461e5fc391f68d1284637353c30e7b223856692f1572499c7d. -/
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

theorem row_class_le_global (m : Message) (c : hashSpec.QueryCache)
    (i : Fin WeightedSchedule.M) :
    classCounts (rowDomain m) c WeightedSchedule.decode i ≤
      classCounts indexDomain c WeightedSchedule.decode i :=
  classCounts_mono (row_subset m) c WeightedSchedule.decode i

theorem fresh_row_succ_bound (m : Message) (c : hashSpec.QueryCache)
    (q : Query) (hq : q ∈ rowDomain m) (hc : c q = none) :
    (seen (rowDomain m) c).card + 1 ≤ 2^86 :=
  (fresh_seen_succ_le (rowDomain m) c q (0 : BitVec hashBits) hq hc).trans_eq
    (row_card m)

#print axioms row_class_le_global
#print axioms fresh_row_succ_bound
end OptimalOTS.WeightedConstruction.WideDomains
end
end

/- Original module: Submissions.UpperCompressions.WideConcentration; SHA256 f2d70a3e365277ff9a1eb34b6375afa2f54a3ea172119a610029e7a2faf4ff48. -/
section

/-! Concrete time-uniform pre-sign score bounds for every message row.
The underlying execution is the contract's actual shared oracle throughout. -/
noncomputable section
open OracleSpec OracleComp
open scoped Classical
namespace WeightedProtectedCache
variable {ι α : Type} [Fintype ι] [DecidableEq ι]
theorem row_reweighted (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query) (hcard : A.card ≤ 2^86)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b=x)).card:ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (g : ι → ℝ) (hg0 : ∀ i,0 ≤ g i)
    (lower : Bool) (G : ℝ) (hG : 0 < G) (hg : ∀ i,g i ≤ G)
    (oa : OracleComp OptimalOTS.Spec α) (cache : OptimalOTS.hashSpec.QueryCache)
    (hq0 : (WeightedCacheCounts.seen A cache).card=0)
    (hk0 : WeightedCacheCounts.classCounts A cache decode=(fun _ => 0)) :
    let hit := fun (_ : ℕ) (c : OptimalOTS.hashSpec.QueryCache) =>
      G*(2^86:ℝ)/(100*(2^20:ℝ)) ≤ WeightedActualScore.signedM1 (w.withScore g hg0)
        (fun c => (WeightedCacheCounts.seen A c).card)
        (fun c => WeightedCacheCounts.classCounts A c decode) lower c
    let kill := fun (_ : ℕ) (_ : OptimalOTS.hashSpec.QueryCache) => False
    Pr[fun out => out.2.status = .hit |
      (simulateQ (WeightedOracleExecution.stoppedImpl OptimalOTS.oracleImpl hit kill) oa).run
        (WeightedFirstHit.classify hit kill 0 cache)] ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  apply row_score (w.withScore g hg0) A hcard decode _ lower G hG hg oa cache hq0 hk0
  intro x
  exact (hfiber x).trans (WeightedRow.Weights.withScore_classMass w g hg0 x).symm
end WeightedProtectedCache
namespace OptimalOTS.WeightedConstruction.WideConcentration
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedReference WeightedConstants WeightedSchedule WideDomains
open WeightedCacheCounts WeightedRow.Weights WeightedOracleExecution WeightedFirstHit
open scoped Classical ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter

def crossing {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (bad : hashSpec.QueryCache → Prop) : ℝ≥0∞ :=
  Pr[fun out => out.2.status = .hit |
    (simulateQ (stoppedImpl oracleImpl (fun _ c => bad c) (fun _ _ => False)) oa).run
      (classify (fun _ c => bad c) (fun _ _ => False) 0 c)]

theorem row_initial (m : Message) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    (seen (rowDomain m) c).card=0 ∧ classCounts (rowDomain m) c decode=(fun _ => 0) := by
  obtain ⟨hq,hk⟩ := WidePreSign.index_initial c hf
  constructor
  · have h := Finset.card_le_card (seen_row_subset m c)
    rw [hq] at h
    exact Nat.eq_zero_of_le_zero h
  · funext i
    have h := row_class_le_global m c i
    rw [hk] at h
    exact Nat.eq_zero_of_le_zero h

theorem global_bound {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (fun d => (kappa/100)*max ((seen indexDomain d).card:ℝ) ((2:ℝ)^86/10) ≤
      securityWeights.M1 (seen indexDomain d).card (classCounts indexDomain d decode)) ≤
        ENNReal.ofReal (Real.exp (-(2^40:ℝ))) := by
  obtain ⟨hq,hk⟩ := WidePreSign.index_initial c hf
  have hm : securityWeights.mean ≤ kappa := securityWeights_mean.trans (by norm_num [kappa])
  exact WeightedProtectedCache.global_score securityWeights indexDomain decode decoder_law kappa
    (by norm_num [kappa]) hm (fun i => by
      simpa only [securityWeights,L,Nat.cast_pow,Nat.cast_ofNat] using referenceWeight_le i) oa c hq hk

theorem row_withScore_bound {α : Type} (g : Fin M → ℝ) (hg0 : ∀ i,0 ≤ g i)
    (G : ℝ) (hG : 0 < G) (hg : ∀ i,g i ≤ G) (lower : Bool)
    (m : Message) (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (fun d => G*(2:ℝ)^86/(100*(2:ℝ)^20) ≤
      WeightedActualScore.signedM1 (securityWeights.withScore g hg0)
        (fun d => (seen (rowDomain m) d).card)
        (fun d => classCounts (rowDomain m) d decode) lower d) ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  obtain ⟨hq,hk⟩ := row_initial m c hf
  exact WeightedProtectedCache.row_reweighted securityWeights (rowDomain m)
    (row_card m).le decode decoder_law g hg0 lower G hG hg oa c hq hk

def excessWeights : WeightedRow.Weights (Fin M) := securityWeights.withScore
  (fun i => referenceWeight i*excess i/classProbability i) excessScore_nonneg

theorem excessWeights_mean : excessWeights.mean=(∑ i : Fin M,referenceWeight i*excess i) := by
  unfold WeightedRow.Weights.mean
  apply Finset.sum_congr rfl
  intro i hi
  change classProbability i*(referenceWeight i*excess i/classProbability i)=_
  field_simp [(classProbability_pos i).ne']

theorem row_excess_bound {α : Type} (m : Message) (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (fun d => kappa*(2:ℝ)^86/100 ≤
      excessWeights.M1 (seen (rowDomain m) d).card (classCounts (rowDomain m) d decode)) ≤
      ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  have h := row_withScore_bound
    (fun i => referenceWeight i*excess i/classProbability i) excessScore_nonneg
    ((L:ℝ)*kappa) (by norm_num [L,kappa]) excessScore_le false m oa c hf
  have he : ((L:ℝ)*kappa)*(2:ℝ)^86/(100*(2:ℝ)^20)=kappa*(2:ℝ)^86/100 := by
    norm_num [L,kappa]
  simp only [WeightedActualScore.signedM1,Bool.false_eq_true,ite_false,he] at h
  exact h

#print axioms global_bound
#print axioms row_withScore_bound
#print axioms row_excess_bound
end OptimalOTS.WeightedConstruction.WideConcentration
end
end

/- Original module: Submissions.UpperCompressions.FirstHitUnion; SHA256 99292e25bed08ed3fcb78f7146a9d2f64ac9f05f8fcdb3593b0dfb4f5b53a6e9. -/
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

/-- Actual mixed72 Good-event union, including all message rows and the global
boundary, once the explicit per-event crossing bounds are supplied. -/
theorem stopped_mixed_union (impl : QueryImpl spec (StateT S ProbComp))
    (hit : I → ℕ → S → Prop) (oa : OracleComp spec α) (t : ℕ) (s : S)
    (hcard : Fintype.card I ≤ 74*2^256+1)
    (hbound : ∀ i, Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (hit i) (fun _ _ => False)) oa).run
        (classify (hit i) (fun _ _ => False) t s)] ≤
          ENNReal.ofReal (Real.exp (-(2^30:ℝ)))) :
    Pr[fun out => out.2.status = .hit |
      (simulateQ (stoppedImpl impl (fun n s => ∃ i, hit i n s) (fun _ _ => False)) oa).run
        (classify (fun n s => ∃ i, hit i n s) (fun _ _ => False) t s)] ≤
      ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have hn : (Fintype.card I:ℝ) ≤ 74*(2^256:ℝ)+1 := by exact_mod_cast hcard
  calc
    _ ≤ (Fintype.card I:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(2^30:ℝ))) :=
      stopped_hit_union_uniform impl hit oa t s _ hbound
    _ = ENNReal.ofReal ((Fintype.card I:ℝ)*Real.exp (-(2^30:ℝ))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((74*(2^256:ℝ)+1)*Real.exp (-(2^30:ℝ))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _))
    _ ≤ ENNReal.ofReal (((2:ℝ)^512)⁻¹) :=
      ENNReal.ofReal_le_ofReal WeightedEmpirical.mixed_row_union_margin

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

#print axioms stopped_hit_union_uniform
#print axioms stopped_mixed_union
#print axioms terminal_bad_le_firstHit

#print axioms firstHitRun_union_le
#print axioms stopped_hit_union_le
end WeightedOracleExecution
end
end

/- Original module: Submissions.UpperCompressions.WideEmpiricalGood; SHA256 c638154d911963644d18fffd17a30b74b403899348e8bc9a250c10d104bea748. -/
section

/-! A single actual pre-sign Good event, simultaneously over all messages and
72 tier prefixes, row scores, row excess scores, and the global score. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideEmpirical
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedReference WeightedConstants WeightedSchedule WideDomains WideConcentration
open WeightedCacheCounts WeightedRow.Weights WeightedOracleExecution WeightedFirstHit
open scoped Classical ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter

def prefixClasses (j : Fin 72) : Finset (Fin M) := Finset.univ.filter (fun i => tier i ≤ j.val)
def prefixWeight (j : Fin 72) : WeightedRow.Weights (Fin M) := securityWeights.prefixWeights (prefixClasses j)

def globalBad (c : hashSpec.QueryCache) : Prop :=
  (kappa/100)*max ((seen indexDomain c).card:ℝ) ((2:ℝ)^86/10) ≤
    securityWeights.M1 (seen indexDomain c).card (classCounts indexDomain c decode)
def prefixBad (m : Message) (j : Fin 72) (c : hashSpec.QueryCache) : Prop :=
  (2:ℝ)^86/(100*(2:ℝ)^20) ≤
    -(prefixWeight j).M1 (seen (rowDomain m) c).card (classCounts (rowDomain m) c decode)
def scoreBad (m : Message) (c : hashSpec.QueryCache) : Prop :=
  kappa*(2:ℝ)^86/100 ≤ securityWeights.M1
    (seen (rowDomain m) c).card (classCounts (rowDomain m) c decode)
def excessBad (m : Message) (c : hashSpec.QueryCache) : Prop :=
  kappa*(2:ℝ)^86/100 ≤ excessWeights.M1
    (seen (rowDomain m) c).card (classCounts (rowDomain m) c decode)

theorem prefix_bound {α : Type} (m : Message) (j : Fin 72) (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (prefixBad m j) ≤ ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  obtain ⟨hq,hk⟩ := row_initial m c hf
  have h := row_withScore_bound (fun i => if i ∈ prefixClasses j then 1 else 0)
    (fun i => by split_ifs <;> norm_num) 1 (by norm_num)
    (securityWeights.prefix_weight_bound (prefixClasses j)) true m oa c hf
  simp only [WeightedActualScore.signedM1,ite_true,one_mul] at h
  exact h

theorem score_bound {α : Type} (m : Message) (oa : OracleComp Spec α)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (scoreBad m) ≤ ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  obtain ⟨hq,hk⟩ := row_initial m c hf
  have hg (i : Fin M) : securityWeights.g i ≤ (L:ℝ)*kappa := by
    have h := referenceWeight_le i
    change referenceWeight i ≤ _
    have hn : 0 ≤ (L:ℝ)*kappa := by norm_num [L,kappa]
    linarith
  have h : crossing oa c (fun d => ((L:ℝ)*kappa)*(2:ℝ)^86/(100*(2:ℝ)^20) ≤
      WeightedActualScore.signedM1 securityWeights
        (fun d => (seen (rowDomain m) d).card)
        (fun d => classCounts (rowDomain m) d decode) false d) ≤
        ENNReal.ofReal (Real.exp (-(2^30:ℝ))) :=
    WeightedProtectedCache.row_score securityWeights (rowDomain m) (row_card m).le
      decode decoder_law false ((L:ℝ)*kappa) (by norm_num [L,kappa]) hg oa c hq hk
  have he : ((L:ℝ)*kappa)*(2:ℝ)^86/(100*(2:ℝ)^20)=kappa*(2:ℝ)^86/100 := by norm_num [L,kappa]
  simp only [WeightedActualScore.signedM1,Bool.false_eq_true,ite_false,he] at h
  exact h

abbrev BadIndex := Unit ⊕ (Message × Fin 74)
def event : BadIndex → hashSpec.QueryCache → Prop
  | .inl _ => globalBad
  | .inr (m,j) => if h : j.val < 72 then prefixBad m ⟨j.val,h⟩
      else if j.val=72 then scoreBad m else excessBad m

theorem event_bound {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) (i : BadIndex) :
    crossing oa c (event i) ≤ ENNReal.ofReal (Real.exp (-(2^30:ℝ))) := by
  cases i with
  | inl u =>
    apply (global_bound oa c hf).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    norm_num
  | inr p =>
    obtain ⟨m,j⟩ := p
    dsimp only [event]
    split_ifs with h h'
    · exact prefix_bound m ⟨j.val,h⟩ oa c hf
    · exact score_bound m oa c hf
    · exact row_excess_bound m oa c hf

def Good (c : hashSpec.QueryCache) : Prop := ∀ i : BadIndex,¬ event i c

theorem all_crossings {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    crossing oa c (fun d => ∃ i : BadIndex,event i d) ≤ ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have hc : Fintype.card BadIndex ≤ 74*2^256+1 := by
    norm_num [BadIndex,Message,msgBits,Fintype.card_sum,Fintype.card_prod,Fintype.card_bitVec]
  exact stopped_mixed_union oracleImpl (fun i _ c => event i c) oa 0 c hc (event_bound oa c hf)

theorem terminal_bad {α : Type} (oa : OracleComp Spec α) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query,q.1=342 → c q=none) :
    Pr[fun out => ¬Good out.2 | (simulateQ oracleImpl oa).run c] ≤
      ENNReal.ofReal (((2:ℝ)^512)⁻¹) := by
  have hgood (d : hashSpec.QueryCache) : (¬Good d) = (∃ i : BadIndex,event i d) := by
    simp only [Good,not_forall,not_not]
  simp only [hgood]
  apply (terminal_bad_le_firstHit oracleImpl (fun d => ∃ i : BadIndex,event i d) oa 0 c).trans
  have h := all_crossings oa c hf
  simpa only [crossing,prob_stopped_hit_eq_firstHitRun] using h

#print axioms all_crossings
#print axioms terminal_bad
end OptimalOTS.WeightedConstruction.WideEmpirical
end
end

/- Original module: Submissions.UpperCompressions.WideReplayBounds; SHA256 e64e7f3870bb0c3fea67475d28f077decb9dac69749365c133bf08779fe2306f. -/
section

/-! Concrete mixed72 replay/excess bounds for literal uniform completion tables.
The remaining Good-tail premise is supplied by global table concentration. -/
noncomputable section
open scoped BigOperators Classical
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedCompletion WeightedReplacement WeightedConstants WeightedReference
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
variable {D : Type} [Fintype D] [Nonempty D] [DecidableEq D]

def rowGood (table : D → Option (Fin M)) : Prop := ∀ i,
  fraction (weakRank tier i ∘ table) ≤ survival (tier i)+1/(100*(L:ℝ)) ∧
  fraction (strictRank tier i ∘ table) ≤ lower (tier i)+1/(100*(L:ℝ))

theorem rowGood_kernel (table : D → Option (Fin M)) (hg : rowGood table) (i : Fin M) :
    kernel L (fraction (weakRank tier i ∘ table)) (fraction (strictRank tier i ∘ table)) ≤
      (99:ℝ)/98 * (referenceWeight i / classProbability i) := by
  apply empirical_kernel_le i _ _ _ _ (hg i).1 (hg i).2
  all_goals
    unfold fraction uniformMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x _
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg _

/-- The replay formula is concrete at nonce-domain D; D=BitVec86 gives N=2^86.
The independent table is sampled before applying the joint Good indicator. -/
theorem concrete_replay_bound (R : Finset D) (fixed : D → Option (Fin M)) (k : Fin M → ℕ)
    (Good : (D → BitVec 256) → Prop) (δ : ℝ)
    (hgood : ∀ g, Good g → rowGood (completionTable R fixed decode g))
    (hbad : uniformMean (fun g => if Good g then 0 else 1) ≤ δ) :
    uniformMean (fun g : D → BitVec 256 =>
      tableKernel L (completionTable R fixed decode g) tier (fun a i =>
        if a ∈ R then (if 2 ≤ k i then 1 else 0) else (if k i = 0 then 0 else 1))) ≤
      (99:ℝ)/98 * securityWeights.hazard (Fintype.card D) R.card k (rowCount R fixed) + δ := by
  apply replay_kernel_bound securityWeights L tier R fixed (completionTable R fixed decode) k
    (completionTable_known R fixed decode)
    (completion_decode_probability R fixed) Good ((99:ℝ)/98) δ (by norm_num)
  · intro g hg i
    exact rowGood_kernel _ (hgood g hg) i
  · exact hbad

/-- Concrete expected excess score, including zero payoff on signing failure. -/
theorem concrete_excess_bound (R : Finset D) (fixed : D → Option (Fin M))
    (Good : (D → BitVec 256) → Prop) (δ emax : ℝ) (hemax : 0 ≤ emax)
    (hesc : ∀ i, excess i ≤ emax)
    (hgood : ∀ g, Good g → rowGood (completionTable R fixed decode g))
    (hbad : uniformMean (fun g => if Good g then 0 else 1) ≤ δ) :
    uniformMean (fun g : D → BitVec 256 =>
      tableKernel L (completionTable R fixed decode g) tier (fun _ i => excess i)) ≤
      (99:ℝ)/98 * ((1-(R.card : ℝ)/Fintype.card D) * (∑ i, referenceWeight i * excess i) +
        (∑ i, (rowCount R fixed i : ℝ) * (referenceWeight i/classProbability i * excess i)) /
          Fintype.card D) + emax * δ := by
  apply excess_kernel_bound securityWeights L tier R fixed (completionTable R fixed decode)
    (completionTable_known R fixed decode) (completion_decode_probability R fixed)
    excess (fun i => le_max_right _ _) emax hemax hesc Good ((99:ℝ)/98) δ (by norm_num)
  · intro g hg i
    exact rowGood_kernel _ (hgood g hg) i
  · exact hbad

end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.concrete_replay_bound
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.concrete_excess_bound
end
end

/- Original module: Submissions.UpperCompressions.WideEmpiricalBounds; SHA256 59df98fe826bc35855270a7f349da889541876297345cb81663ae0314b947356. -/
section

/-! Pointwise consequences of the single concrete empirical Good event. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideEmpirical
open WeightedReference WeightedConstants WeightedSchedule WideDomains WideConcentration
open WeightedCacheCounts WeightedRow.Weights
open scoped Classical
set_option maxHeartbeats 1000000

theorem good_global (c : hashSpec.QueryCache) (hc : Good c) :
    securityWeights.score (classCounts indexDomain c decode) ≤
      mean*(seen indexDomain c).card+(kappa/100)*max ((seen indexDomain c).card:ℝ) ((2:ℝ)^86/10) := by
  have h := hc (.inl ())
  change ¬((kappa/100)*max ((seen indexDomain c).card:ℝ) ((2:ℝ)^86/10) ≤
    securityWeights.M1 (seen indexDomain c).card (classCounts indexDomain c decode)) at h
  have hh := lt_of_not_ge h
  change securityWeights.score _-mean*(seen indexDomain c).card < _ at hh
  linarith

theorem good_row_score (c : hashSpec.QueryCache) (hc : Good c) (m : Message) :
    securityWeights.score (classCounts (rowDomain m) c decode) ≤
      mean*(seen (rowDomain m) c).card+kappa*(2:ℝ)^86/100 := by
  have h := hc (.inr (m,⟨72,by decide⟩))
  change ¬scoreBad m c at h
  have hh := lt_of_not_ge h
  change securityWeights.score _-mean*(seen (rowDomain m) c).card < _ at hh
  linarith

theorem good_row_excess (c : hashSpec.QueryCache) (hc : Good c) (m : Message) :
    excessWeights.score (classCounts (rowDomain m) c decode) ≤
      (∑ i : Fin M,referenceWeight i*excess i)*(seen (rowDomain m) c).card+kappa*(2:ℝ)^86/100 := by
  have h := hc (.inr (m,⟨73,by decide⟩))
  change ¬excessBad m c at h
  have hh := lt_of_not_ge h
  unfold excessBad WeightedRow.Weights.M1 at hh
  rw [excessWeights_mean] at hh
  linarith

theorem good_prefix (c : hashSpec.QueryCache) (hc : Good c) (m : Message) (j : Fin 72) :
    (∑ i ∈ prefixClasses j,classProbability i)*(seen (rowDomain m) c).card -
      ∑ i ∈ prefixClasses j,(classCounts (rowDomain m) c decode i:ℝ) ≤
        (2:ℝ)^86/(100*(2:ℝ)^20) := by
  have h := hc (.inr (m,⟨j.val,by have := j.isLt; omega⟩))
  have he : event (.inr (m,⟨j.val,by have := j.isLt; omega⟩)) c = prefixBad m j c := by
    dsimp only [event]
    rw [dif_pos j.isLt]
  rw [he] at h
  have hh := (lt_of_not_ge h).le
  change -(securityWeights.prefixWeights (prefixClasses j)).M1 _ _ ≤ _ at hh
  rw [prefix_deficit] at hh
  exact hh

/-- On Good, the full-completion expected excess has a common class-independent
ceiling. The failure-table allowance remains explicit and joint. -/
theorem good_excess_payoff (c : hashSpec.QueryCache) (hc : Good c) (m : Message) :
    (1-((seen (rowDomain m) c).card:ℝ)/(2:ℝ)^86)*(∑ i : Fin M,referenceWeight i*excess i)+
      excessWeights.score (classCounts (rowDomain m) c decode)/(2:ℝ)^86 ≤
        kappa*(2/5)+kappa/100 := by
  have hs := good_row_excess c hc m
  have hn : (0:ℝ)<2^86 := by positivity
  have hd := (div_le_div_iff_of_pos_right hn).mpr hs
  have hm := excess_mean_le
  have he : (1-((seen (rowDomain m) c).card:ℝ)/(2:ℝ)^86)*(∑ i : Fin M,referenceWeight i*excess i)+
      ((∑ i : Fin M,referenceWeight i*excess i)*(seen (rowDomain m) c).card+kappa*(2:ℝ)^86/100)/(2:ℝ)^86 =
      (∑ i : Fin M,referenceWeight i*excess i)+kappa/100 := by ring
  linarith

#print axioms good_global
#print axioms good_row_score
#print axioms good_prefix
#print axioms good_excess_payoff
end OptimalOTS.WeightedConstruction.WideEmpirical
end
end

/- Original module: Submissions.UpperCompressions.WideCachedRow; SHA256 a05acfd5a94ffbe092a16d0231abd0a750624e9b2b57a0e125ba1fa76de4320f. -/
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

namespace OptimalOTS.WeightedConstruction.WideCachedRow
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedSchedule WideDomains WideForest WeightedReference WeightedConstants
open WeightedReplacement WeightedCompletion WeightedCacheCounts
open scoped Classical
attribute [local irreducible] Finset.univ Finset.filter

def exposed (m : Message) (c : Cache) : Finset (BitVec 86) :=
  Finset.univ.filter (fun η => (c (WideForest.encQuery (m,η))).isSome)
def fixed (m : Message) (c : Cache) (η : BitVec 86) : Option (Fin M) :=
  (c (WideForest.encQuery (m,η))).bind decode

theorem row_injective (m : Message) : Function.Injective (fun η : BitVec 86 => WideForest.encQuery (m,η)) :=
  fun _ _ h => WeightedSampling.Availability.nonce_query_inj m h

theorem exposed_card (m : Message) (c : Cache) :
    (exposed m c).card=(seen (rowDomain m) c).card :=
  (seen_image_card _ (row_injective m) c).symm

theorem fixed_counts (m : Message) (c : Cache) :
    rowCount (exposed m c) (fixed m c)=classCounts (rowDomain m) c decode :=
  (counts_image _ (row_injective m) c decode).symm

theorem cached_known (m : Message) (c : Cache) (g : BitVec 342 → BitVec 256)
    (η : BitVec 86) (hη : η ∈ exposed m c) :
    decode (cachedRow 86 m c g η)=fixed m c η := by
  have hc : (c (WideForest.encQuery (m,η))).isSome := (Finset.mem_filter.mp hη).2
  cases hh : c (WideForest.encQuery (m,η)) with
  | none => simp [hh] at hc
  | some y =>
    change decode ((c (WideForest.encQuery (m,η))).getD _)=(c (WideForest.encQuery (m,η))).bind decode
    rw [hh]
    rfl

theorem cached_fresh (m : Message) (c : Cache) (g : BitVec 342 → BitVec 256)
    (η : BitVec 86) (hη : η ∉ exposed m c) :
    decode (cachedRow 86 m c g η)=decode (g (m++η)) := by
  have hc : c (WideForest.encQuery (m,η))=none := by
    cases hh : c (WideForest.encQuery (m,η)) with
    | none => rfl
    | some y => exact False.elim (hη (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [hh]⟩))
  change decode ((c (WideForest.encQuery (m,η))).getD _)=_
  rw [hc]
  rfl

theorem cached_fresh_probability (m : Message) (c : Cache) (η : BitVec 86)
    (hη : η ∉ exposed m c) (i : Fin M) :
    uniformMean (fun g : BitVec 342 → BitVec 256 =>
      if decode (cachedRow 86 m c g η)=some i then 1 else 0)=classProbability i := by
  simp only [cached_fresh m c _ η hη]
  exact (uniformMean_coordinate (W:=BitVec 256) (m++η)
    (fun x => if decode x=some i then 1 else 0)).trans (uniform_decode_probability i)

theorem tableKernel_nonneg {D I : Type} [Fintype D] [Nonempty D] [DecidableEq D]
    [Fintype I] [DecidableEq I] (k : ℕ) (table : D → Option I) (tier : I → ℕ)
    (f : D → I → ℝ) (hf : ∀ a i,0 ≤ f a i) : 0 ≤ tableKernel k table tier f := by
  rw [← iid_selected_score]
  apply iidMean_nonneg
  intro xs
  cases hs : selected table tier xs with
  | none => simp [score,hs]
  | some p => simpa [score,hs] using hf p.1 p.2

/-- Exact payoff of the actual all-L signing loop, from an arbitrary real cache.
Its conditional row completion is averaged; no Good conditioning is performed. -/
theorem actual_sign_payoff (m : Message) (c : Cache) (f : BitVec 86 → Fin M → ℝ)
    (hf : ∀ a i,0 ≤ f a i) :
    outE (WeightedSampling.loop 86 decode tier m L) c
      (fun s => ENNReal.ofReal (score s (fun r => f r.1 r.2))) =
      ENNReal.ofReal (uniformMean (fun g : BitVec 342 → BitVec 256 =>
        tableKernel L (decode ∘ cachedRow 86 m c g) tier f)) := by
  rw [outE_index342_preload]
  have he (g : BitVec 342 → BitVec 256) :
      outE (WeightedSampling.loop 86 decode tier m L) ((lengthSlice 342).preload c g)
        (fun s => ENNReal.ofReal (score s (fun r => f r.1 r.2))) =
        ENNReal.ofReal (tableKernel L (decode ∘ cachedRow 86 m c g) tier f) :=
    E_loop_fixed_row_score 86 M L decode tier m (cachedRow 86 m c g)
      ((lengthSlice 342).preload c g) (length_preload_row 86 m c g) f hf
  calc
    _ = E ($ᵗ (BitVec 342 → BitVec 256)) (fun g => ENNReal.ofReal
        (tableKernel L (decode ∘ cachedRow 86 m c g) tier f)) := by
      congr 1
      funext g
      exact he g
    _ = _ := E_uniform_ofReal _ (fun g => tableKernel_nonneg L _ tier f hf)

#print axioms exposed_card
#print axioms fixed_counts
#print axioms cached_fresh_probability
#print axioms actual_sign_payoff
end OptimalOTS.WeightedConstruction.WideCachedRow
end
end

/- Original module: Submissions.UpperCompressions.ReplacementCompletion; SHA256 c3ad2e9a1618abf7712f7cdb58e6c60a013b4e2f1a2f06a426858633ca06c2d9. -/
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


#print axioms cacheE_finite_completion
end
end WeightedReplacement
end

