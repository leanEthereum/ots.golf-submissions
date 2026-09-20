import Submissions.UpperCompressions.SigningReserve
import Submissions.UpperCompressions.IndexedResources
import Submissions.UpperCompressions.IndexedRho
import Submissions.UpperCompressions.AlgorithmCosts

/-! Apply the existing signing hazard theorem with zero signing charge and a
pure dummy continuation, reserving the real continuation's entire cost first.
The total cache cap is an abstract natural, not the old 2^127 invariant. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical

noncomputable section

namespace OptimalOTS
namespace IndexedAnalysis
namespace ReservedHazard

open OptimalOTS.Dag
open OptimalOTS.AlgorithmCosts
local notation "M" => OptimalOTS.IndexedAnalysis.numCuts

attribute [local irreducible] CostAtMost hashBits msgBits nonceBits idxBits trials

/-- An upper bound matching the reservation lemma's lower bound. -/
theorem costAtMost_signIdxLoop (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce), CostAtMost (signIdxLoop m k tried) k
  | 0, _ => costAtMost_pure _ _
  | k + 1, tried => by
      rw [signIdxLoop]
      split_ifs
      · refine CostAtMost.bind_le (costAtMost_liftM_probComp _ 0)
          (b₂ := k + 1) (fun j => ?_) (by simp)
        refine CostAtMost.bind_le (IndexedDag.costAtMost_submittedIndex (by
          norm_num [blockCost, msgBits, nonceBits, blockBits]) _ _)
          (b₂ := k) (fun i => ?_) (by omega)
        split_ifs
        · exact costAtMost_pure _ _
        · exact costAtMost_signIdxLoop m k _
      · exact costAtMost_pure _ _

theorem costAtMost_signIdx (m : Message) : CostAtMost (signIdx m) trials :=
  costAtMost_signIdxLoop m trials ∅

/-- Reserved signing hazard: the real continuations are already bounded by
`b-trials`; signing itself is analyzed using a zero-charge pure continuation. -/
theorem reserved_signRho_bound
    (hM : M ≤ 2 ^ idxBits) (hidx : idxBits ≤ hashBits)
    (m : Message) (d : Cache) {β J : Type}
    (kont : J → Option (Nonce × Fin M) → OracleComp Spec β)
    (Fn : Option (Nonce × Fin M) → Cache → ℝ≥0∞)
    (Φ : Cache → ℝ≥0∞) (hΦ : EncInvariant Φ) (κ lam ρ : ℝ≥0∞)
    (cap b : ℕ) (hLb : trials ≤ b) (hinit : encCount d + b ≤ cap)
    (hkont : ∀ j r, CostAtMost (kont j r) (b - trials))
    (hF : ∀ r d', SignExt m d r d' → encCount d' + (b - trials) ≤ cap →
      (∀ j, CostAtMost (kont j r) (b - trials)) →
      Fn r d' ≤ Φ d' + lam *
        (if ∃ η i, r = some (η, i) ∧ IdxPre d (m ++ η) i.val then 1 else 0) +
        κ * ((b - trials : ℕ) : ℝ≥0∞))
    (hρ : ∀ c : ℕ, (rowFresh d m).card ≤ c + trials → c ≤ (rowFresh d m).card →
      ((rowBad d m).card : ℝ≥0∞) + c * (((V d).card : ℝ≥0∞) / 2 ^ idxBits) ≤
        ρ * ((rowAcc d m).card + c * ((M : ℝ≥0∞) / 2 ^ idxBits))) :
    E (run (signIdx m) d) (fun p => Fn p.1 p.2) ≤
      Φ d + lam * ρ + κ * ((b - trials : ℕ) : ℝ≥0∞) := by
  let Ψ : Cache → ℝ≥0∞ := fun c => Φ c + κ * ((b - trials : ℕ) : ℝ≥0∞)
  let Inv : Cache → ℕ → Prop := fun c rem => encCount c + rem + (b - trials) ≤ cap
  let dummy : Unit → Option (Nonce × Fin M) → OracleComp Spec Unit := fun _ _ => pure ()
  have hΨ : EncInvariant Ψ := by
    intro c u w
    dsimp only [Ψ]
    rw [hΦ c u w]
  have hfresh : ∀ c rem q, Inv c rem → c q = none → queryCost (.inr q) ≤ rem →
      ∀ u, Inv (c.cacheQuery q u) (rem - queryCost (.inr q)) := by
    intro c rem q hI _ hq u
    have hc := encCount_cacheQuery_le c q u
    have hcost : 1 ≤ queryCost (.inr q) := by
      exact Nat.le_max_left _ _
    dsimp only [Inv] at hI ⊢
    omega
  have hcached : ∀ c rem q, Inv c rem → (c q).isSome → queryCost (.inr q) ≤ rem →
      Inv c (rem - queryCost (.inr q)) := by
    intro c rem q hI _ _
    dsimp only [Inv] at hI ⊢
    omega
  have hstart : Inv d trials := by
    dsimp only [Inv]
    omega
  have hdummy : ∀ j : Unit, CostAtMost (signIdx m >>= dummy j) trials := by
    intro j
    exact CostAtMost.bind_le (costAtMost_signIdx m)
      (fun _ => costAtMost_pure () 0) (by simp)
  have hcont : ∀ r d' rem, SignExt m d r d' → Inv d' rem →
      (∀ j : Unit, CostAtMost (dummy j r) rem) →
      Fn r d' ≤ Ψ d' + lam *
        (if ∃ η i, r = some (η, i) ∧ IdxPre d (m ++ η) i.val then 1 else 0) +
        0 * rem := by
    intro r d' rem hext hI _
    have hcount : encCount d' + (b - trials) ≤ cap := by
      dsimp only [Inv] at hI
      omega
    have h := hF r d' hext hcount (fun j => hkont j r)
    simpa only [Ψ, zero_mul, add_zero, zero_add, add_assoc, add_left_comm, add_comm] using h
  have h := signRho_bound hM hidx m d dummy Fn Ψ hΨ 0 lam ρ
    Inv hfresh hcached hcont hρ hstart hdummy
  simpa only [Ψ, zero_mul, add_zero, zero_add, add_assoc, add_left_comm, add_comm] using h

/-- The resource reservation is discharged directly from the actual composed
signing/continuation programs. -/
theorem reserved_signRho_bound_of_cost
    (hM : M ≤ 2 ^ idxBits) (hidx : idxBits ≤ hashBits)
    (m : Message) (d : Cache) {β J : Type} [Nonempty J]
    (kont : J → Option (Nonce × Fin M) → OracleComp Spec β)
    (Fn : Option (Nonce × Fin M) → Cache → ℝ≥0∞)
    (Φ : Cache → ℝ≥0∞) (hΦ : EncInvariant Φ) (κ lam ρ : ℝ≥0∞)
    (cap b : ℕ) (hinit : encCount d + b ≤ cap)
    (hB : ∀ j, CostAtMost (signIdx m >>= kont j) b)
    (hF : ∀ r d', SignExt m d r d' → encCount d' + (b - trials) ≤ cap →
      (∀ j, CostAtMost (kont j r) (b - trials)) →
      Fn r d' ≤ Φ d' + lam *
        (if ∃ η i, r = some (η, i) ∧ IdxPre d (m ++ η) i.val then 1 else 0) +
        κ * ((b - trials : ℕ) : ℝ≥0∞))
    (hρ : ∀ c : ℕ, (rowFresh d m).card ≤ c + trials → c ≤ (rowFresh d m).card →
      ((rowBad d m).card : ℝ≥0∞) + c * (((V d).card : ℝ≥0∞) / 2 ^ idxBits) ≤
        ρ * ((rowAcc d m).card + c * ((M : ℝ≥0∞) / 2 ^ idxBits))) :
    E (run (signIdx m) d) (fun p => Fn p.1 p.2) ≤
      Φ d + lam * ρ + κ * ((b - trials : ℕ) : ℝ≥0∞) := by
  have hreserve := fun j => SigningReserve.signIdx_reserve m (kont j) (hB j)
  exact reserved_signRho_bound hM hidx m d kont Fn Φ hΦ κ lam ρ cap b
    (hreserve (Classical.arbitrary J)).1 hinit (fun j => (hreserve j).2) hF hρ

#print axioms costAtMost_signIdxLoop
#print axioms reserved_signRho_bound
#print axioms reserved_signRho_bound_of_cost

end ReservedHazard
end IndexedAnalysis
end OptimalOTS
