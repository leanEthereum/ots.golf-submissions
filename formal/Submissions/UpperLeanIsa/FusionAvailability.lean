import Submissions.UpperLeanIsa.FusionKeygen

/-! Availability under actual key generation, including messages chosen from the public key. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
noncomputable section
variable {P : Params}

theorem Record.cache_noIdx (hP : P.Hyp) (ξ : Record P) : P.codec.NoIdx ξ.cache := by
  intro m η pk
  cases h : ξ.cache ⟨896,P.codec.idxInput m η pk⟩ with
  | none => rfl
  | some y =>
    obtain ⟨a,ha,-⟩ := (ξ.cache_some_iff hP _ y).mp h
    exact (ξ.query_ne_idx hP a m η pk ha).elim

theorem Record.cache_noIdxBut (hP : P.Hyp) (ξ : Record P) : P.codec.NoIdxBut ξ.cache :=
  ⟨⟨0,0⟩,fun m η pk _ => ξ.cache_noIdx hP m η pk⟩

namespace Params
variable (P : Params)

theorem recW_ne_zero : recW P ≠ 0 := by
  unfold recW
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

theorem sum_recW : ∑ _ξ : Record P, recW P = 1 := by
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  unfold recW
  have h : (Fintype.card (Record P) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact ENNReal.mul_inv_cancel h (ENNReal.natCast_ne_top _)

theorem signingFailure (hP : P.Hyp) (hl : P.locationOrder.Pairwise Earlier)
    {S : Tier.Sched} (hS : S.Valid) (hT : P.codec.TierHyp S) :
    P.scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) := by
  intro message
  rw [Layer.Params.probTrue_eq_E_run,run_bind,E_bind]
  change E (run P.keygen ∅) (fun q =>
    E (run (P.codec.sign q.1.2 (message q.1.1) >>= fun σ => pure σ.isNone) q.2)
      (fun p => if p.1 = true then 1 else 0)) ≤ _
  rw [E_run_keygen hP hl]
  calc
    _ ≤ ∑ ξ : Record P, recW P * (1 / 2 ^ signingFailureBits) := by
      apply Finset.sum_le_sum
      intro ξ _
      exact mul_le_mul' le_rfl (P.codec.sign_isNone_le' hS hT ξ.sk (message ξ.pk)
        ξ.cache (ξ.cache_noIdxBut hP))
    _ = _ := by rw [← Finset.sum_mul,P.sum_recW,one_mul]

end Params

theorem concrete_signingFailure :
    params.scheme.SigningFailureAtMost (1 / 2 ^ signingFailureBits) :=
  params.signingFailure params_hyp concrete_ordered FusionNumeric.schedule_valid FusionCodec.tierHyp

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
