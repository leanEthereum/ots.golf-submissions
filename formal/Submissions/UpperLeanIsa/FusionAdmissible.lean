import Submissions.UpperLeanIsa.FusionCorrectness
import Submissions.UpperLeanIsa.FusionAvailability
import Submissions.UpperLeanIsa.BasicProperties

/-! Pathwise resource bounds, deterministic verification, and full admissibility. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion
open OracleSpec OracleComp
open scoped Classical
noncomputable section
attribute [local irreducible] CostAtMost Deterministic

namespace Params
variable (P : Params)

theorem cost_chain (t : Tops) (k : Fin 42) (j n : ℕ) (x : Word) :
    CostAtMost (P.chain t k j n x) (2*n) := by
  induction n generalizing j x with
  | zero => exact cost_pure _ _
  | succ n ih =>
    have h := cost_bind (cost_map (cost_hash (P.chainInput t k j x)) (P.codec.slice k j))
      (fun y => ih (j+1) y)
    simpa only [chain,chainStep,Nat.mul_succ,Nat.add_comm] using h

theorem cost_reconFrom (I : Index) (bits : List Bool) (l : List (Fin 42)) (t : Tops) :
    CostAtMost (P.reconFrom I bits l t) (2 * (l.map (P.codec.digit I)).sum) := by
  induction l generalizing t with
  | nil => exact cost_pure _ _
  | cons k l ih =>
    have h := cost_bind (P.cost_chain t k (P.codec.len k - 1 - P.codec.digit I k)
      (P.codec.digit I k) (decodeWord bits k)) (fun x => ih (Function.update t k.val x))
    simpa only [reconFrom,List.map_cons,List.sum_cons,Nat.mul_add] using h

theorem chainOrder_sum (I : Index) :
    (chainOrder.map (P.codec.digit I)).sum = ∑ k, P.codec.digit I k := by
  rw [(chainOrder_permutation.map (P.codec.digit I)).sum_eq]
  change (List.ofFn (P.codec.digit I)).sum = _
  exact List.sum_ofFn

theorem cost_rootFrom (t : Tops) (l : List (Fin 3)) (st : BitVec 256) :
    CostAtMost (P.rootFrom t l st) (2*l.length) := by
  induction l generalizing st with
  | nil => exact cost_pure _ _
  | cons r l ih =>
    have h := cost_bind (cost_hash (P.rootInput t r st)) (fun v => ih v)
    simpa only [rootFrom,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm] using h

theorem cost_root (t : Tops) : CostAtMost (P.root t) 6 :=
  cost_map (P.cost_rootFrom t [0,1,2] 0) _

theorem cost_evalLocations (seeds : Fin 42 → Word) (l : List (Loc P)) (y : Tbl P) :
    CostAtMost (P.evalLocations seeds l y) (2*l.length) := by
  induction l generalizing y with
  | nil => exact cost_pure _ _
  | cons a l ih =>
    have h := cost_bind (cost_hash (Record.input (seeds,y) a))
      (fun v => ih (Function.update y a v))
    simpa only [evalLocations,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm] using h

theorem cost_keygen : CostAtMost P.keygen (2 * P.locationOrder.length) := by
  unfold keygen
  have h0 := cost_tabulate (fun _ => 0) (fun _ : Fin 42 => sampleBits 128) (fun _ => cost_sample 128)
  have h := cost_bind h0 (fun seeds => cost_bind (P.cost_evalLocations seeds P.locationOrder (fun _ => 0))
    (fun y => cost_pure (Record.pk (seeds,y),Record.sk (seeds,y)) 0))
  simpa only [Finset.sum_const_zero,Nat.zero_add,Nat.add_zero] using h

theorem cost_verify (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (P.verify pk m bits) (8 + 2 * P.codec.layer) := by
  unfold verify
  split
  · exact cost_pure _ _
  · refine CostAtMost.mono (b := 2 + (2 * P.codec.layer + 6)) ?_ (by omega)
    refine cost_bind (P.codec.cost_index m (decodeNonce bits) pk) (fun I => ?_)
    refine cost_ite _ (fun _ => cost_pure _ _) (fun hI' => ?_)
    have hI : P.codec.Accepted I := not_not.mp hI'
    have hc := P.cost_reconFrom I bits chainOrder (fun _ => 0)
    rw [P.chainOrder_sum I,hI] at hc
    exact cost_bind hc (fun tops => cost_bind (P.cost_root tops) (fun _ => cost_pure _ 0))

open Layer.Params in
theorem deterministic_chain (t : Tops) (k : Fin 42) (j n : ℕ) (x : Word) :
    Deterministic (P.chain t k j n x) := by
  induction n generalizing j x with
  | zero => exact deterministic_pure _
  | succ n ih =>
    exact deterministic_bind (deterministic_map (deterministic_hash _) _) (fun y => ih (j+1) y)

open Layer.Params in
theorem deterministic_reconFrom (I : Index) (bits : List Bool) (l : List (Fin 42)) (t : Tops) :
    Deterministic (P.reconFrom I bits l t) := by
  induction l generalizing t with
  | nil => exact deterministic_pure _
  | cons k l ih =>
    exact deterministic_bind (P.deterministic_chain t k _ _ _) (fun x => ih (Function.update t k.val x))

open Layer.Params in
theorem deterministic_rootFrom (t : Tops) (l : List (Fin 3)) (st : BitVec 256) :
    Deterministic (P.rootFrom t l st) := by
  induction l generalizing st with
  | nil => exact deterministic_pure _
  | cons r l ih => exact deterministic_bind (deterministic_hash _) (fun v => ih v)

open Layer.Params in
theorem verifyDeterministic : P.scheme.VerifyDeterministic := by
  intro pk m bits
  change Deterministic (P.verify pk m bits)
  unfold verify
  refine deterministic_ite _ (fun _ => deterministic_pure _) (fun _ => ?_)
  refine deterministic_bind (deterministic_map (deterministic_hash _) _) (fun I => ?_)
  refine deterministic_ite _ (fun _ => deterministic_pure _) (fun _ => ?_)
  exact deterministic_bind (P.deterministic_reconFrom I bits chainOrder _)
    (fun tops => deterministic_bind (deterministic_map (P.deterministic_rootFrom tops _ _) _)
      (fun _ => deterministic_pure _))

theorem verify_of_length_ne (pk : PublicKey) (m : Message) (bits : List Bool)
    (h : bits.length ≠ sigBits) : P.verify pk m bits = pure false := by
  simp only [verify,if_pos h]

theorem rejectsOversized : P.scheme.RejectsOversized maxSignatureBits := by
  intro pk m σ h
  change true ∉ support (P.verify pk m σ)
  rw [P.verify_of_length_ne pk m σ (by unfold sigBits maxSignatureBits at *; omega)]
  simp

set_option maxHeartbeats 800000 in
theorem admissible (hP : P.Hyp) (hl : P.locationOrder.Pairwise Earlier)
    {S : Tier.Sched} (hS : S.Valid) (hT : P.codec.TierHyp S)
    (hk : 2 * P.locationOrder.length ≤ keygenBudget)
    (hv : 8 + 2 * P.codec.layer ≤ verifyBudget) : P.scheme.Admissible where
  correct := P.correct hP.codec hl
  verifyDeterministic := P.verifyDeterministic
  signingFailure := P.signingFailure hP hl hS hT
  signatureSize := by
    intro sk m σ hσ
    exact P.codec.signatureSize sk m σ hσ
  rejectsOversized := P.rejectsOversized
  keygenCost := CostAtMost.mono P.cost_keygen hk
  signCost := fun sk m => P.codec.cost_sign sk m
  verifyCost := fun pk m σ => CostAtMost.mono (P.cost_verify pk m σ) hv

end Params

theorem concrete_keygenCost : CostAtMost params.keygen 1256 := by
  have h := params.cost_keygen
  rwa [concrete_location_count] at h

theorem concrete_verifyCost (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (params.verify pk m bits) 180 := params.cost_verify pk m bits

theorem concrete_admissible : params.scheme.Admissible :=
  params.admissible params_hyp concrete_ordered FusionNumeric.schedule_valid FusionCodec.tierHyp
    (by rw [concrete_location_count]; decide) (by decide)

end
end OptimalOTS.LeanIsaBaseline.Layer.Fusion
