import OptimalOTS.OracleAlgorithm
import Submissions.UpperRiscv.Cache

/-!
# Safe postponement of rejection

`Prunes early staged` says that `early` is obtained by deleting oracle-query suffixes whose
answer is already fixed. Unlike equality of oracle computations, this relation permits the
machine to perform a few chain hashes before noticing an invalid dispatch digit.

The two facts needed for security are proved separately: final-result probabilities agree
under the shared lazy random oracle, and every pathwise budget for the staged program is also
a budget for the early program. In particular the security reduction does not increase `B`.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.RejectAdapter

variable {α β γ : Type}

/-- Only terminal, constant-answer suffixes may be removed. -/
inductive Prunes : OracleComp Spec α → OracleComp Spec α → Prop
  | stop {β : Type} (head : OracleComp Spec β) (x : α) :
      Prunes (pure x) (head >>= fun _ => pure x)
  | query (t : Spec.Domain) (left right : Spec.Range t → OracleComp Spec α)
      (next : ∀ u, Prunes (left u) (right u)) :
      Prunes (liftM (Spec.query t) >>= left) (liftM (Spec.query t) >>= right)

namespace Prunes

theorem refl (oa : OracleComp Spec α) : Prunes oa oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa only [pure_bind] using Prunes.stop (pure ()) x
  | query_bind t k ih => exact Prunes.query t k k ih

/-- A fixed-answer computation is a deletable terminal suffix. -/
theorem of_support (oa : OracleComp Spec α) (x : α)
    (h : ∀ y ∈ support oa, y = x) : Prunes (pure x) oa := by
  have he : (oa >>= fun _ => pure x) = oa := by
    conv_rhs => rw [← bind_pure oa]
    apply bind_congr_of_forall_mem_support
    intro y hy
    rw [h y hy]
  rw [← he]
  exact Prunes.stop oa x

/-- The unmodified prefix may include all key generation, signing and adversary queries. -/
theorem bind_left (head : OracleComp Spec β)
    (left right : β → OracleComp Spec α) (h : ∀ y, Prunes (left y) (right y)) :
    Prunes (head >>= left) (head >>= right) := by
  induction head using OracleComp.inductionOn with
  | pure x => simpa only [pure_bind] using h x
  | query_bind t k ih =>
    simp only [bind_assoc]
    exact Prunes.query t _ _ ih

/-- Deterministic postprocessing of the final answer preserves pruning. -/
theorem map {left right : OracleComp Spec α} (h : Prunes left right) (f : α → β) :
    Prunes (f <$> left) (f <$> right) := by
  induction h with
  | stop head x =>
    simpa only [map_pure, map_bind] using Prunes.stop head (f x)
  | query t left right _ ih =>
    simpa only [map_bind] using Prunes.query t _ _ ih

/-- Every budget of the staged program bounds the pruned program, at exactly the same `B`. -/
theorem cost {left right : OracleComp Spec α} (h : Prunes left right) :
    ∀ B, CostAtMost right B → CostAtMost left B := by
  induction h with
  | stop head x => intro B _; trivial
  | query t left right _ ih =>
    intro B hB
    unfold CostAtMost at hB ⊢
    rw [isQueryBound_query_bind_iff] at hB ⊢
    exact ⟨hB.1, fun u => ih u _ (hB.2 u)⟩

/-- No new output is introduced by postponing a terminal decision. -/
theorem support_subset {left right : OracleComp Spec α} (h : Prunes left right) :
    support right ⊆ support left := by
  induction h with
  | stop head x =>
    intro y hy
    rw [support_bind] at hy
    simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hy ⊢
    obtain ⟨_, _, rfl⟩ := hy
    rfl
  | query t left right _ ih =>
    intro y hy
    simp only [support_bind, Set.mem_iUnion] at hy ⊢
    obtain ⟨u, hu, hy⟩ := hy
    exact ⟨u, hu, ih u hy⟩

/-- Result probabilities agree from every initial cache. Final caches need not agree. -/
theorem probOutput {left right : OracleComp Spec α} (h : Prunes left right) :
    ∀ (c : Cache) (x : α),
      Pr[= x | Prod.fst <$> run left c] = Pr[= x | Prod.fst <$> run right c] := by
  classical
  induction h with
  | stop head x =>
    intro c y
    simp only [run_bind, run_pure, map_bind, map_pure, probOutput_bind_const,
      probFailure_eq_zero, tsub_zero, one_mul]
  | query t left right _ ih =>
    intro c x
    rw [run_query_bind, run_query_bind, map_bind, map_bind]
    simp only [probOutput_bind_eq_tsum]
    apply tsum_congr
    intro p
    rw [ih p.1 p.2 x]

theorem probTrue {left right : OracleComp Spec Bool} (h : Prunes left right) :
    OptimalOTS.probTrue left = OptimalOTS.probTrue right := by
  unfold OptimalOTS.probTrue
  rw [run'_eq, run'_eq]
  exact h.probOutput ∅ true

end Prunes

/-- Replace only the verification algorithm, keeping key generation and signing unchanged. -/
def scheme (S : OracleAlgorithm.Scheme)
    (verify : PublicKey → Message → List Bool → OracleComp Spec Bool) :
    OracleAlgorithm.Scheme := { S with verify := verify }

variable (S : OracleAlgorithm.Scheme)
  (verify : PublicKey → Message → List Bool → OracleComp Spec Bool)
  (prunes : ∀ pk m bits, Prunes (S.verify pk m bits) (verify pk m bits))

include prunes in
theorem experiment_prunes (A : OracleAlgorithm.Adversary) :
    Prunes (OracleAlgorithm.experiment S A)
      (OracleAlgorithm.experiment (scheme S verify) A) := by
  unfold OracleAlgorithm.experiment scheme
  apply Prunes.bind_left
  intro keys
  apply Prunes.bind_left
  intro chosen
  apply Prunes.bind_left
  intro signed
  apply Prunes.bind_left
  intro forged
  rcases forged with ⟨m, bits⟩
  simpa only [map_eq_pure_bind] using
    (prunes keys.1 m bits).map
      (fun ok => ok && decide (signed.map (fun s => (chosen.1, s)) ≠ some (m, bits)))

include prunes in
/-- Strong security transfers without changing the pathwise whole-experiment budget. -/
theorem secure (h : S.Secure) : (scheme S verify).Secure := by
  intro A B hB
  have hp := experiment_prunes S verify prunes A
  rw [← hp.probTrue]
  exact h A B (hp.cost B hB)

include prunes in
theorem correct (h : S.Correct) : (scheme S verify).Correct := by
  intro message
  rw [← h message]
  apply Eq.symm
  apply Prunes.probTrue
  apply Prunes.bind_left
  intro keys
  apply Prunes.bind_left
  intro signed
  cases signed with
  | none => exact Prunes.refl _
  | some bits =>
    simpa only [scheme, map_eq_pure_bind] using
      (prunes keys.1 (message keys.1) bits).map Bool.not

include prunes in
theorem rejectsOversized (n : ℕ) (h : S.RejectsOversized n) :
    (scheme S verify).RejectsOversized n := by
  intro pk m bits hlen accepted
  exact h pk m bits hlen ((prunes pk m bits).support_subset accepted)

include prunes in
/-- The changed verifier must still establish its own determinism and resource bound. -/
theorem admissible (h : S.Admissible)
    (det : ∀ pk m bits, Deterministic (verify pk m bits))
    (cost : ∀ pk m bits, CostAtMost (verify pk m bits) verifyBudget) :
    (scheme S verify).Admissible where
  correct := correct S verify prunes h.correct
  verifyDeterministic := det
  signingFailure := h.signingFailure
  signatureSize := h.signatureSize
  rejectsOversized := rejectsOversized S verify prunes _ h.rejectsOversized
  keygenCost := h.keygenCost
  signCost := h.signCost
  verifyCost := cost

/--
info: 'OptimalOTS.RejectAdapter.secure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms secure

end OptimalOTS.RejectAdapter
