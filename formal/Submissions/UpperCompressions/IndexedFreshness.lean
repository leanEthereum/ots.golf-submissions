import Submissions.UpperCompressions.IndexedAvailability

/-!
# Index-query freshness after graph key generation

A graph whose hash inputs avoid one length preserves all cache entries of that
length. This argument uses actual oracle executions, needs no tagging or security
record representation, and allows repeated graph hash inputs.

At the index-input length it proves the signing-failure guarantee for every
message chosen as a function of the generated public key.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.IndexedFreshness

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits
  maxSignatureBits keygenBudget signBudget Dag.nonceBits Dag.idxBits Dag.numCuts Dag.trials

/-- Every supported lazy-oracle run leaves cache entries of length `L` unchanged. -/
def PreservesLength {α : Type} (L : ℕ) (oa : OracleComp Spec α) : Prop :=
  ∀ (c : Cache) (p : α × Cache), p ∈ support (run oa c) →
    ∀ q : Query, q.1 = L → p.2 q = c q

namespace PreservesLength

variable {L : ℕ} {α β : Type}

theorem of_pure (x : α) : PreservesLength L (pure x : OracleComp Spec α) := by
  intro c p hp q hq
  rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rfl

theorem bind {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    (h₁ : PreservesLength L oa) (h₂ : ∀ x, PreservesLength L (ob x)) :
    PreservesLength L (oa >>= ob) := by
  intro c p hp q hq
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨x, d⟩, hx, hp⟩ := hp
  exact (h₂ x d p hp q hq).trans (h₁ c (x, d) hx q hq)

theorem map {oa : OracleComp Spec α} (h : PreservesLength L oa) (f : α → β) :
    PreservesLength L (f <$> oa) := by
  intro c p hp q hq
  rw [run_map, support_map, Set.mem_image] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  exact h c p' hp' q hq

theorem of_liftM (pc : ProbComp α) :
    PreservesLength L (liftM pc : OracleComp Spec α) := by
  intro c p hp q hq
  rw [run_liftM, support_map, Set.mem_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  rfl

theorem hash {k : ℕ} (u : BitVec k) (hk : k ≠ L) : PreservesLength L (OptimalOTS.hash u) := by
  intro c p hp q hq
  have hne : q ≠ (⟨k, u⟩ : Query) := by
    intro heq
    exact hk ((congrArg Sigma.fst heq).symm.trans hq)
  unfold OptimalOTS.hash run at hp
  rw [simulateQ_spec_query] at hp
  rcases hc : c ⟨k, u⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨w, _, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact QueryCache.cacheQuery_of_ne _ _ hne
  · rw [oracleImpl_run_inr_some hc, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl

theorem foldlM {γ δ : Type} (f : γ → δ → OracleComp Spec γ)
    (hf : ∀ x a, PreservesLength L (f x a)) :
    ∀ (l : List δ) (init : γ), PreservesLength L (l.foldlM f init)
  | [], _ => of_pure _
  | a :: l, init => by
      rw [List.foldlM_cons]
      exact bind (hf init a) fun y => foldlM f hf l y

end PreservesLength

/-- Every hash node has an input length distinct from `L`. -/
def HashInputsAvoid (G : Dag.Graph) (L : ℕ) : Prop :=
  ∀ v, match G.kind v with
    | .hash p _ _ => G.len p ≠ L
    | _ => True

theorem evalNode_preservesLength (G : Dag.Graph) {L : ℕ} (hG : HashInputsAvoid G L)
    (x : G.Assignment) (v : Fin G.size) (s : OracleComp Spec (BitVec (G.len v)))
    (hs : PreservesLength L s) : PreservesLength L (G.evalNode x v s) := by
  have hv := hG v
  unfold Dag.Graph.evalNode
  cases hk : G.kind v with
  | source => exact hs
  | det => exact PreservesLength.of_pure _
  | hash p _ h =>
    exact PreservesLength.map (PreservesLength.hash _ (by simpa only [hk] using hv)) _

theorem sampleAssignment_preservesLength (G : Dag.Graph) (L : ℕ) :
    PreservesLength L G.sampleAssignment := by
  unfold Dag.Graph.sampleAssignment
  refine PreservesLength.foldlM _ (fun z v => ?_) (List.finRange G.size) (fun _ => 0)
  exact PreservesLength.map (PreservesLength.of_liftM _) _

theorem evaluate_preservesLength (G : Dag.Graph) {L : ℕ} (hG : HashInputsAvoid G L)
    (z : G.Assignment) : PreservesLength L (G.evaluate z) := by
  unfold Dag.Graph.evaluate
  refine PreservesLength.foldlM _ (fun x v => ?_) (List.finRange G.size) (fun _ => 0)
  exact PreservesLength.map
    (evalNode_preservesLength G hG x v _ (PreservesLength.of_pure _)) _

theorem graph_keygen_preservesLength (G : Dag.Graph) {L : ℕ} (hG : HashInputsAvoid G L) :
    PreservesLength L G.keygen :=
  PreservesLength.bind (sampleAssignment_preservesLength G L)
    (fun z => evaluate_preservesLength G hG z)

theorem keygen_preservesLength {M L : ℕ} (S : IndexedDag.Scheme M)
    (hG : HashInputsAvoid S.graph L) : PreservesLength L S.keygen :=
  PreservesLength.bind (graph_keygen_preservesLength S.graph hG)
    (fun _ => PreservesLength.of_pure _)

/-- Starting from an empty cache, every query at an avoided length remains fresh. -/
theorem keygen_fresh {M L : ℕ} (S : IndexedDag.Scheme M)
    (hG : HashInputsAvoid S.graph L) (p : (PublicKey × S.graph.Assignment) × Cache)
    (hp : p ∈ support (run S.keygen ∅)) (q : Query) (hq : q.1 = L) : p.2 q = none := by
  simpa using keygen_preservesLength S hG ∅ p hp q hq

/-- `probTrue` as the expectation of a Boolean indicator under the lazy oracle. -/
theorem probTrue_eq_E_run (oa : OracleComp Spec Bool) :
    probTrue oa = E (run oa ∅) (fun p => if p.1 = true then 1 else 0) := by
  unfold probTrue
  rw [run'_eq, probOutput_map_eq_tsum_ite, E, expectedValue_def]
  refine tsum_congr fun x => ?_
  rcases x with ⟨b, c⟩
  cases b <;> simp

/-- Availability averaged over key generation, including public-key-dependent messages. -/
theorem signingFailure (S : IndexedDag.Scheme IndexedAnalysis.numCuts)
    (hG : HashInputsAvoid S.graph (msgBits + Dag.nonceBits)) :
    S.toAlgorithm.SigningFailureAtMost (1 / 2 ^ 128 : ℝ≥0∞) := by
  intro message
  change probTrue (do
    let kg ← S.keygen
    let σ ← S.sign kg.2 (message kg.1)
    pure σ.isNone) ≤ _
  rw [probTrue_eq_E_run, run_bind, E_bind]
  simp only [run_bind, E_bind, run_pure, E_pure]
  calc
    _ ≤ E (run S.keygen ∅) (fun _ => (1 / 2 ^ 128 : ℝ≥0∞)) := by
      refine expectedValue_mono_of_support fun p hp => ?_
      apply IndexedAnalysis.Availability.sign_failure_le S p.1.2 (message p.1.1) p.2
      intro η
      exact keygen_fresh S hG p hp (IndexedAnalysis.encQuery (message p.1.1 ++ η)) rfl
    _ ≤ _ := E_const_le _ _

end OptimalOTS.IndexedFreshness
