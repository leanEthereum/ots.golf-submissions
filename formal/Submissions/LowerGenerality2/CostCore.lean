import Submissions.LowerGenerality2.Semantics

/-!
# Pathwise compression costs

Cost bounds for sampling, graph evaluation, signing and verification. These lemmas account
for every oracle call, including repeated inputs. `PatternAttack.cost_experiment` combines
these bounds for the full forgery experiment.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


/-! ## Generic rules for `CostAtMost` -/

section Generic

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable {α β : Type}

theorem CostAtMost.mono {oa : OracleComp Spec α} {b b' : ℕ} (h : CostAtMost oa b)
    (hb : b ≤ b') : CostAtMost oa b' := by
  induction oa using OracleComp.inductionOn generalizing b b' with
  | pure _ => trivial
  | query_bind t mx ih =>
      unfold CostAtMost at h ⊢
      rw [isQueryBound_query_bind_iff] at h ⊢
      exact ⟨le_trans h.1 hb, fun u => ih u (h.2 u) (by omega)⟩

theorem costAtMost_pure (x : α) (b : ℕ) : CostAtMost (pure x : OracleComp Spec α) b :=
  trivial

theorem CostAtMost.bind {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    {b₁ b₂ : ℕ} (h₁ : CostAtMost oa b₁) (h₂ : ∀ x, CostAtMost (ob x) b₂) :
    CostAtMost (oa >>= ob) (b₁ + b₂) :=
  isQueryBound_bind (· + ·)
    (fun _ _ _ _ h => ⟨le_add_left h, le_add_right h⟩)
    (fun _ _ _ _ h => ⟨by omega, by omega⟩) h₁ h₂

theorem costAtMost_map_iff (oa : OracleComp Spec α) (f : α → β) (b : ℕ) :
    CostAtMost (f <$> oa) b ↔ CostAtMost oa b :=
  isQueryBound_map_iff _ _ _ _ _

theorem CostAtMost.map {oa : OracleComp Spec α} {b : ℕ} (h : CostAtMost oa b)
    (f : α → β) : CostAtMost (f <$> oa) b :=
  (costAtMost_map_iff oa f b).2 h

theorem costAtMost_liftM_probComp (mx : ProbComp α) (b : ℕ) :
    CostAtMost (liftM mx : OracleComp Spec α) b := by
  change CostAtMost (liftComp mx Spec) b
  induction mx using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [liftComp_bind]
      have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
          (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
        simp [liftComp]; rfl
      rw [hq]
      unfold CostAtMost at ih ⊢
      rw [isQueryBound_query_bind_iff]
      exact ⟨by simp [queryCost], fun u => by simpa [queryCost] using ih u⟩

theorem costAtMost_hash {k : ℕ} (u : BitVec k) {b : ℕ} (hb : blockCost k ≤ b) :
    CostAtMost (hash u) b := by
  unfold CostAtMost hash
  rw [isQueryBound_query_iff]
  exact hb


theorem CostAtMost.bind_le {oa : OracleComp Spec α} {ob : α → OracleComp Spec β}
    {b₁ b₂ b : ℕ} (h₁ : CostAtMost oa b₁) (h₂ : ∀ x, CostAtMost (ob x) b₂)
    (h : b₁ + b₂ ≤ b) : CostAtMost (oa >>= ob) b :=
  (h₁.bind h₂).mono h

theorem costAtMost_foldlM {γ δ : Type} (f : γ → δ → OracleComp Spec γ) (c : δ → ℕ)
    (hf : ∀ x a, CostAtMost (f x a) (c a)) :
    ∀ (l : List δ) (init : γ), CostAtMost (l.foldlM f init) (l.map c).sum
  | [], _ => costAtMost_pure _ _
  | a :: l, init => by
      rw [List.foldlM_cons, List.map_cons, List.sum_cons]
      exact (hf init a).bind fun y => costAtMost_foldlM f c hf l y

end Generic

/-! ## Graph computations -/

namespace Dag.Graph

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

variable (G : Graph)

theorem costAtMost_evalNode (x : G.Assignment) (v : Fin G.size)
    (s : OracleComp Spec (BitVec (G.len v))) (hs : CostAtMost s 0) :
    CostAtMost (G.evalNode x v s) (G.nodeCost v) := by
  unfold Graph.evalNode Graph.nodeCost
  cases G.kind v with
  | source => exact hs
  | det => exact costAtMost_pure _ _
  | hash p _ h => exact (costAtMost_hash _ le_rfl).map _

theorem costAtMost_sampleAssignment : CostAtMost G.sampleAssignment 0 := by
  unfold Graph.sampleAssignment
  have := costAtMost_foldlM
    (fun (z : G.Assignment) v => Function.update z v <$> sampleBits (G.len v)) (fun _ => 0)
    (fun _ _ => (costAtMost_liftM_probComp _ _).map _) (List.finRange G.size) (fun _ => 0)
  simpa using this

theorem costAtMost_evaluate (z : G.Assignment) : CostAtMost (G.evaluate z) G.keygenCost := by
  unfold Graph.evaluate
  have := costAtMost_foldlM
    (fun (x : G.Assignment) v => Function.update x v <$> G.evalNode x v (pure (z v)))
    G.nodeCost (fun x v => (G.costAtMost_evalNode x v _ (costAtMost_pure _ _)).map _)
    (List.finRange G.size) (fun _ => 0)
  rwa [Graph.keygenCost, Fin.sum_univ_def]

theorem costAtMost_keygen : CostAtMost G.keygen G.keygenCost :=
  G.costAtMost_sampleAssignment.bind_le (fun z => G.costAtMost_evaluate z) (by simp)

theorem costAtMost_reconstruct (A : Finset (Fin G.size)) (given : G.Assignment) :
    CostAtMost (G.reconstruct A given) (G.reconstructCost A) := by
  unfold Graph.reconstruct
  refine CostAtMost.mono (costAtMost_foldlM _
    (fun v => if v ∈ A then 0 else if G.Visited A v then G.nodeCost v else 0)
    (fun x v => ?_) (List.finRange G.size) (fun _ => 0)) (le_of_eq ?_)
  · split_ifs
    · exact costAtMost_pure _ _
    · exact (G.costAtMost_evalNode x v _ (costAtMost_pure _ _)).map _
    · exact costAtMost_pure _ _
  · rw [← Fin.sum_univ_def, Graph.reconstructCost, Graph.evaluated, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h₁ : v ∈ A <;> by_cases h₂ : G.Visited A v <;> simp [h₁, h₂]

end Dag.Graph

/-! ## Signing and verification -/

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem costAtMost_index (hidx : blockCost (msgBits + nonceBits) = 1)
    (m : Message) (η : Nonce) : CostAtMost (index m η) 1 :=
  (costAtMost_hash _ hidx.le).map _

namespace Dag.Scheme

variable (S : Scheme)

theorem costAtMost_keygen : CostAtMost S.keygen keygenBudget :=
  (S.graph.costAtMost_keygen.bind_le (fun _ => costAtMost_pure _ 0) (by simp)).mono S.keygen_le

theorem costAtMost_signLoop (hidx : blockCost (msgBits + nonceBits) = 1)
    (x : S.graph.Assignment) (m : Message) :
    ∀ k tried, CostAtMost (S.signLoop x m k tried) k
  | 0, _ => costAtMost_pure _ _
  | k + 1, tried => by
      rw [Scheme.signLoop]
      split_ifs
      · refine (costAtMost_liftM_probComp _ 0).bind_le (b₂ := k + 1) (fun j => ?_) (by simp)
        refine (costAtMost_index hidx _ _).bind_le (b₂ := k) (fun i => ?_) (by omega)
        split_ifs with hi
        · exact costAtMost_pure _ _
        · exact costAtMost_signLoop hidx x m k _
      · exact costAtMost_pure _ _

theorem costAtMost_sign (hidx : blockCost (msgBits + nonceBits) = 1)
    (x : S.graph.Assignment) (m : Message) : CostAtMost (S.sign x m) trials :=
  S.costAtMost_signLoop hidx x m _ _

theorem costAtMost_verify (hidx : blockCost (msgBits + nonceBits) = 1) {v : ℕ}
    (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) (pk : PublicKey) (m : Message)
    (σ : Signature) : CostAtMost (S.verify pk m σ) (1 + v) := by
  unfold Scheme.verify
  refine (costAtMost_index hidx _ _).bind_le (b₂ := v) (fun i => ?_) le_rfl
  split_ifs with hi
  · dsimp only
    split_ifs
    · exact ((S.graph.costAtMost_reconstruct (S.sets ⟨i, hi⟩) _).mono (hv _)).bind_le
        (fun _ => costAtMost_pure _ 0) (by simp)
    · exact costAtMost_pure _ _
  · exact costAtMost_pure _ _

end Dag.Scheme

end OptimalOTS
