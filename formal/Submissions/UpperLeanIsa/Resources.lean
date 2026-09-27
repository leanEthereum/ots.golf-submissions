import Submissions.UpperLeanIsa.Correctness

/-!
# Pathwise resource bounds of a layer scheme

Every oracle query is one 896-bit leanISA `BLAKE2S` input, i.e. two compressions. On every
oracle path:

* key generation costs at most `2 · Σ (len k - 1) + 18` (the chain steps and the 9 root calls);
* signing costs at most `2 · trials = 2 ^ 20` (one index query per trial);
* verification costs at most `20 + 2 · layer` (the index query, the remaining steps of an
  accepted index, which sum to the layer, and the root).

These are algorithm bounds, not leanISA cycle scores.
-/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

attribute [local irreducible] trials

theorem cost_pure {α : Type} (x : α) (b : ℕ) :
    CostAtMost (pure x : OracleComp Spec α) b := by trivial

theorem cost_bind {α β : Type} {oa : OracleComp Spec α}
    {ob : α → OracleComp Spec β} {a b : ℕ}
    (ha : CostAtMost oa a) (hb : ∀ x, CostAtMost (ob x) b) :
    CostAtMost (oa >>= ob) (a + b) :=
  isQueryBound_bind (· + ·)
    (fun _ _ _ _ h => ⟨le_add_left h, le_add_right h⟩)
    (fun _ _ _ _ h => ⟨by omega, by omega⟩) ha hb

theorem cost_map {α β : Type} {oa : OracleComp Spec α} {b : ℕ}
    (h : CostAtMost oa b) (f : α → β) : CostAtMost (f <$> oa) b :=
  (isQueryBound_map_iff _ _ _ _ _).2 h

theorem cost_hash (x : BitVec 896) : CostAtMost (hash x) 2 := by
  unfold CostAtMost hash
  rw [isQueryBound_query_iff]
  norm_num [queryCost, blockCost, blockBits]

theorem cost_liftM {α : Type} (oa : ProbComp α) : CostAtMost (liftM oa : OracleComp Spec α) 0 := by
  change CostAtMost (liftComp oa Spec) 0
  induction oa using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t k ih =>
    rw [liftComp_bind]
    have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
        (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
      simp [liftComp]; rfl
    rw [hq]
    unfold CostAtMost at ih ⊢
    rw [isQueryBound_query_bind_iff]
    exact ⟨by simp [queryCost], fun u => by simpa [queryCost] using ih u⟩

theorem cost_sample (n : ℕ) : CostAtMost (sampleBits n) 0 := cost_liftM _

theorem cost_tabulate {α : Type} {n : ℕ} (b : Fin n → ℕ) (f : Fin n → OracleComp Spec α)
    (h : ∀ i, CostAtMost (f i) (b i)) : CostAtMost (tabulate f) (∑ i, b i) := by
  induction n with
  | zero => exact cost_pure _ _
  | succ n ih =>
    simp only [tabulate]
    have hb := cost_bind (h 0) (fun x =>
      cost_map (ih (fun i => b i.succ) (fun i => f i.succ) (fun i => h i.succ))
        (fun (xs : Fin n → α) (i : Fin (n + 1)) =>
          Fin.cases (motive := fun _ => α) x xs i))
    rw [Fin.sum_univ_succ]
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using hb

theorem cost_ite {α : Type} (p : Prop) [Decidable p] {a c : OracleComp Spec α} {b : ℕ}
    (ha : p → CostAtMost a b) (hc : ¬ p → CostAtMost c b) :
    CostAtMost (if p then a else c) b := by
  split
  · exact ha ‹_›
  · exact hc ‹_›

attribute [local irreducible] CostAtMost

namespace Params

variable (P : Params)

theorem cost_index (m : Message) (η : Nonce) (pk : PublicKey) : CostAtMost (P.index m η pk) 2 :=
  cost_map (cost_hash _) _

theorem cost_signLoop (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce) (β : Option (Nonce × Index)),
      CostAtMost (P.signLoop sk m k tried β) (2 * k) := by
  intro k
  induction k with
  | zero => intro tried β; exact cost_pure _ _
  | succ k ih =>
    intro tried β
    rw [signLoop]
    dsimp only
    split
    · refine CostAtMost.mono (b := 0 + (2 + 2 * k)) ?_ (by omega)
      refine cost_bind (cost_liftM _) (fun j => ?_)
      exact cost_bind (P.cost_index m _ sk.pk) (fun I => ih _ _)
    · exact cost_pure _ _

/-- Signing costs at most `2 · trials = 2 ^ 20` on every path. -/
theorem cost_sign (sk : SecretKey) (m : Message) : CostAtMost (P.sign sk m) (2 ^ 20) := by
  rw [sign_eq]
  have h := P.cost_signLoop sk m trials ∅ none
  have ht : 2 * trials = 2 ^ 20 := by unfold trials; norm_num
  rwa [ht] at h

end Params

end OptimalOTS.LeanIsaBaseline.Layer
