import Submissions.UpperLeanIsa.Correctness

/-!
# Pathwise resource bounds of a layer scheme

Every oracle query is one 896-bit leanISA `BLAKE2S` input, i.e. two compressions. On every
oracle path:

* key generation costs at most `2 · Σ (len k - 1) + 16` (the chain steps and the 8 root calls);
* signing costs at most `2 · trials = 2 ^ 20` (one index query per trial);
* verification costs at most `18 + 2 · layer` (the index query, the remaining steps of an
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

theorem cost_chainStep (k : Fin numChains) (j : ℕ) (x : Word) : CostAtMost (P.chainStep k j x) 2 :=
  cost_map (cost_hash _) _

theorem cost_chain (k : Fin numChains) : ∀ (j n : ℕ) (x : Word),
    CostAtMost (P.chain k j n x) (2 * n) := by
  intro j n
  induction n generalizing j with
  | zero => intro x; exact cost_pure _ _
  | succ n ih =>
    intro x
    have h := cost_bind (P.cost_chainStep k j x) (fun y => ih (j + 1) y)
    simpa only [chain, Nat.mul_succ, Nat.add_comm] using h

theorem cost_chainList (k : Fin numChains) : ∀ (j n : ℕ) (x : Word),
    CostAtMost (P.chainList k j n x) (2 * n) := by
  intro j n
  induction n generalizing j with
  | zero => intro x; exact cost_pure _ _
  | succ n ih =>
    intro x
    have h := cost_bind (P.cost_chainStep k j x)
      (fun y => cost_bind (ih (j + 1) y) (fun ys => cost_pure (x :: ys) 0))
    simpa only [chainList, Nat.mul_succ, Nat.add_comm, Nat.add_zero, Nat.zero_add] using h

theorem cost_index (m : Message) (η : Nonce) (pk : PublicKey) : CostAtMost (P.index m η pk) 2 :=
  cost_map (cost_hash _) _

theorem cost_rootFrom (t : Fin numChains → Word) : ∀ (r n : ℕ) (st : BitVec 256),
    CostAtMost (P.rootFrom t r n st) (2 * n) := by
  intro r n
  induction n generalizing r with
  | zero => intro st; exact cost_pure _ _
  | succ n ih =>
    intro st
    have h := cost_bind (cost_hash (P.rootInput t r st)) (fun st' => ih (r + 1) st')
    simpa only [rootFrom, Nat.mul_succ, Nat.add_comm] using h

theorem cost_root (t : Fin numChains → Word) : CostAtMost (P.root t) 16 :=
  cost_map (P.cost_rootFrom t 0 8 _) _

/-- Key generation costs `2 · Σ (len k - 1) + 16` on every path. -/
theorem cost_keygen : CostAtMost P.keygen (2 * (∑ k, (P.len k - 1)) + 16) := by
  unfold keygen
  have h1 := cost_tabulate (fun _ => 0) (fun _ : Fin numChains => sampleBits 128)
    (fun _ => cost_sample 128)
  have h2 (seeds : Fin numChains → Word) := cost_tabulate (fun k => 2 * (P.len k - 1))
    (fun k => P.chainList k 0 (P.len k - 1) (seeds k)) (fun k => P.cost_chainList k _ _ _)
  have h := cost_bind h1 (fun seeds => cost_bind (h2 seeds) (fun tables =>
    cost_bind (P.cost_root (fun k => (tables k).getD (P.len k - 1) 0))
      (fun pk => cost_pure (pk, (⟨tables, pk⟩ : SecretKey)) 0)))
  simp only [Finset.sum_const_zero, Nat.zero_add, Nat.add_zero, ← Finset.mul_sum] at h
  exact h

theorem cost_signLoop (sk : SecretKey) (m : Message) :
    ∀ (k : ℕ) (tried : Finset Nonce), CostAtMost (P.signLoop sk m k tried) (2 * k) := by
  intro k
  induction k with
  | zero => intro tried; exact cost_pure _ _
  | succ k ih =>
    intro tried
    rw [signLoop]
    dsimp only
    split
    · refine CostAtMost.mono (b := 0 + (2 + 2 * k)) ?_ (by omega)
      refine cost_bind (cost_liftM _) (fun j => ?_)
      refine cost_bind (P.cost_index m _ sk.pk) (fun I => ?_)
      exact cost_ite _ (fun _ => cost_pure _ _) (fun _ => ih _)
    · exact cost_pure _ _

/-- Signing costs at most `2 · trials = 2 ^ 20` on every path. -/
theorem cost_sign (sk : SecretKey) (m : Message) : CostAtMost (P.sign sk m) (2 ^ 20) := by
  rw [sign_eq]
  have h := P.cost_signLoop sk m trials ∅
  have ht : 2 * trials = 2 ^ 20 := by unfold trials; norm_num
  rwa [ht] at h

/-- Verification costs at most `18 + 2 · layer` on every path, including rejects. -/
theorem cost_verify (pk : PublicKey) (m : Message) (bits : List Bool) :
    CostAtMost (P.verify pk m bits) (18 + 2 * P.layer) := by
  unfold verify
  split
  · exact cost_pure _ _
  · refine CostAtMost.mono (b := 2 + (2 * P.layer + 16)) ?_ (by omega)
    refine cost_bind (P.cost_index m (decodeNonce bits) pk) (fun I => ?_)
    refine cost_ite _ (fun _ => cost_pure _ _) (fun hI' => ?_)
    · have hI : P.Accepted I := not_not.mp hI'
      have hsum : ∑ k : Fin numChains, 2 * P.digit I k = 2 * P.layer := by
        rw [← Finset.mul_sum]
        exact congrArg (2 * ·) hI
      have ht := cost_tabulate (fun k => 2 * P.digit I k) _
        (fun k => P.cost_chain k (P.len k - 1 - P.digit I k) (P.digit I k) (decodeWord bits k))
      rw [hsum] at ht
      exact cost_bind ht (fun tops => cost_bind (P.cost_root tops) (fun r => cost_pure _ 0))

end Params

end OptimalOTS.LeanIsaBaseline.Layer
