import Submissions.UpperLeanIsa.Algorithms

/-! Pathwise resource bounds for the candidate algorithm. These bounds hold on raw,
uncached oracle paths as required by the contract. They are not a leanISA cycle claim. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleSpec

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

theorem cost_sample (n : ℕ) : CostAtMost (sampleBits n) 0 := by
  suffices h : ∀ {α : Type} (oa : ProbComp α),
      CostAtMost (liftM oa : OracleComp Spec α) 0 from h _
  intro α oa
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

theorem cost_tabulate {α : Type} (n b : ℕ) (f : Fin n → OracleComp Spec α)
    (h : ∀ i, CostAtMost (f i) b) : CostAtMost (tabulate f) (n * b) := by
  induction n with
  | zero => exact cost_pure _ _
  | succ n ih =>
    simp only [tabulate]
    have hb := cost_bind (h 0) (fun x =>
      cost_map (ih (fun i => f i.succ) (fun i => h i.succ))
        (fun (xs : Fin n → α) (i : Fin (n + 1)) =>
          Fin.cases (motive := fun _ => α) x xs i))
    simpa only [Nat.succ_mul, Nat.add_comm, map_eq_bind_pure_comp, Function.comp_def] using hb

theorem cost_chainStep (i j : ℕ) (x : Word) : CostAtMost (chainStep i j x) 2 :=
  cost_map (cost_hash _) _

theorem cost_chain (i j n : ℕ) (x : Word) : CostAtMost (chain i j n x) (2 * n) := by
  induction n generalizing j x with
  | zero => exact cost_pure _ _
  | succ n ih =>
    have h := cost_bind (cost_chainStep i j x) (fun y => ih (j + 1) y)
    simpa only [chain, Nat.mul_succ, Nat.add_comm] using h

theorem cost_rootFold (xs : List Word) (cv : BitVec 256) :
    CostAtMost (rootFold xs cv) (2 * xs.length) := by
  induction xs generalizing cv with
  | nil => exact cost_pure _ _
  | cons x xs ih =>
    have hquery : CostAtMost (absorb xs.length cv x) 2 := cost_hash _
    have h := cost_bind hquery (fun next => ih next)
    change CostAtMost (absorb xs.length cv x >>= fun next => rootFold xs next) (2 * (xs.length + 1))
    convert h using 1
    omega

theorem cost_root (xs : Words) : CostAtMost (root xs) 78 := by
  change CostAtMost ((fun y : BitVec 256 => y.extractLsb' 0 128) <$>
    rootFold (List.ofFn xs) 0) 78
  have h := cost_map (cost_rootFold (List.ofFn xs) 0) (fun y => y.extractLsb' 0 128)
  simpa only [List.length_ofFn] using h

theorem keygen_cost : scheme.KeygenCostAtMost keygenBudget := by
  apply CostAtMost.mono (b := 9984)
  · change CostAtMost keygen 9984
    unfold keygen
    have first := cost_tabulate 39 0 (fun _ => sampleBits 128) (fun _ => cost_sample 128)
    have endpoints (sk : Words) := cost_tabulate 39 254
      (fun i => chain i.val 0 127 (sk i)) (fun i => cost_chain i.val 0 127 (sk i))
    exact cost_bind first (fun sk => cost_bind (endpoints sk) (fun xs =>
      cost_bind (cost_root xs) (fun pk => cost_pure (pk, sk) 0)))
  · norm_num [keygenBudget]

theorem sign_cost : scheme.SignCostAtMost signBudget := by
  intro sk m
  apply CostAtMost.mono (b := 9906)
  · unfold scheme sign
    exact cost_bind (cost_tabulate 39 254 _ (fun i =>
      CostAtMost.mono (cost_chain i.val 0 (digit m i) (sk i))
        (Nat.mul_le_mul_left 2 (digit_le m i)))) (fun xs => cost_pure _ 0)
  · norm_num [signBudget]

theorem verify_cost : scheme.VerifyCostAtMost 9984 := by
  intro pk m bits
  change CostAtMost (verify pk m bits) 9984
  unfold verify
  split
  · exact cost_pure _ _
  · exact cost_bind (cost_tabulate 39 254 _ (fun i =>
      CostAtMost.mono (cost_chain i.val (digit m i) (127 - digit m i) (decode bits i))
        (Nat.mul_le_mul_left 2 (Nat.sub_le _ _)))) (fun xs =>
      cost_bind (cost_root xs) (fun _ => cost_pure _ 0))

theorem verification_budget : scheme.VerifyCostAtMost verifyBudget :=
  OracleAlgorithm.Scheme.VerifyCostAtMost.mono scheme verify_cost (by norm_num [verifyBudget])

end OptimalOTS.LeanIsaBaseline
