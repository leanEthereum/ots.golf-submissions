import Submissions.UpperLeanIsa.Stages

/-!
# Budgets along the experiment

* `costAtMost_bind_run_support`: a budget for `oa >>= k` is a budget for every continuation
  `k x`, at every output `x` of the lazy-oracle run of `oa`;
* `costAtMost_tabulate_sample_bind`: sampling the secret words is free;
* `two_le_of_costAtMost_experiment`: every budget of the experiment is at least `2`, the cost of
  the first chain query of key generation.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

attribute [local irreducible] hashBits pkBits msgBits securityBits maxSignatureBits
attribute [local irreducible] keygenBudget signBudget verifyBudget

local instance instDecEqRecordBudget : DecidableEq Record := Classical.decEq Record

variable (A : OracleAlgorithm.Adversary)

/-- A budget of `oa >>= k` bounds the continuation at every output of the run of `oa`. -/
theorem costAtMost_bind_run_support {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) {b : ℕ} (h : CostAtMost (oa >>= k) b) :
    ∀ (c : Cache) (p : α × Cache), p ∈ support (run oa c) → CostAtMost (k p.1) b := by
  induction oa using OracleComp.inductionOn generalizing b with
  | pure x =>
    intro c p hp
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [pure_bind] at h
    exact h
  | query_bind t k' ih =>
    intro c p hp
    rw [bind_assoc, costAtMost_query_bind_iff] at h
    obtain ⟨-, h⟩ := h
    rw [run_query_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, -, hp⟩ := hp
    exact CostAtMost.mono (ih u (h u) c' p hp) (Nat.sub_le _ _)

/-- A lifted `ProbComp` costs nothing: the continuation keeps the whole budget. -/
theorem costAtMost_liftM_bind {α β : Type} (pc : ProbComp α)
    (k : α → OracleComp Spec β) {b : ℕ}
    (h : CostAtMost ((liftM pc : OracleComp Spec α) >>= k) b) :
    ∀ x ∈ support pc, CostAtMost (k x) b := by
  change CostAtMost (liftComp pc Spec >>= k) b at h
  induction pc using OracleComp.inductionOn generalizing b with
  | pure x =>
    intro x' hx'
    rw [support_pure, Set.mem_singleton_iff] at hx'
    subst hx'
    rwa [liftComp_pure, pure_bind] at h
  | query_bind t mx ih =>
    intro x hx
    rw [liftComp_bind] at h
    have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) Spec =
        (liftM (Spec.query (.inl t)) : OracleComp Spec _) := by
      simp [liftComp]; rfl
    rw [hq, bind_assoc, costAtMost_query_bind_iff] at h
    obtain ⟨-, h⟩ := h
    rw [support_bind] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, -, hx⟩ := hx
    have := ih u (h u) x hx
    simpa [queryCost] using this

theorem chain_succ (i j n : ℕ) (x : Word) :
    chain i j (n + 1) x = chainStep i j x >>= chain i (j + 1) n := rfl

theorem tabulate_succ {α : Type} {n : ℕ} (f : Fin (n + 1) → OracleComp Spec α) :
    tabulate f = f 0 >>= fun x => tabulate (fun i => f i.succ) >>= fun xs =>
      pure (Fin.cases x xs) := rfl

/-- Peeling the first computation off a `tabulate`. -/
theorem costAtMost_tabulate_succ_bind {α β : Type} {n : ℕ}
    (f : Fin (n + 1) → OracleComp Spec α) (K : (Fin (n + 1) → α) → OracleComp Spec β) {b : ℕ}
    (h : CostAtMost (tabulate f >>= K) b) :
    CostAtMost (f 0 >>= fun x => tabulate (fun i => f i.succ) >>= fun xs =>
      K (Fin.cases x xs)) b := by
  rw [tabulate_succ] at h
  simpa only [bind_assoc, pure_bind] using h

/-- Sampling the secret words is free. -/
theorem costAtMost_tabulate_sample_bind {n m : ℕ} {β : Type}
    (k : (Fin n → BitVec m) → OracleComp Spec β) {b : ℕ}
    (h : CostAtMost (tabulate (fun _ : Fin n => sampleBits m) >>= k) b) :
    ∀ v, CostAtMost (k v) b := by
  induction n with
  | zero =>
    intro v
    rw [tabulate, pure_bind] at h
    have hv : v = Fin.elim0 := funext fun i => Fin.elim0 i
    rw [hv]
    exact h
  | succ n ih =>
    intro v
    have h0 : CostAtMost ((liftM ($ᵗ BitVec m) : OracleComp Spec (BitVec m)) >>= fun x =>
        tabulate (fun _ : Fin n => sampleBits m) >>= fun xs => k (Fin.cases x xs)) b :=
      costAtMost_tabulate_succ_bind (fun _ : Fin (n + 1) => sampleBits m) k h
    have h1 : CostAtMost (tabulate (fun _ : Fin n => sampleBits m) >>= fun xs =>
        k (Fin.cases (v 0) xs)) b :=
      costAtMost_liftM_bind ($ᵗ BitVec m) _ h0 (v 0) (by simp)
    have h2' := ih _ h1 (fun i => v i.succ)
    have h2 : CostAtMost (k (Fin.cases (v 0) (fun i => v i.succ))) b := h2'
    have hv : (Fin.cases (v 0) (fun i => v i.succ) : Fin (n + 1) → BitVec m) = v := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hv] at h2
    exact h2

/-- A nonempty chain walk costs at least one tagged query, i.e. two compressions. -/
theorem two_le_of_costAtMost_chain_bind {β : Type} (i j n : ℕ) (x : Word)
    (K : Word → OracleComp Spec β) {b : ℕ} (h : CostAtMost (chain i j (n + 1) x >>= K) b) :
    2 ≤ b := by
  rw [chain_succ, bind_assoc, chainStep, bind_map_left, hash, costAtMost_query_bind_iff] at h
  have hc : queryCost (.inr (⟨896, chainInput i j x⟩ : Query)) = 2 := by
    norm_num [queryCost, blockCost, blockBits]
  exact (le_of_eq hc.symm).trans h.1

/-- Every budget of the experiment pays for the first chain query of key generation. -/
theorem two_le_of_costAtMost_experiment {B : ℕ}
    (h : CostAtMost (OracleAlgorithm.experiment scheme A) B) : 2 ≤ B := by
  rw [experiment_eq] at h
  unfold keygen at h
  simp only [bind_assoc] at h
  have h1 := costAtMost_tabulate_sample_bind _ h (fun _ => 0)
  have h2 := costAtMost_tabulate_succ_bind (n := 33) _ _ h1
  exact two_le_of_costAtMost_chain_bind _ 0 254 _ _ h2

end OptimalOTS.LeanIsaBaseline

end
