import Submissions.UpperLeanIsa.Resources
import Submissions.UpperLeanIsa.Master

/-! Retain the compression cost already paid by a prefix of an experiment. -/

open OracleSpec OracleComp OracleComp.EvalDist

noncomputable section

namespace OptimalOTS.LeanIsaBaseline.Layer

open scoped Classical

/-- Every supported execution of this prefix pays at least `n`, leaving the
continuation at most the original budget minus `n`. -/
structure Spends {α : Type} (oa : OracleComp Spec α) (n : ℕ) : Prop where
  run_budget : ∀ {β : Type} (k : α → OracleComp Spec β) {B : ℕ} (c : Cache) (p : α × Cache),
    p ∈ support (run oa c) → CostAtMost (oa >>= k) B →
      n ≤ B ∧ CostAtMost (k p.1) (B - n)

theorem spends_zero {α : Type} (oa : OracleComp Spec α) : Spends oa 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    constructor
    intro β k B c p hp h
    rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [pure_bind] at h
    exact ⟨Nat.zero_le _, h⟩
  | query_bind t f ih =>
    constructor
    intro β k B c p hp h
    rw [bind_assoc, costAtMost_query_bind_iff] at h
    rw [run_query_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, -, hp⟩ := hp
    have hh := ((ih u).run_budget k c' p hp (h.2 u)).2
    exact ⟨Nat.zero_le _, CostAtMost.mono hh (by omega)⟩

theorem spends_bind {α β : Type} {oa : OracleComp Spec α} {f : α → OracleComp Spec β}
    {a b : ℕ} (ha : Spends oa a) (hb : ∀ x, Spends (f x) b) :
    Spends (oa >>= f) (a + b) := by
  constructor
  intro γ k B c p hp h
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨q, hq, hp⟩ := hp
  rw [bind_assoc] at h
  obtain ⟨hab, hx⟩ := ha.run_budget (fun x => f x >>= k) c q hq h
  obtain ⟨hbb, hy⟩ := (hb q.1).run_budget k q.2 p hp hx
  exact ⟨by omega, by simpa only [Nat.sub_sub] using hy⟩

theorem spends_map {α β : Type} {oa : OracleComp Spec α} {n : ℕ}
    (h : Spends oa n) (f : α → β) : Spends (f <$> oa) n := by
  have hh := spends_bind h (fun x => spends_zero (pure (f x)))
  simpa only [map_eq_bind_pure_comp, Function.comp_def, Nat.add_zero] using hh

theorem spends_hash (x : BitVec 896) : Spends (hash x) 2 := by
  constructor
  intro β k B c p _ h
  unfold hash at h
  rw [costAtMost_query_bind_iff] at h
  have hc : queryCost (.inr (⟨896, x⟩ : Query)) = 2 := by
    norm_num [queryCost, blockCost, blockBits]
  rw [hc] at h
  exact ⟨h.1, h.2 p.1⟩

theorem spends_tabulate {α : Type} {n : ℕ} (b : Fin n → ℕ)
    (f : Fin n → OracleComp Spec α) (h : ∀ i, Spends (f i) (b i)) :
    Spends (tabulate f) (∑ i, b i) := by
  induction n with
  | zero => simpa [tabulate] using spends_zero (pure (Fin.elim0 : Fin 0 → α))
  | succ n ih =>
    have hb := spends_bind (h 0) (fun x =>
      spends_map (ih (fun i => b i.succ) (fun i => f i.succ) (fun i => h i.succ))
        (fun (xs : Fin n → α) (i : Fin (n + 1)) =>
          Fin.cases (motive := fun _ => α) x xs i))
    rw [Fin.sum_univ_succ]
    simpa only [tabulate, map_eq_bind_pure_comp, Function.comp_def] using hb

namespace Params

variable (P : Params)

theorem spends_chainStep (k : Fin numChains) (j : ℕ) (x : Word) :
    Spends (P.chainStep k j x) 2 := spends_map (spends_hash _) _

theorem spends_chainList (k : Fin numChains) : ∀ (j n : ℕ) (x : Word),
    Spends (P.chainList k j n x) (2 * n) := by
  intro j n
  induction n generalizing j with
  | zero => intro x; exact spends_zero _
  | succ n ih =>
    intro x
    have h := spends_bind (P.spends_chainStep k j x) (fun y =>
      spends_map (ih (j + 1) y) (fun ys => x :: ys))
    simpa only [chainList, map_eq_bind_pure_comp, Function.comp_def,
      Nat.mul_succ, Nat.add_comm] using h

theorem spends_rootFrom (t : Fin numChains → Word) : ∀ (r n : ℕ) (st : BitVec 256),
    Spends (P.rootFrom t r n st) (2 * n) := by
  intro r n
  induction n generalizing r with
  | zero => intro st; exact spends_zero _
  | succ n ih =>
    intro st
    have h := spends_bind (spends_hash (P.rootInput t r st)) (fun st' => ih (r + 1) st')
    simpa only [rootFrom, Nat.mul_succ, Nat.add_comm] using h

def keygenCost : ℕ := 2 * (∑ k, (P.len k - 1)) + 18

theorem spends_root (t : Fin numChains → Word) : Spends (P.root t) 18 :=
  spends_map (P.spends_rootFrom t 0 9 (rootInit t)) _

theorem spends_keygen : Spends P.keygen P.keygenCost := by
  unfold keygen keygenCost
  have h1 := spends_zero (tabulate (fun _ : Fin numChains => sampleBits 128))
  have h2 (seeds : Fin numChains → Word) := spends_tabulate (fun k => 2 * (P.len k - 1))
    (fun k => P.chainList k 0 (P.len k - 1) (seeds k)) (fun k => P.spends_chainList k _ _ _)
  have h := spends_bind h1 (fun seeds => spends_bind (h2 seeds) (fun tables =>
    spends_bind (P.spends_root (fun k => (tables k).getD (P.len k - 1) 0))
      (fun pk => spends_zero (pure (pk, (⟨tables, pk⟩ : SecretKey))))))
  simpa only [Nat.zero_add, Nat.add_zero, ← Finset.mul_sum] using h

theorem keygenCost_pos : 0 < P.keygenCost := by unfold keygenCost; omega

end Params

end OptimalOTS.LeanIsaBaseline.Layer
