import Submissions.UpperLeanIsa.Records
import Submissions.UpperLeanIsa.IUB

/-!
# Key generation is a uniform record

Under the lazy random oracle started from the empty cache, key generation samples the 42 seeds
and then queries every chain step and every root call exactly once, at pairwise distinct
inputs (`location_eq_of_input_eq`). Its output and final cache are those of a uniformly random
record:

```
E[g' | run keygen ∅] = ∑ ξ : Record P, recW P · g' ((ξ.pk, ξ.sk), ξ.cache).
```

Adapted from the record's `KeygenBridge` (after the checked `upper-riscv-687` keygen bridge):
every fresh answer is absorbed into a uniform *full* answer table `y : Loc P → BitVec 256`
(`sum_avg_update`); the caches written along the way are described by `progUpd`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false

theorem tabulate_succ' {α : Type} {n : ℕ} (f : Fin (n + 1) → OracleComp Spec α) :
    tabulate f = f 0 >>= fun x => tabulate (fun i => f i.succ) >>= fun xs =>
      pure (Fin.cases x xs) := rfl

theorem tabulate_zero' {α : Type} (f : Fin 0 → OracleComp Spec α) :
    tabulate f = pure Fin.elim0 := rfl

attribute [local irreducible] Params.chainList Params.rootFrom tabulate

/-! ## Averaging over one coordinate (generic) -/

theorem sum_sum_update_pi {ι : Type} [Fintype ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, Fintype (R i)] (H : ((i : ι) → R i) → ℝ≥0∞) (i : ι) :
    ∑ u : R i, ∑ g : (j : ι) → R j, H (Function.update g i u) =
      Fintype.card (R i) * ∑ g, H g := by
  let φ : ((j : ι) → R j) × R i → ((j : ι) → R j) × R i :=
    fun p => (Function.update p.1 i p.2, p.1 i)
  have hφ : Function.Involutive φ := by
    intro p
    simp [φ]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun g u => H (Function.update g i u))]
  have := Equiv.sum_comp hφ.toPerm (fun p => H p.1)
  simp only [Function.Involutive.coe_toPerm, φ] at this
  rw [this, Fintype.sum_prod_type]
  simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, mul_comm]

theorem sum_inv_card_mul' {α : Type} [Fintype α] [Nonempty α] (a : ℝ≥0∞) :
    ∑ _x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * a = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

theorem sum_avg_update {ι : Type} [Fintype ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, Fintype (R i)] [∀ i, Nonempty (R i)] (i : ι) (Φ : R i → ((j : ι) → R j) → ℝ≥0∞)
    (hΦ : ∀ u u' y, Φ u (Function.update y i u') = Φ u y) :
    ∑ u : R i, (Fintype.card (R i) : ℝ≥0∞)⁻¹ *
        ∑ y : (j : ι) → R j, (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * Φ u y =
      ∑ y : (j : ι) → R j, (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * Φ (y i) y := by
  have key := sum_sum_update_pi (fun y => Φ (y i) y) i
  simp only [Function.update_self, hΦ] at key
  have hn0 : (Fintype.card (R i) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnt : (Fintype.card (R i) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [← Finset.mul_sum]
  rw [key]
  calc (Fintype.card (R i) : ℝ≥0∞)⁻¹ * ((Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ *
        (Fintype.card (R i) * ∑ y, Φ (y i) y))
      = ((Fintype.card (R i) : ℝ≥0∞)⁻¹ * Fintype.card (R i)) *
          ((Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * ∑ y, Φ (y i) y) := by ring
    _ = (Fintype.card ((j : ι) → R j) : ℝ≥0∞)⁻¹ * ∑ y, Φ (y i) y := by
        rw [ENNReal.inv_mul_cancel hn0 hnt, one_mul]

theorem sum_fin_cases {α : Type} [Fintype α] {n : ℕ}
    (F : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∑ f, F f = ∑ x : α, ∑ xs : Fin n → α, F (Fin.cases x xs : Fin (n + 1) → α) := by
  rw [← Fintype.sum_prod_type' (fun (x : α) (xs : Fin n → α) =>
    F (Fin.cases x xs : Fin (n + 1) → α))]
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => α)
    (fun p => F (Fin.cases p.1 p.2 : Fin (n + 1) → α)) F fun _ => rfl).symm

/-! ## Full answer tables and one fresh query -/

variable {P : Params}

/-- A query the cache does not hold gets a fresh uniform answer, which is then cached. -/
theorem run_hash_fresh {n : ℕ} (x : BitVec n) (c : Cache) (hc : c ⟨n, x⟩ = none) :
    run (hash x) c = ($ᵗ BitVec hashBits) >>= fun u => pure (u, c.cacheQuery ⟨n, x⟩ u) := by
  change (simulateQ oracleImpl (liftM (Spec.query (.inr ⟨n, x⟩)))).run c = _
  rw [simulateQ_spec_query]
  exact oracleImpl_run_inr_none hc

theorem run_sampleBits (m : ℕ) (c : Cache) :
    run (sampleBits m) c = (fun x => (x, c)) <$> ($ᵗ BitVec m) := by
  unfold sampleBits
  exact run_liftM _ c

/-! ## Sampling the seeds -/

theorem E_run_tabulate_sample (n : ℕ) :
    ∀ (g : (Fin n → Word) × Cache → ℝ≥0∞) (c : Cache),
      E (run (tabulate fun _ : Fin n => sampleBits 128) c) g =
        ∑ sk : Fin n → Word, (Fintype.card (Fin n → Word) : ℝ≥0∞)⁻¹ * g (sk, c) := by
  induction n with
  | zero =>
    intro g c
    rw [tabulate_zero', run_pure, E_pure]
    symm
    calc ∑ sk : Fin 0 → Word, (Fintype.card (Fin 0 → Word) : ℝ≥0∞)⁻¹ * g (sk, c)
        = ∑ _sk : Fin 0 → Word, (Fintype.card (Fin 0 → Word) : ℝ≥0∞)⁻¹ * g (Fin.elim0, c) :=
          Finset.sum_congr rfl fun sk _ => by
            rw [show sk = Fin.elim0 from funext fun i => Fin.elim0 i]
      _ = g (Fin.elim0, c) := sum_inv_card_mul' _
  | succ n ih =>
    intro g c
    have h0 : (Fintype.card Word : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have ht : (Fintype.card Word : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hcard : (Fintype.card (Fin (n + 1) → Word) : ℝ≥0∞) =
        (Fintype.card Word : ℝ≥0∞) * (Fintype.card (Fin n → Word) : ℝ≥0∞) := by
      rw [← Nat.cast_mul, ← Fintype.card_prod,
        Fintype.card_congr (Fin.consEquiv fun _ : Fin (n + 1) => Word)]
    have hx : ∀ x : Word, E (run (tabulate (fun _ : Fin n => sampleBits 128) >>= fun xs =>
        pure (Fin.cases x xs : Fin (n + 1) → Word)) c) g =
        ∑ xs : Fin n → Word, (Fintype.card (Fin n → Word) : ℝ≥0∞)⁻¹ *
          g ((Fin.cases x xs : Fin (n + 1) → Word), c) := by
      intro x
      rw [run_bind, E_bind, ih]
      refine Finset.sum_congr rfl fun xs _ => ?_
      simp only [run_pure, E_pure]
    calc E (run (tabulate fun _ : Fin (n + 1) => sampleBits 128) c) g
        = E (run (sampleBits 128) c) (fun p => E (run (tabulate (fun _ : Fin n => sampleBits 128)
            >>= fun xs => pure (Fin.cases p.1 xs : Fin (n + 1) → Word)) p.2) g) := by
          rw [tabulate_succ', run_bind, E_bind]
      _ = ∑ x : Word, (Fintype.card Word : ℝ≥0∞)⁻¹ * E (run (tabulate
            (fun _ : Fin n => sampleBits 128) >>= fun xs =>
              pure (Fin.cases x xs : Fin (n + 1) → Word)) c) g := by
          simp only [run_sampleBits, E_map, E_uniform]
      _ = ∑ x : Word, (Fintype.card Word : ℝ≥0∞)⁻¹ * ∑ xs : Fin n → Word,
            (Fintype.card (Fin n → Word) : ℝ≥0∞)⁻¹ *
              g ((Fin.cases x xs : Fin (n + 1) → Word), c) :=
          Finset.sum_congr rfl fun x _ => by rw [hx x]
      _ = ∑ sk : Fin (n + 1) → Word,
            (Fintype.card (Fin (n + 1) → Word) : ℝ≥0∞)⁻¹ * g (sk, c) := by
          rw [sum_fin_cases (fun sk : Fin (n + 1) → Word =>
            (Fintype.card (Fin (n + 1) → Word) : ℝ≥0∞)⁻¹ * g (sk, c))]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun xs _ => ?_
          rw [hcard, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), mul_assoc]

end OptimalOTS.LeanIsaBaseline.Layer
