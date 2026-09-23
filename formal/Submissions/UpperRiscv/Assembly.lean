import Submissions.UpperRiscv.StageB
import Submissions.UpperRiscv.GoodRec

/-!
# The security bound of the concrete scheme

For every adversary `A` whose experiment costs at most `B ≤ 2 ^ 127` on every path,

```
probTrue (GScheme.experiment forestScheme A) ≤ 2 ε (B - 1039) + 2 δ,  ε = 2 ^ (-128),
```

where `δ = 2 · 1025² · 2 ^ (-160)` bounds the weight of the bad records (`GoodRec.lean`).

The proof follows `DESIGN.md`: key generation is a uniform record (`E_run_keygen_le`, up to the
records whose keygen points collide); the bad records are given up at once; the
attacker's first stage is coupled to a run without the keygen cache (`iub`), charged through the
potential `ΦA` by the master lemma; the signing loop is handled by `signRho_bound`; the second
stage is coupled to a run without the hidden keygen points (`iub` again), and the events lemma
turns an accepted forgery into one of the charged events.

Implementation note: `fiberA`, `graph`, `CostAtMost` and the computations of the experiment are
made locally irreducible. Otherwise the unifier unfolds `Finset.univ : Finset Rec` (through
`fiberA`), the structure literal `graph` (through `forestScheme.graph`), or the signing loop
(through `CostAtMost (rest₂ …)`) and hits the maximal recursion depth; every use of these
definitions below goes through their equation lemmas or through `forestScheme`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

attribute [local irreducible] fiberA graph CostAtMost GScheme.experiment rest rest₂ signIdx GScheme.keygen GScheme.sign
attribute [local irreducible] validSet numValid

variable (A : Adversary)
/-! ## Stage A -/

/-- The quantity bounded after the first stage. -/
def FA (pk : BitVec 128) (x : Message × A.State) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiberA pk, w * (ind (GoodRec ξ) * (if Cache.Hits d (kc ξ) then 1 else
    E (run (rest₂ A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) g))

theorem fiberA_nonempty (pk : BitVec 128) : (fiberA pk).Nonempty := by
  refine ⟨(fun _ => 0, fun _ => pk.setWidth 256), ?_⟩
  simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
  show trunc128 (pk.setWidth 256) = pk
  rw [trunc128, BitVec.setWidth_setWidth_of_le _ (by norm_num), BitVec.setWidth_eq]

/-! ### Auxiliary lemmas -/

theorem mem_fiberA_asm {pk : BitVec 128} {ξ : Rec} (h : ξ ∈ fiberA pk) : pkOf ξ = pk := by
  rw [fiberA, Finset.mem_filter] at h
  exact h.2

theorem ind_eq_ite_asm (p : Prop) {inst : Decidable p} : ind p = @ite _ p inst 1 0 := by
  unfold ind
  by_cases h : p
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem ind_mono_asm {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  unfold ind
  by_cases hp : p
  · rw [if_pos hp, if_pos (h hp)]
  · rw [if_neg hp]; exact zero_le

/-- A finite sum of scaled expectations is the expectation of the sum. -/
theorem sum_mul_E_asm {ι : Type} (s : Finset ι) (c : ι → ℝ≥0∞) {α : Type} (p : ProbComp α)
    (G : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, c i * E p (G i) = E p (fun y => ∑ i ∈ s, c i * G i y) := by
  refine Eq.trans ?_ (expectedValue_finsetSum p s (fun i y => c i * G i y)).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  show c i * E p (G i) = E p (fun y => c i * G i y)
  rw [mul_comm, ← expectedValue_mul_const]
  exact congrArg _ (funext fun y => mul_comm _ _)

/-- Signing followed by the second stage, through the signing loop. -/
theorem rest₂_eq_signIdx (pk : BitVec 128) (ξ : Rec) (hpk : pkOf ξ = pk) (x : Message × A.State) :
    rest₂ A pk (graph.evalRec ξ) x =
      signIdx (emsg x.1 pk) >>= fun r => stB A pk x.1 x.2 (sigOf ξ r) := by
  unfold rest₂
  rw [sign_eq, hpk, bind_map_left]

/-- The keygen cache is irrelevant to the signing loop. -/
theorem E_rest₂_extend_kc (pk : BitVec 128) (ξ : Rec) (hpk : pkOf ξ = pk) (x : Message × A.State)
    (d : Cache) :
    E (run (rest₂ A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) g =
      E (run (signIdx (emsg x.1 pk)) d) (fun p =>
        E (run (stB A pk x.1 x.2 (sigOf ξ p.1)) (Cache.extend p.2 (kc ξ))) g) := by
  rw [rest₂_eq_signIdx A pk ξ hpk, run_bind,
    run_signIdx_extend (emsg x.1 pk) d (kc ξ) (fun u => kc_enc ξ u), bind_map_left, E_bind]

/-- The continuation bound after the first stage. -/
theorem stageA_cont (pk : BitVec 128) (x : Message × A.State) (d : Cache) (b' : ℕ)
    (hI : Inv d b') (hB : ∀ ξ ∈ fiberA pk, CostAtMost (rest₂ A pk (graph.evalRec ξ) x) b') :
    FA A pk x d ≤ ΦA pk d + κ * sumW (fiberA pk) * b' := by
  obtain ⟨T, hTdef⟩ : ∃ T : Finset Rec,
      T = (fiberA pk).filter (fun ξ => ¬ Cache.Hits d (kc ξ) ∧ GoodRec ξ) := ⟨_, rfl⟩
  have hT : T ⊆ fiberA pk := by
    rw [hTdef]; exact Finset.filter_subset _ _
  have hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ) := by
    intro ξ hξ
    rw [hTdef, Finset.mem_filter] at hξ
    exact hξ.2.1
  have hTg : ∀ ξ ∈ T, GoodRec ξ := by
    intro ξ hξ
    rw [hTdef, Finset.mem_filter] at hξ
    exact hξ.2.2
  -- Step 1: split `FA` into the records hit by `d` and the good others.
  have hsplit : FA A pk x d ≤ ∑ ξ ∈ fiberA pk, w * ind (Cache.Hits d (kc ξ)) +
      ∑ ξ ∈ T, w * E (run (signIdx (emsg x.1 pk)) d) (fun p =>
        E (run (stB A pk x.1 x.2 (sigOf ξ p.1)) (Cache.extend p.2 (kc ξ))) g) := by
    unfold FA
    rw [hTdef, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ξ hξ => ?_
    have hpk : pkOf ξ = pk := mem_fiberA_asm hξ
    unfold ind
    by_cases hg : GoodRec ξ
    · rw [if_pos hg, one_mul]
      by_cases h : Cache.Hits d (kc ξ)
      · rw [if_pos h, if_pos h,
          if_neg (show ¬ (¬ Cache.Hits d (kc ξ) ∧ GoodRec ξ) from fun h' => h'.1 h), add_zero, mul_one]
      · rw [if_neg h, if_neg h, if_pos (show ¬ Cache.Hits d (kc ξ) ∧ GoodRec ξ from ⟨h, hg⟩),
          mul_zero, zero_add, E_rest₂_extend_kc A pk ξ hpk]
    · rw [if_neg hg, zero_mul, mul_zero]
      exact zero_le
  -- Step 2: the signing bound on the records of `T`.
  have hne : Nonempty {ξ // ξ ∈ fiberA pk} := (fiberA_nonempty pk).to_subtype
  have hΦ : EncInvariant (fun c => ∑ ξ ∈ T, w * ind (Spr c ξ)) := by
    intro c u w'
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [spr_cacheQuery_enc c ξ u w']
  have hB' : ∀ j : {ξ // ξ ∈ fiberA pk},
      CostAtMost (signIdx (emsg x.1 pk) >>= fun r => stB A pk x.1 x.2 (sigOf j.1 r)) b' := by
    intro j
    have h : CostAtMost (rest₂ A pk (graph.evalRec j.1) x) b' := hB j.1 j.2
    rw [rest₂_eq_signIdx A pk j.1 (mem_fiberA_asm j.2)] at h
    exact h
  have hsig : E (run (signIdx (emsg x.1 pk)) d) (fun p => ∑ ξ ∈ T, w *
        E (run (stB A pk x.1 x.2 (sigOf ξ p.1)) (Cache.extend p.2 (kc ξ))) g) ≤
      ∑ ξ ∈ T, w * ind (Spr d ξ) + sumW T * encTerm d + κ * sumW (fiberA pk) * b' := by
    refine signRho_bound (numValid_le) (by decide) (emsg x.1 pk) d
      (β := Bool) (J := {ξ // ξ ∈ fiberA pk}) (fun j r => stB A pk x.1 x.2 (sigOf j.1 r))
      (fun r d' => ∑ ξ ∈ T, w * E (run (stB A pk x.1 x.2 (sigOf ξ r))
        (Cache.extend d' (kc ξ))) g)
      (fun c => ∑ ξ ∈ T, w * ind (Spr c ξ)) hΦ (κ * sumW (fiberA pk)) (sumW T) (encTerm d)
      Inv Inv_fresh Inv_cached ?_
      (fun c h1 h2 => psi_dom paperRowHyp (two_encCount_le hI) (emsg x.1 pk) c h1 h2) hI hB'
    intro r d' b'' hd' hI' hB''
    have hB''' : ∀ ξ ∈ T, CostAtMost (stB A pk x.1 x.2 (sigOf ξ r)) b'' := by
      intro ξ hξ
      exact hB'' ⟨ξ, hT hξ⟩
    refine (stageB A pk x.1 x.2 d T hT hTg hTd r d' hd' b'' hI' hB''').trans ?_
    refine add_le_add (add_le_add ?_ (mul_le_mul_right (le_of_eq (ind_eq_ite_asm _)) _)) le_rfl
    exact Finset.sum_le_sum fun ξ _ => mul_le_mul_right (ind_mono_asm (Spr.mono hd'.1)) w
  -- Step 3: assemble.
  refine hsplit.trans ?_
  rw [sum_mul_E_asm]
  refine (add_le_add_right hsig _).trans ?_
  unfold ΦA
  have h1 : ∑ ξ ∈ T, w * ind (Spr d ξ) ≤ ∑ ξ ∈ fiberA pk, w * ind (Spr d ξ) :=
    Finset.sum_le_sum_of_subset hT
  have h2 : sumW T ≤ sumW (fiberA pk) := Finset.sum_le_sum_of_subset hT
  calc ∑ ξ ∈ fiberA pk, w * ind (Cache.Hits d (kc ξ)) +
        (∑ ξ ∈ T, w * ind (Spr d ξ) + sumW T * encTerm d + κ * sumW (fiberA pk) * b')
      ≤ ∑ ξ ∈ fiberA pk, w * ind (Cache.Hits d (kc ξ)) +
        (∑ ξ ∈ fiberA pk, w * ind (Spr d ξ) + sumW (fiberA pk) * encTerm d +
          κ * sumW (fiberA pk) * b') := by
        gcongr
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        ring

/-- The first stage. -/
theorem stageA_master (pk : BitVec 128) (b : ℕ) (hb : b ≤ 2 ^ 127)
    (hB : ∀ ξ ∈ fiberA pk, CostAtMost (A.choose pk >>= rest₂ A pk (graph.evalRec ξ)) b) :
    E (run (A.choose pk) ∅) (fun p => FA A pk p.1 p.2) ≤ κ * sumW (fiberA pk) * b := by
  have hne : Nonempty {ξ // ξ ∈ fiberA pk} := (fiberA_nonempty pk).to_subtype
  have hF : ∀ (x : Message × A.State) (d : Cache) (b' : ℕ), Inv d b' →
      (∀ j : {ξ // ξ ∈ fiberA pk}, CostAtMost (rest₂ A pk (graph.evalRec j.1) x) b') →
      FA A pk x d ≤ ΦA pk d + κ * sumW (fiberA pk) * b' := by
    intro x d b' hI hB'
    refine stageA_cont A pk x d b' hI fun ξ hξ => ?_
    exact hB' ⟨ξ, hξ⟩
  have hI0 : Inv ∅ b := by
    show encCount ∅ + b ≤ 2 ^ 127
    rw [encCount_empty, zero_add]; exact hb
  have hB0 : ∀ j : {ξ // ξ ∈ fiberA pk},
      CostAtMost (A.choose pk >>= rest₂ A pk (graph.evalRec j.1)) b :=
    fun j => hB j.1 j.2
  have h := master_family (α := Message × A.State) (β := Bool)
    (J := {ξ // ξ ∈ fiberA pk}) (κ * sumW (fiberA pk)) (ΦA pk) Inv Inv_fresh Inv_cached (ΦA_charge pk)
    (A.choose pk) (fun j => rest₂ A pk (graph.evalRec j.1)) (fun x d => FA A pk x d) hF ∅ b hI0 hB0
  rw [ΦA_empty, zero_add] at h
  exact h

/-- The first stage, coupled to the run without the keygen cache. -/
theorem stageA_iub (ξ : Rec) :
    E (run (rest A (pkOf ξ, graph.evalRec ξ)) (kc ξ)) g ≤
      E (run (A.choose (pkOf ξ)) ∅) (fun p => if Cache.Hits p.2 (kc ξ) then 1 else
        E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) g) := by
  unfold rest
  dsimp only
  rw [run_bind, E_bind]
  have hdisj : Cache.Disjoint ∅ (kc ξ) := fun _ _ => rfl
  have h := iub (A.choose (pkOf ξ)) (kc ξ)
    (fun p => E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) p.2) g)
    (fun p => E_le_one _ g_le_one) ∅ hdisj
  rw [Cache.empty_extend] at h
  exact h

theorem regroup (G : Rec → (Message × A.State) × Cache → ℝ≥0∞) :
    ∑ ξ, w * E (run (A.choose (pkOf ξ)) ∅) (G ξ) =
      ∑ pk, E (run (A.choose pk) ∅) (fun p => ∑ ξ ∈ fiberA pk, w * G ξ p) := by
  symm
  calc ∑ pk, E (run (A.choose pk) ∅) (fun p => ∑ ξ ∈ fiberA pk, w * G ξ p)
      = ∑ pk, ∑ ξ ∈ fiberA pk, w * E (run (A.choose (pkOf ξ)) ∅) (G ξ) := by
        refine Finset.sum_congr rfl fun pk _ => ?_
        rw [← sum_mul_E_asm]
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        rw [mem_fiberA_asm hξ]
    _ = ∑ ξ, w * E (run (A.choose (pkOf ξ)) ∅) (G ξ) := by
        unfold fiberA
        exact Finset.sum_fiberwise Finset.univ pkOf _

theorem sum_sumW_fiberA : ∑ pk : BitVec 128, sumW (fiberA pk) = 1 := by
  unfold sumW fiberA
  rw [Finset.sum_fiberwise Finset.univ pkOf (fun _ => w)]
  exact sum_w

/-! ## The bound -/

/-- Key generation as a uniform record, for the concrete scheme, up to the records whose keygen
points collide. -/
theorem E_run_keygen_forest
    (g' : (PublicKey × forestScheme.graph.Assignment) × Cache → ℝ≥0∞) (hg : ∀ a, g' a ≤ 1) :
    E (run forestScheme.keygen ∅) g' ≤
      ∑ ξ : Rec, w * (g' ((pkOf ξ, graph.evalRec ξ), kc ξ) + ind (¬ DistinctRec ξ)) := by
  refine (E_run_keygen_le forestScheme g' hg).trans (le_of_eq ?_)
  show ∑ ξ : Rec, (Fintype.card Rec : ℝ≥0∞)⁻¹ *
    (g' ((forestScheme.publicKey (graph.evalRec ξ), graph.evalRec ξ), graph.keygenCache ξ) +
      if graph.Distinct (graph.evalRec ξ) then 0 else 1) = _
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [publicKey_eq_pkOf]
  refine congrArg _ (congrArg _ ?_)
  unfold ind
  by_cases hd : DistinctRec ξ
  · rw [if_pos (show graph.Distinct (graph.evalRec ξ) from hd), if_neg (not_not.2 hd)]
  · rw [if_neg (show ¬ graph.Distinct (graph.evalRec ξ) from hd), if_pos hd]

/-- The experiment as a uniform average over records of the continuation after key generation,
up to the records whose keygen points collide. -/
theorem E_run_experiment (g' : Bool × Cache → ℝ≥0∞) (hg : ∀ a, g' a ≤ 1) :
    E (run (GScheme.experiment forestScheme A) ∅) g' ≤
      ∑ ξ : Rec, w * (E (run (rest A (pkOf ξ, graph.evalRec ξ)) (kc ξ)) g' + ind (¬ DistinctRec ξ)) := by
  rw [experiment_eq]
  have h1 := run_bind forestScheme.keygen (rest A) ∅
  rw [h1, E_bind]
  exact E_run_keygen_forest _ fun a => E_le_one _ hg

/-- The budget after key generation, for the concrete scheme. -/
theorem costAtMost_rest_forest {B : ℕ} (hB : CostAtMost (GScheme.experiment forestScheme A) B) :
    1039 ≤ B ∧ ∀ ξ : Rec, CostAtMost (rest A (pkOf ξ, graph.evalRec ξ)) (B - 1039) := by
  rw [experiment_eq] at hB
  obtain ⟨h1, h2⟩ := costAtMost_keygen_bind forestScheme (rest A) hB
  refine ⟨?_, fun ξ => ?_⟩
  · have h1' : graph.keygenCost ≤ B := h1
    rwa [graph_keygenCost] at h1'
  · have h2' : CostAtMost (rest A (forestScheme.publicKey (graph.evalRec ξ), graph.evalRec ξ))
        (B - graph.keygenCost) := h2 ξ
    rwa [publicKey_eq_pkOf, graph_keygenCost] at h2'

theorem keygen_le {B : ℕ} (hB : CostAtMost (GScheme.experiment forestScheme A) B) : 1039 ≤ B :=
  (costAtMost_rest_forest A hB).1

theorem sum_w_ind_not_goodRec_le : ∑ ξ : Rec, w * ind (¬ GoodRec ξ) ≤ δ := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_)) sum_w_not_goodRec_le
  unfold ind
  split_ifs <;> simp

theorem sum_w_ind_not_distinctRec_le : ∑ ξ : Rec, w * ind (¬ DistinctRec ξ) ≤ δ := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_)) sum_w_not_distinctRec_le
  unfold ind
  split_ifs <;> simp

theorem main_bound {B : ℕ} (hB : CostAtMost (GScheme.experiment forestScheme A) B) (hB' : B ≤ 2 ^ 127) :
    probTrue (GScheme.experiment forestScheme A) ≤ κ * ((B - 1039 : ℕ) : ℝ≥0∞) + 2 * δ := by
  obtain ⟨h1039, hrest⟩ := costAtMost_rest_forest A hB
  rw [probTrue_eq]
  refine (E_run_experiment A g g_le_one).trans ?_
  simp only [mul_add, Finset.sum_add_distrib]
  refine le_trans (add_le_add le_rfl sum_w_ind_not_distinctRec_le) ?_
  rw [two_mul, ← add_assoc]
  refine add_le_add ?_ le_rfl
  calc ∑ ξ : Rec, w * E (run (rest A (pkOf ξ, graph.evalRec ξ)) (kc ξ)) g
      ≤ ∑ ξ : Rec, (w * ind (¬ GoodRec ξ) +
          w * (ind (GoodRec ξ) * E (run (rest A (pkOf ξ, graph.evalRec ξ)) (kc ξ)) g)) := by
        refine Finset.sum_le_sum fun ξ _ => ?_
        unfold ind
        by_cases hg : GoodRec ξ
        · rw [if_neg (not_not.2 hg), if_pos hg, mul_zero, zero_add, one_mul]
        · rw [if_pos hg, if_neg hg, zero_mul, mul_zero, add_zero, mul_one]
          exact mul_le_of_le_one_right zero_le (E_le_one _ g_le_one)
    _ = ∑ ξ : Rec, w * ind (¬ GoodRec ξ) +
          ∑ ξ : Rec, w * (ind (GoodRec ξ) * E (run (rest A (pkOf ξ, graph.evalRec ξ)) (kc ξ)) g) :=
        Finset.sum_add_distrib
    _ ≤ δ + ∑ ξ : Rec, w * (ind (GoodRec ξ) * E (run (A.choose (pkOf ξ)) ∅) (fun p =>
          if Cache.Hits p.2 (kc ξ) then 1 else
            E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) g)) := by
        refine add_le_add sum_w_ind_not_goodRec_le (Finset.sum_le_sum fun ξ _ => ?_)
        gcongr
        exact stageA_iub A ξ
    _ = δ + ∑ ξ : Rec, w * E (run (A.choose (pkOf ξ)) ∅) (fun p => ind (GoodRec ξ) *
          (if Cache.Hits p.2 (kc ξ) then 1 else
            E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) g)) := by
        refine congrArg _ (Finset.sum_congr rfl fun ξ _ => ?_)
        rw [E_const_mul]
    _ = δ + ∑ pk, E (run (A.choose pk) ∅) (fun p => ∑ ξ ∈ fiberA pk, w * (ind (GoodRec ξ) *
          (if Cache.Hits p.2 (kc ξ) then 1 else
            E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) g))) := by
        refine congrArg _ (regroup A (fun ξ p => ind (GoodRec ξ) *
          (if Cache.Hits p.2 (kc ξ) then 1 else
            E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) g)))
    _ = δ + ∑ pk, E (run (A.choose pk) ∅) (fun p => FA A pk p.1 p.2) := by
        refine congrArg _ (Finset.sum_congr rfl fun pk _ => ?_)
        refine congrArg _ (funext fun p => ?_)
        unfold FA
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        rw [mem_fiberA_asm hξ]
    _ ≤ δ + ∑ pk, κ * sumW (fiberA pk) * ((B - 1039 : ℕ) : ℝ≥0∞) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun pk _ => ?_)
        refine stageA_master A pk (B - 1039) ((Nat.sub_le B 1039).trans hB') fun ξ hξ => ?_
        have h := hrest ξ
        rw [mem_fiberA_asm hξ] at h
        unfold rest at h
        dsimp only at h
        exact h
    _ = κ * ((B - 1039 : ℕ) : ℝ≥0∞) + δ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_sumW_fiberA, mul_one, add_comm]

end Forest

end OptimalOTS
