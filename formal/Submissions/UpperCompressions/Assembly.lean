import Submissions.UpperCompressions.StageB

/-!
# The security bound of the concrete scheme

For every adversary `A` whose experiment costs at most `B ≤ 2 ^ 127` on every path,

```
probTrue (experiment forestScheme A) ≤ 2 ε (B - 782),  ε = 2 ^ (-128).
```

The proof follows `DESIGN.md`: key generation is a uniform record (`E_run_keygen`); the
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

attribute [local irreducible] fiberA graph CostAtMost experiment rest rest₂ signIdx Scheme.keygen Scheme.sign

variable (A : Adversary)
/-! ## Stage A -/

/-- The quantity bounded after the first stage. -/
def FA (pk : BitVec 128) (x : Message × A.State) (d : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ fiberA pk, w * (if Cache.Hits d (kc ξ) then 1 else
    E (run (rest₂ A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) g)

theorem fiberA_nonempty (pk : BitVec 128) : (fiberA pk).Nonempty := by
  refine ⟨(fun _ => 0, fun _ => pk.setWidth 256), ?_⟩
  simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
  show trunc (pk.setWidth 256) = pk
  rw [trunc, BitVec.setWidth_setWidth_of_le _ (by norm_num), BitVec.setWidth_eq]

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
theorem rest₂_eq_signIdx (pk : BitVec 128) (ξ : Rec) (x : Message × A.State) :
    rest₂ A pk (graph.evalRec ξ) x =
      signIdx x.1 >>= fun r => stB A pk x.1 x.2 (sigOf ξ r) := by
  unfold rest₂
  rw [sign_eq, bind_map_left]

/-- The keygen cache is irrelevant to the signing loop. -/
theorem E_rest₂_extend_kc (pk : BitVec 128) (ξ : Rec) (x : Message × A.State)
    (d : Cache) :
    E (run (rest₂ A pk (graph.evalRec ξ) x) (Cache.extend d (kc ξ))) g =
      E (run (signIdx x.1) d) (fun p =>
        E (run (stB A pk x.1 x.2 (sigOf ξ p.1)) (Cache.extend p.2 (kc ξ))) g) := by
  rw [rest₂_eq_signIdx, run_bind, run_signIdx_extend x.1 d (kc ξ) (fun u => kc_enc ξ u),
    bind_map_left, E_bind]

/-- The continuation bound after the first stage. -/
theorem stageA_cont (pk : BitVec 128) (x : Message × A.State) (d : Cache) (b' : ℕ)
    (hI : Inv d b') (hB : ∀ ξ ∈ fiberA pk, CostAtMost (rest₂ A pk (graph.evalRec ξ) x) b') :
    FA A pk x d ≤ ΦA pk d + κ * sumW (fiberA pk) * b' := by
  obtain ⟨T, hTdef⟩ : ∃ T : Finset Rec, T = (fiberA pk).filter (fun ξ => ¬ Cache.Hits d (kc ξ)) :=
    ⟨_, rfl⟩
  have hT : T ⊆ fiberA pk := by
    rw [hTdef]; exact Finset.filter_subset _ _
  have hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ) := by
    intro ξ hξ
    rw [hTdef, Finset.mem_filter] at hξ
    exact hξ.2
  -- Step 1: split `FA` into the records hit by `d` and the others.
  have hsplit : FA A pk x d = ∑ ξ ∈ fiberA pk, w * ind (Cache.Hits d (kc ξ)) +
      ∑ ξ ∈ T, w * E (run (signIdx x.1) d) (fun p =>
        E (run (stB A pk x.1 x.2 (sigOf ξ p.1)) (Cache.extend p.2 (kc ξ))) g) := by
    unfold FA
    rw [hTdef, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    unfold ind
    by_cases h : Cache.Hits d (kc ξ)
    · rw [if_pos h, if_pos h, if_neg (not_not.2 h), add_zero]
    · rw [if_neg h, if_neg h, if_pos h, mul_zero, zero_add, E_rest₂_extend_kc]
  -- Step 2: the signing bound on the records of `T`.
  have hne : Nonempty {ξ // ξ ∈ fiberA pk} := (fiberA_nonempty pk).to_subtype
  have hΦ : EncInvariant (fun c => ∑ ξ ∈ T, w * ind (Spr c ξ)) := by
    intro c u w'
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [spr_cacheQuery_enc c ξ u w']
  have hB' : ∀ j : {ξ // ξ ∈ fiberA pk},
      CostAtMost (signIdx x.1 >>= fun r => stB A pk x.1 x.2 (sigOf j.1 r)) b' := by
    intro j
    have h : CostAtMost (rest₂ A pk (graph.evalRec j.1) x) b' := hB j.1 j.2
    rw [rest₂_eq_signIdx] at h
    exact h
  have hsig : E (run (signIdx x.1) d) (fun p => ∑ ξ ∈ T, w *
        E (run (stB A pk x.1 x.2 (sigOf ξ p.1)) (Cache.extend p.2 (kc ξ))) g) ≤
      ∑ ξ ∈ T, w * ind (Spr d ξ) + sumW T * encTerm d + κ * sumW (fiberA pk) * b' := by
    refine signRho_bound (by decide) (by decide) x.1 d
      (β := Bool) (J := {ξ // ξ ∈ fiberA pk}) (fun j r => stB A pk x.1 x.2 (sigOf j.1 r))
      (fun r d' => ∑ ξ ∈ T, w * E (run (stB A pk x.1 x.2 (sigOf ξ r))
        (Cache.extend d' (kc ξ))) g)
      (fun c => ∑ ξ ∈ T, w * ind (Spr c ξ)) hΦ (κ * sumW (fiberA pk)) (sumW T) (encTerm d)
      Inv Inv_fresh Inv_cached ?_
      (fun c h1 h2 => psi_dom paperRowHyp (two_encCount_le hI) x.1 c h1 h2) hI hB'
    intro r d' b'' hd' hI' hB''
    have hB''' : ∀ ξ ∈ T, CostAtMost (stB A pk x.1 x.2 (sigOf ξ r)) b'' := by
      intro ξ hξ
      exact hB'' ⟨ξ, hT hξ⟩
    refine (stageB A pk x.1 x.2 d T hT hTd r d' hd' b'' hI' hB''').trans ?_
    refine add_le_add (add_le_add ?_ (mul_le_mul_right (le_of_eq (ind_eq_ite_asm _)) _)) le_rfl
    exact Finset.sum_le_sum fun ξ _ => mul_le_mul_right (ind_mono_asm (Spr.mono hd'.1)) w
  -- Step 3: assemble.
  rw [hsplit, sum_mul_E_asm]
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

/-- Key generation as a uniform record, for the concrete scheme. -/
theorem E_run_keygen_forest
    (g' : (PublicKey × forestScheme.graph.Assignment) × Cache → ℝ≥0∞) :
    E (run forestScheme.keygen ∅) g' = ∑ ξ : Rec, w * g' ((pkOf ξ, graph.evalRec ξ), kc ξ) := by
  rw [E_run_keygen forestScheme tagging g']
  show ∑ ξ : Rec, (Fintype.card Rec : ℝ≥0∞)⁻¹ *
    g' ((forestScheme.publicKey (graph.evalRec ξ), graph.evalRec ξ), graph.keygenCache ξ) = _
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [publicKey_eq_pkOf]
  rfl

/-- The experiment as a uniform average over records of the continuation after key generation. -/
theorem E_run_experiment (g' : Bool × Cache → ℝ≥0∞) :
    E (run (experiment forestScheme A) ∅) g' =
      ∑ ξ : Rec, w * E (run (rest A (pkOf ξ, graph.evalRec ξ)) (kc ξ)) g' := by
  rw [experiment_eq]
  have h1 := run_bind forestScheme.keygen (rest A) ∅
  rw [h1, E_bind, E_run_keygen_forest]
  rfl

/-- The budget after key generation, for the concrete scheme. -/
theorem costAtMost_rest_forest {B : ℕ} (hB : CostAtMost (experiment forestScheme A) B) :
    782 ≤ B ∧ ∀ ξ : Rec, CostAtMost (rest A (pkOf ξ, graph.evalRec ξ)) (B - 782) := by
  rw [experiment_eq] at hB
  obtain ⟨h1, h2⟩ := costAtMost_keygen_bind forestScheme (rest A) hB
  refine ⟨?_, fun ξ => ?_⟩
  · have h1' : graph.keygenCost ≤ B := h1
    rwa [graph_keygenCost] at h1'
  · have h2' : CostAtMost (rest A (forestScheme.publicKey (graph.evalRec ξ), graph.evalRec ξ))
        (B - graph.keygenCost) := h2 ξ
    rwa [publicKey_eq_pkOf, graph_keygenCost] at h2'

theorem keygen_le {B : ℕ} (hB : CostAtMost (experiment forestScheme A) B) : 782 ≤ B :=
  (costAtMost_rest_forest A hB).1

theorem main_bound {B : ℕ} (hB : CostAtMost (experiment forestScheme A) B) (hB' : B ≤ 2 ^ 127) :
    probTrue (experiment forestScheme A) ≤ κ * ((B - 782 : ℕ) : ℝ≥0∞) := by
  obtain ⟨h782, hrest⟩ := costAtMost_rest_forest A hB
  rw [probTrue_eq, E_run_experiment]
  calc ∑ ξ : Rec, w * E (run (rest A (pkOf ξ, graph.evalRec ξ)) (kc ξ)) g
      ≤ ∑ ξ : Rec, w * E (run (A.choose (pkOf ξ)) ∅) (fun p =>
          if Cache.Hits p.2 (kc ξ) then 1 else
            E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) g) := by
        gcongr with ξ _
        exact stageA_iub A ξ
    _ = ∑ pk, E (run (A.choose pk) ∅) (fun p => ∑ ξ ∈ fiberA pk, w *
          (if Cache.Hits p.2 (kc ξ) then 1 else
            E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) g)) :=
        regroup A (fun ξ p => if Cache.Hits p.2 (kc ξ) then 1 else
          E (run (rest₂ A (pkOf ξ) (graph.evalRec ξ) p.1) (Cache.extend p.2 (kc ξ))) g)
    _ = ∑ pk, E (run (A.choose pk) ∅) (fun p => FA A pk p.1 p.2) := by
        refine Finset.sum_congr rfl fun pk _ => ?_
        refine congrArg _ (funext fun p => ?_)
        unfold FA
        refine Finset.sum_congr rfl fun ξ hξ => ?_
        rw [mem_fiberA_asm hξ]
    _ ≤ ∑ pk, κ * sumW (fiberA pk) * ((B - 782 : ℕ) : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun pk _ => ?_
        refine stageA_master A pk (B - 782) ((Nat.sub_le B 782).trans hB') fun ξ hξ => ?_
        have h := hrest ξ
        rw [mem_fiberA_asm hξ] at h
        unfold rest at h
        dsimp only at h
        exact h
    _ = κ * ((B - 782 : ℕ) : ℝ≥0∞) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_sumW_fiberA, mul_one]

end Forest

end OptimalOTS
