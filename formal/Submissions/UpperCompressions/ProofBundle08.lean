import Submissions.UpperCompressions.ProofBundle07
import Submissions.UpperCompressions.ProofBundle06
import Submissions.UpperCompressions.ProofBundle02

section

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS OptimalOTS.WeightedSampling
noncomputable section
open scoped Classical
namespace WeightedCompletion
open WeightedReplacement

/-- Exact arbitrary nonnegative payoff under the actual all-trials oracle loop,
once its shared oracle row is fixed. Failure has payoff zero. -/
theorem E_loop_fixed_row_score (n M k : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (table : Nonce n → BitVec hashBits) (c : Cache)
    (hc : ∀ η, c ⟨msgBits+n,m++η⟩ = some (table η))
    (f : Nonce n → Fin M → ℝ) (hf : ∀ a i, 0 ≤ f a i) :
    E (run (loop n decode tier m k) c)
      (fun p => ENNReal.ofReal (score p.1 (fun r => f r.1 r.2))) =
      ENNReal.ofReal (tableKernel k (decode ∘ table) tier f) := by
  rw [run_loop_fixed_row n decode tier m table c hc, E_map]
  have hn : ∀ xs : List (Nonce n),
      0 ≤ score (selected (decode ∘ table) tier xs) (fun r => f r.1 r.2) := by
    intro xs
    cases selected (decode ∘ table) tier xs with
    | none => exact le_rfl
    | some r => exact hf r.1 r.2
  have h := E_drawList_ofReal n k
    (fun xs => score (selected (decode ∘ table) tier xs) (fun r => f r.1 r.2)) hn
  rw [iid_selected_score] at h
  exact h

end WeightedCompletion
end
end

section

/-! Integrate the exact first-minimum kernel with unconditional row completion.
This supplies replay and excess bounds from the pointwise kernel envelope, with
no conditioning on the good-table event. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {Ω D I : Type} [Fintype Ω] [Nonempty Ω] [Fintype D] [Nonempty D]
  [Fintype I] [DecidableEq D] [DecidableEq I]

theorem tableKernel_reference_le (n : ℕ) (R : Finset D)
    (table : Ω → D → Option I) (tier : I → ℕ) (p g fKnown fFresh : I → ℝ)
    (hK : ∀ i, 0 ≤ fKnown i) (hF : ∀ i, 0 ≤ fFresh i) (F : ℝ) (ω : Ω)
    (hk : ∀ i, kernel n (fraction (weakRank tier i ∘ table ω))
      (fraction (strictRank tier i ∘ table ω)) ≤ F * (g i / p i)) :
    tableKernel n (table ω) tier (fun a i => if a ∈ R then fKnown i else fFresh i) ≤
      F * referencePayoff R table p g fKnown fFresh ω := by
  unfold tableKernel referencePayoff
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro a _
  cases ht : table ω a with
  | none => simp [score, ht]
  | some i =>
    simp only [score, ht, Option.map_some, Option.getD_some]
    by_cases ha : a ∈ R
    · rw [if_pos ha, if_pos ha]
      exact (mul_le_mul_of_nonneg_right (hk i) (hK i)).trans_eq (by ring)
    · rw [if_neg ha, if_neg ha]
      exact (mul_le_mul_of_nonneg_right (hk i) (hF i)).trans_eq (by ring)

/-- Actual first-minimum replay probability, averaged over the original table
completion law, is bounded by the clipped public replay hazard plus the bad tail. -/
theorem replay_kernel_bound (w : WeightedRow.Weights I) (n : ℕ) (tier : I → ℕ)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I) (k : I → ℕ)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (Good : Ω → Prop) (F δ : ℝ) (hF : 0 ≤ F)
    (hkernel : ∀ ω, Good ω → ∀ i, kernel n
      (fraction (weakRank tier i ∘ table ω)) (fraction (strictRank tier i ∘ table ω)) ≤
        F * (w.g i / w.p i))
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean (fun ω => tableKernel n (table ω) tier (fun a i =>
      if a ∈ R then (if 2 ≤ k i then 1 else 0) else (if k i = 0 then 0 else 1))) ≤
      F * w.hazard (Fintype.card D) R.card k (rowCount R fixed) + δ := by
  apply replay_bound w R fixed table k hknown hfresh Good _ F δ hF
  · intro ω hg
    exact tableKernel_reference_le n R table tier w.p w.g _ _
      (fun i => by split_ifs <;> norm_num) (fun i => by split_ifs <;> norm_num) F ω (hkernel ω hg)
  · intro ω
    apply tableKernel_le n (table ω) tier _ 1 zero_le_one
    intro a i
    split_ifs <;> norm_num
  · exact hbad

/-- Post-sign excess payoff for the same actual selector and completion law. -/
theorem excess_kernel_bound (w : WeightedRow.Weights I) (n : ℕ) (tier : I → ℕ)
    (R : Finset D) (fixed : D → Option I) (table : Ω → D → Option I)
    (hknown : ∀ ω a, a ∈ R → table ω a = fixed a)
    (hfresh : ∀ a, a ∉ R → ∀ i,
      uniformMean (fun ω => if table ω a = some i then 1 else 0) = w.p i)
    (e : I → ℝ) (he : ∀ i, 0 ≤ e i) (emax : ℝ) (hemax : 0 ≤ emax) (hesc : ∀ i, e i ≤ emax)
    (Good : Ω → Prop) (F δ : ℝ) (hF : 0 ≤ F)
    (hkernel : ∀ ω, Good ω → ∀ i, kernel n
      (fraction (weakRank tier i ∘ table ω)) (fraction (strictRank tier i ∘ table ω)) ≤
        F * (w.g i / w.p i))
    (hbad : uniformMean (fun ω => if Good ω then 0 else 1) ≤ δ) :
    uniformMean (fun ω => tableKernel n (table ω) tier (fun _ i => e i)) ≤
      F * ((1-(R.card : ℝ)/Fintype.card D) * (∑ i, w.g i * e i) +
        (∑ i, (rowCount R fixed i : ℝ) * (w.g i/w.p i * e i)) / Fintype.card D) + emax * δ := by
  apply excess_bound w R fixed table hknown hfresh e he Good _ F emax δ hF hemax
  · intro ω hg
    simpa only [ite_self] using
      tableKernel_reference_le n R table tier w.p w.g e e he he F ω (hkernel ω hg)
  · intro ω
    exact tableKernel_le n (table ω) tier (fun _ i => e i) emax hemax (fun _ i => hesc i)
  · exact hbad

end WeightedCompletion
end
end

section

/-! Literal uniform-table completion has the unconditional one-coordinate
marginals required by the replay/excess formulas. -/
noncomputable section
open scoped BigOperators Classical
namespace WeightedCompletion
open WeightedReplacement
variable {D W I : Type} [Fintype D] [Fintype W] [Nonempty W] [DecidableEq D] [DecidableEq I]

theorem uniformMean_coordinate (a : D) (f : W → ℝ) :
    uniformMean (fun g : D → W => f (g a)) = uniformMean f := by
  have h : uniformMean (fun g : D → W => ∏ d, (if d = a then f (g d) else 1)) =
      ∏ d : D, uniformMean (fun x : W => if d = a then f x else 1) := by
    simp only [uniformMean, Fintype.card_fun, Nat.cast_pow]
    rw [← Fintype.prod_sum (f := fun d : D => fun x : W => if d = a then f x else 1),
      Finset.prod_div_distrib]
    simp
  have hm (d : D) : uniformMean (fun x : W => if d = a then f x else 1) =
      if d = a then uniformMean f else 1 := by
    by_cases hd : d = a <;> simp only [hd, if_true, if_false, uniformMean_const]
  simpa only [hm, Finset.prod_ite_eq', Finset.mem_univ, if_true] using h

theorem uniformMean_indicator (p : W → Prop) [DecidablePred p] :
    uniformMean (fun x => if p x then 1 else 0) =
      ((Finset.univ.filter p).card : ℝ) / Fintype.card W := by
  unfold uniformMean
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end WeightedCompletion

end
end

section

/-! The all-trial signer reserves its entire paid query budget on every
raw answer path. These are resource statements, not probabilistic claims. -/

open OracleSpec OracleComp
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedSampling

variable {M : ℕ}

theorem loop_step_budget {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (k : ℕ) (kont : Option (Winner n M) → OracleComp Spec β)
    (hc : blockCost (msgBits+n) = 1) {b : ℕ}
    (hB : CostAtMost (loop n decode tier m (k+1) >>= kont) b) :
    1 ≤ b ∧ ∀ η w, CostAtMost
      (loop n decode tier m k >>= fun r =>
        kont (best (fun s => tier s.2) (candidate decode η w) r)) (b-1) := by
  rw [loop,bind_assoc,sampleBits] at hB
  have hη := costAtMost_liftM_bind _ _ hB
  have hη' (η : Nonce n) := hη η (by simp)
  have hw (η : Nonce n) : 1 ≤ b ∧ ∀ w, CostAtMost
      (loop n decode tier m k >>= fun r =>
        kont (best (fun s => tier s.2) (candidate decode η w) r)) (b-1) := by
    have hx := hη' η
    rw [bind_assoc,hash,costAtMost_query_bind_iff] at hx
    change blockCost (msgBits+n) ≤ b ∧ ∀ w : BitVec hashBits,
      CostAtMost ((loop n decode tier m k >>= fun r =>
        pure (best (fun s => tier s.2) (candidate decode η w) r)) >>= kont)
        (b-blockCost (msgBits+n)) at hx
    simpa only [hc,bind_assoc,pure_bind] using hx
  exact ⟨(hw 0).1,fun η => (hw η).2⟩

/-- All L hashes are paid before any outcome-dependent continuation.
The guarantee holds for every syntactically possible output, so it also
covers outcomes of a single consistent random oracle. -/
theorem loop_reserve {β : Type} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ)
    (m : Message) (hc : blockCost (msgBits+n) = 1) :
    ∀ k (kont : Option (Winner n M) → OracleComp Spec β) b,
      CostAtMost (loop n decode tier m k >>= kont) b →
      k ≤ b ∧ ∀ r ∈ support (loop n decode tier m k),
        CostAtMost (kont r) (b-k) := by
  intro k
  induction k with
  | zero =>
    intro kont b hB
    rw [loop,pure_bind] at hB
    refine ⟨Nat.zero_le _, ?_⟩
    intro r hr
    simp only [loop,support_pure,Set.mem_singleton_iff] at hr
    subst r
    simpa using hB
  | succ k ih =>
    intro kont b hB
    obtain ⟨hb,hs⟩ := loop_step_budget n decode tier m k kont hc hB
    have hi (η : Nonce n) (w : BitVec hashBits) := ih
      (fun r => kont (best (fun s => tier s.2) (candidate decode η w) r))
      (b-1) (hs η w)
    have hk := (hi 0 0).1
    refine ⟨by omega, ?_⟩
    intro r hr
    rw [loop,support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨η,_,hr⟩ := hr
    rw [support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨w,_,hr⟩ := hr
    rw [support_bind] at hr
    simp only [Set.mem_iUnion] at hr
    obtain ⟨s,hs,hr⟩ := hr
    rw [support_pure,Set.mem_singleton_iff] at hr
    subst r
    have hkont := (hi η w).2 s hs
    simpa only [Nat.sub_sub,show 1+k=k+1 by omega] using hkont

end OptimalOTS.WeightedSampling
end
end
