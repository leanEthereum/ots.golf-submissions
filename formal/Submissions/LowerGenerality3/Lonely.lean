import Submissions.LowerGenerality3.Support

/-!
# Lonely key-generation points

A cached point useful for exactly one message is `Lonely` for it. Over a uniform message, the
chance that some point of a cache with at most `n` entries is lonely for the message is at most
`n / 2 ^ msgBits` (`E_lonelyKey_le`).
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

attribute [local irreducible] hashBits blockBits pkBits securityBits maxSignatureBits keygenBudget signBudget

variable (S : OracleAlgorithm.Scheme) (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic)

/-- Some entry of the cache is lonely for `m`. -/
def LonelyKey (pk : PublicKey) (c₀ : Cache) (m : Message) : Prop :=
  ∃ q y, c₀ q = some y ∧ Lonely S hv hd pk m q y

/-- The entry at `q` is lonely for `m`. -/
def LonelyAt (pk : PublicKey) (c₀ : Cache) (q : Query) (m : Message) : Prop :=
  ∃ y, c₀ q = some y ∧ Lonely S hv hd pk m q y

/-- A uniform draw lands on a property with at most one witness with probability at most the
inverse cardinality. -/
theorem E_uniform_unique {n : ℕ} (P : BitVec n → Prop) (h : ∀ a b, P a → P b → a = b) :
    E ($ᵗ BitVec n) (fun x => if P x then 1 else 0) ≤ (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ := by
  rw [E_uniform]
  by_cases hex : ∃ a, P a
  · obtain ⟨a, ha⟩ := hex
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      have : ¬ P b := fun hpb => hb (h b a hpb ha)
      simp [this]
    · intro ha'; exact absurd (Finset.mem_univ a) ha'
  · push_neg at hex
    simp [hex]

theorem lonely_unique {pk : PublicKey} {q : Query} {y : BitVec hashBits} {m m' : Message}
    (h : Lonely S hv hd pk m q y) (h' : Lonely S hv hd pk m' q y) : m = m' :=
  h'.2 m h.1

theorem E_lonelyKey_le {c₀ : Cache} {D : Finset Query} (hD : HasSupport c₀ D) (pk : PublicKey) :
    E ($ᵗ BitVec msgBits) (fun m => if LonelyKey S hv hd pk c₀ m then 1 else 0) ≤
      D.card * (Fintype.card (BitVec msgBits) : ℝ≥0∞)⁻¹ := by
  have hpt : ∀ m, (if LonelyKey S hv hd pk c₀ m then (1 : ℝ≥0∞) else 0) ≤
      ∑ q ∈ D, (if LonelyAt S hv hd pk c₀ q m then 1 else 0) := by
    intro m
    split_ifs with h
    · obtain ⟨q, y, hq, hl⟩ := h
      have hqD : q ∈ D := hD q (by rw [hq]; rfl)
      calc (1 : ℝ≥0∞) = (if LonelyAt S hv hd pk c₀ q m then 1 else 0) := by
            rw [if_pos ⟨y, hq, hl⟩]
        _ ≤ _ := Finset.single_le_sum (f := fun q => if LonelyAt S hv hd pk c₀ q m then (1 : ℝ≥0∞) else 0)
            (fun _ _ => zero_le) hqD
    · exact zero_le
  calc _ ≤ E ($ᵗ BitVec msgBits) (fun m =>
        ∑ q ∈ D, (if LonelyAt S hv hd pk c₀ q m then 1 else 0)) := E_mono _ hpt
    _ = ∑ q ∈ D, E ($ᵗ BitVec msgBits) (fun m => if LonelyAt S hv hd pk c₀ q m then 1 else 0) := by
        simp only [E_uniform, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ _q ∈ D, (Fintype.card (BitVec msgBits) : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun q _ => E_uniform_unique (LonelyAt S hv hd pk c₀ q) ?_
        rintro a b ⟨y, hy, ha⟩ ⟨y', hy', hb⟩
        rw [hy] at hy'
        cases hy'
        exact lonely_unique S hv hd ha hb
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end OptimalOTS.LowerGenerality3
