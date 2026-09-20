import Submissions.LowerGenerality3.AttackR
import Submissions.LowerGenerality3.AttackH
import Submissions.LowerGenerality3.Lonely
import Submissions.LowerGenerality3.Union
import Submissions.LowerGenerality3.Proof

/-!
# No admissible, weakly secure algorithm verifies within one compression

Every honest signature falls into one of six cases (`pointwise`): signing failed; the candidate
is unconditionally accepted (attacker 0); its verification reads a cached point useful for a
second message (attacker R); it reads a key-generation point lonely for the message (at most
`K / 2 ^ 256` over a uniform message); it reads a fresh promising point (attacker H, up to the
factor `1 / τ`); or it reads a fresh non-promising point (the union bound `T τ`). The six masses
add up to less than one, contradicting signing availability.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.LowerGenerality3

variable (S : OracleAlgorithm.Scheme) (hv : S.VerifyCostAtMost 1) (hd : S.VerifyDeterministic)

/-- A short, non-promising, useful point. -/
def P' (pk : PublicKey) (m : Message) (q : Query) (y : BitVec hashBits) : Prop :=
  q.1 ≤ 512 ∧ q ∉ promising S hv hd pk m ∧ Useful S hv hd pk m q y

theorem pr_P'_le (pk : PublicKey) (m : Message) (q : Query) : pr (P' S hv hd pk m) q ≤ τ := by
  rw [← E_P]
  by_cases h : q.1 ≤ 512 ∧ q ∉ promising S hv hd pk m
  · calc _ ≤ E ($ᵗ BitVec hashBits) (fun y => if Useful S hv hd pk m q y then 1 else 0) :=
          E_mono _ fun y => by
            unfold P'
            split_ifs with h1 h2 <;> simp_all
      _ = pm S hv hd pk m q := E_P (Useful S hv hd pk m) q
      _ ≤ τ := (pm_lt_of_not_promising S hv hd h.1 h.2).le
  · have hz : (fun y => if P' S hv hd pk m q y then (1 : ℝ≥0∞) else 0) = fun _ => 0 :=
      funext fun y => by
        rw [if_neg]
        intro hp
        exact h ⟨hp.1, hp.2.1⟩
    rw [hz, E_const]
    exact zero_le

/-- The honest three-stage expectation. -/
def E3 (f : (PublicKey × S.SecretKey) × Cache → Message →
    Option OracleAlgorithm.Signature × Cache → ℝ≥0∞) : ℝ≥0∞ :=
  E (run S.keygen ∅) fun k => E ($ᵗ BitVec msgBits) fun m => E (run (S.sign k.1.2 m) k.2) fun s => f k m s

theorem E3_add (f g) : E3 S (fun k m s => f k m s + g k m s) = E3 S f + E3 S g := by
  unfold E3
  simp only [expectedValue_add]

theorem E3_const (v : ℝ≥0∞) : E3 S (fun _ _ _ => v) = v := by
  unfold E3
  simp only [E_const]

theorem E3_mono {f g} (h : ∀ k ∈ support (run S.keygen ∅), ∀ m,
    ∀ s ∈ support (run (S.sign k.1.2 m) k.2), f k m s ≤ g k m s) : E3 S f ≤ E3 S g := by
  unfold E3
  apply expectedValue_mono_of_support
  intro k hk
  apply E_mono
  intro m
  apply expectedValue_mono_of_support
  intro s hs
  exact h k hk m s hs

/-- Swapping key generation and the uniform message. -/
theorem E_swap {α : Type} (p : ProbComp α) (n : ℕ) (g : α → BitVec n → ℝ≥0∞) :
    E p (fun k => E ($ᵗ BitVec n) (fun m => g k m)) = E ($ᵗ BitVec n) (fun m => E p (fun k => g k m)) := by
  simp only [E_uniform]
  show expectedValue p (fun k => ∑ m, (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * g k m) = _
  rw [expectedValue_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (fun k => (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * g k m) =
      fun k => g k m * (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ := funext fun k => mul_comm _ _
  show expectedValue p (fun k => (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * g k m) =
    (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * expectedValue p (fun k => g k m)
  rw [this, expectedValue_mul_const, mul_comm]

abbrev ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

theorem one_le_sum6 {a b c d e f : ℝ≥0∞}
    (h : a = 1 ∨ b = 1 ∨ c = 1 ∨ d = 1 ∨ e = 1 ∨ f = 1) : 1 ≤ a + b + c + d + e + f := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact le_add_right (le_add_right (le_add_right (le_add_right (le_add_right le_rfl))))
  · exact le_add_right (le_add_right (le_add_right (le_add_right le_add_self)))
  · exact le_add_right (le_add_right (le_add_right le_add_self))
  · exact le_add_right (le_add_right le_add_self)
  · exact le_add_right le_add_self
  · exact le_add_self

/-- The six-way case split on an honest history. -/
theorem pointwise (hc : S.Correct) (k : (PublicKey × S.SecretKey) × Cache)
    (hk : k ∈ support (run S.keygen ∅)) (m : Message) (s : Option OracleAlgorithm.Signature × Cache)
    (hs : s ∈ support (run (S.sign k.1.2 m) k.2)) :
    1 ≤ (if s.1.isNone then (1 : ℝ≥0∞) else 0) + ind (Good0 S hv hd k.1.1 m) + ind (GR S hv hd k.1.1 m s) +
      ind (LonelyKey S hv hd k.1.1 k.2 m) +
      ind (Dec k.2 (Useful S hv hd k.1.1 m) (promising S hv hd k.1.1 m) s.2) +
      badInd k.2 (P' S hv hd k.1.1 m) s.2 := by
  apply one_le_sum6
  rcases s with ⟨σ?, c⟩
  cases σ? with
  | none => left; simp
  | some σ =>
    have hsub : Cache.Sub k.2 c := sub_of_mem_support_run _ _ _ hs
    rcases honest_cached_or_uncond S hc hv hd m k hk σ c hs with hu | ⟨q, f, y, hsh, hcq, hf⟩
    · have : Good0 S hv hd k.1.1 m := ⟨σ, hu⟩
      right; left; simp [this]
    · have hus : Useful S hv hd k.1.1 m q y := useful_of_shape S hv hd hsh hf
      rcases lonely_or_shared S hv hd hus with hl | hsh'
      · rcases hk2 : k.2 q with _ | y'
        · by_cases hp : q ∈ promising S hv hd k.1.1 m
          · have : Dec k.2 (Useful S hv hd k.1.1 m) (promising S hv hd k.1.1 m) c :=
              ⟨q, hp, hk2, y, hcq, hus⟩
            right; right; right; right; left; simp [this]
          · have : Bad k.2 (P' S hv hd k.1.1 m) c :=
              ⟨q, y, hk2, hcq, shape_short S hv hd k.1.1 m σ q f hsh, hp, hus⟩
            right; right; right; right; right; simp [badInd, this]
        · have hy : y' = y := by
            have := hsub q y' hk2
            rw [hcq] at this
            exact (Option.some.inj this).symm
          subst hy
          have : LonelyKey S hv hd k.1.1 k.2 m := ⟨q, y', hk2, hl⟩
          right; right; right; left; simp [this]
      · have : GR S hv hd k.1.1 m (some σ, c) := ⟨q, f, y, hsh, hcq, hf, hsh'⟩
        right; right; left; simp [this]

theorem badInd_base (c₀ : Cache) (P : Query → BitVec hashBits → Prop) : badInd c₀ P c₀ = 0 := by
  unfold badInd
  rw [if_neg]
  rintro ⟨q, y, h0, hy, -⟩
  rw [h0] at hy
  cases hy

/-- The gap: the six masses are below one. -/
theorem masses_lt_one :
    (1 / 2 ^ signingFailureBits : ℝ≥0∞) +
      ((keygenBudget + signBudget + 1 : ℕ) : ℝ≥0∞) / 2 ^ securityBits +
      ((keygenBudget + signBudget + 2 : ℕ) : ℝ≥0∞) / 2 ^ securityBits +
      (keygenBudget : ℝ≥0∞) / 2 ^ msgBits +
      2 ^ 25 * (((2 * keygenBudget + signBudget + 2 : ℕ) : ℝ≥0∞) / 2 ^ securityBits) +
      1 / 2 ^ 25 * (signBudget : ℕ) < 1 := by
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num [signingFailureBits, keygenBudget, signBudget, securityBits, msgBits]

theorem card_msg : (Fintype.card (BitVec msgBits) : ℝ≥0∞) = 2 ^ msgBits := by
  rw [Fintype.card_bitVec]
  norm_num

theorem tau_inv : τ⁻¹ = 2 ^ 25 := by rw [τ, one_div, inv_inv]

/-- No admissible, weakly secure algorithm verifies within one compression. -/
theorem no_one_verifier (hA : S.Admissible) (hsec : S.WeaklySecure) : ¬ S.VerifyCostAtMost 1 := by
  intro hv
  have hd := hA.verifyDeterministic
  have hk := hA.keygenCost
  have hs := hA.signCost
  set K := keygenBudget with hK
  set T := signBudget with hT
  -- the six masses
  have h1 : E3 S (fun _ _ s => (if s.1.isNone then (1 : ℝ≥0∞) else 0)) ≤ 1 / 2 ^ signingFailureBits := by
    unfold E3
    dsimp only
    rw [E_swap]
    calc _ ≤ E ($ᵗ BitVec msgBits) (fun _ => (1 / 2 ^ signingFailureBits : ℝ≥0∞)) :=
          E_mono _ fun m => failure_expanded S hA.signingFailure m
      _ = _ := E_const _ _
  have h2 : E3 S (fun k m _ => ind (Good0 S hv hd k.1.1 m)) ≤ ((K + T + 1 : ℕ) : ℝ≥0∞) / 2 ^ securityBits := by
    unfold E3
    dsimp only
    simp only [E_const]
    exact (success0 S hv hd).trans (hsec _ _ (cost0 S hv hd hk hs)).le
  have h3 : E3 S (fun k m s => ind (GR S hv hd k.1.1 m s)) ≤ ((K + T + 2 : ℕ) : ℝ≥0∞) / 2 ^ securityBits :=
    (successR S hv hd).trans (hsec _ _ (costR S hv hd hk hs)).le
  have h4 : E3 S (fun k m _ => ind (LonelyKey S hv hd k.1.1 k.2 m)) ≤
      (K : ℝ≥0∞) * (Fintype.card (BitVec msgBits) : ℝ≥0∞)⁻¹ := by
    unfold E3
    dsimp only
    simp only [E_const]
    calc _ ≤ E (run S.keygen ∅) (fun _ => (K : ℝ≥0∞) * (Fintype.card (BitVec msgBits) : ℝ≥0∞)⁻¹) := by
          apply expectedValue_mono_of_support
          intro k hkm
          obtain ⟨D, hD, hDc⟩ := exists_support_run_empty hk k hkm
          calc _ ≤ (D.card : ℝ≥0∞) * (Fintype.card (BitVec msgBits) : ℝ≥0∞)⁻¹ := E_lonelyKey_le S hv hd hD k.1.1
            _ ≤ _ := mul_le_mul' (by exact_mod_cast hDc) le_rfl
      _ = _ := E_const _ _
  have h5 : E3 S (fun k m s => ind (Dec k.2 (Useful S hv hd k.1.1 m) (promising S hv hd k.1.1 m) s.2)) ≤
      τ⁻¹ * (((2 * K + T + 2 : ℕ) : ℝ≥0∞) / 2 ^ securityBits) := by
    unfold E3
    dsimp only
    calc _ ≤ E (run S.keygen ∅) (fun k => E ($ᵗ BitVec msgBits) (fun m => τ⁻¹ * hTerm S hv hd K k m)) := by
          apply expectedValue_mono_of_support
          intro k hkm
          apply E_mono
          intro m
          exact (E_dec_le k.2 (Useful S hv hd k.1.1 m) (promising S hv hd k.1.1 m) _).trans
            (dec_le_hTerm S hv hd hk k hkm m)
      _ = τ⁻¹ * E (run S.keygen ∅) (fun k => E ($ᵗ BitVec msgBits) (fun m => hTerm S hv hd K k m)) := by
          have e1 : ∀ k, E ($ᵗ BitVec msgBits) (fun m => τ⁻¹ * hTerm S hv hd K k m) =
              E ($ᵗ BitVec msgBits) (fun m => hTerm S hv hd K k m) * τ⁻¹ := fun k => by
            rw [← expectedValue_mul_const]
            congr 1
            funext m
            exact mul_comm _ _
          simp only [e1]
          show expectedValue (run S.keygen ∅) (fun k => E ($ᵗ BitVec msgBits) (fun m => hTerm S hv hd K k m) * τ⁻¹) = _
          rw [expectedValue_mul_const, mul_comm]
      _ ≤ τ⁻¹ * (((2 * K + T + 2 : ℕ) : ℝ≥0∞) / 2 ^ securityBits) :=
          mul_le_mul' le_rfl ((successH S hv hd K).trans (hsec _ _ (costH S hv hd hk hs)).le)
  have h6 : E3 S (fun k m s => badInd k.2 (P' S hv hd k.1.1 m) s.2) ≤ τ * (T : ℕ) := by
    unfold E3
    dsimp only
    calc _ ≤ E (run S.keygen ∅) (fun k => E ($ᵗ BitVec msgBits) (fun m => (0 : ℝ≥0∞) + τ * (T : ℕ))) := by
          apply E_mono
          intro k
          apply E_mono
          intro m
          have := E_bad_le k.2 (P' S hv hd k.1.1 m) (pr_P'_le S hv hd k.1.1 m) (S.sign k.1.2 m) T k.2 (hs _ _)
          rwa [badInd_base] at this
      _ = _ := by simp only [zero_add, E_const]
  -- the total
  have htot : (1 : ℝ≥0∞) ≤ E3 S (fun _ _ s => (if s.1.isNone then (1 : ℝ≥0∞) else 0)) + E3 S (fun k m _ => ind (Good0 S hv hd k.1.1 m)) +
      E3 S (fun k m s => ind (GR S hv hd k.1.1 m s)) + E3 S (fun k m _ => ind (LonelyKey S hv hd k.1.1 k.2 m)) +
      E3 S (fun k m s => ind (Dec k.2 (Useful S hv hd k.1.1 m) (promising S hv hd k.1.1 m) s.2)) +
      E3 S (fun k m s => badInd k.2 (P' S hv hd k.1.1 m) s.2) := by
    calc (1 : ℝ≥0∞) = E3 S (fun _ _ _ => 1) := (E3_const S 1).symm
      _ ≤ E3 S (fun k m s => (if s.1.isNone then (1 : ℝ≥0∞) else 0) + ind (Good0 S hv hd k.1.1 m) +
            ind (GR S hv hd k.1.1 m s) + ind (LonelyKey S hv hd k.1.1 k.2 m) +
            ind (Dec k.2 (Useful S hv hd k.1.1 m) (promising S hv hd k.1.1 m) s.2) +
            badInd k.2 (P' S hv hd k.1.1 m) s.2) :=
          E3_mono S fun k hk m s hs => pointwise S hv hd hA.correct k hk m s hs
      _ = _ := by rw [E3_add, E3_add, E3_add, E3_add, E3_add]
  rw [card_msg, ← div_eq_mul_inv] at h4
  rw [tau_inv] at h5
  rw [τ] at h6
  have hsum := htot.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6)
  exact absurd (hsum.trans_lt masses_lt_one) (lt_irrefl _)

/-- Every admissible, secure algorithm needs a verification budget of at least two
compressions. -/
theorem paper_lowerBound_two : LowerBoundGenerality3 2 := by
  intro S hA hS v hv
  by_contra h
  have hv1 : S.VerifyCostAtMost 1 := fun pk m σ => Costs.CostAtMost.mono (hv pk m σ) (by omega)
  exact no_one_verifier S hA hS.weaklySecure hv1

end OptimalOTS.LowerGenerality3
