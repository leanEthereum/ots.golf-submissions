import Submissions.UpperLeanIsa.TierPotential

/-! A linear pre-sign potential for the nonce128/index127 construction.

Inspired by the joint G+Z accounting in lucemans' verified 1115 submission
(42ba840b74994a32a018bc391fc954e5b801e8eb). Here the nonce row is twice the
index space, so even weight-one classes cover the entire collision increment.
This helper does not change Solution.lean or claim a new machine certificate.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option Elab.async false

namespace OptimalOTS.LeanIsaBaseline.Layer.Params

attribute [local irreducible] hashBits msgBits pkBits trials

variable {P : Params} {S : Tier.Sched}

theorem linear_one_le_weight {v : Cls} (hv : v ∈ P.classes) : 1 ≤ P.cweight v := by
  obtain ⟨I, hI, rfl⟩ := P.mem_classes.1 hv
  change 1 ≤ (Finset.univ.filter fun J : Index => P.Accepted J ∧ P.digit J = P.digit I).card
  exact Finset.one_le_card.2 ⟨I, Finset.mem_filter.2 ⟨Finset.mem_univ _, hI, rfl⟩⟩

/-- The factor two is the full nonce bit, not an asymptotic approximation. -/
theorem linear_gbar_eq (v : Cls) :
    P.gbar S v = 2 * (P.cweight v : ℝ≥0∞) * zT S (P.ctier S v) := by
  have h : (2 : ℝ≥0∞) ^ 128 * (2 ^ 127)⁻¹ = 2 := by
    rw [show (128 : ℕ) = 127 + 1 from rfl, pow_succ, mul_right_comm,
      ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]
  rw [gbar, cIE_eq_mul, pC, zT, div_eq_mul_inv]
  calc 2 ^ 128 * ILinv * (P.cweight v * (2 ^ 127)⁻¹) * S.wbar (P.ctier S v)
      = (2 ^ 128 * (2 ^ 127)⁻¹) * P.cweight v * (S.wbar (P.ctier S v) * ILinv) := by ring
    _ = _ := by rw [h]

theorem linear_Gp_fresh {c : Cache} {u₀ : EncInput}
    (hq : c (P.encQuery u₀) = none) (w : BitVec hashBits) :
    P.Gp S (c.cacheQuery (P.encQuery u₀) w) ≤ P.Gp S c +
      (P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 0 else P.gbar S v) := by
  rcases ho : P.cls w with _ | i
  · rw [Gp, Gp, Vc_congr (cls_cq_none hq w ho)]
    exact le_self_add
  · have hsub : P.Vc (c.cacheQuery (P.encQuery u₀) w) ⊆ insert i (P.Vc c) := by
      intro v hv
      obtain ⟨u, hu⟩ := mem_Vc.1 hv
      by_cases h : u = u₀
      · rw [h, cls_cq_self, ho] at hu
        exact Finset.mem_insert.2 (Or.inl (Option.some.inj hu).symm)
      · rw [cls_cq_ne w h] at hu
        exact Finset.mem_insert_of_mem (mem_Vc.2 ⟨u, hu⟩)
    refine (Finset.sum_le_sum_of_subset hsub).trans ?_
    rw [Option.elim_some, Gp]
    by_cases hi : i ∈ P.Vc c
    · rw [Finset.insert_eq_of_mem hi, if_pos hi, add_zero]
    · rw [Finset.sum_insert hi, if_neg hi, add_comm]

theorem linear_surplus (held : Prop) [Decidable held] {a : ℕ} (ha : 1 ≤ a)
    (z : ℝ≥0∞) :
    (if held then 0 else 2 * (a : ℝ≥0∞) * z) + (if held then 2 * z else 0) ≤
      2 * (a : ℝ≥0∞) * z := by
  by_cases h : held
  · rw [if_pos h, if_pos h, zero_add]
    have hcast : (1 : ℝ≥0∞) ≤ a := by exact_mod_cast ha
    calc 2 * z = (2 * 1) * z := by rw [mul_one]
      _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hcast) le_rfl
  · rw [if_neg h, if_neg h, add_zero]

attribute [local irreducible] cweight classes Gp Zp Yp gbar zT Vc

theorem linear_class_dominates {v : Cls} (hv : v ∈ P.classes) :
    2 * zT S (P.ctier S v) ≤ P.gbar S v := by
  rw [linear_gbar_eq]
  have ha : 1 ≤ P.cweight v := linear_one_le_weight (P:=P) (v:=v) hv
  have hc : (1 : ℝ≥0∞) ≤ P.cweight v := by
    simpa only [Nat.cast_one] using (Nat.cast_le (α:=ℝ≥0∞)).2 ha
  calc 2 * zT S (P.ctier S v) = (2 * 1) * zT S (P.ctier S v) := by rw [mul_one]
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hc) le_rfl

theorem linear_option_increment {α : Type} (o : Option α) (held : α → Prop)
    [DecidablePred held] (f z : α → ℝ≥0∞)
    (cover : ∀ i, o = some i → 2 * z i ≤ f i) :
    o.elim 0 (fun i => if held i then 0 else f i) +
      o.elim 0 (fun i => if held i then 2 * z i else 0) ≤ o.elim 0 f := by
  cases o with
  | none => simp only [Option.elim_none, add_zero, le_refl]
  | some i =>
    simp only [Option.elim_some]
    by_cases h : held i
    · simpa only [h, if_true, zero_add] using cover i rfl
    · simp only [h, if_false, add_zero, le_refl]

/-- Pointwise accounting, stated without any cache-update inequalities. -/
theorem linear_increment_le (c : Cache) (w : BitVec hashBits) :
    ((P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 0 else P.gbar S v) +
     (P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 2 * zT S (P.ctier S v) else 0)) ≤
      (P.cls w).elim 0 (P.gbar S) := by
  exact linear_option_increment (P.cls w) (fun v => v ∈ P.Vc c) (P.gbar S)
    (fun v => zT S (P.ctier S v)) (fun v hv =>
      linear_class_dominates (P:=P) (S:=S) (v:=v)
        (cls_mem_classes (P:=P) (w:=w) (v:=v) hv))

/-- Duplicate answers incur no additional budget-dependent surplus. -/
theorem linear_GZ_fresh {c : Cache} {u₀ : EncInput}
    (hq : c (P.encQuery u₀) = none) (w : BitVec hashBits) :
    P.Gp S (c.cacheQuery (P.encQuery u₀) w) + P.Zp S (c.cacheQuery (P.encQuery u₀) w) ≤
      P.Gp S c + P.Zp S c + (P.cls w).elim 0 (P.gbar S) := by
  have hg := linear_Gp_fresh (P:=P) (S:=S) hq w
  have hz := Zp_cacheQuery (P:=P) (S:=S) hq w
  calc P.Gp S (c.cacheQuery (P.encQuery u₀) w) + P.Zp S (c.cacheQuery (P.encQuery u₀) w)
      ≤ (P.Gp S c + (P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 0 else P.gbar S v)) +
        (P.Zp S c + (P.cls w).elim 0
          (fun v => if v ∈ P.Vc c then 2 * zT S (P.ctier S v) else 0)) :=
      add_le_add hg hz
    _ = P.Gp S c + P.Zp S c +
        ((P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 0 else P.gbar S v) +
         (P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 2 * zT S (P.ctier S v) else 0)) :=
      add_add_add_comm _ _ _ _
    _ ≤ P.Gp S c + P.Zp S c + (P.cls w).elim 0 (P.gbar S) := by
      exact add_le_add le_rfl (linear_increment_le (P:=P) (S:=S) c w)

/-- The budget-independent potential. -/
def LinearPre (P : Params) (S : Tier.Sched) (c : Cache) : ℝ≥0∞ :=
  P.Gp S c + P.Zp S c + P.Yp S c

/-- The drift needs only analytic conditions, not a quadratic budget. -/
theorem linear_pre_drift (hS : S.Analytic) (hT : P.TierHyp S)
    {c : Cache} {u₀ : EncInput} (hq : c (P.encQuery u₀) = none) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      P.LinearPre S (c.cacheQuery (P.encQuery u₀) w) ≤
    P.LinearPre S c + S.hpE := by
  set K := (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹
  have hpt : ∀ w : BitVec hashBits,
      P.LinearPre S (c.cacheQuery (P.encQuery u₀) w) ≤
      P.LinearPre S c + ((P.cls w).elim 0 (P.gbar S) + (P.cls w).elim 0 (P.sC S)) := by
    intro w
    exact (add_le_add (linear_GZ_fresh hq w) (Yp_cacheQuery hq w).le).trans
      (le_of_eq (by unfold LinearPre; ring))
  calc _ ≤ ∑ w, K * (P.LinearPre S c +
        ((P.cls w).elim 0 (P.gbar S) + (P.cls w).elim 0 (P.sC S))) :=
      Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl (hpt w)
    _ = P.LinearPre S c + (Tier.cIE * ∑ t ∈ Finset.range S.T,
        (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.wbar t +
        ILinv * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t) := by
      have hK : ∀ a, ∑ _w : BitVec hashBits, K * a = a := fun a => sum_inv_card_mul a
      simp only [mul_add, Finset.sum_add_distrib, hK]
      rw [avg_Gp hS hT, avg_Yp hS hT]
    _ ≤ P.LinearPre S c + S.hpE := by
      apply add_le_add le_rfl
      apply le_trans _ (S.Hprime_le hS)
      apply add_le_add
      · gcongr; exact S.sum_wbar_le hS
      · calc ILinv * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t
            ≤ ILinv * ((2 ^ 19 - 1) * ENNReal.ofReal S.SCsum) := by
              gcongr; exact S.sum_sck_le hS
          _ ≤ Tier.cIE ^ 2 * ((2 ^ 19 - 1) * ENNReal.ofReal S.SCsum) / 2 ^ 128 := ILinv_mul_le _
          _ = _ := by rw [mul_assoc]

/-- A purely linear budget pays every fresh two-compression index query. -/
theorem linear_budget_step {k hp : ℝ≥0∞} (hcharge : hp ≤ 2 * k)
    {b : ℕ} (hb : 2 ≤ b) : k * (b - 2 : ℕ) + hp ≤ k * b := by
  have he : ((b - 2 : ℕ) : ℝ≥0∞) + 2 = b := by
    exact_mod_cast Nat.sub_add_cancel hb
  calc k * (b - 2 : ℕ) + hp ≤ k * (b - 2 : ℕ) + 2 * k := add_le_add le_rfl hcharge
    _ = k * (((b - 2 : ℕ) : ℝ≥0∞) + 2) := by ring
    _ = _ := by rw [he]

/-- The linear budget is below the target at every budget, including the endpoint. -/
theorem linear_budget_bound {k : ℝ≥0∞} (hk : k ≤ (2 ^ 127 : ℝ≥0∞)⁻¹) (b : ℕ) :
    k * b ≤ (2 ^ 127 : ℝ≥0∞)⁻¹ * b := mul_le_mul' hk le_rfl

theorem linear_pre_eq (P : Params) (S : Tier.Sched) (c : Cache) :
    P.LinearPre S c = P.Pre S c 0 := by
  simp only [LinearPre, Pre, Nat.cast_zero, ENNReal.zero_div, add_zero, one_mul]

theorem linear_pre_of_ne (P : Params) (S : Tier.Sched) {c : Cache} {q : Query}
    (hq : ∀ u, q ≠ P.encQuery u) (w : BitVec hashBits) :
    P.LinearPre S (c.cacheQuery q w) = P.LinearPre S c := by
  rw [linear_pre_eq, linear_pre_eq]
  exact P.pre_of_ne S hq w 0

theorem linear_pre_noEnc (P : Params) (S : Tier.Sched) {c : Cache}
    (hc : ∀ u, c (P.encQuery u) = none) : P.LinearPre S c = 0 := by
  rw [linear_pre_eq]
  exact P.pre_noEnc S hc 0

theorem linear_budget_sub_add (k : ℝ≥0∞) {b n : ℕ} (hn : n ≤ b) :
    k * (b - n : ℕ) + k * n = k * b := by
  rw [← mul_add, ← Nat.cast_add, Nat.sub_add_cancel hn]

end OptimalOTS.LeanIsaBaseline.Layer.Params
