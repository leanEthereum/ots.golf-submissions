import Submissions.UpperLeanIsa.TierSign
import Submissions.UpperLeanIsa.TierPotential

/-!
# The loss of rarest-cut signing (P1)

Signing row `M` from the cache `d` loses when another index entry of `d` holds the class of the
best trial (`IdxPreC`) or a fresh non-winning trial holds it (`SelfCol`). Under `RowGood`, the
loss has probability at most `G(d) + Z(d) + Y(d) + SC_f` (`loss_le`):

* a fresh winner whose class is held in `d` is charged `ḡ` of its class (K1), at most `G(d)`;
* a cached winner whose entry is bad in `d` is charged `z` of its tier (K2), at most `Z(d)`;
* a fresh winner with a self-collision is charged `p(v)² SCK_t` (K3a), at most `SC_f`;
* a cached winner with a self-collision is charged `s` of its class (K3b), at most `Y(d)`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

attribute [local irreducible] hashBits msgBits pkBits trials

namespace Params

variable (P : Params)

/-- An index entry of `d` other than `u₁` holds the class `v`. -/
def IdxPreC (d : Cache) (u₁ : EncInput) (v : Cls) : Prop :=
  ∃ u, u ≠ u₁ ∧ ∃ w, d (P.encQuery u) = some w ∧ P.cls w = some v

variable {P} {S : Tier.Sched}

/-- A sum over the nonces of row `M` in `s` is at most the sum over `s`. -/
theorem sum_row_le (M : EMessage) (s : Finset EncInput) (f : EncInput → ℝ≥0∞) :
    ∑ η ∈ Finset.univ.filter (fun η : Nonce => M ++ η ∈ s), f (M ++ η) ≤ ∑ u ∈ s, f u := by
  rw [← Finset.sum_image fun x _ y _ h => append_nonce_inj M h]
  exact Finset.sum_le_sum_of_subset fun u hu => by
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.1 hu
    exact (Finset.mem_filter.1 hη).2

theorem le_sum_of_mem {ι : Type} {s : Finset ι} {f : ι → ℝ≥0∞} {i : ι} (hi : i ∈ s)
    (h : 1 ≤ f i) : 1 ≤ ∑ j ∈ s, f j :=
  h.trans (Finset.single_le_sum (fun _ _ => zero_le) hi)

/-- The class held by the entry of `d` at `M ++ η`, as an index of tier `ctier v`. -/
theorem cached_target {d : Cache} {M : EMessage} {η : Nonce} {v : Cls}
    (h : (d (P.encQuery (M ++ η))).bind P.cls = some v) :
    ∃ w, d (P.encQuery (M ++ η)) = some w ∧ P.Accepted (indexSlice w) ∧
      P.digit (indexSlice w) = v ∧ v ∈ P.classes := by
  obtain ⟨w, hw, hc⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨w, hw, (P.cls_eq_some.1 hc).1, (P.cls_eq_some.1 hc).2, P.cls_mem_classes hc⟩

variable (P) in
/-- **P1.** The loss of signing is at most `G(d) + Z(d) + Y(d) + SC_f`. -/
theorem loss_le (hS : S.Valid) (hT : P.TierHyp S) {d : Cache} {M : EMessage}
    (hRG : P.RowGood S d M) :
    E (run (P.signTier M) d) (fun p => if ∃ b, p.1 = some b ∧
        (P.IdxPreC d (M ++ b.1) (P.digit b.2) ∨ P.SelfCol d M p.2 b) then 1 else 0) ≤
      P.Gp S d + P.Zp S d + P.Yp S d + Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum := by
  -- the fresh targets of class `v` and the cached target at `η₀`, kept opaque so that their
  -- decidability instances match those of `win_le` and `win_sc_le`
  obtain ⟨θF, hθF⟩ : ∃ θF : Cls → Nonce → Index → Prop, ∀ v η I,
      θF v η I ↔ d (P.encQuery (M ++ η)) = none ∧ P.Accepted I ∧ P.digit I = v :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  obtain ⟨θC, hθC⟩ : ∃ θC : Nonce → Nonce → Index → Prop, ∀ η₀ η I,
      θC η₀ η I ↔ η = η₀ ∧ ∃ w, d (P.encQuery (M ++ η₀)) = some w ∧ indexSlice w = I :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  set rowBad := Finset.univ.filter (fun η : Nonce => M ++ η ∈ P.badc d)
  set rowAcc := Finset.univ.filter (fun η : Nonce => M ++ η ∈ P.accc d)
  set A1 : Option (Nonce × Index) × Cache → ℝ≥0∞ := fun p => ∑ v ∈ P.Vc d,
    if ∃ b, p.1 = some b ∧ θF v b.1 b.2 then 1 else 0
  set A2 : Option (Nonce × Index) × Cache → ℝ≥0∞ := fun p => ∑ η ∈ rowBad,
    if ∃ b, p.1 = some b ∧ θC η b.1 b.2 then 1 else 0
  set A3 : Option (Nonce × Index) × Cache → ℝ≥0∞ := fun p => ∑ v ∈ P.classes,
    if ∃ b, p.1 = some b ∧ θF v b.1 b.2 ∧ P.SelfCol d M p.2 b then 1 else 0
  set A4 : Option (Nonce × Index) × Cache → ℝ≥0∞ := fun p => ∑ η ∈ rowAcc,
    if ∃ b, p.1 = some b ∧ θC η b.1 b.2 ∧ P.SelfCol d M p.2 b then 1 else 0
  have hpt : ∀ p ∈ support (run (P.signTier M) d),
      (if ∃ b, p.1 = some b ∧
        (P.IdxPreC d (M ++ b.1) (P.digit b.2) ∨ P.SelfCol d M p.2 b) then 1 else 0) ≤
        A1 p + A2 p + A3 p + A4 p := by
    intro p hp
    obtain ⟨hsub, -, hbest⟩ := P.signTier_ext M d p hp
    by_cases hind : ∃ b, p.1 = some b ∧
        (P.IdxPreC d (M ++ b.1) (P.digit b.2) ∨ P.SelfCol d M p.2 b)
    · rw [if_pos hind]
      obtain ⟨b, hb, hcase⟩ := hind
      obtain ⟨hacc, w₁, hw₁, hI₁⟩ := hbest b hb
      rcases hdq : d (P.encQuery (M ++ b.1)) with _ | w₀
      · have hθ : θF (P.digit b.2) b.1 b.2 := (hθF _ _ _).2 ⟨hdq, hacc, rfl⟩
        rcases hcase with ⟨u, -, w, hw, hc⟩ | hsc
        · have hv : P.digit b.2 ∈ P.Vc d := mem_Vc.2 ⟨u, by rw [hw, Option.bind_some]; exact hc⟩
          refine le_trans ?_ (le_self_add.trans (le_self_add.trans le_self_add))
          exact le_sum_of_mem hv (by rw [if_pos ⟨b, hb, hθ⟩])
        · refine le_trans ?_ (le_add_self.trans le_self_add)
          exact le_sum_of_mem (P.digit_mem_classes hacc) (by rw [if_pos ⟨b, hb, hθ, hsc⟩])
      · have hw : w₁ = w₀ := Option.some.inj (hw₁.symm.trans (hsub _ _ hdq))
        subst hw
        have hθ : θC b.1 b.1 b.2 := (hθC _ _ _).2 ⟨rfl, w₁, hdq, hI₁⟩
        have hcls : P.cls w₁ = some (P.digit b.2) := P.cls_eq_some.2 ⟨hI₁ ▸ hacc, by rw [hI₁]⟩
        have hbind : (d (P.encQuery (M ++ b.1))).bind P.cls = some (P.digit b.2) := by
          rw [hdq, Option.bind_some, hcls]
        rcases hcase with ⟨u, hu, w, hw, hc⟩ | hsc
        · have hη : b.1 ∈ rowBad := Finset.mem_filter.2 ⟨Finset.mem_univ _,
            mem_badc.2 ⟨_, hbind, u, hu, by rw [hw, Option.bind_some]; exact hc⟩⟩
          refine le_trans ?_ (le_add_self.trans (le_self_add.trans le_self_add))
          exact le_sum_of_mem hη (by rw [if_pos ⟨b, hb, hθ⟩])
        · have hη : b.1 ∈ rowAcc := Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_accc.2 ⟨_, hbind⟩⟩
          refine le_trans ?_ le_add_self
          exact le_sum_of_mem hη (by rw [if_pos ⟨b, hb, hθ, hsc⟩])
    · rw [if_neg hind]
      exact zero_le
  -- one fresh trial hits class `v` with probability at most `p(v)`
  have hqF : ∀ v, ∀ tried : Finset Nonce, tried.card < trials →
      P.trialAvg d M tried (fun η w _ => if θF v η (indexSlice w) then 1 else 0) ≤ P.pC v := by
    intro v tried htr
    refine (P.trialAvg_mono' fun η w fr hok => ?_).trans (P.trialAvg_fresh_cls d M htr v)
    obtain ⟨-, -, hfalse⟩ := hok
    by_cases h1 : θF v η (indexSlice w)
    · have h1' := (hθF v η _).1 h1
      have hfr : fr = true := by
        cases fr
        · have := hfalse rfl
          rw [h1'.1] at this
          cases this
        · rfl
      rw [if_pos h1, if_pos ⟨hfr, P.cls_eq_some.2 h1'.2⟩]
    · rw [if_neg h1]
      exact zero_le
  -- one trial is at the nonce `η₀` with probability at most `1 / (I - L)`
  have hqC : ∀ η₀, ∀ tried : Finset Nonce, tried.card < trials →
      P.trialAvg d M tried (fun η w _ => if θC η₀ η (indexSlice w) then 1 else 0) ≤ ILinv := by
    intro η₀ tried htr
    refine (P.trialAvg_mono fun η w fr => ?_).trans (P.trialAvg_nonce d M htr η₀)
    by_cases h1 : θC η₀ η (indexSlice w)
    · rw [if_pos h1, if_pos ((hθC _ _ _).1 h1).1]
    · rw [if_neg h1]
      exact zero_le
  have hrF : ∀ v tried, tried.card < trials →
      P.trialAvg d M tried (fun _ w fr => if fr = true ∧ P.cls w = some v then 1 else 0) ≤
        P.pC v := fun v _ htr => P.trialAvg_fresh_cls d M htr v
  -- K1: fresh winners with a held class
  have hE1 : E (run (P.signTier M) d) A1 ≤ P.Gp S d := by
    simp only [A1]
    rw [tierE_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    have hvc : v ∈ P.classes := (Finset.mem_filter.1 hv).1
    refine (P.win_le hS hT hRG (θF v) (ctier_spec hT hvc).1
      (fun η I h => (tierI_eq_ctier ((hθF v η I).1 h).2.1).trans (by rw [((hθF v η I).1 h).2.2]))
      (hqF v)).trans ?_
    rw [gbar, mul_assoc]
    exact le_mul_of_one_le_left zero_le one_le_cIE
  -- K2: cached winners at bad entries
  have hE2 : E (run (P.signTier M) d) A2 ≤ P.Zp S d := by
    simp only [A2]
    rw [tierE_sum]
    refine le_trans (Finset.sum_le_sum fun η hη => ?_)
      (sum_row_le M (P.badc d) (P.atCls (fun v => zT S (P.ctier S v)) d))
    obtain ⟨v, hv, -⟩ := mem_badc.1 (Finset.mem_filter.1 hη).2
    obtain ⟨w, hw, hacc, hdig, hvc⟩ := cached_target hv
    have hθ : ∀ η' I, θC η η' I → P.tierI S I = P.ctier S v := by
      intro η' I h
      obtain ⟨-, w', hw', rfl⟩ := (hθC η η' I).1 h
      rw [hw] at hw'
      cases hw'
      rw [tierI_eq_ctier hacc, hdig]
    refine (P.win_le hS hT hRG (θC η) (ctier_spec hT hvc).1 hθ (hqC η)).trans (le_of_eq ?_)
    rw [atCls, hv, Option.elim_some, zT, mul_comm]
  -- K3a: fresh winners with a self-collision
  have hE3 : E (run (P.signTier M) d) A3 ≤
      Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum := by
    simp only [A3]
    rw [tierE_sum]
    calc ∑ v ∈ P.classes, E (run (P.signTier M) d) (fun p =>
          if ∃ b, p.1 = some b ∧ θF v b.1 b.2 ∧ P.SelfCol d M p.2 b then 1 else 0)
        ≤ ∑ v ∈ P.classes, (fun t => S.pE t ^ 2 * S.sckT t) (P.ctier S v) := by
          refine Finset.sum_le_sum fun v hv => ?_
          refine (P.win_sc_le hS hT hRG (θF v) (ctier_spec hT hv).1
            (fun η I h => (tierI_eq_ctier ((hθF v η I).1 h).2.1).trans
              (by rw [((hθF v η I).1 h).2.2]))
            (fun η I h => ((hθF v η I).1 h).2.2)
            (hqF v) (hrF v)).trans (le_of_eq ?_)
          rw [pC_eq hT hv]
          ring
      _ = ∑ t ∈ Finset.range S.T, S.N t • (S.pE t ^ 2 * S.sckT t) :=
          sum_classes hS hT (fun t => S.pE t ^ 2 * S.sckT t)
      _ = ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t :=
          Finset.sum_congr rfl fun t _ => by rw [nsmul_eq_mul, mul_assoc]
      _ ≤ (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum := S.sum_sck_le hS
      _ ≤ Tier.cIE ^ 2 * ((2 ^ 19 - 1) * ENNReal.ofReal S.SCsum) :=
          le_mul_of_one_le_left zero_le (one_le_pow₀ one_le_cIE)
      _ = _ := (mul_assoc _ _ _).symm
  -- K3b: cached winners with a self-collision
  have hE4 : E (run (P.signTier M) d) A4 ≤ P.Yp S d := by
    simp only [A4]
    rw [tierE_sum]
    refine le_trans (Finset.sum_le_sum fun η hη => ?_)
      (sum_row_le M (P.accc d) (P.atCls (P.sC S) d))
    obtain ⟨v, hv⟩ := mem_accc.1 (Finset.mem_filter.1 hη).2
    obtain ⟨w, hw, hacc, hdig, hvc⟩ := cached_target hv
    have hθ : ∀ η' I, θC η η' I → P.tierI S I = P.ctier S v ∧ P.digit I = v := by
      intro η' I h
      obtain ⟨-, w', hw', rfl⟩ := (hθC η η' I).1 h
      rw [hw] at hw'
      cases hw'
      exact ⟨by rw [tierI_eq_ctier hacc, hdig], hdig⟩
    refine (P.win_sc_le hS hT hRG (θC η) (ctier_spec hT hvc).1 (fun η' I h => (hθ η' I h).1)
      (fun η' I h => (hθ η' I h).2) (hqC η) (hrF v)).trans (le_of_eq ?_)
    rw [atCls, hv, Option.elim_some, sC]
    ring
  calc E (run (P.signTier M) d) (fun p => if ∃ b, p.1 = some b ∧
        (P.IdxPreC d (M ++ b.1) (P.digit b.2) ∨ P.SelfCol d M p.2 b) then 1 else 0)
      ≤ E (run (P.signTier M) d) (fun p => A1 p + A2 p + A3 p + A4 p) :=
        expectedValue_mono_of_support hpt
    _ = E (run (P.signTier M) d) A1 + E (run (P.signTier M) d) A2 +
          E (run (P.signTier M) d) A3 + E (run (P.signTier M) d) A4 := by
        rw [tierE_add, tierE_add, tierE_add]
    _ ≤ P.Gp S d + P.Zp S d + Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum +
          P.Yp S d := by
        gcongr
    _ = _ := add_right_comm _ _ _

end Params

end OptimalOTS.LeanIsaBaseline.Layer
