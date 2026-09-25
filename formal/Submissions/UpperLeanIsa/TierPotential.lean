import Submissions.UpperLeanIsa.TierRow
import Submissions.UpperLeanIsa.TierKernel

/-!
# The pre-sign potential of rarest-cut signing

The class of the index entry at `u` is the class of its answer (`atCls`). Over a cache `c`:

* `Gp c = Σ_{v ∈ V(c)} ḡ(v)`, over the accepted classes held by index entries;
* `Zp c = Σ_{u ∈ bad(c)} z_{t(u)}`, over the entries whose class another entry holds;
* `Yp c = Σ_{u ∈ acc(c)} s(v(u))`, over the entries with an accepted class;
* `Pre(c, b) = (1 + b / I) Gp c + Zp c + Yp c`.

A fresh index query charges `Pre` at most `(1 + (b - 2) / I) H'` against two compressions of
budget (`pre_charge_enc`, P2); other queries leave it unchanged (`pre_of_ne`, P3). The master
lemma `master_budget_family` (M0) takes a potential that depends on the remaining budget.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

attribute [local irreducible] hashBits msgBits pkBits trials

/-- **Master lemma, budget-dependent potential** (M0). If `Φ` does not grow on average at a
fresh hash query and does not grow at a cached one, both against the budget the query spends,
and every continuation from `d` with budget `b'` is bounded by `Φ d b'`, then the computation
from `c` with budget `b` is bounded by `Φ c b`. -/
theorem master_budget_family {α β J : Type} [Nonempty J] (Φ : Cache → ℕ → ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I c (b - queryCost (.inr q)))
    (hΦ : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * Φ (c.cacheQuery q u) (b - queryCost (.inr q)) ≤ Φ c b)
    (hΦc : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b →
      Φ c (b - queryCost (.inr q)) ≤ Φ c b)
    (oa : OracleComp Spec α) (k : J → α → OracleComp Spec β) (Fv : α → Cache → ℝ≥0∞)
    (hF : ∀ x d b', I d b' → (∀ j, CostAtMost (k j x) b') → Fv x d ≤ Φ d b') :
    ∀ (c : Cache) (b : ℕ), I c b → (∀ j, CostAtMost (oa >>= k j) b) →
      E (run oa c) (fun p => Fv p.1 p.2) ≤ Φ c b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c b hI hB
    rw [run_pure, E_pure]
    exact hF x c b hI fun j => by simpa [pure_bind] using hB j
  | query_bind t k' ih =>
    intro c b hI hB
    have hcost : queryCost t ≤ b := by
      have := hB (Classical.arbitrary J)
      rw [bind_assoc, costAtMost_query_bind_iff] at this
      exact this.1
    have hB' : ∀ u j, CostAtMost (k' u >>= k j) (b - queryCost t) := fun u j => by
      have := hB j
      rw [bind_assoc, costAtMost_query_bind_iff] at this
      exact this.2 u
    rw [run_query_bind, E_bind]
    rcases t with t | q
    · rw [oracleImpl_run_inl, E_bind]
      refine (expectedValue_le_of_le _ fun u => ?_)
      rw [E_pure]
      have := ih u c b hI (hB' u)
      simpa [queryCost] using this
    · rcases hcq : c q with _ | v
      · rw [oracleImpl_run_inr_none hcq, E_bind, E_uniform]
        calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
              E (pure (u, c.cacheQuery q u)) (fun p => E (run (k' p.1) p.2) fun p => Fv p.1 p.2)
            ≤ ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
                Φ (c.cacheQuery q u) (b - queryCost (.inr q)) := by
              refine Finset.sum_le_sum fun u _ => ?_
              rw [E_pure]
              dsimp only
              gcongr
              exact ih u _ _ (hI_fresh c b q hI hcq hcost u) (hB' u)
          _ ≤ Φ c b := hΦ c b q hI hcq hcost
      · rw [oracleImpl_run_inr_some hcq, E_pure]
        have hsome : (c q).isSome := by simp [hcq]
        exact (ih v c _ (hI_cached c b q hI hsome hcost) (hB' v)).trans
          (hΦc c b q hI hsome hcost)

namespace Params

/-- `1 / (I - L)`. -/
def ILinv : ℝ≥0∞ := ((2 ^ 127 - 2 ^ 19 : ℕ) : ℝ≥0∞)⁻¹

variable (P : Params) (S : Tier.Sched)

/-- `p(v)`. -/
def pC (v : Cls) : ℝ≥0∞ := (P.cweight v : ℝ≥0∞) / 2 ^ 127

/-- `ḡ(v) = (I/(I-L)) p(v) w̄_t`. -/
def gbar (v : Cls) : ℝ≥0∞ := Tier.cIE * P.pC v * S.wbar (P.ctier S v)

/-- `z_t = w̄_t / (I - L)`. -/
def zT (t : ℕ) : ℝ≥0∞ := S.wbar t * ILinv

/-- `s(v) = p(v) SCK_t / (I - L)`. -/
def sC (v : Cls) : ℝ≥0∞ := P.pC v * S.sckT (P.ctier S v) * ILinv

/-- The accepted classes held by index entries. -/
def Vc (c : Cache) : Finset Cls :=
  P.classes.filter fun v => ∃ u w, c (P.encQuery u) = some w ∧ P.cls w = some v

/-- The index entries whose class another entry holds. -/
def badc (c : Cache) : Finset EncInput :=
  Finset.univ.filter fun u => ∃ w v, c (P.encQuery u) = some w ∧ P.cls w = some v ∧
    ∃ u', u' ≠ u ∧ ∃ w', c (P.encQuery u') = some w' ∧ P.cls w' = some v

/-- The index entries with an accepted class. -/
def accc (c : Cache) : Finset EncInput :=
  Finset.univ.filter fun u => ∃ w v, c (P.encQuery u) = some w ∧ P.cls w = some v

/-- A function of the class of the entry at `u` (`0` if none). -/
def atCls (f : Cls → ℝ≥0∞) (c : Cache) (u : EncInput) : ℝ≥0∞ :=
  ((c (P.encQuery u)).bind P.cls).elim 0 f

/-- `G(c) = Σ_{v ∈ V(c)} ḡ(v)`. -/
def Gp (c : Cache) : ℝ≥0∞ := ∑ v ∈ P.Vc c, P.gbar S v

/-- `Z(c) = Σ_{u ∈ bad(c)} z_{t(u)}`. -/
def Zp (c : Cache) : ℝ≥0∞ := ∑ u ∈ P.badc c, P.atCls (fun v => zT S (P.ctier S v)) c u

/-- `Y(c) = Σ_{u ∈ acc(c)} s(v(u))`. -/
def Yp (c : Cache) : ℝ≥0∞ := ∑ u ∈ P.accc c, P.atCls (P.sC S) c u

/-- `Pre(c, b) = (1 + b / I) G + Z + Y`. -/
def Pre (c : Cache) (b : ℕ) : ℝ≥0∞ :=
  (1 + (b : ℝ≥0∞) / 2 ^ 127) * P.Gp S c + P.Zp S c + P.Yp S c

variable {P S}

/-! ## Membership -/

theorem mem_Vc {c : Cache} {v : Cls} :
    v ∈ P.Vc c ↔ ∃ u, (c (P.encQuery u)).bind P.cls = some v := by
  simp only [Vc, Finset.mem_filter, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨-, u, w, h1, h2⟩
    exact ⟨u, w, h1, h2⟩
  · rintro ⟨u, w, h1, h2⟩
    exact ⟨P.cls_mem_classes h2, u, w, h1, h2⟩

theorem mem_badc {c : Cache} {u : EncInput} :
    u ∈ P.badc c ↔ ∃ v, (c (P.encQuery u)).bind P.cls = some v ∧
      ∃ u', u' ≠ u ∧ (c (P.encQuery u')).bind P.cls = some v := by
  simp only [badc, Finset.mem_filter, Finset.mem_univ, true_and, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨w, v, h1, h2, u', hu', w', h1', h2'⟩
    exact ⟨v, ⟨w, h1, h2⟩, u', hu', w', h1', h2'⟩
  · rintro ⟨v, ⟨w, h1, h2⟩, u', hu', w', h1', h2'⟩
    exact ⟨w, v, h1, h2, u', hu', w', h1', h2'⟩

theorem mem_accc {c : Cache} {u : EncInput} :
    u ∈ P.accc c ↔ ∃ v, (c (P.encQuery u)).bind P.cls = some v := by
  simp only [accc, Finset.mem_filter, Finset.mem_univ, true_and, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨w, v, h1, h2⟩
    exact ⟨v, w, h1, h2⟩
  · rintro ⟨v, w, h1, h2⟩
    exact ⟨w, v, h1, h2⟩

/-! ## Caches with the same classes -/

section congr

variable {c c' : Cache}
  (h : ∀ u, (c' (P.encQuery u)).bind P.cls = (c (P.encQuery u)).bind P.cls)
include h

theorem Vc_congr : P.Vc c' = P.Vc c := by
  ext v
  simp only [mem_Vc, h]

theorem badc_congr : P.badc c' = P.badc c := by
  ext u
  simp only [mem_badc, h]

theorem accc_congr : P.accc c' = P.accc c := by
  ext u
  simp only [mem_accc, h]

theorem atCls_congr (f : Cls → ℝ≥0∞) (u : EncInput) : P.atCls f c' u = P.atCls f c u := by
  unfold atCls
  rw [h u]

/-- `Pre` depends on the cache only through the classes of the index entries. -/
theorem pre_congr (b : ℕ) : P.Pre S c' b = P.Pre S c b := by
  simp only [Pre, Gp, Zp, Yp, Vc_congr h, badc_congr h, accc_congr h, atCls_congr h]

end congr

/-! ## One fresh index entry -/

section fresh

variable {c : Cache} {u₀ : EncInput} (hq : c (P.encQuery u₀) = none) (w : BitVec hashBits)

theorem cls_cq_self :
    (c.cacheQuery (P.encQuery u₀) w (P.encQuery u₀)).bind P.cls = P.cls w := by
  rw [QueryCache.cacheQuery_self, Option.bind_some]

theorem cls_cq_ne {u : EncInput} (hu : u ≠ u₀) :
    (c.cacheQuery (P.encQuery u₀) w (P.encQuery u)).bind P.cls =
      (c (P.encQuery u)).bind P.cls := by
  rw [QueryCache.cacheQuery_of_ne _ _ fun e => hu (P.encQuery_inj e)]

include hq

theorem cls_at_fresh : (c (P.encQuery u₀)).bind P.cls = none := by
  rw [hq, Option.bind_none]

theorem ne_of_cls_some {u : EncInput} {v : Cls} (h : (c (P.encQuery u)).bind P.cls = some v) :
    u ≠ u₀ := by
  rintro rfl
  rw [cls_at_fresh hq] at h
  cases h

theorem cls_cq_none (ho : P.cls w = none) (u : EncInput) :
    (c.cacheQuery (P.encQuery u₀) w (P.encQuery u)).bind P.cls =
      (c (P.encQuery u)).bind P.cls := by
  by_cases hu : u = u₀
  · rw [hu, cls_cq_self, ho, cls_at_fresh hq]
  · exact cls_cq_ne w hu

/-- `G` grows by at most `ḡ` of the new class. -/
theorem Gp_cacheQuery :
    P.Gp S (c.cacheQuery (P.encQuery u₀) w) ≤ P.Gp S c + (P.cls w).elim 0 (P.gbar S) := by
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
    · rw [Finset.insert_eq_of_mem hi]
      exact le_self_add
    · rw [Finset.sum_insert hi, add_comm]

/-- `Z` grows by at most `2 z` of the new class, and only if an old entry holds it. -/
theorem Zp_cacheQuery :
    P.Zp S (c.cacheQuery (P.encQuery u₀) w) ≤ P.Zp S c +
      (P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 2 * zT S (P.ctier S v) else 0) := by
  set c' := c.cacheQuery (P.encQuery u₀) w
  unfold Zp
  rw [← Finset.sum_filter_add_sum_filter_not (P.badc c') (fun u => u ∈ P.badc c)]
  refine add_le_add ?_ ?_
  · calc ∑ u ∈ (P.badc c').filter (fun u => u ∈ P.badc c),
          P.atCls (fun v => zT S (P.ctier S v)) c' u
        = ∑ u ∈ (P.badc c').filter (fun u => u ∈ P.badc c),
          P.atCls (fun v => zT S (P.ctier S v)) c u := by
          refine Finset.sum_congr rfl fun u hu => ?_
          obtain ⟨v, hv, -⟩ := mem_badc.1 (Finset.mem_filter.1 hu).2
          unfold atCls
          rw [cls_cq_ne w (ne_of_cls_some hq hv)]
      _ ≤ _ := Finset.sum_le_sum_of_subset fun u hu => (Finset.mem_filter.1 hu).2
  · set D := (P.badc c').filter (fun u => u ∉ P.badc c)
    have key : ∀ u ∈ D, ∃ i, P.cls w = some i ∧ i ∈ P.Vc c ∧
        (c' (P.encQuery u)).bind P.cls = some i := by
      intro u hu
      obtain ⟨hbad, hnot⟩ := Finset.mem_filter.1 hu
      obtain ⟨v, hv, u', hu'u, hv'⟩ := mem_badc.1 hbad
      by_cases h : u = u₀
      · have hv0 := hv
        rw [h, cls_cq_self] at hv0
        rw [cls_cq_ne w (h ▸ hu'u)] at hv'
        exact ⟨v, hv0, mem_Vc.2 ⟨u', hv'⟩, hv⟩
      · rw [cls_cq_ne w h] at hv
        by_cases h' : u' = u₀
        · rw [h', cls_cq_self] at hv'
          exact ⟨v, hv', mem_Vc.2 ⟨u, hv⟩, by rw [cls_cq_ne w h]; exact hv⟩
        · rw [cls_cq_ne w h'] at hv'
          exact absurd (mem_badc.2 ⟨v, hv, u', hu'u, hv'⟩) hnot
    rcases D.eq_empty_or_nonempty with hD | ⟨u₁, hu₁⟩
    · rw [hD, Finset.sum_empty]
      exact zero_le
    · obtain ⟨i, hi, hiV, -⟩ := key u₁ hu₁
      have hval : ∀ u ∈ D, P.atCls (fun v => zT S (P.ctier S v)) c' u = zT S (P.ctier S i) := by
        intro u hu
        obtain ⟨i', hi', -, hu'⟩ := key u hu
        rw [hi] at hi'
        cases hi'
        unfold atCls
        rw [hu', Option.elim_some]
      have hcard : D.card ≤ 2 := by
        have h1 : (D.erase u₀).card ≤ 1 := Finset.card_le_one.2 fun a ha b hb => by
          obtain ⟨ha0, ha⟩ := Finset.mem_erase.1 ha
          obtain ⟨hb0, hb⟩ := Finset.mem_erase.1 hb
          by_contra hab
          obtain ⟨ia, hia, -, hka⟩ := key a ha
          obtain ⟨ib, hib, -, hkb⟩ := key b hb
          rw [cls_cq_ne w ha0] at hka
          rw [cls_cq_ne w hb0] at hkb
          rw [hia] at hib
          cases hib
          exact (Finset.mem_filter.1 ha).2 (mem_badc.2 ⟨ia, hka, b, Ne.symm hab, hkb⟩)
        have h2 : D.card - 1 ≤ (D.erase u₀).card := Finset.pred_card_le_card_erase
        omega
      rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, hi, Option.elim_some,
        if_pos hiV]
      gcongr
      exact_mod_cast hcard

omit hq in
theorem Yp_eq_sum (c : Cache) : P.Yp S c = ∑ u, P.atCls (P.sC S) c u := by
  unfold Yp accc
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs with h
  · rfl
  · unfold atCls
    rcases hk : (c (P.encQuery u)).bind P.cls with _ | v
    · rw [Option.elim_none]
    · obtain ⟨w, h1, h2⟩ := Option.bind_eq_some_iff.1 hk
      exact absurd ⟨w, v, h1, h2⟩ h

/-- `Y` grows by exactly `s` of the new class. -/
theorem Yp_cacheQuery :
    P.Yp S (c.cacheQuery (P.encQuery u₀) w) = P.Yp S c + (P.cls w).elim 0 (P.sC S) := by
  have h0 : P.atCls (P.sC S) c u₀ = 0 := by
    unfold atCls
    rw [cls_at_fresh hq, Option.elim_none]
  have hself : P.atCls (P.sC S) (c.cacheQuery (P.encQuery u₀) w) u₀ = (P.cls w).elim 0 (P.sC S) := by
    unfold atCls
    rw [cls_cq_self]
  have hrest : ∀ u ∈ Finset.univ.erase u₀,
      P.atCls (P.sC S) (c.cacheQuery (P.encQuery u₀) w) u = P.atCls (P.sC S) c u := fun u hu => by
    unfold atCls
    rw [cls_cq_ne w (Finset.ne_of_mem_erase hu)]
  rw [Yp_eq_sum, Yp_eq_sum]
  calc ∑ u, P.atCls (P.sC S) (c.cacheQuery (P.encQuery u₀) w) u
      = P.atCls (P.sC S) (c.cacheQuery (P.encQuery u₀) w) u₀ +
          ∑ u ∈ Finset.univ.erase u₀, P.atCls (P.sC S) (c.cacheQuery (P.encQuery u₀) w) u :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ u₀)).symm
    _ = (P.cls w).elim 0 (P.sC S) + ∑ u ∈ Finset.univ.erase u₀, P.atCls (P.sC S) c u := by
        rw [hself, Finset.sum_congr rfl hrest]
    _ = _ := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u₀), h0, zero_add, add_comm]

end fresh

/-! ## Averages over a fresh answer -/

theorem card_hash_ennreal : (Fintype.card (BitVec hashBits) : ℝ≥0∞) = 2 ^ 256 := by
  rw [Fintype.card_bitVec]
  unfold hashBits
  norm_num

theorem two_pow_129_div_256 : (2 : ℝ≥0∞) ^ 129 * ((2 : ℝ≥0∞) ^ 256)⁻¹ = ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
  rw [show (256 : ℕ) = 129 + 127 from rfl, pow_add,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
    ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]

/-- A function of the class of a uniform answer averages to `Σ_v p(v) f(v)`. -/
theorem avg_cls (f : Cls → ℝ≥0∞) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (P.cls w).elim 0 f =
      ∑ v ∈ P.classes, P.pC v * f v := by
  have h1 : ∀ w, (P.cls w).elim 0 f = ∑ v ∈ P.classes, if P.cls w = some v then f v else 0 := by
    intro w
    rcases hw : P.cls w with _ | v0
    · simp
    · simp [Finset.sum_ite_eq, P.cls_mem_classes hw]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, P.card_cls, nsmul_eq_mul,
    card_hash_ennreal, pC, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  calc (P.cweight v : ℝ≥0∞) * 2 ^ 129 * ((2 ^ 256)⁻¹ * f v)
      = (P.cweight v : ℝ≥0∞) * (2 ^ 129 * (2 ^ 256)⁻¹) * f v := by ring
    _ = _ := by rw [two_pow_129_div_256]

theorem pC_eq (hT : P.TierHyp S) {v : Cls} (hv : v ∈ P.classes) :
    P.pC v = S.pE (P.ctier S v) := by
  rw [pC, Tier.Sched.pE, ← cweight_of_mem hT hv, hT.K_eq]

theorem ILinv_cast : ((2 ^ 127 - 2 ^ 19 : ℕ) : ℝ≥0∞) = 2 ^ 127 - 2 ^ 19 := by
  rw [ENNReal.natCast_sub]
  norm_num

theorem cIE_eq_mul : Tier.cIE = 2 ^ 127 * ILinv := by
  rw [Tier.cIE, ILinv, ILinv_cast, div_eq_mul_inv]

theorem one_le_cIE : 1 ≤ Tier.cIE := by
  rw [Tier.cIE, ENNReal.le_div_iff_mul_le (Or.inr (pow_ne_zero _ two_ne_zero))
    (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), one_mul]
  exact tsub_le_self

/-- The average new `G` term: `Σ_v p(v) ḡ(v) = c Σ_t N_t p_t² w̄_t`. -/
theorem avg_Gp (hS : S.Valid) (hT : P.TierHyp S) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (P.cls w).elim 0 (P.gbar S) =
      Tier.cIE * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.wbar t := by
  rw [avg_cls]
  calc ∑ v ∈ P.classes, P.pC v * P.gbar S v
      = ∑ v ∈ P.classes, (fun t => Tier.cIE * (S.pE t ^ 2 * S.wbar t)) (P.ctier S v) :=
        Finset.sum_congr rfl fun v hv => by simp only [gbar, pC_eq hT hv]; ring
    _ = ∑ t ∈ Finset.range S.T, S.N t • (Tier.cIE * (S.pE t ^ 2 * S.wbar t)) :=
        sum_classes hS hT (fun t => Tier.cIE * (S.pE t ^ 2 * S.wbar t))
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [nsmul_eq_mul]
        ring

/-- The average new `Y` term: `Σ_v p(v) s(v) = Σ_t N_t p_t² SCK_t / (I - L)`. -/
theorem avg_Yp (hS : S.Valid) (hT : P.TierHyp S) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (P.cls w).elim 0 (P.sC S) =
      ILinv * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t := by
  rw [avg_cls]
  calc ∑ v ∈ P.classes, P.pC v * P.sC S v
      = ∑ v ∈ P.classes, (fun t => ILinv * (S.pE t ^ 2 * S.sckT t)) (P.ctier S v) :=
        Finset.sum_congr rfl fun v hv => by simp only [sC, pC_eq hT hv]; ring
    _ = ∑ t ∈ Finset.range S.T, S.N t • (ILinv * (S.pE t ^ 2 * S.sckT t)) :=
        sum_classes hS hT (fun t => ILinv * (S.pE t ^ 2 * S.sckT t))
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [nsmul_eq_mul]
        ring

/-- The average new `Z` term: `2 Σ_{v ∈ V(c)} p(v) z_{t(v)} = (2 / I) G(c)`. -/
theorem avg_Zp (c : Cache) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 2 * zT S (P.ctier S v) else 0) =
      2 / 2 ^ 127 * P.Gp S c := by
  rw [avg_cls, Gp, Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  have hsub : P.Vc c ⊆ P.classes := Finset.filter_subset _ _
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [zT, gbar, cIE_eq_mul,
    show (2 : ℝ≥0∞) / 2 ^ 127 * (2 ^ 127 * ILinv * P.pC v * S.wbar (P.ctier S v)) =
      (2 / 2 ^ 127 * 2 ^ 127) * (ILinv * P.pC v * S.wbar (P.ctier S v)) by ring,
    ENNReal.div_mul_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
  ring

theorem ILinv_mul_le (x : ℝ≥0∞) : ILinv * x ≤ Tier.cIE ^ 2 * x / 2 ^ 127 := by
  have h2 : Tier.cIE * ILinv * 2 ^ 127 = Tier.cIE ^ 2 := by rw [cIE_eq_mul]; ring
  rw [ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ two_ne_zero))
    (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), ← h2]
  calc ILinv * x * 2 ^ 127 = 1 * (ILinv * 2 ^ 127 * x) := by ring
    _ ≤ Tier.cIE * (ILinv * 2 ^ 127 * x) := by gcongr; exact one_le_cIE
    _ = Tier.cIE * ILinv * 2 ^ 127 * x := by ring

/-! ## The charge of the pre-sign potential (P2, P3) -/

variable (P S)

/-- **P2.** A fresh index query spends two compressions of budget and charges `Pre` at most
`(1 + (b - 2) / I) H'` on average. -/
theorem pre_charge_enc (hS : S.Valid) (hT : P.TierHyp S) {c : Cache} {u₀ : EncInput}
    (hq : c (P.encQuery u₀) = none) {b : ℕ} (hb : 2 ≤ b) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      P.Pre S (c.cacheQuery (P.encQuery u₀) w) (b - 2) ≤
      P.Pre S c b + (1 + ((b - 2 : ℕ) : ℝ≥0∞) / 2 ^ 127) * S.hpE := by
  set K := (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹
  set β := 1 + ((b - 2 : ℕ) : ℝ≥0∞) / 2 ^ 127
  set A := β * P.Gp S c + P.Zp S c + P.Yp S c
  set g1 := fun w : BitVec hashBits => (P.cls w).elim 0 (P.gbar S)
  set z1 := fun w : BitVec hashBits =>
    (P.cls w).elim 0 (fun v => if v ∈ P.Vc c then 2 * zT S (P.ctier S v) else 0)
  set y1 := fun w : BitVec hashBits => (P.cls w).elim 0 (P.sC S)
  have hpt : ∀ w, P.Pre S (c.cacheQuery (P.encQuery u₀) w) (b - 2) ≤
      A + (β * g1 w + z1 w + y1 w) := by
    intro w
    calc P.Pre S (c.cacheQuery (P.encQuery u₀) w) (b - 2)
        ≤ β * (P.Gp S c + g1 w) + (P.Zp S c + z1 w) + (P.Yp S c + y1 w) :=
          add_le_add (add_le_add (mul_le_mul' le_rfl (Gp_cacheQuery hq w))
            (Zp_cacheQuery hq w)) (Yp_cacheQuery hq w).le
      _ = A + (β * g1 w + z1 w + y1 w) := by ring
  have eβ : ∑ w, K * (β * g1 w) = β * ∑ w, K * g1 w := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
  have hβ : 1 ≤ β := le_self_add
  have hα : β * P.Gp S c + 2 / 2 ^ 127 * P.Gp S c = (1 + (b : ℝ≥0∞) / 2 ^ 127) * P.Gp S c := by
    rw [← add_mul, add_assoc, ENNReal.div_add_div_same]
    congr 3
    exact_mod_cast Nat.sub_add_cancel hb
  have hY : ILinv * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t ≤
      β * (Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum / 2 ^ 127) :=
    calc _ ≤ ILinv * ((2 ^ 19 - 1) * ENNReal.ofReal S.SCsum) := by
          gcongr
          exact S.sum_sck_le hS
      _ ≤ Tier.cIE ^ 2 * ((2 ^ 19 - 1) * ENNReal.ofReal S.SCsum) / 2 ^ 127 := ILinv_mul_le _
      _ = Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum / 2 ^ 127 := by rw [mul_assoc]
      _ ≤ _ := le_mul_of_one_le_left zero_le hβ
  calc ∑ w, K * P.Pre S (c.cacheQuery (P.encQuery u₀) w) (b - 2)
      ≤ ∑ w, K * (A + (β * g1 w + z1 w + y1 w)) :=
        Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl (hpt w)
    _ = A + (∑ w, K * (β * g1 w) + ∑ w, K * z1 w + ∑ w, K * y1 w) := by
        have hK : ∀ a, ∑ _w : BitVec hashBits, K * a = a := fun a => sum_inv_card_mul a
        simp only [mul_add, Finset.sum_add_distrib, hK]
    _ = A + (β * (Tier.cIE * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.wbar t) +
          2 / 2 ^ 127 * P.Gp S c +
          ILinv * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t) := by
        rw [eβ, avg_Gp hS hT, avg_Zp, avg_Yp hS hT]
    _ = (β * P.Gp S c + 2 / 2 ^ 127 * P.Gp S c) + P.Zp S c + P.Yp S c +
          (β * (Tier.cIE * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.wbar t) +
            ILinv * ∑ t ∈ Finset.range S.T, (S.N t : ℝ≥0∞) * S.pE t ^ 2 * S.sckT t) := by
        ring
    _ ≤ P.Pre S c b + β * S.hpE := by
        rw [hα]
        refine add_le_add le_rfl ?_
        calc _ ≤ β * (Tier.cIE * ENNReal.ofReal S.Hsum) +
              β * (Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum / 2 ^ 127) :=
              add_le_add (by gcongr; exact S.sum_wbar_le hS) hY
          _ = β * (Tier.cIE * ENNReal.ofReal S.Hsum +
              Tier.cIE ^ 2 * (2 ^ 19 - 1) * ENNReal.ofReal S.SCsum / 2 ^ 127) := (mul_add _ _ _).symm
          _ ≤ β * S.hpE := by gcongr; exact S.Hprime_le hS

/-- **P3.** A query at no index point leaves `Pre` unchanged. -/
theorem pre_of_ne {c : Cache} {q : Query} (hq : ∀ u, q ≠ P.encQuery u) (w : BitVec hashBits)
    (b : ℕ) : P.Pre S (c.cacheQuery q w) b = P.Pre S c b :=
  pre_congr (fun u => by rw [QueryCache.cacheQuery_of_ne _ _ (hq u).symm]) b

theorem pre_mono (c : Cache) {b b' : ℕ} (h : b' ≤ b) : P.Pre S c b' ≤ P.Pre S c b := by
  unfold Pre
  gcongr

theorem pre_noEnc {c : Cache} (hc : ∀ u, c (P.encQuery u) = none) (b : ℕ) : P.Pre S c b = 0 := by
  have hk : ∀ u, (c (P.encQuery u)).bind P.cls = none := fun u => by rw [hc u, Option.bind_none]
  have hG : P.Gp S c = 0 := Finset.sum_eq_zero fun v hv => by
    obtain ⟨u, hu⟩ := mem_Vc.1 hv
    rw [hk u] at hu
    cases hu
  have hZ : P.Zp S c = 0 := Finset.sum_eq_zero fun u hu => by
    obtain ⟨v, hv, -⟩ := mem_badc.1 hu
    rw [hk u] at hv
    cases hv
  have hY : P.Yp S c = 0 := Finset.sum_eq_zero fun u hu => by
    obtain ⟨v, hv⟩ := mem_accc.1 hu
    rw [hk u] at hv
    cases hv
  rw [Pre, hG, hZ, hY, mul_zero, add_zero, add_zero]

end Params

end OptimalOTS.LeanIsaBaseline.Layer
