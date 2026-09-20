import Submissions.UpperCompressions.ProofBundle04
import Submissions.UpperCompressions.ProofBundle02
import Submissions.UpperCompressions.ProofBundle03

/- Original module: Submissions.UpperCompressions.WideAuthCharges; SHA256 766bd815de692ee78442ad727ed994fa21ab0c807922b9fb35069d5ce969db50. -/
section

/-! Per-compression authentication charges for129-bit internals and a128-bit
public root. These are event/fiber bounds; security-game integration remains separate. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

/-- The root has twice the spurious-match probability of an internal node. -/
def sprRate (h : Name) : ℝ≥0∞ := if h = rh then ε + ε else ε

theorem bindingWidth_le (h : Name) : bindingWidth h ≤ 256 := by
  simp only [bindingWidth]
  split_ifs <;> omega

theorem binding_fiber (h : Name) (a : BitVec (bindingWidth h)) :
    (Finset.univ.filter fun b : BitVec 256 => bindingValue h b = a).card =
      2 ^ (256 - bindingWidth h) :=
  TruncFiber.card_filter_setWidth (bindingWidth_le h) a

theorem inv_card_binding (h : Name) :
    (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      ((2 ^ (256 - bindingWidth h) : ℕ) : ℝ≥0∞) = sprRate h := by
  by_cases hh : h = rh
  · simp only [bindingWidth, sprRate, if_pos hh]
    change (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) : ℝ≥0∞) = ε + ε
    have he : (2 : ℕ)^128 = 2^127 + 2^127 := by
      rw [show (128 : ℕ) = 127+1 from rfl, pow_succ, mul_two]
    rw [he, Nat.cast_add, mul_add, inv_card_bitVec_mul_two_pow]
  · simp only [bindingWidth, sprRate, if_neg hh]
    exact inv_card_bitVec_mul_two_pow

theorem epsilon_le_query_cost (q : Query) : ε ≤ ε * (blockCost q.1 : ℝ≥0∞) := by
  have hc : (1 : ℝ≥0∞) ≤ (blockCost q.1 : ℝ≥0∞) := by
    exact_mod_cast (Nat.le_max_left 1 ((q.1 + blockBits - 1) / blockBits))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (show (0 : ℝ≥0∞) ≤ ε from zero_le)

/-- The root's128-bit match charge is covered by its actual five-compression input. -/
theorem sprRate_le_query_cost {h p : Name} (hp : hashParent h = some p)
    (q : Query) (hlen : q.1 = p.len) : sprRate h ≤ ε * (blockCost q.1 : ℝ≥0∞) := by
  by_cases hh : h = rh
  · subst h
    simp only [hashParent, Option.some.injEq] at hp
    subst p
    rw [sprRate, if_pos rfl, hlen]
    change ε + ε ≤ ε * (blockCost 2338 : ℝ≥0∞)
    have hc : blockCost 2338 = 5 := by norm_num [blockCost, blockBits]
    rw [hc, ← mul_two]
    exact mul_le_mul_of_nonneg_left (by norm_num : (2 : ℝ≥0∞) ≤ 5) zero_le
  · rw [sprRate, if_neg hh]
    exact epsilon_le_query_cost q

/-- A fresh answer increases the spurious-image event by at most2^-129 per
paid compression, including the root's distinct128-bit endpoint. -/
theorem spr_charge (c : Cache) (ξ : Rec) (q : Query) (_hq : c q = none) :
    ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      (if Spr (c.cacheQuery q b) ξ then 1 else 0) ≤
        (if Spr c ξ then 1 else 0) + ε * (blockCost q.1 : ℝ≥0∞) := by
  by_cases hs : Spr c ξ
  · rw [if_pos hs]
    calc ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (if Spr (c.cacheQuery q b) ξ then 1 else 0)
        ≤ ∑ _b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 1 := by
          refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ zero_le
          split_ifs <;> simp
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
              (ENNReal.natCast_ne_top _)]
      _ ≤ _ := le_self_add
  · rw [if_neg hs, zero_add]
    have key : ∀ b, Spr (c.cacheQuery q b) ξ →
        ∃ h p, hashParent h = some p ∧ q.1 = p.len ∧ tagNat q = h.idx ∧
          bindingValue h b = bindingValue h (ξ.2 h.fin) := by
      rintro b ⟨h, p, hp, u, hu, htag, b', hb', ht⟩
      by_cases hqq : (⟨p.len, u⟩ : Query) = q
      · subst hqq
        rw [QueryCache.cacheQuery_self] at hb'
        obtain rfl := Option.some.inj hb'
        exact ⟨h, p, hp, rfl, htag, ht⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hb'
        exact (hs ⟨h, p, hp, u, hu, htag, b', hb', ht⟩).elim
    by_cases hex : ∃ h₀ p₀, hashParent h₀ = some p₀ ∧ q.1 = p₀.len ∧ tagNat q = h₀.idx
    · obtain ⟨h₀, p₀, hp₀, hlen₀, hq₀⟩ := hex
      have key' : ∀ b, Spr (c.cacheQuery q b) ξ →
          bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin) := by
        intro b hb
        obtain ⟨h, p, hp, hlen, hq', ht⟩ := key b hb
        have he : h₀ = h := Name.idx_injective (hq₀.symm.trans hq')
        subst he
        exact ht
      calc ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if Spr (c.cacheQuery q b) ξ then 1 else 0)
          ≤ ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin) then 1 else 0) := by
            refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ zero_le
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd (key' b h1) h2
            · exact zero_le_one
            · exact le_rfl
        _ = (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun b : BitVec 256 =>
              bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin)).card : ℝ≥0∞) := by
            rw [← Finset.mul_sum, Finset.sum_boole]
        _ = sprRate h₀ := by rw [binding_fiber, inv_card_binding]
        _ ≤ _ := sprRate_le_query_cost hp₀ q hlen₀
    · have hno : ∀ b, ¬ Spr (c.cacheQuery q b) ξ := fun b hb => by
        obtain ⟨h, p, hp, hlen, htag, _⟩ := key b hb
        exact hex ⟨h, p, hp, hlen, htag⟩
      rw [Finset.sum_eq_zero fun b _ => by rw [if_neg (hno b), mul_zero]]
      exact zero_le

theorem two_epsilon_eq_half_kappa : ε + ε = (((2 : ℝ≥0∞)^127)⁻¹) / 2 := by
  have hstep (n : ℕ) : ((2 : ℝ≥0∞)^(n+1))⁻¹ = ((2 : ℝ≥0∞)^n)⁻¹ / 2 := by
    rw [pow_succ, ENNReal.mul_inv (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      (Or.inr two_ne_zero), div_eq_mul_inv]
  calc ε + ε = ((2 : ℝ≥0∞)^128)⁻¹ / 2 + ((2 : ℝ≥0∞)^128)⁻¹ / 2 := by
        rw [ε, show (129 : ℕ) = 128+1 from rfl, hstep]
    _ = ((2 : ℝ≥0∞)^128)⁻¹ := ENNReal.add_halves _
    _ = _ := hstep 127

/-- Combining the hidden-input and spurious-image charges costs κ/2 per compression. -/
theorem authentication_charge_budget (q : Query) :
    ε + ε * (blockCost q.1 : ℝ≥0∞) ≤
      ((((2 : ℝ≥0∞)^127)⁻¹) / 2) * (blockCost q.1 : ℝ≥0∞) := by
  calc ε + ε * (blockCost q.1 : ℝ≥0∞)
      ≤ ε * (blockCost q.1 : ℝ≥0∞) + ε * (blockCost q.1 : ℝ≥0∞) :=
        add_le_add (epsilon_le_query_cost q) le_rfl
    _ = (ε+ε) * (blockCost q.1 : ℝ≥0∞) := (add_mul ..).symm
    _ = _ := by rw [two_epsilon_eq_half_kappa]

end OptimalOTS.WeightedConstruction.WideForest

#print axioms OptimalOTS.WeightedConstruction.WideForest.spr_charge
#print axioms OptimalOTS.WeightedConstruction.WideForest.authentication_charge_budget
end
end

/- Original module: Submissions.UpperCompressions.WideAuthPotential; SHA256 ced0baa6af04b9940e2e59ee91989416b638271faf7220a4221db44dbba2abea. -/
section

/-! Authentication record potentials and a joint query-type interface.
The index potential is explicit and must be discharged by the weighted posterior proof. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

def sumW (T : Finset Rec) : ℝ≥0∞ := ∑ ξ ∈ T, w

def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

def authRate : ℝ≥0∞ := (((2:ℝ≥0∞)^127)⁻¹) / 2

def authPotential (T : Finset Rec) (A? : Option (Finset Name)) (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ T, w * (ind (Cache.Hits c (fHid A? ξ)) + ind (Spr c ξ))

theorem sumW_mono {T T' : Finset Rec} (h : T ⊆ T') : sumW T ≤ sumW T' :=
  Finset.sum_le_sum_of_subset h

theorem ind_congr {p r : Prop} (h : p ↔ r) : ind p = ind r := by
  unfold ind; simp only [h]

theorem ind_or_le (p r : Prop) : ind (p ∨ r) ≤ ind p + ind r := by
  unfold ind
  by_cases hp : p <;> by_cases hr : r <;> simp [hp, hr]

theorem ind_exists_some (i : ℕ) (P : ℕ → Prop) :
    ind (∃ i', some i = some i' ∧ P i') = ind (P i) := by
  apply ind_congr; simp

theorem ind_exists_none (P : ℕ → Prop) :
    ind (∃ i', (none : Option ℕ) = some i' ∧ P i') = 0 := by
  simp [ind]

theorem w_mul_ind_le (p : Prop) [Decidable p] : w * ind p ≤ if p then w else 0 := by
  unfold ind; split_ifs <;> simp

/-- Averaging over a fresh answer commutes with a weighted sum over records. -/
theorem avg_sum_comm (T : Finset Rec) (f : Rec → BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ∑ ξ ∈ T, w * f ξ u =
      ∑ ξ ∈ T, w * ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f ξ u := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun u _ => ?_
  ring

theorem avg_const (X : ℝ≥0∞) :
    ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * X = X :=
  sum_inv_card_mul X

/-- Summing a per-record charge of `ε` with the weights `w`. -/
theorem sum_w_mul_le_add (T : Finset Rec) (a b : Rec → ℝ≥0∞) (h : ∀ ξ ∈ T, a ξ ≤ b ξ + ε) :
    ∑ ξ ∈ T, w * a ξ ≤ ∑ ξ ∈ T, w * b ξ + ε * sumW T := by
  unfold sumW
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ hξ => ?_
  rw [mul_comm ε w, ← mul_add]
  exact mul_le_mul_right (h ξ hξ) w

/-- Summing a general per-record charge with the weights. -/
theorem sum_w_mul_le_add_charge (δ : ℝ≥0∞) (T : Finset Rec)
    (a b : Rec → ℝ≥0∞) (h : ∀ ξ ∈ T, a ξ ≤ b ξ + δ) :
    ∑ ξ ∈ T, w * a ξ ≤ ∑ ξ ∈ T, w * b ξ + δ * sumW T := by
  unfold sumW
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ hξ => ?_
  rw [mul_comm δ w, ← mul_add]
  exact mul_le_mul_right (h ξ hξ) w

/-- A fresh answer can only create a hit at the queried point. -/
theorem hits_avg_le (T : Finset Rec) (f : Rec → Cache) (c : Cache) (q : Query) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f ξ)) ≤
      ∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)) + ∑ ξ ∈ T, w * ind ((f ξ q).isSome) := by
  rw [avg_sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [← mul_add]
  refine mul_le_mul_right ?_ w
  calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ind (Cache.Hits (c.cacheQuery q u) (f ξ))
      ≤ ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          (ind (Cache.Hits c (f ξ)) + ind ((f ξ q).isSome)) := by
        refine Finset.sum_le_sum fun u _ => mul_le_mul_right ?_ _
        rw [ind_congr (Cache.hits_cacheQuery c (f ξ) q u)]
        exact ind_or_le _ _
    _ = _ := sum_inv_card_mul _

/-- No hit at a point absent from every `f ξ`. -/
theorem hits_avg_eq (T : Finset Rec) (f : Rec → Cache) (c : Cache) (q : Query)
    (hf : ∀ ξ, f ξ q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f ξ)) =
      ∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  simp only [Cache.hits_cacheQuery, hf, Option.isSome_none, Bool.false_eq_true, or_false]

theorem spr_avg_le (T : Finset Rec) (c : Cache) (q : Query) (hq : c q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Spr (c.cacheQuery q u) ξ) ≤
      ∑ ξ ∈ T, w * ind (Spr c ξ) + (ε * blockCost q.1) * sumW T := by
  rw [avg_sum_comm]
  exact sum_w_mul_le_add_charge (ε * blockCost q.1) T _ _ fun ξ _ => spr_charge c ξ q hq

theorem spr_avg_eq (T : Finset Rec) (c : Cache) (u₀ : EncInput) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Spr (c.cacheQuery (encQuery u₀) u) ξ) =
      ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Spr c ξ))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  exact spr_cacheQuery_enc c ξ u₀ u

theorem hits_charge_A' (pk : BitVec 128) {T : Finset Rec} (hT : T ⊆ fiberA pk) (q : Query) :
    ∑ ξ ∈ T, w * ind ((kc ξ q).isSome) ≤ ε * sumW (fiberA pk) :=
  calc ∑ ξ ∈ T, w * ind ((kc ξ q).isSome)
      ≤ ∑ ξ ∈ T, (if (kc ξ q).isSome then w else 0) :=
        Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ ξ ∈ fiberA pk, (if (kc ξ q).isSome then w else 0) := Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberA pk) := hits_charge_A pk q

theorem hits_charge_B' {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data) {T : Finset Rec}
    (hT : T ⊆ fiberB Ac dt) (q : Query) :
    ∑ ξ ∈ T, w * ind ((fHid (some Ac) ξ q).isSome) ≤ ε * sumW (fiberB Ac dt) :=
  calc ∑ ξ ∈ T, w * ind ((fHid (some Ac) ξ q).isSome)
      ≤ ∑ ξ ∈ T, (if (fHid (some Ac) ξ q).isSome then w else 0) :=
        Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ ξ ∈ fiberB Ac dt, (if (fHid (some Ac) ξ q).isSome then w else 0) :=
        Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberB Ac dt) := hits_charge_B hAc dt q


theorem authPotential_eq (T : Finset Rec) (A? : Option (Finset Name)) (c : Cache) :
    authPotential T A? c = (∑ ξ ∈ T, w * ind (Cache.Hits c (fHid A? ξ))) +
      ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  simp only [authPotential, mul_add, Finset.sum_add_distrib]

theorem authPotential_index (T : Finset Rec) (A? : Option (Finset Name))
    (c : Cache) (u₀ : EncInput) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T A? (c.cacheQuery (encQuery u₀) u)) = authPotential T A? c := by
  simp only [authPotential_eq, mul_add, Finset.sum_add_distrib]
  rw [hits_avg_eq _ _ _ _ (fun ξ => fHid_enc A? ξ u₀), spr_avg_eq]

theorem authPotential_charge {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (c : Cache) (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T (some Ac) (c.cacheQuery q u)) ≤
      authPotential T (some Ac) c + authRate * sumW (fiberB Ac dt) * queryCost (.inr q) := by
  simp only [authPotential_eq, mul_add, Finset.sum_add_distrib]
  have hh := (hits_avg_le T (fHid (some Ac)) c q).trans
    (add_le_add_right (hits_charge_B' hAc dt hT q) _)
  have hs := (spr_avg_le T c q hq).trans
    (add_le_add_right (mul_le_mul_right (sumW_mono hT) (ε * blockCost q.1)) _)
  have hc := mul_le_mul_right (authentication_charge_budget q) (sumW (fiberB Ac dt))
  calc
    _ ≤ ((∑ ξ ∈ T, w * ind (Cache.Hits c (fHid (some Ac) ξ))) + ε * sumW (fiberB Ac dt)) +
        ((∑ ξ ∈ T, w * ind (Spr c ξ)) + (ε * blockCost q.1) * sumW (fiberB Ac dt)) := add_le_add hh hs
    _ = ((∑ ξ ∈ T, w * ind (Cache.Hits c (fHid (some Ac) ξ))) +
        (∑ ξ ∈ T, w * ind (Spr c ξ))) + (ε + ε * blockCost q.1) * sumW (fiberB Ac dt) := by ring
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [authRate, queryCost, mul_assoc, mul_comm, mul_left_comm] using hc

/-- Only the weighted index analysis may supply these hypotheses. Non-index
queries leave this potential unchanged, so authentication and index share a budget. -/
structure IndexCharge (J : Cache → ℝ≥0∞) (rate : ℝ≥0∞) (I : Cache → ℕ → Prop) : Prop where
  fresh : ∀ c b u₀, I c b → c (encQuery u₀) = none → queryCost (.inr (encQuery u₀)) ≤ b →
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * J (c.cacheQuery (encQuery u₀) u)) ≤
      J c + rate * queryCost (.inr (encQuery u₀))
  other : ∀ c q, (∀ u₀ : EncInput, q ≠ encQuery u₀) → ∀ u, J (c.cacheQuery q u) = J c

def jointPotential (T : Finset Rec) (A? : Option (Finset Name)) (J : Cache → ℝ≥0∞)
    (c : Cache) : ℝ≥0∞ := authPotential T A? c + sumW T * J c

theorem avg_mul (a : ℝ≥0∞) (f : BitVec hashBits → ℝ≥0∞) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (a * f u)) =
      a * ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f u := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem jointPotential_charge {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (J : Cache → ℝ≥0∞) (rate : ℝ≥0∞)
    (I : Cache → ℕ → Prop) (hJ : IndexCharge J rate I) :
    ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * jointPotential T (some Ac) J (c.cacheQuery q u)) ≤
      jointPotential T (some Ac) J c +
        max authRate rate * sumW (fiberB Ac dt) * queryCost (.inr q) := by
  intro c b q hI hq hcost
  simp only [jointPotential, mul_add, Finset.sum_add_distrib]
  by_cases he : ∃ u₀ : EncInput, q = encQuery u₀
  · obtain ⟨u₀, rfl⟩ := he
    rw [authPotential_index, avg_mul]
    have h := mul_le_mul_right (hJ.fresh c b u₀ hI hq hcost) (sumW T)
    refine (add_le_add_right h _).trans ?_
    rw [mul_add]
    calc
      _ = authPotential T (some Ac) c + sumW T * J c + rate * sumW T * queryCost (.inr (encQuery u₀)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _; exact sumW_mono hT
  · have hne : ∀ u₀ : EncInput, q ≠ encQuery u₀ := by simpa only [not_exists] using he
    simp only [hJ.other c q hne, avg_const]
    have h := authPotential_charge hAc dt hT c q hq
    refine (add_le_add_left h _).trans ?_
    calc
      _ = authPotential T (some Ac) c + sumW T * J c + authRate * sumW (fiberB Ac dt) * queryCost (.inr q) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-- A single paid OracleComp continuation pays the maximum query-type rate,
not the sum of two separate full-budget estimates. -/
theorem joint_continuation {α : Type} {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (J : Cache → ℝ≥0∞) (rate : ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hIf : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b-queryCost (.inr q)))
    (hIc : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b → I c (b-queryCost (.inr q)))
    (hJ : IndexCharge J rate I) (oa : OracleComp Spec α)
    (F : α → Cache → ℝ≥0∞) (hF : ∀ x c, F x c ≤ jointPotential T (some Ac) J c)
    (c : Cache) (b : ℕ) (hI : I c b) (hB : CostAtMost oa b) :
    E (run oa c) (fun p => F p.1 p.2) ≤ jointPotential T (some Ac) J c +
      max authRate rate * sumW (fiberB Ac dt) * b :=
  master_single (max authRate rate * sumW (fiberB Ac dt)) (jointPotential T (some Ac) J)
    I hIf hIc (jointPotential_charge hAc dt hT J rate I hJ) oa F hF c b hI hB

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.authPotential_charge
#print axioms OptimalOTS.WeightedConstruction.WideForest.joint_continuation
end
end

/- Original module: Submissions.UpperCompressions.WideAuthCoupling; SHA256 1109a5bea4788ed0f731bb307b66c00566519f70303a6114b64cd55722b85de9. -/
section

/-! Uniform record-fiber coupling for arbitrary actual paid continuations.
The continuation may depend on all public disclosure data; the index potential
and its actual-law charge remain explicit hypotheses. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

theorem E_const_mul {α : Type} (p : ProbComp α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    c * E p g = E p (fun x => c * g x) := by
  rw [E, E, expectedValue_def, expectedValue_def, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun x => by ring

theorem E_finsetSum {α ι : Type} (p : ProbComp α) (s : Finset ι) (g : ι → α → ℝ≥0∞) :
    E p (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, E p (g i) :=
  expectedValue_finsetSum p s g

theorem record_regroup (T : Finset Rec) (Ac : Finset Name) (f : Rec → ℝ≥0∞) :
    (∑ ξ ∈ T, f ξ) = ∑ dt ∈ T.image (dataOf Ac), ∑ ξ ∈ T with dataOf Ac ξ = dt, f ξ :=
  (Finset.sum_fiberwise_of_maps_to (fun ξ hξ => Finset.mem_image_of_mem _ hξ) f).symm

theorem pkOf_of_subset_fiberA {pk : BitVec 128} {T : Finset Rec} (hT : T ⊆ fiberA pk) :
    ∀ ξ ∈ T, pkOf ξ = pk := by
  intro ξ hξ
  exact (Finset.mem_filter.mp (hT hξ)).2

/-- Full public-data fibers partition the public-key record fiber. Subsets may
be selected by earlier bad-event filters without assuming conditional uniformity. -/
theorem fiber_weights_le (Ac : Finset Name) {T : Finset Rec} {pk : BitVec 128}
    (hT : T ⊆ fiberA pk) :
    (∑ dt ∈ T.image (dataOf Ac), sumW (fiberB Ac dt)) ≤ sumW (fiberA pk) := by
  have hTpk := pkOf_of_subset_fiberA hT
  have hsub : ∀ dt ∈ T.image (dataOf Ac), fiberB Ac dt ⊆
      ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac)).filter
        fun ξ => dataOf Ac ξ = dt := by
    intro dt hdt
    obtain ⟨ξ₀, hξ₀T, hξ₀⟩ := Finset.mem_image.1 hdt
    have hpk₀ := hTpk ξ₀ hξ₀T
    intro ξ hξ
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and] at hξ
    have hpk : pkOf ξ = pkOf ξ₀ := by
      have := hξ.trans hξ₀.symm
      simp only [dataOf, Prod.mk.injEq] at this
      exact this.1
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hpk.trans hpk₀, ?_⟩, hξ⟩
    rw [hξ]
    exact hdt
  calc
    _ ≤ ∑ dt ∈ T.image (dataOf Ac),
        ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac))
          with dataOf Ac ξ = dt, w :=
      Finset.sum_le_sum fun dt hdt => Finset.sum_le_sum_of_subset (hsub dt hdt)
    _ = ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac)), w :=
      Finset.sum_fiberwise_of_maps_to (fun ξ hξ => (Finset.mem_filter.1 hξ).2) _
    _ ≤ sumW (fiberA pk) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- On one record fiber the actual continuation and starting cache are identical.
Exchange expectation with the finite record sum, then invoke one common budget. -/
theorem fiber_continuation {α : Type} {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (J : Cache → ℝ≥0∞) (rate : ℝ≥0∞)
    (I : Cache → ℕ → Prop)
    (hIf : ∀ c b q, I c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b-queryCost (.inr q)))
    (hIc : ∀ c b q, I c b → (c q).isSome → queryCost (.inr q) ≤ b → I c (b-queryCost (.inr q)))
    (hJ : IndexCharge J rate I) (K : Data → OracleComp Spec α)
    (d : Cache) (b : ℕ) (hI : I (Cache.extend d dt.2.2) b) (hB : CostAtMost (K dt) b) :
    (∑ ξ ∈ T, w * E (run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J p.2)) ≤
      jointPotential T (some Ac) J (Cache.extend d dt.2.2) +
        max authRate rate * sumW (fiberB Ac dt) * b := by
  have hdata : ∀ ξ ∈ T, dataOf Ac ξ = dt := by
    intro ξ hξ
    exact (Finset.mem_filter.mp (hT hξ)).2
  have hrun : ∀ ξ ∈ T,
      run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)) =
        run (K dt) (Cache.extend d dt.2.2) := by
    intro ξ hξ
    have hd := hdata ξ hξ
    have hf : fExp (some Ac) ξ = dt.2.2 := congrArg (fun a : Data => a.2.2) hd
    rw [hd, hf]
  have hsum : (∑ ξ ∈ T, w * E (run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J p.2)) =
      E (run (K dt) (Cache.extend d dt.2.2))
        (fun p => jointPotential T (some Ac) J p.2) := by
    simp only [jointPotential, authPotential, sumW, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← mul_add]
    rw [E_finsetSum]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [hrun ξ hξ, E_const_mul]
  rw [hsum]
  exact joint_continuation hAc dt hT J rate I hIf hIc hJ (K dt)
    (fun _ c => jointPotential T (some Ac) J c) (fun _ _ => le_rfl)
    (Cache.extend d dt.2.2) b hI hB

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.fiber_weights_le
#print axioms OptimalOTS.WeightedConstruction.WideForest.fiber_continuation
end
end

/- Original module: Submissions.UpperCompressions.ExpectedChargeMaster; SHA256 adfc043e20f6291b221bb0c134f815f600e033d5f7f4c3dcc9da654f0dbdd396. -/
section

/-! Expected-cost potential induction for the actual shared-cache interpreter.
The charge is accumulated on the original query stream, including cache hits. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace WeightedExpectedCharge
open OptimalOTS OptimalOTS.Dag WeightedReplacement
set_option maxHeartbeats 800000

/-- Local additive drift charges the actual expected primitive-query cost,
without replacing its expectation by the whole pathwise budget. -/
theorem master_expected {α : Type} (Φ : Cache → ℝ≥0∞)
    (charge : Spec.Domain → ℝ≥0∞) (r : ℝ≥0∞)
    (hstep : ∀ t c, E ((oracleImpl t).run c) (fun p => Φ p.2) ≤ Φ c+r*charge t)
    (oa : OracleComp Spec α) (c : Cache) :
    E (run oa c) (fun p => Φ p.2) ≤ Φ c+r*expectedCharge charge oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [run_pure, E_pure]
  | query_bind t k ih =>
    rw [run_query_bind, E_bind, expectedCharge_query]
    calc
      _ ≤ E ((oracleImpl t).run c) (fun p => Φ p.2+r*expectedCharge charge (k p.1) p.2) :=
        E_mono _ (fun p => ih p.1 p.2)
      _ = E ((oracleImpl t).run c) (fun p => Φ p.2)+
          r*E ((oracleImpl t).run c) (fun p => expectedCharge charge (k p.1) p.2) := by
        simp only [E, expectedValue_def, mul_add, ENNReal.tsum_add]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        apply tsum_congr
        intro p
        ring
      _ ≤ (Φ c+r*charge t)+r*E ((oracleImpl t).run c)
          (fun p => expectedCharge charge (k p.1) p.2) := add_le_add (hstep t c) le_rfl
      _ = _ := by ring

#print axioms master_expected
end WeightedExpectedCharge
end
end

/- Original module: Submissions.UpperCompressions.WideAuthLocality; SHA256 7ae806ea3b8fd25c9be554a04e98c5f9ccc4416e2c1329d172dff36653734ba5. -/
section

/-! Signing locality needed by graph authentication. Accepted nonwinning
signing trials are unrestricted. Only the domain of new cache entries matters. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

def IndexExtension (d d' : Cache) : Prop := Cache.Sub d d' ∧
  ∀ q v, d q = none → d' q = some v → ∃ u : EncInput, q = encQuery u

theorem sub_extend_left (c f : Cache) : Cache.Sub c (Cache.extend c f) :=
  fun _ _ h => Cache.extend_apply_of_some h

/-- With no keygen point of `ξ` in `d`, none is in `d'` either: the new entries of `d'` are
encoding entries. -/
theorem indexExtension_kc_none {d d' : Cache} (hd' : IndexExtension d d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) {q : Query} (hq : (kc ξ q).isSome) : d' q = none := by
  rcases hq' : d' q with _ | v
  · rfl
  · exfalso
    rcases hdq : d q with _ | u
    · obtain ⟨u₀, hqe⟩ := hd'.2 q v hdq hq'
      rw [hqe, kc_enc] at hq
      simp at hq
    · exact hξ ⟨q, hq, by rw [hdq]; rfl⟩

theorem not_hits_fHid_of_indexExtension {d d' : Cache} (hd' : IndexExtension d d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits d' (fHid A? ξ) := by
  rintro ⟨q, hq, hq'⟩
  have hkq : (kc ξ q).isSome := by
    obtain ⟨h, p, hp, -, hqp⟩ := (fHid_isSome_iff A? ξ q).1 hq
    exact (kc_isSome_iff ξ q).2 ⟨h, p, hp, hqp⟩
  rw [indexExtension_kc_none hd' hξ hkq] at hq'
  simp at hq'

theorem not_hits_extend_fExp_fHid {d d' : Cache} (hd' : IndexExtension d d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
  rw [Cache.hits_extend]
  rintro (h | h)
  · exact not_hits_fHid_of_indexExtension hd' hξ A? h
  · exact (disjoint_fExp_fHid A? ξ).not_hits h

theorem spr_indexExtension_iff {d d' : Cache} (hd' : IndexExtension d d')
    (ξ : Rec) : Spr d' ξ ↔ Spr d ξ := by
  constructor
  · rintro ⟨h, p, hp, u, hu, htag, w, hw, htr⟩
    refine ⟨h, p, hp, u, hu, htag, w, ?_, htr⟩
    rcases hdq : d ⟨p.len, u⟩ with _ | v
    · exfalso
      obtain ⟨u₀, hqe⟩ := hd'.2 _ w hdq hw
      exact mk_ne_encQuery hp u _ hqe
    · rw [hd'.1 _ _ hdq] at hw
      exact hw
  · exact Spr.mono hd'.1

theorem spr_extend_fExp_iff {d d' : Cache} (hd' : IndexExtension d d')
    (ξ : Rec) (A? : Option (Finset Name)) :
    Spr (Cache.extend d' (fExp A? ξ)) ξ ↔ Spr d ξ := by
  constructor
  · intro hs
    rcases spr_of_extend hs with hs | hs
    · exact (spr_indexExtension_iff hd' ξ).1 hs
    · exact absurd hs (not_spr_fExp A? ξ)
  · intro hs
    exact Spr.mono (sub_extend_left d' _) ((spr_indexExtension_iff hd' ξ).2 hs)


theorem authPotential_after_sign {d d' : Cache} (hd' : IndexExtension d d')
    (T : Finset Rec) (A? : Option (Finset Name))
    (hT : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (fe : Cache) (he : ∀ ξ ∈ T, fExp A? ξ = fe) :
    authPotential T A? (Cache.extend d' fe) = ∑ ξ ∈ T, w * ind (Spr d ξ) := by
  unfold authPotential
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [← he ξ hξ]
  have hh := not_hits_extend_fExp_fHid hd' (hT ξ hξ) A?
  have hs := spr_extend_fExp_iff hd' ξ A?
  simp only [ind, if_neg hh, hs, zero_add]

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.authPotential_after_sign
end
end

/- Original module: Submissions.UpperCompressions.AuthExpectedCost; SHA256 6335e86cca0a24a7050b8774ac9d0f8ee3552d2a6cce24a75e5e92827537cbf9. -/
section

/-! Authentication charges only actual expected non-index paid queries. Index
entries may already be privately cached or fully preloaded; no posterior law is
assumed for them and no separate copy of the whole paid budget is used. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits Finset.univ Finset.filter

/-- A caller-selected index predicate may mark only encoding hash queries as
free of graph charge. Private uniform queries have zero cost in either category. -/
theorem auth_query_expected {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (t : Spec.Domain) (c : Cache) :
    E ((oracleImpl t).run c) (fun p => authPotential T (some Ac) p.2) ≤
      authPotential T (some Ac) c +
        (authRate*sumW (fiberB Ac dt))*otherPaid isIndex t := by
  cases t with
  | inl n =>
    rw [oracleImpl_run_inl, E_bind]
    simp only [E_pure, otherPaid, queryCost]
    split_ifs <;> simpa using E_const_le (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n))
      (authPotential T (some Ac) c)
  | inr q =>
    cases hc : c q with
    | some u =>
      rw [oracleImpl_run_inr_some hc, E_pure]
      exact le_self_add
    | none =>
      rw [oracleImpl_run_inr_none hc, E_bind, E_uniform]
      simp only [E_pure]
      by_cases hi : isIndex (.inr q)
      · obtain ⟨u,rfl⟩ := hindex q hi
        rw [authPotential_index, otherPaid, if_pos hi, mul_zero, add_zero]
      · rw [otherPaid, if_neg hi]
        exact authPotential_charge hAc dt hT c q hc

/-- Graph-only master refinement, valid for the actual shared oracle from any
starting cache, including a fixed eagerly preloaded index table. -/
theorem auth_continuation_expected {α : Type} {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (oa : OracleComp Spec α) (c : Cache) :
    E (run oa c) (fun p => authPotential T (some Ac) p.2) ≤
      authPotential T (some Ac) c +
        (authRate*sumW (fiberB Ac dt))*expectedCharge (otherPaid isIndex) oa c :=
  WeightedExpectedCharge.master_expected (authPotential T (some Ac)) (otherPaid isIndex)
    (authRate*sumW (fiberB Ac dt)) (auth_query_expected hAc dt hT isIndex hindex) oa c

/-- On a disclosure fiber all records share the same reduced actual execution,
so their graph authentication loss uses one common expected paid-query clock. -/
theorem fiber_auth_expected {α : Type} {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (K : Data → OracleComp Spec α) (d : Cache) :
    (∑ ξ ∈ T, w*E (run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ))+ind (Spr p.2 ξ))) ≤
      authPotential T (some Ac) (Cache.extend d dt.2.2) +
        (authRate*sumW (fiberB Ac dt))*
          expectedCharge (otherPaid isIndex) (K dt) (Cache.extend d dt.2.2) := by
  have hdata : ∀ ξ ∈ T, dataOf Ac ξ = dt := fun ξ hξ => (Finset.mem_filter.mp (hT hξ)).2
  have hrun : ∀ ξ ∈ T,
      run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)) =
        run (K dt) (Cache.extend d dt.2.2) := by
    intro ξ hξ
    have hd := hdata ξ hξ
    have hf : fExp (some Ac) ξ = dt.2.2 := congrArg (fun a : Data => a.2.2) hd
    rw [hd,hf]
  have hsum : (∑ ξ ∈ T, w*E (run (K (dataOf Ac ξ)) (Cache.extend d (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ))+ind (Spr p.2 ξ))) =
      E (run (K dt) (Cache.extend d dt.2.2)) (fun p => authPotential T (some Ac) p.2) := by
    unfold authPotential
    rw [E_finsetSum]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [hrun ξ hξ, E_const_mul]
  rw [hsum]
  exact auth_continuation_expected hAc dt hT isIndex hindex (K dt) (Cache.extend d dt.2.2)

#print axioms auth_query_expected
#print axioms auth_continuation_expected
#print axioms fiber_auth_expected
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.ReplacementLocality; SHA256 e1b1d58b159f39aac13ee58b2e04d7eccd556f00e4fc19bb37ecc4035fa4e3d1. -/
section

/-! Cache locality of the actual all-trial signer. Accepted nonwinners remain
allowed in the implementation cache; every insertion is in the signed row. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.ReplacementLocality

open WeightedSampling

theorem hash_cache_other {n : ℕ} (x : BitVec n) (c : Cache)
    (p : BitVec hashBits × Cache) (hp : p ∈ support (run (hash x) c))
    (q : Query) (hq : q ≠ ⟨n, x⟩) : p.2 q = c q := by
  unfold OptimalOTS.hash run at hp
  rw [simulateQ_spec_query] at hp
  rcases hc : c ⟨n, x⟩ with _ | w
  · rw [oracleImpl_run_inr_none hc, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨w, _, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact QueryCache.cacheQuery_of_ne _ _ hq
  · rw [oracleImpl_run_inr_some hc, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl

theorem loop_cache_outside_row {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message) :
    ∀ k c p, p ∈ support (run (loop n decode tier m k) c) →
      ∀ q : Query, (∀ η : Nonce n, q ≠ ⟨msgBits + n, m ++ η⟩) → p.2 q = c q := by
  intro k
  induction k with
  | zero =>
    intro c p hp q hq
    rw [loop, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    rfl
  | succ k ih =>
    intro c p hp q hq
    rw [run_loop_succ, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨η, _, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨w,d⟩, hd, hp⟩ := hp
    rw [support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨r,e⟩, hr, hp⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact (ih d (r,e) hr q hq).trans (hash_cache_other _ c (w,d) hd q (hq η))

theorem loop_new_cache_row {M : ℕ} (n : ℕ)
    (decode : BitVec hashBits → Option (Fin M)) (tier : Fin M → ℕ) (m : Message)
    (k : ℕ) (c : Cache) (p : Option (Winner n M) × Cache)
    (hp : p ∈ support (run (loop n decode tier m k) c))
    (q : Query) (w : BitVec hashBits) (hc : c q = none) (he : p.2 q = some w) :
    ∃ η : Nonce n, q = ⟨msgBits + n, m ++ η⟩ := by
  by_contra h
  have hq : ∀ η : Nonce n, q ≠ ⟨msgBits + n, m ++ η⟩ := by simpa using h
  have ho := loop_cache_outside_row n decode tier m k c p hp q hq
  rw [he, hc] at ho
  cases ho

theorem sign_cache_outside_row {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache) (hp : p ∈ support (run (S.sign x m) c))
    (q : Query) (hq : ∀ η : Nonce 86, q ≠ ⟨msgBits + 86, m ++ η⟩) :
    p.2 q = c q := by
  rw [WeightedScheme.Scheme.sign, run_map, support_map, Set.mem_image] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  exact loop_cache_outside_row 86 S.decode S.tier m signBudget c p' hp' q hq

theorem sign_new_cache_row {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache) (hp : p ∈ support (run (S.sign x m) c))
    (q : Query) (w : BitVec hashBits) (hc : c q = none) (he : p.2 q = some w) :
    ∃ η : Nonce 86, q = ⟨msgBits + 86, m ++ η⟩ := by
  by_contra h
  have hq : ∀ η : Nonce 86, q ≠ ⟨msgBits + 86, m ++ η⟩ := by simpa using h
  have ho := sign_cache_outside_row S x m c p hp q hq
  rw [he, hc] at ho
  cases ho

end OptimalOTS.ReplacementLocality

#print axioms OptimalOTS.ReplacementLocality.loop_new_cache_row
#print axioms OptimalOTS.ReplacementLocality.sign_new_cache_row
end
end

/- Original module: Submissions.UpperCompressions.WideAuthSigning; SHA256 e99794234af028e7d3f289380b8ae39b0eb05d3aca0ae7009463154aca0cd266. -/
section

/-! The actual all-L signer satisfies precisely the graph locality interface.
No restriction is placed on its accepted nonwinning cache entries. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

theorem sign_indexExtension {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) c)) : IndexExtension c p.2 := by
  refine ⟨sub_of_mem_support_run _ c p hp, ?_⟩
  intro q v hc he
  obtain ⟨η, hη⟩ := ReplacementLocality.sign_new_cache_row S x m c p hp q v hc he
  exact ⟨(m, η), hη⟩

/-- After an actual supported signing run, graph hidden hits remain absent and
spurious graph images agree with their pre-sign values on every public-data fiber. -/
theorem authPotential_after_actual_sign {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) c))
    (T : Finset Rec) (A? : Option (Finset Name))
    (hT : ∀ ξ ∈ T, ¬ Cache.Hits c (kc ξ))
    (fe : Cache) (he : ∀ ξ ∈ T, fExp A? ξ = fe) :
    authPotential T A? (Cache.extend p.2 fe) = ∑ ξ ∈ T, w * ind (Spr c ξ) :=
  authPotential_after_sign (sign_indexExtension S x m c p hp) T A? hT fe he

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.authPotential_after_actual_sign
end
end

/- Original module: Submissions.UpperCompressions.AuthExpectedAssembly; SHA256 d9f414406aa0957f0d16f4aa78229d88e19b1b31eea93b2683e4d17916451305. -/
section

/-! Graph authentication after the actual all-L signer, retaining the expected
non-index paid clock of the reduced continuation on each disclosure fiber. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement
set_option maxHeartbeats 800000
attribute [local irreducible] hashBits blockBits msgBits Finset.univ Finset.filter

/-- Weighted full disclosure fibers lie inside the public-key record fiber.
The weight may be an expected cost of the actual fiber-dependent continuation. -/
theorem fiber_costs_le (Ac : Finset Name) {T : Finset Rec} {pk : BitVec 128}
    (hT : T ⊆ fiberA pk) (F : Data → ℝ≥0∞) :
    (∑ dt ∈ T.image (dataOf Ac), sumW (fiberB Ac dt)*F dt) ≤
      ∑ ξ ∈ fiberA pk, w*F (dataOf Ac ξ) := by
  have hTpk := pkOf_of_subset_fiberA hT
  have hsub : ∀ dt ∈ T.image (dataOf Ac), fiberB Ac dt ⊆
      ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac)).filter
        fun ξ => dataOf Ac ξ = dt := by
    intro dt hdt
    obtain ⟨ξ₀, hξ₀T, hξ₀⟩ := Finset.mem_image.1 hdt
    have hpk₀ := hTpk ξ₀ hξ₀T
    intro ξ hξ
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and] at hξ
    have hpk : pkOf ξ = pkOf ξ₀ := by
      have := hξ.trans hξ₀.symm
      simp only [dataOf, Prod.mk.injEq] at this
      exact this.1
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨hpk.trans hpk₀, ?_⟩, hξ⟩
    rw [hξ]
    exact hdt
  have hcost (dt : Data) : sumW (fiberB Ac dt)*F dt =
      ∑ ξ ∈ fiberB Ac dt, w*F (dataOf Ac ξ) := by
    rw [sumW, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [(Finset.mem_filter.mp hξ).2]
  calc
    _ = ∑ dt ∈ T.image (dataOf Ac), ∑ ξ ∈ fiberB Ac dt, w*F (dataOf Ac ξ) :=
      Finset.sum_congr rfl fun dt _ => hcost dt
    _ ≤ ∑ dt ∈ T.image (dataOf Ac),
        ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac))
          with dataOf Ac ξ = dt, w*F (dataOf Ac ξ) :=
      Finset.sum_le_sum fun dt hdt => Finset.sum_le_sum_of_subset (hsub dt hdt)
    _ = ∑ ξ ∈ ((fiberA pk).filter fun ξ => dataOf Ac ξ ∈ T.image (dataOf Ac)),
        w*F (dataOf Ac ξ) :=
      Finset.sum_fiberwise_of_maps_to (fun ξ hξ => (Finset.mem_filter.1 hξ).2) _
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The signer's private index-only extension creates no graph authentication
loss. The remaining charge is the actual expected non-index cost, averaged over
the full public-key record fiber; it is not a second copy of the paid budget. -/
theorem postsign_auth_expected {α : Type} {Ac : Finset Name} (hAc : IsCut Ac)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (d d' : Cache) (hd' : IndexExtension d d')
    (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (K : Data → OracleComp Spec α) :
    (∑ ξ ∈ T, w*E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ))+ind (Spr p.2 ξ))) ≤
      (∑ ξ ∈ T, w*ind (Spr d ξ)) +
        authRate * ∑ ξ ∈ fiberA pk, w *
          expectedCharge (otherPaid isIndex) (K (dataOf Ac ξ))
            (Cache.extend d' (fExp (some Ac) ξ)) := by
  have hfiber : ∀ dt ∈ T.image (dataOf Ac),
      (∑ ξ ∈ T with dataOf Ac ξ = dt,
        w*E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ))+ind (Spr p.2 ξ))) ≤
      (∑ ξ ∈ T with dataOf Ac ξ = dt, w*ind (Spr d ξ)) +
        authRate * (sumW (fiberB Ac dt)*
          expectedCharge (otherPaid isIndex) (K dt) (Cache.extend d' dt.2.2)) := by
    intro dt hdt
    let Td := T.filter fun ξ => dataOf Ac ξ = dt
    have hdata : ∀ ξ ∈ Td, dataOf Ac ξ = dt := fun ξ hξ => (Finset.mem_filter.mp hξ).2
    have hsub : Td ⊆ fiberB Ac dt := by
      intro ξ hξ
      simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdata ξ hξ
    have hfe : ∀ ξ ∈ Td, fExp (some Ac) ξ = dt.2.2 :=
      fun ξ hξ => congrArg (fun a : Data => a.2.2) (hdata ξ hξ)
    have hc := fiber_auth_expected hAc dt hsub isIndex hindex K d'
    rw [authPotential_after_sign hd' Td (some Ac)
      (fun ξ hξ => hTd ξ (Finset.mem_filter.mp hξ).1) dt.2.2 hfe] at hc
    simpa only [mul_assoc] using hc
  rw [record_regroup T Ac, record_regroup T Ac (fun ξ => w*ind (Spr d ξ))]
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  apply add_le_add_right
  apply mul_le_mul_right
  exact fiber_costs_le Ac hT (fun dt =>
    expectedCharge (otherPaid isIndex) (K dt) (Cache.extend d' dt.2.2))

/-- The graph refinement applies to every supported outcome of the actual
all-L signer, including its accepted nonwinning cached index entries. -/
theorem actual_sign_auth_expected {α : Type} {M : ℕ} (S : WeightedScheme.Scheme M)
    (x : S.graph.Assignment) (m : Message) (d : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) d))
    {Ac : Finset Name} (hAc : IsCut Ac)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (isIndex : Spec.Domain → Prop)
    (hindex : ∀ q, isIndex (.inr q) → ∃ u : EncInput, q = encQuery u)
    (K : Data → OracleComp Spec α) :
    (∑ ξ ∈ T, w*E (run (K (dataOf Ac ξ)) (Cache.extend p.2 (fExp (some Ac) ξ)))
      (fun z => ind (Cache.Hits z.2 (fHid (some Ac) ξ))+ind (Spr z.2 ξ))) ≤
      (∑ ξ ∈ T, w*ind (Spr d ξ)) +
        authRate * ∑ ξ ∈ fiberA pk, w *
          expectedCharge (otherPaid isIndex) (K (dataOf Ac ξ))
            (Cache.extend p.2 (fExp (some Ac) ξ)) :=
  postsign_auth_expected hAc pk T hT d p.2 (sign_indexExtension S x m d p hp)
    hTd isIndex hindex K

/-- Index and graph loss share one actual expected paid-query clock on every
record, before averaging. Both costs use exactly the same program and cache. -/
theorem record_shared_paid_budget {α : Type} (Ac : Finset Name) (pk : BitVec 128)
    (d' : Cache) (isIndex : Spec.Domain → Prop) (a b : ℝ≥0∞)
    (K : Data → OracleComp Spec α) (B : ℕ)
    (hB : ∀ ξ ∈ fiberA pk, CostAtMost (K (dataOf Ac ξ)) B) :
    a * (∑ ξ ∈ fiberA pk, w * expectedCharge (indexPaid isIndex)
      (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ))) +
    b * (∑ ξ ∈ fiberA pk, w * expectedCharge (otherPaid isIndex)
      (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ))) ≤
      max a b * sumW (fiberA pk) * B := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ ξ ∈ fiberA pk, w * (a * expectedCharge (indexPaid isIndex)
        (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)) +
        b * expectedCharge (otherPaid isIndex)
        (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ))) := by
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    _ ≤ ∑ ξ ∈ fiberA pk, w*(max a b*B) :=
      Finset.sum_le_sum fun ξ hξ => mul_le_mul_right
        (paid_shared_budget isIndex a b (K (dataOf Ac ξ))
          (Cache.extend d' (fExp (some Ac) ξ)) B (hB ξ hξ)) w
    _ = _ := by rw [← Finset.sum_mul, ← sumW]; ring

#print axioms fiber_costs_le
#print axioms postsign_auth_expected
#print axioms actual_sign_auth_expected
#print axioms record_shared_paid_budget
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.WideEvents; SHA256 a30a2cd079949592c6f4d176c36424c6f5396d40254832fdea07bc2a320c0b97. -/
section

/-!
# From an accepted forgery to a bad event

Let the verifier reconstruct the root from values `given` at the disclosure set `A'` and obtain the
assignment `y`, all answers being recorded in the cache `d` (`Graph.ReconEqs`), and accept:
the first 128 bits of `y` at the root are the public key of the honest record `ξ`.

* `up` (the walk in the proof of the paper's Section 7.3): if `y` differs from the honest values at a
  non-hash node visited by the reconstruction, some recorded answer at a non-keygen point begins
  with an honest value (`Spr d ξ`).
* `events_none`: if nothing was exposed, then `Spr d ξ` or the root's keygen point was queried.
* `events_ne`: if the signature revealed the cut `A ≠ A'` of the same cost, then `Spr d ξ` or a
  keygen point hidden at `A` was queried.
* `events_same`: if `A' = A` and the supplied values differ from the honest ones, `Spr d ξ`.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace WeightedConstruction.WideForest

open Name

/-- The verifier's value at a node. -/
def yv (y : graph.Assignment) (n : Name) : BitVec n.len := (y n.fin).cast (graph_len_fin n)

/-! ## Bit-vector helpers -/

theorem sigma_cast {a b : ℕ} (h : a = b) (x : BitVec a) :
    (⟨a, x⟩ : Σ k : ℕ, BitVec k) = ⟨b, x.cast h⟩ := by subst h; rfl

theorem lowPk_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) : lowPk (x.cast h) = lowPk x := by
  subst h; rfl

theorem lowWord_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) : lowWord (x.cast h) = lowWord x := by
  subst h; rfl

theorem lowWord_129 (x : BitVec 129) : lowWord x = x := BitVec.setWidth_eq x

theorem lowWord_eq_cast {m : ℕ} (h : m = 129) (x : BitVec m) : lowWord x = x.cast h := by
  subst h; exact BitVec.setWidth_eq x

theorem cast_injective {n m : ℕ} (h : n = m) {x y : BitVec n} (e : x.cast h = y.cast h) :
    x = y := by
  subst h; simpa using e

/-- Both halves of a concatenation are determined by it (any widths; `append_inj` of `Names.lean`
is the special case of a 16-bit tweak). -/
theorem bv_append_inj {n m : ℕ} {x x' : BitVec n} {y y' : BitVec m} (h : x ++ y = x' ++ y') :
    x = x' ∧ y = y' := by
  have key : ∀ i, (x ++ y).getLsbD i = (x' ++ y').getLsbD i := fun i => by rw [h]
  simp only [BitVec.getLsbD_append] at key
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := key (i + m)
    simp only [show ¬ (i + m < m) by omega, if_false, Nat.add_sub_cancel] at this
    exact this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := key i
    simpa [hi] using this

theorem cat3_inj {a b c a' b' c' : BitVec 129} (h : cat3 a b c = cat3 a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  unfold cat3 at h
  obtain ⟨h12, h3⟩ := bv_append_inj (cast_injective _ h)
  obtain ⟨h1, h2⟩ := bv_append_inj h12
  exact ⟨h1, h2, h3⟩

theorem cat18_inj {a b : Fin 18 → BitVec 129} (h : cat18 a = cat18 b) : a = b := by
  unfold cat18 at h
  obtain ⟨hprefix16, h17⟩ := bv_append_inj (cast_injective _ h)
  obtain ⟨hprefix15, h16⟩ := bv_append_inj hprefix16
  obtain ⟨hprefix14, h15⟩ := bv_append_inj hprefix15
  obtain ⟨hprefix13, h14⟩ := bv_append_inj hprefix14
  obtain ⟨hprefix12, h13⟩ := bv_append_inj hprefix13
  obtain ⟨hprefix11, h12⟩ := bv_append_inj hprefix12
  obtain ⟨hprefix10, h11⟩ := bv_append_inj hprefix11
  obtain ⟨hprefix9, h10⟩ := bv_append_inj hprefix10
  obtain ⟨hprefix8, h9⟩ := bv_append_inj hprefix9
  obtain ⟨hprefix7, h8⟩ := bv_append_inj hprefix8
  obtain ⟨hprefix6, h7⟩ := bv_append_inj hprefix7
  obtain ⟨hprefix5, h6⟩ := bv_append_inj hprefix6
  obtain ⟨hprefix4, h5⟩ := bv_append_inj hprefix5
  obtain ⟨hprefix3, h4⟩ := bv_append_inj hprefix4
  obtain ⟨hprefix2, h3⟩ := bv_append_inj hprefix3
  obtain ⟨hprefix1, h2⟩ := bv_append_inj hprefix2
  obtain ⟨hprefix0, h1⟩ := bv_append_inj hprefix1
  funext l
  fin_cases l <;> assumption

/-! ## Names -/

theorem cost_eq_zero_of_len {n : Name} (h : n.len = 129) : n.cost = 0 := by
  cases n <;> first | rfl | (simp [Name.len] at h)

theorem len_eq_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.len = 256 := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp <;> rfl

theorem hashParent_cases {h p : Name} (hp : hashParent h = some p) :
    h = rh ∨ ∃ v, hashOf v = some h := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp
  · exact Or.inr ⟨cv _ _, rfl⟩
  · exact Or.inr ⟨gv _, rfl⟩
  · exact Or.inl rfl

/-- The input of a hash node is a deterministic node. -/
theorem cost_hashParent {h p : Name} (hp : hashParent h = some p) : p.cost = 0 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;> rfl

theorem hashParent_ne_src {h p : Name} (hp : hashParent h = some p) (k : Fin 54) : p ≠ src k := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact fun e => nomatch e

theorem hashParent_of_hashOf {v h : Name} (hh : hashOf v = some h) : ∃ p, hashParent h = some p := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh <;>
    exact ⟨_, rfl⟩

theorem ne_rh_of_hashOf {v h : Name} (hh : hashOf v = some h) : h ≠ rh := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh <;>
    exact fun e => nomatch e

theorem cost_of_hashOf {v h : Name} (hh : hashOf v = some h) : v.cost = 0 := by
  cases v <;> simp only [hashOf, reduceCtorEq] at hh <;> rfl

theorem prev_succ (k : Fin 54) (t : Fin 18) (ht : t.val < 17) :
    prev k ⟨t.val + 1, by omega⟩ = cv k t := by
  simp [prev]

theorem val_gc' (ξ : Rec) (j : Fin 18) :
    val ξ (gc j) = tw (gh j) ++ cat3 (val ξ (cv (chainOf j 0) 17)) (val ξ (cv (chainOf j 1) 17))
      (val ξ (cv (chainOf j 2) 17)) := by
  rw [val_gc, val_cv, val_cv, val_cv]


theorem val_rc' (ξ : Rec) : val ξ rc = tw rh ++ cat18 fun l => val ξ (gv l) := by
  rw [val_rc]
  exact congrArg (fun a => tw rh ++ cat18 a) (funext fun l => (val_gv ξ l).symm)

theorem val_of_hashOf (ξ : Rec) {v h : Name} (hh : hashOf v = some h) :
    lowWord (val ξ v) = lowWord (ξ.2 h.fin) := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh
  · rw [val_cv]; exact lowWord_129 _
  · rw [val_gv]; exact lowWord_129 _

/-! ## The kinds of the nodes -/

theorem graph_kind_hash {h p : Name} (hp : hashParent h = some p) :
    ∃ (hlt : p.fin < h.fin) (hl : graph.len h.fin = hashBits),
      graph.kind h.fin = .hash p.fin hlt hl := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact ⟨_, _, rfl⟩

theorem graph_kind_det {n : Name} (hc : n.cost = 0) (hs : ∀ k, n ≠ src k) :
    ∃ (hlt : ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, w < n.fin)
      (hf : ∀ x y : Asg, (∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, x w = y w) →
        (detVal n x).cast (graph_len_fin n).symm = (detVal n y).cast (graph_len_fin n).symm),
      graph.kind n.fin = .det ((Name.parents n).map nameEquiv.toEmbedding) hlt
        (fun x => (detVal n x).cast (graph_len_fin n).symm) hf := by
  rw [graph_kind_fin]
  cases n
  · exact absurd rfl (hs _)
  all_goals first | exact ⟨_, _, rfl⟩ | (simp [Name.cost] at hc)

/-! ## The reconstruction equations in terms of names -/

section Recon

variable {A : Finset Name} {d : Cache} {given y : graph.Assignment}

theorem yv_mem (hy : graph.ReconEqs d (fins A) given y) {n : Name} (hn : n ∈ A) :
    yv y n = (given n.fin).cast (graph_len_fin n) := by
  unfold yv
  rw [(hy n.fin).1 ((mem_fins A n).mpr hn)]

theorem recon_evaluated (hy : graph.ReconEqs d (fins A) given y) {n : Name}
    (he : Evaluated A n) :
    (∀ p hp hl, graph.kind n.fin = .hash p hp hl →
        ∃ w, d ⟨graph.len p, y p⟩ = some w ∧ y n.fin = w.cast hl.symm) ∧
      (∀ ps hlt f hf, graph.kind n.fin = .det ps hlt f hf → y n.fin = f y) ∧
      (graph.kind n.fin = .source → y n.fin = 0) :=
  (hy n.fin).2.2 (fun h => he.1 ((mem_fins A n).mp h)) ((visited_iff A n).mpr he.2)

/-- The hash equation at an evaluated hash node. -/
theorem yv_hash (hy : graph.ReconEqs d (fins A) given y) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) :
    ∃ w, d ⟨p.len, yv y p⟩ = some w ∧ lowWord w = lowWord (yv y h) := by
  obtain ⟨hlt, hl, hk⟩ := graph_kind_hash hp
  obtain ⟨w, hw, hyw⟩ := (recon_evaluated hy he).1 _ _ _ hk
  refine ⟨w, ?_, ?_⟩
  · rw [sigma_cast (graph_len_fin p) (y p.fin)] at hw
    exact hw
  · unfold yv
    rw [lowWord_cast_eq, hyw, lowWord_cast_eq]

/-- The same actual hash equation at the public-key binding width. -/
theorem yv_hash_lowPk (hy : graph.ReconEqs d (fins A) given y) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) :
    ∃ w, d ⟨p.len, yv y p⟩ = some w ∧ lowPk w = lowPk (yv y h) := by
  obtain ⟨hlt, hl, hk⟩ := graph_kind_hash hp
  obtain ⟨w, hw, hyw⟩ := (recon_evaluated hy he).1 _ _ _ hk
  refine ⟨w, ?_, ?_⟩
  · rw [sigma_cast (graph_len_fin p) (y p.fin)] at hw
    exact hw
  · unfold yv
    rw [lowPk_cast_eq, hyw, lowPk_cast_eq]

/-- The value of an evaluated deterministic node. -/
theorem yv_det (hy : graph.ReconEqs d (fins A) given y) {n : Name} (he : Evaluated A n)
    (hc : n.cost = 0) (hs : ∀ k, n ≠ src k) : yv y n = detVal n y := by
  obtain ⟨hlt, hf, hk⟩ := graph_kind_det hc hs
  have := (recon_evaluated hy he).2.1 _ _ _ _ hk
  unfold yv
  rw [this]
  simp

theorem yv_cv (hy : graph.ReconEqs d (fins A) given y) {k : Fin 54} {t : Fin 18}
    (he : Evaluated A (cv k t)) : yv y (cv k t) = lowWord (yv y (ch k t)) := by
  rw [yv_det hy he rfl (by simp)]
  show lowWord (y _) = _
  unfold yv
  rw [lowWord_cast_eq]

theorem yv_gv (hy : graph.ReconEqs d (fins A) given y) {j : Fin 18}
    (he : Evaluated A (gv j)) : yv y (gv j) = lowWord (yv y (gh j)) := by
  rw [yv_det hy he rfl (by simp)]
  show lowWord (y _) = _
  unfold yv
  rw [lowWord_cast_eq]


/-- The input of a chain hash: its tweak, then the value before it. -/
theorem yv_ci (hy : graph.ReconEqs d (fins A) given y) {k : Fin 54} {t : Fin 18}
    (he : Evaluated A (ci k t)) : yv y (ci k t) = tw (ch k t) ++ lowWord (yv y (prev k t)) := by
  rw [yv_det hy he rfl (by simp)]
  show tw (ch k t) ++ lowWord (y (prev k t).fin) = _
  unfold yv
  rw [lowWord_cast_eq]

theorem yv_gc (hy : graph.ReconEqs d (fins A) given y) {j : Fin 18}
    (he : Evaluated A (gc j)) :
    yv y (gc j) = tw (gh j) ++ cat3 (yv y (cv (chainOf j 0) 17)) (yv y (cv (chainOf j 1) 17))
      (yv y (cv (chainOf j 2) 17)) := by
  rw [yv_det hy he rfl (by simp)]
  show tw (gh j) ++ cat3 (lowWord (y _)) (lowWord (y _)) (lowWord (y _)) = _
  refine congrArg (fun a => tw (gh j) ++ a) ?_
  congr 1 <;> exact lowWord_eq_cast (graph_len_fin _) _


theorem yv_rc (hy : graph.ReconEqs d (fins A) given y) (he : Evaluated A rc) :
    yv y rc = tw rh ++ cat18 fun l => yv y (gv l) := by
  rw [yv_det hy he rfl (by simp)]
  show tw rh ++ cat18 (fun l => lowWord (y (gv l).fin)) = _
  exact congrArg (fun a => tw rh ++ cat18 a)
    (funext fun l => lowWord_eq_cast (graph_len_fin (gv l)) _)

theorem yv_of_hashOf (hy : graph.ReconEqs d (fins A) given y) {v h : Name}
    (hh : hashOf v = some h) (he : Evaluated A v) : lowWord (yv y v) = lowWord (yv y h) := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh
  · rw [yv_cv hy he]; exact lowWord_129 _
  · rw [yv_gv hy he]; exact lowWord_129 _

/-- A forged chain input differs from the honest one as soon as the value before it does. -/
theorem yv_ci_ne (hy : graph.ReconEqs d (fins A) given y) {k : Fin 54} {t : Fin 18}
    (he : Evaluated A (ci k t)) {ξ : Rec} (hne : yv y (prev k t) ≠ val ξ (prev k t)) :
    yv y (ci k t) ≠ val ξ (ci k t) := by
  intro heq
  rw [yv_ci hy he, val_ci] at heq
  exact hne (lowWord_injective_of_len (Name.len_prev k t) (tw_append_inj (n := 129) heq).2)

/-- The input of an evaluated hash node is evaluated: it is not in the cut (its length is not
129), and everything above it is the hash node or above the hash node. -/
theorem evaluated_hashParent (hA : IsCut A) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) : Evaluated A p := by
  refine ⟨fun hm => ?_, fun m hm => ?_⟩
  · have h128 := hA.values p hm
    rcases len_hashParent_cases hp with e | e | e <;> omega
  · rw [above_of_child (child_hashParent hp)] at hm
    rcases hm with rfl | hm
    · exact he.1
    · exact he.2 m hm

/-- The forged input of an evaluated hash node is its deterministic function of the forged
assignment. -/
theorem yv_hashParent (hA : IsCut A) (hy : graph.ReconEqs d (fins A) given y) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) : yv y p = detVal p y :=
  yv_det hy (evaluated_hashParent hA hp he) (cost_hashParent hp) (hashParent_ne_src hp)

/-- The forged input of an evaluated hash node carries the tweak of that node. -/
theorem tagNat_yv (hA : IsCut A) (hy : graph.ReconEqs d (fins A) given y) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) : tagNat ⟨p.len, yv y p⟩ = h.idx := by
  rw [yv_hashParent hA hy hp he]
  exact tagNat_detVal_of_hashParent hp y

end Recon

/-! ## The walk -/

/-- One step of the walk through a hash node: `v` feeds the hash node `h`. -/
theorem hash_step {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y rh) = pkOf ξ) {v h : Name} (hch : child v = some h)
    (hhp : hashParent h = some v) (hv : ∀ m, Above m v → m ∉ A)
    (hne : yv y v ≠ val ξ v)
    (ih : ∀ v', height v' < height v → (∀ m, Above m v' → m ∉ A) → v'.cost = 0 →
      yv y v' ≠ val ξ v' → Spr d ξ) : Spr d ξ := by
  have h256 : h.len = 256 := len_eq_of_hashParent hhp
  have hhA : h ∉ A := fun hm => by have := hA.values h hm; omega
  have hhE : Evaluated A h := ⟨hhA, fun m hm => hv m (Above.step hch hm)⟩
  rcases hashParent_cases hhp with rfl | ⟨v', hv'⟩
  · obtain ⟨w, hd, hw⟩ := yv_hash_lowPk hy hhp hhE
    refine ⟨rh, v, hhp, yv y v, hne, tagNat_yv hA hy hhp hhE, w, hd, ?_⟩
    change lowPk w = pkOf ξ
    exact hw.trans hacc
  · have hroot : h ≠ rh := ne_rh_of_hashOf hv'
    obtain ⟨w, hd, hw⟩ := yv_hash hy hhp hhE
    by_cases hsp : lowWord w = lowWord (ξ.2 h.fin)
    · refine ⟨h, v, hhp, yv y v, hne, tagNat_yv hA hy hhp hhE, w, hd, ?_⟩
      unfold bindingValue
      rw [show bindingWidth h = 129 from if_neg hroot]
      exact hsp
    · have hcv' : child h = some v' := child_hashOf hv'
      have hv'E : Evaluated A v' :=
        ⟨hv v' (Above.step hch (Above.child hcv')),
          fun m hm => hv m (Above.step hch (Above.step hcv' hm))⟩
      refine ih v' ?_ hv'E.2 (cost_of_hashOf hv') ?_
      · have h1 := height_child hch
        have h2 := height_child hcv'
        omega
      · intro heq
        apply hsp
        rw [hw, ← yv_of_hashOf hy hv' hv'E, heq, val_of_hashOf ξ hv']

/-- **The walk.** -/
theorem up {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y rh) = pkOf ξ) {v : Name} (hv : ∀ m, Above m v → m ∉ A)
    (hvh : v.cost = 0) (hne : yv y v ≠ val ξ v) : Spr d ξ := by
  suffices ∀ n, ∀ v, height v = n → (∀ m, Above m v → m ∉ A) → v.cost = 0 →
      yv y v ≠ val ξ v → Spr d ξ from this _ v rfl hv hvh hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv hvh hne
    have ih' : ∀ v', height v' < height v → (∀ m, Above m v' → m ∉ A) → v'.cost = 0 →
        yv y v' ≠ val ξ v' → Spr d ξ :=
      fun v' hlt => ih (height v') (by omega) v' rfl
    cases v with
    | src k =>
      have hch : child (src k) = some (ci k 0) := rfl
      have hcE : Evaluated A (ci k 0) :=
        ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
      refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
      exact yv_ci_ne hy hcE hne
    | ci k t =>
      exact hash_step hA hy hacc (h := ch k t) rfl rfl hv hne ih'
    | cv k t =>
      by_cases ht : t.val = 17
      · have ht' : t = 17 := Fin.ext ht
        subst ht'
        have hch : child (cv k 17) = some (gc ⟨k / 3, by omega⟩) := by simp [Name.child]
        have hcE : Evaluated A (gc ⟨k / 3, by omega⟩) :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        intro heq
        rw [yv_gc hy hcE, val_gc'] at heq
        obtain ⟨h0, h1, h2⟩ := cat3_inj (append_inj (n := 387) heq).2
        have hk : (k : ℕ) % 3 = 0 ∨ (k : ℕ) % 3 = 1 ∨ (k : ℕ) % 3 = 2 := by omega
        rcases hk with hk | hk | hk
        · have e : chainOf ⟨k / 3, by omega⟩ 0 = k := Fin.ext (by simp [chainOf]; omega)
          rw [e] at h0
          exact hne h0
        · have e : chainOf ⟨k / 3, by omega⟩ 1 = k := Fin.ext (by simp [chainOf]; omega)
          rw [e] at h1
          exact hne h1
        · have e : chainOf ⟨k / 3, by omega⟩ 2 = k := Fin.ext (by simp [chainOf]; omega)
          rw [e] at h2
          exact hne h2
      · have hch : child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by simp [Name.child, ht]
        have hcE : Evaluated A (ci k ⟨t.val + 1, by omega⟩) :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        refine yv_ci_ne hy hcE ?_
        rw [prev_succ k t (by omega)]
        exact hne
    | gc j =>
      exact hash_step hA hy hacc (h := gh j) rfl rfl hv hne ih'
    | gv j =>
      have hch : child (gv j) = some rc := rfl
      have hcE : Evaluated A rc :=
        ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
      refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
      intro heq
      rw [yv_rc hy hcE, val_rc'] at heq
      exact hne (congrFun (cat18_inj (append_inj (n := 2322) heq).2) j)
    | rc =>
      exact hash_step hA hy hacc (h := rh) rfl rfl hv hne ih'
    | ch k t => exact absurd hvh (by simp [Name.cost])
    | gh j => exact absurd hvh (by simp [Name.cost])
    | rh => exact absurd hvh (by simp [Name.cost])

/-! ## The events -/

/-- Signing failed: everything is hidden. -/
theorem events_none {A' : Finset Name} (hA' : IsCut A') {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A') given y)
    (hacc : lowPk (yv y rh) = pkOf ξ) : Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  have hrE : Evaluated A' rh := ⟨hA'.rh_not_mem, fun m hm => absurd hm (not_above_rh m)⟩
  obtain ⟨w, hd, -⟩ := yv_hash hy (p := rc) rfl hrE
  by_cases hne : yv y rc = val ξ rc
  · right
    refine ⟨⟨rc.len, yv y rc⟩, ?_, by rw [hd]; rfl⟩
    rw [kc_isSome_iff]
    exact ⟨rh, rc, rfl, by rw [hne]; rfl⟩
  · left
    refine up hA' hy hacc (v := rc) ?_ rfl hne
    intro m hm
    rw [above_of_child (show child rc = some rh from rfl)] at hm
    rcases hm with rfl | hm
    · exact hA'.rh_not_mem
    · exact absurd hm (not_above_rh m)

/-- The forgery uses a different disclosure set of the same cost. -/
theorem events_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hcost : ∑ n ∈ evaluatedSet A, n.cost = ∑ n ∈ evaluatedSet A', n.cost) (hne : A ≠ A')
    {ξ : Rec} {d : Cache} {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y) (hacc : lowPk (yv y rh) = pkOf ξ) :
    Spr d ξ ∨ Cache.Hits d (fHid (some A) ξ) := by
  obtain ⟨v, hvA, hvE⟩ := exists_mem_evaluated_of_ne hA hA' hcost hne
  have hlen : v.len = 129 := hA.values v hvA
  have hns : ∀ k, v ≠ src k := by
    intro k hk
    subst hk
    rcases hA'.covers k with h | ⟨m, hmA', hm⟩
    · exact hvE.1 h
    · exact hvE.2 m hm hmA'
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((hashOf_isSome_iff v).mpr ⟨hlen, hns⟩)
  have hch : child h = some v := child_hashOf hh
  have hhA' : h ∉ A' := fun hm => by
    have := hA'.values h hm
    rw [len_of_hashOf hh] at this
    omega
  have hhE : Evaluated A' h := by
    refine ⟨hhA', fun m hm => ?_⟩
    rw [above_of_child hch] at hm
    rcases hm with rfl | hm
    · exact hvE.1
    · exact hvE.2 m hm
  obtain ⟨p, hhp⟩ := hashParent_of_hashOf hh
  by_cases hvne : yv y v = val ξ v
  · obtain ⟨w, hd, hw⟩ := yv_hash hy hhp hhE
    have htr : lowWord w = lowWord (ξ.2 h.fin) := by
      rw [hw, ← yv_of_hashOf hy hh hvE, hvne, val_of_hashOf ξ hh]
    by_cases hpne : yv y p = val ξ p
    · right
      refine ⟨⟨p.len, yv y p⟩, ?_, by rw [hd]; rfl⟩
      rw [fHid_isSome_some_iff]
      exact ⟨h, p, hhp, hA.not_evaluated_hashOf hvA hh, by rw [hpne]; rfl⟩
    · left
      refine ⟨h, p, hhp, yv y p, hpne, tagNat_yv hA' hy hhp hhE, w, hd, ?_⟩
      unfold bindingValue
      rw [show bindingWidth h = 129 from if_neg (ne_rh_of_hashOf hh)]
      exact htr
  · left
    exact up hA' hy hacc hvE.2 (cost_of_hashOf hh) hvne

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget trials

/-- `encode` only reads the values on the set. -/
theorem encode_congr (G : Graph) (A : Finset (Fin G.size))
    {x x' : G.Assignment} (h : ∀ v ∈ A, x v = x' v) : G.encode A x = G.encode A x' := by
  unfold Graph.encode
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_filter, decide_eq_true_iff] at hv
  rw [h v hv.2]

attribute [local semireducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget trials

/-- The forgery uses the signed disclosure set with different values. -/
theorem events_same {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {x' : List Bool} {y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A) (graph.decode (fins A) x') y)
    (hacc : lowPk (yv y rh) = pkOf ξ) (hlen : x'.length = graph.revealBits (fins A))
    (hne : x' ≠ graph.encode (fins A) (graph.evalRec ξ)) : Spr d ξ := by
  have hex : ∃ a ∈ A, graph.decode (fins A) x' a.fin ≠ graph.evalRec ξ a.fin := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← graph.encode_decode (fins A) x' hlen]
    apply encode_congr
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact hcon a ha
  obtain ⟨a, ha, hne'⟩ := hex
  have hcost : a.cost = 0 := cost_eq_zero_of_len (hA.values a ha)
  refine up hA hy hacc (hA.antichain a ha) hcost ?_
  intro heq
  apply hne'
  rw [yv_mem hy ha] at heq
  unfold val at heq
  exact cast_injective _ heq

end WeightedConstruction.WideForest

end OptimalOTS

#print axioms OptimalOTS.WeightedConstruction.WideForest.events_none
#print axioms OptimalOTS.WeightedConstruction.WideForest.events_ne
#print axioms OptimalOTS.WeightedConstruction.WideForest.events_same
end
end

/- Original module: Submissions.UpperCompressions.WeightedReconstruct; SHA256 11b6840f75165f562181a79b5027dec037b40aa9b670c79260fe73f4e96807f1. -/
section

/-! Every accepted weighted verifier run has its index answer and reconstruction
witness recorded in the final shared-oracle cache. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedScheme

variable {M : ℕ}

theorem verify_support (S : Scheme M) (pk : PublicKey) (m : Message)
    (σ : Signature) (c : Cache) :
    ∀ p ∈ support (run (S.verify pk m σ) c),
      Cache.Sub c p.2 ∧ (p.1 = true →
        ∃ w, p.2 ⟨msgBits + 86, m ++ σ.1⟩ = some w ∧
          ∃ i : Fin M, S.decode w = some i ∧
            σ.2.length = S.graph.revealBits (S.sets i) ∧
            ∃ y : S.graph.Assignment,
              S.graph.ReconEqs p.2 (S.sets i) (S.graph.decode (S.sets i) σ.2) y ∧
              S.publicKey y = pk) := by
  intro p hp
  unfold Scheme.verify at hp
  rw [run_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨w, c₁⟩, hw₁, hp⟩ := hp
  obtain ⟨hsub₁, hw⟩ := Dag.Graph.hash_support (m ++ σ.1) c (w, c₁) hw₁
  cases hi : S.decode w with
  | none =>
    simp only [hi, run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hsub₁, fun h => by cases h⟩
  | some i =>
    simp only [hi] at hp
    by_cases hlen : σ.2.length = S.graph.revealBits (S.sets i)
    · rw [if_pos hlen, run_bind, support_bind] at hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨⟨y, c₂⟩, hy, hp⟩ := hp
      obtain ⟨hsub₂, heq⟩ := S.graph.reconstruct_support _ _ c₁ (y, c₂) hy
      rw [run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨hsub₁.trans hsub₂, fun hok => ?_⟩
      exact ⟨w, hsub₂ _ _ hw, i, hi, hlen, y, heq, of_decide_eq_true hok⟩
    · rw [if_neg hlen, run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hsub₁, fun h => by cases h⟩

end OptimalOTS.WeightedScheme

#print axioms OptimalOTS.WeightedScheme.verify_support
end
end

/- Original module: Submissions.UpperCompressions.WideVerifyEvents; SHA256 160bf4d381539cde65d1b64ad376874ca47122901d96d94684c84899f87350c9. -/
section

/-! Concrete accepted-signature routes for the86-bit weighted verifier.
The remaining same-class, same-payload case belongs to the weighted index event,
including different nonce/message pairs. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

/-- The actual verifier's public-key check is low128 at the full256-bit root. -/
theorem accepted_lowPk (ξ : Rec) (y : graph.Assignment)
    (h : forestScheme.publicKey y = pkOf ξ) : lowPk (yv y rh) = pkOf ξ := by
  unfold yv
  rw [lowPk_cast_eq]
  exact h

/-- If signing returned no signature, every accepting verification reaches an
authentication bad event; the index decoder and nonce are the actual new scheme's. -/
theorem accepted_none_event (ξ : Rec) (m : Message) (σ : WeightedScheme.Signature)
    (c d : Cache) (h : (true, d) ∈ support (run (forestScheme.verify (pkOf ξ) m σ) c)) :
    Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  obtain ⟨_, hh⟩ := WeightedScheme.verify_support forestScheme (pkOf ξ) m σ c (true, d) h
  obtain ⟨w, hw, i, hi, hlen, y, hy, hpk⟩ := hh rfl
  exact events_none (isCut_setsName i) hy (accepted_lowPk ξ y hpk)

/-- Given a signed class, an accepted signature either reproduces that class's
honest payload or reaches a hidden-input/spurious-image event. Payload equality
is full129-bit equality, and thus covers same-message altered-payload forgery. -/
theorem accepted_class_cases (ξ : Rec) (signedClass : Fin WeightedSchedule.M)
    (m : Message) (σ : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (forestScheme.verify (pkOf ξ) m σ) c)) :
    ∃ w, d (encQuery (m, σ.1)) = some w ∧
      ∃ i : Fin WeightedSchedule.M, WeightedSchedule.decode w = some i ∧
        ((i = signedClass ∧ σ.2 = graph.encode (fins (setsName signedClass)) (graph.evalRec ξ)) ∨
          Spr d ξ ∨ Cache.Hits d (fHid (some (setsName signedClass)) ξ)) := by
  obtain ⟨_, hh⟩ := WeightedScheme.verify_support forestScheme (pkOf ξ) m σ c (true, d) h
  obtain ⟨w, hw, i, hi, hlen, y, hy, hpk⟩ := hh rfl
  refine ⟨w, hw, i, hi, ?_⟩
  have hacc := accepted_lowPk ξ y hpk
  by_cases hic : i = signedClass
  · subst i
    by_cases hpayload : σ.2 = graph.encode (fins (setsName signedClass)) (graph.evalRec ξ)
    · exact Or.inl ⟨rfl, hpayload⟩
    · exact Or.inr (Or.inl (events_same (isCut_setsName signedClass) hy hacc hlen hpayload))
  · apply Or.inr
    apply events_ne (isCut_setsName signedClass) (isCut_setsName i)
      (by rw [cost_setsName, cost_setsName])
    · exact fun he => hic (setsName_injective he).symm
    · exact hy
    · exact hacc

end OptimalOTS.WeightedConstruction.WideForest

#print axioms OptimalOTS.WeightedConstruction.WideForest.accepted_none_event
#print axioms OptimalOTS.WeightedConstruction.WideForest.accepted_class_cases
end
end

/- Original module: Submissions.UpperCompressions.WideStrongEvents; SHA256 e1ec67407191db1a0b26488c666ed42bbfb8e8c20b78510aba56f0b30d0384f0. -/
section

/-! Endgame event decomposition for strong forgery. The alternate-input event
includes private signing cache insertions; it has no probability bound here. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] OptimalOTS.WeightedResearch92.classes

namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

/-- A different message/nonce input with the signed class, wherever the answer
was inserted. In particular, private nonwinning signing trials are retained. -/
def AlternateClass (c : Cache) (signedInput : EncInput) (i : Fin WeightedSchedule.M) : Prop :=
  ∃ u : EncInput, u ≠ signedInput ∧
    ∃ w, c (encQuery u) = some w ∧ WeightedSchedule.decode w = some i

/-- Acceptance of a pair different from the signed pair reaches either graph
authentication badness or an alternate encoding input with the signed class. -/
theorem accepted_strong_event (ξ : Rec) (signedClass : Fin WeightedSchedule.M)
    (signedInput : EncInput) (m : Message) (σ : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (forestScheme.verify (pkOf ξ) m σ) c))
    (hne : (m, σ) ≠ (signedInput.1,
      (signedInput.2, graph.encode (fins (setsName signedClass)) (graph.evalRec ξ)))) :
    Spr d ξ ∨ Cache.Hits d (fHid (some (setsName signedClass)) ξ) ∨
      AlternateClass d signedInput signedClass := by
  obtain ⟨w, hw, i, hi, he | hs | hh⟩ :=
    accepted_class_cases ξ signedClass m σ c d h
  · obtain ⟨rfl, hpayload⟩ := he
    right; right
    refine ⟨(m, σ.1), ?_, w, hw, hi⟩
    intro heq
    apply hne
    have hm : m = signedInput.1 := congrArg (fun u : EncInput => u.1) heq
    have hn : σ.1 = signedInput.2 := congrArg (fun u : EncInput => u.2) heq
    exact Prod.ext hm (Prod.ext hn hpayload)
  · exact Or.inl hs
  · exact Or.inr (Or.inl hh)

end OptimalOTS.WeightedConstruction.WideForest

#print axioms OptimalOTS.WeightedConstruction.WideForest.accepted_strong_event
end
end

/- Original module: Submissions.UpperCompressions.WideAuthAssembly; SHA256 2eb6de94bdd1f24d51cd8d2cb1dbad860bd79aa961c12eeeda77d795ec76f882. -/
section

/-! Regroup a real continuation over every disclosure fiber, preserving the
uniform keygen record law and one paid budget. The class-dependent index charge
is an explicit obligation; this theorem is not a strong-security export. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
attribute [local irreducible] Finset.univ Finset.filter
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name

theorem postsign_continuation {α : Type} {Ac : Finset Name} (hAc : IsCut Ac)
    (pk : BitVec 128) (T : Finset Rec) (hT : T ⊆ fiberA pk)
    (d d' : Cache) (hd' : IndexExtension d d') (hTd : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (J : Data → Cache → ℝ≥0∞) (rate : ℝ≥0∞) (I : Data → Cache → ℕ → Prop)
    (hIf : ∀ dt c b q, I dt c b → c q = none → queryCost (.inr q) ≤ b →
      ∀ u, I dt (c.cacheQuery q u) (b-queryCost (.inr q)))
    (hIc : ∀ dt c b q, I dt c b → (c q).isSome → queryCost (.inr q) ≤ b →
      I dt c (b-queryCost (.inr q)))
    (hJ : ∀ dt ∈ T.image (dataOf Ac), IndexCharge (J dt) rate (I dt))
    (K : Data → OracleComp Spec α) (b : ℕ)
    (hI : ∀ dt ∈ T.image (dataOf Ac), I dt (Cache.extend d' dt.2.2) b)
    (hB : ∀ dt ∈ T.image (dataOf Ac), CostAtMost (K dt) b) :
    (∑ ξ ∈ T, w * E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
      (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J (dataOf Ac ξ) p.2)) ≤
      (∑ ξ ∈ T, w * (ind (Spr d ξ) + J (dataOf Ac ξ) (Cache.extend d' (fExp (some Ac) ξ)))) +
        max authRate rate * sumW (fiberA pk) * b := by
  have hfiber : ∀ dt ∈ T.image (dataOf Ac),
      (∑ ξ ∈ T with dataOf Ac ξ = dt,
        w * E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J (dataOf Ac ξ) p.2)) ≤
      (∑ ξ ∈ T with dataOf Ac ξ = dt,
        w * (ind (Spr d ξ) + J (dataOf Ac ξ) (Cache.extend d' (fExp (some Ac) ξ)))) +
        max authRate rate * sumW (fiberB Ac dt) * b := by
    intro dt hdt
    let Td := T.filter fun ξ => dataOf Ac ξ = dt
    have hdata : ∀ ξ ∈ Td, dataOf Ac ξ = dt := fun ξ hξ => (Finset.mem_filter.mp hξ).2
    have hsub : Td ⊆ fiberB Ac dt := by
      intro ξ hξ
      simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdata ξ hξ
    have hfe : ∀ ξ ∈ Td, fExp (some Ac) ξ = dt.2.2 :=
      fun ξ hξ => congrArg (fun a : Data => a.2.2) (hdata ξ hξ)
    have hc := fiber_continuation hAc dt hsub (J dt) rate (I dt) (hIf dt) (hIc dt)
      (hJ dt hdt) K d' b (hI dt hdt) (hB dt hdt)
    have hinit : jointPotential Td (some Ac) (J dt) (Cache.extend d' dt.2.2) =
        ∑ ξ ∈ Td, w * (ind (Spr d ξ) + J (dataOf Ac ξ) (Cache.extend d' (fExp (some Ac) ξ))) := by
      rw [jointPotential, authPotential_after_sign hd' Td (some Ac)
        (fun ξ hξ => hTd ξ (Finset.mem_filter.mp hξ).1) dt.2.2 hfe]
      simp only [sumW, Finset.sum_mul, ← Finset.sum_add_distrib, ← mul_add]
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [hdata ξ hξ, hfe ξ hξ]
    rw [hinit] at hc
    have he : (∑ ξ ∈ Td,
        w * E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J (dataOf Ac ξ) p.2)) =
        ∑ ξ ∈ Td,
        w * E (run (K (dataOf Ac ξ)) (Cache.extend d' (fExp (some Ac) ξ)))
          (fun p => ind (Cache.Hits p.2 (fHid (some Ac) ξ)) + ind (Spr p.2 ξ) + J dt p.2) := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [hdata ξ hξ]
    exact he.le.trans hc
  rw [record_regroup T Ac, record_regroup T Ac (fun ξ =>
    w * (ind (Spr d ξ) + J (dataOf Ac ξ) (Cache.extend d' (fExp (some Ac) ξ))))]
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [Finset.sum_add_distrib]
  apply add_le_add_right
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  exact mul_le_mul_left (mul_le_mul_right (fiber_weights_le Ac hT) (max authRate rate)) b

end OptimalOTS.WeightedConstruction.WideForest
#print axioms OptimalOTS.WeightedConstruction.WideForest.postsign_continuation
end
end

