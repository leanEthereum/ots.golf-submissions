import Submissions.UpperLeanIsa.IdxRows
import Submissions.UpperLeanIsa.RowIneq

/-!
# The row potential

Ported from UpperRiscv `RowPotential.lean`. `psi d = r + Σ_m max (b_m − r a_m) 0 / D_m`: `r` is
the fraction of accepted indices held by the cache, and row `m` has `a_m` accepted entries,
`b_m` of them shared, and `D_m = a_m + q N_m` with `N_m` its uncached nonces and
`q = numValid / 2 ^ 127`.

* `psi_step`: one fresh index answer raises `psi` by at most the class bound `gCls` of its index;
* `sum_gCls_le`: the class bounds add up to at most `11/6` over all indices;
* `psi_charge`: hence `θ psi` grows by at most `2 / 2 ^ 127` on average, `θ = I / (I − 2L)`;
* `psi_dom`: `θ psi` is a valid `ρ` for the signing lemma `signRho_bound`.

The parameters enter through the instance `RowCtx`, so that the RISC-V statements carry over
verbatim (`P` below is `RowCtx.P`); `idxBits = nonceBits = 127` are kept opaque, as in the RISC-V
proof, so that no power `2 ^ 127` is ever unfolded.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace RowPot

/-- The parameters of the row potential. -/
class RowCtx where
  P : Params

/-- Index width (opaque). -/
def idxBits : ℕ := 127

/-- Nonce width (opaque). -/
def nonceBits : ℕ := 127

theorem idxBits_eq : idxBits = 127 := rfl

theorem nonceBits_eq : nonceBits = 127 := rfl

variable [RowCtx]

/-- The parameters. -/
abbrev P : Params := RowCtx.P

/-- The number of accepted indices, as the cardinality of the accepted index values. -/
def numValid : ℕ := P.validSet.card

theorem numValid_eq : numValid = P.numValid := P.card_validSet

attribute [local irreducible] hashBits msgBits pkBits trials Params.validSet Params.encQuery
  Params.V Params.validInputs

theorem mem_validSet_lt' {i : ℕ} (h : i ∈ P.validSet) : i < 2 ^ idxBits := by
  rw [idxBits_eq]; exact P.mem_validSet_lt h

theorem numValid_le'' : P.validSet.card ≤ 2 ^ idxBits := by
  rw [idxBits_eq, P.card_validSet]; exact P.numValid_le'

theorem idxOf_lt' (w : BitVec hashBits) : Params.idxOf w < 2 ^ idxBits := by
  rw [idxBits_eq]; exact Params.idxOf_lt w

theorem card_V_le_numValid' (d : Cache) : (P.V d).card ≤ numValid := by
  unfold numValid; rw [P.card_validSet]; exact P.card_V_le_numValid d

theorem card_idxOf_mem' (_hidx : idxBits ≤ hashBits) (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < 2 ^ idxBits) :
    (Finset.univ.filter fun y : BitVec hashBits => Params.idxOf y ∈ A).card =
      A.card * 2 ^ (hashBits - idxBits) := by
  rw [idxBits_eq] at hA ⊢
  exact card_idxOf_mem A hA

theorem card_nonce : Fintype.card Nonce = 2 ^ nonceBits := by
  rw [nonceBits_eq, Fintype.card_bitVec]

attribute [local irreducible] idxBits nonceBits





/-- The standing hypotheses on the parameters. -/
structure RowHyp : Prop where
  nonce_eq : nonceBits = idxBits
  idx_le : idxBits ≤ hashBits
  two_le : 2 ≤ numValid
  numCuts_le : 2 * numValid ≤ 2 ^ idxBits
  trial_le : 24 * trials ≤ 2 ^ idxBits


namespace Row

def I : ℝ := 2 ^ idxBits
def M : ℝ := numValid
def q : ℝ := M / I
def θ : ℝ := I / (I - 2 * trials)

variable (d : Cache) (m : EMessage)

def v : ℝ := (P.V d).card
def r : ℝ := v d / M
def a : ℝ := (P.rowAcc d m).card
def b : ℝ := (P.rowBad d m).card
def dd : ℝ := (P.rowAcc d m \ P.rowBad d m).card
def u : ℝ := (P.rowCached d m).card
def N : ℝ := 2 ^ nonceBits - u d m
def D : ℝ := a d m + q * N d m
def x : ℝ := b d m - r d * a d m
def pr : ℝ := max (x d m) 0 / D d m
def hit (i : ℕ) : ℝ := (P.rowHit d m i).card

end Row

/-- The row potential. -/
def psi (d : Cache) : ℝ := Row.r d + ∑ m, Row.pr d m

/-- The bound on the growth of `psi` when the answer to `m₀ ++ η₀` has index `i`. -/
def gCls (d : Cache) (m₀ : EMessage) (i : ℕ) : ℝ :=
  if i ∈ P.validSet then
    (if i ∈ P.V d then (1 - Row.r d) / Row.D d m₀ + ∑ m, Row.hit d m i / Row.D d m
    else 1 / Row.M)
  else
    max (Row.x d m₀) 0 / (Row.D d m₀ - Row.q) - max (Row.x d m₀) 0 / Row.D d m₀

namespace Row

/-! ## Real inequalities -/

theorem step_real (x x' D D' t : ℝ) (hD : 0 < D) (hDD : D ≤ D') (ht : 0 ≤ t)
    (hx : x' ≤ x + t) : max x' 0 / D' ≤ max x 0 / D + t / D := by
  have h1 : max x' 0 ≤ max x 0 + t :=
    max_le (by linarith [le_max_left x 0]) (by linarith [le_max_right x 0])
  have h2 : 0 ≤ max x 0 + t := add_nonneg (le_max_right _ _) ht
  calc max x' 0 / D' ≤ (max x 0 + t) / D' := div_le_div_of_nonneg_right h1 (by linarith)
    _ ≤ (max x 0 + t) / D := div_le_div_of_nonneg_left h2 hD hDD
    _ = _ := add_div _ _ _

theorem rej_real (x x' D q : ℝ) (hDq : 0 < D - q) (hx : x' ≤ x) :
    max x' 0 / (D - q) ≤ max x 0 / D + (max x 0 / (D - q) - max x 0 / D) := by
  rw [add_sub_cancel]
  exact div_le_div_of_nonneg_right (max_le_max hx le_rfl) hDq.le

theorem budget_real (d t D M : ℝ) (hM : 0 < M) (hd : 0 ≤ d) (ht0 : 0 ≤ t) (htM : t ≤ M)
    (hD : d + M - t ≤ D) : d / D ≤ (d + t) / M := by
  rcases hd.eq_or_lt with h | h
  · rw [← h, zero_div, zero_add]
    exact div_nonneg ht0 hM.le
  have hpos : 0 < d + M - t := by linarith
  calc d / D ≤ d / (d + M - t) := div_le_div_of_nonneg_left hd hpos hD
    _ ≤ (d + t) / M := by
      rw [div_le_div_iff₀ hpos hM]
      nlinarith [sq_nonneg d, mul_nonneg ht0 (sub_nonneg.2 htM)]

/-! ## Basic facts -/

theorem I_pos : 0 < I := by unfold I; positivity

theorem M_pos (hP : RowHyp) : 0 < M := by
  unfold M; have := hP.two_le; exact_mod_cast (by omega : 0 < numValid)

theorem two_le_M (hP : RowHyp) : 2 ≤ M := by
  unfold M; exact_mod_cast hP.two_le

theorem two_M_le (hP : RowHyp) : 2 * M ≤ I := by
  unfold M I; exact_mod_cast hP.numCuts_le

theorem q_nonneg : 0 ≤ q := by
  unfold q M; exact div_nonneg (Nat.cast_nonneg _) I_pos.le

theorem q_le_half (hP : RowHyp) : q ≤ 1 / 2 := by
  unfold q
  rw [div_le_iff₀ I_pos]
  linarith [two_M_le hP]

theorem qI : q * I = M := div_mul_cancel₀ _ I_pos.ne'

theorem nonce_card (hP : RowHyp) : (2 : ℝ) ^ nonceBits = I := by
  rw [hP.nonce_eq]; rfl

theorem u_nonneg (d : Cache) (m : EMessage) : 0 ≤ u d m := Nat.cast_nonneg _

theorem u_le_card (d : Cache) (m : EMessage) : u d m ≤ 2 ^ nonceBits := by
  unfold u
  have : (P.rowCached d m).card ≤ 2 ^ nonceBits := by
    calc (P.rowCached d m).card ≤ (Finset.univ : Finset Nonce).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ nonceBits := by rw [Finset.card_univ, card_nonce]
  exact_mod_cast this

theorem N_nonneg (d : Cache) (m : EMessage) : 0 ≤ N d m := by
  unfold N; linarith [u_le_card d m]

theorem a_nonneg (d : Cache) (m : EMessage) : 0 ≤ a d m := Nat.cast_nonneg _
theorem dd_nonneg (d : Cache) (m : EMessage) : 0 ≤ dd d m := Nat.cast_nonneg _
theorem v_nonneg (d : Cache) : 0 ≤ v d := Nat.cast_nonneg _
theorem hit_nonneg (d : Cache) (m : EMessage) (i : ℕ) : 0 ≤ hit d m i := Nat.cast_nonneg _

theorem b_le_a (d : Cache) (m : EMessage) : b d m ≤ a d m := by
  unfold a b; exact_mod_cast Finset.card_le_card (P.rowBad_subset d m)

theorem dd_le_a (d : Cache) (m : EMessage) : dd d m ≤ a d m := by
  unfold a dd; exact_mod_cast Finset.card_le_card Finset.sdiff_subset

theorem v_le_M (d : Cache) : v d ≤ M := by
  unfold v M; exact_mod_cast card_V_le_numValid' d

theorem r_nonneg (hP : RowHyp) (d : Cache) : 0 ≤ r d :=
  div_nonneg (v_nonneg d) (M_pos hP).le

theorem r_le_one (hP : RowHyp) (d : Cache) : r d ≤ 1 := by
  unfold r; rw [div_le_one (M_pos hP)]; exact v_le_M d

theorem rM (hP : RowHyp) (d : Cache) : r d * M = v d :=
  div_mul_cancel₀ _ (M_pos hP).ne'

theorem D_nonneg (d : Cache) (m : EMessage) : 0 ≤ D d m :=
  add_nonneg (a_nonneg d m) (mul_nonneg q_nonneg (N_nonneg d m))

theorem pr_nonneg (d : Cache) (m : EMessage) : 0 ≤ pr d m :=
  div_nonneg (le_max_right _ _) (D_nonneg d m)

section Budget

variable (hP : RowHyp) {d : Cache} (hc : 2 * P.encCount d ≤ 2 ^ idxBits)
include hP hc

theorem sum_u_le : ∑ m, u d m ≤ I / 2 := by
  have h1 : (∑ m, (P.rowCached d m).card : ℕ) ≤ P.encCount d := P.sum_rowCached_le d
  have h2 : ((2 * P.encCount d : ℕ) : ℝ) ≤ ((2 ^ idxBits : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at h2
  unfold u I
  have h3 : (∑ m, ((P.rowCached d m).card : ℝ)) ≤ P.encCount d := by exact_mod_cast h1
  linarith

theorem u_le_half (m : EMessage) : u d m ≤ I / 2 :=
  (Finset.single_le_sum (fun m _ => u_nonneg d m) (Finset.mem_univ m)).trans (sum_u_le hP hc)

theorem N_ge (m : EMessage) : I / 2 ≤ N d m := by
  unfold N; rw [nonce_card hP]; linarith [u_le_half hP hc m]

theorem N_le (m : EMessage) : N d m ≤ I := by
  unfold N; rw [nonce_card hP]; linarith [u_nonneg d m]

theorem qN_ge (m : EMessage) : M / 2 ≤ q * N d m := by
  have := mul_le_mul_of_nonneg_left (N_ge hP hc m) (q_nonneg)
  rw [← qI]; linarith

theorem qN_le (m : EMessage) : q * N d m ≤ M := by
  have := mul_le_mul_of_nonneg_left (N_le hP hc m) (q_nonneg)
  rw [← qI]; linarith

theorem D_ge (m : EMessage) : M / 2 ≤ D d m := by
  unfold D; linarith [a_nonneg d m, qN_ge hP hc m]

theorem D_pos (m : EMessage) : 0 < D d m := by
  linarith [D_ge hP hc m, M_pos hP]

theorem one_le_D (m : EMessage) : 1 ≤ D d m := by
  linarith [D_ge hP hc m, two_le_M hP]

end Budget

end Row

theorem psi_nonneg (hP : RowHyp) (d : Cache) : 0 ≤ psi d :=
  add_nonneg (Row.r_nonneg hP d) (Finset.sum_nonneg fun m _ => Row.pr_nonneg d m)

theorem psi_empty : psi ∅ = 0 := by
  have hV : P.V ∅ = ∅ := by
    ext i; simp [P.mem_V_iff]
  have hA : ∀ m, P.rowAcc ∅ m = ∅ := fun m => by ext; simp [Params.rowAcc]
  have hB : ∀ m, P.rowBad ∅ m = ∅ := fun m => by ext; simp [Params.rowBad]
  simp [psi, Row.r, Row.v, Row.pr, Row.x, Row.a, Row.b, hV, hA, hB]

theorem psi_of_ne {d : Cache} {q : Query} (hq : ∀ u : EncInput, q ≠ P.encQuery u)
    (w : BitVec hashBits) : psi (d.cacheQuery q w) = psi d := by
  simp only [psi, Row.r, Row.v, Row.pr, Row.x, Row.a, Row.b, Row.D, Row.N, Row.u,
    P.V_of_ne hq, P.rowAcc_of_ne hq, P.rowBad_of_ne hq, P.rowCached_of_ne hq]

/-! ## One fresh encoding answer -/

section Step

variable (hP : RowHyp) {d : Cache} (hc : 2 * P.encCount d ≤ 2 ^ idxBits)
  {m₀ : EMessage} {η₀ : Nonce} (hfresh : d (P.encQuery (m₀ ++ η₀)) = none)
  (w : BitVec hashBits)
include hP hc hfresh

theorem psi_step :
    psi (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w) ≤ psi d + gCls d m₀ (Params.idxOf w) := by
  set d' := d.cacheQuery (P.encQuery (m₀ ++ η₀)) w with hd'
  set i := Params.idxOf w with hi
  have hu : ∀ m, Row.u d' m = Row.u d m + if m = m₀ then 1 else 0 := fun m => by
    simp only [Row.u, hd', P.rowCached_cacheQuery w hfresh m]; push_cast; rfl
  have ha : ∀ m, Row.a d' m = Row.a d m + if m = m₀ ∧ i ∈ P.validSet then 1 else 0 :=
    fun m => by simp only [Row.a, hd', P.rowAcc_cacheQuery w hfresh m]; push_cast; rfl
  have hv : Row.v d' = Row.v d + if i ∈ P.validSet ∧ i ∉ P.V d then 1 else 0 := by
    simp only [Row.v, hd', P.V_cacheQuery w hfresh]; push_cast; rfl
  have hb : ∀ m, Row.b d' m ≤
      Row.b d m + Row.hit d m i + if m = m₀ ∧ i ∈ P.V d then 1 else 0 := fun m => by
    have := P.rowBad_cacheQuery w hfresh m
    simp only [Row.b, Row.hit, hd']
    exact_mod_cast this
  have hD : ∀ m, Row.D d' m = Row.D d m + (if m = m₀ ∧ i ∈ P.validSet then 1 else 0) -
      Row.q * (if m = m₀ then 1 else 0) := fun m => by
    simp only [Row.D, Row.N, ha, hu]; ring
  have hDpos : ∀ m, 0 < Row.D d m := fun m => Row.D_pos hP hc m
  have hq1 : Row.q ≤ 1 := by linarith [Row.q_le_half hP]
  have hr0 := Row.r_nonneg hP d
  unfold psi gCls
  split_ifs with h1 h2
  · -- an index already held
    have hlt : i ∈ P.validSet := h1
    have hr : Row.r d' = Row.r d := by
      simp only [Row.r, hv, if_neg (fun h : i ∈ P.validSet ∧ i ∉ P.V d => h.2 h2), add_zero]
    have hrow : ∀ m, Row.pr d' m ≤ Row.pr d m + Row.hit d m i / Row.D d m +
        if m = m₀ then (1 - Row.r d) / Row.D d m else 0 := fun m => by
      have hbm := hb m
      have hDD : Row.D d m ≤ Row.D d' m := by
        rw [hD m]; by_cases hm : m = m₀ <;> simp [hm, hlt] <;> linarith
      have hr1 := Row.r_le_one hP d
      have hh0 := Row.hit_nonneg d m i
      by_cases hm : m = m₀
      · rw [if_pos hm]
        have ham : Row.a d' m = Row.a d m + 1 := by
          rw [ha m, if_pos ⟨hm, hlt⟩]
        have hbm' : Row.b d' m ≤ Row.b d m + Row.hit d m i + 1 := by
          rw [if_pos ⟨hm, h2⟩] at hbm; exact hbm
        have hx : Row.x d' m ≤ Row.x d m + (Row.hit d m i + (1 - Row.r d)) := by
          simp only [Row.x]
          rw [ham, hr]
          linarith
        have := Row.step_real _ _ _ _ _ (hDpos m) hDD (by linarith) hx
        unfold Row.pr
        rw [add_div] at this
        linarith
      · rw [if_neg hm]
        have hx : Row.x d' m ≤ Row.x d m + Row.hit d m i := by
          simp only [Row.x, hr, ha m, hm, false_and, if_false, add_zero]
          simp only [hm, false_and, if_false, add_zero] at hbm
          linarith
        have := Row.step_real _ _ _ _ _ (hDpos m) hDD hh0 hx
        unfold Row.pr
        linarith
    calc Row.r d' + ∑ m, Row.pr d' m
        ≤ Row.r d + ∑ m, (Row.pr d m + Row.hit d m i / Row.D d m +
          if m = m₀ then (1 - Row.r d) / Row.D d m else 0) := by
          rw [hr]; exact add_le_add le_rfl (Finset.sum_le_sum fun m _ => hrow m)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_univ, if_true]
          ring
  · -- a new accepted index
    have hlt : i ∈ P.validSet := h1
    have hnV : i ∉ P.V d := h2
    have hM := Row.M_pos hP
    have hr : Row.r d' = Row.r d + 1 / Row.M := by
      simp only [Row.r, hv, if_pos (⟨hlt, hnV⟩ : i ∈ P.validSet ∧ i ∉ P.V d)]
      ring
    have hrow : ∀ m, Row.pr d' m ≤ Row.pr d m := fun m => by
      have hbm := hb m
      have hhit : Row.hit d m i = 0 := by simp [Row.hit, P.rowHit_eq_empty d m hnV]
      simp only [hhit, if_neg (fun h : m = m₀ ∧ i ∈ P.V d => hnV h.2), add_zero] at hbm
      have hDD : Row.D d m ≤ Row.D d' m := by
        rw [hD m]; by_cases hm : m = m₀ <;> simp [hm, hlt] <;> linarith
      have ha' : Row.a d m ≤ Row.a d' m := by
        rw [ha m]; split_ifs <;> linarith
      have hr' : Row.r d ≤ Row.r d' := by
        rw [hr]; linarith [one_div_pos.2 hM]
      have hx : Row.x d' m ≤ Row.x d m + 0 := by
        simp only [Row.x]
        nlinarith [Row.a_nonneg d m]
      have := Row.step_real _ _ _ _ _ (hDpos m) hDD le_rfl hx
      unfold Row.pr
      linarith [zero_div (Row.D d m)]
    calc Row.r d' + ∑ m, Row.pr d' m ≤ Row.r d + 1 / Row.M + ∑ m, Row.pr d m := by
          rw [hr]; exact add_le_add le_rfl (Finset.sum_le_sum fun m _ => hrow m)
      _ = _ := by ring

  · -- a rejected index
    have hnV : i ∉ P.V d := fun h => h1 (P.V_sub_valid d i h)
    have hr : Row.r d' = Row.r d := by
      simp only [Row.r, hv, if_neg (fun h : i ∈ P.validSet ∧ i ∉ P.V d => h1 h.1), add_zero]
    have hrow : ∀ m, Row.pr d' m ≤ Row.pr d m + if m = m₀ then
        (max (Row.x d m₀) 0 / (Row.D d m₀ - Row.q) - max (Row.x d m₀) 0 / Row.D d m₀)
        else 0 := fun m => by
      have hbm := hb m
      have hhit : Row.hit d m i = 0 := by simp [Row.hit, P.rowHit_eq_empty d m hnV]
      have hx : Row.x d' m ≤ Row.x d m := by
        simp only [Row.x, hr, ha m, if_neg (fun h : m = m₀ ∧ i ∈ P.validSet => h1 h.2),
          add_zero]
        simp only [hhit, if_neg (fun h : m = m₀ ∧ i ∈ P.V d => hnV h.2), add_zero] at hbm
        linarith
      by_cases hm : m = m₀
      · rw [if_pos hm]
        subst hm
        have hD' : Row.D d' m = Row.D d m - Row.q := by
          rw [hD m]; simp [h1]
        unfold Row.pr
        rw [hD']
        exact Row.rej_real _ _ _ _ (by linarith [Row.one_le_D hP hc m, Row.q_le_half hP]) hx
      · rw [if_neg hm, add_zero]
        have hD' : Row.D d' m = Row.D d m := by rw [hD m]; simp [hm]
        unfold Row.pr
        rw [hD']
        exact div_le_div_of_nonneg_right (max_le_max hx le_rfl) (hDpos m).le
    calc Row.r d' + ∑ m, Row.pr d' m
        ≤ Row.r d + ∑ m, (Row.pr d m + if m = m₀ then
          (max (Row.x d m₀) 0 / (Row.D d m₀ - Row.q) -
            max (Row.x d m₀) 0 / Row.D d m₀) else 0) := by
          rw [hr]; exact add_le_add le_rfl (Finset.sum_le_sum fun m _ => hrow m)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_univ, if_true]
          ring

end Step

/-! ## Summing the class bounds -/

section Classes

variable (hP : RowHyp) {d : Cache} (hc : 2 * P.encCount d ≤ 2 ^ idxBits)
include hP hc

theorem sum_gCls_le (m₀ : EMessage) :
    ∑ i ∈ Finset.range (2 ^ idxBits), gCls d m₀ i ≤ 11 / 6 := by
  have hM := Row.M_pos hP
  have hMI2 := Row.two_M_le hP
  have hVsub : P.V d ⊆ P.validSet := P.V_sub_valid d
  have hvalid : P.validSet ⊆ Finset.range (2 ^ idxBits) := fun i hi =>
    Finset.mem_range.2 (mem_validSet_lt' hi)
  set A := max (Row.x d m₀) 0 / (Row.D d m₀ - Row.q) -
    max (Row.x d m₀) 0 / Row.D d m₀ with hA
  set B := (1 - Row.r d) / Row.D d m₀ with hB
  have hF1 : (Finset.range (2 ^ idxBits)).filter (fun i => ¬ i ∈ P.validSet) =
      Finset.range (2 ^ idxBits) \ P.validSet := by
    ext i; simp only [Finset.mem_filter, Finset.mem_sdiff]
  have hF2 : ((Finset.range (2 ^ idxBits)).filter (fun i => i ∈ P.validSet)).filter
      (fun i => i ∈ P.V d) = P.V d := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro h
      have := hVsub h
      exact ⟨⟨hvalid this, this⟩, h⟩
  have hF3 : ((Finset.range (2 ^ idxBits)).filter (fun i => i ∈ P.validSet)).filter
      (fun i => ¬ i ∈ P.V d) = P.validSet \ P.V d := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨hvalid h, h⟩, h'⟩
  have hdd : ∀ m, Row.dd d m = ∑ i ∈ P.V d, Row.hit d m i := fun m => by
    simp only [Row.dd, Row.hit]
    rw [← P.sum_rowHit]
    push_cast
    rfl
  have e1 : ∑ _i ∈ Finset.range (2 ^ idxBits) \ P.validSet, A = (Row.I - Row.M) * A := by
    rw [Finset.sum_const, Finset.card_sdiff_of_subset hvalid, Finset.card_range, nsmul_eq_mul,
      Nat.cast_sub (show (P.validSet).card ≤ 2 ^ idxBits from numValid_le'')]
    simp [Row.I, Row.M, numValid]
  have e2 : ∑ i ∈ P.V d, (B + ∑ m, Row.hit d m i / Row.D d m) =
      Row.v d * B + ∑ m, Row.dd d m / Row.D d m := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_div, hdd]
  have e3 : ∑ _i ∈ P.validSet \ P.V d, 1 / Row.M = 1 - Row.r d := by
    rw [Finset.sum_const, Finset.card_sdiff_of_subset hVsub, nsmul_eq_mul,
      Nat.cast_sub (show (P.V d).card ≤ (P.validSet).card from card_V_le_numValid' d)]
    simp only [Row.r, Row.v, Row.M, numValid]
    have : ((P.validSet).card : ℝ) ≠ 0 := hM.ne'
    field_simp
  have hsum : ∑ i ∈ Finset.range (2 ^ idxBits), gCls d m₀ i =
      (Row.I - Row.M) * A + (Row.v d * B + ∑ m, Row.dd d m / Row.D d m) +
        (1 - Row.r d) := by
    unfold gCls
    rw [Finset.sum_ite, Finset.sum_ite, hF1, hF2, hF3, e1, e2, e3]
    ring
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m₀)]
  set S := ∑ m ∈ Finset.univ.erase m₀, Row.dd d m / Row.D d m with hSdef
  have hqI := Row.qI
  have hr0 := Row.r_nonneg hP d
  have hr1 := Row.r_le_one hP d
  have hS : S ≤ Row.r d - Row.dd d m₀ / Row.M + 1 / 2 -
      (Row.M - Row.q * Row.N d m₀) / Row.M := by
    have hrow : ∀ m, Row.dd d m / Row.D d m ≤
        (Row.dd d m + Row.q * Row.u d m) / Row.M := fun m => by
      have hu := Row.u_le_half hP hc m
      have hu0 := Row.u_nonneg d m
      have hq0 := Row.q_nonneg
      refine Row.budget_real _ _ _ _ hM (Row.dd_nonneg d m) (mul_nonneg hq0 hu0) ?_ ?_
      · have := mul_le_mul_of_nonneg_left (show Row.u d m ≤ Row.I by
          linarith [Row.I_pos]) hq0
        linarith
      · simp only [Row.D, Row.N]
        rw [Row.nonce_card hP]
        nlinarith [Row.dd_le_a d m]
    have hfree : ∑ m, Row.dd d m ≤ Row.v d := by
      simp only [Row.dd, Row.v]
      exact_mod_cast P.sum_rowFree_le d
    have hU := Row.sum_u_le hP hc
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m₀)] at hfree hU
    calc S ≤ ∑ m ∈ Finset.univ.erase m₀, (Row.dd d m + Row.q * Row.u d m) / Row.M :=
          Finset.sum_le_sum fun m _ => hrow m
      _ = ((∑ m ∈ Finset.univ.erase m₀, Row.dd d m) +
            Row.q * ∑ m ∈ Finset.univ.erase m₀, Row.u d m) / Row.M := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (Row.v d - Row.dd d m₀ + Row.q * (Row.I / 2 - Row.u d m₀)) / Row.M := by
          gcongr
          · linarith
          · exact Row.q_nonneg
          · linarith
      _ = _ := by
          simp only [Row.N, Row.r]
          rw [Row.nonce_card hP]
          have e : Row.q * (Row.I / 2 - Row.u d m₀) =
              Row.M / 2 - Row.q * Row.u d m₀ := by rw [← hqI]; ring
          have e' : Row.q * (Row.I - Row.u d m₀) = Row.M - Row.q * Row.u d m₀ := by
            rw [← hqI]; ring
          rw [e, e']
          field_simp
          ring
  have hx1 : max (Row.x d m₀) 0 ≤ (1 - Row.r d) * Row.a d m₀ := by
    refine max_le ?_ (mul_nonneg (by linarith) (Row.a_nonneg d m₀))
    simp only [Row.x]
    nlinarith [Row.b_le_a d m₀]
  have key := RowIneq.charge_le (Row.M) (Row.I) (Row.a d m₀) (Row.dd d m₀)
    (Row.q * Row.N d m₀) (max (Row.x d m₀) 0) (Row.r d) S hM (by linarith)
    (Row.qN_ge hP hc m₀) (Row.qN_le hP hc m₀) (Row.a_nonneg d m₀) (Row.dd_nonneg d m₀)
    (Row.dd_le_a d m₀) hr0 hr1 (le_max_right _ _) hx1 (Row.one_le_D hP hc m₀) hMI2 hS
  rw [show Row.M / Row.I = Row.q from rfl,
    show Row.a d m₀ + Row.q * Row.N d m₀ = Row.D d m₀ from rfl] at key
  have e4 : (Row.r d * Row.M * (1 - Row.r d) + Row.dd d m₀) / Row.D d m₀ =
      Row.v d * B + Row.dd d m₀ / Row.D d m₀ := by
    rw [Row.rM hP, hB]; ring
  rw [hA]
  linarith [key, e4]

end Classes

/-! ## The charge and the domination -/

theorem ofReal_two_pow (k : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ k) = (2 : ℝ≥0∞) ^ k := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem natCast_div_two_pow (n k : ℕ) :
    ((n : ℝ≥0∞) / 2 ^ k) = ENNReal.ofReal ((n : ℝ) / 2 ^ k) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ofReal_two_pow]

namespace Row

theorem θ_bounds (hP : RowHyp) : 1 ≤ θ ∧ θ ≤ 12 / 11 := by
  have hL := hP.trial_le
  have hL' : 24 * (trials : ℝ) ≤ I := by unfold I; exact_mod_cast hL
  have hL0 : (0 : ℝ) ≤ trials := Nat.cast_nonneg _
  have hpos : 0 < I - 2 * trials := by linarith [I_pos]
  unfold θ
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

end Row

section Charge

variable (hP : RowHyp) {d : Cache} (hc : 2 * P.encCount d ≤ 2 ^ idxBits)
include hP hc

theorem sum_idxOf (f : ℕ → ℝ) :
    ∑ w : BitVec hashBits, f (Params.idxOf w) =
      (2 : ℝ) ^ (hashBits - idxBits) * ∑ i ∈ Finset.range (2 ^ idxBits), f i := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (2 ^ idxBits))
    (g := Params.idxOf) (fun w _ => Finset.mem_range.2 (idxOf_lt' w)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f i) (fun w hw => by rw [(Finset.mem_filter.1 hw).2]),
    Finset.sum_const, nsmul_eq_mul]
  have := card_idxOf_mem' hP.idx_le {i} (by simpa using Finset.mem_range.1 hi)
  simp only [Finset.mem_singleton, Finset.card_singleton, one_mul] at this
  rw [this]
  push_cast
  ring

theorem psi_avg {m₀ : EMessage} {η₀ : Nonce} (hfresh : d (P.encQuery (m₀ ++ η₀)) = none) :
    (∑ w : BitVec hashBits, psi (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w)) /
        (2 : ℝ) ^ hashBits ≤ psi d + 11 / 6 / Row.I := by
  have hK : (2 : ℝ) ^ hashBits = Row.I * 2 ^ (hashBits - idxBits) := by
    unfold Row.I; rw [← pow_add, Nat.add_sub_cancel' hP.idx_le]
  have hKpos : (0 : ℝ) < 2 ^ hashBits := by positivity
  rw [div_le_iff₀ hKpos]
  calc ∑ w : BitVec hashBits, psi (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w)
      ≤ ∑ w : BitVec hashBits, (psi d + gCls d m₀ (Params.idxOf w)) :=
        Finset.sum_le_sum fun w _ => psi_step hP hc hfresh w
    _ = (2 : ℝ) ^ hashBits * psi d + (2 : ℝ) ^ (hashBits - idxBits) *
          ∑ i ∈ Finset.range (2 ^ idxBits), gCls d m₀ i := by
        rw [Finset.sum_add_distrib, sum_idxOf hP hc, Finset.sum_const, Finset.card_univ,
          Fintype.card_bitVec, nsmul_eq_mul]
        push_cast; ring
    _ ≤ (2 : ℝ) ^ hashBits * psi d + (2 : ℝ) ^ (hashBits - idxBits) * (11 / 6) := by
        gcongr
        exact sum_gCls_le hP hc m₀
    _ = (psi d + 11 / 6 / Row.I) * 2 ^ hashBits := by
        rw [hK]
        have := (Row.I_pos).ne'
        field_simp

/-- One fresh encoding answer raises `θ psi` by at most `2 / 2^idxBits` on average. -/
theorem psi_charge {m₀ : EMessage} {η₀ : Nonce} (hfresh : d (P.encQuery (m₀ ++ η₀)) = none) :
    ∑ w, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (Row.θ * psi (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w)) ≤
      ENNReal.ofReal (Row.θ * psi d) + 2 * ((2 : ℝ≥0∞) ^ idxBits)⁻¹ := by
  obtain ⟨hθ1, hθ2⟩ := Row.θ_bounds hP
  have hθ0 : 0 ≤ Row.θ := by linarith
  have hKpos : (0 : ℝ) < 2 ^ hashBits := by positivity
  have hIpos := Row.I_pos
  have hcard : (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal ((2 : ℝ) ^ hashBits)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hKpos, ofReal_two_pow, Fintype.card_bitVec]
    push_cast; rfl
  have h2 : 2 * ((2 : ℝ≥0∞) ^ idxBits)⁻¹ = ENNReal.ofReal (2 / Row.I) := by
    rw [ENNReal.ofReal_div_of_pos hIpos, ENNReal.ofReal_ofNat, Row.I, ofReal_two_pow,
      div_eq_mul_inv]
  rw [hcard, h2]
  simp_rw [← ENNReal.ofReal_mul (inv_nonneg.2 hKpos.le)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => mul_nonneg (inv_nonneg.2 hKpos.le)
      (mul_nonneg hθ0 (psi_nonneg hP _))),
    ← ENNReal.ofReal_add (mul_nonneg hθ0 (psi_nonneg hP d)) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hav := psi_avg hP hc hfresh
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← div_eq_inv_mul, mul_comm (Row.θ) _]
  calc (∑ w, psi (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w)) * Row.θ / 2 ^ hashBits
      = (∑ w, psi (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w)) / 2 ^ hashBits * Row.θ := by
        ring
    _ ≤ (psi d + 11 / 6 / Row.I) * Row.θ := mul_le_mul_of_nonneg_right hav hθ0
    _ ≤ Row.θ * psi d + 2 / Row.I := by
        have : Row.θ * (11 / 6 / Row.I) ≤ 2 / Row.I := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hIpos]; linarith
        nlinarith

/-- `θ psi` bounds the signing loss of every row (the hypothesis of `signRho_bound`). -/
theorem psi_dom (m : EMessage) (c : ℕ) (hc1 : (P.rowFresh d m).card ≤ c + trials)
    (hc2 : c ≤ (P.rowFresh d m).card) :
    ((P.rowBad d m).card : ℝ≥0∞) + c * (((P.V d).card : ℝ≥0∞) / 2 ^ idxBits) ≤
      ENNReal.ofReal (Row.θ * psi d) *
        ((P.rowAcc d m).card + c * ((numValid : ℝ≥0∞) / 2 ^ idxBits)) := by
  obtain ⟨hθ1, -⟩ := Row.θ_bounds hP
  have hIpos := Row.I_pos
  have hM := Row.M_pos hP
  have hfreshN : ((P.rowFresh d m).card : ℝ) = Row.N d m := by
    have h1 : P.rowFresh d m = Finset.univ \ P.rowCached d m := by
      ext η; simp [Params.rowFresh, Params.rowCached]
    have h2 : (P.rowFresh d m).card + (P.rowCached d m).card = 2 ^ nonceBits := by
      rw [h1, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
        card_nonce]
    have h3 : ((P.rowFresh d m).card : ℝ) + (P.rowCached d m).card = 2 ^ nonceBits := by
      exact_mod_cast h2
    simp only [Row.N, Row.u]; linarith
  have hNge := Row.N_ge hP hc m
  have hDpos := Row.D_pos hP hc m
  have hc1' : Row.N d m ≤ c + trials := by rw [← hfreshN]; exact_mod_cast hc1
  have hc2' : (c : ℝ) ≤ Row.N d m := by rw [← hfreshN]; exact_mod_cast hc2
  clear hc1 hc2 hfreshN
  have hL0 : (0 : ℝ) ≤ trials := Nat.cast_nonneg _
  have hLI : 24 * (trials : ℝ) ≤ Row.I := by
    unfold Row.I; exact_mod_cast hP.trial_le
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hθ0 : (0 : ℝ) ≤ Row.θ := by linarith
  have hq0 : 0 ≤ Row.q := Row.q_nonneg
  have hr0 : 0 ≤ Row.r d := Row.r_nonneg hP d
  have ha0 : 0 ≤ Row.a d m := Row.a_nonneg d m
  have hpsi : Row.r d + max (Row.x d m) 0 / Row.D d m ≤ psi d := by
    unfold psi
    have := Finset.single_le_sum (f := Row.pr d) (fun m _ => Row.pr_nonneg d m)
      (Finset.mem_univ m)
    have hpm : Row.pr d m = max (Row.x d m) 0 / Row.D d m := rfl
    linarith
  have hNc : Row.N d m ≤ Row.θ * c := by
    have hpos : 0 < Row.I - 2 * trials := by linarith
    simp only [Row.θ]
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left (show Row.N d m - trials ≤ c by linarith)
      hIpos.le, mul_nonneg hL0 (show 0 ≤ 2 * Row.N d m - Row.I by linarith)]
  have hDle : Row.D d m ≤ Row.θ * (Row.a d m + c * Row.q) := by
    have h1 := mul_le_mul_of_nonneg_left hNc hq0
    have h2 := mul_le_mul_of_nonneg_right hθ1 ha0
    simp only [Row.D]
    nlinarith
  have hx : Row.x d m ≤
      Row.θ * (Row.a d m + c * Row.q) * (max (Row.x d m) 0 / Row.D d m) := by
    calc Row.x d m ≤ max (Row.x d m) 0 := le_max_left _ _
      _ = Row.D d m * (max (Row.x d m) 0 / Row.D d m) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hDle (div_nonneg (le_max_right _ _) hDpos.le)
  have hapos : 0 ≤ Row.a d m + c * Row.q := add_nonneg ha0 (mul_nonneg hc0 hq0)
  have hreal : Row.b d m + c * (Row.v d / 2 ^ idxBits) ≤
      Row.θ * psi d * (Row.a d m + c * ((numValid : ℝ) / 2 ^ idxBits)) := by
    have hv : Row.v d / 2 ^ idxBits = Row.r d * Row.q := by
      have : (numValid : ℝ) ≠ 0 := hM.ne'
      simp only [Row.r, Row.q, Row.I, Row.M]
      field_simp
    have hq' : (numValid : ℝ) / 2 ^ idxBits = Row.q := rfl
    rw [hv, hq']
    have hxdef : Row.x d m = Row.b d m - Row.r d * Row.a d m := rfl
    have h1 := mul_le_mul_of_nonneg_left hpsi (mul_nonneg hθ0 hapos)
    have h2 := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hr0 hapos)
    nlinarith
  have hvnn : (0 : ℝ) ≤ c * (Row.v d / 2 ^ idxBits) :=
    mul_nonneg hc0 (div_nonneg (Row.v_nonneg d) (by positivity))
  have hL : ((P.rowBad d m).card : ℝ≥0∞) + c * (((P.V d).card : ℝ≥0∞) / 2 ^ idxBits) =
      ENNReal.ofReal (((P.rowBad d m).card : ℝ) + c * (((P.V d).card : ℝ) / 2 ^ idxBits)) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _)
        (mul_nonneg hc0 (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))),
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, natCast_div_two_pow]
  have hR : ENNReal.ofReal (Row.θ * psi d) *
      ((P.rowAcc d m).card + c * ((numValid : ℝ≥0∞) / 2 ^ idxBits)) =
      ENNReal.ofReal (Row.θ * psi d *
        (((P.rowAcc d m).card : ℝ) + c * ((numValid : ℝ) / 2 ^ idxBits))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hθ0 (psi_nonneg hP d)),
      ENNReal.ofReal_add (Nat.cast_nonneg _)
        (mul_nonneg hc0 (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))),
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, natCast_div_two_pow]
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal hreal

end Charge


/-! ## Only the index entries matter -/

section Congr

variable {c c' : Cache} (h : ∀ u : EncInput, c (P.encQuery u) = c' (P.encQuery u))
include h

theorem idxPre_congr (u₁ : EncInput) (i : ℕ) : P.IdxPre c u₁ i ↔ P.IdxPre c' u₁ i := by
  unfold Params.IdxPre
  simp only [h]

theorem rowCached_congr (m : EMessage) : P.rowCached c m = P.rowCached c' m := by
  unfold Params.rowCached
  exact Finset.filter_congr fun η _ => by rw [h]

theorem rowAcc_congr (m : EMessage) : P.rowAcc c m = P.rowAcc c' m := by
  unfold Params.rowAcc
  exact Finset.filter_congr fun η _ => by rw [h]

theorem rowBad_congr (m : EMessage) : P.rowBad c m = P.rowBad c' m := by
  unfold Params.rowBad
  exact Finset.filter_congr fun η _ => by rw [h]; simp only [idxPre_congr h]

theorem V_congr : P.V c = P.V c' := by
  unfold Params.V Params.validInputs
  have hf : (Finset.univ.filter fun u : EncInput =>
      ∃ w, c (P.encQuery u) = some w ∧ Params.idxOf w ∈ P.validSet) =
      Finset.univ.filter fun u : EncInput =>
        ∃ w, c' (P.encQuery u) = some w ∧ Params.idxOf w ∈ P.validSet :=
    Finset.filter_congr fun u _ => by rw [h]
  rw [hf]
  exact Finset.image_congr fun u _ => by simp only [h]

theorem psi_congr : psi c = psi c' := by
  simp only [psi, Row.r, Row.v, Row.pr, Row.x, Row.a, Row.b, Row.D, Row.N, Row.u,
    V_congr h, rowAcc_congr h, rowBad_congr h, rowCached_congr h]

end Congr

theorem psi_noEnc {c : Cache} (hc : ∀ u : EncInput, c (P.encQuery u) = none) : psi c = 0 := by
  rw [psi_congr (c' := ∅) (fun u => by rw [hc u]; rfl), psi_empty]

end RowPot

end OptimalOTS.LeanIsaBaseline.Layer
