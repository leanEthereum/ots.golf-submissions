import Submissions.UpperLeanIsa.TierNumeric

/-! Exact rational rounding and the linear-potential certificate interface.
This module retains the original 25-tier control schedule; SplitNumeric carries
the mixed-packet split-alias schedule used by the submission. -/

set_option linter.constructorNameAsVariable false

-- Serial elaboration: the staged kernel checks of the class table must not run concurrently.
set_option Elab.async false

namespace OptimalOTS.LeanIsaBaseline.Layer.LinearNumeric
open Tier

/-- Tier weights, ascending. -/
def tierA : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216]

/-- Classes per tier. -/
def tierN : List ℕ :=
  [273312850009683383160716105718636, 215608787244449554696067956647180, 123474044600452580798838925337241, 43455241572777104457206878978769, 30357181546805245801627003012731, 21075682289151129560163127271210, 11858788848393508708411316866866, 4690953551201463927452992205740, 8291799291742779724430721253025, 5717624814581491399371523275291, 2927278345734739028771356148696, 979888786313027995282959103951, 593305505482863237010412994946, 372182912357036313408368377086, 191658534061615209973848674216, 69987846537242111979360262556, 17971289751699568148960862168, 8840432280399082736928871692, 2941010527416496433031591408, 1112984374961960564665452288, 243983288416617399780177072, 31067317179615756407361408, 1140981203662701802833888, 10429368196429656274176, 24388311386523135744]

def tA (t : ℕ) : ℕ := tierA.getD t 0
def tN (t : ℕ) : ℕ := tierN.getD t 0

/-- Accepted effective indices of the tiers below `t`. -/
def cum (t : ℕ) : ℕ := ∑ s ∈ Finset.range t, tN s * tA s

/-! ## Outward-rounded squaring -/

/-- The certificate precision. -/
def prec : ℕ := 2 ^ 256

def upSq (m : ℕ) : ℕ := (m * m + prec - 1) / prec
def dnSq (m : ℕ) : ℕ := m * m / prec

def iterUp : ℕ → ℕ → ℕ
  | 0, m => m
  | k + 1, m => upSq (iterUp k m)

def iterDn : ℕ → ℕ → ℕ
  | 0, m => m
  | k + 1, m => dnSq (iterDn k m)

theorem prec_pos : (0 : ℚ) < prec := by unfold prec; positivity

theorem sq_le_upSq (n : ℕ) : ((n : ℚ) / prec) ^ 2 ≤ (upSq n : ℚ) / prec := by
  have hn : n * n ≤ upSq n * prec := by
    have h := Nat.lt_div_mul_add (a := n * n + prec - 1) (b := prec) (by unfold prec; positivity)
    unfold upSq
    generalize (n * n + prec - 1) / prec * prec = y at h ⊢
    have : 1 ≤ prec := by unfold prec; exact Nat.one_le_two_pow
    omega
  have hp := prec_pos
  rw [div_pow, div_le_div_iff₀ (by positivity) hp, sq, pow_two]
  have : ((n * n : ℕ) : ℚ) ≤ ((upSq n * prec : ℕ) : ℚ) := by exact_mod_cast hn
  push_cast at this
  nlinarith

theorem dnSq_le_sq (n : ℕ) : (dnSq n : ℚ) / prec ≤ ((n : ℚ) / prec) ^ 2 := by
  have hn : dnSq n * prec ≤ n * n := Nat.div_mul_le_self _ _
  have hp := prec_pos
  rw [div_pow, div_le_div_iff₀ hp (by positivity), sq, pow_two]
  have : ((dnSq n * prec : ℕ) : ℚ) ≤ ((n * n : ℕ) : ℚ) := by exact_mod_cast hn
  push_cast at this
  nlinarith

theorem pow_le_iterUp {x : ℚ} {m : ℕ} (hx0 : 0 ≤ x) (hx : x ≤ m / prec) :
    ∀ k, x ^ 2 ^ k ≤ (iterUp k m : ℚ) / prec
  | 0 => by simpa [iterUp] using hx
  | k + 1 => by
    have ih := pow_le_iterUp hx0 hx k
    rw [pow_succ, pow_mul, iterUp]
    exact (pow_le_pow_left₀ (pow_nonneg hx0 _) ih 2).trans (sq_le_upSq _)

theorem iterDn_le_pow {x : ℚ} {m : ℕ} (hx : (m : ℚ) / prec ≤ x) :
    ∀ k, (iterDn k m : ℚ) / prec ≤ x ^ 2 ^ k
  | 0 => by simpa [iterDn] using hx
  | k + 1 => by
    have ih := iterDn_le_pow hx k
    rw [pow_succ, pow_mul, iterDn]
    exact (dnSq_le_sq _).trans
      (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) prec_pos.le) ih 2)

/-! ## The schedule -/

/-- `⌈prec · η₀⌉` and `⌊prec · η₀⌋`. -/
def etaUp : ℕ := (prec * (2 ^ 66 + 2 ^ 19) + (2 ^ 128 - 2 ^ 19) - 1) / (2 ^ 128 - 2 ^ 19)
def etaDn : ℕ := prec * (2 ^ 66 + 2 ^ 19) / (2 ^ 128 - 2 ^ 19)

/-- `prec · (1 - P_{<t})`, exact. -/
def rest (t : ℕ) : ℕ := prec - cum t * 2 ^ 129

def m0u (t : ℕ) : ℕ := rest t + etaUp
def m0l (t : ℕ) : ℕ := rest t + etaDn

/-- The rarest-cut schedule of the layer-85 four-child tables. -/
def schedule : Sched where
  T := 25
  K := 127
  a := tA
  N := tN
  Yu t := (iterUp 19 (m0u t) : ℚ) / prec
  Yl t := (iterDn 19 (m0l t) : ℚ) / prec
  yl t := (m0l t : ℚ) / prec
  hp := 2052624143750 / 2 ^ 40 / 2 ^ 127
  k1 := 1026313033686 / 2 ^ 40 / 2 ^ 127
  b0 := 1

/-! ## The conditions -/

theorem cum_le : ∀ t ≤ 25, cum t * 2 ^ 129 ≤ prec := by decide +kernel

theorem mass_eq (t : ℕ) : schedule.mass t = (cum t : ℚ) / 2 ^ 127 := by
  simp only [Sched.mass, cum, schedule]
  push_cast
  rfl

theorem eta0_le : eta0 ≤ (etaUp : ℚ) / prec := by decide +kernel

theorem le_eta0 : (etaDn : ℚ) / prec ≤ eta0 := by decide +kernel

theorem ybar_eq {t : ℕ} (ht : t ≤ 25) : schedule.ybar t = (rest t : ℚ) / prec + eta0 := by
  rw [Sched.ybar, mass_eq, rest, Nat.cast_sub (cum_le t ht)]
  push_cast
  unfold prec
  ring

theorem ybar_le {t : ℕ} (ht : t ≤ 25) : schedule.ybar t ≤ (m0u t : ℚ) / prec := by
  rw [ybar_eq ht, m0u, Nat.cast_add, add_div]
  linarith [eta0_le]

theorem le_ybar {t : ℕ} (ht : t ≤ 25) : (m0l t : ℚ) / prec ≤ schedule.ybar t := by
  rw [ybar_eq ht, m0l, Nat.cast_add, add_div]
  linarith [le_eta0]

theorem ybar_nonneg {t : ℕ} (ht : t ≤ 25) : 0 ≤ schedule.ybar t :=
  (div_nonneg (Nat.cast_nonneg _) prec_pos.le).trans (le_ybar ht)

/-- `(1 - P_{<T}) ^ (2 ^ 19 - 1) ≤ 2 ^ -128`, from `2 ^ 19` outward squarings and one division. -/
theorem avail : (1 - schedule.mass 25) ^ (2 ^ 19 - 1) ≤ 1 / 2 ^ 128 := by
  set x := 1 - schedule.mass 25 with hx
  have hxe : x = (rest 25 : ℚ) / prec := by
    rw [hx, mass_eq, rest, Nat.cast_sub (cum_le 25 le_rfl)]
    push_cast
    unfold prec
    ring
  have hpos : 0 < x := by
    rw [hxe]
    exact div_pos (by exact_mod_cast (show 0 < rest 25 by decide +kernel)) prec_pos
  have hU := pow_le_iterUp hpos.le (le_of_eq hxe) 19
  have hsplit : x ^ 2 ^ 19 = x ^ (2 ^ 19 - 1) * x := by
    rw [← pow_succ]; norm_num
  rw [hsplit] at hU
  have hq : (iterUp 19 (rest 25) : ℚ) / prec / ((rest 25 : ℚ) / prec) ≤ 1 / 2 ^ 128 := by
    decide +kernel
  calc x ^ (2 ^ 19 - 1) ≤ (iterUp 19 (rest 25) : ℚ) / prec / x := by
        rw [le_div_iff₀ hpos]; exact hU
    _ ≤ 1 / 2 ^ 128 := by rw [hxe]; exact hq

/-- Sufficient conditions for the proved linear-potential security theorem. -/
abbrev LinearConditions := Sched.LinearValid

set_option maxRecDepth 100000 in
/-- The layer-85 schedule meets the proposed linear numeric conditions. -/
theorem schedule_linear_conditions : LinearConditions schedule where
  K_le := by decide
  T_le := by decide
  a_pos := by decide +kernel
  a_lt := by
    have h : ∀ t < 25, ∀ s < t, tA s < tA t := by decide +kernel
    intro s t hst ht
    exact h t ht s hst
  mass_lt := by decide +kernel
  Yu_ge := fun t ht => pow_le_iterUp (ybar_nonneg ht) (ybar_le ht) 19
  Yl_le := fun t ht => iterDn_le_pow (le_ybar ht) 19
  yl_pos := by
    intro t ht
    have h : ∀ t < 25, 0 < m0l t := by decide +kernel
    exact div_pos (by exact_mod_cast h t ht) prec_pos
  yl_le := fun t ht => le_ybar ht.le
  hp_ge := by decide +kernel
  k1_post := by decide +kernel
  k1_sc := by decide +kernel
  fresh_index_charge := by decide +kernel
  linear_budget := by decide +kernel
  avail := avail
  acc_le := by rw [mass_eq]; decide +kernel

end OptimalOTS.LeanIsaBaseline.Layer.LinearNumeric
