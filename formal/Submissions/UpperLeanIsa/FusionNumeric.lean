import Submissions.UpperLeanIsa.TierNumeric

/-! Exact rational conditions for the 1149-cycle candidate's 18-tier schedule.
The separate codec proof must establish that these counts describe the accepted indices. -/

set_option linter.constructorNameAsVariable false

-- Serial elaboration: the staged kernel checks of the class table must not run concurrently.
set_option Elab.async false

namespace OptimalOTS.LeanIsaBaseline.Layer.FusionNumeric
open Tier

/-- Tier weights, ascending. -/
def tierA : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072]

/-- Classes per tier. -/
def tierN : List ℕ :=
  [630133605612650613971285375123259, 233877694989528833998161990995752, 129210903331057621338520582524426, 32674016903750495298947337308214, 60206516358752989739773498587954, 18311526650631397277485982537904, 9238323311076052823326534559160, 41314858360526729266382795922846, 12559817305514618617554343791729, 6276798936282040499792465358111, 1324715602770530135644769473581, 3037858581922615780482688681050, 768979946899773033084513362214, 349595318938714752421254770154, 58834595573868741326471295018, 3127850483280695112998485476, 49564865784076804366816968, 171223585161757362297360]

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
def etaUp : ℕ := (prec * (2 ^ 66 + 2 ^ 19) + (2 ^ 127 - 2 ^ 19) - 1) / (2 ^ 127 - 2 ^ 19)
def etaDn : ℕ := prec * (2 ^ 66 + 2 ^ 19) / (2 ^ 127 - 2 ^ 19)

/-- `prec · (1 - P_{<t})`, exact. -/
def rest (t : ℕ) : ℕ := prec - cum t * 2 ^ 129

def m0u (t : ℕ) : ℕ := rest t + etaUp
def m0l (t : ℕ) : ℕ := rest t + etaDn

/-- The rarest-cut schedule of the layer-86 Group3 tables. -/
def schedule : Sched where
  T := 18
  K := 127
  a := tA
  N := tN
  Yu t := (iterUp 19 (m0u t) : ℚ) / prec
  Yl t := (iterDn 19 (m0l t) : ℚ) / prec
  yl t := (m0l t : ℚ) / prec
  hp := 1393370080481 / 2 ^ 40 / 2 ^ 127
  k1 := 1393370080481 / 2 ^ 41 / 2 ^ 127
  b0 := 1

/-! ## The conditions -/

theorem cum_le : ∀ t ≤ 18, cum t * 2 ^ 129 ≤ prec := by decide +kernel

theorem mass_eq (t : ℕ) : schedule.mass t = (cum t : ℚ) / 2 ^ 127 := by
  simp only [Sched.mass, cum, schedule]
  push_cast
  rfl

theorem eta0_le : eta0 ≤ (etaUp : ℚ) / prec := by decide +kernel

theorem le_eta0 : (etaDn : ℚ) / prec ≤ eta0 := by decide +kernel

theorem ybar_eq {t : ℕ} (ht : t ≤ 18) : schedule.ybar t = (rest t : ℚ) / prec + eta0 := by
  rw [Sched.ybar, mass_eq, rest, Nat.cast_sub (cum_le t ht)]
  push_cast
  unfold prec
  ring

theorem ybar_le {t : ℕ} (ht : t ≤ 18) : schedule.ybar t ≤ (m0u t : ℚ) / prec := by
  rw [ybar_eq ht, m0u, Nat.cast_add, add_div]
  linarith [eta0_le]

theorem le_ybar {t : ℕ} (ht : t ≤ 18) : (m0l t : ℚ) / prec ≤ schedule.ybar t := by
  rw [ybar_eq ht, m0l, Nat.cast_add, add_div]
  linarith [le_eta0]

theorem ybar_nonneg {t : ℕ} (ht : t ≤ 18) : 0 ≤ schedule.ybar t :=
  (div_nonneg (Nat.cast_nonneg _) prec_pos.le).trans (le_ybar ht)

/-- `(1 - P_{<T}) ^ (2 ^ 19 - 1) ≤ 2 ^ -128`, from `2 ^ 19` outward squarings and one division. -/
theorem avail : (1 - schedule.mass 18) ^ (2 ^ 19 - 1) ≤ 1 / 2 ^ 128 := by
  set x := 1 - schedule.mass 18 with hx
  have hxe : x = (rest 18 : ℚ) / prec := by
    rw [hx, mass_eq, rest, Nat.cast_sub (cum_le 18 le_rfl)]
    push_cast
    unfold prec
    ring
  have hpos : 0 < x := by
    rw [hxe]
    exact div_pos (by exact_mod_cast (show 0 < rest 18 by decide +kernel)) prec_pos
  have hU := pow_le_iterUp hpos.le (le_of_eq hxe) 19
  have hsplit : x ^ 2 ^ 19 = x ^ (2 ^ 19 - 1) * x := by
    rw [← pow_succ]; norm_num
  rw [hsplit] at hU
  have hq : (iterUp 19 (rest 18) : ℚ) / prec / ((rest 18 : ℚ) / prec) ≤ 1 / 2 ^ 128 := by
    decide +kernel
  calc x ^ (2 ^ 19 - 1) ≤ (iterUp 19 (rest 18) : ℚ) / prec / x := by
        rw [le_div_iff₀ hpos]; exact hU
    _ ≤ 1 / 2 ^ 128 := by rw [hxe]; exact hq

set_option maxRecDepth 100000 in
/-- **The layer-86 schedule meets every numeric condition.** -/
theorem schedule_valid : schedule.Valid where
  K_le := by decide
  T_le := by decide
  a_pos := by decide +kernel
  a_lt := by
    have h : ∀ t < 18, ∀ s < t, tA s < tA t := by decide +kernel
    intro s t hst ht
    exact h t ht s hst
  mass_lt := by decide +kernel
  Yu_ge := fun t ht => pow_le_iterUp (ybar_nonneg ht) (ybar_le ht) 19
  Yl_le := fun t ht => iterDn_le_pow (le_ybar ht) 19
  yl_pos := by
    intro t ht
    have h : ∀ t < 18, 0 < m0l t := by decide +kernel
    exact div_pos (by exact_mod_cast h t ht) prec_pos
  yl_le := fun t ht => le_ybar ht.le
  hp_ge := by decide +kernel
  k1_post := by decide +kernel
  k1_sc := by decide +kernel
  b0_pos := by decide
  b0_le := by decide +kernel
  kmax_le := by decide +kernel
  avail := avail
  acc_le := by rw [mass_eq]; decide +kernel

end OptimalOTS.LeanIsaBaseline.Layer.FusionNumeric
