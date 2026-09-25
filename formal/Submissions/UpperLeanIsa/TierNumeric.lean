import Mathlib

/-!
# The numeric conditions of rarest-cut signing

A tier schedule `S` lists, for the tiers `t < S.T` in ascending order of weight, the weight
`S.a t` (a class of tier `t` is the value of `S.a t * 2 ^ (256 - S.K)` answers) and the number
`S.N t` of classes of the tier, together with outward-rounded rational bounds on the powers
`ybar t ^ 2 ^ 19` and the literals `hp` (the collision slope `H'`), `k1` (the linear slope `κ₁`)
and `b0` (the knee of the quadratic budget term). `Sched.Valid` is the list of exact conditions
used by the security proof: the row has `2 ^ 127` nonces, signing makes `2 ^ 19` trials, the
non-index charge is `2 ^ -128` per compression, and the final slope is at most `2 ^ -127`.
-/

namespace OptimalOTS.LeanIsaBaseline.Layer.Tier

/-- A tier schedule with its rational certificate. -/
structure Sched where
  /-- Number of tiers. -/
  T : ℕ
  /-- Effective index bits: a class of tier `t` has `a t * 2 ^ (256 - K)` answers. -/
  K : ℕ
  /-- Tier weights, strictly increasing on `t < T`. -/
  a : ℕ → ℕ
  /-- Number of classes of each tier. -/
  N : ℕ → ℕ
  /-- Upper bounds on `ybar t ^ 2 ^ 19`, `t ≤ T`. -/
  Yu : ℕ → ℚ
  /-- Lower bounds on `ybar t ^ 2 ^ 19`, `t ≤ T`. -/
  Yl : ℕ → ℚ
  /-- Positive lower bounds on `ybar t`, `t < T`. -/
  yl : ℕ → ℚ
  /-- Upper bound on the collision slope `H'`. -/
  hp : ℚ
  /-- The linear slope `κ₁`. -/
  k1 : ℚ
  /-- The knee of the quadratic budget term. -/
  b0 : ℕ

/-- The RowGood deviation shift `η₀ = (δ + L) / (I - L)` with `δ = 2 ^ 66`, `L = 2 ^ 19`,
`I = 2 ^ 127`. -/
def eta0 : ℚ := (2 ^ 66 + 2 ^ 19) / (2 ^ 127 - 2 ^ 19)

/-- The row factor `I / (I - L)`. -/
def cI : ℚ := 2 ^ 127 / (2 ^ 127 - 2 ^ 19)

namespace Sched

variable (S : Sched)

/-- The mass `P_{<t}` of the tiers below `t`. -/
def mass (t : ℕ) : ℚ := (∑ s ∈ Finset.range t, (S.N s * S.a s : ℚ)) / 2 ^ S.K

/-- `ȳ_t = 1 - P_{<t} + η₀`: the per-trial bound on missing every tier below `t`. -/
def ybar (t : ℕ) : ℚ := 1 - S.mass t + eta0

/-- The probability `p_t` of one class of tier `t`. -/
def p (t : ℕ) : ℚ := S.a t / 2 ^ S.K

/-- `Σ_t p_t (Ȳ_t - Ȳ_{t+1})`, from the certificate bounds. -/
def Hsum : ℚ := ∑ t ∈ Finset.range S.T, S.p t * (S.Yu t - S.Yl (t + 1))

/-- `Σ_t p_t (Ȳ_t - Ȳ_{t+1}) / ȳ_t`, from the certificate bounds. -/
def SCsum : ℚ := ∑ t ∈ Finset.range S.T, S.p t * (S.Yu t - S.Yl (t + 1)) / S.yl t

/-- `H̄ = (I / (I - L)) Σ_t p_t (Ȳ_t - Ȳ_{t+1})`. -/
def Hbar : ℚ := cI * S.Hsum

/-- `SC_f = (I / (I - L)) ^ 2 (L - 1) Σ_t p_t (Ȳ_t - Ȳ_{t+1}) / ȳ_t`. -/
def SCf : ℚ := cI ^ 2 * (2 ^ 19 - 1) * S.SCsum

/-- `H' = H̄ + SC_f / I`. -/
def Hprime : ℚ := S.Hbar + S.SCf / 2 ^ 127

/-- `f_t = (p_t - 2 ρ_N)⁺` with `ρ_N = 2 ^ -128`. -/
def f (t : ℕ) : ℚ := max 0 (S.p t - 1 / 2 ^ 127)

/-- `Pos = Σ_t (f_t - f_{t-1}) min(1, Ȳ_t)`, `f_{-1} = 0`. -/
def Pos : ℚ :=
  ∑ t ∈ Finset.range S.T, (S.f t - if t = 0 then 0 else S.f (t - 1)) * min 1 (S.Yu t)

/-- The post-sign rate `κ_post = ρ_N + Pos / 2`. -/
def kpost : ℚ := 1 / 2 ^ 128 + S.Pos / 2

/-- The exact conditions (tier-proof.md §10 with `I = 2 ^ 127`, `CR = 1/2`). -/
structure Valid : Prop where
  K_le : S.K ≤ 256
  T_le : S.T ≤ 2 ^ 64
  a_pos : ∀ t < S.T, 0 < S.a t
  a_lt : ∀ s t, s < t → t < S.T → S.a s < S.a t
  mass_lt : ∑ t ∈ Finset.range S.T, S.N t * S.a t < 2 ^ S.K
  Yu_ge : ∀ t ≤ S.T, S.ybar t ^ 2 ^ 19 ≤ S.Yu t
  Yl_le : ∀ t ≤ S.T, S.Yl t ≤ S.ybar t ^ 2 ^ 19
  yl_pos : ∀ t < S.T, 0 < S.yl t
  yl_le : ∀ t < S.T, S.yl t ≤ S.ybar t
  hp_ge : S.Hprime ≤ S.hp
  k1_post : S.kpost ≤ S.k1
  k1_sc : S.SCf ≤ 2 * 2 ^ 19 * S.k1
  b0_pos : 1 ≤ S.b0
  b0_le : S.hp * ((S.b0 : ℚ) - 1) ≤ 2 ^ 127 * (2 * S.k1 - S.hp)
  kmax_le : S.k1 + S.hp / (4 * 2 ^ 127) * ((2 ^ 127 - S.b0 : ℕ) : ℚ) ^ 2 / 2 ^ 127 ≤
    1 / 2 ^ 127
  avail : (1 - S.mass S.T) ^ (2 ^ 19 - 1) ≤ 1 / 2 ^ 128
  acc_le : S.mass S.T ≤ 1 / 2 ^ 10

end Sched

end OptimalOTS.LeanIsaBaseline.Layer.Tier
