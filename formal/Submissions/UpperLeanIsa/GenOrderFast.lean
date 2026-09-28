import LeanerVM.Semantics.Instruction
import Submissions.UpperLeanIsa.BF64Fast

/-! The order certificate of the generator `g`, re-checked with `BF64Fast.fastMul`.

`LeanerVM.Parameters.orderOf_g` checks its seven `g ^ ((2 ^ 64 - 1) / p) ≠ 1` facts by kernel
unfolding of `BF64` powers, which dominates that module's replay. The statements below are
identical to the trusted ones (`orderOf_g`, `gpow_injOn`, `gLog?_spec`, `gLog?_gpow_eq_none`,
`MemImage.read_gpow`, `Program.fetch_gpow`, `Program.fetch_eq_some_iff`); only the order checks
are evaluated by square-and-multiply over closed `Nat` primitives. -/

namespace OptimalOTS.GenFast
open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.BF64Fast

/-- Square-and-multiply on the natural-number representation, with `k` bits of fuel. -/
def fpow (A : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, n =>
    cond (Nat.beq (Nat.land n 1) 0)
      (fastMul (fpow A k (Nat.shiftRight n 1)) (fpow A k (Nat.shiftRight n 1)))
      (fastMul (fastMul (fpow A k (Nat.shiftRight n 1)) (fpow A k (Nat.shiftRight n 1))) A)

/-- `fpow` computes `BF64` powers of exponents below `2 ^ k`. -/
theorem pow_toNat (a : BF64) : ∀ (k n : Nat), n < 2 ^ k → (a ^ n).toNat = fpow a.toNat k n
  | 0, n, hn => by
    obtain rfl : n = 0 := by simpa using hn
    rw [pow_zero]; rfl
  | k + 1, n, hn => by
    have hs : Nat.shiftRight n 1 = n / 2 := by
      change n >>> 1 = n / 2
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    have hl : Nat.land n 1 = n % 2 := Nat.and_one_is_mod n
    have ih := pow_toNat a k (n / 2) (by rw [pow_succ] at hn; omega)
    have hsq : a ^ (n / 2) * a ^ (n / 2) = a ^ (n / 2 + n / 2) := (pow_add a _ _).symm
    simp only [fpow, hs, hl, ← ih, ← mul_toNat, hsq]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [h]
      change _ = (a ^ (n / 2 + n / 2)).toNat
      congr 2; omega
    · rw [h]
      change _ = (a ^ (n / 2 + n / 2) * a).toNat
      rw [← pow_succ]
      congr 2; omega

/-- A power is not one when its closed square-and-multiply evaluation is not one. -/
theorem pow_ne_one {a : BF64} {n : Nat} (hn : n < 2 ^ 64) (h : Nat.beq (fpow a.toNat 64 n) 1 = false) :
    a ^ n ≠ 1 := by
  intro he
  have := congrArg BitVec.toNat he
  rw [pow_toNat a 64 n hn] at this
  rw [this] at h
  exact absurd h (by decide)

theorem g_pow_div_three_ne_one : g ^ ((2 ^ 64 - 1) / 3) ≠ 1 :=
  pow_ne_one (by decide) (by decide +kernel)
theorem g_pow_div_five_ne_one : g ^ ((2 ^ 64 - 1) / 5) ≠ 1 :=
  pow_ne_one (by decide) (by decide +kernel)
theorem g_pow_div_seventeen_ne_one : g ^ ((2 ^ 64 - 1) / 17) ≠ 1 :=
  pow_ne_one (by decide) (by decide +kernel)
theorem g_pow_div_257_ne_one : g ^ ((2 ^ 64 - 1) / 257) ≠ 1 :=
  pow_ne_one (by decide) (by decide +kernel)
theorem g_pow_div_641_ne_one : g ^ ((2 ^ 64 - 1) / 641) ≠ 1 :=
  pow_ne_one (by decide) (by decide +kernel)
theorem g_pow_div_65537_ne_one : g ^ ((2 ^ 64 - 1) / 65537) ≠ 1 :=
  pow_ne_one (by decide) (by decide +kernel)
theorem g_pow_div_6700417_ne_one : g ^ ((2 ^ 64 - 1) / 6700417) ≠ 1 :=
  pow_ne_one (by decide) (by decide +kernel)

/-- `g` generates `K^×` (same statement and argument as `LeanerVM.Parameters.orderOf_g`). -/
theorem orderOf_g : orderOf g = 2 ^ 64 - 1 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) g_pow_card_sub_one
    fun p hp hdvd ↦ ?_
  rw [card_sub_one_factorization] at hdvd
  simp only [Nat.Prime.dvd_mul hp, or_assoc] at hdvd
  rcases hdvd with h | h | h | h | h | h | h <;>
    rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h]
  exacts [g_pow_div_three_ne_one, g_pow_div_five_ne_one, g_pow_div_seventeen_ne_one,
    g_pow_div_257_ne_one, g_pow_div_641_ne_one, g_pow_div_65537_ne_one,
    g_pow_div_6700417_ne_one]

/-- Distinct indices below `2^64 - 1` are distinct addresses. -/
theorem gpow_injOn : Set.InjOn gpow (Set.Iio (2 ^ 64 - 1)) := by
  rw [← orderOf_g]
  exact pow_injOn_Iio_orderOf

/-- The specification of `gLog?` (as `LeanerVM.Semantics.gLog?_spec`). -/
theorem gLog?_spec {κ : ℕ} (hκ : κ < 64) {a : K} {i : Fin (2 ^ κ)} :
    gLog? κ a = some i ↔ a = gpow i := by
  unfold gLog?
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro hi
      obtain rfl := Option.some.inj hi
      exact hc
    · intro hi
      have hbound : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hj : ((Classical.choose h : Fin (2 ^ κ)) : ℕ) < 2 ^ 64 - 1 := by
        have := (Classical.choose h).isLt; omega
      have hi' : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
      exact congrArg some (Fin.ext (gpow_injOn hj hi' (hc.symm.trans hi)))
  · exact ⟨fun hi ↦ (nomatch hi), fun hi ↦ absurd ⟨i, hi⟩ h⟩

/-- A power past the end is no address (as `LeanerVM.Semantics.gLog?_gpow_eq_none`). -/
theorem gLog?_gpow_eq_none {κ j : ℕ} (hj : 2 ^ κ ≤ j) (hj' : j < 2 ^ 64 - 1) :
    gLog? κ (gpow j) = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ by
    have hi : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
    have := gpow_injOn hj' hi h
    have := i.isLt
    omega

/-- Reading at the address of index `i` gives word `i` (as `MemImage.read_gpow`). -/
theorem MemImage.read_gpow {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) (i : Fin (2 ^ κ)) :
    L.read (gpow i) = some (L i) := by
  rw [LeanerVM.Semantics.MemImage.read, (gLog?_spec hκ).mpr rfl, Option.map_some]

private theorem logSize_lt (prog : Program) : prog.logSize < 64 :=
  lt_of_le_of_lt prog.logSize_le (by decide)

/-- Fetching at the address of index `i` gives instruction `i` (as `Program.fetch_gpow`). -/
theorem Program.fetch_gpow (prog : Program) (i : Fin (2 ^ prog.logSize)) :
    prog.fetch (gpow i) = some (prog.code i) := by
  rw [LeanerVM.Semantics.Program.fetch, (gLog?_spec (logSize_lt prog)).mpr rfl, Option.map_some]

/-- A successful fetch is the instruction of the counter's index (as `Program.fetch_eq_some_iff`). -/
theorem Program.fetch_eq_some_iff (prog : Program) {pc : K} {ins : Instr} :
    prog.fetch pc = some ins ↔ ∃ i : Fin (2 ^ prog.logSize), pc = gpow i ∧ prog.code i = ins := by
  simp only [LeanerVM.Semantics.Program.fetch, Option.map_eq_some_iff, gLog?_spec (logSize_lt prog)]

end OptimalOTS.GenFast
