import LeanerVM.Parameters.Field

/-! Fast kernel evaluation of `GF(2^64)` products.

`BF64`'s `Mul` is `reduce (carryLessMul a b)`, and `carryLessMul` is a `Fin.foldl`, which the
kernel unfolds through well-founded recursion. `mul_eq_of_fastMul` proves, once and for all
inputs, that `a * b = c` follows from a closed natural-number identity `fastMul a.toNat b.toNat =
c.toNat` built only from the kernel's GMP-accelerated `Nat` primitives, fully unrolled. -/

namespace OptimalOTS.BF64Fast
open BinaryField

/-- One carry-less multiplication step: xor in `B <<< i` when bit `i` of `A` is set. -/
def clStep (A B acc i : Nat) : Nat :=
  Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight A i) 1) (Nat.shiftLeft B i))

/-- The bit positions of a 64-bit word. -/
def idx64 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

/-- The carry-less product of two naturals below `2 ^ 64`, unrolled into kernel primitives. -/
def clU (A B : Nat) : Nat :=
  (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor 0
    (Nat.mul (Nat.land (Nat.shiftRight A 0) 1) (Nat.shiftLeft B 0)))
    (Nat.mul (Nat.land (Nat.shiftRight A 1) 1) (Nat.shiftLeft B 1)))
    (Nat.mul (Nat.land (Nat.shiftRight A 2) 1) (Nat.shiftLeft B 2)))
    (Nat.mul (Nat.land (Nat.shiftRight A 3) 1) (Nat.shiftLeft B 3)))
    (Nat.mul (Nat.land (Nat.shiftRight A 4) 1) (Nat.shiftLeft B 4)))
    (Nat.mul (Nat.land (Nat.shiftRight A 5) 1) (Nat.shiftLeft B 5)))
    (Nat.mul (Nat.land (Nat.shiftRight A 6) 1) (Nat.shiftLeft B 6)))
    (Nat.mul (Nat.land (Nat.shiftRight A 7) 1) (Nat.shiftLeft B 7)))
    (Nat.mul (Nat.land (Nat.shiftRight A 8) 1) (Nat.shiftLeft B 8)))
    (Nat.mul (Nat.land (Nat.shiftRight A 9) 1) (Nat.shiftLeft B 9)))
    (Nat.mul (Nat.land (Nat.shiftRight A 10) 1) (Nat.shiftLeft B 10)))
    (Nat.mul (Nat.land (Nat.shiftRight A 11) 1) (Nat.shiftLeft B 11)))
    (Nat.mul (Nat.land (Nat.shiftRight A 12) 1) (Nat.shiftLeft B 12)))
    (Nat.mul (Nat.land (Nat.shiftRight A 13) 1) (Nat.shiftLeft B 13)))
    (Nat.mul (Nat.land (Nat.shiftRight A 14) 1) (Nat.shiftLeft B 14)))
    (Nat.mul (Nat.land (Nat.shiftRight A 15) 1) (Nat.shiftLeft B 15)))
    (Nat.mul (Nat.land (Nat.shiftRight A 16) 1) (Nat.shiftLeft B 16)))
    (Nat.mul (Nat.land (Nat.shiftRight A 17) 1) (Nat.shiftLeft B 17)))
    (Nat.mul (Nat.land (Nat.shiftRight A 18) 1) (Nat.shiftLeft B 18)))
    (Nat.mul (Nat.land (Nat.shiftRight A 19) 1) (Nat.shiftLeft B 19)))
    (Nat.mul (Nat.land (Nat.shiftRight A 20) 1) (Nat.shiftLeft B 20)))
    (Nat.mul (Nat.land (Nat.shiftRight A 21) 1) (Nat.shiftLeft B 21)))
    (Nat.mul (Nat.land (Nat.shiftRight A 22) 1) (Nat.shiftLeft B 22)))
    (Nat.mul (Nat.land (Nat.shiftRight A 23) 1) (Nat.shiftLeft B 23)))
    (Nat.mul (Nat.land (Nat.shiftRight A 24) 1) (Nat.shiftLeft B 24)))
    (Nat.mul (Nat.land (Nat.shiftRight A 25) 1) (Nat.shiftLeft B 25)))
    (Nat.mul (Nat.land (Nat.shiftRight A 26) 1) (Nat.shiftLeft B 26)))
    (Nat.mul (Nat.land (Nat.shiftRight A 27) 1) (Nat.shiftLeft B 27)))
    (Nat.mul (Nat.land (Nat.shiftRight A 28) 1) (Nat.shiftLeft B 28)))
    (Nat.mul (Nat.land (Nat.shiftRight A 29) 1) (Nat.shiftLeft B 29)))
    (Nat.mul (Nat.land (Nat.shiftRight A 30) 1) (Nat.shiftLeft B 30)))
    (Nat.mul (Nat.land (Nat.shiftRight A 31) 1) (Nat.shiftLeft B 31)))
    (Nat.mul (Nat.land (Nat.shiftRight A 32) 1) (Nat.shiftLeft B 32)))
    (Nat.mul (Nat.land (Nat.shiftRight A 33) 1) (Nat.shiftLeft B 33)))
    (Nat.mul (Nat.land (Nat.shiftRight A 34) 1) (Nat.shiftLeft B 34)))
    (Nat.mul (Nat.land (Nat.shiftRight A 35) 1) (Nat.shiftLeft B 35)))
    (Nat.mul (Nat.land (Nat.shiftRight A 36) 1) (Nat.shiftLeft B 36)))
    (Nat.mul (Nat.land (Nat.shiftRight A 37) 1) (Nat.shiftLeft B 37)))
    (Nat.mul (Nat.land (Nat.shiftRight A 38) 1) (Nat.shiftLeft B 38)))
    (Nat.mul (Nat.land (Nat.shiftRight A 39) 1) (Nat.shiftLeft B 39)))
    (Nat.mul (Nat.land (Nat.shiftRight A 40) 1) (Nat.shiftLeft B 40)))
    (Nat.mul (Nat.land (Nat.shiftRight A 41) 1) (Nat.shiftLeft B 41)))
    (Nat.mul (Nat.land (Nat.shiftRight A 42) 1) (Nat.shiftLeft B 42)))
    (Nat.mul (Nat.land (Nat.shiftRight A 43) 1) (Nat.shiftLeft B 43)))
    (Nat.mul (Nat.land (Nat.shiftRight A 44) 1) (Nat.shiftLeft B 44)))
    (Nat.mul (Nat.land (Nat.shiftRight A 45) 1) (Nat.shiftLeft B 45)))
    (Nat.mul (Nat.land (Nat.shiftRight A 46) 1) (Nat.shiftLeft B 46)))
    (Nat.mul (Nat.land (Nat.shiftRight A 47) 1) (Nat.shiftLeft B 47)))
    (Nat.mul (Nat.land (Nat.shiftRight A 48) 1) (Nat.shiftLeft B 48)))
    (Nat.mul (Nat.land (Nat.shiftRight A 49) 1) (Nat.shiftLeft B 49)))
    (Nat.mul (Nat.land (Nat.shiftRight A 50) 1) (Nat.shiftLeft B 50)))
    (Nat.mul (Nat.land (Nat.shiftRight A 51) 1) (Nat.shiftLeft B 51)))
    (Nat.mul (Nat.land (Nat.shiftRight A 52) 1) (Nat.shiftLeft B 52)))
    (Nat.mul (Nat.land (Nat.shiftRight A 53) 1) (Nat.shiftLeft B 53)))
    (Nat.mul (Nat.land (Nat.shiftRight A 54) 1) (Nat.shiftLeft B 54)))
    (Nat.mul (Nat.land (Nat.shiftRight A 55) 1) (Nat.shiftLeft B 55)))
    (Nat.mul (Nat.land (Nat.shiftRight A 56) 1) (Nat.shiftLeft B 56)))
    (Nat.mul (Nat.land (Nat.shiftRight A 57) 1) (Nat.shiftLeft B 57)))
    (Nat.mul (Nat.land (Nat.shiftRight A 58) 1) (Nat.shiftLeft B 58)))
    (Nat.mul (Nat.land (Nat.shiftRight A 59) 1) (Nat.shiftLeft B 59)))
    (Nat.mul (Nat.land (Nat.shiftRight A 60) 1) (Nat.shiftLeft B 60)))
    (Nat.mul (Nat.land (Nat.shiftRight A 61) 1) (Nat.shiftLeft B 61)))
    (Nat.mul (Nat.land (Nat.shiftRight A 62) 1) (Nat.shiftLeft B 62)))
    (Nat.mul (Nat.land (Nat.shiftRight A 63) 1) (Nat.shiftLeft B 63)))

/-- The unrolled product is the fold of `clStep` over the 64 bit positions. -/
theorem clU_eq (A B : Nat) : clU A B = idx64.foldl (clStep A B) 0 := rfl

/-- One reduction fold by `x^64 = x^4 + x^3 + x + 1` on natural numbers. -/
def foldN (C : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.shiftRight C 64)
    (Nat.shiftLeft (Nat.shiftRight C 64) 1)) (Nat.shiftLeft (Nat.shiftRight C 64) 3))
    (Nat.shiftLeft (Nat.shiftRight C 64) 4)) (Nat.land C 18446744073709551615)

/-- The `GF(2^64)` product on the natural-number representation. -/
def fastMul (A B : Nat) : Nat := Nat.land (foldN (foldN (clU A B))) 18446744073709551615

/-! ## Correctness of the unrolled product -/

private theorem fin_foldl_eq_range {α : Type} (G : α → Nat → α) :
    ∀ (n : Nat) (f : α → Fin n → α), (∀ acc (i : Fin n), f acc i = G acc i.val) →
      ∀ init : α, Fin.foldl n f init = (List.range n).foldl G init
  | 0, _, _, init => by simp
  | n + 1, f, hf, init => by
    rw [Fin.foldl_succ_last, List.range_succ, List.foldl_append,
      fin_foldl_eq_range G n _ (fun acc i => by rw [hf]; rfl) init]
    simp only [List.foldl_cons, List.foldl_nil, hf, Fin.val_last]

private theorem foldl_hom {α β : Type} (φ : α → β) (G : α → Nat → α) (H : β → Nat → β) :
    ∀ (l : List Nat) (init : α), (∀ acc i, i ∈ l → φ (G acc i) = H (φ acc) i) →
      φ (l.foldl G init) = l.foldl H (φ init)
  | [], _, _ => rfl
  | i :: l, init, h => by
    simp only [List.foldl_cons]
    rw [foldl_hom φ G H l (G init i) (fun acc j hj => h acc j (List.mem_cons_of_mem i hj)),
      h init i List.mem_cons_self]

private theorem land_shift_one (A i : Nat) :
    Nat.land (Nat.shiftRight A i) 1 = if A.testBit i then 1 else 0 := by
  change (A >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (A / 2 ^ i) with h | h <;> simp [h]

private theorem step_toNat (a b : BitVec 64) (acc : BitVec 128) {i : Nat} (hi : i < 64) :
    (if a.getLsbD i then acc ^^^ (zeroExtendTo b <<< i) else acc).toNat =
      clStep a.toNat b.toNat acc.toNat i := by
  unfold clStep
  rw [land_shift_one]
  change _ = acc.toNat ^^^ ((if a.toNat.testBit i then 1 else 0) * (b.toNat <<< i))
  rw [BitVec.getLsbD]
  cases a.toNat.testBit i
  · simp
  · simp only [if_true, Nat.one_mul, BitVec.toNat_xor, BitVec.toNat_shiftLeft,
      toNat_zeroExtendTo b (by omega : 64 ≤ 128)]
    congr 1
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    calc b.toNat * 2 ^ i < 2 ^ 64 * 2 ^ i := Nat.mul_lt_mul_of_pos_right b.isLt (by positivity)
      _ = 2 ^ (64 + i) := (Nat.pow_add 2 64 i).symm
      _ ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The carry-less product of two 64-bit words, as a natural number. -/
theorem carryLessMul_toNat (a b : BitVec 64) :
    (carryLessMul (w := 128) a b).toNat = clU a.toNat b.toNat := by
  rw [clU_eq, show idx64 = List.range 64 from rfl]
  unfold carryLessMul
  rw [fin_foldl_eq_range
    (fun acc i => if a.getLsbD i then acc ^^^ (zeroExtendTo b <<< i) else acc) 64 _
    (fun _ _ => rfl)]
  exact foldl_hom BitVec.toNat _ _ _ 0
    (fun acc i hi => step_toNat a b acc (List.mem_range.mp hi))

private theorem toPoly_injective {w : Nat} {a b : BitVec w} (h : toPoly a = toPoly b) : a = b := by
  have h0 : toPoly (a ^^^ b) = 0 := by rw [toPoly_xor, h, ZMod2Poly.add_self_cancel]
  have hx : a ^^^ b = 0 := by
    by_contra hne
    exact (toPoly_ne_zero_iff_ne_zero _).mpr hne h0
  calc a = a ^^^ (b ^^^ b) := by rw [BitVec.xor_self, BitVec.xor_zero]
    _ = (a ^^^ b) ^^^ b := (BitVec.xor_assoc a b b).symm
    _ = b := by rw [hx]; simp

private theorem carryLessMul_comm (a b : BitVec 64) :
    carryLessMul (w := 128) a b = carryLessMul (w := 128) b a :=
  toPoly_injective (by
    rw [toPoly_carryLessMul a b (by omega), toPoly_carryLessMul b a (by omega), mul_comm])

private theorem clU_27 (h : Nat) :
    clU 27 h = Nat.xor (Nat.xor (Nat.xor h (Nat.shiftLeft h 1)) (Nat.shiftLeft h 3))
      (Nat.shiftLeft h 4) := by
  have nl : ∀ x y : Nat, Nat.land x y = x &&& y := fun _ _ => rfl
  have nr : ∀ x y : Nat, Nat.shiftRight x y = x >>> y := fun _ _ => rfl
  have ns : ∀ x y : Nat, Nat.shiftLeft x y = x <<< y := fun _ _ => rfl
  have nx : ∀ x y : Nat, Nat.xor x y = x ^^^ y := fun _ _ => rfl
  have nm : ∀ x y : Nat, Nat.mul x y = x * y := fun _ _ => rfl
  simp only [clU, nl, nr, ns, nx, nm, Nat.reduceShiftRight, Nat.reduceAnd, Nat.zero_mul,
    Nat.one_mul, Nat.xor_zero, Nat.zero_xor, Nat.shiftLeft_zero]

private theorem mask_eq (x : Nat) : Nat.land x 18446744073709551615 = x % 2 ^ 64 := by
  change x &&& (2 ^ 64 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod x 64

private theorem foldStep_toNat (x : BitVec 128) : (BF64.foldStep x).toNat = foldN x.toNat := by
  unfold BF64.foldStep foldN
  rw [BitVec.toNat_xor, carryLessMul_comm, carryLessMul_toNat,
    toNat_zeroExtendTo _ (by omega : 64 ≤ 128), mask_eq]
  have hh : (BF64.highHalf x).toNat = Nat.shiftRight x.toNat 64 := by
    unfold BF64.highHalf
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by simpa using x.isLt)
  rw [hh, show BF64.reductionConstant.toNat = 27 from rfl, clU_27]
  rfl

/-- `BF64` multiplication, as a natural-number computation. -/
theorem mul_toNat (a b : BF64) : (a * b).toNat = fastMul a.toNat b.toNat := by
  rw [BF64.mul_def, BF64.reduce, fastMul, mask_eq, ← carryLessMul_toNat, ← foldStep_toNat,
    ← foldStep_toNat]
  unfold BF64.lowHalf
  rw [BitVec.toNat_setWidth]

/-- A `BF64` product certificate by closed natural-number evaluation. -/
theorem mul_eq_of_fastMul {a b c : BF64} (h : fastMul a.toNat b.toNat = c.toNat) : a * b = c :=
  BitVec.eq_of_toNat_eq (by rw [mul_toNat, h])

end OptimalOTS.BF64Fast
