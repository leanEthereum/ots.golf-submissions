import Submissions.UpperRiscv.Program
import Submissions.UpperRiscv.Valid

/-!
# Lane arithmetic of the index check

A lane word holds four 16-bit lanes. The pair mask leaves `4 · dA + 1024 · dB` in every lane of
words 0–2, the single mask `4 · d` in every lane of word 3 (`laneValue_toNat`). The four masked
words are summed without carries; the fold `(a + (a >>> 8)) &&& m` with the mask of
bits `2 … 9` then leaves `4 · (Σ dA + Σ dB)` in every lane (`fold_toNat`), and the sum of the
four lanes is read from the top lane of a product (`topLane`). Everything reduces to natural
number arithmetic through `Nat.and_mod_two_pow` and `Nat.and_div_two_pow`.
-/

namespace OptimalOTS.Riscv2Program

open RiscvZkvm.Rv64

/-! ## Masks -/

theorem and_split_at (x a b n : ℕ) (ha : a < 2 ^ n) :
    x &&& (a + 2 ^ n * b) = (x % 2 ^ n &&& a) + 2 ^ n * (x / 2 ^ n &&& b) := by
  rw [← Nat.mod_add_div (x &&& (a + 2 ^ n * b)) (2 ^ n), Nat.and_mod_two_pow,
    Nat.and_div_two_pow]
  have e1 : (a + 2 ^ n * b) % 2 ^ n = a := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have e2 : (a + 2 ^ n * b) / 2 ^ n = b := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [e1, e2]

theorem and_split (x a b : ℕ) (ha : a < 2 ^ 16) :
    x &&& (a + 2 ^ 16 * b) = (x % 2 ^ 16 &&& a) + 2 ^ 16 * (x / 2 ^ 16 &&& b) :=
  and_split_at x a b 16 ha

/-- A mask of `b` bits shifted up by two keeps `4 · (y / 4 % 2 ^ b)`. -/
theorem and_field (y b : ℕ) : y &&& (4 * (2 ^ b - 1)) = 4 * (y / 4 % 2 ^ b) := by
  rw [← Nat.mod_add_div (y &&& (4 * (2 ^ b - 1))) (2 ^ 2), Nat.and_mod_two_pow,
    Nat.and_div_two_pow]
  have e1 : (4 * (2 ^ b - 1)) % 2 ^ 2 = 0 := by omega
  have e2 : (4 * (2 ^ b - 1)) / 2 ^ 2 = 2 ^ b - 1 := by omega
  rw [e1, e2, Nat.and_zero, Nat.and_two_pow_sub_one_eq_mod]
  norm_num

/-- The pair mask of one lane: bits `2 … 6` and `10 … 13`. -/
theorem and_pairLane (y : ℕ) : y &&& pairMask = 4 * (y / 4 % 32) + 1024 * (y / 1024 % 16) := by
  have hm : pairMask = 4 * (2 ^ 5 - 1) + 2 ^ 10 * (2 ^ 4 - 1) := by norm_num [pairMask]
  rw [hm, and_split_at _ _ _ 10 (by norm_num), and_field, Nat.and_two_pow_sub_one_eq_mod]
  have e : y % 2 ^ 10 / 4 % 2 ^ 5 = y / 4 % 32 := by
    rw [show (2 : ℕ) ^ 10 = 4 * 2 ^ 8 by norm_num, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (by norm_num : (2 ^ 5 : ℕ) ∣ 2 ^ 8)]
    norm_num
  rw [e]
  norm_num

/-! The fields of the lanes of a word, one at a time: `omega` handles each on its own. -/

theorem lane0_fine (x : ℕ) : x % 2 ^ 16 / 4 % 32 = x / 4 % 32 := by omega
theorem lane0_coarse (x : ℕ) : x % 2 ^ 16 / 1024 % 16 = x / 2 ^ 10 % 16 := by omega
theorem lane1_fine (x : ℕ) : x / 2 ^ 16 % 2 ^ 16 / 4 % 32 = x / 2 ^ 18 % 32 := by omega
theorem lane1_coarse (x : ℕ) : x / 2 ^ 16 % 2 ^ 16 / 1024 % 16 = x / 2 ^ 26 % 16 := by omega
theorem lane2_fine (x : ℕ) : x / 2 ^ 16 / 2 ^ 16 % 2 ^ 16 / 4 % 32 = x / 2 ^ 34 % 32 := by omega
theorem lane2_coarse (x : ℕ) : x / 2 ^ 16 / 2 ^ 16 % 2 ^ 16 / 1024 % 16 = x / 2 ^ 42 % 16 := by
  omega
theorem lane3_fine (x : ℕ) : x / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 4 % 32 = x / 2 ^ 50 % 32 := by omega
theorem lane3_coarse (x : ℕ) : x / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 1024 % 16 = x / 2 ^ 58 % 16 := by
  omega
theorem lane0_fold (x : ℕ) : x % 2 ^ 16 / 4 % 256 = x / 4 % 256 := by omega
theorem lane1_fold (x : ℕ) : x / 2 ^ 16 % 2 ^ 16 / 4 % 256 = x / 2 ^ 18 % 256 := by omega
theorem lane2_fold (x : ℕ) : x / 2 ^ 16 / 2 ^ 16 % 2 ^ 16 / 4 % 256 = x / 2 ^ 34 % 256 := by omega
theorem lane3_fold (x : ℕ) : x / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 4 % 256 = x / 2 ^ 50 % 256 := by omega

/-- The mask `0x3C7C3C7C3C7C3C7C`, lane by lane. -/
theorem and_maskPair (x : ℕ) :
    x &&& broadcast pairMask =
      (4 * (x / 4 % 32) + 1024 * (x / 2 ^ 10 % 16)) +
      2 ^ 16 * (4 * (x / 2 ^ 18 % 32) + 1024 * (x / 2 ^ 26 % 16)) +
      2 ^ 32 * (4 * (x / 2 ^ 34 % 32) + 1024 * (x / 2 ^ 42 % 16)) +
      2 ^ 48 * (4 * (x / 2 ^ 50 % 32) + 1024 * (x / 2 ^ 58 % 16)) := by
  have hb : broadcast pairMask = pairMask + 2 ^ 16 * (pairMask + 2 ^ 16 *
      (pairMask + 2 ^ 16 * pairMask)) := by
    unfold broadcast; ring
  have hp : pairMask < 2 ^ 16 := by norm_num [pairMask]
  rw [hb, and_split _ _ _ hp, and_split _ _ _ hp, and_split _ _ _ hp, and_pairLane, and_pairLane,
    and_pairLane, and_pairLane, lane0_fine, lane0_coarse, lane1_fine, lane1_coarse, lane2_fine,
    lane2_coarse, lane3_fine, lane3_coarse]
  ring

/-- The mask `0x007C007C007C007C` keeps bits `2 … 6` of every lane. -/
theorem and_maskSingle (x : ℕ) :
    x &&& broadcast singleMask =
      4 * (x / 4 % 32) + 2 ^ 16 * (4 * (x / 2 ^ 18 % 32)) +
      2 ^ 32 * (4 * (x / 2 ^ 34 % 32)) + 2 ^ 48 * (4 * (x / 2 ^ 50 % 32)) := by
  have hb : broadcast singleMask = 4 * (2 ^ 5 - 1) + 2 ^ 16 * (4 * (2 ^ 5 - 1) + 2 ^ 16 *
      (4 * (2 ^ 5 - 1) + 2 ^ 16 * (4 * (2 ^ 5 - 1)))) := by
    norm_num [broadcast, singleMask]
  rw [hb, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num), and_field, and_field, and_field, and_field]
  rw [show (2 : ℕ) ^ 5 = 32 by norm_num, lane0_fine, lane1_fine, lane2_fine, lane3_fine]
  ring

/-- The mask `0x03FC03FC03FC03FC` keeps bits `2 … 9` of every lane. -/
theorem and_maskFold (x : ℕ) :
    x &&& broadcast foldMask =
      4 * (x / 4 % 256) + 2 ^ 16 * (4 * (x / 2 ^ 18 % 256)) +
      2 ^ 32 * (4 * (x / 2 ^ 34 % 256)) + 2 ^ 48 * (4 * (x / 2 ^ 50 % 256)) := by
  have hb : broadcast foldMask = 4 * (2 ^ 8 - 1) + 2 ^ 16 * (4 * (2 ^ 8 - 1) + 2 ^ 16 *
      (4 * (2 ^ 8 - 1) + 2 ^ 16 * (4 * (2 ^ 8 - 1)))) := by
    norm_num [broadcast, foldMask]
  rw [hb, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num), and_field, and_field, and_field, and_field]
  rw [show (2 : ℕ) ^ 8 = 256 by norm_num, lane0_fold, lane1_fold, lane2_fold, lane3_fold]
  ring

/-! ## Fields of a word -/

/-- A field of a word: bits `p …` of width `b`. -/
def fld (u p b : ℕ) : ℕ := u / 2 ^ p % 2 ^ b

/-- The fine field of lane `l`: bits `2 … 6`. -/
def fineFld (u l : ℕ) : ℕ := fld u (16 * l + 2) 5

/-- The coarse field of lane `l`: bits `10 … 13`. -/
def coarseFld (u l : ℕ) : ℕ := fld u (16 * l + 10) 4

/-- The mask of lane word `g`. -/
def maskNat (g : ℕ) : ℕ := if g < 3 then broadcast pairMask else broadcast singleMask

/-- The coarse contribution of lane word `g`: only the pair words have one. -/
def coarseOf (g u l : ℕ) : ℕ := if g < 3 then coarseFld u l else 0

/-- Lane word `g` of the index word `u`: `4 · dA + 1024 · dB` in the four lanes. -/
def laneNat (u g : ℕ) : ℕ :=
  (4 * fineFld u 0 + 1024 * coarseOf g u 0) + 2 ^ 16 * (4 * fineFld u 1 + 1024 * coarseOf g u 1) +
  2 ^ 32 * (4 * fineFld u 2 + 1024 * coarseOf g u 2) + 2 ^ 48 * (4 * fineFld u 3 + 1024 * coarseOf g u 3)

/-- The machine's lane word. -/
def laneValue (u mask : Word) : Word := u &&& mask

theorem maskNat_toNat (g : ℕ) : (BitVec.ofNat 64 (maskNat g)).toNat = maskNat g := by
  rw [BitVec.toNat_ofNat]
  unfold maskNat broadcast pairMask singleMask
  split_ifs <;> norm_num

theorem laneValue_toNat (u : Word) (g : ℕ) :
    (laneValue u (BitVec.ofNat 64 (maskNat g))).toNat = laneNat u.toNat g := by
  unfold laneValue laneNat fineFld coarseOf coarseFld fld
  rw [BitVec.toNat_and, maskNat_toNat]
  unfold maskNat
  split_ifs with hg
  · rw [and_maskPair]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    norm_num
  · rw [and_maskSingle]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    norm_num

/-! ## Folding the coarse fields onto the fine ones -/

/-- The lane sum of the four masked words, with fine sums `s` and coarse sums `t`, before the
fold. -/
def preFold (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ) : ℕ :=
  (4 * s0 + 1024 * t0) + 2 ^ 16 * (4 * s1 + 1024 * t1) + 2 ^ 32 * (4 * s2 + 1024 * t2) +
    2 ^ 48 * (4 * s3 + 1024 * t3)

theorem lowByte (a b : Nat) (ha : a < 256) :
    (a+256*b)%256 = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem fold_fields (s0 s1 s2 s3 t0 t1 t2 t3 : Nat)
    (hs0 : s0 < 128) (hs1 : s1 < 128) (hs2 : s2 < 128) (hs3 : s3 < 128)
    (ht0 : t0 < 48) (ht1 : t1 < 48) (ht2 : t2 < 48) (ht3 : t3 < 48) :
    let p := (4*s0+1024*t0) + 65536*(4*s1+1024*t1) +
      4294967296*(4*s2+1024*t2) + 281474976710656*(4*s3+1024*t3)
    let q := (p+p/256)%18446744073709551616
    q/4%256 = s0+t0 ∧ q/262144%256 = s1+t1 ∧
      q/17179869184%256 = s2+t2 ∧ q/1125899906842624%256 = s3+t3 := by
  dsimp
  let n := s0+256*t0+65536*s1+16777216*t1+4294967296*s2+
    1099511627776*t2+281474976710656*s3+72057594037927936*t3
  have hp : (4*s0+1024*t0) + 65536*(4*s1+1024*t1) +
      4294967296*(4*s2+1024*t2) + 281474976710656*(4*s3+1024*t3) = 4*n := by
    dsimp [n]; ring
  rw [hp]
  have hn : n/256 = t0+256*s1+65536*t1+16777216*s2+4294967296*t2+
      1099511627776*s3+281474976710656*t3 := by dsimp [n]; omega
  have hq : (4*n+4*n/256)/4 = n+n/256 := by omega
  have hbound : 4*n+4*n/256 < 18446744073709551616 := by dsimp [n]; omega
  rw [Nat.mod_eq_of_lt hbound]
  have q0 : n+n/256 = (s0+t0)+256*((t0+s1)+256*((s1+t1)+256*((t1+s2)+
      256*((s2+t2)+256*((t2+s3)+256*((s3+t3)+256*t3)))))) := by rw [hn]; dsimp [n]; ring
  have q1 : (n+n/256)/65536 = (s1+t1)+256*((t1+s2)+
      256*((s2+t2)+256*((t2+s3)+256*((s3+t3)+256*t3)))) := by rw [q0]; omega
  have q2 : (n+n/256)/4294967296 = (s2+t2)+256*((t2+s3)+256*((s3+t3)+256*t3)) := by
    rw [q0]; omega
  have q3 : (n+n/256)/281474976710656 = (s3+t3)+256*t3 := by rw [q0]; omega
  constructor
  · rw [hq, q0]; exact lowByte _ _ (by omega)
  constructor
  · rw [show (262144:Nat) = 4*65536 by decide, ← Nat.div_div_eq_div_mul, hq, q1]
    exact lowByte _ _ (by omega)
  constructor
  · rw [show (17179869184:Nat) = 4*4294967296 by decide, ← Nat.div_div_eq_div_mul, hq, q2]
    exact lowByte _ _ (by omega)
  · rw [show (1125899906842624:Nat) = 4*281474976710656 by decide, ← Nat.div_div_eq_div_mul, hq, q3]
    exact lowByte _ _ (by omega)

/-- Mask once after addition; low discarded bits cannot carry into retained fields. -/
theorem fold_toNat (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ)
    (hs0 : s0 < 128) (hs1 : s1 < 128) (hs2 : s2 < 128) (hs3 : s3 < 128)
    (ht0 : t0 < 48) (ht1 : t1 < 48) (ht2 : t2 < 48) (ht3 : t3 < 48) :
    ((preFold s0 s1 s2 s3 t0 t1 t2 t3 + preFold s0 s1 s2 s3 t0 t1 t2 t3 / 2 ^ 8) % 2 ^ 64
        &&& broadcast foldMask) =
      4 * (s0 + t0) + 2 ^ 16 * (4 * (s1 + t1)) + 2 ^ 32 * (4 * (s2 + t2)) +
        2 ^ 48 * (4 * (s3 + t3)) := by
  obtain ⟨h0, h1, h2, h3⟩ := fold_fields s0 s1 s2 s3 t0 t1 t2 t3 hs0 hs1 hs2 hs3 ht0 ht1 ht2 ht3
  rw [and_maskFold]
  norm_num [preFold] at *
  rw [h0, h1, h2, h3]

/-- The pre-fold value fits in a word. -/
theorem preFold_lt (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ)
    (hs0 : s0 < 128) (hs1 : s1 < 128) (hs2 : s2 < 128) (hs3 : s3 < 128)
    (ht0 : t0 < 48) (ht1 : t1 < 48) (ht2 : t2 < 48) (ht3 : t3 < 48) :
    preFold s0 s1 s2 s3 t0 t1 t2 t3 < 2 ^ 64 := by
  unfold preFold; omega

/-! ## Summing lanes -/

/-- The top lane of `A * 0x0001000100010001` is the sum of the lanes of `A`, when no lane of `A`
exceeds `1000`. -/
theorem topLane (a0 a1 a2 a3 : ℕ) (h0 : a0 ≤ 1000) (h1 : a1 ≤ 1000) (h2 : a2 ≤ 1000)
    (h3 : a3 ≤ 1000) :
    (a0 + 2 ^ 16 * a1 + 2 ^ 32 * a2 + 2 ^ 48 * a3) * broadcast 1 % 2 ^ 64 / 2 ^ 48 =
      a0 + a1 + a2 + a3 := by
  have e : (a0 + 2 ^ 16 * a1 + 2 ^ 32 * a2 + 2 ^ 48 * a3) * broadcast 1 =
      (a0 + 2 ^ 16 * (a0 + a1) + 2 ^ 32 * (a0 + a1 + a2) + 2 ^ 48 * (a0 + a1 + a2 + a3)) +
        2 ^ 64 * (a1 + a2 + a3 + 2 ^ 16 * (a2 + a3) + 2 ^ 32 * a3) := by
    unfold broadcast; ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

end OptimalOTS.Riscv2Program
