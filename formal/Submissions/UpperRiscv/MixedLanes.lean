import Submissions.UpperRiscv.MixedProgram
import Submissions.UpperRiscv.Lanes

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (broadcast and_split and_split_at and_field fld laneValue)

def fineBits (g l : ℕ) : ℕ := if g = 0 ∧ l < 2 then 5 else 4
def coarseBits (g l : ℕ) : ℕ := if g = 0 ∧ l < 2 then 3 else 4
def fineFld (g u l : ℕ) : ℕ := fld u (16*l+2) (fineBits g l)
def coarseFld (g u l : ℕ) : ℕ := fld u (16*l+9) (coarseBits g l)
def maskNat (g : ℕ) : ℕ := if g = 0 then firstMask else broadcast 0x1e3c
def laneNat (u g : ℕ) : ℕ :=
  (4*fineFld g u 0+512*coarseFld g u 0) + 2^16*(4*fineFld g u 1+512*coarseFld g u 1) +
  2^32*(4*fineFld g u 2+512*coarseFld g u 2) + 2^48*(4*fineFld g u 3+512*coarseFld g u 3)

theorem and_pair (y a b : ℕ) (ha : a ≤ 7) :
    y &&& (4*(2^a-1)+512*(2^b-1)) = 4*(y/4%2^a)+512*(y/512%2^b) := by
  have hb : 4*(2^a-1) < 2^9 := by
    have : 2^a ≤ (2:ℕ)^7 := Nat.pow_le_pow_right (by omega) ha
    omega
  rw [show (512:ℕ)=2^9 by norm_num, and_split_at _ _ _ 9 hb, and_field,
    Nat.and_two_pow_sub_one_eq_mod]
  have h : y % 2^9 / 4 % 2^a = y/4%2^a := by
    rw [show (2:ℕ)^9 = 4*2^7 by norm_num, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 ha)]
  rw [h]

private theorem mod_f5 (u : ℕ) : u%65536/4%32=u/4%32 := by omega
private theorem mod_f4 (u : ℕ) : u%65536/4%16=u/4%16 := by omega
private theorem mod_c3 (u : ℕ) : u%65536/512%8=u/512%8 := by omega
private theorem mod_c4 (u : ℕ) : u%65536/512%16=u/512%16 := by omega
private theorem mod_fold (u : ℕ) : u%65536/4%128=u/4%128 := by omega

theorem and_mask (u g : ℕ) : u &&& maskNat g = laneNat u g := by
  unfold maskNat laneNat fineFld coarseFld fineBits coarseBits fld
  by_cases hg : g = 0
  · subst g
    simp only [true_and, Nat.reduceLT, ↓reduceIte]
    have hm : firstMask = (4*(2^5-1)+512*(2^3-1)) + 2^16*((4*(2^5-1)+512*(2^3-1)) +
        2^16*((4*(2^4-1)+512*(2^4-1)) + 2^16*(4*(2^4-1)+512*(2^4-1)))) := by
      norm_num [firstMask]
    rw [hm, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
      and_split _ _ _ (by norm_num)]
    simp only [and_pair _ 5 3 (by omega), and_pair _ 4 4 (by omega)]
    norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    simp only [mod_f5, mod_f4, mod_c3, mod_c4, Nat.div_div_eq_div_mul]
    norm_num only [Nat.reduceMul]
    ring
  · simp only [hg, false_and, ↓reduceIte]
    have hm : broadcast 0x1e3c = (4*(2^4-1)+512*(2^4-1)) + 2^16*((4*(2^4-1)+512*(2^4-1)) +
        2^16*((4*(2^4-1)+512*(2^4-1)) + 2^16*(4*(2^4-1)+512*(2^4-1)))) := by
      norm_num [broadcast]
    rw [hm, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
      and_split _ _ _ (by norm_num)]
    simp only [and_pair _ 5 3 (by omega), and_pair _ 4 4 (by omega)]
    norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    simp only [mod_f5, mod_f4, mod_c3, mod_c4, Nat.div_div_eq_div_mul]
    norm_num only [Nat.reduceMul]
    ring

theorem maskNat_toNat (g : ℕ) : (BitVec.ofNat 64 (maskNat g)).toNat = maskNat g := by
  unfold maskNat
  split_ifs <;> norm_num [firstMask, broadcast]

theorem laneValue_toNat (u : Word) (g : ℕ) :
    (laneValue u (BitVec.ofNat 64 (maskNat g))).toNat = laneNat u.toNat g := by
  rw [laneValue, BitVec.toNat_and, maskNat_toNat, and_mask]

def preFold (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ) : ℕ :=
  (4*s0+512*t0)+2^16*(4*s1+512*t1)+2^32*(4*s2+512*t2)+2^48*(4*s3+512*t3)

theorem and_foldMask (x : ℕ) : x &&& broadcast 0x1fc =
    4*(x/4%128)+2^16*(4*(x/2^18%128))+2^32*(4*(x/2^34%128))+2^48*(4*(x/2^50%128)) := by
  have hm : broadcast 0x1fc = 4*(2^7-1)+2^16*(4*(2^7-1)+2^16*(4*(2^7-1)+2^16*(4*(2^7-1)))) := by
    norm_num [broadcast]
  rw [hm, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num), and_field, and_field, and_field, and_field]
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  simp only [mod_fold, Nat.div_div_eq_div_mul]
  norm_num only [Nat.reduceMul]
  ring

theorem preFold_lt (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ)
    (hs0 : s0 < 128) (hs1 : s1 < 128) (hs2 : s2 < 128) (hs3 : s3 < 128)
    (ht0 : t0 < 64) (ht1 : t1 < 64) (ht2 : t2 < 64) (ht3 : t3 < 64) :
    preFold s0 s1 s2 s3 t0 t1 t2 t3 < 2^64 := by unfold preFold; omega

private theorem lane_div (s t rest : ℕ) (hs : s < 128) (ht : t < 64) :
    (4*s+512*t+65536*rest)/65536 = rest := by omega
private theorem lane_fine (s t rest : ℕ) (hs : s < 128) :
    (4*s+512*t+65536*rest)/4%128 = s := by omega
private theorem lane_coarse (s t rest : ℕ) (hs : s < 128) (ht : t < 64) :
    (4*s+512*t+65536*rest)/512%128 = t := by omega

theorem fold_toNat (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ)
    (hs0 : s0 < 128) (hs1 : s1 < 128) (hs2 : s2 < 128) (hs3 : s3 < 128)
    (ht0 : t0 < 64) (ht1 : t1 < 64) (ht2 : t2 < 64) (ht3 : t3 < 64) :
    let p := preFold s0 s1 s2 s3 t0 t1 t2 t3
    (p/128 &&& broadcast 0x1fc) + (p &&& broadcast 0x1fc) =
      4*(s0+t0)+2^16*(4*(s1+t1))+2^32*(4*(s2+t2))+2^48*(4*(s3+t3)) := by
  dsimp only
  rw [and_foldMask, and_foldMask]
  let n3 := 4*s3+512*t3
  let n2 := 4*s2+512*t2+65536*n3
  let n1 := 4*s1+512*t1+65536*n2
  let n0 := 4*s0+512*t0+65536*n1
  have ep : preFold s0 s1 s2 s3 t0 t1 t2 t3 = n0 := by
    dsimp [preFold, n0, n1, n2, n3]; ring
  have q0 : n0/65536 = n1 := lane_div s0 t0 n1 hs0 ht0
  have q1 : n1/65536 = n2 := lane_div s1 t1 n2 hs1 ht1
  have q2 : n2/65536 = n3 := lane_div s2 t2 n3 hs2 ht2
  have es0 : n0/4%128 = s0 := lane_fine _ _ _ hs0
  have et0 : n0/512%128 = t0 := lane_coarse _ _ _ hs0 ht0
  have es1 : n0/262144%128 = s1 := by
    rw [show (262144:ℕ)=65536*4 by decide, ← Nat.div_div_eq_div_mul, q0]
    exact lane_fine _ _ _ hs1
  have et1 : n0/33554432%128 = t1 := by
    rw [show (33554432:ℕ)=65536*512 by decide, ← Nat.div_div_eq_div_mul, q0]
    exact lane_coarse _ _ _ hs1 ht1
  have es2 : n0/17179869184%128 = s2 := by
    rw [show (17179869184:ℕ)=65536*(65536*4) by decide, ← Nat.div_div_eq_div_mul, q0,
      ← Nat.div_div_eq_div_mul, q1]
    exact lane_fine _ _ _ hs2
  have et2 : n0/2199023255552%128 = t2 := by
    rw [show (2199023255552:ℕ)=65536*(65536*512) by decide, ← Nat.div_div_eq_div_mul, q0,
      ← Nat.div_div_eq_div_mul, q1]
    exact lane_coarse _ _ _ hs2 ht2
  have es3 : n0/1125899906842624%128 = s3 := by
    rw [show (1125899906842624:ℕ)=65536*(65536*(65536*4)) by decide,
      ← Nat.div_div_eq_div_mul, q0, ← Nat.div_div_eq_div_mul, q1,
      ← Nat.div_div_eq_div_mul, q2]
    simpa only [Nat.mul_zero, Nat.add_zero] using lane_fine s3 t3 0 hs3
  have et3 : n0/144115188075855872%128 = t3 := by
    rw [show (144115188075855872:ℕ)=65536*(65536*(65536*512)) by decide,
      ← Nat.div_div_eq_div_mul, q0, ← Nat.div_div_eq_div_mul, q1,
      ← Nat.div_div_eq_div_mul, q2]
    simpa only [Nat.mul_zero, Nat.add_zero] using lane_coarse s3 t3 0 hs3 ht3
  rw [ep]
  norm_num only [Nat.reducePow, Nat.div_div_eq_div_mul, Nat.reduceMul]
  rw [et0, et1, et2, et3, es0, es1, es2, es3]
  ring

theorem lane_remainder (a b c d : ℕ) (h : a+b+c+d < 65535) :
    (a+2^16*b+2^32*c+2^48*d)%65535 = a+b+c+d := by
  have e : a+2^16*b+2^32*c+2^48*d =
      (a+b+c+d)+65535*(b+65537*c+4295032833*d) := by ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

end OptimalOTS.RiscvMixedProgram
