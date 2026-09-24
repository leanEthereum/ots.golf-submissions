import Submissions.UpperRiscv.MixedProgram
import Submissions.UpperRiscv.Lanes

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (broadcast and_split and_split_at and_field fld laneValue)

def fineBits (_g _l : ℕ) : ℕ := 4
def coarseBits (_g _l : ℕ) : ℕ := 4
def fineFld (g u l : ℕ) : ℕ := fld u (16*l+2) (fineBits g l)
def coarseFld (g u l : ℕ) : ℕ := fld u (16*l+10) (coarseBits g l)
def maskNat (_g : ℕ) : ℕ := broadcast 0x3c3c
def laneNat (u g : ℕ) : ℕ :=
  (4*fineFld g u 0+1024*coarseFld g u 0) + 2^16*(4*fineFld g u 1+1024*coarseFld g u 1) +
  2^32*(4*fineFld g u 2+1024*coarseFld g u 2) + 2^48*(4*fineFld g u 3+1024*coarseFld g u 3)

theorem and_pair (y a b : ℕ) (ha : a ≤ 8) :
    y &&& (4*(2^a-1)+1024*(2^b-1)) = 4*(y/4%2^a)+1024*(y/1024%2^b) := by
  have hb : 4*(2^a-1) < 2^10 := by
    have : 2^a ≤ (2:ℕ)^8 := Nat.pow_le_pow_right (by omega) ha
    omega
  rw [show (1024:ℕ)=2^10 by norm_num, and_split_at _ _ _ 10 hb, and_field,
    Nat.and_two_pow_sub_one_eq_mod]
  have h : y % 2^10 / 4 % 2^a = y/4%2^a := by
    rw [show (2:ℕ)^10 = 4*2^8 by norm_num, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 ha)]
  rw [h]

private theorem mod_f5 (u : ℕ) : u%65536/4%32=u/4%32 := by omega
private theorem mod_f4 (u : ℕ) : u%65536/4%16=u/4%16 := by omega
private theorem mod_c3 (u : ℕ) : u%65536/1024%8=u/1024%8 := by omega
private theorem mod_c4 (u : ℕ) : u%65536/1024%16=u/1024%16 := by omega
private theorem mod_fold (u : ℕ) : u%65536/4%128=u/4%128 := by omega

theorem and_mask (u g : ℕ) : u &&& maskNat g = laneNat u g := by
  unfold maskNat laneNat fineFld coarseFld fineBits coarseBits fld
  have hm : broadcast 0x3c3c = (4*(2^4-1)+1024*(2^4-1)) + 2^16*((4*(2^4-1)+1024*(2^4-1)) +
      2^16*((4*(2^4-1)+1024*(2^4-1)) + 2^16*(4*(2^4-1)+1024*(2^4-1)))) := by
    norm_num [broadcast]
  rw [hm, and_split _ _ _ (by norm_num), and_split _ _ _ (by norm_num),
    and_split _ _ _ (by norm_num)]
  simp only [and_pair _ 5 3 (by omega), and_pair _ 4 4 (by omega)]
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  simp only [mod_f5, mod_f4, mod_c3, mod_c4, Nat.div_div_eq_div_mul]
  norm_num only [Nat.reduceMul]
  ring

theorem maskNat_toNat (g : ℕ) : (BitVec.ofNat 64 (maskNat g)).toNat = maskNat g := by
  norm_num [maskNat, broadcast]

theorem laneValue_toNat (u : Word) (g : ℕ) :
    (laneValue u (BitVec.ofNat 64 (maskNat g))).toNat = laneNat u.toNat g := by
  rw [laneValue, BitVec.toNat_and, maskNat_toNat, and_mask]

def preFold (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ) : ℕ :=
  (4*s0+1024*t0)+2^16*(4*s1+1024*t1)+2^32*(4*s2+1024*t2)+2^48*(4*s3+1024*t3)

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
    (4*s+1024*t+65536*rest)/65536 = rest := by omega
private theorem lane_fine (s t rest : ℕ) (hs : s < 128) :
    (4*s+1024*t+65536*rest)/4%128 = s := by omega
private theorem lane_coarse (s t rest : ℕ) (hs : s < 128) (ht : t < 64) :
    (4*s+1024*t+65536*rest)/1024%64 = t := by omega

private theorem fold_digit (a b r : ℕ) (ha : a < 128) :
    (a+256*b+65536*r)%128 = a := by omega

private theorem fold_quotient (a b r : ℕ) (ha : a < 128) (hb : b < 256) :
    (a+256*b+65536*r)/65536 = r := by omega

/-- The shifted fields fit into eight-bit cells; sums fit into seven bits. -/
theorem fold_fields (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ)
    (hs0 : s0 < 64) (hs1 : s1 < 64) (hs2 : s2 < 64) (hs3 : s3 < 64)
    (ht0 : t0 < 64) (ht1 : t1 < 64) (ht2 : t2 < 64) (ht3 : t3 < 64) :
    let p := preFold s0 s1 s2 s3 t0 t1 t2 t3
    let q := (p+p/256)%18446744073709551616
    q/4%128 = s0+t0 ∧ q/262144%128 = s1+t1 ∧
      q/17179869184%128 = s2+t2 ∧ q/1125899906842624%128 = s3+t3 := by
  dsimp only
  let n := s0+256*t0+65536*s1+16777216*t1+4294967296*s2+
    1099511627776*t2+281474976710656*s3+72057594037927936*t3
  let rest := t0+256*s1+65536*t1+16777216*s2+4294967296*t2+
    1099511627776*s3+281474976710656*t3
  have hp : preFold s0 s1 s2 s3 t0 t1 t2 t3 = 4*n := by dsimp [preFold,n]; ring
  have hn0 : n = s0+256*rest := by dsimp [n,rest]; ring
  have hn : n/256 = rest := by rw [hn0]; omega
  have hq : (4*n+4*n/256)/4 = n+n/256 := by omega
  have hb : 4*n+4*n/256 < 18446744073709551616 := by dsimp [n]; omega
  rw [hp, Nat.mod_eq_of_lt hb]
  let m3 := (s3+t3)+256*t3
  let m2 := (s2+t2)+256*(t2+s3)+65536*m3
  let m1 := (s1+t1)+256*(t1+s2)+65536*m2
  let m0 := (s0+t0)+256*(t0+s1)+65536*m1
  have q0 : n+n/256 = m0 := by rw [hn]; dsimp [n,rest,m0,m1,m2,m3]; ring
  have q1 : m0/65536 = m1 := fold_quotient _ _ _ (by omega) (by omega)
  have q2 : m1/65536 = m2 := fold_quotient _ _ _ (by omega) (by omega)
  have q3 : m2/65536 = m3 := fold_quotient _ _ _ (by omega) (by omega)
  constructor
  · rw [hq,q0]; exact fold_digit _ _ _ (by omega)
  constructor
  · rw [show (262144:ℕ)=4*65536 by decide, ← Nat.div_div_eq_div_mul,hq,q0,q1]
    exact fold_digit _ _ _ (by omega)
  constructor
  · rw [show (17179869184:ℕ)=4*(65536*65536) by decide,
      ← Nat.div_div_eq_div_mul,hq,q0, ← Nat.div_div_eq_div_mul,q1,q2]
    exact fold_digit _ _ _ (by omega)
  · rw [show (1125899906842624:ℕ)=4*(65536*(65536*65536)) by decide,
      ← Nat.div_div_eq_div_mul,hq,q0, ← Nat.div_div_eq_div_mul,q1,
      ← Nat.div_div_eq_div_mul,q2,q3]
    simpa only [Nat.mul_zero,Nat.add_zero] using fold_digit (s3+t3) t3 0 (by omega)

theorem fold_toNat (s0 s1 s2 s3 t0 t1 t2 t3 : ℕ)
    (hs0 : s0 < 64) (hs1 : s1 < 64) (hs2 : s2 < 64) (hs3 : s3 < 64)
    (ht0 : t0 < 64) (ht1 : t1 < 64) (ht2 : t2 < 64) (ht3 : t3 < 64) :
    let p := preFold s0 s1 s2 s3 t0 t1 t2 t3
    ((p+p/256)%2^64 &&& broadcast 0x1fc) =
      4*(s0+t0)+2^16*(4*(s1+t1))+2^32*(4*(s2+t2))+2^48*(4*(s3+t3)) := by
  dsimp only
  obtain ⟨h0,h1,h2,h3⟩ := fold_fields s0 s1 s2 s3 t0 t1 t2 t3 hs0 hs1 hs2 hs3 ht0 ht1 ht2 ht3
  rw [and_foldMask]
  norm_num only [Nat.reducePow] at *
  rw [h0,h1,h2,h3]

theorem lane_remainder (a b c d : ℕ) (h : a+b+c+d < 65535) :
    (a+2^16*b+2^32*c+2^48*d)%65535 = a+b+c+d := by
  have e : a+2^16*b+2^32*c+2^48*d =
      (a+b+c+d)+65535*(b+65537*c+4295032833*d) := by ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

end OptimalOTS.RiscvMixedProgram
