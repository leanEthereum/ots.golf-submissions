import Submissions.UpperRiscvHint.MixedProgram
import Submissions.UpperRiscvHint.Lanes

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

end OptimalOTS.RiscvMixedProgram
