import Submissions.UpperLeanIsa.ConstraintMath
import Submissions.UpperLeanIsa.FieldRescale

/-!
# Layout and interfaces for the 1209-cycle Group3 machine

The raw 128-bit index has widths [10,9,9,9,9,11,11,10,10,10,10,10,10]. Two adjacent entries
of its first field share a tuple; the tie still checks every raw bit. MachineTable proves
that these raw fields implement the 127-bit effective scheme index.

Cost-banded blocks follow the prologue slots 0 … 21 (slot 21 is a pad), one block per live field
value (aliases of a tuple have separate blocks). The (3,10) groups have no block for their dummy
entry: group `u` has `VF u` blocks. A second copy of the first
group's region (frame 14, used when the free digit is 0) follows at `gEnd … zEnd`. Free entries
are 255615+68*s for s<64.
Frames reuse C_(f+1), where C_c=g^(2^60*c); C_16=g and C_0=ONE. Compat states the
scheme's lengths, digits, selected output halves, tags, metadata, and 88-step layer.
-/

namespace OptimalOTS.HLG3

open LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits)

/-! ## Exponent arithmetic -/

/-- The order of `g`, `2 ^ 64 - 1`, as a literal (so `omega` can reduce modulo it). -/
def ordG : ℕ := 18446744073709551615

theorem ordG_eq : ordG = 2 ^ 64 - 1 := by norm_num [ordG]

theorem gpow_mod (n : ℕ) : gpow (n % ordG) = gpow n := by
  rw [ordG_eq, ← orderOf_g]; exact pow_mod_orderOf g n

theorem mod_ord_of_lt {n : ℕ} (h : n < ordG) : n % ordG = n := Nat.mod_eq_of_lt h

theorem mod_ord_of_ge {n : ℕ} (h : ordG ≤ n) (h' : n < 2 * ordG) : n % ordG = n - ordG := by
  rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

theorem gpow_mul_gpow (a b : ℕ) : gpow a * gpow b = gpow (a + b) := (pow_add g a b).symm

theorem gpow_zero' : gpow 0 = 1 := pow_zero g

theorem g_mul_gpow (k : ℕ) : g * gpow k = gpow (k + 1) := (gpow_succ k).symm

/-- `gpow` is injective below the group order. -/
theorem gpow_inj {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1) (h : gpow a = gpow b) :
    a = b := gpow_injOn (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr hb) h

/-! ## Partial sums and bands -/

/-- `F 0 + ⋯ + F (c - 1)`. -/
def psum (F : ℕ → ℕ) (c : ℕ) : ℕ := ∑ i ∈ Finset.range c, F i

theorem psum_zero (F : ℕ → ℕ) : psum F 0 = 0 := rfl

theorem psum_succ (F : ℕ → ℕ) (c : ℕ) : psum F (c + 1) = psum F c + F c :=
  Finset.sum_range_succ F c

theorem psum_mono (F : ℕ → ℕ) : Monotone (psum F) := fun _ _ h =>
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- The band of `o` under the boundaries `F 0 ≤ F 1 ≤ ⋯ ≤ F N`: the number of `c < N` with
`F (c + 1) ≤ o`. -/
def bandIdx (F : ℕ → ℕ) (N o : ℕ) : ℕ := ((Finset.range N).filter (fun c => F (c + 1) ≤ o)).card

theorem bandIdx_eq {F : ℕ → ℕ} (hF : Monotone F) {N c o : ℕ} (hc : c < N) (h1 : F c ≤ o)
    (h2 : o < F (c + 1)) : bandIdx F N o = c := by
  unfold bandIdx
  have : (Finset.range N).filter (fun c' => F (c' + 1) ≤ o) = Finset.range c := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hle⟩
      by_contra hxc
      have := hF (show c + 1 ≤ x + 1 by omega)
      omega
    · intro hx
      exact ⟨by omega, le_trans (hF (show x + 1 ≤ c by omega)) h1⟩
  rw [this, Finset.card_range]

theorem bandIdx_spec {F : ℕ → ℕ} (hF : Monotone F) {N o : ℕ} (h0 : F 0 ≤ o) (hN : o < F N) :
    bandIdx F N o < N ∧ F (bandIdx F N o) ≤ o ∧ o < F (bandIdx F N o + 1) := by
  have hN0 : N ≠ 0 := by rintro rfl; omega
  have hex : ∃ c, o < F (c + 1) := ⟨N - 1, by rwa [Nat.sub_add_cancel (by omega)]⟩
  classical
  set c := Nat.find hex with hc
  have hspec : o < F (c + 1) := Nat.find_spec hex
  have hle : c ≤ N - 1 := Nat.find_min' hex (by rwa [Nat.sub_add_cancel (by omega)])
  have hlo : F c ≤ o := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h]; exact h0
    · have := Nat.find_min hex (show c - 1 < c by omega)
      rw [Nat.sub_add_cancel h] at this
      omega
  rw [bandIdx_eq hF (show c < N by omega) hlo hspec]
  exact ⟨by omega, hlo, hspec⟩

/-! ## Groups -/

/-- The first two homes have four chains; every other group has three. -/
def gk (u : ℕ) : ℕ := if u = 5 ∨ u = 6 then 4 else 3

/-- The index field width of group `u`. -/
def gb (u : ℕ) : ℕ := [10, 9, 9, 9, 9, 11, 11, 10, 10, 10, 10, 10, 10].getD u 0

/-- The bit position of group `u`'s field. -/
def POS (u : ℕ) : ℕ := posW gb u

/-- The exporter groups `1 … 4`. -/
def isExp (u : ℕ) : Prop := 1 ≤ u ∧ u < 5

instance (u : ℕ) : Decidable (isExp u) := by unfold isExp; infer_instance

/-- The uniform non-hash instruction count of a block of group `u` (entry and exit included). -/
def gcu (u : ℕ) : ℕ := if u = 0 then 5 else if isExp u then 8 else 6

/-- Root calls in a block: none for the exporters `1 … 4`, one for every home. Group `0` is the
home of call 1, groups `5, 6` the homes of calls `0, 7`, groups `7 … 11` those of `2 … 6` and
group `12` that of call `8`. -/
def hm (u : ℕ) : ℕ := if u = 0 ∨ 5 ≤ u then 1 else 0

/-- Layer profile of the exporters' (3, 9) tables: field values of each cost. -/
def P39 : List ℕ := [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 57]

/-- Layer profile of the (3, 10) tables (aliases counted; the last field value is a dummy). -/
def P310 : List ℕ := [1, 6, 48, 20, 15, 21, 28, 36, 44, 55, 66, 78, 91, 105, 120, 136, 153]

/-- Raw first-group profile: the doubled profile of its (3,9) table. -/
def P310no : List ℕ :=
  [2, 6, 12, 18, 30, 42, 54, 70, 90, 110, 130, 156, 182, 118, 4]

/-- Layer profile of the (4, 11) tables. -/
def P411 : List ℕ := [0, 4, 10, 20, 34, 55, 84, 120, 165, 219, 286, 363, 454, 229, 1, 0, 4]

/-- The layer profile of group `u`'s table: `pn u c` field values of cost `c`. -/
def prof (u : ℕ) : List ℕ :=
  if u = 0 then P310no else if u = 5 ∨ u = 6 then P411 else if u < 5 then P39 else P310

/-- Number of cost bands of group `u` (maximal cost plus one). -/
def nb (u : ℕ) : ℕ := (prof u).length

/-- Number of table tuples of cost `c` in group `u`. -/
def pn (u c : ℕ) : ℕ := (prof u).getD c 0

/-- Field values of cost below `c`: the band of cost `c` is `[A u c, A u (c + 1))`. -/
def A (u c : ℕ) : ℕ := psum (pn u) c

/-- Block length of cost `c` in group `u`. -/
def L (u c : ℕ) : ℕ := gcu u + c + hm u

/-- Slot offset of cost band `c` in group `u`'s region. -/
def OFF (u c : ℕ) : ℕ := psum (fun c => pn u c * L u c) c

/-- Size of group `u`'s region. -/
def RS (u : ℕ) : ℕ := OFF u (nb u)

/-- First slot of group `u`'s region (the prologue is slots `0 … 21`). -/
def BASE (u : ℕ) : ℕ := 22 + psum RS u

/-- End of the group regions. -/
def gEnd : ℕ := 234654

/-- Shift of the first group's `s = 0` region (frame 14) from its `s > 0` region: it starts at
`gEnd`. -/
def zOff : ℕ := 234632

/-- End of the first group's `s = 0` region. -/
def zEnd : ℕ := 250526

/-- The number of blocks (live field values) of group `u`: the (3,10) groups `7 … 12` omit their
dummy entry. -/
def VF (u : ℕ) : ℕ := if 7 ≤ u then 1023 else 2 ^ gb u

/-- The cost band of field value `v` of group `u`. -/
def band (u v : ℕ) : ℕ := bandIdx (A u) (nb u) v

/-- The entry slot of field value `v` of group `u`. -/
def entryOf (u v : ℕ) : ℕ :=
  BASE u + OFF u (band u v) + (v - A u (band u v)) * L u (band u v)

/-- First free-chain entry, `sentinel − 68 · 96`. -/
def baseF : ℕ := 255615

/-- The sentinel slot `2 ^ 18 - 1`. -/
def sentinel : ℕ := 262143

/-- The free-chain entry of digit `s` (block length `s + 5 ≤ 68`). -/
def entF (s : ℕ) : ℕ := baseF + 68 * s

theorem baseF_add : baseF + 68 * 96 = sentinel := rfl

theorem A_mono (u : ℕ) : Monotone (A u) := psum_mono _
theorem OFF_mono (u : ℕ) : Monotone (OFF u) := psum_mono _
theorem BASE_mono : Monotone BASE := fun _ _ h => Nat.add_le_add_left (psum_mono RS h) 22

theorem BASE_zero : BASE 0 = 22 := rfl

theorem BASE_succ (u : ℕ) : BASE (u + 1) = BASE u + RS u := by
  unfold BASE; rw [psum_succ]; ring

theorem BASE_13 : BASE 13 = gEnd := by decide

theorem BASE_one : BASE 1 = 15894 := by decide

theorem A_full : ∀ u < 13, A u (nb u) = VF u := by decide

theorem VF_le : ∀ u < 13, VF u ≤ 2 ^ gb u := by decide

theorem nb_le : ∀ u < 13, nb u ≤ 17 := by decide

theorem nb_pos : ∀ u < 13, 1 ≤ nb u := by decide

theorem L_pos (u c : ℕ) : 6 ≤ L u c := by unfold L gcu hm; split_ifs <;> omega

theorem OFF_succ (u c : ℕ) : OFF u (c + 1) = OFF u c + pn u c * L u c := psum_succ _ c

theorem A_succ (u c : ℕ) : A u (c + 1) = A u c + pn u c := psum_succ _ c

theorem gb_le : ∀ u < 13, gb u ≤ 11 := by decide

theorem POS_13 : POS 13 = 128 := by decide

theorem gk_le (u : ℕ) : gk u ≤ 4 := by unfold gk; split_ifs <;> omega

theorem gk_ge (u : ℕ) : 3 ≤ gk u := by unfold gk; split_ifs <;> omega

/-! ### Bands of field values -/

/-- The band of a field value and its position inside the band. -/
theorem band_spec {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    band u v < nb u ∧ A u (band u v) ≤ v ∧ v < A u (band u v + 1) := by
  have h := bandIdx_spec (A_mono u) (N := nb u) (o := v) (Nat.zero_le _)
    (by rw [A_full u hu]; exact hv)
  exact h

theorem band_lt_17 {u v : ℕ} (hu : u < 13) (hv : v < VF u) : band u v < 17 := by
  have := (band_spec hu hv).1; have := nb_le u hu; omega

/-- The block of field value `v` lies inside group `u`'s region. -/
theorem entry_region {u v i : ℕ} (hu : u < 13) (hv : v < VF u) (hi : i < L u (band u v)) :
    BASE u ≤ entryOf u v + i ∧ entryOf u v + i < BASE (u + 1) := by
  obtain ⟨hc, h1, h2⟩ := band_spec hu hv
  rw [BASE_succ]
  unfold entryOf RS
  set c := band u v
  have hq : v - A u c < pn u c := by rw [A_succ] at h2; omega
  have hoff : OFF u (c + 1) ≤ OFF u (nb u) := OFF_mono u (by omega)
  rw [OFF_succ] at hoff
  have hm : (v - A u c) * L u c + i < pn u c * L u c := by
    have : (v - A u c + 1) * L u c ≤ pn u c * L u c := Nat.mul_le_mul_right _ hq
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  omega

/-! ### The group decode -/

/-- Decode a group slot: the group, the field value and the offset in its block. -/
def dec (s : ℕ) : ℕ × ℕ × ℕ :=
  let u := bandIdx BASE 13 s
  let o := s - BASE u
  let c := bandIdx (OFF u) (nb u) o
  let q := o - OFF u c
  (u, A u c + q / L u c, q % L u c)

/-- Slots of a block decode to it. -/
theorem dec_entry {u v i : ℕ} (hu : u < 13) (hv : v < VF u) (hi : i < L u (band u v)) :
    dec (entryOf u v + i) = (u, v, i) := by
  obtain ⟨hr1, hr2⟩ := entry_region hu hv hi
  obtain ⟨hc, h1, h2⟩ := band_spec hu hv
  have hU : bandIdx BASE 13 (entryOf u v + i) = u := bandIdx_eq BASE_mono hu hr1 hr2
  set c := band u v with hcdef
  have hq : v - A u c < pn u c := by rw [A_succ] at h2; omega
  have hm : (v - A u c) * L u c + i < pn u c * L u c := by
    have : (v - A u c + 1) * L u c ≤ pn u c * L u c := Nat.mul_le_mul_right _ hq
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have ho : entryOf u v + i - BASE u = OFF u c + ((v - A u c) * L u c + i) := by
    unfold entryOf; rw [← hcdef]; omega
  have hC : bandIdx (OFF u) (nb u) (entryOf u v + i - BASE u) = c := by
    rw [ho]
    refine bandIdx_eq (OFF_mono u) hc (by omega) ?_
    rw [OFF_succ]; omega
  have hLp := L_pos u c
  unfold dec
  simp only
  rw [hU, hC, ho, Nat.add_sub_cancel_left]
  have hdiv : ((v - A u c) * L u c + i) / L u c = v - A u c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod : ((v - A u c) * L u c + i) % L u c = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  rw [hdiv, hmod]
  congr 2
  omega

/-- Every group slot is a slot of a block of a field value in range. -/
theorem dec_spec {s : ℕ} (h1 : 22 ≤ s) (h2 : s < gEnd) :
    (dec s).1 < 13 ∧ (dec s).2.1 < VF (dec s).1 ∧
      (dec s).2.2 < L (dec s).1 (band (dec s).1 (dec s).2.1) ∧
      s = entryOf (dec s).1 (dec s).2.1 + (dec s).2.2 := by
  obtain ⟨hu, hb1, hb2⟩ := bandIdx_spec BASE_mono (N := 13) (o := s) (by rw [BASE_zero]; exact h1)
    (by rw [BASE_13]; exact h2)
  set u := bandIdx BASE 13 s with hudef
  have hRS : s - BASE u < OFF u (nb u) := by
    have := BASE_succ u; unfold RS at this; omega
  obtain ⟨hc, hc1, hc2⟩ := bandIdx_spec (OFF_mono u) (N := nb u) (o := s - BASE u)
    (Nat.zero_le _) hRS
  set c := bandIdx (OFF u) (nb u) (s - BASE u) with hcdef
  set q := s - BASE u - OFF u c with hqdef
  have hLp := L_pos u c
  rw [OFF_succ] at hc2
  have hqlt : q < pn u c * L u c := by omega
  have hj : q / L u c < pn u c := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hqlt
  have hv1 : A u c ≤ A u c + q / L u c := Nat.le_add_right _ _
  have hv2 : A u c + q / L u c < A u (c + 1) := by rw [A_succ]; omega
  have hband : band u (A u c + q / L u c) = c := bandIdx_eq (A_mono u) hc hv1 hv2
  have hvlt : A u c + q / L u c < VF u := by
    have := A_mono u (show c + 1 ≤ nb u by omega)
    rw [A_full u hu] at this; omega
  have hd : dec s = (u, A u c + q / L u c, q % L u c) := rfl
  rw [hd]
  refine ⟨hu, hvlt, ?_, ?_⟩
  · simp only; rw [hband]; exact Nat.mod_lt _ (by omega)
  · simp only
    unfold entryOf
    rw [hband, Nat.add_sub_cancel_left]
    have := Nat.div_add_mod q (L u c)
    rw [mul_comm] at this
    omega

/-- Distinct field values have distinct entries. -/
theorem entryOf_inj {u v v' : ℕ} (hu : u < 13) (hv : v < VF u) (hv' : v' < VF u)
    (h : entryOf u v = entryOf u v') : v = v' := by
  have h1 := dec_entry hu hv (i := 0) (by have := L_pos u (band u v); omega)
  have h2 := dec_entry hu hv' (i := 0) (by have := L_pos u (band u v'); omega)
  rw [Nat.add_zero] at h1 h2
  rw [h] at h1
  rw [h1] at h2
  exact (Prod.mk.inj (Prod.mk.inj h2).2).1

theorem entryOf_ge {u v : ℕ} (hu : u < 13) (hv : v < VF u) : 22 ≤ entryOf u v := by
  have := (entry_region hu hv (i := 0) (by have := L_pos u (band u v); omega)).1
  have := BASE_mono (Nat.zero_le u); rw [BASE_zero] at this; omega

theorem block_lt_gEnd {u v i : ℕ} (hu : u < 13) (hv : v < VF u) (hi : i < L u (band u v)) :
    entryOf u v + i < gEnd := by
  have := (entry_region hu hv hi).2
  have := BASE_mono (show u + 1 ≤ 13 by omega); rw [BASE_13] at this; omega

/-! ## Chains -/

/-- Chain lengths (positions), from the tables' maximal coordinates. -/
def LENL : List ℕ := [64, 13, 13, 12, 13, 13, 13, 13, 12, 13, 13, 13, 13, 13, 17, 17, 17, 13, 13, 17, 17, 17, 13, 13, 17, 17, 17, 13, 13, 17, 17, 17, 13, 13, 17, 17, 17, 13, 13, 17, 17, 17]

/-- Positions of chain `k`. -/
def LEN (k : ℕ) : ℕ := LENL.getD k 0

/-- First tag position of chain `k`: steps are numbered consecutively over the chains. -/
def OFFT (k : ℕ) : ℕ := psum (fun j => LEN j - 1) k

/-- First scratch cell of chain `k`. -/
def xcBase (k : ℕ) : ℕ := 4096 + 2 * psum LEN k

theorem LEN_le : ∀ k < 42, LEN k ≤ 64 := by decide

theorem LEN_pos : ∀ k < 42, 2 ≤ LEN k := by decide

theorem OFFT_bound : ∀ k < 42, OFFT k + LEN k ≤ 656 := by decide

theorem xcBase_bound : ∀ k < 42, xcBase k + 2 * LEN k ≤ 5430 := by decide

theorem xcBase_mono : Monotone xcBase := fun _ _ h =>
  Nat.add_le_add_left (Nat.mul_le_mul_left 2 (psum_mono LEN h)) 4096

theorem xcBase_succ (k : ℕ) : xcBase (k + 1) = xcBase k + 2 * LEN k := by
  unfold xcBase; rw [psum_succ]; ring

theorem xcBase_42 : xcBase 42 = 5430 := by decide

theorem xcBase_zero : xcBase 0 = 4096 := rfl

/-- The explicit chain assignment: the home of call 1, four exporter groups, the homes of calls 0
and 7, the homes of calls 2 … 6, and the home of call 8. -/
def chainOf (u i : ℕ) : ℕ := ([[1, 2, 7], [12, 13, 17], [18, 22, 23], [27, 28, 32], [33, 37, 38], [3, 4, 5, 6], [8, 9, 10, 11], [14, 15, 16], [19, 20, 21], [24, 25, 26], [29, 30, 31], [34, 35, 36], [39, 40, 41]].getD u []).getD i 0

def unitOf (k : ℕ) : ℕ := [0, 0, 0, 5, 5, 5, 5, 0, 6, 6, 6, 6, 1, 1, 7, 7, 7, 1, 2, 8, 8, 8, 2, 2, 9, 9, 9, 3, 3, 10, 10, 10, 3, 4, 11, 11, 11, 4, 4, 12, 12, 12].getD k 0

def coordOf (k : ℕ) : ℕ := [0, 0, 1, 0, 1, 2, 3, 2, 0, 1, 2, 3, 0, 1, 0, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2].getD k 0

/-- Tops placed at fixed cells: the cv words of root calls `0` and `2 … 6`. -/
def exported (k : ℕ) : Prop := k ∈ [12, 13, 17, 18, 22, 23, 27, 28, 32, 33, 37, 38]

instance (k : ℕ) : Decidable (exported k) := by unfold exported; infer_instance

theorem chainOf_lt : ∀ u < 13, ∀ i < gk u, chainOf u i < 42 := by decide

theorem chainOf_pos : ∀ u < 13, ∀ i < gk u, 1 ≤ chainOf u i := by decide

theorem unitOf_chainOf : ∀ u < 13, ∀ i < gk u, unitOf (chainOf u i) = u := by decide

theorem coordOf_chainOf : ∀ u < 13, ∀ i < gk u, coordOf (chainOf u i) = i := by decide

theorem chainOf_unitOf : ∀ k < 42, 1 ≤ k →
    unitOf k < 13 ∧ coordOf k < gk (unitOf k) ∧ chainOf (unitOf k) (coordOf k) = k := by decide

theorem exported_iff : ∀ u < 13, ∀ i < gk u, (exported (chainOf u i) ↔ isExp u) := by decide

/-! ## Values -/

/-- The constant `1`. -/
def oneV : E := ofK 1

/-- The generator `g`. -/
def gV : E := ofK g

/-- The cost constant `C_c = g ^ (2^60 * c)`, also the tag symbol `c`. -/
def cV (c : ℕ) : E := ofK (gpow (1152921504606846976 * c))

/-- Upper bound on the fifteen frame exponents. -/
def eLen : ℕ := 17293822569102704640

/-- Frame f is cost factor C_(f+1). -/
def frameExp (f : ℕ) : ℕ := (f + 1) * 1152921504606846976

/-- The frame pointer of frame `f`. -/
def frame (f : ℕ) : K := gpow (frameExp f)

/-- The frame constant of frame `f`; `frameV r` is also the metadata of root call `r`. -/
def frameV (f : ℕ) : E := ofK (frame f)

/-- The tie pattern of field value `v` of group `u`. -/
def fpat (u v : ℕ) : E := natV (v * 2 ^ POS u)

theorem cV_zero : cV 0 = oneV := by unfold cV oneV; rw [Nat.mul_zero, gpow_zero']

theorem cV_sixteen : cV 16 = gV := by
  exact congrArg ofK LeanIsaFieldRescale.factor_sixteen

theorem frameV_eq_cV (f : ℕ) : frameV f = cV (f + 1) := by
  unfold frameV frame frameExp cV
  rw [Nat.mul_comm]

/-- Frame exponents are far apart and far from `0` modulo the order of `g`. -/
theorem frameExp_bounds {f : ℕ} (hf : f < 15) :
    2 ^ 33 ≤ frameExp f ∧ frameExp f ≤ eLen := by
  unfold frameExp eLen; omega

theorem frameExp_sep {f j : ℕ} (hf : f < 15) (hj : j < 15) (h : j < f) :
    frameExp j + 2 ^ 33 ≤ frameExp f := by
  unfold frameExp; omega

/-! ## The table and scheme interfaces -/

/-- A group table: coordinate `i` of the tuple of field value `v` of group `u`. -/
abbrev Tab := ℕ → ℕ → ℕ → ℕ

/-- The cost (coordinate sum) of the tuple of field value `v` of group `u`. -/
def cost (T : Tab) (u v : ℕ) : ℕ := ((List.range (gk u)).map (T u v)).sum

/-- What the machine needs of the tables: the cost of a live tuple is its cost band, and every
coordinate is below its chain's length. -/
structure Tab.Hyp (T : Tab) : Prop where
  cost_eq : ∀ u < 13, ∀ v < VF u, cost T u v = band u v
  coord_lt : ∀ u < 13, ∀ v < 2 ^ gb u, ∀ i < gk u, T u v i < LEN (chainOf u i)

/-- The free chain's digit: `88 − c` for group cost `c` when that is in `[0, 63]`, else `0`. -/
def freeDigit (c : ℕ) : ℕ := if c ≤ 88 ∧ 88 - c ≤ 63 then 88 - c else 0

/-- Group `u`'s field of the index. -/
def field (u : ℕ) (I : Word) : ℕ := digitW gb I.toNat u

/-- The total group cost of an index. -/
def gcost (T : Tab) (I : Word) : ℕ := ((List.range 13).map (fun u => cost T u (field u I))).sum

/-- The facts about the scheme parameters the machine relies on. -/
structure Compat (P : Params) (T : Tab) : Prop where
  len : ∀ k : Fin numChains, P.len k = LEN k.val
  layer : P.layer = 88
  digit_grp : ∀ (I : Word) (u i : ℕ) (hu : u < 13) (hi : i < gk u),
    P.digit (effective I) ⟨chainOf u i, chainOf_lt u hu i hi⟩ = T u (field u I) i
  digit_free : ∀ I : Word, (∀ u < 13, field u I < VF u) →
    P.digit (effective I) 0 = freeDigit (gcost T I)
  /-- Accepted indices have no dummy field. -/
  live : ∀ I : Word, P.Accepted (effective I) → ∀ u < 13, field u I < VF u
  tag : ∀ (k : Fin numChains) (j : ℕ), j + 1 < LEN k.val →
    P.tag k j 0 = cellBits (cV ((OFFT k.val + j) % 9)) ∧
      P.tag k j 1 = cellBits (cV ((OFFT k.val + j) / 9 % 9)) ∧
      P.tag k j 2 = cellBits (cV ((OFFT k.val + j) / 81))
  hiTop : ∀ k : Fin numChains, P.hiTop k = decide (k.val ∈ [1, 7, 12, 17, 22, 27, 32, 38, 39])
  cv : P.cv = cellBits gV ++ cellBits oneV
  chainMd : P.chainMd = cellBits oneV
  idxMd : P.idxMd = cellBits gV
  rootMd : ∀ r < 9, P.rootMd r = cellBits (frameV r)

end OptimalOTS.HLG3
