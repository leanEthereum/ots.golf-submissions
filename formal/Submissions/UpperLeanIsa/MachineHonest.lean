import Submissions.UpperLeanIsa.MachineProver
import Submissions.UpperLeanIsa.MachineCycles

/-!
# The honest direction of faithfulness

Design `NOTES.md` §7, §9.6. When the verifier accepts under a fixed table `f`, the
honest image `imageF f pk m bits` (loaded with the statement) satisfies the relation of every
slot on the walk selected by the digit vector `dig m`:

* `hv`: the honest cell values after loading, and the `hv_*` value lemmas;
* `VRel f v ci`: the relation of `ci` on the values `v` (no range conditions), and
  `holds_of_vrel`, which turns it into `Holds` on the loaded honest image;
* `honest_const`, `honest_dispatch`, `honest_c32`, `honest_leaf`, `honest_body`,
  `honest_leaf32`, `honest_root`, `honest_pk`, assembled into `holds_honest_path`
  (`PathFacts ∧ DispatchFacts` for `E := dig m`);
* `honest_run`: the honest run of `totalSteps (dig m)` steps completes with cost
  `totalCost (dig m)` (`walk_full_mk`, then `sim_of_walk`).
-/

namespace OptimalOTS.LeanIsaBaseline.Honest

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits eq_of_cellBits_eq blake2sQuery
  hashInput inputWord statementBits OracleCompressCells)
open OptimalOTS.LeanIsaBaseline.Machine

noncomputable section

/-! ## The loader -/

theorem inputCells_eq : LeanIsa.inputCells = 47 := rfl

theorem Lx_loadInput {κ : ℕ} (pk : PublicKey) (m : Message) (bits : List Bool) (L : MemImage κ)
    {c : ℕ} (h : c < 2 ^ κ) :
    Lx (LeanIsa.loadInput pk m bits L) c = if c < 47 then inputWord pk m bits c else Lx L c := by
  rw [Lx_of_lt _ h, Lx_of_lt _ h]
  show (if c < LeanIsa.inputCells then inputWord pk m bits c else L ⟨c, h⟩) = _
  rw [inputCells_eq]

theorem Lx_loadInput_pin {κ : ℕ} (hκ : 16 ≤ κ) (pk : PublicKey) (m : Message)
    (bits : List Bool) (L : MemImage κ) {c : ℕ} (hc : c < 47) :
    Lx (LeanIsa.loadInput pk m bits L) c = inputWord pk m bits c := by
  have h16 : (2 : ℕ) ^ 16 ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
  have h2 : c < 2 ^ κ := Nat.lt_of_lt_of_le hc (le_trans (by norm_num) h16)
  rw [Lx_loadInput pk m bits L h2, if_pos hc]

/-! ## Relations on cell values -/

/-- The relation the cell-level instruction `ci` asserts on the cell values `v` under the table
`f`: `CInstr.Rel` without the range conditions. The trap `.pad` never holds. -/
def VRel (f : HashTable) (v : ℕ → E) : CInstr → Prop
  | .xor a b c => v c = v a + v b
  | .mul a b c => v c = v a * v b
  | .setc a k => v a = k
  | .blake m0 m1 m2 m3 cv out md =>
      OracleCompressCells ![v m0, v m1, v m2, v m3] (v cv) (v (cv + 1)) (v out) (v (out + 1))
        (v md) (f ⟨896, blake2sQuery ![v m0, v m1, v m2, v m3] (v cv) (v (cv + 1)) (v md)⟩)
  | .jump a b c => IsInK (v a) ∧ IsInK (v b) ∧ IsInK (v c)
  | .pad => False

/-- A value relation of a bounded instruction on values that agree with the image below the
bound is the image relation. -/
theorem rel_of_vrel (f : HashTable) {κ : ℕ} (L : MemImage κ) {v : ℕ → E}
    (hv : ∀ c < 2 ^ κ, Lx L c = v c) {ci : CInstr} (hb : ci.Bounded (2 ^ κ))
    (h : VRel f v ci) : ci.Rel f L := by
  cases ci with
  | xor a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    refine ⟨ha, hb', hc, ?_⟩
    rw [hv a ha, hv b hb', hv c hc]
    exact h
  | mul a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    refine ⟨ha, hb', hc, ?_⟩
    rw [hv a ha, hv b hb', hv c hc]
    exact h
  | setc a k =>
    refine ⟨hb, ?_⟩
    rw [hv a hb]
    exact h
  | blake m0 m1 m2 m3 cv out md =>
    obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := hb
    refine ⟨⟨b0, b1, b2, b3, Nat.lt_of_succ_lt b4, b4, Nat.lt_of_succ_lt b5, b5, b6⟩, ?_⟩
    rw [hv m0 b0, hv m1 b1, hv m2 b2, hv m3 b3, hv cv (Nat.lt_of_succ_lt b4), hv (cv + 1) b4,
      hv out (Nat.lt_of_succ_lt b5), hv (out + 1) b5, hv md b6]
    exact h
  | jump a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    refine ⟨ha, hb', hc, ?_⟩
    rw [hv a ha, hv b hb', hv c hc]
    exact h
  | pad => exact absurd h id

/-! ## The honest values after loading -/

/-- The honest cell values after loading: the statement below 47, the honest image above. -/
def hv (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) (c : ℕ) : E :=
  if c < 47 then inputWord pk m bits c
  else cellVal m bits (chainTab f m bits) (rootTab f m bits) c

theorem Lx_honest (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) {c : ℕ}
    (hc : c < 65536) :
    Lx (LeanIsa.loadInput pk m bits (imageF f pk m bits)) c = hv f pk m bits c := by
  have hc' : c < 2 ^ 16 := lt_of_lt_of_eq hc (by norm_num)
  rw [Lx_loadInput pk m bits _ hc', Lx_of_lt _ hc']
  all_goals rfl

/-- Every relation holding on the honest values holds on the loaded honest image. -/
theorem holds_of_vrel (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) {s : ℕ}
    (h : VRel f (hv f pk m bits) (cinstrAt s)) :
    Holds f (LeanIsa.loadInput pk m bits (imageF f pk m bits)) s :=
  rel_of_vrel f _ (fun c hc => Lx_honest f pk m bits (lt_of_lt_of_eq hc (by norm_num)))
    (cinstrAt_bounded s) h

theorem isCanonical_oneV : IsCanonical128 oneV := by
  rw [oneV_eq_cellOfBits]
  exact isCanonical_cellOfBits 1

theorem canon4 {a b c d : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b)
    (hc : IsCanonical128 c) (hd : IsCanonical128 d) : ∀ k, IsCanonical128 (![a, b, c, d] k) := by
  intro k
  fin_cases k <;> first | exact ha | exact hb | exact hc | exact hd

theorem isInK_tgtV (t : ℕ) : IsInK (tgtV t) := (isInK_iff _).mpr ⟨_, rfl⟩

theorem isInK_zero : IsInK (0 : E) := ⟨limb_zero 1, limb_zero 2⟩

theorem isInK_ite (p : Prop) [Decidable p] : IsInK (if p then oneV else 0) := by
  split
  · exact isInK_oneV
  · exact isInK_zero

theorem ite_eq_zero_iff (p : Prop) [Decidable p] : (if p then oneV else 0) = 0 ↔ ¬ p := by
  split
  · exact ⟨fun h => absurd h oneV_ne_zero, fun h => absurd ‹p› h⟩
  · exact ⟨fun _ => ‹¬ p›, fun _ => rfl⟩

theorem oneV_mul (x : E) : oneV * x = x := by
  rw [oneV_eq_ofK, show ofK 1 = (1 : E) from map_one (algebraMap K E), one_mul]

/-! ## Honest tie and checksum values -/

theorem bytePos_lo {i : ℕ} (hi : i < 16) : bytePos i = 15 - i := by
  unfold bytePos; omega

theorem accV_head (m : Message) {k : ℕ} (h : k % 16 = 0) : accV m k = vV (bytePos k) (dig m k) := by
  unfold accV
  rw [show 16 * (k / 16) = k by omega, Finset.sum_Ico_succ_top (le_refl k), Finset.Ico_self,
    Finset.sum_empty, zero_add]

theorem accV_succ (m : Message) {k : ℕ} (h : k % 16 ≠ 0) :
    accV m k = accV m (k - 1) + vV (bytePos k) (dig m k) := by
  unfold accV
  rw [show (k - 1) / 16 = k / 16 by omega, show k - 1 + 1 = k by omega,
    Finset.sum_Ico_succ_top (by omega : 16 * (k / 16) ≤ k)]

/-- The full lower-half accumulator is message cell 2 (`pack_sum_of_bytes`). -/
theorem accV_15 (m : Message) : accV m 15 = cellOfBits (m.extractLsb' 128 128) := by
  unfold accV
  rw [show 16 * (15 / 16) = 0 by norm_num, ← Finset.range_eq_Ico, show 15 + 1 = 16 by norm_num]
  have hterm : ∀ i ∈ Finset.range 16, vV (bytePos i) (dig m i) =
      (fun p => cellOfBits (BitVec.ofNat 128
        (((m.extractLsb' 128 128).toNat / 256 ^ p % 256) <<< (8 * p)))) (16 - 1 - i) := by
    intro i hi
    have hi' : i < 16 := Finset.mem_range.mp hi
    have h1 : dig m i = (m.extractLsb' 128 128).toNat / 256 ^ (15 - i) % 256 :=
      (dig_fin m ⟨i, by omega⟩).trans (digit_cell2 m ⟨i, by omega⟩ hi')
    unfold vV
    rw [bytePos_lo hi', h1, show 16 - 1 - i = 15 - i by omega]
  rw [Finset.sum_congr rfl hterm]
  exact (Finset.sum_range_reflect (fun p => cellOfBits (BitVec.ofNat 128
    (((m.extractLsb' 128 128).toNat / 256 ^ p % 256) <<< (8 * p)))) 16).trans
    (pack_sum_of_bytes _)

/-- The full upper-half accumulator is message cell 1. -/
theorem accV_31 (m : Message) : accV m 31 = cellOfBits (m.extractLsb' 0 128) := by
  unfold accV
  rw [show 16 * (31 / 16) = 16 by norm_num, Finset.sum_Ico_eq_sum_range,
    show 31 + 1 - 16 = 16 by norm_num]
  have hterm : ∀ i ∈ Finset.range 16, vV (bytePos (16 + i)) (dig m (16 + i)) =
      (fun p => cellOfBits (BitVec.ofNat 128
        (((m.extractLsb' 0 128).toNat / 256 ^ p % 256) <<< (8 * p)))) (16 - 1 - i) := by
    intro i hi
    have hi' : i < 16 := Finset.mem_range.mp hi
    have h1 : dig m (16 + i) = (m.extractLsb' 0 128).toNat / 256 ^ (31 - (16 + i)) % 256 :=
      (dig_fin m ⟨16 + i, by omega⟩).trans (digit_cell1 m ⟨16 + i, by omega⟩
        (show 16 ≤ 16 + i by omega) (show 16 + i < 32 by omega))
    rw [show 31 - (16 + i) = 15 - i by omega] at h1
    have h2 : bytePos (16 + i) = 15 - i := by unfold bytePos; omega
    unfold vV
    rw [h2, h1, show 16 - 1 - i = 15 - i by omega]
  rw [Finset.sum_congr rfl hterm]
  exact (Finset.sum_range_reflect (fun p => cellOfBits (BitVec.ofNat 128
    (((m.extractLsb' 0 128).toNat / 256 ^ p % 256) <<< (8 * p)))) 16).trans
    (pack_sum_of_bytes _)

theorem dig_lt32 (m : Message) {i : ℕ} (hi : i < 32) :
    dig m i = m.toNat / 256 ^ (31 - i) % 256 :=
  (dig_fin m ⟨i, by omega⟩).trans (digit_of_lt m ⟨i, by omega⟩ hi)

theorem dig_32 (m : Message) : dig m 32 = Checksum.wotsChecksumValue 256 (messageDigits m) / 256 :=
  (dig_fin m ⟨32, by norm_num⟩).trans (digit_hi_checksum m ⟨32, by norm_num⟩ rfl)

theorem dig_33 (m : Message) : dig m 33 = Checksum.wotsChecksumValue 256 (messageDigits m) % 256 :=
  (dig_fin m ⟨33, by norm_num⟩).trans (digit_lo_checksum m ⟨33, by norm_num⟩ rfl)

/-- The honest digits satisfy the checksum identity `Σ_{k<32} d_k + 256 d_32 + d_33 = 8160`. -/
theorem honest_digit_sum (m : Message) :
    ∑ i ∈ Finset.range 32, dig m i + 256 * dig m 32 + dig m 33 = 8160 := by
  have hC : Checksum.wotsChecksumValue 256 (messageDigits m) =
      ∑ i ∈ Finset.range 32, (255 - dig m i) := by
    rw [checksum_eq_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [dig_lt32 m (Finset.mem_range.mp hi)])
  have hsum : ∑ i ∈ Finset.range 32, (255 - dig m i) + ∑ i ∈ Finset.range 32, dig m i = 8160 := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (dig_le m i)), Finset.sum_const,
      Finset.card_range, smul_eq_mul]
  have hdm := Nat.div_add_mod (Checksum.wotsChecksumValue 256 (messageDigits m)) 256
  rw [dig_32, dig_33]
  omega

theorem dig_32_lt (m : Message) : dig m 32 < 32 := by
  rw [dig_32]
  have := wotsChecksum_le m
  omega

theorem honest_valid (m : Message) : Valid (dig m) :=
  ⟨fun k _ => Nat.lt_succ_of_le (dig_le m k), dig_32_lt m⟩

/-- The honest checksum target: `K0 = gExp 32 + (s0 33 + d_33 + 1)`. -/
theorem honest_K0 (m : Message) : K0 = gExp m 32 + (s0 33 + dig m 33 + 1) := by
  have hs : ∑ i ∈ Finset.range 32, (s0 i + dig m i + 1) =
      ∑ i ∈ Finset.range 32, (s0 i + 1) + ∑ i ∈ Finset.range 32, dig m i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by omega)
  have hd := honest_digit_sum m
  unfold K0 gExp
  rw [if_neg (by norm_num), hs]
  omega

/-! ## Honest cell values -/

section Values

variable {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}

theorem hv_lt {c : ℕ} (h : c < 47) : hv f pk m bits c = inputWord pk m bits c := by
  unfold hv
  exact if_pos h

theorem hv_cell {c : ℕ} (h : 47 ≤ c) :
    hv f pk m bits c = cellVal m bits (chainTab f m bits) (rootTab f m bits) c := by
  unfold hv
  exact if_neg (by omega)

theorem hv_posPos {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 255) : hv f pk m bits (posCell j) = posV j := by
  rw [posCell_of_pos (by omega), hv_cell (by omega)]
  unfold cellVal
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem hv_zero (hlen : bits.length = 4352) {c : ℕ} (h1 : 38 ≤ c) (h2 : c < 47) :
    hv f pk m bits c = 0 := by
  rw [hv_lt h2]
  exact inputWord_of_ge_38 pk m bits hlen h1

theorem hv_z0 (hlen : bits.length = 4352) : hv f pk m bits zCell = 0 :=
  hv_zero hlen (by decide) (by decide)

theorem hv_z1 (hlen : bits.length = 4352) : hv f pk m bits (zCell + 1) = 0 :=
  hv_zero hlen (by decide) (by decide)

theorem posV_zero : posV 0 = 0 := Machine.cellOfBits_zero

theorem hv_pos (hlen : bits.length = 4352) {j : ℕ} (hj : j ≤ 255) :
    hv f pk m bits (posCell j) = posV j := by
  rcases Nat.eq_zero_or_pos j with rfl | h
  · rw [posCell_zero, hv_z0 hlen, posV_zero]
  · exact hv_posPos h hj

theorem hv_one : hv f pk m bits oneCell = oneV := by
  rw [← posCell_one, hv_posPos (le_refl 1) (by norm_num), posV_one]

theorem hv_k0 : hv f pk m bits k0Cell = tgtV K0 := by
  rw [hv_cell (by decide)]
  unfold cellVal k0Cell
  rw [if_neg (by norm_num), if_pos rfl]

theorem hv_len (hlen : bits.length = 4352) : hv f pk m bits lenCell = lenV := by
  rw [hv_lt (by decide)]
  show inputWord pk m bits 3 = lenV
  rw [inputWord_three]
  unfold lenV
  congr 2
  rw [hlen]
  unfold maxSignatureBits
  norm_num

theorem hv_sig (hlen : bits.length = 4352) {i : ℕ} (hi : i < 34) :
    hv f pk m bits (sigCell i) = cellOfBits (sigW bits i) := by
  rw [hv_lt (by unfold sigCell; omega)]
  exact inputWord_sig pk m bits hlen i

theorem hv_pk : hv f pk m bits pkCell = cellOfBits pk := by
  rw [hv_lt (by decide)]
  exact inputWord_zero pk m bits

theorem hv_scr {k o : ℕ} (hk : k < 34) (ho : o < 160) :
    hv f pk m bits (scr k + o) = scrVal m k o := by
  rw [hv_cell (by unfold scr; omega)]
  unfold cellVal scr
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (1024 + 160 * k + o - 1024) / 160 = k by omega,
    show (1024 + 160 * k + o - 1024) % 160 = o by omega]

theorem hv_zu {k i : ℕ} (hk : k < 34) (hk32 : k ≠ 32) (hi : i < 63) :
    hv f pk m bits (zuCell k i) = if i < dig m k / 4 then oneV else 0 := by
  unfold zuCell
  rw [hv_scr hk (by omega)]
  unfold scrVal
  rw [if_pos (by omega), if_neg hk32]

theorem hv_zu32 {i : ℕ} (hi : i < 31) :
    hv f pk m bits (zuCell 32 i) = if i < 31 - dig m 32 then oneV else 0 := by
  unfold zuCell
  rw [hv_scr (by norm_num) (by omega)]
  unfold scrVal
  rw [if_pos (by omega), if_pos rfl]

theorem hv_tu {k i : ℕ} (hk : k < 34) (hk32 : k ≠ 32) (hi : i < 63) :
    hv f pk m bits (tuCell k i) = tgtV (rBase k + 46 * (i + 1)) := by
  unfold tuCell
  rw [show scr k + 64 + i = scr k + (64 + i) by omega, hv_scr hk (by omega)]
  unfold scrVal
  rw [if_neg (by omega), if_pos (by omega), if_neg hk32, show 64 + i - 64 = i by omega]

theorem hv_tu32 {i : ℕ} (hi : i < 31) :
    hv f pk m bits (tuCell 32 i) = tgtV (rBase 32 + 7 * (i + 1)) := by
  unfold tuCell
  rw [show scr 32 + 64 + i = scr 32 + (64 + i) by omega, hv_scr (by norm_num) (by omega)]
  unfold scrVal
  rw [if_neg (by omega), if_pos (by omega), if_pos rfl, show 64 + i - 64 = i by omega]

theorem hv_zb0 {k : ℕ} (hk : k < 34) :
    hv f pk m bits (zbCell k 0) = if 2 ≤ dig m k % 4 then oneV else 0 := by
  unfold zbCell
  rw [show scr k + 128 + 0 = scr k + 128 by omega, hv_scr hk (by norm_num)]
  unfold scrVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem hv_zb1 {k : ℕ} (hk : k < 34) :
    hv f pk m bits (zbCell k 1) = if dig m k % 2 = 1 then oneV else 0 := by
  unfold zbCell
  rw [show scr k + 128 + 1 = scr k + 129 by omega, hv_scr hk (by norm_num)]
  unfold scrVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem hv_tb0 {k : ℕ} (hk : k < 34) :
    hv f pk m bits (tbCell k 0) = tgtV (gBase k (dig m k / 4) + 24) := by
  unfold tbCell
  rw [show scr k + 130 + 0 = scr k + 130 by omega, hv_scr hk (by norm_num)]
  unfold scrVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos rfl]

theorem hv_tb1 {k : ℕ} (hk : k < 34) :
    hv f pk m bits (tbCell k 1) =
      tgtV (gBase k (dig m k / 4) + 11 * (2 * (dig m k % 4 / 2) + 1) + 4) := by
  unfold tbCell
  rw [show scr k + 130 + 1 = scr k + 131 by omega, hv_scr hk (by norm_num)]
  unfold scrVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num), if_pos rfl]

theorem hv_t {k : ℕ} (hk : k < 34) : hv f pk m bits (tCell k) = tgtV (s0 k + dig m k + 1) := by
  unfold tCell
  rw [hv_scr hk (by norm_num)]
  unfold scrVal
  simp only [show ¬ (132 : ℕ) < 64 by norm_num, show ¬ (132 : ℕ) < 128 by norm_num,
    show ¬ (132 : ℕ) = 128 by norm_num, show ¬ (132 : ℕ) = 129 by norm_num,
    show ¬ (132 : ℕ) = 130 by norm_num, show ¬ (132 : ℕ) = 131 by norm_num, if_false, if_true]

theorem hv_v {k : ℕ} (hk : k < 34) : hv f pk m bits (vCell k) = tgtV (s0 k + 255) := by
  unfold vCell
  rw [hv_scr hk (by norm_num)]
  unfold scrVal
  simp only [show ¬ (133 : ℕ) < 64 by norm_num, show ¬ (133 : ℕ) < 128 by norm_num,
    show ¬ (133 : ℕ) = 128 by norm_num, show ¬ (133 : ℕ) = 129 by norm_num,
    show ¬ (133 : ℕ) = 130 by norm_num, show ¬ (133 : ℕ) = 131 by norm_num,
    show ¬ (133 : ℕ) = 132 by norm_num, if_false, if_true]

theorem hv_g {k : ℕ} (hk : k < 34) : hv f pk m bits (gCell k) = tgtV (gExp m k) := by
  unfold gCell
  rw [hv_scr hk (by norm_num)]
  unfold scrVal
  simp only [show ¬ (134 : ℕ) < 64 by norm_num, show ¬ (134 : ℕ) < 128 by norm_num,
    show ¬ (134 : ℕ) = 128 by norm_num, show ¬ (134 : ℕ) = 129 by norm_num,
    show ¬ (134 : ℕ) = 130 by norm_num, show ¬ (134 : ℕ) = 131 by norm_num,
    show ¬ (134 : ℕ) = 132 by norm_num, show ¬ (134 : ℕ) = 133 by norm_num, if_false, if_true]

theorem hv_f {k : ℕ} (hk : k < 34) :
    hv f pk m bits (fCell k) = vV (bytePos k) (dig m k) := by
  unfold fCell
  rw [hv_scr hk (by norm_num)]
  unfold scrVal
  simp only [show ¬ (135 : ℕ) < 64 by norm_num, show ¬ (135 : ℕ) < 128 by norm_num,
    show ¬ (135 : ℕ) = 128 by norm_num, show ¬ (135 : ℕ) = 129 by norm_num,
    show ¬ (135 : ℕ) = 130 by norm_num, show ¬ (135 : ℕ) = 131 by norm_num,
    show ¬ (135 : ℕ) = 132 by norm_num, show ¬ (135 : ℕ) = 133 by norm_num,
    show ¬ (135 : ℕ) = 134 by norm_num, if_false, if_true]

theorem hv_u : hv f pk m bits uCell = tgtV (256 * dig m 32) := by
  unfold uCell
  rw [hv_scr (by norm_num) (by norm_num)]
  unfold scrVal
  simp only [show ¬ (137 : ℕ) < 64 by norm_num, show ¬ (137 : ℕ) < 128 by norm_num,
    show ¬ (137 : ℕ) = 128 by norm_num, show ¬ (137 : ℕ) = 129 by norm_num,
    show ¬ (137 : ℕ) = 130 by norm_num, show ¬ (137 : ℕ) = 131 by norm_num,
    show ¬ (137 : ℕ) = 132 by norm_num, show ¬ (137 : ℕ) = 133 by norm_num,
    show ¬ (137 : ℕ) = 134 by norm_num, show ¬ (137 : ℕ) = 135 by norm_num,
    show ¬ (137 : ℕ) = 136 by norm_num, if_false]

theorem hv_acc {k : ℕ} (hk : k < 32) : hv f pk m bits (accCell k) = accV m k := by
  by_cases h15 : k = 15
  · subst h15
    rw [accCell_15, hv_lt (by norm_num), inputWord_two, accV_15]
  by_cases h31 : k = 31
  · subst h31
    rw [accCell_31, hv_lt (by norm_num), inputWord_one, accV_31]
  rw [accCell_of h15 h31, hv_scr (by omega) (by norm_num)]
  unfold scrVal
  simp only [show ¬ (136 : ℕ) < 64 by norm_num, show ¬ (136 : ℕ) < 128 by norm_num,
    show ¬ (136 : ℕ) = 128 by norm_num, show ¬ (136 : ℕ) = 129 by norm_num,
    show ¬ (136 : ℕ) = 130 by norm_num, show ¬ (136 : ℕ) = 131 by norm_num,
    show ¬ (136 : ℕ) = 132 by norm_num, show ¬ (136 : ℕ) = 133 by norm_num,
    show ¬ (136 : ℕ) = 134 by norm_num, show ¬ (136 : ℕ) = 135 by norm_num, if_false, if_true]

theorem hv_xv {k o : ℕ} (hk : k < 34) (ho : o < 512) :
    hv f pk m bits (8192 + 512 * k + o) = xVal m bits (chainTab f m bits) k o := by
  rw [hv_cell (by omega)]
  unfold cellVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), show (8192 + 512 * k + o - 8192) / 512 = k by omega,
    show (8192 + 512 * k + o - 8192) % 512 = o by omega]

theorem hv_x {k j : ℕ} (hk : k < 34) (hj : j ≤ 255) :
    hv f pk m bits (xCell k j) =
      cellOfBits (inW (dig m k) (sigW bits k) (tabN (chainTab f m bits) k) j) := by
  unfold xCell
  rw [hv_xv hk (by omega)]
  unfold xVal
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]

theorem hv_xh {k j : ℕ} (hk : k < 34) (hj : j < 255) :
    hv f pk m bits (xCell k (j + 1) + 1) = highE (tabN (chainTab f m bits) k) j := by
  unfold xCell
  rw [show 8192 + 512 * k + 2 * (j + 1) + 1 = 8192 + 512 * k + (2 * j + 3) by omega,
    hv_xv hk (by omega)]
  unfold xVal
  rw [if_neg (by omega), show (2 * j + 3) / 2 - 1 = j by omega]

theorem hv_rootv {o : ℕ} (h1 : 2 ≤ o) (h2 : o < 1192) :
    hv f pk m bits (7000 + o) = rootVal (rootTab f m bits) o := by
  rw [hv_cell (by omega)]
  unfold cellVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), Nat.add_sub_cancel_left]

theorem hv_stLo {t : ℕ} (ht : t < 34) :
    hv f pk m bits (rootStateCell (t + 1)) = lowE (rootTab f m bits) t := by
  rw [rootStateCell_of_pos (by omega), hv_rootv (by omega) (by omega)]
  unfold rootVal
  rw [if_pos (by omega), show 2 * (t + 1) / 2 - 1 = t by omega]

theorem hv_stHi {t : ℕ} (ht : t < 34) :
    hv f pk m bits (rootStateCell (t + 1) + 1) = highE (rootTab f m bits) t := by
  rw [rootStateCell_of_pos (by omega), Nat.add_assoc, hv_rootv (by omega) (by omega)]
  unfold rootVal
  rw [if_neg (by omega), show (2 * (t + 1) + 1) / 2 - 1 = t by omega]

theorem hv_st_canon (hlen : bits.length = 4352) {t : ℕ} (ht : t ≤ 34) :
    IsCanonical128 (hv f pk m bits (rootStateCell t)) ∧
      IsCanonical128 (hv f pk m bits (rootStateCell t + 1)) := by
  rcases Nat.eq_zero_or_pos t with rfl | h
  · rw [rootStateCell_zero, hv_z0 hlen, hv_z1 hlen]
    exact ⟨isCanonical_zero, isCanonical_zero⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [hv_stLo (by omega), hv_stHi (by omega)]
    exact ⟨isCanonical_cellOfBits _, isCanonical_cellOfBits _⟩

theorem hv_stPair (hlen : bits.length = 4352) {t : ℕ} (ht : t ≤ 34) :
    cellBits (hv f pk m bits (rootStateCell t + 1)) ++ cellBits (hv f pk m bits (rootStateCell t)) =
      stOf (rootTab f m bits) t := by
  rcases Nat.eq_zero_or_pos t with rfl | h
  · rw [rootStateCell_zero, hv_z0 hlen, hv_z1 hlen, cellBits_zero]
    exact zero_append_zero_128
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [hv_stLo (by omega), hv_stHi (by omega)]
    exact out_pair _ _ _ (cellBits_cellOfBits _) (cellBits_cellOfBits _)

end Values

/-! ## The honest relations -/

section Honest

variable {f : HashTable} {pk : PublicKey} {m : Message} {bits : List Bool}

/-- A chain step (the leaf's first hash at `j = d`, or a body step `j > d`): the hashed cell
holds `inW`, and the output pair is the honest answer. -/
theorem vrel_step (hlen : bits.length = 4352) {k j cin : ℕ} (hk : k < 34) (hj : j < 255)
    (hdj : dig m k ≤ j)
    (hin : hv f pk m bits cin =
      cellOfBits (inW (dig m k) (sigW bits k) (tabN (chainTab f m bits) k) j)) :
    VRel f (hv f pk m bits)
      (.blake cin (posCell k) (posCell j) zCell zCell (xCell k (j + 1)) oneCell) := by
  show OracleCompressCells
    ![hv f pk m bits cin, hv f pk m bits (posCell k), hv f pk m bits (posCell j),
      hv f pk m bits zCell]
    (hv f pk m bits zCell) (hv f pk m bits (zCell + 1)) (hv f pk m bits (xCell k (j + 1)))
    (hv f pk m bits (xCell k (j + 1) + 1)) (hv f pk m bits oneCell)
    (f ⟨896, blake2sQuery ![hv f pk m bits cin, hv f pk m bits (posCell k),
      hv f pk m bits (posCell j), hv f pk m bits zCell] (hv f pk m bits zCell)
      (hv f pk m bits (zCell + 1)) (hv f pk m bits oneCell)⟩)
  rw [hin, hv_pos hlen (by omega : k ≤ 255), hv_pos hlen (by omega : j ≤ 255), hv_z0 hlen,
    hv_z1 hlen, hv_x hk (by omega : j + 1 ≤ 255), hv_xh hk hj, hv_one,
    tabN_chainTab f m bits hk]
  have hq : blake2sQuery ![cellOfBits (inW (dig m k) (sigW bits k)
      (cutAns 255 (chainAnsF f k (dig m k) (sigW bits k))) j), posV k, posV j, 0] 0 0 oneV =
      chainInput k j (inW (dig m k) (sigW bits k)
        (cutAns 255 (chainAnsF f k (dig m k) (sigW bits k))) j) := by
    rw [blake2sQuery_chain k j _ (posV k) (posV j) 0 0 0 oneV (cellBits_cellOfBits _)
      (cellBits_cellOfBits _) cellBits_zero cellBits_zero cellBits_zero cellBits_oneV,
      cellBits_cellOfBits]
  have hx : inW (dig m k) (sigW bits k) (cutAns 255 (chainAnsF f k (dig m k) (sigW bits k)))
      (j + 1) = (cutAns 255 (chainAnsF f k (dig m k) (sigW bits k)) j).extractLsb' 0 128 := by
    unfold inW
    rw [if_neg (by omega)]
    rfl
  rw [hq, chain_answer f k (dig m k) (sigW bits k) hj, hx]
  exact ⟨canon4 (isCanonical_cellOfBits _) (isCanonical_cellOfBits _)
    (isCanonical_cellOfBits _) isCanonical_zero, isCanonical_zero, isCanonical_zero,
    isCanonical_cellOfBits _, isCanonical_cellOfBits _, isCanonical_oneV,
    cellBits_cellOfBits _, cellBits_cellOfBits _⟩

/-- The leaf's hashed cell is `σ`: `inW` at the digit itself. -/
theorem hin_sig (hlen : bits.length = 4352) {k : ℕ} (hk : k < 34) :
    hv f pk m bits (sigCell k) =
      cellOfBits (inW (dig m k) (sigW bits k) (tabN (chainTab f m bits) k) (dig m k)) := by
  rw [hv_sig hlen hk]
  unfold inW
  rw [if_pos (le_refl _)]

/-- The checksum product step of chain `k ∈ {0..31, 33}`. -/
theorem vrel_gmul {k : ℕ} (hk : k < 32 ∨ k = 33) :
    VRel f (hv f pk m bits) (.mul (gPrev k) (tCell k) (gOut k)) := by
  show hv f pk m bits (gOut k) = hv f pk m bits (gPrev k) * hv f pk m bits (tCell k)
  rw [hv_t (by omega)]
  rcases hk with hk | rfl
  · rw [gOut_of (by omega), hv_g (by omega)]
    rcases Nat.eq_zero_or_pos k with rfl | h0
    · rw [gPrev_zero, hv_one, oneV_mul]
      unfold gExp
      rw [if_pos (by norm_num), Finset.sum_range_one]
    · rw [gPrev_of (by omega) (by omega), hv_g (by omega), tgtV_mul]
      unfold gExp
      rw [if_pos hk, if_pos (by omega), show k - 1 + 1 = k by omega,
        show k + 1 = k + 1 from rfl, Finset.sum_range_succ]
  · rw [gOut_33, gPrev_33, hv_k0, hv_g (by norm_num), tgtV_mul, honest_K0]

theorem vrel_jump {a b : ℕ} (ha : IsInK (hv f pk m bits a)) (hb : IsInK (hv f pk m bits b)) :
    VRel f (hv f pk m bits) (.jump a b oneCell) := by
  refine ⟨ha, hb, ?_⟩
  rw [hv_one]
  exact isInK_oneV

/-- Every tie op of the leaf of chain `k < 32` at its digit. -/
theorem honest_tieOp (hlen : bits.length = 4352) {k i : ℕ} (hk : k < 32) (hi : i < tieLen k) :
    VRel f (hv f pk m bits) (leafOp k (dig m k) i) := by
  by_cases h0 : k % 16 = 0
  · rw [tieLen_of_zero hk h0] at hi
    obtain rfl : i = 0 := by omega
    rw [leafOp_tie0 hk h0]
    show hv f pk m bits (accCell k) = _
    rw [hv_acc hk, accV_head m h0]
  by_cases h15 : k % 16 = 15
  · rw [tieLen_of_15 hk h15] at hi
    obtain rfl : i = 0 := by omega
    rw [leafOp_tie15 hk h15]
    show hv f pk m bits (accCell k) = hv f pk m bits (accCell (k - 1)) +
      hv f pk m bits (posCell (dig m k))
    rw [hv_acc hk, hv_acc (by omega), hv_pos hlen (dig_le m k), accV_succ m h0,
      show bytePos k = 0 by unfold bytePos; omega, vV_zero]
  rw [tieLen_of_mid hk h0 h15] at hi
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · rw [leafOp_mid0 hk h0 h15]
    show hv f pk m bits (fCell k) = _
    rw [hv_f (by omega)]
  · rw [leafOp_mid1 hk h0 h15]
    show hv f pk m bits (accCell k) = hv f pk m bits (accCell (k - 1)) + hv f pk m bits (fCell k)
    rw [hv_acc hk, hv_acc (by omega), hv_f (by omega), accV_succ m h0]

/-- Every core op of the leaf of chain `k ∈ {0..31, 33}` at its digit. -/
theorem honest_coreOp (hlen : bits.length = 4352) {k i : ℕ} (hk : k < 32 ∨ k = 33)
    (hi : i < if dig m k < 255 then 4 else 5) :
    VRel f (hv f pk m bits) (coreOp k (dig m k) i) := by
  have hk34 : k < 34 := by omega
  by_cases he : dig m k < 255
  · rw [if_pos he] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [coreOp_blake he]
      exact vrel_step hlen hk34 he (le_refl _) (hin_sig hlen hk34)
    · rw [coreOp_mul he]
      exact vrel_gmul hk
    · rw [coreOp_set he]
      exact hv_t hk34
    · rw [coreOp_jmp he]
      exact vrel_jump (by rw [hv_one]; exact isInK_oneV) (by rw [hv_t hk34]; exact isInK_tgtV _)
  · have he' : dig m k = 255 := by have := dig_le m k; omega
    rw [if_neg he] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · rw [coreOp255_xor (by omega)]
      show hv f pk m bits (xCell k 255) = hv f pk m bits (sigCell k) + hv f pk m bits zCell
      rw [hv_x hk34 (le_refl _), hv_sig hlen hk34, hv_z0 hlen, add_zero]
      unfold inW
      rw [if_pos (by omega)]
    · rw [coreOp255_setT (by omega)]
      show hv f pk m bits (tCell k) = _
      rw [hv_t hk34, he']
    · rw [coreOp255_mul (by omega)]
      exact vrel_gmul hk
    · rw [coreOp255_setV (by omega)]
      exact hv_v hk34
    · rw [coreOp255_jmp (by omega)]
      exact vrel_jump (by rw [hv_one]; exact isInK_oneV) (by rw [hv_v hk34]; exact isInK_tgtV _)

theorem honest_leafOp (hlen : bits.length = 4352) {k i : ℕ} (hk : k < 32 ∨ k = 33)
    (hi : i < leafLen k (dig m k)) : VRel f (hv f pk m bits) (leafOp k (dig m k) i) := by
  by_cases hti : i < tieLen k
  · have hk32 : k < 32 := by
      rcases hk with hk | rfl
      · exact hk
      · rw [tieLen_of_ge (by norm_num)] at hti; omega
    exact honest_tieOp hlen hk32 hti
  · obtain ⟨i', rfl⟩ : ∃ i', i = tieLen k + i' := ⟨i - tieLen k, by omega⟩
    rw [leafOp_core]
    unfold leafLen at hi
    exact honest_coreOp hlen hk (by omega)

variable (f pk m bits)

/-- The loaded honest image. -/
local notation "LH" => LeanIsa.loadInput pk m bits (imageF f pk m bits)

theorem honest_const (hlen : bits.length = 4352) : ∀ s < 257, Holds f LH s := by
  intro s hs
  apply holds_of_vrel
  rcases Nat.lt_or_ge s 255 with h | h
  · rw [cinstrAt_const h]
    exact hv_posPos (by omega) (by omega)
  · rcases (show s = 255 ∨ s = 256 by omega) with rfl | rfl
    · rw [cinstrAt_k0]
      exact hv_k0
    · rw [cinstrAt_len]
      exact hv_len hlen

theorem honest_leaf (hlen : bits.length = 4352) :
    ∀ k, (k < 32 ∨ k = 33) → ∀ i < leafLen k (dig m k), Holds f LH (leafSlot k (dig m k) + i) := by
  intro k hk i hi
  apply holds_of_vrel
  rw [cinstrAt_leaf hk (Nat.lt_succ_of_le (dig_le m k)) (lt_of_lt_of_le hi (leafLen_le k _))]
  exact honest_leafOp hlen hk hi

theorem honest_leaf32 (hlen : bits.length = 4352) :
    ∀ i < 5, Holds f LH (leafSlot32 (dig m 32) + i) := by
  intro i hi
  apply holds_of_vrel
  rw [cinstrAt_leaf32 (dig_32_lt m) hi]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [leaf32Op_blake]
    exact vrel_step hlen (by norm_num) (by have := dig_32_lt m; omega) (le_refl _)
      (hin_sig hlen (by norm_num))
  · rw [leaf32Op_setU]
    exact hv_u
  · rw [leaf32Op_mul]
    show hv f pk m bits (gCell 32) = hv f pk m bits (gCell 31) * hv f pk m bits uCell
    rw [hv_g (by norm_num), hv_g (by norm_num), hv_u, tgtV_mul]
    unfold gExp
    rw [if_neg (by norm_num), if_pos (by norm_num)]
  · rw [leaf32Op_setT]
    exact hv_t (by norm_num)
  · rw [leaf32Op_jmp]
    exact vrel_jump (by rw [hv_one]; exact isInK_oneV)
      (by rw [hv_t (by norm_num)]; exact isInK_tgtV _)

theorem honest_body (hlen : bits.length = 4352) :
    ∀ k < 34, ∀ j, dig m k < j → j ≤ 254 → Holds f LH (s0 k + j) := by
  intro k hk j hj1 hj2
  apply holds_of_vrel
  rw [cinstrAt_body hk (by omega) hj2]
  exact vrel_step hlen hk (by omega) (by omega) (hv_x hk (by omega))

theorem honest_root (hlen : bits.length = 4352) : ∀ t < 34, Holds f LH (rootBase + t) := by
  intro t ht
  apply holds_of_vrel
  rw [cinstrAt_root ht]
  show OracleCompressCells
    ![hv f pk m bits (xCell t 255), hv f pk m bits zCell, hv f pk m bits zCell,
      hv f pk m bits zCell]
    (hv f pk m bits (rootStateCell t)) (hv f pk m bits (rootStateCell t + 1))
    (hv f pk m bits (rootStateCell (t + 1))) (hv f pk m bits (rootStateCell (t + 1) + 1))
    (hv f pk m bits (posCell (35 - t)))
    (f ⟨896, blake2sQuery ![hv f pk m bits (xCell t 255), hv f pk m bits zCell,
      hv f pk m bits zCell, hv f pk m bits zCell] (hv f pk m bits (rootStateCell t))
      (hv f pk m bits (rootStateCell t + 1)) (hv f pk m bits (posCell (35 - t)))⟩)
  have hz : cellBits (hv f pk m bits zCell) = 0 := by
    rw [hv_z0 hlen]
    exact cellBits_zero
  have hmd : cellBits (hv f pk m bits (posCell (35 - t))) = BitVec.ofNat 128 (2 + (33 - t)) := by
    rw [hv_pos hlen (by omega)]
    show cellBits (cellOfBits (BitVec.ofNat 128 (35 - t))) = _
    rw [cellBits_cellOfBits, show 35 - t = 2 + (33 - t) by omega]
  have hq := blake2sQuery_absorb (33 - t) (hv f pk m bits (xCell t 255)) (hv f pk m bits zCell)
    (hv f pk m bits zCell) (hv f pk m bits zCell) (hv f pk m bits (rootStateCell t))
    (hv f pk m bits (rootStateCell t + 1)) (hv f pk m bits (posCell (35 - t))) hz hz hz hmd
  have hend : cellBits (hv f pk m bits (xCell t 255)) = endsOf m bits (chainTab f m bits) t := by
    rw [hv_x (by omega) (le_refl _), cellBits_cellOfBits]
    unfold endsOf endW inW
    by_cases hd : dig m t ≤ 254
    · rw [if_neg (by omega), if_pos hd]
    · rw [if_pos (by have := dig_le m t; omega), if_neg hd]
  have hans : f ⟨896, hashInput (stOf (rootTab f m bits) t)
      ((endsOf m bits (chainTab f m bits) t).setWidth 512) (BitVec.ofNat 128 (2 + (33 - t)))⟩ =
      rootTab f m bits t :=
    root_answer f (endsOf m bits (chainTab f m bits)) ht
  have hcanon := hv_st_canon (f := f) (pk := pk) (m := m) hlen (show t ≤ 34 by omega)
  have hzc : IsCanonical128 (hv f pk m bits zCell) := by
    rw [hv_z0 hlen]
    exact isCanonical_zero
  have hmdc : IsCanonical128 (hv f pk m bits (posCell (35 - t))) := by
    rw [hv_pos hlen (by omega)]
    exact isCanonical_cellOfBits _
  have hxc : IsCanonical128 (hv f pk m bits (xCell t 255)) := by
    rw [hv_x (by omega) (le_refl _)]
    exact isCanonical_cellOfBits _
  rw [hq, hv_stPair hlen (show t ≤ 34 by omega), hend, hans, hv_stLo ht, hv_stHi ht]
  exact ⟨canon4 hxc hzc hzc hzc, hcanon.1, hcanon.2, isCanonical_cellOfBits _,
    isCanonical_cellOfBits _, hmdc, cellBits_cellOfBits _, cellBits_cellOfBits _⟩

theorem honest_pk (hlen : bits.length = 4352)
    (hpk : rootValue f (reconstructedWords f m bits) = pk) : Holds f LH pkSlot := by
  apply holds_of_vrel
  rw [cinstrAt_pk]
  show hv f pk m bits pkCell = hv f pk m bits (rootStateCell 34) + hv f pk m bits zCell
  have hr : (rootValueFold f (List.ofFn (reconstructedWords f m bits)) 0).extractLsb' 0 128 =
      pk := hpk
  rw [hv_pk, show rootStateCell 34 = rootStateCell (33 + 1) from rfl, hv_stLo (by norm_num),
    hv_z0 hlen, add_zero]
  show cellOfBits pk = cellOfBits ((rootTab f m bits 33).extractLsb' 0 128)
  rw [rootTab_33, hr]

/-- The honest Rice dispatch of chain `k` selects leaf `dig m k`. -/
theorem honest_dispatch :
    ∀ k, (k < 32 ∨ k = 33) → ChainDispatch (Holds f LH) LH k (dig m k) := by
  intro k hk
  have hk34 : k < 34 := by omega
  have hk32 : k ≠ 32 := by omega
  have hq : dig m k / 4 < 64 := by have := dig_le m k; omega
  refine ⟨fun i hi hix => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply holds_of_vrel
    rw [cinstrAt_uset hk hi]
    exact hv_tu hk34 hk32 hi
  · apply holds_of_vrel
    rw [cinstrAt_ujmp hk hi]
    exact vrel_jump (by rw [hv_zu hk34 hk32 hi]; exact isInK_ite _)
      (by rw [hv_tu hk34 hk32 hi]; exact isInK_tgtV _)
  · rw [Lx_honest f pk m bits (by unfold zuCell scr; omega), hv_zu hk34 hk32 hi, ite_eq_zero_iff]
    omega
  · apply holds_of_vrel
    rw [cinstrAt_g0set hk hq]
    exact hv_tb0 hk34
  · apply holds_of_vrel
    rw [cinstrAt_g0jmp hk hq]
    exact vrel_jump (by rw [hv_zb0 hk34]; exact isInK_ite _)
      (by rw [hv_tb0 hk34]; exact isInK_tgtV _)
  · rw [Lx_honest f pk m bits (by unfold zbCell scr; omega), hv_zb0 hk34, ite_eq_zero_iff]
    omega
  · apply holds_of_vrel
    rw [cinstrAt_g1set hk hq (by omega)]
    exact hv_tb1 hk34
  · apply holds_of_vrel
    rw [cinstrAt_g1jmp hk hq (by omega)]
    exact vrel_jump (by rw [hv_zb1 hk34]; exact isInK_ite _)
      (by rw [hv_tb1 hk34]; exact isInK_tgtV _)
  · rw [Lx_honest f pk m bits (by unfold zbCell scr; omega), hv_zb1 hk34, ite_eq_zero_iff]
    omega

/-- The honest unary dispatch of chain 32 selects leaf `dig m 32`. -/
theorem honest_c32 : C32Dispatch (Holds f LH) LH (dig m 32) := by
  intro i hi hix
  refine ⟨?_, ?_, ?_⟩
  · apply holds_of_vrel
    rw [cinstrAt_u32set hi]
    exact hv_tu32 hi
  · apply holds_of_vrel
    rw [cinstrAt_u32jmp hi]
    exact vrel_jump (by rw [hv_zu32 hi]; exact isInK_ite _)
      (by rw [hv_tu32 hi]; exact isInK_tgtV _)
  · rw [Lx_honest f pk m bits (by unfold zuCell scr; omega), hv_zu32 hi, ite_eq_zero_iff]
    omega

/-- **The honest path.** Under an accepting fixed table, every slot on the walk selected by the
digits `dig m` holds on the loaded honest image, and its hints select exactly those digits. -/
theorem holds_honest_path (hlen : bits.length = 4352)
    (hpk : rootValue f (reconstructedWords f m bits) = pk) :
    PathFacts (Holds f LH) (dig m) ∧ DispatchFacts (Holds f LH) LH (dig m) :=
  ⟨⟨honest_const f pk m bits hlen, honest_leaf f pk m bits hlen, honest_leaf32 f pk m bits hlen,
    honest_body f pk m bits hlen, honest_root f pk m bits hlen, honest_pk f pk m bits hlen hpk⟩,
    ⟨honest_dispatch f pk m bits, honest_c32 f pk m bits⟩⟩

/-- **Honest run.** When the verifier accepts under the fixed table `f`, the honest image drives
the run to the sentinel in exactly `totalSteps (dig m)` steps, at cost `totalCost (dig m)`. -/
theorem honest_run (hlen : bits.length = 4352)
    (hpk : rootValue f (reconstructedWords f m bits) = pk) :
    simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost program LH (totalSteps (dig m)) Regs.initial) =
      pure (some (totalCost (dig m))) := by
  have hone : Lx LH oneCell = oneV := by
    rw [Lx_honest f pk m bits (by decide), hv_one]
  obtain ⟨hP, hD⟩ := holds_honest_path f pk m bits hlen hpk
  rw [initial_eq]
  exact sim_of_walk (by decide) hone
    (walk_full_mk (fun _ h => holdsNH_of_holds h) hone (honest_valid m) hP hD)

end Honest


/-! ## The faithfulness clause -/

set_option linter.constructorNameAsVariable false in
/-- **Faithfulness clause**, for any submission whose verifier is the scheme's and whose honest run
under a fixed table is the run of the honest image for `totalSteps (dig m)` steps (`hrun`).
Accept direction: `honest_run`. Reject direction: `hfs`, fixed-table soundness of a completing
honest run (from `walk_of_sim`, `walk_full` and `accept_of_path`). -/
theorem faithful_clause (S : LeanIsa.Submission)
    (hver : ∀ pk m bits, S.scheme.verify pk m bits = verify pk m bits)
    (hrun : ∀ (f : HashTable) pk m bits,
      simulateQ (unifFwdAnswerImpl f) (S.honestRun pk m bits) =
        (fun o => o.isSome) <$> simulateQ (unifFwdAnswerImpl f)
          (LeanIsa.runCost program (LeanIsa.loadInput pk m bits (imageF f pk m bits))
            (totalSteps (dig m)) Regs.initial))
    (hfs : ∀ (f : HashTable) pk m bits c, some c ∈ support (simulateQ (unifFwdAnswerImpl f)
      (LeanIsa.runCost program (LeanIsa.loadInput pk m bits (imageF f pk m bits))
        (totalSteps (dig m)) Regs.initial)) →
      bits.length = 4352 ∧ rootValue f (reconstructedWords f m bits) = pk) :
    ∀ pk m bits, probTrue (do
      let completed ← S.honestRun pk m bits
      let accepted ← S.scheme.verify pk m bits
      pure (completed != accepted)) = 0 := by
  intro pk m bits
  apply probTrue_zero_of_fixed
  intro f
  have hs := hfs f pk m bits
  have hh := fun h1 h2 => honest_run f pk m bits h1 h2
  rw [simulateQ_bind, hrun f pk m bits, hver]
  generalize simulateQ (unifFwdAnswerImpl f) (LeanIsa.runCost program
    (LeanIsa.loadInput pk m bits (imageF f pk m bits)) (totalSteps (dig m)) Regs.initial) = X
    at hs hh ⊢
  simp only [simulateQ_bind, simulateQ_pure, fixed_verify, pure_bind]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨b, hb, hmem⟩ := hmem
  rw [mem_support_pure_iff] at hmem
  rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hb
  obtain ⟨o, ho, hb⟩ := hb
  rw [Function.comp_apply, mem_support_pure_iff] at hb
  subst hb
  by_cases hacc : bits.length = 4352 ∧ rootValue f (reconstructedWords f m bits) = pk
  · rw [hh hacc.1 hacc.2, mem_support_pure_iff] at ho
    subst ho
    rw [if_pos hacc.1, hacc.2] at hmem
    simp at hmem
  · cases o with
    | none =>
      have hverd : (if bits.length = 4352 then rootValue f (reconstructedWords f m bits) == pk
          else false) = false := by
        by_cases hl : bits.length = 4352
        · rw [if_pos hl]
          cases hbq : (rootValue f (reconstructedWords f m bits) == pk)
          · rfl
          · exact absurd ⟨hl, beq_iff_eq.mp hbq⟩ hacc
        · rw [if_neg hl]
      rw [hverd] at hmem
      simp at hmem
    | some c => exact hacc (hs c ho)

end

end OptimalOTS.LeanIsaBaseline.Honest
