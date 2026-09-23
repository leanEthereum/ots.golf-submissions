import Submissions.UpperLeanIsa.MachineSound
import Submissions.UpperLeanIsa.MachineRun
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Soundness and faithfulness of the leanISA machine

* `fixed_sound`: under a fixed table, every image whose `N` relations hold (`run_complete`)
  certifies a signature the verifier accepts (`accept_of_rel`).
* `holds_honest`: when the verifier accepts under a fixed table, the honest image satisfies all
  `N` relations, so the run of `N` steps completes (`run_of_holds`).
* `sound`, `faithful`: the two contract clauses, through `probTrue_zero_of_fixed`.
-/

namespace OptimalOTS.LeanIsaBaseline.Honest

open OracleComp LeanerVM.Parameters LeanerVM.Semantics
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits eq_of_cellBits_eq blake2sQuery
  hashInput inputWord statementBits OracleCompressCells)
open OptimalOTS.LeanIsaBaseline.Machine

noncomputable section

/-! ## Glue with `MachineRun` -/

theorem crel_of_rel (f : HashTable) {κ : ℕ} (L : MemImage κ) {ci : CInstr} (h : ci.Rel f L) :
    CRel f (Lx L) ci := by
  cases ci with
  | xor a b c =>
    obtain ⟨_, _, _, h'⟩ := h
    exact h'
  | mul a b c =>
    obtain ⟨_, _, _, h'⟩ := h
    exact h'
  | setc a k =>
    obtain ⟨_, h'⟩ := h
    exact h'
  | blake m0 m1 m2 m3 cv out md =>
    obtain ⟨_, h'⟩ := h
    exact h'
  | jump a b c =>
    obtain ⟨_, _, _, h'⟩ := h
    exact h'

theorem rel_of_crel (f : HashTable) {κ : ℕ} (L : MemImage κ) {ci : CInstr}
    (hb : ci.Bounded (2 ^ κ)) (h : CRel f (Lx L) ci) : ci.Rel f L := by
  cases ci with
  | xor a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    exact ⟨ha, hb', hc, h⟩
  | mul a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    exact ⟨ha, hb', hc, h⟩
  | setc a k => exact ⟨hb, h⟩
  | blake m0 m1 m2 m3 cv out md =>
    obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := hb
    exact ⟨⟨b0, b1, b2, b3, Nat.lt_of_succ_lt b4, b4, Nat.lt_of_succ_lt b5, b5, b6⟩, h⟩
  | jump a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    exact ⟨ha, hb', hc, h⟩

/-- A relation only reads the cells of its instruction. -/
theorem crel_congr (f : HashTable) {v w : ℕ → E} {B : ℕ} {ci : CInstr} (hb : ci.Bounded B)
    (hvw : ∀ c < B, v c = w c) (h : CRel f v ci) : CRel f w ci := by
  cases ci with
  | xor a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    show w c = w a + w b
    rw [← hvw a ha, ← hvw b hb', ← hvw c hc]
    exact h
  | mul a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    show w c = w a * w b
    rw [← hvw a ha, ← hvw b hb', ← hvw c hc]
    exact h
  | setc a k =>
    show w a = k
    rw [← hvw a hb]
    exact h
  | blake m0 m1 m2 m3 cv out md =>
    obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := hb
    show OracleCompressCells ![w m0, w m1, w m2, w m3] (w cv) (w (cv + 1)) (w out) (w (out + 1))
      (w md) (f ⟨896, blake2sQuery ![w m0, w m1, w m2, w m3] (w cv) (w (cv + 1)) (w md)⟩)
    rw [← hvw m0 b0, ← hvw m1 b1, ← hvw m2 b2, ← hvw m3 b3, ← hvw cv (Nat.lt_of_succ_lt b4),
      ← hvw (cv + 1) b4, ← hvw out (Nat.lt_of_succ_lt b5), ← hvw (out + 1) b5, ← hvw md b6]
    exact h
  | jump a b c =>
    obtain ⟨ha, hb', hc⟩ := hb
    show IsInK (w a) ∧ IsInK (w b) ∧ IsInK (w c)
    rw [← hvw a ha, ← hvw b hb', ← hvw c hc]
    exact h

/-! ## The loader -/

theorem inputCells_eq : LeanIsa.inputCells = 47 := by
  first
    | rfl
    | decide
    | norm_num [LeanIsa.inputCells, LeanIsa.signatureCells, maxSignatureBits]

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

/-! ## Fixed-table soundness -/

/-- **Fixed-table soundness.** If all `N` relations hold on the loaded image under the table
`f`, the verifier accepts under `f`. -/
theorem fixed_sound {κ : ℕ} (hκ : 16 ≤ κ) (f : HashTable) (pk : PublicKey) (m : Message)
    (bits : List Bool) (L : MemImage κ)
    (h : ∀ k < N, Holds f (LeanIsa.loadInput pk m bits L) k) :
    bits.length = 4352 ∧ rootValue f (reconstructedWords f m bits) = pk :=
  accept_of_rel f pk m bits (Lx (LeanIsa.loadInput pk m bits L))
    (fun _ hc => Lx_loadInput_pin hκ pk m bits L hc) (fun k hk => crel_of_rel f _ (h k hk))

/-! ## The honest values after loading -/

/-- The honest cell values after loading: the statement below 47, the honest image above. -/
def hv (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) (c : ℕ) : E :=
  if c < 47 then inputWord pk m bits c
  else cellVal m bits (chainTab f m bits) (rootTab f m bits) c

theorem Lx_honest (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool) {c : ℕ}
    (hc : c < 2 ^ 17) :
    Lx (LeanIsa.loadInput pk m bits (imageF f pk m bits)) c = hv f pk m bits c := by
  rw [Lx_loadInput pk m bits _ hc, Lx_of_lt _ hc]
  all_goals rfl

theorem isCanonical_oneV : IsCanonical128 oneV := by
  rw [oneV_eq_cellOfBits]
  exact isCanonical_cellOfBits 1

theorem canon4 {a b c d : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b)
    (hc : IsCanonical128 c) (hd : IsCanonical128 d) : ∀ k, IsCanonical128 (![a, b, c, d] k) := by
  intro k
  fin_cases k <;> first | exact ha | exact hb | exact hc | exact hd

theorem bytePos_lt (i : ℕ) : bytePos i < 16 := by
  unfold bytePos
  split <;> omega

section Decode

variable (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

theorem hv_lt {c : ℕ} (h : c < 47) : hv f pk m bits c = inputWord pk m bits c := by
  unfold hv
  exact if_pos h

theorem hv_ge {c : ℕ} (h : 47 ≤ c) :
    hv f pk m bits c = cellVal m bits (chainTab f m bits) (rootTab f m bits) c := by
  unfold hv
  exact if_neg (by omega)

theorem hv_const {c : ℕ} (h1 : 47 ≤ c) (h2 : c < 8192) : hv f pk m bits c = hConst c := by
  rw [hv_ge f pk m bits h1]
  unfold cellVal
  rw [if_pos h2]

/-! ### Segment A cells -/

theorem hv_z0 : hv f pk m bits zCell = 0 := by
  rw [hv_const f pk m bits (by decide) (by decide)]
  first | rfl | (unfold hConst; norm_num)

theorem hv_z1 : hv f pk m bits (zCell + 1) = 0 := by
  rw [hv_const f pk m bits (by decide) (by decide)]
  first | rfl | (unfold hConst; norm_num)

theorem hv_one : hv f pk m bits oneCell = oneV := by
  rw [hv_const f pk m bits (by decide) (by decide)]
  first | rfl | (unfold hConst; norm_num)

theorem hv_fpc : hv f pk m bits fpcCell = fpcV := by
  rw [hv_const f pk m bits (by decide) (by decide)]
  first | rfl | (unfold hConst; norm_num)

theorem hv_ubHi : hv f pk m bits ubHiCell = ubHiV := by
  rw [hv_const f pk m bits (by decide) (by decide)]
  first | rfl | (unfold hConst; norm_num)

theorem hv_ubLo : hv f pk m bits ubLoCell = ubLoV := by
  rw [hv_const f pk m bits (by decide) (by decide)]
  first | rfl | (unfold hConst; norm_num)

theorem hv_chainId {i : ℕ} (hi : i < 34) :
    hv f pk m bits (chainIdCell i) = chainIdV i := by
  show hv f pk m bits (64 + i) = chainIdV i
  rw [hv_const f pk m bits (c := 64 + i) (by omega) (by omega)]
  unfold hConst
  have e0 : 64 + i - 64 = i := by omega
  rw [if_neg (show ¬ (64 + i = 3) by omega),
    if_neg (show ¬ (64 + i = 50) by omega),
    if_neg (show ¬ (64 + i = 51) by omega),
    if_pos (show 64 ≤ 64 + i ∧ 64 + i < 98 from ⟨by omega, by omega⟩),
    e0]

theorem hv_rootMd {r : ℕ} (hr : r < 34) :
    hv f pk m bits (rootMdCell r) = rootMdV r := by
  show hv f pk m bits (100 + r) = rootMdV r
  rw [hv_const f pk m bits (c := 100 + r) (by omega) (by omega)]
  unfold hConst
  have e0 : 100 + r - 100 = r := by omega
  rw [if_neg (show ¬ (100 + r = 3) by omega),
    if_neg (show ¬ (100 + r = 50) by omega),
    if_neg (show ¬ (100 + r = 51) by omega),
    if_neg (show ¬ (64 ≤ 100 + r ∧ 100 + r < 98) from fun h => absurd h.2 (by omega)),
    if_pos (show 100 ≤ 100 + r ∧ 100 + r < 134 from ⟨by omega, by omega⟩),
    e0]

theorem hv_pos {j : ℕ} (hj : j < 255) :
    hv f pk m bits (posCell j) = posV j := by
  show hv f pk m bits (256 + j) = posV j
  rw [hv_const f pk m bits (c := 256 + j) (by omega) (by omega)]
  unfold hConst
  have e0 : 256 + j - 256 = j := by omega
  rw [if_neg (show ¬ (256 + j = 3) by omega),
    if_neg (show ¬ (256 + j = 50) by omega),
    if_neg (show ¬ (256 + j = 51) by omega),
    if_neg (show ¬ (64 ≤ 256 + j ∧ 256 + j < 98) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (100 ≤ 256 + j ∧ 256 + j < 134) from fun h => absurd h.2 (by omega)),
    if_pos (show 256 ≤ 256 + j ∧ 256 + j < 511 from ⟨by omega, by omega⟩),
    e0]

theorem hv_wvCell {p j : ℕ} (hp : p < 16) (hj : j < 255) :
    hv f pk m bits (wvCell p j) = wvV p j := by
  show hv f pk m bits (1024 + 256 * p + j) = wvV p j
  rw [hv_const f pk m bits (c := 1024 + 256 * p + j) (by omega) (by omega)]
  unfold hConst
  have e0 : (1024 + 256 * p + j - 1024) / 256 = p := by omega
  have e1 : (1024 + 256 * p + j - 1024) % 256 = j := by omega
  rw [if_neg (show ¬ (1024 + 256 * p + j = 3) by omega),
    if_neg (show ¬ (1024 + 256 * p + j = 50) by omega),
    if_neg (show ¬ (1024 + 256 * p + j = 51) by omega),
    if_neg (show ¬ (64 ≤ 1024 + 256 * p + j ∧ 1024 + 256 * p + j < 98)
      from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (100 ≤ 1024 + 256 * p + j ∧ 1024 + 256 * p + j < 134)
      from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (256 ≤ 1024 + 256 * p + j ∧ 1024 + 256 * p + j < 511)
      from fun h => absurd h.2 (by omega)),
    if_pos (show 1024 ≤ 1024 + 256 * p + j ∧ 1024 + 256 * p + j < 5120 from ⟨by omega, by omega⟩),
    e0,
    e1]

theorem hv_wu {j : ℕ} (hj : j < 255) :
    hv f pk m bits (wuCell j) = wuV j := by
  show hv f pk m bits (5120 + j) = wuV j
  rw [hv_const f pk m bits (c := 5120 + j) (by omega) (by omega)]
  unfold hConst
  have e0 : 5120 + j - 5120 = j := by omega
  rw [if_neg (show ¬ (5120 + j = 3) by omega),
    if_neg (show ¬ (5120 + j = 50) by omega),
    if_neg (show ¬ (5120 + j = 51) by omega),
    if_neg (show ¬ (64 ≤ 5120 + j ∧ 5120 + j < 98) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (100 ≤ 5120 + j ∧ 5120 + j < 134) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (256 ≤ 5120 + j ∧ 5120 + j < 511) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (1024 ≤ 5120 + j ∧ 5120 + j < 5120) from fun h => absurd h.2 (by omega)),
    if_pos (show 5120 ≤ 5120 + j ∧ 5120 + j < 5375 from ⟨by omega, by omega⟩),
    e0]

theorem hv_wuHi {j : ℕ} (hj : j < 255) :
    hv f pk m bits (wuHiCell j) = wuHiV j := by
  show hv f pk m bits (5376 + j) = wuHiV j
  rw [hv_const f pk m bits (c := 5376 + j) (by omega) (by omega)]
  unfold hConst
  have e0 : 5376 + j - 5376 = j := by omega
  rw [if_neg (show ¬ (5376 + j = 3) by omega),
    if_neg (show ¬ (5376 + j = 50) by omega),
    if_neg (show ¬ (5376 + j = 51) by omega),
    if_neg (show ¬ (64 ≤ 5376 + j ∧ 5376 + j < 98) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (100 ≤ 5376 + j ∧ 5376 + j < 134) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (256 ≤ 5376 + j ∧ 5376 + j < 511) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (1024 ≤ 5376 + j ∧ 5376 + j < 5120) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (5120 ≤ 5376 + j ∧ 5376 + j < 5375) from fun h => absurd h.2 (by omega)),
    if_pos (show 5376 ≤ 5376 + j ∧ 5376 + j < 5631 from ⟨by omega, by omega⟩),
    e0]

theorem hv_wuLo {j : ℕ} (hj : j < 255) :
    hv f pk m bits (wuLoCell j) = wuLoV j := by
  show hv f pk m bits (5632 + j) = wuLoV j
  rw [hv_const f pk m bits (c := 5632 + j) (by omega) (by omega)]
  unfold hConst
  have e0 : 5632 + j - 5632 = j := by omega
  rw [if_neg (show ¬ (5632 + j = 3) by omega),
    if_neg (show ¬ (5632 + j = 50) by omega),
    if_neg (show ¬ (5632 + j = 51) by omega),
    if_neg (show ¬ (64 ≤ 5632 + j ∧ 5632 + j < 98) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (100 ≤ 5632 + j ∧ 5632 + j < 134) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (256 ≤ 5632 + j ∧ 5632 + j < 511) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (1024 ≤ 5632 + j ∧ 5632 + j < 5120) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (5120 ≤ 5632 + j ∧ 5632 + j < 5375) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (5376 ≤ 5632 + j ∧ 5632 + j < 5631) from fun h => absurd h.2 (by omega)),
    if_pos (show 5632 ≤ 5632 + j ∧ 5632 + j < 5887 from ⟨by omega, by omega⟩),
    e0]

theorem hv_vb {p : ℕ} (hp : p < 16) :
    hv f pk m bits (vbCell p) = vbV p := by
  show hv f pk m bits (5890 + p) = vbV p
  rw [hv_const f pk m bits (c := 5890 + p) (by omega) (by omega)]
  unfold hConst
  have e0 : 5890 + p - 5890 = p := by omega
  rw [if_neg (show ¬ (5890 + p = 3) by omega),
    if_neg (show ¬ (5890 + p = 50) by omega),
    if_neg (show ¬ (5890 + p = 51) by omega),
    if_neg (show ¬ (64 ≤ 5890 + p ∧ 5890 + p < 98) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (100 ≤ 5890 + p ∧ 5890 + p < 134) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (256 ≤ 5890 + p ∧ 5890 + p < 511) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (1024 ≤ 5890 + p ∧ 5890 + p < 5120) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (5120 ≤ 5890 + p ∧ 5890 + p < 5375) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (5376 ≤ 5890 + p ∧ 5890 + p < 5631) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (5632 ≤ 5890 + p ∧ 5890 + p < 5887) from fun h => absurd h.2 (by omega)),
    if_neg (show ¬ (5890 + p = 5888) by omega),
    if_neg (show ¬ (5890 + p = 5889) by omega),
    if_pos (show 5890 ≤ 5890 + p ∧ 5890 + p < 5906 from ⟨by omega, by omega⟩),
    e0]

/-! ### The pinned cells -/

theorem hv_pk : hv f pk m bits pkCell = cellOfBits pk := by
  rw [hv_lt f pk m bits (by decide)]
  exact inputWord_zero pk m bits

theorem hv_msg0 : hv f pk m bits 1 = cellOfBits (m.extractLsb' 0 128) := by
  rw [hv_lt f pk m bits (by norm_num)]
  exact inputWord_one pk m bits

theorem hv_msg1 : hv f pk m bits 2 = cellOfBits (m.extractLsb' 128 128) := by
  rw [hv_lt f pk m bits (by norm_num)]
  exact inputWord_two pk m bits

theorem hv_len (hlen : bits.length = 4352) : hv f pk m bits lenCell = lenV := by
  rw [hv_lt f pk m bits (by decide)]
  show inputWord pk m bits 3 = lenV
  have e : min 4352 (maxSignatureBits + 1) = 4352 := by
    unfold maxSignatureBits
    omega
  rw [inputWord_three, hlen, e]
  all_goals rfl

theorem hv_sig (hlen : bits.length = 4352) {i : ℕ} (hi : i < 34) :
    hv f pk m bits (sigCell i) = cellOfBits (sigW bits i) := by
  rw [hv_lt f pk m bits (show sigCell i < 47 by unfold sigCell; omega)]
  exact inputWord_sig pk m bits hlen i

/-! ### Segment B cells -/

theorem hv_off {i o : ℕ} (hi : i < 34) (ho : o < 2560) :
    hv f pk m bits (chainBase i + o) =
      chainOffVal (dig m i) (sigW bits i) (tabN (chainTab f m bits) i) i o := by
  have e1 : ¬ chainBase i + o < 8192 := by unfold chainBase; omega
  have e2 : chainBase i + o < 95232 := by unfold chainBase; omega
  have e3 : (chainBase i + o - 8192) / 2560 = i := by unfold chainBase; omega
  have e4 : (chainBase i + o - 8192) % 2560 = o := by unfold chainBase; omega
  rw [hv_ge f pk m bits (by unfold chainBase; omega)]
  unfold cellVal chainCellVal
  rw [if_neg e1, if_pos e2, e3, e4]

theorem hv_step {i j r : ℕ} (hi : i < 34) (hj : j < 255) (hr : r < 10) :
    hv f pk m bits (stepCell i j r) =
      stepVal (dig m i) (sigW bits i) (tabN (chainTab f m bits) i) i j r := by
  have e : stepCell i j r = chainBase i + (10 * j + r) := by
    unfold stepCell
    omega
  rw [e, hv_off f pk m bits hi (by omega)]
  unfold chainOffVal
  rw [if_pos (show 10 * j + r < 2550 by omega), show (10 * j + r) / 10 = j by omega,
    show (10 * j + r) % 10 = r by omega]

theorem hv_t {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (tCell i j) = thermo (dig m i) j :=
  hv_step f pk m bits hi hj (r := 0) (by norm_num)

theorem hv_s {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (sCell i j) =
      xE (sigW bits i) (tabN (chainTab f m bits) i) j + cellOfBits (sigW bits i) :=
  hv_step f pk m bits hi hj (r := 1) (by norm_num)

theorem hv_u {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (uCell i j) = thermoPrev (dig m i) j *
      (xE (sigW bits i) (tabN (chainTab f m bits) i) j + cellOfBits (sigW bits i)) :=
  hv_step f pk m bits hi hj (r := 2) (by norm_num)

theorem hv_in {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (inCell i j) = cellOfBits (sigW bits i) + thermoPrev (dig m i) j *
      (xE (sigW bits i) (tabN (chainTab f m bits) i) j + cellOfBits (sigW bits i)) :=
  hv_step f pk m bits hi hj (r := 3) (by norm_num)

theorem hv_inW {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (inCell i j) =
      cellOfBits (inW (dig m i) (sigW bits i) (tabN (chainTab f m bits) i) j) :=
  (hv_in f pk m bits hi hj).trans (inE_eq _ _ _ _)

theorem hv_pV {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (pVCell i j) = prodE (dig m i) (avW i) j :=
  hv_step f pk m bits hi hj (r := 6) (by norm_num)

theorem hv_pU {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (pUCell i j) = prodE (dig m i) (auW i) j :=
  hv_step f pk m bits hi hj (r := 8) (by norm_num)

theorem hv_x (hlen : bits.length = 4352) {i j : ℕ} (hi : i < 34) (hj : j ≤ 255) :
    hv f pk m bits (xCell i j) = xE (sigW bits i) (tabN (chainTab f m bits) i) j := by
  cases j with
  | zero =>
    rw [xCell_zero]
    exact hv_sig f pk m bits hlen hi
  | succ j =>
    rw [xCell_succ]
    exact hv_step f pk m bits hi (by omega) (r := 4) (by norm_num)

theorem hv_x1 {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (xCell i (j + 1) + 1) = highE (tabN (chainTab f m bits) i) j := by
  rw [xCell_succ_add_one]
  exact hv_step f pk m bits hi hj (r := 5) (by norm_num)

theorem hv_tPrev {i j : ℕ} (hi : i < 34) (hj : j < 255) :
    hv f pk m bits (tPrevCell i j) = thermoPrev (dig m i) j := by
  cases j with
  | zero => rw [tPrevCell_zero, hv_z0 f pk m bits, thermoPrev_zero]
  | succ j => rw [tPrevCell_succ, hv_t f pk m bits hi (by omega), thermoPrev_succ]

theorem hv_aV {i j : ℕ} (hi : i < 34) (hj : j ≤ 255) :
    hv f pk m bits (aVCell i j) = accE (dig m i) (avBase i) (avW i) j := by
  cases j with
  | zero =>
    rw [aVCell_zero, hv_vb f pk m bits (bytePos_lt i)]
    all_goals rfl
  | succ j =>
    rw [aVCell_succ]
    exact hv_step f pk m bits hi (by omega) (r := 7) (by norm_num)

theorem hv_aU {i j : ℕ} (hi : i < 34) (hj : j ≤ 255) :
    hv f pk m bits (aUCell i j) = accE (dig m i) (auBase i) (auW i) j := by
  cases j with
  | zero =>
    rw [aUCell_zero]
    show hv f pk m bits (aUBaseCell i) = auBase i
    unfold aUBaseCell auBase
    by_cases h1 : i < 32
    · rw [if_pos h1, if_pos h1]
      exact hv_one f pk m bits
    · by_cases h2 : i = 32
      · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
        exact hv_ubHi f pk m bits
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
        exact hv_ubLo f pk m bits
  | succ j =>
    rw [aUCell_succ]
    exact hv_step f pk m bits hi (by omega) (r := 9) (by norm_num)

theorem hv_wvSel (i : ℕ) {j : ℕ} (hj : j < 255) :
    hv f pk m bits (wvCell (bytePos i) j) = avW i j :=
  hv_wvCell f pk m bits (bytePos_lt i) hj

theorem hv_wuSel (i : ℕ) {j : ℕ} (hj : j < 255) : hv f pk m bits (wuSelCell i j) = auW i j := by
  unfold wuSelCell auW
  by_cases h1 : i < 32
  · rw [if_pos h1, if_pos h1]
    exact hv_wu f pk m bits hj
  · by_cases h2 : i = 32
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
      exact hv_wuHi f pk m bits hj
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      exact hv_wuLo f pk m bits hj

theorem hv_d {i : ℕ} (hi : i < 34) : hv f pk m bits (dCell i) = dVal m i :=
  hv_step f pk m bits hi (by norm_num : 254 < 255) (r := 7) (by norm_num)

theorem hv_p {i : ℕ} (hi : i < 34) : hv f pk m bits (pCell i) = pVal m i :=
  hv_step f pk m bits hi (by norm_num : 254 < 255) (r := 9) (by norm_num)

theorem hv_e0 {i : ℕ} (hi : i < 34) :
    hv f pk m bits (e0Cell i) = xE (sigW bits i) (tabN (chainTab f m bits) i) 255 +
      cellOfBits (sigW bits i) := by
  rw [show e0Cell i = chainBase i + 2550 from rfl, hv_off f pk m bits hi (by norm_num)]
  unfold chainOffVal
  rw [if_neg (by norm_num), if_pos rfl]
  all_goals rfl

theorem hv_e1 {i : ℕ} (hi : i < 34) :
    hv f pk m bits (e1Cell i) = thermo (dig m i) 254 *
      (xE (sigW bits i) (tabN (chainTab f m bits) i) 255 + cellOfBits (sigW bits i)) := by
  rw [show e1Cell i = chainBase i + 2551 from rfl, hv_off f pk m bits hi (by norm_num)]
  unfold chainOffVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  all_goals rfl

theorem hv_end {i : ℕ} (hi : i < 34) :
    hv f pk m bits (endCell i) = cellOfBits (sigW bits i) + thermo (dig m i) 254 *
      (xE (sigW bits i) (tabN (chainTab f m bits) i) 255 + cellOfBits (sigW bits i)) := by
  rw [show endCell i = chainBase i + 2552 from rfl, hv_off f pk m bits hi (by norm_num)]
  unfold chainOffVal
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  all_goals rfl

theorem hv_endW {i : ℕ} (hi : i < 34) :
    cellBits (hv f pk m bits (endCell i)) = endsOf m bits (chainTab f m bits) i := by
  rw [hv_end f pk m bits hi]
  show cellBits (endE (dig m i) (sigW bits i) (tabN (chainTab f m bits) i)) = _
  rw [endE_eq]
  exact cellBits_cellOfBits _

theorem hv_end_canon {i : ℕ} (hi : i < 34) : IsCanonical128 (hv f pk m bits (endCell i)) := by
  rw [hv_end f pk m bits hi]
  show IsCanonical128 (endE (dig m i) (sigW bits i) (tabN (chainTab f m bits) i))
  rw [endE_eq]
  exact isCanonical_cellOfBits _

/-! ### Segments C, D, E, F cells -/

theorem hv_temp {o : ℕ} (h : o < 1000) : hv f pk m bits (96000 + o) = tempVal m o := by
  rw [hv_ge f pk m bits (by omega)]
  unfold cellVal
  rw [if_neg (show ¬ 96000 + o < 8192 by omega), if_neg (show ¬ 96000 + o < 95232 by omega),
    if_neg (show ¬ 96000 + o < 96000 by omega), if_pos (show 96000 + o < 97000 by omega),
    show 96000 + o - 96000 = o by omega]

theorem hv_linkAcc {h s : ℕ} (hh : h < 2) (hs : s < 15) :
    hv f pk m bits (linkAccCell h s) = linkAccV m h s := by
  by_cases h0 : s = 0
  · subst h0
    rw [linkAccCell_zero, hv_d f pk m bits (by unfold linkChain; omega)]
    all_goals rfl
  · have e : linkAccCell h s = 96000 + (16 * h + s) := by
      unfold linkAccCell
      rw [if_neg h0, if_neg (by omega)]
      all_goals omega
    rw [e, hv_temp f pk m bits (by omega)]
    unfold tempVal
    rw [if_pos (show 16 * h + s < 32 by omega),
      if_pos (show 1 ≤ (16 * h + s) % 16 ∧ (16 * h + s) % 16 < 15 by omega),
      show (16 * h + s) / 16 = h by omega, show (16 * h + s) % 16 = s by omega]

theorem hv_prodAcc {s : ℕ} (hs : s < 32) : hv f pk m bits (prodAccCell s) = prodAccV m s := by
  by_cases h0 : s = 0
  · subst h0
    rw [prodAccCell_zero, hv_p f pk m bits (by norm_num)]
    all_goals rfl
  · have e : prodAccCell s = 96000 + (100 + s) := by
      unfold prodAccCell
      rw [if_neg h0]
      all_goals omega
    rw [e, hv_temp f pk m bits (by omega)]
    unfold tempVal
    rw [if_neg (show ¬ 100 + s < 32 by omega),
      if_pos (show 101 ≤ 100 + s ∧ 100 + s < 132 by omega), show 100 + s - 100 = s by omega]

theorem hv_root {o : ℕ} (h : 97000 ≤ o) :
    hv f pk m bits o = rootOffVal (rootTab f m bits) (o - 97000) := by
  rw [hv_ge f pk m bits (by omega)]
  unfold cellVal
  rw [if_neg (show ¬ o < 8192 by omega), if_neg (show ¬ o < 95232 by omega),
    if_neg (show ¬ o < 96000 by omega), if_neg (show ¬ o < 97000 by omega)]

theorem hv_stLo {k : ℕ} (hk : k < 34) :
    hv f pk m bits (rootStateCell (k + 1)) = lowE (rootTab f m bits) k := by
  have e : rootStateCell (k + 1) = 97000 + 2 * (k + 1) := by
    unfold rootStateCell
    rw [if_neg (by omega)]
  rw [e, hv_root f pk m bits (by omega), show 97000 + 2 * (k + 1) - 97000 = 2 * (k + 1) by omega]
  unfold rootOffVal
  rw [if_pos (show 2 ≤ 2 * (k + 1) ∧ 2 * (k + 1) < 70 by omega),
    if_pos (show 2 * (k + 1) % 2 = 0 by omega), show 2 * (k + 1) / 2 - 1 = k by omega]

theorem hv_stHi {k : ℕ} (hk : k < 34) :
    hv f pk m bits (rootStateCell (k + 1) + 1) = highE (rootTab f m bits) k := by
  have e : rootStateCell (k + 1) + 1 = 97000 + (2 * (k + 1) + 1) := by
    unfold rootStateCell
    rw [if_neg (by omega)]
    all_goals omega
  rw [e, hv_root f pk m bits (by omega),
    show 97000 + (2 * (k + 1) + 1) - 97000 = 2 * (k + 1) + 1 by omega]
  unfold rootOffVal
  rw [if_pos (show 2 ≤ 2 * (k + 1) + 1 ∧ 2 * (k + 1) + 1 < 70 by omega),
    if_neg (show ¬ ((2 * (k + 1) + 1) % 2 = 0) by omega),
    show (2 * (k + 1) + 1) / 2 - 1 = k by omega]

theorem hv_haltOne : hv f pk m bits haltOneCell = oneV := by
  rw [hv_root f pk m bits (by decide)]
  show rootOffVal (rootTab f m bits) (97100 - 97000) = oneV
  first | rfl | (unfold rootOffVal; norm_num)

theorem hv_haltFpc : hv f pk m bits haltFpcCell = fpcV := by
  rw [hv_root f pk m bits (by decide)]
  show rootOffVal (rootTab f m bits) (97101 - 97000) = fpcV
  first | rfl | (unfold rootOffVal; norm_num)

/-- The root state pair before absorb `t`, as the oracle sees it. -/
theorem hv_stPair {t : ℕ} (ht : t ≤ 34) :
    cellBits (hv f pk m bits (rootStateCell t + 1)) ++ cellBits (hv f pk m bits (rootStateCell t)) =
      stOf (rootTab f m bits) t := by
  cases t with
  | zero =>
    rw [rootStateCell_zero, hv_z1 f pk m bits, hv_z0 f pk m bits, cellBits_zero]
    exact zero_append_zero_128
  | succ t =>
    rw [hv_stHi f pk m bits (by omega), hv_stLo f pk m bits (by omega)]
    exact out_pair _ _ _ (cellBits_cellOfBits _) (cellBits_cellOfBits _)

theorem hv_st_canon {t : ℕ} (ht : t ≤ 34) :
    IsCanonical128 (hv f pk m bits (rootStateCell t)) ∧
      IsCanonical128 (hv f pk m bits (rootStateCell t + 1)) := by
  cases t with
  | zero =>
    rw [rootStateCell_zero, hv_z1 f pk m bits, hv_z0 f pk m bits]
    exact ⟨isCanonical_zero, isCanonical_zero⟩
  | succ t =>
    rw [hv_stHi f pk m bits (by omega), hv_stLo f pk m bits (by omega)]
    exact ⟨isCanonical_cellOfBits _, isCanonical_cellOfBits _⟩

end Decode

/-! ## Honest link and checksum values -/

theorem linkAccV_sum (m : Message) (h : ℕ) :
    ∀ s, linkAccV m h s = ∑ b ∈ Finset.range (s + 1), dVal m (linkChain h b)
  | 0 => by
    show linkAccV m h 0 = ∑ b ∈ Finset.range 1, dVal m (linkChain h b)
    rw [Finset.sum_range_one]
    all_goals rfl
  | s + 1 => by
    rw [Finset.sum_range_succ, ← linkAccV_sum m h s]
    all_goals rfl

theorem prodAccV_prod (m : Message) :
    ∀ s, prodAccV m s = ∏ b ∈ Finset.range (s + 1), pVal m b
  | 0 => by
    show prodAccV m 0 = ∏ b ∈ Finset.range 1, pVal m b
    rw [Finset.prod_range_one]
    all_goals rfl
  | s + 1 => by
    rw [Finset.prod_range_succ, ← prodAccV_prod m s]
    all_goals rfl

/-- The honest `D` of a message chain is the byte word of its digit. -/
theorem dVal_link (m : Message) {h b : ℕ} (hh : h < 2) (hb : b < 16) :
    dVal m (linkChain h b) =
      cellOfBits (BitVec.ofNat 128 (dig m (linkChain h b) <<< (8 * b))) := by
  have e := accE_V (dig m (linkChain h b)) (dig_le m _) (linkChain h b)
  rw [bytePos_linkChain hh hb] at e
  exact e

theorem linkAccV_lo (m : Message) : linkAccV m 0 15 = cellOfBits (m.extractLsb' 0 128) := by
  have hsum : linkAccV m 0 15 = ∑ b ∈ Finset.range 16, dVal m (linkChain 0 b) :=
    linkAccV_sum m 0 15
  have hterm : ∀ b ∈ Finset.range 16, dVal m (linkChain 0 b) = cellOfBits (BitVec.ofNat 128
      (((m.extractLsb' 0 128).toNat / 256 ^ b % 256) <<< (8 * b))) := by
    intro b hb
    have hb' : b < 16 := Finset.mem_range.mp hb
    have hc : linkChain 0 b < 34 := by unfold linkChain; omega
    have h1 : dig m (linkChain 0 b) = digit m ⟨linkChain 0 b, hc⟩ := dig_fin m ⟨_, hc⟩
    have h2 : digit m ⟨linkChain 0 b, hc⟩ =
        (m.extractLsb' 0 128).toNat / 256 ^ (31 - linkChain 0 b) % 256 :=
      digit_cell1 m ⟨linkChain 0 b, hc⟩ (show 16 ≤ linkChain 0 b by unfold linkChain; omega)
        (show linkChain 0 b < 32 by unfold linkChain; omega)
    have h3 : 31 - linkChain 0 b = b := by unfold linkChain; omega
    rw [dVal_link m (by norm_num) hb', h1, h2, h3]
  rw [hsum, Finset.sum_congr rfl hterm, pack_sum_of_bytes]

theorem linkAccV_hi (m : Message) : linkAccV m 1 15 = cellOfBits (m.extractLsb' 128 128) := by
  have hsum : linkAccV m 1 15 = ∑ b ∈ Finset.range 16, dVal m (linkChain 1 b) :=
    linkAccV_sum m 1 15
  have hterm : ∀ b ∈ Finset.range 16, dVal m (linkChain 1 b) = cellOfBits (BitVec.ofNat 128
      (((m.extractLsb' 128 128).toNat / 256 ^ b % 256) <<< (8 * b))) := by
    intro b hb
    have hb' : b < 16 := Finset.mem_range.mp hb
    have hc : linkChain 1 b < 34 := by unfold linkChain; omega
    have h1 : dig m (linkChain 1 b) = digit m ⟨linkChain 1 b, hc⟩ := dig_fin m ⟨_, hc⟩
    have h2 : digit m ⟨linkChain 1 b, hc⟩ =
        (m.extractLsb' 128 128).toNat / 256 ^ (15 - linkChain 1 b) % 256 :=
      digit_cell2 m ⟨linkChain 1 b, hc⟩ (show linkChain 1 b < 16 by unfold linkChain; omega)
    have h3 : 15 - linkChain 1 b = b := by unfold linkChain; omega
    rw [dVal_link m (by norm_num) hb', h1, h2, h3]
  rw [hsum, Finset.sum_congr rfl hterm, pack_sum_of_bytes]

/-- The honest checksum product passes the check. -/
theorem prodAcc_full (m : Message) : prodAccV m 31 = pVal m 32 * pVal m 33 := by
  have hprod : prodAccV m 31 = ∏ b ∈ Finset.range 32, pVal m b := prodAccV_prod m 31
  have hP : ∀ b ∈ Finset.range 32,
      pVal m b = ofK (gpow (255 - m.toNat / 256 ^ (31 - b) % 256)) := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    have h1 : pVal m b = uV b (dig m b) := accE_U (dig m b) (dig_le m b) b
    have h2 : dig m b = m.toNat / 256 ^ (31 - b) % 256 :=
      (dig_fin m ⟨b, by omega⟩).trans (digit_of_lt m ⟨b, by omega⟩ hb')
    rw [h1, h2]
    unfold uV uExp
    rw [if_pos hb']
  have hC := checksum_eq_sum m
  have h32 : pVal m 32 =
      ofK (gpow (256 * (Checksum.wotsChecksumValue 256 (messageDigits m) / 256))) := by
    have h1 : pVal m 32 = uV 32 (dig m 32) := accE_U (dig m 32) (dig_le m 32) 32
    have hd : dig m 32 = Checksum.wotsChecksumValue 256 (messageDigits m) / 256 :=
      (dig_fin m ⟨32, by norm_num⟩).trans (digit_hi_checksum m ⟨32, by norm_num⟩ rfl)
    rw [h1]
    unfold uV uExp
    rw [if_neg (by norm_num), if_pos rfl, hd]
  have h33 : pVal m 33 = ofK (gpow (Checksum.wotsChecksumValue 256 (messageDigits m) % 256)) := by
    have h1 : pVal m 33 = uV 33 (dig m 33) := accE_U (dig m 33) (dig_le m 33) 33
    have hd : dig m 33 = Checksum.wotsChecksumValue 256 (messageDigits m) % 256 :=
      (dig_fin m ⟨33, by norm_num⟩).trans (digit_lo_checksum m ⟨33, by norm_num⟩ rfl)
    rw [h1]
    unfold uV uExp
    rw [if_neg (by norm_num), if_neg (by norm_num), hd]
  have hsum : ∏ b ∈ Finset.range 32, pVal m b =
      ofK (gpow (Checksum.wotsChecksumValue 256 (messageDigits m))) := by
    rw [Finset.prod_congr rfl hP, hC]
    exact ofK_gpow_prod (fun b => 255 - m.toNat / 256 ^ (31 - b) % 256) 32
  rw [hprod, hsum, h32, h33, checksum_honest]

/-! ## The honest answers -/

theorem chain_answer (f : HashTable) (i d : ℕ) (σ : Word) {j : ℕ} (hj : j < 255) :
    f ⟨896, chainInput i j (inW d σ (cutAns 255 (chainAnsF f i d σ)) j)⟩ =
      cutAns 255 (chainAnsF f i d σ) j := by
  have hq : chainQ i d σ j (cutAns 255 (chainAnsF f i d σ)) = chainQ i d σ j (chainAnsF f i d σ) :=
    chainQ_congr (i := i) (d := d) (σ := σ) (A := chainAnsF f i d σ)
      (B := cutAns 255 (chainAnsF f i d σ)) (j := j)
      (fun k hk => cutAns_of_lt _ (show k < 255 by omega))
  have hq' : chainInput i j (inW d σ (cutAns 255 (chainAnsF f i d σ)) j) =
      chainQ i d σ j (chainAnsF f i d σ) := hq
  rw [hq', cutAns_of_lt _ hj, chainAnsF_spec f i d σ j]

theorem root_answer (f : HashTable) (ends : ℕ → Word) {t : ℕ} (ht : t < 34) :
    f ⟨896, rootQ ends t (cutAns 34 (rootAnsF f ends))⟩ = cutAns 34 (rootAnsF f ends) t := by
  have hq : rootQ ends t (cutAns 34 (rootAnsF f ends)) = rootQ ends t (rootAnsF f ends) := by
    unfold rootQ
    rw [stOf_congr (R := rootAnsF f ends) (R' := cutAns 34 (rootAnsF f ends)) (k := t)
      (fun s hs => cutAns_of_lt _ (show s < 34 by omega))]
  rw [hq, cutAns_of_lt _ ht, rootAnsF_spec f ends t]

/-! ## The honest relations -/

section Honest

variable (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)

theorem honest_step (hlen : bits.length = 4352) {i j r : ℕ} (hi : i < 34) (hj : j < 255)
    (hr : r < 10) : CRel f (hv f pk m bits) (stepInstr i j r) := by
  interval_cases r
  · rw [stepInstr_0]
    show hv f pk m bits (tCell i j) = hv f pk m bits (tCell i j) * hv f pk m bits (tCell i j)
    rw [hv_t f pk m bits hi hj]
    exact thermo_mul_self _ _
  · rw [stepInstr_1]
    show hv f pk m bits (tPrevCell i j) =
      hv f pk m bits (tPrevCell i j) * hv f pk m bits (tCell i j)
    rw [hv_tPrev f pk m bits hi hj, hv_t f pk m bits hi hj]
    exact thermoPrev_mul_thermo _ _
  · rw [stepInstr_2]
    show hv f pk m bits (sCell i j) = hv f pk m bits (xCell i j) + hv f pk m bits (sigCell i)
    rw [hv_s f pk m bits hi hj, hv_x f pk m bits hlen hi (by omega : j ≤ 255),
      hv_sig f pk m bits hlen hi]
  · rw [stepInstr_3]
    show hv f pk m bits (uCell i j) = hv f pk m bits (tPrevCell i j) * hv f pk m bits (sCell i j)
    rw [hv_u f pk m bits hi hj, hv_tPrev f pk m bits hi hj, hv_s f pk m bits hi hj]
  · rw [stepInstr_4]
    show hv f pk m bits (inCell i j) = hv f pk m bits (sigCell i) + hv f pk m bits (uCell i j)
    rw [hv_in f pk m bits hi hj, hv_sig f pk m bits hlen hi, hv_u f pk m bits hi hj]
  · rw [stepInstr_5]
    show OracleCompressCells
      ![hv f pk m bits (inCell i j), hv f pk m bits (chainIdCell i), hv f pk m bits (posCell j),
        hv f pk m bits zCell]
      (hv f pk m bits zCell) (hv f pk m bits (zCell + 1)) (hv f pk m bits (xCell i (j + 1)))
      (hv f pk m bits (xCell i (j + 1) + 1)) (hv f pk m bits oneCell)
      (f ⟨896, blake2sQuery ![hv f pk m bits (inCell i j), hv f pk m bits (chainIdCell i),
        hv f pk m bits (posCell j), hv f pk m bits zCell] (hv f pk m bits zCell)
        (hv f pk m bits (zCell + 1)) (hv f pk m bits oneCell)⟩)
    rw [hv_inW f pk m bits hi hj, hv_chainId f pk m bits hi, hv_pos f pk m bits hj,
      hv_z0 f pk m bits, hv_z1 f pk m bits, hv_x f pk m bits hlen hi (by omega : j + 1 ≤ 255),
      hv_x1 f pk m bits hi hj, hv_one f pk m bits, tabN_chainTab f m bits hi]
    have hq : blake2sQuery ![cellOfBits (inW (dig m i) (sigW bits i)
        (cutAns 255 (chainAnsF f i (dig m i) (sigW bits i))) j), chainIdV i, posV j, 0] 0 0 oneV =
        chainInput i j (inW (dig m i) (sigW bits i)
          (cutAns 255 (chainAnsF f i (dig m i) (sigW bits i))) j) := by
      rw [blake2sQuery_chain i j _ (chainIdV i) (posV j) 0 0 0 oneV (cellBits_cellOfBits _)
        (cellBits_cellOfBits _) cellBits_zero cellBits_zero cellBits_zero cellBits_oneV,
        cellBits_cellOfBits]
    rw [hq, chain_answer f i (dig m i) (sigW bits i) hj]
    exact ⟨canon4 (isCanonical_cellOfBits _) (isCanonical_cellOfBits _)
      (isCanonical_cellOfBits _) isCanonical_zero, isCanonical_zero, isCanonical_zero,
      isCanonical_cellOfBits _, isCanonical_cellOfBits _, isCanonical_oneV,
      cellBits_cellOfBits _, cellBits_cellOfBits _⟩
  · rw [stepInstr_6]
    show hv f pk m bits (pVCell i j) =
      hv f pk m bits (tCell i j) * hv f pk m bits (wvCell (bytePos i) j)
    rw [hv_pV f pk m bits hi hj, hv_t f pk m bits hi hj, hv_wvSel f pk m bits i hj]
    all_goals rfl
  · rw [stepInstr_7]
    show hv f pk m bits (aVCell i (j + 1)) =
      hv f pk m bits (aVCell i j) + hv f pk m bits (pVCell i j)
    rw [hv_aV f pk m bits hi (by omega : j + 1 ≤ 255), hv_aV f pk m bits hi (by omega : j ≤ 255),
      hv_pV f pk m bits hi hj, accE_succ]
  · rw [stepInstr_8]
    show hv f pk m bits (pUCell i j) = hv f pk m bits (tCell i j) * hv f pk m bits (wuSelCell i j)
    rw [hv_pU f pk m bits hi hj, hv_t f pk m bits hi hj, hv_wuSel f pk m bits i hj]
    all_goals rfl
  · rw [stepInstr_9]
    show hv f pk m bits (aUCell i (j + 1)) =
      hv f pk m bits (aUCell i j) + hv f pk m bits (pUCell i j)
    rw [hv_aU f pk m bits hi (by omega : j + 1 ≤ 255), hv_aU f pk m bits hi (by omega : j ≤ 255),
      hv_pU f pk m bits hi hj, accE_succ]

theorem honest_end (hlen : bits.length = 4352) {i e : ℕ} (hi : i < 34) (he : e < 3) :
    CRel f (hv f pk m bits) (endInstr i e) := by
  interval_cases e
  · rw [endInstr_0]
    show hv f pk m bits (e0Cell i) = hv f pk m bits (xCell i 255) + hv f pk m bits (sigCell i)
    rw [hv_e0 f pk m bits hi, hv_x f pk m bits hlen hi (le_refl 255), hv_sig f pk m bits hlen hi]
  · rw [endInstr_1]
    show hv f pk m bits (e1Cell i) = hv f pk m bits (tCell i 254) * hv f pk m bits (e0Cell i)
    rw [hv_e1 f pk m bits hi, hv_t f pk m bits hi (by norm_num), hv_e0 f pk m bits hi]
  · rw [endInstr_2]
    show hv f pk m bits (endCell i) = hv f pk m bits (sigCell i) + hv f pk m bits (e1Cell i)
    rw [hv_end f pk m bits hi, hv_sig f pk m bits hlen hi, hv_e1 f pk m bits hi]

theorem honest_link {h s : ℕ} (hh : h < 2) (hs : s < 15) :
    CRel f (hv f pk m bits) (linkInstr h s) := by
  show hv f pk m bits (linkAccCell h (s + 1)) =
    hv f pk m bits (linkAccCell h s) + hv f pk m bits (dCell (linkChain h (s + 1)))
  rw [hv_linkAcc f pk m bits hh hs, hv_d f pk m bits (by unfold linkChain; omega)]
  by_cases h14 : s + 1 < 15
  · rw [hv_linkAcc f pk m bits hh h14]
    rfl
  · obtain rfl : s = 14 := by omega
    show hv f pk m bits (linkAccCell h 15) = linkAccV m h 15
    rw [linkAccCell_15]
    obtain rfl | rfl : h = 0 ∨ h = 1 := by omega
    · show hv f pk m bits 1 = linkAccV m 0 15
      rw [hv_msg0, linkAccV_lo]
    · show hv f pk m bits 2 = linkAccV m 1 15
      rw [hv_msg1, linkAccV_hi]

theorem honest_prod {s : ℕ} (hs : s < 32) : CRel f (hv f pk m bits) (prodInstr s) := by
  by_cases h31 : s < 31
  · rw [prodInstr_lt h31]
    show hv f pk m bits (prodAccCell (s + 1)) =
      hv f pk m bits (prodAccCell s) * hv f pk m bits (pCell (s + 1))
    rw [hv_prodAcc f pk m bits (by omega : s + 1 < 32), hv_prodAcc f pk m bits (by omega : s < 32),
      hv_p f pk m bits (by omega : s + 1 < 34)]
    all_goals rfl
  · obtain rfl : s = 31 := by omega
    rw [prodInstr_31]
    show hv f pk m bits (prodAccCell 31) = hv f pk m bits (pCell 32) * hv f pk m bits (pCell 33)
    rw [hv_prodAcc f pk m bits (by norm_num : (31 : ℕ) < 32),
      hv_p f pk m bits (by norm_num : (32 : ℕ) < 34),
      hv_p f pk m bits (by norm_num : (33 : ℕ) < 34)]
    exact prodAcc_full m

theorem honest_absorb {t : ℕ} (ht : t < 34) : CRel f (hv f pk m bits) (rootInstr t) := by
  rw [rootInstr_lt ht]
  show OracleCompressCells
    ![hv f pk m bits (endCell t), hv f pk m bits zCell, hv f pk m bits zCell, hv f pk m bits zCell]
    (hv f pk m bits (rootStateCell t)) (hv f pk m bits (rootStateCell t + 1))
    (hv f pk m bits (rootStateCell (t + 1))) (hv f pk m bits (rootStateCell (t + 1) + 1))
    (hv f pk m bits (rootMdCell (33 - t)))
    (f ⟨896, blake2sQuery ![hv f pk m bits (endCell t), hv f pk m bits zCell,
      hv f pk m bits zCell, hv f pk m bits zCell] (hv f pk m bits (rootStateCell t))
      (hv f pk m bits (rootStateCell t + 1)) (hv f pk m bits (rootMdCell (33 - t)))⟩)
  have hz : cellBits (hv f pk m bits zCell) = 0 := by
    rw [hv_z0 f pk m bits]
    exact cellBits_zero
  have hq := blake2sQuery_absorb (33 - t) (hv f pk m bits (endCell t)) (hv f pk m bits zCell)
    (hv f pk m bits zCell) (hv f pk m bits zCell) (hv f pk m bits (rootStateCell t))
    (hv f pk m bits (rootStateCell t + 1)) (hv f pk m bits (rootMdCell (33 - t))) hz hz hz
    (by rw [hv_rootMd f pk m bits (show 33 - t < 34 by omega)]; exact cellBits_cellOfBits _)
  have hans : f ⟨896, hashInput (stOf (rootTab f m bits) t)
      ((endsOf m bits (chainTab f m bits) t).setWidth 512) (BitVec.ofNat 128 (2 + (33 - t)))⟩ =
      rootTab f m bits t :=
    root_answer f (endsOf m bits (chainTab f m bits)) ht
  have hcanon := hv_st_canon f pk m bits (show t ≤ 34 by omega)
  have hzc : IsCanonical128 (hv f pk m bits zCell) := by
    rw [hv_z0 f pk m bits]
    exact isCanonical_zero
  have hmdc : IsCanonical128 (hv f pk m bits (rootMdCell (33 - t))) := by
    rw [hv_rootMd f pk m bits (show 33 - t < 34 by omega)]
    exact isCanonical_cellOfBits _
  rw [hq, hv_stPair f pk m bits (show t ≤ 34 by omega), hv_endW f pk m bits ht, hans,
    hv_stLo f pk m bits ht, hv_stHi f pk m bits ht]
  exact ⟨canon4 (hv_end_canon f pk m bits ht) hzc hzc hzc, hcanon.1, hcanon.2,
    isCanonical_cellOfBits _, isCanonical_cellOfBits _, hmdc,
    cellBits_cellOfBits _, cellBits_cellOfBits _⟩

theorem honest_pk (hpk : rootValue f (reconstructedWords f m bits) = pk) :
    CRel f (hv f pk m bits) (rootInstr 34) := by
  rw [rootInstr_34]
  show hv f pk m bits pkCell = hv f pk m bits (rootStateCell 34) + hv f pk m bits zCell
  have h34 : hv f pk m bits (rootStateCell 34) = lowE (rootTab f m bits) 33 :=
    hv_stLo f pk m bits (k := 33) (by norm_num)
  have hr : (rootValueFold f (List.ofFn (reconstructedWords f m bits)) 0).extractLsb' 0 128 =
      pk := hpk
  rw [hv_pk f pk m bits, h34, hv_z0 f pk m bits, add_zero]
  show cellOfBits pk = cellOfBits ((rootTab f m bits 33).extractLsb' 0 128)
  rw [rootTab_33, hr]

theorem honest_halt {u : ℕ} (hu : u < 3) : CRel f (hv f pk m bits) (haltInstr u) := by
  interval_cases u
  · show hv f pk m bits haltOneCell = oneV
    exact hv_haltOne f pk m bits
  · show hv f pk m bits haltFpcCell = fpcV
    exact hv_haltFpc f pk m bits
  · show IsInK (hv f pk m bits haltOneCell) ∧ IsInK (hv f pk m bits haltFpcCell) ∧
      IsInK (hv f pk m bits haltOneCell)
    rw [hv_haltOne f pk m bits, hv_haltFpc f pk m bits]
    exact ⟨isInK_oneV, isInK_fpcV, isInK_oneV⟩

theorem honest_const (hlen : bits.length = 4352) :
    ∀ a < A_len, CRel f (hv f pk m bits) (constInstr a) := by
  refine (forall_lt_A_iff _).mpr
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [constInstr_zero]
    exact hv_z0 f pk m bits
  · rw [constInstr_one]
    exact hv_z1 f pk m bits
  · rw [constInstr_two]
    exact hv_one f pk m bits
  · rw [constInstr_three]
    exact hv_fpc f pk m bits
  · intro i hi
    rw [constInstr_chainId hi]
    exact hv_chainId f pk m bits hi
  · intro r hr
    rw [constInstr_rootMd hr]
    exact hv_rootMd f pk m bits hr
  · intro j hj
    rw [constInstr_pos hj]
    exact hv_pos f pk m bits hj
  · intro p hp j hj
    rw [constInstr_wv hp hj]
    exact hv_wvCell f pk m bits hp hj
  · intro j hj
    rw [constInstr_wu hj]
    exact hv_wu f pk m bits hj
  · intro j hj
    rw [constInstr_wuHi hj]
    exact hv_wuHi f pk m bits hj
  · intro j hj
    rw [constInstr_wuLo hj]
    exact hv_wuLo f pk m bits hj
  · rw [constInstr_ubHi]
    exact hv_ubHi f pk m bits
  · rw [constInstr_ubLo]
    exact hv_ubLo f pk m bits
  · intro p hp
    rw [constInstr_vb hp]
    exact hv_vb f pk m bits hp
  · rw [constInstr_len]
    exact hv_len f pk m bits hlen

/-- Under an accepting fixed table, the honest values satisfy all `N` relations. -/
theorem honest_allRel (hlen : bits.length = 4352)
    (hpk : rootValue f (reconstructedWords f m bits) = pk) : AllRel f (hv f pk m bits) := by
  show ∀ k < N, CRel f (hv f pk m bits) (cinstrAt k)
  refine (forall_lt_N_iff _).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [cinstrAt_const ha]
    exact honest_const f pk m bits hlen a ha
  · intro i hi j hj r hr
    rw [cinstrAt_step hi hj hr]
    exact honest_step f pk m bits hlen hi hj hr
  · intro i hi e he
    rw [cinstrAt_end hi he]
    exact honest_end f pk m bits hlen hi he
  · intro h hh s hs
    rw [cinstrAt_link hh hs]
    exact honest_link f pk m bits hh hs
  · intro s hs
    rw [cinstrAt_prod hs]
    exact honest_prod f pk m bits hs
  · intro t ht
    rw [cinstrAt_root ht]
    by_cases h34 : t < 34
    · exact honest_absorb f pk m bits h34
    · obtain rfl : t = 34 := by omega
      exact honest_pk f pk m bits hpk
  · intro u hu
    rw [cinstrAt_halt hu]
    exact honest_halt f pk m bits hu

end Honest

/-! ## Completeness -/

/-- **Honest completeness.** When the verifier accepts under a fixed table, every relation holds
on the loaded honest image. -/
theorem holds_honest (f : HashTable) (pk : PublicKey) (m : Message) (bits : List Bool)
    (hlen : bits.length = 4352) (hpk : rootValue f (reconstructedWords f m bits) = pk) :
    ∀ k < N, Holds f (LeanIsa.loadInput pk m bits (imageF f pk m bits)) k := by
  intro k hk
  have hb := cinstrAt_bounded17 k hk
  have hrel := honest_allRel f pk m bits hlen hpk k hk
  have hb' : (cinstrAt k).Bounded (2 ^ 17) := hb
  exact rel_of_crel f _ hb' (crel_congr f hb
    (fun c hc => (Lx_honest f pk m bits (lt_of_lt_of_eq hc (by norm_num))).symm) hrel)

/-! ## The contract clauses -/

/-- The machine half of the submission: the baseline scheme, the bytecode, memory `2 ^ 17`, the
honest prover and `N` steps. -/
def machineSubmission : LeanIsa.Submission where
  scheme := scheme
  program := program
  memLog := 17
  prover := prover
  steps := fun _ _ _ => N

/-- **Sound**: any submission running this bytecode for this scheme is sound. -/
theorem sound (S : LeanIsa.Submission) (hs : S.scheme = scheme) (hp : S.program = program) :
    S.Sound := by
  intro pk m bits κ h16 h32 L n
  apply probTrue_zero_of_fixed
  intro f
  have hexec : S.exec L n pk m bits =
      LeanIsa.runCost program (LeanIsa.loadInput pk m bits L) n Regs.initial := by
    unfold LeanIsa.Submission.exec
    rw [hp]
  have hver : S.scheme.verify pk m bits = verify pk m bits := by
    rw [hs]
    all_goals rfl
  rw [hexec, hver]
  simp only [simulateQ_bind, simulateQ_pure, fixed_verify, pure_bind]
  intro hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨o, ho, hmem⟩ := hmem
  rw [mem_support_pure_iff] at hmem
  cases o with
  | none => simp at hmem
  | some c =>
    obtain ⟨-, -, hall⟩ := run_complete h32 f _ ho
    obtain ⟨hlen, hroot⟩ := fixed_sound h16 f pk m bits L hall
    rw [if_pos hlen, hroot] at hmem
    simp at hmem

set_option linter.constructorNameAsVariable false in
/-- **Faithful**: the honest prover's run completes exactly when the verifier accepts. -/
theorem faithful : machineSubmission.Faithful := by
  refine ⟨show minLogMem ≤ 17 by decide, show (17 : ℕ) ≤ maxLogMem by decide, ?_⟩
  intro pk m bits
  apply probTrue_zero_of_fixed
  intro f
  have hrun : simulateQ (unifFwdAnswerImpl f) (machineSubmission.honestRun pk m bits) =
      (fun o => o.isSome) <$> simulateQ (unifFwdAnswerImpl f)
        (LeanIsa.runCost program (LeanIsa.loadInput pk m bits (imageF f pk m bits)) N
          Regs.initial) := by
    show simulateQ (unifFwdAnswerImpl f) (prover pk m bits >>= fun L =>
      (fun o : Option ℕ => o.isSome) <$>
        LeanIsa.runCost program (LeanIsa.loadInput pk m bits L) N Regs.initial) = _
    rw [simulateQ_bind, fixed_prover, pure_bind, simulateQ_map]
  have hver : machineSubmission.scheme.verify pk m bits = verify pk m bits := rfl
  generalize hL : LeanIsa.loadInput pk m bits (imageF f pk m bits) = L at hrun
  generalize hN : N = n at hrun
  rw [simulateQ_bind, hrun, hver]
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
  · subst hL
    subst hN
    rw [run_of_holds (κ := 17) (show (17 : ℕ) ≤ maxLogMem by decide) f _
      (holds_honest f pk m bits hacc.1 hacc.2),
      mem_support_pure_iff] at ho
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
    | some c =>
      have hall := (run_complete (κ := 17) (show (17 : ℕ) ≤ maxLogMem by decide) f L ho).2.2
      subst hL
      exact hacc (fixed_sound (κ := 17) (show (16 : ℕ) ≤ 17 by decide) f pk m bits
        (imageF f pk m bits) hall)

end

end OptimalOTS.LeanIsaBaseline.Honest
