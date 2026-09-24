import OptimalOTS.LeanIsa
import Submissions.UpperLeanIsa.ConstraintMath

/-!
# The HL-FLAT-A bytecode

The hinted-landing machine for the FLAT-42 layer scheme (`SchemeFlat.lean`), design
`leanisa-frontier/hlflat/hlflat_model.py` with the *uniform-cost* block layout (`NOTES.md`):
every block of chain `k` costs the same number of non-hash instructions whatever its digit, so
every completing run executes exactly `425` instructions (`117` of them `BLAKE2S`).

* **Frames.** `F_k = g ^ ((k + 1) · 2 ^ 33)`. The dispatch of chain `k` is
  `MUL(H_k, g, H'_k); JUMP(ONE, H_k, F_k)` with `H_k` a prover hint. The only instructions that
  can execute in frame `F_k` are the entries `I0_k = JUMP(ONE, H'_k, ONE)` of chain `k`, whose
  operands are frame-shifted (`sop`); they return to frame `1` at the next slot.
* **Entries.** Entry `s` of chain `k` sits at `BASE k + 21 · s` (`s < W k`).
* **Blocks.** The tie (`SET T_k; XOR` into the accumulator, or for `s = 0` the zero copy and an
  accumulator copy), the landing-encoded product `MUL(G_{k-1}, H_k, G_k)` (chain 0 has
  `G_0 = H_0`), the `s` inline chain steps, then the next dispatch; chain 41 ends with the exit
  `JUMP(ONE, K0, ONE)` into the root at `rootSlot`, and `K0 = g ^ rootSlot`.
* **Root.** Ten tagged `BLAKE2S` (the first one's cv pair is `(top 0, top 1)`, held at
  `cvCell, cvCell + 1`), then `XOR` into the public key cell; it falls through to the sentinel.

This file holds the cells, the constants, the cell-level instructions, the image and its
builder-level decode lemmas, and the frame lemma. No slot range is ever evaluated: the builders
are irreducible and decoded segment by segment.
-/

namespace OptimalOTS.HLFlat

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

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

/-- The word of cell `c`, total: `0` past the end of the image. -/
def Lx {κ : ℕ} (L : MemImage κ) (c : ℕ) : E := if h : c < 2 ^ κ then L ⟨c, h⟩ else 0

/-- An address whose reduced exponent is at least `2 ^ 32` is out of range at every `κ ≤ 32`. -/
theorem read_gpow_none {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) {n : ℕ}
    (h : 2 ^ 32 ≤ n % ordG) : L.read (gpow n) = none := by
  rw [← gpow_mod, MemImage.read,
    gLog?_gpow_eq_none (le_trans (Nat.pow_le_pow_right (by norm_num) hκ) h)
      (by rw [← ordG_eq]; exact Nat.mod_lt _ (by norm_num [ordG])),
    Option.map_none]

/-- An address whose reduced exponent is a cell `c < 2 ^ κ` reads that cell. -/
theorem read_gpow_some {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) {n c : ℕ}
    (h : n % ordG = c) (hc : c < 2 ^ κ) : L.read (gpow n) = some (Lx L c) := by
  rw [← gpow_mod, h, Lx, dif_pos hc]
  exact MemImage.read_gpow (by omega) L ⟨c, hc⟩

/-! ## Frames -/

/-- The frame exponent of chain `k`: `(k + 1) · 2 ^ 33` (frames are indexed from 1). -/
def frameExp (k : ℕ) : ℕ := (k + 1) * 8589934592

/-- The frame pointer of chain `k`. -/
def frame (k : ℕ) : K := gpow (frameExp k)

/-- The operand that names cell `c` in frame `k`: `g ^ (c - frameExp k)` in the exponent group. -/
def sop (k c : ℕ) : K := gpow (c + ordG - frameExp k)

/-- Frame pointers of chains `k < 42` are never `1`: the sentinel needs `fp = 1`. -/
theorem frame_ne_one {k : ℕ} (hk : k < 42) : frame k ≠ 1 := by
  intro h
  have h' : gpow (frameExp k) = gpow 0 := h.trans (pow_zero g).symm
  have := gpow_inj (show frameExp k < 2 ^ 64 - 1 by unfold frameExp; omega)
    (show (0 : ℕ) < 2 ^ 64 - 1 by norm_num) h'
  unfold frameExp at this; omega

/-! ## Layout constants -/

/-- Positions (digit range) of chain `k`: 8 for `k < 40`, 16 for `k = 40, 41`. -/
def W (k : ℕ) : ℕ := if k < 40 then 8 else 16

/-- Entry base of chain `k`; entry `s` of chain `k` sits at `BASE k + 21 · s`. -/
def BASE (k : ℕ) : ℕ := if k < 41 then 2740 + 168 * k else 9806

/-- The root segment's first slot, the exit target `K0 = g ^ rootSlot`. -/
def rootSlot : ℕ := 262132

/-- The sentinel slot `2 ^ 18 - 1`. -/
def sentinel : ℕ := 262143

theorem W_le {k : ℕ} : W k ≤ 16 := by unfold W; split_ifs <;> omega

theorem W_pos {k : ℕ} : 8 ≤ W k := by unfold W; split_ifs <;> omega

theorem W_eq_len (k : Fin numChains) : W k.val = Flat.len k := by
  unfold W Flat.len Flat.wid
  have := k.isLt
  by_cases h : k.val < 40
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h, if_pos (by omega)]; rfl

/-! ## Cells -/

def pkCell : ℕ := 0
def msgLo : ℕ := 1
def msgHi : ℕ := 2
def lenCell : ℕ := 3
/-- The revealed word of chain `k` (signature cell `k`). -/
def wCell (k : ℕ) : ℕ := 4 + k
def nonceCell : ℕ := 46
/-- The zero cell; `(zCell, oneCell)` is the constant cv pair `(0, 1)`. -/
def zCell : ℕ := 47
def oneCell : ℕ := 48
def tidxCell : ℕ := 49
def gCell : ℕ := 50
def k0Cell : ℕ := 51
/-- The symbol cell `v < 7`, value `v + 3`. -/
def symCell (v : ℕ) : ℕ := 52 + v
/-- The frame constant of chain `k`. -/
def fCell (k : ℕ) : ℕ := 59 + k
/-- The index output pair. -/
def idxCell : ℕ := 101
/-- The tie pattern of chain `k`. -/
def tCell (k : ℕ) : ℕ := 103 + k
/-- The tie accumulator after chain `k`; the last one is the index cell. -/
def accCell (k : ℕ) : ℕ := if k = 41 then idxCell else 145 + k
/-- The landing hint of chain `k`. -/
def hCell (k : ℕ) : ℕ := 186 + k
/-- `H'_k = H_k · g`, the return address of the entry. -/
def h1Cell (k : ℕ) : ℕ := 228 + k
/-- The running landing product after chain `k ≥ 1` (after chain 41 it is `K0`). -/
def prodOut (k : ℕ) : ℕ := if k = 41 then k0Cell else 270 + k
/-- The running landing product before chain `k ≥ 1` (`G_0 = H_0`). -/
def prodPrev (k : ℕ) : ℕ := if k = 1 then hCell 0 else 270 + (k - 1)
/-- The output pair of the last step of chain `k ≥ 2` (and of chain 0, then copied). -/
def topCell (k : ℕ) : ℕ := 320 + 2 * k
/-- The root's first cv pair `(top 0, top 1)`; `cvCell + 2` is chain 1's junk high half. -/
def cvCell : ℕ := 410
/-- The cell the root reads top `k` from. -/
def rootTop (k : ℕ) : ℕ := if k = 0 then cvCell else if k = 1 then cvCell + 1 else topCell k
/-- The output pair of the last step of chain `k`. -/
def chainOut (k : ℕ) : ℕ := if k = 1 then cvCell + 1 else topCell k
/-- The intermediate pair after inline step `t` of chain `k`. -/
def xCell (k t : ℕ) : ℕ := 1024 + 32 * k + 2 * t
/-- The root state pair after call `r`. -/
def stCell (r : ℕ) : ℕ := 2400 + 2 * r
/-- The cv pair of root call `r`. -/
def rootCv (r : ℕ) : ℕ := if r = 0 then cvCell else stCell (r - 1)
/-- The metadata cell of root call `r`: `Z, g, SYM_0, …, SYM_6, LEN` (values `0, 2, 3, …, 5504`). -/
def rhoCell (r : ℕ) : ℕ :=
  if r = 0 then zCell else if r = 1 then gCell else if r < 9 then symCell (r - 2) else lenCell

/-! ## Constants -/

def oneV : E := ofK 1
def gV : E := ofK g
/-- The tie pattern of digit `s` of chain `k`: `s` in the bit field of chain `k`. -/
def fpat (k s : ℕ) : E := natV (s * 2 ^ posW Flat.wid k)
def k0V : E := ofK (gpow rootSlot)
def frameV (k : ℕ) : E := ofK (frame k)
/-- Tag position of the step of chain `k` at chain position `j`. -/
def tagPos (k j : ℕ) : ℕ := Flat.off k + j

/-! ## Cell-level instructions -/

/-- An instruction over cell indices. `dispatch k` is `JUMP(ONE, H_k, F_k)`, `exit` is
`JUMP(ONE, K0, ONE)`, and `entry k` is the frame-shifted `I0_k`. -/
inductive CInstr
  | xor (a b c : ℕ)
  | mul (a b c : ℕ)
  | setc (a : ℕ) (v : E)
  | blake (m0 m1 m2 m3 cv out md : ℕ)
  | dispatch (k : ℕ)
  | exit
  | entry (k : ℕ)
  | pad

namespace CInstr

/-- The ISA instruction; all but `entry` address frame-1 cells `gpow c`. -/
def toInstr : CInstr → Instr
  | .xor a b c => .xor (gpow a) (gpow b) (gpow c)
  | .mul a b c => .mulNative (gpow a) (gpow b) (gpow c)
  | .setc a v => .setConstant (gpow a) v
  | .blake m0 m1 m2 m3 cv out md =>
      .blake2s ![gpow m0, gpow m1, gpow m2, gpow m3] (gpow cv) (gpow out) (gpow md)
  | .dispatch k => .jump (gpow oneCell) (gpow (hCell k)) (gpow (fCell k))
  | .exit => .jump (gpow oneCell) (gpow k0Cell) (gpow oneCell)
  | .pad => .xor 0 0 0
  | .entry k => .jump (sop k oneCell) (sop k (h1Cell k)) (sop k oneCell)

/-- The cycles of a walk step at this instruction: a dispatch step also pays the entry. -/
def cost : CInstr → ℕ
  | .blake .. => 10
  | .dispatch _ => 2
  | _ => 1

/-- The instructions a walk step at this instruction executes. -/
def steps : CInstr → ℕ
  | .dispatch _ => 2
  | _ => 1

/-- Straight-line instructions: they fall through to the next slot. -/
def straight : CInstr → Bool
  | .xor .. => true
  | .mul .. => true
  | .setc .. => true
  | .blake .. => true
  | _ => false

/-- The first cell an instruction reads, for the frame-range argument. -/
def cell0 : CInstr → ℕ
  | .xor a _ _ => a
  | .mul a _ _ => a
  | .setc a _ => a
  | .blake m0 .. => m0
  | .dispatch _ => oneCell
  | .exit => oneCell
  | .pad => 0
  | .entry _ => 0

/-- The shape invariant of every slot: all frame-1 cells below `2 ^ 16`, chains `< 42`. -/
def Bounded : CInstr → Prop
  | .xor a b c => a < 2 ^ 16 ∧ b < 2 ^ 16 ∧ c < 2 ^ 16
  | .mul a b c => a < 2 ^ 16 ∧ b < 2 ^ 16 ∧ c < 2 ^ 16
  | .setc a _ => a < 2 ^ 16
  | .blake m0 m1 m2 m3 cv out md =>
      m0 < 2 ^ 16 ∧ m1 < 2 ^ 16 ∧ m2 < 2 ^ 16 ∧ m3 < 2 ^ 16 ∧ cv + 1 < 2 ^ 16 ∧
        out + 1 < 2 ^ 16 ∧ md < 2 ^ 16
  | .dispatch k => k < 42
  | .exit => True
  | .entry k => k < 42
  | .pad => True

theorem cell0_lt {ci : CInstr} (hb : ci.Bounded) (hpad : ci ≠ .pad) (hent : ∀ j, ci ≠ .entry j) :
    ci.cell0 < 2 ^ 16 := by
  cases ci with
  | xor a b c => exact hb.1
  | mul a b c => exact hb.1
  | setc a v => exact hb
  | blake m0 m1 m2 m3 cv out md => exact hb.1
  | dispatch k => show 48 < 2 ^ 16; norm_num
  | exit => show 48 < 2 ^ 16; norm_num
  | entry k => exact absurd rfl (hent k)
  | pad => exact absurd rfl hpad

theorem opcode_blake {m0 m1 m2 m3 cv out md : ℕ} :
    (CInstr.blake m0 m1 m2 m3 cv out md).toInstr.opcode = .blake2s := rfl

end CInstr

/-! ## The generic frame lemma -/

/-- If the first read fails, the instruction fails (every arm reads its first operand first). -/
theorem exec_none_of_first {κ : ℕ} (L : MemImage κ) (r : Regs K) (ci : CInstr)
    (hpad : ci ≠ .pad) (hent : ∀ j, ci ≠ .entry j)
    (h : L.read (r.fp * gpow ci.cell0) = none) :
    LeanIsa.execute L r ci.toInstr = pure none := by
  cases ci with
  | pad => exact absurd rfl hpad
  | entry j => exact absurd rfl (hent j)
  | blake m0 m1 m2 m3 cv out md =>
    simp only [CInstr.cell0] at h
    simp [CInstr.toInstr, LeanIsa.execute, h]
  | _ =>
    simp only [CInstr.cell0] at h
    simp [CInstr.toInstr, LeanIsa.execute, LeanerVM.Semantics.execute, h]

/-- The pad fails in every frame (it reads address `0`). -/
theorem exec_pad {κ : ℕ} (L : MemImage κ) (r : Regs K) :
    LeanIsa.execute L r CInstr.pad.toInstr = pure none := by
  have h : LeanerVM.Semantics.execute L r (.xor 0 0 0) = none := by
    simp only [LeanerVM.Semantics.execute, mul_zero, MemImage.read_zero, Option.bind_eq_bind,
      Option.bind_none]
  exact congrArg pure h

/-- Entry `j` executed in frame `fp = g ^ f` whose first read is out of range fails. -/
theorem exec_entry_none {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {f j : ℕ}
    (h : 2 ^ 32 ≤ (f + (oneCell + ordG - frameExp j)) % ordG) :
    LeanIsa.execute L ⟨pc, gpow f⟩ (CInstr.entry j).toInstr = pure none := by
  have hr : L.read (gpow f * sop j oneCell) = none := by
    rw [sop, gpow_mul_gpow]; exact read_gpow_none hκ L h
  simp [CInstr.toInstr, LeanIsa.execute, LeanerVM.Semantics.execute, hr]

/-- **Frame lemma, generic form.** In frame `F_k`, every bounded instruction other than `I0_k`
fails at every memory size `κ ≤ 32`. -/
theorem exec_frame_fail {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {k : ℕ} (hk : k < 42)
    {ci : CInstr} (hb : ci.Bounded) (hne : ci ≠ .entry k) :
    LeanIsa.execute L ⟨pc, frame k⟩ ci.toInstr = pure none := by
  have first : ci ≠ .pad → (∀ j, ci ≠ .entry j) →
      LeanIsa.execute L ⟨pc, frame k⟩ ci.toInstr = pure none := fun hpad hent => by
    have ha := CInstr.cell0_lt hb hpad hent
    apply exec_none_of_first L _ ci hpad hent
    show L.read (gpow (frameExp k) * gpow ci.cell0) = none
    rw [gpow_mul_gpow]
    apply read_gpow_none hκ L
    rw [mod_ord_of_lt (by unfold frameExp ordG; omega)]
    unfold frameExp; omega
  cases ci with
  | pad => exact exec_pad L _
  | entry j =>
    have hj : j < 42 := hb
    have hjk : j ≠ k := fun h => hne (h ▸ rfl)
    apply exec_entry_none hκ L pc
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · rw [mod_ord_of_ge (by unfold frameExp ordG oneCell; omega)
        (by unfold frameExp ordG oneCell; omega)]
      unfold frameExp ordG oneCell; omega
    · rw [mod_ord_of_lt (by unfold frameExp ordG oneCell; omega)]
      unfold frameExp ordG oneCell; omega
  | xor a b c => exact first (by simp) (by simp)
  | mul a b c => exact first (by simp) (by simp)
  | setc a v => exact first (by simp) (by simp)
  | blake m0 m1 m2 m3 cv out md => exact first (by simp) (by simp)
  | dispatch j => exact first (by simp) (by simp)
  | exit => exact first (by simp) (by simp)

/-- In frame `1`, every entry fails: its shifted operands are out of range. -/
theorem exec_entry_frame_one {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {j : ℕ}
    (hj : j < 42) : LeanIsa.execute L ⟨pc, 1⟩ (CInstr.entry j).toInstr = pure none := by
  have h := exec_entry_none (f := 0) (j := j) hκ L pc (by
    rw [mod_ord_of_lt (by unfold frameExp ordG oneCell; omega)]
    unfold frameExp ordG oneCell; omega)
  rwa [show gpow 0 = 1 from pow_zero g] at h

/-! ## The builders -/

/-- Slots `0 … 57`: the constants, the index hash, then chain 0's dispatch. -/
def prologue (s : ℕ) : CInstr :=
  if s = 0 then .setc zCell 0
  else if s = 1 then .setc oneCell oneV
  else if s = 2 then .setc lenCell (natV 5504)
  else if s = 3 then .setc tidxCell (natV 10)
  else if s = 4 then .setc gCell gV
  else if s = 5 then .setc k0Cell k0V
  else if s < 13 then .setc (symCell (s - 6)) (natV (s - 3))
  else if s < 55 then .setc (fCell (s - 13)) (frameV (s - 13))
  else if s = 55 then .blake msgLo msgHi nonceCell pkCell zCell idxCell tidxCell
  else if s = 56 then .mul (hCell 0) gCell (h1Cell 0)
  else if s = 57 then .dispatch 0
  else .pad

/-- Inline step `t` of the `s` steps of chain `k`: position `W k - 1 - s + t`. -/
def chainOp (k s t : ℕ) : CInstr :=
  .blake (if t = 0 then wCell k else xCell k (t - 1))
    (symCell (tagPos k (W k - 1 - s + t) % 7))
    (symCell (tagPos k (W k - 1 - s + t) / 7 % 7))
    (symCell (tagPos k (W k - 1 - s + t) / 49))
    zCell (if t + 1 = s then chainOut k else xCell k t) oneCell

/-- Op `i ∈ [1, 21)` of the block of digit `s` of chain `k`. -/
def blockOp (k s i : ℕ) : CInstr :=
  if k = 0 then
    if i = 1 then .setc (accCell 0) (fpat 0 s)
    else if i < s + 2 then chainOp 0 s (i - 2)
    else if i = s + 2 then .xor (if s = 0 then wCell 0 else topCell 0) zCell cvCell
    else if i = s + 3 then .mul (hCell 1) gCell (h1Cell 1)
    else if i = s + 4 then .dispatch 1
    else .pad
  else
    if i = 1 then (if s = 0 then .xor (wCell k) zCell (rootTop k) else .setc (tCell k) (fpat k s))
    else if i = 2 then .xor (accCell (k - 1)) (if s = 0 then zCell else tCell k) (accCell k)
    else if i = 3 then .mul (prodPrev k) (hCell k) (prodOut k)
    else if i < s + 4 then chainOp k s (i - 4)
    else if i = s + 4 then
      (if k < 41 then .mul (hCell (k + 1)) gCell (h1Cell (k + 1)) else .exit)
    else if i = s + 5 ∧ k < 41 then .dispatch (k + 1)
    else .pad

/-- Slot `o` of chain `k`'s region: entries every 21 slots. -/
def unitInstr (k o : ℕ) : CInstr := if o % 21 = 0 then .entry k else blockOp k (o / 21) (o % 21)

/-- Root call `t < 10`, then the public-key check. -/
def rootOp (t : ℕ) : CInstr :=
  if t < 10 then
    .blake (rootTop (4 * t + 2)) (rootTop (4 * t + 3)) (rootTop (4 * t + 4)) (rootTop (4 * t + 5))
      (rootCv t) (stCell t) (rhoCell t)
  else .xor (stCell 9) zCell pkCell

/-- The cell-level instruction at slot `s`, decoded by segment. -/
def cinstrAt (s : ℕ) : CInstr :=
  if s < 58 then prologue s
  else if s < 2740 then .pad
  else if s < 9460 then unitInstr ((s - 2740) / 168) ((s - 2740) % 168)
  else if s < 9796 then unitInstr 40 (s - 9460)
  else if s < 9806 then .pad
  else if s < 10142 then unitInstr 41 (s - 9806)
  else if s < 262132 then .pad
  else if s < 262143 then rootOp (s - 262132)
  else .pad

/-- The ISA instruction at slot `s`. -/
abbrev instrAt (s : ℕ) : Instr := (cinstrAt s).toInstr

/-- The bytecode: `2 ^ 18` slots, sentinel at `2 ^ 18 - 1`. -/
def program : Program where
  logSize := 18
  logSize_le := by decide
  code i := (cinstrAt i).toInstr

theorem program_logSize : program.logSize = 18 := rfl

/- The if-chain builders are irreducible: elaborating a predicate defined by `match` on a
builder applied to `s - c` would otherwise `whnf` through `Nat.sub`. -/
attribute [irreducible] prologue chainOp blockOp unitInstr rootOp cinstrAt

/-! ## Segment decoding of `cinstrAt` -/

theorem cinstrAt_pro {s : ℕ} (h : s < 58) : cinstrAt s = prologue s := by
  unfold cinstrAt; rw [if_pos h]

theorem cinstrAt_gapA {s : ℕ} (h1 : 58 ≤ s) (h2 : s < 2740) : cinstrAt s = .pad := by
  unfold cinstrAt; rw [if_neg (by omega), if_pos h2]

theorem cinstrAt_u39 {s : ℕ} (h1 : 2740 ≤ s) (h2 : s < 9460) :
    cinstrAt s = unitInstr ((s - 2740) / 168) ((s - 2740) % 168) := by
  unfold cinstrAt; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem cinstrAt_u40 {s : ℕ} (h1 : 9460 ≤ s) (h2 : s < 9796) :
    cinstrAt s = unitInstr 40 (s - 9460) := by
  unfold cinstrAt; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem cinstrAt_gapB {s : ℕ} (h1 : 9796 ≤ s) (h2 : s < 9806) : cinstrAt s = .pad := by
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem cinstrAt_u41 {s : ℕ} (h1 : 9806 ≤ s) (h2 : s < 10142) :
    cinstrAt s = unitInstr 41 (s - 9806) := by
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos h2]

theorem cinstrAt_gapC {s : ℕ} (h1 : 10142 ≤ s) (h2 : s < 262132) : cinstrAt s = .pad := by
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos h2]

theorem cinstrAt_rootSeg {s : ℕ} (h1 : 262132 ≤ s) (h2 : s < 262143) :
    cinstrAt s = rootOp (s - 262132) := by
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem cinstrAt_tail {s : ℕ} (h1 : 262143 ≤ s) : cinstrAt s = .pad := by
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Slot `o < 21 · W k` of chain `k`'s region. -/
theorem cinstrAt_unit {k o : ℕ} (hk : k < 42) (ho : o < 21 * W k) :
    cinstrAt (BASE k + o) = unitInstr k o := by
  by_cases h40 : k < 40
  · have hW : W k = 8 := if_pos h40
    have hB : BASE k = 2740 + 168 * k := if_pos (by omega)
    rw [hW] at ho
    rw [hB, cinstrAt_u39 (by omega) (by omega),
      show (2740 + 168 * k + o - 2740) / 168 = k by omega,
      show (2740 + 168 * k + o - 2740) % 168 = o by omega]
  · have hW : W k = 16 := if_neg h40
    rw [hW] at ho
    by_cases h41 : k < 41
    · obtain rfl : k = 40 := by omega
      have hB : BASE 40 = 9460 := rfl
      rw [hB, cinstrAt_u40 (by omega) (by omega), show 9460 + o - 9460 = o by omega]
    · obtain rfl : k = 41 := by omega
      have hB : BASE 41 = 9806 := rfl
      rw [hB, cinstrAt_u41 (by omega) (by omega), show 9806 + o - 9806 = o by omega]

/-- The entry of digit `s` of chain `k`. -/
theorem cinstrAt_entry {k s : ℕ} (hk : k < 42) (hs : s < W k) :
    cinstrAt (BASE k + 21 * s) = .entry k := by
  rw [cinstrAt_unit hk (by omega)]
  unfold unitInstr; rw [if_pos (by omega)]

/-- Op `i ∈ [1, 21)` of the block of digit `s` of chain `k`. -/
theorem cinstrAt_block {k s i : ℕ} (hk : k < 42) (hs : s < W k) (hi0 : 0 < i) (hi : i < 21) :
    cinstrAt (BASE k + 21 * s + i) = blockOp k s i := by
  rw [Nat.add_assoc, cinstrAt_unit hk (by omega)]
  unfold unitInstr
  rw [if_neg (by omega), show (21 * s + i) / 21 = s by omega, show (21 * s + i) % 21 = i by omega]

theorem cinstrAt_root {t : ℕ} (ht : t < 11) : cinstrAt (rootSlot + t) = rootOp t := by
  rw [cinstrAt_rootSeg (by unfold rootSlot; omega) (by unfold rootSlot; omega),
    show rootSlot + t - 262132 = t by unfold rootSlot; omega]

theorem cinstrAt_sentinel : cinstrAt sentinel = .pad := cinstrAt_tail (le_refl _)

/-! ## Entries -/

/-- `e` is an entry `I0_k` of chain `k`. -/
def IsEntry (k e : ℕ) : Prop :=
  k < 42 ∧ BASE k ≤ e ∧ e < BASE k + 21 * W k ∧ (e - BASE k) % 21 = 0

theorem isEntry_of {k s : ℕ} (hk : k < 42) (hs : s < W k) : IsEntry k (BASE k + 21 * s) :=
  ⟨hk, by omega, by omega, by omega⟩

/-- An entry is the entry of its digit `(e - BASE k) / 21`. -/
theorem isEntry_eq {k e : ℕ} (h : IsEntry k e) :
    e = BASE k + 21 * ((e - BASE k) / 21) ∧ (e - BASE k) / 21 < W k := by
  obtain ⟨-, h1, h2, h3⟩ := h
  omega

theorem cinstrAt_of_entry {s k : ℕ} (h : IsEntry k s) : cinstrAt s = .entry k := by
  obtain ⟨he, hlt⟩ := isEntry_eq h
  rw [he]; exact cinstrAt_entry h.1 hlt

theorem base_le (k : ℕ) : BASE k ≤ 9806 := by unfold BASE; split_ifs <;> omega

theorem base_ge (k : ℕ) : 2740 ≤ BASE k := by unfold BASE; split_ifs <;> omega

theorem isEntry_lt {k e : ℕ} (h : IsEntry k e) : e < 10142 := by
  obtain ⟨hk, -, h2, -⟩ := h
  have := base_le k
  have : W k ≤ 16 := W_le
  unfold BASE at h2
  unfold W at h2
  split_ifs at h2 <;> omega

theorem blockOp_ne_entry (k s i j : ℕ) : blockOp k s i ≠ .entry j := by
  unfold blockOp chainOp; split_ifs <;> simp

theorem unitInstr_eq_entry {k o j : ℕ} (h : unitInstr k o = .entry j) : j = k ∧ o % 21 = 0 := by
  unfold unitInstr at h
  split_ifs at h with ho
  · exact ⟨(CInstr.entry.inj h).symm, ho⟩
  · exact absurd h (blockOp_ne_entry _ _ _ _)

theorem prologue_ne_entry (s j : ℕ) : prologue s ≠ .entry j := by
  unfold prologue; split_ifs <;> simp

theorem rootOp_ne_entry (t j : ℕ) : rootOp t ≠ .entry j := by
  unfold rootOp; split_ifs <;> simp

/-- The only `I0_k` slots are the entries of chain `k`. -/
theorem cinstrAt_eq_entry {s k : ℕ} (h : cinstrAt s = .entry k) : IsEntry k s := by
  by_cases a : s < 58
  · rw [cinstrAt_pro a] at h; exact absurd h (prologue_ne_entry _ _)
  by_cases b : s < 2740
  · rw [cinstrAt_gapA (by omega) b] at h; exact absurd h (by simp)
  by_cases c : s < 9460
  · rw [cinstrAt_u39 (by omega) c] at h
    obtain ⟨rfl, ho⟩ := unitInstr_eq_entry h
    have hq : (s - 2740) / 168 < 40 := by omega
    refine ⟨by omega, ?_, ?_, ?_⟩ <;> unfold BASE <;> rw [if_pos (by omega)]
    · omega
    · unfold W; rw [if_pos hq]; omega
    · omega
  by_cases d : s < 9796
  · rw [cinstrAt_u40 (by omega) d] at h
    obtain ⟨rfl, ho⟩ := unitInstr_eq_entry h
    refine ⟨by omega, ?_, ?_, ?_⟩ <;> unfold BASE <;> rw [if_pos (by omega)]
    · omega
    · unfold W; rw [if_neg (by omega)]; omega
    · omega
  by_cases e : s < 9806
  · rw [cinstrAt_gapB (by omega) e] at h; exact absurd h (by simp)
  by_cases f : s < 10142
  · rw [cinstrAt_u41 (by omega) f] at h
    obtain ⟨rfl, ho⟩ := unitInstr_eq_entry h
    refine ⟨by omega, ?_, ?_, ?_⟩ <;> unfold BASE <;> rw [if_neg (by omega)]
    · omega
    · unfold W; rw [if_neg (by omega)]; omega
    · omega
  by_cases g' : s < 262132
  · rw [cinstrAt_gapC (by omega) g'] at h; exact absurd h (by simp)
  by_cases i : s < 262143
  · rw [cinstrAt_rootSeg (by omega) i] at h; exact absurd h (rootOp_ne_entry _ _)
  · rw [cinstrAt_tail (by omega)] at h; exact absurd h (by simp)

/-! ## Boundedness -/

theorem prologue_bounded (s : ℕ) : (prologue s).Bounded := by
  unfold prologue
  split_ifs <;> simp [CInstr.Bounded, zCell, oneCell, gCell, k0Cell, fCell, hCell, h1Cell,
    lenCell, tidxCell, symCell, msgLo, msgHi, nonceCell, pkCell, idxCell] <;> omega

theorem chainOp_bounded (k s t : ℕ) (hk : k < 42) (ht : t < 16) : (chainOp k s t).Bounded := by
  have hW := @W_le k
  have htp : tagPos k (W k - 1 - s + t) < 400 := by
    unfold tagPos Flat.off; split_ifs <;> omega
  unfold chainOp
  simp only [CInstr.Bounded, symCell, zCell, oneCell]
  refine ⟨?_, by omega, by omega, by omega, by norm_num, ?_, by norm_num⟩
  · unfold wCell xCell; split_ifs <;> omega
  · unfold chainOut xCell topCell cvCell; split_ifs <;> omega

theorem blockOp_bounded (k s i : ℕ) (hk : k < 42) (hs : s < 16) : (blockOp k s i).Bounded := by
  unfold blockOp
  split_ifs
  all_goals first
    | (apply chainOp_bounded <;> omega)
    | (simp only [CInstr.Bounded, tCell, accCell, prodPrev, prodOut, wCell, hCell, h1Cell,
        zCell, k0Cell, gCell, rootTop, topCell, cvCell, idxCell]
       try split_ifs
       all_goals omega)

theorem unitInstr_bounded (k o : ℕ) (hk : k < 42) (ho : o < 21 * 16) :
    (unitInstr k o).Bounded := by
  unfold unitInstr
  split_ifs
  · exact hk
  · exact blockOp_bounded k _ _ hk (by omega)

theorem rootOp_bounded (t : ℕ) : (rootOp t).Bounded := by
  unfold rootOp
  split_ifs
  · simp only [CInstr.Bounded, rootTop, topCell, cvCell, rootCv, stCell, rhoCell, zCell, gCell,
      symCell, lenCell]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> omega
  · simp only [CInstr.Bounded, stCell, zCell, pkCell]; omega

/-- Every slot satisfies the shape invariant. -/
theorem cinstrAt_bounded (s : ℕ) : (cinstrAt s).Bounded := by
  by_cases a : s < 58
  · rw [cinstrAt_pro a]; exact prologue_bounded s
  by_cases b : s < 2740
  · rw [cinstrAt_gapA (by omega) b]; trivial
  by_cases c : s < 9460
  · rw [cinstrAt_u39 (by omega) c]; exact unitInstr_bounded _ _ (by omega) (by omega)
  by_cases d : s < 9796
  · rw [cinstrAt_u40 (by omega) d]; exact unitInstr_bounded _ _ (by omega) (by omega)
  by_cases e : s < 9806
  · rw [cinstrAt_gapB (by omega) e]; trivial
  by_cases f : s < 10142
  · rw [cinstrAt_u41 (by omega) f]; exact unitInstr_bounded _ _ (by omega) (by omega)
  by_cases g' : s < 262132
  · rw [cinstrAt_gapC (by omega) g']; trivial
  by_cases i : s < 262143
  · rw [cinstrAt_rootSeg (by omega) i]; exact rootOp_bounded _
  · rw [cinstrAt_tail (by omega)]; trivial

/-! ## The frame lemma on the image -/

/-- **Frame lemma.** In frame `F_k`, every slot that is not an entry of chain `k` fails, at every
memory size `κ ≤ 32` and whatever the image. -/
theorem frame_fail {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {k s : ℕ} (hk : k < 42)
    (hs : ¬ IsEntry k s) : LeanIsa.execute L ⟨pc, frame k⟩ (instrAt s) = pure none :=
  exec_frame_fail hκ L pc hk (cinstrAt_bounded s) fun h => hs (cinstrAt_eq_entry h)

/-- In frame `1`, every entry slot fails: `I0` is reachable only through a frame jump. -/
theorem entry_fail_frame_one {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {k s : ℕ}
    (hs : IsEntry k s) : LeanIsa.execute L ⟨pc, 1⟩ (instrAt s) = pure none := by
  show LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt s).toInstr = pure none
  rw [cinstrAt_of_entry hs]
  exact exec_entry_frame_one hκ L pc hs.1

/-! ## Program facts -/

theorem finalPc_eq : program.finalPc = gpow sentinel := by
  show gpow (2 ^ 18 - 1) = gpow 262143; norm_num

theorem gpow_ne_finalPc {e : ℕ} (he : e < sentinel) : gpow e ≠ program.finalPc := by
  intro h
  have := gpow_inj (show e < 2 ^ 64 - 1 by unfold sentinel at he; omega)
    (show (262143 : ℕ) < 2 ^ 64 - 1 by norm_num) (h.trans finalPc_eq)
  unfold sentinel at he; omega

theorem fetch_eq {s : ℕ} (hs : s < 2 ^ 18) :
    program.fetch (gpow s) = some (cinstrAt s).toInstr :=
  program.fetch_gpow ⟨s, hs⟩

/-- Well-formed bytecode: the size cap and no `JUMP` in the halt slot. -/
theorem valid : LeanIsa.BytecodeValid program := by
  refine ⟨le_refl _, ?_⟩
  show (cinstrAt (2 ^ 18 - 1)).toInstr.opcode ≠ .jump
  rw [show 2 ^ 18 - 1 = sentinel by rfl, cinstrAt_sentinel]
  decide

end OptimalOTS.HLFlat
