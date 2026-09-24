import OptimalOTS.LeanIsa
import Submissions.UpperLeanIsa.ConstraintMath

/-!
# The HL-TRI bytecode

The hinted-landing machine for the FLAT-42 layer scheme (`SchemeFlat.lean`), design
`.tmp/hl/hltri_1390_model.py`: the 42 chains are dispatched in 14 groups of three, one landing
per group, and every block of group `g` costs the same number of non-hash instructions whatever
its digits, so every completing run executes exactly `253` instructions (`113` of them
`BLAKE2S`).

* **Groups.** `G_g = (3g, 3g + 1, 3g + 2)` for `g < 12`, `G_12 = (36, 37, 40)`,
  `G_13 = (38, 39, 41)` (`gch g j`). A block is indexed by the junk digit `d < Wd g` and the three
  digits `(a, b, c)` of its group, `a, b < 8`, `c < Wc g` (`16` only for group 13, whose last
  chain is chain 41).
* **Frames.** `F_g = g ^ ((g + 1) · 2 ^ 33)`. The dispatch of group `g` is
  `MUL(H_g, g, H'_g); JUMP(ONE, H_g, F_g)` with `H_g` a prover hint. The only instructions that
  can execute in frame `F_g` are the entries `I0_g = JUMP(ONE, H'_g, ONE)` of group `g`, whose
  operands are frame-shifted (`sop`); they return to frame `1` at the next slot.
* **Entries.** The entry of digits `(d, a, b, c)` of group `g` sits at `BASE g + SP g · grank`,
  `grank = 512 · d + (a · 8 + b) · Wc g + c`.
* **Junk bit.** The index is bits `1 … 127` of the index cell; bit `0` is the junk digit `d < 2`
  of group 0 (1024 group-0 blocks), and the other groups have `d = 0`. Group 0's tie word
  `d + T_0` sets `acc_0`, so `acc_13 = d + Σ T_g` is the whole index cell.
* **Blocks** (frame `1`, after `I0`): the tie (`SET acc_0` for `g = 0`; else `SET T_g; XOR` into
  the accumulator, or an accumulator copy if all digits are `0`), the zero copies `XOR(W_k, Z, rootTop k)`
  of the zero digits, the layer factor (`SET L_0 := g ^ (rootSlot - 103 + σ)` for `g = 0`; else
  `MUL(L_{g-1}, ·, L_g)` by `ONE`, a prologue constant `g ^ σ` (`σ ≤ 7`) or a
  `SET C_g := g ^ σ`), pads `XOR(Z, Z, Z)` up to `NH g` non-hash ops, the `σ` inline chain steps,
  then the next dispatch; group 13 ends with the exit `JUMP(ONE, K0, ONE)` into the root at
  `rootSlot`. `L_13 = K0 = g ^ rootSlot`.
* **Tops.** The last step of a high-top chain (`hiChain k`) writes its pair to
  `(rootTop k - 1, rootTop k)`, so the root reads the answer's high half; every other chain's last
  step writes `(rootTop k, rootTop k + 1)`. The tops that feed a root call's cv pair sit in that
  call's cv cells `cvCell r, cvCell r + 1`.
* **Root.** Nine tagged `BLAKE2S` (calls `1 … 7` chain the low half of the previous state through
  the message, call 8 takes the full state as cv), then `XOR` into the public key cell; it falls
  through to the sentinel.
* **Constants.** Tag symbols and metadata reuse the prologue's constant cells (`Z`, `ONE`,
  `g ^ 1 … g ^ 7`, `K0`, the length cell).

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

/-- The frame exponent of group `g`: `(g + 1) · 2 ^ 33` (frames are indexed from 1). -/
def frameExp (g : ℕ) : ℕ := (g + 1) * 8589934592

/-- The frame pointer of group `g`. -/
def frame (g : ℕ) : K := gpow (frameExp g)

/-- The operand that names cell `c` in frame `g`: `g ^ (c - frameExp g)` in the exponent group. -/
def sop (g c : ℕ) : K := gpow (c + ordG - frameExp g)

/-- Frame pointers of groups `g < 14` are never `1`: the sentinel needs `fp = 1`. -/
theorem frame_ne_one {g : ℕ} (hg : g < 14) : frame g ≠ 1 := by
  intro h
  have h' : gpow (frameExp g) = gpow 0 := h.trans (pow_zero _).symm
  have := gpow_inj (show frameExp g < 2 ^ 64 - 1 by unfold frameExp; omega)
    (show (0 : ℕ) < 2 ^ 64 - 1 by norm_num) h'
  unfold frameExp at this; omega

/-! ## Chains and groups -/

/-- Positions (digit range) of chain `k`: 8 for `k < 41`, 16 for `k = 41`. -/
def W (k : ℕ) : ℕ := if k < 41 then 8 else 16

theorem W_le {k : ℕ} : W k ≤ 16 := by unfold W; split_ifs <;> omega

theorem W_pos {k : ℕ} : 8 ≤ W k := by unfold W; split_ifs <;> omega

theorem W_eq_len (k : Fin numChains) : W k.val = Flat.len k := by
  unfold W Flat.len Flat.wid
  have := k.isLt
  by_cases h : k.val < 41
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h, if_pos (by omega)]; rfl

/-- Chain `j < 3` of group `g`. -/
def gch (g j : ℕ) : ℕ := if g < 12 then 3 * g + j else if j < 2 then 12 + 2 * g + j else 28 + g

/-- The group of chain `k`. -/
def grp (k : ℕ) : ℕ := if k < 36 then k / 3 else if k = 36 ∨ k = 37 ∨ k = 40 then 12 else 13

/-- The place of chain `k` in its group. -/
def gpos (k : ℕ) : ℕ := if k < 36 then k % 3 else if k < 40 then k % 2 else 2

theorem gch_lt {g j : ℕ} (hg : g < 14) (hj : j < 3) : gch g j < 42 := by
  unfold gch; split_ifs <;> omega

theorem gch_grp {k : ℕ} (hk : k < 42) : gch (grp k) (gpos k) = k := by
  unfold gch grp gpos; split_ifs <;> omega

theorem grp_gch {g j : ℕ} (hg : g < 14) (hj : j < 3) : grp (gch g j) = g ∧ gpos (gch g j) = j := by
  unfold gch grp gpos; split_ifs <;> omega

theorem grp_lt {k : ℕ} (hk : k < 42) : grp k < 14 ∧ gpos k < 3 := by
  unfold grp gpos; split_ifs <;> omega

/-- The range of the last digit of group `g`. -/
def Wc (g : ℕ) : ℕ := if g < 13 then 8 else 16

theorem W_gch {g j : ℕ} (hg : g < 14) (hj : j < 3) :
    W (gch g j) = if j < 2 then 8 else Wc g := by
  unfold W gch Wc; split_ifs <;> omega

/-- The range of the junk digit of group `g`: bit `0` of the index cell is group 0's. -/
def Wd (g : ℕ) : ℕ := if g = 0 then 2 else 1

/-- Blocks of group `g`: `Wd g · 8 · 8 · Wc g`. -/
def NT (g : ℕ) : ℕ := Wd g * (64 * Wc g)

/-- Non-hash ops of a block of group `g` before its tail, counting `I0` and the pads. -/
def NH (g : ℕ) : ℕ := if g < 13 then 6 else 7

/-- Slots per block of group `g`. -/
def SP (g : ℕ) : ℕ := if g < 13 then 29 else 37

/-- The first entry of group `g`. -/
def BASE (g : ℕ) : ℕ := if g = 0 then 28 else if g < 13 then 14876 + 14848 * g else 207900

/-- The rank of the digits `(d, a, b, c)` in group `g`. -/
def grank (g d a b c : ℕ) : ℕ :=
  512 * d + if g < 13 then 64 * a + 8 * b + c else 128 * a + 16 * b + c

/-- The per-group constants, by case. -/
theorem grp_consts {g : ℕ} (hg : g < 14) :
    (g = 0 ∧ Wc g = 8 ∧ NH g = 6 ∧ SP g = 29 ∧ BASE g = 28 ∧ Wd g = 2) ∨
    ((0 < g ∧ g < 13) ∧ Wc g = 8 ∧ NH g = 6 ∧ SP g = 29 ∧ BASE g = 14876 + 14848 * g ∧
      Wd g = 1) ∨
    (g = 13 ∧ Wc g = 16 ∧ NH g = 7 ∧ SP g = 37 ∧ BASE g = 207900 ∧ Wd g = 1) := by
  unfold Wc NH SP BASE Wd
  by_cases h0 : g = 0
  · left; simp [h0]
  by_cases h : g < 13
  · right; left; refine ⟨⟨by omega, h⟩, ?_⟩; simp [h0, h]
  · right; right; refine ⟨by omega, ?_⟩; simp [h0, h]

theorem grank_lt {g d a b c : ℕ} (hg : g < 14) (hd : d < Wd g) (ha : a < 8) (hb : b < 8)
    (hc : c < Wc g) : grank g d a b c < NT g := by
  unfold grank NT
  rcases grp_consts hg with ⟨rfl, hw, -, -, -, hwd⟩ | ⟨⟨h0, h⟩, hw, -, -, -, hwd⟩ |
      ⟨rfl, hw, -, -, -, hwd⟩ <;> rw [hw] at hc ⊢ <;> rw [hwd] at hd ⊢ <;>
    simp_all <;> omega

/-- The root segment's first slot, the exit target `K0 = g ^ rootSlot`. -/
def rootSlot : ℕ := 262133

/-- The sentinel slot `2 ^ 18 - 1`. -/
def sentinel : ℕ := 262143

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
def gCell : ℕ := 50
def k0Cell : ℕ := 51
/-- The frame constant of group `g`. -/
def fCell (g : ℕ) : ℕ := 59 + g
/-- The index output pair. -/
def idxCell : ℕ := 101
/-- The tie word of group `g`. -/
def tCell (g : ℕ) : ℕ := 103 + g
/-- The tie accumulator after group `g`; the last one is the index cell. -/
def accCell (g : ℕ) : ℕ := if g = 13 then idxCell else 145 + g
/-- The landing hint of group `g`. -/
def hCell (g : ℕ) : ℕ := 186 + g
/-- `H'_g = H_g · g`, the return address of the entry. -/
def h1Cell (g : ℕ) : ℕ := 228 + g
/-- The layer constant `g ^ σ` of group `g` when `σ > 7`. -/
def cCell (g : ℕ) : ℕ := 270 + g
/-- The layer product after group `g`; after group 13 it is `K0`. -/
def layCell (g : ℕ) : ℕ := if g = 13 then k0Cell else 290 + g
/-- The prologue constant `g ^ v`, `1 ≤ v ≤ 7` (`g ^ 1` is `gCell`). -/
def gpCell (v : ℕ) : ℕ := if v = 1 then gCell else 440 + v
/-- The symbol cell `v < 7` (value `0, 1, 2, 4, …, 32`): `Z`, `ONE`, then `g ^ (v - 1)`. -/
def symCell (v : ℕ) : ℕ := if v = 0 then zCell else if v = 1 then oneCell else gpCell (v - 1)
/-- The output pair of the last step of a chain the root does not read through a cv cell. -/
def topCell (k : ℕ) : ℕ := 320 + 2 * k
/-- The cv pair of root call `r < 8`. -/
def cvCell (r : ℕ) : ℕ := 410 + 4 * r
/-- The chains whose top is the high half of the last step's answer: `0` and `5r + 1`, `1 ≤ r ≤ 7`
(`Flat.hiTop` on chain indices). -/
def hiChain (k : ℕ) : Bool := k = 0 || (6 ≤ k && k ≤ 36 && k % 5 = 1)
/-- The cell the root reads top `k` from: the cv pairs of the calls for `0, 1` and `5r + 1, 5r + 2`. -/
def rootTop (k : ℕ) : ℕ :=
  if k < 2 then cvCell 0 + k
  else if 6 ≤ k ∧ k ≤ 37 ∧ (k - 1) % 5 < 2 then cvCell ((k - 1) / 5) + (k - 1) % 5
  else topCell k
/-- The output pair of the last step of chain `k`. -/
def chainOut (k : ℕ) : ℕ := if hiChain k then rootTop k - 1 else rootTop k
theorem rootTop_of_hi {k : ℕ} (h : hiChain k = true) : rootTop k = chainOut k + 1 := by
  have : 1 ≤ rootTop k := by unfold rootTop cvCell topCell; split_ifs <;> omega
  unfold chainOut; rw [if_pos h]; omega

theorem rootTop_of_lo {k : ℕ} (h : ¬ hiChain k = true) : rootTop k = chainOut k := by
  unfold chainOut; rw [if_neg h]

/-- Root call `r ∈ [1, 8)` reads its cv pair from the tops `5r + 1, 5r + 2`. -/
theorem rootTop_cv {r : ℕ} (h1 : 1 ≤ r) (h8 : r < 8) :
    rootTop (5 * r + 1) = cvCell r ∧ rootTop (5 * r + 2) = cvCell r + 1 := by
  unfold rootTop cvCell
  constructor <;> rw [if_neg (by omega), if_pos (by omega)] <;> omega

/-- The intermediate pair after inline step `t` of chain `k`. -/
def xCell (k t : ℕ) : ℕ := 1024 + 32 * k + 2 * t
/-- The root state pair after call `r`. -/
def stCell (r : ℕ) : ℕ := 2400 + 2 * r
/-- The cv pair of root call `r`: its own cv cells for `r < 8`, the full state of call 7 for `r = 8`. -/
def rootCv (r : ℕ) : ℕ := if r < 8 then cvCell r else stCell 7
/-- The metadata cell of root call `r`: `Z, g ^ 1, …, g ^ 7, K0`. -/
def rhoCell (r : ℕ) : ℕ := if r = 0 then zCell else if r < 8 then gpCell r else k0Cell

/-! ## Constants -/

def oneV : E := ofK 1
def gV : E := ofK g
def k0V : E := ofK (gpow rootSlot)
def frameV (g : ℕ) : E := ofK (frame g)
/-- The value of symbol cell `v`. -/
def symV (v : ℕ) : E := if v = 0 then 0 else ofK (gpow (v - 1))
/-- The tie word of digits `(d, a, b, c)` of group `g`: the junk digit at bit `0`, each digit in
its chain's bit field of the index cell, one bit above its field in the index word. -/
def gword (g d a b c : ℕ) : ℕ :=
  d + a * 2 ^ (1 + posW Flat.wid (gch g 0)) + b * 2 ^ (1 + posW Flat.wid (gch g 1)) +
    c * 2 ^ (1 + posW Flat.wid (gch g 2))
/-- Tag position of the step of chain `k` at chain position `j`. -/
def tagPos (k j : ℕ) : ℕ := Flat.off k + j

/-! ## Cell-level instructions -/

/-- An instruction over cell indices. `dispatch g` is `JUMP(ONE, H_g, F_g)`, `exit` is
`JUMP(ONE, K0, ONE)`, and `entry g` is the frame-shifted `I0_g`. -/
inductive CInstr
  | xor (a b c : ℕ)
  | mul (a b c : ℕ)
  | setc (a : ℕ) (v : E)
  | blake (m0 m1 m2 m3 cv out md : ℕ)
  | dispatch (g : ℕ)
  | exit
  | entry (g : ℕ)
  | pad

namespace CInstr

/-- The ISA instruction; all but `entry` address frame-1 cells `gpow c`. -/
def toInstr : CInstr → Instr
  | .xor a b c => .xor (gpow a) (gpow b) (gpow c)
  | .mul a b c => .mulNative (gpow a) (gpow b) (gpow c)
  | .setc a v => .setConstant (gpow a) v
  | .blake m0 m1 m2 m3 cv out md =>
      .blake2s ![gpow m0, gpow m1, gpow m2, gpow m3] (gpow cv) (gpow out) (gpow md)
  | .dispatch g => .jump (gpow oneCell) (gpow (hCell g)) (gpow (fCell g))
  | .exit => .jump (gpow oneCell) (gpow k0Cell) (gpow oneCell)
  | .pad => .xor 0 0 0
  | .entry g => .jump (sop g oneCell) (sop g (h1Cell g)) (sop g oneCell)

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

/-- The shape invariant of every slot: all frame-1 cells below `2 ^ 16`, groups `< 14`. -/
def Bounded : CInstr → Prop
  | .xor a b c => a < 2 ^ 16 ∧ b < 2 ^ 16 ∧ c < 2 ^ 16
  | .mul a b c => a < 2 ^ 16 ∧ b < 2 ^ 16 ∧ c < 2 ^ 16
  | .setc a _ => a < 2 ^ 16
  | .blake m0 m1 m2 m3 cv out md =>
      m0 < 2 ^ 16 ∧ m1 < 2 ^ 16 ∧ m2 < 2 ^ 16 ∧ m3 < 2 ^ 16 ∧ cv + 1 < 2 ^ 16 ∧
        out + 1 < 2 ^ 16 ∧ md < 2 ^ 16
  | .dispatch g => g < 14
  | .exit => True
  | .entry g => g < 14
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

theorem ne_entry_of_straight {ci : CInstr} (h : ci.straight = true) (j : ℕ) : ci ≠ .entry j := by
  rintro rfl; cases h

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

/-- **Frame lemma, generic form.** In frame `F_g`, every bounded instruction other than `I0_g`
fails at every memory size `κ ≤ 32`. -/
theorem exec_frame_fail {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {k : ℕ} (hk : k < 14)
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
    have hj : j < 14 := hb
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
    (hj : j < 14) : LeanIsa.execute L ⟨pc, 1⟩ (CInstr.entry j).toInstr = pure none := by
  have h := exec_entry_none (f := 0) (j := j) hκ L pc (by
    rw [mod_ord_of_lt (by unfold frameExp ordG oneCell; omega)]
    unfold frameExp ordG oneCell; omega)
  rwa [show gpow 0 = 1 from pow_zero _] at h

/-! ## The builders -/

/-- Slots `0 … 27`: the constants, the index hash, then group 0's dispatch. -/
def prologue (s : ℕ) : CInstr :=
  if s = 0 then .setc zCell 0
  else if s = 1 then .setc oneCell oneV
  else if s = 2 then .setc lenCell (natV 5504)
  else if s = 3 then .setc gCell gV
  else if s = 4 then .setc k0Cell k0V
  else if s < 19 then .setc (fCell (s - 5)) (frameV (s - 5))
  else if s < 25 then .setc (gpCell (s - 17)) (ofK (gpow (s - 17)))
  else if s = 25 then .blake msgLo msgHi nonceCell pkCell zCell idxCell lenCell
  else if s = 26 then .mul (hCell 0) gCell (h1Cell 0)
  else if s = 27 then .dispatch 0
  else .pad

/-- Inline step `t` of the `s` steps of chain `k`: position `W k - 1 - s + t`. -/
def chainOp (k s t : ℕ) : CInstr :=
  .blake (if t = 0 then wCell k else xCell k (t - 1))
    (symCell (tagPos k (W k - 1 - s + t) % 7))
    (symCell (tagPos k (W k - 1 - s + t) / 7 % 7))
    (symCell (tagPos k (W k - 1 - s + t) / 49))
    zCell (if t + 1 = s then chainOut k else xCell k t) oneCell

/-- The pad of a block, `XOR(Z, Z, Z)`. -/
def nop : CInstr := .xor zCell zCell zCell

/-- Tie ops: one, or two (`SET T_g; XOR`) for `g ≠ 0` with a nonzero digit. -/
def tieLen (g σ : ℕ) : ℕ := if g ≠ 0 ∧ σ ≠ 0 then 2 else 1

/-- Zero digits of a block. -/
def zeroCount (a b c : ℕ) : ℕ :=
  (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) + (if c = 0 then 1 else 0)

/-- Layer ops: one, or two (`SET C_g; MUL`) for `g ≠ 0` with `σ > 7`. -/
def layLen (g σ : ℕ) : ℕ := if g ≠ 0 ∧ 7 < σ then 2 else 1

/-- Ops of the pre part: tie, zero copies, layer factor. -/
def preLen (g a b c : ℕ) : ℕ := tieLen g (a + b + c) + zeroCount a b c + layLen g (a + b + c)

/-- The place in its group of the `q`-th zero digit of `(a, b, c)`. -/
def zeroIdx (a b q : ℕ) : ℕ :=
  if q = 0 then (if a = 0 then 0 else if b = 0 then 1 else 2)
  else if q = 1 then (if a = 0 ∧ b = 0 then 1 else 2) else 2

/-- Tie op `q`. -/
def tieOp (g d a b c q : ℕ) : CInstr :=
  if g = 0 then .setc (accCell 0) (natV (gword 0 d a b c))
  else if a + b + c = 0 then .xor (accCell (g - 1)) zCell (accCell g)
  else if q = 0 then .setc (tCell g) (natV (gword g d a b c))
  else .xor (accCell (g - 1)) (tCell g) (accCell g)

/-- Zero copy `q`: `XOR(W_k, Z, rootTop k)` for the `q`-th zero digit's chain `k`. -/
def zcOp (g a b q : ℕ) : CInstr :=
  .xor (wCell (gch g (zeroIdx a b q))) zCell (rootTop (gch g (zeroIdx a b q)))

/-- Layer op `q` of a block with digit sum `σ`. -/
def layOp (g σ q : ℕ) : CInstr :=
  if g = 0 then .setc (layCell 0) (ofK (gpow (rootSlot - 103 + σ)))
  else if σ = 0 then .mul (layCell (g - 1)) oneCell (layCell g)
  else if σ ≤ 7 then .mul (layCell (g - 1)) (gpCell σ) (layCell g)
  else if q = 0 then .setc (cCell g) (ofK (gpow σ))
  else .mul (layCell (g - 1)) (cCell g) (layCell g)

/-- Pre op `q`. -/
def preOp (g d a b c q : ℕ) : CInstr :=
  if q < tieLen g (a + b + c) then tieOp g d a b c q
  else if q < tieLen g (a + b + c) + zeroCount a b c then zcOp g a b (q - tieLen g (a + b + c))
  else layOp g (a + b + c) (q - tieLen g (a + b + c) - zeroCount a b c)

/-- Chain step `t` of the block: the steps of the group's chains in group order. -/
def stepOp (g a b c t : ℕ) : CInstr :=
  if t < a then chainOp (gch g 0) a t
  else if t < a + b then chainOp (gch g 1) b (t - a)
  else chainOp (gch g 2) c (t - a - b)

/-- Op `i ≥ 1` of the block of digits `(d, a, b, c)` of group `g` (op `0` is `I0_g`). -/
def blockOp (g d a b c i : ℕ) : CInstr :=
  if i < 1 + preLen g a b c then preOp g d a b c (i - 1)
  else if i < NH g then nop
  else if i < NH g + (a + b + c) then stepOp g a b c (i - NH g)
  else if i = NH g + (a + b + c) then
    (if g < 13 then .mul (hCell (g + 1)) gCell (h1Cell (g + 1)) else .exit)
  else if i = NH g + (a + b + c) + 1 ∧ g < 13 then .dispatch (g + 1)
  else .pad

/-- Slot `o` of group `g`'s region: entries every `SP g` slots, blocks by rank. -/
def unitInstr (g o : ℕ) : CInstr :=
  if o % SP g = 0 then .entry g
  else if g < 13 then
    blockOp g (o / SP g / 512) (o / SP g / 64 % 8) (o / SP g / 8 % 8) (o / SP g % 8) (o % SP g)
  else blockOp g 0 (o / SP g / 128) (o / SP g / 16 % 8) (o / SP g % 16) (o % SP g)

/-- Root call `t < 9`, then the public-key check. Calls `1 … 7` take the low half of the previous
state as their first message word; call 8 takes the full state of call 7 as its cv pair. -/
def rootOp (t : ℕ) : CInstr :=
  if t = 0 then
    .blake (rootTop 2) (rootTop 3) (rootTop 4) (rootTop 5) (rootCv 0) (stCell 0) (rhoCell 0)
  else if t < 8 then
    .blake (stCell (t - 1)) (rootTop (5 * t + 3)) (rootTop (5 * t + 4)) (rootTop (5 * t + 5))
      (rootCv t) (stCell t) (rhoCell t)
  else if t = 8 then .blake (rootTop 41) zCell zCell zCell (rootCv 8) (stCell 8) (rhoCell 8)
  else .xor (stCell 8) zCell pkCell

/-- The cell-level instruction at slot `s`, decoded by segment. -/
def cinstrAt (s : ℕ) : CInstr :=
  if s < 28 then prologue s
  else if s < 29724 then unitInstr 0 (s - 28)
  else if s < 207900 then unitInstr ((s - 14876) / 14848) ((s - 14876) % 14848)
  else if s < 245788 then unitInstr 13 (s - 207900)
  else if s < 262133 then .pad
  else if s < 262143 then rootOp (s - 262133)
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
attribute [irreducible] prologue chainOp tieOp zcOp layOp preOp stepOp blockOp unitInstr rootOp
  cinstrAt

/-! ## Segment decoding of `cinstrAt` -/

theorem cinstrAt_pro {s : ℕ} (h : s < 28) : cinstrAt s = prologue s := by
  unfold cinstrAt; rw [if_pos h]

theorem cinstrAt_g0 {s : ℕ} (h1 : 28 ≤ s) (h2 : s < 29724) :
    cinstrAt s = unitInstr 0 (s - 28) := by
  unfold cinstrAt; rw [if_neg (by omega), if_pos h2]

theorem cinstrAt_gA {s : ℕ} (h1 : 29724 ≤ s) (h2 : s < 207900) :
    cinstrAt s = unitInstr ((s - 14876) / 14848) ((s - 14876) % 14848) := by
  unfold cinstrAt; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem cinstrAt_g13 {s : ℕ} (h1 : 207900 ≤ s) (h2 : s < 245788) :
    cinstrAt s = unitInstr 13 (s - 207900) := by
  unfold cinstrAt; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem cinstrAt_gap {s : ℕ} (h1 : 245788 ≤ s) (h2 : s < 262133) : cinstrAt s = .pad := by
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem cinstrAt_rootSeg {s : ℕ} (h1 : 262133 ≤ s) (h2 : s < 262143) :
    cinstrAt s = rootOp (s - 262133) := by
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos h2]

theorem cinstrAt_tail {s : ℕ} (h1 : 262143 ≤ s) : cinstrAt s = .pad := by
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

/-- Slot `o < SP g · NT g` of group `g`'s region. -/
theorem cinstrAt_unit {g o : ℕ} (hg : g < 14) (ho : o < SP g * NT g) :
    cinstrAt (BASE g + o) = unitInstr g o := by
  unfold NT at ho
  rcases grp_consts hg with ⟨rfl, hw, -, hs, hb, hd⟩ | ⟨⟨h0, h⟩, hw, -, hs, hb, hd⟩ |
      ⟨rfl, hw, -, hs, hb, hd⟩ <;> rw [hw, hs, hd] at ho <;> rw [hb]
  · rw [cinstrAt_g0 (by omega) (by omega), show 28 + o - 28 = o by omega]
  · rw [cinstrAt_gA (by omega) (by omega),
      show (14876 + 14848 * g + o - 14876) / 14848 = g by omega,
      show (14876 + 14848 * g + o - 14876) % 14848 = o by omega]
  · rw [cinstrAt_g13 (by omega) (by omega), show 207900 + o - 207900 = o by omega]

/-- The entry of rank `r` of group `g`. -/
theorem cinstrAt_entry {g r : ℕ} (hg : g < 14) (hr : r < NT g) :
    cinstrAt (BASE g + SP g * r) = .entry g := by
  have hsp : 0 < SP g := by unfold SP; split_ifs <;> omega
  rw [cinstrAt_unit hg (Nat.mul_lt_mul_of_pos_left hr hsp)]
  unfold unitInstr; rw [if_pos (Nat.mul_mod_right _ _)]

/-- Op `i ∈ [1, SP g)` of the block of digits `(d, a, b, c)` of group `g`. -/
theorem cinstrAt_block {g d a b c i : ℕ} (hg : g < 14) (hd : d < Wd g) (ha : a < 8) (hb : b < 8)
    (hc : c < Wc g) (hi0 : 0 < i) (hi : i < SP g) :
    cinstrAt (BASE g + SP g * grank g d a b c + i) = blockOp g d a b c i := by
  have hr := grank_lt hg hd ha hb hc
  rw [Nat.add_assoc, cinstrAt_unit hg (by
    unfold NT at hr ⊢
    rcases grp_consts hg with ⟨-, hw, -, hs, -, hwd⟩ | ⟨-, hw, -, hs, -, hwd⟩ |
        ⟨-, hw, -, hs, -, hwd⟩ <;>
      rw [hw, hwd] at hr <;> rw [hs] at hi ⊢ <;> rw [hw, hwd] <;> omega)]
  unfold unitInstr grank
  rcases grp_consts hg with ⟨rfl, hw, -, hs, -, hwd⟩ | ⟨⟨h0, h⟩, hw, -, hs, -, hwd⟩ |
      ⟨rfl, hw, -, hs, -, hwd⟩ <;>
    rw [hw] at hc <;> rw [hwd] at hd <;> rw [hs] at hi ⊢
  · simp only [show (0 : ℕ) < 13 by omega, if_true]
    rw [if_neg (by omega),
      show (29 * (512 * d + (64 * a + 8 * b + c)) + i) / 29 = 512 * d + (64 * a + 8 * b + c) by
        omega,
      show (29 * (512 * d + (64 * a + 8 * b + c)) + i) % 29 = i by omega,
      show (512 * d + (64 * a + 8 * b + c)) / 512 = d by omega,
      show (512 * d + (64 * a + 8 * b + c)) / 64 % 8 = a by omega,
      show (512 * d + (64 * a + 8 * b + c)) / 8 % 8 = b by omega,
      show (512 * d + (64 * a + 8 * b + c)) % 8 = c by omega]
  · obtain rfl : d = 0 := by omega
    rw [if_pos h, if_neg (by omega), if_pos h,
      show (29 * (512 * 0 + (64 * a + 8 * b + c)) + i) / 29 = 512 * 0 + (64 * a + 8 * b + c) by
        omega,
      show (29 * (512 * 0 + (64 * a + 8 * b + c)) + i) % 29 = i by omega,
      show (512 * 0 + (64 * a + 8 * b + c)) / 512 = 0 by omega,
      show (512 * 0 + (64 * a + 8 * b + c)) / 64 % 8 = a by omega,
      show (512 * 0 + (64 * a + 8 * b + c)) / 8 % 8 = b by omega,
      show (512 * 0 + (64 * a + 8 * b + c)) % 8 = c by omega]
  · obtain rfl : d = 0 := by omega
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (37 * (512 * 0 + (128 * a + 16 * b + c)) + i) / 37 = 512 * 0 + (128 * a + 16 * b + c) by
        omega,
      show (37 * (512 * 0 + (128 * a + 16 * b + c)) + i) % 37 = i by omega,
      show (512 * 0 + (128 * a + 16 * b + c)) / 128 = a by omega,
      show (512 * 0 + (128 * a + 16 * b + c)) / 16 % 8 = b by omega,
      show (512 * 0 + (128 * a + 16 * b + c)) % 16 = c by omega]

theorem cinstrAt_root {t : ℕ} (ht : t < 10) : cinstrAt (rootSlot + t) = rootOp t := by
  rw [cinstrAt_rootSeg (by unfold rootSlot; omega) (by unfold rootSlot; omega),
    show rootSlot + t - 262133 = t by unfold rootSlot; omega]

theorem cinstrAt_sentinel : cinstrAt sentinel = .pad := cinstrAt_tail (le_refl _)

/-! ## Block op decoding -/

theorem preOp_straight (g d a b c q : ℕ) :
    (preOp g d a b c q).straight = true ∧ (preOp g d a b c q).cost = 1 := by
  unfold preOp tieOp zcOp layOp; split_ifs <;> exact ⟨rfl, rfl⟩

theorem chainOp_straight (k s t : ℕ) :
    (chainOp k s t).straight = true ∧ (chainOp k s t).cost = 10 := by
  unfold chainOp; exact ⟨rfl, rfl⟩

theorem stepOp_straight (g a b c t : ℕ) :
    (stepOp g a b c t).straight = true ∧ (stepOp g a b c t).cost = 10 := by
  unfold stepOp; split_ifs <;> exact chainOp_straight _ _ _

/-- The pre part fits before the chain steps. -/
theorem pre_fit {g a b c : ℕ} (hg : g < 14) (ha : a < 8) (hb : b < 8) (hc : c < Wc g) :
    1 + preLen g a b c ≤ NH g := by
  unfold preLen tieLen zeroCount layLen
  rcases grp_consts hg with ⟨h, hw, hn, -⟩ | ⟨h, hw, hn, -⟩ | ⟨h, hw, hn, -⟩ <;>
    rw [hw] at hc <;> rw [hn] <;> split_ifs <;> omega

/-- The block, tail included, fits in its `SP g` slots (group 13's tail is the exit alone). -/
theorem blk_fit {g a b c : ℕ} (hg : g < 14) (ha : a < 8) (hb : b < 8) (hc : c < Wc g) :
    NH g + (a + b + c) + (if g < 13 then 1 else 0) < SP g := by
  rcases grp_consts hg with ⟨h, hw, hn, hs, -⟩ | ⟨h, hw, hn, hs, -⟩ | ⟨h, hw, hn, hs, -⟩ <;>
    rw [hw] at hc <;> rw [hn, hs] <;> split_ifs <;> omega

theorem blockOp_pre {g d a b c q : ℕ} (hq : q < preLen g a b c) :
    blockOp g d a b c (1 + q) = preOp g d a b c q := by
  unfold blockOp; rw [if_pos (by omega), show 1 + q - 1 = q by omega]

theorem blockOp_nop {g d a b c i : ℕ} (h1 : 1 + preLen g a b c ≤ i) (h2 : i < NH g) :
    blockOp g d a b c i = nop := by
  unfold blockOp; rw [if_neg (by omega), if_pos h2]

theorem blockOp_step {g d a b c t : ℕ} (hpre : 1 + preLen g a b c ≤ NH g)
    (ht : t < a + b + c) : blockOp g d a b c (NH g + t) = stepOp g a b c t := by
  unfold blockOp
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem blockOp_tail {g d a b c : ℕ} (hpre : 1 + preLen g a b c ≤ NH g) :
    blockOp g d a b c (NH g + (a + b + c)) =
      if g < 13 then .mul (hCell (g + 1)) gCell (h1Cell (g + 1)) else .exit := by
  unfold blockOp
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem blockOp_disp {g d a b c : ℕ} (hpre : 1 + preLen g a b c ≤ NH g) (hg : g < 13) :
    blockOp g d a b c (NH g + (a + b + c) + 1) = .dispatch (g + 1) := by
  unfold blockOp
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos ⟨rfl, hg⟩]

theorem blockOp_ne_entry (g d a b c i j : ℕ) : blockOp g d a b c i ≠ .entry j := by
  unfold blockOp
  split_ifs
  · exact CInstr.ne_entry_of_straight (preOp_straight _ _ _ _ _ _).1 j
  · simp [nop]
  · exact CInstr.ne_entry_of_straight (stepOp_straight _ _ _ _ _).1 j
  · simp
  · simp
  · simp
  · simp

/-! ## Entries -/

/-- `e` is an entry `I0_g` of group `g`. -/
def IsEntry (g e : ℕ) : Prop :=
  g < 14 ∧ BASE g ≤ e ∧ e < BASE g + SP g * NT g ∧ (e - BASE g) % SP g = 0

/-- An entry is the entry of its rank `(e - BASE g) / SP g`. -/
theorem isEntry_eq {g e : ℕ} (h : IsEntry g e) :
    e = BASE g + SP g * ((e - BASE g) / SP g) ∧ (e - BASE g) / SP g < NT g := by
  obtain ⟨hg, h1, h2, h3⟩ := h
  unfold NT at h2 ⊢
  rcases grp_consts hg with ⟨-, hw, -, hs, -, hd⟩ | ⟨-, hw, -, hs, -, hd⟩ | ⟨-, hw, -, hs, -, hd⟩ <;>
    rw [hw, hs, hd] at h2 <;> rw [hs] at h3 <;> rw [hw, hs, hd] <;> omega

theorem cinstrAt_of_entry {s g : ℕ} (h : IsEntry g s) : cinstrAt s = .entry g := by
  obtain ⟨he, hlt⟩ := isEntry_eq h
  rw [he]; exact cinstrAt_entry h.1 hlt

theorem isEntry_lt {g e : ℕ} (h : IsEntry g e) : e < 245788 := by
  obtain ⟨hg, -, h2, -⟩ := h
  unfold NT at h2
  rcases grp_consts hg with ⟨-, hw, -, hs, hb, hd⟩ | ⟨-, hw, -, hs, hb, hd⟩ |
      ⟨-, hw, -, hs, hb, hd⟩ <;> rw [hw, hs, hb, hd] at h2 <;> omega

theorem unitInstr_eq_entry {g o j : ℕ} (h : unitInstr g o = .entry j) :
    j = g ∧ o % SP g = 0 := by
  unfold unitInstr at h
  split_ifs at h with ho
  · exact ⟨(CInstr.entry.inj h).symm, ho⟩
  · exact absurd h (blockOp_ne_entry _ _ _ _ _ _ _)
  · exact absurd h (blockOp_ne_entry _ _ _ _ _ _ _)

theorem prologue_ne_entry (s j : ℕ) : prologue s ≠ .entry j := by
  unfold prologue
  repeat (first | exact fun h => CInstr.noConfusion h | split)

theorem rootOp_ne_entry (t j : ℕ) : rootOp t ≠ .entry j := by
  unfold rootOp; split_ifs <;> simp

/-- The only `I0_g` slots are the entries of group `g`. -/
theorem cinstrAt_eq_entry {s k : ℕ} (h : cinstrAt s = .entry k) : IsEntry k s := by
  by_cases a : s < 28
  · rw [cinstrAt_pro a] at h; exact absurd h (prologue_ne_entry _ _)
  by_cases a0 : s < 29724
  · rw [cinstrAt_g0 (by omega) a0] at h
    obtain ⟨rfl, ho⟩ := unitInstr_eq_entry h
    exact ⟨by omega, by unfold BASE; simp; omega, by unfold BASE SP NT Wc Wd; simp; omega,
      by unfold BASE SP at *; simp at *; omega⟩
  by_cases b : s < 207900
  · rw [cinstrAt_gA (by omega) b] at h
    obtain ⟨rfl, ho⟩ := unitInstr_eq_entry h
    have hq : (s - 14876) / 14848 < 13 := by omega
    have hq0 : (s - 14876) / 14848 ≠ 0 := by omega
    have hsp : SP ((s - 14876) / 14848) = 29 := by unfold SP; rw [if_pos hq]
    rw [hsp] at ho
    refine ⟨by omega, ?_, ?_, ?_⟩ <;> unfold BASE <;> rw [if_neg hq0, if_pos hq]
    · omega
    · unfold NT Wc Wd; rw [if_neg hq0, if_pos hq, hsp]; omega
    · rw [hsp]; omega
  by_cases d : s < 245788
  · rw [cinstrAt_g13 (by omega) d] at h
    obtain ⟨rfl, ho⟩ := unitInstr_eq_entry h
    exact ⟨by omega, by unfold BASE; simp; omega, by unfold BASE SP NT Wc Wd; simp; omega,
      by unfold BASE SP at *; simp at *; omega⟩
  by_cases e : s < 262133
  · rw [cinstrAt_gap (by omega) e] at h; exact absurd h (by simp)
  by_cases i : s < 262143
  · rw [cinstrAt_rootSeg (by omega) i] at h; exact absurd h (rootOp_ne_entry _ _)
  · rw [cinstrAt_tail (by omega)] at h; exact absurd h (by simp)

/-! ## Boundedness -/

theorem prologue_bounded (s : ℕ) : (prologue s).Bounded := by
  unfold prologue
  repeat' split
  all_goals try simp only [CInstr.Bounded, zCell, oneCell, gCell, k0Cell, fCell, hCell,
    h1Cell, lenCell, msgLo, msgHi, nonceCell, pkCell, idxCell, gpCell]
  all_goals (try split_ifs) <;> omega

/-- Symbol cells are constant cells below `2 ^ 16`. -/
theorem symCell_lt {v : ℕ} (hv : v < 9) : symCell v < 2 ^ 16 := by
  unfold symCell gpCell zCell oneCell gCell; split_ifs <;> omega

theorem rootTop_le (k : ℕ) : rootTop k ≤ 440 + 2 * k := by
  unfold rootTop cvCell topCell; split_ifs <;> omega

theorem chainOp_bounded (k s t : ℕ) (hk : k < 42) (ht : t < 16) : (chainOp k s t).Bounded := by
  have hW := @W_le k
  have htp : tagPos k (W k - 1 - s + t) < 400 := by
    unfold tagPos Flat.off; split_ifs <;> omega
  unfold chainOp
  simp only [CInstr.Bounded, zCell, oneCell]
  refine ⟨?_, symCell_lt (by omega), symCell_lt (by omega), symCell_lt (by omega), by norm_num, ?_,
    by norm_num⟩
  · unfold wCell xCell; split_ifs <;> omega
  · have := rootTop_le k
    unfold chainOut xCell; split_ifs <;> omega

theorem preOp_bounded (g d a b c q : ℕ) (hg : g < 14) : (preOp g d a b c q).Bounded := by
  have h0 := gch_lt hg (show zeroIdx a b (q - tieLen g (a + b + c)) < 3 by
    unfold zeroIdx; split_ifs <;> omega)
  have hr := rootTop_le (gch g (zeroIdx a b (q - tieLen g (a + b + c))))
  unfold preOp tieOp zcOp layOp
  split_ifs <;> simp only [CInstr.Bounded, accCell, tCell, idxCell, zCell, wCell,
    layCell, k0Cell, oneCell, gpCell, gCell, cCell] <;>
    (try split_ifs) <;> omega

theorem stepOp_bounded {g a b c t : ℕ} (hg : g < 14) (ha : a < 8) (hb : b < 8) (hc : c < 16)
    (ht : t < a + b + c) : (stepOp g a b c t).Bounded := by
  unfold stepOp
  split_ifs
  · exact chainOp_bounded _ _ _ (gch_lt hg (by omega)) (by omega)
  · exact chainOp_bounded _ _ _ (gch_lt hg (by omega)) (by omega)
  · exact chainOp_bounded _ _ _ (gch_lt hg (by omega)) (by omega)

theorem blockOp_bounded {g d a b c : ℕ} (i : ℕ) (hg : g < 14) (ha : a < 8) (hb : b < 8)
    (hc : c < 16) : (blockOp g d a b c i).Bounded := by
  unfold blockOp
  split_ifs with h1 h2 h3
  · exact preOp_bounded _ _ _ _ _ _ hg
  · simp only [nop, CInstr.Bounded, zCell]; omega
  · exact stepOp_bounded hg ha hb hc (by omega)
  · simp only [CInstr.Bounded, hCell, gCell, h1Cell]; omega
  · trivial
  · show g + 1 < 14; omega
  · trivial

theorem unitInstr_bounded (g o : ℕ) (hg : g < 14) (ho : o < SP g * NT g) :
    (unitInstr g o).Bounded := by
  unfold NT at ho
  unfold unitInstr
  rcases grp_consts hg with ⟨h, hw, -, hs, -, hd⟩ | ⟨h, hw, -, hs, -, hd⟩ | ⟨h, hw, -, hs, -, hd⟩ <;>
    rw [hw, hs, hd] at ho <;> rw [hs] <;> split_ifs <;>
    first
      | exact hg
      | omega
      | exact blockOp_bounded _ hg (by omega) (by omega) (by omega)

theorem rootOp_bounded (t : ℕ) : (rootOp t).Bounded := by
  unfold rootOp
  split_ifs <;>
    simp only [CInstr.Bounded, rootTop, topCell, cvCell, rootCv, stCell, rhoCell, zCell, gCell,
      gpCell, k0Cell, pkCell] <;>
    (try refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) <;> (try split_ifs) <;> omega

/-- Every slot satisfies the shape invariant. -/
theorem cinstrAt_bounded (s : ℕ) : (cinstrAt s).Bounded := by
  by_cases a : s < 28
  · rw [cinstrAt_pro a]; exact prologue_bounded s
  by_cases a0 : s < 29724
  · rw [cinstrAt_g0 (by omega) a0]
    exact unitInstr_bounded _ _ (by omega) (by unfold SP NT Wc Wd; simp; omega)
  by_cases b : s < 207900
  · rw [cinstrAt_gA (by omega) b]
    have hq : (s - 14876) / 14848 < 13 := by omega
    have hq0 : (s - 14876) / 14848 ≠ 0 := by omega
    refine unitInstr_bounded _ _ (by omega) ?_
    unfold SP NT Wc Wd; rw [if_pos hq, if_pos hq, if_neg hq0]; omega
  by_cases d : s < 245788
  · rw [cinstrAt_g13 (by omega) d]
    exact unitInstr_bounded _ _ (by omega) (by unfold SP NT Wc Wd; simp; omega)
  by_cases e : s < 262133
  · rw [cinstrAt_gap (by omega) e]; trivial
  by_cases i : s < 262143
  · rw [cinstrAt_rootSeg (by omega) i]; exact rootOp_bounded _
  · rw [cinstrAt_tail (by omega)]; trivial

/-! ## The frame lemma on the image -/

/-- **Frame lemma.** In frame `F_g`, every slot that is not an entry of group `g` fails, at every
memory size `κ ≤ 32` and whatever the image. -/
theorem frame_fail {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {k s : ℕ} (hk : k < 14)
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
