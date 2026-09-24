import OptimalOTS.LeanIsaMachine

/-!
# The leanISA bytecode of the RT-128 ("Rice-tree forced dispatch", base 128) Winternitz verifier

Design: `NOTES.md` (memory layout, bytecode layout); `b128_model.py` is the executable spec, and
every layout constant below is pinned to it by a `rfl`/`decide` lemma.

The program runs in frame `fp = 1`: every operand is `op c = g ^ c` naming cell `c`. It has
`2 ^ 16` slots; slot `s` holds `(cinstrAt s).toInstr`, where `cinstrAt` is decoded
arithmetically by segment (no proof evaluates the program over a range of indices):

* `[0, 127)`: `SET posCell (s+1) := posV (s+1)`; `127`: `SET k0Cell := tgtV K0`;
  `128`: `SET lenCell := lenV` (`constInstr`).
* `[129, 397)`: chain 0, its Rice(1) dispatch of 16 leaves (142 slots), then body steps
  `j = 1..126` at `s0 0 + j` (`chainInstr 0`).
* `[rBase k, rBase k + 1276)`, `1 ≤ k ≤ 36`: chain `k`, the Rice(1) dispatch of 128 leaves
  (1150 slots), then its body (`chainInstr k`).
* `[46333, 46716)`: chain 37 (`c_hi`), unary dispatch and leaves, then its body (`hiInstr`).
* `[46716, 47866)`: chain 38 (`c_lo`) Rice dispatch; `[47866, 65369)`: `.pad`;
  `[65369, 65495)`: chain 38 body.
* `[65495, 65534)`: root absorptions (`rootInstr`); `65534`: the pk `XOR` (`pkInstr`), which
  falls through into the sentinel `65535` (`.pad`).
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters LeanerVM.Semantics

noncomputable section

/-! ## Operands -/

/-- The operand naming cell `c` in frame `fp = 1`: the address `g ^ c`. -/
def op (c : ℕ) : K := gpow c

theorem g_mul_op (c : ℕ) : g * op c = op (c + 1) := (gpow_succ c).symm

theorem gpow_zero : gpow 0 = 1 := pow_zero g

theorem g_mul_gpow (k : ℕ) : g * gpow k = gpow (k + 1) := (gpow_succ k).symm

/-! ## Cells -/

/-- The pinned public-key cell. -/
def pkCell : ℕ := 0
/-- The pinned length cell. -/
def lenCell : ℕ := 3
/-- The pinned signature cell of chain `k`. -/
def sigCell (k : ℕ) : ℕ := 4 + k
/-- The zero cell `Z` (pinned, zero once the length is checked); `(Z, Z + 1)` is the zero pair. -/
def zCell : ℕ := 43
/-- The position / chain-id / root-metadata constant cell of `j` (`posCell 0 = Z`). -/
def posCell (j : ℕ) : ℕ := if j = 0 then zCell else 100 + j
/-- The cell holding ONE (`= posCell 1`). -/
def oneCell : ℕ := 101
/-- The checksum target cell `tgtV K0`. -/
def k0Cell : ℕ := 400
/-- Base of the scratch block of chain `k`. -/
def scr (k : ℕ) : ℕ := 1024 + 160 * k
/-- Condition hint of unary node `i`. -/
def zuCell (k i : ℕ) : ℕ := scr k + i
/-- Target of unary node `i`. -/
def tuCell (k i : ℕ) : ℕ := scr k + 64 + i
/-- Condition hint of the group node (shared by all groups of the chain). -/
def zbCell (k : ℕ) : ℕ := scr k + 128
/-- Target of the group node. -/
def tbCell (k : ℕ) : ℕ := scr k + 129
/-- `T_k`: the checksum contribution (and the leaf jump cell when `e < 127`). -/
def tCell (k : ℕ) : ℕ := scr k + 132
/-- `V_k`: the leaf jump cell when `e = 127`. -/
def vCell (k : ℕ) : ℕ := scr k + 133
/-- `G_k`: the running checksum product. -/
def gCell (k : ℕ) : ℕ := scr k + 134
/-- `F_k`: the leaf's tie term. -/
def fCell (k : ℕ) : ℕ := scr k + 135
/-- The tie accumulator of chain `k`. Chains 18 and 36 close the message cells 2 and 1. -/
def accCell (k : ℕ) : ℕ := scr k + 136
/-- `U = g ^ (128 c_hi)`. -/
def uCell : ℕ := scr 37 + 137
/-- The previous checksum product. -/
def gPrev (k : ℕ) : ℕ := if k = 0 then oneCell else gCell (k - 1)
/-- The checksum product output of chain `k`. -/
def gOut (k : ℕ) : ℕ := if k = 38 then k0Cell else gCell k
/-- Root state pair `S_t` (low cell); `S_0` is the zero pair. -/
def rootStateCell (t : ℕ) : ℕ := if t = 0 then zCell else 7400 + 2 * t
/-- Chain word `x_{k,j}`; `xCell k (j+1) + 1` is the high half `h_{k,j}`. -/
def xCell (k j : ℕ) : ℕ := 8192 + 256 * k + 2 * j
/-- In-cell bit offset of the tie word of chain `k ∉ {18, 36}`: digit `k < 18` sits in cell 2
at `7 (36 - k) - 128`, digit `k > 18` in cell 1 at `7 (36 - k)`. -/
def tieShift (k : ℕ) : ℕ := if k < 18 then 7 * (36 - k) - 128 else 7 * (36 - k)

theorem posCell_zero : posCell 0 = zCell := rfl
theorem posCell_of_pos {j : ℕ} (hj : j ≠ 0) : posCell j = 100 + j := if_neg hj
theorem posCell_one : posCell 1 = oneCell := rfl
theorem uCell_eq : uCell = 7081 := rfl
theorem rootStateCell_zero : rootStateCell 0 = zCell := rfl
theorem rootStateCell_of_pos {t : ℕ} (ht : t ≠ 0) : rootStateCell t = 7400 + 2 * t := if_neg ht
theorem gPrev_zero : gPrev 0 = oneCell := rfl
theorem gPrev_of {k : ℕ} (h0 : k ≠ 0) : gPrev k = gCell (k - 1) := if_neg h0
theorem gPrev_38 : gPrev 38 = gCell 37 := rfl
theorem gOut_38 : gOut 38 = k0Cell := rfl
theorem gOut_of {k : ℕ} (h38 : k ≠ 38) : gOut k = gCell k := if_neg h38
theorem xCell_succ_add_one (k j : ℕ) : xCell k (j + 1) + 1 = xCell k j + 3 := by
  unfold xCell; omega
theorem zCell_add_one : zCell + 1 = 44 := rfl
theorem tieShift_zero : tieShift 0 = 124 := rfl
theorem tieShift_of_lt {k : ℕ} (hk : k < 18) : tieShift k = 7 * (36 - k) - 128 := if_pos hk
theorem tieShift_of_ge {k : ℕ} (hk : 18 ≤ k) : tieShift k = 7 * (36 - k) := if_neg (by omega)

/-! ## Values -/

/-- ONE: the cell `cellOfBits 1`, also the field one (`oneV_eq_cellOfBits`, `oneV_eq_ofK`). -/
def oneV : E := E.ofLimbs 1 0 0
/-- The position / id / metadata constant `j`. -/
def posV (j : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 j)
/-- The checked length `4992`. -/
def lenV : E := LeanIsa.cellOfBits (BitVec.ofNat 128 4992)
/-- The jump target / exponent constant `g ^ t` as a word. -/
def tgtV (t : ℕ) : E := ofK (gpow t)
/-- The tie word: `e` at in-cell bit offset `p`. -/
def vV (p e : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 (e <<< p))

theorem isInK_oneV : IsInK oneV := isInK_ofLimbs 1

theorem oneV_ne_zero : oneV ≠ 0 := fun h =>
  (by decide : (1 : K) ≠ 0) ((ofLimbs_eq_zero_iff 1).mp h)

theorem oneV_eq_ofK : oneV = ofK 1 := (ofK_eq_ofLimbs 1).symm

theorem oneV_eq_cellOfBits : oneV = LeanIsa.cellOfBits 1 := by
  unfold oneV LeanIsa.cellOfBits; congr 1

theorem cellBits_oneV : LeanIsa.cellBits oneV = 1 := by
  rw [oneV_eq_cellOfBits, LeanIsa.cellBits_cellOfBits]

theorem posV_one : posV 1 = oneV := by
  rw [oneV_eq_cellOfBits]; rfl

theorem vV_zero (e : ℕ) : vV 0 e = posV e := by
  unfold vV posV; rw [Nat.shiftLeft_zero]

/-! ## Cell-level instructions -/

/-- An instruction over cell indices; `toInstr` turns cell `c` into the operand `op c`. -/
inductive CInstr
  /-- `[c] = [a] + [b]`. -/
  | xor (a b c : ℕ)
  /-- `[c] = [a] · [b]`. -/
  | mul (a b c : ℕ)
  /-- `[a] = v`. -/
  | setc (a : ℕ) (v : E)
  /-- `BLAKE2S` on message cells `m0..m3`, chaining pair at `cv, cv + 1`, output pair at
  `out, out + 1`, metadata `md`. -/
  | blake (m0 m1 m2 m3 cv out md : ℕ)
  /-- `JUMP` with condition `a`, target pc `b`, target fp `c`. -/
  | jump (a b c : ℕ)
  /-- The trap `Instr.xor 0 0 0`, which always fails (it reads address `0`). -/
  | pad

namespace CInstr

/-- The ISA instruction, in frame `fp = 1`. -/
def toInstr : CInstr → Instr
  | .xor a b c => .xor (op a) (op b) (op c)
  | .mul a b c => .mulNative (op a) (op b) (op c)
  | .setc a v => .setConstant (op a) v
  | .blake m0 m1 m2 m3 cv out md =>
      .blake2s ![op m0, op m1, op m2, op m3] (op cv) (op out) (op md)
  | .jump a b c => .jump (op a) (op b) (op c)
  | .pad => .xor 0 0 0

/-- Every cell the instruction reads is below `B`. -/
def Bounded (B : ℕ) : CInstr → Prop
  | .xor a b c => a < B ∧ b < B ∧ c < B
  | .mul a b c => a < B ∧ b < B ∧ c < B
  | .setc a _ => a < B
  | .blake m0 m1 m2 m3 cv out md =>
      m0 < B ∧ m1 < B ∧ m2 < B ∧ m3 < B ∧ cv + 1 < B ∧ out + 1 < B ∧ md < B
  | .jump a b c => a < B ∧ b < B ∧ c < B
  | .pad => True

/-- Cycles charged: ten for `BLAKE2S`, one otherwise. -/
def cost : CInstr → ℕ
  | .blake .. => 10
  | _ => 1

def isJump : CInstr → Bool
  | .jump .. => true
  | _ => false

/-- Every `JUMP` has frame operand `oneCell`. -/
def JumpOne : CInstr → Prop
  | .jump _ _ c => c = oneCell
  | _ => True

theorem Bounded.mono {B B' : ℕ} {ci : CInstr} (h : ci.Bounded B) (hB : B ≤ B') :
    ci.Bounded B' := by
  cases ci <;> simp only [Bounded] at h ⊢ <;> omega

theorem weight_toInstr (ci : CInstr) : LeanIsa.weight ci.toInstr.opcode = ci.cost := by
  cases ci <;> rfl

end CInstr

/-! ## Layout constants -/

/-- Unary nodes of the Rice dispatch of chain `k`: one per group but the last. -/
def nU (k : ℕ) : ℕ := if k = 0 then 7 else 63
/-- Leaves of Rice chain `k`: chain 0 carries the 4-bit top digit. -/
def nLeaves (k : ℕ) : ℕ := if k = 0 then 16 else 128
/-- Slots of the Rice dispatch of chain `k`: `nU k` unary nodes of 18 slots, then the last
group of 16. -/
def dispLen (k : ℕ) : ℕ := 18 * nU k + 16
/-- Base slot of chain `k`'s segment (`k ≤ 37`), and of chain 38's dispatch. -/
def rBase (k : ℕ) : ℕ := if k = 0 then 129 else if k ≤ 37 then 397 + 1276 * (k - 1) else 46716
/-- Body step `j` of chain `k` sits at `s0 k + j` (`1 ≤ j ≤ 126`). -/
def s0 (k : ℕ) : ℕ :=
  if k = 0 then 270 else if k < 37 then rBase k + 1149 else if k = 37 then 46589 else 65368
/-- Entry slot of group `q` of a Rice chain. -/
def gBase (k q : ℕ) : ℕ := if q < nU k then rBase k + 18 * q + 2 else rBase k + 18 * nU k
/-- First slot of leaf `e` of a Rice chain. -/
def leafSlot (k e : ℕ) : ℕ := gBase k (e / 2) + 2 + 7 * (e % 2)
/-- First slot of leaf `c` of chain 37. -/
def leafSlotHi (c : ℕ) : ℕ := if 1 ≤ c then rBase 37 + 7 * (36 - c) + 2 else rBase 37 + 252
/-- First root absorption. -/
def rootBase : ℕ := 65495
/-- The pk `XOR`. -/
def pkSlot : ℕ := 65534
/-- The sentinel slot `2 ^ 16 - 1`. -/
def sentinel : ℕ := 65535
/-- The checksum exponent: `Σ_{k<37} (s0 k + 1) + (s0 38 + 1) + 4699`. -/
def K0 : ℕ := (∑ k ∈ Finset.range 37, (s0 k + 1)) + (s0 38 + 1) + 4699

theorem nU_zero : nU 0 = 7 := rfl
theorem nU_of {k : ℕ} (hk : k ≠ 0) : nU k = 63 := if_neg hk
theorem nU_le (k : ℕ) : nU k ≤ 63 := by unfold nU; split_ifs <;> omega
theorem nLeaves_zero : nLeaves 0 = 16 := rfl
theorem nLeaves_of {k : ℕ} (hk : k ≠ 0) : nLeaves k = 128 := if_neg hk
theorem nLeaves_eq (k : ℕ) : nLeaves k = 2 * nU k + 2 := by
  unfold nLeaves nU; split_ifs <;> rfl
theorem nLeaves_le (k : ℕ) : nLeaves k ≤ 128 := by unfold nLeaves; split_ifs <;> omega
theorem dispLen_zero : dispLen 0 = 142 := rfl
theorem dispLen_of {k : ℕ} (hk : k ≠ 0) : dispLen k = 1150 := by
  unfold dispLen; rw [nU_of hk]
theorem rBase_zero : rBase 0 = 129 := rfl
theorem rBase_of_mid {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 37) : rBase k = 397 + 1276 * (k - 1) := by
  unfold rBase; rw [if_neg (by omega), if_pos h2]
theorem rBase_37 : rBase 37 = 46333 := rfl
theorem rBase_38 : rBase 38 = 46716 := rfl
theorem s0_zero : s0 0 = 270 := rfl
theorem s0_of_mid {k : ℕ} (h1 : 1 ≤ k) (h2 : k < 37) : s0 k = 397 + 1276 * (k - 1) + 1149 := by
  unfold s0; rw [if_neg (by omega), if_pos h2, rBase_of_mid h1 (by omega)]
theorem s0_37 : s0 37 = 46589 := rfl
theorem s0_38 : s0 38 = 65368 := rfl
/-- A Rice chain's body starts right after its dispatch. -/
theorem s0_rice {k : ℕ} (hk : k < 37) : s0 k + 1 = rBase k + dispLen k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · rfl
  · rw [s0_of_mid h hk, rBase_of_mid h (by omega), dispLen_of (by omega)]
theorem s0_add_127 {k : ℕ} (hk : k ≤ 37) : s0 k + 127 = rBase (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · rfl
  rcases Nat.lt_or_ge k 37 with h' | h'
  · rw [s0_of_mid h h', rBase_of_mid (by omega) (by omega)]; omega
  · obtain rfl : k = 37 := by omega
    rfl
theorem s0_38_add_127 : s0 38 + 127 = rootBase := rfl
theorem rootBase_add_39 : rootBase + 39 = pkSlot := rfl
theorem pkSlot_add_one : pkSlot + 1 = sentinel := rfl
theorem sentinel_eq : sentinel = 2 ^ 16 - 1 := rfl
theorem gBase_of_lt {k q : ℕ} (hq : q < nU k) : gBase k q = rBase k + 18 * q + 2 := if_pos hq
theorem gBase_last (k : ℕ) : gBase k (nU k) = rBase k + 18 * nU k := if_neg (lt_irrefl _)
theorem leafSlot_eq {k q b : ℕ} (hb : b < 2) : leafSlot k (2 * q + b) = gBase k q + 2 + 7 * b := by
  unfold leafSlot
  rw [show (2 * q + b) / 2 = q by omega, show (2 * q + b) % 2 = b by omega]
theorem leafSlotHi_of_node {i : ℕ} (hi : i < 36) : leafSlotHi (36 - i) = rBase 37 + 7 * i + 2 := by
  unfold leafSlotHi; rw [if_pos (by omega), show 36 - (36 - i) = i by omega]
theorem leafSlotHi_zero : leafSlotHi 0 = rBase 37 + 252 := rfl
theorem leafSlotHi_of_pos {c : ℕ} (hc : 1 ≤ c) : leafSlotHi c = rBase 37 + 7 * (36 - c) + 2 :=
  if_pos hc

theorem K0_eq : K0 = 929911 := by decide

/-! ## Builders -/

/-- Slots `0..128`: the position constants, the checksum target and the length. -/
def constInstr (s : ℕ) : CInstr :=
  if s < 127 then .setc (posCell (s + 1)) (posV (s + 1))
  else if s = 127 then .setc k0Cell (tgtV K0)
  else .setc lenCell lenV

/-- Number of tie ops of chain `k`'s leaves. -/
def tieLen (k : ℕ) : ℕ := if k = 0 ∨ k = 36 then 1 else if k < 36 then 2 else 0

/-- Tie op `i` of leaf `e` of chain `k < 37`. XOR is addition in `E`: the accumulators sum the
digits' words, chain 18 closes cell 2 with the high 5 bits of its digit and opens cell 1 with
the low 2, and chain 36 closes cell 1. -/
def tieOp (k e i : ℕ) : CInstr :=
  if k = 0 then .setc (accCell 0) (vV (tieShift 0) e)
  else if k = 18 then
    if i = 0 then .xor (accCell 17) (posCell (e / 4)) 2 else .setc (accCell 18) (vV 126 (e % 4))
  else if k = 36 then .xor (accCell 35) (posCell e) 1
  else if i = 0 then .setc (fCell k) (vV (tieShift k) e)
  else .xor (accCell (k - 1)) (fCell k) (accCell k)

/-- Core op `i` of leaf `e` of chain `k` (`.pad` past the end). -/
def coreOp (k e i : ℕ) : CInstr :=
  if e < 127 then
    if i = 0 then .blake (sigCell k) (posCell k) (posCell e) zCell zCell (xCell k (e + 1)) oneCell
    else if i = 1 then .mul (gPrev k) (tCell k) (gOut k)
    else if i = 2 then .setc (tCell k) (tgtV (s0 k + e + 1))
    else if i = 3 then .jump oneCell (tCell k) oneCell
    else .pad
  else
    if i = 0 then .xor (sigCell k) zCell (xCell k 127)
    else if i = 1 then .setc (tCell k) (tgtV (s0 k + 128))
    else if i = 2 then .mul (gPrev k) (tCell k) (gOut k)
    else if i = 3 then .setc (vCell k) (tgtV (s0 k + 127))
    else if i = 4 then .jump oneCell (vCell k) oneCell
    else .pad

/-- Op `i` of leaf `e` of a Rice chain `k`: the tie ops, then the core ops. -/
def leafOp (k e i : ℕ) : CInstr :=
  if i < tieLen k then tieOp k e i else coreOp k e (i - tieLen k)

/-- Slot `t < 16` of group `q`: the node, then leaves `2q` and `2q + 1` of 7 slots each. -/
def groupInstr (k q t : ℕ) : CInstr :=
  if t = 0 then .setc (tbCell k) (tgtV (gBase k q + 9))
  else if t = 1 then .jump (zbCell k) (tbCell k) oneCell
  else leafOp k (2 * q + (t - 2) / 7) ((t - 2) % 7)

/-- Slot `o < dispLen k` of the Rice dispatch of chain `k`. -/
def riceInstr (k o : ℕ) : CInstr :=
  if o < 18 * nU k then
    if o % 18 = 0 then .setc (tuCell k (o / 18)) (tgtV (rBase k + 18 * (o / 18 + 1)))
    else if o % 18 = 1 then .jump (zuCell k (o / 18)) (tuCell k (o / 18)) oneCell
    else groupInstr k (o / 18) (o % 18 - 2)
  else groupInstr k (nU k) (o - 18 * nU k)

/-- Body step `j` of chain `k`. -/
def bodyInstr (k j : ℕ) : CInstr :=
  .blake (xCell k j) (posCell k) (posCell j) zCell zCell (xCell k (j + 1)) oneCell

/-- Slot `o < dispLen k + 126` of chain `k < 37`. -/
def chainInstr (k o : ℕ) : CInstr :=
  if o < dispLen k then riceInstr k o else bodyInstr k (o + 1 - dispLen k)

/-- Op `i` of leaf `c` of chain 37. -/
def hiLeafOp (c i : ℕ) : CInstr :=
  if i = 0 then .blake (sigCell 37) (posCell 37) (posCell c) zCell zCell (xCell 37 (c + 1)) oneCell
  else if i = 1 then .setc uCell (tgtV (128 * c))
  else if i = 2 then .mul (gCell 36) uCell (gCell 37)
  else if i = 3 then .setc (tCell 37) (tgtV (s0 37 + c + 1))
  else if i = 4 then .jump oneCell (tCell 37) oneCell
  else .pad

/-- Slot `o < 383` of chain 37: unary nodes and leaves `c ≥ 1`, leaf 0, then the body. -/
def hiInstr (o : ℕ) : CInstr :=
  if o < 252 then
    if o % 7 = 0 then .setc (tuCell 37 (o / 7)) (tgtV (rBase 37 + 7 * (o / 7 + 1)))
    else if o % 7 = 1 then .jump (zuCell 37 (o / 7)) (tuCell 37 (o / 7)) oneCell
    else hiLeafOp (36 - o / 7) (o % 7 - 2)
  else if o < 257 then hiLeafOp 0 (o - 252)
  else bodyInstr 37 (o - 256)

/-- Root absorption `t < 39`. -/
def rootInstr (t : ℕ) : CInstr :=
  .blake (xCell t 127) zCell zCell zCell (rootStateCell t) (rootStateCell (t + 1))
    (posCell (40 - t))

/-- The pk check. -/
def pkInstr : CInstr := .xor (rootStateCell 39) zCell pkCell

/-- The cell-level instruction at slot `s`, decoded by segment. -/
def cinstrAt (s : ℕ) : CInstr :=
  if s < 129 then constInstr s
  else if s < 397 then chainInstr 0 (s - 129)
  else if s < 46333 then chainInstr ((s - 397) / 1276 + 1) ((s - 397) % 1276)
  else if s < 46716 then hiInstr (s - 46333)
  else if s < 47866 then riceInstr 38 (s - 46716)
  else if s < 65369 then .pad
  else if s < 65495 then bodyInstr 38 (s - 65368)
  else if s < 65534 then rootInstr (s - 65495)
  else if s = 65534 then pkInstr
  else .pad

/-- The ISA instruction at slot `s`. -/
abbrev instrAt (s : ℕ) : Instr := (cinstrAt s).toInstr

/-- The bytecode: `2 ^ 16` slots. -/
def program : Program where
  logSize := 16
  logSize_le := by decide
  code i := (cinstrAt i).toInstr

/- The if-chain builders are irreducible: elaborating a lemma whose conclusion is a predicate
defined by `match` on an instruction (`Bounded`, `JumpOne`, a relation) makes the app elaborator
`whnf` that conclusion, and unfolding a builder at an argument such as `o - 1150` then unfolds
`Nat.sub` by structural recursion and exhausts `maxRecDepth`. Use the decode and shape lemmas
(or `unfold`) instead of definitional unfolding. -/
attribute [irreducible] constInstr tieOp coreOp leafOp groupInstr riceInstr chainInstr
  hiLeafOp hiInstr cinstrAt

/-! ## Cost closed forms -/

/-- Dispatch nodes on the path to leaf `e` of Rice chain `k`. -/
def riceDepth (k e : ℕ) : ℕ := if e / 2 < nU k then e / 2 + 2 else nU k + 1
/-- Dispatch nodes on the path to leaf `c` of chain 37. -/
def hiDepth (c : ℕ) : ℕ := if c = 0 then 36 else 37 - c
/-- Number of ops of leaf `e` of chain `k`. -/
def leafLen (k e : ℕ) : ℕ := tieLen k + if e < 127 then 4 else 5
/-- Cycles of leaf `e` of chain `k`. -/
def leafCost (k e : ℕ) : ℕ := tieLen k + if e < 127 then 13 else 5
/-- Body steps after leaf `e`. -/
def bodyLen (e : ℕ) : ℕ := 126 - e
def chainSteps (k e : ℕ) : ℕ := 2 * riceDepth k e + leafLen k e + bodyLen e
def chainCost (k e : ℕ) : ℕ := 2 * riceDepth k e + leafCost k e + 10 * bodyLen e
def hiSteps (c : ℕ) : ℕ := 2 * hiDepth c + 5 + (126 - c)
def hiCost (c : ℕ) : ℕ := 2 * hiDepth c + 14 + 10 * (126 - c)

/-- Steps of the walk with leaf vector `E`: constants, the 37 message chains, `c_hi`, `c_lo`, and
the 39 absorptions plus the pk check. -/
def totalSteps (E : ℕ → ℕ) : ℕ :=
  129 + (∑ k ∈ Finset.range 37, chainSteps k (E k)) + hiSteps (E 37) + chainSteps 38 (E 38) + 40

/-- Cost of the walk with leaf vector `E`. -/
def totalCost (E : ℕ → ℕ) : ℕ :=
  129 + (∑ k ∈ Finset.range 37, chainCost k (E k)) + hiCost (E 37) + chainCost 38 (E 38) + 391

/-- The claimed score: `boundaryCycles + 49215`. -/
def claim : ℕ := LeanIsa.boundaryCycles + 49215

theorem claim_eq : claim = 49335 := rfl

theorem chainCost_bound (k : ℕ) {e : ℕ} (he : e < 128) :
    chainCost k e + 9 * e ≤ 1277 + tieLen k := by
  unfold chainCost riceDepth leafCost bodyLen nU
  split_ifs <;> omega

theorem hiCost_bound {c : ℕ} (hc : c ≤ 36) : hiCost c + 12 * c ≤ 1348 := by
  unfold hiCost hiDepth
  split_ifs <;> omega

theorem tieLen_cases (k : ℕ) : tieLen k = 0 ∨ tieLen k = 1 ∨ tieLen k = 2 := by
  unfold tieLen; split_ifs <;> simp

theorem tieLen_of_ge {k : ℕ} (hk : 37 ≤ k) : tieLen k = 0 := by
  unfold tieLen; rw [if_neg (by omega), if_neg (by omega)]
theorem tieLen_one {k : ℕ} (hk : k = 0 ∨ k = 36) : tieLen k = 1 := if_pos hk
theorem tieLen_two {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 35) : tieLen k = 2 := by
  unfold tieLen; rw [if_neg (by omega), if_pos (by omega)]
theorem tieLen_le (k : ℕ) : tieLen k ≤ 2 := by
  rcases tieLen_cases k with h | h | h <;> omega
theorem tieLen_sum : ∑ k ∈ Finset.range 37, tieLen k = 72 := by decide
theorem leafLen_le (k e : ℕ) : leafLen k e ≤ 7 := by
  have := tieLen_le k
  unfold leafLen; split_ifs <;> omega
theorem leafLen_ge (k e : ℕ) : 4 ≤ leafLen k e := by
  unfold leafLen; split_ifs <;> omega

/-! ## Global facts -/

theorem program_logSize : program.logSize = 16 := rfl

theorem finalPc_eq : program.finalPc = gpow (2 ^ 16 - 1) := rfl

theorem fetch_eq {k : ℕ} (hk : k < 2 ^ 16) : program.fetch (gpow k) = some (instrAt k) :=
  program.fetch_gpow ⟨k, hk⟩

/-- Below the sentinel, a slot address is never the final counter. -/
theorem gpow_ne_finalPc {k : ℕ} (hk : k < 65535) : gpow k ≠ program.finalPc := by
  intro h
  have h' : gpow k = gpow 65535 := h
  have hk64 : k < 2 ^ 64 - 1 := lt_of_lt_of_le hk (by norm_num)
  have h64 : (65535 : ℕ) < 2 ^ 64 - 1 := by norm_num
  have hkk : k = 65535 := gpow_injOn hk64 h64 h'
  omega

theorem seeded : 2 ^ 16 + 2 ^ 16 < LeanIsa.maxSeededRows := by
  norm_num [LeanIsa.maxSeededRows]

/-! ## Segment decoding -/

theorem cinstrAt_const_seg {s : ℕ} (h : s < 129) : cinstrAt s = constInstr s := by
  unfold cinstrAt; rw [if_pos h]

theorem cinstrAt_chain0_seg {s : ℕ} (h1 : 129 ≤ s) (h2 : s < 397) :
    cinstrAt s = chainInstr 0 (s - 129) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 129 by omega), if_pos h2]

theorem cinstrAt_chain_seg {s : ℕ} (h1 : 397 ≤ s) (h2 : s < 46333) :
    cinstrAt s = chainInstr ((s - 397) / 1276 + 1) ((s - 397) % 1276) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 129 by omega), if_neg (show ¬ s < 397 by omega), if_pos h2]

theorem cinstrAt_hi_seg {s : ℕ} (h1 : 46333 ≤ s) (h2 : s < 46716) :
    cinstrAt s = hiInstr (s - 46333) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 129 by omega), if_neg (show ¬ s < 397 by omega),
    if_neg (show ¬ s < 46333 by omega), if_pos h2]

theorem cinstrAt_rice38_seg {s : ℕ} (h1 : 46716 ≤ s) (h2 : s < 47866) :
    cinstrAt s = riceInstr 38 (s - 46716) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 129 by omega), if_neg (show ¬ s < 397 by omega),
    if_neg (show ¬ s < 46333 by omega), if_neg (show ¬ s < 46716 by omega), if_pos h2]

theorem cinstrAt_gap {s : ℕ} (h1 : 47866 ≤ s) (h2 : s < 65369) : cinstrAt s = .pad := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 129 by omega), if_neg (show ¬ s < 397 by omega),
    if_neg (show ¬ s < 46333 by omega), if_neg (show ¬ s < 46716 by omega),
    if_neg (show ¬ s < 47866 by omega), if_pos h2]

theorem cinstrAt_body38_seg {s : ℕ} (h1 : 65369 ≤ s) (h2 : s < 65495) :
    cinstrAt s = bodyInstr 38 (s - 65368) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 129 by omega), if_neg (show ¬ s < 397 by omega),
    if_neg (show ¬ s < 46333 by omega), if_neg (show ¬ s < 46716 by omega),
    if_neg (show ¬ s < 47866 by omega), if_neg (show ¬ s < 65369 by omega), if_pos h2]

theorem cinstrAt_root_seg {s : ℕ} (h1 : 65495 ≤ s) (h2 : s < 65534) :
    cinstrAt s = rootInstr (s - 65495) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 129 by omega), if_neg (show ¬ s < 397 by omega),
    if_neg (show ¬ s < 46333 by omega), if_neg (show ¬ s < 46716 by omega),
    if_neg (show ¬ s < 47866 by omega), if_neg (show ¬ s < 65369 by omega),
    if_neg (show ¬ s < 65495 by omega), if_pos h2]

theorem cinstrAt_pk : cinstrAt pkSlot = pkInstr := by with_unfolding_all rfl

theorem cinstrAt_sentinel : cinstrAt sentinel = .pad := by with_unfolding_all rfl

theorem valid : LeanIsa.BytecodeValid program := by
  refine ⟨by decide, ?_⟩
  show (cinstrAt (2 ^ 16 - 1)).toInstr.opcode ≠ .jump
  rw [show (2 ^ 16 - 1 : ℕ) = sentinel from rfl, cinstrAt_sentinel]
  intro h; cases h

/-! ## Decode lemmas -/

theorem cinstrAt_const {s : ℕ} (hs : s < 127) :
    cinstrAt s = .setc (posCell (s + 1)) (posV (s + 1)) := by
  rw [cinstrAt_const_seg (by omega)]; unfold constInstr; rw [if_pos hs]

theorem cinstrAt_k0 : cinstrAt 127 = .setc k0Cell (tgtV K0) := by with_unfolding_all rfl

theorem cinstrAt_len : cinstrAt 128 = .setc lenCell lenV := by with_unfolding_all rfl

/-- The Rice dispatch of chain `k ∈ {0..36, 38}`. -/
theorem cinstrAt_rice {k o : ℕ} (hk : k < 37 ∨ k = 38) (ho : o < dispLen k) :
    cinstrAt (rBase k + o) = riceInstr k o := by
  rcases hk with hk | rfl
  · rcases Nat.eq_zero_or_pos k with rfl | h0
    · rw [dispLen_zero] at ho
      rw [rBase_zero, cinstrAt_chain0_seg (by omega) (by omega),
        show 129 + o - 129 = o by omega]
      unfold chainInstr; rw [if_pos (by rw [dispLen_zero]; exact ho)]
    · have ho' := ho
      rw [dispLen_of (by omega)] at ho'
      rw [rBase_of_mid h0 (by omega), cinstrAt_chain_seg (by omega) (by omega),
        show (397 + 1276 * (k - 1) + o - 397) / 1276 + 1 = k by omega,
        show (397 + 1276 * (k - 1) + o - 397) % 1276 = o by omega]
      unfold chainInstr; rw [if_pos ho]
  · rw [dispLen_of (by omega)] at ho
    rw [rBase_38, cinstrAt_rice38_seg (by omega) (by omega), show 46716 + o - 46716 = o by omega]

theorem dispLen_eq (k : ℕ) : dispLen k = 18 * nU k + 16 := rfl

theorem cinstrAt_uset {k i : ℕ} (hk : k < 37 ∨ k = 38) (hi : i < nU k) :
    cinstrAt (rBase k + 18 * i) = .setc (tuCell k i) (tgtV (rBase k + 18 * (i + 1))) := by
  rw [cinstrAt_rice hk (by rw [dispLen_eq]; omega)]
  unfold riceInstr
  rw [if_pos (by omega), if_pos (by omega), show 18 * i / 18 = i by omega]

theorem cinstrAt_ujmp {k i : ℕ} (hk : k < 37 ∨ k = 38) (hi : i < nU k) :
    cinstrAt (rBase k + 18 * i + 1) = .jump (zuCell k i) (tuCell k i) oneCell := by
  rw [Nat.add_assoc, cinstrAt_rice hk (by rw [dispLen_eq]; omega)]
  unfold riceInstr
  rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), show (18 * i + 1) / 18 = i by omega]

/-- Slot `t < 16` of group `q ≤ nU k`. -/
theorem cinstrAt_group {k q t : ℕ} (hk : k < 37 ∨ k = 38) (hq : q ≤ nU k) (ht : t < 16) :
    cinstrAt (gBase k q + t) = groupInstr k q t := by
  rcases Nat.lt_or_ge q (nU k) with hq' | hq'
  · rw [gBase_of_lt hq', show rBase k + 18 * q + 2 + t = rBase k + (18 * q + 2 + t) by omega,
      cinstrAt_rice hk (by rw [dispLen_eq]; omega)]
    unfold riceInstr
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
      show (18 * q + 2 + t) / 18 = q by omega, show (18 * q + 2 + t) % 18 - 2 = t by omega]
  · obtain rfl : q = nU k := by omega
    rw [gBase_last, Nat.add_assoc, cinstrAt_rice hk (by rw [dispLen_eq]; omega)]
    unfold riceInstr
    rw [if_neg (by omega), show 18 * nU k + t - 18 * nU k = t by omega]

theorem cinstrAt_gset {k q : ℕ} (hk : k < 37 ∨ k = 38) (hq : q ≤ nU k) :
    cinstrAt (gBase k q) = .setc (tbCell k) (tgtV (gBase k q + 9)) := by
  have h := cinstrAt_group hk hq (t := 0) (by omega)
  rw [Nat.add_zero] at h
  rw [h]; unfold groupInstr; rw [if_pos rfl]

theorem cinstrAt_gjmp {k q : ℕ} (hk : k < 37 ∨ k = 38) (hq : q ≤ nU k) :
    cinstrAt (gBase k q + 1) = .jump (zbCell k) (tbCell k) oneCell := by
  rw [cinstrAt_group hk hq (by omega)]; unfold groupInstr; rw [if_neg (by omega), if_pos rfl]

/-- Op `i` of leaf `e` of a Rice chain. -/
theorem cinstrAt_leaf {k e i : ℕ} (hk : k < 37 ∨ k = 38) (he : e < nLeaves k) (hi : i < 7) :
    cinstrAt (leafSlot k e + i) = leafOp k e i := by
  rw [nLeaves_eq] at he
  unfold leafSlot
  rw [show gBase k (e / 2) + 2 + 7 * (e % 2) + i = gBase k (e / 2) + (2 + 7 * (e % 2) + i)
      by omega, cinstrAt_group hk (by omega) (by omega)]
  unfold groupInstr
  rw [if_neg (by omega), if_neg (by omega),
    show 2 * (e / 2) + (2 + 7 * (e % 2) + i - 2) / 7 = e by omega,
    show (2 + 7 * (e % 2) + i - 2) % 7 = i by omega]

theorem cinstrAt_hi {o : ℕ} (ho : o < 383) : cinstrAt (rBase 37 + o) = hiInstr o := by
  rw [rBase_37, cinstrAt_hi_seg (by omega) (by omega), show 46333 + o - 46333 = o by omega]

theorem cinstrAt_hiset {i : ℕ} (hi : i < 36) :
    cinstrAt (rBase 37 + 7 * i) = .setc (tuCell 37 i) (tgtV (rBase 37 + 7 * (i + 1))) := by
  rw [cinstrAt_hi (by omega)]
  unfold hiInstr
  rw [if_pos (by omega), if_pos (by omega), show 7 * i / 7 = i by omega]

theorem cinstrAt_hijmp {i : ℕ} (hi : i < 36) :
    cinstrAt (rBase 37 + 7 * i + 1) = .jump (zuCell 37 i) (tuCell 37 i) oneCell := by
  rw [Nat.add_assoc, cinstrAt_hi (by omega)]
  unfold hiInstr
  rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), show (7 * i + 1) / 7 = i by omega]

theorem cinstrAt_hileaf {c i : ℕ} (hc : c ≤ 36) (hi : i < 5) :
    cinstrAt (leafSlotHi c + i) = hiLeafOp c i := by
  rcases Nat.lt_or_ge c 1 with h0 | h0
  · obtain rfl : c = 0 := by omega
    rw [leafSlotHi_zero, Nat.add_assoc, cinstrAt_hi (by omega)]
    unfold hiInstr
    rw [if_neg (by omega), if_pos (by omega), show 252 + i - 252 = i by omega]
  · rw [leafSlotHi_of_pos h0,
      show rBase 37 + 7 * (36 - c) + 2 + i = rBase 37 + (7 * (36 - c) + 2 + i) by omega,
      cinstrAt_hi (by omega)]
    unfold hiInstr
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
      show 36 - (7 * (36 - c) + 2 + i) / 7 = c by omega,
      show (7 * (36 - c) + 2 + i) % 7 - 2 = i by omega]

theorem cinstrAt_body {k j : ℕ} (hk : k < 39) (hj1 : 1 ≤ j) (hj2 : j ≤ 126) :
    cinstrAt (s0 k + j) = bodyInstr k j := by
  rcases Nat.lt_or_ge k 37 with h | h
  · rcases Nat.eq_zero_or_pos k with rfl | h0
    · rw [s0_zero, cinstrAt_chain0_seg (by omega) (by omega)]
      unfold chainInstr
      rw [dispLen_zero, if_neg (by omega), show 270 + j - 129 + 1 - 142 = j by omega]
    · rw [s0_of_mid h0 h, cinstrAt_chain_seg (by omega) (by omega),
        show (397 + 1276 * (k - 1) + 1149 + j - 397) / 1276 + 1 = k by omega,
        show (397 + 1276 * (k - 1) + 1149 + j - 397) % 1276 = 1149 + j by omega]
      unfold chainInstr
      rw [dispLen_of (by omega), if_neg (by omega), show 1149 + j + 1 - 1150 = j by omega]
  · rcases Nat.lt_or_ge k 38 with h' | h'
    · obtain rfl : k = 37 := by omega
      rw [s0_37, show 46589 + j = rBase 37 + (256 + j) by rw [rBase_37]; omega,
        cinstrAt_hi (by omega)]
      unfold hiInstr
      rw [if_neg (by omega), if_neg (by omega), show 256 + j - 256 = j by omega]
    · obtain rfl : k = 38 := by omega
      rw [s0_38, cinstrAt_body38_seg (by omega) (by omega), show 65368 + j - 65368 = j by omega]

theorem cinstrAt_root {t : ℕ} (ht : t < 39) : cinstrAt (rootBase + t) = rootInstr t := by
  rw [show rootBase = 65495 from rfl, cinstrAt_root_seg (by omega) (by omega),
    show 65495 + t - 65495 = t by omega]

/-! ## Leaf shapes -/

theorem tieOp_isJump (k e i : ℕ) : (tieOp k e i).isJump = false := by
  unfold tieOp; split_ifs <;> rfl

theorem tieOp_cost (k e i : ℕ) : (tieOp k e i).cost = 1 := by
  unfold tieOp; split_ifs <;> rfl

theorem leafOp_tie {k e i : ℕ} (hi : i < tieLen k) : leafOp k e i = tieOp k e i := by
  unfold leafOp; exact if_pos hi

theorem leafOp_core (k e i : ℕ) : leafOp k e (tieLen k + i) = coreOp k e i := by
  unfold leafOp; rw [if_neg (by omega), show tieLen k + i - tieLen k = i by omega]

/-- Chain 0 opens the cell-2 accumulator. -/
theorem leafOp_tie0 (e : ℕ) : leafOp 0 e 0 = .setc (accCell 0) (vV (tieShift 0) e) := by
  rw [leafOp_tie (by rw [tieLen_one (Or.inl rfl)]; omega)]; unfold tieOp; rw [if_pos rfl]

/-- Chain 18, first tie op: closes cell 2 with the high 5 bits of the digit. -/
theorem leafOp_tie18a (e : ℕ) : leafOp 18 e 0 = .xor (accCell 17) (posCell (e / 4)) 2 := by
  rw [leafOp_tie (by rw [tieLen_two (by omega) (by omega)]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_pos rfl, if_pos rfl]

/-- Chain 18, second tie op: opens the cell-1 accumulator with the low 2 bits of the digit. -/
theorem leafOp_tie18b (e : ℕ) : leafOp 18 e 1 = .setc (accCell 18) (vV 126 (e % 4)) := by
  rw [leafOp_tie (by rw [tieLen_two (by omega) (by omega)]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_pos rfl, if_neg (by omega)]

/-- Chain 36 closes cell 1 (its digit sits at offset 0, so the word is `posV e`). -/
theorem leafOp_tie36 (e : ℕ) : leafOp 36 e 0 = .xor (accCell 35) (posCell e) 1 := by
  rw [leafOp_tie (by rw [tieLen_one (Or.inr rfl)]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem leafOp_mid0 {k e : ℕ} (h1 : 1 ≤ k) (h35 : k ≤ 35) (h18 : k ≠ 18) :
    leafOp k e 0 = .setc (fCell k) (vV (tieShift k) e) := by
  rw [leafOp_tie (by rw [tieLen_two h1 h35]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_neg h18, if_neg (by omega), if_pos rfl]

theorem leafOp_mid1 {k e : ℕ} (h1 : 1 ≤ k) (h35 : k ≤ 35) (h18 : k ≠ 18) :
    leafOp k e 1 = .xor (accCell (k - 1)) (fCell k) (accCell k) := by
  rw [leafOp_tie (by rw [tieLen_two h1 h35]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_neg h18, if_neg (by omega), if_neg (by omega)]

theorem coreOp_blake {k e : ℕ} (he : e < 127) :
    coreOp k e 0 =
      .blake (sigCell k) (posCell k) (posCell e) zCell zCell (xCell k (e + 1)) oneCell := by
  unfold coreOp; rw [if_pos he]; rfl

theorem coreOp_mul {k e : ℕ} (he : e < 127) : coreOp k e 1 = .mul (gPrev k) (tCell k) (gOut k) := by
  unfold coreOp; rw [if_pos he]; rfl

theorem coreOp_set {k e : ℕ} (he : e < 127) :
    coreOp k e 2 = .setc (tCell k) (tgtV (s0 k + e + 1)) := by
  unfold coreOp; rw [if_pos he]; rfl

theorem coreOp_jmp {k e : ℕ} (he : e < 127) : coreOp k e 3 = .jump oneCell (tCell k) oneCell := by
  unfold coreOp; rw [if_pos he]; rfl

theorem coreOp127_xor {k e : ℕ} (he : 127 ≤ e) :
    coreOp k e 0 = .xor (sigCell k) zCell (xCell k 127) := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

theorem coreOp127_setT {k e : ℕ} (he : 127 ≤ e) :
    coreOp k e 1 = .setc (tCell k) (tgtV (s0 k + 128)) := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

theorem coreOp127_mul {k e : ℕ} (he : 127 ≤ e) :
    coreOp k e 2 = .mul (gPrev k) (tCell k) (gOut k) := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

theorem coreOp127_setV {k e : ℕ} (he : 127 ≤ e) :
    coreOp k e 3 = .setc (vCell k) (tgtV (s0 k + 127)) := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

theorem coreOp127_jmp {k e : ℕ} (he : 127 ≤ e) :
    coreOp k e 4 = .jump oneCell (vCell k) oneCell := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

/-- The jump cell of leaf `e`. -/
def leafJC (k e : ℕ) : ℕ := if e < 127 then tCell k else vCell k

/-- The last op of every leaf is the unconditional `JUMP` through `leafJC`. -/
theorem leafOp_last (k e : ℕ) : leafOp k e (leafLen k e - 1) = .jump oneCell (leafJC k e) oneCell := by
  unfold leafLen leafJC
  by_cases he : e < 127
  · rw [if_pos he, if_pos he, show tieLen k + 4 - 1 = tieLen k + 3 by omega, leafOp_core,
      coreOp_jmp he]
  · rw [if_neg he, if_neg he, show tieLen k + 5 - 1 = tieLen k + 4 by omega, leafOp_core,
      coreOp127_jmp (by omega)]

/-- The op before the leaf `JUMP` sets its target to `s0 k + min e 126 + 1`. -/
theorem leafOp_setJ (k e : ℕ) :
    leafOp k e (leafLen k e - 2) = .setc (leafJC k e) (tgtV (s0 k + min e 126 + 1)) := by
  unfold leafLen leafJC
  by_cases he : e < 127
  · rw [if_pos he, if_pos he, show tieLen k + 4 - 2 = tieLen k + 2 by omega, leafOp_core,
      coreOp_set he, show min e 126 = e by omega]
  · rw [if_neg he, if_neg he, show tieLen k + 5 - 2 = tieLen k + 3 by omega, leafOp_core,
      coreOp127_setV (by omega), show s0 k + min e 126 + 1 = s0 k + 127 by omega]

theorem coreOp_isJump {k e i : ℕ} (h : i + 1 < if e < 127 then 4 else 5) :
    (coreOp k e i).isJump = false := by
  unfold coreOp; split_ifs at h ⊢ <;> first | rfl | omega

theorem leafOp_isJump {k e i : ℕ} (h : i + 1 < leafLen k e) : (leafOp k e i).isJump = false := by
  unfold leafOp
  split_ifs
  · exact tieOp_isJump k e i
  · unfold leafLen at h
    exact coreOp_isJump (by split_ifs at h ⊢ <;> omega)

theorem coreOp_cost (k e i : ℕ) : (coreOp k e i).cost = if e < 127 ∧ i = 0 then 10 else 1 := by
  unfold coreOp; split_ifs <;> first | rfl | omega

theorem leafOp_cost (k e i : ℕ) : (leafOp k e i).cost = if e < 127 ∧ i = tieLen k then 10 else 1 := by
  unfold leafOp
  split_ifs with hi hc hc
  · omega
  · exact tieOp_cost k e i
  · rw [coreOp_cost, if_pos ⟨hc.1, by omega⟩]
  · rw [coreOp_cost, if_neg (fun h' => hc ⟨h'.1, by omega⟩)]

theorem leafOp_cost_sum (k e : ℕ) :
    ∑ i ∈ Finset.range (leafLen k e), (leafOp k e i).cost = leafCost k e := by
  rw [Finset.sum_congr rfl (fun i _ => leafOp_cost k e i)]
  unfold leafLen leafCost
  rcases tieLen_cases k with h | h | h <;> rw [h] <;> by_cases he : e < 127 <;>
    simp [he, Finset.sum_range_succ]

theorem hiLeafOp_blake (c : ℕ) :
    hiLeafOp c 0 =
      .blake (sigCell 37) (posCell 37) (posCell c) zCell zCell (xCell 37 (c + 1)) oneCell := by
  with_unfolding_all rfl
theorem hiLeafOp_setU (c : ℕ) : hiLeafOp c 1 = .setc uCell (tgtV (128 * c)) := by
  with_unfolding_all rfl
theorem hiLeafOp_mul (c : ℕ) : hiLeafOp c 2 = .mul (gCell 36) uCell (gCell 37) := by
  with_unfolding_all rfl
theorem hiLeafOp_setT (c : ℕ) : hiLeafOp c 3 = .setc (tCell 37) (tgtV (s0 37 + c + 1)) := by
  with_unfolding_all rfl
theorem hiLeafOp_jmp (c : ℕ) : hiLeafOp c 4 = .jump oneCell (tCell 37) oneCell := by
  with_unfolding_all rfl

theorem hiLeafOp_cost_sum (c : ℕ) : ∑ i ∈ Finset.range 5, (hiLeafOp c i).cost = 14 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hiLeafOp_blake, hiLeafOp_setU,
    hiLeafOp_mul, hiLeafOp_setT, hiLeafOp_jmp, CInstr.cost]

theorem bodyInstr_cost (k j : ℕ) : (bodyInstr k j).cost = 10 := rfl
theorem bodyInstr_isJump (k j : ℕ) : (bodyInstr k j).isJump = false := rfl
theorem rootInstr_cost (t : ℕ) : (rootInstr t).cost = 10 := rfl
theorem rootInstr_isJump (t : ℕ) : (rootInstr t).isJump = false := rfl
theorem pkInstr_cost : pkInstr.cost = 1 := rfl

/-! ## Uniform facts over the program -/

section Uniform

set_option maxHeartbeats 1000000

theorem constInstr_bounded (s : ℕ) : (constInstr s).Bounded 65536 := by
  unfold constInstr
  split_ifs <;> simp only [CInstr.Bounded, posCell, zCell, k0Cell, lenCell] <;>
    (try split_ifs) <;> omega

theorem bodyInstr_bounded {k j : ℕ} (hk : k < 39) (hj : j ≤ 127) :
    (bodyInstr k j).Bounded 65536 := by
  simp only [bodyInstr, CInstr.Bounded, xCell, posCell, zCell, oneCell]
  split_ifs <;> omega

theorem tieOp_bounded {k e : ℕ} (hk : k < 37) (he : e < 128) (i : ℕ) :
    (tieOp k e i).Bounded 65536 := by
  unfold tieOp
  split_ifs <;> simp only [CInstr.Bounded, accCell, fCell, posCell, scr, zCell] <;>
    (try split_ifs) <;> omega

theorem coreOp_bounded {k e : ℕ} (hk : k ≤ 38) (he : e < 128) (i : ℕ) :
    (coreOp k e i).Bounded 65536 := by
  unfold coreOp
  split_ifs <;>
    simp only [CInstr.Bounded, sigCell, posCell, zCell, xCell, oneCell, gPrev, gOut, gCell,
      tCell, vCell, k0Cell, scr] <;>
    (try split_ifs) <;> omega

theorem leafOp_bounded {k e : ℕ} (hk : k ≤ 38) (he : e < 128) (i : ℕ) :
    (leafOp k e i).Bounded 65536 := by
  unfold leafOp
  split_ifs with hi
  · have hk' : k < 37 := by
      unfold tieLen at hi; split_ifs at hi <;> omega
    exact tieOp_bounded hk' he i
  · exact coreOp_bounded hk he _

theorem groupInstr_bounded {k q t : ℕ} (hk : k ≤ 38) (hq : q < 64) (ht : t < 16) :
    (groupInstr k q t).Bounded 65536 := by
  unfold groupInstr
  split_ifs
  · simp only [CInstr.Bounded, tbCell, scr]; omega
  · simp only [CInstr.Bounded, tbCell, zbCell, oneCell, scr]; omega
  · exact leafOp_bounded hk (by omega) _

theorem riceInstr_bounded {k o : ℕ} (hk : k ≤ 38) (ho : o < dispLen k) :
    (riceInstr k o).Bounded 65536 := by
  have hn := nU_le k
  rw [dispLen_eq] at ho
  unfold riceInstr
  split_ifs
  · simp only [CInstr.Bounded, tuCell, scr]; omega
  · simp only [CInstr.Bounded, zuCell, tuCell, oneCell, scr]; omega
  · exact groupInstr_bounded hk (by omega) (by omega)
  · exact groupInstr_bounded hk (by omega) (by omega)

theorem chainInstr_bounded {k o : ℕ} (hk : k < 37) (ho : o < dispLen k + 126) :
    (chainInstr k o).Bounded 65536 := by
  unfold chainInstr
  split_ifs with h
  · exact riceInstr_bounded (by omega) h
  · exact bodyInstr_bounded (by omega) (by omega)

theorem hiLeafOp_bounded {c : ℕ} (hc : c ≤ 36) (i : ℕ) : (hiLeafOp c i).Bounded 65536 := by
  unfold hiLeafOp
  split_ifs <;>
    simp only [CInstr.Bounded, sigCell, posCell, zCell, xCell, oneCell, uCell, gCell, tCell,
      scr] <;>
    (try split_ifs) <;> omega

theorem hiInstr_bounded {o : ℕ} (ho : o < 383) : (hiInstr o).Bounded 65536 := by
  unfold hiInstr
  split_ifs
  · simp only [CInstr.Bounded, tuCell, scr]; omega
  · simp only [CInstr.Bounded, zuCell, tuCell, oneCell, scr]; omega
  · exact hiLeafOp_bounded (by omega) _
  · exact hiLeafOp_bounded (by omega) _
  · exact bodyInstr_bounded (by omega) (by omega)

theorem rootInstr_bounded {t : ℕ} (ht : t < 39) : (rootInstr t).Bounded 65536 := by
  simp only [rootInstr, CInstr.Bounded, xCell, zCell, rootStateCell, posCell]
  split_ifs <;> omega

theorem pkInstr_bounded : pkInstr.Bounded 65536 := by
  simp only [pkInstr, CInstr.Bounded, rootStateCell, zCell, pkCell]
  split_ifs <;> omega

/-- Every cell of every instruction is below `2 ^ 16`. -/
theorem cinstrAt_bounded (s : ℕ) : (cinstrAt s).Bounded (2 ^ 16) := by
  rw [show (2 : ℕ) ^ 16 = 65536 by norm_num]
  unfold cinstrAt
  split_ifs
  · exact constInstr_bounded s
  · exact chainInstr_bounded (by omega) (by rw [dispLen_zero]; omega)
  · exact chainInstr_bounded (by omega) (by rw [dispLen_of (by omega)]; omega)
  · exact hiInstr_bounded (by omega)
  · exact riceInstr_bounded (by omega) (by rw [dispLen_of (by omega)]; omega)
  · trivial
  · exact bodyInstr_bounded (by omega) (by omega)
  · exact rootInstr_bounded (by omega)
  · exact pkInstr_bounded
  · trivial

theorem tieOp_jumpOne (k e i : ℕ) : (tieOp k e i).JumpOne := by
  unfold tieOp; split_ifs <;> trivial

theorem coreOp_jumpOne (k e i : ℕ) : (coreOp k e i).JumpOne := by
  unfold coreOp; split_ifs <;> trivial

theorem leafOp_jumpOne (k e i : ℕ) : (leafOp k e i).JumpOne := by
  unfold leafOp; split_ifs
  · exact tieOp_jumpOne k e i
  · exact coreOp_jumpOne k e _

theorem groupInstr_jumpOne (k q t : ℕ) : (groupInstr k q t).JumpOne := by
  unfold groupInstr; split_ifs
  · trivial
  · rfl
  · exact leafOp_jumpOne k _ _

theorem riceInstr_jumpOne (k o : ℕ) : (riceInstr k o).JumpOne := by
  unfold riceInstr; split_ifs
  · trivial
  · rfl
  · exact groupInstr_jumpOne k _ _
  · exact groupInstr_jumpOne k _ _

theorem hiLeafOp_jumpOne (c i : ℕ) : (hiLeafOp c i).JumpOne := by
  unfold hiLeafOp; split_ifs <;> trivial

theorem hiInstr_jumpOne (o : ℕ) : (hiInstr o).JumpOne := by
  unfold hiInstr; split_ifs
  · trivial
  · rfl
  · exact hiLeafOp_jumpOne _ _
  · exact hiLeafOp_jumpOne _ _
  · trivial

theorem chainInstr_jumpOne (k o : ℕ) : (chainInstr k o).JumpOne := by
  unfold chainInstr; split_ifs
  · exact riceInstr_jumpOne _ _
  · trivial

theorem cinstrAt_jumpOne (s : ℕ) : (cinstrAt s).JumpOne := by
  unfold cinstrAt; split_ifs
  · unfold constInstr; split_ifs <;> trivial
  · exact chainInstr_jumpOne _ _
  · exact chainInstr_jumpOne _ _
  · exact hiInstr_jumpOne _
  · exact riceInstr_jumpOne _ _
  all_goals trivial

/-- Every `JUMP` of the program has frame operand `oneCell`. -/
theorem jump_f {s a b c : ℕ} (h : cinstrAt s = .jump a b c) : c = oneCell := by
  have := cinstrAt_jumpOne s
  rw [h] at this
  exact this

end Uniform

end

end OptimalOTS.LeanIsaBaseline.Machine
