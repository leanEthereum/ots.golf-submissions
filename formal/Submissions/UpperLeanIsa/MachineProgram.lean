import OptimalOTS.LeanIsaMachine

/-!
# The leanISA bytecode of the RT ("Rice-tree forced dispatch") Winternitz verifier

Design: `NOTES.md` (§3 memory layout, §4 bytecode layout); its Appendix A
`rt_model.py` is the executable spec, and every layout constant below is pinned to it by a
`rfl`/`decide` lemma.

The program runs in frame `fp = 1`: every operand is `op c = g ^ c` naming cell `c`. It has
`2 ^ 17` slots; slot `s` holds `(cinstrAt s).toInstr`, where `cinstrAt` is decoded
arithmetically by segment (no proof evaluates the program over a range of indices):

* `[0, 255)`: `SET posCell (s+1) := posV (s+1)`; `255`: `SET k0Cell := tgtV K0`;
  `256`: `SET lenCell := lenV` (`constInstr`).
* `[rBase k, rBase k + 3196)`, `k < 32`: chain `k`, the Rice dispatch (`riceInstr`, 2942
  slots), then body steps `j = 1..254` at `s0 k + j` (`chainInstr`).
* `[102529, 103005)`: chain 32 (`c_hi`), unary dispatch and leaves, then its body
  (`c32Instr`).
* `[103005, 105947)`: chain 33 (`c_lo`) Rice dispatch; `[105947, 130782)`: `.pad`;
  `[130782, 131036)`: chain 33 body.
* `[131036, 131070)`: root absorptions (`rootInstr`); `131070`: the pk `XOR` (`pkInstr`), which
  falls through into the sentinel `131071` (`.pad`).
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

/-! ## Cells (§3) -/

/-- The pinned public-key cell. -/
def pkCell : ℕ := 0
/-- The pinned length cell. -/
def lenCell : ℕ := 3
/-- The pinned signature cell of chain `k`. -/
def sigCell (k : ℕ) : ℕ := 4 + k
/-- The zero cell `Z` (pinned, zero once the length is checked); `(Z, Z + 1)` is the zero pair. -/
def zCell : ℕ := 38
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
/-- Condition hint of group depth `j`. -/
def zbCell (k j : ℕ) : ℕ := scr k + 128 + j
/-- Target of group depth `j`. -/
def tbCell (k j : ℕ) : ℕ := scr k + 130 + j
/-- `T_k`: the checksum contribution (and the leaf jump cell when `e < 255`). -/
def tCell (k : ℕ) : ℕ := scr k + 132
/-- `V_k`: the leaf jump cell when `e = 255`. -/
def vCell (k : ℕ) : ℕ := scr k + 133
/-- `G_k`: the running checksum product. -/
def gCell (k : ℕ) : ℕ := scr k + 134
/-- `F_k`: the leaf's tie term. -/
def fCell (k : ℕ) : ℕ := scr k + 135
/-- The tie accumulator; the last cells of the halves are the pinned message cells. -/
def accCell (k : ℕ) : ℕ := if k = 15 then 2 else if k = 31 then 1 else scr k + 136
/-- `U = g ^ (256 c_hi)`. -/
def uCell : ℕ := scr 32 + 137
/-- The previous checksum product. -/
def gPrev (k : ℕ) : ℕ := if k = 0 then oneCell else if k = 33 then gCell 32 else gCell (k - 1)
/-- The checksum product output of chain `k`. -/
def gOut (k : ℕ) : ℕ := if k = 33 then k0Cell else gCell k
/-- Root state pair `S_t` (low cell); `S_0` is the zero pair. -/
def rootStateCell (t : ℕ) : ℕ := if t = 0 then zCell else 7000 + 2 * t
/-- Chain word `x_{k,j}`; `xCell k (j+1) + 1` is the high half `h_{k,j}`. -/
def xCell (k j : ℕ) : ℕ := 8192 + 512 * k + 2 * j
/-- In-cell byte position of the digit of chain `k < 32`. -/
def bytePos (k : ℕ) : ℕ := (31 - k) % 16

theorem posCell_zero : posCell 0 = zCell := rfl
theorem posCell_of_pos {j : ℕ} (hj : j ≠ 0) : posCell j = 100 + j := if_neg hj
theorem posCell_one : posCell 1 = oneCell := rfl
theorem accCell_15 : accCell 15 = 2 := rfl
theorem accCell_31 : accCell 31 = 1 := rfl
theorem accCell_of {k : ℕ} (h15 : k ≠ 15) (h31 : k ≠ 31) : accCell k = scr k + 136 := by
  unfold accCell; rw [if_neg h15, if_neg h31]
theorem uCell_eq : uCell = 6281 := rfl
theorem rootStateCell_zero : rootStateCell 0 = zCell := rfl
theorem rootStateCell_of_pos {t : ℕ} (ht : t ≠ 0) : rootStateCell t = 7000 + 2 * t := if_neg ht
theorem gPrev_zero : gPrev 0 = oneCell := rfl
theorem gPrev_33 : gPrev 33 = gCell 32 := rfl
theorem gPrev_of {k : ℕ} (h0 : k ≠ 0) (h33 : k ≠ 33) : gPrev k = gCell (k - 1) := by
  unfold gPrev; rw [if_neg h0, if_neg h33]
theorem gOut_33 : gOut 33 = k0Cell := rfl
theorem gOut_of {k : ℕ} (h33 : k ≠ 33) : gOut k = gCell k := if_neg h33
theorem xCell_succ_add_one (k j : ℕ) : xCell k (j + 1) + 1 = xCell k j + 3 := by
  unfold xCell; omega
theorem zCell_add_one : zCell + 1 = 39 := rfl

/-! ## Values -/

/-- ONE: the cell `cellOfBits 1`, also the field one (`oneV_eq_cellOfBits`, `oneV_eq_ofK`). -/
def oneV : E := E.ofLimbs 1 0 0
/-- The position / id / metadata constant `j`. -/
def posV (j : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 j)
/-- The checked length `4352`. -/
def lenV : E := LeanIsa.cellOfBits (BitVec.ofNat 128 4352)
/-- The jump target / exponent constant `g ^ t` as a word. -/
def tgtV (t : ℕ) : E := ofK (gpow t)
/-- The tie word: digit `e` at in-cell byte `p`. -/
def vV (p e : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 (e <<< (8 * p)))

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
  unfold vV posV; rw [Nat.mul_zero, Nat.shiftLeft_zero]

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

/-! ## Layout constants (§4) -/

/-- Base slot of chain `k`'s segment (`k ≤ 32`), and of chain 33's dispatch. -/
def rBase (k : ℕ) : ℕ := if k ≤ 32 then 257 + 3196 * k else 103005
/-- Body step `j` of chain `k` sits at `s0 k + j` (`1 ≤ j ≤ 254`). -/
def s0 (k : ℕ) : ℕ := if k < 32 then rBase k + 2941 else if k = 32 then 102750 else 130781
/-- Entry slot of group `q` of a Rice chain. -/
def gBase (k q : ℕ) : ℕ := if q < 63 then rBase k + 46 * q + 2 else rBase k + 2898
/-- First slot of leaf `e` of a Rice chain. -/
def leafSlot (k e : ℕ) : ℕ := gBase k (e / 4) + 11 * (e % 4) + 4
/-- First slot of leaf `c` of chain 32. -/
def leafSlot32 (c : ℕ) : ℕ := if 1 ≤ c then rBase 32 + 7 * (31 - c) + 2 else rBase 32 + 217
/-- First root absorption. -/
def rootBase : ℕ := 131036
/-- The pk `XOR`. -/
def pkSlot : ℕ := 131070
/-- The sentinel slot `2 ^ 17 - 1`. -/
def sentinel : ℕ := 131071
/-- The checksum exponent: `Σ_{k<32} (s0 k + 1) + (s0 33 + 1) + 8160`. -/
def K0 : ℕ := (∑ k ∈ Finset.range 32, (s0 k + 1)) + (s0 33 + 1) + 8160

theorem rBase_of_le {k : ℕ} (hk : k ≤ 32) : rBase k = 257 + 3196 * k := if_pos hk
theorem rBase_32 : rBase 32 = 102529 := rfl
theorem rBase_33 : rBase 33 = 103005 := rfl
theorem s0_of_lt {k : ℕ} (hk : k < 32) : s0 k = 257 + 3196 * k + 2941 := by
  unfold s0; rw [if_pos hk, rBase_of_le (by omega)]
theorem s0_32 : s0 32 = 102750 := rfl
theorem s0_33 : s0 33 = 130781 := rfl
theorem s0_add_255 {k : ℕ} (hk : k ≤ 32) : s0 k + 255 = rBase (k + 1) := by
  rcases Nat.lt_or_ge k 32 with h | h
  · rw [s0_of_lt h, rBase_of_le (by omega)]; omega
  · obtain rfl : k = 32 := by omega
    rfl
theorem s0_33_add_255 : s0 33 + 255 = rootBase := rfl
theorem rootBase_add_34 : rootBase + 34 = pkSlot := rfl
theorem pkSlot_add_one : pkSlot + 1 = sentinel := rfl
theorem sentinel_eq : sentinel = 2 ^ 17 - 1 := rfl
theorem gBase_of_lt {k q : ℕ} (hq : q < 63) : gBase k q = rBase k + 46 * q + 2 := if_pos hq
theorem gBase_63 (k : ℕ) : gBase k 63 = rBase k + 2898 := rfl
/-- Unary node `i`'s taken target is the next node, or group 63 when `i = 62`. -/
theorem unary_next_62 (k : ℕ) : rBase k + 46 * (62 + 1) = gBase k 63 := rfl
theorem leafSlot_eq {k q b : ℕ} (hb : b < 4) : leafSlot k (4 * q + b) = gBase k q + 11 * b + 4 := by
  unfold leafSlot
  rw [show (4 * q + b) / 4 = q by omega, show (4 * q + b) % 4 = b by omega]
theorem leafSlot32_of_node {i : ℕ} (hi : i < 31) : leafSlot32 (31 - i) = rBase 32 + 7 * i + 2 := by
  unfold leafSlot32; rw [if_pos (by omega), show 31 - (31 - i) = i by omega]
theorem leafSlot32_zero : leafSlot32 0 = rBase 32 + 217 := rfl
/-- The last `c_hi` unary node's taken target is leaf 0. -/
theorem u32_next_30 : rBase 32 + 7 * (30 + 1) = leafSlot32 0 := rfl
theorem leafSlot32_of_pos {c : ℕ} (hc : 1 ≤ c) : leafSlot32 c = rBase 32 + 7 * (31 - c) + 2 :=
  if_pos hc

theorem K0_eq : K0 = 1826526 := by decide

/-! ## Builders -/

/-- Slots `0..256`: the position constants, the checksum target and the length. -/
def constInstr (s : ℕ) : CInstr :=
  if s < 255 then .setc (posCell (s + 1)) (posV (s + 1))
  else if s = 255 then .setc k0Cell (tgtV K0)
  else .setc lenCell lenV

/-- Number of tie ops of chain `k`'s leaves. -/
def tieLen (k : ℕ) : ℕ := if 32 ≤ k then 0 else if k % 16 = 0 ∨ k % 16 = 15 then 1 else 2

/-- Tie op `i` of leaf `e` of chain `k < 32`. -/
def tieOp (k e i : ℕ) : CInstr :=
  if k % 16 = 0 then .setc (accCell k) (vV (bytePos k) e)
  else if k % 16 = 15 then .xor (accCell (k - 1)) (posCell e) (accCell k)
  else if i = 0 then .setc (fCell k) (vV (bytePos k) e)
  else .xor (accCell (k - 1)) (fCell k) (accCell k)

/-- Core op `i` of leaf `e` of chain `k` (`.pad` past the end). -/
def coreOp (k e i : ℕ) : CInstr :=
  if e < 255 then
    if i = 0 then .blake (sigCell k) (posCell k) (posCell e) zCell zCell (xCell k (e + 1)) oneCell
    else if i = 1 then .mul (gPrev k) (tCell k) (gOut k)
    else if i = 2 then .setc (tCell k) (tgtV (s0 k + e + 1))
    else if i = 3 then .jump oneCell (tCell k) oneCell
    else .pad
  else
    if i = 0 then .xor (sigCell k) zCell (xCell k 255)
    else if i = 1 then .setc (tCell k) (tgtV (s0 k + 256))
    else if i = 2 then .mul (gPrev k) (tCell k) (gOut k)
    else if i = 3 then .setc (vCell k) (tgtV (s0 k + 255))
    else if i = 4 then .jump oneCell (vCell k) oneCell
    else .pad

/-- Op `i` of leaf `e` of a Rice chain `k`: the tie ops, then the core ops. -/
def leafOp (k e i : ℕ) : CInstr :=
  if i < tieLen k then tieOp k e i else coreOp k e (i - tieLen k)

/-- Node slot `r < 4` of block `b` of group `q` (`.pad` where the block has no node). -/
def groupNode (k q b r : ℕ) : CInstr :=
  if r = 0 ∧ b = 0 then .setc (tbCell k 0) (tgtV (gBase k q + 24))
  else if r = 1 ∧ b = 0 then .jump (zbCell k 0) (tbCell k 0) oneCell
  else if r = 2 ∧ (b = 0 ∨ b = 2) then .setc (tbCell k 1) (tgtV (gBase k q + 11 * (b + 1) + 4))
  else if r = 3 ∧ (b = 0 ∨ b = 2) then .jump (zbCell k 1) (tbCell k 1) oneCell
  else .pad

/-- Slot `t < 44` of group `q`: block `t / 11`, offset `t % 11`. -/
def groupInstr (k q t : ℕ) : CInstr :=
  if t % 11 < 4 then groupNode k q (t / 11) (t % 11) else leafOp k (4 * q + t / 11) (t % 11 - 4)

/-- Slot `o < 2942` of the Rice dispatch of chain `k`. -/
def riceInstr (k o : ℕ) : CInstr :=
  if o < 2898 then
    if o % 46 = 0 then .setc (tuCell k (o / 46)) (tgtV (rBase k + 46 * (o / 46 + 1)))
    else if o % 46 = 1 then .jump (zuCell k (o / 46)) (tuCell k (o / 46)) oneCell
    else groupInstr k (o / 46) (o % 46 - 2)
  else groupInstr k 63 (o - 2898)

/-- Body step `j` of chain `k`. -/
def bodyInstr (k j : ℕ) : CInstr :=
  .blake (xCell k j) (posCell k) (posCell j) zCell zCell (xCell k (j + 1)) oneCell

/-- Slot `o < 3196` of chain `k < 32`. -/
def chainInstr (k o : ℕ) : CInstr :=
  if o < 2942 then riceInstr k o else bodyInstr k (o - 2941)

/-- Op `i` of leaf `c` of chain 32. -/
def leaf32Op (c i : ℕ) : CInstr :=
  if i = 0 then .blake (sigCell 32) (posCell 32) (posCell c) zCell zCell (xCell 32 (c + 1)) oneCell
  else if i = 1 then .setc uCell (tgtV (256 * c))
  else if i = 2 then .mul (gCell 31) uCell (gCell 32)
  else if i = 3 then .setc (tCell 32) (tgtV (s0 32 + c + 1))
  else if i = 4 then .jump oneCell (tCell 32) oneCell
  else .pad

/-- Slot `o < 476` of chain 32: unary nodes and leaves `c ≥ 1`, leaf 0, then the body. -/
def c32Instr (o : ℕ) : CInstr :=
  if o < 217 then
    if o % 7 = 0 then .setc (tuCell 32 (o / 7)) (tgtV (rBase 32 + 7 * (o / 7 + 1)))
    else if o % 7 = 1 then .jump (zuCell 32 (o / 7)) (tuCell 32 (o / 7)) oneCell
    else leaf32Op (31 - o / 7) (o % 7 - 2)
  else if o < 222 then leaf32Op 0 (o - 217)
  else bodyInstr 32 (o - 221)

/-- Root absorption `t < 34`. -/
def rootInstr (t : ℕ) : CInstr :=
  .blake (xCell t 255) zCell zCell zCell (rootStateCell t) (rootStateCell (t + 1))
    (posCell (35 - t))

/-- The pk check. -/
def pkInstr : CInstr := .xor (rootStateCell 34) zCell pkCell

/-- The cell-level instruction at slot `s`, decoded by segment. -/
def cinstrAt (s : ℕ) : CInstr :=
  if s < 257 then constInstr s
  else if s < 102529 then chainInstr ((s - 257) / 3196) ((s - 257) % 3196)
  else if s < 103005 then c32Instr (s - 102529)
  else if s < 105947 then riceInstr 33 (s - 103005)
  else if s < 130782 then .pad
  else if s < 131036 then bodyInstr 33 (s - 130781)
  else if s < 131070 then rootInstr (s - 131036)
  else if s = 131070 then pkInstr
  else .pad

/-- The ISA instruction at slot `s`. -/
abbrev instrAt (s : ℕ) : Instr := (cinstrAt s).toInstr

/-- The bytecode: `2 ^ 17` slots. -/
def program : Program where
  logSize := 17
  logSize_le := by decide
  code i := (cinstrAt i).toInstr

/- The if-chain builders are irreducible: elaborating a lemma whose conclusion is a predicate
defined by `match` on an instruction (`Bounded`, `JumpOne`, a relation) makes the app elaborator
`whnf` that conclusion, and unfolding a builder at an argument such as `o - 2898` then unfolds
`Nat.sub` by structural recursion and exhausts `maxRecDepth`. Use the decode and shape lemmas
(or `unfold`) instead of definitional unfolding. -/
attribute [irreducible] constInstr tieOp coreOp leafOp groupNode groupInstr riceInstr chainInstr
  leaf32Op c32Instr cinstrAt

/-! ## Cost closed forms (§5) -/

/-- Dispatch nodes on the path to leaf `e` of a Rice chain. -/
def riceDepth (e : ℕ) : ℕ := if e / 4 < 63 then e / 4 + 3 else 65
/-- Dispatch nodes on the path to leaf `c` of chain 32. -/
def u32Depth (c : ℕ) : ℕ := if c = 0 then 31 else 32 - c
/-- Number of ops of leaf `e` of chain `k`. -/
def leafLen (k e : ℕ) : ℕ := tieLen k + if e < 255 then 4 else 5
/-- Cycles of leaf `e` of chain `k`. -/
def leafCost (k e : ℕ) : ℕ := tieLen k + if e < 255 then 13 else 5
/-- Body steps after leaf `e`. -/
def bodyLen (e : ℕ) : ℕ := 254 - e
def chainSteps (k e : ℕ) : ℕ := 2 * riceDepth e + leafLen k e + bodyLen e
def chainCost (k e : ℕ) : ℕ := 2 * riceDepth e + leafCost k e + 10 * bodyLen e
def c32Steps (c : ℕ) : ℕ := 2 * u32Depth c + 5 + (254 - c)
def c32Cost (c : ℕ) : ℕ := 2 * u32Depth c + 14 + 10 * (254 - c)
/-- The claimed score: `boundaryCycles + 85223`. -/
def claim : ℕ := LeanIsa.boundaryCycles + 85223

theorem claim_eq : claim = 85343 := rfl

theorem chainCost_bound (k : ℕ) {e : ℕ} (he : e < 256) :
    2 * chainCost k e + 19 * e ≤ 5118 + 2 * tieLen k := by
  unfold chainCost riceDepth leafCost bodyLen
  split_ifs <;> omega

theorem c32Cost_bound {c : ℕ} (hc : c < 32) : c32Cost c + 12 * c ≤ 2618 := by
  unfold c32Cost u32Depth
  split_ifs <;> omega

theorem riceDepth_bound (e : ℕ) : 4 * riceDepth e ≤ 12 + e := by
  unfold riceDepth
  split_ifs <;> omega

theorem tieLen_cases (k : ℕ) : tieLen k = 0 ∨ tieLen k = 1 ∨ tieLen k = 2 := by
  unfold tieLen; split_ifs <;> simp

theorem tieLen_of_ge {k : ℕ} (hk : 32 ≤ k) : tieLen k = 0 := if_pos hk
theorem tieLen_of_zero {k : ℕ} (hk : k < 32) (h : k % 16 = 0) : tieLen k = 1 := by
  unfold tieLen; rw [if_neg (by omega), if_pos (Or.inl h)]
theorem tieLen_of_15 {k : ℕ} (hk : k < 32) (h : k % 16 = 15) : tieLen k = 1 := by
  unfold tieLen; rw [if_neg (by omega), if_pos (Or.inr h)]
theorem tieLen_of_mid {k : ℕ} (hk : k < 32) (h0 : k % 16 ≠ 0) (h15 : k % 16 ≠ 15) :
    tieLen k = 2 := by
  unfold tieLen; rw [if_neg (by omega), if_neg (by omega)]
theorem tieLen_le (k : ℕ) : tieLen k ≤ 2 := by
  rcases tieLen_cases k with h | h | h <;> omega
theorem leafLen_le (k e : ℕ) : leafLen k e ≤ 7 := by
  have := tieLen_le k
  unfold leafLen; split_ifs <;> omega
theorem leafLen_ge (k e : ℕ) : 4 ≤ leafLen k e := by
  unfold leafLen; split_ifs <;> omega

/-! ## Global facts -/

theorem program_logSize : program.logSize = 17 := rfl

theorem finalPc_eq : program.finalPc = gpow (2 ^ 17 - 1) := rfl

theorem fetch_eq {k : ℕ} (hk : k < 2 ^ 17) : program.fetch (gpow k) = some (instrAt k) :=
  program.fetch_gpow ⟨k, hk⟩

/-- Below the sentinel, a slot address is never the final counter. -/
theorem gpow_ne_finalPc {k : ℕ} (hk : k < 131071) : gpow k ≠ program.finalPc := by
  intro h
  have h' : gpow k = gpow 131071 := h
  have hk64 : k < 2 ^ 64 - 1 := lt_of_lt_of_le hk (by norm_num)
  have h64 : (131071 : ℕ) < 2 ^ 64 - 1 := by norm_num
  have hkk : k = 131071 := gpow_injOn hk64 h64 h'
  omega

theorem seeded : 2 ^ 17 + 2 ^ 16 < LeanIsa.maxSeededRows := by
  norm_num [LeanIsa.maxSeededRows]

/-! ## Segment decoding -/

theorem cinstrAt_const_seg {s : ℕ} (h : s < 257) : cinstrAt s = constInstr s := by
  unfold cinstrAt; rw [if_pos h]

theorem cinstrAt_chain_seg {s : ℕ} (h1 : 257 ≤ s) (h2 : s < 102529) :
    cinstrAt s = chainInstr ((s - 257) / 3196) ((s - 257) % 3196) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 257 by omega), if_pos h2]

theorem cinstrAt_c32_seg {s : ℕ} (h1 : 102529 ≤ s) (h2 : s < 103005) :
    cinstrAt s = c32Instr (s - 102529) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 257 by omega), if_neg (show ¬ s < 102529 by omega), if_pos h2]

theorem cinstrAt_rice33_seg {s : ℕ} (h1 : 103005 ≤ s) (h2 : s < 105947) :
    cinstrAt s = riceInstr 33 (s - 103005) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 257 by omega), if_neg (show ¬ s < 102529 by omega),
    if_neg (show ¬ s < 103005 by omega), if_pos h2]

theorem cinstrAt_gap {s : ℕ} (h1 : 105947 ≤ s) (h2 : s < 130782) : cinstrAt s = .pad := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 257 by omega), if_neg (show ¬ s < 102529 by omega),
    if_neg (show ¬ s < 103005 by omega), if_neg (show ¬ s < 105947 by omega), if_pos h2]

theorem cinstrAt_body33_seg {s : ℕ} (h1 : 130782 ≤ s) (h2 : s < 131036) :
    cinstrAt s = bodyInstr 33 (s - 130781) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 257 by omega), if_neg (show ¬ s < 102529 by omega),
    if_neg (show ¬ s < 103005 by omega), if_neg (show ¬ s < 105947 by omega),
    if_neg (show ¬ s < 130782 by omega), if_pos h2]

theorem cinstrAt_root_seg {s : ℕ} (h1 : 131036 ≤ s) (h2 : s < 131070) :
    cinstrAt s = rootInstr (s - 131036) := by
  unfold cinstrAt
  rw [if_neg (show ¬ s < 257 by omega), if_neg (show ¬ s < 102529 by omega),
    if_neg (show ¬ s < 103005 by omega), if_neg (show ¬ s < 105947 by omega),
    if_neg (show ¬ s < 130782 by omega), if_neg (show ¬ s < 131036 by omega), if_pos h2]

theorem cinstrAt_pk : cinstrAt pkSlot = pkInstr := by with_unfolding_all rfl

theorem cinstrAt_sentinel : cinstrAt sentinel = .pad := by with_unfolding_all rfl

theorem valid : LeanIsa.BytecodeValid program := by
  refine ⟨by decide, ?_⟩
  show (cinstrAt (2 ^ 17 - 1)).toInstr.opcode ≠ .jump
  rw [show (2 ^ 17 - 1 : ℕ) = sentinel from rfl, cinstrAt_sentinel]
  intro h; cases h

/-! ## Decode lemmas -/

theorem cinstrAt_const {s : ℕ} (hs : s < 255) :
    cinstrAt s = .setc (posCell (s + 1)) (posV (s + 1)) := by
  rw [cinstrAt_const_seg (by omega)]; unfold constInstr; rw [if_pos hs]

theorem cinstrAt_k0 : cinstrAt 255 = .setc k0Cell (tgtV K0) := by with_unfolding_all rfl

theorem cinstrAt_len : cinstrAt 256 = .setc lenCell lenV := by with_unfolding_all rfl

/-- The Rice dispatch of chain `k ∈ {0..31, 33}`. -/
theorem cinstrAt_rice {k o : ℕ} (hk : k < 32 ∨ k = 33) (ho : o < 2942) :
    cinstrAt (rBase k + o) = riceInstr k o := by
  rcases hk with hk | rfl
  · rw [rBase_of_le (by omega), cinstrAt_chain_seg (by omega) (by omega),
      show (257 + 3196 * k + o - 257) / 3196 = k by omega,
      show (257 + 3196 * k + o - 257) % 3196 = o by omega]
    unfold chainInstr; rw [if_pos ho]
  · rw [rBase_33, cinstrAt_rice33_seg (by omega) (by omega), show 103005 + o - 103005 = o by omega]

theorem cinstrAt_uset {k i : ℕ} (hk : k < 32 ∨ k = 33) (hi : i < 63) :
    cinstrAt (rBase k + 46 * i) = .setc (tuCell k i) (tgtV (rBase k + 46 * (i + 1))) := by
  rw [cinstrAt_rice hk (by omega)]
  unfold riceInstr
  rw [if_pos (by omega), if_pos (by omega), show 46 * i / 46 = i by omega]

theorem cinstrAt_ujmp {k i : ℕ} (hk : k < 32 ∨ k = 33) (hi : i < 63) :
    cinstrAt (rBase k + 46 * i + 1) = .jump (zuCell k i) (tuCell k i) oneCell := by
  rw [Nat.add_assoc, cinstrAt_rice hk (by omega)]
  unfold riceInstr
  rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), show (46 * i + 1) / 46 = i by omega]

/-- Slot `t < 44` of group `q < 64`. -/
theorem cinstrAt_group {k q t : ℕ} (hk : k < 32 ∨ k = 33) (hq : q < 64) (ht : t < 44) :
    cinstrAt (gBase k q + t) = groupInstr k q t := by
  rcases Nat.lt_or_ge q 63 with hq' | hq'
  · rw [gBase_of_lt hq', show rBase k + 46 * q + 2 + t = rBase k + (46 * q + 2 + t) by omega,
      cinstrAt_rice hk (by omega)]
    unfold riceInstr
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
      show (46 * q + 2 + t) / 46 = q by omega, show (46 * q + 2 + t) % 46 - 2 = t by omega]
  · obtain rfl : q = 63 := by omega
    rw [gBase_63, Nat.add_assoc, cinstrAt_rice hk (by omega)]
    unfold riceInstr
    rw [if_neg (by omega), show 2898 + t - 2898 = t by omega]

theorem cinstrAt_g0set {k q : ℕ} (hk : k < 32 ∨ k = 33) (hq : q < 64) :
    cinstrAt (gBase k q) = .setc (tbCell k 0) (tgtV (gBase k q + 24)) := by
  have h := cinstrAt_group hk hq (t := 0) (by omega)
  rw [Nat.add_zero] at h
  rw [h]; with_unfolding_all rfl

theorem cinstrAt_g0jmp {k q : ℕ} (hk : k < 32 ∨ k = 33) (hq : q < 64) :
    cinstrAt (gBase k q + 1) = .jump (zbCell k 0) (tbCell k 0) oneCell := by
  rw [cinstrAt_group hk hq (by omega)]; with_unfolding_all rfl

theorem cinstrAt_g1set {k q b : ℕ} (hk : k < 32 ∨ k = 33) (hq : q < 64) (hb : b = 0 ∨ b = 2) :
    cinstrAt (gBase k q + 11 * b + 2) =
      .setc (tbCell k 1) (tgtV (gBase k q + 11 * (b + 1) + 4)) := by
  rw [Nat.add_assoc, cinstrAt_group hk hq (by omega)]
  rcases hb with rfl | rfl <;> with_unfolding_all rfl

theorem cinstrAt_g1jmp {k q b : ℕ} (hk : k < 32 ∨ k = 33) (hq : q < 64) (hb : b = 0 ∨ b = 2) :
    cinstrAt (gBase k q + 11 * b + 3) = .jump (zbCell k 1) (tbCell k 1) oneCell := by
  rw [Nat.add_assoc, cinstrAt_group hk hq (by omega)]
  rcases hb with rfl | rfl <;> with_unfolding_all rfl

/-- Op `i` of leaf `e` of a Rice chain. -/
theorem cinstrAt_leaf {k e i : ℕ} (hk : k < 32 ∨ k = 33) (he : e < 256) (hi : i < 7) :
    cinstrAt (leafSlot k e + i) = leafOp k e i := by
  unfold leafSlot
  rw [show gBase k (e / 4) + 11 * (e % 4) + 4 + i = gBase k (e / 4) + (11 * (e % 4) + 4 + i)
      by omega, cinstrAt_group hk (by omega) (by omega)]
  unfold groupInstr
  rw [if_neg (by omega), show 4 * (e / 4) + (11 * (e % 4) + 4 + i) / 11 = e by omega,
    show (11 * (e % 4) + 4 + i) % 11 - 4 = i by omega]

theorem cinstrAt_c32 {o : ℕ} (ho : o < 476) : cinstrAt (rBase 32 + o) = c32Instr o := by
  rw [rBase_32, cinstrAt_c32_seg (by omega) (by omega), show 102529 + o - 102529 = o by omega]

theorem cinstrAt_u32set {i : ℕ} (hi : i < 31) :
    cinstrAt (rBase 32 + 7 * i) = .setc (tuCell 32 i) (tgtV (rBase 32 + 7 * (i + 1))) := by
  rw [cinstrAt_c32 (by omega)]
  unfold c32Instr
  rw [if_pos (by omega), if_pos (by omega), show 7 * i / 7 = i by omega]

theorem cinstrAt_u32jmp {i : ℕ} (hi : i < 31) :
    cinstrAt (rBase 32 + 7 * i + 1) = .jump (zuCell 32 i) (tuCell 32 i) oneCell := by
  rw [Nat.add_assoc, cinstrAt_c32 (by omega)]
  unfold c32Instr
  rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), show (7 * i + 1) / 7 = i by omega]

theorem cinstrAt_leaf32 {c i : ℕ} (hc : c < 32) (hi : i < 5) :
    cinstrAt (leafSlot32 c + i) = leaf32Op c i := by
  rcases Nat.lt_or_ge c 1 with h0 | h0
  · obtain rfl : c = 0 := by omega
    rw [leafSlot32_zero, Nat.add_assoc, cinstrAt_c32 (by omega)]
    unfold c32Instr
    rw [if_neg (by omega), if_pos (by omega), show 217 + i - 217 = i by omega]
  · rw [leafSlot32_of_pos h0,
      show rBase 32 + 7 * (31 - c) + 2 + i = rBase 32 + (7 * (31 - c) + 2 + i) by omega,
      cinstrAt_c32 (by omega)]
    unfold c32Instr
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
      show 31 - (7 * (31 - c) + 2 + i) / 7 = c by omega,
      show (7 * (31 - c) + 2 + i) % 7 - 2 = i by omega]

theorem cinstrAt_body {k j : ℕ} (hk : k < 34) (hj1 : 1 ≤ j) (hj2 : j ≤ 254) :
    cinstrAt (s0 k + j) = bodyInstr k j := by
  rcases Nat.lt_or_ge k 32 with h | h
  · rw [s0_of_lt h, cinstrAt_chain_seg (by omega) (by omega),
      show (257 + 3196 * k + 2941 + j - 257) / 3196 = k by omega,
      show (257 + 3196 * k + 2941 + j - 257) % 3196 = 2941 + j by omega]
    unfold chainInstr
    rw [if_neg (by omega), show 2941 + j - 2941 = j by omega]
  · rcases Nat.lt_or_ge k 33 with h' | h'
    · obtain rfl : k = 32 := by omega
      rw [s0_32, show 102750 + j = rBase 32 + (221 + j) by rw [rBase_32]; omega,
        cinstrAt_c32 (by omega)]
      unfold c32Instr
      rw [if_neg (by omega), if_neg (by omega), show 221 + j - 221 = j by omega]
    · obtain rfl : k = 33 := by omega
      rw [s0_33, cinstrAt_body33_seg (by omega) (by omega), show 130781 + j - 130781 = j by omega]

theorem cinstrAt_root {t : ℕ} (ht : t < 34) : cinstrAt (rootBase + t) = rootInstr t := by
  rw [show rootBase = 131036 from rfl, cinstrAt_root_seg (by omega) (by omega),
    show 131036 + t - 131036 = t by omega]

/-! ## Leaf shapes -/

theorem tieOp_isJump (k e i : ℕ) : (tieOp k e i).isJump = false := by
  unfold tieOp; split_ifs <;> rfl

theorem tieOp_cost (k e i : ℕ) : (tieOp k e i).cost = 1 := by
  unfold tieOp; split_ifs <;> rfl

theorem leafOp_tie {k e i : ℕ} (hi : i < tieLen k) : leafOp k e i = tieOp k e i := by
  unfold leafOp; exact if_pos hi

theorem leafOp_core (k e i : ℕ) : leafOp k e (tieLen k + i) = coreOp k e i := by
  unfold leafOp; rw [if_neg (by omega), show tieLen k + i - tieLen k = i by omega]

theorem leafOp_tie0 {k e : ℕ} (hk : k < 32) (h : k % 16 = 0) :
    leafOp k e 0 = .setc (accCell k) (vV (bytePos k) e) := by
  rw [leafOp_tie (by rw [tieLen_of_zero hk h]; omega)]; unfold tieOp; rw [if_pos h]

theorem leafOp_tie15 {k e : ℕ} (hk : k < 32) (h : k % 16 = 15) :
    leafOp k e 0 = .xor (accCell (k - 1)) (posCell e) (accCell k) := by
  rw [leafOp_tie (by rw [tieLen_of_15 hk h]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_pos h]

theorem leafOp_mid0 {k e : ℕ} (hk : k < 32) (h0 : k % 16 ≠ 0) (h15 : k % 16 ≠ 15) :
    leafOp k e 0 = .setc (fCell k) (vV (bytePos k) e) := by
  rw [leafOp_tie (by rw [tieLen_of_mid hk h0 h15]; omega)]
  unfold tieOp; rw [if_neg h0, if_neg h15, if_pos rfl]

theorem leafOp_mid1 {k e : ℕ} (hk : k < 32) (h0 : k % 16 ≠ 0) (h15 : k % 16 ≠ 15) :
    leafOp k e 1 = .xor (accCell (k - 1)) (fCell k) (accCell k) := by
  rw [leafOp_tie (by rw [tieLen_of_mid hk h0 h15]; omega)]
  unfold tieOp; rw [if_neg h0, if_neg h15, if_neg (by omega)]

theorem coreOp_blake {k e : ℕ} (he : e < 255) :
    coreOp k e 0 =
      .blake (sigCell k) (posCell k) (posCell e) zCell zCell (xCell k (e + 1)) oneCell := by
  unfold coreOp; rw [if_pos he]; rfl

theorem coreOp_mul {k e : ℕ} (he : e < 255) : coreOp k e 1 = .mul (gPrev k) (tCell k) (gOut k) := by
  unfold coreOp; rw [if_pos he]; rfl

theorem coreOp_set {k e : ℕ} (he : e < 255) :
    coreOp k e 2 = .setc (tCell k) (tgtV (s0 k + e + 1)) := by
  unfold coreOp; rw [if_pos he]; rfl

theorem coreOp_jmp {k e : ℕ} (he : e < 255) : coreOp k e 3 = .jump oneCell (tCell k) oneCell := by
  unfold coreOp; rw [if_pos he]; rfl

theorem coreOp255_xor {k e : ℕ} (he : 255 ≤ e) :
    coreOp k e 0 = .xor (sigCell k) zCell (xCell k 255) := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

theorem coreOp255_setT {k e : ℕ} (he : 255 ≤ e) :
    coreOp k e 1 = .setc (tCell k) (tgtV (s0 k + 256)) := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

theorem coreOp255_mul {k e : ℕ} (he : 255 ≤ e) :
    coreOp k e 2 = .mul (gPrev k) (tCell k) (gOut k) := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

theorem coreOp255_setV {k e : ℕ} (he : 255 ≤ e) :
    coreOp k e 3 = .setc (vCell k) (tgtV (s0 k + 255)) := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

theorem coreOp255_jmp {k e : ℕ} (he : 255 ≤ e) :
    coreOp k e 4 = .jump oneCell (vCell k) oneCell := by
  unfold coreOp; rw [if_neg (by omega)]; rfl

/-- The jump cell of leaf `e`. -/
def leafJC (k e : ℕ) : ℕ := if e < 255 then tCell k else vCell k

/-- The last op of every leaf is the unconditional `JUMP` through `leafJC`. -/
theorem leafOp_last (k e : ℕ) : leafOp k e (leafLen k e - 1) = .jump oneCell (leafJC k e) oneCell := by
  unfold leafLen leafJC
  by_cases he : e < 255
  · rw [if_pos he, if_pos he, show tieLen k + 4 - 1 = tieLen k + 3 by omega, leafOp_core,
      coreOp_jmp he]
  · rw [if_neg he, if_neg he, show tieLen k + 5 - 1 = tieLen k + 4 by omega, leafOp_core,
      coreOp255_jmp (by omega)]

/-- The op before the leaf `JUMP` sets its target to `s0 k + min e 254 + 1`. -/
theorem leafOp_setJ (k e : ℕ) :
    leafOp k e (leafLen k e - 2) = .setc (leafJC k e) (tgtV (s0 k + min e 254 + 1)) := by
  unfold leafLen leafJC
  by_cases he : e < 255
  · rw [if_pos he, if_pos he, show tieLen k + 4 - 2 = tieLen k + 2 by omega, leafOp_core,
      coreOp_set he, show min e 254 = e by omega]
  · rw [if_neg he, if_neg he, show tieLen k + 5 - 2 = tieLen k + 3 by omega, leafOp_core,
      coreOp255_setV (by omega), show s0 k + min e 254 + 1 = s0 k + 255 by omega]

theorem coreOp_isJump {k e i : ℕ} (h : i + 1 < if e < 255 then 4 else 5) :
    (coreOp k e i).isJump = false := by
  unfold coreOp; split_ifs at h ⊢ <;> first | rfl | omega

theorem leafOp_isJump {k e i : ℕ} (h : i + 1 < leafLen k e) : (leafOp k e i).isJump = false := by
  unfold leafOp
  split_ifs
  · exact tieOp_isJump k e i
  · unfold leafLen at h
    exact coreOp_isJump (by split_ifs at h ⊢ <;> omega)

theorem coreOp_cost (k e i : ℕ) : (coreOp k e i).cost = if e < 255 ∧ i = 0 then 10 else 1 := by
  unfold coreOp; split_ifs <;> first | rfl | omega

theorem leafOp_cost (k e i : ℕ) : (leafOp k e i).cost = if e < 255 ∧ i = tieLen k then 10 else 1 := by
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
  rcases tieLen_cases k with h | h | h <;> rw [h] <;> by_cases he : e < 255 <;>
    simp [he, Finset.sum_range_succ]

theorem leaf32Op_blake (c : ℕ) :
    leaf32Op c 0 =
      .blake (sigCell 32) (posCell 32) (posCell c) zCell zCell (xCell 32 (c + 1)) oneCell := by
  with_unfolding_all rfl
theorem leaf32Op_setU (c : ℕ) : leaf32Op c 1 = .setc uCell (tgtV (256 * c)) := by
  with_unfolding_all rfl
theorem leaf32Op_mul (c : ℕ) : leaf32Op c 2 = .mul (gCell 31) uCell (gCell 32) := by
  with_unfolding_all rfl
theorem leaf32Op_setT (c : ℕ) : leaf32Op c 3 = .setc (tCell 32) (tgtV (s0 32 + c + 1)) := by
  with_unfolding_all rfl
theorem leaf32Op_jmp (c : ℕ) : leaf32Op c 4 = .jump oneCell (tCell 32) oneCell := by
  with_unfolding_all rfl

theorem leaf32Op_cost_sum (c : ℕ) : ∑ i ∈ Finset.range 5, (leaf32Op c i).cost = 14 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, leaf32Op_blake, leaf32Op_setU,
    leaf32Op_mul, leaf32Op_setT, leaf32Op_jmp, CInstr.cost]

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

theorem bodyInstr_bounded {k j : ℕ} (hk : k < 34) (hj : j ≤ 254) :
    (bodyInstr k j).Bounded 65536 := by
  simp only [bodyInstr, CInstr.Bounded, xCell, posCell, zCell, oneCell]
  split_ifs <;> omega

theorem tieOp_bounded {k e : ℕ} (hk : k < 32) (he : e < 256) (i : ℕ) :
    (tieOp k e i).Bounded 65536 := by
  unfold tieOp
  split_ifs <;> simp only [CInstr.Bounded, accCell, fCell, posCell, scr, zCell] <;>
    (try split_ifs) <;> omega

theorem coreOp_bounded {k e : ℕ} (hk : k ≤ 33) (he : e < 256) (i : ℕ) :
    (coreOp k e i).Bounded 65536 := by
  unfold coreOp
  split_ifs <;>
    simp only [CInstr.Bounded, sigCell, posCell, zCell, xCell, oneCell, gPrev, gOut, gCell,
      tCell, vCell, k0Cell, scr] <;>
    (try split_ifs) <;> omega

theorem leafOp_bounded {k e : ℕ} (hk : k ≤ 33) (he : e < 256) (i : ℕ) :
    (leafOp k e i).Bounded 65536 := by
  unfold leafOp
  split_ifs with hi
  · have hk' : k < 32 := by
      unfold tieLen at hi; split_ifs at hi <;> omega
    exact tieOp_bounded hk' he i
  · exact coreOp_bounded hk he _

theorem groupNode_bounded {k : ℕ} (hk : k ≤ 33) (q b r : ℕ) :
    (groupNode k q b r).Bounded 65536 := by
  unfold groupNode
  split_ifs <;> simp only [CInstr.Bounded, tbCell, zbCell, oneCell, scr] <;> omega

theorem groupInstr_bounded {k q t : ℕ} (hk : k ≤ 33) (hq : q < 64) (ht : t < 44) :
    (groupInstr k q t).Bounded 65536 := by
  unfold groupInstr
  split_ifs
  · exact groupNode_bounded hk _ _ _
  · exact leafOp_bounded hk (by omega) _

theorem riceInstr_bounded {k o : ℕ} (hk : k ≤ 33) (ho : o < 2942) :
    (riceInstr k o).Bounded 65536 := by
  unfold riceInstr
  split_ifs
  · simp only [CInstr.Bounded, tuCell, scr]; omega
  · simp only [CInstr.Bounded, zuCell, tuCell, oneCell, scr]; omega
  · exact groupInstr_bounded hk (by omega) (by omega)
  · exact groupInstr_bounded hk (by omega) (by omega)

theorem chainInstr_bounded {k o : ℕ} (hk : k < 32) (ho : o < 3196) :
    (chainInstr k o).Bounded 65536 := by
  unfold chainInstr
  split_ifs
  · exact riceInstr_bounded (by omega) (by omega)
  · exact bodyInstr_bounded (by omega) (by omega)

theorem leaf32Op_bounded {c : ℕ} (hc : c < 32) (i : ℕ) : (leaf32Op c i).Bounded 65536 := by
  unfold leaf32Op
  split_ifs <;>
    simp only [CInstr.Bounded, sigCell, posCell, zCell, xCell, oneCell, uCell, gCell, tCell,
      scr] <;>
    (try split_ifs) <;> omega

theorem c32Instr_bounded {o : ℕ} (ho : o < 476) : (c32Instr o).Bounded 65536 := by
  unfold c32Instr
  split_ifs
  · simp only [CInstr.Bounded, tuCell, scr]; omega
  · simp only [CInstr.Bounded, zuCell, tuCell, oneCell, scr]; omega
  · exact leaf32Op_bounded (by omega) _
  · exact leaf32Op_bounded (by omega) _
  · exact bodyInstr_bounded (by omega) (by omega)

theorem rootInstr_bounded {t : ℕ} (ht : t < 34) : (rootInstr t).Bounded 65536 := by
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
  · exact chainInstr_bounded (by omega) (by omega)
  · exact c32Instr_bounded (by omega)
  · exact riceInstr_bounded (by omega) (by omega)
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
  · unfold groupNode; split_ifs <;> trivial
  · exact leafOp_jumpOne k _ _

theorem riceInstr_jumpOne (k o : ℕ) : (riceInstr k o).JumpOne := by
  unfold riceInstr; split_ifs
  · trivial
  · rfl
  · exact groupInstr_jumpOne k _ _
  · exact groupInstr_jumpOne k _ _

theorem leaf32Op_jumpOne (c i : ℕ) : (leaf32Op c i).JumpOne := by
  unfold leaf32Op; split_ifs <;> trivial

theorem c32Instr_jumpOne (o : ℕ) : (c32Instr o).JumpOne := by
  unfold c32Instr; split_ifs
  · trivial
  · rfl
  · exact leaf32Op_jumpOne _ _
  · exact leaf32Op_jumpOne _ _
  · trivial

theorem chainInstr_jumpOne (k o : ℕ) : (chainInstr k o).JumpOne := by
  unfold chainInstr; split_ifs
  · exact riceInstr_jumpOne _ _
  · trivial

theorem cinstrAt_jumpOne (s : ℕ) : (cinstrAt s).JumpOne := by
  unfold cinstrAt; split_ifs
  · unfold constInstr; split_ifs <;> trivial
  · exact chainInstr_jumpOne _ _
  · exact c32Instr_jumpOne _
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
