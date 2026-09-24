import OptimalOTS.LeanIsaMachine

/-!
# The leanISA bytecode of the RT-MX ("Rice-tree forced dispatch", mixed 7/6-bit) Winternitz verifier

Design: `NOTES.md` (memory layout, bytecode layout); `mx_model.py` is the executable spec, and
every layout constant below is pinned to it by a `rfl`/`decide` lemma.

The program runs in frame `fp = 1`: every operand is `op c = g ^ c` naming cell `c`. It has
`2 ^ 16` slots; slot `s` holds `(cinstrAt s).toInstr`, where `cinstrAt` is decoded
arithmetically by segment (no proof evaluates the program over a range of indices).

Chain `k < 41` carries message field `k`: 7 bits for `k ∈ {0..7, 20, 21}` ("wide"), else 6 bits.
A field `d` is the chain digit `e = off k + d` (`off k = 0` for wide chains, `64` otherwise); the
checksum chains `c_hi = 41`, `c_lo = 42` carry `64 + C / 64` and `64 + C % 64`. Rice chain `k`
has `nLeaves k` leaves indexed by `d = e - off k`, and body steps `j ∈ [off k + 1, 126]`.

* `[0, 127)`: `SET posCell (s+1) := posV (s+1)`; `127`: `SET k0Cell := tgtV K0`;
  `128`: `SET lenCell := lenV`; `129`, `130`: `SET zCell := 0`, `SET zCell + 1 := 0`
  (`constInstr`).
* `[rBase k, rBase (k + 1))`, `k < 41`: chain `k`, its Rice(1) dispatch (`dispLen k` slots),
  then its body (`chainInstr k`): 1276 slots for a wide chain, 636 for a narrow one.
  Wide chains `0..7` start at `131`, narrow `8..19` at `10339`, wide `20, 21` at `17971`,
  narrow `22..40` at `20523`.
* `[32607, 33024)`: chain 41 (`c_hi`), unary dispatch of 50 nodes and 51 leaves, then its body
  (`hiInstr`).
* `[33024, 33598)`: chain 42 (`c_lo`) Rice dispatch; `[33598, 65429)`: `.pad`;
  `[65429, 65491)`: chain 42 body.
* `[65491, 65534)`: root absorptions (`rootInstr`); `65534`: the pk `XOR` (`pkInstr`), which
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

/-! ## Message fields -/

/-- Width of message field `k < 41`: 7 bits for `k ∈ {0..7, 20, 21}`, else 6 (mirrors
`fieldWidth`). -/
def mFieldWidth (k : ℕ) : ℕ := if k < 8 ∨ k = 20 ∨ k = 21 then 7 else 6
/-- Bit offset of message field `k < 41` in the message, `Σ_{j>k} mFieldWidth j` (mirrors
`fieldOff`). Fields `0..19` lie in bits `128..255`, fields `20..40` in bits `0..127`. -/
def mFieldOff (k : ℕ) : ℕ :=
  if k < 8 then 249 - 7 * k else if k < 20 then 242 - 6 * k else if k < 22 then 261 - 7 * k
  else 240 - 6 * k
/-- Leaf offset of chain `k`: chain digit `e = off k + d` for leaf `d` (mirrors `digitOff` on
`k < 41`; `64` on the checksum chains). -/
def off (k : ℕ) : ℕ := if k < 8 ∨ k = 20 ∨ k = 21 then 0 else 64
/-- First body step of chain `k`. -/
def bodyFirst (k : ℕ) : ℕ := off k + 1
/-- In-cell bit offset of field `k`'s tie word: cell 2 for `k < 20`, cell 1 otherwise. -/
def tieShift (k : ℕ) : ℕ := if k < 20 then mFieldOff k - 128 else mFieldOff k

theorem off_wide {k : ℕ} (h : k < 8 ∨ k = 20 ∨ k = 21) : off k = 0 := if_pos h
theorem off_narrow {k : ℕ} (h : ¬ (k < 8 ∨ k = 20 ∨ k = 21)) : off k = 64 := if_neg h
theorem off_41 : off 41 = 64 := rfl
theorem off_42 : off 42 = 64 := rfl
theorem off_le (k : ℕ) : off k ≤ 64 := by unfold off; split_ifs <;> omega
theorem off_cases (k : ℕ) : off k = 0 ∨ off k = 64 := by unfold off; split_ifs <;> simp
theorem bodyFirst_le (k : ℕ) : bodyFirst k ≤ 65 := by have := off_le k; unfold bodyFirst; omega
theorem mFieldWidth_off (k : ℕ) : off k + 2 ^ mFieldWidth k = 128 := by
  unfold off mFieldWidth; split_ifs <;> rfl
theorem tieShift_zero : tieShift 0 = 121 := rfl
theorem tieShift_20 : tieShift 20 = 121 := rfl
theorem tieShift_19 : tieShift 19 = 0 := rfl
theorem tieShift_40 : tieShift 40 = 0 := rfl
theorem tieShift_of_lt {k : ℕ} (hk : k < 20) : tieShift k = mFieldOff k - 128 := if_pos hk
theorem tieShift_of_ge {k : ℕ} (hk : 20 ≤ k) : tieShift k = mFieldOff k := if_neg (by omega)
/-- The fields partition the two message cells: field `k < 20` fits in cell 2 above
`tieShift k`, field `20 ≤ k < 41` in cell 1. -/
theorem tieShift_add_width {k : ℕ} (hk : k < 41) :
    tieShift k + mFieldWidth k ≤ 128 ∧ (k < 20 → mFieldOff k = 128 + tieShift k) := by
  unfold tieShift mFieldOff mFieldWidth; split_ifs <;> omega

/-! ## Cells -/

/-- The pinned public-key cell. -/
def pkCell : ℕ := 0
/-- The pinned length cell. -/
def lenCell : ℕ := 3
/-- The pinned signature cell of chain `k`. -/
def sigCell (k : ℕ) : ℕ := 4 + k
/-- The zero cell `Z`, set to zero by slot 129 (slot 130 zeroes `Z + 1`); `(Z, Z + 1)` is the
zero pair. -/
def zCell : ℕ := 48
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
/-- The tie accumulator of chain `k`. Chains 19 and 40 close the message cells 2 and 1. -/
def accCell (k : ℕ) : ℕ := scr k + 136
/-- `U = g ^ (64 · (e_hi - 64))`. -/
def uCell : ℕ := scr 41 + 137
/-- The previous checksum product. -/
def gPrev (k : ℕ) : ℕ := if k = 0 then oneCell else gCell (k - 1)
/-- The checksum product output of chain `k`. -/
def gOut (k : ℕ) : ℕ := if k = 42 then k0Cell else gCell k
/-- Root state pair `S_t` (low cell); `S_0` is the zero pair. -/
def rootStateCell (t : ℕ) : ℕ := if t = 0 then zCell else 8000 + 2 * t
/-- Chain word `x_{k,j}`; `xCell k (j+1) + 1` is the high half `h_{k,j}`. -/
def xCell (k j : ℕ) : ℕ := 9000 + 256 * k + 2 * j

theorem posCell_zero : posCell 0 = zCell := rfl
theorem posCell_of_pos {j : ℕ} (hj : j ≠ 0) : posCell j = 100 + j := if_neg hj
theorem posCell_one : posCell 1 = oneCell := rfl
theorem uCell_eq : uCell = 7721 := rfl
theorem rootStateCell_zero : rootStateCell 0 = zCell := rfl
theorem rootStateCell_of_pos {t : ℕ} (ht : t ≠ 0) : rootStateCell t = 8000 + 2 * t := if_neg ht
theorem gPrev_zero : gPrev 0 = oneCell := rfl
theorem gPrev_of {k : ℕ} (h0 : k ≠ 0) : gPrev k = gCell (k - 1) := if_neg h0
theorem gPrev_42 : gPrev 42 = gCell 41 := rfl
theorem gOut_42 : gOut 42 = k0Cell := rfl
theorem gOut_of {k : ℕ} (h42 : k ≠ 42) : gOut k = gCell k := if_neg h42
theorem xCell_succ_add_one (k j : ℕ) : xCell k (j + 1) + 1 = xCell k j + 3 := by
  unfold xCell; omega
theorem zCell_add_one : zCell + 1 = 49 := rfl

/-! ## Values -/

/-- ONE: the cell `cellOfBits 1`, also the field one (`oneV_eq_cellOfBits`, `oneV_eq_ofK`). -/
def oneV : E := E.ofLimbs 1 0 0
/-- The position / id / metadata constant `j`. -/
def posV (j : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 j)
/-- The checked length `5504`. -/
def lenV : E := LeanIsa.cellOfBits (BitVec.ofNat 128 5504)
/-- The jump target / exponent constant `g ^ t` as a word. -/
def tgtV (t : ℕ) : E := ofK (gpow t)
/-- The tie word: `d` at in-cell bit offset `p`. -/
def vV (p d : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 (d <<< p))

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

/-- The zero pair's value is the position constant `0`. -/
theorem posV_zero : posV 0 = 0 := by
  unfold posV LeanIsa.cellOfBits
  exact (ofLimbs_eq_zero_iff 0).mpr rfl

theorem vV_zero (d : ℕ) : vV 0 d = posV d := by
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
def nU (k : ℕ) : ℕ := if k < 8 ∨ k = 20 ∨ k = 21 then 63 else 31
/-- Leaves of Rice chain `k`: `2 ^ mFieldWidth k`, so `off k + nLeaves k = 128`. -/
def nLeaves (k : ℕ) : ℕ := if k < 8 ∨ k = 20 ∨ k = 21 then 128 else 64
/-- Slots of the Rice dispatch of chain `k`: `nU k` unary nodes of 18 slots, then the last
group of 16. -/
def dispLen (k : ℕ) : ℕ := 18 * nU k + 16
/-- Base slot of chain `k`'s segment (`k ≤ 41`), and of chain 42's dispatch. -/
def rBase (k : ℕ) : ℕ :=
  if k ≤ 8 then 131 + 1276 * k
  else if k ≤ 20 then 10339 + 636 * (k - 8)
  else if k ≤ 22 then 17971 + 1276 * (k - 20)
  else if k ≤ 41 then 20523 + 636 * (k - 22)
  else 33024
/-- Body step `j` of chain `k` sits at `s0 k + j` (`bodyFirst k ≤ j ≤ 126`). -/
def s0 (k : ℕ) : ℕ :=
  if k < 41 then rBase k + dispLen k - bodyFirst k else if k = 41 then 32897 else 65364
/-- Entry slot of group `q` of a Rice chain. -/
def gBase (k q : ℕ) : ℕ := if q < nU k then rBase k + 18 * q + 2 else rBase k + 18 * nU k
/-- First slot of the leaf of chain digit `e` of a Rice chain (leaf `e - off k`). -/
def leafSlot (k e : ℕ) : ℕ := gBase k ((e - off k) / 2) + 2 + 7 * ((e - off k) % 2)
/-- First slot of leaf `dh = e - 64` of chain 41. -/
def leafSlotHi (dh : ℕ) : ℕ := if 1 ≤ dh then rBase 41 + 7 * (50 - dh) + 2 else rBase 41 + 350
/-- First root absorption. -/
def rootBase : ℕ := 65491
/-- The pk `XOR`. -/
def pkSlot : ℕ := 65534
/-- The sentinel slot `2 ^ 16 - 1`. -/
def sentinel : ℕ := 65535
/-- The checksum exponent: `Σ_{k<41} (s0 k + 1) + (s0 42 + 1) + 5271`. -/
def K0 : ℕ := (∑ k ∈ Finset.range 41, (s0 k + 1)) + (s0 42 + 1) + 5271

/-- The per-chain constants of a wide (7-bit) chain. -/
theorem layout_wide {k : ℕ} (h : k < 8 ∨ k = 20 ∨ k = 21) :
    off k = 0 ∧ nU k = 63 ∧ nLeaves k = 128 ∧ dispLen k = 1150 ∧ bodyFirst k = 1 := by
  unfold dispLen bodyFirst nU nLeaves off; rw [if_pos h, if_pos h, if_pos h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The per-chain constants of a narrow (6-bit) chain, including chains 41 and 42. -/
theorem layout_narrow {k : ℕ} (h : ¬ (k < 8 ∨ k = 20 ∨ k = 21)) :
    off k = 64 ∧ nU k = 31 ∧ nLeaves k = 64 ∧ dispLen k = 574 ∧ bodyFirst k = 65 := by
  unfold dispLen bodyFirst nU nLeaves off; rw [if_neg h, if_neg h, if_neg h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nU_le (k : ℕ) : nU k ≤ 63 := by unfold nU; split_ifs <;> omega
theorem nU_42 : nU 42 = 31 := rfl
theorem nLeaves_42 : nLeaves 42 = 64 := rfl
theorem dispLen_42 : dispLen 42 = 574 := rfl
theorem nLeaves_eq (k : ℕ) : nLeaves k = 2 * nU k + 2 := by
  unfold nLeaves nU; split_ifs <;> rfl
theorem nLeaves_le (k : ℕ) : nLeaves k ≤ 128 := by unfold nLeaves; split_ifs <;> omega
/-- Every Rice chain's leaves are the chain digits `off k .. 127`. -/
theorem off_add_nLeaves (k : ℕ) : off k + nLeaves k = 128 := by
  unfold off nLeaves; split_ifs <;> rfl
theorem nLeaves_pow (k : ℕ) : nLeaves k = 2 ^ mFieldWidth k := by
  unfold nLeaves mFieldWidth; split_ifs <;> rfl
theorem dispLen_eq (k : ℕ) : dispLen k = 18 * nU k + 16 := rfl
theorem dispLen_ge (k : ℕ) : 574 ≤ dispLen k := by unfold dispLen nU; split_ifs <;> omega
theorem rBase_zero : rBase 0 = 131 := rfl
theorem rBase_A {k : ℕ} (hk : k ≤ 8) : rBase k = 131 + 1276 * k := by
  unfold rBase; rw [if_pos hk]
theorem rBase_B {k : ℕ} (h1 : 8 ≤ k) (h2 : k ≤ 20) : rBase k = 10339 + 636 * (k - 8) := by
  unfold rBase; split_ifs <;> omega
theorem rBase_C {k : ℕ} (h1 : 20 ≤ k) (h2 : k ≤ 22) : rBase k = 17971 + 1276 * (k - 20) := by
  unfold rBase; split_ifs <;> omega
theorem rBase_D {k : ℕ} (h1 : 22 ≤ k) (h2 : k ≤ 41) : rBase k = 20523 + 636 * (k - 22) := by
  unfold rBase; split_ifs <;> omega
theorem rBase_41 : rBase 41 = 32607 := rfl
theorem rBase_42 : rBase 42 = 33024 := rfl
theorem s0_of_lt {k : ℕ} (hk : k < 41) : s0 k = rBase k + dispLen k - bodyFirst k := if_pos hk
theorem s0_41 : s0 41 = 32897 := rfl
theorem s0_42 : s0 42 = 65364 := rfl
/-- A Rice chain's first body step follows its dispatch. -/
theorem s0_rice {k : ℕ} (hk : k < 41) : s0 k + bodyFirst k = rBase k + dispLen k := by
  have := dispLen_ge k; have := bodyFirst_le k
  rw [s0_of_lt hk]; omega
theorem s0_add_127 {k : ℕ} (hk : k ≤ 41) : s0 k + 127 = rBase (k + 1) := by
  interval_cases k <;> rfl
theorem s0_42_add_127 : s0 42 + 127 = rootBase := rfl
theorem rootBase_add_43 : rootBase + 43 = pkSlot := rfl
theorem pkSlot_add_one : pkSlot + 1 = sentinel := rfl
theorem sentinel_eq : sentinel = 2 ^ 16 - 1 := rfl
theorem gBase_of_lt {k q : ℕ} (hq : q < nU k) : gBase k q = rBase k + 18 * q + 2 := if_pos hq
theorem gBase_last (k : ℕ) : gBase k (nU k) = rBase k + 18 * nU k := if_neg (lt_irrefl _)
theorem leafSlot_eq {k q b : ℕ} (hb : b < 2) :
    leafSlot k (off k + 2 * q + b) = gBase k q + 2 + 7 * b := by
  unfold leafSlot
  rw [show (off k + 2 * q + b - off k) / 2 = q by omega,
    show (off k + 2 * q + b - off k) % 2 = b by omega]
theorem leafSlotHi_of_node {i : ℕ} (hi : i < 50) : leafSlotHi (50 - i) = rBase 41 + 7 * i + 2 := by
  unfold leafSlotHi; rw [if_pos (by omega), show 50 - (50 - i) = i by omega]
theorem leafSlotHi_zero : leafSlotHi 0 = rBase 41 + 350 := rfl
theorem leafSlotHi_of_pos {dh : ℕ} (hdh : 1 ≤ dh) : leafSlotHi dh = rBase 41 + 7 * (50 - dh) + 2 :=
  if_pos hdh

theorem K0_eq : K0 = 836677 := by decide

/-! ## Builders -/

/-- Slots `0..130`: the position constants, the checksum target, the length and the zero pair. -/
def constInstr (s : ℕ) : CInstr :=
  if s < 127 then .setc (posCell (s + 1)) (posV (s + 1))
  else if s = 127 then .setc k0Cell (tgtV K0)
  else if s = 128 then .setc lenCell lenV
  else if s = 129 then .setc zCell 0
  else .setc (zCell + 1) 0

/-- Number of tie ops of chain `k`'s leaves. -/
def tieLen (k : ℕ) : ℕ :=
  if k = 0 ∨ k = 19 ∨ k = 20 ∨ k = 40 then 1 else if k < 41 then 2 else 0

/-- Tie op `i` of the leaf of chain digit `e` of chain `k < 41`, with field `d = e - off k`.
XOR is addition in `E`: chain 0 (20) opens the cell-2 (cell-1) accumulator, the middle chains
add their words, and chain 19 (40) closes cell 2 (1) with its field at offset 0. -/
def tieOp (k e i : ℕ) : CInstr :=
  if k = 0 ∨ k = 20 then .setc (accCell k) (vV (tieShift k) (e - off k))
  else if k = 19 then .xor (accCell 18) (posCell (e - off k)) 2
  else if k = 40 then .xor (accCell 39) (posCell (e - off k)) 1
  else if i = 0 then .setc (fCell k) (vV (tieShift k) (e - off k))
  else .xor (accCell (k - 1)) (fCell k) (accCell k)

/-- Core op `i` of the leaf of chain digit `e` of chain `k` (`.pad` past the end). -/
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

/-- Op `i` of the leaf of chain digit `e` of a Rice chain `k`: the tie ops, then the core ops. -/
def leafOp (k e i : ℕ) : CInstr :=
  if i < tieLen k then tieOp k e i else coreOp k e (i - tieLen k)

/-- Slot `t < 16` of group `q`: the node, then leaves `2q` and `2q + 1` of 7 slots each. -/
def groupInstr (k q t : ℕ) : CInstr :=
  if t = 0 then .setc (tbCell k) (tgtV (gBase k q + 9))
  else if t = 1 then .jump (zbCell k) (tbCell k) oneCell
  else leafOp k (off k + 2 * q + (t - 2) / 7) ((t - 2) % 7)

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

/-- Slot `o < dispLen k + 127 - bodyFirst k` of chain `k < 41`. -/
def chainInstr (k o : ℕ) : CInstr :=
  if o < dispLen k then riceInstr k o else bodyInstr k (o + bodyFirst k - dispLen k)

/-- Op `i` of leaf `dh` (chain digit `64 + dh`) of chain 41. -/
def hiLeafOp (dh i : ℕ) : CInstr :=
  if i = 0 then
    .blake (sigCell 41) (posCell 41) (posCell (64 + dh)) zCell zCell (xCell 41 (64 + dh + 1))
      oneCell
  else if i = 1 then .setc uCell (tgtV (64 * dh))
  else if i = 2 then .mul (gCell 40) uCell (gCell 41)
  else if i = 3 then .setc (tCell 41) (tgtV (s0 41 + (64 + dh) + 1))
  else if i = 4 then .jump oneCell (tCell 41) oneCell
  else .pad

/-- Slot `o < 417` of chain 41: unary nodes and leaves `dh ≥ 1`, leaf 0, then the body. -/
def hiInstr (o : ℕ) : CInstr :=
  if o < 350 then
    if o % 7 = 0 then .setc (tuCell 41 (o / 7)) (tgtV (rBase 41 + 7 * (o / 7 + 1)))
    else if o % 7 = 1 then .jump (zuCell 41 (o / 7)) (tuCell 41 (o / 7)) oneCell
    else hiLeafOp (50 - o / 7) (o % 7 - 2)
  else if o < 355 then hiLeafOp 0 (o - 350)
  else bodyInstr 41 (o - 290)

/-- Root absorption `t < 43`. -/
def rootInstr (t : ℕ) : CInstr :=
  .blake (xCell t 127) zCell zCell zCell (rootStateCell t) (rootStateCell (t + 1))
    (posCell (44 - t))

/-- The pk check. -/
def pkInstr : CInstr := .xor (rootStateCell 43) zCell pkCell

/-- The cell-level instruction at slot `s`, decoded by segment. -/
def cinstrAt (s : ℕ) : CInstr :=
  if s < 131 then constInstr s
  else if s < 10339 then chainInstr ((s - 131) / 1276) ((s - 131) % 1276)
  else if s < 17971 then chainInstr ((s - 10339) / 636 + 8) ((s - 10339) % 636)
  else if s < 20523 then chainInstr ((s - 17971) / 1276 + 20) ((s - 17971) % 1276)
  else if s < 32607 then chainInstr ((s - 20523) / 636 + 22) ((s - 20523) % 636)
  else if s < 33024 then hiInstr (s - 32607)
  else if s < 33598 then riceInstr 42 (s - 33024)
  else if s < 65429 then .pad
  else if s < 65491 then bodyInstr 42 (s - 65364)
  else if s < 65534 then rootInstr (s - 65491)
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

/-- Dispatch nodes on the path to leaf `d` of Rice chain `k`. -/
def riceDepth (k d : ℕ) : ℕ := if d / 2 < nU k then d / 2 + 2 else nU k + 1
/-- Dispatch nodes on the path to leaf `dh` of chain 41. -/
def hiDepth (dh : ℕ) : ℕ := if dh = 0 then 50 else 51 - dh
/-- Number of ops of the leaf of chain digit `e` of chain `k`. -/
def leafLen (k e : ℕ) : ℕ := tieLen k + if e < 127 then 4 else 5
/-- Cycles of the leaf of chain digit `e` of chain `k`. -/
def leafCost (k e : ℕ) : ℕ := tieLen k + if e < 127 then 13 else 5
/-- Body steps after the leaf of chain digit `e`. -/
def bodyLen (e : ℕ) : ℕ := 126 - e
def chainSteps (k e : ℕ) : ℕ := 2 * riceDepth k (e - off k) + leafLen k e + bodyLen e
def chainCost (k e : ℕ) : ℕ := 2 * riceDepth k (e - off k) + leafCost k e + 10 * bodyLen e
def hiSteps (dh : ℕ) : ℕ := 2 * hiDepth dh + 5 + (62 - dh)
def hiCost (dh : ℕ) : ℕ := 2 * hiDepth dh + 14 + 10 * (62 - dh)

/-- Steps of the walk with leaf vector `E`: constants, the 41 message chains, `c_hi`, `c_lo`, and
the 43 absorptions plus the pk check. -/
def totalSteps (E : ℕ → ℕ) : ℕ :=
  131 + (∑ k ∈ Finset.range 41, chainSteps k (E k)) + hiSteps (E 41 - 64) + chainSteps 42 (E 42)
    + 44

/-- Cost of the walk with leaf vector `E`. -/
def totalCost (E : ℕ → ℕ) : ℕ :=
  131 + (∑ k ∈ Finset.range 41, chainCost k (E k)) + hiCost (E 41 - 64) + chainCost 42 (E 42)
    + 431

/-- The claimed score: `boundaryCycles + 33723`. -/
def claim : ℕ := LeanIsa.boundaryCycles + 33723

theorem claim_eq : claim = 33843 := rfl

/-- Affine bound on a Rice chain: `1277` for a wide chain, `1213` for a narrow one. -/
theorem chainCost_bound (k : ℕ) {e : ℕ} (h1 : off k ≤ e) (h2 : e < off k + nLeaves k) :
    chainCost k e + 9 * e ≤ 1277 - off k + tieLen k := by
  unfold chainCost riceDepth leafCost bodyLen
  generalize tieLen k = t
  unfold nU off nLeaves at *
  split_ifs at * <;> omega

theorem hiCost_bound {dh : ℕ} (hdh : dh ≤ 50) : hiCost dh + 12 * dh ≤ 736 := by
  unfold hiCost hiDepth
  split_ifs <;> omega

theorem tieLen_cases (k : ℕ) : tieLen k = 0 ∨ tieLen k = 1 ∨ tieLen k = 2 := by
  unfold tieLen; split_ifs <;> simp

theorem tieLen_of_ge {k : ℕ} (hk : 41 ≤ k) : tieLen k = 0 := by
  unfold tieLen; rw [if_neg (by omega), if_neg (by omega)]
theorem tieLen_one {k : ℕ} (hk : k = 0 ∨ k = 19 ∨ k = 20 ∨ k = 40) : tieLen k = 1 := if_pos hk
theorem tieLen_two {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 39) (h19 : k ≠ 19) (h20 : k ≠ 20) :
    tieLen k = 2 := by
  unfold tieLen; rw [if_neg (by omega), if_pos (by omega)]
theorem tieLen_le (k : ℕ) : tieLen k ≤ 2 := by
  rcases tieLen_cases k with h | h | h <;> omega
theorem tieLen_sum : ∑ k ∈ Finset.range 41, tieLen k = 78 := by decide
/-- The constant of the per-chain bounds, summed over the message chains. -/
theorem chainBound_sum : ∑ k ∈ Finset.range 41, (1277 - off k + tieLen k) = 50451 := by decide
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

theorem cinstrAt_const_seg {s : ℕ} (h2 : s < 131) : cinstrAt s = constInstr s := by
  unfold cinstrAt; rw [if_pos h2]

theorem cinstrAt_segA {s : ℕ} (h1 : 131 ≤ s) (h2 : s < 10339) : cinstrAt s = chainInstr ((s - 131) / 1276) ((s - 131) % 1276) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_pos h2]

theorem cinstrAt_segB {s : ℕ} (h1 : 10339 ≤ s) (h2 : s < 17971) : cinstrAt s = chainInstr ((s - 10339) / 636 + 8) ((s - 10339) % 636) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_neg (show ¬ s < 10339 by omega), if_pos h2]

theorem cinstrAt_segC {s : ℕ} (h1 : 17971 ≤ s) (h2 : s < 20523) : cinstrAt s = chainInstr ((s - 17971) / 1276 + 20) ((s - 17971) % 1276) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_neg (show ¬ s < 10339 by omega), if_neg (show ¬ s < 17971 by omega), if_pos h2]

theorem cinstrAt_segD {s : ℕ} (h1 : 20523 ≤ s) (h2 : s < 32607) : cinstrAt s = chainInstr ((s - 20523) / 636 + 22) ((s - 20523) % 636) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_neg (show ¬ s < 10339 by omega), if_neg (show ¬ s < 17971 by omega), if_neg (show ¬ s < 20523 by omega), if_pos h2]

theorem cinstrAt_hi_seg {s : ℕ} (h1 : 32607 ≤ s) (h2 : s < 33024) : cinstrAt s = hiInstr (s - 32607) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_neg (show ¬ s < 10339 by omega), if_neg (show ¬ s < 17971 by omega), if_neg (show ¬ s < 20523 by omega), if_neg (show ¬ s < 32607 by omega), if_pos h2]

theorem cinstrAt_rice42_seg {s : ℕ} (h1 : 33024 ≤ s) (h2 : s < 33598) : cinstrAt s = riceInstr 42 (s - 33024) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_neg (show ¬ s < 10339 by omega), if_neg (show ¬ s < 17971 by omega), if_neg (show ¬ s < 20523 by omega), if_neg (show ¬ s < 32607 by omega), if_neg (show ¬ s < 33024 by omega), if_pos h2]

theorem cinstrAt_gap {s : ℕ} (h1 : 33598 ≤ s) (h2 : s < 65429) : cinstrAt s = .pad := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_neg (show ¬ s < 10339 by omega), if_neg (show ¬ s < 17971 by omega), if_neg (show ¬ s < 20523 by omega), if_neg (show ¬ s < 32607 by omega), if_neg (show ¬ s < 33024 by omega), if_neg (show ¬ s < 33598 by omega), if_pos h2]

theorem cinstrAt_body42_seg {s : ℕ} (h1 : 65429 ≤ s) (h2 : s < 65491) : cinstrAt s = bodyInstr 42 (s - 65364) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_neg (show ¬ s < 10339 by omega), if_neg (show ¬ s < 17971 by omega), if_neg (show ¬ s < 20523 by omega), if_neg (show ¬ s < 32607 by omega), if_neg (show ¬ s < 33024 by omega), if_neg (show ¬ s < 33598 by omega), if_neg (show ¬ s < 65429 by omega), if_pos h2]

theorem cinstrAt_root_seg {s : ℕ} (h1 : 65491 ≤ s) (h2 : s < 65534) : cinstrAt s = rootInstr (s - 65491) := by
  unfold cinstrAt; rw [if_neg (show ¬ s < 131 by omega), if_neg (show ¬ s < 10339 by omega), if_neg (show ¬ s < 17971 by omega), if_neg (show ¬ s < 20523 by omega), if_neg (show ¬ s < 32607 by omega), if_neg (show ¬ s < 33024 by omega), if_neg (show ¬ s < 33598 by omega), if_neg (show ¬ s < 65429 by omega), if_neg (show ¬ s < 65491 by omega), if_pos h2]


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

theorem cinstrAt_z0 : cinstrAt 129 = .setc zCell 0 := by with_unfolding_all rfl

theorem cinstrAt_z1 : cinstrAt 130 = .setc (zCell + 1) 0 := by with_unfolding_all rfl

/-- The segment of message chain `k < 41`: dispatch, then body. -/
theorem cinstrAt_chain {k o : ℕ} (hk : k < 41) (ho : o < dispLen k + 127 - bodyFirst k) :
    cinstrAt (rBase k + o) = chainInstr k o := by
  by_cases hw : k < 8 ∨ k = 20 ∨ k = 21
  · obtain ⟨-, -, -, hd, hb⟩ := layout_wide hw
    rw [hd, hb] at ho
    rcases hw with hw | hw | hw
    · rw [rBase_A (by omega), cinstrAt_segA (by omega) (by omega),
        show (131 + 1276 * k + o - 131) / 1276 = k by omega,
        show (131 + 1276 * k + o - 131) % 1276 = o by omega]
    all_goals
      rw [rBase_C (by omega) (by omega), cinstrAt_segC (by omega) (by omega),
        show (17971 + 1276 * (k - 20) + o - 17971) / 1276 + 20 = k by omega,
        show (17971 + 1276 * (k - 20) + o - 17971) % 1276 = o by omega]
  · obtain ⟨-, -, -, hd, hb⟩ := layout_narrow hw
    rw [hd, hb] at ho
    rcases (show k < 20 ∨ 22 ≤ k by omega) with h | h
    · rw [rBase_B (by omega) (by omega), cinstrAt_segB (by omega) (by omega),
        show (10339 + 636 * (k - 8) + o - 10339) / 636 + 8 = k by omega,
        show (10339 + 636 * (k - 8) + o - 10339) % 636 = o by omega]
    · rw [rBase_D (by omega) (by omega), cinstrAt_segD (by omega) (by omega),
        show (20523 + 636 * (k - 22) + o - 20523) / 636 + 22 = k by omega,
        show (20523 + 636 * (k - 22) + o - 20523) % 636 = o by omega]

/-- The Rice dispatch of chain `k ∈ {0..40, 42}`. -/
theorem cinstrAt_rice {k o : ℕ} (hk : k < 41 ∨ k = 42) (ho : o < dispLen k) :
    cinstrAt (rBase k + o) = riceInstr k o := by
  rcases hk with hk | rfl
  · have := bodyFirst_le k
    rw [cinstrAt_chain hk (by omega)]
    unfold chainInstr; rw [if_pos ho]
  · rw [dispLen_42] at ho
    rw [rBase_42, cinstrAt_rice42_seg (by omega) (by omega), show 33024 + o - 33024 = o by omega]

theorem cinstrAt_uset {k i : ℕ} (hk : k < 41 ∨ k = 42) (hi : i < nU k) :
    cinstrAt (rBase k + 18 * i) = .setc (tuCell k i) (tgtV (rBase k + 18 * (i + 1))) := by
  rw [cinstrAt_rice hk (by rw [dispLen_eq]; omega)]
  unfold riceInstr
  rw [if_pos (by omega), if_pos (by omega), show 18 * i / 18 = i by omega]

theorem cinstrAt_ujmp {k i : ℕ} (hk : k < 41 ∨ k = 42) (hi : i < nU k) :
    cinstrAt (rBase k + 18 * i + 1) = .jump (zuCell k i) (tuCell k i) oneCell := by
  rw [Nat.add_assoc, cinstrAt_rice hk (by rw [dispLen_eq]; omega)]
  unfold riceInstr
  rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), show (18 * i + 1) / 18 = i by omega]

/-- Slot `t < 16` of group `q ≤ nU k`. -/
theorem cinstrAt_group {k q t : ℕ} (hk : k < 41 ∨ k = 42) (hq : q ≤ nU k) (ht : t < 16) :
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

theorem cinstrAt_gset {k q : ℕ} (hk : k < 41 ∨ k = 42) (hq : q ≤ nU k) :
    cinstrAt (gBase k q) = .setc (tbCell k) (tgtV (gBase k q + 9)) := by
  have h := cinstrAt_group hk hq (t := 0) (by omega)
  rw [Nat.add_zero] at h
  rw [h]; unfold groupInstr; rw [if_pos rfl]

theorem cinstrAt_gjmp {k q : ℕ} (hk : k < 41 ∨ k = 42) (hq : q ≤ nU k) :
    cinstrAt (gBase k q + 1) = .jump (zbCell k) (tbCell k) oneCell := by
  rw [cinstrAt_group hk hq (by omega)]; unfold groupInstr; rw [if_neg (by omega), if_pos rfl]

/-- Op `i` of the leaf of chain digit `e` of a Rice chain. -/
theorem cinstrAt_leaf {k e i : ℕ} (hk : k < 41 ∨ k = 42) (he1 : off k ≤ e)
    (he2 : e < off k + nLeaves k) (hi : i < 7) :
    cinstrAt (leafSlot k e + i) = leafOp k e i := by
  rw [nLeaves_eq] at he2
  unfold leafSlot
  rw [show gBase k ((e - off k) / 2) + 2 + 7 * ((e - off k) % 2) + i =
      gBase k ((e - off k) / 2) + (2 + 7 * ((e - off k) % 2) + i) by omega,
    cinstrAt_group hk (by omega) (by omega)]
  unfold groupInstr
  rw [if_neg (by omega), if_neg (by omega),
    show off k + 2 * ((e - off k) / 2) + (2 + 7 * ((e - off k) % 2) + i - 2) / 7 = e by omega,
    show (2 + 7 * ((e - off k) % 2) + i - 2) % 7 = i by omega]

theorem cinstrAt_hi {o : ℕ} (ho : o < 417) : cinstrAt (rBase 41 + o) = hiInstr o := by
  rw [rBase_41, cinstrAt_hi_seg (by omega) (by omega), show 32607 + o - 32607 = o by omega]

theorem cinstrAt_hiset {i : ℕ} (hi : i < 50) :
    cinstrAt (rBase 41 + 7 * i) = .setc (tuCell 41 i) (tgtV (rBase 41 + 7 * (i + 1))) := by
  rw [cinstrAt_hi (by omega)]
  unfold hiInstr
  rw [if_pos (by omega), if_pos (by omega), show 7 * i / 7 = i by omega]

theorem cinstrAt_hijmp {i : ℕ} (hi : i < 50) :
    cinstrAt (rBase 41 + 7 * i + 1) = .jump (zuCell 41 i) (tuCell 41 i) oneCell := by
  rw [Nat.add_assoc, cinstrAt_hi (by omega)]
  unfold hiInstr
  rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), show (7 * i + 1) / 7 = i by omega]

theorem cinstrAt_hileaf {dh i : ℕ} (hdh : dh ≤ 50) (hi : i < 5) :
    cinstrAt (leafSlotHi dh + i) = hiLeafOp dh i := by
  rcases Nat.lt_or_ge dh 1 with h0 | h0
  · obtain rfl : dh = 0 := by omega
    rw [leafSlotHi_zero, Nat.add_assoc, cinstrAt_hi (by omega)]
    unfold hiInstr
    rw [if_neg (by omega), if_pos (by omega), show 350 + i - 350 = i by omega]
  · rw [leafSlotHi_of_pos h0,
      show rBase 41 + 7 * (50 - dh) + 2 + i = rBase 41 + (7 * (50 - dh) + 2 + i) by omega,
      cinstrAt_hi (by omega)]
    unfold hiInstr
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega),
      show 50 - (7 * (50 - dh) + 2 + i) / 7 = dh by omega,
      show (7 * (50 - dh) + 2 + i) % 7 - 2 = i by omega]

theorem cinstrAt_body {k j : ℕ} (hk : k < 43) (hj1 : bodyFirst k ≤ j) (hj2 : j ≤ 126) :
    cinstrAt (s0 k + j) = bodyInstr k j := by
  rcases Nat.lt_or_ge k 41 with h | h
  · have hd := dispLen_ge k
    have hb := bodyFirst_le k
    rw [s0_of_lt h, show rBase k + dispLen k - bodyFirst k + j =
        rBase k + (dispLen k - bodyFirst k + j) by omega, cinstrAt_chain h (by omega)]
    unfold chainInstr
    rw [if_neg (by omega), show dispLen k - bodyFirst k + j + bodyFirst k - dispLen k = j by omega]
  · rcases (show k = 41 ∨ k = 42 by omega) with rfl | rfl
    · rw [show bodyFirst 41 = 65 from rfl] at hj1
      rw [s0_41, show 32897 + j = rBase 41 + (290 + j) by rw [rBase_41]; omega,
        cinstrAt_hi (by omega)]
      unfold hiInstr
      rw [if_neg (by omega), if_neg (by omega), show 290 + j - 290 = j by omega]
    · rw [show bodyFirst 42 = 65 from rfl] at hj1
      rw [s0_42, cinstrAt_body42_seg (by omega) (by omega), show 65364 + j - 65364 = j by omega]

theorem cinstrAt_root {t : ℕ} (ht : t < 43) : cinstrAt (rootBase + t) = rootInstr t := by
  rw [show rootBase = 65491 from rfl, cinstrAt_root_seg (by omega) (by omega),
    show 65491 + t - 65491 = t by omega]

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
theorem leafOp_tie0 (e : ℕ) : leafOp 0 e 0 = .setc (accCell 0) (vV (tieShift 0) (e - off 0)) := by
  rw [leafOp_tie (by rw [tieLen_one (Or.inl rfl)]; omega)]; unfold tieOp; rw [if_pos (Or.inl rfl)]

/-- Chain 19 closes cell 2 (its field sits at in-cell offset 0, so the word is `posV d`). -/
theorem leafOp_tie19 (e : ℕ) : leafOp 19 e 0 = .xor (accCell 18) (posCell (e - off 19)) 2 := by
  rw [leafOp_tie (by rw [tieLen_one (by omega)]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_pos rfl]

/-- Chain 20 opens the cell-1 accumulator. -/
theorem leafOp_tie20 (e : ℕ) :
    leafOp 20 e 0 = .setc (accCell 20) (vV (tieShift 20) (e - off 20)) := by
  rw [leafOp_tie (by rw [tieLen_one (by omega)]; omega)]; unfold tieOp; rw [if_pos (Or.inr rfl)]

/-- Chain 40 closes cell 1. -/
theorem leafOp_tie40 (e : ℕ) : leafOp 40 e 0 = .xor (accCell 39) (posCell (e - off 40)) 1 := by
  rw [leafOp_tie (by rw [tieLen_one (by omega)]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem leafOp_mid0 {k e : ℕ} (h1 : 1 ≤ k) (h39 : k ≤ 39) (h19 : k ≠ 19) (h20 : k ≠ 20) :
    leafOp k e 0 = .setc (fCell k) (vV (tieShift k) (e - off k)) := by
  rw [leafOp_tie (by rw [tieLen_two h1 h39 h19 h20]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_neg h19, if_neg (by omega), if_pos rfl]

theorem leafOp_mid1 {k e : ℕ} (h1 : 1 ≤ k) (h39 : k ≤ 39) (h19 : k ≠ 19) (h20 : k ≠ 20) :
    leafOp k e 1 = .xor (accCell (k - 1)) (fCell k) (accCell k) := by
  rw [leafOp_tie (by rw [tieLen_two h1 h39 h19 h20]; omega)]
  unfold tieOp; rw [if_neg (by omega), if_neg h19, if_neg (by omega), if_neg (by omega)]

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

theorem hiLeafOp_blake (dh : ℕ) :
    hiLeafOp dh 0 =
      .blake (sigCell 41) (posCell 41) (posCell (64 + dh)) zCell zCell (xCell 41 (64 + dh + 1))
        oneCell := by
  with_unfolding_all rfl
theorem hiLeafOp_setU (dh : ℕ) : hiLeafOp dh 1 = .setc uCell (tgtV (64 * dh)) := by
  with_unfolding_all rfl
theorem hiLeafOp_mul (dh : ℕ) : hiLeafOp dh 2 = .mul (gCell 40) uCell (gCell 41) := by
  with_unfolding_all rfl
theorem hiLeafOp_setT (dh : ℕ) :
    hiLeafOp dh 3 = .setc (tCell 41) (tgtV (s0 41 + (64 + dh) + 1)) := by
  with_unfolding_all rfl
theorem hiLeafOp_jmp (dh : ℕ) : hiLeafOp dh 4 = .jump oneCell (tCell 41) oneCell := by
  with_unfolding_all rfl

theorem hiLeafOp_cost_sum (dh : ℕ) : ∑ i ∈ Finset.range 5, (hiLeafOp dh i).cost = 14 := by
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

theorem bodyInstr_bounded {k j : ℕ} (hk : k < 43) (hj : j < 4000) :
    (bodyInstr k j).Bounded 65536 := by
  simp only [bodyInstr, CInstr.Bounded, xCell, posCell, zCell, oneCell]
  split_ifs <;> omega

theorem tieOp_bounded {k e : ℕ} (hk : k < 41) (he : e < 128) (i : ℕ) :
    (tieOp k e i).Bounded 65536 := by
  unfold tieOp
  split_ifs <;> simp only [CInstr.Bounded, accCell, fCell, posCell, scr, zCell] <;>
    (try split_ifs) <;> omega

theorem coreOp_bounded {k e : ℕ} (hk : k ≤ 42) (he : e < 128) (i : ℕ) :
    (coreOp k e i).Bounded 65536 := by
  unfold coreOp
  split_ifs <;>
    simp only [CInstr.Bounded, sigCell, posCell, zCell, xCell, oneCell, gPrev, gOut, gCell,
      tCell, vCell, k0Cell, scr] <;>
    (try split_ifs) <;> omega

theorem leafOp_bounded {k e : ℕ} (hk : k ≤ 42) (he : e < 128) (i : ℕ) :
    (leafOp k e i).Bounded 65536 := by
  unfold leafOp
  split_ifs with hi
  · have hk' : k < 41 := by
      unfold tieLen at hi; split_ifs at hi <;> omega
    exact tieOp_bounded hk' he i
  · exact coreOp_bounded hk he _

theorem groupInstr_bounded {k q t : ℕ} (hk : k ≤ 42) (hq : q ≤ nU k) (ht : t < 16) :
    (groupInstr k q t).Bounded 65536 := by
  have h128 := off_add_nLeaves k
  rw [nLeaves_eq] at h128
  unfold groupInstr
  split_ifs
  · simp only [CInstr.Bounded, tbCell, scr]; omega
  · simp only [CInstr.Bounded, tbCell, zbCell, oneCell, scr]; omega
  · exact leafOp_bounded hk (by omega) _

theorem riceInstr_bounded {k o : ℕ} (hk : k ≤ 42) (ho : o < dispLen k) :
    (riceInstr k o).Bounded 65536 := by
  have hn := nU_le k
  rw [dispLen_eq] at ho
  unfold riceInstr
  split_ifs
  · simp only [CInstr.Bounded, tuCell, scr]; omega
  · simp only [CInstr.Bounded, zuCell, tuCell, oneCell, scr]; omega
  · exact groupInstr_bounded hk (by omega) (by omega)
  · exact groupInstr_bounded hk (by omega) (by omega)

theorem chainInstr_bounded {k o : ℕ} (hk : k < 41) (ho : o < 2000) :
    (chainInstr k o).Bounded 65536 := by
  have := bodyFirst_le k
  unfold chainInstr
  split_ifs with h
  · exact riceInstr_bounded (by omega) h
  · exact bodyInstr_bounded (by omega) (by omega)

theorem hiLeafOp_bounded {dh : ℕ} (hdh : dh ≤ 50) (i : ℕ) : (hiLeafOp dh i).Bounded 65536 := by
  unfold hiLeafOp
  split_ifs <;>
    simp only [CInstr.Bounded, sigCell, posCell, zCell, xCell, oneCell, uCell, gCell, tCell,
      scr] <;>
    (try split_ifs) <;> omega

theorem hiInstr_bounded {o : ℕ} (ho : o < 417) : (hiInstr o).Bounded 65536 := by
  unfold hiInstr
  split_ifs
  · simp only [CInstr.Bounded, tuCell, scr]; omega
  · simp only [CInstr.Bounded, zuCell, tuCell, oneCell, scr]; omega
  · exact hiLeafOp_bounded (by omega) _
  · exact hiLeafOp_bounded (by omega) _
  · exact bodyInstr_bounded (by omega) (by omega)

theorem rootInstr_bounded {t : ℕ} (ht : t < 43) : (rootInstr t).Bounded 65536 := by
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
  · exact chainInstr_bounded (by omega) (by omega)
  · exact chainInstr_bounded (by omega) (by omega)
  · exact chainInstr_bounded (by omega) (by omega)
  · exact hiInstr_bounded (by omega)
  · exact riceInstr_bounded (by omega) (by rw [dispLen_42]; omega)
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
