import OptimalOTS.LeanIsa
import Submissions.UpperLeanIsa.MachineLayout

/-!
# The 1281-cycle bytecode

A 21-slot prologue pins ONE, the 5503-bit length, g, and fifteen additional cost constants
(`C_1 … C_15`; `C_16 = g`), then hashes the index and dispatches the free block (slot 20; slot
21 is a pad). The fifteen landing frames reuse cost constants C_1..C_15. Their isolation holds
through memory log-size 32.

FREE-Z: the free top is a message word of root call 1 (home: group 0), so the free block no
longer copies it. Group 0 has two block regions: frame 1 (`s > 0`, the top is read from the free
chain's output cell) and frame 14 (`s = 0`, the top is the signature cell). The free block of
digit `s` dispatches the first group in frame `frG0 s`, so the variant is forced by `s`.

The free block seeds g^sentinel / C_96 * C_s. Each group multiplies the landing product by its
cost factor; the exit jumps to the last product GP_13 = g^(sentinel + Q (s + Σ costs - 96)).
Only the layer s + Σ costs = 96 lands on the sentinel; every other reachable total lands on a
pad (sentinel - 6 … sentinel - 1) or past the bytecode (`seed_table`, hash-free). Group 0 is the
home of root call 1, groups 1 … 4 and 12 export the cv words of calls 0 … 7, groups 5 and 6 are
the homes of calls 0 and 7, and groups 7 … 11 those of calls 2 … 6. The last call's metadata
operand is the low cell of the state after call 6. The image is committed, so call 1 may run
before call 0 writes its state. Designated high-half tops occupy adjacent cv cells without an
extra copy.

The cost-17 entries of the (3,10) tables have no blocks, so no block multiplies by `C_17`.
Every completing run executes 216 instructions: 111 non-hash and 105 BLAKE2S instructions.
Its cost is 111+10*105+120=1281. Builders are irreducible; slots decode by cost-band arithmetic.
-/

namespace OptimalOTS.HLG3

open LeanerVM.Parameters LeanerVM.Semantics OracleComp
open OptimalOTS.LeanIsaBaseline.Layer

/-! ## Memory reads -/

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

/-- The operand that names cell `c` in frame `f`: `g ^ (c - frameExp f)` in the exponent group. -/
def sop (f c : ℕ) : K := gpow (c + ordG - frameExp f)

/-- Frame pointers are never `1`: the sentinel needs `fp = 1`. -/
theorem frame_ne_one {f : ℕ} (hf : f < 15) : frame f ≠ 1 := by
  intro h
  have h' : gpow (frameExp f) = gpow 0 := h.trans (pow_zero g).symm
  have hb := frameExp_bounds hf
  have := gpow_inj (show frameExp f < 2 ^ 64 - 1 by unfold eLen at hb; omega)
    (show (0 : ℕ) < 2 ^ 64 - 1 by norm_num) h'
  omega

/-! ## Cells -/

def pkCell : ℕ := 0
def msgLo : ℕ := 1
def msgHi : ℕ := 2
def lenCell : ℕ := 3
/-- The revealed word of chain `k` (signature cell `k`). -/
def wCell (k : ℕ) : ℕ := 4 + k
def nonceCell : ℕ := 46
/-- `ONE`; `(oneCell, oneCell + 1) = (ONE, g)` is the constant cv pair. -/
def oneCell : ℕ := 48
def gCell : ℕ := 49
/-- The cost constant / tag symbol `C_c` (`C_0 = ONE`). -/
def cCell (c : ℕ) : ℕ := if c = 0 then 48 else if c = 16 then 49 else 50 + c

/-- The frame constant of frame `f`: frame f reuses cost factor C_(f+1). -/
def fCell (f : ℕ) : ℕ := cCell (f + 1)

/-- The index output pair. -/
def idxCell : ℕ := 68

/-- The tie pattern of group `u`. -/
def tCell (u : ℕ) : ℕ := 70 + u

/-- The tie accumulator after group `u`; the last one is the index cell. -/
def accCell (u : ℕ) : ℕ := if u = 12 then 68 else 96 + u

/-- The landing hint of frame `f` (frame 14 uses a spare cell). -/
def hCell (f : ℕ) : ℕ := if f = 14 then 183 else 108 + f

/-- `H'_f = H_f · g`, the return address of the entry. -/
def h1Cell (f : ℕ) : ℕ := if f = 14 then 184 else 122 + f

/-- The running landing product before group `u` (`GP_0` is seeded in the free block); `GP_13` is the exit target. -/
def gpCell (u : ℕ) : ℕ := if u = 13 then 50 else 136 + u

/-- The first cv word of root call 0 (the top of chain 38). -/
def cvCell : ℕ := 150

/-- The free chain's last output pair. -/
def tfCell : ℕ := 153

/-- The selected top of exported chain k, arranged into adjacent root cv pairs: 38 and 41 for call
0, 37 below the state after call 0, 39 and 40 in the former home cells of chains 39 and 40. -/
def topCell (k : ℕ) : ℕ :=
  if k = 41 then 151 else if k = 39 then 232 else if k = 40 then 233
  else if k = 38 then 150 else if k = 37 then 236
  else if k < 3 then 155 + k else 160 + 4 * ((k - 7) / 5) + (k - 7) % 5

/-- The last output pair of an in-block home chain `k`. Chains 1, 2, 7 and 8 use the former cv
cells: the high-half tops 1 and 7 write `(xhCell k - 1, xhCell k)`. -/
def xhCell (k : ℕ) : ℕ := [0, 156, 157, 187, 189, 191, 193, 160, 161, 195, 197, 199, 0, 0, 201, 203, 205, 0, 0, 207, 209, 211, 0, 0, 213, 215, 217, 0, 0, 219, 221, 223, 0, 0, 225, 227, 229, 0, 0, 231, 233, 235].getD k 0

/-- The root state pair after call `r`. -/
def stCell (r : ℕ) : ℕ := 237 + 2 * r

/-- The intermediate pair after step `t` of chain `k`. -/
def xcCell (k t : ℕ) : ℕ := xcBase k + 2 * t
/-- The cell the root reads chain `k`'s top from, when its digit is `d`. -/
def rtopCell (k d : ℕ) : ℕ :=
  if k = 0 then (if d = 0 then wCell 0 else tfCell) else if exported k then topCell k
  else if d = 0 then wCell k else xhCell k
/-- The cv pair of root call `r`: the tops `(38, 41)`, top 37 beside the state after call 0, then
the exported top pairs `(5r+2, 5r+3)` for `r = 2 … 6`, and `(39, 40)`. -/
def rootCv (r : ℕ) : ℕ :=
  if r = 0 then cvCell else if r = 1 then 236 else if r < 7 then 156 + 4 * r else 232

/-- The metadata operand of root call `r`: its frame constant, or for the last call the low
cell of the state after call 6. -/
def rmdCell (r : ℕ) : ℕ := if r = 7 then stCell 6 else fCell r

/-- Offset selecting the high half at the final step. -/
def topOff (k : ℕ) : ℕ := if k ∈ [1, 7, 12, 17, 22, 27, 32, 37, 38, 39] then 1 else 0

theorem topOff_le (k : ℕ) : topOff k ≤ 1 := by unfold topOff; split_ifs <;> omega

/-- Coordinates whose top is materialized even for a zero digit. -/
def copied (u _i : ℕ) : Prop := isExp u
instance (u i : ℕ) : Decidable (copied u i) := by unfold copied; infer_instance

/-! ## Cell-level instructions -/

/-- An instruction over cell indices. `dispatch f` is `JUMP(ONE, H_f, F_f)`, `exit` is
`JUMP(ONE, GP_13, ONE)`, and `entry f` is the frame-shifted `I0_f`. -/
inductive CInstr
  | xor (a b c : ℕ)
  | mul (a b c : ℕ)
  | setc (a : ℕ) (v : E)
  | blake (m0 m1 m2 m3 cv out md : ℕ)
  | dispatch (f : ℕ)
  | exit
  | entry (f : ℕ)
  | pad

namespace CInstr

/-- The ISA instruction; all but `entry` address frame-1 cells `gpow c`. -/
def toInstr : CInstr → Instr
  | .xor a b c => .xor (gpow a) (gpow b) (gpow c)
  | .mul a b c => .mulNative (gpow a) (gpow b) (gpow c)
  | .setc a v => .setConstant (gpow a) v
  | .blake m0 m1 m2 m3 cv out md =>
      .blake2s ![gpow m0, gpow m1, gpow m2, gpow m3] (gpow cv) (gpow out) (gpow md)
  | .dispatch f => .jump (gpow oneCell) (gpow (hCell f)) (gpow (fCell f))
  | .exit => .jump (gpow oneCell) (gpow (gpCell 13)) (gpow oneCell)
  | .pad => .xor 0 0 0
  | .entry f => .jump (sop f oneCell) (sop f (h1Cell f)) (sop f oneCell)

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

/-- The shape invariant of every slot: all frame-1 cells below `2 ^ 16`, frames `< 15`. -/
def Bounded : CInstr → Prop
  | .xor a b c => a < 2 ^ 16 ∧ b < 2 ^ 16 ∧ c < 2 ^ 16
  | .mul a b c => a < 2 ^ 16 ∧ b < 2 ^ 16 ∧ c < 2 ^ 16
  | .setc a _ => a < 2 ^ 16
  | .blake m0 m1 m2 m3 cv out md =>
      m0 < 2 ^ 16 ∧ m1 < 2 ^ 16 ∧ m2 < 2 ^ 16 ∧ m3 < 2 ^ 16 ∧ cv + 1 < 2 ^ 16 ∧
        out + 1 < 2 ^ 16 ∧ md < 2 ^ 16
  | .dispatch f => f < 15
  | .exit => True
  | .entry f => f < 15
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

theorem ne_entry_of_straight {ci : CInstr} (h : ci.straight = true) (f : ℕ) : ci ≠ .entry f := by
  rintro rfl; simp [straight] at h

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

/-- **Frame lemma, generic form.** In frame `F_f`, every bounded instruction other than `I0_f`
fails at every memory size `κ ≤ 32`. -/
theorem exec_frame_fail {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {f : ℕ} (hf : f < 15)
    {ci : CInstr} (hb : ci.Bounded) (hne : ci ≠ .entry f) :
    LeanIsa.execute L ⟨pc, frame f⟩ ci.toInstr = pure none := by
  have first : ci ≠ .pad → (∀ j, ci ≠ .entry j) →
      LeanIsa.execute L ⟨pc, frame f⟩ ci.toInstr = pure none := fun hpad hent => by
    have ha := CInstr.cell0_lt hb hpad hent
    apply exec_none_of_first L _ ci hpad hent
    show L.read (gpow (frameExp f) * gpow ci.cell0) = none
    rw [gpow_mul_gpow]
    apply read_gpow_none hκ L
    have hb := frameExp_bounds hf
    unfold eLen at hb
    rw [mod_ord_of_lt (by unfold ordG; omega)]
    omega
  cases ci with
  | pad => exact exec_pad L _
  | entry j =>
    have hj : j < 15 := hb
    have hjk : j ≠ f := fun h => hne (h ▸ rfl)
    apply exec_entry_none hκ L pc
    have hbf := frameExp_bounds hf
    have hbj := frameExp_bounds hj
    unfold eLen at hbf hbj
    rcases Nat.lt_or_gt_of_ne hjk with h | h
    · have := frameExp_sep hf hj h
      rw [mod_ord_of_ge (by unfold ordG oneCell; omega) (by unfold ordG oneCell; omega)]
      unfold ordG oneCell; omega
    · have := frameExp_sep hj hf h
      rw [mod_ord_of_lt (by unfold ordG oneCell; omega)]
      unfold ordG oneCell; omega
  | xor a b c => exact first (by simp) (by simp)
  | mul a b c => exact first (by simp) (by simp)
  | setc a v => exact first (by simp) (by simp)
  | blake m0 m1 m2 m3 cv out md => exact first (by simp) (by simp)
  | dispatch j => exact first (by simp) (by simp)
  | exit => exact first (by simp) (by simp)

/-- In frame `1`, every entry fails: its shifted operands are out of range. -/
theorem exec_entry_frame_one {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {j : ℕ}
    (hj : j < 15) : LeanIsa.execute L ⟨pc, 1⟩ (CInstr.entry j).toInstr = pure none := by
  have hb := frameExp_bounds hj
  unfold eLen at hb
  have h := exec_entry_none (f := 0) (j := j) hκ L pc (by
    rw [mod_ord_of_lt (by unfold ordG oneCell; omega)]
    unfold ordG oneCell; omega)
  rwa [show gpow 0 = 1 from pow_zero g] at h

/-! ## The builders -/

/-- `MUL(ONE, ONE, ONE)`: the padding instruction. -/
def NOP : CInstr := .mul oneCell oneCell oneCell

/-- `MUL(a, ONE, b)`: the copy `b := a`. -/
def copy (a b : ℕ) : CInstr := .mul a oneCell b

/-- The tag position of step `t` of the `d` steps of chain `k`. -/
def tpos (k d t : ℕ) : ℕ := OFFT k + (LEN k - 1 - d + t)

/-- Step `t` of the `d` steps of chain `k` (the last writes `dst`): position `LEN k − 1 − d + t`,
tag cells `C` of the base-9 digits of its tag position, cv pair `(ONE, g)`, metadata `ONE`. -/
def chainOp (k d t dst : ℕ) : CInstr :=
  .blake (if t = 0 then wCell k else xcCell k (t - 1))
    (cCell (tpos k d t % 9)) (cCell (tpos k d t / 9 % 9)) (cCell (tpos k d t / 81))
    oneCell (if t + 1 = d then dst - topOff k else xcCell k t) oneCell

/-- The `d` steps of chain `k`. -/
def chainOps (k d dst : ℕ) : List CInstr := (List.range d).map (fun t => chainOp k d t dst)

/-- The straight part of the prologue (slots `0 … 19`). -/
def proList : List CInstr :=
  [.setc oneCell oneV, .setc lenCell (natV 5503), .setc gCell gV] ++
    ((List.range 15).map (fun c => .setc (cCell (c + 1)) (cV (c + 1)))) ++
    [.blake msgLo msgHi nonceCell pkCell oneCell idxCell gCell, .mul (hCell 0) gCell (h1Cell 0)]

/-- Slots `0 … 21`: the straight prologue, the free chain's dispatch (slot `20`), and a pad
(slot `21`, never reached). -/
def prologue (s : ℕ) : CInstr :=
  if s < 20 then proList.getD s .pad else if s = 20 then .dispatch 0 else .pad

/-- The control op after the block of group `f - 1`: the next dispatch, or the exit. -/
def ctlF (f : ℕ) : CInstr := if f < 13 then .dispatch (f + 1) else .exit

/-- The frame of the first group after the free block of digit `s`: frame 14 when `s = 0` (its
root call reads the free top from the signature cell), frame 1 otherwise. -/
def frG0 (s : ℕ) : ℕ := if s = 0 then 14 else 1

/-- The straight part of the free chain's block of digit `s`: the seed, the `s` chain steps, and
the first group's `MUL(H, g, H')`. -/
def fbody (s : ℕ) : List CInstr :=
  [.setc (gpCell 0) (ofK (LeanIsaFieldRescale.initialProduct 96 s))] ++
  (if s = 0 then [] else chainOps 0 s tfCell) ++ [.mul (hCell (frG0 s)) gCell (h1Cell (frG0 s))]

/-- The tie of field value `v` of group `u`. -/
def tie (u v : ℕ) : List CInstr :=
  if u = 0 then [.setc (accCell 0) (fpat 0 v)]
  else if v = 0 then [copy (accCell (u - 1)) (accCell u)]
  else [.setc (tCell u) (fpat u v), .xor (accCell (u - 1)) (tCell u) (accCell u)]

/-- The ops of coordinate `i` of the block of `v` in group `u`. -/
def seg (T : Tab) (u v i : ℕ) : List CInstr :=
  if copied u i then
    (if T u v i = 0 then [copy (wCell (chainOf u i)) (topCell (chainOf u i))]
      else chainOps (chainOf u i) (T u v i) (topCell (chainOf u i)))
  else chainOps (chainOf u i) (T u v i) (xhCell (chainOf u i))

/-- The chain ops of the block of `v` in group `u`. -/
def segs (T : Tab) (u v : ℕ) : List CInstr := (List.range (gk u)).flatMap (seg T u v)

/-- Zero digits of an exporter block (each costs one copy). -/
def zexp (T : Tab) (u v : ℕ) : ℕ :=
  ((List.range (gk u)).map (fun i => if copied u i ∧ T u v i = 0 then 1 else 0)).sum

/-- The root call a home group executes: call 1 in group 0, calls 0 and 7 in groups 5 and 6, call
`u − 5` in groups `7 … 11`. -/
def hcall (u : ℕ) : ℕ := if u = 0 then 1 else if u = 5 then 0 else if u = 6 then 7 else u - 5

/-- The message cell `j < 4` of root call `hcall u` in the home block of `v`; the first group's
variant `z` (free digit `0`) reads the free top from its signature cell. -/
def rt (T : Tab) (u v : ℕ) (z : Bool) (j : ℕ) : ℕ :=
  if u = 0 then
    (if j = 0 then (if z then wCell 0 else tfCell) else rtopCell (chainOf 0 (j - 1)) (T u v (j - 1)))
  else if u = 5 then rtopCell (3 + j) (T u v j)
  else if u = 6 then rtopCell (8 + j) (T u v j)
  else if j = 0 then stCell (u - 6)
  else rtopCell (5 * (u - 5) + 3 + j) (T u v (j - 1))

/-- The root call of a home block. -/
def rootIns (T : Tab) (u v : ℕ) (z : Bool) : List CInstr :=
  if u = 0 ∨ (5 ≤ u ∧ u < 12) then
    [.blake (rt T u v z 0) (rt T u v z 1) (rt T u v z 2) (rt T u v z 3) (rootCv (hcall u))
      (stCell (hcall u)) (rmdCell (hcall u))]
  else []

/-- Padding to the unit's constant non-hash count. -/
def npad (T : Tab) (u v : ℕ) : ℕ := gcu u - 4 - (tie u v).length - zexp T u v

/-- The last straight op: the next group's `MUL(H, g, H')`, or the public-key copy. -/
def nextOp (u : ℕ) : CInstr :=
  if u < 12 then .mul (hCell (u + 2)) gCell (h1Cell (u + 2)) else copy (stCell 7) pkCell

/-- The product op of the block of `v` in group `u`. -/
def prodOp (T : Tab) (u v : ℕ) : CInstr := .mul (gpCell u) (cCell (cost T u v)) (gpCell (u + 1))

/-- The straight part of the block of `v` in group `u`, variant `z`. -/
def body (T : Tab) (u v : ℕ) (z : Bool) : List CInstr :=
  tie u v ++ [prodOp T u v] ++ segs T u v ++ rootIns T u v z ++ List.replicate (npad T u v) NOP ++
    [nextOp u]

/-- Op `i` of the block of `v` in group `u`, variant `z` (entered in frame 14 when set). -/
def blockInstr (T : Tab) (u v : ℕ) (z : Bool) (i : ℕ) : CInstr :=
  if i = 0 then .entry (if z then 14 else u + 1)
  else if i ≤ (body T u v z).length then (body T u v z).getD (i - 1) .pad
  else if i = (body T u v z).length + 1 then ctlF (u + 1) else .pad

/-- Op `i` of the free chain's block of digit `s`. -/
def fblockInstr (s i : ℕ) : CInstr :=
  if i = 0 then .entry 0
  else if i ≤ (fbody s).length then (fbody s).getD (i - 1) .pad
  else if i = (fbody s).length + 1 then .dispatch (frG0 s) else .pad

/-- The cell-level instruction at slot `s`, decoded by segment. -/
def cinstrAt (T : Tab) (s : ℕ) : CInstr :=
  if s < 22 then prologue s
  else if s < gEnd then blockInstr T (dec s).1 (dec s).2.1 false (dec s).2.2
  else if s < zEnd then blockInstr T 0 (dec (s - zOff)).2.1 true (dec (s - zOff)).2.2
  else if s < baseF then .pad
  else if s < baseF + 4352 then fblockInstr ((s - baseF) / 68) ((s - baseF) % 68)
  else .pad

/-- The ISA instruction at slot `s`. -/
abbrev instrAt (T : Tab) (s : ℕ) : Instr := (cinstrAt T s).toInstr

/-- The bytecode: `2 ^ 18` slots, sentinel at `2 ^ 18 - 1`. -/
def program (T : Tab) : Program where
  logSize := 18
  logSize_le := by decide
  code i := (cinstrAt T i).toInstr

theorem program_logSize (T : Tab) : (program T).logSize = 18 := rfl

/- The builders are irreducible: elaboration never unfolds a block or a slot decode. -/
attribute [irreducible] proList prologue fbody body blockInstr
  fblockInstr cinstrAt

/-! ## Units -/

/-- The group of frame `f ≥ 1`: frame 14 is the first group's `s = 0` variant. -/
def gOf (f : ℕ) : ℕ := if f = 14 then 0 else f - 1

/-- The block variant of frame `f`. -/
def zOf (f : ℕ) : Bool := decide (f = 14)

/-- Entries of frame `f`: `64` for the free chain, `VF u` for group `u`. -/
def Wf (f : ℕ) : ℕ := if f = 0 then 64 else VF (gOf f)

/-- The entry of index `x` of frame `f`. -/
def ent (f x : ℕ) : ℕ :=
  if f = 0 then entF x else if f = 14 then entryOf 0 x + zOff else entryOf (f - 1) x

/-- The straight part of the block of index `x` of frame `f`. -/
def bodyF (T : Tab) (f x : ℕ) : List CInstr := if f = 0 then fbody x else body T (gOf f) x (zOf f)

/-- The index of the entry slot `e` of frame `f`. -/
def xOf (f e : ℕ) : ℕ :=
  if f = 0 then (e - baseF) / 68 else if f = 14 then (dec (e - zOff)).2.1 else (dec e).2.1

/-- `e` is an entry `I0_f` of frame `f`. -/
def IsEntry (f e : ℕ) : Prop := f < 15 ∧ ∃ x < Wf f, e = ent f x

theorem ent_zero (x : ℕ) : ent 0 x = entF x := rfl
theorem ent_succ {u : ℕ} (hu : u < 13) (x : ℕ) : ent (u + 1) x = entryOf u x := by
  unfold ent; rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
theorem ent_14 (x : ℕ) : ent 14 x = entryOf 0 x + zOff := rfl
theorem bodyF_zero (T : Tab) (x : ℕ) : bodyF T 0 x = fbody x := rfl
theorem bodyF_succ (T : Tab) {u : ℕ} (hu : u < 13) (x : ℕ) : bodyF T (u + 1) x = body T u x false := by
  have h1 : gOf (u + 1) = u := by unfold gOf; rw [if_neg (by omega), Nat.add_sub_cancel]
  have h2 : zOf (u + 1) = false := decide_eq_false (by omega)
  unfold bodyF; rw [if_neg (by omega), h1, h2]
theorem bodyF_14 (T : Tab) (x : ℕ) : bodyF T 14 x = body T 0 x true := rfl
theorem Wf_zero : Wf 0 = 64 := rfl
theorem Wf_succ {u : ℕ} (hu : u < 13) : Wf (u + 1) = VF u := by
  unfold Wf gOf; rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
theorem Wf_14 : Wf 14 = VF 0 := rfl

theorem xOf_ent {f x : ℕ} (hf : f < 15) (hx : x < Wf f) : xOf f (ent f x) = x := by
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · unfold xOf ent entF; rw [if_pos rfl, if_pos rfl]; omega
  · by_cases h14 : f = 14
    · subst f
      rw [Wf_14] at hx
      unfold xOf; rw [if_neg (by omega), if_pos rfl, ent_14, Nat.add_sub_cancel]
      have := dec_entry (i := 0) (by omega) hx (by have := L_pos 0 (band 0 x); omega)
      rw [Nat.add_zero] at this
      rw [this]
    · obtain ⟨u, rfl⟩ : ∃ u, f = u + 1 := ⟨f - 1, by omega⟩
      rw [Wf_succ (by omega)] at hx
      unfold xOf; rw [if_neg (by omega), if_neg h14, ent_succ (by omega)]
      have := dec_entry (i := 0) (by omega) hx (by have := L_pos u (band u x); omega)
      rw [Nat.add_zero] at this
      rw [this]

/-- The index of an entry determines it. -/
theorem isEntry_eq {f e : ℕ} (h : IsEntry f e) : xOf f e < Wf f ∧ e = ent f (xOf f e) := by
  obtain ⟨hf, x, hx, rfl⟩ := h
  rw [xOf_ent hf hx]; exact ⟨hx, rfl⟩

/-! ## Straightness, lengths and costs of the blocks -/

/-- Total cycles of a list of walk steps. -/
def lcost (l : List CInstr) : ℕ := (l.map CInstr.cost).sum

theorem lcost_append (a b : List CInstr) : lcost (a ++ b) = lcost a + lcost b := by
  unfold lcost; rw [List.map_append, List.sum_append]

theorem lcost_cons (x : CInstr) (l : List CInstr) : lcost (x :: l) = x.cost + lcost l := by
  unfold lcost; rw [List.map_cons, List.sum_cons]

theorem lcost_nil : lcost [] = 0 := rfl

theorem lcost_flatMap (f : ℕ → List CInstr) (l : List ℕ) :
    lcost (l.flatMap f) = (l.map (fun i => lcost (f i))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, lcost_append, ih, List.map_cons, List.sum_cons]

theorem lcost_replicate (n : ℕ) (x : CInstr) : lcost (List.replicate n x) = n * x.cost := by
  unfold lcost; rw [List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem chainOps_length (k d dst : ℕ) : (chainOps k d dst).length = d := by
  unfold chainOps; rw [List.length_map, List.length_range]

theorem chainOps_lcost (k d dst : ℕ) : lcost (chainOps k d dst) = 10 * d := by
  unfold chainOps lcost
  rw [List.map_map]
  have : (CInstr.cost ∘ fun t => chainOp k d t dst) = fun _ => 10 := by
    funext t; rfl
  rw [this, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, mul_comm]

theorem mem_chainOps {k d dst : ℕ} {x : CInstr} :
    x ∈ chainOps k d dst ↔ ∃ t < d, x = chainOp k d t dst := by
  unfold chainOps
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, List.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, List.mem_range.mpr ht, rfl⟩

theorem chainOp_straight (k d t dst : ℕ) : (chainOp k d t dst).straight = true := rfl

theorem tie_straight {u v : ℕ} : ∀ x ∈ tie u v, x.straight = true := by
  intro x hx; unfold tie at hx; split_ifs at hx <;> simp at hx <;>
    (try rcases hx with rfl | rfl) <;> rfl

theorem seg_straight (T : Tab) {u v i : ℕ} : ∀ x ∈ seg T u v i, x.straight = true := by
  intro x hx
  unfold seg at hx
  split_ifs at hx
  · simp at hx; subst hx; rfl
  · obtain ⟨t, -, rfl⟩ := mem_chainOps.mp hx; rfl
  · obtain ⟨t, -, rfl⟩ := mem_chainOps.mp hx; rfl

theorem mem_segs {T : Tab} {u v : ℕ} {x : CInstr} :
    x ∈ segs T u v ↔ ∃ i < gk u, x ∈ seg T u v i := by
  unfold segs
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨i, hi, hx⟩; exact ⟨i, List.mem_range.mp hi, hx⟩
  · rintro ⟨i, hi, hx⟩; exact ⟨i, List.mem_range.mpr hi, hx⟩

theorem rootIns_straight (T : Tab) {u v : ℕ} {z : Bool} : ∀ x ∈ rootIns T u v z, x.straight = true := by
  intro x hx
  unfold rootIns at hx
  split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl <;> rfl

theorem nextOp_straight (u : ℕ) : (nextOp u).straight = true := by
  unfold nextOp; split_ifs <;> rfl

/-- Every op of a group block's straight part is straight. -/
theorem body_straight (T : Tab) (u v : ℕ) (z : Bool) : ∀ x ∈ body T u v z, x.straight = true := by
  intro x hx
  unfold body at hx
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hx
  rcases hx with ((((h | h) | h) | h) | h) | h
  · exact tie_straight x h
  · subst h; rfl
  · obtain ⟨i, -, hi⟩ := mem_segs.mp h; exact seg_straight T x hi
  · exact rootIns_straight T x h
  · rw [h.2]; rfl
  · subst h; exact nextOp_straight u

/-- Every op of the free block's straight part is straight. -/
theorem fbody_straight (s : ℕ) : ∀ x ∈ fbody s, x.straight = true := by
  intro x hx
  unfold fbody at hx
  split_ifs at hx
  · simp at hx; rcases hx with rfl | rfl <;> rfl
  · simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (rfl | h) | rfl
    · rfl
    · obtain ⟨t, -, rfl⟩ := mem_chainOps.mp h; rfl
    · rfl

theorem bodyF_straight (T : Tab) (f x : ℕ) : ∀ y ∈ bodyF T f x, y.straight = true := by
  unfold bodyF; split_ifs
  · exact fbody_straight x
  · exact body_straight T _ x _

/-- The unit cost of frame `f`: `4` for the free chain. -/
def gcuF (f : ℕ) : ℕ := if f = 0 then 4 else gcu (gOf f)

/-- Hashes of the block of `x` in frame `f` beyond the root call. -/
def cF (T : Tab) (f x : ℕ) : ℕ := if f = 0 then x else cost T (gOf f) x

/-- Root calls of frame `f`'s blocks. -/
def hmF (f : ℕ) : ℕ := if f = 0 then 0 else hm (gOf f)

theorem fbody_len (s : ℕ) : (fbody s).length = 2 + s := by
  unfold fbody; split_ifs with h
  · subst h; rfl
  · simp only [List.length_append, chainOps_length, List.length_singleton]; omega

theorem fbody_lcost (s : ℕ) : lcost (fbody s) = 2 + 10 * s := by
  unfold fbody; split_ifs with h
  · subst h; rfl
  · simp only [lcost_append, chainOps_lcost]; simp [lcost, CInstr.cost]; omega

theorem tie_len (u v : ℕ) : (tie u v).length = if u ≠ 0 ∧ v ≠ 0 then 2 else 1 := by
  unfold tie; split_ifs <;> simp_all

theorem tie_lcost (u v : ℕ) : lcost (tie u v) = (tie u v).length := by
  unfold tie; split_ifs <;> rfl

theorem seg_len (T : Tab) (u v i : ℕ) :
    (seg T u v i).length = T u v i + (if copied u i ∧ T u v i = 0 then 1 else 0) := by
  unfold seg; split_ifs with h1 h2 <;> simp_all [chainOps_length]

theorem seg_lcost (T : Tab) (u v i : ℕ) :
    lcost (seg T u v i) = 10 * T u v i + (if copied u i ∧ T u v i = 0 then 1 else 0) := by
  unfold seg
  by_cases h1 : copied u i
  · rw [if_pos h1]
    by_cases h2 : T u v i = 0
    · rw [if_pos h2, if_pos ⟨h1, h2⟩, h2]; rfl
    · rw [if_neg h2, chainOps_lcost, if_neg (fun h => h2 h.2), Nat.add_zero]
  · rw [if_neg h1, chainOps_lcost, if_neg (fun h => h1 h.1), Nat.add_zero]

theorem segs_len (T : Tab) (u v : ℕ) : (segs T u v).length = cost T u v + zexp T u v := by
  unfold segs cost zexp
  rw [List.length_flatMap, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  exact seg_len T u v i

theorem segs_lcost (T : Tab) (u v : ℕ) : lcost (segs T u v) = 10 * cost T u v + zexp T u v := by
  unfold segs cost zexp
  rw [lcost_flatMap, ← List.sum_map_mul_left, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  exact seg_lcost T u v i

theorem rootIns_len (T : Tab) (u v : ℕ) (z : Bool) : (rootIns T u v z).length = hm u := by
  unfold rootIns hm; split_ifs <;> (try omega) <;> rfl

theorem rootIns_lcost (T : Tab) (u v : ℕ) (z : Bool) : lcost (rootIns T u v z) = 10 * hm u := by
  unfold rootIns hm; split_ifs <;> (try omega) <;> rfl

/-- Home groups copy nothing: their zero-digit tops are read from the signature cells. -/
theorem zexp_home (T : Tab) {u v : ℕ} (hu : ¬ isExp u) : zexp T u v = 0 := by
  have hcopy : ∀ i, ¬ copied u i := fun _ => hu
  simp [zexp, hcopy]

theorem zexp_le (T : Tab) (u v : ℕ) (hc : 1 ≤ cost T u v) : zexp T u v ≤ 2 := by
  by_cases hu : isExp u
  · have hk : gk u = 3 := by unfold gk; rw [if_neg (by unfold isExp at hu; omega)]
    have hcopy : ∀ i, copied u i := fun _ => hu
    unfold cost at hc
    simp only [zexp, hk, hcopy, true_and, show List.range 3 = [0, 1, 2] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hc ⊢
    split_ifs <;> omega
  · rw [zexp_home T hu]; omega

theorem zexp_le3 (T : Tab) (u v : ℕ) : zexp T u v ≤ 3 := by
  by_cases hu : isExp u
  · have hk : gk u = 3 := by unfold gk; rw [if_neg (by unfold isExp at hu; omega)]
    have hcopy : ∀ i, copied u i := fun _ => hu
    simp only [zexp, hk, hcopy, true_and, show List.range 3 = [0, 1, 2] from rfl,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega
  · rw [zexp_home T hu]; omega

/-- Outside the first group, a band `0` value is the origin `v = 0`. -/
theorem band_pos {u v : ℕ} (hu : u < 13) (hv : v < VF u) (hu0 : u ≠ 0) (hz : v ≠ 0) :
    1 ≤ band u v := by
  obtain ⟨-, -, h2⟩ := band_spec hu hv
  by_contra h0
  have h0' : band u v = 0 := by omega
  rw [h0', A_succ, show A u 0 = 0 from rfl, Nat.zero_add] at h2
  have hp : pn u 0 = 1 := by
    unfold pn prof
    rw [if_neg hu0]
    split_ifs <;> rfl
  rw [hp] at h2
  omega

/-- The padding is exact: the tie and the exporter copies fit the unit's count. -/
theorem pad_fit {T : Tab} (hT : T.Hyp) {u v : ℕ} (hu : u < 13) (hv : v < VF u) :
    (tie u v).length + zexp T u v + 4 ≤ gcu u := by
  rw [tie_len]
  have h3 := zexp_le3 T u v
  by_cases hh : isExp u
  · have hu0 : u ≠ 0 := by unfold isExp at hh; omega
    have hg : gcu u = 8 := by unfold gcu; rw [if_neg hu0, if_pos hh]
    rw [hg]
    by_cases hz : v ≠ 0
    · have hc : 1 ≤ cost T u v := by rw [hT.cost_eq u hu v hv]; exact band_pos hu hv hu0 hz
      have := zexp_le T u v hc
      split_ifs <;> omega
    · split_ifs <;> omega
  · have := zexp_home T (v := v) hh
    have hg : gcu u = if u = 0 then 5 else 6 := by
      unfold gcu; by_cases h0 : u = 0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg hh, if_neg h0]
    rw [hg]
    split_ifs <;> omega

theorem body_len {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    (body T u v z).length = gcu u - 2 + cost T u v + hm u := by
  have hfit := pad_fit hT hu hv
  unfold body npad
  simp only [List.length_append, List.length_singleton, List.length_replicate, segs_len,
    rootIns_len]
  omega

theorem body_lcost {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    lcost (body T u v z) = gcu u - 2 + 10 * (cost T u v + hm u) := by
  have hfit := pad_fit hT hu hv
  unfold body npad
  rw [lcost_append, lcost_append, lcost_append, lcost_append, lcost_append, tie_lcost,
    segs_lcost, rootIns_lcost, lcost_replicate]
  have h1 : lcost [prodOp T u v] = 1 := rfl
  have h2 : lcost [nextOp u] = 1 := by unfold nextOp; split_ifs <;> rfl
  have h3 : NOP.cost = 1 := rfl
  rw [h1, h2, h3]
  omega

/-- The block of `v` in group `u` has the band's length. -/
theorem body_len_L {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    (body T u v z).length + 2 = L u (band u v) := by
  rw [body_len hT hu hv, hT.cost_eq u hu v hv]
  unfold L gcu; split_ifs <;> omega

theorem gcuF_zero : gcuF 0 = 4 := rfl
theorem cF_zero (T : Tab) (x : ℕ) : cF T 0 x = x := rfl
theorem hmF_zero : hmF 0 = 0 := rfl

theorem gOf_lt {f : ℕ} (hf0 : f ≠ 0) (hf : f < 15) : gOf f < 13 := by
  unfold gOf; split_ifs <;> omega

theorem bodyF_pos (T : Tab) {f : ℕ} (hf0 : f ≠ 0) (x : ℕ) :
    bodyF T f x = body T (gOf f) x (zOf f) := if_neg hf0

theorem Wf_pos {f : ℕ} (hf0 : f ≠ 0) : Wf f = VF (gOf f) := if_neg hf0

theorem bodyF_len {T : Tab} (hT : T.Hyp) {f x : ℕ} (hf : f < 15) (hx : x < Wf f) :
    (bodyF T f x).length = gcuF f - 2 + cF T f x + hmF f := by
  by_cases hf0 : f = 0
  · subst hf0; rw [bodyF_zero, fbody_len, gcuF_zero, cF_zero, hmF_zero]; omega
  · rw [Wf_pos hf0] at hx
    rw [bodyF_pos T hf0, body_len hT (gOf_lt hf0 hf) hx]
    unfold gcuF cF hmF; rw [if_neg hf0, if_neg hf0, if_neg hf0]

theorem bodyF_lcost {T : Tab} (hT : T.Hyp) {f x : ℕ} (hf : f < 15) (hx : x < Wf f) :
    lcost (bodyF T f x) = gcuF f - 2 + 10 * (cF T f x + hmF f) := by
  by_cases hf0 : f = 0
  · subst hf0; rw [bodyF_zero, fbody_lcost, gcuF_zero, cF_zero, hmF_zero]; omega
  · rw [Wf_pos hf0] at hx
    rw [bodyF_pos T hf0, body_lcost hT (gOf_lt hf0 hf) hx]
    unfold gcuF cF hmF; rw [if_neg hf0, if_neg hf0, if_neg hf0]

/-! ## Boundedness -/

theorem chainOp_bounded {k d t dst : ℕ} (hk : k < 42) (ht : t < d) (hd : d ≤ 64)
    (hdst : dst + 1 < 2 ^ 16) : (chainOp k d t dst).Bounded := by
  have hx := xcBase_bound k hk
  have hL := LEN_le k hk
  unfold chainOp
  simp only [CInstr.Bounded, cCell, oneCell]
  refine ⟨?_, ?_, ?_, ?_, by norm_num, ?_, by norm_num⟩
  · unfold wCell xcCell; split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · have : tpos k d t / 81 < 64 := by
      have := OFFT_bound k hk; unfold tpos; omega
    split_ifs <;> omega
  · unfold xcCell; split_ifs <;> omega

theorem topCell_lt {k : ℕ} (hk : k < 42) : topCell k + 1 < 240 := by
  unfold topCell; split_ifs <;> omega

theorem xhCell_lt {k : ℕ} (hk : k < 42) : xhCell k + 1 < 300 := by
  have h : ∀ k < 42, xhCell k + 1 < 300 := by decide
  exact h k hk

theorem rtopCell_lt {k d : ℕ} (hk : k < 42) : rtopCell k d < 300 := by
  have := topCell_lt hk; have := xhCell_lt hk
  unfold rtopCell wCell tfCell; split_ifs <;> omega

theorem rt_lt (T : Tab) {u v : ℕ} {z : Bool} {j : ℕ} (hu : u < 13) (hj : j < 4) : rt T u v z j < 300 := by
  unfold rt
  split_ifs <;> first
    | (unfold wCell; omega)
    | (unfold tfCell; omega)
    | (unfold stCell; omega)
    | exact rtopCell_lt (by omega)
    | exact rtopCell_lt (chainOf_lt 0 (by omega) _ (by show j - 1 < 3; omega))

theorem rootIns_bounded (T : Tab) {u v : ℕ} {z : Bool} (hu : u < 13) :
    ∀ x ∈ rootIns T u v z, x.Bounded := by
  intro x hx
  unfold rootIns at hx
  split_ifs at hx
  · simp only [List.mem_singleton] at hx
    subst x
    have b0 := rt_lt T (v := v) (z := z) hu (j := 0) (by omega)
    have b1 := rt_lt T (v := v) (z := z) hu (j := 1) (by omega)
    have b2 := rt_lt T (v := v) (z := z) hu (j := 2) (by omega)
    have b3 := rt_lt T (v := v) (z := z) hu (j := 3) (by omega)
    simp only [CInstr.Bounded, rootCv, rmdCell, stCell, fCell, cCell, hcall, oneCell, cvCell]
    split_ifs <;> omega
  · simp at hx

theorem body_bounded {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} (hu : u < 13) (hv : v < VF u) :
    ∀ x ∈ body T u v z, x.Bounded := by
  intro x hx
  unfold body at hx
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hx
  rcases hx with ((((h | h) | h) | h) | h) | h
  · unfold tie at h
    split_ifs at h <;> simp at h <;> (try rcases h with rfl | rfl) <;>
      simp only [CInstr.Bounded, accCell, tCell, copy, oneCell] <;> (try split_ifs) <;> omega
  · subst h
    have := band_lt_17 hu hv
    rw [← hT.cost_eq u hu v hv] at this
    simp only [prodOp, CInstr.Bounded, gpCell, cCell]
    split_ifs <;> omega
  · obtain ⟨i, hi, hx⟩ := mem_segs.mp h
    have hk := chainOf_lt u hu i hi
    have hd := hT.coord_lt u hu v (lt_of_lt_of_le hv (VF_le u hu)) i hi
    have hL := LEN_le _ hk
    unfold seg at hx
    split_ifs at hx
    · simp at hx; subst hx
      have := topCell_lt hk
      simp only [copy, CInstr.Bounded, wCell, oneCell]; omega
    · obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp hx
      exact chainOp_bounded hk ht (by omega) (by have := topCell_lt hk; omega)
    · obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp hx
      exact chainOp_bounded hk ht (by omega) (by have := xhCell_lt hk; omega)
  · exact rootIns_bounded T hu x h
  · rw [h.2]; simp only [NOP, CInstr.Bounded, oneCell]; omega
  · subst h; unfold nextOp; split_ifs <;> simp only [CInstr.Bounded, copy, hCell, gCell, h1Cell,
      stCell, oneCell, pkCell] <;> (try split_ifs) <;> omega

theorem fbody_bounded (s : ℕ) (hs : s < 64) : ∀ x ∈ fbody s, x.Bounded := by
  intro x hx
  unfold fbody at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (rfl | h) | rfl
  · change 136 < 2 ^ 16; norm_num
  · split_ifs at h
    · simp at h
    · obtain ⟨t, ht, rfl⟩ := mem_chainOps.mp h
      exact chainOp_bounded (by omega) ht (by omega) (by unfold tfCell; omega)
  · simp only [CInstr.Bounded, hCell, gCell, h1Cell, frG0]; split_ifs <;> omega

theorem proList_length : proList.length = 20 := by unfold proList; rfl

theorem proList_straight : ∀ x ∈ proList, x.straight = true := by
  intro x hx
  unfold proList at hx
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hx
  rcases hx with ((rfl | rfl | rfl) | ⟨c, -, rfl⟩) | rfl | rfl <;> rfl

theorem proList_bounded : ∀ x ∈ proList, x.Bounded := by
  intro x hx
  unfold proList at hx
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hx
  rcases hx with ((rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl | rfl <;>
    simp only [CInstr.Bounded, cCell, oneCell, lenCell, gCell, msgLo, msgHi,
      nonceCell, pkCell, idxCell, hCell, h1Cell] <;> (try split_ifs) <;> omega

theorem getD_mem_or {l : List CInstr} {i : ℕ} : l.getD i .pad ∈ l ∨ l.getD i .pad = .pad := by
  by_cases h : i < l.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; rw [List.getD_eq_default _ _ (by omega)]

theorem prologue_bounded (s : ℕ) : (prologue s).Bounded := by
  unfold prologue
  split_ifs
  · rcases getD_mem_or (l := proList) (i := s) with h | h
    · exact proList_bounded _ h
    · rw [h]; trivial
  · show 0 < 15; omega
  · trivial

theorem ctlF_bounded {f : ℕ} (hf : f < 14) : (ctlF f).Bounded := by
  unfold ctlF; split_ifs
  · show f + 1 < 15; omega
  · trivial

theorem blockInstr_bounded {T : Tab} (hT : T.Hyp) {u v : ℕ} {z : Bool} {i : ℕ} (hu : u < 13)
    (hv : v < VF u) : (blockInstr T u v z i).Bounded := by
  unfold blockInstr
  by_cases h0 : i = 0
  · rw [if_pos h0]; show (if z = true then 14 else u + 1) < 15; split_ifs <;> omega
  rw [if_neg h0]
  split_ifs
  · rcases getD_mem_or (l := body T u v z) (i := i - 1) with h | h
    · exact body_bounded hT hu hv _ h
    · rw [h]; trivial
  · exact ctlF_bounded (by omega)
  · trivial

theorem fblockInstr_bounded {s i : ℕ} (hs : s < 64) : (fblockInstr s i).Bounded := by
  unfold fblockInstr
  split_ifs
  · show 0 < 15; omega
  · rcases getD_mem_or (l := fbody s) (i := i - 1) with h | h
    · exact fbody_bounded s hs _ h
    · rw [h]; trivial
  · show frG0 s < 15; unfold frG0; split_ifs <;> omega
  · trivial

/-- A slot of the frame-14 region is a slot of the first group's region, shifted by `zOff`. -/
theorem zdec_spec {s : ℕ} (h1 : gEnd ≤ s) (h2 : s < zEnd) :
    (dec (s - zOff)).1 = 0 ∧ (dec (s - zOff)).2.1 < VF 0 ∧
      (dec (s - zOff)).2.2 < L 0 (band 0 (dec (s - zOff)).2.1) ∧
      s - zOff = entryOf 0 (dec (s - zOff)).2.1 + (dec (s - zOff)).2.2 := by
  have e1 : 22 ≤ s - zOff := by unfold gEnd zOff at *; omega
  have e2 : s - zOff < gEnd := by unfold gEnd zEnd zOff at *; omega
  obtain ⟨hu, hv, hi, hs⟩ := dec_spec e1 e2
  have hr := entry_region hu hv hi
  rw [← hs] at hr
  have h0 : (dec (s - zOff)).1 = 0 := by
    by_contra hne
    have := BASE_mono (show 1 ≤ (dec (s - zOff)).1 by omega)
    rw [BASE_one] at this
    unfold zEnd zOff at *; omega
  rw [h0] at hv hi hs
  exact ⟨h0, hv, hi, hs⟩

theorem cinstrAt_cases (T : Tab) (s : ℕ) :
    (s < 22 ∧ cinstrAt T s = prologue s) ∨
    (22 ≤ s ∧ s < gEnd ∧ cinstrAt T s = blockInstr T (dec s).1 (dec s).2.1 false (dec s).2.2) ∨
    (gEnd ≤ s ∧ s < zEnd ∧
      cinstrAt T s = blockInstr T 0 (dec (s - zOff)).2.1 true (dec (s - zOff)).2.2) ∨
    (baseF ≤ s ∧ s < baseF + 4352 ∧
      cinstrAt T s = fblockInstr ((s - baseF) / 68) ((s - baseF) % 68)) ∨
    cinstrAt T s = .pad := by
  unfold cinstrAt
  by_cases h1 : s < 22
  · left; exact ⟨h1, if_pos h1⟩
  rw [if_neg h1]
  by_cases h2 : s < gEnd
  · right; left; exact ⟨by omega, h2, if_pos h2⟩
  rw [if_neg h2]
  by_cases h2' : s < zEnd
  · right; right; left; exact ⟨by omega, h2', if_pos h2'⟩
  rw [if_neg h2']
  by_cases h3 : s < baseF
  · right; right; right; right; exact if_pos h3
  rw [if_neg h3]
  by_cases h4 : s < baseF + 4352
  · right; right; right; left; exact ⟨by omega, h4, if_pos h4⟩
  · right; right; right; right; exact if_neg h4

/-- Every slot satisfies the shape invariant. -/
theorem cinstrAt_bounded {T : Tab} (hT : T.Hyp) (s : ℕ) : (cinstrAt T s).Bounded := by
  rcases cinstrAt_cases T s with ⟨-, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | h <;> rw [h]
  · exact prologue_bounded s
  · obtain ⟨hu, hv, -, -⟩ := dec_spec h1 h2
    exact blockInstr_bounded hT hu hv
  · obtain ⟨-, hv, -, -⟩ := zdec_spec h1 h2
    exact blockInstr_bounded hT (by omega) hv
  · have hs : (s - baseF) / 68 < 64 := by
      rw [show baseF = 255615 from rfl] at h1 h2 ⊢; omega
    exact fblockInstr_bounded hs
  · trivial

/-! ## Segment decoding -/

theorem cinstrAt_pro (T : Tab) {s : ℕ} (h : s < 22) : cinstrAt T s = prologue s := by
  unfold cinstrAt; rw [if_pos h]

theorem cinstrAt_grp (T : Tab) {u v i : ℕ} (hu : u < 13) (hv : v < VF u)
    (hi : i < L u (band u v)) : cinstrAt T (entryOf u v + i) = blockInstr T u v false i := by
  have h1 := entryOf_ge hu hv
  have h2 := block_lt_gEnd hu hv hi
  unfold cinstrAt
  rw [if_neg (by omega), if_pos h2, dec_entry hu hv hi]

theorem cinstrAt_grpZ (T : Tab) {v i : ℕ} (hv : v < VF 0) (hi : i < L 0 (band 0 v)) :
    cinstrAt T (entryOf 0 v + zOff + i) = blockInstr T 0 v true i := by
  have h1 := entryOf_ge (u := 0) (by omega) hv
  have hr := (entry_region (u := 0) (by omega) hv hi).2
  rw [BASE_one] at hr
  unfold cinstrAt
  rw [if_neg (by omega), if_neg (by unfold gEnd zOff; omega),
    if_pos (by unfold zEnd zOff; omega), show entryOf 0 v + zOff + i - zOff = entryOf 0 v + i by omega,
    dec_entry (u := 0) (by omega) hv hi]

theorem cinstrAt_free (T : Tab) {s i : ℕ} (hs : s < 64) (hi : i < 68) :
    cinstrAt T (entF s + i) = fblockInstr s i := by
  unfold cinstrAt entF
  rw [if_neg (by unfold baseF; omega), if_neg (by unfold baseF gEnd; omega),
    if_neg (by unfold baseF zEnd; omega),
    if_neg (by omega), if_pos (by omega),
    show (baseF + 68 * s + i - baseF) / 68 = s by omega,
    show (baseF + 68 * s + i - baseF) % 68 = i by omega]

theorem cinstrAt_sentinel (T : Tab) : cinstrAt T sentinel = .pad := by
  unfold cinstrAt sentinel
  rw [if_neg (by omega), if_neg (by unfold gEnd; omega), if_neg (by unfold zEnd; omega),
    if_neg (by unfold baseF; omega), if_neg (by unfold baseF; omega)]

theorem ent_lt {f x : ℕ} (hf : f < 15) (hx : x < Wf f) : ent f x + 68 ≤ sentinel := by
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · rw [Wf_zero] at hx; unfold ent entF baseF sentinel; rw [if_pos rfl]; omega
  · by_cases h14 : f = 14
    · subst f
      rw [Wf_14] at hx
      rw [ent_14]
      have := (entry_region (u := 0) (i := 0) (by omega) hx
        (by have := L_pos 0 (band 0 x); omega)).2
      rw [BASE_one] at this
      unfold zOff sentinel; omega
    · obtain ⟨u, rfl⟩ : ∃ u, f = u + 1 := ⟨f - 1, by omega⟩
      rw [Wf_succ (by omega)] at hx
      rw [ent_succ (by omega)]
      have := block_lt_gEnd (i := 0) (by omega) hx (by have := L_pos u (band u x); omega)
      unfold gEnd sentinel at *; omega

/-- The control op after the block of index `x` of frame `f`. -/
def ctlOf (f x : ℕ) : CInstr := if f = 0 then .dispatch (frG0 x) else ctlF (gOf f + 1)

/-- **Block decode.** The block of index `x` of frame `f`: its entry, its straight part, its
control op, all below the sentinel. -/
theorem cinstrAt_blk {T : Tab} (hT : T.Hyp) {f x : ℕ} (hf : f < 15) (hx : x < Wf f) :
    cinstrAt T (ent f x) = .entry f ∧
      (∀ i (hi : i < (bodyF T f x).length), cinstrAt T (ent f x + 1 + i) = (bodyF T f x)[i]) ∧
      cinstrAt T (ent f x + 1 + (bodyF T f x).length) = ctlOf f x ∧
      ent f x + 1 + (bodyF T f x).length < sentinel := by
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · rw [Wf_zero] at hx
    have hl := fbody_len x
    rw [bodyF_zero]
    rw [ent_zero]
    refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
    · have := cinstrAt_free T hx (i := 0) (by omega)
      rw [Nat.add_zero] at this
      rw [this]; unfold fblockInstr; rw [if_pos rfl]
    · rw [Nat.add_assoc, cinstrAt_free T hx (by omega)]
      unfold fblockInstr
      rw [if_neg (by omega), if_pos (by omega), show 1 + i - 1 = i by omega,
        List.getD_eq_getElem _ _ hi]
    · rw [Nat.add_assoc, cinstrAt_free T hx (by omega)]
      unfold fblockInstr ctlOf
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos rfl]
    · unfold entF baseF sentinel; omega
  · by_cases h14 : f = 14
    · subst f
      rw [Wf_14] at hx
      have hl := body_len_L (z := true) hT (u := 0) (by omega) hx
      rw [bodyF_14, ent_14]
      refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
      · have := cinstrAt_grpZ T (i := 0) hx (by omega)
        rw [Nat.add_zero] at this
        rw [this]; unfold blockInstr; rw [if_pos rfl]; rfl
      · rw [Nat.add_assoc, cinstrAt_grpZ T hx (by omega)]
        unfold blockInstr
        rw [if_neg (by omega), if_pos (by omega), show 1 + i - 1 = i by omega,
          List.getD_eq_getElem _ _ hi]
      · rw [Nat.add_assoc, cinstrAt_grpZ T hx (by omega)]
        unfold blockInstr ctlOf
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
        rfl
      · have := (entry_region (u := 0) (i := (body T 0 x true).length + 1) (by omega) hx
          (by omega)).2
        rw [BASE_one] at this
        unfold zOff sentinel; omega
    obtain ⟨u, rfl⟩ : ∃ u, f = u + 1 := ⟨f - 1, by omega⟩
    have hu : u < 13 := by omega
    rw [Wf_succ hu] at hx
    have hl := body_len_L (z := false) hT hu hx
    rw [bodyF_succ T hu, ent_succ hu]
    refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
    · have := cinstrAt_grp T (i := 0) hu hx (by omega)
      rw [Nat.add_zero] at this
      rw [this]; unfold blockInstr; rw [if_pos rfl]; rfl
    · rw [Nat.add_assoc, cinstrAt_grp T hu hx (by omega)]
      unfold blockInstr
      rw [if_neg (by omega), if_pos (by omega), show 1 + i - 1 = i by omega,
        List.getD_eq_getElem _ _ hi]
    · rw [Nat.add_assoc, cinstrAt_grp T hu hx (by omega)]
      unfold blockInstr ctlOf gOf
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
        if_neg h14, Nat.add_sub_cancel]
    · have := block_lt_gEnd (i := (body T u x false).length + 1) hu hx (by omega)
      unfold gEnd sentinel at *; omega

theorem cinstrAt_of_entry {T : Tab} (hT : T.Hyp) {f e : ℕ} (h : IsEntry f e) :
    cinstrAt T e = .entry f := by
  obtain ⟨hf, x, hx, rfl⟩ := h
  exact (cinstrAt_blk hT hf hx).1

theorem isEntry_lt {f e : ℕ} (h : IsEntry f e) : e + 68 ≤ sentinel := by
  obtain ⟨hf, x, hx, rfl⟩ := h
  exact ent_lt hf hx

theorem prologue_ne_entry (s j : ℕ) : prologue s ≠ .entry j := by
  unfold prologue
  split_ifs
  · rcases getD_mem_or (l := proList) (i := s) with h | h
    · exact CInstr.ne_entry_of_straight (proList_straight _ h) j
    · rw [h]; simp
  · simp
  · simp

theorem ctlF_ne_entry (f j : ℕ) : ctlF f ≠ .entry j := by
  unfold ctlF; split_ifs <;> simp

theorem blockInstr_eq_entry {T : Tab} {u v : ℕ} {z : Bool} {i j : ℕ}
    (h : blockInstr T u v z i = .entry j) : i = 0 ∧ j = (if z then 14 else u + 1) := by
  unfold blockInstr at h
  by_cases h0 : i = 0
  · rw [if_pos h0] at h; exact ⟨h0, (CInstr.entry.inj h).symm⟩
  rw [if_neg h0] at h
  split_ifs at h
  · rcases getD_mem_or (l := body T u v z) (i := i - 1) with hm | hm
    · exact absurd h (CInstr.ne_entry_of_straight (body_straight T u v z _ hm) j)
    · rw [hm] at h; cases h
  · exact absurd h (ctlF_ne_entry _ _)

theorem fblockInstr_eq_entry {s i j : ℕ} (h : fblockInstr s i = .entry j) : i = 0 ∧ j = 0 := by
  unfold fblockInstr at h
  split_ifs at h with h0
  · exact ⟨h0, (CInstr.entry.inj h).symm⟩
  · rcases getD_mem_or (l := fbody s) (i := i - 1) with hm | hm
    · exact absurd h (CInstr.ne_entry_of_straight (fbody_straight s _ hm) j)
    · rw [hm] at h; cases h

/-- The only `I0_f` slots are the entries of frame `f`. -/
theorem cinstrAt_eq_entry {T : Tab} {s f : ℕ} (h : cinstrAt T s = .entry f) : IsEntry f s := by
  rcases cinstrAt_cases T s with ⟨-, h'⟩ | ⟨h1, h2, h'⟩ | ⟨h1, h2, h'⟩ | ⟨h1, h2, h'⟩ | h' <;>
    rw [h'] at h
  · exact absurd h (prologue_ne_entry _ _)
  · obtain ⟨hi, rfl⟩ := blockInstr_eq_entry h
    obtain ⟨hu, hv, -, hs⟩ := dec_spec h1 h2
    rw [hi, Nat.add_zero] at hs
    refine ⟨by simp only [Bool.false_eq_true, ↓reduceIte]; omega, (dec s).2.1, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [Wf_succ hu]; exact hv
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [ent_succ hu]; exact hs
  · obtain ⟨hi, rfl⟩ := blockInstr_eq_entry h
    obtain ⟨-, hv, -, hs⟩ := zdec_spec h1 h2
    rw [hi, Nat.add_zero] at hs
    refine ⟨by simp, (dec (s - zOff)).2.1, by simp only [↓reduceIte, Wf_14]; exact hv, ?_⟩
    simp only [↓reduceIte, ent_14]
    unfold gEnd zOff at *; omega
  · obtain ⟨hi, rfl⟩ := fblockInstr_eq_entry h
    have hs : (s - baseF) / 68 < 64 := by
      rw [show baseF = 255615 from rfl] at h1 h2 ⊢; omega
    refine ⟨by omega, (s - baseF) / 68, by rw [Wf_zero]; exact hs, ?_⟩
    rw [ent_zero]; unfold entF; omega
  · cases h

/-! ## The frame lemma on the image -/

/-- **Frame lemma.** In frame `F_f`, every slot that is not an entry of frame `f` fails, at every
memory size `κ ≤ 32` and whatever the image. -/
theorem frame_fail {T : Tab} (hT : T.Hyp) {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K)
    {f s : ℕ} (hf : f < 15) (hs : ¬ IsEntry f s) :
    LeanIsa.execute L ⟨pc, frame f⟩ (instrAt T s) = pure none :=
  exec_frame_fail hκ L pc hf (cinstrAt_bounded hT s) fun h => hs (cinstrAt_eq_entry h)

/-- In frame `1`, every entry slot fails: `I0` is reachable only through a frame jump. -/
theorem entry_fail_frame_one {T : Tab} (hT : T.Hyp) {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ)
    (pc : K) {f s : ℕ} (hs : IsEntry f s) :
    LeanIsa.execute L ⟨pc, 1⟩ (instrAt T s) = pure none := by
  show LeanIsa.execute L ⟨pc, 1⟩ (cinstrAt T s).toInstr = pure none
  rw [cinstrAt_of_entry hT hs]
  exact exec_entry_frame_one hκ L pc hs.1

/-! ## Program facts -/

theorem finalPc_eq (T : Tab) : (program T).finalPc = gpow sentinel := by
  show gpow (2 ^ 18 - 1) = gpow 262143; norm_num

theorem gpow_ne_finalPc (T : Tab) {e : ℕ} (he : e < sentinel) : gpow e ≠ (program T).finalPc := by
  intro h
  have := gpow_inj (show e < 2 ^ 64 - 1 by unfold sentinel at he; omega)
    (show (262143 : ℕ) < 2 ^ 64 - 1 by norm_num) (h.trans (finalPc_eq T))
  unfold sentinel at he; omega

theorem fetch_eq (T : Tab) {s : ℕ} (hs : s < 2 ^ 18) :
    (program T).fetch (gpow s) = some (cinstrAt T s).toInstr :=
  (program T).fetch_gpow ⟨s, hs⟩

/-- Well-formed bytecode: the size cap and no `JUMP` in the halt slot. -/
theorem valid (T : Tab) : LeanIsa.BytecodeValid (program T) := by
  refine ⟨le_refl _, ?_⟩
  show (cinstrAt T (2 ^ 18 - 1)).toInstr.opcode ≠ .jump
  rw [show 2 ^ 18 - 1 = sentinel by rfl, cinstrAt_sentinel]
  decide

end OptimalOTS.HLG3
