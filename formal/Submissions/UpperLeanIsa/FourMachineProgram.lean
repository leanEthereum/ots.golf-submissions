import OptimalOTS.LeanIsa
import Submissions.UpperLeanIsa.LengthFrame
import Submissions.UpperLeanIsa.LengthGate128

/-! The 1124-cycle model bytecode and its local instruction algebra. The complete machine
certificate is assembled in `FourMachine.lean`. -/

namespace OptimalOTS.HLFour

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
theorem frame_ne_one {f : ℕ} (hf : f < 14) : frame f ≠ 1 := by
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
def cCell (c : ℕ) : ℕ :=
  if c = 0 then 48 else if c = 16 then 49
  else if c = 1 then 105 else if c = 2 then 106 else if c = 3 then 47
  else if c = 4 then 107 else 50 + c

/-- Frame 1 is the validated length; the other frames reuse C1..C13. -/
def fCell (f : ℕ) : ℕ := if f = 1 then lenCell else cCell (if f = 0 then 1 else f)

/-- The index output pair. -/
def idxCell : ℕ := 80

/-- The tie pattern of group `u`. -/
def tCell (u : ℕ) : ℕ := if 5 ≤ u ∧ u ≤ 7 then 135 + u else 100 + u

/-- The tie accumulator after group `u`; the last one is the index cell. -/
def accCell (u : ℕ) : ℕ := if u = 12 then idxCell else 120 + u

/-- The landing hint of frame `f`. -/
def hCell (f : ℕ) : ℕ := 160 + f

/-- `H'_f = H_f · g`, the return address of the entry. -/
def h1Cell (f : ℕ) : ℕ := 180 + f

/-- The running landing product before group `u` (`GP_0` is seeded in the free block); `GP_13` is the exit target. -/
def gpCell (u : ℕ) : ℕ := 200 + u

/-- The first root CV word (the top of chain 8). -/
def cvCell : ℕ := 293

/-- The free chain's last output pair. -/
def tfCell : ℕ := 296

/-- The selected chain tops, arranged into adjacent cv pairs for fused and root hashes. -/
def topCell (k : ℕ) : ℕ := [296, 298, 300, 302, 304, 306, 308, 261, 293, 294, 257, 258, 310, 281, 262, 312, 314, 282, 316, 265, 266, 318, 320, 285, 322, 269, 270, 286, 324, 326, 328, 273, 330, 289, 274, 332, 334, 290, 336, 277, 278, 338].getD k 0

/-- The selected last output of a home chain; `topOff` determines its half of the pair. -/
def xhCell (k : ℕ) : ℕ := topCell k

/-- The root state pair after call `r`. -/
def stCell (_r : ℕ) : ℕ := 344

/-- The intermediate pair after step `t` of chain `k`. -/
def xcCell (k t : ℕ) : ℕ := xcBase k + 2 * t
/-- The cell the root reads chain `k`'s top from, when its digit is `d`. -/
def rtopCell (k d : ℕ) : ℕ := if d = 0 ∧ ¬ exported k then wCell k else topCell k
/-- The root CV pair consists of tops 8 and 9. -/
def rootCv (_r : ℕ) : ℕ := 293

/-- Offset selecting the high half at the final step. -/
def topOff (k : ℕ) : ℕ := if k ∈ [7, 8, 10, 13, 19, 23, 25, 31, 33, 39] then 1 else 0

theorem topOff_le (k : ℕ) : topOff k ≤ 1 := by unfold topOff; split_ifs <;> omega

/-- Coordinates whose top is materialized even for a zero digit. -/
def copied (u _i : ℕ) : Prop := isExp u
instance (u i : ℕ) : Decidable (copied u i) := by unfold copied; infer_instance

/-! ## Cell-level instructions -/

/-- An instruction over cell indices. `dispatch f` is `JUMP(ONE, H_f, F_f)`, `exit` is
`JUMP(ONE, GP_13, ONE)`, and `entry f` is the frame-shifted `I0_f`. -/
inductive CInstr
  | init
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
  | .init => .deref (gpow lenCell) OptimalOTS.HLG3.LengthGate128.scale (gpow lenCell) .fp
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
  | .init => true
  | .xor .. => true
  | .mul .. => true
  | .setc .. => true
  | .blake .. => true
  | _ => false

/-- The first cell an instruction reads, for the frame-range argument. -/
def cell0 : CInstr → ℕ
  | .init => lenCell
  | .xor a _ _ => a
  | .mul a _ _ => a
  | .setc a _ => a
  | .blake m0 .. => m0
  | .dispatch _ => oneCell
  | .exit => oneCell
  | .pad => 0
  | .entry _ => 0

/-- The shape invariant of every slot: all frame-1 cells below `2 ^ 16`, frames `< 14`. -/
def Bounded : CInstr → Prop
  | .init => True
  | .xor a b c => a < 2 ^ 16 ∧ b < 2 ^ 16 ∧ c < 2 ^ 16
  | .mul a b c => a < 2 ^ 16 ∧ b < 2 ^ 16 ∧ c < 2 ^ 16
  | .setc a _ => a < 2 ^ 16
  | .blake m0 m1 m2 m3 cv out md =>
      m0 < 2 ^ 16 ∧ m1 < 2 ^ 16 ∧ m2 < 2 ^ 16 ∧ m3 < 2 ^ 16 ∧ cv + 1 < 2 ^ 16 ∧
        out + 1 < 2 ^ 16 ∧ md < 2 ^ 16
  | .dispatch f => f < 14
  | .exit => True
  | .entry f => f < 14
  | .pad => True

theorem cell0_lt {ci : CInstr} (hb : ci.Bounded) (hpad : ci ≠ .pad) (hent : ∀ j, ci ≠ .entry j) :
    ci.cell0 < 2 ^ 16 := by
  cases ci with
  | init => show 3 < 2 ^ 16; norm_num
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
theorem exec_frame_fail {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {f : ℕ} (hf : f < 14)
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
    have hj : j < 14 := hb
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
  | init => exact first (by simp) (by simp)
  | mul a b c => exact first (by simp) (by simp)
  | setc a v => exact first (by simp) (by simp)
  | blake m0 m1 m2 m3 cv out md => exact first (by simp) (by simp)
  | dispatch j => exact first (by simp) (by simp)
  | exit => exact first (by simp) (by simp)

/-- In frame `1`, every entry fails: its shifted operands are out of range. -/
theorem exec_entry_frame_one {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) (pc : K) {j : ℕ}
    (hj : j < 14) : LeanIsa.execute L ⟨pc, 1⟩ (CInstr.entry j).toInstr = pure none := by
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

/-- Chains whose final step fuses four dependency tops. -/
def binds (k : ℕ) : Prop := k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 19, 20, 21, 24, 25, 26, 29, 30, 31, 34, 35, 36, 39, 40, 41]
instance (k : ℕ) : Decidable (binds k) := by unfold binds; infer_instance

def depTop (k i : ℕ) : ℕ :=
  ([[19, 20, 21, 24], [], [], [], [], [10, 11, 1, 2], [7, 14, 15, 16], [25, 26, 29, 30], [31, 34, 35, 36], [39, 40, 41, 12], [13, 17, 18, 22], [23, 27, 28, 32], [33, 37, 38, 0]].getD (unitOf k) []).getD i 0

def depCv (k : ℕ) : ℕ := [265, 0, 0, 0, 0, 257, 261, 269, 273, 277, 281, 285, 289].getD (unitOf k) 0

def fusedMdCell (k : ℕ) : ℕ := cCell ([6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 2, 2, 6, 6, 2, 2, 2, 6, 6, 2, 2, 2, 6, 6, 2, 2, 3, 6, 6, 3, 3, 3, 6, 6, 3, 3, 3].getD k 0)

def fusedTagCell (k : ℕ) : ℕ := cCell ([1, 9, 10, 1, 2, 3, 4, 11, 5, 6, 7, 8, 2, 3, 13, 1, 2, 4, 5, 4, 5, 6, 6, 7, 8, 9, 10, 8, 9, 12, 13, 1, 10, 11, 3, 4, 5, 12, 13, 7, 8, 9].getD k 0)

def rootMdCell (_r : ℕ) : ℕ := cCell 4

/-- Step `t` of the `d` steps of chain `k` (the last writes `dst`): position `LEN k − 1 − d + t`,
tag cells `C` of the base-9 digits of its tag position, cv pair `(ONE, g)`, metadata `ONE`.
A binding final step consumes four child tops and its two domain words. -/
def chainOp (k d t dst : ℕ) : CInstr :=
  let x := if t = 0 then wCell k else xcCell k (t-1)
  let out := if t+1 = d then dst - topOff k else xcCell k t
  if t+1 = d ∧ binds k then
    .blake x (topCell (depTop k 2)) (topCell (depTop k 3)) (fusedTagCell k)
      (depCv k) out (fusedMdCell k)
  else .blake x (cCell (tpos k d t % 9)) (cCell (tpos k d t / 9 % 9))
    (cCell (tpos k d t / 81)) oneCell out oneCell

/-- The `d` steps of chain `k`. -/
def chainOps (k d dst : ℕ) : List CInstr := (List.range d).map (fun t => chainOp k d t dst)

/-- The straight part of the prologue (slots `0 … 16`). -/
def proList : List CInstr :=
  ((List.range 13).map (fun c => .setc (cCell (c+1)) (cV (c+1)))) ++
    [.init,.setc gCell gV,
      .blake msgLo msgHi nonceCell pkCell oneCell idxCell gCell,
      .mul (hCell 0) gCell (h1Cell 0)]

/-- Slots `0 … 26`: the straight prologue, the free dispatch at 17, and nine pads. -/
def prologue (s : ℕ) : CInstr :=
  if s < 17 then proList.getD s .pad else if s = 17 then .dispatch 0 else .pad

/-- The control op after the block of group `f - 1`: the next dispatch, or the exit. -/
def ctlF (f : ℕ) : CInstr := if f < 13 then .dispatch (f + 1) else .exit

/-- The first group always uses frame 1; the free top has a fixed materialized cell. -/
def frG0 (_s : ℕ) : ℕ := 1

/-- The free block: seed, `s` chain steps, top materialization, and the next hint product. -/
def fbody (s : ℕ) : List CInstr :=
  [.setc (gpCell 0) (ofK (LeanIsaFieldRescale.initialProduct 77 s))] ++
  chainOps 0 s tfCell ++ [copy (if s = 0 then wCell 0 else tfCell) tfCell,
    .mul (hCell 1) gCell (h1Cell 1)]

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

/-- The single root call executes in group 5. -/
def hcall (_u : ℕ) : ℕ := 0

/-- The message cell `j < 4` of a home root call. The legacy variant argument is unused. -/
def rt (T : Tab) (u v : ℕ) (_z : Bool) (j : ℕ) : ℕ :=
  rtopCell (3+j) (T u v j)

/-- The root call of a home block, using its fixed domain-separated metadata cell. -/
def rootIns (T : Tab) (u v : ℕ) (z : Bool) : List CInstr :=
  if u = 5 then
    [.blake (rt T u v z 0) (rt T u v z 1) (rt T u v z 2) (rt T u v z 3)
      (rootCv (hcall u)) (stCell (hcall u)) (rootMdCell (hcall u))]
  else []

/-- Padding to the unit's constant non-hash count. -/
def npad (T : Tab) (u v : ℕ) : ℕ := gcu u - 4 - (tie u v).length - zexp T u v

/-- The last straight op: the next group's `MUL(H, g, H')`, or the public-key copy. -/
def nextOp (u : ℕ) : CInstr :=
  if u < 12 then .mul (hCell (u+2)) gCell (h1Cell (u+2)) else copy (stCell 0) pkCell

/-- The cost multiplier omits one guaranteed hash in every binding group. -/
def chargedCost (T : Tab) (u v : ℕ) : ℕ := cost T u v - LengthFrame.deduction u

/-- The product op of the block of `v` in group `u`. -/
def prodOp (T : Tab) (u v : ℕ) : CInstr := .mul (gpCell u) (cCell (chargedCost T u v)) (gpCell (u + 1))

/-- The straight part of the block of `v` in group `u`, variant `z`. -/
def body (T : Tab) (u v : ℕ) (z : Bool) : List CInstr :=
  tie u v ++ [prodOp T u v] ++ segs T u v ++ rootIns T u v z ++ List.replicate (npad T u v) NOP ++
    [nextOp u]

/-- Op `i` of the block of `v` in group `u`, entered in frame `u+1`. -/
def blockInstr (T : Tab) (u v : ℕ) (z : Bool) (i : ℕ) : CInstr :=
  if i = 0 then .entry (u+1)
  else if i ≤ (body T u v z).length then (body T u v z).getD (i-1) .pad
  else if i = (body T u v z).length + 1 then ctlF (u+1) else .pad

/-- Op `i` of the free chain's block of digit `s`. -/
def fblockInstr (s i : ℕ) : CInstr :=
  if i = 0 then .entry 0
  else if i ≤ (fbody s).length then (fbody s).getD (i - 1) .pad
  else if i = (fbody s).length + 1 then .dispatch (frG0 s) else .pad

/-- The cell-level instruction at slot `s`, decoded by segment. -/
def cinstrAt (T : Tab) (s : ℕ) : CInstr :=
  if s < 27 then prologue s
  else if s < gEnd then blockInstr T (dec s).1 (dec s).2.1 false (dec s).2.2
  else if s < baseF then .pad
  else if s < baseF + 4352 then fblockInstr ((s-baseF)/68) ((s-baseF)%68)
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


end OptimalOTS.HLFour
