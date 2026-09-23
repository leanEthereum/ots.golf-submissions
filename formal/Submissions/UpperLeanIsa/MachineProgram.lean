import OptimalOTS.LeanIsaMachine

/-!
# The leanISA bytecode of the baseline Winternitz verifier

Layout: `.work/leanisa/M-machine-design.md`. The code is straight-line and runs in frame
`fp = 1`: instruction `k` sits in slot `k`, every operand is `op c = g ^ c` naming cell `c`, and
the last instruction is the halting `JUMP`.

Instructions are described at the level of cells by `CInstr` and turned into ISA instructions by
`CInstr.toInstr`. The instruction at index `k` is `cinstrAt k`, decoded arithmetically by segment
(no proof ever evaluates the program over a range of indices):

* Segment A, `k < A_len = 5191`, `SET_CONSTANT`s (`constInstr`), in this order:
  `0, 1`: cells `48, 49 ← 0`; `2`: cell `50 ← ONE`; `3`: cell `51 ← FPC`;
  `4 + i` (`i < 34`): chain ids; `38 + r` (`r < 34`): root metadata;
  `72 + j` (`j < 255`): position tags; `327 + 255 p + j` (`p < 16`, `j < 255`): V-links;
  `4407 + j`, `4662 + j`, `4917 + j` (`j < 255`): U-links of the message chains, of chain 32
  and of chain 33; `5172`, `5173`: the U bases of chains 32 and 33; `5174 + p` (`p < 16`): the
  V bases; `5190`: the length cell `3`.
* Segment B: chain `i < 34`, step `j < 255`, slot `r < 10` at `A_len + 2553 i + 10 j + r`
  (`stepInstr`); endpoint slot `e < 3` at `A_len + 2553 i + 2550 + e` (`endInstr`).
* Segment C, `C_start + 15 h + s` (`h < 2`, `s < 15`): message links (`linkInstr`).
* Segment D, `D_start + s` (`s < 32`): checksum product and check (`prodInstr`).
* Segment E, `E_start + t` (`t < 35`): root absorptions and the public-key XOR (`rootInstr`).
* Segment F, `F_start + u` (`u < 3`): two halting constants and the `JUMP` (`haltInstr`).
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

/-- The zero cell `Z`; with `z2Cell` it is the zero chaining pair. -/
def zCell : ℕ := 48
def z2Cell : ℕ := 49
/-- The cell holding ONE (chain metadata, field one, jump condition). -/
def oneCell : ℕ := 50
/-- The cell holding FPC (unused by the halt, kept for the layout of the spec). -/
def fpcCell : ℕ := 51
/-- The pinned length cell. -/
def lenCell : ℕ := 3
/-- The pinned public-key cell. -/
def pkCell : ℕ := 0
/-- The pinned signature cell of chain `i`. -/
def sigCell (i : ℕ) : ℕ := 4 + i
def chainIdCell (i : ℕ) : ℕ := 64 + i
def rootMdCell (r : ℕ) : ℕ := 100 + r
def posCell (j : ℕ) : ℕ := 256 + j
def wvCell (p j : ℕ) : ℕ := 1024 + 256 * p + j
def wuCell (j : ℕ) : ℕ := 5120 + j
def wuHiCell (j : ℕ) : ℕ := 5376 + j
def wuLoCell (j : ℕ) : ℕ := 5632 + j
def ubHiCell : ℕ := 5888
def ubLoCell : ℕ := 5889
def vbCell (p : ℕ) : ℕ := 5890 + p

/-- Base cell of chain `i`. -/
def chainBase (i : ℕ) : ℕ := 8192 + 2560 * i
/-- Cell `r` of step `j` of chain `i`. -/
def stepCell (i j r : ℕ) : ℕ := chainBase i + 10 * j + r
/-- `t_j`, the thermometer bit. -/
def tCell (i j : ℕ) : ℕ := stepCell i j 0
/-- `s_j = x_j + σ`. -/
def sCell (i j : ℕ) : ℕ := stepCell i j 1
/-- `u_j = t_{j-1} s_j`. -/
def uCell (i j : ℕ) : ℕ := stepCell i j 2
/-- `in_j = σ + u_j`, the hashed word. -/
def inCell (i j : ℕ) : ℕ := stepCell i j 3
/-- `h_j`, the high half of the answer of step `j` (the low half is `xCell i (j + 1)`). -/
def hCell (i j : ℕ) : ℕ := stepCell i j 5
def pVCell (i j : ℕ) : ℕ := stepCell i j 6
def pUCell (i j : ℕ) : ℕ := stepCell i j 8

/-- In-cell byte position of the digit of chain `i` (`0` for the checksum chains). -/
def bytePos (i : ℕ) : ℕ := if i < 32 then (31 - i) % 16 else 0
/-- `t_{j-1}`, with `t_{-1}` the zero cell. -/
def tPrevCell (i j : ℕ) : ℕ := if j = 0 then zCell else stepCell i (j - 1) 0
/-- `x_j`, with `x_0 = σ_i`. -/
def xCell (i j : ℕ) : ℕ := if j = 0 then sigCell i else stepCell i (j - 1) 4
/-- The V accumulator `aV_j`, starting at `VB_p`. -/
def aVCell (i j : ℕ) : ℕ := if j = 0 then vbCell (bytePos i) else stepCell i (j - 1) 7
/-- Start of the U accumulator of chain `i`. -/
def aUBaseCell (i : ℕ) : ℕ := if i < 32 then oneCell else if i = 32 then ubHiCell else ubLoCell
/-- The U accumulator `aU_j`. -/
def aUCell (i j : ℕ) : ℕ := if j = 0 then aUBaseCell i else stepCell i (j - 1) 9
/-- The U-link constant cell of step `j` of chain `i`. -/
def wuSelCell (i j : ℕ) : ℕ :=
  if i < 32 then wuCell j else if i = 32 then wuHiCell j else wuLoCell j
def e0Cell (i : ℕ) : ℕ := chainBase i + 2550
def e1Cell (i : ℕ) : ℕ := chainBase i + 2551
/-- The chain endpoint `end_i`. -/
def endCell (i : ℕ) : ℕ := chainBase i + 2552
/-- `D_i = aV_255`. -/
def dCell (i : ℕ) : ℕ := stepCell i 254 7
/-- `P_i = aU_255`. -/
def pCell (i : ℕ) : ℕ := stepCell i 254 9

/-- The chain of term `b` of link half `h` (`h = 0`: cell 1, chains 31..16; `h = 1`: cell 2,
chains 15..0). -/
def linkChain (h b : ℕ) : ℕ := 31 - 16 * h - b
/-- Partial XOR of the first `s + 1` terms of half `h`; the full sum (`s = 15`) is the pinned
message cell `1 + h`. -/
def linkAccCell (h s : ℕ) : ℕ :=
  if s = 0 then dCell (linkChain h 0) else if s = 15 then 1 + h else 96000 + 16 * h + s
/-- Partial checksum product `Π_{i ≤ s} P_i`. -/
def prodAccCell (s : ℕ) : ℕ := if s = 0 then pCell 0 else 96100 + s

/-- Root state pair `S_k` (low cell; the high cell is the next one). -/
def rootStateCell (k : ℕ) : ℕ := if k = 0 then zCell else 97000 + 2 * k
def haltOneCell : ℕ := 97100
def haltFpcCell : ℕ := 97101

theorem zCell_add_one : zCell + 1 = z2Cell := rfl

theorem xCell_zero (i : ℕ) : xCell i 0 = sigCell i := by
  unfold xCell
  exact if_pos rfl

theorem xCell_succ (i j : ℕ) : xCell i (j + 1) = stepCell i j 4 := by
  have h : j + 1 - 1 = j := by omega
  unfold xCell
  rw [if_neg (show j + 1 ≠ 0 by omega), h]

theorem xCell_succ_add_one (i j : ℕ) : xCell i (j + 1) + 1 = hCell i j := by
  rw [xCell_succ]
  unfold hCell stepCell
  omega

theorem tPrevCell_zero (i : ℕ) : tPrevCell i 0 = zCell := by
  unfold tPrevCell
  exact if_pos rfl

theorem tPrevCell_succ (i j : ℕ) : tPrevCell i (j + 1) = tCell i j := by
  have h : j + 1 - 1 = j := by omega
  unfold tPrevCell tCell
  rw [if_neg (show j + 1 ≠ 0 by omega), h]

theorem aVCell_zero (i : ℕ) : aVCell i 0 = vbCell (bytePos i) := by
  unfold aVCell
  exact if_pos rfl

theorem aVCell_succ (i j : ℕ) : aVCell i (j + 1) = stepCell i j 7 := by
  have h : j + 1 - 1 = j := by omega
  unfold aVCell
  rw [if_neg (show j + 1 ≠ 0 by omega), h]

theorem aUCell_zero (i : ℕ) : aUCell i 0 = aUBaseCell i := by
  unfold aUCell
  exact if_pos rfl

theorem aUCell_succ (i j : ℕ) : aUCell i (j + 1) = stepCell i j 9 := by
  have h : j + 1 - 1 = j := by omega
  unfold aUCell
  rw [if_neg (show j + 1 ≠ 0 by omega), h]

theorem dCell_eq (i : ℕ) : dCell i = aVCell i 255 := (aVCell_succ i 254).symm

theorem pCell_eq (i : ℕ) : pCell i = aUCell i 255 := (aUCell_succ i 254).symm

theorem rootStateCell_zero : rootStateCell 0 = zCell := by
  unfold rootStateCell
  exact if_pos rfl

/-! ## Constants (§1) -/

def zeroV : E := 0
/-- ONE: the cell `cellOfBits 1`, also the field one (`oneV_eq_cellOfBits`, `oneV_eq_ofK`). -/
def oneV : E := E.ofLimbs 1 0 0
/-- FPC: the final program counter as a word. -/
def fpcV : E := E.ofLimbs (gpow (2 ^ 17 - 1)) 0 0
def chainIdV (i : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 i)
def rootMdV (r : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 (2 + r))
def posV (j : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 j)
def wvV (p j : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 ((j ^^^ (j + 1)) <<< (8 * p)))
def wuV (j : ℕ) : E := ofK (gpow (255 - j)) + ofK (gpow (255 - (j + 1)))
def wuHiV (j : ℕ) : E := ofK (gpow (256 * j)) + ofK (gpow (256 * (j + 1)))
def wuLoV (j : ℕ) : E := ofK (gpow j) + ofK (gpow (j + 1))
def ubHiV : E := ofK (gpow (256 * 255))
def ubLoV : E := ofK (gpow 255)
def vbV (p : ℕ) : E := LeanIsa.cellOfBits (BitVec.ofNat 128 (255 <<< (8 * p)))
def lenV : E := LeanIsa.cellOfBits (BitVec.ofNat 128 4352)

theorem isInK_oneV : IsInK oneV := isInK_ofLimbs 1

theorem isInK_fpcV : IsInK fpcV := isInK_ofLimbs _

theorem oneV_ne_zero : oneV ≠ 0 := fun h =>
  (by decide : (1 : K) ≠ 0) ((ofLimbs_eq_zero_iff 1).mp h)

theorem oneV_eq_ofK : oneV = ofK 1 := (ofK_eq_ofLimbs 1).symm

theorem oneV_eq_cellOfBits : oneV = LeanIsa.cellOfBits 1 := by
  first
    | (unfold oneV LeanIsa.cellOfBits; congr 1 <;> decide)
    | decide
    | rfl

theorem cellBits_oneV : LeanIsa.cellBits oneV = 1 := by
  rw [oneV_eq_cellOfBits, LeanIsa.cellBits_cellOfBits]

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

namespace CInstr

/-- The ISA instruction, in frame `fp = 1`. -/
def toInstr : CInstr → Instr
  | .xor a b c => .xor (op a) (op b) (op c)
  | .mul a b c => .mulNative (op a) (op b) (op c)
  | .setc a v => .setConstant (op a) v
  | .blake m0 m1 m2 m3 cv out md =>
      .blake2s ![op m0, op m1, op m2, op m3] (op cv) (op out) (op md)
  | .jump a b c => .jump (op a) (op b) (op c)

/-- Every cell the instruction reads is below `B`. -/
def Bounded (B : ℕ) : CInstr → Prop
  | .xor a b c => a < B ∧ b < B ∧ c < B
  | .mul a b c => a < B ∧ b < B ∧ c < B
  | .setc a _ => a < B
  | .blake m0 m1 m2 m3 cv out md =>
      m0 < B ∧ m1 < B ∧ m2 < B ∧ m3 < B ∧ cv + 1 < B ∧ out + 1 < B ∧ md < B
  | .jump a b c => a < B ∧ b < B ∧ c < B

/-- Cycles charged: ten for `BLAKE2S`, one otherwise. -/
def cost : CInstr → ℕ
  | .blake .. => 10
  | _ => 1

def isJump : CInstr → Bool
  | .jump .. => true
  | _ => false

theorem Bounded.mono {B B' : ℕ} {ci : CInstr} (h : ci.Bounded B) (hB : B ≤ B') :
    ci.Bounded B' := by
  cases ci <;> simp only [Bounded] at h ⊢ <;> omega

theorem weight_toInstr (ci : CInstr) : LeanIsa.weight ci.toInstr.opcode = ci.cost := by
  cases ci <;> rfl

end CInstr

/-! ## The segments -/

/-- Segment A: cell and value of constant `a`, in the order documented in the module header.
Only this pair is an if-chain; `constInstr a` is syntactically a `SET_CONSTANT`, so its opcode,
cost and jump flag never need the chain to be evaluated. -/
def constPair (a : ℕ) : ℕ × E :=
  if a = 0 then (zCell, zeroV)
  else if a = 1 then (z2Cell, zeroV)
  else if a = 2 then (oneCell, oneV)
  else if a = 3 then (fpcCell, fpcV)
  else if a < 38 then (chainIdCell (a - 4), chainIdV (a - 4))
  else if a < 72 then (rootMdCell (a - 38), rootMdV (a - 38))
  else if a < 327 then (posCell (a - 72), posV (a - 72))
  else if a < 4407 then
    (wvCell ((a - 327) / 255) ((a - 327) % 255), wvV ((a - 327) / 255) ((a - 327) % 255))
  else if a < 4662 then (wuCell (a - 4407), wuV (a - 4407))
  else if a < 4917 then (wuHiCell (a - 4662), wuHiV (a - 4662))
  else if a < 5172 then (wuLoCell (a - 4917), wuLoV (a - 4917))
  else if a = 5172 then (ubHiCell, ubHiV)
  else if a = 5173 then (ubLoCell, ubLoV)
  else if a < 5190 then (vbCell (a - 5174), vbV (a - 5174))
  else (lenCell, lenV)

/-- The cell of constant `a`. -/
def constCell (a : ℕ) : ℕ := (constPair a).1

/-- The value of constant `a`. -/
def constVal (a : ℕ) : E := (constPair a).2

/-- Segment A: constant `a` is `SET_CONSTANT [constCell a] ← constVal a`. -/
def constInstr (a : ℕ) : CInstr := .setc (constCell a) (constVal a)

theorem constInstr_of_pair {a c : ℕ} {v : E} (h : constPair a = (c, v)) :
    constInstr a = .setc c v :=
  congrArg (fun q : ℕ × E => CInstr.setc q.1 q.2) h

/-- Segment B, step `j` of chain `i`, slot `r` (§2). -/
def stepInstr (i j r : ℕ) : CInstr :=
  if r = 0 then .mul (tCell i j) (tCell i j) (tCell i j)
  else if r = 1 then .mul (tPrevCell i j) (tCell i j) (tPrevCell i j)
  else if r = 2 then .xor (xCell i j) (sigCell i) (sCell i j)
  else if r = 3 then .mul (tPrevCell i j) (sCell i j) (uCell i j)
  else if r = 4 then .xor (sigCell i) (uCell i j) (inCell i j)
  else if r = 5 then
    .blake (inCell i j) (chainIdCell i) (posCell j) zCell zCell (xCell i (j + 1)) oneCell
  else if r = 6 then .mul (tCell i j) (wvCell (bytePos i) j) (pVCell i j)
  else if r = 7 then .xor (aVCell i j) (pVCell i j) (aVCell i (j + 1))
  else if r = 8 then .mul (tCell i j) (wuSelCell i j) (pUCell i j)
  else .xor (aUCell i j) (pUCell i j) (aUCell i (j + 1))

/-- Segment B, the endpoint of chain `i`, slot `e`. -/
def endInstr (i e : ℕ) : CInstr :=
  if e = 0 then .xor (xCell i 255) (sigCell i) (e0Cell i)
  else if e = 1 then .mul (tCell i 254) (e0Cell i) (e1Cell i)
  else .xor (sigCell i) (e1Cell i) (endCell i)

/-- Segment B, chain `i`, in-chain offset `q < 2553`. -/
def chainInstr (i q : ℕ) : CInstr :=
  if q < 2550 then stepInstr i (q / 10) (q % 10) else endInstr i (q - 2550)

/-- Segment C, half `h`, link `s`. -/
def linkInstr (h s : ℕ) : CInstr :=
  .xor (linkAccCell h s) (dCell (linkChain h (s + 1))) (linkAccCell h (s + 1))

/-- Segment D. -/
def prodInstr (s : ℕ) : CInstr :=
  if s < 31 then .mul (prodAccCell s) (pCell (s + 1)) (prodAccCell (s + 1))
  else .mul (pCell 32) (pCell 33) (prodAccCell 31)

/-- Segment E. -/
def rootInstr (t : ℕ) : CInstr :=
  if t < 34 then
    .blake (endCell t) zCell zCell zCell (rootStateCell t) (rootStateCell (t + 1))
      (rootMdCell (33 - t))
  else .xor (rootStateCell 34) zCell pkCell

/-- Segment F. -/
def haltInstr (u : ℕ) : CInstr :=
  if u = 0 then .setc haltOneCell oneV
  else if u = 1 then .setc haltFpcCell fpcV
  else .jump haltOneCell haltFpcCell haltOneCell

/-! ## Sizes -/

def A_len : ℕ := 5191
def C_start : ℕ := A_len + 34 * 2553
def D_start : ℕ := C_start + 30
def E_start : ℕ := D_start + 32
def F_start : ℕ := E_start + 35
/-- The number of instructions (and executed steps). -/
def N : ℕ := F_start + 3
/-- `BLAKE2S` executed on every completing run: `34 · 255 + 34`. -/
def hashCount : ℕ := 8704
def totalCost : ℕ := N + 9 * hashCount
def claim : ℕ := LeanIsa.boundaryCycles + totalCost

theorem A_len_eq : A_len = 5191 := rfl
theorem C_start_eq : C_start = 91993 := rfl
theorem D_start_eq : D_start = 92023 := rfl
theorem E_start_eq : E_start = 92055 := rfl
theorem F_start_eq : F_start = 92090 := rfl
theorem N_eq : N = 92093 := rfl
theorem F_start_add_three : F_start + 3 = N := rfl
theorem hashCount_eq : hashCount = 34 * 255 + 34 := rfl
theorem totalCost_eq : totalCost = 170429 := by
  first
    | rfl
    | decide
theorem claim_eq : claim = 170549 := by
  first
    | rfl
    | decide

/-! ## The program -/

/-- The cell-level instruction at index `k`, decoded by segment. -/
def cinstrAt (k : ℕ) : CInstr :=
  if k < A_len then constInstr k
  else if k < C_start then chainInstr ((k - A_len) / 2553) ((k - A_len) % 2553)
  else if k < D_start then linkInstr ((k - C_start) / 15) ((k - C_start) % 15)
  else if k < E_start then prodInstr (k - D_start)
  else if k < F_start then rootInstr (k - E_start)
  else haltInstr (k - F_start)

/-- The ISA instruction at index `k`. -/
abbrev instrAt (k : ℕ) : Instr := (cinstrAt k).toInstr

/-- The bytecode: `2 ^ 17` slots, the first `N` holding the verifier, the rest inert. -/
def program : Program where
  logSize := 17
  logSize_le := by decide
  code i := if (i : ℕ) < N then instrAt i else .xor 0 0 0

theorem program_logSize : program.logSize = 17 := rfl

theorem finalPc_eq : program.finalPc = gpow (2 ^ 17 - 1) := rfl

theorem fetch_eq (k : ℕ) (hk : k < N) : program.fetch (gpow k) = some (instrAt k) := by
  have hN : N = 92093 := rfl
  have hk' : k < 2 ^ program.logSize := by
    show k < 2 ^ 17
    have h17 : (2 : ℕ) ^ 17 = 131072 := by norm_num
    omega
  have h : program.fetch (gpow k) = some (program.code ⟨k, hk'⟩) := program.fetch_gpow ⟨k, hk'⟩
  rw [h]
  show some (if k < N then instrAt k else .xor 0 0 0) = some (instrAt k)
  rw [if_pos hk]

/-- Below `N`, a slot address is never the sentinel counter. -/
theorem gpow_ne_finalPc {k : ℕ} (hk : k < N) : gpow k ≠ program.finalPc := by
  intro h
  have h' : gpow k = gpow 131071 := h
  have hN : N = 92093 := rfl
  have hk64 : k < 2 ^ 64 - 1 := lt_of_lt_of_le hk (by rw [hN]; norm_num)
  have h64 : (131071 : ℕ) < 2 ^ 64 - 1 := by norm_num
  have hkk : k = 131071 := gpow_injOn hk64 h64 h'
  omega

theorem valid : LeanIsa.BytecodeValid program := by
  refine ⟨by decide, ?_⟩
  have hc : program.code (LeanIsa.sentinelSlot program) = .xor 0 0 0 := by
    show (if (2 ^ 17 - 1 : ℕ) < N then instrAt (2 ^ 17 - 1) else .xor 0 0 0) = .xor 0 0 0
    rw [if_neg (show ¬ ((2 ^ 17 - 1 : ℕ) < N) by decide)]
  rw [hc]
  first
    | decide
    | (intro h; cases h)
    | simp [Instr.opcode]

theorem seeded : 2 ^ 17 + 2 ^ 17 < LeanIsa.maxSeededRows := by
  norm_num [LeanIsa.maxSeededRows]

/-! ## Decoding -/

theorem cinstrAt_const {a : ℕ} (ha : a < A_len) : cinstrAt a = constInstr a := by
  unfold cinstrAt
  rw [if_pos ha]

theorem cinstrAt_step {i j r : ℕ} (hi : i < 34) (hj : j < 255) (hr : r < 10) :
    cinstrAt (A_len + 2553 * i + 10 * j + r) = stepInstr i j r := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have h1 : ¬ (A_len + 2553 * i + 10 * j + r < A_len) := by omega
  have h2 : A_len + 2553 * i + 10 * j + r < C_start := by omega
  have h3 : (A_len + 2553 * i + 10 * j + r - A_len) / 2553 = i := by omega
  have h4 : (A_len + 2553 * i + 10 * j + r - A_len) % 2553 = 10 * j + r := by omega
  have h5 : 10 * j + r < 2550 := by omega
  have h6 : (10 * j + r) / 10 = j := by omega
  have h7 : (10 * j + r) % 10 = r := by omega
  unfold cinstrAt chainInstr
  rw [if_neg h1, if_pos h2, h3, h4, if_pos h5, h6, h7]

theorem cinstrAt_end {i e : ℕ} (hi : i < 34) (he : e < 3) :
    cinstrAt (A_len + 2553 * i + 2550 + e) = endInstr i e := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have h1 : ¬ (A_len + 2553 * i + 2550 + e < A_len) := by omega
  have h2 : A_len + 2553 * i + 2550 + e < C_start := by omega
  have h3 : (A_len + 2553 * i + 2550 + e - A_len) / 2553 = i := by omega
  have h4 : (A_len + 2553 * i + 2550 + e - A_len) % 2553 = 2550 + e := by omega
  have h5 : ¬ (2550 + e < 2550) := by omega
  have h6 : 2550 + e - 2550 = e := by omega
  unfold cinstrAt chainInstr
  rw [if_neg h1, if_pos h2, h3, h4, if_neg h5, h6]

theorem cinstrAt_link {h s : ℕ} (hh : h < 2) (hs : s < 15) :
    cinstrAt (C_start + 15 * h + s) = linkInstr h s := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hD : D_start = 92023 := rfl
  have h1 : ¬ (C_start + 15 * h + s < A_len) := by omega
  have h2 : ¬ (C_start + 15 * h + s < C_start) := by omega
  have h3 : C_start + 15 * h + s < D_start := by omega
  have h4 : (C_start + 15 * h + s - C_start) / 15 = h := by omega
  have h5 : (C_start + 15 * h + s - C_start) % 15 = s := by omega
  unfold cinstrAt
  rw [if_neg h1, if_neg h2, if_pos h3, h4, h5]

theorem cinstrAt_prod {s : ℕ} (hs : s < 32) : cinstrAt (D_start + s) = prodInstr s := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hD : D_start = 92023 := rfl
  have hE : E_start = 92055 := rfl
  have h1 : ¬ (D_start + s < A_len) := by omega
  have h2 : ¬ (D_start + s < C_start) := by omega
  have h3 : ¬ (D_start + s < D_start) := by omega
  have h4 : D_start + s < E_start := by omega
  have h5 : D_start + s - D_start = s := by omega
  unfold cinstrAt
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, h5]

theorem cinstrAt_root {t : ℕ} (ht : t < 35) : cinstrAt (E_start + t) = rootInstr t := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hD : D_start = 92023 := rfl
  have hE : E_start = 92055 := rfl
  have hF : F_start = 92090 := rfl
  have h1 : ¬ (E_start + t < A_len) := by omega
  have h2 : ¬ (E_start + t < C_start) := by omega
  have h3 : ¬ (E_start + t < D_start) := by omega
  have h4 : ¬ (E_start + t < E_start) := by omega
  have h5 : E_start + t < F_start := by omega
  have h6 : E_start + t - E_start = t := by omega
  unfold cinstrAt
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, h6]

theorem cinstrAt_halt {u : ℕ} (hu : u < 3) : cinstrAt (F_start + u) = haltInstr u := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hD : D_start = 92023 := rfl
  have hE : E_start = 92055 := rfl
  have hF : F_start = 92090 := rfl
  have h1 : ¬ (F_start + u < A_len) := by omega
  have h2 : ¬ (F_start + u < C_start) := by omega
  have h3 : ¬ (F_start + u < D_start) := by omega
  have h4 : ¬ (F_start + u < E_start) := by omega
  have h5 : ¬ (F_start + u < F_start) := by omega
  have h6 : F_start + u - F_start = u := by omega
  unfold cinstrAt
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, h6]

theorem cinstrAt_haltOne : cinstrAt F_start = .setc haltOneCell oneV := by
  have h := cinstrAt_halt (u := 0) (by norm_num)
  rw [Nat.add_zero] at h
  exact h

theorem cinstrAt_haltFpc : cinstrAt (F_start + 1) = .setc haltFpcCell fpcV :=
  cinstrAt_halt (u := 1) (by norm_num)

theorem cinstrAt_haltJump :
    cinstrAt (F_start + 2) = .jump haltOneCell haltFpcCell haltOneCell :=
  cinstrAt_halt (u := 2) (by norm_num)

theorem instrAt_step {i j r : ℕ} (hi : i < 34) (hj : j < 255) (hr : r < 10) :
    instrAt (A_len + 2553 * i + 10 * j + r) = (stepInstr i j r).toInstr :=
  congrArg CInstr.toInstr (cinstrAt_step hi hj hr)

theorem instrAt_end {i e : ℕ} (hi : i < 34) (he : e < 3) :
    instrAt (A_len + 2553 * i + 2550 + e) = (endInstr i e).toInstr :=
  congrArg CInstr.toInstr (cinstrAt_end hi he)

/-! ### Segment A in detail -/

theorem constPair_zero : constPair 0 = (zCell, zeroV) := rfl
theorem constPair_one : constPair 1 = (z2Cell, zeroV) := rfl
theorem constPair_two : constPair 2 = (oneCell, oneV) := rfl
theorem constPair_three : constPair 3 = (fpcCell, fpcV) := rfl

theorem constInstr_zero : constInstr 0 = .setc zCell zeroV := constInstr_of_pair constPair_zero
theorem constInstr_one : constInstr 1 = .setc z2Cell zeroV := constInstr_of_pair constPair_one
theorem constInstr_two : constInstr 2 = .setc oneCell oneV := constInstr_of_pair constPair_two
theorem constInstr_three : constInstr 3 = .setc fpcCell fpcV :=
  constInstr_of_pair constPair_three

theorem constPair_chainId {i : ℕ} (hi : i < 34) :
    constPair (4 + i) = (chainIdCell i, chainIdV i) := by
  have d : 4 + i - 4 = i := by omega
  unfold constPair
  rw [if_neg (show ¬ (4 + i = 0) by omega), if_neg (show ¬ (4 + i = 1) by omega),
    if_neg (show ¬ (4 + i = 2) by omega), if_neg (show ¬ (4 + i = 3) by omega),
    if_pos (show 4 + i < 38 by omega), d]

theorem constInstr_chainId {i : ℕ} (hi : i < 34) :
    constInstr (4 + i) = .setc (chainIdCell i) (chainIdV i) :=
  constInstr_of_pair (constPair_chainId hi)

theorem constPair_rootMd {r : ℕ} (hr : r < 34) :
    constPair (38 + r) = (rootMdCell r, rootMdV r) := by
  have d : 38 + r - 38 = r := by omega
  unfold constPair
  rw [if_neg (show ¬ (38 + r = 0) by omega), if_neg (show ¬ (38 + r = 1) by omega),
    if_neg (show ¬ (38 + r = 2) by omega), if_neg (show ¬ (38 + r = 3) by omega),
    if_neg (show ¬ (38 + r < 38) by omega), if_pos (show 38 + r < 72 by omega), d]

theorem constInstr_rootMd {r : ℕ} (hr : r < 34) :
    constInstr (38 + r) = .setc (rootMdCell r) (rootMdV r) :=
  constInstr_of_pair (constPair_rootMd hr)

theorem constPair_pos {j : ℕ} (hj : j < 255) :
    constPair (72 + j) = (posCell j, posV j) := by
  have d : 72 + j - 72 = j := by omega
  unfold constPair
  rw [if_neg (show ¬ (72 + j = 0) by omega), if_neg (show ¬ (72 + j = 1) by omega),
    if_neg (show ¬ (72 + j = 2) by omega), if_neg (show ¬ (72 + j = 3) by omega),
    if_neg (show ¬ (72 + j < 38) by omega), if_neg (show ¬ (72 + j < 72) by omega),
    if_pos (show 72 + j < 327 by omega), d]

theorem constInstr_pos {j : ℕ} (hj : j < 255) :
    constInstr (72 + j) = .setc (posCell j) (posV j) :=
  constInstr_of_pair (constPair_pos hj)

theorem constPair_wv {p j : ℕ} (hp : p < 16) (hj : j < 255) :
    constPair (327 + 255 * p + j) = (wvCell p j, wvV p j) := by
  have d1 : (327 + 255 * p + j - 327) / 255 = p := by omega
  have d2 : (327 + 255 * p + j - 327) % 255 = j := by omega
  unfold constPair
  rw [if_neg (show ¬ (327 + 255 * p + j = 0) by omega),
    if_neg (show ¬ (327 + 255 * p + j = 1) by omega),
    if_neg (show ¬ (327 + 255 * p + j = 2) by omega),
    if_neg (show ¬ (327 + 255 * p + j = 3) by omega),
    if_neg (show ¬ (327 + 255 * p + j < 38) by omega),
    if_neg (show ¬ (327 + 255 * p + j < 72) by omega),
    if_neg (show ¬ (327 + 255 * p + j < 327) by omega),
    if_pos (show 327 + 255 * p + j < 4407 by omega), d1, d2]

theorem constInstr_wv {p j : ℕ} (hp : p < 16) (hj : j < 255) :
    constInstr (327 + 255 * p + j) = .setc (wvCell p j) (wvV p j) :=
  constInstr_of_pair (constPair_wv hp hj)

theorem constPair_wu {j : ℕ} (hj : j < 255) :
    constPair (4407 + j) = (wuCell j, wuV j) := by
  have d : 4407 + j - 4407 = j := by omega
  unfold constPair
  rw [if_neg (show ¬ (4407 + j = 0) by omega), if_neg (show ¬ (4407 + j = 1) by omega),
    if_neg (show ¬ (4407 + j = 2) by omega), if_neg (show ¬ (4407 + j = 3) by omega),
    if_neg (show ¬ (4407 + j < 38) by omega), if_neg (show ¬ (4407 + j < 72) by omega),
    if_neg (show ¬ (4407 + j < 327) by omega), if_neg (show ¬ (4407 + j < 4407) by omega),
    if_pos (show 4407 + j < 4662 by omega), d]

theorem constInstr_wu {j : ℕ} (hj : j < 255) :
    constInstr (4407 + j) = .setc (wuCell j) (wuV j) :=
  constInstr_of_pair (constPair_wu hj)

theorem constPair_wuHi {j : ℕ} (hj : j < 255) :
    constPair (4662 + j) = (wuHiCell j, wuHiV j) := by
  have d : 4662 + j - 4662 = j := by omega
  unfold constPair
  rw [if_neg (show ¬ (4662 + j = 0) by omega), if_neg (show ¬ (4662 + j = 1) by omega),
    if_neg (show ¬ (4662 + j = 2) by omega), if_neg (show ¬ (4662 + j = 3) by omega),
    if_neg (show ¬ (4662 + j < 38) by omega), if_neg (show ¬ (4662 + j < 72) by omega),
    if_neg (show ¬ (4662 + j < 327) by omega), if_neg (show ¬ (4662 + j < 4407) by omega),
    if_neg (show ¬ (4662 + j < 4662) by omega), if_pos (show 4662 + j < 4917 by omega), d]

theorem constInstr_wuHi {j : ℕ} (hj : j < 255) :
    constInstr (4662 + j) = .setc (wuHiCell j) (wuHiV j) :=
  constInstr_of_pair (constPair_wuHi hj)

theorem constPair_wuLo {j : ℕ} (hj : j < 255) :
    constPair (4917 + j) = (wuLoCell j, wuLoV j) := by
  have d : 4917 + j - 4917 = j := by omega
  unfold constPair
  rw [if_neg (show ¬ (4917 + j = 0) by omega), if_neg (show ¬ (4917 + j = 1) by omega),
    if_neg (show ¬ (4917 + j = 2) by omega), if_neg (show ¬ (4917 + j = 3) by omega),
    if_neg (show ¬ (4917 + j < 38) by omega), if_neg (show ¬ (4917 + j < 72) by omega),
    if_neg (show ¬ (4917 + j < 327) by omega), if_neg (show ¬ (4917 + j < 4407) by omega),
    if_neg (show ¬ (4917 + j < 4662) by omega), if_neg (show ¬ (4917 + j < 4917) by omega),
    if_pos (show 4917 + j < 5172 by omega), d]

theorem constInstr_wuLo {j : ℕ} (hj : j < 255) :
    constInstr (4917 + j) = .setc (wuLoCell j) (wuLoV j) :=
  constInstr_of_pair (constPair_wuLo hj)

theorem constPair_vb {p : ℕ} (hp : p < 16) :
    constPair (5174 + p) = (vbCell p, vbV p) := by
  have d : 5174 + p - 5174 = p := by omega
  unfold constPair
  rw [if_neg (show ¬ (5174 + p = 0) by omega), if_neg (show ¬ (5174 + p = 1) by omega),
    if_neg (show ¬ (5174 + p = 2) by omega), if_neg (show ¬ (5174 + p = 3) by omega),
    if_neg (show ¬ (5174 + p < 38) by omega), if_neg (show ¬ (5174 + p < 72) by omega),
    if_neg (show ¬ (5174 + p < 327) by omega), if_neg (show ¬ (5174 + p < 4407) by omega),
    if_neg (show ¬ (5174 + p < 4662) by omega), if_neg (show ¬ (5174 + p < 4917) by omega),
    if_neg (show ¬ (5174 + p < 5172) by omega), if_neg (show ¬ (5174 + p = 5172) by omega),
    if_neg (show ¬ (5174 + p = 5173) by omega), if_pos (show 5174 + p < 5190 by omega), d]

theorem constInstr_vb {p : ℕ} (hp : p < 16) :
    constInstr (5174 + p) = .setc (vbCell p) (vbV p) :=
  constInstr_of_pair (constPair_vb hp)

theorem constPair_ubHi : constPair 5172 = (ubHiCell, ubHiV) := by
  first
    | rfl
    | (unfold constPair; norm_num)

theorem constInstr_ubHi : constInstr 5172 = .setc ubHiCell ubHiV :=
  constInstr_of_pair constPair_ubHi

theorem constPair_ubLo : constPair 5173 = (ubLoCell, ubLoV) := by
  first
    | rfl
    | (unfold constPair; norm_num)

theorem constInstr_ubLo : constInstr 5173 = .setc ubLoCell ubLoV :=
  constInstr_of_pair constPair_ubLo

theorem constPair_len : constPair 5190 = (lenCell, lenV) := by
  first
    | rfl
    | (unfold constPair; norm_num)

theorem constInstr_len : constInstr 5190 = .setc lenCell lenV :=
  constInstr_of_pair constPair_len

/-! ## Segment decomposition -/

set_option maxHeartbeats 1000000 in
/-- Every index below `N` lies in exactly one segment slot. -/
theorem forall_lt_N_iff (P : ℕ → Prop) :
    (∀ k < N, P k) ↔
      (∀ a < A_len, P a) ∧
      (∀ i < 34, ∀ j < 255, ∀ r < 10, P (A_len + 2553 * i + 10 * j + r)) ∧
      (∀ i < 34, ∀ e < 3, P (A_len + 2553 * i + 2550 + e)) ∧
      (∀ h < 2, ∀ s < 15, P (C_start + 15 * h + s)) ∧
      (∀ s < 32, P (D_start + s)) ∧
      (∀ t < 35, P (E_start + t)) ∧
      (∀ u < 3, P (F_start + u)) := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hD : D_start = 92023 := rfl
  have hE : E_start = 92055 := rfl
  have hF : F_start = 92090 := rfl
  have hN : N = 92093 := rfl
  constructor
  · intro hP
    refine ⟨fun a ha => hP a (by omega), fun i hi j hj r hr => hP _ (by omega),
      fun i hi e he => hP _ (by omega), fun h hh s hs => hP _ (by omega),
      fun s hs => hP _ (by omega), fun t ht => hP _ (by omega), fun u hu => hP _ (by omega)⟩
  · rintro ⟨hPA, hPB, hPE, hPC, hPD, hPR, hPF⟩ k hk
    by_cases h1 : k < A_len
    · exact hPA k h1
    by_cases h2 : k < C_start
    · by_cases h3 : (k - A_len) % 2553 < 2550
      · have e : A_len + 2553 * ((k - A_len) / 2553) + 10 * ((k - A_len) % 2553 / 10) +
            (k - A_len) % 2553 % 10 = k := by omega
        have := hPB ((k - A_len) / 2553) (by omega) ((k - A_len) % 2553 / 10) (by omega)
          ((k - A_len) % 2553 % 10) (by omega)
        rwa [e] at this
      · have e : A_len + 2553 * ((k - A_len) / 2553) + 2550 + ((k - A_len) % 2553 - 2550) =
            k := by omega
        have := hPE ((k - A_len) / 2553) (by omega) ((k - A_len) % 2553 - 2550) (by omega)
        rwa [e] at this
    by_cases h4 : k < D_start
    · have e : C_start + 15 * ((k - C_start) / 15) + (k - C_start) % 15 = k := by omega
      have := hPC ((k - C_start) / 15) (by omega) ((k - C_start) % 15) (by omega)
      rwa [e] at this
    by_cases h5 : k < E_start
    · have e : D_start + (k - D_start) = k := by omega
      have := hPD (k - D_start) (by omega)
      rwa [e] at this
    by_cases h6 : k < F_start
    · have e : E_start + (k - E_start) = k := by omega
      have := hPR (k - E_start) (by omega)
      rwa [e] at this
    · have e : F_start + (k - F_start) = k := by omega
      have := hPF (k - F_start) (by omega)
      rwa [e] at this

set_option maxHeartbeats 1000000 in
/-- Segment A split into its constant groups. -/
theorem forall_lt_A_iff (P : ℕ → Prop) :
    (∀ a < A_len, P a) ↔
      P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ (∀ i < 34, P (4 + i)) ∧ (∀ r < 34, P (38 + r)) ∧
      (∀ j < 255, P (72 + j)) ∧ (∀ p < 16, ∀ j < 255, P (327 + 255 * p + j)) ∧
      (∀ j < 255, P (4407 + j)) ∧ (∀ j < 255, P (4662 + j)) ∧ (∀ j < 255, P (4917 + j)) ∧
      P 5172 ∧ P 5173 ∧ (∀ p < 16, P (5174 + p)) ∧ P 5190 := by
  have hA : A_len = 5191 := rfl
  constructor
  · intro hP
    refine ⟨hP 0 (by omega), hP 1 (by omega), hP 2 (by omega), hP 3 (by omega),
      fun i hi => hP _ (by omega), fun r hr => hP _ (by omega), fun j hj => hP _ (by omega),
      fun p hp j hj => hP _ (by omega), fun j hj => hP _ (by omega),
      fun j hj => hP _ (by omega), fun j hj => hP _ (by omega), hP 5172 (by omega),
      hP 5173 (by omega), fun p hp => hP _ (by omega), hP 5190 (by omega)⟩
  · rintro ⟨h0, h1, h2, h3, hI, hR, hJ, hW, hU, hUH, hUL, hBH, hBL, hVB, hLen⟩ a ha
    by_cases c0 : a = 0
    · subst c0; exact h0
    by_cases c1 : a = 1
    · subst c1; exact h1
    by_cases c2 : a = 2
    · subst c2; exact h2
    by_cases c3 : a = 3
    · subst c3; exact h3
    by_cases c4 : a < 38
    · have := hI (a - 4) (by omega)
      rwa [show 4 + (a - 4) = a by omega] at this
    by_cases c5 : a < 72
    · have := hR (a - 38) (by omega)
      rwa [show 38 + (a - 38) = a by omega] at this
    by_cases c6 : a < 327
    · have := hJ (a - 72) (by omega)
      rwa [show 72 + (a - 72) = a by omega] at this
    by_cases c7 : a < 4407
    · have := hW ((a - 327) / 255) (by omega) ((a - 327) % 255) (by omega)
      rwa [show 327 + 255 * ((a - 327) / 255) + (a - 327) % 255 = a by omega] at this
    by_cases c8 : a < 4662
    · have := hU (a - 4407) (by omega)
      rwa [show 4407 + (a - 4407) = a by omega] at this
    by_cases c9 : a < 4917
    · have := hUH (a - 4662) (by omega)
      rwa [show 4662 + (a - 4662) = a by omega] at this
    by_cases c10 : a < 5172
    · have := hUL (a - 4917) (by omega)
      rwa [show 4917 + (a - 4917) = a by omega] at this
    by_cases c11 : a = 5172
    · subst c11; exact hBH
    by_cases c12 : a = 5173
    · subst c12; exact hBL
    by_cases c13 : a < 5190
    · have := hVB (a - 5174) (by omega)
      rwa [show 5174 + (a - 5174) = a by omega] at this
    · have e : a = 5190 := by omega
      subst e
      exact hLen

/-! ## Uniform facts over the program -/

section Uniform

/-- Every Segment A cell is below `2 ^ 17`, group by group (the chain of `constPair` is never
split). -/
theorem constInstr_bounded : ∀ a < A_len, (constInstr a).Bounded 131072 := by
  refine (forall_lt_A_iff _).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [constInstr_zero]; simp only [CInstr.Bounded, zCell]; omega
  · rw [constInstr_one]; simp only [CInstr.Bounded, z2Cell]; omega
  · rw [constInstr_two]; simp only [CInstr.Bounded, oneCell]; omega
  · rw [constInstr_three]; simp only [CInstr.Bounded, fpcCell]; omega
  · intro i hi; rw [constInstr_chainId hi]; simp only [CInstr.Bounded, chainIdCell]; omega
  · intro r hr; rw [constInstr_rootMd hr]; simp only [CInstr.Bounded, rootMdCell]; omega
  · intro j hj; rw [constInstr_pos hj]; simp only [CInstr.Bounded, posCell]; omega
  · intro p hp j hj; rw [constInstr_wv hp hj]; simp only [CInstr.Bounded, wvCell]; omega
  · intro j hj; rw [constInstr_wu hj]; simp only [CInstr.Bounded, wuCell]; omega
  · intro j hj; rw [constInstr_wuHi hj]; simp only [CInstr.Bounded, wuHiCell]; omega
  · intro j hj; rw [constInstr_wuLo hj]; simp only [CInstr.Bounded, wuLoCell]; omega
  · rw [constInstr_ubHi]; simp only [CInstr.Bounded, ubHiCell]; omega
  · rw [constInstr_ubLo]; simp only [CInstr.Bounded, ubLoCell]; omega
  · intro p hp; rw [constInstr_vb hp]; simp only [CInstr.Bounded, vbCell]; omega
  · rw [constInstr_len]; simp only [CInstr.Bounded, lenCell]; omega

set_option maxHeartbeats 1000000 in
theorem stepInstr_bounded {i j : ℕ} (hi : i < 34) (hj : j < 255) (r : ℕ) :
    (stepInstr i j r).Bounded 131072 := by
  unfold stepInstr
  split_ifs <;>
    simp only [CInstr.Bounded, tCell, sCell, uCell, inCell, pVCell, pUCell, stepCell,
      chainBase, tPrevCell, xCell, aVCell, aUCell, aUBaseCell, wuSelCell, bytePos, sigCell,
      chainIdCell, posCell, wvCell, wuCell, wuHiCell, wuLoCell, vbCell, zCell, oneCell,
      ubHiCell, ubLoCell] <;>
    (try split_ifs) <;>
    omega

set_option maxHeartbeats 1000000 in
theorem endInstr_bounded {i : ℕ} (hi : i < 34) (e : ℕ) : (endInstr i e).Bounded 131072 := by
  unfold endInstr
  split_ifs <;>
    simp only [CInstr.Bounded, tCell, stepCell, chainBase, xCell, sigCell, e0Cell, e1Cell,
      endCell] <;>
    (try split_ifs) <;>
    omega

set_option maxHeartbeats 1000000 in
theorem linkInstr_bounded {h s : ℕ} (hh : h < 2) (hs : s < 15) :
    (linkInstr h s).Bounded 131072 := by
  simp only [linkInstr, CInstr.Bounded, linkAccCell, dCell, linkChain, stepCell, chainBase]
  (try split_ifs) <;> omega

set_option maxHeartbeats 1000000 in
theorem prodInstr_bounded {s : ℕ} (hs : s < 32) : (prodInstr s).Bounded 131072 := by
  unfold prodInstr
  split_ifs <;>
    simp only [CInstr.Bounded, prodAccCell, pCell, stepCell, chainBase] <;>
    (try split_ifs) <;>
    omega

set_option maxHeartbeats 1000000 in
theorem rootInstr_bounded {t : ℕ} (ht : t < 35) : (rootInstr t).Bounded 131072 := by
  unfold rootInstr
  split_ifs <;>
    simp only [CInstr.Bounded, endCell, zCell, rootStateCell, rootMdCell, chainBase,
      pkCell] <;>
    (try split_ifs) <;>
    omega

theorem haltInstr_bounded (u : ℕ) : (haltInstr u).Bounded 131072 := by
  unfold haltInstr
  split_ifs <;> simp only [CInstr.Bounded, haltOneCell, haltFpcCell] <;> omega

/-- Every cell of every instruction is below `2 ^ 17`. -/
theorem cinstrAt_bounded17 : ∀ k < N, (cinstrAt k).Bounded 131072 := by
  refine (forall_lt_N_iff _).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [cinstrAt_const ha]
    exact constInstr_bounded a ha
  · intro i hi j hj r hr
    rw [cinstrAt_step hi hj hr]
    exact stepInstr_bounded hi hj r
  · intro i hi e he
    rw [cinstrAt_end hi he]
    exact endInstr_bounded hi e
  · intro h hh s hs
    rw [cinstrAt_link hh hs]
    exact linkInstr_bounded hh hs
  · intro s hs
    rw [cinstrAt_prod hs]
    exact prodInstr_bounded hs
  · intro t ht
    rw [cinstrAt_root ht]
    exact rootInstr_bounded ht
  · intro u hu
    rw [cinstrAt_halt hu]
    exact haltInstr_bounded u

theorem cinstrAt_bounded (k : ℕ) (hk : k < N) : (cinstrAt k).Bounded (2 ^ 64 - 1) :=
  CInstr.Bounded.mono (cinstrAt_bounded17 k hk) (by norm_num)

theorem constInstr_isJump (a : ℕ) : (constInstr a).isJump = false := rfl

theorem stepInstr_isJump (i j r : ℕ) : (stepInstr i j r).isJump = false := by
  unfold stepInstr
  split_ifs <;> rfl

theorem endInstr_isJump (i e : ℕ) : (endInstr i e).isJump = false := by
  unfold endInstr
  split_ifs <;> rfl

theorem linkInstr_isJump (h s : ℕ) : (linkInstr h s).isJump = false := rfl

theorem prodInstr_isJump (s : ℕ) : (prodInstr s).isJump = false := by
  unfold prodInstr
  split_ifs <;> rfl

theorem rootInstr_isJump (t : ℕ) : (rootInstr t).isJump = false := by
  unfold rootInstr
  split_ifs <;> rfl

theorem haltInstr_isJump {u : ℕ} (hu : u < 2) : (haltInstr u).isJump = false := by
  unfold haltInstr
  split_ifs <;> first | rfl | (exfalso; omega)

theorem cinstrAt_isJump' : ∀ k < N, k + 1 < N → (cinstrAt k).isJump = false := by
  have hF : F_start + 3 = N := rfl
  refine (forall_lt_N_iff _).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha _
    rw [cinstrAt_const ha]
    exact constInstr_isJump a
  · intro i hi j hj r hr _
    rw [cinstrAt_step hi hj hr]
    exact stepInstr_isJump i j r
  · intro i hi e he _
    rw [cinstrAt_end hi he]
    exact endInstr_isJump i e
  · intro h hh s hs _
    rw [cinstrAt_link hh hs]
    exact linkInstr_isJump h s
  · intro s hs _
    rw [cinstrAt_prod hs]
    exact prodInstr_isJump s
  · intro t ht _
    rw [cinstrAt_root ht]
    exact rootInstr_isJump t
  · intro u hu hu1
    rw [cinstrAt_halt hu]
    exact haltInstr_isJump (by omega)

/-- Only the last instruction is a `JUMP`. -/
theorem cinstrAt_isJump (k : ℕ) (hk : k + 1 < N) : (cinstrAt k).isJump = false :=
  cinstrAt_isJump' k (by omega) hk

/-! ### Costs -/

theorem constInstr_cost (a : ℕ) : (constInstr a).cost = 1 := rfl

theorem stepInstr_cost (i j r : ℕ) : (stepInstr i j r).cost = if r = 5 then 10 else 1 := by
  unfold stepInstr
  split_ifs <;> first | rfl | omega

theorem endInstr_cost (i e : ℕ) : (endInstr i e).cost = 1 := by
  unfold endInstr
  split_ifs <;> rfl

theorem linkInstr_cost (h s : ℕ) : (linkInstr h s).cost = 1 := rfl

theorem prodInstr_cost (s : ℕ) : (prodInstr s).cost = 1 := by
  unfold prodInstr
  split_ifs <;> rfl

theorem rootInstr_cost (t : ℕ) : (rootInstr t).cost = if t < 34 then 10 else 1 := by
  unfold rootInstr
  split_ifs <;> first | rfl | omega

theorem haltInstr_cost (u : ℕ) : (haltInstr u).cost = 1 := by
  unfold haltInstr
  split_ifs <;> rfl

/-- The number of `BLAKE2S` instructions at indices below `k`. -/
def blakesBefore (k : ℕ) : ℕ :=
  if k < A_len then 0
  else if k < C_start then 255 * ((k - A_len) / 2553) + ((k - A_len) % 2553 + 4) / 10
  else if k < E_start then 8670
  else if k < E_start + 34 then 8670 + (k - E_start)
  else 8704

/-- The cost of the straight-line run from index `k` to the sentinel. -/
def costFrom (k : ℕ) : ℕ := (N - k) + 9 * (hashCount - blakesBefore k)

theorem costFrom_zero : costFrom 0 = totalCost := by
  first
    | rfl
    | decide

theorem costFrom_F_start : costFrom F_start = 3 := by
  first
    | rfl
    | decide

set_option maxHeartbeats 1000000 in
theorem costFrom_succ_const {a : ℕ} (ha : a < A_len) :
    costFrom a = (cinstrAt a).cost + costFrom (a + 1) := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hE : E_start = 92055 := rfl
  have hN : N = 92093 := rfl
  have hH : hashCount = 8704 := rfl
  rw [cinstrAt_const ha, constInstr_cost]
  simp only [costFrom, blakesBefore, if_pos ha]
  (try split_ifs) <;> omega

set_option maxHeartbeats 1000000 in
theorem costFrom_succ_step {i j r : ℕ} (hi : i < 34) (hj : j < 255) (hr : r < 10) :
    costFrom (A_len + 2553 * i + 10 * j + r) =
      (cinstrAt (A_len + 2553 * i + 10 * j + r)).cost +
        costFrom (A_len + 2553 * i + 10 * j + r + 1) := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hN : N = 92093 := rfl
  have hH : hashCount = 8704 := rfl
  have d1 : (A_len + 2553 * i + 10 * j + r - A_len) / 2553 = i := by omega
  have d2 : (A_len + 2553 * i + 10 * j + r - A_len) % 2553 = 10 * j + r := by omega
  have d3 : (A_len + 2553 * i + 10 * j + r + 1 - A_len) / 2553 = i := by omega
  have d4 : (A_len + 2553 * i + 10 * j + r + 1 - A_len) % 2553 = 10 * j + r + 1 := by omega
  have e1 : ¬ (A_len + 2553 * i + 10 * j + r < A_len) := by omega
  have e2 : A_len + 2553 * i + 10 * j + r < C_start := by omega
  have e3 : ¬ (A_len + 2553 * i + 10 * j + r + 1 < A_len) := by omega
  have e4 : A_len + 2553 * i + 10 * j + r + 1 < C_start := by omega
  rw [cinstrAt_step hi hj hr, stepInstr_cost]
  simp only [costFrom, blakesBefore, if_neg e1, if_pos e2, if_neg e3, if_pos e4, d1, d2, d3, d4]
  (try split_ifs) <;> omega

set_option maxHeartbeats 1000000 in
theorem costFrom_succ_end {i e : ℕ} (hi : i < 34) (he : e < 3) :
    costFrom (A_len + 2553 * i + 2550 + e) =
      (cinstrAt (A_len + 2553 * i + 2550 + e)).cost +
        costFrom (A_len + 2553 * i + 2550 + e + 1) := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hE : E_start = 92055 := rfl
  have hN : N = 92093 := rfl
  have hH : hashCount = 8704 := rfl
  have d1 : (A_len + 2553 * i + 2550 + e - A_len) / 2553 = i := by omega
  have d2 : (A_len + 2553 * i + 2550 + e - A_len) % 2553 = 2550 + e := by omega
  have e1 : ¬ (A_len + 2553 * i + 2550 + e < A_len) := by omega
  have e2 : A_len + 2553 * i + 2550 + e < C_start := by omega
  rw [cinstrAt_end hi he, endInstr_cost]
  simp only [costFrom, blakesBefore, if_neg e1, if_pos e2, d1, d2]
  (try split_ifs) <;> omega

set_option maxHeartbeats 1000000 in
theorem costFrom_succ_link {h s : ℕ} (hh : h < 2) (hs : s < 15) :
    costFrom (C_start + 15 * h + s) =
      (cinstrAt (C_start + 15 * h + s)).cost + costFrom (C_start + 15 * h + s + 1) := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hE : E_start = 92055 := rfl
  have hN : N = 92093 := rfl
  have hH : hashCount = 8704 := rfl
  have e1 : ¬ (C_start + 15 * h + s < A_len) := by omega
  have e2 : ¬ (C_start + 15 * h + s < C_start) := by omega
  have e3 : C_start + 15 * h + s < E_start := by omega
  have e4 : ¬ (C_start + 15 * h + s + 1 < A_len) := by omega
  have e5 : ¬ (C_start + 15 * h + s + 1 < C_start) := by omega
  have e6 : C_start + 15 * h + s + 1 < E_start := by omega
  rw [cinstrAt_link hh hs, linkInstr_cost]
  simp only [costFrom, blakesBefore, if_neg e1, if_neg e2, if_pos e3, if_neg e4, if_neg e5,
    if_pos e6]
  (try split_ifs) <;> omega

set_option maxHeartbeats 1000000 in
theorem costFrom_succ_prod {s : ℕ} (hs : s < 32) :
    costFrom (D_start + s) = (cinstrAt (D_start + s)).cost + costFrom (D_start + s + 1) := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hD : D_start = 92023 := rfl
  have hE : E_start = 92055 := rfl
  have hN : N = 92093 := rfl
  have hH : hashCount = 8704 := rfl
  have e1 : ¬ (D_start + s < A_len) := by omega
  have e2 : ¬ (D_start + s < C_start) := by omega
  have e3 : D_start + s < E_start := by omega
  have e4 : ¬ (D_start + s + 1 < A_len) := by omega
  have e5 : ¬ (D_start + s + 1 < C_start) := by omega
  rw [cinstrAt_prod hs, prodInstr_cost]
  simp only [costFrom, blakesBefore, if_neg e1, if_neg e2, if_pos e3, if_neg e4, if_neg e5]
  (try split_ifs) <;> omega

set_option maxHeartbeats 1000000 in
theorem costFrom_succ_root {t : ℕ} (ht : t < 35) :
    costFrom (E_start + t) = (cinstrAt (E_start + t)).cost + costFrom (E_start + t + 1) := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hE : E_start = 92055 := rfl
  have hN : N = 92093 := rfl
  have hH : hashCount = 8704 := rfl
  have e1 : ¬ (E_start + t < A_len) := by omega
  have e2 : ¬ (E_start + t < C_start) := by omega
  have e3 : ¬ (E_start + t < E_start) := by omega
  have e4 : ¬ (E_start + t + 1 < A_len) := by omega
  have e5 : ¬ (E_start + t + 1 < C_start) := by omega
  have e6 : ¬ (E_start + t + 1 < E_start) := by omega
  rw [cinstrAt_root ht, rootInstr_cost]
  simp only [costFrom, blakesBefore, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
    if_neg e6]
  (try split_ifs) <;> omega

set_option maxHeartbeats 1000000 in
theorem costFrom_succ_halt {u : ℕ} (hu : u < 3) :
    costFrom (F_start + u) = (cinstrAt (F_start + u)).cost + costFrom (F_start + u + 1) := by
  have hA : A_len = 5191 := rfl
  have hC : C_start = 91993 := rfl
  have hE : E_start = 92055 := rfl
  have hF : F_start = 92090 := rfl
  have hN : N = 92093 := rfl
  have hH : hashCount = 8704 := rfl
  have e1 : ¬ (F_start + u < A_len) := by omega
  have e2 : ¬ (F_start + u < C_start) := by omega
  have e3 : ¬ (F_start + u < E_start) := by omega
  have e4 : ¬ (F_start + u < E_start + 34) := by omega
  have e5 : ¬ (F_start + u + 1 < A_len) := by omega
  have e6 : ¬ (F_start + u + 1 < C_start) := by omega
  have e7 : ¬ (F_start + u + 1 < E_start) := by omega
  have e8 : ¬ (F_start + u + 1 < E_start + 34) := by omega
  rw [cinstrAt_halt hu, haltInstr_cost]
  simp only [costFrom, blakesBefore, if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5,
    if_neg e6, if_neg e7, if_neg e8]
  (try split_ifs) <;> omega

theorem costFrom_succ' : ∀ k < N, costFrom k = (cinstrAt k).cost + costFrom (k + 1) := by
  refine (forall_lt_N_iff _).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact costFrom_succ_const ha
  · intro i hi j hj r hr
    exact costFrom_succ_step hi hj hr
  · intro i hi e he
    exact costFrom_succ_end hi he
  · intro h hh s hs
    exact costFrom_succ_link hh hs
  · intro s hs
    exact costFrom_succ_prod hs
  · intro t ht
    exact costFrom_succ_root ht
  · intro u hu
    exact costFrom_succ_halt hu

/-- The potential decreases by exactly the cost of the instruction executed. -/
theorem costFrom_succ (k : ℕ) (hk : k < N) :
    costFrom k = (cinstrAt k).cost + costFrom (k + 1) :=
  costFrom_succ' k hk

end Uniform

end

end OptimalOTS.LeanIsaBaseline.Machine
