import Submissions.UpperRiscvHint.Program

/-! The 315-cycle free-chain image. Caps 31 and 32 occupy the opposite boundaries
of an 884-byte root at 0x400046; caps 0 through 12 have 192-bit states, and the boundary
caps have 144-bit states. Other chains have 144-bit states and a mandatory final hash.
Chain 32's state uses answer bits [112,256), leaving its input pointer at the root start.
Chain 31's top uses [0,144); chain 30 contributes a full 256-bit top before it.

The loader supplies the capped view length L in x13. ANDI with -1924 preserves its
2048-bit bank and bits 2 through 6. An honest view supplies the dispatch base 6144
and displacement 4*(31-c) together, removing one ADD before the indirect jump.
The adjusted checksum equals the HASH call number exactly when S+c = 145 modulo 255.
Other banks either fault outside the image or land in reserved rejection windows.
Counts at least 16 reject within the honest bank. Raw forms are padded into a guarded bank.

Pair 0's prologue occurs once, so its jump links a fixed address into x1: the root length is
that address plus 2044, and no constant load is needed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix wordReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

/-- The answer buffer of chain `k`, and for a cap also its value and state. -/
def outAddr (k : ℕ) : ℕ :=
  if k = 32 then 0x400038 else if k = 31 then 0x4003A8 else 0x400058 +
    if k ≤ 12 then 56 * k else if k < 25 then 56 * (k - 13) + 24 else 696 + 24 * (k - 25)
/-- View byte offset of chain `k`'s value, after the 16-byte nonce. -/
def wireByte (k : ℕ) : ℕ :=
  if k = 32 then 6 else 24 +
    if k ≤ 12 then 56 * k else if k < 25 then 56 * (k - 13) + 32 else 704 + 24 * (k - 25)
/-- The input address while chain `k` hashes: its value in the view, then its state. -/
def work (k : ℕ) : ℕ := 0x400040 + wireByte k
/-- A bound containing every fixed payload position in an honest view. -/
def honestViewBits : ℕ := 7248
/-- The former count byte, now unused by execution. -/
def freeByte : ℕ := 0x400070
/-- The honest bank's dispatch base: the masked tag of an honest view length less `4*(31-c)`. -/
def freeBase : ℕ := 6144
def fineWidth (_q : ℕ) : ℕ := 4
def copies (_q : ℕ) : ℕ := 16
/-- Corresponding pairs of all four words share one base. Adjacent groups interleave
their boundary rows; the final row has fifteen fewer hashes in each body. -/
def group (q : ℕ) : ℕ := q % 4
def withinGroup (q : ℕ) : ℕ := q / 4
def groupOffset (_g : ℕ) : ℕ := 0
def slotOffset (q : ℕ) : ℕ :=
  [0,3899,7446,11596,37,3705,7506,11407,352,4253,7861,11558,181,4093,7799,11517].getD q 0
/-- The code index of the first copy: after the index phase, the free dispatch, the free row and
pair 0's prologue. -/
def copiesIndex : ℕ := 233
def copiesStart : ℕ := 4096 + 4 * copiesIndex
def copyStart (q d : ℕ) : ℕ :=
  copiesStart + 4 * (groupOffset (group q) + 256 * (copies q - 1 - d) + slotOffset q)
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 4 * (2 ^ fineWidth q - 1)
/-- Lane 0 carries the bias for the masked tag: adding `6144 + 4*(31-c)` gives
residue 1 exactly when the digit sum plus `c` is 145 modulo 255. -/
def baseLane (q : ℕ) : ℕ := min (landing0 (q % 4)) 65532 + if q % 4 = 0 then 233 else 0
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
/-- A cap pair's first chain hashes once per digit unit, one hash fewer than a normal chain, so
its landing is one row later. -/
def lead (q : ℕ) : ℕ := if q < 6 ∨ 15 ≤ q then 1 else 0
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) + 4 * lead q - baseLane q
def baseReg (_g : ℕ) : Reg := .x3

/-- The four index words, the lane mask, the checksum modulus and the dispatch base. -/
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16, .LD .x23 .x12 24,
   .LD .x25 .x12 32, .LD .x2 .x12 40, .LD .x3 .x12 48]
/-- The length bank and complemented count: `x6 = cappedViewLength & ~0x783`. -/
def freeCount : Code :=
  [.ANDI .x6 .x13 (imm12 (-1924))]
def maskReg (_g : ℕ) : Reg := .x25
def laneWord (g : ℕ) : Code :=
  let dst := if g = 0 then Reg.x27 else Reg.x26
  [.AND dst (wordReg g) (maskReg g), .SUB dst (baseReg g) dst] ++
    (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
    [.SD .x10 dst (imm12 ((laneWordAddr g : ℤ) - hashBase))]
def freeSum : Code := [.ADD .x27 .x27 .x6]
/-- The residue lands in `x5`: 1, the HASH call number, exactly when the digit sum plus the free
count is 145 modulo 255. Any other residue traps at the first hash. -/
def sumCheck : Code := [.REMU .x5 .x27 .x2]
/-- The free chain and the caps hash first: the chain width is 192 bits until pair 6. -/
def chainSetup : Code := [.ADDI .x11 .x0 192]
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ loadWords ++ freeCount ++
    (List.range 4).flatMap laneWord ++ freeSum ++ sumCheck ++ chainSetup

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((work k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - work k))]
/-- Pair 0's prologue, where the free dispatch lands for count 0. -/
def freeLanding : ℕ := 4096 + 4 * 229
/-- The link of pair 0's jump, from which the root length is computed. -/
def rootBase : ℕ := freeLanding + 16
/-- The free chain's pointers, then the jump `c` cells before pair 0's prologue. The padding
places pair 0's jump within `ADDI` reach of the root length. -/
def freeDispatch : Code :=
  enter 0 hashBase ++ .JALR .x0 .x6 (imm12 ((freeLanding : ℤ) - freeBase - 124)) ::
    List.replicate 130 nop
/-- Only pair 0's jump links: its prologue is the one copy at `freeLanding`. -/
def linkReg (q : ℕ) : Reg := if q = 0 then .x1 else .x0
/-- The table-row register `x28` changes only while `x12` points at neither chain of the pair. -/
def prologue (q : ℕ) : Code :=
  (if q = 6 then [.ADDI .x11 .x0 144] else []) ++
    [.ADDI .x12 .x10 (imm12 ((outAddr (2*q+1) : ℤ) - work (2*q))),
     .LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q+1))),
     .ADDI .x10 .x12 (imm12 ((work (2*q+1) : ℤ) - outAddr (2*q+1))),
     .JALR (linkReg q) .x28 (imm12 (jumpImm q))]
/-- The last chain's state is the root input's first slot, so `x10` needs no move. The root length
is pair 0's link plus 2044. -/
def root : Code := [.ADDI .x11 .x1 (imm12 (7072 - (rootBase : ℤ))), .ECALL]
def pairCap (_q : ℕ) : ℕ := 24
/-- Each unexpected length bank has 32 rejection targets and a preceding rejection stub. -/
def guardStart (bank : ℕ) : ℕ := 198 + 512*(bank-3)
def guardBanks : List ℕ := (List.range 509).map (· + 4)
def rejectStubs : List ℕ := guardBanks.map (fun bank => guardStart bank - 3)
def guardCode : Code := (List.range 32).map fun d =>
  .BEQ .x0 .x0 (BitVec.ofInt 13 (-12 - 4*(d : ℤ)))
def stubFor (ip : ℕ) : ℕ :=
  (rejectStubs.find? fun (s : ℕ) => decide (-4096 ≤ 4*((s : ℤ)-ip) ∧ 4*((s : ℤ)-ip) < 4096)).getD 707
def rejectJump (ip : ℕ) : Instr :=
  .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((stubFor ip : ℤ)-ip)))
/-- The free cell `c` instructions before pair 0's prologue: a hash of the free chain, or for
`c ≥ 16` a jump to a rejection stub. -/
def freeCell (c : ℕ) : Instr := if c < 16 then .ECALL else rejectJump (229 - c)
def freeRow : Code := [nop] ++ (List.range 63).map fun p => freeCell (63 - p)
/-- Landing at row `i` hashes the first chain `16 - i` times, that is for digit
`15 - i + lead q`. A cap row's entry 0 would need digit 16 and is never a landing. -/
def rowInstr (q d i : ℕ) : Instr :=
  if i < lead q ∨ 15-i+lead q+d ≤ pairCap q then .ECALL
  else rejectJump (copiesIndex + groupOffset (group q) + 256*(15-d) + slotOffset q + i)
def hashRow (q d : ℕ) : Code := (List.range (2 ^ fineWidth q)).map (rowInstr q d)
def copyCode (q d : ℕ) : Code :=
  hashRow q d ++ enter (2*q+2) (work (2*q+1)) ++ List.replicate (d+1-lead q) .ECALL ++
    (if q = 15 then root ++ decision else prologue (q+1))
/-- Bodies in physical order. At each boundary the old final row and new first row alternate. -/
def rowKeys (g c : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).map fun j => (g+4*j, 15-c)
def fragmentKeys : List (ℕ × ℕ) :=
  [(0,15), (4,15), (12,15), (0,14), (4,14), (8,15), (12,14), (0,13),
   (4,13), (8,14), (12,13), (0,12), (4,12), (8,13), (12,12), (0,11),
   (4,11), (8,12), (12,11), (0,10), (4,10), (8,11), (12,10), (0,9),
   (4,9), (8,10), (12,9), (0,8), (4,8), (8,9), (12,8), (0,7),
   (4,7), (8,8), (12,7), (0,6), (4,6), (8,7), (12,6), (0,5),
   (4,5), (8,6), (12,5), (0,4), (4,4), (8,5), (12,4), (0,3),
   (4,3), (8,4), (12,3), (0,2), (4,2), (8,3), (12,2), (0,1),
   (4,1), (8,2), (5,15), (12,1), (0,0), (4,0), (1,15), (8,1),
   (5,14), (12,0), (13,15), (1,14), (8,0), (5,13), (9,15), (13,14),
   (1,13), (5,12), (9,14), (13,13), (1,12), (5,11), (9,13), (13,12),
   (1,11), (5,10), (9,12), (13,11), (1,10), (5,9), (9,11), (13,10),
   (1,9), (5,8), (9,10), (13,9), (1,8), (5,7), (9,9), (13,8),
   (1,7), (5,6), (9,8), (13,7), (1,6), (5,5), (9,7), (13,6),
   (1,5), (5,4), (9,6), (13,5), (1,4), (5,3), (9,5), (13,4),
   (1,3), (5,2), (9,4), (13,3), (1,2), (5,1), (9,3), (13,2),
   (2,15), (1,1), (6,15), (5,0), (9,2), (13,1), (2,14), (1,0),
   (6,14), (14,15), (9,1), (10,15), (13,0), (2,13), (6,13), (14,14),
   (9,0), (10,14), (2,12), (6,12), (14,13), (10,13), (2,11), (6,11),
   (14,12), (10,12), (2,10), (6,10), (14,11), (10,11), (2,9), (6,9),
   (14,10), (10,10), (2,8), (6,8), (14,9), (10,9), (2,7), (6,7),
   (14,8), (10,8), (2,6), (6,6), (14,7), (10,7), (2,5), (6,5),
   (14,6), (10,6), (2,4), (6,4), (14,5), (10,5), (2,3), (6,3),
   (14,4), (10,4), (2,2), (6,2), (14,3), (10,3), (2,1), (6,1),
   (14,2), (10,2), (2,0), (6,0), (14,1), (7,15), (10,1), (15,15),
   (11,15), (3,15), (14,0), (7,14), (10,0), (15,14), (11,14), (3,14),
   (7,13), (15,13), (11,13), (3,13), (7,12), (15,12), (11,12), (3,12),
   (7,11), (15,11), (11,11), (3,11), (7,10), (15,10), (11,10), (3,10),
   (7,9), (15,9), (11,9), (3,9), (7,8), (15,8), (11,8), (3,8),
   (7,7), (15,7), (11,7), (3,7), (7,6), (15,6), (11,6), (3,6),
   (7,5), (15,5), (11,5), (3,5), (7,4), (15,4), (11,4), (3,4),
   (7,3), (15,3), (11,3), (3,3), (7,2), (15,2), (11,2), (3,2),
   (7,1), (15,1), (11,1), (3,1), (7,0), (15,0), (11,0), (3,0)]
def copyFragments : List (ℕ × Code) :=
  fragmentKeys.map fun (q, d) =>
    (groupOffset (group q) + 256 * (15-d) + slotOffset q, copyCode q d)
def insertFragment (a : ℕ × Code) : List (ℕ × Code) → List (ℕ × Code)
  | [] => [a]
  | b :: rest => if a.1 ≤ b.1 then a :: b :: rest else b :: insertFragment a rest
def addStubs : List ℕ → List (ℕ × Code)
  | [] => copyFragments
  | ip :: rest => insertFragment (ip-copiesIndex,reject) (addStubs rest)
def addGuards : List ℕ → List (ℕ × Code) → List (ℕ × Code)
  | [], parts => parts
  | bank :: rest, parts => insertFragment (guardStart bank-copiesIndex,guardCode) (addGuards rest parts)
def fragments : List (ℕ × Code) := addGuards guardBanks (addStubs rejectStubs)
def assemble (cursor : ℕ) : List (ℕ × Code) → Code
  | [] => []
  | (off, body) :: rest =>
    List.replicate (off-cursor) (.JALR .x0 .x0 0) ++ body ++ assemble (off+body.length) rest
def assembledLength (cursor : ℕ) : List (ℕ × Code) → ℕ
  | [] => 0
  | (off, body) :: rest => off-cursor + body.length + assembledLength (off+body.length) rest

theorem assemble_length (cursor : ℕ) (parts : List (ℕ × Code)) :
    (assemble cursor parts).length = assembledLength cursor parts := by
  induction parts generalizing cursor with
  | nil => rfl
  | cons p rest ih => simp only [assemble, assembledLength, List.length_append, List.length_replicate, ih]

theorem assemble_admitted (cursor : ℕ) (parts : List (ℕ × Code))
    (h : ∀ p ∈ parts, p.2.all Riscv.admittedInstruction = true) :
    (assemble cursor parts).all Riscv.admittedInstruction = true := by
  induction parts generalizing cursor with
  | nil => rfl
  | cons p rest ih =>
    simp [assemble, List.all_append, h p (by simp),
      ih (p.1+p.2.length) (fun q hq => h q (by simp [hq])), Riscv.admittedInstruction]
def tables : Code := assemble 0 fragments
def verifier : Code := indexPhase ++ freeDispatch ++ freeRow ++ prologue 0 ++ tables

/-- The 32-byte index answer buffer, then the words loaded after the index query. -/
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes (broadcast 0x3c3c) ++ wordBytes 255 ++ wordBytes (baseWord 0)
def image : Riscv.Image := ⟨verifier, dataImage⟩

theorem index_length : indexPhase.length = 32 := by decide +kernel
theorem code_length : verifier.length = 260838 := by
  simp only [verifier, List.length_append, tables, assemble_length]
  decide +kernel
theorem data_length : dataImage.length = 56 := by decide +kernel
theorem admitted : verifier.all Riscv.admittedInstruction = true := by
  have h : fragments.all (fun p => p.2.all Riscv.admittedInstruction) = true := by decide +kernel
  have ht := assemble_admitted 0 fragments (List.all_eq_true.mp h)
  have hf : (indexPhase ++ freeDispatch ++ freeRow ++ prologue 0).all Riscv.admittedInstruction = true :=
    by decide +kernel
  exact (List.all_append).trans (by rw [hf, tables, ht]; rfl)
theorem image_valid : image.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · change verifier.length ≤ 262144
    rw [code_length]; norm_num
  · change dataImage.length ≤ 1048576
    rw [data_length]; norm_num
  · exact List.all_eq_true.mp admitted

theorem image_size : image.byteSize < 1048576 := by
  simp only [Riscv.Image.byteSize, image, code_length, data_length]
  decide

end OptimalOTS.RiscvMixedProgram
