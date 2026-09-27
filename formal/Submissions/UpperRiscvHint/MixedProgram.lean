import Submissions.UpperRiscvHint.Program

/-! The 320-cycle free-chain image. This module proves image validity; the execution and
refinement certificate is a separate obligation.

The view holds the nonce and then the 888-byte root region from 0x400040. Chain 0 is the free
chain and chains 1 to 12 are the index caps: a cap takes answer bytes `[0,24)` as its 192-bit
state and hashes in place, so its top is its value when its count is 0. Chains 13 to 32 are normal
chains with their 144-bit value eight bytes into a 32-byte answer buffer. Chain 32, which hashes
last, has its value at region byte 0 and its buffer eight bytes lower, in the nonce's high word:
after its last hash `x10` already points at the root input. The free chain is at region byte 24
and cap `k` at `24 + 56 k`; normal `13 + j` has its buffer at region byte `48 + 56 j` below cap
`j + 1` for `j < 12`, and at `720 + 24 (j - 12)` after. The free chain runs first, then the caps,
then the normals.

The free chain's count `c` is the view byte `v` at 0x400070, a dead byte of normal 13's buffer:
`v & 0xFC = 4 c`. The checksum subtracts `4 c` from the address sum, so its residue is the HASH call
number exactly when the digit sum plus `c` is 145 modulo 255. The free dispatch lands `c` cells
before pair 0's prologue; cells for `c ≥ 16` jump to a rejection stub. -/

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix wordReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

/-- The answer buffer of chain `k`, and for a cap also its value and state. -/
def outAddr (k : ℕ) : ℕ :=
  if k = 32 then 0x400038 else 0x400058 +
    if k ≤ 12 then 56 * k else if k < 25 then 56 * (k - 13) + 24 else 696 + 24 * (k - 25)
/-- View byte offset of chain `k`'s value, after the 16-byte nonce. -/
def wireByte (k : ℕ) : ℕ :=
  if k = 32 then 0 else 24 +
    if k ≤ 12 then 56 * k else if k < 25 then 56 * (k - 13) + 32 else 704 + 24 * (k - 25)
/-- The input address while chain `k` hashes: its value in the view, then its state. -/
def work (k : ℕ) : ℕ := 0x400040 + wireByte k
/-- The length of the honest view. -/
def honestViewBits : ℕ := 7248
/-- The view byte that carries the free chain's count. -/
def freeByte : ℕ := 0x400070
/-- The constant in `x1`: the free dispatch base and, less 960, the root length. -/
def freeBase : ℕ := 6144
def fineWidth (_q : ℕ) : ℕ := 4
def copies (_q : ℕ) : ℕ := 16
/-- Corresponding pairs of all four words share one base. Adjacent groups interleave
their boundary rows; the final row has fifteen fewer hashes in each body. -/
def group (q : ℕ) : ℕ := q % 4
def withinGroup (q : ℕ) : ℕ := q / 4
def groupOffset (g : ℕ) : ℕ := 3840*g
def slotOffset (q : ℕ) : ℕ :=
  ([[0,63,126,190], [25,87,152,213], [48,112,175,236], [72,136,198,259]].getD
    (group q) []).getD (withinGroup q) 0
/-- The code index of the first copy: after the index phase, the free dispatch, the free row and
pair 0's prologue. -/
def copiesIndex : ℕ := 105
def copiesStart : ℕ := 4096 + 4 * copiesIndex
def copyStart (q d : ℕ) : ℕ :=
  copiesStart + 4 * (groupOffset (group q) + 256 * (copies q - 1 - d) + slotOffset q)
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 4 * (2 ^ fineWidth q - 1)
/-- Lane 0 carries the checksum adjustment: the address sum less `4 c` has residue 1 modulo 255
exactly when the digit sum plus `c` is 145 modulo 255. -/
def baseLane (q : ℕ) : ℕ := min (landing0 (q % 4)) 65532 + if q % 4 = 0 then 49 else 0
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
/-- A cap pair's first chain hashes once per digit unit, one hash fewer than a normal chain, so
its landing is one row later. -/
def lead (q : ℕ) : ℕ := if q < 6 then 1 else 0
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) + 4 * lead q - baseLane q
def baseReg (_g : ℕ) : Reg := .x3

/-- The four index words, the lane mask, the checksum modulus, the dispatch base and the free
base. -/
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16, .LD .x23 .x12 24,
   .LD .x25 .x12 32, .LD .x2 .x12 40, .LD .x3 .x12 48, .LD .x1 .x12 56]
/-- The free chain's count, four times over: `x6 = v & 0xFC`. -/
def freeCount : Code :=
  [.LBU .x6 .x10 (imm12 ((freeByte : ℤ) - hashBase)), .ANDI .x6 .x6 (imm12 0xFC)]
def maskReg (_g : ℕ) : Reg := .x25
def laneWord (g : ℕ) : Code :=
  let dst := if g = 0 then Reg.x27 else Reg.x26
  [.AND dst (wordReg g) (maskReg g), .SUB dst (baseReg g) dst] ++
    (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
    [.SD .x10 dst (imm12 ((laneWordAddr g : ℤ) - hashBase))]
def freeSum : Code := [.SUB .x27 .x27 .x6]
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
def freeLanding : ℕ := 4096 + 4 * 101
/-- The free chain's pointers, then the jump `c` cells before pair 0's prologue. -/
def freeDispatch : Code :=
  enter 0 hashBase ++ [.SUB .x28 .x1 .x6, .JALR .x0 .x28 (imm12 ((freeLanding : ℤ) - freeBase))]
/-- The table-row register `x28` changes only while `x12` points at neither chain of the pair. -/
def prologue (q : ℕ) : Code :=
  (if q = 6 then [.ADDI .x11 .x0 144] else []) ++
    [.ADDI .x12 .x10 (imm12 ((outAddr (2*q+1) : ℤ) - work (2*q))),
     .LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q+1))),
     .ADDI .x10 .x12 (imm12 ((work (2*q+1) : ℤ) - outAddr (2*q+1))),
     .JALR .x0 .x28 (imm12 (jumpImm q))]
/-- The last chain's state is the root input's first slot, so `x10` needs no move. The root length
is the free base less 960. -/
def root : Code := [.ADDI .x11 .x1 (imm12 (7104 - (freeBase : ℤ))), .ECALL]
def pairCap (_q : ℕ) : ℕ := 24
/-- Rejection fragments occupy previously unreachable padding, in discovery order. -/
def rejectStubs : List ℕ := [655,4518,8382,12247,716,4581,8447,12310]
def stubFor (ip : ℕ) : ℕ :=
  (rejectStubs.find? fun (s : ℕ) => decide (-4096 ≤ 4*((s : ℤ)-ip) ∧ 4*((s : ℤ)-ip) < 4096)).getD 655
def rejectJump (ip : ℕ) : Instr :=
  .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((stubFor ip : ℤ)-ip)))
/-- The free cell `c` instructions before pair 0's prologue: a hash of the free chain, or for
`c ≥ 16` a jump to a rejection stub. -/
def freeCell (c : ℕ) : Instr := if c < 16 then .ECALL else rejectJump (101 - c)
def freeRow : Code := (List.range 63).map fun p => freeCell (63 - p)
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
  (List.range 15).flatMap (rowKeys 0) ++
  (List.range 3).flatMap (fun g =>
    (List.range 4).flatMap (fun j => [(g+4*j, 0), (g+1+4*j, 15)]) ++
    (List.range 14).flatMap (fun c => rowKeys (g+1) (c+1))) ++ rowKeys 3 15
def copyFragments : List (ℕ × Code) :=
  fragmentKeys.map fun (q, d) =>
    (groupOffset (group q) + 256 * (15-d) + slotOffset q, copyCode q d)
def insertFragment (a : ℕ × Code) : List (ℕ × Code) → List (ℕ × Code)
  | [] => [a]
  | b :: rest => if a.1 ≤ b.1 then a :: b :: rest else b :: insertFragment a rest
def addStubs : List ℕ → List (ℕ × Code)
  | [] => copyFragments
  | ip :: rest => insertFragment (ip-copiesIndex,reject) (addStubs rest)
def fragments : List (ℕ × Code) := addStubs rejectStubs
def assemble (cursor : ℕ) : List (ℕ × Code) → Code
  | [] => []
  | (off, body) :: rest =>
    List.replicate (off-cursor) nop ++ body ++ assemble (off+body.length) rest
def tables : Code := assemble 0 fragments
def verifier : Code := indexPhase ++ freeDispatch ++ freeRow ++ prologue 0 ++ tables

/-- The 32-byte index answer buffer, then the words loaded after the index query. -/
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes (broadcast 0x3c3c) ++ wordBytes 255 ++ wordBytes (baseWord 0) ++
    wordBytes freeBase
def image : Riscv.Image := ⟨verifier, dataImage⟩

theorem index_length : indexPhase.length = 34 := by decide +kernel
theorem code_length : verifier.length = 15751 := by decide +kernel
theorem data_length : dataImage.length = 64 := by decide +kernel
theorem admitted : verifier.all Riscv.admittedInstruction = true := by decide +kernel
theorem image_valid : image.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · change verifier.length ≤ 262144
    rw [code_length]; norm_num
  · change dataImage.length ≤ 1048576
    rw [data_length]; norm_num
  · exact List.all_eq_true.mp admitted

theorem image_size : image.byteSize < 1048576 := by
  change 4 * verifier.length + dataImage.length < 1048576
  rw [code_length, data_length]
  norm_num

end OptimalOTS.RiscvMixedProgram
