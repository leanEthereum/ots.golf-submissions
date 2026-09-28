import Submissions.UpperRiscv.Program

/-! The 341-cycle image: a free first chain whose hash count is the index checksum remainder,
then sixteen dispatched pairs, whose final chain is a cap (no extra hash), and the root.

Chains are numbered by execution position `k < 33`. Chain `k` reads its signature value at
`valueAddr k`, writes every answer at `outAddr k`, and after its first hash reads its state
`truncBytes k` bytes into its answer (`work k`). An expanding chain's first hash moves its value into
its answer buffer; every other chain's value already lies at `work k`. This module proves image
validity; the execution certificate is separate. -/

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix wordReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop)

/-- The payload (signature bits from 128) and root region start at the same address. -/
def payloadAddr : ℕ := 0x400040
def regionAddr : ℕ := 0x400040

def valueOffs : List ℕ :=
  [612, 594, 324, 540, 522, 648, 630, 468, 576, 558, 396, 504, 486, 450, 432, 414, 378, 360, 342, 306, 288, 264, 240, 216, 192, 168, 144, 120, 96, 72, 48, 24, 0]
def outOffs : List ℕ :=
  [776, 752, 728, 704, 680, 656, 632, 608, 584, 560, 536, 512, 488, 464, 440, 416, 392, 368, 344, 320, 296, 272, 248, 224, 200, 176, 152, 128, 104, 80, 56, 32, 0]
def truncs : List ℕ :=
  [0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]

/-- Signature value of chain `k`. -/
def valueAddr (k : ℕ) : ℕ := payloadAddr + valueOffs.getD k 0
/-- Answer buffer of chain `k` (8-byte aligned). -/
def outAddr (k : ℕ) : ℕ := regionAddr - 8 + outOffs.getD k 0
def truncBytes (k : ℕ) : ℕ := truncs.getD k 0
/-- The input address while the chain hashes. -/
def work (k : ℕ) : ℕ := outAddr k + truncBytes k
/-- State bytes: chains 21 to 32 are 192-bit, the others 144-bit. -/
def chainBytes (k : ℕ) : ℕ := if 21 ≤ k then 24 else 18
/-- Chains whose first hash moves the value into the answer buffer. -/
def expands (k : ℕ) : Bool := k ∈ [0, 1, 2, 3, 4, 7, 10, 13, 16, 19]
/-- Caps: the hash count is the digit itself. -/
def capChain (k : ℕ) : Bool := k = 32
/-- Chains whose table row has fifteen hash steps: a cap, or an expanding chain whose first
hash precedes the landing. -/
def shortRow (k : ℕ) : Bool := expands k || capChain k

def pairCap (q : ℕ) : ℕ := if q < 5 then 20 else if q < 10 then 21 else 30

/-! ## Code layout -/

def indexStub : ℕ := 37
def freeTableAt : ℕ := 44
def prologue0At : ℕ := 299
def copiesAt : ℕ := 305
/-- Column of pair `q`: its `d = 15` body; body `d` lies `256 * (15 - d)` instructions later. -/
def place (q : ℕ) : ℕ :=
  [0, 3610, 7321, 11072, 64, 3711, 7361, 11109, 170, 3673, 7681, 11403, 210, 4073, 7719, 11441].getD q 0
def bodyAt (q d : ℕ) : ℕ := copiesAt + place q + 256*(15-d)
def copyStart (q d : ℕ) : ℕ := 4096 + 4*bodyAt q d
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 60
/-- The shared base of lane `j` of every word; lane 0 is offset so that the sum check
residue is zero exactly at `S + v = 146 (mod 255)`. -/
def baseLane (q : ℕ) : ℕ := landing0 (q % 4) + if q % 4 = 0 then 232 else 0
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) - baseLane q
def baseReg (_g : ℕ) : Reg := .x3
def laneAddr (q : ℕ) : ℕ := laneBase + 2*q

/-- The dispatch base of the free chain's table and the length bound of the decision. -/
def boundWord : ℕ := 5457
def freeImm : ℤ := (4096 + 4*prologue0At : ℤ) - boundWord

/-! ## The index phase -/

/-- The bound `5457` in `x1`. -/
def countLoad : Code := [.LD .x1 .x12 (BitVec.ofNat 12 72)]
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16, .LD .x23 .x12 24,
   .LD .x25 .x12 40, .LD .x2 .x12 56,
   .LD .x3 .x12 80]
def maskReg (_g : ℕ) : Reg := .x25
def laneWord (g : ℕ) : Code :=
  let dst := if g = 0 then Reg.x27 else Reg.x26
  [.AND dst (wordReg g) (maskReg g), .SUB dst (baseReg g) dst] ++
    (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
    [.SD .x10 dst (imm12 ((laneWordAddr g : ℤ) - hashBase))]
/-- `x29 = 4 * ((146 - S) mod 255)`: the scaled free digit, from the lane sum alone. -/
def sumCheck : Code := [.REMU .x29 .x27 .x2]
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ countLoad ++ loadWords ++
    (List.range 4).flatMap laneWord ++ sumCheck ++ [.ADDI .x11 .x0 144]

/-! ## Chains -/

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((valueAddr k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - valueAddr k))] ++
    if expands k then [.ECALL, .ADDI .x10 .x12 (imm12 (truncBytes k))] else []
def widthChange (k previous : ℕ) : Code :=
  if chainBytes k = chainBytes previous then [] else [.ADDI .x11 .x0 (imm12 (8 * chainBytes k))]

/-- The free chain's first hash, then the jump to `v` hash steps before prologue 0. -/
def freePrologue : Code :=
  enter 0 hashBase ++ [.SUB .x28 .x1 .x29, .JALR .x0 .x28 (imm12 freeImm)]
/-- The rejection of a free digit of 16 or more, then padding up to the table. -/
def freePad : Code := reject ++ List.replicate 4 nop
/-- Entry `i` serves the free digit `v = 255 - i`: a hash step for `v < 16`, else a branch to
the rejection after the free jump. -/
def freeEntry (i : ℕ) : Instr :=
  if 255 - i < 16 then .ECALL
  else .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((indexStub : ℤ) - (freeTableAt + i))))
def freeTable : Code := (List.range 255).map freeEntry

def prologue (q : ℕ) : Code :=
  widthChange (2*q+1) (2*q) ++ enter (2*q+1) (work (2*q)) ++
    [.LHU .x28 .x12 (imm12 ((laneAddr q : ℤ) - outAddr (2*q+1))),
     .JALR .x0 .x28 (imm12 (jumpImm q))]
/-- The root reads the first `a3 + 944` bits of the region: 6400 bits for a full signature. -/
def root : Code :=
  [.ADDI .x11 .x13 944, .ECALL]
/-- Accept exactly when both root words match the public key and `a3 < 5457`. -/
def decision : Code :=
  [.LD .x26 .x12 0, .BNE .x26 .x30 24, .LD .x28 .x12 8, .BNE .x28 .x31 16,
   .SLTU .x10 .x13 .x1, .ADDI .x5 .x0 0, .ECALL] ++ reject

/-- Rejection fragments in padding, each within branch range of the rows it serves. -/
def rejectStubs : List ℕ := [408, 1535, 2555, 4056, 4983, 6007, 7703, 8723, 9743, 11453, 12434, 13458]
def stubFor (ip : ℕ) : ℕ :=
  (rejectStubs.find? fun (s : ℕ) => decide (-4096 ≤ 4*((s : ℤ)-ip) ∧ 4*((s : ℤ)-ip) < 4096)).getD 456
def rowInstr (q d i : ℕ) : Instr :=
  if 15-i+d ≤ pairCap q then .ECALL
  else let ip := bodyAt q d + i
    .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((stubFor ip : ℤ)-ip)))
def hashRow (q d : ℕ) : Code :=
  (List.range (16 - if shortRow (2*q+1) then 1 else 0)).map (rowInstr q d)
def copyCode (q d : ℕ) : Code :=
  hashRow q d ++ widthChange (2*q+2) (2*q+1) ++
    enter (2*q+2) (work (2*q+1)) ++
    List.replicate (d+1 - if shortRow (2*q+2) then 1 else 0) .ECALL ++
    (if q = 15 then root ++ decision else prologue (q+1))

def insertFragment (a : ℕ × Code) : List (ℕ × Code) → List (ℕ × Code)
  | [] => [a]
  | b :: rest => if a.1 ≤ b.1 then a :: b :: rest else b :: insertFragment a rest
def fragmentKeys : List (ℕ × ℕ) :=
  (List.range 16).flatMap fun q => (List.range 16).map fun d => (q, d)
def copyFragments : List (ℕ × Code) :=
  fragmentKeys.map fun (q, d) => (bodyAt q d, copyCode q d)
/-- Every body and stub, sorted by position. -/
def fragments : List (ℕ × Code) :=
  (copyFragments ++ rejectStubs.map fun ip => (ip, reject)).foldr insertFragment []
def assemble (cursor : ℕ) : List (ℕ × Code) → Code
  | [] => []
  | (off, body) :: rest =>
    List.replicate (off-cursor) nop ++ body ++ assemble (off+body.length) rest
def tables : Code := assemble copiesAt fragments
def verifier : Code := indexPhase ++ freePrologue ++ freePad ++ freeTable ++ prologue 0 ++ tables

def firstMask : ℕ := broadcast 0x3c3c
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes firstMask ++ wordBytes (broadcast 0x3c3c) ++
    wordBytes (broadcast 0x1fc) ++ wordBytes 1020 ++ wordBytes 0 ++ wordBytes boundWord ++
    wordBytes (baseWord 0)
def image : Riscv.Image := ⟨verifier, dataImage⟩

theorem index_length : indexPhase.length = 31 := by decide +kernel
theorem head_length :
    (indexPhase ++ freePrologue ++ freePad ++ freeTable ++ prologue 0).length = copiesAt := by
  decide +kernel
theorem code_length : verifier.length = 15616 := by decide +kernel
theorem data_length : dataImage.length = 88 := by decide +kernel
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
