import Submissions.UpperRiscvHint.Program

/-! The 324-cycle cap-chain image. This module proves image validity; the execution and
refinement certificate is a separate obligation.

The view holds the nonce and then the 888-byte root region from 0x400040. Chains 0 to 15 are the
caps: cap `j` takes answer bytes `[0,24)` as its 192-bit state and hashes in place at region byte
`56 j`, so its top is its value when its digit is 0. Chain `16 + j` is a normal chain: its 32-byte
answer buffer is at region byte `56 j + 24`, and its 144-bit value and state are eight bytes into
it. The caps run first, then the normals. -/

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix wordReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

/-- The answer buffer of chain `k`, and for a cap also its value and state. -/
def outAddr (k : ℕ) : ℕ := 0x400040 + if k < 16 then 56 * k else 56 * (k - 16) + 24
/-- View byte offset of chain `k`'s value, after the 16-byte nonce. -/
def wireByte (k : ℕ) : ℕ := if k < 16 then 56 * k else 56 * (k - 16) + 32
/-- The input address while chain `k` hashes: its value in the view, then its state. -/
def work (k : ℕ) : ℕ := 0x400040 + wireByte k
/-- The length of the honest view; pair 0 rejects every other length. -/
def honestViewBits : ℕ := 7248
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
def copiesStart : ℕ := 4096 + 4 * 50
def copyStart (q d : ℕ) : ℕ :=
  copiesStart + 4 * (groupOffset (group q) + 256 * (copies q - 1 - d) + slotOffset q)
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 4 * (2 ^ fineWidth q - 1)
/-- Lane 0 carries the checksum adjustment: the accepted address sum has residue 1 modulo 255. -/
def baseLane (q : ℕ) : ℕ := min (landing0 (q % 4)) 65532 + if q % 4 = 0 then 1997 else 0
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
/-- A cap pair's first chain hashes once per digit unit, one hash fewer than a normal chain, so
its landing is one row later. -/
def lead (q : ℕ) : ℕ := if q < 8 then 1 else 0
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) + 4 * lead q - baseLane q
def baseReg (_g : ℕ) : Reg := .x3

/-- The four index words, the lane mask, the checksum modulus, the dispatch base and the honest
view length. -/
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16, .LD .x23 .x12 24,
   .LD .x25 .x12 32, .LD .x2 .x12 40, .LD .x3 .x12 48, .LD .x6 .x12 56]
def maskReg (_g : ℕ) : Reg := .x25
def laneWord (g : ℕ) : Code :=
  let dst := if g = 0 then Reg.x27 else Reg.x26
  [.AND dst (wordReg g) (maskReg g), .SUB dst (baseReg g) dst] ++
    (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
    [.SD .x10 dst (imm12 ((laneWordAddr g : ℤ) - hashBase))]
def fold : Code :=
  [.SRLI .x26 .x27 8, .ADD .x27 .x27 .x26, .AND .x27 .x27 .x1]
/-- The residue lands in `x5`: 1, the HASH call number, exactly on the two checksum ranks.
Any other residue traps at the first chain hash. -/
def sumCheck : Code := [.REMU .x5 .x27 .x2]
/-- The caps hash first: the chain width is 192 bits until pair 8. -/
def chainSetup : Code := [.ADDI .x11 .x0 192]
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ loadWords ++
    (List.range 4).flatMap laneWord ++ sumCheck ++ chainSetup

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((work k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - work k))]
/-- The table-row register `x28` changes only while `x12` points at neither chain of the pair.
Pair 0 also rejects every view whose length differs from the honest one: `BNE` from code index
33 to the rejection stub at 600. -/
def prologue (q : ℕ) : Code :=
  (if q = 8 then [.ADDI .x11 .x0 144] else []) ++
    [.ADDI .x12 .x10 (imm12 ((outAddr (2*q) : ℤ) - if q = 0 then hashBase else work (2*q-1))),
     .LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q)))] ++
    (if q = 0 then [.BNE .x13 .x6 (BitVec.ofNat 13 (4 * (600 - 33)))] else []) ++
    [.ADDI .x10 .x12 (imm12 ((work (2*q) : ℤ) - outAddr (2*q))),
     .JALR .x0 .x28 (imm12 (jumpImm q))]
/-- The root length is the honest view length less 144, which the raw-form test fixed. -/
def root : Code :=
  [.ADDI .x10 .x10 (imm12 ((outAddr 0 : ℤ) - work 31)), .ADDI .x11 .x13 (imm12 (-144)), .ECALL]
def pairCap (q : ℕ) : ℕ := if q < 8 then 23 else if q < 10 then 24 else 30
/-- Rejection fragments occupy previously unreachable padding, in discovery order. -/
def rejectStubs : List ℕ := [600,4463,8327,12192,661,4526,8392,12255]
def stubFor (ip : ℕ) : ℕ :=
  (rejectStubs.find? fun (s : ℕ) => decide (-4096 ≤ 4*((s : ℤ)-ip) ∧ 4*((s : ℤ)-ip) < 4096)).getD 600
/-- Landing at row `i` hashes the first chain `16 - i` times, that is for digit
`15 - i + lead q`. A cap row's entry 0 would need digit 16 and is never a landing. -/
def rowInstr (q d i : ℕ) : Instr :=
  if i < lead q ∨ 15-i+lead q+d ≤ pairCap q then .ECALL
  else let ip := 50 + groupOffset (group q) + 256*(15-d) + slotOffset q + i
    .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((stubFor ip : ℤ)-ip)))
def hashRow (q d : ℕ) : Code := (List.range (2 ^ fineWidth q)).map (rowInstr q d)
def copyCode (q d : ℕ) : Code :=
  hashRow q d ++ enter (2*q+1) (work (2*q)) ++ List.replicate (d+1-lead q) .ECALL ++
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
  | ip :: rest => insertFragment (ip-50,reject) (addStubs rest)
def fragments : List (ℕ × Code) := addStubs rejectStubs
def assemble (cursor : ℕ) : List (ℕ × Code) → Code
  | [] => []
  | (off, body) :: rest =>
    List.replicate (off-cursor) nop ++ body ++ assemble (off+body.length) rest
def tables : Code := assemble 0 fragments
def verifier : Code := indexPhase ++ prologue 0 ++ List.replicate 14 nop ++ tables

/-- The 32-byte index answer buffer, then the words loaded after the index query. -/
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes (broadcast 0x3c3c) ++ wordBytes 255 ++ wordBytes (baseWord 0) ++
    wordBytes honestViewBits
def image : Riscv.Image := ⟨verifier, dataImage⟩

theorem index_length : indexPhase.length = 31 := by decide +kernel
theorem code_length : verifier.length = 15697 := by decide +kernel
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
