import Submissions.UpperRiscv.Program

/-! The 349-cycle mixed-width candidate image. This module proves image validity;
the complete execution/refinement certificate is a separate obligation.

Chains 6, 9, 12 and 15 are hashed in place: each wire value starts six bytes into its own cell,
inside the chain's 32-byte answer buffer at byte 14, so the chain has no expansion hash and no
redirect, and while it hashes `x10` points at its wire value (`work k = wireSlot k`). -/

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix lengthCheck wordReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

/-- Working cell of chain `k`: 24-byte cells from 0x3FFFE0, in execution order. -/
def slot (k : ℕ) : ℕ := 0x3FFFE0 + 24 * k
/-- Wire byte offsets: sixteen permuted 18-byte states, then sixteen 24-byte states. -/
def wireByte (k : ℕ) : ℕ :=
  if k < 16 then
    [18,36,90,108,0,162,54,72,180,126,144,234,198,216,252,270].getD k 0
  else 288 + 24 * (k - 16)
def wireSlot (k : ℕ) : ℕ := 0x400040 + wireByte k
/-- Chains whose wire value is not already in its cell and need an expansion step. -/
def narrow (k : ℕ) : Bool := decide (wireSlot k ≠ slot k)

theorem wireSlot_eq_slot_of_not_narrow {k : ℕ} (hn : ¬ narrow k = true) : wireSlot k = slot k := by
  unfold narrow at hn; simpa using hn

theorem wireSlot_ne_slot_of_narrow {k : ℕ} (hn : narrow k = true) : wireSlot k ≠ slot k := by
  unfold narrow at hn; simpa using hn
/-- Chains whose first hash moves the wire value into the cell, followed by the redirect. A value
at its cell (byte 8 of the answer buffer) or six bytes above it (byte 14) is hashed in place. -/
def expands (k : ℕ) : Bool := decide (wireSlot k ≠ slot k ∧ wireSlot k ≠ slot k + 6)
/-- The input address while the chain hashes. -/
def work (k : ℕ) : ℕ := if expands k then slot k else wireSlot k
def outAddr (k : ℕ) : ℕ := slot k - 8
def fineWidth (_q : ℕ) : ℕ := 4
def copies (_q : ℕ) : ℕ := 16
/-- Corresponding pairs of all four words share one base. Adjacent groups interleave
their boundary rows; the final row has fifteen fewer hashes in each body. -/
def group (q : ℕ) : ℕ := q % 4
def withinGroup (q : ℕ) : ℕ := q / 4
def groupOffset (g : ℕ) : ℕ := 3840*g
def slotOffset (q : ℕ) : ℕ :=
  ([[0,63,126,190], [25,87,152,213], [48,112,175,236], [72,137,198,259]].getD
    (group q) []).getD (withinGroup q) 0
def copiesStart : ℕ := 4096 + 4 * 50
def copyStart (q d : ℕ) : ℕ :=
  copiesStart + 4 * (groupOffset (group q) + 256 * (copies q - 1 - d) + slotOffset q)
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 4 * (2 ^ fineWidth q - 1)
def baseLane (q : ℕ) : ℕ := min (landing0 (q % 4)) 65532 + if q % 4 = 0 then 148 else 0
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) - baseLane q
def baseReg (_g : ℕ) : Reg := .x3

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
def fold : Code :=
  [.SRLI .x26 .x27 8, .ADD .x27 .x27 .x26, .AND .x27 .x27 .x1]
def sumCheck : Code := [.REMU .x27 .x27 .x2, .BEQ .x27 .x0 16] ++ reject
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ lengthCheck ++ loadWords ++
    (List.range 4).flatMap laneWord ++ sumCheck ++ [.ADDI .x11 .x0 144]

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((wireSlot k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - wireSlot k))] ++
    if expands k then [.ECALL, .ADDI .x10 .x12 8] else []
def prologue (q : ℕ) : Code :=
  (if q = 8 then [.ADDI .x11 .x0 192] else []) ++
    enter (2*q) (if q = 0 then hashBase else work (2*q-1)) ++
    [.LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q))),
     .JALR .x0 .x28 (imm12 (jumpImm q))]
def root : Code :=
  [.ADDI .x10 .x10 (imm12 ((0x3FFFD8 : ℤ) - slot 31)), .ADDI .x11 .x13 640, .ECALL]
def pairCap (q : ℕ) : ℕ := if q < 8 then 23 else if q < 10 then 24 else 30
/-- Rejection fragments occupy previously unreachable padding, in discovery order. -/
def rejectStubs : List ℕ := [600,4463,8327,12192,660,4526,8392,12255]
def stubFor (ip : ℕ) : ℕ :=
  (rejectStubs.find? fun (s : ℕ) => decide (-4096 ≤ 4*((s : ℤ)-ip) ∧ 4*((s : ℤ)-ip) < 4096)).getD 600
def rowInstr (q d i : ℕ) : Instr :=
  if 15-i+d ≤ pairCap q then .ECALL
  else let ip := 50 + groupOffset (group q) + 256*(15-d) + slotOffset q + i
    .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((stubFor ip : ℤ)-ip)))
def hashRow (q d : ℕ) : Code :=
  (List.range (2 ^ fineWidth q - if expands (2*q) then 1 else 0)).map (rowInstr q d)
def copyBody (q d : ℕ) : Code :=
  hashRow q d ++
    enter (2*q+1) (work (2*q)) ++
    List.replicate (d+1 - if expands (2*q+1) then 1 else 0) .ECALL ++
    (if q = 15 then root ++ decision else prologue (q+1))
def copyCode (q d : ℕ) : Code :=
  copyBody q d ++ []
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
def verifier : Code := indexPhase ++ prologue 0 ++ List.replicate 5 nop ++ tables

def firstMask : ℕ := broadcast 0x3c3c
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes firstMask ++ wordBytes (broadcast 0x3c3c) ++
    wordBytes (broadcast 0x1fc) ++ wordBytes 255 ++ wordBytes 0 ++ wordBytes 5504 ++
    wordBytes (baseWord 0)
def image : Riscv.Image := ⟨verifier, dataImage⟩

theorem index_length : indexPhase.length = 39 := by decide +kernel
theorem code_length : verifier.length = 15701 := by decide +kernel
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
