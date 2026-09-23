import Submissions.UpperRiscv.Program

/-! The 360-cycle mixed-width candidate image. This module proves image validity;
the complete execution/refinement certificate is a separate obligation.

Chains 7, 11, 15 and 19 are hashed in place: each wire value starts five bytes into its own cell,
inside the chain's 32-byte answer buffer at byte 13, so the chain has no expansion hash and no
redirect, and while it hashes `x10` points at its wire value (`work k = wireSlot k`). -/

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix lengthCheck wordReg baseReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

/-- Working cell of chain `k`: 24-byte cells from 0x3FFFE0, in execution order. -/
def slot (k : ℕ) : ℕ := 0x3FFFE0 + 24 * k
/-- Byte offset of chain `k`'s value in the wire payload: four 96-byte blocks holding
chains `4b+4, b, 4b+5, 4b+6, 4b+7`, then chains 20–31 in place. -/
def wireByte (k : ℕ) : ℕ :=
  if k < 4 then 96 * k + 19
  else if k < 20 then 96 * ((k - 4) / 4) +
    (if (k - 4) % 4 = 0 then 0 else if (k - 4) % 4 = 1 then 39
      else if (k - 4) % 4 = 2 then 58 else 77)
  else 384 + 24 * (k - 20)
def wireSlot (k : ℕ) : ℕ := 0x400040 + wireByte k
/-- Chains whose wire value is not already in its cell and need an expansion step. -/
def narrow (k : ℕ) : Bool := decide (wireSlot k ≠ slot k)

theorem wireSlot_eq_slot_of_not_narrow {k : ℕ} (hn : ¬ narrow k = true) : wireSlot k = slot k := by
  unfold narrow at hn; simpa using hn

theorem wireSlot_ne_slot_of_narrow {k : ℕ} (hn : narrow k = true) : wireSlot k ≠ slot k := by
  unfold narrow at hn; simpa using hn
/-- Chains whose first hash moves the wire value into the cell, followed by the redirect. A value
at its cell (byte 8 of the answer buffer) or five bytes above it (byte 13) is hashed in place. -/
def expands (k : ℕ) : Bool := decide (wireSlot k ≠ slot k ∧ wireSlot k ≠ slot k + 5)
/-- The input address while the chain hashes. -/
def work (k : ℕ) : ℕ := if expands k then slot k else wireSlot k
def outAddr (k : ℕ) : ℕ := slot k - 8
def fineWidth (_q : ℕ) : ℕ := 4
def copies (_q : ℕ) : ℕ := 16
/-- Row group of each pair: `[12,1,8] / [13,9,4] / [14,10,6] / [11,0,15] / [3,5,2] / [7]`. -/
def group (q : ℕ) : ℕ := [3,0,4,4,1,4,2,5,0,1,2,3,0,1,2,3].getD q 0
def withinGroup (q : ℕ) : ℕ := [1,1,2,0,2,1,2,0,2,1,1,0,0,0,0,2].getD q 0
def copyCapacity (q : ℕ) : ℕ := if q = 7 then 128 else if withinGroup q = 2 then 48 else 40
def groupOffset (g : ℕ) : ℕ := 2048*g
def copiesStart : ℕ := 4096 + 4 * 52
def copyStart (q d : ℕ) : ℕ :=
  copiesStart + 4 * (groupOffset (group q) + 128 * (copies q - 1 - d) + 40 * withinGroup q)
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 4 * (2 ^ fineWidth q - 1)
def baseLane (q : ℕ) : ℕ := min (landing0 (if q < 12 then q else q - 4)) 65532
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) - baseLane q

def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16, .LD .x23 .x12 24,
   .LD .x25 .x12 40, .LD .x1 .x12 48, .LD .x2 .x12 56,
   .LD .x3 .x12 80, .LD .x4 .x12 88, .LD .x7 .x12 96]
def maskReg (_g : ℕ) : Reg := .x25
def laneWord (g : ℕ) : Code :=
  let dst := if g = 0 then Reg.x27 else Reg.x26
  [.AND dst (wordReg g) (maskReg g)] ++ (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
    [.SUB .x26 (baseReg g) dst, .SD .x10 .x26 (imm12 ((laneWordAddr g : ℤ) - hashBase))]
def fold : Code :=
  [.SRLI .x26 .x27 7, .ADD .x27 .x27 .x26, .AND .x27 .x27 .x1]
def sumCheck : Code := [.REMU .x27 .x27 .x2, .XORI .x27 .x27 628, .BEQ .x27 .x0 16] ++ reject
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ lengthCheck ++ loadWords ++
    (List.range 4).flatMap laneWord ++ fold ++ sumCheck ++ [.ADDI .x11 .x0 160]

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((wireSlot k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - wireSlot k))] ++
    if expands k then [.ECALL, .ADDI .x10 .x12 8] else []
def prologue (q : ℕ) : Code :=
  (if q = 2 then [.ADDI .x11 .x0 152] else if q = 10 then [.ADDI .x11 .x0 192] else []) ++
    enter (2*q) (if q = 0 then hashBase else work (2*q-1)) ++
    [.LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q))),
     .JALR .x0 .x28 (imm12 (jumpImm q))]
def root : Code :=
  [.ADDI .x10 .x10 (imm12 ((0x3FFFD8 : ℤ) - slot 31)), .ADDI .x11 .x13 640, .ECALL]
def copyBody (q d : ℕ) : Code :=
  List.replicate (2 ^ fineWidth q - if expands (2*q) then 1 else 0) .ECALL ++
    enter (2*q+1) (work (2*q)) ++
    List.replicate (d+1 - if expands (2*q+1) then 1 else 0) .ECALL ++
    (if q = 15 then root ++ decision else prologue (q+1))
def copyCode (q d : ℕ) : Code :=
  copyBody q d ++ List.replicate (copyCapacity q - (copyBody q d).length) nop
def groupPairs (g : ℕ) : List ℕ :=
  if g = 0 then [12,1,8] else if g = 1 then [13,9,4] else if g = 2 then [14,10,6] else
    if g = 3 then [11,0,15] else if g = 4 then [3,5,2] else [7]
def groupCode (g : ℕ) : Code :=
  (List.range 16).flatMap fun c =>
    (groupPairs g).flatMap fun q => copyCode q (copies q - 1 - c)
def verifier : Code := indexPhase ++ prologue 0 ++ (List.range 6).flatMap groupCode

def firstMask : ℕ := broadcast 0x1e3c
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes firstMask ++ wordBytes (broadcast 0x1e3c) ++
    wordBytes (broadcast 0x1fc) ++ wordBytes 65535 ++ wordBytes 0 ++ wordBytes 5504 ++
    wordBytes (baseWord 0) ++ wordBytes (baseWord 1) ++ wordBytes (baseWord 2)
def image : Riscv.Image := ⟨verifier, dataImage⟩

theorem index_length : indexPhase.length = 46 := by decide +kernel
theorem code_length : verifier.length = 12340 := by decide +kernel
theorem data_length : dataImage.length = 104 := by decide +kernel
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
