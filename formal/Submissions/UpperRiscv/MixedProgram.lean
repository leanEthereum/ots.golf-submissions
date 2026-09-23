import Submissions.UpperRiscv.Program
import Submissions.UpperRiscv.Payload

/-! The 362-cycle in-place candidate image. This module proves image validity;
the complete execution/refinement certificate is a separate obligation.

Chains are numbered in execution order. Chains 0–12 are narrow chains whose first hash
*expands* the 20-byte wire value into a separate 32-byte output block, followed by the redirect
`ADDI x10, x12, 8`. Chains 13–23 (narrow) and 24–31 (wide) are hashed *in place*: every hash
reads the state at its wire address (`work k = wireSlot k`) and writes its answer to an 8-byte
aligned block `outAddr k` that contains it, `j = wireSlot k - outAddr k` bytes below it. The last
chain's block starts at `0x400038`, eight bytes below the root input, so after it `x10` already
points at the root input. -/

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix lengthCheck wordReg baseReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

def narrow (k : ℕ) : Bool := decide (k < 24)
/-- The chain's first hash expands a packed narrow value and is followed by the redirect. -/
def expands (k : ℕ) : Bool := decide (k ≤ 12)
/-- Offset of chain `k`'s 32-byte output block (`x12`) from `0x400038`. -/
def outOffset (k : ℕ) : ℕ :=
  [904, 880, 856, 832, 808, 784, 760, 736, 712, 688, 664, 504, 480, 64, 128, 192,
    256, 320, 384, 448, 536, 568, 600, 632, 32, 96, 160, 224, 288, 352, 416, 0].getD k 0
def outAddr (k : ℕ) : ℕ := 0x400038 + outOffset k
/-- The disclosed value of chain `k` in the signature. -/
def wireSlot (k : ℕ) : ℕ := 0x400040 + 4 * Payload.wireUnit k
/-- The state of an expanding chain after the redirect. -/
def slot (k : ℕ) : ℕ := outAddr k + 8
/-- The input address while the chain hashes. -/
def work (k : ℕ) : ℕ := if expands k then slot k else wireSlot k
def fineWidth (_q : ℕ) : ℕ := 4
def copies (_q : ℕ) : ℕ := 16
def group (q : ℕ) : ℕ := if q < 3 then 0 else if q = 3 then 1 else
  if q < 8 then q-2 else if q < 12 then q-6 else q-10
def withinGroup (q : ℕ) : ℕ := if q < 3 then q else if q = 3 then 0 else
  if q < 8 then 1 else if q < 12 then 0 else 2
def copyCapacity (q : ℕ) : ℕ := if q = 3 then 128 else if withinGroup q = 2 then 48 else 40
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
/-- The narrow chains run first. -/
def chainSetup : Code := [.ADDI .x11 .x0 160]
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ lengthCheck ++ loadWords ++
    (List.range 4).flatMap laneWord ++ fold ++ sumCheck ++ chainSetup

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((wireSlot k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - wireSlot k))] ++
    if expands k then [.ECALL, .ADDI .x10 .x12 8] else []
def prologue (q : ℕ) : Code :=
  (if q = 12 then [.ADDI .x11 .x0 192] else []) ++
    enter (2*q) (if q = 0 then hashBase else work (2*q-1)) ++
    [.LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q))),
     .JALR .x0 .x28 (imm12 (jumpImm q))]
/-- `x10` already points at the root input after the last chain. -/
def root : Code := [.ADDI .x11 .x13 1920, .ECALL]
def copyBody (q d : ℕ) : Code :=
  List.replicate (2 ^ fineWidth q - if expands (2*q) then 1 else 0) .ECALL ++
    enter (2*q+1) (work (2*q)) ++
    List.replicate (d+1 - if expands (2*q+1) then 1 else 0) .ECALL ++
    (if q = 15 then root ++ decision else prologue (q+1))
def copyCode (q d : ℕ) : Code :=
  copyBody q d ++ List.replicate (copyCapacity q - (copyBody q d).length) nop
def groupPairs (g : ℕ) : List ℕ :=
  if g = 0 then [0,1,2] else if g = 1 then [3] else [g+6,g+2,g+10]
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
