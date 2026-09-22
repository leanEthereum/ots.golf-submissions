import Submissions.UpperRiscv.Program

/-! The 377-cycle mixed-width candidate image. This module proves image validity;
the complete execution/refinement certificate is a separate obligation. -/

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix lengthCheck loadWords wordReg baseReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

def physical (k : ℕ) : ℕ := if k < 8 then k else 39 - k
def narrow (k : ℕ) : Bool := decide (8 ≤ k)
def slot (k : ℕ) : ℕ := 0x400040 + 24 * physical k + if narrow k then 8 else 0
def wireSlot (k : ℕ) : ℕ :=
  if narrow k then 0x400100 + 20 * (physical k - 8) else slot k
def outAddr (k : ℕ) : ℕ := slot k - 8
def fineWidth (q : ℕ) : ℕ := if q < 2 then 5 else 4
def copies (q : ℕ) : ℕ := if q < 2 then 8 else 16
def group (q : ℕ) : ℕ := if q < 8 then q / 2 else 4 + q % 4
def withinGroup (q : ℕ) : ℕ := if q < 8 then q % 2 else (q - 8) / 4
def groupOffset (g : ℕ) : ℕ := if g = 0 then 0 else 1024 + 2048 * (g - 1)
def copiesStart : ℕ := 4096 + 4 * 52
def copyStart (q d : ℕ) : ℕ :=
  copiesStart + 4 * (groupOffset (group q) + 128 * (copies q - 1 - d) + 64 * withinGroup q)
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 4 * (2 ^ fineWidth q - 1)
def baseLane (q : ℕ) : ℕ := min (landing0 (if q < 12 then q else q - 4)) 65532
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) - baseLane q

def maskReg (g : ℕ) : Reg := if g = 0 then .x24 else .x25
def laneWord (g : ℕ) : Code :=
  let dst := if g = 0 then Reg.x27 else Reg.x26
  [.AND dst (wordReg g) (maskReg g)] ++ (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
    [.SUB .x26 (baseReg g) dst, .SD .x10 .x26 (imm12 ((laneWordAddr g : ℤ) - hashBase))]
def fold : Code :=
  [.SRLI .x26 .x27 7, .AND .x26 .x26 .x1, .AND .x27 .x27 .x1, .ADD .x27 .x27 .x26]
def sumCheck : Code := [.REMU .x27 .x27 .x2, .XORI .x27 .x27 640, .BEQ .x27 .x0 16] ++ reject
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ lengthCheck ++ loadWords ++
    (List.range 4).flatMap laneWord ++ fold ++ sumCheck ++ [.ADDI .x11 .x0 192]

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((wireSlot k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - wireSlot k))] ++
    if narrow k then [.ECALL, .ADDI .x10 .x12 8] else []
def prologue (q : ℕ) : Code :=
  (if q = 4 then [.ADDI .x11 .x0 160] else []) ++
    enter (2*q) (if q = 0 then hashBase else slot (2*q-1)) ++
    [.LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q))),
     .JALR .x0 .x28 (imm12 (jumpImm q))]
def root : Code :=
  [.ADDI .x10 .x10 (imm12 ((0x400038 : ℤ) - slot 31)), .ADDI .x11 .x13 768, .ECALL]
def copyBody (q d : ℕ) : Code :=
  List.replicate (2 ^ fineWidth q - if narrow (2*q) then 1 else 0) .ECALL ++
    enter (2*q+1) (slot (2*q)) ++
    List.replicate (d+1 - if narrow (2*q+1) then 1 else 0) .ECALL ++
    (if q = 15 then root ++ decision else prologue (q+1))
def copyCode (q d : ℕ) : Code :=
  copyBody q d ++ List.replicate (64 - (copyBody q d).length) nop
def groupPairs (g : ℕ) : List ℕ :=
  if g < 4 then [2*g, 2*g+1] else [g+4, g+8]
def groupCode (g : ℕ) : Code :=
  (List.range (if g = 0 then 8 else 16)).flatMap fun c =>
    (groupPairs g).flatMap fun q => copyCode q (copies q - 1 - c)
def verifier : Code := indexPhase ++ prologue 0 ++ (List.range 8).flatMap groupCode

def firstMask : ℕ := 0xe7c + 0xe7c * 2^16 + 0x1e3c * 2^32 + 0x1e3c * 2^48
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes firstMask ++ wordBytes (broadcast 0x1e3c) ++
    wordBytes (broadcast 0x1fc) ++ wordBytes 65535 ++ wordBytes 0 ++ wordBytes 5504 ++
    wordBytes (baseWord 0) ++ wordBytes (baseWord 1) ++ wordBytes (baseWord 2)
def image : Riscv.Image := ⟨verifier, dataImage⟩

theorem index_length : indexPhase.length = 48 := by decide +kernel
theorem code_length : verifier.length = 15412 := by decide +kernel
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
