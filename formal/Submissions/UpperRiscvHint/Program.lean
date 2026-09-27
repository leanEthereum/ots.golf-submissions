import OptimalOTS.RiscvMachine

/-! Shared pieces of the image: the code type, the index prefix, the rejection and decision
fragments, the memory addresses of the index phase and the data-image encoders. -/

namespace OptimalOTS.Riscv2Program

open RiscvZkvm.Rv64

abbrev Code := List Instr

def reject : Code := [.ADDI .x5 .x0 0, .ADDI .x10 .x0 0, .ECALL]

def imm12 (z : ℤ) : BitVec 12 := BitVec.ofInt 12 z

def nop : Instr := .ADDI .x0 .x0 0

/-- The public-key pointer: the input of the 512-bit index query `pk ‖ message ‖ nonce` and the
store base of the lane area (`x10` through the index phase). -/
def hashBase : ℕ := 0x400000

/-- The lane area: four words above the root region and the honest view. -/
def laneBase : ℕ := 0x4003C0

/-- The address of lane word `g`. -/
def laneWordAddr (g : ℕ) : ℕ := laneBase + 8 * g

def indexPrefix : Code :=
  [.LD .x30 .x10 0, .LD .x31 .x10 8, .ADDI .x11 .x0 512, .LUI .x12 0x200, .ADDI .x5 .x0 1]

/-- The register of index word `g`. -/
def wordReg (g : ℕ) : Reg := match g with | 0 => .x20 | 1 => .x21 | 2 => .x22 | _ => .x23

/-- `x5` is the low-word difference and `x10` the high-word difference from the stored key, whose
high word has bit 0 flipped: HALT accepts exactly on the root. Every other case halts rejecting,
traps, or hashes and then traps at the `JALR` to address 0. -/
def decision : Code :=
  [.LD .x26 .x12 0, .LD .x27 .x12 8, .XOR .x5 .x26 .x30, .XOR .x10 .x27 .x31, .ECALL,
   .JALR .x0 .x0 0]

def broadcast (v : ℕ) : ℕ := v + v * 2 ^ 16 + v * 2 ^ 32 + v * 2 ^ 48

def wordBytes (v : ℕ) : List (BitVec 8) := (List.range 8).map fun j => BitVec.ofNat 8 (v / 2 ^ (8 * j))

end OptimalOTS.Riscv2Program
