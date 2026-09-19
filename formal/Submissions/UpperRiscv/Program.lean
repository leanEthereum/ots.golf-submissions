import OptimalOTS.RiscvMachine
import Submissions.UpperRiscv.Constants

/-!
# The RV64IM image of the flat forest verifier

Straight-line code except for two rejection branches and one computed jump per chain.

1. **Index.** Save the public key in `x30`/`x31`, copy the nonce over it so that
   `nonce ‖ message` is contiguous, and hash these 384 bits into the data area. Reject a
   signature of other than 4224 bits.
2. **Lanes.** From the two index words, build eight lane words: 16-bit lanes holding
   `8 · nibble`. Their sum, multiplied by `0x0001000100010001`, carries `8 · Σ nibbles` in its top
   lane; reject unless the nibbles sum to `target = 160`. Store `jumpBase - 8 · nibble` for every
   chain.
3. **Chains.** Chain `k`'s slot holds its value at `Flat.slotAddr k`, after an 8-byte header.
   The block copies the disclosed word into the slot, writes the slot address as the header,
   loads its jump target and jumps into a table of 15 steps: each step stores its level tag in
   the header's top halfword and hashes the 192-bit header and value in place.
4. **Root.** The 32 slots with the headers between them are the 6080-bit root input; the low
   128 bits of its hash are compared with the saved public key.
-/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

abbrev Code := List Instr

/-- The inline rejection: HALT with decision `0`. -/
def reject : Code := [.ADDI .x5 .x0 0, .ADDI .x10 .x0 0, .ECALL]

/-- Copy a 128-bit value between register-relative, doubleword-aligned locations. -/
def copy128 (src : Reg) (srcOff : ℕ) (dst : Reg) (dstOff : ℕ) : Code :=
  [.LD .x26 src (BitVec.ofNat 12 srcOff), .LD .x27 src (BitVec.ofNat 12 (srcOff + 8)),
   .SD dst .x26 (BitVec.ofNat 12 dstOff), .SD dst .x27 (BitVec.ofNat 12 (dstOff + 8))]

/-! ## The index phase -/

/-- Everything before the index HASH: the payload cursor, the saved public key, the nonce copied
below the message, and the HASH arguments (output at the data base). -/
def indexPrefix : Code :=
  [.ADDI .x9 .x12 16, .LD .x30 .x10 0, .LD .x31 .x10 8] ++ copy128 .x12 0 .x10 0 ++
  [.ADDI .x11 .x0 384, .LUI .x12 0x200, .ADDI .x5 .x0 1]

/-- Reject unless the signature has exactly 4224 bits. -/
def lengthCheck : Code := [.LUI .x6 1, .ADDI .x6 .x6 128, .BEQ .x13 .x6 16] ++ reject

/-- Load the index words and the four lane constants. -/
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 32, .LD .x23 .x12 40, .LD .x24 .x12 48,
   .LD .x25 .x12 56]

/-- Lane word `(w, i)`: the nibbles `16 w + 4 l + i` of the index, times eight, in the 16-bit
lanes `l`. The first lane word starts the sum in `x27`; the others are added to it. Each lane word
is subtracted from its broadcast jump base and stored. -/
def laneWord (w i : ℕ) : Code :=
  let src : Reg := if w = 0 then .x20 else .x21
  let base : Reg := if w = 0 then .x24 else .x25
  let dst : Reg := if w = 0 ∧ i = 0 then .x27 else .x26
  (if i = 0 then [.SLLI dst src 3] else [.SRLI dst src (BitVec.ofNat 6 (4 * i - 3))]) ++
  [.AND dst dst .x22] ++ (if w = 0 ∧ i = 0 then [] else [.ADD .x27 .x27 .x26]) ++
  [.SUB .x26 base dst, .SD .x12 .x26 (BitVec.ofNat 12 (64 + 8 * (4 * w + i)))]

def lanes : Code := (List.range 8).flatMap fun j => laneWord (j / 4) (j % 4)

/-- Reject unless the nibbles sum to 160: the top lane of `sum * 0x0001000100010001` is `8 · Σ`. -/
def sumCheck : Code :=
  [.MUL .x27 .x27 .x23, .SRLI .x27 .x27 48, .XORI .x27 .x27 1280, .BEQ .x27 .x0 16] ++ reject

/-- The level tags not already held by a register, and the chain input length. -/
def levelSetup : Code :=
  [.ADDI .x1 .x0 2, .ADDI .x2 .x0 3, .ADDI .x3 .x0 4, .ADDI .x4 .x0 5, .ADDI .x6 .x0 6,
   .ADDI .x7 .x0 7, .ADDI .x8 .x0 8, .ADDI .x11 .x0 192]

def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ lengthCheck ++ loadWords ++ lanes ++ sumCheck ++ levelSetup

/-! ## The chains -/

/-- The register holding the level tag of level `t` in its low sixteen bits. -/
def levReg (t : ℕ) : Reg :=
  match t with
  | 0 => .x5 | 1 => .x11 | 2 => .x9 | 3 => .x22 | 4 => .x13 | 5 => .x24 | 6 => .x25
  | 7 => .x1 | 8 => .x2 | 9 => .x3 | 10 => .x4 | 11 => .x6 | 12 => .x7 | 13 => .x8
  | _ => .x0

/-- Step `t` of a chain: store the level tag, hash the header and value in place. -/
def chainStep (t : ℕ) : Code := [.SH .x12 (levReg t) (BitVec.ofNat 12 4094), .ECALL]

/-- The fifteen steps of a chain; the prologue jumps to step `15 - nibble`. -/
def chainTable : Code := (List.range 15).flatMap chainStep

/-- Number of instructions before chain `0`. -/
def indexLength : ℕ := 77

/-- Number of instructions of a chain block. -/
def blockLength : ℕ := 39

/-- The code address after chain `k`'s table. -/
def tableEnd (k : ℕ) : ℕ := 4096 + 4 * (indexLength + blockLength * (k + 1))

/-- The lane word and lane of chain `k`: chains `0-15` use the low index word. -/
def laneAddr (k : ℕ) : ℕ :=
  0x200000 + 64 + 8 * (4 * (k / 16) + k % 4) + 2 * (k % 16 / 4)

/-- The jump base of chain `k`. -/
def jumpBase (k : ℕ) : ℕ := if k < 16 then Flat.jumpBase0 else Flat.jumpBase1

/-- A signed 12-bit immediate. -/
def imm12 (z : ℤ) : BitVec 12 := BitVec.ofInt 12 z

/-- Chain `k`'s prologue: move the slot pointer, copy the disclosed word, write the header,
load the jump target `jumpBase - 8 · nibble` and jump to `tableEnd k - 8 · nibble`. -/
def chainPrologue (k : ℕ) : Code :=
  [.ADDI .x12 .x12 (BitVec.ofNat 12 (if k = 0 then 136 else 24)), .ADDI .x10 .x12 (imm12 (-8))] ++
  copy128 .x9 (16 * k) .x12 0 ++
  [.SD .x12 .x12 (imm12 (-8)),
   .LHU .x28 .x12 (imm12 ((laneAddr k : ℤ) - (Flat.slotAddr k : ℤ))),
   .JALR .x0 .x28 (imm12 ((tableEnd k : ℤ) - (jumpBase k : ℤ)))]

def chainBlock (k : ℕ) : Code := chainPrologue k ++ chainTable

def chains : Code := (List.range 32).flatMap chainBlock

/-! ## The root and the decision -/

/-- The root input starts at chain `0`'s slot and has 6080 bits; the answer overwrites it. -/
def root : Code := [.ADDI .x10 .x12 (imm12 (-744)), .LUI .x11 1, .ADDI .x11 .x11 1984, .ECALL]

/-- Compare the root answer's low 128 bits with the saved public key and halt. -/
def decision : Code :=
  [.LD .x26 .x12 0, .XOR .x26 .x26 .x30, .LD .x28 .x12 8, .XOR .x28 .x28 .x31,
   .OR .x26 .x26 .x28, .SLTIU .x10 .x26 1, .ADDI .x5 .x0 0, .ECALL]

def verifier : Code := indexPhase ++ chains ++ root ++ decision

/-! ## The data image -/

/-- The four lane constants, broadcast to the 16-bit lanes. -/
def broadcast (v : ℕ) : ℕ := v + v * 2 ^ 16 + v * 2 ^ 32 + v * 2 ^ 48

/-- Little-endian bytes of a word. -/
def wordBytes (v : ℕ) : List (BitVec 8) := (List.range 8).map fun j => BitVec.ofNat 8 (v / 2 ^ (8 * j))

/-- The data image: 32 zero bytes (the index answer), then `0x78`, `1` and the two jump bases,
broadcast. -/
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes (broadcast 0x78) ++ wordBytes (broadcast 1) ++
    wordBytes (broadcast Flat.jumpBase0) ++ wordBytes (broadcast Flat.jumpBase1)

def image : Riscv.Image := ⟨verifier, dataImage⟩

end OptimalOTS.RiscvUpperProgram
