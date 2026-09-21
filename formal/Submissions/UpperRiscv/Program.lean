import OptimalOTS.RiscvMachine
import Submissions.UpperRiscv.Valid

/-!
# The RV64IM image of the bare-chain verifier

1. **Index.** Save the public key and hash the 384 bits `message ‖ nonce` as the loader placed
   them, with the message in the low bits, to the data base; reject unless the signature has
   5504 bits.
2. **Lanes.** Chain `k` reads byte `slotOf k` of the answer, masked to 5 bits (`k < 16`) or
   4 bits (`16 ≤ k < 28`); the last four chains take the even bytes 24, 26, 28, 30, and the odd
   bytes 25, 27, 29, 31 are ignored. Seven lane words hold `4 · field` in 16-bit lanes; their sum
   is checked against `4 · 215` with one multiplication; `jumpBase - 4 · field` is stored for
   every chain in the 56 bytes below the signature region (the public key and the message have
   been consumed).
3. **Chains.** Chain `k`'s 192-bit value sits at `sig + 16 + 24 k`; chains run from 0 up to 27,
   hashing the value at its slot with the 32-byte answer written eight bytes below the slot
   (`x12 = x10 - 8`): the high 192 bits of the answer land on the slot and feed the next step,
   the low eight bytes overwrite the tail of the already final chain below. A block is four
   instructions and a table of `field + 1` hashes.
4. **Root.** The 680 bytes from `sig + 8` are the 5440-bit root input: the low 192 bits of every
   top and the full top of chain 27; its hash overwrites the last top, and the low 128 bits of the
   answer are compared with the saved public key.
-/

namespace OptimalOTS.Riscv2Program

open RiscvZkvm.Rv64

abbrev Code := List Instr

def reject : Code := [.ADDI .x5 .x0 0, .ADDI .x10 .x0 0, .ECALL]

def copy128 (src : Reg) (srcOff : ℕ) (dst : Reg) (dstOff : ℕ) : Code :=
  [.LD .x26 src (BitVec.ofNat 12 srcOff), .LD .x27 src (BitVec.ofNat 12 (srcOff + 8)),
   .SD dst .x26 (BitVec.ofNat 12 dstOff), .SD dst .x27 (BitVec.ofNat 12 (dstOff + 8))]

/-- Number of chains. -/
def C : ℕ := 28

/-- Chain `k` has a 5-bit field (32 levels) for `k < 16`, a 4-bit field (16 levels) otherwise. -/
def levels (k : ℕ) : ℕ := if k < 16 then 32 else 16

/-- The field sum of an accepted index. -/
def target : ℕ := 215

def sigBits : ℕ := 5504

/-! ## The index phase -/

def indexPrefix : Code :=
  [.LD .x30 .x10 0, .LD .x31 .x10 8, .ADDI .x11 .x0 512, .LUI .x12 0x200, .ADDI .x5 .x0 1]

def lengthCheck : Code := [.LD .x6 .x12 (BitVec.ofNat 12 64), .BEQ .x13 .x6 16] ++ reject

/-- The four index words, the two masks, the lane multiplier and the broadcast jump base. -/
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16, .LD .x23 .x12 24,
   .LD .x24 .x12 32, .LD .x25 .x12 40, .LD .x2 .x12 48, .LD .x3 .x12 56]

/-- The offset of lane word `(w, i)` in the lane area, which starts at `laneBase`. -/
def laneOff (w i : ℕ) : ℕ := 8 * (2 * w + i)

/-- The lane area: seven words below the signature region, over the consumed public key,
message and nonce. -/
def laneBase : ℕ := 0x3FFFF8

/-- The public-key pointer: the input of the 512-bit index query `pk ‖ message ‖ nonce` and the
store base of the lane area (`x10` through the index phase). -/
def hashBase : ℕ := 0x400000

def srcReg (w : ℕ) : Reg := match w with | 0 => .x20 | 1 => .x21 | 2 => .x22 | _ => .x23

def maskReg (w : ℕ) : Reg := if w < 2 then .x24 else .x25

/-- Lane word `(w, i)`: fields `8 w + 2 l + i` (bytes of index word `w`), times four, in the 16-bit
lanes `l`. -/
def laneWord (w i : ℕ) : Code :=
  let dst : Reg := if w = 0 ∧ i = 0 then .x27 else .x26
  (if i = 0 then [.SLLI dst (srcReg w) 2] else [.SRLI dst (srcReg w) 6]) ++
  [.AND dst dst (maskReg w)] ++ (if w = 0 ∧ i = 0 then [] else [.ADD .x27 .x27 .x26]) ++
  [.SUB .x26 .x3 dst, .SD .x10 .x26 (BitVec.ofInt 12 ((laneBase + laneOff w i : ℤ) - hashBase))]

def lanes : Code := (List.range 7).flatMap fun j => laneWord (j / 2) (j % 2)

def sumCheck : Code :=
  [.MUL .x27 .x27 .x2, .SRLI .x27 .x27 48, .XORI .x27 .x27 (BitVec.ofNat 12 (4 * target)),
   .BEQ .x27 .x0 16] ++ reject

/-- The chain input length; the input pointer still holds the message address, 48 bytes below
chain 0's slot. -/
def setup : Code := [.ADDI .x11 .x0 192]

def indexPhase : Code := indexPrefix ++ [.ECALL] ++ lengthCheck ++ loadWords ++ lanes ++ sumCheck ++ setup

def indexLength : ℕ := indexPhase.length

/-! ## The chains -/

def imm12 (z : ℤ) : BitVec 12 := BitVec.ofInt 12 z

/-- The offset of the halfword of chain `k` in the lane area: chain `k` sits in slot `slotOf k`,
which is lane `slotOf k % 8 / 2` of lane word `(slotOf k / 8, slotOf k % 2)`. -/
def laneHalf (k : ℕ) : ℕ :=
  laneOff (slotOf k / 8) (slotOf k % 2) + 2 * (slotOf k % 8 / 2)

/-- The answer buffer of chain `k`, eight bytes below its slot `0x400040 + 24 k`. -/
def outAddr (k : ℕ) : ℕ := 0x400038 + 24 * k

/-- Instructions of the block of chain `k`. -/
def blockLength (k : ℕ) : ℕ := 4 + levels k

/-- Code address (bytes) of the end of chain `k`'s table; chains are laid out from 0 up. -/
def tableEnd (k : ℕ) : ℕ :=
  4096 + 4 * (indexLength + ((List.range (k + 1)).map blockLength).sum)

def jumpBase : ℕ := 6088

def chainPrologue (k : ℕ) : Code :=
  [.ADDI .x10 .x10 (if k = 0 then 64 else 24), .ADDI .x12 .x10 (imm12 (-8)),
   .LHU .x28 .x12 (imm12 ((laneBase + laneHalf k : ℤ) - outAddr k)),
   .JALR .x0 .x28 (imm12 ((tableEnd k : ℤ) - 4 - jumpBase))]

def chainBlock (k : ℕ) : Code := chainPrologue k ++ List.replicate (levels k) .ECALL

def chains : Code := (List.range C).flatMap chainBlock

/-! ## The root and the decision -/

/-- The root hash reads the 680-byte region and writes its answer over the last top, where the
answer buffer already points. -/
def root : Code := [.ADDI .x10 .x10 (imm12 (-656)), .ADDI .x11 .x13 (imm12 (-64)), .ECALL]

def decision : Code :=
  [.LD .x26 .x12 0, .BNE .x26 .x30 24, .LD .x28 .x12 8, .BNE .x28 .x31 16,
   .ADDI .x10 .x0 1, .ADDI .x5 .x0 0, .ECALL] ++ reject

def verifier : Code := indexPhase ++ chains ++ root ++ decision

/-! ## The data image -/

def broadcast (v : ℕ) : ℕ := v + v * 2 ^ 16 + v * 2 ^ 32 + v * 2 ^ 48

def wordBytes (v : ℕ) : List (BitVec 8) := (List.range 8).map fun j => BitVec.ofNat 8 (v / 2 ^ (8 * j))

def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes (broadcast 0x7C) ++ wordBytes (broadcast 0x3C) ++
    wordBytes 0x0001000100010001 ++ wordBytes (broadcast jumpBase) ++ wordBytes sigBits

def image : Riscv.Image := ⟨verifier, dataImage⟩

end OptimalOTS.Riscv2Program
