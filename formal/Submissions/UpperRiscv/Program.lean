import OptimalOTS.RiscvMachine

/-!
# The RV64IM image of the bare-chain verifier

1. **Index.** Save the public key and hash the 384 bits `message ‖ nonce` as the loader placed
   them, with the message in the low bits, to the data base; reject unless the signature has
   5504 bits.
2. **Lanes.** The 28 fields sit in the 16-bit lanes of the first three answer words: two per
   lane in words 0 and 1 (five bits each, at lane bits 2 and 7) and three per lane in word 2
   (four bits each, at lane bits 2, 6 and 10), so that after at most one shift a single mask
   leaves `4 · field` in every lane. Seven lane words hold these; their sum is checked against
   `4 · 215` with one multiplication; `jumpBase - 4 · field` is stored for every chain in the 56
   bytes below the signature region (the public key and the message have been consumed).
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

def lengthCheck : Code := [.LD .x6 .x12 (BitVec.ofNat 12 72), .BEQ .x13 .x6 16] ++ reject

/-- The three index words, the two masks, the lane multiplier and the broadcast jump base. -/
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16,
   .LD .x24 .x12 32, .LD .x25 .x12 40, .LD .x2 .x12 56, .LD .x3 .x12 64]

/-- The lane area: seven words below the signature region, over the consumed public key and
message. -/
def laneBase : ℕ := 0x3FFFF8

/-- The public-key pointer: the input of the 512-bit index query `pk ‖ message ‖ nonce` and the
store base of the lane area (`x10` through the index phase). -/
def hashBase : ℕ := 0x400000

/-- The register of index word `w`. -/
def wordReg (w : ℕ) : Reg := match w with | 0 => .x20 | 1 => .x21 | _ => .x22

/-- The index word of lane word `g`: word 0 for the first two lane words, word 1 for the next
two, word 2 for the last three. -/
def wordIdx (g : ℕ) : ℕ := if g < 2 then 0 else if g < 4 then 1 else 2

/-- The right shift of lane word `g`, which brings its fields to bits `2 …` of every lane. -/
def shiftOf (g : ℕ) : ℕ :=
  if g = 1 ∨ g = 3 then 5 else if g = 5 then 4 else if g = 6 then 8 else 0

/-- The field width of lane word `g`. -/
def widthOf (g : ℕ) : ℕ := if g < 4 then 5 else 4

def srcReg (g : ℕ) : Reg := wordReg (wordIdx g)

def maskReg (g : ℕ) : Reg := if g < 4 then .x24 else .x25

/-- The offset of lane word `g` in the lane area, which starts at `laneBase`. -/
def laneOff (g : ℕ) : ℕ := 8 * g

/-- Lane word `g`: four fields of its index word, times four, in the 16-bit lanes — at most one
shift, a mask, the accumulation, the subtraction from the broadcast jump base and the store. -/
def laneWord (g : ℕ) : Code :=
  let dst : Reg := if g = 0 then .x27 else .x26
  (if shiftOf g = 0 then [.AND dst (srcReg g) (maskReg g)]
   else [.SRLI dst (srcReg g) (BitVec.ofNat 6 (shiftOf g)), .AND dst dst (maskReg g)]) ++
  (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
  [.SUB .x26 .x3 dst, .SD .x10 .x26 (BitVec.ofInt 12 ((laneBase + laneOff g : ℤ) - hashBase))]

def lanes : Code := (List.range 7).flatMap laneWord

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

/-- The lane word holding chain `k`'s field: chains `0 … 15` alternate between the two lane
words of their index word, chains `16 … 27` cycle through the three lane words of word 2. -/
def laneOfChain (k : ℕ) : ℕ := if k < 16 then 2 * (k / 8) + k % 2 else 4 + (k - 16) % 3

/-- The lane of chain `k` within its lane word. -/
def laneIdx (k : ℕ) : ℕ := if k < 16 then k % 8 / 2 else (k - 16) / 3

/-- The offset of the halfword of chain `k` in the lane area. -/
def laneHalf (k : ℕ) : ℕ := laneOff (laneOfChain k) + 2 * laneIdx k

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
    wordBytes 0x003C003C ++ wordBytes 0x0001000100010001 ++ wordBytes (broadcast jumpBase) ++
    wordBytes sigBits

def image : Riscv.Image := ⟨verifier, dataImage⟩

end OptimalOTS.Riscv2Program
