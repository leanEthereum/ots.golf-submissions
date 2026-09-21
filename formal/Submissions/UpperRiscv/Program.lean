import OptimalOTS.RiscvMachine

/-!
# The RV64IM image of the bare-chain verifier, with paired dispatch

1. **Index.** Save the public key and hash the 512 bits `pk ‖ message ‖ nonce` as the loader
   placed them; reject unless the signature has 5504 bits.
2. **Lanes.** The 28 fields sit in the 16-bit lanes of the four answer words. Words 0–2 hold
   twelve *pairs*, one per lane: a five-bit field at lane bits `2 … 6` (chain `2p`) and a
   four-bit field at lane bits `10 … 13` (chain `2p + 1`), so that one mask leaves
   `4 · dA + 1024 · dB` in the lane. Word 3 holds the four remaining five-bit fields at lane bits
   `2 … 6`. Each masked word is subtracted from a broadcast jump base and stored as four dispatch
   halfwords; the running sum of the masked words is folded so that every lane holds
   `4 · (Σ dA + Σ dB)`, and the field sum is checked against `4 · 215` with one multiplication.
3. **Blocks.** Block `q < 12` handles chains `2q` and `2q + 1`; blocks `12 … 15` handle chains
   `24 … 27` alone. A block's prologue advances the input pointer to its first slot, points the
   answer buffer eight bytes below it, loads the block's dispatch halfword and jumps. For a pair the
   jump lands in one of sixteen *copies*, selected by `dB`, at the hash step of `dA`'s position:
   `dA + 1` hashes of chain `2q`, two pointer moves, `dB + 1` hashes of chain `2q + 1`, then the
   next block's prologue, replicated in the copy. The copies of the four pairs of one lane word
   are interleaved at 256-byte slots, so a lane's halfword `base − 4 dA − 1024 dB` plus the
   block's `JALR` immediate is exactly the landing address. A single block is a table of 32
   hash steps followed by the next prologue.
4. **Root.** The 680 bytes from `sig + 8` are the 5440-bit root input; its hash overwrites the
   last top, and the low 128 bits of the answer are compared with the saved public key.
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

/-- The field sum of an accepted index. -/
def target : ℕ := 215

def sigBits : ℕ := 5504

def imm12 (z : ℤ) : BitVec 12 := BitVec.ofInt 12 z

/-! ## Memory layout -/

/-- The public-key pointer: the input of the 512-bit index query `pk ‖ message ‖ nonce` and the
store base of the lane area (`x10` through the index phase). -/
def hashBase : ℕ := 0x400000

/-- The lane area: four words below the public key. -/
def laneBase : ℕ := 0x3FFFE0

/-- The address of lane word `g`. -/
def laneWordAddr (g : ℕ) : ℕ := laneBase + 8 * g

/-- The first chain of block `q`: pairs for `q < 12`, singles after. -/
def firstChain (q : ℕ) : ℕ := if q < 12 then 2 * q else 12 + q

/-- The lane word and lane holding block `q`'s dispatch halfword. -/
def laneGroup (q : ℕ) : ℕ := if q < 12 then q / 4 else 3

def laneIdx (q : ℕ) : ℕ := if q < 12 then q % 4 else q - 12

/-- The address of the dispatch halfword of block `q`. -/
def laneAddr (q : ℕ) : ℕ := laneWordAddr (laneGroup q) + 2 * laneIdx q

/-- The answer buffer of chain `k`, eight bytes below its slot `0x400040 + 24 k`. -/
def outAddr (k : ℕ) : ℕ := 0x400038 + 24 * k

/-! ## Code layout -/

/-- The length of the index phase. -/
def indexLength : ℕ := 49

/-- The code address of the first copy: after the index phase and block 0's prologue. -/
def copiesStart : ℕ := 4096 + 4 * (indexLength + 4)

/-- Each copy occupies 64 instructions; copies of the four pairs of lane word `g` are interleaved,
with `dB` decreasing along memory. -/
def copyStart (q dB : ℕ) : ℕ := copiesStart + 4 * (4096 * (q / 4) + 256 * (15 - dB) + 64 * (q % 4))

def singlesStart : ℕ := copiesStart + 4 * 12288

/-- The table of single block `12 + s`. -/
def singleTableStart (s : ℕ) : ℕ := singlesStart + 4 * (36 * s)

/-- The landing address of block `q` for `dA = 0` (and `dB = 0`): the last step of its table. -/
def landing0 (q : ℕ) : ℕ :=
  if q < 12 then copyStart q 0 + 124 else singleTableStart (q - 12) + 124

/-- The broadcast jump base of lane word `g`. -/
def laneBaseOf (g : ℕ) : ℕ := if g = 0 then 0x4ED0 else if g = 1 then 0x8ED0 else 0xD028

/-- The `JALR` immediate of block `q`. -/
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) - laneBaseOf (laneGroup q)

/-! ## The index phase -/

def indexPrefix : Code :=
  [.LD .x30 .x10 0, .LD .x31 .x10 8, .ADDI .x11 .x0 512, .LUI .x12 0x200, .ADDI .x5 .x0 1]

def lengthCheck : Code := [.LD .x6 .x12 (BitVec.ofNat 12 72), .BEQ .x13 .x6 16] ++ reject

/-- The four index words, the three masks, the lane multiplier and the three jump bases. -/
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16, .LD .x23 .x12 24,
   .LD .x24 .x12 32, .LD .x25 .x12 40, .LD .x1 .x12 48, .LD .x2 .x12 56,
   .LD .x3 .x12 80, .LD .x4 .x12 88, .LD .x7 .x12 96]

/-- The register of index word `g`. -/
def wordReg (g : ℕ) : Reg := match g with | 0 => .x20 | 1 => .x21 | 2 => .x22 | _ => .x23

/-- The mask register of lane word `g`: the pair mask for words 0–2, the single mask for word 3. -/
def maskReg (g : ℕ) : Reg := if g < 3 then .x24 else .x25

/-- The jump-base register of lane word `g`. -/
def baseReg (g : ℕ) : Reg := match g with | 0 => .x3 | 1 => .x4 | _ => .x7

/-- Lane word `g`: mask, accumulate, subtract from the jump base, store. -/
def laneWord (g : ℕ) : Code :=
  let dst : Reg := if g = 0 then .x27 else .x26
  [.AND dst (wordReg g) (maskReg g)] ++ (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
  [.SUB .x26 (baseReg g) dst, .SD .x10 .x26 (imm12 ((laneWordAddr g : ℤ) - hashBase))]

def lanes : Code := (List.range 4).flatMap laneWord

/-- Bring the coarse fields down onto the fine ones: every lane then holds `4 · (dA + dB)`. -/
def fold : Code := [.SRLI .x26 .x27 8, .AND .x26 .x26 .x1, .AND .x27 .x27 .x1, .ADD .x27 .x27 .x26]

def sumCheck : Code :=
  [.MUL .x27 .x27 .x2, .SRLI .x27 .x27 48, .XORI .x27 .x27 (BitVec.ofNat 12 (4 * target)),
   .BEQ .x27 .x0 16] ++ reject

/-- The chain input length; the input pointer still holds the public-key address. -/
def setup : Code := [.ADDI .x11 .x0 192]

def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ lengthCheck ++ loadWords ++ lanes ++ fold ++ sumCheck ++ setup

/-! ## The blocks -/

/-- The prologue of block `q`: advance the input pointer to the block's first slot, point the
answer buffer eight bytes below, load the dispatch halfword and jump. -/
def prologue (q : ℕ) : Code :=
  [.ADDI .x10 .x10 (if q = 0 then 64 else 24), .ADDI .x12 .x10 (imm12 (-8)),
   .LHU .x28 .x12 (imm12 ((laneAddr q : ℤ) - outAddr (firstChain q))),
   .JALR .x0 .x28 (imm12 (jumpImm q))]

/-- Between the two chains of a pair: the pointers move to the next slot. -/
def switch : Code := [.ADDI .x10 .x10 24, .ADDI .x12 .x10 (imm12 (-8))]

def nop : Instr := .ADDI .x0 .x0 0

/-- Copy `dB` of pair block `q`: the 32-step table of chain `2q`, the switch, `dB + 1` steps of
chain `2q + 1`, the next block's prologue, and padding to 64 instructions. -/
def copyCode (q dB : ℕ) : Code :=
  List.replicate 32 .ECALL ++ switch ++ List.replicate (dB + 1) .ECALL ++ prologue (q + 1) ++
    List.replicate (25 - dB) nop

/-- The copies of the four pairs of lane word `g`, `dB` decreasing, pairs interleaved. -/
def groupCode (g : ℕ) : Code :=
  (List.range 16).flatMap fun c => (List.range 4).flatMap fun j => copyCode (4 * g + j) (15 - c)

def pairsCode : Code := (List.range 3).flatMap groupCode

/-- Single block `12 + s`: its table, then the next prologue. -/
def singleBlock (s : ℕ) : Code :=
  List.replicate 32 .ECALL ++ (if s < 3 then prologue (13 + s) else [])

def singlesCode : Code := (List.range 4).flatMap singleBlock

/-! ## The root and the decision -/

/-- The root hash reads the 680-byte region and writes its answer over the last top, where the
answer buffer already points. -/
def root : Code := [.ADDI .x10 .x10 (imm12 (-656)), .ADDI .x11 .x13 (imm12 (-64)), .ECALL]

def decision : Code :=
  [.LD .x26 .x12 0, .BNE .x26 .x30 24, .LD .x28 .x12 8, .BNE .x28 .x31 16,
   .ADDI .x10 .x0 1, .ADDI .x5 .x0 0, .ECALL] ++ reject

def verifier : Code := indexPhase ++ prologue 0 ++ pairsCode ++ singlesCode ++ root ++ decision

/-! ## The data image -/

def broadcast (v : ℕ) : ℕ := v + v * 2 ^ 16 + v * 2 ^ 32 + v * 2 ^ 48

def wordBytes (v : ℕ) : List (BitVec 8) := (List.range 8).map fun j => BitVec.ofNat 8 (v / 2 ^ (8 * j))

/-- The pair mask keeps lane bits `2 … 6` and `10 … 13`; the single mask bits `2 … 6`; the fold
mask bits `2 … 8`. -/
def pairMask : ℕ := 0x3C7C
def singleMask : ℕ := 0x7C
def foldMask : ℕ := 0x1FC

def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes (broadcast pairMask) ++ wordBytes (broadcast singleMask) ++
    wordBytes (broadcast foldMask) ++ wordBytes (broadcast 1) ++ wordBytes 0 ++ wordBytes sigBits ++
    wordBytes (broadcast (laneBaseOf 0)) ++ wordBytes (broadcast (laneBaseOf 1)) ++
    wordBytes (broadcast (laneBaseOf 2))

def image : Riscv.Image := ⟨verifier, dataImage⟩

end OptimalOTS.Riscv2Program
