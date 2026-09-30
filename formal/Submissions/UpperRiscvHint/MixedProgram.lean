import Submissions.UpperRiscvHint.Program
import Submissions.UpperRiscvHint.WeightedPairs

/-! The 311-cycle free-chain image. Caps 31 and 32 occupy the opposite boundaries
of an 884-byte root at 0x400046; caps 0 through 12 have 192-bit states, and the boundary
caps have 144-bit states. Other chains have 144-bit states and a mandatory final hash.
Chain 32's state uses answer bits [112,256), leaving its input pointer at the root start.
Chain 31's top uses [0,144); chain 30 contributes a full 256-bit top before it.

The loader supplies the capped view length L in x13. ANDI with -1924 preserves its
2048-bit bank and bits 2 through 6. An honest view supplies the dispatch base 6144
and displacement 4*(31-c) together, removing one ADD before the indirect jump.
The adjusted checksum equals the HASH call number exactly when S+c = 147 modulo 257, where S is
the shifted weighted sum (cap pairs 0–5 carry one extra unit each).
Other banks either fault outside the image or land in reserved rejection windows.
Counts at least 19 reject within the honest bank. Raw forms are padded into a guarded bank.

Pair 0's prologue occurs once, so its jump links a fixed address into x1: the root length is
that address plus 2044, and no constant load is needed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix wordReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

/-- The answer buffer of chain `k`, and for a cap also its value and state. -/
def outAddr (k : ℕ) : ℕ :=
  if k = 32 then 0x400038 else if k = 31 then 0x4003A8 else 0x400058 +
    if k ≤ 12 then 56 * k else if k < 25 then 56 * (k - 13) + 24 else 696 + 24 * (k - 25)
/-- View byte offset of chain `k`'s value, after the 16-byte nonce. -/
def wireByte (k : ℕ) : ℕ :=
  if k = 32 then 6 else 24 +
    if k ≤ 12 then 56 * k else if k < 25 then 56 * (k - 13) + 32 else 704 + 24 * (k - 25)
/-- The input address while chain `k` hashes: its value in the view, then its state. -/
def work (k : ℕ) : ℕ := 0x400040 + wireByte k
/-- A bound containing every fixed payload position in an honest view. -/
def honestViewBits : ℕ := 7248
/-- The former count byte, now unused by execution. -/
def freeByte : ℕ := 0x400070
/-- The honest bank's dispatch base: the masked tag of an honest view length less `4*(31-c)`. -/
def freeBase : ℕ := 6144
def fineWidth (_q : ℕ) : ℕ := 4
def copies (_q : ℕ) : ℕ := 16
/-- Corresponding pairs of all four words share one base. Adjacent groups interleave
their boundary rows; the final row has fifteen fewer hashes in each body. -/
def group (q : ℕ) : ℕ := q % 4
def withinGroup (q : ℕ) : ℕ := q / 4
def groupOffset (_g : ℕ) : ℕ := 0
def slotOffset (q : ℕ) : ℕ :=
  [0,3705,7327,11261,144,3509,7165,11363,37,4119,7803,11298,81,4181,7741,11425].getD q 0
/-- The code index of the first copy: after the index phase, the free dispatch, the free row and
pair 0's prologue. -/
def copiesIndex : ℕ := 233
def copiesStart : ℕ := 4096 + 4 * copiesIndex
def copyStart (q d : ℕ) : ℕ :=
  copiesStart + 4 * (groupOffset (group q) + 256 * (copies q - 1 - d) + slotOffset q)
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 4 * (2 ^ fineWidth q - 1)
/-- Lane 0 carries the bias for the masked tag: adding `6144 + 4*(31-c)` gives
residue 1 exactly when the shifted digit sum plus `c` is 147 modulo 257. -/
def baseLane (q : ℕ) : ℕ := min (landing0 (q % 4)) 65532 + if q % 4 = 0 then 75 else 0
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
/-- A cap pair's first chain hashes once per digit unit, one hash fewer than a normal chain, so
its landing is one row later. -/
def lead (q : ℕ) : ℕ := if q < 6 ∨ 15 ≤ q then 1 else 0
def jumpImm (q : ℕ) : ℤ := (landing0 q : ℤ) + 4 * lead q - baseLane q
def baseReg (_g : ℕ) : Reg := .x3

/-- The four index words, the lane mask, the checksum modulus and the dispatch base. -/
def loadWords : Code :=
  [.LD .x20 .x12 0, .LD .x21 .x12 8, .LD .x22 .x12 16, .LD .x23 .x12 24,
   .LD .x25 .x12 32, .LD .x2 .x12 40, .LD .x3 .x12 48]
/-- The length bank and complemented count: `x6 = cappedViewLength & ~0x783`. -/
def freeCount : Code :=
  [.ANDI .x6 .x13 (imm12 (-1924))]
def maskReg (_g : ℕ) : Reg := .x25
def laneWord (g : ℕ) : Code :=
  let dst := if g = 0 then Reg.x27 else Reg.x26
  [.AND dst (wordReg g) (maskReg g), .SUB dst (baseReg g) dst] ++
    (if g = 0 then [] else [.ADD .x27 .x27 .x26]) ++
    [.SD .x10 dst (imm12 ((laneWordAddr g : ℤ) - hashBase))]
def freeSum : Code := [.ADD .x27 .x27 .x6]
/-- The residue lands in `x5`: 1, the HASH call number, exactly when the digit sum plus the free
count is 147 modulo 257. This check runs at the root boundary, after helper corrections;
any other residue traps before the root query. -/
def sumCheck : Code := [.REMU .x5 .x27 .x2]
/-- The free chain and the caps hash first: the chain width is 192 bits until pair 6. -/
def chainSetup : Code := [.ADDI .x11 .x0 192]
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ loadWords ++ freeCount ++
    (List.range 4).flatMap laneWord ++ freeSum ++ chainSetup

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((work k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - work k))]
/-- Pair 0's prologue, where the free dispatch lands for count 0. -/
def freeLanding : ℕ := 4096 + 4 * 229
/-- The link of pair 0's jump, from which the root length is computed. -/
def rootBase : ℕ := freeLanding + 16
/-- The free chain's pointers, then the jump `c` cells before pair 0's prologue. The padding
places pair 0's jump within `ADDI` reach of the root length. -/
def freeDispatch : Code :=
  enter 0 hashBase ++ .JALR .x0 .x6 (imm12 ((freeLanding : ℤ) - freeBase - 124)) ::
    List.replicate 131 nop
/-- Only pair 0's jump links: its prologue is the one copy at `freeLanding`. -/
def linkReg (q : ℕ) : Reg := if q = 0 then .x1 else .x0
/-- The table-row register `x28` changes only while `x12` points at neither chain of the pair. -/
def prologue (q : ℕ) : Code :=
  (if q = 6 then [.ADDI .x11 .x0 144] else []) ++
    [.ADDI .x12 .x10 (imm12 ((outAddr (2*q+1) : ℤ) - work (2*q))),
     .LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q+1))),
     .ADDI .x10 .x12 (imm12 ((work (2*q+1) : ℤ) - outAddr (2*q+1))),
     .JALR (linkReg q) .x28 (imm12 (jumpImm q))]
/-- After a skipped right chain `x10` still holds the left chain's state, so the next
prologue measures `x12` from `work (2*q-1)`. Only used after cap pairs, so `q ≤ 6`. -/
def skipPrologue (q : ℕ) : Code :=
  (if q = 6 then [.ADDI .x11 .x0 144] else []) ++
    [.ADDI .x12 .x10 (imm12 ((outAddr (2*q+1) : ℤ) - work (2*q-1))),
     .LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q+1))),
     .ADDI .x10 .x12 (imm12 ((work (2*q+1) : ℤ) - outAddr (2*q+1))),
     .JALR (linkReg q) .x28 (imm12 (jumpImm q))]
/-- The last chain's state is the root input's first slot, so `x10` needs no move. The root length
is pair 0's link plus 2044. -/
def root : Code := sumCheck ++ [.ADDI .x11 .x1 (imm12 (7072 - (rootBase : ℤ))), .ECALL]
def pairCap (q : ℕ) : ℕ := if q < 12 then 24 else 23
/-- Each unexpected length bank has 32 rejection targets and a preceding rejection stub. -/
def guardStart (bank : ℕ) : ℕ := 198 + 512*(bank-3)
def guardBanks : List ℕ := (List.range 509).map (· + 4)
def rejectStubs : List ℕ := guardBanks.map (fun bank => guardStart bank - 3)
def guardCode : Code := (List.range 32).map fun d =>
  .BEQ .x0 .x0 (BitVec.ofInt 13 (-12 - 4*(d : ℤ)))
def stubFor (ip : ℕ) : ℕ :=
  (rejectStubs.find? fun (s : ℕ) => decide (-4096 ≤ 4*((s : ℤ)-ip) ∧ 4*((s : ℤ)-ip) < 4096)).getD 707
def rejectJump (ip : ℕ) : Instr :=
  .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((stubFor ip : ℤ)-ip)))
/-- The free cell `c` instructions before pair 0's prologue: a hash of the free chain, or for
`c ≥ 19` a jump to a rejection stub. -/
def freeCell (c : ℕ) : Instr := if c < 19 then .ECALL else rejectJump (229 - c)
def freeRow : Code := [nop] ++ (List.range 63).map fun p => freeCell (63 - p)
/-- Fixed placements of the 492 redirected pairs (32 per cap pair, 30 per normal pair), in
`WeightedPairs.swapsOf` order. -/
def helperStarts : List (List ℕ) :=
 [[2393,1879,2455,1427,1941,2480,851,1108,1453,1968,2504,449,913,1170,1480,1993,2650,398,594,939,1197,1622,2136,2712,337,423,656,966,1365,1684,2198,2907],
  [5403,4988,5502,4563,5050,5564,3483,4022,4632,5077,5588,3164,3508,4375,4731,5146,5660,2992,3226,3534,4474,4838,5245,5759,2969,3017,3421,3678,4536,4889,5350,5917],
  [8610,7839,8633,7133,8096,8706,6530,6787,7202,8123,8768,6174,6592,6945,7459,8353,8867,6078,6273,6618,7044,7620,8449,8963,6016,6103,6431,6688,7106,7716,8511,9025],
  [10923,10505,11019,10152,10567,11081,9539,9796,10178,10666,11180,9282,9638,9895,10248,10691,11206,9147,9381,9664,9991,10310,10762,11685,9124,9220,9477,9734,10053,10409,10824,11712],
  [13932,13418,14124,13096,13610,14189,12390,12713,13161,13675,14255,12199,12456,12739,13227,13741,14281,12068,12226,12582,12839,13254,13762,14381,11942,12133,12325,12647,12904,13353,13867,14446],
  [16102,15911,16126,15776,15936,16152,15409,15670,15803,15964,16177,14895,15590,15697,15831,15990,16204,14703,15152,15617,15725,15859,16012,16229,14638,14769,15283,15645,15748,15885,16039,16257],
  [16980,16812,17005,16671,16838,17032,16503,16699,16867,17058,16420,16530,16727,16896,17126,16313,16367,16448,16614,16755,16925,17155,16285,16338,16393,16475,16642,16784,16951,17182],
  [17891,17723,17916,17542,17749,17943,17429,17570,17778,17969,17346,17456,17638,17807,17996,17239,17293,17374,17485,17666,17836,18025,17211,17264,17319,17401,17513,17695,17862,18052],
  [18804,18594,18829,18453,18662,18856,18340,18481,18691,18882,18257,18367,18509,18720,18909,18150,18204,18285,18396,18537,18749,18938,18081,18175,18230,18312,18424,18566,18775,18965],
  [19715,19511,19740,19370,19537,19767,19257,19398,19566,19793,19174,19284,19426,19595,19820,19022,19076,19202,19313,19454,19624,19849,18994,19047,19102,19229,19341,19483,19686,19876],
  [20593,20425,20618,20284,20451,20645,20123,20312,20480,20710,20040,20198,20340,20509,20737,19933,19987,20068,20227,20368,20538,20766,19905,19958,20013,20095,20255,20397,20564,20793],
  [21503,21335,21528,21153,21361,21555,21040,21222,21390,21581,20957,21067,21250,21419,21608,20850,20904,20985,21096,21278,21448,21637,20822,20875,20930,21012,21124,21307,21474,21664],
  [22414,22246,22439,22065,22272,22466,21952,22093,22301,22492,21869,21979,22121,22330,22519,21762,21816,21897,22008,22149,22359,22548,21734,21787,21842,21924,22036,22178,22385,22575],
  [23325,23122,23350,22981,23148,23377,22868,23009,23177,23403,22785,22895,23037,23206,23430,22632,22686,22813,22924,23065,23270,23459,22604,22657,22758,22840,22952,23094,23296,23486],
  [24204,24036,24229,23895,24062,24294,23782,23923,24091,24320,23650,23809,23951,24120,24347,23543,23597,23678,23838,23979,24149,24376,23515,23568,23623,23705,23866,24008,24175,24403],
  [25180,24994,25208,24838,25023,25238,24674,24869,25055,25318,24582,24704,24900,25087,25348,24463,24523,24613,24736,24931,25119,25380,24432,24491,24552,24643,24806,24963,25148,25410]]
/-- Pairs 0–5 (both chains caps) use the skip-aware alphabet. -/
abbrev capPair (q : ℕ) : Bool := WeightedPairs.capPos q
def helperNo (q a b : ℕ) : ℕ :=
  (WeightedPairs.swapsOf (capPair q)).findIdx fun e => e.1 == (a,b)
def helperStart (q a b : ℕ) : ℕ :=
  (helperStarts.getD q []).getD (helperNo q a b) 0
def mappedPair (q a b : ℕ) : ℕ × ℕ :=
  (((WeightedPairs.swapsOf (capPair q)).find? fun e => e.1 == (a,b)).map Prod.snd).getD (a,b)
/-- The checksum sees the raw lanes; the correction adds the difference to the shifted weight. -/
def correction (q a b x y : ℕ) : ℕ :=
  4*(a+b+(if capPair q then 1 else 0)-WeightedPairs.pairWeight (capPair q) x y)
/-- A cap pair whose right chain hashes zero times skips that chain's pointer pair. -/
def isSkip (q y : ℕ) : Bool := capPair q && y == 0
def nextCode (q : ℕ) : Code := if q = 15 then root ++ decision else prologue (q+1)
/-- The continuation after a skipped right chain: the next prologue, rebased. -/
def skipNext (q : ℕ) : Code := skipPrologue (q+1)
/-- The right chain: its pointer pair and hashes, or nothing if it is skipped. -/
def rightCode (q y : ℕ) : Code :=
  if isSkip q y then skipNext q
  else enter (2*q+2) (work (2*q+1)) ++ List.replicate (y+1-lead q) .ECALL ++ nextCode q
def helperCode (q a b x y : ℕ) : Code :=
  [.ADDI .x27 .x27 (imm12 (correction q a b x y))] ++
    List.replicate (x+1-lead q) .ECALL ++ rightCode q y
/-- Redirect only the terminal interval of high raw digits; every ordinary suffix stays hashes. -/
def rowInstr (q d i : ℕ) : Instr :=
  let a := 15-i+lead q
  let b := 15-d
  if i < lead q ∨ mappedPair q a b = (a,b) then .ECALL else
    .JAL .x0 (BitVec.ofInt 21 (4*((helperStart q a b : ℤ)-
      (copiesIndex + groupOffset (group q) + 256*b + slotOffset q + i))))
def hashRow (q d : ℕ) : Code := (List.range (2 ^ fineWidth q)).map (rowInstr q d)
/-- A row: the left chain's hashes, then the right chain. A skip row's single `ADDI` is the
checksum correction `4 · 1` of its unit saving. -/
def copyCode (q d : ℕ) : Code :=
  hashRow q d ++ if isSkip q (15-d) then [.ADDI .x27 .x27 (imm12 4)] ++ skipNext q
    else enter (2*q+2) (work (2*q+1)) ++ List.replicate (15-d+1-lead q) .ECALL ++ nextCode q
/-- Bodies in physical order. At each boundary the old final row and new first row alternate. -/
def rowKeys (g c : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).map fun j => (g+4*j, 15-c)
def fragmentKeys : List (ℕ × ℕ) :=
  [(0,15), (8,15), (12,15), (4,15), (0,14), (8,14), (12,14), (4,14),
   (0,13), (8,13), (12,13), (4,13), (0,12), (8,12), (12,12), (4,12),
   (0,11), (8,11), (12,11), (4,11), (0,10), (8,10), (12,10), (4,10),
   (0,9), (8,9), (12,9), (4,9), (0,8), (8,8), (12,8), (4,8),
   (0,7), (8,7), (12,7), (4,7), (0,6), (8,6), (12,6), (4,6),
   (0,5), (8,5), (12,5), (4,5), (0,4), (8,4), (12,4), (4,4),
   (0,3), (8,3), (12,3), (4,3), (0,2), (8,2), (12,2), (4,2),
   (5,15), (0,1), (8,1), (12,1), (1,15), (4,1), (5,14), (0,0),
   (8,0), (12,0), (1,14), (4,0), (5,13), (9,15), (13,15), (1,13),
   (5,12), (9,14), (13,14), (1,12), (5,11), (9,13), (13,13), (1,11),
   (5,10), (9,12), (13,12), (1,10), (5,9), (9,11), (13,11), (1,9),
   (5,8), (9,10), (13,10), (1,8), (5,7), (9,9), (13,9), (1,7),
   (5,6), (9,8), (13,8), (1,6), (5,5), (9,7), (13,7), (1,5),
   (5,4), (9,6), (13,6), (1,4), (5,3), (9,5), (13,5), (1,3),
   (5,2), (9,4), (13,4), (1,2), (5,1), (6,15), (9,3), (13,3),
   (1,1), (2,15), (5,0), (6,14), (9,2), (13,2), (1,0), (2,14),
   (6,13), (9,1), (14,15), (13,1), (10,15), (2,13), (6,12), (9,0),
   (14,14), (13,0), (10,14), (2,12), (6,11), (14,13), (10,13), (2,11),
   (6,10), (14,12), (10,12), (2,10), (6,9), (14,11), (10,11), (2,9),
   (6,8), (14,10), (10,10), (2,8), (6,7), (14,9), (10,9), (2,7),
   (6,6), (14,8), (10,8), (2,6), (6,5), (14,7), (10,7), (2,5),
   (6,4), (14,6), (10,6), (2,4), (6,3), (14,5), (10,5), (2,3),
   (6,2), (14,4), (10,4), (2,2), (6,1), (14,3), (10,3), (2,1),
   (6,0), (14,2), (10,2), (2,0), (3,15), (11,15), (14,1), (7,15),
   (10,1), (15,15), (3,14), (11,14), (14,0), (7,14), (10,0), (15,14),
   (3,13), (11,13), (7,13), (15,13), (3,12), (11,12), (7,12), (15,12),
   (3,11), (11,11), (7,11), (15,11), (3,10), (11,10), (7,10), (15,10),
   (3,9), (11,9), (7,9), (15,9), (3,8), (11,8), (7,8), (15,8),
   (3,7), (11,7), (7,7), (15,7), (3,6), (11,6), (7,6), (15,6),
   (3,5), (11,5), (7,5), (15,5), (3,4), (11,4), (7,4), (15,4),
   (3,3), (11,3), (7,3), (15,3), (3,2), (11,2), (7,2), (15,2),
   (3,1), (11,1), (7,1), (15,1), (3,0), (11,0), (7,0), (15,0)]
def copyFragments : List (ℕ × Code) :=
  fragmentKeys.map fun (q, d) =>
    (groupOffset (group q) + 256 * (15-d) + slotOffset q, copyCode q d)
def insertFragment (a : ℕ × Code) : List (ℕ × Code) → List (ℕ × Code)
  | [] => [a]
  | b :: rest => if a.1 ≤ b.1 then a :: b :: rest else b :: insertFragment a rest
def addStubs : List ℕ → List (ℕ × Code)
  | [] => copyFragments
  | ip :: rest => insertFragment (ip-copiesIndex,reject) (addStubs rest)
def addGuards : List ℕ → List (ℕ × Code) → List (ℕ × Code)
  | [], parts => parts
  | bank :: rest, parts => insertFragment (guardStart bank-copiesIndex,guardCode) (addGuards rest parts)
def helperFragments : List (ℕ × Code) :=
  (List.range 16).flatMap fun q => (WeightedPairs.swapsOf (capPair q)).map fun ((a,b),(x,y)) =>
    (helperStart q a b-copiesIndex, helperCode q a b x y)
def addHelpers : List (ℕ × Code) → List (ℕ × Code) → List (ℕ × Code)
  | [], parts => parts
  | p :: rest, parts => insertFragment p (addHelpers rest parts)
def fragments : List (ℕ × Code) := addHelpers helperFragments (addGuards guardBanks (addStubs rejectStubs))
def assemble (cursor : ℕ) : List (ℕ × Code) → Code
  | [] => []
  | (off, body) :: rest =>
    List.replicate (off-cursor) (.JALR .x0 .x0 0) ++ body ++ assemble (off+body.length) rest
def assembledLength (cursor : ℕ) : List (ℕ × Code) → ℕ
  | [] => 0
  | (off, body) :: rest => off-cursor + body.length + assembledLength (off+body.length) rest

theorem assemble_length (cursor : ℕ) (parts : List (ℕ × Code)) :
    (assemble cursor parts).length = assembledLength cursor parts := by
  induction parts generalizing cursor with
  | nil => rfl
  | cons p rest ih => simp only [assemble, assembledLength, List.length_append, List.length_replicate, ih]

theorem assemble_admitted (cursor : ℕ) (parts : List (ℕ × Code))
    (h : ∀ p ∈ parts, p.2.all Riscv.admittedInstruction = true) :
    (assemble cursor parts).all Riscv.admittedInstruction = true := by
  induction parts generalizing cursor with
  | nil => rfl
  | cons p rest ih =>
    simp [assemble, List.all_append, h p (by simp),
      ih (p.1+p.2.length) (fun q hq => h q (by simp [hq])), Riscv.admittedInstruction]
def tables : Code := assemble 0 fragments
def verifier : Code := indexPhase ++ freeDispatch ++ freeRow ++ prologue 0 ++ tables

/-- The 32-byte index answer buffer, then the words loaded after the index query. -/
def dataImage : List (BitVec 8) :=
  List.replicate 32 0 ++ wordBytes (broadcast 0x3c3c) ++ wordBytes 257 ++ wordBytes (baseWord 0)
def image : Riscv.Image := ⟨verifier, dataImage⟩

theorem index_length : indexPhase.length = 31 := by decide +kernel
theorem code_length : verifier.length = 260838 := by
  simp only [verifier, List.length_append, tables, assemble_length]
  decide +kernel
theorem data_length : dataImage.length = 56 := by decide +kernel
theorem admitted : verifier.all Riscv.admittedInstruction = true := by
  have h : fragments.all (fun p => p.2.all Riscv.admittedInstruction) = true := by decide +kernel
  have ht := assemble_admitted 0 fragments (List.all_eq_true.mp h)
  have hf : (indexPhase ++ freeDispatch ++ freeRow ++ prologue 0).all Riscv.admittedInstruction = true :=
    by decide +kernel
  exact (List.all_append).trans (by rw [hf, tables, ht]; rfl)
theorem image_valid : image.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · change verifier.length ≤ 262144
    rw [code_length]; norm_num
  · change dataImage.length ≤ 1048576
    rw [data_length]; norm_num
  · exact List.all_eq_true.mp admitted

theorem image_size : image.byteSize < 1048576 := by
  simp only [Riscv.Image.byteSize, image, code_length, data_length]
  decide

end OptimalOTS.RiscvMixedProgram
