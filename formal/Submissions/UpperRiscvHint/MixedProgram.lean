import Submissions.UpperRiscvHint.Program
import Submissions.UpperRiscvHint.WeightedPairs

/-! The combined 310-cycle image uses skip-aware pairs on the variable-disclosure graph.
Chains 0–13 have 192-bit states and may disclose their tops without hashing.
The nineteen later states are 141 bits. Chain 32 commits a 144-bit top at the
start of the 7133-bit root, leaving its input pointer ready for the root hash.
Pairs 0–5 omit the pointer updates when their right chain performs zero hashes.
Pair 6 changes width between chains 13 and 14.

The loader supplies the capped view length L in x13. ANDI with -1924 preserves its
2048-bit bank and bits 2 through 6. An honest view supplies the dispatch base 6144
and displacement 4*(31-c) together, removing one ADD before the indirect jump.
The adjusted checksum equals the HASH call number exactly when S+c = 147 modulo 257, where S is
the shifted weighted sum (cap pairs 0–5 carry one extra unit each).
Other banks either fault outside the image or land in reserved rejection windows.
Counts at least 19 reject within the honest bank. Raw forms are padded into a guarded bank.

Pair 0's prologue occurs once, so its jump links a fixed address into x1: the root length is
that address plus 2041, and no constant load is needed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace OptimalOTS.RiscvMixedProgram

open RiscvZkvm.Rv64
open Riscv2Program (Code imm12 reject indexPrefix wordReg
  laneWordAddr hashBase laneBase wordBytes broadcast nop decision)

/-- The answer buffer of chain `k`, and for a cap also its value and state. -/
def outAddr (k : ℕ) : ℕ :=
  if k = 32 then 0x400038 else if k = 31 then 0x4003B0 else
    if k < 14 then 0x400058 + 56*k else if k < 28 then 0x400070 + 56*(k-14)
    else 0x400360 + 24*(k-28)
/-- View byte offset of chain `k`'s value, after the 16-byte nonce. -/
def wireByte (k : ℕ) : ℕ :=
  outAddr k + (if k < 14 ∨ k = 31 then 0 else 14) - 0x400040
/-- The input address while chain `k` hashes: its value in the view, then its state. -/
def work (k : ℕ) : ℕ := 0x400040 + wireByte k
/-- A bound containing every fixed payload position in an honest view. -/
def honestViewBits : ℕ := 7312
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
  [0,3706,7328,11303,145,3510,7165,11426,42,4182,7742,11364,84,4120,7804,11261].getD q 0
/-- The code index of the first copy: after the index phase, the free dispatch, the free row and
pair 0's prologue. -/
def copiesIndex : ℕ := 249
def copiesStart : ℕ := 4096 + 4 * copiesIndex
def copyStart (q d : ℕ) : ℕ :=
  copiesStart + 4 * (groupOffset (group q) + 256 * (copies q - 1 - d) + slotOffset q)
def landing0 (q : ℕ) : ℕ := copyStart q 0 + 4 * (2 ^ fineWidth q - 1)
/-- Lane 0 carries the bias for the masked tag: adding `6144 + 4*(31-c)` gives
residue 1 exactly when the shifted digit sum plus `c` is 147 modulo 257. -/
def baseLane (q : ℕ) : ℕ := min (landing0 (q % 4)) 65532 + if q % 4 = 0 then 92 else 0
def baseWord (g : ℕ) : ℕ :=
  (List.range 4).foldl (fun n j => n + baseLane (4 * g + j) * 2 ^ (16 * j)) 0
/-- A cap pair's first chain hashes once per digit unit, one hash fewer than a normal chain, so
its landing is one row later. -/
def lead (q : ℕ) : ℕ := if q ≤ 6 ∨ 15 ≤ q then 1 else 0
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
/-- The free chain and the caps hash first: the chain width is 192 bits through the left chain of pair 6. -/
def chainSetup : Code := [.ADDI .x11 .x0 192]
def indexPhase : Code :=
  indexPrefix ++ [.ECALL] ++ loadWords ++ freeCount ++
    (List.range 4).flatMap laneWord ++ freeSum ++ chainSetup

def enter (k previous : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((work k : ℤ) - previous)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ) - work k))]
/-- Pair 0's prologue, where the free dispatch lands for count 0. -/
def freeLanding : ℕ := 4096 + 4 * 245
/-- The link of pair 0's jump, from which the root length is computed. -/
def rootBase : ℕ := freeLanding + 16
/-- The free chain's pointers, then the jump `c` cells before pair 0's prologue. The padding
places pair 0's jump within `ADDI` reach of the root length. -/
def freeDispatch : Code :=
  enter 0 hashBase ++ .JALR .x0 .x6 (imm12 ((freeLanding : ℤ) - freeBase - 124)) ::
    List.replicate 147 nop
/-- Only pair 0's jump links: its prologue is the one copy at `freeLanding`. -/
def linkReg (q : ℕ) : Reg := if q = 0 then .x1 else .x0
/-- The table-row register `x28` changes only while `x12` points at neither chain of the pair. -/
def prologue (q : ℕ) : Code :=
  [.ADDI .x12 .x10 (imm12 ((outAddr (2*q+1) : ℤ) - work (2*q))),
     .LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q+1))),
     .ADDI .x10 .x12 (imm12 ((work (2*q+1) : ℤ) - outAddr (2*q+1))),
     .JALR (linkReg q) .x28 (imm12 (jumpImm q))]
/-- After a skipped right chain `x10` still holds the left chain's state, so the next
prologue measures `x12` from `work (2*q-1)`. Only used after cap pairs, so `q ≤ 6`. -/
def skipPrologue (q : ℕ) : Code :=
  [.ADDI .x12 .x10 (imm12 ((outAddr (2*q+1) : ℤ) - work (2*q-1))),
     .LHU .x28 .x12 (imm12 ((laneBase + 2*q : ℤ) - outAddr (2*q+1))),
     .ADDI .x10 .x12 (imm12 ((work (2*q+1) : ℤ) - outAddr (2*q+1))),
     .JALR (linkReg q) .x28 (imm12 (jumpImm q))]
/-- The last chain's state is the root input's first slot, so `x10` needs no move. The root length
is pair 0's link plus 2041. -/
def root : Code := sumCheck ++ [.ADDI .x11 .x1 (imm12 (7133 - (rootBase : ℤ))), .ECALL]
def pairCap (q : ℕ) : ℕ := if q < 12 then 24 else 23
/-- Each unexpected length bank has 32 rejection targets and a preceding rejection stub. -/
def guardStart (bank : ℕ) : ℕ := 214 + 512*(bank-3)
def guardBanks : List ℕ := (List.range 509).map (· + 4)
def rejectStubs : List ℕ := guardBanks.map (fun bank => guardStart bank - 3)
def guardCode : Code := (List.range 32).map fun d =>
  .BEQ .x0 .x0 (BitVec.ofInt 13 (-12 - 4*(d : ℤ)))
def stubFor (ip : ℕ) : ℕ :=
  (rejectStubs.find? fun (s : ℕ) => decide (-4096 ≤ 4*((s : ℤ)-ip) ∧ 4*((s : ℤ)-ip) < 4096)).getD 723
def rejectJump (ip : ℕ) : Instr :=
  .BEQ .x0 .x0 (BitVec.ofInt 13 (4*((stubFor ip : ℤ)-ip)))
/-- The free cell `c` instructions before pair 0's prologue: a hash of the free chain, or for
`c ≥ 19` a jump to a rejection stub. -/
def freeCell (c : ℕ) : Instr := if c < 19 then .ECALL else rejectJump (245 - c)
def freeRow : Code := [nop] ++ (List.range 63).map fun p => freeCell (63 - p)
/-- Fixed placements of the 492 redirected pairs (32 per cap pair, 30 per normal pair), in
`WeightedPairs.swapsOf` order. -/
def helperStarts : List (List ℕ) :=
 [[2472,1958,2495,1471,1982,2520,870,1127,1497,2009,2669,466,930,1187,1641,2155,2729,415,613,956,1384,1701,2215,2926,356,440,673,983,1444,1898,2412,2986],[5580,5091,5603,4748,5163,5677,3527,4491,4854,5262,5776,3243,4038,4552,4906,5366,5878,3036,3440,4342,4579,5005,5420,5934,3013,3183,3500,4392,4649,5066,5519,6033],[8627,7856,8650,7149,8113,8723,6547,6804,7219,8140,8785,6290,6608,6902,7476,8370,8884,6117,6390,6634,6962,7636,8466,8980,6094,6191,6448,6705,7122,7733,8528,9042],[10940,10522,11036,10169,10584,11098,9556,9813,10195,10683,11197,9299,9655,9912,10265,10708,11223,9164,9398,9681,10008,10327,10779,11698,9141,9237,9494,9751,10070,10426,10841,11725],[13780,13373,13887,12983,13435,13949,12407,12726,13116,13497,14144,12212,12469,12752,13178,13630,14206,12088,12239,12602,12859,13240,13692,14268,11955,12150,12345,12664,12921,13265,13754,14295],[15987,15838,16010,15708,15862,16035,14915,15606,15734,15889,16118,14720,14977,15632,15761,15914,16144,14463,14782,15296,15659,15788,15935,16168,14401,14658,14808,15323,15681,15813,15961,16195],[16911,16743,16936,16553,16769,16963,16440,16630,16798,16989,16357,16467,16658,16827,17016,16250,16304,16385,16496,16686,16856,17045,16222,16275,16330,16412,16524,16715,16882,17072],[17822,17654,17847,17473,17680,17874,17360,17501,17709,17900,17277,17387,17529,17738,17927,17170,17224,17305,17416,17557,17767,17956,17142,17195,17250,17332,17444,17586,17793,17983],[18733,18530,18758,18389,18556,18785,18276,18417,18585,18811,18193,18303,18445,18614,18838,18040,18094,18221,18332,18473,18678,18867,18012,18065,18166,18248,18360,18502,18704,18894],[19612,19444,19637,19303,19470,19702,19190,19331,19499,19728,19058,19217,19359,19528,19755,18951,19005,19086,19246,19387,19557,19784,18923,18976,19031,19113,19274,19416,19583,19811],[20523,20355,20548,20214,20381,20575,20058,20242,20410,20601,19975,20085,20270,20439,20628,19868,19922,20003,20114,20298,20468,20657,19840,19893,19948,20030,20142,20327,20494,20726],[21434,21266,21459,21086,21292,21486,20973,21114,21321,21512,20890,21000,21142,21350,21539,20783,20837,20918,21029,21170,21379,21568,20755,20808,20863,20945,21057,21238,21405,21595],[22346,22140,22371,21999,22166,22398,21886,22027,22195,22424,21803,21913,22055,22262,22451,21652,21750,21831,21942,22083,22291,22480,21624,21677,21776,21858,21970,22112,22317,22507],[23224,23056,23286,22915,23082,23313,22802,22943,23111,23339,22671,22829,22971,23140,23366,22564,22618,22699,22858,22999,23169,23395,22536,22589,22644,22774,22886,23028,23195,23422],[24136,23968,24161,23827,23994,24188,23669,23855,24023,24214,23586,23696,23883,24052,24241,23479,23533,23614,23725,23911,24081,24310,23451,23504,23559,23641,23798,23940,24107,24337],[25133,24947,25161,24733,24976,25191,24608,24822,25008,25220,24516,24638,24853,25040,25250,24397,24457,24547,24670,24884,25072,25334,24366,24425,24486,24577,24701,24916,25101,25364]]
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
/-- Pair 6 switches to the narrow width between its two chains. -/
def tailLead (q : ℕ) : ℕ := if q < 6 ∨ 15 ≤ q then 1 else 0
def between (q : ℕ) : Code :=
  (if q = 6 then [.ADDI .x11 .x0 141] else []) ++ enter (2*q+2) (work (2*q+1))
/-- The right chain and continuation, omitting pointers and hashes for a skipped chain. -/
def rightCode (q y : ℕ) : Code :=
  if isSkip q y then skipNext q
  else between q ++ List.replicate (y+1-tailLead q) .ECALL ++ nextCode q
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
    else between q ++ List.replicate (15-d+1-tailLead q) .ECALL ++ nextCode q
/-- Bodies in physical order. At each boundary the old final row and new first row alternate. -/
def rowKeys (g c : ℕ) : List (ℕ × ℕ) :=
  (List.range 4).map fun j => (g+4*j, 15-c)
def fragmentKeys : List (ℕ × ℕ) :=
  [(0,15),(8,15),(12,15),(4,15),(0,14),(8,14),(12,14),(4,14),(0,13),(8,13),(12,13),(4,13),(0,12),(8,12),(12,12),(4,12),(0,11),(8,11),(12,11),(4,11),(0,10),(8,10),(12,10),(4,10),(0,9),(8,9),(12,9),(4,9),(0,8),(8,8),(12,8),(4,8),(0,7),(8,7),(12,7),(4,7),(0,6),(8,6),(12,6),(4,6),(0,5),(8,5),(12,5),(4,5),(0,4),(8,4),(12,4),(4,4),(0,3),(8,3),(12,3),(4,3),(0,2),(8,2),(12,2),(4,2),(5,15),(0,1),(8,1),(12,1),(1,15),(4,1),(5,14),(0,0),(8,0),(12,0),(1,14),(4,0),(5,13),(13,15),(9,15),(1,13),(5,12),(13,14),(9,14),(1,12),(5,11),(13,13),(9,13),(1,11),(5,10),(13,12),(9,12),(1,10),(5,9),(13,11),(9,11),(1,9),(5,8),(13,10),(9,10),(1,8),(5,7),(13,9),(9,9),(1,7),(5,6),(13,8),(9,8),(1,6),(5,5),(13,7),(9,7),(1,5),(5,4),(13,6),(9,6),(1,4),(5,3),(13,5),(9,5),(1,3),(5,2),(13,4),(9,4),(1,2),(5,1),(6,15),(13,3),(9,3),(1,1),(2,15),(5,0),(6,14),(13,2),(9,2),(1,0),(2,14),(6,13),(13,1),(10,15),(9,1),(14,15),(2,13),(6,12),(13,0),(10,14),(9,0),(14,14),(2,12),(6,11),(10,13),(14,13),(2,11),(6,10),(10,12),(14,12),(2,10),(6,9),(10,11),(14,11),(2,9),(6,8),(10,10),(14,10),(2,8),(6,7),(10,9),(14,9),(2,7),(6,6),(10,8),(14,8),(2,6),(6,5),(10,7),(14,7),(2,5),(6,4),(10,6),(14,6),(2,4),(6,3),(10,5),(14,5),(2,3),(6,2),(10,4),(14,4),(2,2),(6,1),(10,3),(14,3),(2,1),(6,0),(10,2),(14,2),(2,0),(15,15),(3,15),(10,1),(11,15),(14,1),(7,15),(15,14),(3,14),(10,0),(11,14),(14,0),(7,14),(15,13),(3,13),(11,13),(7,13),(15,12),(3,12),(11,12),(7,12),(15,11),(3,11),(11,11),(7,11),(15,10),(3,10),(11,10),(7,10),(15,9),(3,9),(11,9),(7,9),(15,8),(3,8),(11,8),(7,8),(15,7),(3,7),(11,7),(7,7),(15,6),(3,6),(11,6),(7,6),(15,5),(3,5),(11,5),(7,5),(15,4),(3,4),(11,4),(7,4),(15,3),(3,3),(11,3),(7,3),(15,2),(3,2),(11,2),(7,2),(15,1),(3,1),(11,1),(7,1),(15,0),(3,0),(11,0),(7,0)]
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
theorem code_length : verifier.length = 260854 := by
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
