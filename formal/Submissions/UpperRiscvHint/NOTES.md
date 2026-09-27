# Hinted RISC-V: a free chain, 320 cycles

This entry changes one thing in the 321-cycle free-chain entry: the chain that hashes last,
normal chain 32, moves to the bottom of the root region. Its 144-bit value is at region byte 0
and its 32-byte answer buffer starts eight bytes lower, in the high word of the nonce, which the
machine reads only for the index query. After its last hash `x10` already points at the root
input, so the root setup `ADDI x10` is gone. The root input is still 888 bytes (14 blocks).

The scheme: chain 0 is the free chain, a 192-bit cap whose count is `c = 145 - S`, where `S` is
the sum of the 32 index digits. Chains 1 to 12 are the index caps (digits 0 to 11, pairs 0 to 5)
and chains 13 to 32 are the 144-bit normal chains (digits 12 to 31, pairs 6 to 15). Pair `q` is
chains `2q + 1` and `2q + 2`. The accepted digit set is every vector with all sixteen pair sums at
most 24 and `S` in `[130, 145]`. A cap's next state is answer bytes `[0,24)` and its top is its
final state, so a count-0 cap reveals its top. A normal's next state is answer bytes `[8,26)`.

## Layout

The view is at `0x400030`: the nonce, then the root region from `0x400040`.

| Region bytes | Content |
|---|---|
| `[0, 24)` | normal 32: value at byte 0, top = answer bits `[64, 256)` (buffer at `-8`) |
| `[24, 48)` | free chain, in place |
| `48 + 56 j` | normal `13 + j`, 32-byte buffer, value 8 bytes in (`j < 12`) |
| `80 + 56 j` | cap `1 + j`, in place (`j < 12`) |
| `720 + 24 t` | normal `25 + t`, buffer, value 8 bytes in (`t < 7`) |

The root input is the region in memory order (`Names.rootCat`, `slotChain`). View byte 64
(region byte 48, a pad byte of normal 13's buffer) is the free count `v`, and
`viewDigit view = v / 4`. A view with `viewDigit view ≥ 16` is the raw form, with the signature
after view bit 520 (`HintView.rawView`). The signature order is the graph order: the nonce, the
free chain, then chains 1 to 32 (`ViewLayout.viewPayload`). The honest view is 7248 bits.

Every hash writes 32 bytes at an 8-aligned `x12`, and each top keeps 24 bytes, so every chain
spills 8 bytes into a neighbour. Normal 32 spills downwards into the nonce, every other chain
upwards. A cap can have count 0, so nothing may spill into it: each of the 12 index caps has a
32-byte normal below it. That gives 888 = 33 · 24 + 12 · 8 bytes.

## Machine

- Index phase (34): `LD x30; LD x31` save the key, the index query is hashed, then eight loads
  (four answer words, the lane mask, 255, the dispatch base word, the free base 6144 into `x1`),
  `LBU x6 x10 112; ANDI x6 x6 0xFC`, the four lane words, `SUB x27 x27 x6`,
  `REMU x5 x27 x2` and `ADDI x11 x0 192`. Lane 0 carries 49, so the residue is 1, the HASH call
  number, exactly when `S + c = 145` (`MixedIndexArith.free_remainder_iff`). Any other residue
  traps at the first hash.
- Free dispatch (4): `ADDI x10; ADDI x12; SUB x28 x1 x6; JALR x0 x28 -1644` lands at code
  address `4500 - 4 c`. The free row holds 48 jumps to the rejection stub at 655 for `c ≥ 16` and
  15 `ECALL`s, then pair 0's prologue at code index 101.
- Pairs: prologue `ADDI x12 x10; LHU x28 x12; ADDI x10 x12; JALR` (pair 6's prologue first sets
  the width 144), a hash row of 16 entries, the pointer move and the second chain's hashes. Cap
  pairs land one row later (`lead`). Forbidden pair landings branch to eight rejection stubs.
- Root and decision (20): `ADDI x11 x1 960; ECALL` (14 blocks), then
  `LD x26; LD x27; XOR x5 x26 x30; XOR x10 x27 x31; ECALL; JALR x0 x0 0`. The public key's high
  word has bit 0 flipped (`GScheme.flipHi`): HALT accepts the honest root, rejects a root equal to
  the stored key, and every other root traps.

Accounting on every accepting path: **320** = 34 index + 4 free dispatch + `c` free hashes +
`137 + S` for the pairs, the root and the decision (`CappedCost.cost_allowed`), with
`S + c = 145`. The image is 15,751 instructions and 64 data bytes (63,068 bytes).

## Proof

`MixedVerifier.image_refines_trap` proves that the machine on every view refines `trapVerify`
for every fuel of at least 1337 instructions, and that every accepting path costs at most 320
cycles (`Refines` bounds accepting paths only; a forbidden pair after many passing pairs costs
more, but never accepts). `trapVerify` hashes the index input, then returns `some false` for
`viewDigit view ≥ 16`, the staged run `freeDecision` when `freeDigit index = viewDigit view`,
`none` for another positive count (the free chain's first hash traps), and otherwise the first
hashing cap pair's verdict (`firstBusy`, `walk_refines`). `HintTrap.certificate` turns the
refinement into `Expands`, `Faithful`, `Sound` and `CyclesAtMost 320`; `HintView` proves the view
facts (`layoutView_compress`, `raw_compress`, `trap_raw`, `trap_sound`, `trap_accepts`).

The graph change is two definitions. `Names.topOf` commits answer bits `[topOff k, topOff k +
topBits k)`, with `topOff 32 = 64` and 0 otherwise, and `slotChain` puts normal 32 in root slot 0.
Security resamples the last answer of chain 32 for the root query (`Values.coordOf rh`): the
lowest root slot is a 192-bit window of that answer, so at most `2^64` answers hit a given root
input (`card_updHash_rc_le`). On the machine side `MixedLayout.topAddr k = outAddr k +
topOff k / 8` is where a top lies, and `MixedMemory.Completed` is stated at `topAddr`.

Module map. Scheme and security: `Names`, `Tree`, `Cuts`, `FixedChoice`, `Values`, `Scheme`,
`GScheme`, `Keygen*`, `FreshKeygen`, `Correctness`, `Reconstruct`, `Events`, `Resample`,
`GoodRec`, `StageB`, `Assembly`, `Main`, `Potentials`, `Row*`, `EncCharges`, `Sign*`, `Digits`,
`PackFiber`, `Valid`, `PairCount`, `Availability`; the typed-algorithm bridge `TypedScheme`,
`Adapter`, `AlgorithmCosts`, `Deterministic`, `Resources`, `ForestAlgorithm`, `WireAdapter`,
`Wire`, `ForestVerifier*`, `Layout`, `Reader`; staged rejection `StagedVerifier`,
`RejectAdapter`. Machine: `Program`, `MixedProgram` (the image), `MachineFacts`,
`MachineMemory`, `LoaderProof`, `BlockExecution`, `Refines`, `Lanes`, `MixedIndex*`,
`MixedDispatchArith`, `MixedContext`, `MixedLayout`, `ViewLayout`, `MixedMemory`, `MixedCode`,
`MixedChain*`, `MixedHashStep`, `MixedRoot`, `MixedDispatch`, `MixedLanding`, `MixedPair`,
`MixedFree`, `MixedVerifier`. Hint track: `HintTransfer`, `HintTrap`, `HintView`, `Solution`.

## Validation

- `RVH_STAGE=D python3 rvh.py` (stage D of `.tmp/portrvh/rvh.py`, in
  `.tmp/clean/CleanRvh-scratch/model`) is the generator; `compare.py` confirms that the Lean
  image equals it (15,751 instructions, 64 data bytes, sha256 `47f5de0c…`).
- `RVH_STAGE=D python3 transcript.py` passes 13,299 cases: all pair and digit landings with `S`
  in the window, every free byte `v` on accepted views, the residue aliases `S + c = 145` with
  `c` in `16 … 63`, sum aliases, every bit flip of one honest view, view lengths, raw forms, and
  a wrong key and message. Honest runs never trap and every accepting run costs exactly 320.
- `lake build Submissions.UpperRiscvHint.Solution` passes; `certificate : submission.Certificate
  320` depends on `propext`, `Classical.choice` and `Quot.sound` only.

## Rejected directions, checked against this layout

- Fewer root blocks: 13 blocks need at most 832 bytes. With 33 chains of 24 bytes, every
  count-0-capable cap needs 8 dead bytes below it unless it sits next to a downward spiller. Caps
  that keep answer bytes `[8,32)` can pair up (`[8,32)` cap below a `[0,24)` cap), but 13 caps
  still need 6 dead 8-byte units: 840 bytes. Turning one cap into a normal reaches 832 bytes and
  costs one hash: net 0.
- 64-bit nonce (one more cap, −1): the security proof's `RowHyp.nonce_eq : nonceBits = idxBits`
  must be generalised first.
- A view digit without `ANDI`: `v` and `v + 1` alias under `JALR`; the caps that exclude the alias
  leave availability below 0.1 against 88.7 needed.
- Digits or jump targets delivered in the view: checking a dispatch word costs 4 against 3 to
  compute it, and an unchecked target breaks `CyclesAtMost`.
- Register reuse in the index phase: the modulus must be 255 (`2^16 ≡ 1` and `1024 ≡ 4`), the
  free base must lie within `JALR` reach of the free row, and the view length `x13` is
  prover-chosen once the length check is gone, so no load can be shared.
- Removing the width change: caps need 192-bit states for canonicity, normals 144 bits for the
  signature budget, so at least one `ADDI x11` remains.

## Lineage

- **321**: free chain; the count byte is the raw-form flag; accepting paths only are costed.
- **324**: cap chains (a digit costs `d` hashes, digit 0 reveals the top), 14-block root.
- **337**: in-place views in trap mode, the flipped-key `XOR` decision, the raw form rejected
  before any trap. Hinted identity port of Nicolas Consigny's 349-cycle deterministic verifier,
  [PR #40](https://github.com/leanEthereum/ots.golf-submissions/pull/40), source
  `162d80e00c6f9263389c9d87bbdbfc799d60a582`. Design study and implementation: Claude Opus 5.5.
- **349**: restricted fixed-rank antichain (pair caps 23/24/30, sum 158) and the address
  checksum modulo 255; `StagedVerifier` and `RejectAdapter` for exact staged rejection. Extends
  Nicolas Consigny's 353 (PR #34, `0b21c2e8…`). Assisted by Codex.
- **353**: exact availability without a key-generation collision charge, 144/192-bit states.
  Extends Nicolas Consigny's 358 (PR #33, `b6dbcb94…`). Assisted by Codex.
- **358**: one dispatch base (mask `0x3c3c`). Extends the 359 of PR #32 (`60a13667…`), credited
  to Nicolas Consigny. Assisted by Codex.
- **359**: two dispatch bases. Extends scaraven's 360 (#30, `16be83e7…`). Assisted by Codex.
- **360**: four more chains hashed in place above the cell. Extends dhsorens's 364-cycle
  ascending cell grid (PR #28). Design Claude Fable 5.1, implementation Claude Opus 5.5.
- **364**: ascending cell grid and wire permutation. Extends the 372-cycle dense dispatch
  (PR #27), which builds on Alexander Hicks's 377-cycle mixed-width image and dhsorens's paired
  dispatch. Assisted by Claude Fable 5.1.
