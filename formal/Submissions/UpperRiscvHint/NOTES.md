# Hinted RISC-V: 316 cycles through masked dispatch

The 317-cycle image masked the view length to obtain a displacement, then added
the free-chain base. The new mask obtains both in one instruction. The OTS,
accepted index set, signature format, state widths and root input are unchanged.

## Mask and guarded targets

The loader supplies `L = min(view.length, 1048577)`. Let `bank = L / 2048`,
`d = (L % 128) / 4` and `c = 31-d`. `ANDI x6 x13 -1924` computes
`2048*bank + 4*d`, preserving bits 2 through 6 and bits above 10. Honest view
lengths have bank 3, so `JALR x0 x6 -1768` lands at `4500 - 4*c` directly.
The former ADD is replaced by padding after the jump, preserving the free row
and pair 0's prologue. The checksum bias is 239 instead of 18, accounting for
the base now included in the masked tag.

Banks 0 through 2 fault outside the image. For each bank 4 through 512, the 32
possible targets occupy a reserved instruction window beginning at
`70 + 512*(bank-3)`. Every instruction jumps to a three-instruction rejection
stub immediately before its window. The 256 chain bodies are packed around
these windows; kernel-checked fragment coverage and non-overlap justify every
landing. Unused gaps contain a jump to the faulting zero address.

Raw encodings are padded to at least 8192 bits, as well as to a multiple of 128.
Their projection still recovers the original signature, including oversized
signatures. They now select a guarded bank and halt rejecting. `HintView`
proves the projection, expansion, faithfulness and accepted-view soundness;
`MaskedDispatch` covers every possible bank and `MixedVerifier` proves the
accepting bound for arbitrary views and fuel.

Exact accepting cost: **316 = 33 index + 3 free dispatch + 145 digit units +
135 pair/root/decision overhead**, comprising 178 compression cycles and 138
ordinary instructions. There are 260,710 instructions and 64 data bytes:
**1,042,904 bytes**, strictly less than 1 MiB.

## Validation

The complete certificate and image-size theorem build with Lean 4.33.1 against
contract `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c`.
Exact statement/primitive comparison and permitted-axiom checking pass. A fresh
Lean kernel replay passes all 22,494 exported declarations. Comparison and replay
take 238.72 seconds wall clock with sampled peak PSS of 9.96 GiB.
Source policy passes all 86 files, and all 18 protected build files match the
pinned contract.

The byte-memory interpreter runs the actual Lean-exported image, which exactly
matches the independently assembled prototype. All 21,305 cases pass: 4,288
accepting transcripts, 256 ignored-byte variants, 395 length cases, 13 raw
forms and 16,353 out-of-bank cases. Accepting oracle queries match the abstract
forest in order, and each accepting run costs 316 cycles. An arithmetic check
also covers all 1,048,578 possible capped length values.

The official local runner fails closed at Landlock preflight on this host.
Standalone development checks are not a hosted verdict; hosted verification
is pending.

The constrained-target layout adapts the address-masking idea described by
[McCamant and Morrisett (2006)](https://people.csail.mit.edu/smcc/projects/pittsfield/pubs/usenix-sec-2006/pittsfield.html).
The OTS layout and cycle saving here are our implementation and proof.
The following sections record the historical 317, 318 and 320 versions.

---

# Hinted RISC-V: 317 cycles with a count encoded in the view length

This extends the locally checked 318-cycle boundary-cap construction below.
The two new caps save two hashes relative to lucemans's published 320-cycle
submission. Encoding the free count in the view length saves another ordinary
instruction. The signature scheme, accepted index set and 5504-bit signature
format are the same as in the 318-cycle construction.

## Count encoding and checks

For free count `c < 16`, the honest view has `7296 + 4*(31-c)` bits, between
7360 and 7420. The loader supplies `L = min(view.length, 1048577)` in `x13`.
The single instruction `ANDI x6 x13 124` gives `4*d`, with `d = (L % 128)/4`.
The projected count is `c = 31-d`, so every view has a count between 0 and 31.
The checksum uses ADD with a revised lane bias (18 rather than 49); it equals
the HASH call number exactly when the index digit sum plus `c` is 145 modulo
255. The free dispatch uses ADD and an adjusted jump immediate. It still lands
exactly `c` instructions before pair 0's prologue. Counts 16 through 31 reject.
One unreachable padding instruction preserves every subsequent table address.

Raw forms encode `signature ++ [true] ++ zero padding` to a multiple of 128
bits. The pure projection removes trailing zeros and the true marker, recovering
any signature exactly. A raw view below the loader cap has count 31. Above the
cap, `L = 1048577` also has count 31. Thus both cases halt rejecting, as required
by faithfulness; the length register cannot send a raw form to a faulting path.
The machine no longer depends on view byte 64.

`HintView` proves projection/expansion, raw rejection, accepted-view soundness
and honest acceptance. `MixedIndexPhase` proves the loader-length arithmetic;
`MixedFree` proves every dispatch target; `MixedVerifier` bounds accepting
executions over arbitrary views and fuel. The proof uses layout lemmas without
reducing the variable-length bit list during elaboration.

Exact accepting cost: **317 = 33 index + 4 free dispatch + 145 digit units +
135 pair/root/decision overhead**, comprising 178 compression cycles and 139
ordinary cycles. The root remains 884 bytes (14 compression blocks). The image
has 15,750 instructions and 64 data bytes: **63,064 bytes**.

## Validation

The full certificate and image-size theorem build with Lean 4.33.1 and trusted
contract `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c`. Exact exported statement,
definition and primitive comparison passes against the rendered 317 challenge.
The three exported declarations use only `propext`, `Classical.choice` and
`Quot.sound`. A fresh Lean kernel replay passes all 22,423 exported declarations; comparison
and replay take 98.03 seconds wall clock, with sampled peak PSS of 5.05 GiB.

Independent byte-memory execution of the Lean-exported image matches all hash
queries of the abstract forest for 768 accepting fixtures. Additional checks
cover 256 variations of the ignored former count byte, 395 length cases
(including half-byte views and loader-cap boundaries), and 13 raw forms,
including oversized signatures. Every accepting fixture costs 317 cycles.
These deterministic oracle fixtures supplement the universal Lean certificate.

The official local verifier fails closed because Landlock is unavailable on
this host. Standalone export/comparison/kernel checks are not a hosted verdict;
hosted verification is pending.

This derives from lucemans's [320-cycle submission](https://ots.golf/submissions/0380117cf0362ee8535e725c194cf03a),
source `3bfb3022de749d253c8faa5b5068c72b91e5bb06` (PR 53). The 318 and 320 notes
below describe their historical versions; this section specifies the current
input encoding, cost and validation.

---

# Hinted RISC-V: 318 cycles with caps at both root boundaries

This extends lucemans's verified 320-cycle submission, source
`3bfb3022de749d253c8faa5b5068c72b91e5bb06` (PR 53), by turning chains 31 and 32 into
144-bit caps. Each can now have zero hashes. Together they save two hashes on
every accepting execution; the accepted digit set and 5504-bit signatures stay
unchanged.

Chain 32 occupies the bottom of the root. Its state and top use answer bits
`[112,256)`, so the final chain's input pointer is already the root pointer.
Chain 31 occupies the top of the root, uses answer bits `[0,144)`, and has its
answer buffer moved up eight bytes. Chain 30's top grows from 192 to 256 bits
to fill the intervening gap. These two boundary caps need no additional spacer
chains. The root is 884 bytes (7072 bits), still 14 compression blocks. The lane
scratch area moves to `0x4003D0` to avoid the final answer write.

Caps are chains 0 through 12, 31 and 32; chain widths remain 192 bits for 0
through 12 and 144 bits for 13 through 32. The final dispatch pair is now a
cap pair. The free count still comes from view byte 64, and honest views remain
7248 bits. Root resampling now allows a fiber of size `2^112` instead of `2^64`;
the existing security bound already accommodates this and is proved in Lean.

Exact accepting cost: **318 = 34 index + 4 free dispatch + 145 digit units +
135 pair/root/decision overhead**. This is 178 hash-compression cycles and 140
ordinary cycles. The image contains 15,750 instructions and 64 data bytes,
**63,064 bytes** total.

Local validation (2026-09-27, trusted contract
`8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c`, Lean 4.33.1):

- The full `submission.Certificate 318` and `image_size` build successfully.
- Exact exported statements, definitions and primitives match the rendered
  318 challenge; only `propext`, `Quot.sound` and `Classical.choice` occur as axioms.
- An unchanged fresh Lean kernel replays all 22,416 exported declarations.
  Export took 6.51 seconds; comparison and replay took 97.88 seconds wall clock.
- An independent emulator executes the exported image and matches the complete
  abstract hash transcript for 768 accepting fixtures, including both new
  zero-count caps. It also checks all 256 free-byte values and six raw views.
- The official local verifier refuses to run because this host lacks Landlock.
  These are standalone local proof checks, not a hosted competition verdict.

The previous 320-cycle notes follow as historical context. Their numerical
costs, cap classification and boundary layout describe that predecessor; the
current construction is specified above and by the Lean definitions.

---

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
