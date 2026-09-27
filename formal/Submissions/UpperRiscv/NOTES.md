# Descending chain buffers: 345-cycle candidate

This extends the 346-cycle non-hinted source in the submissions repository
(`c238c85e4e21e990e9ff1534a611f01e8d7f948e` checkout baseline).

## Construction and savings

The signature still contains a 128-bit nonce, 21 values of 144 bits, 12 values
of 192 bits, and the free-count byte: 5464 bits total. Chain 0 hashes `v + 1`
times. Sixteen pairs consume the 32 four-bit index digits. The accepted
language is unchanged: `S + v = 146`, `v < 16`, with pair-sum caps of 20 for
pairs 0–4, 21 for 5–9 and 30 for 10–15. The exact accepted-index count remains
32768630519944966874703949789741158. The availability and security arguments
use the same width bounds and accepted language.

Execution-order chains 0–20 now have 144-bit states and chains 21–32 have
192-bit states. Their answer buffers descend from root offset 768 to 24 in
24-byte steps, with the last buffer at offset -8. Chain 32 is the sole cap;
its state and root slot start at offset 0. It may take zero hashes. Each of
the other chains takes its digit plus one hashes. Ten chains expand, as in
the prior image.

The root begins at the payload address `0x400040`. It contains 33 top slots
in reverse execution order: 24 bytes each, except chain 31's 32-byte slot.
The total is 800 bytes / 6400 bits / 13 compressions. The final working
pointer already equals the root address. The root code is therefore just
`ADDI x11, x13, 936; ECALL`, followed by the existing decision.

One fewer cap adds a mandatory hash. Grouping widths removes one width-change
instruction, cancelling that cost. Removing the root pointer update saves
one further instruction. A full-length accepting run uses 192 compressions
and 153 ordinary instructions, totalling 345 cycles. The earlier image used
191 compressions and 155 ordinary instructions.

## Every raw input and memory safety

The root reads `a3 + 936` bits, where `a3 = min(signature length, 5505)`.
The six bytes after the root region are outside the loader's signature area
and all chain writes, and remain zero. Dispatch lanes move to `0x400380`,
above the root and tail. The length decision still requires `a3 < 5465`.
Thus short, partial-byte and oversized signatures all have an exact staged
oracle computation, including rejection after a matching root.

`MixedLayout` checks all unread-value and completed-slot disjointness facts,
cap placement, state slices, and the preserved tail. `MixedPayload` proves
that the initial tail is zero. `MixedChain*` preserves that invariant through
all hashes. `MixedRoot` uses `work 32 = regionAddr` to omit the pointer update.
The graph/wire mapping and the root commitment change with the layout; their
correctness and security are proved for these new definitions.

Code bodies and rejection stubs are repacked without overlap. Lane 0's bias
is 232. `MixedIndexArith` checks the wrapped checksum with the new bases.
`CappedCost.bound` proves that free-chain work plus the pairs and root costs
at most 310 after the 35-cycle index phase. It includes the first failed pair
and the alias `S + v = 401`; the free table rejects all count bytes at least
16, including the larger raw aliases. The certificate covers all executions,
not only accepting runs.

Key generation costs 1069 compressions; full-length verification costs 192.
The image contains 15,616 instructions and 88 data bytes: 62,552 bytes, below
the contract's 1 MiB cap.

## Validation

- The full `Submissions.UpperRiscv.Solution` build passes on the pinned
  Lean 4.33.1 contract.
- An independent byte-memory interpreter executes the actual Lean-exported
  image against a separate forest verifier. All 16,560 cases agree on the
  decision and exact ordered oracle queries; the maximum observed is 345.
  Cases cover all 4096 pair landings, all 256 raw count bytes, 336 checksum
  aliases, every raw bit length from 0 to 5506 and four large lengths, all
  5464 signature-bit flips, all key/message-bit flips, and 512 unforced
  random inputs. Programmed root matches exercise oversized rejection.
  SHA-256 supplies consistent test answers; the Lean proof establishes
  the universal and random-oracle claims.

- The pinned comparator's exact challenge-statement/primitive comparison and
  axiom check pass; the only permitted axioms are `propext`, `Quot.sound` and
  `Classical.choice`. Fresh Lean-kernel replay of all 22,241 exported
  declarations passes. This standalone check takes 186.385 seconds locally,
  with sampled peak proportional memory of 8,017,782,784 bytes.
- Source policy passes: 103 files, below 1 MiB of source. The development
  build's 18 protected formal files match contract
  `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c`.
- The unchanged official runner, using that contract and the pinned tools,
  fails closed at Landlock preflight before compilation on this host.
  The standalone checks above do not certify production isolation or the
  hosted time/memory envelope. No hosted verdict is claimed.

Implementation and proof adaptation: OpenAI Codex. The construction builds
on the predecessor work credited in the historical notes below.

Historical notes below refer to their original versions.

---

# Free count digit and two caps: 346-cycle candidate

This extends the 348-cycle candidate (length test folded into the decision).

## Construction

- 33 chains. The signature is 5464 bits: nonce 128, 21 chain values of 144
  bits and 12 of 192 bits (payload 5328 bits), then the count byte `v` (bits
  5456 to 5463). Chain 0 (the free chain) hashes `v + 1` times. The 32 index
  digits `d` go to 16 pairs of chains `2q+1`, `2q+2`.
- Accepted set: `S + v = 146` with `S` the index digit sum and `v < 16`. The
  pair caps are `20` for pairs 0 to 4, `21` for pairs 5 to 9 and `30` for pairs 10 to 15. The
  caps sum to 385, which excludes the alias `S + v = 401`.
- Chains 1 and 15 are caps: they hash `d` times instead of `d + 1`. A cap with
  digit 0 reveals its top. Its value lies on its root slot, and no other
  answer buffer covers that slot.
- The root region is 826 bytes from `0x3FFFA0`: the root slots of the 33
  chains in address order (18, 24 or 32 bytes each). The root query reads the
  first `a3 + 1144` bits, which is 6608 for a full signature and at most 6649
  (13 blocks). Past the region are six bytes: the high cap's answer bytes 18 to
  23 if it hashed, else the loaded signature. Every chain has its own value
  address, answer buffer and state offset (`MixedProgram` tables). 10 chains
  expand.

## Machine

- Index phase: 38 instructions and 35 cycles. `LD x1` loads 5465, which is
  both the dispatch base of the free chain and the decision bound.
  `LBU x29` and `SLLI` compute `4 v`. `SUB x27, x27, x29` runs before the
  `REMU` check. The lane words are at `0x4002E8`, above every answer buffer.
  Lane 0's base is raised by 167, so that the residue is zero exactly when
  `S + v = 146 (mod 255)`. The lane sum wraps three times for every input.
- Free chain: the first hash, then `SUB x28, x1, x29` and `JALR` into a
  255-entry table that ends at prologue 0. The entries for `v < 16` are hash
  steps. The others branch to the index phase's rejection.
- Pairs: the 348 dispatch, with a new column table (`place`), 12 rejection
  stubs, and 15-step rows for expanding or cap first chains.
- Decision: `SLTU x10, x13, x1` accepts only if `a3 < 5465`.

Accounting on an accepting run: 35 index + (6 + v) free chain + 137 pair
overhead + S pair hashes + 22 root/decision = 346, with `S + v = 146`. The
image has 15,719 instructions and 88 data bytes, which is 62,964 bytes.

## Proof

- `MixedIndexArith.count_remainder_iff` proves the count check.
  `MixedIndexPhase` proves the index phase.
- `MixedFree`: the free chain refines `entryNodes 0`, then the `v < 16`
  test, then `tableNodes 0`. `MixedFreeArith` proves the table facts.
- `MixedChain*`, `MixedPair`, `MixedPhase`: chains are indexed by execution
  position (`Fin 33`). The memory invariant (`ChainsInv`) keeps the unread
  values, the committed root slots and the six bytes past the region.
  `MixedLayout` proves the order constraints on every answer buffer by kernel
  decision (`unread_disjoint'`, `completed_disjoint'`, `tail_disjoint'`).
  `MixedMemory.memBits_region` assembles the region from the slots.
- `MixedRoot`: the root reads any 6656-bit value at the region, in at most
  13 blocks, then the decision.
- `CappedCost.bound`: `6 + v + pairs + 22 <= 311` on every path that passes
  the count check. `MixedVerifier.image_refines` gives at most 346 cycles on
  every execution.
- Scheme (`Names` to `FixedChoice`): each chain has a top node `tp k`, the
  root slot of its last answer. For the caps (chains 1 and 15) this slot is
  the state itself, so a zero cap digit reveals the top. The root input is the
  6608-bit region of the 33 tops in address order (`rootRegion_injective`).
  Keygen costs 1069 compressions and verification costs 191.
- Accepted set (`Valid`, `PairCount`): digit sum in `[131, 146]` and pair caps
  20×5, 21×5, 30×6. The free digit is `146 - sum`, so all 33 digits sum to 146
  and distinct cuts are incomparable. The exact count is
  32768630519944966874703949789741158, which is at least `89 · 2^108`
  (availability unchanged).
- Free digit: `GScheme.tag` appends the free digit as 8 bits, and the verifier
  rejects any other tag. An accepted forgery with the signed nonce and message
  has the same index and therefore the same tag. Freshness on bit strings
  thus reduces to freshness of the revealed values (`StageB.events_stB`).
- Security (`Values` to `Main`): the simulation event at level 31 compares
  the root slot (at least 144 bits, so at most `2^112` answers match).
  `events_ne` and `events_same` handle a revealed cap top. The bound becomes
  `κ(B − 1069) + 2δ` with `δ = 2 · 1057² · 2^-144`.
- Short and oversized signatures (`StagedVerifier`): at 5464 bits the staged
  verifier prunes to the forest verifier. With a valid index, the count check
  holds exactly when the byte is the tag (`count_iff_free`, `freeTag_iff`).
  Every other path is a constant `false` suffix. This covers the alias
  `v = 255`, digit sums in `[386, 401]` (pair caps sum to 385), a failed pair
  cap and `v ≥ 16`. Below 5464 bits, acceptance requires a root query of length
  `ℓ + 1144 ∈ [1144, 6608)` whose answer begins with the public key
  (`Values.SprShort`). Above 5464 bits, `a ≥ 5465` rejects on every path. The
  root query reads the six bytes past the region (`rootTail`).

## Validation

- An independent generator reproduces the Lean-exported image instruction for
  instruction (sha256 of the canonical JSON
  `90553ebb152a53f39853045b3fc8be9659245ff5e152851770633c3710e8c7b3`).
- 22,346 transcript executions against a chain-level staged reference, with
  the same oracle and programmed answers. They cover:
  - all 4,096 pair landings,
  - every count byte from 0 to 255,
  - the checksum aliases 401 and 656 at every first forbidden pair,
  - digit sums from 0 to 480,
  - all 5,464 bit flips of one honest signature,
  - every length from 0 to 5505, larger lengths up to 2^20, and oversized
    tails,
  - programmed short and oversized roots (accepted exactly at 5464 bits or
    less).
- Every execution made the same queries and gave the same verdict as the
  reference, and none trapped. The cycle count equalled the analytic path
  cost. The maximum was 346. An exact worst-case search over every execution
  gives 346.
- `lake build Submissions.UpperRiscv.Solution` succeeds. `certificate`
  (`Certificate 346`) and `image_size` use only `propext`, `Classical.choice`
  and `Quot.sound`. No hosted verdict is claimed.

---

# Length test folded into the decision: 348-cycle candidate

This extends the 349-cycle capped-rank record (PR #40). Earlier notes below
are historical snapshots.

## Machine change

- `lenBlock` is `LD x6, 72(x12)`, and the data word at offset 72 is 5505. The
  length `BEQ` and its three-instruction rejection are gone, so the index phase
  is 35 instructions and 32 cycles. Nine NOPs (not five) follow prologue 0, so
  `copiesStart`, every landing, the dispatch bases, the jump immediates and the
  rejection stubs are unchanged.
- `root` is `ADDI x11, x13, 639`: the root query reads the first `a3 + 639` bits
  of the 768-byte region, with `a3 = min(|σ|, 5505)`. That is 6143 bits for a
  full signature and never more than 6144, so at most twelve blocks.
- `decision` accepts with `SLTU x10, x13, x6` instead of `ADDI x10, x0, 1`. Both
  root words must match the public key, and then the verdict is `a3 < 5505`.
  An oversized signature (`a3 = 5505`) is rejected on every oracle path, and
  `x10` is 0 or 1 at every HALT.

Accounting: **32 + 295 + 21 = 348** on an accepting run. Every run is bounded
by 348: the index phase is 32 cycles, the chain phase is bounded by
`CappedCost.bound` (316 including the root and the decision), and the root
costs `blockCost (a3 + 639) ≤ 12`.

## Proof change

- `Ctx` carries the length `a` (`x13 = a`, `a ≤ 5505`, `x6 = 5505`); `x6` is a
  frame register of every chain step. `indexPhase_refines` has no length
  branch. `rootDecision_refines` hashes `(rootRegion tops).setWidth (a + 639)`
  and proves the `SLTU` verdict (`sltu_bound`).
- `image_refines` refines `stagedVerify`, which runs the chains on
  `padded σ` (the first 5504 bits, zero-extended) with `a = min |σ| 5505`.
  `padded_slice` shows that the chain values in memory are the same slices.

## Security of short signatures

Signatures shorter than 5504 bits now run the whole verifier. Such a signature
is accepted only if the root query of length `ℓ + 639 ∈ [639, 6142]`
(`Values.ShortLen`) returns an answer whose low 128 bits are the public key.
The simulation event `Spr` gains this case (`Values.SprShort`,
`Spr = SprHash ∨ SprShort`). No hash node and no index query has a short
length (graph inputs are 144, 192 and 6143 bits, the index query 512), so a
fresh query creates `Spr` with probability at most `ε = 2^-128` either way
(`Values.spr_charge`, `card_simSet_le`). The per-compression charge `κ = 2ε`
is unchanged, and the bound stays `κ(B − 1036) + 2δ`. The security theorem is
stated on signature bits for every verifier that satisfies
`Forest.WireVerifier` (the forest verifier at 5504 bits, a short-root-query
witness otherwise): `Main.wireScheme_secure`. `StageB.stB_support` and
`events_stB` turn a short acceptance into `SprShort`. The submitted verifier
`stagedVerify` prunes to `strictVerify` (`StagedVerifier.strict_prunes_staged`,
`strictVerify_wire`). The graph root input is 6143 bits
(`Names.rootCat = (rootRegion c).setWidth 6143`); chain 31 commits 191 bits
(`Values.rootSlice`).

## Validation

An independent generator reproduces the Lean-exported 349 image and the new
image instruction for instruction (15,701 instructions and 88 data bytes,
62,892 bytes). The 348 transcript test runs 15,770 executions against a staged
reference with the same oracle: every 4,096 pair/digit landing, first
forbidden pairs at the high checksum alias 413, digit sums 0, 157, 159,
412–414 and 480, all 5,504 bit flips of one honest signature, every length from
0 to 5505, lengths 5506, 5512, 6000, 6143, 6144, 65,536 and 2^20, oversized
tails, and short signatures whose programmed root answer is the public key
(accepted; rejected at length 5505). No run traps. Every run makes the same
oracle queries as the reference and returns the same verdict. The maximum is
348 cycles, for accepting runs at 5504 bits and for the programmed 5505-bit run.

---

# Restricted antichain and address checksum: 349-cycle candidate

This extends Nicolas Consigny's officially verified 353-cycle record in PR #34,
checked source `0b21c2e8b5db210ff4feba8daab76a345cb03a6d`.
Assisted by: Codex. Earlier notes below are historical snapshots.

The full 349-cycle certificate builds and passes a cold pinned-comparator
replay through Lean's default kernel in 226.127 seconds locally. No hosted
verdict is claimed; the unchanged official verifier fails this host's Landlock
preflight before compilation. No production isolation requirement is bypassed.

## Construction

Keep thirty-two four-bit chain digits, but use target sum 158. Restrict the
first eight pair sums to at most 23, the next two to at most 24, and the last
six to at most 30. Restricting a fixed-rank antichain preserves the existing
disclosure/security structure. The generating function is
`[x^158] P23(x)^8 P24(x)^2 P30(x)^6`, where `Pt` counts digit pairs whose sum
is at most `t`. `PairCount` and `Valid` prove that the actual packed index set
has exactly 29,517,020,996,343,900,342,099,578,715,398,432 elements.

The reduced acceptance rate needs a new availability proof. Its rational lower
bound is `89 / 2^20`. Thirty-two-trial reciprocal bounds give a failure bound
of one half per 8192 trials, hence `2^-128` over the full signing budget.
Actual cached key-generation freshness and public-key-dependent messages are
still covered. No floating-point or transcendental estimate is assumed.

The machine accumulates its already-computed dispatch addresses instead of the
masked index words. The adjusted first base lane and exactly three RV64 wraps
make remainder zero modulo 255 equivalent to digit sum 158 or 413. The pair
caps total 412, excluding the high alias. The table rejects forbidden pair
landings without adding instructions to an accepting path: 266 forbidden
cells branch to eight rejection stubs in existing padding.

Five index instructions disappear and one chain hash is added:
`33 + 295 + 21 = 349` cycles. The image stays at 15,701 instructions plus
88 data bytes, or 62,892 bytes. Signature layout and the 5504-bit full size
are unchanged from 353. The latest forbidden-pair rejection costs at most 330
cycles including index processing.

## Exact staged rejection and security

Some invalid inputs perform prefix hashes before their forbidden landing.
The new `StagedVerifier` specifies these exact oracle queries. It is not
syntactically equated with an immediate-reject verifier. `RejectAdapter`
proves that deleting only terminal constant-answer query suffixes preserves
the result distribution from every initial random-oracle cache and transfers
the same pathwise whole-experiment budget `B`. This is the security bridge to
the certified strict forest verifier. A separate deterministic query-cost
bound establishes admissibility without relying on the machine-cycle proof.

The mathematical inspiration is fixed-rank order structure, local restrictions,
and choosing a representation that makes the checksum cheap. No theorem of
Grothendieck, Noether, Weil, or Bourbaki is assumed by the Lean certificate.

## Validation checkpoint

The actual Lean-exported image exactly matches the independent generator:
canonical JSON SHA-256
`1c5c586854daffa80e0379acd95151b5aafa03e152a2569d3d5555621020c602`.
All 32,822 transcript tests pass, including every 4096 pair/digit landing,
all 5504 bit flips of one honest signature, malformed lengths, both checksum
aliases, and each possible first forbidden pair. Arithmetic/counting,
availability, and the normal and rejecting pair-refinement lemmas have been
kernel checked. The final certificate covers admissibility, 127-bit strong
security, exact all-input machine refinement, every-path cycle bounds, and
strict image size. The permitted-axiom guard and cold comparator both pass,
using only `propext`, `Classical.choice`, and `Quot.sound`. Source-policy and
contract-pin checks pass. The comparator uses the pinned genuine landrun and
lean4export tools; this development replay is not a hosted verdict or a
certification of the official production isolation and resource limits.

---

# Exact availability and thinner states: 353-cycle candidate

This extends Nicolas Consigny's officially verified 358-cycle record in PR #33,
checked source `b6dbcb94fdecd2cd0ad00501d201ca1fb26e52fa` (836.1 seconds hosted).
The earlier construction and attribution notes are retained below as historical
snapshots. Assisted by: Codex.

## Mathematical change

The former availability proof compared actual key generation with an independent
ideal record, charging for collisions. That was unnecessarily pessimistic:
key generation only queries inputs of chain-state length or root length, never
the index-query length. `FreshKeygen` proves that actual cached graph evaluation
leaves every index query fresh even if some key-generation queries collide.
The signer uses distinct nonces. `Availability.signingFailure_exact` therefore
proves exact failure `miss ^ trials` for every public-key-dependent message.
No collision allowance is needed for availability.

This allows the first sixteen chain states to be 144 bits and the last sixteen
to be 192 bits: still exactly 5376 payload bits. The security proof still accounts
for collisions. Its resampling bound becomes `2^-144`; fixing a state leaves at
most 112 answer bits free. The same strong-security argument closes using
`1025 * 2^112 <= 2^128` and `4 * 1025^2 < 1036 * 2^17`.
No assumption of collision-free actual key generation is introduced.

## Machine change

The first sixteen 18-byte wire offsets relative to the payload are
`[18,36,90,108,0,162,54,72,180,126,144,234,198,216,252,270]`.
The remaining sixteen 24-byte states follow at offset 288 in execution order.
Cells remain `BASE - 32 + 24*k`, with 32-byte hash outputs starting eight bytes
below each cell. Chains 6, 9, 12 and 15 keep state bits `[112,256)` and hash in
place six bytes above their cells; other states use offset 64. Twenty-four
chains now hash in place. The eight redirect chains are 0, 1, 2, 3, 5, 8, 11, 14.
There is one width change, at pair 8, from 144 to 192.

The shared-base dispatch arithmetic and digit mapping from 358 are unchanged.
The row slots are repacked to
`[0,63,126,190] / [25,87,152,213] / [48,112,175,236] / [72,137,198,259]`.
`MixedCode.wellPlaced` proves non-overlap and `MixedLayout` proves payload and
memory geometry. `Payload` proves the wire permutation via a 16-entry inverse
check and general quotient/remainder arithmetic, not a per-bit enumeration.

The root still commits the low 192 bits of every final answer: 6144 bits and
twelve compressions. There remain 32 four-bit digits, target sum 157, 189 chain
hashes, and a 128-bit nonce. Accounting is
**38 + (189 + 64 + 32 + 8 + 1) + 21 = 353 cycles**.
The image contains **15,701 instructions + 88 data bytes = 62,892 bytes**.

## Validation status

- The full Lean certificate, strict image-size theorem, and permitted-axiom guard
  build against contract `da1418bfec2a599ac36d035f3a1ec551e73d73a0`.
- The actual Lean-exported code and data exactly match the independent generator.
  All 20,840 transcript tests pass, including every one of the 4,096 pair/digit
  landings. Eight honest cases cost exactly 38/294/21; 20,832 cases reject.
- The pinned development comparator rebuilds the complete candidate from cold
  submission-module caches, checks the statements and permitted axioms, and
  replays the proof through Lean's default kernel: "Your solution is okay!"
  Local wall time is 291.395 seconds, not a hosted-runtime estimate or an
  official resource-limit measurement. Genuine pinned landrun and lean4export
  tools are used; the trusted contract is unchanged.
- Source-policy and contract-pin checks pass. Changes stay in UpperRiscv.
- The unchanged official verifier fails this local host's Landlock preflight,
  before checking the proof. No production isolation requirement is bypassed.
  No hosted verdict for 353 is claimed; 358 remains the verified checkpoint.

## Rejected directions and next experiments

Exact enumeration of 100 mixed-radix mixtures with 128 index bits (3-, 4-, and
5-bit digits) did not beat the earlier layout family. Simpler quotient-checksum
tests alias valid sum 157 with invalid sums; weakening the rejection predicate
without a new availability/security argument is not an optimization. Reducing
the root to eleven blocks is not available in this 24-byte-cell construction.
These are scoped search results, not global lower bounds.

Further improvements could change the number of chains, acceptance code, or
memory grid. Cost the complete dispatch and root before porting another proof.
The useful mathematical idea here is a conditional-independence argument for
fresh queries; no result of Weil or Bourbaki is assumed by the certificate.

---

# One dispatch base: 358-cycle candidate

This extends the officially verified 359-cycle submission in PR #32, checked
source `60a13667e3335e2e372d31930a996a89984b3e81`, credited to Nicolas Consigny.
The earlier construction and attribution notes follow unchanged below.

Assisted by: Codex

## Change

All four index words now share one dispatch-base word, removing `LD x4, x12, 88`.
Coarse digits move from bit 9 to bit 10 in each 16-bit lane; the mask is `0x3c3c`
and the fold shift is 8. This changes the answer-to-index mapping, while retaining
32 independent four-bit digits, target sum 157, and exactly 128 unread bits.
The updated `Valid.jw` and existing uniform-fiber argument prove the new mapping.
Nonce, payload, chain widths, truncations, and root layout are unchanged.

Rows are 256 instructions apart. Group q%4 contains corresponding pairs from all
four words. Its origin is `3840*g`, with slots
`[0,64,128,192] / [25,90,154,215] / [49,112,177,238] / [75,138,200,261]`.
At each boundary, a group's final row interleaves with the next group's first row.
This saves enough address space for all stored destinations to remain halfwords;
all remaining JALR displacements fit signed 12-bit immediates.

`MixedCode.wellPlaced` certifies non-overlap of the 256 bodies; a generic
`assemble_located` theorem lifts these small layout facts to the concrete image.
It avoids separately normalizing the complete image at every landing.

Accounting: **38 index + 299 chains + 21 root/decision = 358 cycles**.
The image has 15,703 instructions and 88 data bytes: **62,900 bytes**.

## Validation

- The full exported 358-cycle certificate and strict image-size theorem build
  with the pinned toolchain. The permitted-axiom guard passes.
- The independent generator exactly matches the Lean-exported code and data.
- 20,840 full executions agree with the updated chain-level reference on every
  oracle query and verdict, with maximum 358, including all 4,096 pair/digit
  landings. Eight honest cases cost exactly 38/299/21.
- The pinned development comparator exports the required statements and permitted
  axioms, replays them through Lean's default kernel, and reports "Your solution
  is okay!" This run uses the genuine pinned landrun and lean4export tools.
- The unchanged official verifier fails this local host's Landlock preflight,
  before checking the proof. No production isolation requirement was bypassed.
  No hosted verdict or new publication is claimed; official 359 is unchanged.

---

# Two dispatch bases: 359-cycle candidate

This extends scaraven's verified 360-cycle construction (#30), checked source
`16be83e74b3eb670535bcf09c00f1e9f9ca2d5ab`, and retains its scheme and memory layout.

Assisted by: Codex

## Change

The three base words previously loaded for packed dispatch are reduced to two.
Index words 0, 2 and 3 share the same base word: for each lane their pairs now
occupy a common row group. Index word 1 uses the other base word.

Rows are `[0,12,8] / [1,9,13] / [10,14,2] / [3,11,15] / [5,7,4] / [6]`.
Slots are still 40, 40 and 48 instructions. The bodies larger than 40 instructions
occupy the third slot or the standalone row. All jump displacements fit signed
12-bit immediates, and all stored destinations fit unsigned halfwords.

`LD x7, x12, 96` is removed; words 2 and 3 now use x3. The unused final embedded
constant is removed too. The proof checks the new finite layout facts and proves
`baseWord 2 = baseWord 0` and `baseWord 3 = baseWord 0`.

No nonce, accepted index, chain state width, payload permutation, truncation,
root input, or oracle query changes. In particular, security and availability
proofs are reused unchanged.

Accounting: **39 index + 299 chains + 21 root/decision = 359 cycles**.
The image has 12,339 instructions and 96 data bytes: **49,452 bytes**.

## Validation

- The full exported 359-cycle certificate and image-size theorem build with the
  pinned Lean toolchain. The certificate's axiom guard passes with only `propext`,
  `Classical.choice`, and `Quot.sound`.
- An independent generator exactly matches the Lean-exported instruction and
  data images, for both the 360 baseline and this candidate.
- 4,456 candidate executions agree with a chain-level reference on every oracle
  query and verdict; eight honest cases cost exactly 39/299/21. Rejection cases
  include wrong lengths, index sums 156/158/412, root mismatches, and mutations.
- The official verifier was attempted unchanged but fails the host's Landlock
  preflight before proof checking. This is an infrastructure failure, not a
  hosted proof verdict. No production isolation requirement was bypassed.
- The pinned development comparator passes: it exports the required statements
  and permitted axioms, replays them in Lean's default kernel, and reports
  "Your solution is okay!" This uses the genuine landrun binary but the local
  development build; it is not a hosted verdict or a production-isolation check.

## Search scope and next direction

The first experiment changed row placement and base sharing only. For the four
choices of a single index word kept separate, only word 1 lets each corresponding
three-pair group have at most one body larger than 40 instructions. A single
shared base word would require four bodies per corresponding lane group, outside
this three-body layout. This does not establish global optimality.

Further gains need different index arithmetic, dispatch encoding, or a broader
layout/construction search. The earlier research notes follow for attribution
and their rejected directions.

---

# In-place chains above the cell: 360-cycle candidate

This extends dhsorens's 364-cycle ascending cell grid (PR #28), which extends the 372-cycle dense
dispatch and the constructions it credits. The notes of the 364 construction follow unchanged
after this section.

Assisted by: Claude Fable 5.1 (design), Claude Opus 5.5 (implementation)

## What changes (364 -> 360)

- **Machine.** Chains 7, 11, 15 and 19 (the last 152-bit value of each 96-byte wire group, at
  group offset 77 = cell + 5) are hashed in place: `x12 = outAddr k` as before, `x10 = wireSlot k
  = outAddr k + 13` for every hash, next state = answer bytes `[13, 32)`. Their buffer bytes
  `[0, 13)` hold the previous chain's discarded top 8 bytes and already-read wire bytes, so no
  unread input and no committed root byte is overwritten. Their entries lose `ECALL; ADDI x10,
  x12, 8`, their copy bodies use 16-ECALL ladders, and prologues 4, 6, 8, 10 start from
  `work (2q-1) = slot (2q-1) + 5`.
- **Root, wire, rows, dispatch.** Unchanged. Each chain still commits its answer bytes `[0, 24)`
  at `outAddr k`, so `R`, `rootCat` and the 12-block root hash are untouched.
- **Accounting.** 40 + (189 + 64 + 12 + 32 + 2 = 299) + 21 = 360; 12340 instructions and
  104 data bytes as before.

## Proof changes

- `Names.truncOff` (104 for chains 7, 11, 15, 19, else 64) and `trunc` at
  `min (truncOff k) (w - chainBits k)`. `Values` adds `card_filter_extract_le` (256-bit words
  with a fixed `c`-bit window at any offset), and `card_filter_trunc_le'` goes through it
  (still `2 ^ 104`, since every state has at least 152 bits). No other security file reads the
  offset.
- `MixedProgram`: `expands k` (the wire value is neither at its cell nor five bytes above it)
  and `work k` (`slot k` if the chain expands, else `wireSlot k`). The machine invariants
  (`HashInv`, `HoldsAt`, `Prepared`, dispatch, landing) are stated at `work k`, and `prevInput`
  is the previous chain's `work`. `MixedLayout.work_eq'`, `MixedEntry.prevInput_bounds'` and
  `MixedChainFrame.prevInput_32` are kernel checks over all chains. The unused `Holds` and
  `holds_of_answer`, which hard-coded offset 64, are removed.
- `MixedCost`/`MixedPhase`: 12 early hashes, per-pair overhead 110, chains 299.

## Validation status

Checked on a CI mirror of the verifier: a GitHub Actions build of
`Submissions.UpperRiscv.Solution` against the pinned `.contract`, with the policy, stub-statement,
axiom and pinned-comparator checks. The hosted ots.golf verifier has not checked it yet. Before
the push, a Python port of the edited image definitions reproduced the 364 image
(12340 instructions, 104 data bytes), checked every new kernel table fact, and replayed byte
provenance for 202 digit vectors: every first hash reads its wire value, every later hash reads
exactly its own state, no unread signature byte is overwritten, and the root region holds bytes
`[0, 24)` of every chain's final answer.

## What did not work, and what is left

- **More in-place chains on the strict grid.** An exhaustive search over wire orders with
  152/160/192-bit states (on-grid iff the value lies inside its own chain's 32-byte block with
  dead bytes around it) finds at most 20 in-place chains with a 12-block root, i.e. this 360.
  Every 12-block layout is a single-direction slice grid (or one `D…D U…U` junction), and the
  only sub-360 witness we found (a hybrid with a zero-hash bottom chain) fails byte contiguity.
- **Fewer root blocks.** Under 8-aligned 32-byte answer blocks a chain keeps 8, 16, 24 or 32
  bytes of the root region, so even 152-bit retention needs at least 758 bytes: 11 blocks are
  impossible for 32 chains.
- **Imbalanced acceptance rules** (reject the costliest accepted digit vectors using the
  availability slack): cost only varies at digit 0 in this machine, and the SWAR check of any
  such rule costs far more than it saves.
- A non-grid layout with in-place narrow chains, a stack of moved tiles and a zero-hash last
  chain reaches 361-362 with a 15-block root; it does not beat the grid.

---

# Ascending cell grid: 364-cycle candidate

This extends the officially verified 372-cycle dense-dispatch submission (PR #27,
commit 9fe2362), which builds on Alexander Hicks's 377-cycle mixed-width image and
dhsorens's paired dispatch.

Assisted by: Claude Fable 5.1

## What changes

The 372 image expands 24 of its 32 chains: a chain whose wire value is not already
in its 24-byte working cell pays one `ADDI x10, x12, 8` after its first hash. Only
the eight 192-bit chains at the bottom of the payload sit on the cell grid, because
the wide chains run upwards from the payload base while the narrow chains are
relocated downwards from the top, and the two families meet at a 16-byte junction
that costs two full 256-bit root slices.

Here every chain runs in the same direction. The 32 cells are `0x3FFFE0 + 24k` in
execution order, each hash writing its 32 bytes at `0x3FFFD8 + 24k`, eight bytes
below the state. A chain needs no expansion exactly when its wire value starts at
its own cell, and a wire block survives until it is read exactly when it lies at or
above its own cell's state address: the writes of the chains processed so far cover
`[0x3FFFD8, 0x3FFFE0 + 24k)`, and every later block is above that. So the payload
can be permuted freely as long as `wireSlot k ≥ slot k` for every chain.

The signature budget is 672 bytes = 28 cells of 24 bytes. A group of consecutive wire
blocks whose lengths sum to a multiple of 24 places one chain on the grid. With the
152-bit (19-byte) minimum state, only one-chain groups (a 192-bit chain) and
five-chain groups (four 152-bit chains and one 160-bit chain, 96 bytes) pay off, and
12 + 4 such groups fill the budget exactly: sixteen chains on the grid, sixteen
relocated, against eight and twenty-four before.

- Chains 0–3 carry 160-bit states, 4–19 carry 152-bit states, 20–31 carry 192-bit
  states (5376 bits, signature 5504 bits as before).
- The wire holds four 96-byte blocks with chains `4b+4` (on the grid), `b`,
  `4b+5`, `4b+6`, `4b+7`, then chains 20–31 in place. `Payload.index`/`coindex`
  are the two directions of this permutation, checked inverse by kernel decision;
  the verifier applies `permute`, the signer `unpermute`.
- The root reads the low 192 bits of every cell, 768 contiguous bytes from
  `0x3FFFD8`: 6144 bits, twelve compression blocks instead of thirteen.
- The dispatch halfwords move from `0x3FFFE0` (now cell 0) to `0x4002E0`, the first
  bytes after the signature buffer.
- `x11` starts at 160, becomes 152 at pair 2 and 192 at pair 10: two width changes,
  both on pair boundaries.

Rows are `[12,1,8] / [13,9,4] / [14,10,6] / [11,0,15] / [3,5,2] / [7]`, still 16 rows of
128 instructions per group with bodies at offsets 0, 40 and 80. The four pairs whose
left chain is on the grid and whose right chain is relocated need 41 instructions and
take the 48-instruction third slot, as does pair 15 with the root and decision (47).
Pairs 12–15 share a row with pairs 8–11 at displacements −320, −160, −160 and +320
bytes, so the fourth dispatch word again reuses the third word's base constants.
Chain 0 is now relocated, so the first prologue is six instructions and the copies
start at instruction 52.

The proved accounting is:

- Index phase: 40 cycles.
- Chains: 189 hashes + 64 pointer instructions + 16 redirects + 32 dispatch
  instructions + two width changes = 303 cycles.
- Root hash (12 blocks) and decision: 21 cycles.
- Total: 364 cycles; 12340 instructions + 104 data bytes = 49464 bytes.

## Security and availability at 152 bits

The bad-record weight is `δ = 2 · 1025² · 2⁻¹⁵²`, about `0.125 · 2⁻¹²⁸`, and the
signing-failure allowance is `2⁻¹²⁸` in total. The 372 proof spent `0.882 · 2⁻¹²⁸` of it
on the availability term through the bound `numValid ≥ 712 · 2¹⁰⁵`; the true count at
sum 157 is `751.03 · 2¹⁰⁵`, so `Valid.numValid_avail` now certifies `750 · 2¹⁰⁵` and the
miss term becomes `(1 − 750/2²³)^(2²⁰) ≤ 0.482¹²⁸ < 0.74 · 2⁻¹²⁸`, leaving `0.26 · 2⁻¹²⁸`
for `δ ≤ 2⁻¹³⁰`. Strong unforgeability keeps its margin: `2δ < 1036 κ` with the
keygen cost now 1036 (1024 chain hashes and a 12-block root), and verification costs
202 compressions. Chain states of 144 bits would put `δ` near `32 · 2⁻¹²⁸` and are not
admissible under this proof, which is why the narrow width is 152.

## Validation status

`lake build Submissions.UpperRiscv.Solution` passes with the pinned toolchain, and the
exported submission, certificate and image-size theorem use only `propext`,
`Classical.choice` and `Quot.sound`. The layout was first checked by a small model of
the image (block sizes, row capacities, landing addresses below 65536, the
`wireSlot ≥ slot` and commit-disjointness invariants); the Lean image reproduces its
12340-instruction length and the same invariants by decision.

## Rejected directions

- 144-bit states (sixteen wide, sixteen narrow, one width change) fail the
  signing-failure budget as described above.
- A twelve-block root with the record's two-directional layout is impossible: the
  junction between an upward and a downward family always needs two 256-bit slices.
- With the grid but the wire in execution order, on-grid chains must form a suffix
  of the payload and at most twelve fit (368 cycles); the sixteenth on-grid chain
  needs the block permutation.
- Two widths only ({152, 192}) cannot fill 672 bytes with sixteen on-grid chains:
  the relocated deficit of 96 bytes is not a multiple of 5.
- Fewer chains (30 or 31) save expansions and a root block but raise the accepted
  digit sum by more than they save.
