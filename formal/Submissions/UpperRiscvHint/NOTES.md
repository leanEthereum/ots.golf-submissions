# Hinted RISC-V: combined pointer skips and variable disclosure, 310

This combines the certified local 311 pointer-skip construction at `1cbee19`
with the locally certified variable-disclosure 311 construction. Both parents
remain preserved. The combined image passes independent machine and completion
tests. The complete Lean 4.33.1 certificate compiles and passes exact-statement
comparison, the permitted-axiom audit and fresh kernel replay of all
23,094 exported declarations.
Only `propext`, `Quot.sound` and `Classical.choice` are used.

## Combined construction

Keep the skip-aware alphabets: pairs 0–5 use 32 redirects each, and pairs 6–15
use the previous 30 redirects each. The shifted rank target is 147 and the free
count is 0–18. The accepted set has exactly
29392495299674139897463880312407816 indices, greater than 89 times 2^108.
The maximum pair rank is 374; adding the largest free count gives 392, below
the next modulo-257 alias at 404.

A right chain with zero hashes in pairs 0–5 needs no pointer update. Ordinary
skip rows replace the two pointer instructions with one checksum correction;
redirected skip rows fold that correction into their existing helper. The next
prologue measures its pointer from the left chain's retained state. These six
pairs operate on chains 1–12, all still 192 bits wide.

Chain 13 also becomes a 192-bit optional-hash cap. The other nineteen states
are 141 bits; chain 32 commits a 144-bit top. The full signature has 5495 or
5498 bits, and a pure projection retains exactly 5495. The algorithmic verifier
tries the short signature and its eight three-bit extensions, then re-verifies
the selected full signature. The generic security transfer preserves the
whole-experiment query budget. A conservative bound is 1800 verification
compressions, within 2^20. Minimum state width 141 still satisfies the concrete
127-bit strong-security inequalities.

## Machine and proof composition

The width change occurs inside pair 6, after chain 13 and before chain 14.
This permits a skip in pair 5 immediately before the newly optional cap.
`EntryInv` tracks the skipped pointers; `between_refines` handles the width
change; `cursorAt` accounts for the bottom chain's variable disclosure.

The combined pair and root overhead is 129. Thus every accepting execution
costs 31 index + 3 dispatch + 129 overhead + 147 rank = 310 cycles.
Equivalently, for h redirects and s saved pointer instructions, compression
cycles are 173 - 2h + s and ordinary cycles are 137 + 2h - s.

The root is 7133 bits, still fourteen compression blocks. Sixteen unreachable
padding instructions put the root length within immediate reach of pair 0's
link: 5092 + 2041 = 7133. The image has 260854 instructions and 56 data bytes,
1043472 bytes total, leaving 5104 bytes below the strict 1 MiB limit. There are
492 helpers. The new lane bias is 92.

## Validation

The independent suite covers every pair landing and free count, checksum
boundaries, both bottom-chain disclosure cases, individual view-bit mutations,
unexpected length banks and every honest-bank length. Additional tests exercise
all skip rows, simultaneous skips and the pair 5 to pair 6 width boundary.
Completion tests cover sixteen keys, all eight omitted-bit values under coherent
alternative-root oracle answers, and signature mutations.

Reproduction scripts and audit results are in the workspace evidence directory
`riscv-innovation-evidence/combined310`. The production verifier uses the unchanged
contract `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c` and Lean 4.33.1. The host's lack
of Landlock prevents official sandbox verification; no hosted verdict is claimed.

### Hosted build repair

The first submitted head, `d5e34ac`, was rejected on PR #69 because
`MixedHelpers.landing_refines` used an undeclared assignment `x`. The local
helper had invoked Lean directly with its default `autoImplicit` setting;
the pinned Lake project sets both `autoImplicit` and `relaxedAutoImplicit`
to `false`. The checksum goal in the bot's short report was a secondary
error after elaboration failed at the missing binder.

Declare `{x : graph.Assignment}` explicitly. This changes the proof's
elaboration, with no change to the image, scheme or 310-cycle claim. For
reproduction, build `Submissions.UpperRiscvHint.Solution` through the pinned
Lake project after removing this submission's prior build artifacts, then
export and replay that fresh build. Source fingerprints and kernel replay
alone do not check that a source elaborates under the project's options.

## Next steps

The two one-cycle savings compose because the skipped pairs stop at chain 12.
Further gains need another executed-instruction reduction, or a new graph and
encoding whose availability count and strong-security bounds still close.
Simply lowering target 147 is not justified by the existing count.

## Historical variable-disclosure parent

The following notes describe the earlier 311 construction and its own audit.

# Hinted RISC-V: variable-disclosure 311 implementation

The complete `Solution.certificate : submission.Certificate 311` compiles with
Lean 4.33.1. Exact-statement comparison, the permitted-axiom audit and fresh
kernel replay of all 22,928 exported declarations pass. The certificate
depends only on `propext`, `Quot.sound` and `Classical.choice`.

## Construction

The weighted pair alphabet and rank target 142 are unchanged from the 312
construction. Converting chain 13 to a zero-step-capable 192-bit chain removes
one mandatory compression. All nineteen later chain states shrink to 141 bits,
so the state disclosures total 5367 payload bits. The bottom chain still needs
a byte-aligned 144-bit committed top: it discloses 144 bits when no hash remains,
and 141 bits otherwise. Full forest signatures therefore have 5498 or 5495 bits.

`Completion.project` always keeps the first 5495 bits. It is pure and does not
consult the index oracle. The verifier tries the short signature and its eight
three-bit extensions, keeps an accepted full signature, checks its projection,
and verifies it once more. This last verification makes `ProjectionTransfer`
preserve the whole-experiment query budget exactly in the strong-security
reduction. The verifier costs at most 1770 compressions, below the fixed 2^20
budget. `CompletionCorrect` proves perfect correctness, and `Completion` proves
the remaining admission requirements and 127-bit strong security.

The graph security proof uses minimum state width 141 and fiber bound 2^115.
The original concrete inequality still closes; no new axiom or cryptographic
assumption is introduced. The key generator uses 1070 compressions.

## Machine proof

The root is 7133 bits, still fourteen compression blocks. Its first slot is
the bottom chain's 144-bit top; its last slot is the other boundary chain's
141-bit top. Fourteen wide caps interleave with mandatory chains. The sole
width switch moves inside pair 6, between chains 13 and 14. Sixteen skipped
padding instructions put pair zero's link within signed-immediate reach of
the root length. The program has 260854 instructions and 56 data bytes:
1043472 bytes, strictly below 1 MiB.

Every accepting path has 137 + 2h ordinary cycles and 174 - 2h compression
cycles, where h is its number of redirected pairs. Equivalently:
31 index + 3 dispatch + c + 135 + weighted sum = 311,
because c + weighted sum = 142. `MixedVerifier.image_refines_trap` proves the
bound for every view and every sufficiently fueled run. Fuel monotonicity in
`HintTrap` covers every fuel in the exported contract.

Views retain the three omitted bottom bits. `HintView.trap_full` extracts a
full accepted signature from every accepting view. Completion remains accepting
after the machine cache grows, which supplies soundness even though the
algorithmic verifier performs more queries than the machine. Honest expansion
recovers a full signature, pads it to 5498 bits and lays out its disclosures.
Its view length is 7424 + 4*(31-c), with c from 0 through 18. Cached replay proves
faithfulness. The raw marker encoding still handles all rejecting signatures.

## Validation and reproduction

The independent VM suite passes 37810 executions, including 4418 primary
accepting fixtures with exact oracle transcripts, all at 311 cycles. These
cover all 4096 pair landings, every free count, zero and positive bottom counts,
all honest-bank lengths, malformed banks and individual view-bit flips.
Completion tests additionally cover sixteen independent keys and all eight
bottom-bit completions, including coherent alternative-root oracle answers.
The Lean image exactly matches the tested image. Canonical JSON SHA-256:
`b5faed53ed9501592890654aedc157515ae0fb21e291b255e6bae6b416e9610e`.

Scripts, reports and independent image artifacts are in the project workspace
at `riscv-innovation-evidence/variable311`. The original 312 checkout remains
unchanged. The contract pin is `8b140a99afa5b3e0bc785ab202c7b0a9c1f7fe7c`.

## Why the earlier obstacle is avoidable

A fixed 141-bit disclosure cannot directly represent a 144-bit zero-step top.
Discarding those bits without recovery breaks soundness. Variable full
signatures plus a fixed pure projection and exhaustive three-bit completion
remove that obstacle while preserving the exact security budget. The 192-bit
caps and fixed-width disclosure assumptions in earlier restricted-family
floors therefore do not constitute a global 312 lower bound.

Further gains could come from dispatch cost or another graph layout with a
smaller mandatory-hash count. Any larger omitted suffix must still meet the
algorithmic verifier budget and preserve strong security at the same B.

## Historical baseline notes

The sections below describe earlier images and their own validation results.

# Hinted RISC-V: weighted-pair 312 implementation

30 September 2026. The complete claim-312 certificate compiles and passed
local exact-statement comparison, permitted-axiom checks and fresh kernel
replay of all 22,620 exported declarations. Official sandbox verification
is unavailable on this host because it lacks Landlock.
The graph, chain widths, 128-bit nonce and packed index, 5,504-bit signature,
and 884-byte root remain those of the 315 record. This work changes the
encoding and dispatch, not the security parameter of chain values.

## Encoding and exact accepted count

Complement the second raw nibble, then use `WeightedPairs.swaps` to redirect
30 high-cost points of the 16-by-16 square into 30 points with one coordinate
from 16 through 20. The remaining 226 points stay fixed. Define
`phi(d) = d + 2*[16 <= d]` and sum it over the 32 nonfree digits. Accept sums
124 through 142; the free digit is 142 minus that sum, from 0 through 18.

`PairCount` transports counting through the coarse complement involution.
The tuple-count recurrence is proved equal to the cardinality of actual
accepted tuples, and `Valid.card_validAt` connects tuples to packed indices.
The accepted set has exactly 29040465820198574112934315249983761 members,
exceeding 89 * 2^108 = 28882151275599978683700885831286784.

## Security proof

`phi` is strictly increasing. Distinct vectors of equal weighted rank have
a crossing coordinate, even when their unweighted hash costs differ.
`FixedChoice.fixedCut_witness` supplies the disclosed/evaluated node used by
`Events.events_ne` and `StageB`. The original same-index strong-unforgeability
branch remains intact. The complete availability, correctness and 127-bit
security proofs are connected to the actual recoded accepted set.

## Machine proof and exact cost

The image contains 480 helpers, one for each position and redirected pair.
A redirect executes a `JAL`, then an `ADDI` adding four times the difference
between the raw and weighted pair sums to `x27`. The existing `REMU` moves
from the index phase to the root boundary. The lane bias becomes 76, and
pairs 11 and 15 exchange row offsets. Image size stays 1,043,408 bytes.

`ChainIndex` explicitly carries the free count read from an arbitrary view.
`Ctx` tracks `x27` and the modulus register through hashes and pointer moves.
`MixedHelpers.landing_refines` proves the ordinary and redirected entry paths,
the two-instruction fee, and preservation of values and memory.
`MixedFree.checkedRun_refines` accumulates all corrections.
`MixedRoot.rootReject_refines` handles a wrong residue, including zero, before
the root query. This covers malformed views that hash entire chains first.
The maximum weighted sum is 368 and the maximum admitted free count is 18,
so the next modulo-257 alias at 399 cannot pass.

For `h` redirects, compression cycles are 175-2*h and ordinary instructions
are 137+2*h. Equivalently, the accepting path costs
31 index + 3 dispatch + c + 136 + weighted sum = 312.
`MixedVerifier.image_refines_trap` proves this on every accepting execution.
`HintView` supplies compression, expansion and cached-oracle replay;
`Solution.certificate` assembles the complete hinted-track contract.

The independent VM passes 30,428 executions, with 4,414 accepting fixtures
at exactly 312 cycles and matching ordered oracle transcripts. The exact
Lean-exported image JSON SHA-256 is
`93f04e16b860e3f0195ea4697bb87123b4a5c16c5764086bc536195a70904aea`.
Reproduction and final validation reports live in
`golf/riscv-innovation-evidence/record312-port` in the project workspace.

## Historical 314 and earlier notes

The following section records the preceding construction. Its 314 claim,
counts and validation results apply to that historical image only.

# Hinted RISC-V: 314 cycles with a modulo-257 checksum

This extends the 315-cycle image at `df3ac8e`. The sixteen index pairs keep their
four-bit fields and machine lane mask. If their raw fields are `(a, b)`, their
chain digits are `(a, 15-b)`. Since `256 = -1 (mod 257)`, the existing lane sum
checks this interpretation with modulus 257 and a different constant bias.
The second chain's code rows are reversed and repacked around the same guarded
view-length banks. No additional executed instruction is needed.

## Accepted indices and the excluded alias

Write `S = sum(a + 15-b)`. The accepted window is `124 <= S <= 144`, and the
free chain supplies `c = 144-S`, from 0 through 20. The first twelve pair sums
are at most 24; the final four are at most 23. Thus `S <= 380`, and an admitted
free count gives `S+c <= 400`. The next checksum alias is `144+257 = 401`, so
it cannot pass all pair checks. Merely changing the modulus without these
caps would be unsound.

`PairCount.window_count` proves the exact accepted count:

```
28910611234910622126543565794415129
  >= 89 * 2^108
   = 28882151275599978683700885831286784.
```

This preserves the existing availability bound. Complementing each coarse
field is an involution, so distinct packed indices still give distinct cuts.
The 128-bit nonce and packed index, chain widths, root input, signature format,
and strong-unforgeability argument retain the 315 construction's parameters.
`FixedChoice.fixedDigits_injective` proves injectivity for the new interpretation.

## Machine and cost

The index phase loads 257 instead of 255; lane 0's bias is 78 instead of 233.
The free row admits counts through 20 and rejects larger counts. Each second
chain hashes according to `15-b`. The sixteen table offsets are:

```
0, 3705, 7327, 11261, 144, 3509, 7165, 11363,
37, 4119, 7803, 11425, 81, 4181, 7741, 11298.
```

Exact accepting cost: **314 = 32 index + 3 free dispatch + 144 digit units +
135 pair/root/decision overhead**. This is 177 hash-compression cycles and
137 ordinary instructions. Signatures are 5504 bits; honest views range from
7340 through 7420 bits. The 884-byte root still costs 14 compressions.
The image has 260,838 instructions and 56 data bytes: **1,043,408 bytes**,
5,168 bytes below the image limit.

## Validation

The complete `Certificate 314` and `image_size` compile with Lean 4.33.1.
Exact challenge-statement and primitive comparison, the permitted-axiom check,
and a fresh kernel replay of all 22,555 exported declarations pass. The replay
takes 220.903 seconds, or 241.126 seconds including parsing and comparison.
The certificate uses only `propext`, `Classical.choice`, and `Quot.sound`.
Source-policy checks pass. The official verifier stops at its Landlock
preflight on this host, before compilation; no hosted verdict is claimed.

The exported machine image exactly matches the independently generated
and tested image, with canonical JSON SHA-256
`7de0c51c7b1cd52180b85a07038b79833a9250cd873c3a7021d88dc4b3901c2b`.

The byte-memory interpreter passes 30,180 executions: 16 calibrations of the
original 315 image; 4,375 candidate fixtures, including all 4,096 pair landings,
all 21 free counts, random cuts and checksum boundaries; 16,353 out-of-bank
cases; all 2,048 honest-bank lengths; and 7,388 individual view-bit flips.
The 3,903 accepted candidate fixtures have exactly 314 cycles and match the
abstract verifier's ordered oracle queries. All cuts use one fixed key and
complete chain histories, and reconstruct the same root.

## Follow-up

The natural next targets are fewer dispatch instructions or another reduction
in the accepted layer. Any further window change must satisfy both the exact
availability count and the modular-alias exclusion. The tight margin above
the availability threshold makes estimates inadequate here.

The following sections retain the historical 315, 316, 317, 318 and 320 notes.
Their counts, windows and constants describe those versions.

---

# Hinted RISC-V: 315 cycles with a linked root length

In the 316-cycle image, `x1` held the constant 6144 only for the root length
`ADDI x11 x1 928`. The masked dispatch had already removed its other use. Pair 0's
prologue occurs once in the image, so its jump can link into `x1` at no cost:
`JALR x1 x28 imm` writes the fixed address 5028. The root then computes
`ADDI x11 x1 2044`, and the index phase loses `LD x1`. The OTS, accepted index set,
signature format, view encoding and banks are unchanged.

## Layout

The link must lie within `ADDI` reach of 7072, so pair 0's jump must be at code
index 231 or later. The free row, pair 0's prologue, every chain body, every
rejection stub and every guard window move up by 128 instructions. Pair 0's
prologue is at index 229. The masked jump immediate is -1256, and bank `b` has its
window at `198 + 512*(b-3)`. The padding after the free dispatch's jump is 130
unreachable `ADDI x0 x0 0`. Lanes 0 to 2 move their bases with the tables, and the
lane-0 bias becomes 233. Lane 3 keeps base 65532, and its largest jump immediate
grows from 792 to 1304, still below 2048.

`Ctx.base` now states that `x1` holds pair 0's link whenever `x12` addresses a
chain after the free chain. The free phase satisfies it vacuously. Pair 0's
prologue sets it, and nothing writes `x1` again. The chain lemmas report their
final `pc`, so the free chain ends exactly at `freeLanding` and pair 0's link is
known.

Exact accepting cost: **315 = 32 index + 3 free dispatch + 145 digit units +
135 pair/root/decision overhead**, comprising 178 compression cycles and 137
ordinary instructions. There are 260,838 instructions and 56 data bytes:
**1,043,408 bytes**, strictly less than 1 MiB.

## Validation

`lake build Submissions.UpperRiscvHint.Solution` passes with Lean 4.33.1.
`certificate : submission.Certificate 315` and `image_size` depend on `propext`,
`Classical.choice` and `Quot.sound` only. The Lean-exported image equals the
independent generator (sha256 `b08b7fd4…`). The generator also reproduces the
316-cycle image exactly. The byte-memory transcript test passes 17,079 cases:
all 4,096 pair landings (3,760 accepting), every encodable count on accepted
and out-of-window digit sums, 2,372 view lengths across banks 0 to 5 and 255 to
512 including every bank-3 length, 16 raw forms, and all 7,392 bit flips of one
honest view. Accepting oracle queries match the abstract forest in order, and
every accepting run costs 315 cycles. An arithmetic check covers all 1,048,578
capped length values.

The following sections record the historical 316, 317, 318 and 320 versions.

---

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
