# In-place chains: 362-cycle candidate

This extends the 372-cycle dense-dispatch record (PR #27 by alexanderlhicks, which builds
on dhsorens's paired dispatch and the 377/393-cycle optimizations credited below). The
notes of the 372 construction follow unchanged after this section.

Assisted by: Claude Fable 5.1 (design search) and Claude Opus 5.5 (Lean implementation),
Anthropic.

## Byte layout (offsets from `0x400040`; `k` = execution order)

```
 k   type    mode   wire        x12   j   note
 0-9 narrow  EXP    gaps        896..680 (24-byte stack, top-down)   retain answer[8,32)
 10  narrow  EXP    [652,672)   656   -   stack base, retains all 32 bytes
 11  narrow  EXP    [492,512)   496   -   in-span tile, retains answer[8,32)
 12  narrow  EXP    [472,492)   472   -   in-span tile, overwrites chain 11's read value
 13-19 narrow IP    68+64m      56+64m 12  unit `gap | N(j=12) | W(j=0)`
 20  narrow  IP     [532,552)   528   4
 21  narrow  IP     [572,592)   560   12
 22  narrow  IP     [592,612)   592   0
 23  narrow  IP     [632,652)   624   8
 24-30 wide  IP     24+64m      24+64m 0   spill 8 bytes up into the next gap
 31  wide    IP     [0,24)      -8    8   last chain; spill into the consumed nonce tail
```

`R = [0, 928)`: chains 31, 24, 13, 25, 14, ..., 30, 19, 12, 11, 20-23, 10, 9, ..., 0 in
memory order (`Forest.rootChain`); chains 0-9, 11 and 31 keep answer bytes `[8, 32)`,
the others all 32 bytes (`Forest.rootStart`).

## Accounting

- Index 40 (unchanged; its final instruction now sets `x11 = 160` because the narrow
  chains run first, and `prologue 12` switches to 192).
- Chains: 189 hashes + 64 pointer ADDIs + 13 redirects + 32 dispatch + 1 width change = 299.
- Root `ADDI x11, x13, 1920` (7424 bits) + 15-cycle ECALL + decision 7 = 23.
- 362 on every accepted input; the proof bounds every run by 362.

## Proof changes

- `Payload`: 32-bit-unit permutation tables with kernel-checked inverse laws.
- `Names`: `chainBits` (narrow first), `truncOff` (0/32/64/96), root input `rootCat` as a
  recursive concatenation `rootPart` over the memory-order table, and the generic
  `rootCat_extract`; root cost 15, keygen cost 1039.
- `Values`/`Events`: `rootSlice` is uniformly the high 192 bits; `rootCat_slice_inj` and
  `card_updHash_rc_le` follow from `rootCat_extract`. Constants 7424/204/205/1039.
- `MixedProgram`/`MixedLayout`/`MixedMemory`: table-driven `outAddr`, `wireSlot`,
  `slot = outAddr + 8`, `work`; every per-chain fact is `decide +kernel` over `Fin 32`.
- `MixedRootMemory` assembles `R` by induction over `rootPart`; `MixedRoot` has no pointer
  update and hashes 15 blocks; `MixedIndexPhase`/`MixedPair`/`MixedLanding` move the
  width change to pair 12.

## Validation status

Checked by our private CI mirror of the verifier (build of
`Submissions.UpperRiscv.Solution` against the pinned `.contract`, policy check,
stub-statement and axiom check, pinned comparator); **not** yet by the hosted ots.golf
verifier. A Python emulator of this exact image (a port of the Lean image definitions over
the pinned machine semantics, with a stand-in random oracle) measured 362 = 40/299/23 on
every accepted input and at most 362 on every rejecting path we exercised, rejected every
single-bit flip of whole honest signatures, reproduced the key-generation root input on
every run, and a byte-ownership replay confirmed that no hash overwrites an unread byte and
no signature byte goes unread.

## What did not work, and what is left

- **Imbalanced acceptance rules.** Rejecting the most expensive accepted digit vectors needs
  digit-dependent cost, which this machine only creates at digit 0 (a moved chain whose
  coarse digit is 0 can skip its redirect). The availability slack at sum 157 is 5.5 %
  (751 vs 712 in units of 2^105); the best weighted level set `Σd + #{nonzero} = 167` over
  those 12 chains gains 2 cycles but its SWAR check costs 13 (index 40 → 53). Digit-range
  restrictions never reach the availability threshold at useful targets.
- **Zero-hash chains.** A chain that hashes zero times must disclose its own root slice and
  leave every other root byte unchanged; with spills into neighbouring cells this is possible
  for at most one chain, so the per-chain `+1` hash is not removable in general.
- **The root input is 15 blocks here**: in-place narrow chains retain full 32-byte answers
  and the moved tiles stack above the signature. Reconciling this with a 12-block root (as
  in the 364 ascending grid) is the obvious next direction.
- Dropping the fold with `REMU 255` fails: sum 157 aliases 412, and a grindable 412-sum
  index would run ~444 chain hashes before rejecting.

---

# Dense dispatch: 372-cycle candidate

This extends Alexander Hicks's officially verified 377-cycle mixed-width submission
(PR #26, commit 7635add16c45b513b8afe37f6b3b3916e55b0fae), which builds on dhsorens's
paired-dispatch construction and the earlier 393-cycle fold optimization.

Assisted by: GPT-6 (Codex)

## What changes

The 377 image reserves 64 instructions per pair body and packs two bodies into a
128-instruction coarse-digit row. It uses two 5/3-bit digit pairs to keep that image
within the reach of halfword-based dispatch. Here up to three bodies share a row,
so the scheme can use 32 four-bit digits and accepted sum 157 instead of 160.
That removes three chain hashes without reducing the nonce or state widths.

Pair groups are `[0,1,2]`, `[3]`, `[8,4,12]`, `[9,5,13]`, `[10,6,14]`, `[11,7,15]`.
Every group has 16 rows of 128 instructions. Body starts are at offsets 0, 40 and 80
instructions. Pair 3 occupies a row on its own because its continuation changes the
hash-input width. Ordinary wide bodies need at most 38 instructions, pair 3 needs 41,
ordinary narrow bodies need 40, and the final body needs 47. This preserves the
`4*dA + 512*dB` displacement. Pairs 8/12 through 11/15 differ by 320 bytes, allowing
the final dispatch word to reuse the third word's base constants.

The masks are now identical in all four index-answer words, so one load is removed.
For each accumulated 16-bit lane the fine and coarse sums are each at most 60.
After division by four, the shifted addition has alternating seven- and nine-bit
cells: a fine-plus-coarse sum is below 128, and each intervening field is below 512.
Thus `SRLI 7; ADD; AND 0x01fc` replaces the two-mask fold. REMU 65535 then sums the
four lanes. `MixedLanes.fold_fields` factors the arithmetic into small digit and
quotient lemmas to keep proof checking economical.

The 128-bit nonce, 8 wide/24 narrow state split, reverse expansion, and 6272-bit root
input are unchanged. The proved accounting is:

- Index phase: 40 cycles.
- Chains: 189 hashes + 64 pointer instructions + 24 redirects + 32 dispatch
  instructions + one width change = 310 cycles.
- Root hash and decision: 22 cycles.
- Total: 372 cycles; 12338 instructions + 104 data bytes = 49456 bytes.

## Validation status

The Python prototype passes 6170 full-transcript cases, eight honest signing/key
cases and 528 signature mutations (6706 in total). Seven fixtures replay through
the pinned RISC-V loader and instruction/hash semantics. The Lean image exactly
matches the generator. These checks supplement the universal proof.

The complete public 372-cycle certificate and image-size theorem compile with the
pinned Lean toolchain: `lake build Submissions.UpperRiscv.Solution` passes (8900 jobs).
The exported submission, certificate, image-size theorem and machine refinement use
only `propext`, `Classical.choice` and `Quot.sound`. The full proof includes security,
signing availability and exact oracle-computation refinement on every raw input.

The local production verifier was attempted, but stopped before proof checking:
this Linux host lacks the required dedicated filesystem of at most 64 GiB for
`OTS_WORK_DIR`. Its isolation checks were not bypassed. The hosted comparator and
resource-limited verification are requested by this PR; no hosted verdict is claimed
in these submission notes.

## Rejected directions and next work

The earlier 375-cycle nonce-64 variant fails the quantitative security requirement:
a chosen-message collision attack exceeds the permitted bound by at least 7.28x.
This candidate retains the verified construction's 128-bit nonce. An earlier
mixed-state placement also corrupted four unread input bytes; retain the shifted
boundary and both full boundary tops in the root input.

The denser packing was missed by counting every body as a 64-instruction allocation.
It is distinct from dispatching three chain digits together: this still dispatches
two digits, while packing three independent bodies into one coarse-digit row.
Future work could explore dispatch encodings or a stronger availability/freshness
argument. Neither the histogram search nor these layouts establish a global optimum.

The score is not hardware latency or zkVM proving time. REMU may be expensive on a
physical core, and a zkVM must charge real arithmetic, memory and hash-precompile
traces. Fewer hashes and a smaller image are potentially useful across those models,
but no hardware or zkVM wall-time benchmark is claimed.
