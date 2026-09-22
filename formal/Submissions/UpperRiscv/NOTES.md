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
