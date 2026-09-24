# RT-128: base-128 Winternitz under the RT bytecode, 49335 cycles

## Idea

The 85343 record (RT, PR #35) spends 84490 of its cycles on `BLAKE2S`: 34 base-256 chains, so
the worst message (all zero digits) walks 8415 chain steps plus 34 root absorptions. Its notes
put the bytecode-only floor about 730 cycles lower. The large lever is the scheme, not the
bytecode.

With 128-bit chain words the 5504-bit signature limit allows at most 43 words. Uniform base 64
needs 45 words, so base 128 is the smallest uniform base that fits:

| base | message digits | checksum digits | words | worst chain steps | root | BLAKE2S |
|---|---:|---:|---:|---:|---:|---:|
| 256 (RT) | 32 | 2 | 34 | 8415 | 34 | 8449 |
| 128 (this) | 37 | 2 | 39 | 4826 | 39 | 4865 |

This root keeps RT's scheme structure, proof architecture and bytecode design, with new
parameters.

## Construction

- Scheme: `digits m = wotsFullDigits (digitsOfBaseW m.toNat 128 37) 128 37 2`. There are 39
  chains of 127 steps. The signature is 4992 bits, and root absorption tags run from 40 down to 2.
  The generic checksum lemmas take `w` as a parameter, and the security charge (one location per
  query, `2^-129` per compression) does not depend on the chain count. Every scheme and security
  file therefore ports by changing constants.
- Digit `k` is `m.toNat / 128^(36-k) % 128` and sits at message bit `7(36-k)`. Digits 0..17
  lie in message cell 2 and digits 19..36 in cell 1. Digit 18 straddles the two cells: its
  `e % 4` is cell-1 bits 126..127 and its `e / 4` is cell-2 bits 0..4. The leaf of chain 18
  closes cell 2 with `XOR (acc17, posCell (e/4)) → 2` and opens cell 1 with
  `SET acc18 := w((e%4) <<< 126)`. Digit 0 has only 4 bits. Chain 0 therefore has only 16
  leaves, which is also what makes `e <<< 124` injective.
- Bytecode: `logSize = 16`, `memLog = 16`. There are 129 constant `SET`s (positions 1..127, `K0`,
  length). Dispatch uses Rice(1) trees (unary on `e/2`, then one binary node), and
  `c_hi ∈ [0, 36]` uses a descending unary tree. Leaves hash straight from the pinned `σ` cell.
  The checksum is checked in the exponent (`Σ_{k<37} E_k + 128·E_37 + E_38 = 4699`), and the halt
  falls through into the sentinel.
- The Rice parameter was chosen by exhaustive search over `r ∈ 0..4` for the message, top and
  `c_lo` trees, using a DP over all feasible leaf vectors. `r = 1` everywhere is optimal in that
  family (49214). Between digit sums 0 and 91 the hash count is flat at 4826, so the worst case
  is decided by dispatch alone. Ascending Rice(1) on both the message chains and `c_lo` keeps that
  plateau flat.

## Result

- Worst case (message 0: `c_hi = 36`, `c_lo = 91`): 5429 steps, 4865 `BLAKE2S`, 49214 cycles.
- Proved bound: `chainCost k e + 9e ≤ 1277 + tieLen k` and `hiCost c + 12c ≤ 1348`, which with the
  checksum identity give `totalCost E ≤ 8175 + 1140·E_37 ≤ 49215`. The claim is
  `49215 + 120 = 49335`, one cycle above the exact worst case because of the `⌊e/2⌋` floor.
- `seededRows = 2^16 + 2^16`.
- The whole root builds in about 65 s from a warm Mathlib.

## Executable model

`b128_model.py` (not included, same shape as RT's `rt_model.py`) builds the full 2^16-slot
bytecode and simulates walks for 400 honest messages and 300 arbitrary leaf vectors. It checks the
closed forms, the tie arithmetic and both cost bounds.

## What to try next

- Mixed radix. Message cell 1 = 2×7 + 19×6 bits and cell 2 = 8×7 + 12×6 bits give 41 aligned
  message digits (no straddle) plus two 6-bit checksum digits: 43 words. The worst case is then
  about 3276 chain steps + 43 root = 3319 `BLAKE2S`, roughly 34k cycles. This needs a mixed-radix
  checksum-incomparability proof (`Checksum.lean` is uniform-`w`) and dependent chain lengths in
  `Records`/`KeygenBridge`.
- Root packing: absorb four words per `BLAKE2S` (the message block has four 128-bit cells). This
  saves about 29 `BLAKE2S` but changes `RootBinding` and the keygen bridge.
- Tighter tree shapes at the leaf-0 end (leaf 0 at depth 1), and RT's §10.3 micro-savings (drop
  chain 0's `MUL`).
