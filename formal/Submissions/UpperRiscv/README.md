> **Work in progress:** This branch targets 377 cycles. The mixed-width oracle algorithm is certified, but the assembly refinement is unfinished. Inherited 393-cycle machine exports below are not a certificate for this branch. See NOTES.md.

# RISC-V upper bound: 393 cycles

A certified RV64IM verifier for a bare-chain forest one-time signature: every execution,
accepting or rejecting, terminates within 393 cycles and computes exactly the Lean verifier's
oracle computation. `Solution.lean` exports `OptimalOTS.Challenge.UpperRiscv.submission` and
`certificate` at the claim in `claim.txt`, and `image_size` (the image is 50076 bytes, under
the 1 MiB limit). The rules are on
[ots.golf/rules](https://ots.golf/rules); the proof guide is
[upper-riscv.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/upper-riscv.md).

This extends dhsorens's 394-cycle construction. The packed index fold now uses
`SRLI; ADD; AND` with broadcast mask `0x03fc`, saving one instruction.
The scheme and its complete oracle transcript are unchanged. See `NOTES.md`
for validation status and attribution.

## Construction

- **Scheme.** 28 hash chains of 32 levels under one root (`Names.lean`), with a complete Lean
  certificate for admissibility, 127-bit strong security and verification within 256
  compressions. Chain values are 192 bits and chain inputs carry no header and no level tag: a
  chain step hashes the 192-bit value, and the *high* 192 bits of the 256-bit answer are the next
  value. The index is `H(pk ‖ message ‖ nonce)` read as 28 digits in the 16-bit lanes of its
  four words: each lane of words 0–2 holds a five-bit digit at lane bits 2–6 (chain `2p`) and a
  four-bit digit at lane bits 10–13 (chain `2p + 1`), and each lane of word 3 a five-bit digit at
  lane bits 2–6 (chains 24–27) (`Valid.lean`); it is accepted when the 28 digits sum to 215. Chain `k` is disclosed at position `31 - field k` (`FixedChoice.lean`), so a signature is
  the nonce and 28 values, exactly 5504 bits. The root input is 5440 bits: the low 192 bits of
  the tops of chains 0–26 followed by the full top of chain 27; the public key is the low 128 bits
  of its hash. The three input lengths (192, 5440 and the 512-bit index query) are distinct.
- **Security without tags.** Every chain query is a candidate preimage for all 896 chain hash
  nodes at once, but each honest output is matched on 192 bits, so the multi-target second-preimage
  event costs `896 · 2^-192 < 2^-128` per query (`Values.lean`, `spr_charge`). The keygen cache is
  handled through *good records* — pairwise distinct keygen points and no honest output simulating
  another hash node (`GoodRec.lean`) — whose failure weight `δ = 2 · 897² · 2^-192` is added to
  the final bound: `probTrue ≤ 2ε(B - 907) + 2δ < B / 2^127` (`Assembly.lean`, `Main.lean`).
- **Machine image.** `Program.lean` is a 12493-instruction RV64IM image with a 104-byte data
  image. The index phase hashes the 512 bits `pk ‖ message ‖ nonce` in place from the loader's
  public-key pointer, which is where `x10` already points (the index query is
  `H(swapHalves (m ‖ pk ‖ η))`, and `swapHalves` is injective), rejects
  unless the signature has 5504 bits, masks the four answer words into four lane words holding
  `4 · dA + 1024 · dB` per lane (one mask each), folds the coarse digits onto the fine ones and
  checks the digit sum with one multiplication, and stores `base − (4 · dA + 1024 · dB)` for every
  block in the 32 bytes just below the signature, over the consumed public key and message. The
  chains run in 16 blocks. A block's prologue is four instructions — advance the input pointer to
  the slot, point the answer buffer eight bytes below it, load the dispatch halfword relative to
  that buffer, jump. For the twelve *pair* blocks (chains `2q` and `2q + 1`) the jump selects one
  of sixteen 64-instruction copies of the block by `dB` and the hash step by `dA`: `dA + 1`
  `ECALL`s for chain `2q`, two pointer moves, `dB + 1` `ECALL`s for chain `2q + 1`, then the next
  prologue. The four remaining chains have single 32-step tables. Chains run from 0 up: hashing a
  slot writes the answer eight bytes below, so the high 192 bits land on the slot for the next
  step and the low eight bytes overwrite only the tail of the previous, already final top. After the last chain the 680 bytes from
  `sig + 8` are the root input as it stands; its hash is written where chain 27 left its answer
  buffer. The root pointer is one `ADDI` from the last slot pointer, the root length one `ADDI`
  from the checked signature length still in `x13`, and the decision branches on each mismatching word to a rejection placed after the accepting HALT.
- **Availability.** `compW wid 28 215 ≥ 712 · 2^105` indices are accepted (`Valid.lean`), so a
  fresh index is accepted with probability at least `712 / 2^23` and the `2^20` signing trials
  fail with probability at most `0.882 · 2^-128`; with the bad records this stays within `2^-128`
  (`Availability.lean`). Target 214 would not: its failure probability is about `2^-118`.
- **Cycle count.** One cycle per executed instruction and eleven for the 5440-bit root hash: 42
  for the index phase, `6 + (dA + 1) + (dB + 1)` per pair block and `4 + (d + 1)` per single
  block (331 in all, since the digits sum to 215), and 20 for the root and the decision
  (2 + 11 + 7, on every path).

## Proof map

| File | Content |
|---|---|
| `Names.lean`, `Tree.lean`, `Cuts.lean`, `FixedChoice.lean`, `Scheme.lean` | the graph, its cuts and the field layout |
| `Digits.lean`, `Count.lean`, `Valid.lean`, `PackFiber.lean`, `PackCount.lean` | the lane-field index, its counting and packing |
| `Values.lean`, `Events.lean`, `Resample.lean`, `GoodRec.lean`, `StageB.lean`, `Assembly.lean`, `Main.lean` and the index-side files | 127-bit strong security |
| `Wire.lean`, `WireAdapter.lean` | the OTS certificate transferred to raw signature bit strings |
| `ForestVerifier.lean`, `ForestVerifierProof.lean`, `Reader.lean` | the explicit interpreter and its sequential reader |
| `Lanes.lean`, `IndexLanes.lean`, `IndexArith.lean`, `IndexPhase.lean` | the index query, the lane arithmetic and the rejections |
| `ChainContext.lean`, `ChainPrologue.lean`, `ChainSteps.lean`, `ChainBlock.lean`, `ChainPhase.lean` | the chain blocks and their cost |
| `RootPhase.lean` | the root hash and the decision |
| `Verifier.lean` | `image_refines`: the image equals the certified verifier on every input, within 393 cycles |
| `Refines.lean`, `BlockExecution.lean`, `MachineFacts.lean`, `MachineMemory.lean`, `LoaderProof.lean`, `CopyProof.lean`, `HashOutput.lean` | machine semantics, memory and reusable execution rules |
| `Candidate.lean` | `machineCertificate`, bundling the OTS and machine proofs |
| `Solution.lean` | the exported declarations |

## Verify

From the root of this repository:

```sh
python3 /path/to/current-contract/verifier/verify.py upper-riscv \
  --source . --trusted /path/to/current-contract
```

Use the service's current trusted contract. This candidate was developed against
`1bd23e523bae3bb49188acea055e3c93c6eca70b`; the repository's historical `.contract`
pointer is preserved. Local Lean checks do not replace the service verdict.
