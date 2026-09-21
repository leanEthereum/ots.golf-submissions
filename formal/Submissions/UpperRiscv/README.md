# RISC-V upper bound: 430 cycles

A certified RV64IM verifier for a bare-chain forest one-time signature: every execution,
accepting or rejecting, terminates within 430 cycles and computes exactly the Lean verifier's
oracle computation. `Solution.lean` exports `OptimalOTS.Challenge.UpperRiscv.submission` and
`certificate` at the claim in `claim.txt`. The rules are on
[ots.golf/rules](https://ots.golf/rules); the proof guide is
[upper-riscv.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/upper-riscv.md).

## Construction

- **Scheme.** 28 hash chains of 32 levels under one root (`Names.lean`), with a complete Lean
  certificate for admissibility, 127-bit strong security and verification within 256
  compressions. Chain values are 192 bits and chain inputs carry no header and no level tag: a
  chain step hashes the 192-bit value, and the *high* 192 bits of the 256-bit answer are the next
  value. The index is `H(pk ‖ message ‖ nonce)` read as byte fields: the low five bits of bytes 0–15,
  the low four bits of bytes 16–23 and the low four bits of the *even* bytes 24, 26, 28, 30
  (`Valid.lean`, `wid` and `slotOf`); the odd bytes 25, 27, 29, 31 have width zero. It is accepted
  when the 28 fields sum to
  215. Chain `k` is disclosed at position `31 - field k` (`FixedChoice.lean`), so a signature is
  the nonce and 28 values, exactly 5504 bits. The root input is 5440 bits: the low 192 bits of
  the tops of chains 0–26 followed by the full top of chain 27; the public key is the low 128 bits
  of its hash. The three input lengths (192, 5440 and the 512-bit index query) are distinct.
- **Security without tags.** Every chain query is a candidate preimage for all 896 chain hash
  nodes at once, but each honest output is matched on 192 bits, so the multi-target second-preimage
  event costs `896 · 2^-192 < 2^-128` per query (`Values.lean`, `spr_charge`). The keygen cache is
  handled through *good records* — pairwise distinct keygen points and no honest output simulating
  another hash node (`GoodRec.lean`) — whose failure weight `δ = 2 · 897² · 2^-192` is added to
  the final bound: `probTrue ≤ 2ε(B - 907) + 2δ < B / 2^127` (`Assembly.lean`, `Main.lean`).
- **Machine image.** `Program.lean` is a 890-instruction RV64IM image with a 72-byte data image.
  The index phase hashes the 512 bits `pk ‖ message ‖ nonce` in place from the loader's
  public-key pointer, which is where `x10` already points (the index query is
  `H(swapHalves (m ‖ pk ‖ η))`, and `swapHalves` is injective), rejects
  unless the signature has 5504 bits, builds seven lane words holding `4 · field` in 16-bit
  lanes with one shift and one mask each, checks the field sum with one multiplication, and
  stores `jumpBase - 4 · field` for every chain in the 56 bytes just below the signature, over the
  consumed public key and message. Spreading the last four chains over the even bytes 24, 26, 28,
  30 puts all four in a single lane word, so seven lane words — one per group of four chains —
  suffice, and the extra `0x003C003C` mask constant is gone. A chain
  block is four instructions — advance the input pointer to the slot, point the answer buffer
  eight bytes below it, load the jump target relative to that buffer, jump — followed by a table
  of `field + 1` `ECALL`s. Chains run from 0 up: hashing a slot writes the answer eight bytes
  below, so the high 192 bits land on the slot for the next step and the low eight bytes overwrite
  only the tail of the previous, already final top. After the last chain the 680 bytes from
  `sig + 8` are the root input as it stands; its hash is written where chain 27 left its answer
  buffer. The root pointer is one `ADDI` from the last slot pointer, the root length one `ADDI`
  from the checked signature length still in `x13`, and the decision branches on each mismatching word to a rejection placed after the accepting HALT.
- **Availability.** `compW wid 32 215 ≥ 712 · 2^105` indices are accepted (`Valid.lean`), so a
  fresh index is accepted with probability at least `712 / 2^23` and the `2^20` signing trials
  fail with probability at most `0.882 · 2^-128`; with the bad records this stays within `2^-128`
  (`Availability.lean`). Target 214 would not: its failure probability is about `2^-118`.
- **Cycle count.** One cycle per executed instruction and eleven for the 5440-bit root hash: 55
  for the index phase, `4 + (field + 1)` per chain (355 in all, since the fields sum to 215), and
  20 for the root and the decision (2 + 11 + 7, on every path).

## Proof map

| File | Content |
|---|---|
| `Names.lean`, `Tree.lean`, `Cuts.lean`, `FixedChoice.lean`, `Scheme.lean` | the graph, its cuts and the field layout |
| `Digits.lean`, `Count.lean`, `Valid.lean`, `PackFiber.lean`, `PackCount.lean` | the byte-field index, its counting and packing |
| `Values.lean`, `Events.lean`, `Resample.lean`, `GoodRec.lean`, `StageB.lean`, `Assembly.lean`, `Main.lean` and the index-side files | 127-bit strong security |
| `Wire.lean`, `WireAdapter.lean` | the OTS certificate transferred to raw signature bit strings |
| `ForestVerifier.lean`, `ForestVerifierProof.lean`, `Reader.lean` | the explicit interpreter and its sequential reader |
| `Lanes.lean`, `IndexLanes.lean`, `IndexArith.lean`, `IndexPhase.lean` | the index query, the lane arithmetic and the rejections |
| `ChainContext.lean`, `ChainPrologue.lean`, `ChainSteps.lean`, `ChainBlock.lean`, `ChainPhase.lean` | the chain blocks and their cost |
| `RootPhase.lean` | the root hash and the decision |
| `Verifier.lean` | `image_refines`: the image equals the certified verifier on every input, within 430 cycles |
| `Refines.lean`, `BlockExecution.lean`, `MachineFacts.lean`, `MachineMemory.lean`, `LoaderProof.lean`, `CopyProof.lean`, `HashOutput.lean` | machine semantics, memory and reusable execution rules |
| `Candidate.lean` | `machineCertificate`, bundling the OTS and machine proofs |
| `Solution.lean` | the exported declarations |

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py upper-riscv --source .
```
