# RISC-V upper bound: 702 cycles

A certified RV64IM verifier for a flat forest one-time signature: every execution, accepting or
rejecting, terminates within 702 cycles and computes exactly the Lean verifier's oracle
computation. `Solution.lean` exports `OptimalOTS.Challenge.UpperRiscv.submission` and
`certificate` at the claim in `claim.txt`. The rules are on
[ots.golf/rules](https://ots.golf/rules); the proof guide is
[upper-riscv.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/upper-riscv.md).

## Construction

- **Scheme.** 32 hash chains of length 15 under one root (`Names.lean`), with a complete Lean
  certificate for admissibility, 127-bit strong security and verification within 173
  compressions. The index, the low 128 bits of `H(message ‖ nonce)`, is accepted when its 32
  nibbles sum to 160; every nibble value is allowed (`Valid.lean`). Chain `k` is disclosed at
  position `15 - nibble k` (`FixedChoice.lean`), so a signature is the nonce and 32 words, 4224
  bits. A chain input is the chain's value above a 64-bit header, the slot address of the chain
  and a level tag (`Constants.lean`); the root input is the 32 chain tops with the headers between
  them, 6080 bits. The three input lengths (192, 6080 and the 384-bit index query) are distinct.
- **Machine image.** `Program.lean` is a 1337-instruction RV64IM image with a 64-byte data image.
  The index phase hashes `nonce ‖ message` in place, builds eight lane words holding
  `8 · nibble` in 16-bit lanes, checks the nibble sum with one multiplication, and stores a jump
  target for every chain. A chain block copies the disclosed word into its slot, writes the
  header, loads its jump target and runs the last `nibble` of 15 two-instruction steps: store the
  level tag, hash in place. The slots, 24 bytes apart, then form the root input.
- **Cycle count.** One cycle per executed instruction and twelve for the 6080-bit root hash: 71
  for the index phase, `9 + 2 · nibble` per chain (608 in all), and 23 for the root and the
  decision.

## Proof map

| File | Content |
|---|---|
| `Names.lean`, `Tree.lean`, `Cuts.lean`, `FixedChoice.lean`, `Scheme.lean` | the graph, its cuts and the nibble layout |
| `Values.lean`, `Events.lean`, `Resample.lean`, `StageB.lean`, `Assembly.lean`, `Main.lean` and the index-side files | 127-bit strong security, ported from the forest proof |
| `Wire.lean`, `WireAdapter.lean` | the OTS certificate transferred to raw signature bit strings |
| `ForestVerifier.lean`, `ForestVerifierProof.lean`, `Reader.lean` | the explicit interpreter and its sequential reader |
| `Lanes.lean`, `IndexLanes.lean`, `IndexArith.lean`, `IndexPhase.lean` | the index query, the lane arithmetic and the rejections |
| `ChainContext.lean`, `ChainPrologue.lean`, `ChainSteps.lean`, `ChainBlock.lean`, `ChainPhase.lean` | the chain blocks and their cost |
| `RootPhase.lean` | the root hash and the decision |
| `Verifier.lean` | `image_refines`: the image equals the certified verifier on every input, within 702 cycles |
| `Refines.lean`, `BlockExecution.lean`, `MachineFacts.lean`, `MachineMemory.lean`, `LoaderProof.lean`, `CopyProof.lean`, `HashOutput.lean` | machine semantics, memory and reusable execution rules |
| `Candidate.lean` | `machineCertificate`, bundling the OTS and machine proofs |
| `Solution.lean` | the exported declarations |

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py upper-riscv --source .
```
