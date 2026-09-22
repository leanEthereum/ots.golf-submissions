# RISC-V upper bound: 377-cycle mixed-width candidate

The complete Lean certificate proves correctness, signing availability, resource limits,
127-bit strong security, exact machine refinement on every raw input, and a worst-case
377-cycle bound. Official service validation is pending.

The candidate retains a 128-bit nonce and uses 32 hash chains: eight with 192-bit states
and twenty-four with 160-bit states. Its signature occupies exactly 5504 bits. The index
has digit widths `[5,3,5,3]` followed by 28 four-bit digits and accepts digit sum 160.
Verification executes `32 + 160 = 192` chain hashes. The root input has 6272 bits,
so the complete oracle algorithm costs at most 206 compressions.

The machine processes the wide states forwards and expands the packed narrow states
backwards. Each narrow chain's first hash reads its packed input; a pointer update then
selects the expanded slot for its remaining hashes. Completed hash outputs form the root
input directly: seven low 192-bit slices, two full tops, and twenty-three high 192-bit
slices. This layout avoids a separate root-copy pass while preserving unread inputs.

Scalar 16-bit lanes encode two digits and their dispatch address. A `REMU` by 65535
sums four bounded lanes. Halfword loads and `JALR` dispatch into replicated hash sequences.
The executed cost is 42 for index processing, 313 for all chain blocks, and 22 for the
root and decision. The image contains 15,412 instructions and 104 data bytes: 61,752 bytes.

| Files | Proof responsibility |
|---|---|
| `Names`, `Tree`, `Cuts`, `FixedChoice`, `Scheme`, `Valid` | Mixed-width graph, digit layout, cuts and accepted-index count |
| `Values`, `Events`, `Resample`, `GoodRec`, `Availability`, `Main`, `Wire` | Security, signing availability, resource limits and raw signature algorithm |
| `Payload`, `ForestVerifier`, `ForestVerifierProof`, `Reader` | Wire permutation and sequential oracle interpreter |
| `MixedProgram` | Concrete admitted machine image and image-size bound |
| `MixedLanes`, `MixedIndexArith`, `MixedIndexPhase`, `MixedDispatchArith` | Index query, rejection branches, REMU sum and dispatch words |
| `MixedLayout`, `MixedMemory`, `MixedPayload`, `MixedRootMemory` | Packed inputs, reverse writes and exact root serialization |
| `MixedChainStart`, `MixedChainSteps`, `MixedPrepare`, `MixedChain` | Chain entry, arbitrary oracle answers and remaining hash steps |
| `MixedCode`, `MixedJump`, `MixedDispatch`, `MixedLanding` | Packed jump targets and replicated instruction locations |
| `MixedPair`, `MixedPhase`, `MixedRoot`, `MixedVerifier` | Complete execution composition and cycle accounting |
| `Candidate`, `Solution` | Public submission, 377-cycle certificate and image-size theorem |

This extends dhsorens's paired-dispatch construction and Alexander Hicks's verified
393-cycle submission, assisted by GPT-6. See `NOTES.md` for the design tradeoffs and
rejected nonce-64 proposal. Rules: [ots.golf/rules](https://ots.golf/rules).

For official validation, from the repository root:

```sh
python3 /path/to/current-contract/verifier/verify.py upper-riscv \
  --source . --trusted /path/to/current-contract
```

Development uses trusted core `1bd23e523bae3bb49188acea055e3c93c6eca70b`.
Local Lean checks do not replace the service verdict.
