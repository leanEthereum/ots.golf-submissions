# leanISA — 85343 cycles

This root replaces the bytecode of the 170549-cycle baseline (PR #31) with a forced-dispatch
design; the design notes and the executable cost model are in `NOTES.md`. The scheme
and its proofs (`Algorithms`, `Encoding`, `Checksum`, `Correctness`, `Security` and its
dependencies, `Wire`, `Resources`, `BasicProperties`) are unchanged.

- **Bytecode** (`MachineProgram.lean`): `logSize = 17`, `memLog = 16`, only `XOR`, `MUL`, `SET`,
  `BLAKE2S` and `JUMP`. Each of the 34 chains starts with a `JUMP` tree that selects the signed
  digit: a Rice(2) prefix tree for chains 0..31 and 33 (depth `⌊e/4⌋ + 3`), a unary tree
  31, 30, …, 0 for `c_hi`. Every `JUMP` target is a `SET` constant in the slot just before it.
  The reached leaf hashes the pinned signature word, then the chain runs its remaining
  `254 − e` steps; unused slots are `.pad` traps. Digits are tied to the pinned message cells
  by XOR-accumulated byte words, and the checksum is checked in the exponent as a product of
  the leaves' landing constants. The halt falls through into the sentinel.
- **Execution** (`MachineRun`, `MachineWalk`, `MachinePath`): every completing run, on any
  image, is the walk of one leaf vector `E`, with `totalSteps E` instructions and cost
  `totalCost E`.
- **Cycles** (`MachineCycles`): the hash-free relations force the checksum identity
  `Σ_{k<32} E k + 256·E 32 + E 33 = 8160`, and under it `totalCost E ≤ 85223`, so every
  completing run costs at most `85223 + 120 = 85343`. The bound is attained by the honest run
  on the all-zero message (733 non-hash instructions and 8449 `BLAKE2S`; checked by
  `rt_model.py`, not in Lean).
- **Soundness** (`ConstraintMath`, `MachineSound`, `MachineFaithful.fixed_sound`): the path
  relations force the verifier's digits, chain values and root on any committed image.
- **Faithfulness** (`MachineProver`, `MachineHonest`, `MachineFaithful`): the honest image
  satisfies every relation on the path of `dig m` exactly when the verifier accepts, and the
  run then completes in `totalSteps (dig m)` steps.
- `seededRows = 2^17 + 2^16 < 2^20`.

Build with `lake build Submissions.UpperLeanIsa.Solution`.

---

# leanISA baseline — work in progress

This is an unfinished candidate, not a certified competition entry. There is no cycle
claim, `Solution.lean`, or exported `Submission.Certificate` yet.

The candidate uses 34 Winternitz chains: 32 base-256 message digits and two checksum
digits. Each chain value has 128 bits, giving a 4,352-bit signature. Every chain step
includes its chain number and position in an explicit 896-bit oracle query. Root
absorption uses distinct position tags (35 down to 2) and a full 256-bit chaining
state. Chain steps use metadata 1. All honest query positions are therefore distinct.

Checked in Lean against core `2d900ae486930689af01a6963d58c574cf17e5f7`:

- Distinct messages have incomparable checksum encodings.
- Signatures have exactly 4,352 bits; oversized raw signatures are rejected.
- Signing never fails, and verification is deterministic.
- Encoding and decoding round-trip in both directions, with no alternative encoding
  of the same signature words.
- Perfect correctness holds under the shared cached random oracle, for every
  public-key-dependent message choice. All eight `scheme.Admissible` fields are proved.
- Key generation and verification each cost at most 17,408 compressions; signing
  costs at most 17,340. All three fit the current 2²⁰ budgets on every oracle path.
- A structural forgery theorem covers both new-message and same-message forgeries:
  acceptance of a different pair requires a hidden chain word or a second preimage
  along the evaluated chain/root paths.
- For a fixed honest record, an adaptive computation starting with its programmed
  cache finds a new matching hash output with probability at most `B / 2^129`,
  where `B` bounds its model compression cost.
- Conditioned on the public information at any signing cut, guessing a hidden
  chain input has the same adaptive per-compression bound. Exposed and hidden
  cache entries form a disjoint partition.
- A coupling theorem bounds the change in any bounded payoff when hidden programmed
  answers are replaced by fresh oracle answers. These lemmas are not yet assembled
  into the contract's full security experiment.
- Programmed records reproduce the algorithm's chain values, signed words, and
  public key. Distributional equivalence to honest key generation remains to prove.
- Signing against any cache extending the honest record returns its recorded
  signature and leaves the cache unchanged, for every chosen message.

The compression bounds are algorithm bounds, **not leanISA cycle scores**.

Still required:

- The contract's strong-unforgeability theorem. Its 127-bit target has not yet been proved
  for this construction; the parameters remain provisional until that proof is complete.
- Concrete leanISA bytecode and an honest memory-filling strategy.
- Machine faithfulness, soundness, a universal cycle bound, and the seeded-row bound.
- The exact competition exports and a successful official verifier run.

Build the current modules with the updated trusted core's Lean project and this root
available at `formal/Submissions/UpperLeanIsa`:

```sh
lake build Submissions.UpperLeanIsa.Replay
```

`Checksum.lean` adapts the namespace and module header of VCVio's
[`HashSig/SLHDSA/WotsChecksum.lean`](https://github.com/Verified-zkEVM/VCVio/blob/25f26bfee60d6700644eb1a69f091091948f15da/HashSig/SLHDSA/WotsChecksum.lean),
by Vitalik Buterin, Nicolas Consigny, and Alexander Hicks. Its Apache-2.0 copyright
notice is retained; the repository's `LICENSE` contains the license.

`Cache.lean`, `IUB.lean`, and `Master.lean` adapt the generic proofs in the
[checked RISC-V submission from PR #5](https://github.com/leanEthereum/ots.golf-submissions/tree/2d25dd58d7a2fa1fe3ec1bf13be5240ccd04631f/formal/Submissions/UpperRiscv),
credited to Tom Wambsgans. The finite-word counting and resampling proofs adapt
`Values.lean` and `Resample.lean` from the
[RISC-V snapshot in PR #15](https://github.com/leanEthereum/ots.golf-submissions/tree/a12c7abf5958fc85a726cbbf4010df416c0fa9d4/formal/Submissions/UpperRiscv),
credited to Holindauer and Claude Fable 5.1, building on that earlier submission.
Imports and namespaces remain local to this root. New and adapted work here was
prepared with assistance from Codex.
