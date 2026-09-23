# leanISA baseline — 170549 cycles

This root completes the leanISA Winternitz baseline started in PR #23 by Tom Wambsgans. The
scheme (`Algorithms.lean`) is unchanged: 34 chains of 128-bit words, 32 base-256 message digits
plus two checksum digits, every chain step tagged with its chain and position, and an MD-style
root fold with distinct metadata. What this root adds:

- **Strong unforgeability** (`Security.lean`, `theorem secure`), assembled from PR #23's
  ingredients in two stages: `Stages`, `Budget`, `KeygenBridge` (key generation as a uniform
  average over records), `Transcript`, `CutTargets`, `Events` (an accepted fresh forgery is a
  hidden-word hit or a cut-target hit on the exposed run), `StageB`, `StageA` (supermartingale
  via `master_family`). Two charges of `2^-129` per compression give `B / 2^128 < B / 2^127`.
- **Bytecode** (`MachineProgram.lean`): straight-line, `fp = 1` throughout, one final `JUMP`.
  Each chain runs all 255 steps; a thermometer mux feeds the signature word in at the signed
  digit and hashes it as a dummy before. Digits are tied to the pinned message cells by
  XOR-accumulating shifted byte constants; the checksum is checked in the exponent
  (`g^C = g^(256·c_hi) · g^(c_lo)`). 92093 instructions, 8704 `BLAKE2S`.
- **Execution** (`MachineRun.lean`): every completing run executes exactly the 92093
  instructions, so the cost is `92093 + 9 · 8704 = 170429`, plus the 120-cycle boundary charge.
- **Soundness and faithfulness** (`ConstraintMath`, `MachineProver`, `MachineSound`,
  `MachineFaithful`): the constraints force the verifier's chain values, digits and root on any
  committed image; the honest prover's image satisfies all of them exactly when the verifier
  accepts.
- `seededRows = 2^17 + 2^17 < 2^20`.

The design is deliberately simple rather than cycle-optimal; it is a baseline.

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
