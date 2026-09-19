# Upper bound: 104 compressions

An admissible, 127-bit strongly secure one-time signature whose verification costs at most 104
compressions on every input and oracle-answer path. `Solution.lean` exports `scheme`,
`admissible`, `secure` and `cost` at the claim in `claim.txt`. The rules are on
[ots.golf/rules](https://ots.golf/rules); the proof guide is
[upper-compressions.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/upper-compressions.md).

## Construction

The forest of Section 7 of the paper with six subtrees instead of seven, wrapped as a generic
oracle algorithm:

- **Graph.** 2,396 nodes: 54 hash chains of length 14, grouped three by three into 18 group
  digests, then three by three into 6 subtree digests, and one root.
- **Separation.** Every hash input starts with an explicit 16-bit tweak naming its node, charged
  in the input's full length: 144, 400 or 784 bits (the root costs two compressions).
- **Key generation** costs 782 compressions.
- **Signing** tries at most `2^20` distinct nonces; a signature carries a 128-bit nonce and at
  most 5,376 disclosed bits (42 values). Availability is proved with failure at most `2^-256`.
- **Verification** hashes the 384-bit message-and-nonce input, then reconstructs the selected cut
  within 103 further compressions: `1 + 103 = 104`. The cuts reveal one subtree digest and two
  group digests, six group digests, or one subtree digest and three group digests, with the
  remaining chains at total cost 83, 83 or 84: more than `2^115` cuts of at most 42 values.

## Proof map

| File | Content |
|---|---|
| `TypedScheme.lean` | internal interface: oracle algorithms with a typed signature and an injective encoding |
| `Adapter.lean` | a DAG scheme as a `TypedScheme`; equal security experiments |
| `AlgorithmCosts.lean`, `Resources.lean` | pathwise costs, wire size and rejection of oversized signatures |
| `KeygenSupport.lean`, `Correctness.lean` | cache consistency and perfect correctness of the adapter |
| `Deterministic.lean` | verification makes only hash queries |
| `Availability.lean` | fresh index queries and the repeated-failure bound |
| `Main.lean` and the modules it imports | the forest and its strong-security proof (`Pr[forge] ≤ (B - 782) / 2^127`) |
| `ForestAlgorithm.lean` | admissibility, security and cost of the wrapped scheme |
| `WireAdapter.lean`, `Wire.lean` | the certificate transferred to the contract's `OracleAlgorithm.Scheme` on bit strings (nonce bits, then disclosed values) |
| `Solution.lean` | the exported declarations |

The security proof's architecture is described in
[upper-bound-proof.md](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/upper-bound-proof.md).

## Verify

From the root of this repository:

```sh
python3 .contract/verifier/verify.py upper-compressions --source .
```
