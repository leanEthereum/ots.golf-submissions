# Upper bound: 100 compressions

`Solution.lean` exports an oracle algorithm, admissibility, 127-bit strong
unforgeability, and an all-input verification bound of 100 compressions.
The complete certificate passed a frozen dependency rebuild and independent
kernel replay with pinned Lean 4.33.1. Exact export-type, transitive-axiom,
protected-source and submission-policy audits also pass.
Official hosted verification is pending.

The improvement from the verified 102 construction comes from a tighter
index-security proof. The index retains 127 bits while the nonce keeps 128.
The new proof uses the full signing-budget reservation and an exponential cache
potential. This halves the required cut family at the same signing success rate.

| Quantity | Exact value |
|---|---:|
| Key generation | 995 compressions |
| Signature | 128 nonce bits + 42*128 disclosed bits = 5504 bits |
| Accepted cut classes | 45*2^108 |
| Index query | 1 compression |
| Chain reconstruction | 82 compressions |
| Group hashes | 12 compressions |
| Public-key root | 5 compressions |
| Worst-case verification | 100 compressions |
| Signing failure | At most 2^-128 in 2^20 trials |

## Proof map

- `IndexedScheme`, `IndexedSampling`, `IndexedResources`, `IndexedCorrectness`,
  `IndexedAvailability`, `IndexedFreshness`: the submitted 127-bit index, actual
  signing and verification programs, correctness, availability and resources.
- `ShallowNames`, `ShallowTree`, `ShallowCount`, `ShallowCount100`, `ShallowCuts`,
  `ShallowScheme`: the fixed forest and its rank-82 family.
- `RepeatedFibers`, `TightRow`, `TightDrift`, `TightPotential`: repeated-class
  counting, the row bound, exponential drift and the actual cache potential.
- `SigningReserve`, `ReservedHazard`, `MasterReserve`: reserve the full signing
  budget and carry it through the probabilistic proof.
- `ShallowValues`, `ShallowResample`, `ShallowEvents`, `ShallowPotentials`,
  `ShallowStageB`, `ShallowAssembly`, `ShallowMain`: the common security analysis
  for hidden inputs, spurious reconstruction and index replay.
- `ShallowResources`, `WireAdapter`, `ShallowWire`, `Solution`: exact protected
  interfaces, canonical raw encoding and final exports.

Generic supporting lemmas and unaffected historical proof modules are retained.
The obsolete `IndexedPotential` is replaced by the new potential modules.

`NOTES.md` explains the technique, evidence, unsuccessful experiments and next
directions. On a supported verifier host, run from the checkout root:

```sh
python3 .contract/verifier/verify.py upper-compressions --source .
```
