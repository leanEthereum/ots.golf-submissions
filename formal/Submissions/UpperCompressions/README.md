# Upper bound: 102 compressions

An admissible, 127-bit strongly secure one-time signature whose verification costs
at most 102 compressions on every input and oracle-answer path. `Solution.lean`
exports `scheme`, `admissible`, `secure` and `cost` at the claim in `claim.txt`.
The complete certificate passes local Lean 4.33.1 checking, independent kernel
replay of all new/changed proof modules, and exact contract-type and axiom audits.
A hosted verdict is still required; this machine cannot run the official verifier's Linux sandbox.

## Construction

The previous 104-compression construction is replaced by a shallow forest and a
smaller accepted-index family. The protected oracle model and competition limits
are unchanged.

- **Graph:** 54 independent 128-bit sources, chains of length 18, 18 ternary group
  digests, and one root. There are 3,026 nodes.
- **Hash inputs:** explicit 16-bit node tags followed by the input values. Chain,
  group and root inputs have 144, 400 and 2,320 bits; the root costs five
  compressions.
- **Key generation:** `54*18 + 18 + 5 = 995` compressions.
- **Cuts:** reveal six group digests and one value from each of the other 36
  chains. Their remaining chain cost totals 84. Every cut reveals exactly 42
  words (5,376 bits) and reconstructs in `84 + 12 + 5 = 101` compressions.
- **Index family:** choose `M = 45*2^109` distinct cuts from a certified family of
  29,487,481,484,631,239,862,222,768,351,166,608 cuts. The local indexed scheme
  accepts a 128-bit hash index precisely when it is less than M.
- **Signing:** try at most `2^20` distinct 128-bit nonces. The fresh-trial success
  probability is `45/524288`; the proved failure bound is at most `2^-128`, even
  for a message chosen as a function of the public key.
- **Wire format:** a 128-bit nonce followed by the 5,376 disclosed bits, totaling
  5,504 bits. Accepted bit strings have a canonical parse.
- **Verification:** one compression for the 384-bit message-and-nonce index plus
  101 for reconstruction, giving an all-input bound of 102.

## Proof map

| Files | Content |
|---|---|
| `IndexedScheme`, `IndexedResources`, `IndexedReconstruct` | Local accepted-index parameter, typed adapter, resource bounds, verifier support |
| `IndexedSampling`, `IndexedAvailability`, `IndexedFreshness`, `ShallowAvailability` | Actual signing-loop semantics, fresh queries after keygen, and the failure bound |
| `IndexedCorrectness` | Perfect correctness for the indexed scheme |
| `IndexedCharges`, `IndexedRho`, `IndexedRows`, `IndexedPotential` | Security potential for the smaller index family |
| `ShallowNames`, `ShallowTree`, `ShallowCount`, `ShallowCuts`, `ShallowScheme` | Concrete graph, traversal, exact counting, distinct valid cuts and costs |
| `ShallowValues`, `ShallowResample`, `ShallowEvents` | Tagged keygen inputs, hidden-coordinate bounds and all strong-forgery cases |
| `ShallowPotentials`, `ShallowStageB`, `ShallowAssembly`, `ShallowMain` | Security assembly, including `Pr[forge] ≤ (B-995)/2^127` for `B ≤ 2^127` |
| `ShallowResources` | Typed admissibility and all-input 102-compression cost |
| `WireAdapter`, `ShallowWire`, `Solution` | Transfer to the protected bit-string interface and final exports |

Unchanged generic cache, graph, oracle-semantics and wire lemmas are reused from
the original certificate. The earlier concrete 104 proof modules remain in this
root. The new proof introduces no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`; it uses no `sorry` or `native_decide`.

## Verification

From the repository root, on a supported verifier host:

```sh
python3 .contract/verifier/verify.py upper-compressions --source .
```

This checkout's contract pin is unchanged. Local checks use the exact pinned Lean
release and dependency revisions. The official command currently stops because
its comparator/exporter tools are not installed. Separately, host preflight found Landlock ABI 2 rather than the
required ABI 3, and systemd 252 rejects `PrivatePIDs=yes`. The official verifier's
gates have not been bypassed. See `NOTES.md` for local verification evidence,
research history and tested alternatives. This initial submission requests the
official hosted verification of the locally checked certificate.
