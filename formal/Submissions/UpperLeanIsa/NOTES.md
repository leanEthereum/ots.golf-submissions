# 1095-cycle split-alias leanISA construction

The complete `Submission.Certificate 1095` passes a clean local build, exact
challenge comparison, allowed-axiom checking and fresh Lean kernel replay.
The competition model and admission requirements are unchanged. These are
local checks, not a hosted verdict. Historical 1096 measurements are marked below.

## Result and construction

The proved bound is `105 + 87 * 10 + 120 = 1095` cycles, compared with the complete
1110-cycle ancestor. Every completing run has 192 instructions and 975 execution
cycles before the unchanged 120-cycle public-boundary surcharge. The signature
still contains 42 disclosed 128-bit words and the full 128-bit nonce: 5504 bits.
The effective index has 127 bits. Code and memory have respectively 2^18 and
2^16 rows, totaling 327680.

The fifteen-cycle improvement is one fewer chain hash (ten cycles) and five
fewer ordinary instructions. It combines four changes:

1. A sharper linear security potential permits layer 85.
2. Mixed four-/five-child binding packets keep chains 10, 11, 36 and 41 internal
   to their group blocks. A zero-step internal child is read directly from the
   signature; a positive-step child is read from its computed top.
3. Unequal alias multiplicities within a cost band improve the distribution of
   accepted indices while respecting each actual block's ordinary-operation budget.
4. Centering the checksum and replacing the other uses of the fourteenth power
   remove one initialization, with group lengths and budgets unchanged.

Eight binding groups replace the earlier nine. Their visible parent prefixes
are positive, so each accepted tuple binds its children. Hidden coordinates are
included in the full digit tuple and its injectivity proof, but are not assumed
to be positive binding parents. The graph is acyclic and covers all 42 tops.
The verifier uses 85 chain hashes, one index hash and one root hash.

## Exact counting, not an entropy approximation

A field code selects a tuple through disjoint contiguous intervals. An interval
length is the tuple's alias multiplicity. Two tuples of the same cost can have
different multiplicities; therefore cost alone is insufficient to identify a
security tier.

`SplitIntervals`, `SplitCodec` and `FourChildCodec` prove the actual aliases,
full tuple injectivity, visible-prefix positivity and class weights. The weight
of a full index class is the product of its local multiplicities. A sparse
multiplicative dynamic program counts raw indices jointly by cost and weight,
then selects the accepted cost window 22 through 85. This yields 440 exact
weight tiers, including the exceptional local multiplicities 496 and 144.
`SplitCount` links this calculation to all actual 127-bit effective indices;
`FourChildTier` links it to the security schedule. No floating-point estimate
is used in the certificate.

The numeric schedule uses exact outward rounding at precision 2^256.
Its linear security coefficient, normalized by 2^-127, is
`1094562261779 / 2^40`, approximately 0.995499. The fresh-index drift bound is
`2189121718849 / (2^40 * 2^127)`, no greater than twice that coefficient.
Rarest-cut signing still uses 2^19 trials. The research-model failure upper
bound is approximately 0.587825 times 2^-128; Lean checks the required inequality.

The linear argument jointly accounts for new classes and repeated classes.
These are disjoint cases, not two simultaneous costs. The nonce space is twice
the effective-index space, and every nonempty class has weight at least one.
The duplicate increment is paid within the same potential, allowing a constant
fresh-query drift. Hidden key generation, post-signing, second-preimage and
signing self-collision terms remain in the proof. The competition's security
definition and budget accounting are unchanged.

This is consistent with an information-theoretic design heuristic—allocate
limited index mass where it helps the exact objective—but is not an application
of a named Shannon or Bourbaki theorem. No optimality or lower bound is claimed.

## Machine proof

The affine-frame architecture of the 1110 ancestor is retained. A fixed field
base is chosen by finite polynomial avoidance; it depends only on the table,
not on an input, execution, committed image or oracle. Per-block affine frames
remove entry jumps, and a separate checksum guard excludes prologue re-entry.

Four-child packets use a tag and the actual validated length word as metadata.
Five-child packets use the extra child word and power metadata. Additional
polynomial constraints separate the length word from the needed powers.
`SplitDomains` and `AffineDomains` prove the resulting packet/domain separation.

Eight guaranteed positive binding hashes are deducted from the checksum.
For each charged cost `c` in 0 through 16, the centered update checks
`q' = q * a^(c-6)` when `c >= 6`, or `q = q' * a^(6-c)` otherwise.
Both are one real MUL; reversing the equation executes no division instruction.
Only powers through 10 are needed for these updates. The 845 blocks that formerly
used two checksum MULs keep a counted `ONE * ONE = ONE` padding instruction.
The saving comes from removing the SET for `a^14`, not from free padding.

The new free seed is `g^sentinel * a^(s+1)`. Thirteen centered updates give
the exponent `s + 1 + (sum costs - 8) - 13*6 = s + sum costs - 85`.
The exit guard therefore forces the same full layer 85. Hint rewriting remains
restricted to actual hint cells and cannot rewrite checksum operations.

The free-stage bias is now ONE, giving frame `g^target + 1`; group stages
retain their positive-power biases. Normal and index hashes use the existing
adjacent C1/C2 words, with index metadata C11. Domain separation is proved for
these actual new query words. C1 through C13 and the length guards remain.

Mixed positive/fixed-frame collisions are excluded by polynomial avoidance.
Fixed-to-fixed landings use exact field certificates for all 4288 non-entry
free-region slots; fixed-to-initial landings cover all 26 positive initial
targets. The fixed frame at target zero is zero and its first read fails;
the proof does not assume this frame nonzero. Correct free entries are positive,
and the halt frame differs from ONE. These guards cover every admitted memory size.

The packed prefix ends at slot 250577; free blocks begin at 255615, leaving
5038 slots. There are 14820 raw group blocks. Group 7 has 996 live field codes;
the remaining 28 codes trap. The low raw bit of the first field is ignored by
the 127-bit abstract index but remains pinned by the complete 128-bit index tie.

`AffinePath`/`AffineCycles` cover every completing run and every permitted
memory size. `AffineValues`/`AffineSound` prove that an arbitrary completing
committed image implies acceptance. `AffineProver`, `AffineCells`,
`AffineHonestChain` and `AffineHonestPath` construct a faithful honest image,
including zero-step internal reads, reversed checksum MULs and counted padding.
`AffineFaithful` handles both verifier decisions.

## Validation and proof engineering

### 1095 proof port (2026-09-28)

The final 1095 sources pass a build with no prior UpperLeanIsa artifacts
(8962 jobs, 273.201 s). The rendered challenge compiles in 2.250 s; challenge
and solution exports take 4.924 s and 12.164 s. Exact statement and primitive
comparison, exported dependency-axiom checking and fresh kernel replay of
62686 declarations pass in 241.754 s total, with 196.840 s inside kernel replay.
The measured standalone stages total 534.293 s (8 minutes 54 seconds).

Peak sampled proportional memory is 11.5 GiB for the build and 4.14 GiB for
comparison/replay, below the 24 GiB budget on this host. These are local process
samples, not hosted cgroup measurements or a guaranteed hosted runtime.
The only exported axioms are `propext`, `Classical.choice` and `Quot.sound`.
The admitted root has 136 files and passes the pinned source policy.
All Lean-source hashes remained unchanged through build, export and replay.
Final packaging removed one trailing blank line and finalized this documentation;
the rebuilt, re-exported solution is byte-identical to the replayed export.
Seven independent
centered-checksum/frame regression tests also pass. The 1096 fallback is untouched.

The normal verifier was attempted with the exact pinned contract and configured
pinned tools. It refuses to start because this kernel lacks Landlock. No sandbox
requirement was bypassed; hosted verification is still required.

### Historical 1096 check-time engineering pass (2026-09-28)

In that earlier pass, the exported statements, program, tables and claim were unchanged;
only proof terms and module structure were reworked so that the hosted sandbox
(build + lean4export + kernel replay under `RuntimeMaxSec=1200`) has margin.
GF(2^64) products certified by `decide +kernel` (about 10,500 of them, roughly
20 ms each in replay) were replaced by structural Bool/Nat-primitive checks
(`BF64Fast`, `GenOrderFast`); the serial `SplitDPStage*` dynamic-program chain was
replaced by a packed certificate (`SplitPack`, `SplitContraction`, `SplitDP`); the
length-power and log-value tables use `rfl`/linear Bool scans instead of
`decide`; and the `SplitNumeric`/`AffineCodec`/`FourChildTier` checks use
certified scans (`ListCert`). Measured on an idle host: clean build 203.5 s
(peak PSS 12.96 GB, was 423.7 s / 18.75 GB), Solution export 10.4 s (288 MB),
CheckExports replay 117.3 s of which kernel replay 74.6 s (was 743.2 s / 695.6 s).
An independent structural walk over the old and new lean4export closures of
`submission`, `certificate` and `seeded_rows` found 3656 constants in each and
no differences. These are local measurements, not a hosted verdict.


Before that engineering pass, the complete 1096 certificate and seeded-row bound passed a clean build with no prior
submission artifacts (8968 jobs, 423.679 seconds). Exact comparison against the
rendered 1096 challenge and its primitive declarations passes. The exported
dependency audit and named-theorem audits use only `propext`, `Classical.choice`
and `Quot.sound`. A fresh, unchanged Lean kernel replay accepts all 62151
exported declarations: replay itself takes 695.624 seconds, and parsing,
comparison, axiom checking and replay together take 743.160 seconds including
the local process wrapper.

The measured required build/export/check stages total 1187.366 seconds
(19 minutes 47 seconds), leaving only about 13 seconds against the 20-minute
limit on this host. This is a sum of standalone local measurements, not an
official sandboxed end-to-end verdict; hosted timeout remains a material risk.
Peak sampled proportional memory is about 17.5 GiB during the parallel build
and 6.0 GiB during replay. These are PSS samples, not a hosted cgroup measurement.
Build output is 34036 bytes. Source hashes were unchanged through validation.

Large dynamic-program certificates must be split into serial modules and
bounded row checks: a monolithic check exceeded the hosted memory cap locally.
The last two profiles are composed algebraically and their cost-window sum is
transposed into seven coefficient-vector dot products against the stage-11 rows.
This avoids constructing the last two full matrices. The generic composition
and transposition identities and every resulting count are kernel checked.
The numeric schedule similarly uses a certified linear scan of tier masses;
the cached schedule is proved equal to the original for every index.
These transformations change proof representation, not the table, arithmetic,
security conditions or machine score.
Obsolete unreachable machine/research modules are archived outside the
submission; the admitted root contains the active dependency chain.

The official Linux verifier fails closed here because Landlock is unavailable.
No sandbox requirement is bypassed, and local development checks are not a
hosted verdict. Submission requests the official hosted check.

## Failed approaches and next work

Earlier 1094/sub-1095 candidates failed exact security checks; removing padding
alone did not suffice. Uniform alias multiplicities by cost restricted the
search unnecessarily. Rotating packets alone does not separate domains on
attacker-chosen child values. None of these failures is an impossibility proof.

Further savings must count every initialization, copy, extra multiplication,
jump, length check and boundary charge. Useful next targets are a joint search
over packet arity, internal-child placement and split aliases, followed by exact
security and code-size screening. A still-lower estimate is not a certificate.

## Credits

- The user's 1332-cycle Group3 baseline, developed with Claude Opus 5.5, supplies the grouped
  tables, hinted-landing architecture, and most machine proof structure. It builds on the
  1598-cycle HL-FLAT-A and earlier 85343-cycle leanISA records.
- The R9 generic scheme and security-proof structure were adapted from the public submission
  at [d2dcc9edda216eec46943eab4b5752a670674554](https://github.com/leanEthereum/ots.golf-submissions/tree/d2dcc9edda216eec46943eab4b5752a670674554/formal/Submissions/UpperLeanIsa),
  with rotated chain numbering, ONE padding, and the effective-index budget proof added here.
- `Cache`, `IUB`, `Master`, counting/availability lemmas, and adaptive index-grinding proofs
  inherit the earlier UpperRiscv and leanISA authors' work, including Tom Wambsgans (PR #5)
  and Holindauer with Claude Fable 5.1 (PR #15), as credited in the preserved baseline.
- The field-rescaling model and 1295 plan are retained in `leanisa-frontier/field-opt`.
  The 1295 implementation and proof adaptation were completed with Codex.
- The landing exit (hash-free exit table, pads below the sentinel) is from the 1319-cycle
  record, prepared with Claude Opus 5.5; its port onto the 1295 machine (1294) was prepared
  with Claude Opus 5.5.
- The root rehoming (1291) was prepared with Claude Opus 5.5.
- The 8-call root with a state-word tag (1283), its good-record security argument and the
  one-entry signing bound were prepared with Claude Opus 5.5.
- TRIM16 (dummy cost-17 entries, 1282) and FREE-Z (the free top in call 1 with a frame-14 variant
  of the first group, 1281) were prepared with Claude Opus 5.5.
- The 9-call root with constant tags on the 1281 machine (1289) was prepared with Claude Opus 5.5.
- Rarest-cut signing (the tier proof, the `Tier*` files and the rewired stage proofs), the
  aliased layer-88 tables with their tier-schedule certificate, and the 1209 machine were
  prepared with Claude Opus 5.5.

- This layer-87 table search, regenerated tier certificates, and fused length-guard port were prepared with Codex.

- The six-group fused construction, exact layer-86 search, dependency-aware security proof,
  new address layout, and complete 1149-cycle machine certificate were prepared with Codex.

- The light seventh binding group on chains 39, 40, 41, the two-call root, the (C_1, C_2) light
  cv, and the 1138-cycle machine certificate were prepared with Claude Opus 5.5.

- The full-nonce revision and the four-child single-root construction, exact codec/tier
  proofs, address layout, security proof and 1125-cycle machine certificate were prepared with Codex.
- The validated-length frame and shifted checksum, reducing the machine to 1124 cycles,
  were prepared with Codex.
- The affine-frame candidate and its polynomial avoidance, secure codec, instruction
  semantics, length check, universal 1110-cycle proof, soundness, honest prover and complete certificate were prepared with Codex.

- The mixed-packet split-alias layer-85 construction, linear security argument, exact multiplicative counting, and 1096 proof port were prepared with Codex using parallel agents.
- The centered-checksum and fixed-free-frame 1095 revision, exact landing certificates,
  and full machine proof port were prepared with Codex using parallel agents.
