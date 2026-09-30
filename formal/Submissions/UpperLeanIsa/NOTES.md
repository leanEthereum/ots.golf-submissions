# 1088-cycle leanISA proof

The certificate improves the 1089-cycle construction at commit
`fafaac02719c753addd045dba805b3a586cb8193` by one ordinary instruction.
Every completing execution has 185 instructions and 968 execution cycles,
plus the contract's 120-cycle boundary charge. The program has 2^18 slots
and 2^16 memory cells, totaling 327680 seeded rows.

## Change

The old prologue initialized powers 1 through 12. The twelfth power served
as stage 11's bias and chain 30's packet tag. Stage 11 now uses ONE, while
the packet tag uses the already validated length 5504. The selected-base
constraints prove that this tag differs from all other packet tags. The
prologue now has fifteen straight instructions and one dispatch.

The signature tables, alias multiplicities, layer-85 signing schedule,
three landing hints, and physical block layout are preserved. Group budgets
sum to 82. The normal and zero-free-chain variants both cost 1088 cycles.
The group order is `[0,2,3,4,5,6,7,8,9,10,11,12,1]`.

The new constant frame requires explicit isolation from both incoming ONE
and length-biased frames, and from the exit frame ONE. `OneFrame11Scan`,
`OneFrame11Data0` through `OneFrame11Data7`, and `OneFrame11` supply exact
kernel-checked field relations covering every stage-11 interval and exit.
Entry and length equalities are checked separately before reducing the
numeric relations, avoiding repeated expansion of the inverse hint index.

A zero-exponent free dispatch can now reach a stage-11 entry. The universal
path proof excludes completion after this return by determinism: it would
repeat a previously visited continuation with a different remaining length.
The proof also excludes wrong interior landings, prologue re-entry, variant
switching, premature halts, and all other invalid transitions.

## Proof map

- `FreeLastSelect` and `FreeLastBase` choose a nonzero field base avoiding
  all nonconstant landing constraints. The weighted bound is
  `14637086839355824200 < 2^64`; free exponents range from -77 through 131.
- `FreeLastDecode`, `FreeLastGuard`, `FreeLastSemantics`, and `FreeLastRun`
  connect actual reads and instructions to those constraints and the finite guards.
- `FreeLastPrefix`, `FreeLastFacts`, `FreeLastGroups`, `FreeLastChecksum`,
  and `FreeLastPath` prove the shape and exact cost of every completing run.
- `FreeLastCodec` proves tag separation and reuses the scheme security proof.
  `FreeLastValues`, `FreeLastTie`, and `FreeLastSound` establish soundness for
  every committed image at all admitted memory log-sizes 16 through 32.
- `FreeLastProver`, `FreeLastHonest`, `FreeLastHonestPath`, and
  `FreeLastFaithful` supply honest memory, execution, and the complete certificate.

Unused historical modules were removed after checking the full import closure.
The proof uses no `sorry`, `native_decide`, or additional axioms. No optimality
or hosted-verification claim is made. The separate fourth-hint encoding candidate
is research only and is not part of this submission.

## Checking cost and further work

Finite-field evaluation uses certified 11-bit lookup windows. A window starts
from its first table entry, avoiding a redundant multiplication by ONE. The
length-frame guard used by this machine depends only on its 1024 length
blocks; unused historical free-frame checks do not enter that lemma. These
changes reduce proof-checking work without changing the bytecode or score.
The two partial-hint budget lemmas check each table entry and its alias interval
directly; `selected_spec` then transfers those checks to every raw code. This
avoids repeating a linear table search for every alias. The independent guard
chunks use bounded parallel import chains to keep build time and memory within
the submission limits.

A separate exact integer/field search found a fourth landing-hint layout by
rescaling the low index limb by `g^(-196608)` and redistributing aliases
between group 10 and the root. Its layout and security inequalities pass an
independent numerical audit, but the encoding and machine proof remain to be
ported. Combining that direction with this initialization saving is the next
candidate to test. Earlier fixed-alias coexistence searches failed to pack;
that is a limit of those tested configurations, not an impossibility proof.
