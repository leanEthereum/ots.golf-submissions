# HL-TRI-1390: a 127-bit index on layer 103, junk bit by dispatch, 1390 cycles

Lineage: HL-FLAT-A (1598) → HL-TRI (1439, grouped dispatch) → HL-TRI-TM (1433, reused constant
cells) → HL-TRI-R9 (1422, nine root calls) → HL-TRI-R9 without the index-metadata constant
(1421) → HL-TRI-I127 (1391, 127-bit index) → this root (1390, junk bit by dispatch). HL-TRI-TM
kept HL-FLAT-A's security proof and changed only tag-symbol and root-metadata *values*. HL-TRI-R9 changes the scheme: a per-chain high-half
top (`Params.hiTop`, `Params.slice`) and the 9-call root (section 6); the security proof keeps
its structure. HL-TRI-I127 shortened the index to 127 bits (section 0); this root reads the junk
bit 0 of the index cell with group 0's dispatch; the grouped bytecode keeps its shape.

## 0. This root: the 127-bit index

**Why a shorter index is sound.** Every leanISA query is 896 bits, so every query costs 2
compressions. The previous proof showed `probTrue ≤ κ·B` with `κ = 2^-128` per compression and
then weakened it to `< B/2^127`: a factor-2 slack. The chain and root charges are `2^-129`
(hidden input) plus `2^-129` (second preimage) per query-half, that is `2^-128` per compression.
The index charge is `2^-idxBits` per compression at the crude bound 2; the true bound is
`(11/6)·θ` (`sum_gCls_le`). With `idxBits = 127`, `θ ≤ 32/31` and `(32/31)·(11/6) ≤ 19/10`, the
index charge is `(19/10)·2^-127` per index query. The new constant is
`κ' = (19/10)·2^-128 = (19/20)·2^-127` per compression (`StageB.lean`, `κ`):

- chains and root: `2·rate = 2^-128 ≤ κ'` (`two_rate_le_κ`, used in `ΦA_charge`, `ΦB_charge`);
- index: `RowPot.psi_charge` is `(19/10)/2^127 = 2·κ'` per query (`κ_mul_two`,
  `encTerm_charge`); the `IdxPost` charge `2^-127 ≤ 2·κ'` (`inv_two_pow_127_le`);
- the index budget invariant is `2·encCount + b ≤ 2^127` (each index query pays two
  compressions); nonces (`2^128`) now outnumber indices (`2^127`), so a row's fresh mass can
  exceed its size, handled by `RowIneq.charge_le_clamp`;
- strictness: `κ' < 2^-127` (`κ_lt`), so `κ'·B < B/2^127` (`κ_mul_lt`); `Flat.secure` keeps its
  statement.

**Scheme.** The index word is bits `1 … 127` of the low half of the index answer
(`idxAns y = y.extractLsb' 1 127`); bit `0` is never read, so every index has a fiber of
`2^129` answers. Chains `0 … 40` have 3-bit digits (length 8) and chain 41 a 4-bit digit (length
16), at positions `3k` and `123`; `Σ (len − 1) = 302`. The layer is 103 with
`N₁₀₃ = 31836335063033790258067380181515840 ≈ 98.10·2^108`; `N₁₀₂ ≈ 79.2·2^108` is below the
availability threshold `90·2^108`, and `(1 − 90·2^108/2^127)^(2^19) ≤ 2^-128`
(`LayerAvailability`, 128-trial reciprocal blocks). Key generation costs `2·(302 + 9) = 622`
compressions, verification `2·(1 + 103 + 9) = 226`. Tags, metadata, `hiTop` and the 9-call root
are unchanged; `rootSlot = 262133` is unchanged, so `k0Md` is too.

**Machine.** Digit `k` sits at bit `1 + pos k` of the 128-bit index cell, and the tie words are
`T_g = Σ s_k·2^(1 + pos k)`. The junk bit 0 is a radix-2 digit `d` of group 0 (section 6, first
item):

- group 0 has `2·8·8·8 = 1024` blocks, `grank 0 d a b c = 512·d + 64·a + 8·b + c`; the other
  groups have `d = 0` (`Wd g`);
- group 0's tie is one `SET(acc_0, d + T_0)` for every tuple, the all-zero one included; groups
  `g ≥ 1` add their word to `acc_{g−1}` as before;
- so `acc_13 = d + 2·I'` with `I'` the number of the landing digits (`tie_sum`), and the index
  cell `idx = acc_13` gives `I = idx / 2 = I'` (`accept_of_path`). The landing fixes `d < 2`, so
  it cannot absorb a difference between `idx` and the tie words;
- in the proofs the digit vector `s` carries `d` at index 42 (`Valid s` adds `s 42 < 2`,
  `jdig s g`); `digitOf v 42` reads it off group 0's landing rank, and the honest `dg y 42` is
  bit `0` of the index answer.

Group 0 keeps `NH = 6`: `I0`, the `SET`, at most three zero copies, `SET L_0`. The junk-bit
gadget of HL-TRI-I127 (the hint cell `J`, the prologue `MUL(J, J, J)` and `fact_j`) is gone
(`−1`).

**Accounting.** Group 0: `SP = 29`, `NH = 6`, 1024 blocks, `BASE = 28`; groups `1 … 12`:
`SP = 29`, `NH = 6`, 512 blocks, `BASE g = 14876 + 14848·g`; group 13: `SP = 37`, `NH = 7`, 1024
blocks, `BASE = 207900`; code ends at 245788 `< rootSlot = 262133`. The prologue is 28 slots.
Every completing run executes 253 instructions, 113 of them `BLAKE2S` (1 index, 103 chain steps,
9 root calls): `140 + 10·113 = 1270`, claim `1270 + 120 = 1390` (`1391 − 1`).

**Model.** `.tmp/hl/hltri_1390_model.py` (Appendix A) prints `RESULT: PASS`, claim 1390: the
frame lemma exhaustively over every slot and frame, 401 support-mode walks of layer vectors
(both junk bits) with constant cost 1270 in 253 steps (including the worst digit vector),
off-layer vectors rejected, mid-block landings rejected, 180 group-0 landings whose junk bit
disagrees with the index cell rejected (the other bit, a random index cell), and 8 honest
signatures with tampered words, nonce, message and key agreeing with the verifier. The previous
root's model is `.tmp/hl/hltri_i127_model.py`.

## 1. Where HL-FLAT-A's cycles were

`1598 = 308 + 10·117 + 120`. The 117 `BLAKE2S` (1 index, 106 chain steps on layer 106, 10 root
calls) are fixed by the scheme. An exhaustive search over all 689,249 digit-width mixes with
Σ widths = 128 and at most 42 chains (24 processes) confirms that 40×3 + 2×4 bits on layer 106
is optimal for a 128-bit index: no mix reaches the availability bound `200·2^108` on a lower
layer. So the gain had to come from the 308 non-hash instructions (until section 0 shortened
the index).

Of those, 42 × 7 were per-chain dispatch: a frame `SET`, `MUL(H,g,H')`, the dispatch `JUMP`,
the frame-shifted entry `I0`, the tie `SET T; XOR`, and the landing product `MUL(G, H)`.

## 2. Idea: dispatch a group of three chains per landing

- 14 groups: `(3g, 3g+1, 3g+2)` for `g < 12`, then `(36, 37, 40)` and `(38, 39, 41)`. With the
  128-bit index this balanced the two 4-bit chains 40 and 41; with the 127-bit index only chain
  41 is 4-bit, so group 12 is all radix 8.
- One frame per group (`F_g = g^((g+1)·2^33)`, 14 `SET`s instead of 42), one dispatch
  (`MUL(H_g, g, H'_g); JUMP(ONE, H_g, F_g)`) and one entry `I0_g = JUMP(ONE, H'_g, ONE)` per group.
  Entry of tuple `t` is `BASE g + SP g · rank t` (mixed radix over the group's digits).
- One tie word per group: `SET T_g := Σ s_k·2^pos_k; XOR(acc_{g−1}, T_g, acc_g)`, `acc_13 = idx`
  (this root: `2^(1 + pos_k)`, and group 0's word `SET(acc_0, d + T_0)` carries the junk bit,
  section 0).
- The layer is checked by a product of per-group factors `g^σ` (`σ` = the group's digit sum),
  `L_13 = K0 = g^rootSlot`. Six precomputed constants `g^2..g^7` (plus `gCell = g^1`) let most
  groups use one `MUL` with no `SET`; `σ > 7` pays `SET C_g; MUL`.
- Zero digits copy the revealed word into the root's top cell (`XOR(W_k, Z, rootTop k)`), as in
  HL-FLAT-A. The contract's `steps` must not depend on the oracle's index answer, so every block
  of a group pads with `XOR(Z, Z, Z)` to the group's maximum non-hash count
  (`[6]*12 + [7, 7]` before the tail; this root: `[6]*13 + [7]`).
- Every completing run of HL-TRI: 266 instructions, 117 `BLAKE2S`: `149 + 1170 = 1319`, 1439.
- HL-TRI-TM (section 6, first item, now done): 260 instructions, `143 + 1170 = 1313`, claim
  `1313 + 120 = 1433`. The tag symbols are the cells `Z, ONE, g, g^2..g^5` (values
  `0, 1, 2, 4, 8, 16, 32`), the root metadata `0, 2, 4, …, 128, 5504, 3` (one new `SET` for 3),
  and the seven symbol `SET`s are gone. The prologue is 30 slots.
- HL-TRI-R9 (section 6, second item): 258 instructions, 116 `BLAKE2S`, `142 + 1160 = 1302`, claim
  `1302 + 120 = 1422`. The root cv cells are `410 + 4r` (`cvCell r`, `r < 8`); a high-top chain's
  last step writes `(rootTop k − 1, rootTop k)`, so no top copy is needed; the constant `3` and
  its `SET` are gone, so the prologue is 29 slots and the root segment (9 `BLAKE2S` and the pk
  `XOR`) starts at `sentinel − 10`.
- HL-TRI-R9 at 1421: the index metadata is `5504` (the `LEN` cell) and root call 8's metadata is
  the bits of `K0 = g^rootSlot` (`k0Md = 3909124629532110206`, checked by `decide +kernel`), so the
  index-metadata `SET` is gone: prologue 28 slots, 257 instructions, `141 + 1160 = 1301`, claim
  `1301 + 120 = 1421`.
- HL-TRI-I127 (1391): section 0. Prologue 29 slots (the `MUL(J, J, J)`), 254 instructions,
  `141 + 1130 = 1271`, claim `1271 + 120 = 1391`.
- This root (1390): the junk bit by group-0 dispatch (section 0). Prologue 28 slots, 253
  instructions, `140 + 1130 = 1270`, claim `1270 + 120 = 1390`.

## 3. A tempting design that is unsound

A cheaper variant (1425) ran each block entirely in its group's frame and ended the block with
an entry assertion `SET(H_g, g^entry)` instead of the `I0` jump and the `MUL(H, g, H')`. It fails:
the block's tail `JUMP` is itself group-`g` code, so a dispatch can land on the tail and skip the
whole block (tie, layer factor, copies, chain steps). The skipped cells become free image cells,
and a forged signature follows. Any design in which some executable slot of a group's code is a
jump has this hole unless landings are pinned by the frame, as `I0` does. The attack script
completes on the 1425 model and is rejected on this one.

## 4. How it was built

1. Cost breakdown, then the width search (section 1).
2. An exact executable model (appendix) that builds all 2^18 slots, checks the frame lemma
   exhaustively for every slot and frame, runs honest signatures and tampered inputs through the
   leanVM semantics, runs 400 random layer vectors in support mode (constant cost), rejects
   off-layer vectors, and rejects mid-block landings with adversarial cell fills. This root:
   `.tmp/hl/hltri_1390_model.py` (Appendix A), which adds the junk-bit landing runs.
3. A Python mirror of the Lean `cinstrAt` matched the model on all 262,144 slots (for HL-TRI-R9:
   `.tmp/hl/hltri_r9_lean_mirror.py` against `.tmp/hl/hltri_r9_model.py`, 0 mismatches).
4. Two agents: machine core (`MachineProgram` → `MachineCycles`) and machine proofs
   (`MachineSound`, `MachineProver`, `MachineHonest`, `MachineFaithful`, `Solution`). For this
   root: a scheme/security agent (the 127-bit index, `κ'`) and a machine agent (the layout port
   and the `J` gadget), the model first; then one machine agent for the junk bit by dispatch.

## 5. Validation

- `lake build Submissions.UpperLeanIsa.Solution` succeeds.
- `check_submission.py upper-leanisa`: ok, claim 1390.
- `certificate : submission.Certificate 1390` and `seeded_rows` type-check; `#print axioms`
  gives `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `native_decide` or `admit` in the root.

## 6. What next

- **Junk bit by dispatch (done: 1390).** Bit 0 of the index cell is a radix-2 digit of group 0:
  1024 group-0 blocks whose tie word includes the bit (`SET(acc_0, word)`), so `J` and its `MUL`
  are gone. Code end 245788 < 262133; the block builders take a fourth digit `d < Wd g`.
- **Tag and metadata constants (done in HL-TRI-TM: 1433).** Tag symbols `{0, 1, 2, 4, 8, 16, 32}` are
  exactly the existing cells `Z, ONE, g, g^2..g^5`, and the root metadata can use
  `0, 2, 4, …, 128, 5504` plus one new constant. That removes the seven symbol `SET`s and nets −6.
  It changes only `SchemeFlat`'s `sym`/`rootMd`/`idxMd` and `FlatHyp`'s decidable facts; the
  security proof is generic in `Params`.
- **Nine root calls (done: 1422).** A 128-bit chaining state in `m` absorbs five
  tops per call if the cv pair holds two tops. Two tops sit in adjacent cells without a copy
  because one chain's top is the *high* half of its last output (output pair `(c−1, c)`) and the
  other's the low half (`(c+1, c+2)`). In the scheme: `Params.hiTop` marks the chains
  `0, 6, 11, …, 36`; the step producing their top keeps the high half (`Params.slice`, offset
  `stepOff = 128`). Root call 0 has cv `(top 0, top 1)` and block tops 2..5; call `r = 1..7` has
  cv `(top (5r+1), top (5r+2))` and block `[lo state, top (5r+3), top (5r+4), top (5r+5)]`; call
  8 has cv the full state and block `[top 41, 0, 0, 0]`; `pk = lo(state 8)`. Metadata
  `0, 2, 4, …, 128, 5504`; the extra constant `3` is gone. Keygen costs `2·(310 + 9) = 638`,
  verification `2·(1 + 106 + 9) = 232`. Security: every location is charged hidden input plus
  second preimage against at most `2^128` matching answers, the step's slice at chain steps and
  the low half at every root call (the next call reads the low half; call 8's low half is `pk`).
- Larger groups do not fit: a quadruple of 3-bit chains needs about 90k slots.

## 7. Credits (carried over from HL-FLAT-A)

- Adapted from the 85343-cycle leanISA record (this root's previous contents) and its
  predecessors; see that record's README for the earlier chain of credit.
- `Cache`, `IUB`, `Master`, the `Layer*` counting/digit/availability files and the `Idx*`,
  `RowIneq`, `RowPotential` index-grinding proofs are ported from the checked UpperRiscv
  submission (`formal/Submissions/UpperRiscv` on `main`); proof credit belongs to their
  authors as credited there (including Tom Wambsgans, PR #5, and Holindauer with Claude
  Fable 5.1, PR #15). Namespaces and imports are local to this root.
- HL-FLAT-A design, security layer, UNI bytecode and machine proofs prepared with Claude Opus 5.5.

- HL-TRI grouped bytecode and machine proofs: prepared with Claude Opus 5.5, building on the HL-FLAT-A machine proofs.

## Appendix A. The model (`.tmp/hl/hltri_1390_model.py`)

The exact executable model of this root: fields, scheme spec and checks, layout, the leanVM simulator, and the checks (Pool of 9 processes). `python3 hltri_1390_model.py` prints `claim 1390` and `RESULT: PASS`.

```python
#!/usr/bin/env python3
"""HL-TRI-1390 executable model: 127-bit index on layer 103, junk bit dispatched by group 0.

Exact model of the leanISA image (42 chains, 41 x radix 8 + 1 x radix 16, index = bits 1..127 of
the low half of the index answer, nine-call root with high-half tops, grouped hinted-landing
dispatch), executed with the leanerVM semantics of `Semantics/Step.lean` and the contract's
`LeanIsaMachine.runCost` (oracle BLAKE2S, sentinel test, weights 1 / 10), over the real fields
K = GF(2)[x]/(x^64+x^4+x^3+x+1), g = x, E = K[y]/(y^3+y+1).

Everything is exact integer arithmetic.  Run: python3 hltri_1390_model.py  (exit 0 = all pass).

Checks:
  A. scheme spec (mirrors SchemeFlat.lean): N_103 numeral, layer 102 below the threshold,
     availability, budgets, tag injectivity, md separation;
  B. image: frame-range lemma exhaustive over every slot and every frame;
  C. honest runs: machine completes iff scheme verify accepts, tampered inputs agree;
  D. worst case: support-mode walks of random layer vectors, constant cost = claim;
  E. adversarial: off-layer vectors, mid-block landings, junk-bit landings that disagree with
     the index cell.
"""
import hashlib, random, sys

random.seed(20260924)
FAIL = []
def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)

# ============================================================================ fields
POLY = (1 << 64) | 0b11011          # x^64 + x^4 + x^3 + x + 1
M = (1 << 64) - 1                   # |K*|

def kmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> 64: a ^= POLY
    return r

def kpow(a, e):
    r = 1
    while e:
        if e & 1: r = kmul(r, a)
        a = kmul(a, a); e >>= 1
    return r

G = 2
PRIMES = [3, 5, 17, 257, 641, 65537, 6700417]
assert eval('*'.join(map(str, PRIMES))) == M

DLOG = {1: 0}
def dlog(h):
    """Pohlig-Hellman + BSGS discrete log base g (order M, squarefree smooth); cached."""
    assert h != 0
    if h in DLOG: return DLOG[h]
    rs, ms = [], []
    for p in PRIMES:
        gp = kpow(G, M // p); hp = kpow(h, M // p)
        m = int(p ** 0.5) + 1
        table = {}; cur = 1
        for j in range(m):
            table.setdefault(cur, j); cur = kmul(cur, gp)
        step = kpow(gp, p - m % p if m % p else 0)   # gp^(-m)
        step = kpow(gp, (p - m) % p)
        cur = hp
        for i in range(m + 1):
            if cur in table:
                rs.append((i * m + table[cur]) % p); break
            cur = kmul(cur, step)
        else:
            raise ValueError
        ms.append(p)
    x = 0
    for r, p in zip(rs, ms):
        Mi = M // p
        x = (x + r * Mi * pow(Mi, -1, p)) % M
    assert kpow(G, x) == h
    DLOG[h] = x
    return x

def gpow(e):
    v = kpow(G, e % M); DLOG[v] = e % M; return v

# E elements: (l0, l1, l2); y^3 = y + 1
def eadd(a, b): return (a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2])
def emul(a, b):
    if a[1] == a[2] == b[1] == b[2] == 0:
        v = kmul(a[0], b[0])
        if a[0] in DLOG and b[0] in DLOG: DLOG[v] = (DLOG[a[0]] + DLOG[b[0]]) % M
        return (v, 0, 0)
    c = [0] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] ^= kmul(a[i], b[j])
    # y^4 = y^2 + y, y^3 = y + 1
    c[2] ^= c[4]; c[1] ^= c[4]
    c[1] ^= c[3]; c[0] ^= c[3]
    return (c[0], c[1], c[2])
def ofK(a): return (a, 0, 0)
def isK(x): return x[1] == 0 and x[2] == 0
def canon(x): return x[2] == 0
def cellBits(x): return x[0] | (x[1] << 64)
def cellOf(b): return (b & M, b >> 64, 0)
ZERO = (0, 0, 0)

# ============================================================================ scheme constants
N_CHAINS = 42
W = [8] * 41 + [16]                          # positions per chain; digit s_k < W[k]
BITS = [3] * 41 + [4]
POS = [sum(BITS[:k]) for k in range(N_CHAINS)]
assert POS[:41] == [3 * k for k in range(41)] and POS[41] == 123
LAYER = 103
STEPS = [w - 1 for w in W]                   # 302 chain positions (steps)
OFF = [sum(STEPS[:k]) for k in range(N_CHAINS)]
assert sum(BITS) == 127 and sum(STEPS) == 302
SYMV = [0, 1, 2, 4, 8, 16, 32]
SYM = lambda v: SYMV[v]
def tag(k, j):
    p = OFF[k] + j
    return (SYM(p % 7), SYM(p // 7 % 7), SYM(p // 49))
CHAIN_MD, IDX_MD = 1, 5504
RHO = [0, 2, 4, 8, 16, 32, 64, 128, gpow((1 << 18) - 1 - 10)]   # K0 = g ^ rootSlot
HI_SET = {0} | {5 * r + 1 for r in range(1, 8)}
HI = lambda y: y >> 128
def stepval(k, j, y):
    return HI(y) if (k in HI_SET and j + 1 == W[k] - 1) else LO(y)
CV_CONST = 0 | (1 << 128)                    # cv pair (Z, ONE): cv0 = 0, cv1 = 1
NONCE_BITS = 128
TRIALS = 2 ** 19
SIG_BITS = 43 * 128

def hashInput(cv, block, md): return cv | (block << 256) | (md << 768)
ORACLE = {}
def H(q):
    if q not in ORACLE:
        ORACLE[q] = int.from_bytes(hashlib.blake2s(q.to_bytes(112, 'little'), digest_size=32).digest(), 'little')
    return ORACLE[q]
LO = lambda y: y & ((1 << 128) - 1)

def chainQuery(k, j, x):
    a, b, c = tag(k, j)
    return hashInput(CV_CONST, x | (a << 128) | (b << 256) | (c << 384), CHAIN_MD)
def chain(k, j, n, x):
    for t in range(n):
        x = stepval(k, j + t, H(chainQuery(k, j + t, x)))
    return x
def idxQuery(m, eta, pk): return hashInput(CV_CONST, m | (eta << 256) | (pk << 384), IDX_MD)
def idxOf(y): return LO(y) >> 1              # bits 1..127 of the low half; bit 0 is junk
def digits(I): return [(I >> POS[k]) % (1 << BITS[k]) for k in range(N_CHAINS)]
def accepted(I): return sum(digits(I)) == LAYER
def rootQueries(tops):
    qs = []
    q = hashInput(tops[0] | (tops[1] << 128),
                  tops[2] | (tops[3] << 128) | (tops[4] << 256) | (tops[5] << 384), RHO[0])
    st = H(q); qs.append(q)
    for r in range(1, 8):
        a, b, c, d, e = tops[5 * r + 1: 5 * r + 6]
        q = hashInput(a | (b << 128), LO(st) | (c << 128) | (d << 256) | (e << 384), RHO[r])
        st = H(q); qs.append(q)
    q = hashInput(st, tops[41], RHO[8])
    st = H(q); qs.append(q)
    return LO(st), qs
def root(tops): return rootQueries(tops)[0]

def keygen(rng):
    seeds = [rng.getrandbits(128) for _ in range(N_CHAINS)]
    table = [[seeds[k]] for k in range(N_CHAINS)]
    for k in range(N_CHAINS):
        for j in range(STEPS[k]):
            table[k].append(stepval(k, j, H(chainQuery(k, j, table[k][j]))))
    pk = root([table[k][W[k] - 1] for k in range(N_CHAINS)])
    return pk, (table, pk)
def toBits(x, n): return [(x >> i) & 1 for i in range(n)]
def ofBits(bits): return sum(b << i for i, b in enumerate(bits))
def sign(sk, m, rng, trials=TRIALS):
    table, pk = sk
    tried = set()
    for _ in range(trials):
        eta = rng.getrandbits(128)
        while eta in tried: eta = rng.getrandbits(128)
        tried.add(eta)
        I = idxOf(H(idxQuery(m, eta, pk)))
        if accepted(I):
            s = digits(I)
            words = [table[k][W[k] - 1 - s[k]] for k in range(N_CHAINS)]
            bits = []
            for x in words: bits += toBits(x, 128)
            return bits + toBits(eta, 128)
    return None
def verify(pk, m, bits):
    if len(bits) != SIG_BITS: return False
    xs = [ofBits(bits[128 * i:128 * i + 128]) for i in range(42)]
    eta = ofBits(bits[128 * 42:])
    I = idxOf(H(idxQuery(m, eta, pk)))
    if not accepted(I): return False
    s = digits(I)
    tops = [chain(k, W[k] - 1 - s[k], s[k], xs[k]) for k in range(N_CHAINS)]
    return root(tops) == pk

# ============================================================================ A. scheme checks
def layer_counts(radices):
    p = [1]
    for w in radices:
        q = [0] * (len(p) + w - 1)
        for i, x in enumerate(p):
            for j in range(w): q[i + j] += x
        p = q
    return p
CNT = layer_counts(W)
N103 = CNT[103]
check(N103 == 31836335063033790258067380181515840, "N_103 numeral")
print("N_103 =", N103, "=", N103 / 2 ** 108, "* 2^108")
THRESH = 90 * 2 ** 108

def pow_rounded(m, P, L, up):
    result = 1 << P; base = m; e = L; first = True
    while e > 0:
        if e & 1:
            if first: result = base; first = False
            else:
                num = result * base
                result = -((-num) >> P) if up else (num >> P)
        e >>= 1
        if e:
            num = base * base
            base = -((-num) >> P) if up else (num >> P)
    return result
def miss_bounds(N, L, P=1024):
    m = (2 ** 127 - N) << (P - 127)
    return pow_rounded(m, P, L, True), pow_rounded(m, P, L, False), P
check(THRESH <= N103 and 2 * N103 <= 2 ** 127, "90*2^108 <= N103, 2*N103 <= 2^127")
check(CNT[102] < THRESH, "layer 102 below the threshold")
up, lo, P = miss_bounds(THRESH, TRIALS)
check(up <= 1 << (P - 128), "availability: (1-90*2^108/2^127)^(2^19) <= 2^-128")
# budgets (blockCost 896 = 2)
bc = max(1, (896 + 511) // 512)
check(bc == 2, "blockCost 896 = 2")
check(bc * (302 + 9) == 622, "keygen 622")
check(bc * TRIALS == 2 ** 20, "sign = 2^20 exactly")
check(bc * (1 + LAYER + 9) == 226, "verify 226")
check(SIG_BITS == 5504, "sig bits")
# tags / md separation
alltags = {tag(k, j) for k in range(42) for j in range(STEPS[k])}
check(len(alltags) == 302, "chain tags injective on 302 positions")
check(len(set(RHO)) == 9 and CHAIN_MD not in RHO and IDX_MD not in RHO and CHAIN_MD != IDX_MD,
      "md separation chain/index/root")
check(all(v < 2 ** 128 for v in RHO), "root tags 128-bit")
# ============================================================================ HL-TRI-1390 layout
# The machine dispatches three chains per landing: one frame, one hinted landing, one tie word
# and one layer factor per group of chains. Digit k sits at bit 1 + POS[k] of the index cell; the
# junk bit 0 is a radix-2 digit of group 0 (1024 group-0 blocks), set by group 0's tie word
# SET(acc_0, j + T_0).
import os
from multiprocessing import Pool

LOG_SIZE = 18
NSLOTS = 1 << LOG_SIZE
SENT = NSLOTS - 1
MEMLOG = 16
GROUPS = [tuple(range(3 * g, 3 * g + 3)) for g in range(12)] + [(36, 37, 40), (38, 39, 41)]
NG = len(GROUPS)
C_PK, C_M0, C_M1, C_LEN = 0, 1, 2, 3
C_W = [4 + k for k in range(42)]
C_NONCE = 46
C_Z, C_ONE, C_G, C_K0 = 47, 48, 50, 51
C_SYM = [47, 48, 50, 442, 443, 444, 445]
C_F = [59 + g for g in range(NG)]
C_IDX = 101
C_T = [103 + g for g in range(NG)]
C_ACC = [145 + g for g in range(NG - 1)] + [C_IDX]
C_H = [186 + g for g in range(NG)]
C_H1 = [228 + g for g in range(NG)]
C_C = [270 + g for g in range(NG)]
C_L = [290 + g for g in range(NG - 1)] + [C_K0]
C_TOP = [320 + 2 * k for k in range(42)]
PRE_MAX = int("7")
C_GP = {1: 50}
C_GP.update({v: 440 + v for v in range(2, PRE_MAX + 1)})
C_CV = 410
CVC = [410 + 4 * r for r in range(8)]
def XC(k, t): return 1024 + 32 * k + 2 * t
C_S = [2400 + 2 * r for r in range(9)]
ROOT_TOP = [C_TOP[k] for k in range(42)]
ROOT_TOP[0], ROOT_TOP[1] = CVC[0], CVC[0] + 1
for r in range(1, 8):
    ROOT_TOP[5 * r + 1], ROOT_TOP[5 * r + 2] = CVC[r], CVC[r] + 1
CHAIN_OUT = [ROOT_TOP[k] - 1 if k in HI_SET else ROOT_TOP[k] for k in range(42)]
RHO_CELL = [C_Z, C_G, 442, 443, 444, 445, 446, 447, C_K0]

ROOT_LEN = 10
R_SLOT = SENT - ROOT_LEN
E_FRAME = [(g + 1) * 2 ** 33 for g in range(NG)]
OPB = lambda a: a % M
def op(a): return ('g', OPB(a))
def X_(a, b, c): return ('xor', op(a), op(b), op(c))
def MUL(a, b, c): return ('mul', op(a), op(b), op(c))
def SET(a, v): return ('set', op(a), v)
def JMP(c, d, f): return ('jump', op(c), op(d), op(f))
def BLK(m, cv, out, md): return ('blake', tuple(op(x) for x in m), op(cv), op(out), op(md))
def I0(g): return ('jump', ('g', (C_ONE - E_FRAME[g]) % M), ('g', (C_H1[g] - E_FRAME[g]) % M),
                   ('g', (C_ONE - E_FRAME[g]) % M))
PAD = ('xor', ('zero',), ('zero',), ('zero',))
NOP = X_(C_Z, C_Z, C_Z)
K0_VAL = ofK(gpow(R_SLOT))
F_VAL = [ofK(gpow(e)) for e in E_FRAME]
prog = {}
def emit(slot, ins):
    assert slot not in prog and 0 <= slot < SENT, slot
    prog[slot] = ins

PRO = [SET(C_Z, ZERO), SET(C_ONE, ofK(1)), SET(C_LEN, cellOf(5504)),
       SET(C_G, ofK(G)), SET(C_K0, K0_VAL)]
PRO += [SET(C_F[g], F_VAL[g]) for g in range(NG)]
PRO += [SET(C_GP[v], ofK(gpow(v))) for v in range(2, PRE_MAX + 1)]
PRO += [BLK([C_M0, C_M1, C_NONCE, C_PK], C_Z, C_IDX, C_LEN), MUL(C_H[0], C_G, C_H1[0]),
        JMP(C_ONE, C_H[0], C_F[0])]
for i, x in enumerate(PRO): emit(i, x)
PROLOGUE_LEN = len(PRO)

def chain_ops(k, s):
    j0 = W[k] - 1 - s
    ops = []
    for t in range(s):
        src = C_W[k] if t == 0 else XC(k, t - 1)
        dst = CHAIN_OUT[k] if t == s - 1 else XC(k, t)
        a, bb, c = tag(k, j0 + t)
        ops.append(BLK([src, C_SYM[SYMV.index(a)], C_SYM[SYMV.index(bb)], C_SYM[SYMV.index(c)]], C_Z, dst, C_ONE))
    return ops

# A group-0 tuple is (j, a, b, c) with j the junk bit; the other groups' tuples are (a, b, c).
def radices(g):
    return ([2] if g == 0 else []) + [W[k] for k in GROUPS[g]]

def tuples(g):
    out = [()]
    for w in radices(g):
        out = [t + (s,) for t in out for s in range(w)]
    return out

def dig(g, tup): return tup[1:] if g == 0 else tup
def jbit(g, tup): return tup[0] if g == 0 else 0

def nonhash(g, tup):
    ks = GROUPS[g]
    ds = dig(g, tup)
    word = jbit(g, tup) + sum(s << (1 + POS[k]) for k, s in zip(ks, ds))
    sigma = sum(ds)
    ops = [I0(g)]
    if g == 0:
        ops.append(SET(C_ACC[0], cellOf(word)))
    elif word:
        ops += [SET(C_T[g], cellOf(word)), X_(C_ACC[g - 1], C_T[g], C_ACC[g])]
    else:
        ops.append(X_(C_ACC[g - 1], C_Z, C_ACC[g]))
    for k, s in zip(ks, ds):
        if s == 0:
            ops.append(X_(C_W[k], C_Z, ROOT_TOP[k]))

    if g == 0:
        ops.append(SET(C_L[0], ofK(gpow(R_SLOT - LAYER + sigma))))
    elif sigma in C_GP:
        ops.append(MUL(C_L[g - 1], C_GP[sigma], C_L[g]))
    elif sigma:
        ops += [SET(C_C[g], ofK(gpow(sigma))), MUL(C_L[g - 1], C_C[g], C_L[g])]
    else:
        ops.append(MUL(C_L[g - 1], C_ONE, C_L[g]))
    return ops

def tail(g):
    if g < NG - 1:
        return [MUL(C_H[g + 1], C_G, C_H1[g + 1]), JMP(C_ONE, C_H[g + 1], C_F[g + 1])]
    return [JMP(C_ONE, C_K0, C_ONE)]

NH_MAX = [max(len(nonhash(g, t)) for t in tuples(g)) for g in range(NG)]

def block(g, tup):
    ks = GROUPS[g]
    head = nonhash(g, tup)
    # chain 0's top copy must follow its steps; keep all copies/ties before the steps except that one
    pre = head
    post = []
    pad = [NOP] * (NH_MAX[g] - len(head))
    steps = [b for k, s in zip(ks, dig(g, tup)) for b in chain_ops(k, s)]
    return pre + pad + steps + post + tail(g)

ENTRY = {}
BLOCK_LEN = {}
SP = [max(len(block(g, t)) for t in tuples(g)) for g in range(NG)]
BASE = []
slot = PROLOGUE_LEN
for g in range(NG):
    BASE.append(slot); slot += SP[g] * len(tuples(g))
LAST_CODE = slot
def rank(g, tup):
    r = 0
    for w, s in zip(radices(g), tup): r = r * w + s
    return r
for g in range(NG):
    for tup in tuples(g):
        e = BASE[g] + SP[g] * rank(g, tup)
        ops = block(g, tup)
        ENTRY[e] = (g, tup); BLOCK_LEN[(g, tup)] = len(ops)
        for i, x in enumerate(ops): emit(e + i, x)
print("SP", SP, "BASE", BASE)
check(LAST_CODE <= R_SLOT, f"code fits: {LAST_CODE} <= {R_SLOT}")
ENTRY_OF = {(g, tup): e for e, (g, tup) in ENTRY.items()}
ROOT = [BLK([ROOT_TOP[2], ROOT_TOP[3], ROOT_TOP[4], ROOT_TOP[5]], CVC[0], C_S[0], RHO_CELL[0])]
for r in range(1, 8):
    ROOT.append(BLK([C_S[r - 1], ROOT_TOP[5 * r + 3], ROOT_TOP[5 * r + 4], ROOT_TOP[5 * r + 5]],
                    CVC[r], C_S[r], RHO_CELL[r]))
ROOT.append(BLK([ROOT_TOP[41], C_Z, C_Z, C_Z], C_S[7], C_S[8], RHO_CELL[8]))
ROOT.append(X_(C_S[8], C_Z, C_PK))
for i, x in enumerate(ROOT): emit(R_SLOT + i, x)
check(R_SLOT + len(ROOT) == SENT, "root to sentinel")
print("prologue", PROLOGUE_LEN, "code end", LAST_CODE, "entries", len(ENTRY), "NH_MAX", NH_MAX)

def fetch(i):
    if not (0 <= i < NSLOTS): return None
    if i == SENT: return PAD
    return prog.get(i, PAD)
def operands(ins):
    t = ins[0]
    if t == 'blake':
        m, cv, out, md = ins[1:]
        return list(m) + [cv, ('g', (cv[1] + 1) % M), out, ('g', (out[1] + 1) % M), md]
    if t == 'set': return [ins[1]]
    return list(ins[1:4])
FRAMES = [0] + E_FRAME
def reads_ok(ins, fe, kappa=32):
    for o in operands(ins):
        if o[0] == 'zero': return False
        if (o[1] + fe) % M >= 2 ** kappa: return False
    return True
def frame_chunk(items):
    bad = 0
    for i, ins in items:
        for fi, fe in enumerate(FRAMES):
            ok = reads_ok(ins, fe)
            want = (fi == 0 and i not in ENTRY and i != SENT) or (fi > 0 and i in ENTRY and ENTRY[i][0] == fi - 1)
            if ok != want: bad += 1
    return bad
class Stop(Exception): pass
class Machine:
    """runCost over a (lazily committed) image.  `choose(cell, ctx)` is the prover's choice for an
    unassigned cell read as an input; outputs of relations are solved when unassigned."""
    def __init__(self, pinned, kappa=MEMLOG, choose=None, image=None, support=False):
        self.mem = dict(image or {}); self.mem.update(pinned)
        self.kappa = kappa; self.choose = choose; self.support = support
        self.trace = []; self.cost = 0
    def addr(self, fe, o):
        if o[0] == 'zero': raise Stop('read 0')
        a = (o[1] + fe) % M
        if a >= 2 ** self.kappa: raise Stop('read out of range')
        return a
    def rd(self, a, ctx):
        if a not in self.mem:
            v = self.choose(a, ctx) if self.choose else None
            if v is None: return None
            self.mem[a] = v
        return self.mem[a]
    def solve(self, a, v):
        if a not in self.mem: self.mem[a] = v
        if self.mem[a] != v: raise Stop('relation')
    def run(self, max_steps=5000):
        pc, fe = 0, 0                        # (g^0, fp = g^0)
        for _ in range(max_steps):
            if pc == SENT:
                if fe == 0: return self.cost
                raise Stop('sentinel with fp != 1')
            ins = fetch(pc)
            if ins is None: raise Stop('fetch')
            self.trace.append((pc, fe))
            t = ins[0]
            if t in ('xor', 'mul'):
                a, b, c = (self.addr(fe, o) for o in ins[1:4])
                va, vb = self.rd(a, ('in', pc)), self.rd(b, ('in', pc))
                if va is None or vb is None: raise Stop('unassigned')
                self.solve(c, eadd(va, vb) if t == 'xor' else emul(va, vb))
                pc += 1; self.cost += 1
            elif t == 'set':
                self.solve(self.addr(fe, ins[1]), ins[2]); pc += 1; self.cost += 1
            elif t == 'jump':
                c, d, f = (self.addr(fe, o) for o in ins[1:4])
                vc, vd, vf = (self.rd(x, ('jump', pc, i)) for i, x in enumerate((c, d, f)))
                if None in (vc, vd, vf) or not (isK(vc) and isK(vd) and isK(vf)): raise Stop('jump guard')
                self.cost += 1
                if vc[0] == 0: pc += 1
                else:
                    if vd[0] == 0 or vf[0] == 0: raise Stop('jump to 0')
                    pc_e, fe_n = dlog(vd[0]), dlog(vf[0])
                    if pc_e >= NSLOTS: raise Stop('fetch')
                    pc, fe = pc_e, fe_n
            elif t == 'blake':
                m, cv, out, md = ins[1:]
                ms = [self.rd(self.addr(fe, o), ('in', pc)) for o in m]
                cva = self.addr(fe, cv); cvb = (cva + 1) % M
                oa = self.addr(fe, out); ob = (oa + 1) % M
                for x in (cvb, ob):
                    if x >= 2 ** self.kappa: raise Stop('read out of range')
                cv0, cv1 = self.rd(cva, ('in', pc)), self.rd(cvb, ('in', pc))
                mdv = self.rd(self.addr(fe, md), ('in', pc))
                if None in ms or None in (cv0, cv1, mdv): raise Stop('unassigned')
                if not all(canon(x) for x in ms + [cv0, cv1, mdv]): raise Stop('canonical')
                q = hashInput(cellBits(cv0) | (cellBits(cv1) << 128),
                              sum(cellBits(x) << (128 * i) for i, x in enumerate(ms)), cellBits(mdv))
                if self.support:                 # incoherent oracle: answer = committed output
                    if oa not in self.mem: self.mem[oa] = cellOf(random.getrandbits(128))
                    if ob not in self.mem: self.mem[ob] = cellOf(random.getrandbits(128))
                    if not (canon(self.mem[oa]) and canon(self.mem[ob])): raise Stop('canonical')
                else:
                    y = H(q)
                    self.solve(oa, cellOf(LO(y))); self.solve(ob, cellOf(y >> 128))
                pc += 1; self.cost += 10
            else:
                raise AssertionError
        raise Stop('steps')

def loader(pk, m, bits):
    L = min(len(bits), SIG_BITS + 1)
    st = toBits(pk, 128) + toBits(m, 256) + toBits(L, 128) + bits[:SIG_BITS]
    return {i: cellOf(ofBits(st[128 * i:128 * i + 128])) for i in range(4 + 43)}
# ============================================================================ HL-TRI checks
def split_groups(svec, j):
    return [((j,) if g == 0 else ()) + tuple(svec[k] for k in GROUPS[g]) for g in range(NG)]

def entry_choice(svec, j):
    tups = split_groups(svec, j)
    def ch(a, ctx):
        if a in C_H:
            g = C_H.index(a)
            return ofK(gpow(ENTRY_OF[(g, tups[g])]))
        return None
    return ch

def idx_cell(v, j):
    return cellOf(j | sum(v[k] << (1 + POS[k]) for k in range(42)))

def forced_walk(svec, j):
    tr = list(range(PROLOGUE_LEN))
    for g, tup in enumerate(split_groups(svec, j)):
        e = ENTRY_OF[(g, tup)]
        tr += list(range(e, e + BLOCK_LEN[(g, tup)]))
    tr += list(range(R_SLOT, SENT))
    return tr

def layer_vector(rng):
    v = [rng.randrange(W[k]) for k in range(42)]
    while sum(v) != LAYER:
        k = rng.randrange(42)
        if sum(v) < LAYER and v[k] < W[k] - 1: v[k] += 1
        elif sum(v) > LAYER and v[k] > 0: v[k] -= 1
    return v

def support_run(v, seed):
    random.seed(seed)
    j = seed & 1
    img = {C_IDX: idx_cell(v, j)}
    mac = Machine(loader(7, 0, [0] * SIG_BITS), choose=entry_choice(v, j), image=img, support=True)
    mac.mem[C_S[8]] = cellOf(7)
    cost = mac.run()
    return cost, len(mac.trace), [pc for pc, _ in mac.trace] == forced_walk(v, j)

def offlayer_run(v, seed):
    random.seed(seed)
    j = seed & 1
    img = {C_IDX: idx_cell(v, j)}
    mac = Machine(loader(1, 0, [0] * SIG_BITS), choose=entry_choice(v, j), image=img, support=True)
    mac.mem[C_S[8]] = cellOf(1)
    try:
        mac.run(); return 'completed'
    except Stop as e:
        return str(e)

def jland_run(v, seed, mode):
    """Group-0 landings whose junk bit disagrees with the index cell, on an on-layer vector v.
    `flip`: the index's bit 0 is the other bit. `rand`: the index cell is a random word."""
    rng = random.Random(seed)
    random.seed(seed)
    j = rng.randrange(2)
    if mode == 'flip':
        idx = idx_cell(v, 1 - j)
    else:
        idx = cellOf(rng.getrandbits(128))
        assert idx != idx_cell(v, j)
    mac = Machine(loader(7, 0, [0] * SIG_BITS), choose=entry_choice(v, j), image={C_IDX: idx},
                  support=True)
    mac.mem[C_S[8]] = cellOf(7)
    try:
        mac.run(); return 'completed'
    except Stop as e:
        return str(e)

def honest_trial(seed):
    rng = random.Random(seed)
    pk, sk = keygen(rng)
    out = []
    m = rng.getrandbits(256)
    bits = sign(sk, m, rng)
    ok = verify(pk, m, bits)
    y = H(idxQuery(m, ofBits(bits[128 * 42:]), pk))
    s = digits(idxOf(y))
    mac = Machine(loader(pk, m, bits), choose=entry_choice(s, y & 1))
    cost = mac.run()
    out.append((ok, cost, len(mac.trace), [pc for pc, _ in mac.trace] == forced_walk(s, y & 1)))
    for what in ('word', 'nonce', 'msg', 'pk'):
        b2, m2, pk2 = list(bits), m, pk
        if what == 'word': b2[rng.randrange(42 * 128)] ^= 1
        if what == 'nonce': b2[42 * 128 + rng.randrange(128)] ^= 1
        if what == 'msg': m2 ^= 1 << rng.randrange(256)
        if what == 'pk': pk2 ^= 1 << rng.randrange(128)
        v = verify(pk2, m2, b2)
        y2 = H(idxQuery(m2, ofBits(b2[128 * 42:]), pk2))
        s2 = digits(idxOf(y2))
        mac = Machine(loader(pk2, m2, b2), choose=entry_choice(s2, y2 & 1))
        try: mac.run(); ok2 = True
        except Stop: ok2 = False
        out.append((what, ok2 == v))
    return out

def midblock_run(v, seed):
    rng = random.Random(seed)
    j = seed & 1
    tups = split_groups(v, j)
    g = rng.randrange(NG)
    delta = rng.randrange(1, BLOCK_LEN[(g, tups[g])])
    def ch(a, ctx):
        if a in C_H:
            gg = C_H.index(a)
            e = ENTRY_OF[(gg, tups[gg])]
            return ofK(gpow(e + (delta if gg == g else 0)))
        return cellOf(rng.getrandbits(128))
    random.seed(seed)
    img = {C_IDX: idx_cell(v, j)}
    mac = Machine(loader(7, 0, [0] * SIG_BITS), choose=ch, image=img, support=True)
    mac.mem[C_S[8]] = cellOf(7)
    try:
        mac.run(); return 'completed'
    except Stop as e:
        return str(e)

if __name__ == "__main__":
    items = list(prog.items()) + [(SENT, PAD)]
    chunks = [items[i::9] for i in range(9)]
    with Pool(9) as pool:
        bad = sum(pool.map(frame_chunk, chunks))
        check(bad == 0, f"frame lemma bad={bad}")
        rng = random.Random(11)
        vecs = [layer_vector(rng) for _ in range(400)]
        z = [0] * 42; z[41] = 15; rest = LAYER - 15
        for k in range(41):
            a = min(7, rest); z[k] = a; rest -= a
        vecs.append(z)
        sup = pool.starmap(support_run, [(v, i) for i, v in enumerate(vecs)])
        check(all(f for _, _, f in sup), "support forced walk")
        costs = {(c, n) for c, n, _ in sup}
        print("support (cost, steps):", costs)
        check(len(costs) == 1, "constant cost and steps")
        off = []
        for i in range(80):
            v = [rng.randrange(W[k]) for k in range(42)]
            if sum(v) != LAYER: off.append(v)
        offr = pool.starmap(offlayer_run, [(v, i) for i, v in enumerate(off)])
        check(all(r == 'relation' for r in offr), f"off-layer rejected {set(offr)}")
        mids = pool.starmap(midblock_run, [(v, 1000 + i) for i, v in enumerate(vecs[:200])])
        check(all(r != 'completed' for r in mids), "mid-block landings never complete")
        print("mid-block outcomes", set(mids))
        jr = pool.starmap(jland_run, [(v, 2000 + i, mode) for i, v in enumerate(vecs[:90])
                                      for mode in ('flip', 'rand')])
        check(all(r == 'relation' for r in jr), f"junk-bit landings rejected {set(jr)}")
        print("junk-bit landing outcomes", set(jr), len(jr))
        hon = pool.map(honest_trial, range(8))
        for h in hon:
            ok, cost, n, fw = h[0]
            check(ok and fw, "honest verify/forced walk")
            check(all(x[1] for x in h[1:]), "tamper agree")
        print("honest (cost, steps):", {(h[0][1], h[0][2]) for h in hon})
    c = next(iter(costs))[0]
    print("claim", c + 120)
    print("RESULT:", "PASS" if not FAIL else f"FAIL {FAIL[:5]}")
```
