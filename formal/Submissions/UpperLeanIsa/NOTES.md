# HL-FLAT-A: design notes

Claim **1598** cycles (planned 1629; `MachineFaithful.machine_cycles_1629` also holds).
Previous record: 85343 (Winternitz w=256, Rice-tree dispatch).

## 1. Scheme (`SchemeFlat.lean`, `LayerScheme`, `LayerBits`, `LayerWire`, `LayerDigits`, `LayerCount`, `LayerAvailability`)

- 42 chains, `wid k = 3` for `k < 40` and `4` for `k ∈ {40, 41}`; `len k = 2^wid k`.
  Digits are consecutive `wid`-bit fields of the 128-bit index (`digitW`, `pos_42 = 128`);
  chain positions are numbered from `off k = 7k` / `280 + 15(k−40)`.
- The accepted layer is `Σ_k s_k = 106`, with `s_k` the verifier's remaining steps. The layer
  below 106 is certified to fail availability (`LayerAvailability`, exact integer counts from
  `LayerCount`).
- Signing samples fresh uniform 128-bit nonces (never a counter; a counter admits a birthday
  search on signed classes) until the index lands on the layer, for at most `2^19` trials;
  `Flat.signingFailure` bounds the failure probability.
- Every query is 896 bits. Chain step `(k, j)`: metadata 1, tags `sym` in 3 cells (7 symbols,
  343 ≥ 310 positions). Index: metadata 10. Root: a tagged 10-call Merkle–Damgård absorption
  (R10) whose first call uses two XOR-copied tops as its cv pair; metadata `0, 2, …, 9, 5504`.
- Costs (`Resources`): keygen `2·310 + 20 = 640`, sign `2^20`, verify `2·106 + 2 + 20 = 234`.

## 2. Security (Tier A, κ = 2^-128 per compression)

Generic in `P : Params` under the hypothesis bundle `Params.Hyp` (`Records.lean`), discharged by
`Flat.hyp` (`FlatHyp.lean`): digit and tag injectivity, metadata separation, `1 ≤ layer`,
`2 ≤ len 0`, `200·2^108 ≤ numValid ≤ 2^127`, and keygen/verify costs `≤ 2^20`.

- `Correctness` (fixed-table semantics `verifyValue` / `fixed_verify`, `correct`), `Resources`,
  `BasicProperties` (`encode_decode`, determinism, `admissible`).
- `Records` (`location_eq_of_input_eq` by tags and metadata, no collision exception), `IdxBase`
  (index queries are content-separated from records), `KeygenBridge` (`E_run_keygen`).
- `Events` (`root_binding` for R10, `accept_core`, antichain `digits_eq_of_le`).
- `Exposure`, `Targets`: chain steps are charged hidden-input + second-preimage, `2·2^-129` per
  compression; root calls second-preimage only.
- `IdxLoop`, `IdxCharges`, `IdxRho`, `IdxRows`, `RowIneq`, `RowPotential`: the UpperRiscv index
  analysis (`signRho_bound`, `psi_charge`, `psi_dom`), charging `θψ` at `2·2^-128` per index
  query before signing and `IdxPost` at `2^-128` per query after.
- `StageB` (`ΦB`, split by query shape), `StageA` (`ΦA` with `θψ`), `Security`:
  `Pr ≤ B/2^128 < B/2^127` (keygen's first chain query gives `B ≥ 2`).

## 3. Bytecode (`MachineProgram.lean`, UNI layout)

`logSize = 18`, `memLog = 16`, 58-slot prologue. Frames `F_k = g^((k+1)·2^33)` (indexed from 1;
`e_0 = 0` would give a universal forgery). Chain `k` is dispatched by
`MUL(H_k, g, H'_k); JUMP(ONE, H_k, F_k)` with `H_k` a prover hint; only the frame-shifted entries
`JUMP(ONE, H'_k, ONE)` of chain `k` can execute in frame `F_k`. Entry `s` sits at
`BASE k + 21·s`. A block is the tie into the accumulator, the landing-encoded product
`MUL(G_{k−1}, H_k, G_k)`, the `s` inline chain `BLAKE2S` steps and the next dispatch; chain 41 exits
by `JUMP(ONE, K0, ONE)` with `K0 = g^rootSlot`. The root is 10 tagged `BLAKE2S` and an `XOR` into
the pk cell, falling through to the sentinel.

The plan's model (`hlflat_model.py`) has one extra non-hash op in a zero-digit block, so its
instruction count depends on the oracle's index answer, while the contract's `steps` is a pure
function of `(pk, m, σ)`. The UNI variant makes every block's non-hash cost digit-independent:

- chain `k ≥ 1` with `s = 0`: `XOR(W_k, Z, rootTop k)` replaces `SET T_k`, and
  `XOR(acc_{k−1}, Z, acc_k)` replaces the tie XOR;
- chain 0: the root's first XOR copy moves into the block (`XOR(TOP_0, Z, CV)` if `s ≥ 1`,
  `XOR(W_0, Z, CV)` if `s = 0`); chain 1's last `BLAKE2S` writes straight to `(CV+1, CV+2)`;
- the root segment is 10 `BLAKE2S` plus the pk XOR, `rootSlot = 262132`;
- `BASE k = 2740 + 168k` for `k ≤ 40`, `BASE 41 = 9806`; `Σ BASE + 21·106 = rootSlot`
  (`decide`). All cells have closed-form addresses below `2^16`.

Every completing run: 425 instructions, `308 + 1170 + 120 = 1598` cycles. `MachineCycles`
derives `Σ s = 106` from hash-free relations (`layer_of_facts`); `MachineSound.fixed_sound`
shows a completing run forces length 5504, an accepted index and root = pk;
`MachineFaithful.faithful` shows the honest image completes in exactly 425 steps iff the
verifier accepts. No program is evaluated over index ranges in the kernel: builders are
`@[irreducible]` and slots are decoded by arithmetic lemmas and `omega`.

## 4. Credits

- Adapted from the 85343-cycle leanISA record (this root's previous contents) and its
  predecessors; see that record's README for the earlier chain of credit.
- `Cache`, `IUB`, `Master`, the `Layer*` counting/digit/availability files and the `Idx*`,
  `RowIneq`, `RowPotential` index-grinding proofs are ported from the checked UpperRiscv
  submission (`formal/Submissions/UpperRiscv` on `main`); proof credit belongs to their
  authors as credited there (including Tom Wambsgans, PR #5, and Holindauer with Claude
  Fable 5.1, PR #15). Namespaces and imports are local to this root.
- HL-FLAT-A design, security layer, UNI bytecode and machine proofs prepared with Claude Opus 5.5.

## Appendix A. Executable model (`hlflat_uni_model.py`)

Exact-integer model of the UNI layout: builds the image, runs the frame lemma exhaustively,
checks honest and tampered runs against the verifier, and checks constant cost (1478 + 120) and
steps (425). Output: `honest costs {1478} steps(trace) {425}` … `RESULT: PASS`.

```python
#!/usr/bin/env python3
"""HL-FLAT-A executable model (milestone M1 + scheme spec for S-1).

Exact model of the leanISA image for HL-FLAT-A (FLAT-42 scheme, 128-bit index, tagged R10 root,
hinted-landing dispatch), executed with the leanerVM semantics of `Semantics/Step.lean` and the
contract's `LeanIsaMachine.runCost` (oracle BLAKE2S, sentinel test, weights 1 / 10), over the real
fields K = GF(2)[x]/(x^64+x^4+x^3+x+1), g = x, E = K[y]/(y^3+y+1).

Everything is exact integer arithmetic.  Run: python3 hlflat_model.py  (exit code 0 = all pass).

Checks:
  A. scheme spec (mirrors SchemeFlat.lean): N_106 numeral, layer 105 fails, availability
     certificate, budgets, tag injectivity, md separation;
  B. image: every slot, every cell, frames F_k = g^((k+1)*2^33), entry spacing 21,
     K0 = g^(root slot), operand ranges, frame-range lemma (exhaustive over every non-pad slot and
     every frame), no pad on any walk;
  C. honest runs: machine completes iff scheme verify accepts (random-oracle mock), cycles;
  D. worst case: exact DP over the layer + walks of every entry-vector class in support mode
     (incoherent oracle), max = CLAIM;
  E. adversarial simulator: random malicious hints / images / kappa; every completing run is the
     forced walk of a layer vector and verify accepts it.
"""
import hashlib, random, sys
from fractions import Fraction

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
W = [8] * 40 + [16] * 2                      # positions per chain; digit s_k < W[k]
BITS = [3] * 40 + [4] * 2
POS = [sum(BITS[:k]) for k in range(N_CHAINS)]
LAYER = 106
STEPS = [w - 1 for w in W]                   # 310 chain positions (steps)
OFF = [sum(STEPS[:k]) for k in range(N_CHAINS)]
assert sum(BITS) == 128 and sum(STEPS) == 310
SYM = lambda v: v + 3                        # symbol cell values 3..9
def tag(k, j):
    p = OFF[k] + j
    return (SYM(p % 7), SYM(p // 7 % 7), SYM(p // 49))
CHAIN_MD, IDX_MD = 1, 10
RHO = [0, 2, 3, 4, 5, 6, 7, 8, 9, 5504]      # Z, g, SYM_0..6, LEN: existing constant cells
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
        x = LO(H(chainQuery(k, j + t, x)))
    return x
def idxQuery(m, eta, pk): return hashInput(CV_CONST, m | (eta << 256) | (pk << 384), IDX_MD)
def digits(I): return [(I >> POS[k]) % (1 << BITS[k]) for k in range(N_CHAINS)]
def accepted(I): return sum(digits(I)) == LAYER
def rootQueries(tops):
    qs = []
    q = hashInput(tops[0] | (tops[1] << 128),
                  tops[2] | (tops[3] << 128) | (tops[4] << 256) | (tops[5] << 384), RHO[0])
    st = H(q); qs.append(q)
    for r in range(1, 10):
        t = tops[6 + 4 * (r - 1): 10 + 4 * (r - 1)]
        q = hashInput(st, t[0] | (t[1] << 128) | (t[2] << 256) | (t[3] << 384), RHO[r])
        st = H(q); qs.append(q)
    return LO(st), qs
def root(tops): return rootQueries(tops)[0]

def keygen(rng):
    seeds = [rng.getrandbits(128) for _ in range(N_CHAINS)]
    table = [[seeds[k]] for k in range(N_CHAINS)]
    for k in range(N_CHAINS):
        for j in range(STEPS[k]):
            table[k].append(LO(H(chainQuery(k, j, table[k][j]))))
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
        I = LO(H(idxQuery(m, eta, pk)))
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
    I = LO(H(idxQuery(m, eta, pk)))
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
N106 = CNT[106]
check(N106 == 69117521303608168194311003377855640, "N_106 numeral")
print("N_106 =", N106)

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
    m = (2 ** 128 - N) << (P - 128)
    return pow_rounded(m, P, L, True), pow_rounded(m, P, L, False), P
up, lo, P = miss_bounds(N106, TRIALS)
check(up <= 1 << (P - 128), "availability: (1-N106/2^128)^(2^19) <= 2^-128")
up5, lo5, _ = miss_bounds(CNT[105], TRIALS)
check(lo5 > 1 << (P - 128), "layer 105 certified to fail")
# the Lean certificate (SchemeAvailability.lean): p >= PLO/2^20, block 2^9, x^32 <= R1, R1^32 <= 2^-128
PLO = 212
check(N106 * 2 ** 20 >= PLO * 2 ** 128, "Lean cert: N106/2^128 >= 212/2^20")
X = Fraction(2 ** 20, 2 ** 20 + 2 ** 9 * PLO)          # (1-p)^(2^9) <= 1/(1 + 2^9 p)
R1 = Fraction(428, 10000)
check(X ** 32 <= R1, "Lean cert: x^32 <= 428/10000")
check(R1 ** 32 <= Fraction(1, 2 ** 128), "Lean cert: (428/10000)^32 <= 2^-128")
check(2 ** 9 * 32 * 32 == TRIALS, "Lean cert: 2^9*32*32 = 2^19")
# budgets (blockCost 896 = 2)
bc = max(1, (896 + 511) // 512)
check(bc == 2, "blockCost 896 = 2")
check(bc * (310 + 10) == 640, "keygen 640")
check(bc * TRIALS == 2 ** 20, "sign = 2^20 exactly")
check(bc * (1 + LAYER + 10) == 234, "verify 234")
check(SIG_BITS == 5504, "sig bits")
# tags / md separation
alltags = {tag(k, j) for k in range(42) for j in range(STEPS[k])}
check(len(alltags) == 310, "chain tags injective on 310 positions")
check(len(set(RHO)) == 10 and CHAIN_MD not in RHO and IDX_MD not in RHO and CHAIN_MD != IDX_MD,
      "md separation chain/index/root")
check(all(v < 2 ** 128 for v in RHO), "root tags 128-bit")
# ============================================================================ B'. UNI layout (constant per-block cost)
LOG_SIZE = 18
NSLOTS = 1 << LOG_SIZE
SENT = NSLOTS - 1
MEMLOG = 16
SPACING = 21
C_PK, C_M0, C_M1, C_LEN = 0, 1, 2, 3
C_W = [4 + k for k in range(42)]
C_NONCE = 46
C_Z, C_ONE, C_TIDX, C_G, C_K0 = 47, 48, 49, 50, 51
C_SYM = [52 + v for v in range(7)]
C_F = [59 + k for k in range(42)]
C_IDX = 101
C_T = [103 + k for k in range(42)]
C_ACC = [145 + k for k in range(41)] + [C_IDX]
C_H = [186 + k for k in range(42)]
C_H1 = [228 + k for k in range(42)]
C_GP = [C_H[0]] + [270 + k for k in range(1, 41)] + [C_K0]
C_TOP = [320 + 2 * k for k in range(42)]
C_CV = 410
def XC(k, t): return 1024 + 32 * k + 2 * t
C_S = [2400 + 2 * r for r in range(10)]
ROOT_TOP = [C_CV, C_CV + 1] + [C_TOP[k] for k in range(2, 42)]
CHAIN_OUT = [C_TOP[0], C_CV + 1] + [C_TOP[k] for k in range(2, 42)]
RHO_CELL = [C_Z, C_G] + C_SYM + [C_LEN]
check([cellBits(v) for v in [(0,0,0), ofK(G)] + [cellOf(SYM(v)) for v in range(7)] + [cellOf(5504)]] == RHO, "rho")
ROOT_LEN = 11
R_SLOT = SENT - ROOT_LEN
BASE = [2740 + 168 * k if k < 41 else 9806 for k in range(42)]
check(sum(BASE) + SPACING * LAYER == R_SLOT, "sum base")
E_FRAME = [(k + 1) * 2 ** 33 for k in range(42)]
OPB = lambda a: a % M
prog = {}
def emit(slot, ins):
    assert slot not in prog and 0 <= slot < SENT, slot
    prog[slot] = ins
def op(a): return ('g', OPB(a))
def X_(a, b, c): return ('xor', op(a), op(b), op(c))
def MUL(a, b, c): return ('mul', op(a), op(b), op(c))
def SET(a, v): return ('set', op(a), v)
def JMP(c, d, f): return ('jump', op(c), op(d), op(f))
def BLK(m, cv, out, md): return ('blake', tuple(op(x) for x in m), op(cv), op(out), op(md))
def I0(k): return ('jump', ('g', (C_ONE - E_FRAME[k]) % M), ('g', (C_H1[k] - E_FRAME[k]) % M),
                   ('g', (C_ONE - E_FRAME[k]) % M))
PAD = ('xor', ('zero',), ('zero',), ('zero',))
K0_VAL = ofK(gpow(R_SLOT))
F_VAL = [ofK(gpow(e)) for e in E_FRAME]
def fpat(k, s): return cellOf(s << POS[k])
PRO = []
PRO += [SET(C_Z, ZERO), SET(C_ONE, ofK(1)), SET(C_LEN, cellOf(5504)), SET(C_TIDX, cellOf(IDX_MD)),
        SET(C_G, ofK(G)), SET(C_K0, K0_VAL)]
PRO += [SET(C_SYM[v], cellOf(SYM(v))) for v in range(7)]
PRO += [SET(C_F[k], F_VAL[k]) for k in range(42)]
PRO += [BLK([C_M0, C_M1, C_NONCE, C_PK], C_Z, C_IDX, C_TIDX), MUL(C_H[0], C_G, C_H1[0]),
        JMP(C_ONE, C_H[0], C_F[0])]
for i, x in enumerate(PRO): emit(i, x)
PROLOGUE_LEN = len(PRO)
check(PROLOGUE_LEN == 58, "prologue 58")
def chain_ops(k, s):
    j0 = W[k] - 1 - s
    ops = []
    for t in range(s):
        src = C_W[k] if t == 0 else XC(k, t - 1)
        dst = CHAIN_OUT[k] if t == s - 1 else XC(k, t)
        a, bb, c = tag(k, j0 + t)
        ops.append(BLK([src, C_SYM[a - 3], C_SYM[bb - 3], C_SYM[c - 3]], C_Z, dst, C_ONE))
    return ops
def block(k, s):
    ops = [I0(k)]
    if k == 0:
        ops.append(SET(C_ACC[0], fpat(0, s)))
        ops += chain_ops(0, s)
        ops.append(X_(C_W[0] if s == 0 else C_TOP[0], C_Z, C_CV))
    else:
        ops.append(X_(C_W[k], C_Z, ROOT_TOP[k]) if s == 0 else SET(C_T[k], fpat(k, s)))
        ops.append(X_(C_ACC[k - 1], C_Z if s == 0 else C_T[k], C_ACC[k]))
        ops.append(MUL(C_GP[k - 1], C_H[k], C_GP[k]))
        ops += chain_ops(k, s)
    if k < 41: ops += [MUL(C_H[k + 1], C_G, C_H1[k + 1]), JMP(C_ONE, C_H[k + 1], C_F[k + 1])]
    else: ops.append(JMP(C_ONE, C_K0, C_ONE))
    return ops
ENTRY = {}
BLOCK_LEN = {}
for k in range(42):
    for s in range(W[k]):
        e = BASE[k] + SPACING * s
        ENTRY[e] = (k, s)
        ops = block(k, s)
        BLOCK_LEN[(k, s)] = len(ops)
        check(len(ops) <= SPACING, "fits")
        for i, x in enumerate(ops): emit(e + i, x)
check(BASE[0] >= PROLOGUE_LEN and BASE[41] + SPACING * W[41] <= R_SLOT, "regions")
p = R_SLOT
ROOT = [BLK([ROOT_TOP[2], ROOT_TOP[3], ROOT_TOP[4], ROOT_TOP[5]], C_CV, C_S[0], RHO_CELL[0])]
for r in range(1, 10):
    ROOT.append(BLK([ROOT_TOP[6 + 4 * (r - 1) + i] for i in range(4)], C_S[r - 1], C_S[r], RHO_CELL[r]))
ROOT.append(X_(C_S[9], C_Z, C_PK))
for i, x in enumerate(ROOT): emit(R_SLOT + i, x)
check(R_SLOT + len(ROOT) == SENT, "root to sentinel")
SENT_INS = PAD
def fetch(i):
    if not (0 <= i < NSLOTS): return None
    if i == SENT: return SENT_INS
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
bad = 0
for i, ins in list(prog.items()) + [(SENT, SENT_INS)]:
    for fi, fe in enumerate(FRAMES):
        ok = reads_ok(ins, fe)
        want = (fi == 0 and i not in ENTRY and i != SENT) or (fi > 0 and ENTRY.get(i, (None,))[0] == fi - 1)
        if ok != want: bad += 1
check(bad == 0, f"frame lemma bad={bad}")
# every non-entry frame-1 operand < 2^16
for i, ins in prog.items():
    if i not in ENTRY:
        check(all(o[1] < 2 ** 16 for o in operands(ins)), "ops < 2^16")
# output cells written once per path: cells distinct families
print("image", len(prog), "R", R_SLOT, "BASE", BASE[0], BASE[40], BASE[41])
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

def entry_choice(svec):
    """Prover strategy: H_k := g^(entry of (k, s_k))."""
    def ch(a, ctx):
        if a in C_H: return ofK(gpow(BASE[C_H.index(a)] + SPACING * svec[C_H.index(a)]))
        return None
    return ch

def forced_walk(svec):
    tr = list(range(PROLOGUE_LEN))
    for k in range(42):
        e = BASE[k] + SPACING * svec[k]
        tr += list(range(e, e + BLOCK_LEN[(k, svec[k])]))
    tr += list(range(R_SLOT, SENT))
    return tr
rng = random.Random(7)
pk, sk = keygen(rng)
costs = set(); steps = set()
for trial in range(6):
    m = rng.getrandbits(256)
    bits = sign(sk, m, rng)
    check(verify(pk, m, bits), "honest verify")
    I = LO(H(idxQuery(m, ofBits(bits[128 * 42:]), pk)))
    s = digits(I)
    mac = Machine(loader(pk, m, bits), choose=entry_choice(s))
    try:
        cost = mac.run(); costs.add(cost); steps.add(len(mac.trace))
        check([pc for pc, _ in mac.trace] == forced_walk(s), "forced walk")
    except Stop as e:
        check(False, f"honest stop {e}")
    for what in ('word', 'nonce', 'msg', 'pk'):
        b2, m2, pk2 = list(bits), m, pk
        if what == 'word': b2[rng.randrange(42 * 128)] ^= 1
        if what == 'nonce': b2[42 * 128 + rng.randrange(128)] ^= 1
        if what == 'msg': m2 ^= 1 << rng.randrange(256)
        if what == 'pk': pk2 ^= 1 << rng.randrange(128)
        v = verify(pk2, m2, b2)
        s2 = digits(LO(H(idxQuery(m2, ofBits(b2[128 * 42:]), pk2))))
        mac = Machine(loader(pk2, m2, b2), choose=entry_choice(s2))
        try: mac.run(); ok = True
        except Stop: ok = False
        check(ok == v, f"agree {what}")
print("honest costs", costs, "steps(trace)", steps)
# all layer classes in support mode: constant cost
allc = set()
for trial in range(300):
    v = [rng.randrange(W[k]) for k in range(42)]
    while sum(v) != LAYER:
        k = rng.randrange(42)
        if sum(v) < LAYER and v[k] < W[k] - 1: v[k] += 1
        elif sum(v) > LAYER and v[k] > 0: v[k] -= 1
    if trial % 3 == 0:
        for k in range(42):
            if sum(v) > LAYER - 0: pass
    img = {C_IDX: cellOf(sum(v[k] << POS[k] for k in range(42)))}
    pk_s = rng.getrandbits(128)
    mac = Machine(loader(pk_s, 0, [0] * SIG_BITS), choose=entry_choice(v), image=img, support=True)
    mac.mem[C_S[9]] = cellOf(pk_s)
    try:
        cost = mac.run(); allc.add((cost, len(mac.trace)))
        check([pc for pc, _ in mac.trace] == forced_walk(v), "support forced walk")
    except Stop as e:
        check(False, f"support stop {e}")
# many zeros vector
v = [0] * 42; v[40] = 15; v[41] = 15; rest = 76
for k in range(40):
    a = min(7, rest); v[k] = a; rest -= a
assert sum(v) == 106
img = {C_IDX: cellOf(sum(v[k] << POS[k] for k in range(42)))}
mac = Machine(loader(5, 0, [0] * SIG_BITS), choose=entry_choice(v), image=img, support=True)
mac.mem[C_S[9]] = cellOf(5)
cost = mac.run(); allc.add((cost, len(mac.trace)))
print("support (cost, trace len) set:", allc)
check(len(allc) == 1, "constant cost")
for trial in range(60):
    v = [rng.randrange(W[k]) for k in range(42)]
    if sum(v) == LAYER: continue
    img = {C_IDX: cellOf(sum(v[k] << POS[k] for k in range(42)))}
    mac = Machine(loader(1, 0, [0] * SIG_BITS), choose=entry_choice(v), image=img, support=True)
    mac.mem[C_S[9]] = cellOf(1)
    try: mac.run(); check(False, "off-layer completed")
    except Stop as e: check(str(e) == 'relation', f"offlayer {e}")
print("RESULT:", "PASS" if not FAIL else f"FAIL {FAIL[:5]}")
```
