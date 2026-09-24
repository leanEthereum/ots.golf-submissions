# RT-MX: mixed 7/6-bit Winternitz with offset leaves, 33843 cycles

Lineage: RT (nconsigny, PR #35, 85343) → RT-128 (lucemans, PR #36, 49335, the current record)
→ RT-MX (this root, claim 33843). The scheme and security proofs, the forced-dispatch bytecode
and the machine proofs all descend from RT. Only the encoding and the parameters changed.

## 1. Where the cycles are

In leanISA a `BLAKE2S` costs 10 cycles and every other instruction costs 1, plus a fixed 120.
All three generations spend almost everything on hashing:

| root | words | worst `BLAKE2S` | other instructions | score |
|---|---:|---:|---:|---:|
| RT (base 256) | 34 | 8449 | 733 | 85343 |
| RT-128 (base 128) | 39 | 4865 | 564 | 49335 |
| RT-MX (this) | 43 | 3319 | 532 | 33843 |

The worst-case hash count is the Winternitz chain walk of the worst message plus one root
absorption per word. Only the scheme can move it. Bytecode tricks are worth tens of cycles.

## 2. Idea

The 5504-bit signature limit allows 43 words of 128 bits. A uniform base cannot use all of
them: base 64 needs 45 words, base 128 uses 39. Mixed widths can:

- 41 message fields: ten of 7 bits and thirty-one of 6 bits (70 + 186 = 256 bits);
- 2 checksum digits of 6 bits (the checksum is at most 3223 < 4096).

The fields are aligned to the two 128-bit message cells, so no field straddles a cell:
cell 2 (message bits 128..255) = fields 0..19 = 8×7 + 12×6 bits,
cell 1 (bits 0..127) = fields 20..40 = 2×7 + 19×6 bits.

Exhaustive search over 7/6-bit mixes and checksum bases (all 43-word layouts) found this
split optimal: 3319 worst-case `BLAKE2S`. With a base-128 checksum the same fields give 3472.

## 3. The trick that keeps the proofs cheap: offset leaves

Chains of different lengths would need dependent types all through `Records`, `KeygenBridge`
and the security files. Instead every chain keeps 127 steps, and a 6-bit field `d` is stored
as the chain digit `e = 64 + d`. Verification walks `127 − e = 63 − d` steps, exactly the
cost of a 64-step chain. Every digit stays below 128, so:

- `Checksum.wotsChecksumValue 128 (messageDigits m) = Σ (127 − e_k) = Σ (max_k − d_k)` is the
  mixed-width checksum with no new definition;
- the security half sees 43 uniform chains of 127 steps. It changed by constants only
  (39 → 43 chains, 40 → 44 root states, 4992 → 5504 bits, budgets 11008 / 10922).

`digits m = messageDigits m ++ [64 + C / 64, 64 + C % 64]`. The only new mathematics on the
scheme side is in `Encoding.lean`:
`messageDigits_injective` (contiguous fields: `toNat_eq_sum_fields`) and
`digits_incomparable`, proved through `digits_le_imp_eq`: componentwise `≤` on the message
digits gives `C a ≥ C b`, componentwise `≤` on the two offset checksum digits gives
`C a ≤ C b`, so the checksums and then the digit sums agree, and pointwise `≤` with equal
sums forces equality.

## 4. Bytecode

RT's design with these parameters (`MachineProgram.lean`, `logSize = 16`, `memLog = 16`):

- 131 constants: positions 1..127, `K0`, the length (5504), and a zero pair (cells 48, 49).
  The statement now fills all 47 loader cells, so no free zero cell exists; the pair costs
  2 cycles. `posCell 0` is the zero cell.
- Rice(1) `JUMP` trees on the leaf index `d = e − off k`: 128 leaves (63 unary nodes) for
  7-bit fields, 64 leaves (31 nodes) for 6-bit fields and for `c_lo`; a descending unary tree
  of 50 nodes for `c_hi − 64 ∈ [0, 50]`. Body steps exist only for positions
  `[off k + 1, 126]`.
- Ties: in each cell group the first field `SET`s the accumulator, middle fields `SET` a word
  and `XOR` it in, and the last field (in-cell offset 0) `XOR`s `posCell d` straight into the
  pinned message cell. 78 tie ops. Only `2^(width)` leaves exist per chain, which bounds `d`
  and makes each shifted word injective.
- Checksum in the exponent, forced identity `Σ_{k<41} E k + 64·(E 41 − 64) + E 42 = 5271`,
  `K0 = 836677`.
- 43 root absorptions, tags `44 − t`, then the pk `XOR` falls through into the sentinel.

## 5. Cost and the proved bound

Exact worst case (DP over every feasible leaf vector): 33722 cycles, at the all-zero message
(`c_hi = 114`, `c_lo = 87`): 3851 steps, 3319 `BLAKE2S`. For digit sums 0..23 the hash total is
constant (message hashes fall exactly as `c_lo` hashes rise), so dispatch cost alone decides the
worst case, and ascending Rice(1) trees keep that plateau flat.

Lean bound (`MachineCycles.totalCost_le`), with λ = 9:
`chainCost k e + 9e ≤ 1277 − off k + tieLen k` per Rice chain and `hiCost dh + 12·dh ≤ 736`
(`dh ≤ 50`). With the checksum identity these give `totalCost E ≤ 33723`, one above the exact
value because of the `⌊d/2⌋` floor. Claim `33723 + 120 = 33843`.
`seededRows = 2^16 + 2^16`.

## 6. How it was built

1. Cost breakdown first (section 1), to find which half of the certificate holds the score.
2. `mx_model.py` (appendix): builds all 65536 slots, simulates 300 honest messages and 300
   arbitrary leaf vectors against the closed forms, checks the tie arithmetic, and runs the DP
   for the exact worst case. A Python transcription of the Lean `cinstrAt` matched the model on
   all 65536 slots.
3. A design document with every constant, then three agents with one owner per file and
   milestones: scheme port (`Encoding` rewrite plus constants, about 9 minutes), machine core
   (`MachineProgram` to `MachineCycles`, about 16 minutes), machine proofs (`ConstraintMath`,
   `MachineProver/Honest/Sound/Faithful`, `Solution`, about 22 minutes).

## 7. Validation

- Clean build of the whole root from a fresh copy of the pinned contract: 49 s.
- `check_submission.py upper-leanisa`: ok, claim 33843, 572286 bytes.
- `certificate : submission.Certificate 33843` and `seeded_rows` type-check against the stub's
  statements; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `native_decide`, `admit` or `axiom` in the root.
- comparator was not run locally (its setup script clones with git); the hosted verifier is the
  judge.

## 8. What did not pay, and what is left

- A tighter security bound does not help leanISA. Words are fixed 128-bit cells, and a 44th
  word needs 125-bit words: about 3 bits more margin than `Pr ≤ B / 2^128` leaves under the
  required `B / 2^127`. That bound is already tight against the generic attack (each 896-bit
  query is 2 compressions and gives two independent ~2^-128 chances).
- Non-power-of-two radices near 76 would save about 150 more `BLAKE2S` but break the
  bit-disjoint `XOR` tie; a different tie (for example a mixed-radix `MUL`/add accumulation in
  the field) would be needed.
- Root packing: absorb four words per `BLAKE2S` (the message block has four 128-bit cells).
  43 → 11 root calls, about −320 cycles. Changes `RootBinding`, `QueryLayout` and the root part
  of `KeygenBridge`.
- Bytecode: leaf 0 at depth 1, dropping chain 0's `MUL` (RT §10.3), and a cheaper zero pair.
  Tens of cycles.
- The 1-cycle gap between the exact worst case and the proved bound.

## Appendix: `mx_model.py`

```python
"""Executable spec of RT-MX: mixed 7/6-bit digits with offset leaves, 43 chains of 127 steps.

Message digit k (k = 0..40, big-endian) is a bit field of width W[k] at bit offset O[k].
A 7-bit field d is stored as chain digit e = d; a 6-bit field d as e = 64 + d, so every chain
has 127 steps and every digit is < 128. Checksum C = sum (127 - e_k) = sum (max_k - d_k) <= 3223,
stored as two offset 6-bit digits e_41 = 64 + C / 64, e_42 = 64 + C % 64.
"""
import random

LOG = 16
SENT = (1 << LOG) - 1
NMSG, HI, LO = 41, 41, 42
NCH = 43
SIGLEN = NCH * 128                              # 5504 = maxSignatureBits
W = [7] * 8 + [6] * 12 + [7] * 2 + [6] * 19     # cell 2 = fields 0..19, cell 1 = fields 20..40
assert sum(W[:20]) == 128 and sum(W[20:]) == 128 and len(W) == NMSG
O = [sum(W[j] for j in range(k + 1, NMSG)) for k in range(NMSG)]
OFF = [0 if w == 7 else 64 for w in W]
MAXD = [(1 << w) - 1 for w in W]
TOTAL = NMSG * 127                              # sum e_k + C = 5207
CMAX = sum(MAXD)                                # 3223
HI_MAX = CMAX // 64                             # 50


def cell_of(k):
    return 2 if k < 20 else 1


def in_off(k):
    return O[k] - 128 if k < 20 else O[k]


def n_leaves(k):
    if k < NMSG:
        return 1 << W[k]
    return 64                                   # LO (HI uses the unary tree)


def off_of(k):
    return OFF[k] if k < NMSG else 64


LW, GW, UW = 7, 16, 18


def nU(k):
    return n_leaves(k) // 2 - 1


def disp_len(k):
    if k == HI:
        return 7 * HI_MAX + 5
    return UW * nU(k) + GW


def body_first(k):                              # first body position a run can reach
    return off_of(k) + 1


def region(k):
    return disp_len(k) + 127 - body_first(k)


N_CONST = 131                                   # 127 positions, K0, length, zero pair
R0 = N_CONST


def rBase(k):
    return R0 + sum(region(j) for j in range(k))


ROOT = SENT - 1 - NCH
PK = SENT - 1


def s0(k):
    if k == LO:
        return ROOT - 127
    return rBase(k) + disp_len(k) - body_first(k)   # s0 + body_first = end of dispatch


# ---- memory ----
Z = 48                                          # zero pair (48, 49), set by constants
def posCell(j): return Z if j == 0 else 100 + j
ONE, K0C = posCell(1), 400
def scr(k): return 1024 + 160 * k
zu = lambda k, i: scr(k) + i
tu = lambda k, i: scr(k) + 64 + i
zb = lambda k: scr(k) + 128
tb = lambda k: scr(k) + 129
tC = lambda k: scr(k) + 132
vC = lambda k: scr(k) + 133
gC = lambda k: scr(k) + 134
fC = lambda k: scr(k) + 135
acc = lambda k: scr(k) + 136
uC = scr(HI) + 137
def root(t): return Z if t == 0 else 8000 + 2 * t
def xC(k, j): return 9000 + 256 * k + 2 * j
sig = lambda k: 4 + k
gPrev = lambda k: ONE if k == 0 else gC(k - 1)
gOut = lambda k: K0C if k == LO else gC(k)

K0 = sum(s0(k) + 1 for k in range(NMSG)) + s0(LO) + 1 + TOTAL + 64


def tieOps(k, e):
    if k >= NMSG:
        return []
    d = e - OFF[k]
    first, last = k in (0, 20), k in (19, 40)
    if first:
        return [('setc', acc(k), ('w', d << in_off(k)))]
    if last:
        assert in_off(k) == 0
        return [('xor', acc(k - 1), posCell(d), cell_of(k))]
    return [('setc', fC(k), ('w', d << in_off(k))), ('xor', acc(k - 1), fC(k), acc(k))]


tieLen = lambda k: len(tieOps(k, OFF[k])) if k < NMSG else 0


def coreOps(k, e):
    if e < 127:
        return [('blake', sig(k), posCell(k), posCell(e), Z, Z, xC(k, e + 1), ONE),
                ('mul', gPrev(k), tC(k), gOut(k)),
                ('setc', tC(k), ('tgt', s0(k) + e + 1)),
                ('jump', ONE, tC(k), ONE)]
    return [('xor', sig(k), Z, xC(k, 127)),
            ('setc', tC(k), ('tgt', s0(k) + 128)),
            ('mul', gPrev(k), tC(k), gOut(k)),
            ('setc', vC(k), ('tgt', s0(k) + 127)),
            ('jump', ONE, vC(k), ONE)]


def hiOps(dh):
    e = 64 + dh
    return [('blake', sig(HI), posCell(HI), posCell(e), Z, Z, xC(HI, e + 1), ONE),
            ('setc', uC, ('tgt', 64 * dh)),
            ('mul', gC(NMSG - 1), uC, gC(HI)),
            ('setc', tC(HI), ('tgt', s0(HI) + e + 1)),
            ('jump', ONE, tC(HI), ONE)]


def gBase(k, q):
    R = rBase(k)
    return R + UW * q + 2 if q < nU(k) else R + UW * nU(k)


def leafSlot(k, d):                             # d = leaf index = e - offset
    if k == HI:
        return rBase(HI) + 7 * (HI_MAX - d) + 2 if d >= 1 else rBase(HI) + 7 * HI_MAX
    return gBase(k, d // 2) + 2 + LW * (d % 2)


code = [('pad',)] * (SENT + 1)
def put(s, ins):
    assert code[s] == ('pad',), (s, code[s], ins)
    code[s] = ins

for s in range(127):
    put(s, ('setc', posCell(s + 1), ('pos', s + 1)))
put(127, ('setc', K0C, ('tgt', K0)))
put(128, ('setc', 3, ('len',)))
put(129, ('setc', Z, ('zero',)))
put(130, ('setc', Z + 1, ('zero',)))
for k in [k for k in range(NCH) if k != HI]:
    R = rBase(k)
    for i in range(nU(k)):
        put(R + UW * i, ('setc', tu(k, i), ('tgt', R + UW * (i + 1))))
        put(R + UW * i + 1, ('jump', zu(k, i), tu(k, i), ONE))
    for q in range(nU(k) + 1):
        g0 = gBase(k, q)
        put(g0, ('setc', tb(k), ('tgt', g0 + 2 + LW)))
        put(g0 + 1, ('jump', zb(k), tb(k), ONE))
        for b in range(2):
            e = off_of(k) + 2 * q + b
            ops = tieOps(k, e) + coreOps(k, e)
            assert len(ops) <= LW
            for i, op in enumerate(ops):
                put(g0 + 2 + LW * b + i, op)
R = rBase(HI)
for i in range(HI_MAX):
    put(R + 7 * i, ('setc', tu(HI, i), ('tgt', R + 7 * (i + 1))))
    put(R + 7 * i + 1, ('jump', zu(HI, i), tu(HI, i), ONE))
for dh in range(HI_MAX + 1):
    for i, op in enumerate(hiOps(dh)):
        put(leafSlot(HI, dh) + i, op)
for k in range(NCH):
    for j in range(body_first(k), 127):
        put(s0(k) + j, ('blake', xC(k, j), posCell(k), posCell(j), Z, Z, xC(k, j + 1), ONE))
for t in range(NCH):
    put(ROOT + t, ('blake', xC(t, 127), Z, Z, Z, root(t), root(t + 1), posCell(NCH + 1 - t)))
put(PK, ('xor', root(NCH), Z, 0))
assert code[SENT] == ('pad',)
for k in range(LO):
    assert s0(k) + 127 == rBase(k + 1)
assert rBase(LO) + disp_len(LO) <= s0(LO) + body_first(LO)


# ---- closed forms ----
def riceDepth(k, d):
    return d // 2 + 2 if d // 2 < nU(k) else nU(k) + 1

hiDepth = lambda dh: HI_MAX if dh == 0 else HI_MAX + 1 - dh
leafLen = lambda k, e: tieLen(k) + (4 if e < 127 else 5)
leafCost = lambda k, e: tieLen(k) + (13 if e < 127 else 5)
bodyLen = lambda e: max(126 - e, 0)
chainSteps = lambda k, e: 2 * riceDepth(k, e - off_of(k)) + leafLen(k, e) + bodyLen(e)
chainCost = lambda k, e: 2 * riceDepth(k, e - off_of(k)) + leafCost(k, e) + 10 * bodyLen(e)
hiSteps = lambda dh: 2 * hiDepth(dh) + 5 + bodyLen(64 + dh)
hiCost = lambda dh: 2 * hiDepth(dh) + 14 + 10 * bodyLen(64 + dh)
def totalSteps(E):
    return N_CONST + sum(chainSteps(k, E[k]) for k in range(NMSG)) + hiSteps(E[HI] - 64) + chainSteps(LO, E[LO]) + NCH + 1
def totalCost(E):
    return N_CONST + sum(chainCost(k, E[k]) for k in range(NMSG)) + hiCost(E[HI] - 64) + chainCost(LO, E[LO]) + 10 * NCH + 1


def walk(E):
    z = {}
    for k in [k for k in range(NCH) if k != HI]:
        q, b = divmod(E[k] - off_of(k), 2)
        for i in range(nU(k)):
            z[zu(k, i)] = 1 if i < q else 0
        z[zb(k)] = b
    for i in range(HI_MAX):
        z[zu(HI, i)] = 1 if i < HI_MAX - (E[HI] - 64) else 0
    mem, s, n, cost, h = {}, 0, 0, 0, 0
    while s != SENT:
        ins = code[s]
        assert ins[0] != 'pad', s
        n += 1; cost += 10 if ins[0] == 'blake' else 1; h += ins[0] == 'blake'
        if ins[0] == 'setc':
            assert mem.get(ins[1], ins[2]) == ins[2], (s, ins)
            mem[ins[1]] = ins[2]
        if ins[0] == 'jump':
            assert code[s - 1][0] == 'setc' and code[s - 1][1] == ins[2]
            if ins[1] == ONE or z[ins[1]]:
                t = mem[ins[2]][1]
                assert t > s
                s = t
                continue
        s += 1
    return n, cost, h


def digits(m):
    d = [(m >> O[k]) & MAXD[k] for k in range(NMSG)]
    e = [OFF[k] + d[k] for k in range(NMSG)]
    C = sum(127 - x for x in e)
    assert C == sum(MAXD[k] - d[k] for k in range(NMSG))
    return e + [64 + C // 64, 64 + C % 64]


def tie_check(m):
    E = digits(m)
    for cell, ks in ((2, range(0, 20)), (1, range(20, 41))):
        acc_v = 0
        for k in ks:
            acc_v ^= (E[k] - OFF[k]) << in_off(k)
        assert acc_v == ((m >> 128) if cell == 2 else (m & (2**128 - 1)))


def worst_dp():
    NEG = -10**9
    dp = [NEG] * (TOTAL + 1)
    dp[0] = 0
    for k in range(NMSG):
        costs = [(OFF[k] + d, chainCost(k, OFF[k] + d)) for d in range(1 << W[k])]
        nd = [NEG] * (TOTAL + 1)
        for s, v in enumerate(dp):
            if v == NEG:
                continue
            for e, c in costs:
                if s + e <= TOTAL and v + c > nd[s + e]:
                    nd[s + e] = v + c
        dp = nd
    best = NEG
    for s, v in enumerate(dp):
        if v == NEG or TOTAL - s > CMAX or TOTAL - s < 0:
            continue
        C = TOTAL - s
        tot = v + hiCost(C // 64) + chainCost(LO, 64 + C % 64)
        best = max(best, tot)
    return best + N_CONST + 10 * NCH + 1


if __name__ == "__main__":
    random.seed(7)
    for trial in range(300):
        m = random.getrandbits(256) if trial % 3 else random.choice([0, 2**256 - 1, random.getrandbits(9)])
        E = digits(m)
        tie_check(m)
        assert sum(E[:NMSG]) + 64 * (E[HI] - 64) + E[LO] == TOTAL + 64
        assert walk(E)[:2] == (totalSteps(E), totalCost(E)), E
    for trial in range(300):
        E = [OFF[k] + random.randrange(1 << W[k]) for k in range(NMSG)] + [64 + random.randrange(HI_MAX + 1), 64 + random.randrange(64)]
        assert walk(E)[:2] == (totalSteps(E), totalCost(E)), E
    n, cost, h = walk(digits(0))
    print("layout OK; live", sum(1 for c in code if c[0] != 'pad'), "; K0 =", K0, "; tie ops", sum(tieLen(k) for k in range(NMSG)))
    print("m=0: steps", n, "blake", h, "cost", cost, "score", cost + 120)
    wc = worst_dp()
    print("exact worst over all feasible leaf vectors:", wc, "score", wc + 120)
```
