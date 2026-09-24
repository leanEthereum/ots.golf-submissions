# HL-TRI-R9: three chains per landing, nine root calls with high-half tops, 1422 cycles

Lineage: HL-FLAT-A (1598) → HL-TRI (1439, grouped dispatch) → HL-TRI-TM (1433, reused constant
cells) → HL-TRI-R9 (this root, claim 1422, nine root calls). HL-TRI-TM kept HL-FLAT-A's security
proof and changed only tag-symbol and root-metadata *values*. HL-TRI-R9 changes the scheme: a
per-chain high-half top (`Params.hiTop`, `Params.slice`) and the 9-call root (section 6); the
security proof keeps its structure. The bytecode and the machine proofs are new.

## 1. Where HL-FLAT-A's cycles were

`1598 = 308 + 10·117 + 120`. The 117 `BLAKE2S` (1 index, 106 chain steps on layer 106, 10 root
calls) are fixed by the scheme. An exhaustive search over all 689,249 digit-width mixes with
Σ widths = 128 and at most 42 chains (24 processes) confirms that 40×3 + 2×4 bits on layer 106
is optimal: no mix reaches the availability bound `200·2^108` on a lower layer. So the gain
has to come from the 308 non-hash instructions.

Of those, 42 × 7 were per-chain dispatch: a frame `SET`, `MUL(H,g,H')`, the dispatch `JUMP`,
the frame-shifted entry `I0`, the tie `SET T; XOR`, and the landing product `MUL(G, H)`.

## 2. Idea: dispatch a group of three chains per landing

- 14 groups: `(3g, 3g+1, 3g+2)` for `g < 12`, then `(36, 37, 40)` and `(38, 39, 41)`. This
  balances the two 4-bit chains so that every group fits a uniform entry spacing inside 2^18 slots.
- One frame per group (`F_g = g^((g+1)·2^33)`, 14 `SET`s instead of 42), one dispatch
  (`MUL(H_g, g, H'_g); JUMP(ONE, H_g, F_g)`) and one entry `I0_g = JUMP(ONE, H'_g, ONE)` per group.
  Entry of tuple `t` is `BASE g + SP g · rank t` (mixed radix over the group's digits).
- One tie word per group: `SET T_g := Σ s_k·2^pos_k; XOR(acc_{g−1}, T_g, acc_g)`, `acc_13 = idx`.
- The layer is checked by a product of per-group factors `g^σ` (`σ` = the group's digit sum),
  `L_13 = K0 = g^rootSlot`. Six precomputed constants `g^2..g^7` (plus `gCell = g^1`) let most
  groups use one `MUL` with no `SET`; `σ > 7` pays `SET C_g; MUL`.
- Zero digits copy the revealed word into the root's top cell (`XOR(W_k, Z, rootTop k)`), as in
  HL-FLAT-A. The contract's `steps` must not depend on the oracle's index answer, so every block
  of a group pads with `XOR(Z, Z, Z)` to the group's maximum non-hash count
  (`[6]*12 + [7, 7]` before the tail).
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
   leanVM semantics, runs 400 random layer vectors in support mode (constant 1319 / 266), rejects
   off-layer vectors, and rejects mid-block landings with adversarial cell fills.
3. A Python mirror of the Lean `cinstrAt` matched the model on all 262,144 slots (for HL-TRI-R9:
   `.tmp/hl/hltri_r9_lean_mirror.py` against `.tmp/hl/hltri_r9_model.py`, 0 mismatches).
4. Two agents: machine core (`MachineProgram` → `MachineCycles`) and machine proofs
   (`MachineSound`, `MachineProver`, `MachineHonest`, `MachineFaithful`, `Solution`).

## 5. Validation

- `lake build Submissions.UpperLeanIsa.Solution` from a clean copy of the pinned contract.
- `check_submission.py upper-leanisa`: ok, claim 1422.
- `certificate : submission.Certificate 1422` and `seeded_rows` type-check against the stub's
  statements; axioms are `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `native_decide` or `admit` in the root.

## 6. What next

- **Tag and metadata constants (done in HL-TRI-TM: 1433).** Tag symbols `{0, 1, 2, 4, 8, 16, 32}` are
  exactly the existing cells `Z, ONE, g, g^2..g^5`, and the root metadata can use
  `0, 2, 4, …, 128, 5504` plus one new constant. That removes the seven symbol `SET`s and nets −6.
  It changes only `SchemeFlat`'s `sym`/`rootMd`/`idxMd` and `FlatHyp`'s decidable facts; the
  security proof is generic in `Params`.
- **Nine root calls (done in this root: 1422).** A 128-bit chaining state in `m` absorbs five
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

## Appendix A. Layout of the model (`hltri_i0_layout.py`)

The field arithmetic, the scheme spec and the leanVM simulator are HL-FLAT-A's model (this root's
previous `NOTES.md`, Appendix A, lines up to `B'. UNI layout` and its `Machine` class). This
appendix replaces its layout and checks.

```python
# ============================================================================ HL-TRI layout
# Same scheme as HL-FLAT-A. The machine dispatches three chains per landing: one frame, one
# hinted landing, one tie word and one layer factor per group of chains.
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
C_Z, C_ONE, C_TIDX, C_G, C_K0 = 47, 48, 49, 50, 51
C_SYM = [52 + v for v in range(7)]
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
def XC(k, t): return 1024 + 32 * k + 2 * t
C_S = [2400 + 2 * r for r in range(10)]
ROOT_TOP = [C_CV, C_CV + 1] + [C_TOP[k] for k in range(2, 42)]
CHAIN_OUT = [C_TOP[0], C_CV + 1] + [C_TOP[k] for k in range(2, 42)]
RHO_CELL = [C_Z, C_G] + C_SYM + [C_LEN]
check([cellBits(v) for v in [(0,0,0), ofK(G)] + [cellOf(SYM(v)) for v in range(7)] + [cellOf(5504)]] == RHO, "rho")
ROOT_LEN = 11
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

PRO = [SET(C_Z, ZERO), SET(C_ONE, ofK(1)), SET(C_LEN, cellOf(5504)), SET(C_TIDX, cellOf(IDX_MD)),
       SET(C_G, ofK(G)), SET(C_K0, K0_VAL)]
PRO += [SET(C_SYM[v], cellOf(SYM(v))) for v in range(7)]
PRO += [SET(C_F[g], F_VAL[g]) for g in range(NG)]
PRO += [SET(C_GP[v], ofK(gpow(v))) for v in range(2, PRE_MAX + 1)]
PRO += [BLK([C_M0, C_M1, C_NONCE, C_PK], C_Z, C_IDX, C_TIDX), MUL(C_H[0], C_G, C_H1[0]),
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
        ops.append(BLK([src, C_SYM[a - 3], C_SYM[bb - 3], C_SYM[c - 3]], C_Z, dst, C_ONE))
    return ops

def tuples(g):
    ks = GROUPS[g]
    out = [()]
    for k in ks:
        out = [t + (s,) for t in out for s in range(W[k])]
    return out

def nonhash(g, tup):
    ks = GROUPS[g]
    word = sum(s << POS[k] for k, s in zip(ks, tup))
    sigma = sum(tup)
    ops = [I0(g)]
    if g == 0:
        ops.append(SET(C_ACC[0], cellOf(word)))
    elif word:
        ops += [SET(C_T[g], cellOf(word)), X_(C_ACC[g - 1], C_T[g], C_ACC[g])]
    else:
        ops.append(X_(C_ACC[g - 1], C_Z, C_ACC[g]))
    for k, s in zip(ks, tup):
        if s == 0:
            ops.append(X_(C_W[k], C_Z, ROOT_TOP[k]))
        elif k == 0:
            ops.append(X_(C_TOP[0], C_Z, C_CV))
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
    pre = [x for x in head if not (x == X_(C_TOP[0], C_Z, C_CV))]
    post = [x for x in head if x == X_(C_TOP[0], C_Z, C_CV)]
    pad = [NOP] * (NH_MAX[g] - len(head))
    steps = [b for k, s in zip(ks, tup) for b in chain_ops(k, s)]
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
    for k, s in zip(GROUPS[g], tup): r = r * W[k] + s
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
ROOT = [BLK([ROOT_TOP[2], ROOT_TOP[3], ROOT_TOP[4], ROOT_TOP[5]], C_CV, C_S[0], RHO_CELL[0])]
for r in range(1, 10):
    ROOT.append(BLK([ROOT_TOP[6 + 4 * (r - 1) + i] for i in range(4)], C_S[r - 1], C_S[r], RHO_CELL[r]))
ROOT.append(X_(C_S[9], C_Z, C_PK))
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
```

## Appendix B. Checks (`hltri2_checks.py`)

```python
# ============================================================================ HL-TRI checks
def split_groups(svec):
    return [tuple(svec[k] for k in GROUPS[g]) for g in range(NG)]

def entry_choice(svec):
    tups = split_groups(svec)
    def ch(a, ctx):
        if a in C_H:
            g = C_H.index(a)
            return ofK(gpow(ENTRY_OF[(g, tups[g])]))
        return None
    return ch

def forced_walk(svec):
    tr = list(range(PROLOGUE_LEN))
    for g, tup in enumerate(split_groups(svec)):
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
    img = {C_IDX: cellOf(sum(v[k] << POS[k] for k in range(42)))}
    mac = Machine(loader(7, 0, [0] * SIG_BITS), choose=entry_choice(v), image=img, support=True)
    mac.mem[C_S[9]] = cellOf(7)
    cost = mac.run()
    return cost, len(mac.trace), [pc for pc, _ in mac.trace] == forced_walk(v)

def offlayer_run(v, seed):
    random.seed(seed)
    img = {C_IDX: cellOf(sum(v[k] << POS[k] for k in range(42)))}
    mac = Machine(loader(1, 0, [0] * SIG_BITS), choose=entry_choice(v), image=img, support=True)
    mac.mem[C_S[9]] = cellOf(1)
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
    I = LO(H(idxQuery(m, ofBits(bits[128 * 42:]), pk)))
    s = digits(I)
    mac = Machine(loader(pk, m, bits), choose=entry_choice(s))
    cost = mac.run()
    out.append((ok, cost, len(mac.trace), [pc for pc, _ in mac.trace] == forced_walk(s)))
    for what in ('word', 'nonce', 'msg', 'pk'):
        b2, m2, pk2 = list(bits), m, pk
        if what == 'word': b2[rng.randrange(42 * 128)] ^= 1
        if what == 'nonce': b2[42 * 128 + rng.randrange(128)] ^= 1
        if what == 'msg': m2 ^= 1 << rng.randrange(256)
        if what == 'pk': pk2 ^= 1 << rng.randrange(128)
        v = verify(pk2, m2, b2)
        s2 = digits(LO(H(idxQuery(m2, ofBits(b2[128 * 42:]), pk2))))
        mac = Machine(loader(pk2, m2, b2), choose=entry_choice(s2))
        try: mac.run(); ok2 = True
        except Stop: ok2 = False
        out.append((what, ok2 == v))
    return out


def midblock_run(v, seed):
    rng = random.Random(seed)
    tups = split_groups(v)
    g = rng.randrange(NG)
    delta = rng.randrange(1, BLOCK_LEN[(g, tups[g])])
    def ch(a, ctx):
        if a in C_H:
            gg = C_H.index(a)
            e = ENTRY_OF[(gg, tups[gg])]
            return ofK(gpow(e + (delta if gg == g else 0)))
        return cellOf(rng.getrandbits(128))
    random.seed(seed)
    img = {C_IDX: cellOf(sum(v[k] << POS[k] for k in range(42)))}
    mac = Machine(loader(7, 0, [0] * SIG_BITS), choose=ch, image=img, support=True)
    mac.mem[C_S[9]] = cellOf(7)
    try:
        mac.run(); return 'completed'
    except Stop as e:
        return str(e)

if __name__ == "__main__":
    items = list(prog.items()) + [(SENT, PAD)]
    chunks = [items[i::24] for i in range(24)]
    with Pool(24) as pool:
        bad = sum(pool.map(frame_chunk, chunks))
        check(bad == 0, f"frame lemma bad={bad}")
        rng = random.Random(11)
        vecs = [layer_vector(rng) for _ in range(400)]
        z = [0] * 42; z[40] = 15; z[41] = 15; rest = 76
        for k in range(40):
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
