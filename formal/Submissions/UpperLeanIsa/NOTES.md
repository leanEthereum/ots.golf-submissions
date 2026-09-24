# Phase 1 design: RT, "Rice-tree forced dispatch"

Status: design phase. Nothing has been built. Every number below is checked by the executable
model in Appendix A, `rt_model.py`, which passes.

- Target claim: **85343** cycles. The current record is 170549 (PR #31).
- Worst case: 733 non-hash instructions plus 8449 `BLAKE2S`:
  `9182 + 9·8449 + 120 = 85343`.
- The bound is tight. The honest run on the all-zero message attains it.
- Scope: the scheme and its proofs are unchanged (`Algorithms`, `Encoding`, `Checksum`,
  `Correctness`, `Security` and its dependencies, `Wire`, `Resources`, `BasicProperties`).
  Only the bytecode and the machine proofs are replaced: `MachineProgram`, `MachineRun`,
  `MachineSound`, `MachineProver`, `MachineFaithful`, the additions to `ConstraintMath`,
  `Solution`, `claim.txt` and `README`.

---

## 0. The decision

RT is the **attack-first** design (JUMP-tree dispatch, leaf-entry chain steps), with three
changes grafted on:

1. **Every `JUMP` target is a `SET_CONSTANT` executed in the slot immediately before the
   `JUMP`.** This includes `c_hi`. Attack-first's hinted `D32` is removed, and with it the
   eight squarings, the `DEREF` entry binding, the negative-offset trick and the look-ahead
   landing lemma. The program uses only `XOR`, `MUL`, `SET`, `BLAKE2S` and `JUMP`. There is no
   `DEREF` and no hint-controlled jump target, and no landing argument depends on facts from
   earlier chains.
2. **Rice(r=2) prefix trees replace the balanced depth-8 trees** for the 33 chains
   0..31 and 33. A leaf `e` is reached through a unary chain on `q = ⌊e/4⌋`, then a 2-level
   binary subtree on `e mod 4`. The dispatch depth is `⌊e/4⌋ + 3` nodes. The reason this
   helps: the worst case forces `c_hi = 31`, and then the other 33 digits sum to exactly 224
   (§5). The dispatch cost at the worst case drops from 528 to 310.
3. **`c_hi` gets a unary tree ordered 31, 30, …, 0.** At the worst case (`c_hi = 31`) its
   dispatch is a single node, 2 cycles.

Kept from attack-first:

- Each leaf hashes its chain's first step straight from the pinned `σ` cell, so no entry
  binding is needed.
- The message tie is the XOR-accumulated byte words `vV(p, e)` written into the pinned
  message cells. This is the baseline's link argument unchanged.
- The checksum is checked in the exponent, as a product of leaf landing constants.
- The pinned zero cells 38 and 39 are used once the length is checked.
- The halt is a fall-through into the sentinel.

| design | claim | status |
|---|---:|---|
| **RT (this document)** | **85343** | chosen |
| RT + Phase-1b micro-optimisations (§10.3) | 85341 | optional follow-up |
| attack-first as reviewed | 85566 | sound after fixes; the base of RT |
| refine-A (A*) / A+ | 85933 / 85924 | sound after fixes; rejected |
| proof-first | 86882 | sound after its aliasing fix; rejected |
| baseline (PR #31) | 170549 | current record |

---

## 1. Fixed inputs the bytecode must match

These facts are re-derived from `Algorithms.lean`, `Encoding.lean`, `Checksum.lean` and
`ConstraintMath.lean`.

- **Chain step.** `chainInput i j x = hashInput 0 (0 ++ ofNat j ++ ofNat i ++ x) 1`. It is the
  `BLAKE2S` with m = `[x, I_i, J_j, 0]`, cv = `(0,0)` and md = `1`, where `I_i` and `J_j` are
  cells with `cellBits = ofNat 128 i` and `ofNat 128 j` (`blake2sQuery_chain`). The next
  word is the low 128 bits of the answer.
- **Root.** `absorb r cv x = hash (hashInput cv (x.setWidth 512) (ofNat 128 (2 + r)))`,
  where `r` is the number of words still to absorb. So absorption `t` (0-based) uses
  md = `2 + (33 − t) = 35 − t`, m = `[x, 0, 0, 0]` and cv = the full 256-bit state as a pair
  (low cell first). The initial state is `0`, and pk is the low 128 bits of the final state
  (`blake2sQuery_absorb`, `root_sound`).
- **Verify.** It checks `|bits| = 4352` and `xs = decode bits`. The endpoint of chain `i` is
  `chain i (digit m i) (255 − digit m i) (xs i)`.
- **Digits.**
  - For `i < 32`, `digit m i` is byte `31 − i` of `m.toNat` (`digit_of_lt`).
  - For `16 ≤ i < 32` it is in-cell byte `31 − i` of cell 1; for `i < 16` it is in-cell byte
    `15 − i` of cell 2 (`digit_cell1`, `digit_cell2`).
  - `digit 32 = C / 256` and `digit 33 = C % 256`, where
    `C = Σ_{i<32} (255 − digit i) ≤ 8160` (`digit_hi_checksum`, `digit_lo_checksum`,
    `checksum_eq_sum`, `wotsChecksum_le`).
- **Loader.**
  - Cell 0 holds pk; cells 1 and 2 hold message bits 0..127 and 128..255.
  - Cell 3 holds `cellOfBits (ofNat 128 (min |σ| 5505))`.
  - Cells `4 + i` hold the signature words (`inputWord_decode`, when `|σ| = 4352`).
  - With `|σ| = 4352` the statement is `4864 = 38·128` bits, so cells 38..46 hold
    `cellOfBits (ofBits 128 []) = 0`. This needs a new lemma, `inputWord_pad_zero`.

## 2. Machine facts used

The contract is `LeanIsaMachine.lean`, `LeanIsa.lean` and leanerVM `Step`/`Execution`/`Memory`/
`Instruction`.

- `runCost prog L (n+1) r` fails (`none`) when `r.pc = finalPc`. Otherwise it fetches, executes
  and recurses. `runCost 0 r = some 0` exactly when `r.pc = finalPc ∧ r.fp = 1`. So a
  completing run reaches the sentinel after exactly `n` steps and never executes it.
- `JUMP a b c` reads the three cells fp-relatively and guards `IsInK` on all three.
  - If `[a] = 0` the successor is `(g·pc, fp)`.
  - Otherwise it is `([b].limb 0, [c].limb 0)`.
- `SET o k` asserts `[o] = k`. `XOR` and `MUL` assert `c = a + b` and `c = a·b` in `E`.
  `BLAKE2S` asserts the oracle relation (under `support`, any answer).
- Every instruction except a taken `JUMP` goes to `g·pc`.
- `Instr.xor 0 0 0` always fails, because it reads address `1·0 = 0` (`MemImage.read_zero`).
  RT uses it as the trap in every unused slot.
- `Program.fetch (gpow i) = code i` for `i < 2^logSize`. `finalPc = gpow (2^logSize − 1)`.
  `gpow` is injective below `2^64 − 1` (`gpow_injOn`).
- The score is weighted instructions plus 120, with `BLAKE2S` weighing 10 and everything
  else 1. It is taken over **all** completing runs: every image, every `κ ∈ [16,32]`, every
  step count, and incoherent oracle paths (`support`, no cache).

---

## 3. Memory layout (fp = 1 throughout; cell `c` ↔ address `gpow c`; memLog = 16)

| cells | contents | pinned by |
|---|---|---|
| 0 | pk | loader |
| 1, 2 | message halves; they are also the two tie accumulators' final cells (`accCell 31 = 1`, `accCell 15 = 2`) | loader |
| 3 | length | loader; checked by `SET` at slot 256 |
| 4 + k (k < 34) | `σ_k` = `sigCell k` | loader |
| 38 | `zCell` = Z. It is 0 once `|σ| = 4352`. Z doubles as `posCell 0` (chain id 0 and position 0), the zero message word, and the zero pair `(38, 39)` | loader + len |
| 101..355 | `posCell j = 100 + j` for `1 ≤ j ≤ 255`, holding `posV j = cellOfBits (ofNat 128 j)`. `oneCell = posCell 1 = 101`. These cells also serve as chain ids 1..33 and root metadata 2..35 | slots 0..254 |
| 400 | `k0Cell`, holding `tgtV K0` | slot 255 |
| `scr k = 1024 + 160k` (k ≤ 33) | per-chain scratch, layout below | hints |
| 7000 + 2t, 7001 + 2t (1 ≤ t ≤ 34) | root state pair `S_t`. `S_0` is the pair `(38, 39)` | `BLAKE2S` |
| `xCell k j = 8192 + 512k + 2j` (j ≤ 255) | chain word `x_{k,j}`. Step `j` writes the pair `(xCell k (j+1), xCell k (j+1) + 1)`, whose high cell is `h_{k,j}`. `xCell k 0` is unused | `BLAKE2S` / `XOR` |

Per-chain scratch cells, all relative to `scr k`:

| offset | cell | meaning |
|---|---|---|
| i (i < 63) | `zuCell k i` | condition hint of unary node `i` |
| 64 + i | `tuCell k i` | target of unary node `i` |
| 128 + j (j < 2) | `zbCell k j` | condition hint of group depth `j` (shared by all groups and blocks) |
| 130 + j | `tbCell k j` | target of group depth `j` |
| 132 | `tCell k` | `T_k`: the checksum contribution, and also the jump cell when `e < 255` |
| 133 | `vCell k` | `V_k`: the jump cell when `e = 255` |
| 134 | `gCell k` | `G_k`: the running checksum product |
| 135 | `fCell k` | `F_k`: the leaf's tie term |
| 136 | `accCell k` | the tie accumulator. For `k = 15` it is cell 2 and for `k = 31` it is cell 1, as noted above |
| `scr 32 + 137 = 6281` | `uCell` | `g^(256·c_hi)` |

- The highest cell is `xCell 33 255 + 1 = 25599 < 2^16`.
- All the families are pairwise disjoint and ≥ 47; the model checks this.
- On every legal path, each output cell (the target of a `SET`, the `c` of an `XOR`/`MUL`, a
  `BLAKE2S` output pair) is defined by exactly one instruction. The one exception is
  `k0Cell`, which is defined by `SET` and by the chain-33 `MUL`, and that is the checksum
  equation itself.

Values:

- `posV j := cellOfBits (ofNat 128 j)`.
- `oneV := E.ofLimbs 1 0 0`, which equals `posV 1` and `ofK 1` (baseline `oneV_eq_cellOfBits`,
  `oneV_eq_ofK`).
- `lenV := cellOfBits (ofNat 128 4352)`.
- `tgtV t := ofK (gpow t)`.
- `vV p e := cellOfBits (ofNat 128 (e <<< 8p))` (baseline `MachineProver.vV`).
- `bytePos k := (31 − k) % 16`.
- `K0 := Σ_{k<32} (s0 k + 1) + (s0 33 + 1) + 8160 = 1826526`.

Accumulator and product helpers:

- `accPrev k`: for `k % 16 = 0` there is none (the tie term alone). Otherwise it is
  `accCell (k−1)`.
- `gPrev k := if k = 0 then oneCell else if k = 33 then gCell 32 else gCell (k−1)`.
- `gOut k := if k = 33 then k0Cell else gCell k`.

---

## 4. Bytecode layout (logSize = 17, 131072 slots, sentinel 131071)

`CInstr` gains one constructor, `.pad`:

- It lowers to `Instr.xor 0 0 0`.
- Its cost is 1, it is not a jump, and `Bounded` holds trivially.
- Its `Rel`, `CRel` and `RelNH` are all `False`. It is the trap.

The other constructors are the baseline's. `.blake m0 m1 m2 m3 cv out md` reads
`m0..m3, cv, cv+1, md` and constrains `out, out+1`. There is **no** `.deref`.

### 4.1 Segment map

| slots | segment |
|---|---|
| `[0, 255)` | `s ↦ SET posCell (s+1) := posV (s+1)` |
| 255 | `SET k0Cell := tgtV K0` |
| 256 | `SET lenCell (=3) := lenV` |
| `[rBase k, rBase k + 3196)` for `k < 32`, with `rBase k = 257 + 3196k` | chain k: Rice dispatch `[rBase k, rBase k + 2942)`, then body steps `j = 1..254` at `s0 k + j`, where `s0 k = rBase k + 2941` |
| `[102529, 103005)` | chain 32 (`c_hi`): unary dispatch `[102529, 102751)`, then body at `s0 32 + j`, where `s0 32 = 102750` |
| `[103005, 105947)` | chain 33 (`c_lo`) Rice dispatch, with `rBase 33 = 103005` |
| `[105947, 130782)` | gap: `.pad`. This includes `s0 33 = 130781`, which is never executed |
| `[130782, 131036)` | chain 33 body: step `j` at `s0 33 + j`, `j = 1..254` |
| `[131036, 131070)` | root absorption `t` at `rootBase + t`, where `rootBase = 131036` |
| 131070 | `XOR (S_34 low) Z → pkCell 0`, the pk check. It falls through into the sentinel |
| 131071 | sentinel: `.pad` (not a `JUMP`, so `BytecodeValid` holds) |

- `rBase 32 = 102529` and `rBase 33 = 103005`. For `k ≤ 32`, `s0 k + 255 = rBase (k+1)`, and
  `s0 33 + 255 = rootBase`.
- There are 75165 live slots, and every other slot is `.pad`.
- `seededRows = 2^17 + 2^16 = 196608 < 2^20`.

### 4.2 Rice dispatch of chain k ∈ {0..31, 33} (base R = rBase k, 2942 slots)

**Unary node i**, for `i < 63`, occupies the two slots at `R + 46i`:

```
R + 46i     : SET  tuCell k i := tgtV (R + 46(i+1))
R + 46i + 1 : JUMP (zuCell k i, tuCell k i, oneCell)
```

- Taken (`z ≠ 0`): the next unary node, or group 63 when `i = 62`. Both are at
  `R + 46(i+1)`, the same formula.
- Not taken: `R + 46i + 2 = gBase k i`, the entry of group i.

**Group q.**

- Base: `gBase k q = R + 46q + 2` for `q < 63`, and `gBase k 63 = R + 2898`.
- Size: 44 slots, as 4 blocks `b = 0..3` of width 11 at `gBase k q + 11b`.

```
gB      : SET  tbCell k 0 := tgtV (gB + 24)                 -- node (0,0)
gB + 1  : JUMP (zbCell k 0, tbCell k 0, oneCell)             -- taken → node (1,2); fall → node (1,0)
gB+11b+2: SET  tbCell k 1 := tgtV (gB + 11(b+1) + 4)        -- node (1,b), b ∈ {0,2}
gB+11b+3: JUMP (zbCell k 1, tbCell k 1, oneCell)             -- taken → leaf 4q+b+1; fall → leaf 4q+b
gB+11b+4+i (i < 7): leaf 4q+b, op i                          -- leafSlot k e = gBase k (e/4) + 11(e%4) + 4
```

Node slots that do not exist in a block are `.pad`: offsets 0..3 of blocks 1 and 3, and
offsets 0..1 of block 2. So are leaf offsets past the leaf's length.

**Path to leaf e = 4q + b.**

1. Unary nodes `0..q−1` are taken and node `q` is not. When `q = 63`, all 63 nodes are taken.
2. Then node (0,0), which is taken iff `b ≥ 2`.
3. Then node `(1, 2⌊b/2⌋)`, which is taken iff `b` is odd.

The number of nodes on the path is `riceDepth e := if e/4 < 63 then e/4 + 3 else 65`. Each
node costs 2 cycles and 2 steps.

### 4.3 Leaves of chain k ∈ {0..31, 33}

`tieOps k e`. This is empty for `k = 33`.

| k | ops |
|---|---|
| `k % 16 = 0` (k = 0, 16) | `SET accCell k := vV (bytePos k) e` |
| `k % 16 = 15` (k = 15, 31) | `XOR (accCell (k−1), posCell e) → accCell k` (bytePos is 0, so `vV 0 e = posV e`) |
| other k < 32 | `SET fCell k := vV (bytePos k) e`, then `XOR (accCell (k−1), fCell k) → accCell k` |

`coreOps k e`. The slot immediately before every `JUMP` sets its target cell.

```
e < 255:  BLAKE2S (sigCell k, posCell k, posCell e, Z; cv Z; out xCell k (e+1); md oneCell)
          MUL (gPrev k, tCell k) → gOut k
          SET tCell k := tgtV (s0 k + e + 1)
          JUMP (oneCell, tCell k, oneCell)                -- → body step e+1, or s0 k + 255 when e = 254
e = 255:  XOR (sigCell k, Z) → xCell k 255               -- the endpoint is σ
          SET tCell k := tgtV (s0 k + 256)                 -- the checksum contribution stays uniform
          MUL (gPrev k, tCell k) → gOut k
          SET vCell k := tgtV (s0 k + 255)
          JUMP (oneCell, vCell k, oneCell)                -- → s0 k + 255 = next segment
```

- `leafOps k e = tieOps k e ++ coreOps k e`. Its length is
  `leafLen k e = tieLen k + (e < 255 ? 4 : 5)`, which is at most 7 and so fits the block.
- `tieLen k = 0` for `k ≥ 32`, `1` if `k % 16 ∈ {0, 15}`, and `2` otherwise. So
  `Σ_{k<32} tieLen k = 60`.
- The leaf's non-dispatch cost is `leafCost k e = tieLen k + (e < 255 ? 13 : 5)`.

### 4.4 Chain 32 (`c_hi`), base R = 102529, 222 slots

```
R + 7i     : SET  tuCell 32 i := tgtV (R + 7(i+1))     -- i < 31
R + 7i + 1 : JUMP (zuCell 32 i, tuCell 32 i, oneCell)  -- taken → next node, or leaf 0 at R+217; fall → leaf 31−i
leafSlot32 c = if c ≥ 1 then R + 7(31−c) + 2 else R + 217
leaf c (5 ops):
  BLAKE2S (sigCell 32, posCell 32, posCell c, Z; cv Z; out xCell 32 (c+1); md oneCell)
  SET uCell := tgtV (256·c)
  MUL (gCell 31, uCell) → gCell 32
  SET tCell 32 := tgtV (s0 32 + c + 1)
  JUMP (oneCell, tCell 32, oneCell)                        -- → body step c+1 (c ≤ 31)
```

The dispatch depth is `u32Depth c := if c = 0 then 31 else 32 − c`.

### 4.5 Body, root, pk

```
bodyInstr k j (1 ≤ j ≤ 254), at s0 k + j:
   BLAKE2S (xCell k j, posCell k, posCell j, Z; cv Z; out xCell k (j+1); md oneCell)
rootInstr t (t < 34), at 131036 + t:
   BLAKE2S (xCell t 255, Z, Z, Z; cv rootStateCell t; out rootStateCell (t+1); md posCell (35−t))
pkInstr, at 131070:  XOR (rootStateCell 34, Z) → 0
```

### 4.6 `cinstrAt` decoding (all arithmetic, omega-friendly)

```
cinstrAt s :=
  if s < 257 then constInstr s
  else if s < 102529 then chainInstr ((s−257)/3196) ((s−257)%3196)     -- k < 32
  else if s < 103005 then c32Instr (s − 102529)
  else if s < 105947 then riceInstr 33 (s − 103005)
  else if s < 130782 then .pad
  else if s < 131036 then bodyInstr 33 (s − 130781)
  else if s < 131070 then rootInstr (s − 131036)
  else if s = 131070 then pkInstr else .pad
chainInstr k o := if o < 2942 then riceInstr k o else bodyInstr k (o − 2941)
riceInstr k o  := if o < 2898 then
                    (if o%46 = 0 then SET tu… else if o%46 = 1 then JUMP zu… else groupInstr k (o/46) (o%46 − 2))
                  else groupInstr k 63 (o − 2898)
groupInstr k q t := let b := t/11; r := t%11; if r < 4 then groupNode k q b r else leafOp k (4q+b) (r−4)
c32Instr o := if o < 222 then (if o < 217 then (o%7 = 0: SET, o%7 = 1: JUMP, else leaf32Op (31 − o/7) (o%7 − 2))
                                else leaf32Op 0 (o − 217))
              else bodyInstr 32 (o − 221)
leafOp k e i := if i < tieLen k then tieOp k e i else coreOp k e (i − tieLen k)   -- .pad past the end
program.code i := (cinstrAt i).toInstr
```

`s0 k` itself decodes as a dispatch or leaf slot: for `k < 32` it is leaf 255's op 6 or a pad,
and for `k = 32` it is leaf 0's `JUMP`. The body is only ever entered at `j ≥ 1`.

---

## 5. Cost: exact formulas, the worst case, tightness

Let `E k` be the leaf a run reaches in chain `k`. Then `E k < 256` for `k ≠ 32` and
`E 32 < 32`. Write `bodyLen e := 254 − e`, using ℕ subtraction, so it is 0 for `e ≥ 254`.

```
chainSteps k e = 2·riceDepth e + leafLen k e + bodyLen e
chainCost  k e = 2·riceDepth e + leafCost k e + 10·bodyLen e
c32Steps c     = 2·u32Depth c + 5 + (254 − c)
c32Cost  c     = 2·u32Depth c + 14 + 10·(254 − c)
totalSteps E   = 257 + Σ_{k<32} chainSteps k (E k) + c32Steps (E 32) + chainSteps 33 (E 33) + 35
totalCost  E   = 257 + Σ_{k<32} chainCost k (E k)  + c32Cost (E 32)  + chainCost 33 (E 33)  + 341
```

The model checks these closed forms against simulated runs on 500 random leaf vectors, all
of which match.

**Checksum identity.** Section 6 shows that every completing run satisfies
`Σ_{k<32} E k + 256·E 32 + E 33 = 8160`, and that this identity comes from non-hash relations
only.

**Bound.** The proof uses three per-chain facts, each checked for every value:

- `2·chainCost k e + 19e ≤ 5118 + 2·tieLen k` for `e < 256`. Equality holds at `e = 0`.
  At `e = 255` the left side is `5115 + 2·tieLen`, so the `e = 255` extras are absorbed.
- `c32Cost c + 12c ≤ 2618` for `c < 32`. Equality holds at `c = 31`.
- `4·riceDepth e ≤ 12 + e`.

Summing the first fact over the 33 Rice chains, adding `2·598` for the constants, root and pk,
and substituting `Σ E = 8160 − 256c` gives:

```
2·totalCost E ≤ 1196 + (33·5118 + 120 − 19(8160 − 256c)) + (5236 − 24c) = 20406 + 4840c ≤ 170446
```

So `totalCost E ≤ 85223`, and the claim is `120 + 85223 = 85343`.

**Tightness.** Take `m = 0`: every digit is 0, `C = 8160`, `c_hi = 31` and `c_lo = 224`.
The walk then has 9182 steps, 8449 of them `BLAKE2S`, and costs
`9182 + 9·8449 = 85223` (model output). More generally, the exact dynamic program over all
`(E, c)` satisfying the checksum identity gives a maximum of 85223, reached at `c = 31`.

Where the 733 non-hash cycles go at the worst case:

| item | cycles |
|---|---:|
| constants | 257 |
| Rice dispatch (`2·(99 + 224/4)`) | 310 |
| `c_hi` dispatch | 2 |
| 32 message leaves (`MUL`, `SET`, `JUMP`) | 96 |
| tie | 60 |
| `c_lo` leaf | 3 |
| `c_hi` leaf | 4 |
| pk | 1 |
| **total** | **733** |

For comparison, attack-first spends 528 on balanced trees and 11 on `c_hi`.

---

## 6. Soundness (any κ ∈ [16,32], any image, any n; fixed table f)

`probTrue_zero_of_fixed` is used as in the baseline. It reduces `Sound` to this: under every
fixed table `f`, a completing simulated run on `loadInput pk m σ L` implies that
`|σ| = 4352 ∧ rootValue f (reconstructedWords f m σ) = pk`. Memory is immutable, so the
order in which relations are asserted is irrelevant.

1. **fp and ONE.**
   - The run starts at `(gpow 0, 1)`. Slot 0 is `SET posCell 1 := posV 1 = oneV`, so a
     completing run gives `Lx L oneCell = oneV`.
   - Every `JUMP` in the program has f-operand `oneCell`. This is a program lemma. So every
     taken `JUMP` sets `fp := oneV.limb 0 = 1`, fp is 1 at every state, and operand `op c`
     always names cell `c`.
2. **Walk.** The run is a `Walk (Holds f L)`: a slot sequence with all relations holding,
   ending at the sentinel (§9.2, `walk_of_sim`).
3. **Shape.** Every `JUMP` is preceded by the `SET` of its target cell, and that `SET` is on
   the path, since no jump target is a `JUMP` slot. So every taken jump lands on a bytecode
   constant. The layout makes every such constant, and every fall-through, one of the
   following:
   - the next node;
   - a group entry;
   - a leaf start;
   - a body step `≥ 1`;
   - the next segment.

   Every target is strictly forward, and pads trap. Leaf `JUMP`s have condition `oneCell ≠ 0`,
   so they are always taken. Hence the walk is exactly:
   - the constants;
   - for each `k < 32`: dispatch `k`, leaf `E k`, body steps `E k + 1..254`;
   - chain 32's unary dispatch, leaf `E 32`, body;
   - chain 33's dispatch, leaf `E 33`, body;
   - the root, then pk.

   Here `E k < 256` and `E 32 < 32`. The leaf index is fixed by the `z` hints, and nothing
   else is free.
4. **Constants.**
   - `posCell j = posV j` for `1 ≤ j ≤ 255`, and `k0Cell = tgtV K0`.
   - `cell 3 = lenV`, so `|σ| = 4352` (`length_of_inputWord_three`), so cells 38 and 39 are 0
     (`inputWord_pad_zero`).
   - Hence `Z = posCell 0 = 0` and the zero pair is `(0, 0)`.
5. **Tie.**
   - The leaf's tie ops give
     `accCell k = [k%16 ≠ 0]·accCell (k−1) + vV (bytePos k) (E k)` for `k < 32`.
   - Induction then gives `cell 2 = Σ_{k<16} vV (bytePos k) (E k)` and
     `cell 1 = Σ_{16≤k<32} vV (bytePos k) (E k)`.
   - Reindex by `b = bytePos k`. This gives `k = 15 − b` for cell 2 and `k = 31 − b` for
     cell 1, which is the baseline `linkChain`.
   - Then `pack_sum_eq`, `byte_of_pack`, `digit_cell1`, `digit_cell2` and the pinned cells 1
     and 2 give `E k = digit m k` for all `k < 32`. This is the baseline `hhalf`/`hdig`
     block, reused with `dd := E`.
6. **Checksum.**
   - The leaf relations give:
     - `T_k = tgtV (s0 k + E k + 1)` for `k ≠ 32`;
     - `G_0 = oneV·T_0`, and `G_k = G_{k−1}·T_k`;
     - `U = tgtV (256·E 32)`, and `G_32 = G_31·U`;
     - `k0Cell = G_32·T_33`, and also `k0Cell = tgtV K0`.
   - With `ofK_mul` and `gpow_mul_gpow`: `ofK (gpow A) = ofK (gpow K0)`, where
     `A = Σ_{k<32}(s0 k + E k + 1) + 256·E 32 + s0 33 + E 33 + 1 ≤ 1834717 < 2^64 − 1`.
   - `ofK_injective` and `gpow_injOn` give `A = K0`, that is,
     `Σ_{k<32} E k + 256·E 32 + E 33 = 8160`.
   - With `E k = digit k` and `C = Σ (255 − digit k) = 8160 − Σ digit k`, this becomes
     `256·E 32 + E 33 = C`. Since `E 33 ≤ 255`, `E 32 = C/256 = digit 32` and
     `E 33 = C%256 = digit 33`.

   This step uses no hash and no tie. The cycle bound (§8) reuses it verbatim.
7. **Chains.** Fix `k` and put `e = E k = digit m k`.
   - If `e < 255`: the leaf's `BLAKE2S` holds under `f`. `blake2sQuery_chain` needs
     `cellBits (posCell k) = ofNat k`, `cellBits (posCell e) = ofNat e`, `cellBits Z = 0`
     (twice, for the cv pair) and `cellBits oneCell = 1`. It then gives
     `cellBits x_{k,e+1} = low (f (chainInput k e (cellBits σ_k)))`. Body steps
     `j ∈ [e+1, 254]` give the same relation from `x_{k,j}`. The new `chain_from` then gives
     `cellBits x_{k,255} = chainValue f k e (255 − e) (cellBits σ_k)`.
   - If `e = 255`: the `XOR` gives `x_{k,255} = σ_k = chainValue … 0 …`.
   - In both cases `cellBits σ_k = decode σ k` (`inputWord_decode`), so
     `x_{k,255} = reconstructedWords f m σ k`.
8. **Root and pk.**
   - `root_sound` is used unchanged, with `endCell k := xCell k 255`, `S_0 = (Z, Z+1)` and
     md `posCell (35 − t) = cellOfBits (ofNat (2 + (33 − t)))`.
   - The pk `XOR` gives `pk = cellBits S_34.lo = rootValue f (…)`, which verify accepts
     (`fixed_verify`).

Hint inventory. Every cell above 47 that the path reads is pinned by a non-hash relation, is
a `BLAKE2S` output, or is a free hint whose only role is to choose a branch:

- **Free branch hints:** `zuCell`, `zbCell`, and `zuCell 32 ·`. Each may take any value in K;
  a value outside K fails the `JUMP` guard. Each only selects a leaf, and the tie and
  checksum then force that leaf to be the true digit.
- **Branch targets** (`tuCell`, `tbCell`, `tCell`, `vCell`, `uCell`): each is `SET` on the path.
- **Tie and products** (`fCell`, `accCell`, `gCell`): XOR, MUL or SET outputs.
- **Chain words, highs and root states** (`xCell`, `h`, root states): `BLAKE2S` outputs, or
  `XOR`-bound to σ.
- **Skipped cells:** `x_{k,j}` for `j ≤ E k`, and the cells of unvisited leaves, are never read.

## 7. Faithfulness (honest image)

- **Prover.** Reuse the baseline machinery verbatim:
  - `CA ← tabulate (chainAnswers i (digit m i) (decode σ i))`, which queries positions
    `0..254`; positions below the digit are harmless dummies under a fixed table;
  - `RA ← rootAnswers (endsOf m σ CA)`;
  - `imageOf`, with the new layout;
  - `fixed_prover` as in the baseline.
- **Steps.** `steps pk m σ := totalSteps (dig m)`. It depends on `m` only.
- **Honest cell values** (`d = dig m`, `q_k = d_k / 4`, `b_k = d_k % 4`, `c = d_32`):
  - `posCell j ↦ posV j`; `k0Cell ↦ tgtV K0`.
  - **Unary hints and targets.**
    - `zuCell k i ↦ if i < q_k then oneV else 0`.
    - `zuCell 32 i ↦ if i < 31 − c then oneV else 0`.
    - `tuCell k i ↦ tgtV (rBase k + 46(i+1))`, and `tuCell 32 i ↦ tgtV (rBase 32 + 7(i+1))`.
      All of these are set, which is harmless off the path.
  - **Group hints and targets.**
    - `zbCell k 0 ↦ [b_k ≥ 2]`, `zbCell k 1 ↦ [b_k odd]`, as `oneV` or `0`.
    - `tbCell k 0 ↦ tgtV (gBase k q_k + 24)`.
    - `tbCell k 1 ↦ tgtV (gBase k q_k + 11(2⌊b_k/2⌋ + 1) + 4)`.
  - **Leaf cells.**
    - `fCell k ↦ vV (bytePos k) d_k`.
    - `accCell k ↦` the partial sum over the half, up to and including `k`. Cells 1 and 2
      are pinned and equal the full sums, by the baseline `linkAccV_lo`/`linkAccV_hi`
      argument and `pack_sum_of_bytes`.
    - `tCell k ↦ tgtV (s0 k + d_k + 1)`, `vCell k ↦ tgtV (s0 k + 255)`, and
      `uCell ↦ tgtV (256c)`.
    - `gCell k ↦ tgtV (Σ_{i≤k} (s0 i + d_i + 1))` for `k < 32`, and
      `gCell 32 ↦ tgtV (Σ_{i<32}(s0 i + d_i + 1) + 256c)`.
  - **Chain words.** `xCell k j ↦ cellOfBits (inW d_k σ_k A_k j)` (baseline `inW`: σ for
    `j ≤ d`, the chain value after that), and `h_{k,j} ↦ highE A_k j`.
  - **Root states:** as in the baseline (`rootStF`).
- **Accept direction.** When verify accepts, every relation on the path for `E = dig m` holds:
  - the checksum holds by the honest identity `Σ d + 256(C/256) + C%256 = 8160`;
  - the tie holds by `pack_sum_of_bytes`;
  - the chains hold by `chainAnsF_spec` and `inW`;
  - the root and pk hold as in the baseline.

  The z hints select exactly leaf `d_k`. So `walk_full_mk` builds the `Walk`, and
  `sim_of_walk` gives `runCost (totalSteps d) = pure (some (totalCost d))`.
- **Reject direction.** If the honest run completes, `fixed_sound` applies, as in the
  baseline's `faithful`.

## 8. Cycle bound (`CyclesAtMost 85343`)

1. Take `some cost ∈ support (S.exec L n pk m σ)`. The first step gives
   `Lx L oneCell = oneV`.
2. `walk_of_supp` makes the run a `Walk (HoldsNH L)`. `HoldsNH` is the relation with
   `BLAKE2S ↦ True`: under `support`, a `BLAKE2S` step either fails or advances to `g·pc`,
   whatever the answer.
3. `walk_full` with `R := HoldsNH` gives the shape, `n = totalSteps E` and
   `cost = totalCost E`. It also gives the non-hash relations of the constants and leaves.
4. §6 step 6 gives the checksum identity. It uses no hash and no tie.
5. `totalCost_le` (§5) gives `120 + cost ≤ 85343`.

This holds for every `κ`, every image, every `n` and every statement, including incoherent
answer paths. The reasons:

- no jump condition, jump target or fp is ever a `BLAKE2S` output;
- every target is strictly forward, so there are no loops and nothing advances fp;
- the step count is a function of `E` alone.

---

## 9. Lean proof plan

### 9.1 `MachineProgram.lean` (rewrite)

- **Keep:** `op`, `g_mul_op`, `gpow_zero`, `g_mul_gpow`, `CInstr` (add `.pad`), `toInstr`,
  `Bounded`, `cost`, `isJump`, `weight_toInstr`, `oneV` and its lemmas, `lenV`.
- **Cells, values and layout constants** from §3 and §4: `posCell`, `oneCell`, `k0Cell`,
  `scr`, `zuCell`, `tuCell`, `zbCell`, `tbCell`, `tCell`, `vCell`, `gCell`, `fCell`, `accCell`,
  `uCell`, `gPrev`, `gOut`, `rootStateCell`, `xCell`, `sigCell`, `bytePos`, `posV`, `tgtV`,
  `vV` (move it here from `MachineProver`), `rBase`, `s0`, `gBase`, `leafSlot`, `leafSlot32`,
  `rootBase = 131036`, `pkSlot = 131070`, `sentinel = 131071`,
  `K0 := Σ … + 8160`, `K0_eq : K0 = 1826526`.
- **Builders:** `constInstr`, `riceInstr`, `groupInstr`, `groupNode`, `tieLen`, `tieOp`,
  `coreOp`, `leafOp`, `leaf32Op`, `c32Instr`, `chainInstr`, `bodyInstr`, `rootInstr`,
  `pkInstr`, `cinstrAt`, and `program` (logSize 17, `code i := (cinstrAt i).toInstr`).
- **Global facts:**
  - `valid`: `logSize 17 ≤ 18`, and the sentinel decodes to `.pad` (opcode xor).
  - `seeded : 2^17 + 2^16 < maxSeededRows`.
  - `fetch_eq (k < 2^17)`.
  - `gpow_ne_finalPc (k < 131071)`.
  - `cinstrAt_bounded : (cinstrAt s).Bounded (2^16)`.
  - `jump_f : cinstrAt s = .jump a b c → c = oneCell`.
  - `jump_prev : cinstrAt s = .jump a b c → ∃ t < 131071, cinstrAt (s−1) = .setc b (tgtV t)`.
    This one is optional; the path lemmas below state it per site.
- **Decode lemmas,** each by `unfold cinstrAt` plus `omega` and heartbeat bumps as needed:
  - `cinstrAt_const (s<255)`, `cinstrAt_k0`, `cinstrAt_len`;
  - `cinstrAt_uset`, `cinstrAt_ujmp` (`k ∈ rice`, `i < 63`);
  - `cinstrAt_g0set`, `cinstrAt_g0jmp`, `cinstrAt_g1set`, `cinstrAt_g1jmp` (`b ∈ {0,2}`);
  - `cinstrAt_leaf (e < 256, i < leafLen k e) : cinstrAt (leafSlot k e + i) = leafOp k e i`;
  - `cinstrAt_u32set`, `cinstrAt_u32jmp` (`i < 31`), `cinstrAt_leaf32 (c < 32, i < 5)`;
  - `cinstrAt_body (k < 34, 1 ≤ j ≤ 254)`;
  - `cinstrAt_root (t < 34)`, `cinstrAt_pk`.
- **Per-op shape lemmas:** `leafOp` at each index (by `rcases` on the tie class and `e < 255`),
  `isJump` and `cost` of each.

### 9.2 `MachineRun.lean` (rewrite)

Keep the whole "reading cells", `optGuard`, pure-exec and `BLAKE2S`-tail toolkit:

- `Lx`, `read_op_*`, `optGuard*`;
- `exec_xor_iff`, `exec_mul_iff`, `exec_set_iff`, `exec_*_next`;
- `blakeReads*`, `sim_blakeTail`, `supp_blakeTail`;
- `CInstr.Rel` (add `.pad ↦ False`), `Holds`;
- `sim_exec_pos`, `sim_exec_supp`, `supp_exec_next` (add the `.pad` arm: `execute = none`);
- `initial_eq`, `next_gpow`, `runCost_succ_of`, `runCost_final_*`.

New definitions:

```lean
def RelNH (L) : CInstr → Prop        -- Rel with .blake ↦ True, .pad ↦ False (f-free)
def HoldsNH (L) (s : ℕ) : Prop := (cinstrAt s).RelNH L
noncomputable def slotOf (pc : K) : ℕ :=
  if h : ∃ i, i < 2^17 ∧ pc = gpow i then Classical.choose h else 2^17
noncomputable def nextSlot (L) (s : ℕ) : ℕ :=
  match cinstrAt s with
  | .jump a b _ => if Lx L a = 0 then s + 1 else slotOf ((Lx L b).limb 0)
  | _ => s + 1
inductive Walk (R : ℕ → Prop) (L : MemImage κ) : ℕ → ℕ → ℕ → Prop   -- steps, start slot, cost
  | done : Walk R L 0 sentinel 0
  | step : s < sentinel → R s → Walk R L n (nextSlot L s) c → Walk R L (n+1) s ((cinstrAt s).cost + c)
```

New execution lemmas:

- `exec_jump_iff`: the JUMP successor, as in §2, for the operands `op a, op b, op c`.
- `runCost_pc_valid_sim`, `runCost_pc_valid_supp`:
  `some c ∈ support (… runCost n ⟨pc, fp⟩) → ∃ i < 2^17, pc = gpow i`. The `n = 0` case gives
  the sentinel; the `n+1` case gives the fetch.

Semantic bridges, each proved once, by induction on `n` or on the `Walk`:

```lean
theorem one_of_sim  : some c ∈ support (sim (runCost program L n ⟨gpow 0,1⟩)) → Lx L oneCell = oneV
theorem one_of_supp : some c ∈ support (runCost program L n ⟨gpow 0,1⟩) → Lx L oneCell = oneV
theorem walk_of_sim  (hκ : κ ≤ 32) (hone) (hs : s < 2^17) :
  some c ∈ support (simulateQ (unifFwdAnswerImpl f) (runCost program L n ⟨gpow s,1⟩)) → Walk (Holds f L) L n s c
theorem walk_of_supp (hκ) (hone) (hs) :
  some c ∈ support (runCost program L n ⟨gpow s,1⟩) → Walk (HoldsNH L) L n s c
theorem sim_of_walk  (hκ) (hone) :
  Walk (Holds f L) L n s c → simulateQ (unifFwdAnswerImpl f) (runCost program L n ⟨gpow s,1⟩) = pure (some c)
```

For a jump step, `walk_of_*` uses `runCost_pc_valid` on the continuation to get
`slotOf pc' = i`. `sim_of_walk` uses the fact that a walk from `slotOf pc' ≥ 2^17` cannot
reach the sentinel.

Pure path lemmas. These carry no monad and are proved once, for any `R` with
`hR : ∀ s, R s → HoldsNH L s`, plus `hone`. Destructors are named `walk_*` and constructors
`walk_*_mk`.

- `Walk.inv`: if `s ≠ sentinel`, a walk steps from `s`.
- `walk_seg (a)`: over non-jump slots `[s, s+a)` with `s + a ≤ sentinel`, it gives
  `∀ i < a, R (s+i)` and splits `n` and `c` by `segCost s a`.
- `walk_node`: given `SET tc (tgtV t)` at `s`, `JUMP zc tc oneCell` at `s+1` and
  `t < 2^17`, it gives `R s`, `R (s+1)` and a continuation at
  `if Lx L zc = 0 then s+2 else t`, with cost and steps `+2`.
- `walk_unary (base w L0 zc tc)`: generic. It gives an exit
  `i ≤ L0 (base + w·i + 2, or base + w·L0)` at `2·min (i+1) L0`, with the z facts. It is
  instantiated as `(rBase k, 46, 63)` and `(102529, 7, 31)`.
- `walk_group`: from `gBase k q`, leaf `4q + b` after 4 steps and 4 cycles.
- `walk_leaf`: straight `leafLen − 2` ops, then the node. It lands on
  `s0 k + min e 254 + 1` (or `s0 32 + c + 1`).
- `walk_body`: steps `e+1..254`, landing on `s0 k + 255`.
- `walk_rice_chain k`: returns
  `∃ e < 256, facts ∧ n = chainSteps k e + n' ∧ c = chainCost k e + c' ∧ Walk … (s0 k + 255)`.
- `walk_c32`, and `walk_full`:
  `Walk R L n 0 c → ∃ E, Valid E ∧ n = totalSteps E ∧ c = totalCost E ∧ PathFacts R E`.
  `PathFacts` covers `R` on: constants, leaf ops, body steps `[E k+1, 254]`, the chain-32 leaf
  and body, the root and pk.
- `walk_full_mk`: `PathFacts R E ∧ DispatchFacts R L E` (R on the node slots of the honest
  dispatch, with z values encoding `E`) implies `Walk R L (totalSteps E) 0 (totalCost E)`.

The cycle bound:

```lean
theorem checksum_of_facts (hR) (hone) (h : PathFacts R E) (hE : Valid E) :
    ∑ k ∈ range 32, E k + 256 * E 32 + E 33 = 8160
theorem chainCost_bound (e < 256) : 2 * chainCost k e + 19 * e ≤ 5118 + 2 * tieLen k
theorem c32Cost_bound (c < 32) : c32Cost c + 12 * c ≤ 2618
theorem totalCost_le (hE : Valid E) (hsum : …) : totalCost E ≤ 85223
theorem cycles (S) (hS : S.program = program) : S.CyclesAtMost claim   -- claim := boundaryCycles + 85223
theorem seededRows_lt (hm : S.memLog = 16)
```

`chainCost_bound` and `c32Cost_bound` are proved by `split_ifs` and `omega`. `totalCost_le`
uses `Finset.sum_le_sum` and `Finset.sum_add_distrib`, then `omega`.

### 9.3 `ConstraintMath.lean` (additions only)

- `inputWord_pad_zero : σ.length = 4352 → 38 ≤ i → i < 47 → inputWord pk m σ i = 0`.
- `chain_from`: from the leaf relation (if `e < 255`), the body relations on `[e+1, 254]`,
  and `x_255 = σ` (if `e = 255`), conclude
  `cellBits (x 255) = chainValue f i e (255 − e) σ`. Prove it by induction with
  `chainValue_succ'` and `chainValue_zero'`.
- `checksum_digits (hd : ∀ k < 32, E k = digit m k) (h33 : E 33 ≤ 255) (hsum) :
  E 32 = digit m 32 ∧ E 33 = digit m 33`. Use `checksum_eq_sum` and `omega`.
- `checksum_honest_sum : Σ_{k<32} digit m k + 256·(C/256) + C%256 = 8160`.
- `tie_sum_half`, which reindexes the in-leaf accumulator sums to the baseline `linkChain` form.
- **Delete, or leave unused:** thermometer, telescope and mux lemmas, `chain_sound*`,
  `checksum_of_gpow`/`E`, `wv`/`wu`/`vb`/`ub` constants.

### 9.4 `MachineSound.lean` (rewrite)

- Keep `CRel` (add `.pad ↦ False`).
- `constFacts_of` (posCell, k0Cell, len).
- `tie_rel` and `tie_run`, as the three-case accumulator lemma.
- `accept_of_path (hpin : ∀ c < 47, v c = inputWord …) (hE) (h : PathFacts (CRel f v ∘ cinstrAt) E)
  : |σ| = 4352 ∧ rootValue f (reconstructedWords f m σ) = pk`. Assemble it from `constFacts`,
  the tie (reusing the `hhalf`/`hdig` blocks), `checksum_of_facts`, `checksum_digits`,
  `chain_from` with `blake2sQuery_chain`, `root_sound`, and the pk `XOR`.

### 9.5 `MachineProver.lean` (image rewrite, answers reused)

- **Reuse:** `seqAnswers`, `fixed_seqAnswers`, `xOf`, `inW`, `chainQ`, `chainAnswers`,
  `chainXF*`, `chainAnsF*`, `fixed_chainAnswers`, `endW`, `endW_honest`, the whole root-answer
  block, `inputWord_*`, `length_of_inputWord_three`, `lowE`, `highE`, canonicality lemmas,
  `dig`, `sigW`, `tabN`, `prover`, `chainTab`, `rootTab`, `fixed_prover`, `endsOf_honest`,
  `rootTab_33`.
- **New:** `cellVal` and `imageOf` for the §7 values (`MemImage 16`).
- **Drop:** `thermo*`, `accE*`, `dVal`, `pVal`, `stepVal`, `hConst`'s old table.

### 9.6 `MachineFaithful.lean` (rewrite of the relation half)

- **Keep:** `crel_of_rel`, `rel_of_crel`, `crel_congr` (add the `.pad` arm), the loader
  lemmas, and the shape of the top-level `sound`, `faithful` and `machineSubmission`
  (`memLog := 16`, `steps := fun _ m _ => totalSteps (dig m)`).
- `fixed_sound` is `walk_of_sim`, then `walk_full`, then `accept_of_path`.
- `hv_*` value lemmas; `honest_const`, `honest_dispatch`, `honest_leaf`, `honest_body`,
  `honest_leaf32`, `honest_root`, `honest_pk`.
- `holds_honest_path`, giving `PathFacts ∧ DispatchFacts`; then `walk_full_mk`, then
  `sim_of_walk`.

### 9.7 `Solution.lean`, `claim.txt`, `README`

- The claim is `85343`, with `Machine.claim_eq : claim = 85343` by `rfl` or `decide`.
- `seeded_rows` is `2^17 + 2^16`.

### 9.8 Suggested order and parallelism

The critical path is steps 1, 2, then the destructor half of step 3, then 4.

1. `MachineProgram`, with defs and decode lemmas, and `rt_model.py` constants checked
   against Lean `rfl` lemmas.
2. The walk bridges (§9.2 part 1).
3. The pure path lemmas, destructors first.
4. The cycle bound, which delivers `CyclesAtMost`.
5. `accept_of_path`, which delivers `Sound`.
6. The prover, the `DispatchFacts`/constructor lemmas, and `faithful`.

Steps 5 and 6 can proceed in parallel with step 4.

---

## 10. Risks, fallbacks, optional savings

### 10.1 Risks (none of them is a soundness gap in the design)

1. **Path framework volume.** The baseline analysed one straight path. RT needs
   `Walk`, three bridges and about ten pure path lemmas in two directions. The estimate is
   4–6k changed lines.
   - Mitigation: the monadic part is proved once per semantics, and all tree and chain
     reasoning is pure. The unary lemma is generic and serves both Rice chains and `c_hi`.
2. **Decode lemmas** use nested div/mod by 3196, 46, 11 and 7. `omega` handles these, but
   heartbeat bumps will be needed, as the baseline needed them for `stepInstr_bounded`.
   Never evaluate `cinstrAt` over ranges.
3. **Program-wide lemmas** (`jump_f`, `cinstrAt_bounded`) quantify over every slot. Prove
   them per builder, then case-split `cinstrAt` once.
4. **Constructor direction** for `Faithful`. It needs the honest z/tgt values and
   `DispatchFacts` along a data-dependent path. It mirrors the destructor lemma for lemma.
5. **Zero cells.** Cells 38 and 39 are zero only through the length `SET`, which sits on
   every path. `inputWord_pad_zero` is new but short.
6. **Kernel.** Keep `tgtV`, `vV`, `posV` and `K0` symbolic. Only ℕ layout arithmetic should
   reduce. No BF64 or E literal needs `decide`; RT uses no field identity beyond `ofK_mul`,
   `gpow_mul_gpow` and `ofK_injective`.
7. **Layout drift.** A wrong target constant breaks soundness, not merely faithfulness. The
   path lemmas would then fail to prove, so the build catches it, but the fix is expensive.
   Before writing Lean, re-run `rt_model.py` after any layout edit. It asserts
   SET-before-JUMP, forward targets, no pad on any path, the closed-form costs and the
   affine bounds.
8. **Fall-through halt.** The pk `XOR` must sit at `2^17 − 2`. If this becomes awkward, use
   the explicit-halt fallback below.

### 10.2 Fallbacks (each keeps every other part of the design)

| change | claim |
|---|---:|
| balanced depth-8 trees instead of Rice (attack-first geometry, W = 23) | 85561 |
| balanced 5-level `c_hi` tree instead of unary | 85351 |
| explicit halt: `SET fpc`, then `JUMP(ONE, fpc, ONE)` | +2 |
| uniform 2-op tie for all 32 chains (drops the tie case split) | +4 (+3 if pos 255 is dropped) |
| `SET`-constant zero pair instead of pinned 38 and 39 | +2 |

### 10.3 Phase-1b micro-optimisations (checked by the model: 85341)

- **Drop `posCell 255`**, going to 256 constants: −1. For `k ∈ {15, 31}` at `e = 255`, use
  the 2-op tie. That costs +1 on those paths only, and they never reach the worst case.
- **Chain 0 without `MUL`**: −1. Alias `G_0 := tCell 0`, so `gPrev 1 = tCell 0`, and drop
  chain 0's `MUL`.

Both leave the affine bound intact (`5117 ≤ 5118` at `e = 255`).

### 10.4 Headroom

- The information bound: at `c_hi = 31` there are `C(256, 32)` feasible digit vectors, so some
  path must make at least `log2 C(256, 32) ≈ 135.4` binary decisions. The dispatch therefore
  needs at least about 271 cycles; RT uses 312.
- Constants need at least 1 instruction per forced value.
- The remaining gap to the hash floor `84490 + 120` is 733 cycles. Further gains need Phase 2
  (scheme changes).

---

## 11. Candidate verdicts

| candidate | claim | verdict |
|---|---:|---|
| **attack-first** | 85566 | Sound, after the honest-image fix (`xCell 32 c_hi := σ_32`) and correcting 288 to 290. It is adopted as RT's base. Its hinted `c_hi` (`DEREF`, squarings, look-ahead) is dominated by a unary tree, which is cheaper by 5 and DEREF-free. Its balanced trees give way to Rice trees, a further −218. |
| **refine-A (A*) / A+** | 85933 / 85924 | Sound, after moving the checksum partials off the Horner cells (and, for A+, the `C_32 = g^(S0_32+8)` fix). Rejected: 590 cycles worse. It also needs `DEREF` (entry binding and table tie), a data-dependent BF64 byte-shift lemma, two-root gadgets with symbolic negative powers, and a `J_32` look-ahead. |
| **proof-first** | 86882 | Sound, after moving `linkAccCell` off the gadget block (cells 1024..1030 were aliased, which breaks `Faithful` as written). Rejected: 1539 cycles worse. Its "straight prelude pins every target" idea is subsumed by RT's SET-before-JUMP rule and the generic `Walk`. |

---

## Appendix A: `rt_model.py`, the executable spec

This is pure Python. It builds the full 2^17-slot bytecode, simulates the walk for 500 leaf
vectors, and asserts the following:

- every `JUMP` is preceded by the `SET` of its target;
- every taken jump goes forward;
- no path touches a pad;
- the closed forms of §5 match the simulation;
- the affine bounds hold;
- `K0 = 1826526`.

It prints:

```
layout OK; K0 = 1826526 ; worst witness m=0: steps 9182 blake 8449 cost 85223 score 85343
```

```python
import random
SENT = (1 << 17) - 1                      # sentinel slot, logSize 17
UW, GW, BW, DISP, REGION, DISP32 = 46, 44, 11, 2942, 3196, 222
def rBase(k): return 257 + REGION*k if k <= 32 else 103005
def s0(k): return rBase(k) + 2941 if k < 32 else (102750 if k == 32 else 130781)
ROOT, PK = 131036, 131070
Z = 38
def posCell(j): return Z if j == 0 else 100 + j
ONE, K0C = posCell(1), 400
def scr(k): return 1024 + 160*k
zu = lambda k, i: scr(k) + i;        tu = lambda k, i: scr(k) + 64 + i
zb = lambda k, j: scr(k) + 128 + j;  tb = lambda k, j: scr(k) + 130 + j
tC = lambda k: scr(k) + 132; vC = lambda k: scr(k) + 133; gC = lambda k: scr(k) + 134
fC = lambda k: scr(k) + 135
def accC(k): return 2 if k == 15 else (1 if k == 31 else scr(k) + 136)
uC = scr(32) + 137
def root(t): return Z if t == 0 else 7000 + 2*t
def xC(k, j): return 8192 + 512*k + 2*j
sig = lambda k: 4 + k
bytePos = lambda k: (31 - k) % 16
def gPrev(k): return ONE if k == 0 else (gC(32) if k == 33 else gC(k-1))
def gOut(k): return K0C if k == 33 else gC(k)
def gBase(k, q): return rBase(k) + UW*q + 2 if q < 63 else rBase(k) + 2898
def leafSlot(k, e):
    if k == 32: return rBase(32) + 7*(31 - e) + 2 if e >= 1 else rBase(32) + 217
    return gBase(k, e // 4) + BW*(e % 4) + 4
K0 = sum(s0(k) + 1 for k in range(32)) + s0(33) + 1 + 8160
def tieLen(k): return 0 if k >= 32 else (1 if k % 16 in (0, 15) else 2)
def tieOps(k, e):
    if k >= 32: return []
    if k % 16 == 0: return [('setc', accC(k), ('vV', bytePos(k), e))]
    if k % 16 == 15: return [('xor', accC(k-1), posCell(e), accC(k))]
    return [('setc', fC(k), ('vV', bytePos(k), e)), ('xor', accC(k-1), fC(k), accC(k))]
def coreOps(k, e):
    if e < 255:
        return [('blake', sig(k), posCell(k), posCell(e), Z, Z, xC(k, e+1), ONE),
                ('mul', gPrev(k), tC(k), gOut(k)),
                ('setc', tC(k), ('tgt', s0(k) + e + 1)),
                ('jump', ONE, tC(k), ONE)]
    return [('xor', sig(k), Z, xC(k, 255)),
            ('setc', tC(k), ('tgt', s0(k) + 256)),
            ('mul', gPrev(k), tC(k), gOut(k)),
            ('setc', vC(k), ('tgt', s0(k) + 255)),
            ('jump', ONE, vC(k), ONE)]
def leaf32Ops(c):
    return [('blake', sig(32), posCell(32), posCell(c), Z, Z, xC(32, c+1), ONE),
            ('setc', uC, ('tgt', 256*c)),
            ('mul', gC(31), uC, gC(32)),
            ('setc', tC(32), ('tgt', s0(32) + c + 1)),
            ('jump', ONE, tC(32), ONE)]
code = [('pad',)] * (SENT + 1)
def put(s, ins):
    assert code[s] == ('pad',), (s, code[s], ins); code[s] = ins
for s in range(255): put(s, ('setc', posCell(s+1), ('pos', s+1)))
put(255, ('setc', K0C, ('tgt', K0))); put(256, ('setc', 3, ('len',)))
for k in list(range(32)) + [33]:
    for i in range(63):
        put(rBase(k) + UW*i, ('setc', tu(k, i), ('tgt', rBase(k) + UW*(i+1))))
        put(rBase(k) + UW*i + 1, ('jump', zu(k, i), tu(k, i), ONE))
    for q in range(64):
        g0 = gBase(k, q)
        put(g0, ('setc', tb(k, 0), ('tgt', g0 + 24))); put(g0 + 1, ('jump', zb(k, 0), tb(k, 0), ONE))
        for b in (0, 2):
            put(g0 + BW*b + 2, ('setc', tb(k, 1), ('tgt', g0 + BW*(b+1) + 4)))
            put(g0 + BW*b + 3, ('jump', zb(k, 1), tb(k, 1), ONE))
        for b in range(4):
            ops = tieOps(k, 4*q + b) + coreOps(k, 4*q + b); assert len(ops) <= 7
            for i, op in enumerate(ops): put(g0 + BW*b + 4 + i, op)
for i in range(31):
    put(rBase(32) + 7*i, ('setc', tu(32, i), ('tgt', rBase(32) + 7*(i+1))))
    put(rBase(32) + 7*i + 1, ('jump', zu(32, i), tu(32, i), ONE))
for c in range(32):
    for i, op in enumerate(leaf32Ops(c)): put(leafSlot(32, c) + i, op)
for k in range(34):
    for j in range(1, 255):
        put(s0(k) + j, ('blake', xC(k, j), posCell(k), posCell(j), Z, Z, xC(k, j+1), ONE))
for t in range(34):
    put(ROOT + t, ('blake', xC(t, 255), Z, Z, Z, root(t), root(t+1), posCell(35 - t)))
put(PK, ('xor', root(34), Z, 0))
assert code[SENT] == ('pad',) and PK + 1 == SENT
riceDepth = lambda e: e//4 + 3 if e//4 < 63 else 65
u32Depth = lambda c: 31 if c == 0 else 32 - c
leafLen = lambda k, e: tieLen(k) + (4 if e < 255 else 5)
leafCost = lambda k, e: tieLen(k) + (13 if e < 255 else 5)
bodyLen = lambda e: max(254 - e, 0)
chainSteps = lambda k, e: 2*riceDepth(e) + leafLen(k, e) + bodyLen(e)
chainCost = lambda k, e: 2*riceDepth(e) + leafCost(k, e) + 10*bodyLen(e)
c32Steps = lambda c: 2*u32Depth(c) + 5 + (254 - c)
c32Cost = lambda c: 2*u32Depth(c) + 14 + 10*(254 - c)
totalSteps = lambda E: 257 + sum(chainSteps(k, E[k]) for k in range(32)) + c32Steps(E[32]) + chainSteps(33, E[33]) + 35
totalCost = lambda E: 257 + sum(chainCost(k, E[k]) for k in range(32)) + c32Cost(E[32]) + chainCost(33, E[33]) + 341
def walk(E):
    z = {}
    for k in list(range(32)) + [33]:
        q, b = divmod(E[k], 4)
        for i in range(63): z[zu(k, i)] = 1 if i < q else 0
        z[zb(k, 0)], z[zb(k, 1)] = b >> 1, b & 1
    for i in range(31): z[zu(32, i)] = 1 if i < 31 - E[32] else 0
    mem, s, n, cost, h = {}, 0, 0, 0, 0
    while s != SENT:
        ins = code[s]; assert ins[0] != 'pad', s
        n += 1; cost += 10 if ins[0] == 'blake' else 1; h += ins[0] == 'blake'
        if ins[0] == 'setc':
            assert mem.get(ins[1], ins[2]) == ins[2]; mem[ins[1]] = ins[2]
        if ins[0] == 'jump':
            assert code[s-1][0] == 'setc' and code[s-1][1] == ins[2]   # SET-before-JUMP
            if ins[1] == ONE or z[ins[1]]:
                t = mem[ins[2]][1]; assert t > s; s = t; continue
        s += 1
    return n, cost, h
random.seed(1)
for trial in range(500):
    E = [random.randrange(256) for _ in range(34)]; E[32] = random.randrange(32)
    if trial % 4 == 0:
        E = [random.choice([0, 1, 3, 4, 250, 251, 252, 254, 255]) for _ in range(34)]; E[32] = random.choice([0, 1, 30, 31])
    assert walk(E)[:2] == (totalSteps(E), totalCost(E)), E
for e in range(256):
    assert 2*chainCost(0, e) + 19*e <= 5118 + 2*tieLen(0) and 4*riceDepth(e) <= 12 + e
for c in range(32): assert c32Cost(c) + 12*c <= 2618
assert sum(tieLen(k) for k in range(32)) == 60 and K0 == 1826526
Ew = [0]*32 + [31, 224]                     # m = 0: C = 8160, c_hi = 31, c_lo = 224
n, cost, h = walk(Ew)
print("layout OK; K0 =", K0, "; worst witness m=0: steps", n, "blake", h, "cost", cost, "score", cost + 120)
```

Other checks were run during design but are not included in this appendix:

- Statically, over all 16926 `JUMP`s:
  - each is immediately preceded by `SET` of its own target cell to a `tgtV` constant;
  - each target is a live, non-`JUMP` slot strictly after the `JUMP`;
  - each conditional `JUMP` falls through to a live, non-`JUMP` slot;
  - each f-operand is `oneCell`.
- The cell families are pairwise disjoint and every cell is below 2^16. On 200 paths, every
  output cell is defined by exactly one instruction, except `k0Cell` (`SET` plus `MUL`).
- An exact dynamic program over all `(E, c)` satisfying the checksum identity:
  - RT: maximum 85223;
  - with the Phase-1b micro-optimisations: 85221;
  - balanced depth-8: 85441;
  - balanced 5-level `c_hi`: 85231.




( https://github.com/leanEthereum/ots.golf-submissions/compare/main...nconsigny:ots.golf-submissions:autoresearch/riscv-353?expand=1&title=RISC-V%3A%20353%20cycles%20via%20exact%20availability%20and%20thinner%20s
        tates&body=Assisted%20by%3A%20Codex%0A%0AImproves%20the%20officially%20verified%20358-cycle%20record%20(%2333)%20to%20353%20cycles.%20Exact%20availability%20is%20proved%20for%20actual%20cached%20key%20generation%2C%20including%20collisions.%20Six
        teen%20144-bit%20and%20sixteen%20192-bit%20states%20fit%20the%20same%205376-bit%20payload%3B%20repacking%20saves%20four%20redirects%20and%20one%20width%20change.%20Security%20is%20re-proved%20at%20the%20narrower%20width.%0A%0A38%20index%20%2B%202
        94%20chains%20%2B%2021%20root%2Fdecision%20%3D%20353%20cycles.%20Image%3A%2015%2C701%20instructions%20%2B%2088%20data%20bytes%20%3D%2062%2C892%20bytes.%20Full%20signature%3A%205504%20bits.%0A%0AThe%20full%20Lean%20certificate%2C%20strict%20image-
        size%20theorem%2C%20permitted-axiom%20guard%2C%20source-policy%20and%20contract-pin%20checks%20pass.%20The%20pinned%20development%20comparator%20passes%20after%20a%20cold%20candidate%20rebuild%20and%20default-kernel%20replay%20(291.395%20seconds%
        20locally).%20The%20actual%20Lean%20image%20matches%20the%20independent%20generator%3B%2020%2C840%20transcript%20tests%20cover%20all%204%2C096%20pair%2Fdigit%20landings.%0A%0AOnly%20formal%2FSubmissions%2FUpperRiscv%2F%20changes.%20Contract%3A%20
        da1418bfec2a599ac36d035f3a1ec551e73d73a0.%20NOTES.md%20contains%20technical%20details%20and%20attribution.%0A%0AOfficial%20command%3A%20python3%20.contract%2Fverifier%2Fverify.py%20upper-riscv%20--source%20.%0AThe%20unchanged%20local%20official%2
        0verifier%20stops%20at%20this%20host's%20Landlock%20preflight.%20No%20isolation%20requirement%20was%20bypassed.%20Local%20checks%20are%20not%20a%20hosted%20verdict.%20This%20PR%20requests%20hosted%20verification.)
---

# Scheme development notes (baseline, PR #23/#31)


## Construction

Use a conservative Winternitz encoding before optimizing cycles. The 256-bit message
is represented by 32 bytes. Append the two-byte checksum `sum(255 - byte)`; it fits
because its maximum is 8,160. Signing reveals position `digit` of each of 34 chains;
verification advances it through positions `digit .. 254` to the endpoint.

Each chain query uses the leanISA input format: a zero chaining value, a 512-bit block
containing the 128-bit value, chain identifier, position and a zero cell, and metadata
1. Its low 128 output bits become the next value. Root absorption folds the 34
endpoints with distinct metadata 35 down to 2 and retains the full 256-bit state between calls, finally
truncating to the 128-bit public key. Every call costs two model compressions.

## Checked results

`Encoding.lean` proves message-encoding injectivity and checksum incomparability.
`Resources.lean` proves all three pathwise algorithm budgets, including the newly
required verification cap. `BasicProperties.lean` proves the signature-size bound,
oversized rejection, zero signing failure and deterministic verification.

`Wire.lean` proves both serialization round trips. `Correctness.lean` first proves
correctness for every fixed oracle answer table, then uses VCVio's cached-oracle
support characterization to transfer it to the protected random-oracle experiment.
This proves perfect correctness even when the message depends on the public key,
and completes `scheme.Admissible`. The fixed-table lemmas also characterize
verification on arbitrary raw inputs, not just signatures produced by the signer.

`ForgeryStructure.lean` extracts chain second preimages or an honest word before
the signed cut, conditional on reconstruction matching the honest endpoint vector.
`RootBinding.lean` removes that condition by extracting a root second preimage when
the vectors differ. Its internal comparisons use all 256 hash-output bits; only
the final root comparison uses the 128 public-key bits. The combined theorem is
`accepted_forgery_event`. It covers a different signature at the same message too.
The second-preimage inputs are restricted to the actual reconstructed paths:
existence of a collision somewhere in the entire oracle table would not give a
useful probability bound.

`QueryLayout.lean` proves that equal honest query inputs have the same position,
even across different records. `Records.lean` gives independent coordinates for
sources and full hash outputs, together with the programmed cache.
`RecordSemantics.lean` proves that any table respecting this cache reproduces
all chain values, signed words, endpoints, and the public key.

`TargetBound.lean` derives adaptive target-output bounds from a cache potential.
`SecondPreimages.lean` specializes this to the tagged chain/root queries. A query
matches at most one position; its target set has at most 2^128 full answers and
it costs two compressions. The resulting rate is 2^-129 per compression.

`Resampling.lean` partitions records by the information at a signing cut. It
exposes all root answers, each cut word, and subsequent chain answers; this may
reveal extra data, which is safe for an upper bound on adversarial success.
`Exposure.lean` proves that this information determines the exposed oracle cache
and that the remaining hidden cache is disjoint. `HiddenCharges.lean` resamples
one hidden input coordinate to bound a fixed query, without a union factor over
chain positions. `HiddenBound.lean` lifts this to adaptive computations using the
same 2^-129 per-compression rate. `Coupling.lean` combines that bound with identical-
until-bad to replace hidden programmed answers by fresh answers for a whole public
fiber and any bounded payoff.

`Replay.lean` proves exact cached executions for the chains and signing. It allows
any cache extending the honest record, including one extended by adversarial queries.
Signing produces the recorded cut signature and leaves the cache unchanged. The
signature is also proved to depend only on the post-signing public data.

These are checked ingredients, not yet the full security theorem.

## Remaining proof work

Do not infer a security certificate from the checksum theorem. It excludes simple
chain-advancing attacks but does not bound oracle attacks. A full proof must account
for guessing hidden chain inputs, matching chain outputs, root collisions, adaptive
message choice, and strong forgeries on the already signed message. Only that proof
can justify the tentative 128-bit chain values under the exact cost-normalized target.

The remaining gap is probabilistic, not checksum arithmetic. In particular:

1. Relate the real cached experiment to independently sampled chain records,
   preserving the adversary's views before and after its adaptive signing request.
   Distinct chain/root position tags now guarantee pairwise distinct honest inputs
   for every record. No bad-record collision allowance is needed for this step.
2. Translate the structural witnesses into queries on the real experiment's
   transcript. The fixed-table support characterization proves correctness; it
   does not preserve the probability weights needed for security.
3. Bound hidden-word hits and targeted second preimages, including prior queries,
   cache hits, root compression, and the final verifier's queries. Charge them to
   `CostAtMost (experiment scheme adversary) B`, then establish the strict
   `B / 2^127` inequality.

VCVio's `RandomOracle.ProbeEps` supplies a single-hidden-target hit bound, and
`RandomOracle.DeferredSampling` supplies probability manipulations. Neither is
an instantiated WOTS reduction. The pinned `HashSig.SLHDSA.Security` explicitly
packages primitives without a complete unforgeability theorem; do not replace
the missing competition proof with an assumed primitive-security hypothesis.

For the bytecode, prefer bounded control flow with every hint constrained. The
protected cycle bound quantifies over all committed images and uncached answer
paths; hash binding cannot be used to justify a loop bound. Include the mandatory
120-cycle boundary charge. No bytecode or cycle estimate is certified here yet.

## Why existing entries were not copied

Existing RISC-V entries query the oracle on lengths that leanISA's fixed 896-bit
interface cannot issue. Merkle–Damgård hashing is a different oracle program and
needs its own proof; substituting it does not preserve the old certificate.

The local leanVM checkout's current branch is RISC-V work. Its older `origin/main`
contains leanISA signature code, but the XMSS instance has different key/signature
sizes and budgets. It is implementation inspiration, not a ready competition proof.

## Elaboration notes

Use explicit classical deciders for existential searches over the finite record
space. An inferred executable decider may enumerate a function space of astronomical
size while Lean checks definitional equality. Keep finite-set membership lemmas
generic in the element type before specializing them to records (`finiteFiber`).
Do not unfold a concrete `Finset.univ` of records or 256-bit words to prove a counting
identity. Normalize scalar exponents separately from finite-set expressions.

The prospective final accounting can allow separate hidden-input and output-match
charges before and after signing: four charges at 2^-129 on the remaining budget.
To obtain the required strict 127-bit bound, prove and subtract the positive cost
already spent on key generation. This is a proposed assembly strategy, not a checked
experiment bound. The stage transitions must still preserve the relevant cache and
public-data invariants, including queries made before the signing request.
