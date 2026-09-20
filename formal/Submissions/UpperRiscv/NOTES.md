# upper-riscv: 687 cycles

## Idea

The 693-cycle image spends 70 cycles on the index phase, `9 + 2 · nibble` per chain (602) and 21
on the root and decision. Each chain step is `SH x12, tag, -2; ECALL`: the store puts a 16-bit
level tag into the top halfword of the chain header, so that the 192-bit chain input
`header ‖ value` names its node `(chain, level)`. The fifteen tags must be pairwise distinct, and
eight of them were values that happen to sit in registers after the index phase; the other seven
cost one `ADDI` each in `levelSetup`.

**Widen the tag field.** A `SW x12, tag, -4` costs the same cycle as the `SH`, but a 32-bit tag is
the low 32 bits of the register, and many more registers have pairwise distinct known low words:

| register | low 32 bits | why it is known |
|---|---|---|
| `x0` | 0 | zero (last level, so the final header is the root's) |
| `x5` | 1 | HASH call number |
| `x11` | 192 | chain input length |
| `x9` | `0x400040` | payload cursor |
| `x13` | 4224 | checked signature length |
| `x22` | `0x00780078` | lane mask `0x0078007800780078` |
| `x23` | `0x00010001` | lane-sum multiplier (distinct from `x5` only at 32 bits) |
| `x24`, `x25` | `0x16621662`, `0x20222022` | broadcast jump bases |
| `x2` | `0x01000000` | the loader's stack top, never written by the image |
| `x1` | 1256 | the sum comparator `8 · 157` (see below) |
| `x12`, `x10` | `slotAddr k`, `slotAddr k - 8` | the chain's own HASH pointers |
| `x14` | `4412 + 156 k` | the prologue's `JALR x14, x28, imm` return address |
| `x3` | 2 | the one remaining `ADDI` |

Three tags depend on the chain (`x12`, `x10`, `x14`); the header is
`slotAddr k + levVal k t · 2^32` and `hdrNat_injective` still recovers `(k, t)`: the low 32 bits
give the chain, the high 32 bits the level within it. The `JALR` return address is free because
the prologue's jump already exists; its `rd` was `x0`.

**Let the sum comparator be a tag.** The sum check was `MUL; SRLI 48; XORI 1256; BEQ x27, x0`.
Loading the comparator instead, `ADDI x1, x0, 1256; MUL; SRLI 48; BEQ x27, x1`, costs the same
four cycles but leaves 1256 in `x1` for the rest of the run, which is one tag fewer to set up.

## Result

`levelSetup` shrinks from eight instructions to two (`ADDI x3, x0, 2; ADDI x11, x0, 192`): the
index phase costs **64** cycles, the total **687** (`64 + 602 + 21`), image length 1331. Nothing
else changed: same scheme graph, same 32 chains × 15, same target 157, same 4224-bit signature,
same root input. The security proof only reads the header through `Flat.hdrNat`, `hdrNat_lt` and
`hdrNat_injective`, whose statements are unchanged, so `Names/Values/Events/Resample/StageB` were
rebuilt but not edited. The machine proof changes are in `Constants`, `Program`,
`ChainContext` (`Ctx.levels` covers only the twelve fixed registers), `ChainSteps` (`StepInv`
carries `x14`; `StepInv.tag` assembles all fifteen tags), `ChainBlock` (`JALR` with `rd = x14`),
`IndexPhase`, `MachineFacts` (word-store lemmas) and `BlockExecution` (`SW` is straight-line).

Official verifier: `python3 .contract/verifier/verify.py upper-riscv --source .`. This
WSL2 development host cannot start the judge's systemd/Landlock sandbox (systemd 249, no
securityfs), so the same `verify.py` pipeline was run through comparator's development shim, as
on macOS: policy checks, staging over the trusted tree, warm `.lake` clone, stub rendering,
comparator with statement comparison, axiom audit and kernel replay →
`verified: track=upper-riscv claim=687`, comparator exit 0, in 1642 s unsandboxed on a machine
about three times slower than the hosted judge (whose run of the 693 root took 388 s).

## What did not work, and what is left

- **A fifteenth free tag.** Everything else with a known low word is a duplicate: `x6` (the
  loaded 4224 equals `x13`), `x27` after the check (equals `x1`), the zero registers, and
  `x26`/`x28`/`x20`/`x21`/`x30`/`x31` are input-dependent. A tag must be a function of `(k, t)`
  only, so the nibble-dependent jump target `x28` is out.
- **The index phase is otherwise tight for this dispatch.** The copy of the nonce is forced by the
  protected index `H(m ++ η)` (nonce in the low bits, i.e. below the message in memory). The
  eight lane words (shift, mask, subtract, store) are the cheapest way found to give 32 chains a
  16-bit `jumpBase - 8·nibble` each, and their seven `ADD`s are the cheapest nibble sum given
  that the masked words exist anyway; SWAR byte-lane sums cost more once the 16-bit fold and
  masks are counted. Two jump bases are forced by the 4992-byte span of the chain tables.
- **The prologue stays at nine.** The HASH ABI needs `x10 = x12 - 8` for in-place chaining, so two
  pointer updates; the disclosed word must be copied because the signature stride (16) leaves no
  room for the 32-byte output and the header; a constant-scratch variant saves the pointer updates
  but pays four to move the top into the root input. Using the `JALR` return address as the slot
  pointer would put the slots at the 156-byte code stride and inflate the root input.
- **Next single cycle: the root's `ADDI x10`.** After chain 31 the input pointer sits at the top
  of the slot region while the root input starts at the bottom. Taking the chain value from the
  *high* half of the hash output, processing slots downward and reading the root input as
  `value ‖ header` pairs (6144 bits, still 12 compressions) would leave `x10` already at the root
  input; it needs the low-half `trunc` replaced throughout `Values/Events` and a new root format,
  for one cycle.
- **The big prizes are unchanged** from the previous notes: dropping the per-step tag store
  (about 157 cycles) needs the security potential re-derived with a level-split second-preimage
  charge; wide chain states (about 70) need a full redesign.
