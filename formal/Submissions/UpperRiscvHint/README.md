# Combined hinted RISC-V: 310 cycles

This proof combines the zero-hash pointer skips of `1cbee19` with the variable
disclosure construction. The six skipped-pair alphabets retain target 147;
chain 13 loses its mandatory final hash. Signatures are 5495 bits and the image
is 1043472 bytes.

The complete Lean 4.33.1 certificate compiles and passes exact-statement
comparison, the permitted-axiom audit and fresh kernel replay of all
23,094 exported declarations.
Independent VM and completion tests pass. See `NOTES.md` for the construction
and `riscv-innovation-evidence/combined310` in the workspace for reproduction.
The contract remains pinned and unchanged. Official sandbox verification needs
a host with Landlock support; no hosted verdict is claimed.
