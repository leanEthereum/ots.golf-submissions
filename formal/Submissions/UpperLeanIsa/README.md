# 1198-cycle leanISA continuation

This root exports a complete locally checked `Submission.Certificate 1198`, extending the verified 1209
rarest-cut construction with layer-87 tables and a fused signature-length/ONE initializer.
See [NOTES.md](NOTES.md) for the construction, proof obligations, validation status and credits.

Build from a prepared pinned Lean project with:

```sh
lake build Submissions.UpperLeanIsa.Solution
```

The competition entry point is `Solution.lean`; the claim is in `claim.txt`.
