# ExactOverlaps

This directory contains the **555-module dependency closure** of
`ExactOverlaps.MainTheorem.Theorem11` and `ExactOverlaps.SelfSimilar.NoExactOverlaps`,
from Samuel Kittle and Constantin Kogler,
*The exact overlaps conjecture for self-similar measures on the real line*,
arXiv:2610.10511v1 (2026).

- [Public source](https://github.com/ckkogler/exact-overlaps-one-dim-lean)
- Revision: `99c43adec5c5127ff9a65663641fe51f57c8f7d3`.
- Every retained Lean file is unchanged; `provenance/sources.json` records hashes.
- The upstream root umbrella and 37 other modules outside this closure are omitted.
- The BSD Zero Clause licence is in [LICENSE](LICENSE); the adapted LpSelfSimilar
  code's notice is retained in [LpSelfSimilar-LICENSE](LpSelfSimilar-LICENSE).

Import `ExactOverlaps.MainTheorem.Theorem11` or
`ExactOverlaps.SelfSimilar.NoExactOverlaps` directly, or use
`FractalGeometry.ExactOverlaps`, which imports both. `BoxLike.KittleKogler` derives its
exact-dimensionality statement from them. The Lake library builds every retained
module, with `srcDir = "vendor"`, `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3`, matching the source's options. The toolchain and
Mathlib revision are pinned in the main project.

The library's axiom audit covers all declarations in these retained modules.
