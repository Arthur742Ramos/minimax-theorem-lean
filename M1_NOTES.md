# Mathlib API notes for M2/M3

- The import `Mathlib.Data.Real.Basic` is deprecated in this checkout. Its
  replacement is `Mathlib.Basic.Real.Basic`; for the real conditionally
  complete order instances, use `Mathlib.Algebra.Order.Archimedean.Real.Basic`
  (as M1 does).
- The function-set `stdSimplex`, `convex_stdSimplex`, and associated older
  lemmas in `Mathlib/Analysis/Convex/StdSimplex.lean` are deprecated since
  2026-08-29. The replacement is `Convexity.StdSimplex`, with finitely supported
  `weights`. `Convexity.StdSimplex.range_toFun_comp_weights` describes its
  image in a finite function space; `isClosedEmbedding_toFun_comp_weights`
  and `compactSpace` are available in the corresponding convex-space topology
  and compactness files. For the recommended Sion specialization, directly
  proving the elementary coordinate simplex closed, compact, and convex
  avoids this representation conversion.
- `Sion.minimax'` and the generic indexed saddle-value identities require
  complete linear orders. For real payoffs, use
  `Sion.exists_isSaddlePointOn`, then the conditional `ciSup`/`ciInf` lemmas
  with M1's bounds. Its first player minimizes and its second player maximizes.
