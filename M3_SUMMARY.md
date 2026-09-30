# M3: hard direction and the main minimax theorem

Implemented by Codex (gpt-6.1-sol, high effort) in `Minimax/HardDirection.lean`
(129 lines), imported from the root `Minimax.lean`. Committed as `c862dcd`,
pushed to origin/main. M1 (`Minimax/Basic.lean`) and M2
(`Minimax/EasyDirection.lean`) untouched.

## Proof route

Followed the M1 survey recommendation: `Sion.exists_isSaddlePointOn`
(Mathlib/Topology/Sion.lean), with the minimizing player first
(E := B → ℝ, X := B coordinate simplex; F := A → ℝ, Y := A coordinate simplex)
and `f yB xA := weightedPayoff u xA yB`.

- `coordSimplex S : Set (S → ℝ)` defined directly from coordinate constraints;
  bridge lemmas both ways to `MixedStrategy` (`val_mem_coordSimplex`,
  `ofCoordSimplex`).
- Simplex geometry proved directly (no deprecated stdSimplex API):
  nonempty (uniform weights), convex (coordinate-wise), closed (continuous
  coordinate evaluations and finite sum), compact (closed subset of the
  compact pi-set `Set.pi Set.univ (fun _ => Set.Icc 0 1)`).
- Sections shown affine via real linear maps: `LinearMap.convexOn` /
  `LinearMap.concaveOn`, then `ConvexOn.quasiconvexOn` /
  `ConcaveOn.quasiconcaveOn`; separate continuity from finite sums/products,
  lifted to semicontinuity for Sion's hypotheses.
- `exists_payoff_saddle` extracts MixedStrategy saddle strategies from Sion;
  `minmax_le_maxmin` bridges the saddle inequality to the M1 value
  definitions via `ciInf_le`/`ciSup_le`/`le_ciInf`/`le_ciSup` with M1's
  boundedness lemmas.
- `minimax_theorem : maxminValue u = minmaxValue u` :=
  `le_antisymm (maxmin_le_minmax u) (minmax_le_minmax u)`.

## Verification (independent)

- Force-rebuilt `Minimax.HardDirection` from scratch (olean deleted):
  1735 jobs, exit 0.
- Rebuilt with warning scan: 0 warnings, no deprecations.
- Grep for `sorry`/`admit`/`axiom`/`unsafe`: none.
- `#print axioms` on all 12 new declarations: each depends only on
  `[propext, Classical.choice, Quot.sound]`.
- `git ls-remote` confirms origin/main = local HEAD `c862dcd`.
