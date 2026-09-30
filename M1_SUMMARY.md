# M1: finite mixed strategies and the M3 proof route

Surveyed the vendored Mathlib v4.35.0-rc2 checkout, commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Paths below are relative to
`.lake/packages/mathlib/`. This is a local source survey, not a claim about
other Mathlib revisions.

## Implemented

`Minimax/Basic.lean` defines `Minimax.MixedStrategy` with explicit real
coordinates, nonnegativity, and total mass one. Its API includes extensionality,
uniform distributions and a `Nonempty` instance, coordinate bounds, convex
mixtures, pure strategies, and the three pure-payoff identities.

`weightedPayoff` extends expected payoff to arbitrary real vectors, with
additivity and real homogeneity in each argument. `expPayoff_linear_left` and
`expPayoff_linear_right` transfer these identities to any strategies with the
specified coordinate relation; `expPayoff_mix_left/right` specialize them to
convex mixtures. A probability simplex is not closed under vector addition or
arbitrary scaling, so it cannot itself carry the usual linear-space API.

`maxminValue` and `minmaxValue` use real indexed suprema and infima as requested.
The explicit bound `payoffBound u = ∑ a, ∑ b, |u a b|` bounds every expected
payoff between its negative and itself. Both inner payoff ranges and both
outer extremum ranges have `BddBelow` and `BddAbove` lemmas. The inner extrema
and both values also satisfy the same explicit bounds. No minimax inequality
or equality is proved in M1.

## Requested Mathlib survey

### (a) Separating hyperplanes / geometric Hahn–Banach: present

All three declarations below are in
`Mathlib/Analysis/LocallyConvex/Separation.lean`:

- `geometric_hahn_banach_open`: separates disjoint convex sets when the first
  is open, with a continuous real linear functional and a scalar threshold.
- `geometric_hahn_banach_compact_closed`: strongly separates a compact convex
  set and a disjoint closed convex set in a locally convex real vector space.
- `geometric_hahn_banach_closed_compact`: the reversed-order variant.

The compact/closed result returns a functional `f` and scalars `u < v` such
that `f a < u` on the compact set and `v < f b` on the closed set.

### (b) Farkas lemma: present geometrically; LP duality: absent

In `Mathlib/Analysis/Convex/Cone/Dual.lean`:

- `ProperCone.hyperplane_separation`: separates a closed convex cone from a
  disjoint compact convex set, nonnegatively on the cone and negatively on
  the compact set.
- `ProperCone.hyperplane_separation_point`: the singleton specialization,
  yielding `∃ f, (∀ x ∈ C, 0 ≤ f x) ∧ f x₀ < 0` for `x₀ ∉ C`.

In `Mathlib/Analysis/Convex/Cone/InnerDual.lean`:

- `ProperCone.hyperplane_separation'`: the Hilbert-space inner-product version
  of the point theorem.
- `ProperCone.relative_hyperplane_separation`: the relative inner-dual
  formulation. Its `C.map f` is a **closure** of the image; it is not directly
  a finite matrix feasibility theorem without a closed-image argument.

There is no ready-made finite matrix Farkas alternative or linear programming
strong-duality theorem in this checkout. The TODO in
`Mathlib/Analysis/Convex/Cone/Basic.lean` explicitly lists defining primal/dual
cone programs, proving strong duality, and deriving LP duality as future work.
The tactic simplex algorithm is certificate-search code, not an LP duality
API.

### (c) Brouwer fixed-point theorem: absent

There is no Brouwer fixed-point declaration or file in this checkout. Searches
across `Mathlib/` for Brouwer, Schauder fixed points, Kakutani fixed points,
no-retraction, and topological Sperner lemmas found no such theorem.
`Mathlib/Dynamics/FixedPoints/Topology.lean` contains
`isFixedPt_of_tendsto_iterate` and `isClosed_fixedPoints`; these do not assert
existence of a fixed point for continuous simplex self-maps. The combinatorial
antichain Sperner theorem is a different result.

## One recommended M3 path: specialize Sion's real saddle-point theorem

Use **`Sion.exists_isSaddlePointOn`**, in `Mathlib/Topology/Sion.lean`.
It already proves the hard minimax content for real-valued functions on
nonempty compact convex sets, assuming separate lower/upper semicontinuity
and quasiconvexity/quasiconcavity. This recommendation reuses Mathlib's
minimax theorem rather than constructing an independent separation proof.

1. Work in the ambient vector spaces `B → ℝ` and `A → ℝ`, using the sets
   `{w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}`. Their points correspond directly
   to our `MixedStrategy` records. Prove convexity from the coordinate
   constraints. Prove closedness by finite continuous sums and coordinate
   inequalities, and compactness as a closed subset of `Set.Icc 0 1` in the
   finite function space.
2. Put the minimizing player first: `X` is the `B` simplex, `Y` is the `A`
   simplex, and `f y x = weightedPayoff u x y`. Separate continuity follows
   from finite sums and products. Bilinearity makes both sections affine;
   use `LinearMap.convexOn`, `LinearMap.concaveOn`
   (`Mathlib/Analysis/Convex/Function.lean`), then
   `ConvexOn.quasiconvexOn`, `ConcaveOn.quasiconcaveOn`
   (`Mathlib/Analysis/Convex/Quasiconvex.lean`).
3. The returned strategies `y*`, `x*` satisfy
   `expPayoff u x y* ≤ expPayoff u x* y` for all strategies. Specializing
   one side to the saddle strategy gives
   `expPayoff u x y* ≤ v ≤ expPayoff u x* y`, with
   `v = expPayoff u x* y*`. Apply the M1 range bounds with `ciSup_le`,
   `ciInf_le`, `le_ciSup`, and `le_ciInf` to obtain
   `minmaxValue u ≤ v ≤ maxminValue u`.

**Expected length:** approximately 150–250 new Lean lines for the simplex
geometry, separate continuity/affinity, and saddle-to-value bridge. This is a
planning estimate, not an implemented M3 proof. **Risk:** low to moderate;
most work is finite-dimensional API plumbing. The main pitfalls are player
orientation, deprecated simplex APIs, and real conditional completeness.
There is no need to construct a separator, normalize a dual functional,
establish closedness of a cone image, or develop a fixed-point theorem.

`Sion.minimax` in the same file is also present and accepts explicit
`IsLUB`/`IsGLB` witnesses over a general densely ordered linear order.
`Sion.minimax'` requires a **complete** linear order and therefore cannot be
applied directly with codomain `ℝ`. The recommended path uses only the
real-valued saddle-point theorem above.

## Validation

The default target imports `Minimax.Basic`. `lake build` succeeds without
warnings or deprecations. A temporary audit outside the project prints axioms
for all 74 declarations in the `Minimax` namespace, including structure-generated
declarations, and rejects any axiom other than `propext`, `Classical.choice`,
and `Quot.sound`. The surveyed positive declarations were also checked by Lean;
`Sion.exists_isSaddlePointOn` uses only those permitted axioms.
