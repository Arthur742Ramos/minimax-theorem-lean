# Von Neumann Minimax Theorem in Lean 4

A Lean 4 / Mathlib formalization of von Neumann's minimax theorem (1928) for
finite two-player zero-sum games: for finite nonempty pure-strategy sets and a
real payoff matrix, the maxmin value over mixed strategies equals the minmax
value.

## Plan

- **M1**: Mixed strategies (probability distributions on finite types), the
  expected-payoff bilinear form, basic API lemmas. Survey Mathlib for the hard
  direction (separating hyperplane / LP duality / fixed point) and lock the
  proof path.
- **M2**: Easy direction: maxmin ≤ minmax.
- **M3**: Hard direction: minmax ≤ maxmin, zero `sorry`s.
- **M4**: Palomar packaging (`Challenge.lean` / `Solution.lean` /
  `comparator.json` / `formalization.yaml`), local verifier replica green,
  prose-vs-artifact audit.
- **M5**: Palomar intake: submit, monitor mechanical verification and automated
  review, repair fixable issues. Stop before Register (Arthur clicks).

## Status

Scaffold only. No milestones implemented yet.
