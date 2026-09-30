# Von Neumann's minimax theorem in Lean

This library proves von Neumann's finite two-player zero-sum minimax equality
for arbitrary real payoffs. The exact common hypotheses are
`{A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (u : A → B → ℝ)`:
`A` and `B` are finite nonempty pure-strategy types. Player `A` maximizes the
single payoff `u`, and player `B` minimizes it, representing opposing payoffs
`u` and `-u`. There is no separately stored second payoff.

The source is John von Neumann's [“Zur Theorie der Gesellschaftsspiele”](https://link.springer.com/article/10.1007/BF01448847),
*Mathematische Annalen* **100**, 295–320 (1928). The result is a foundation of
modern game theory and mathematical economics. Its mixed-strategy solution
concept is the two-player zero-sum precursor to Nash's more general equilibrium
existence theory; this package proves the minimax statement. See the
[historical account from SFI Press](https://www.sfipress.org/12-nash-1951).

`Minimax.MixedStrategy (A : Type*) [Fintype A] [Nonempty A]` is a probability
vector with these exact fields:

```lean
val : A → ℝ
nonneg : ∀ a, 0 ≤ val a
sum_one : ∑ a, val a = 1
```

In [Minimax/Basic.lean](Minimax/Basic.lean), the three definitions have the
common hypotheses quoted above; `expPayoff` additionally takes
`(x : MixedStrategy A) (y : MixedStrategy B)`. Their bodies are:

```lean
expPayoff u x y = ∑ a, ∑ b, x.val a * y.val b * u a b
maxminValue u = ⨆ x : MixedStrategy A, ⨅ y : MixedStrategy B, expPayoff u x y
minmaxValue u = ⨅ y : MixedStrategy B, ⨆ x : MixedStrategy A, expPayoff u x y
```

Expected payoff extends to the bilinear `weightedPayoff` on unrestricted real
vectors. On the probability simplices it is affine in each strategy.
`payoffBound u = ∑ a, ∑ b, |u a b|` bounds every expected payoff and both
values between `-payoffBound u` and `payoffBound u`, as proved by
`expPayoff_bounds`, `maxminValue_bounds`, and `minmaxValue_bounds`.
Thus the real indexed infima and suprema have nonempty bounded ranges.

The three public results in [Solution.lean](Solution.lean) have these statements:

```lean
Minimax.Palomar.maxmin_le_minmax
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : maxminValue u ≤ minmaxValue u

Minimax.Palomar.minmax_le_maxmin
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : minmaxValue u ≤ maxminValue u

Minimax.Palomar.minimax_theorem
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : maxminValue u = minmaxValue u
```

Each proof applies the corresponding library theorem in namespace `Minimax`.
The easy inequality uses conditional supremum/infimum bounds.
[Minimax/HardDirection.lean](Minimax/HardDirection.lean) proves that the
coordinate simplices are nonempty, compact, and convex and that the payoff is
separately continuous and affine. `Minimax.exists_payoff_saddle` applies
Mathlib's `Sion.exists_isSaddlePointOn` with the minimizing player first:
`f := fun y x => weightedPayoff u x y`, with `y` on the `B` simplex and `x`
on the `A` simplex. Its exact conclusion, under the common hypotheses, is:

```lean
∃ x : MixedStrategy A, ∃ y : MixedStrategy B,
  ∀ x' : MixedStrategy A, ∀ y' : MixedStrategy B,
    expPayoff u x' y ≤ expPayoff u x y'
```

This gives `minmaxValue u ≤ expPayoff u x y ≤ maxminValue u`. Antisymmetry
combines the two inequalities. The proof specializes Sion's theorem rather
than reproducing von Neumann's original argument. Infinite pure-strategy sets
and general n-player games are outside the advertised statement.

The library and Solution contain zero sorries and use only the permitted
axioms `propext`, `Classical.choice`, and `Quot.sound`.
[Challenge.lean](Challenge.lean) contains exactly six deliberate sorries:
three definition holes and three theorem placeholders required by the Palomar
statement-surface format. Its intentional placeholder warnings are disabled
only for the Challenge build target.

The packaging layout is:

| File | Role |
| --- | --- |
| `Minimax/Basic.lean` | Strategies, payoffs, bounds, and value definitions |
| `Minimax/EasyDirection.lean` | `maxmin_le_minmax` |
| `Minimax/HardDirection.lean` | Sion saddle point, reverse inequality, equality |
| `Minimax.lean` | Library imports |
| `Challenge.lean` | Self-contained statement surface importing only Mathlib |
| `Solution.lean` | Library-backed proofs; imports Minimax separately from Challenge |
| `comparator.json` | Three definition names, three theorem names, permitted axioms |
| `formalization.yaml` | Schema v0.4 metadata and source alignment |
| `scripts/verify-palomar.sh` | Local compilation, declaration, axiom, and comparator checks |
| `M4_AUDIT.md` | Claim-by-claim evidence and exact binders |

The toolchain is Lean **v4.35.0-rc2**, pinned in `lean-toolchain`, with Mathlib
**v4.35.0-rc2**, pinned in `lakefile.toml` and resolved in `lake-manifest.json`.
Run from the repository root:

```bash
scripts/verify-palomar.sh
```

The script configures the pinned Lean environment and compiles the process shim
needed in the managed namespace. It runs `lake build`, builds Challenge and
Solution, checks every comparator declaration's presence and kind in both
separate module environments, checks proof tokens and axioms throughout the
library, and runs `lake comparator --config=comparator.json --inadvisably-no-sandbox`.
It also verifies Challenge's import surface and runs `git diff --check`.
Challenge can be built independently with `lake build Challenge` in the same
configured environment. The structure is copied verbatim into Challenge and
excluded from `definition_names`, which contains genuine definitions only.
Challenge and Solution are compiled separately because their fully qualified
statement names coincide.

The reported Palomar registry API search on **2026-09-29** for `minimax`
returned zero entries. The M1 survey found no finite zero-sum game specialization
in the pinned Mathlib; its general Sion theorem is the proof ingredient here.
These are limited, dated prior-art observations. [M4_AUDIT.md](M4_AUDIT.md)
records their provenance and the prose-versus-artifact checks.

Author and responsible maintainer: **Arthur Freitas Ramos**. License:
[BSD-3-Clause](LICENSE). Acknowledgements: Mathlib contributors and John von Neumann.
AI assistance was used for formalization and packaging. M4 performs no Palomar
submission or registration; packaging changes are left uncommitted for review.
