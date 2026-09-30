# M4 prose-versus-artifact audit

Audited on 2026-09-30 against the finished library, the rewritten README,
and formalization.yaml. Every model or theorem claim below points to its Lean
declaration and quotes its binders. Historical, toolchain, licensing, search,
and administrative claims have separate non-Lean provenance: Lean declarations
do not establish those facts. Repeated claims in different metadata fields
use the same evidence catalogue.

## C1: exact model and quantification

[Minimax/Basic.lean:20](Minimax/Basic.lean#L20):

```lean
structure MixedStrategy (A : Type*) [Fintype A] [Nonempty A] where
  val : A → ℝ
  nonneg : ∀ a, 0 ≤ val a
  sum_one : ∑ a, val a = 1
```

Finite means `[Fintype A]` / `[Fintype B]`; nonempty means `[Nonempty A]` /
`[Nonempty B]`. These constrain pure-strategy types, not the cardinality of
the mixed-strategy simplices. The payoff binder is `(u : A → B → ℝ)`, so
payoffs are arbitrary real numbers. Nonnegative probability coordinates and
mass one are the exact fields above. There are two strategy arguments, one
for each player. The zero-sum description is the interpretation of maximizing
one payoff while the opponent minimizes it (payoffs `u` and `-u`); there is
no Lean record storing two payoffs or an extra zero-sum hypothesis.

## C2: definitions, player orientation, linearity, and bounds

[Minimax/Basic.lean:97](Minimax/Basic.lean#L97): `Minimax.expPayoff` has binders
`{A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (u : A → B → ℝ) (x : MixedStrategy A) (y : MixedStrategy B)` and result `ℝ`.

[Minimax/Basic.lean:260](Minimax/Basic.lean#L260): `Minimax.maxminValue` has binders
`{A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (u : A → B → ℝ)` and result `ℝ`.

[Minimax/Basic.lean:264](Minimax/Basic.lean#L264): `Minimax.minmaxValue` has binders
`{A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (u : A → B → ℝ)` and result `ℝ`.

The bodies, copied from Basic.lean, are:

```lean
expPayoff u x y = ∑ a, ∑ b, x.val a * y.val b * u a b
maxminValue u = ⨆ x : MixedStrategy A, ⨅ y : MixedStrategy B, expPayoff u x y
minmaxValue u = ⨅ y : MixedStrategy B, ⨆ x : MixedStrategy A, expPayoff u x y
```

The supremum over `x : MixedStrategy A` is the maximizing player and the
infimum over `y : MixedStrategy B` is the minimizing player. Each inequality
in the prose follows this orientation, without reversing quantifiers.
`weightedPayoff`, its four additivity/homogeneity lemmas, both mixed-strategy
linearity lemmas, and the explicit payoff/value bounds have the exact
`#check @Minimax.<name>` signatures quoted in C5 below. In particular,
`weightedPayoff` and `payoffBound` need only the two Fintype instances;
the bounds need both Nonempty instances too. The mixed-strategy structure
is not a vector space; the bilinear form is on unrestricted real vectors,
while its restrictions to simplices are affine.

[Minimax/Basic.lean:187](Minimax/Basic.lean#L187):
`Minimax.payoffBound {A B : Type*} [Fintype A] [Fintype B]
(u : A → B → ℝ) : ℝ := ∑ a, ∑ b, |u a b|`.
The C5 bound statements have the correct directions
`-payoffBound u ≤ ... ∧ ... ≤ payoffBound u`.
The C5 `MixedStrategy.instNonempty` establishes nonempty indexing types;
`bddBelow_payoff_left/right`, `bddAbove_payoff_left/right`,
`bddBelow_iInf_payoff`, `bddAbove_iInf_payoff`, `bddBelow_iSup_payoff`, and
`bddAbove_iSup_payoff` in Basic.lean establish the bounds for the inner and
outer extrema. These have the C2 common binders and `(u : A → B → ℝ)`;
the payoff-left lemmas additionally take `(y : MixedStrategy B)`, and
payoff-right lemmas take `(x : MixedStrategy A)`.

## C3: all advertised statements and hypothesis directions

[Minimax/EasyDirection.lean:15](Minimax/EasyDirection.lean#L15) and [Solution.lean:7](Solution.lean#L7):

```lean
Minimax.maxmin_le_minmax
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : maxminValue u ≤ minmaxValue u
Minimax.Palomar.maxmin_le_minmax
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : maxminValue u ≤ minmaxValue u
```

Solution's proof is `exact Minimax.maxmin_le_minmax u`. Challenge has the same
statement under `Minimax.Palomar` with one deliberate placeholder.

[Minimax/HardDirection.lean:115](Minimax/HardDirection.lean#L115) and [Solution.lean:11](Solution.lean#L11):

```lean
Minimax.minmax_le_maxmin
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : minmaxValue u ≤ maxminValue u
Minimax.Palomar.minmax_le_maxmin
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : minmaxValue u ≤ maxminValue u
```

Solution's proof is `exact Minimax.minmax_le_maxmin u`. Challenge has the same
statement under `Minimax.Palomar` with one deliberate placeholder.

[Minimax/HardDirection.lean:126](Minimax/HardDirection.lean#L126) and [Solution.lean:15](Solution.lean#L15):

```lean
Minimax.minimax_theorem
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : maxminValue u = minmaxValue u
Minimax.Palomar.minimax_theorem
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) : maxminValue u = minmaxValue u
```

Solution's proof is `exact Minimax.minimax_theorem u`. Challenge has the same
statement under `Minimax.Palomar` with one deliberate placeholder.

These are the only three advertised Solution results. There is no extra
continuity, regularity, boundedness, positivity, or rational-payoff hypothesis
on `u`. The easy proof uses conditional infimum/supremum inequalities. The
reverse proof has `minmaxValue u ≤ expPayoff u x y ≤ maxminValue u`; the
library equality proof uses `le_antisymm` in that order.

## C4: the Sion proof route and its precise scope

[Minimax/HardDirection.lean:98](Minimax/HardDirection.lean#L98):

```lean
Minimax.exists_payoff_saddle
  {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  (u : A → B → ℝ) :
  ∃ x : MixedStrategy A, ∃ y : MixedStrategy B,
    ∀ x' : MixedStrategy A, ∀ y' : MixedStrategy B,
      expPayoff u x' y ≤ expPayoff u x y'
```

The proof applies `Sion.exists_isSaddlePointOn`
(in `.lake/packages/mathlib/Mathlib/Topology/Sion.lean`) with
`f := fun y x => weightedPayoff u x y`, obtaining `y` on the B simplex
first and `x` on the A simplex second. The two section-continuity lemmas
and simplex nonemptiness, convexity, and compactness lemmas have the C5
exact binders. Sion is a proved Mathlib ingredient, not an additional axiom.
This is a finite-game specialization of Sion, not the original 1928 proof.
The advertised results quantify two finite pure-strategy types, so the prose
excludes infinite pure-strategy sets and general n-player games. They do not
assert or formalize Nash's general equilibrium existence theorem.

## C5: additional signatures checked by Lean

These are the actual outputs of `#check @Minimax.<name>` and the library
`#print axioms` calls in a temporary file importing only Minimax:

```text
@Minimax.weightedPayoff : {A : Type u_1} →
  {B : Type u_2} → [Fintype A] → [Fintype B] → (A → B → ℝ) → (A → ℝ) → (B → ℝ) → ℝ
@Minimax.weightedPayoff_add_left : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  (u : A → B → ℝ) (x z : A → ℝ) (y : B → ℝ),
  Minimax.weightedPayoff u (x + z) y = Minimax.weightedPayoff u x y + Minimax.weightedPayoff u z y
@Minimax.weightedPayoff_smul_left : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  (u : A → B → ℝ) (c : ℝ) (x : A → ℝ) (y : B → ℝ), Minimax.weightedPayoff u (c • x) y = c * Minimax.weightedPayoff u x y
@Minimax.weightedPayoff_add_right : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  (u : A → B → ℝ) (x : A → ℝ) (y z : B → ℝ),
  Minimax.weightedPayoff u x (y + z) = Minimax.weightedPayoff u x y + Minimax.weightedPayoff u x z
@Minimax.weightedPayoff_smul_right : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  (u : A → B → ℝ) (c : ℝ) (x : A → ℝ) (y : B → ℝ), Minimax.weightedPayoff u x (c • y) = c * Minimax.weightedPayoff u x y
@Minimax.expPayoff_linear_left : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  [inst_2 : Nonempty A] [inst_3 : Nonempty B] (u : A → B → ℝ) (x z w : Minimax.MixedStrategy A)
  (y : Minimax.MixedStrategy B) (p q : ℝ),
  (∀ (a : A), w.val a = p * x.val a + q * z.val a) →
    Minimax.expPayoff u w y = p * Minimax.expPayoff u x y + q * Minimax.expPayoff u z y
@Minimax.expPayoff_linear_right : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  [inst_2 : Nonempty A] [inst_3 : Nonempty B] (u : A → B → ℝ) (x : Minimax.MixedStrategy A)
  (y z w : Minimax.MixedStrategy B) (p q : ℝ),
  (∀ (b : B), w.val b = p * y.val b + q * z.val b) →
    Minimax.expPayoff u x w = p * Minimax.expPayoff u x y + q * Minimax.expPayoff u x z
@Minimax.payoffBound : {A : Type u_1} → {B : Type u_2} → [Fintype A] → [Fintype B] → (A → B → ℝ) → ℝ
@Minimax.expPayoff_bounds : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  [inst_2 : Nonempty A] [inst_3 : Nonempty B] (u : A → B → ℝ) (x : Minimax.MixedStrategy A)
  (y : Minimax.MixedStrategy B),
  -Minimax.payoffBound u ≤ Minimax.expPayoff u x y ∧ Minimax.expPayoff u x y ≤ Minimax.payoffBound u
@Minimax.maxminValue_bounds : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  [inst_2 : Nonempty A] [inst_3 : Nonempty B] (u : A → B → ℝ),
  -Minimax.payoffBound u ≤ Minimax.maxminValue u ∧ Minimax.maxminValue u ≤ Minimax.payoffBound u
@Minimax.minmaxValue_bounds : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  [inst_2 : Nonempty A] [inst_3 : Nonempty B] (u : A → B → ℝ),
  -Minimax.payoffBound u ≤ Minimax.minmaxValue u ∧ Minimax.minmaxValue u ≤ Minimax.payoffBound u
@Minimax.MixedStrategy.instNonempty : ∀ {A : Type u_1} [inst : Fintype A] [inst_1 : Nonempty A],
  Nonempty (Minimax.MixedStrategy A)
Minimax.coordSimplex : (S : Type u_1) → [Fintype S] → [Nonempty S] → Set (S → ℝ)
@Minimax.coordSimplex_nonempty : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S],
  (Minimax.coordSimplex S).Nonempty
@Minimax.convex_coordSimplex : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S],
  Convex ℝ (Minimax.coordSimplex S)
@Minimax.isCompact_coordSimplex : ∀ {S : Type u_1} [inst : Fintype S] [inst_1 : Nonempty S],
  IsCompact (Minimax.coordSimplex S)
@Minimax.continuous_weightedPayoff_left : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  (u : A → B → ℝ) (y : B → ℝ), Continuous fun x => Minimax.weightedPayoff u x y
@Minimax.continuous_weightedPayoff_right : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  (u : A → B → ℝ) (x : A → ℝ), Continuous fun y => Minimax.weightedPayoff u x y
@Minimax.exists_payoff_saddle : ∀ {A : Type u_1} {B : Type u_2} [inst : Fintype A] [inst_1 : Fintype B]
  [inst_2 : Nonempty A] [inst_3 : Nonempty B] (u : A → B → ℝ),
  ∃ x y,
    ∀ (x' : Minimax.MixedStrategy A) (y' : Minimax.MixedStrategy B), Minimax.expPayoff u x' y ≤ Minimax.expPayoff u x y'
'Minimax.maxmin_le_minmax' depends on axioms: [propext, Classical.choice, Quot.sound]
'Minimax.minmax_le_maxmin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Minimax.minimax_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Q1 (resolved): module migration and full verification

The module-format conflict is resolved. The four library files were given
`module` headers, `public import` dependencies, `public` visibility on all
sixty exported declarations (the two `private noncomputable def` unfolding
helpers in HardDirection.lean stay private), and `@[expose]` on all ten
public `def`s, mirroring the proven Bulow-Klemperer layout. No theorem body,
statement, or binder changed; `git diff` on the library shows only header,
visibility, and exposure lines.

After the migration, scripts/verify-palomar.sh passes end to end with exit 0:
`lake build` succeeds, `lake comparator` prints "Your solution is okay!",
the Lean default kernel accepts the solution, all 91 Minimax declarations
use only the permitted axioms, and the three Solution theorems each depend
only on `propext`, `Classical.choice`, and `Quot.sound`. A forced recompile
of all six project modules shows zero warnings and zero deprecations.

## Q0: proof integrity and packaging evidence (supersedes the earlier Q1 draft)

The source-token scan reports zero `sorry`, `admit`, `axiom`, or `unsafe`
in Minimax.lean, Minimax/*.lean, and Solution.lean. Challenge has exactly
six `sorry` tokens and no other forbidden tokens. The structure, including
its docstring, matches the Basic.lean substring byte-for-byte. The three
library theorem axiom reports are in C5 and show exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The Challenge-only check compiled `#check` for all six comparator names and
inspected declaration kinds: the three definitions are `.defnInfo` and the
three theorems are `.thmInfo`. MixedStrategy is a structure and is excluded
from definition_names. `lake build Challenge` exited 0 without warnings.
Its direct imports are only the two Mathlib modules shown in Challenge.lean;
`lake env lean --src-deps Challenge.lean` also completed successfully.
`moreLeanArgs = ["-Dwarn.sorry=false"]` belongs only to the Challenge
lean_lib target in lakefile.toml, suppressing its deliberate placeholder
warnings without suppressing warnings in the proof library or Solution.

The verifier is adapted from the passing BK script. The required files,
module list, declaration names, six-placeholder count, and all-axiom namespace
prefix were changed to Minimax. It also checks Challenge's direct imports
against a Lean/Mathlib-only allowlist. The BK module-header check is retained for every listed module;
the four protected legacy files therefore fail that prerequisite. All BK
checks remain in place, including the official `lake comparator` invocation.

Historical note, superseded by Q1 (resolved) above: the Codex packaging run
hit `cannot import non-'module' Minimax from 'module'` because the four
library files still used the legacy import style. The required mechanical
migration (module headers, `public import`, `public` declarations, `@[expose]`
on defs) has since been applied as the smallest possible change; theorem
bodies, statements, and binders are untouched, and the full verifier now
passes end to end.

## P1: history and prior-art provenance

The original article's title, author, journal, volume, pages, and 1928 date
are confirmed by the [publisher record](https://link.springer.com/article/10.1007/BF01448847).
The research-interest description refers to the established mathematical
importance of this statement, not additional Lean results. Nash's equilibrium
existence builds on the mixed-strategy solution concept historically;
it is not asserted to follow logically from the minimax theorem. The
[Santa Fe Institute historical account](https://www.sfipress.org/12-nash-1951)
explains the extension from two-person zero-sum minimax to Nash's general
setting. These external historical facts have no Lean binders.

The dated 2026-09-29 API search for `minimax` returning zero Palomar entries
was supplied by the user as M4 packaging evidence. It was not rerun here and
is described as reported, not as a universal absence of prior formalizations.
`related_formalizations: []` records that limited known registry evidence.
The M1 local survey is recorded in M1_SUMMARY.md and M1_NOTES.md, against
Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The packaging
source search found Sion's general minimax and saddle-point declarations and
its TODO to spell out the von Neumann specialization. Thus the claim is
restricted to no finite zero-sum game specialization found in that pinned
checkout; it does not claim Mathlib lacks general minimax theorems.

## P2: nonmathematical metadata provenance

| Claim | Evidence |
| --- | --- |
| Lean v4.35.0-rc2 | lean-toolchain: `leanprover/lean4:v4.35.0-rc2`; `lake --version` reports Lean version 4.35.0-rc2 |
| Mathlib v4.35.0-rc2 | lakefile.toml `rev = "v4.35.0-rc2"`; lake-manifest.json inputRev and resolved commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Schema v0.4 | `version: "v0.4"`; metadata validated with jsonschema against the official v0.4 schema fetched through the web tool |
| Project name, Arthur Freitas Ramos, maintainership | Explicit user-provided packaging metadata |
| BSD-3-Clause | Repository LICENSE text and copyright attribution |
| Article relationship and not-contacted endorsement | User-directed source attribution; formal statement C3 and proof route C4 |
| cs.GT and math.OC | User-directed classification of the game-theory/optimization statement C3 |
| GPT-6.1 via Codex; subscription-based; AI assistance | User-provided automation attribution and billing description |
| Wall time not tracked; local machine | No formalization duration accounting; local workspace compilation |
| Self-assessed; no reviewers | This local packaging audit; no independent registry review performed |
| No submission or registration; uncommitted changes | M4 user scope and actions performed in this session; git status/diff |
| Acknowledgements | Deliberate attribution to Mathlib contributors and John von Neumann, justified by C4/P1 |

Versions, authors, cost, license, and review state are not theorem hypotheses.
No Lean declaration is presented as proving these administrative facts.

## P3: packaging and verifier claims

The README layout table points to the actual files and the C1-C4 declarations.
Minimax.lean imports Basic, EasyDirection, and HardDirection. Challenge's
statement declarations and Solution's proof declarations use the same fully
qualified comparator names in separate environments. Challenge imports only
Mathlib; Solution imports only Minimax and never Challenge. comparator.json
lists the exact three definitions from C2, three theorems from C3, and
three permitted axioms from C5. lakefile.toml adds both packaging lean_lib
targets and defaultTargets `["Minimax", "Challenge", "Solution"]`.

README's run commands are literal commands in scripts/verify-palomar.sh.
Its environment setup and C shim are copied from BK. The script implements
file/header/token checks, Challenge import checks, separate declaration-kind
checks, library-wide axiom checks, `lake comparator`, and `git diff --check`.
These are descriptions of checks implemented; the Q1 (resolved) section above
records that the module migration is complete and the full comparator stage
now passes.

## Complete prose coverage

| README claim group | Evidence with quoted binders above |
| --- | --- |
| Introductory equality, finite, nonempty, two-player, real payoff, zero-sum interpretation | C1-C3 |
| Source bibliography, historical significance and Nash context | P1; formalized scope C3 |
| Probability-vector fields | C1 |
| Three definition signatures, formulas and sup/inf player orientation | C2 |
| Bilinear extension, affine restrictions, bound, nonempty bounded ranges | C2/C5 |
| All three Solution statements and their proofs | C3 |
| Easy conditional-order proof; compact convex nonempty simplices; continuity/affinity | C3-C5 |
| Sion application, minimizing player first, exact saddle conclusion and value bridge | C4/C5 |
| Antisymmetry, original proof divergence, excluded infinite and n-player cases | C3/C4 |
| Zero library placeholders, exactly six Challenge holes, allowed axioms, warning scope | Q1/C5 |
| Every row of the file layout table | P3/C1-C4 |
| Versions, build/run commands, environment shim, declarations/kinds/imports/comparator | P2/P3/Q1 |
| Structure copy, genuine defs, separate global declaration environments | Q1/P3 |
| Dated registry search and M1 survey | P1 |
| Author, license, acknowledgements, AI assistance, no submission/registration or commit | P2 |

| formalization.yaml field (all leaves) | Evidence |
| --- | --- |
| `version` | P2 |
| `project.name` | P2 |
| `project.description` | C1-C4, P1 |
| `project.authors[0]` | P2 |
| `project.responsible_maintainers[0]` | P2 |
| `project.license` | P2 |
| `sources[0].title` | P1/P2 |
| `sources[0].authors[0]` | P1/P2 |
| `sources[0].type` | P1/P2 |
| `sources[0].location` | P1/P2 |
| `sources[0].relationship` | C1-C4, P1/P2 |
| `sources[0].author_endorsement` | P1/P2 |
| `sources[0].note` | C1-C4, P1/P2 |
| `related_formalizations` | P1 |
| `classification.arxiv[0]` | P2 |
| `classification.arxiv[1]` | P2 |
| `status.scope` | C1-C4, Q1, P1 |
| `status.sorry_count` | C5/Q1 |
| `status.sorry_in_definitions` | C5/Q1 |
| `status.axioms[0]` | C5/Q1 |
| `status.axioms[1]` | C5/Q1 |
| `status.axioms[2]` | C5/Q1 |
| `status.main_results[0].declaration` | C3/C5, Q1/P3 |
| `status.main_results[0].file` | C3/C5, Q1/P3 |
| `status.main_results[0].description` | C3/C5, Q1/P3 |
| `status.main_results[0].sorry_count` | C3/C5, Q1/P3 |
| `status.main_results[0].axioms[0]` | C3/C5, Q1/P3 |
| `status.main_results[0].axioms[1]` | C3/C5, Q1/P3 |
| `status.main_results[0].axioms[2]` | C3/C5, Q1/P3 |
| `status.main_results[0].comparator_config` | C3/C5, Q1/P3 |
| `status.main_results[1].declaration` | C3/C5, Q1/P3 |
| `status.main_results[1].file` | C3/C5, Q1/P3 |
| `status.main_results[1].description` | C3/C5, Q1/P3 |
| `status.main_results[1].sorry_count` | C3/C5, Q1/P3 |
| `status.main_results[1].axioms[0]` | C3/C5, Q1/P3 |
| `status.main_results[1].axioms[1]` | C3/C5, Q1/P3 |
| `status.main_results[1].axioms[2]` | C3/C5, Q1/P3 |
| `status.main_results[1].comparator_config` | C3/C5, Q1/P3 |
| `status.main_results[2].declaration` | C3/C5, Q1/P3 |
| `status.main_results[2].file` | C3/C5, Q1/P3 |
| `status.main_results[2].description` | C3/C5, Q1/P3 |
| `status.main_results[2].sorry_count` | C3/C5, Q1/P3 |
| `status.main_results[2].axioms[0]` | C3/C5, Q1/P3 |
| `status.main_results[2].axioms[1]` | C3/C5, Q1/P3 |
| `status.main_results[2].axioms[2]` | C3/C5, Q1/P3 |
| `status.main_results[2].comparator_config` | C3/C5, Q1/P3 |
| `automation.methods[0].method` | P2/P3, Q1 |
| `automation.methods[0].models[0]` | P2/P3, Q1 |
| `automation.methods[0].framework` | P2/P3, Q1 |
| `automation.methods[0].tool_setup` | P2/P3, Q1 |
| `automation.methods[0].cost.wall_time` | P2/P3, Q1 |
| `automation.methods[0].cost.spend_usd` | P2/P3, Q1 |
| `automation.methods[0].cost.hardware` | P2/P3, Q1 |
| `automation.methods[0].prompting_notes` | P2/P3, Q1 |
| `automation.spend_usd` | P2/P3, Q1 |
| `automation.notes` | P2/P3, Q1 |
| `fidelity.divergences` | C1-C5 |
| `alignment.namespace` | C1-C4, P3 |
| `alignment.statements[0].source` | C1-C4, P3 |
| `alignment.statements[0].lean` | C1-C4, P3 |
| `alignment.statements[0].module` | C1-C4, P3 |
| `alignment.statements[0].status` | C1-C4, P3 |
| `alignment.statements[0].note` | C1-C4, P3 |
| `alignment.statements[1].source` | C1-C4, P3 |
| `alignment.statements[1].lean` | C1-C4, P3 |
| `alignment.statements[1].module` | C1-C4, P3 |
| `alignment.statements[1].status` | C1-C4, P3 |
| `alignment.statements[1].note` | C1-C4, P3 |
| `alignment.statements[2].source` | C1-C4, P3 |
| `alignment.statements[2].lean` | C1-C4, P3 |
| `alignment.statements[2].module` | C1-C4, P3 |
| `alignment.statements[2].status` | C1-C4, P3 |
| `alignment.statements[2].note` | C1-C4, P3 |
| `alignment.statements[3].source` | C1-C4, P3 |
| `alignment.statements[3].lean` | C1-C4, P3 |
| `alignment.statements[3].module` | C1-C4, P3 |
| `alignment.statements[3].status` | C1-C4, P3 |
| `alignment.statements[3].note` | C1-C4, P3 |
| `review.status` | Q1, P2/P3 |
| `review.reviewers[0]` | Q1, P2/P3 |
| `review.notes` | Q1, P2/P3 |
| `acknowledgements` | P2 |

The audit rewrote the scaffold status from the final artifact, described
bilinearity on unrestricted vectors, kept the zero-sum interpretation explicit,
quoted every theorem binder, and limited historical/search claims to their
stated evidence. The module migration described in Q1 (resolved) is the only
structural change since the Codex packaging run; no mathematical hypothesis
or direction changed.
