# Backlog

Work that is **not** the active focus, kept here so it isn't forgotten.

> Active focus: **Erdős #42** — see `Erdos/P42/`. P283 + #351 shipped axiom-free
> via the formalized RSG theorem; Route B of #42 is now also fully axiom-free
> after the compact-Cayley axiom was discharged.

## Currently active

### Erdős #42 — Sidon difference avoidance
- **Status**: in progress (`Erdos/P42/`). Two parallel routes.
- **Route B (compact-Cayley) — axiom-free.** The compact-Cayley clique theorem
  (compact PDF Theorem 2.1) is now proved end-to-end. `compact_cayley_clique`
  and `theorem_1_1_from_compact_cayley` depend only on Mathlib core
  (`propext`, `Classical.choice`, `Quot.sound`). Independently confirmed by
  SafeVerify against the flat bundle `CompactCayley/Proof.lean` (49 spec
  declarations, 1140 in submission, no extra allowed axiom).
- **Route A (Fourier-positive, active public wrapper).** Drives `theorem_1_1`
  and `erdos_42` over `Set ℕ`. Conditional on
  `finite_fourier_avoidance_count` (Green-Tao `U²` regularity / complexity-1
  counting). Existence interface used downstream is derived from the count
  statement. Confirmed by SafeVerify under the count-axiom allow-list.
- **Remaining work for axiom-free Route A**: prove
  `finite_fourier_avoidance_count` from the compact extraction-dual model
  scaffolding already in place (see `FourierPositive/CompactDual.lean`,
  `CompactModel.lean`, `Counterexample.lean`).

### Erdős #43 — Sharp asymptotic Sidon-pair bound
- **Status**: scaffolded (`Erdos/P43/`), bodies still `sorry`.
- First half (asymptotic upper bound) ← negative answer follows from #42 by
  Tao's argument; can be derived directly from `Erdos.P42.theorem_1_1`.
- Second half (equal-cardinality strengthening) ← Bose-Chowla parity
  construction (Section 4 of `Erdos/P42/docs/combined_42_43_proof.pdf`).
- Live #43 thread reports an Aristotle/Harmonic Lean formalization of the
  Erdős-Turán bound + Bose-Chowla; option to port that for the second half.

## Mathlib upstream PRs

### PR #1: cycle-reduction lemma (extracted from P750)
- **Target file**: `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` (fills the explicit `TODO` at line 61).
- **Source**: `Erdos/P750/Proof.lean` lines ~700–980 (`exists_isCycle_of_odd_closedWalk` and supporting lemmas).
- **Already proved** axiom-free; just needs Mathlib-style polish, naming convention pass, and possibly the `cycleGraph (2n+1)`-shape iff version that the TODO comment expects.
- Effort: 1–3 days.
- Payoff: closes a known Mathlib gap; once merged, our P750 can drop the inline lemma and `import` it.

### PR #2: Mertens product theorem
- **Target file**: probably `Mathlib/NumberTheory/Mertens.lean` (new file).
- **Source**: nothing yet — would need a from-scratch proof.
- **Statement**: `∏_{p ≤ y} (1 - 1/p)⁻¹ ~ e^γ · log y`.
- Mathlib has the surrounding scaffolding (`eulerMascheroniConstant`, `Tendsto (harmonic n - log n) → γ`, `EulerProduct.{Basic,ExpLog,DirichletLSeries}`, `Primorial`).
- Classical Mertens (1874) — proof goes via either the elementary Chebyshev-Mertens argument or the integration-by-parts on `log ζ`.
- Effort: weeks.
- Payoff: drops `mertens_product` axiom from P694 → trust boundary becomes just `linnik_dvd`.

### PR #3 (stretch): Green-Tao `U²` complexity-1 counting + arithmetic regularity
- Would discharge `finite_fourier_avoidance_count` and make Route A of P42
  axiom-free, matching the already-axiom-free Route B.
- Compact-extraction scaffolding for this is partially in place under
  `Erdos/P42/FourierPositive/{CompactDual,CompactModel,Counterexample,Counting,Fejer,LargeSpectrum,Limit,TrigPolynomial}.lean`;
  remaining gap is constructing the extraction-dual model and proving the
  level-one subgroup is null / infinite-index (see `FourierPositive/Main.lean`).
- Effort: weeks-to-months.

### PR #4 (already shipped): Roth-Szekeres-Graham / Graham complete polynomial sequences
- Closed: `Erdos/P283/RSG/` formalizes Graham 1964 axiom-free.
- P283 + #351 are now Mathlib-core-only.

## Earlier polynomial-Egyptian-fraction work (Woett, August 2025)

`arXiv:2502.02200` — *The binomial case of Graham's conjecture on polynomial representations with prescribed sum of reciprocals*. Reduces the conjecture for `p(x) = a x^d + b` to a finite search.

Aristotle Lean autoformalization of the related `n_{α,m}` asymptotic: `github.com/Woett/Lean-files/blob/main/ExplicitGraham.lean` (~4000 lines, off-topic from current proof but parts may be reusable).

**On hold**: not needed for the May 2026 Liam Price + GPT-5.5 Pro full proof we're formalizing. Useful if we later want to formalize the explicit-bound improvements.

## Croot's solutions to #284, #286

Cited in the May 2026 #283 proof but not formalized by it. Already in the literature; no scaffold needed unless someone wants a self-contained Mathlib copy.

## Ideas / parking lot

- **Live-link CDN cache busting**: when pushing changes to `Proof.lean` files, recommend the SHA-pinned URL form to defeat `raw.githubusercontent.com` caching.
- **`Type` vs `Type*` cosmetic gap**: the `erdos_750_FC` form differs from the literal FC syntax by a universe-binder convention because of `autoImplicit = false` in our `lakefile.toml`. ULift bridge is ~50–100 lines if we ever want bit-for-bit FC matching.
