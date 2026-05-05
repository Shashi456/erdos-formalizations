# Backlog

Work that is **not** the active focus, kept here so it isn't forgotten.

> Active focus: **Erdős #283 + #351** — see `Erdos/P283/`. Everything below is on hold until that ships.

## Adjacent Erdős problems we could pick up later

### Erdős #42 — Sidon difference avoidance
- **Status**: scaffolded (`Erdos/P42/`), not in progress.
- All three proof PDFs (`proof.pdf`, `proof_combined_42_43.pdf`, `proof_ulam_note.pdf`), forum thread snapshot, informal outline, and Lean stub are in place.
- Trust-boundary axioms identified: `complexity_one_counting_lemma` (Green-Tao 2008), `compact_U2_regularity_subsequential_limit` (classical compactness packaging).
- 3-layer structure: Tao's continuous-version key lemma → finite avoidance lemma → Erdős statement.
- Estimated effort to complete: ~500–1000 lines of Lean.

### Erdős #43 — Sharp asymptotic Sidon-pair bound
- **Status**: not scaffolded.
- Closed by the *same proof file* as #42 (`Erdos/P42/proof_combined_42_43.pdf`):
  - First half (asymptotic upper bound) ← negative answer follows from #42 by Tao's argument.
  - Second half (equal-cardinality strengthening) ← Bose-Chowla parity construction by Kevin Barreto.
- **Reason on hold**: `BryanKim` is the listed formalization volunteer on the forum (`I am working on formalising the results on this problem`), and FC has no skeleton yet (404 on `FormalConjectures/ErdosProblems/43.lean`). Don't duplicate.
- If we revisit: the first half can be derived from our `theorem_1_1` in `Erdos/P42/Proof.lean`; second half is ~50-line independent argument.

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

### PR #3 (stretch): Green-Tao `U²` complexity-1 counting lemma
- Would unblock half of P42's trust boundary (`complexity_one_counting_lemma`).
- Effort: months. Out of scope unless we make P42 a flagship project.

### PR #4 (stretch): `U²` arithmetic regularity packaging
- Would unblock the other half of P42's trust boundary.
- Effort: months.

## Earlier polynomial-Egyptian-fraction work (Woett, August 2025)

`arXiv:2502.02200` — *The binomial case of Graham's conjecture on polynomial representations with prescribed sum of reciprocals*. Reduces the conjecture for `p(x) = a x^d + b` to a finite search.

Aristotle Lean autoformalization of the related `n_{α,m}` asymptotic: `github.com/Woett/Lean-files/blob/main/ExplicitGraham.lean` (~4000 lines, off-topic from current proof but parts may be reusable).

**On hold**: not needed for the May 2026 Liam Price + GPT-5.5 Pro full proof we're formalizing. Useful if we later want to formalize the explicit-bound improvements.

## Croot's solutions to #284, #286

Cited in the May 2026 #283 proof but not formalized by it. Already in the literature; no scaffold needed unless someone wants a self-contained Mathlib copy.

## Ideas / parking lot

- **Live-link CDN cache busting**: when pushing changes to `Proof.lean` files, recommend the SHA-pinned URL form to defeat `raw.githubusercontent.com` caching.
- **`Type` vs `Type*` cosmetic gap**: the `erdos_750_FC` form differs from the literal FC syntax by a universe-binder convention because of `autoImplicit = false` in our `lakefile.toml`. ULift bridge is ~50–100 lines if we ever want bit-for-bit FC matching.
