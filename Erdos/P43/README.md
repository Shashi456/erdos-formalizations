# Erdős Problem 43 — Sidon difference avoidance (equal-cardinality)

> [erdosproblems.com/43](https://www.erdosproblems.com/43)
>
> ⚠️ **Scaffold only.** All theorem bodies are `sorry`.

For all sufficiently large `N`, do there exist Sidon `A, B ⊆ {1, …, N}` with
`(A − A) ∩ (B − B) = {0}` such that `binomial(|A|, 2) + binomial(|B|, 2)` is
"close to" `binomial(f(N), 2)`?

The combined writeup `Erdos/P42/combined_42_43_proof.pdf` answers both
sub-parts: the first part is a direct corollary of #42 (Tao's first remark on
the #42 thread); the second part follows from a Bose-Chowla parity
construction.

## Files

| File | Status |
|------|--------|
| [`Common.lean`](Common.lean) | `sidonNumber` definition |
| [`FirstPartFromP42.lean`](FirstPartFromP42.lean) | `sorry` — depends on #42 |
| [`BoseChowlaParity.lean`](BoseChowlaParity.lean) | `sorry` — combined PDF §4 / Aristotle/Harmonic Lean port |
| [`FC/Local.lean`](FC/Local.lean) | placeholder `True := trivial` |
| [`Proof.lean`](Proof.lean) | umbrella |

## Plan

1. **First half** depends on #42 (`Erdos.P42.FC.Local.theorem_1_1`); once #42
   is proved (Route A or Route B), the corollary is short.
2. **Second half** can either port the existing Aristotle/Harmonic
   formalization mentioned on the live #43 thread, or develop the Bose-Chowla
   parity construction in-house.
3. The FC wrapper bundles both into the upstream
   [`FormalConjectures/ErdosProblems/43.lean`] iff form.
