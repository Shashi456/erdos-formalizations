# Erdős Problem 694 — Totient fibre extremes

> [erdosproblems.com/694](https://www.erdosproblems.com/694)

Let `f_max(n)` and `f_min(n)` be the largest / smallest positive `m` with
`φ(m) = n`. Define
```
R(x) := max_{n ≤ x, n ∈ φ(ℕ)} f_max(n) / f_min(n).
```
**Theorem (PDF Theorem 2.1).** `R(x) = (e^γ + o(1)) log log x`.

## Files

| File | What |
|------|------|
| [`Proof.lean`](Proof.lean) | The full Lean 4 / Mathlib formalization. Single `Erdos694` namespace, `import Mathlib`, ~2,800 lines. |
| [`proof.pdf`](proof.pdf) | The original informal proof (Liam Price + GPT-5.5 Pro). |
| [`informal.md`](informal.md) | Human-readable proof outline / strategy notes. |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P694.Proof
```

**Online (no Lake required):** open
[live.lean-lang.org](https://live.lean-lang.org/), paste the contents of
`Proof.lean`, wait for the build. Tested on Lean / Mathlib `v4.27.0` and
`v4.28.0`.

## Trust boundary

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Extra axioms |
|---|---|
| `totient_sq_ge_half`, `permanence_step`, `infinitely_many_collisions`, `LowerConstruction.totient_a_eq_totient_b` | none |
| `landau_max_ratio`, `R_upper_bound`, `collision_at_height` | `mertens_product` |
| `totient_collision_construction`, `R_lower_bound`, `totient_fibre_extremes`, `erdos_694_asymptotic` | `mertens_product`, `linnik_dvd` |

`mertens_product` is Mertens' product theorem (1874).
`linnik_dvd` is Linnik's theorem (1944) in divisibility form. Both are
classical, unconditional results; Mathlib has surrounding infrastructure but
not these named statements yet.

The audit block at the bottom of `Proof.lean` (`#print axioms …`) reproduces
this table at build time.

## Relationship to `formal-conjectures`

Upstream [`FormalConjectures/ErdosProblems/694.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/694.lean)
states `erdos_694` in the shape

```lean
IsGreatest { (max n : ℚ) / min n | n ≤ x } answer(sorry) := by sorry
```

— the FC repo's standard exact-value template. For an asymptotic problem this
template can only be filled tautologically; the substantive `(e^γ + o(1)) log
log x` answer naturally lives in a `Tendsto` shape, which is what we prove
(`Erdos694.erdos_694_asymptotic`). If/when the upstream repo retemplates to
`Tendsto`-form (as already happens for other asymptotic FC entries), this
companion theorem becomes the proof.

## Source

Proof by Liam Price + GPT-5.5 Pro, May 2026. Formalization assembled
incrementally with Claude Code subagents, May 2026.
