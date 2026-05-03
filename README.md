# Erdős formalizations

Lean 4 / Mathlib formalizations of problems from
[erdosproblems.com](https://www.erdosproblems.com).

Each row links to (a) the informal write-up the formalization is based on,
(b) the standalone Lean file (single-namespace, `import Mathlib`, copy-pastes
into [live.lean-lang.org](https://live.lean-lang.org/) without a Lake project),
and (c) the upstream
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
skeleton when one exists, with a note on whether our proof is a syntactic
match for it.

| # | Problem | Informal | Formal proof | Live editor | FC skeleton |
|---|---------|----------|--------------|-------------|-------------|
| [694](https://www.erdosproblems.com/694) | Totient fibre extremes: `R(x) = max_{n ≤ x} f_max(n)/f_min(n) = (e^γ + o(1)) log log x` | [informal.md](Erdos/P694/informal.md) · [proof.pdf](Erdos/P694/proof.pdf) | [Proof.lean](Erdos/P694/Proof.lean) | paste into [live.lean-lang.org](https://live.lean-lang.org/) | [`erdos_694`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/694.lean) — **unaligned** (`IsGreatest … answer(sorry)` template; we ship the asymptotic in `Tendsto` form) |

## Trust boundaries

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| # | Extra axioms | Status |
|---|--------------|--------|
| 694 | `mertens_product`, `linnik_dvd` | Both classical and unconditional (Mertens 1874, Linnik 1944). Mathlib has surrounding infrastructure but not these named statements. |

Inspect by enabling the `#print axioms …` block at the bottom of each
`Proof.lean`, or by reading the per-problem `README.md`.

## Build

```
lake exe cache get   # optional: prebuilt Mathlib cache
lake build
```

Toolchain: Lean 4 `v4.27.0`, Mathlib `v4.27.0`. The shipped
`Erdos/P*/Proof.lean` files are also written to typecheck standalone on
[live.lean-lang.org](https://live.lean-lang.org/) against more recent Mathlib
versions (verified on `v4.28.0`).

## License

Apache 2.0 — matches Mathlib and `formal-conjectures`.
