# Erdős formalizations

Lean 4 / Mathlib formalizations of problems from
[erdosproblems.com](https://www.erdosproblems.com).

Each row links to the informal write-up and to the standalone Lean file —
single-namespace, `import Mathlib`, ready to copy-paste into
[live.lean-lang.org](https://live.lean-lang.org/) without a Lake project.

| # | Problem | Informal | Formal proof |
|---|---------|----------|--------------|
| [694](https://www.erdosproblems.com/694) | Totient fibre extremes: `R(x) = max_{n ≤ x} f_max(n)/f_min(n) = (e^γ + o(1)) log log x` | [informal.md](Erdos/P694/informal.md) · [proof.pdf](Erdos/P694/proof.pdf) | [Proof.lean](Erdos/P694/Proof.lean) · [live](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP694%2FProof.lean) |
| [750](https://www.erdosproblems.com/750) | Almost-half independent sets: ∃ graph of infinite chromatic number with `α(F) ≥ |V(F)|/2 − f(|V(F)|)` for every `f → ∞` | [informal.md](Erdos/P750/informal.md) · [proof.pdf](Erdos/P750/proof.pdf) | [Proof.lean](Erdos/P750/Proof.lean) · [live](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP750%2FProof.lean) |

See each problem's per-folder README for the full statement, trust boundary,
and notes on alignment with the upstream
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
skeleton when one exists.

## Trust boundaries

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| # | Extra axioms | Status |
|---|--------------|--------|
| 694 | `mertens_product`, `linnik_dvd` | Both classical and unconditional (Mertens 1874, Linnik 1944). Mathlib has surrounding infrastructure but not these named statements. |
| 750 | `stiebitz_lower_bound` | Stiebitz's theorem on chromatic number of recursively built generalized Mycielski graphs (Stiebitz 1985 thesis; topological method of Lovász). Mathlib has fragments but not this named result. |

Inspect by enabling the `#print axioms …` block at the bottom of each
`Proof.lean`, or by reading the per-problem `README.md`. The trust boundary
for #694 is also independently confirmed by
[SafeVerify](https://github.com/GasStationManager/SafeVerify); see
[Erdos/P694/README.md § Verifying with SafeVerify](Erdos/P694/README.md#verifying-with-safeverify)
for the spec, the JSON report, and reproduction steps.

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
