# Erdős formalizations

Lean 4 / Mathlib formalizations of problems from
[erdosproblems.com](https://www.erdosproblems.com).

| # | Problem | Informal | Formal proof |
|---|---------|----------|--------------|
| [694](https://www.erdosproblems.com/694) | Totient fibre extremes | [proof.pdf](Erdos/P694/proof.pdf) | [Proof.lean](Erdos/P694/Proof.lean) · [live](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP694%2FProof.lean) |
| [750](https://www.erdosproblems.com/750) | Almost-half independent sets in graphs of infinite chromatic number | [proof.pdf](Erdos/P750/proof.pdf) | [Proof.lean](Erdos/P750/Proof.lean) · [live](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP750%2FProof.lean) |
| [283](https://www.erdosproblems.com/283) + [351](https://www.erdosproblems.com/351) | Polynomial Egyptian sums | [proof.pdf](Erdos/P283/proof.pdf) | [Proof.lean](Erdos/P283/Proof.lean) |
| [42](https://www.erdosproblems.com/42) (in progress) | Sidon difference avoidance | [proof.pdf](Erdos/P42/proof.pdf) | [Proof.lean](Erdos/P42/Proof.lean) (sorries) |

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
| 283 + 351 | none | Graham's complete-polynomial-values theorem is now formalized in [`Erdos/P283/RSG`](Erdos/P283/RSG/README.md), so P283/P351 depend only on Mathlib core foundations. |
| 42 (in progress) | `complexity_one_counting_lemma`, `compact_U2_regularity_subsequential_limit` | Green-Tao 2008 generalized von Neumann theorem for complexity-1 linear forms, plus the standard compactness/`U²`-regularity packaging. Both classical. |

The RSG proof roadmap and source list live in [Erdos/P283/RSG/README.md](Erdos/P283/RSG/README.md).

Inspect by enabling the `#print axioms …` block at the bottom of each
`Proof.lean`, or by reading the per-problem `README.md`. The trust boundaries
for #694 and #283 + #351 are also independently confirmed by
[SafeVerify](https://github.com/GasStationManager/SafeVerify); see
[Erdos/P694/README.md § Verifying with SafeVerify](Erdos/P694/README.md#verifying-with-safeverify) and
[Erdos/P283/README.md § Verifying with SafeVerify](Erdos/P283/README.md#verifying-with-safeverify)
for the specs and reproduction steps.

## Build

```
lake exe cache get   # optional: prebuilt Mathlib cache
lake build
```

Toolchain: Lean 4 `v4.27.0`, Mathlib `v4.27.0`. Single-file `Proof.lean`
(P694, P750) and `Proof_flat.lean` (P283) bundles also typecheck standalone
on [live.lean-lang.org](https://live.lean-lang.org/), so they can be loaded
in the browser without a Lake project (P694/P750 verified on `v4.28.0`;
P283 currently only on `v4.27.0`).

## License

Apache 2.0 — matches Mathlib and `formal-conjectures`.
