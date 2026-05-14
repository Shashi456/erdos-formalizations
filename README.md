# Erdős formalizations

Lean 4 / Mathlib formalizations of problems from
[erdosproblems.com](https://www.erdosproblems.com).

## Problems

| # | Problem | Status |
|:---|:---|:---|
| [694](https://www.erdosproblems.com/694) | Totient fibre extremes | Complete |
| [750](https://www.erdosproblems.com/750) | Almost-half independent sets in graphs of infinite chromatic number | Complete |
| [283](https://www.erdosproblems.com/283) + [351](https://www.erdosproblems.com/351) | Polynomial Egyptian sums | Complete |
| [42](https://www.erdosproblems.com/42) | Sidon difference avoidance | Route B complete; Route A in progress |
| [43](https://www.erdosproblems.com/43) | Sidon difference avoidance (equal cardinality) | Scaffold |
| [202](https://www.erdosproblems.com/202) | Disjoint AP residue classes — sharp asymptotic | Scaffold |

### Artifacts

| # | Informal | Lean source | Browser (live.lean-lang.org) |
|:---|:---|:---|:---|
| 694 | [PDF](Erdos/P694/proof.pdf) | [`Proof.lean`](Erdos/P694/Proof.lean) | [open](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP694%2FProof.lean) |
| 750 | [PDF](Erdos/P750/proof.pdf) | [`Proof.lean`](Erdos/P750/Proof.lean) (v4.27) · [`Proof_v4.28.lean`](Erdos/P750/Proof_v4.28.lean) | [open](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP750%2FProof_v4.28.lean) |
| 283 + 351 | [PDF](Erdos/P283/proof.pdf) | [`Proof.lean`](Erdos/P283/Proof.lean) · [`Proof_flat.lean`](Erdos/P283/Proof_flat.lean) | — (v4.27 only) |
| 42 | [PDF](Erdos/P42/docs/compact_cayley_proof.pdf) | [`Proof.lean`](Erdos/P42/Proof.lean) | Route A: [open](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP42%2FFourierPositive%2FProof.lean) · Route B: [open](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP42%2FCompactCayley%2FProof.lean) |
| 43 | [combined P42/43 PDF](Erdos/P42/docs/combined_42_43_proof.pdf) | [`Proof.lean`](Erdos/P43/Proof.lean) | — (scaffold) |
| 202 | [PDF](Erdos/P202/docs/erdos202.pdf) | [`P202Main.lean`](Erdos/P202/P202Main.lean) | — (scaffold) |

See each problem's per-folder `README.md` for the full statement, trust
boundary, and notes on alignment with the upstream
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
skeleton when one exists.

## Trust boundaries

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| # | Extra axioms | Status |
|:---|:---|:---|
| 694 | `mertens_product`, `linnik_dvd` | Classical and unconditional (Mertens 1874, Linnik 1944). Mathlib has surrounding infrastructure but not these named statements. |
| 750 | `stiebitz_lower_bound` | Stiebitz's theorem on chromatic number of recursively built generalized Mycielski graphs (Stiebitz 1985 thesis; topological method of Lovász). Mathlib has fragments but not this named result. |
| 283 + 351 | none | Graham's complete-polynomial-values theorem is formalized in [`Erdos/P283/RSG`](Erdos/P283/RSG/README.md), so P283/P351 depend only on Mathlib core. |
| 42 Route A (active) | `finite_fourier_avoidance_count` | Finite Fourier avoidance counting theorem (Green–Tao `U²` regularity / complexity-1 counting). Drives `theorem_1_1` and `erdos_42`; the existence interface used downstream is derived from the count statement. |
| 42 Route B | none | Compact-Cayley clique theorem (compact PDF Theorem 2.1) proved end-to-end; Route B's `compact_cayley_clique` and `theorem_1_1_from_compact_cayley` depend only on Mathlib core. |
| 43 | depends on #42 + Bose–Chowla parity (scaffold) | First half inherits Route A's axiom via #42; second half (Bose–Chowla parity construction) is still `sorry`. |
| 202 | none | Sharp BFV (de la Bretèche–Ford–Vandehey, *On non-intersecting arithmetic progressions*, Acta Arith. 157) asymptotic `f(N) = N · exp(-(1+o(1))·√(log N · log log N))` for PDF Theorem 1.1 / Erdős Problem 202. `erdos202_main` depends only on Lean core (`propext`, `Classical.choice`, `Quot.sound`); BFV ingredients and the Park–Pham / Kahn–Kalai spread-core lemma are fully discharged. The integral / partial-summation Corollary 1.2 about Erdős Problem 1190 is NOT formalized. |

Inspect by enabling the `#print axioms …` block at the bottom of each
`Proof.lean`, or by reading the per-problem `README.md`. The trust boundaries
for #694, #283 + #351, and #42 (both routes) are independently confirmed by
[SafeVerify](https://github.com/GasStationManager/SafeVerify); see
[Erdos/P694/README.md § Verifying with SafeVerify](Erdos/P694/README.md#verifying-with-safeverify),
[Erdos/P283/README.md § Verifying with SafeVerify](Erdos/P283/README.md#verifying-with-safeverify),
and [Erdos/P42/README.md § Verifying with SafeVerify](Erdos/P42/README.md#verifying-with-safeverify)
for the specs and reproduction steps.

## Build

```
lake exe cache get   # optional: prebuilt Mathlib cache
lake build
```

Local toolchain: Lean 4 `v4.27.0`, Mathlib `v4.27.0` (pinned in
`lean-toolchain` and `lakefile.toml`).

The standalone flat bundles loadable in
[live.lean-lang.org](https://live.lean-lang.org/) are:

- **v4.28.0** — P694 `Proof.lean`, P750 `Proof_v4.28.lean`, P42 `FourierPositive/Proof.lean`, P42 `CompactCayley/Proof.lean`.
- **v4.27.0** — P750 `Proof.lean`, P283 `Proof_flat.lean`.

P43 and P202 do not yet ship a single-file bundle (both are scaffolds).

## License

Apache 2.0 — matches Mathlib and `formal-conjectures`.
