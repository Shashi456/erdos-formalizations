# Erdős formalizations

Lean 4 / Mathlib formalizations of problems from
[erdosproblems.com](https://www.erdosproblems.com).

Each row links to the informal write-up and to the Lean formalization.
For #694, #750 the development lives in a single self-contained file (single
namespace, `import Mathlib`, loadable directly into
[live.lean-lang.org](https://live.lean-lang.org/) without a Lake project).
P283 + P351 use a 10-file modular split — see the per-problem README for the
live-link tradeoff.

| # | Problem | Informal | Formal proof |
|---|---------|----------|--------------|
| [694](https://www.erdosproblems.com/694) | Totient fibre extremes: `R(x) = max_{n ≤ x} f_max(n)/f_min(n) = (e^γ + o(1)) log log x` | [informal.md](Erdos/P694/informal.md) · [proof.pdf](Erdos/P694/proof.pdf) | [Proof.lean](Erdos/P694/Proof.lean) · [live](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP694%2FProof.lean) |
| [750](https://www.erdosproblems.com/750) | Almost-half independent sets: graphs of infinite chromatic number whose finite induced subgraphs `F` admit independent sets of size `≥ |V(F)|/2 − f(|V(F)|)`, for any `f → ∞` | [informal.md](Erdos/P750/informal.md) · [proof.pdf](Erdos/P750/proof.pdf) | [Proof.lean](Erdos/P750/Proof.lean) (v4.27) · [Proof_v4.28.lean](Erdos/P750/Proof_v4.28.lean) (v4.28+) · [live v4.27](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP750%2FProof.lean) · [live v4.28](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP750%2FProof_v4.28.lean) |
| [283](https://www.erdosproblems.com/283) + [351](https://www.erdosproblems.com/351) | Polynomial Egyptian sums: `∑ p(n_i) = m, ∑ 1/n_i = α` for any `α ∈ ℚ_{>0}` and qualifying polynomial | [informal.md](Erdos/P283/informal.md) · [proof.pdf](Erdos/P283/proof.pdf) | 10-file modular split under [Erdos/P283/](Erdos/P283/) — [Proof.lean](Erdos/P283/Proof.lean) re-exports · single-file bundle [Proof_flat.lean](Erdos/P283/Proof_flat.lean) (~8 000 lines) for live · [live v4.27](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP283%2FProof_flat.lean). **0 sorries**, SafeVerify-confirmed. See [P283/README.md](Erdos/P283/README.md). |
| [42](https://www.erdosproblems.com/42) (in progress) | Sidon difference avoidance: every Sidon `A ⊆ [N]` admits a Sidon `B` of size `M` with `(A−A)∩(B−B)={0}` | [informal.md](Erdos/P42/informal.md) · [forum_thread.md](Erdos/P42/forum_thread.md) · [proof.pdf](Erdos/P42/proof.pdf) · [combined 42+43](Erdos/P42/proof_combined_42_43.pdf) · [ulam note](Erdos/P42/proof_ulam_note.pdf) | [Proof.lean](Erdos/P42/Proof.lean) (scaffolded; sorries) |

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
| 283 + 351 | `roth_szekeres_graham` | Graham's complete-polynomial-values theorem (*Duke Math. J.* 1964) with Roth-Szekeres (*Quart. J. Math.* 1954) as the asymptotic input. Both classical and unconditional. |
| 42 (in progress) | `complexity_one_counting_lemma`, `compact_U2_regularity_subsequential_limit` | Green-Tao 2008 generalized von Neumann theorem for complexity-1 linear forms, plus the standard compactness/`U²`-regularity packaging. Both classical. |

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
