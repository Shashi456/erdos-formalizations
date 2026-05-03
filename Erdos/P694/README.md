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
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target — the four public theorems with `sorry` bodies. |
| [`safeverify/report.json`](safeverify/report.json) | Per-declaration SafeVerify report (output artifact). |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P694.Proof
```

**Online (no Lake required):** open the file in
[live.lean-lang.org against Mathlib v4.28.0](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP694%2FProof.lean)
(or [v4.27.0](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP694%2FProof.lean)).
Both versions verified compile-clean.

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
this table at build time. The result is also independently confirmed by
[SafeVerify](https://github.com/GasStationManager/SafeVerify) — see below.

## Verifying with SafeVerify

[SafeVerify](https://github.com/GasStationManager/SafeVerify) is a stronger
checker than `lake build` + `#print axioms`: it replays each declaration
through the kernel via `Environment.replay`, enforces a hard axiom
allow-list, and bans `partial` / `unsafe` constants.

Our proof depends on two named axioms beyond `{propext, Quot.sound,
Classical.choice}` — `Erdos694.mertens_product` and `Erdos694.linnik_dvd`,
both classical and unconditional but not yet in Mathlib. So SafeVerify's
default allow-list needs to be extended with these two names; that
extension is local to this problem.

**Reproduction** (assumes a clone of SafeVerify pinned to
`leanprover/lean4:v4.27.0` — the same toolchain this repo uses):

```bash
# 1. Build this repo so Erdos/P694/Proof.olean exists.
cd erdos-formalizations
lake exe cache get
lake build

# 2. Build the SafeVerify target spec to .olean.
lake env lean -o Erdos/P694/safeverify/Spec.olean Erdos/P694/safeverify/Spec.lean

# 3. In your SafeVerify clone, extend `allowedAxioms` (Main.lean:355)
#    with the two axioms used by this proof:
#
#      allowedAxioms := #[`propext, `Quot.sound, `Classical.choice,
#        `Erdos694.mertens_product, `Erdos694.linnik_dvd]
#
#    Then `lake exe cache get && lake build`.

# 4. Run the check.
cd /path/to/SafeVerify
lake exe safe_verify --verbose --disallow-partial \
  -s /path/to/erdos-formalizations/Erdos/P694/safeverify/report.json \
  /path/to/erdos-formalizations/Erdos/P694/safeverify/Spec.olean \
  /path/to/erdos-formalizations/.lake/build/lib/lean/Erdos/P694/Proof.olean
```

Expected output ends with `SafeVerify check passed.`. The committed
[`report.json`](safeverify/report.json) is the result of running this
recipe; per declaration:

| Declaration | Kind | Beyond `{propext, Quot.sound, Classical.choice}` |
|---|---|---|
| `Erdos694.R` | def | — |
| `Erdos694.permanence_step` | theorem | — |
| `Erdos694.infinitely_many_collisions` | theorem | — |
| `Erdos694.totient_fibre_extremes` | theorem | `mertens_product`, `linnik_dvd` |
| `Erdos694.erdos_694_asymptotic` | theorem | `mertens_product`, `linnik_dvd` |

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
