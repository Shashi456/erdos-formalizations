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
| [`compact_cayley_proof.pdf`](compact_cayley_proof.pdf) | The original informal proof (Liam Price + GPT-5.5 Pro). |
| [`proof.tex`](proof.tex) | LaTeX source of `compact_cayley_proof.pdf`. |
| [`proof_outline.md`](proof_outline.md) | Human-readable proof outline / strategy notes. |
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

## Alignment with the informal proof

[`proof.tex`](proof.tex) is the GPT-5.5 Pro / Liam Price LaTeX writeup the
formalization is based on. We split it into three sections (Preliminaries,
Theorem 2.1, Proposition 3.1) and audited each independently against
`Proof.lean`. **All three sections are faithfully aligned**, with the
following deliberate, documented deviations:

* **Lemma 1.1 (Landau max-ratio).** LaTeX argues by primorial extremality
  + PNT (`ϑ(y) ~ y`). Lean uses an analytic split-at-`Y` bound
  `m/φ(m) ≤ primeEulerProdNat(Y) · ((Y+1)/Y)^(log m / log(Y+1))` with
  `Y(T) = ⌊log T / log 4⌋`, **avoiding PNT** in favor of Mathlib's
  elementary `primorial_le_4_pow`. Same conclusion, smaller trust boundary.
* **Lower-bound height bound.** LaTeX has `n_y ≤ A_y U_y² ≪ A_y^{2L-1}`
  combined with `log A_y ~ y` (PNT). Lean uses the cruder but deterministic
  `A_Y ≤ P_Y ≤ 4^Y`, giving `n_Y ≤ exp(K·Y)` for an explicit constant `K`.
  Lean picks `Y(x) = ⌊log x / (2K)⌋`; both choices give
  `log Y = log log x + O(1)`. Again avoids PNT.
* **Linnik invocation.** LaTeX takes `ℓ ≡ 1 (mod A_y)`. Lean takes
  `ℓ ≡ 1 (mod A_Y · P_Y)` — strictly stronger, since
  `A_Y · P_Y ∣ ℓ-1` implies `A_Y ∣ ℓ-1`. Polynomial bound becomes
  `ℓ ≤ C · (A·P)^L` rather than `ℓ ≤ C · A^L`; only changes the constant.
* **Proposition 3.1 statement.** Lean's `infinitely_many_collisions` returns
  explicit witnesses `(x, y) = (r·a, r·b)` satisfying `b·x = a·y` (equality);
  this is strictly stronger than the LaTeX claim
  `f_max(N)/f_min(N) ≥ a/b` and directly entails it.

The construction objects (`P_Y, A_Y, ℓ, U_Y = (ℓ-1)/A_Y, Q_Y, a_Y = ℓ Q_Y,
b_Y = P_Y U_Y Q_Y`) are formalized exactly as in the LaTeX, the totient
collision identity `φ(a_Y) = φ(b_Y) = A_Y · U_Y · ∏(q-1)` is proven
verbatim, and the ratio `b_Y/a_Y = (P_Y/A_Y) · (ℓ-1)/ℓ` matches
character-for-character.

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
