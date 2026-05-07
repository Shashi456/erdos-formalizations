# Erdős Problem 42 — Sidon difference avoidance

> [erdosproblems.com/42](https://www.erdosproblems.com/42)
>
> ⚠️ **In progress.** The active public #42 wrapper now uses Route A and no
> longer depends on the compact-Cayley clique axiom. It is conditional on the
> theorem-shaped finite Fourier avoidance axiom `finite_fourier_avoidance_exists`.
> See
> [§ Current state](#current-state).

For every `M ≥ 1`, every sufficiently large `N`, and every non-empty Sidon set `A ⊆ {1, …, N}`, there is another Sidon set `B ⊆ {1, …, N}` of size `M` with

```
(A − A) ∩ (B − B) = {0}.
```

Erdős's #42, [`[Er95]`]. The active Lean route follows the Fourier-positive /
Green-Tao `U²` route from the Ulam/Tao note: a finite avoidance theorem gives a
large tuple avoiding `A - A`, and the downstream Sidon extraction is finite
combinatorics. The compact-Cayley route remains preserved separately in
`CompactCayley/RouteB.lean`.

## Files

| File | What |
|------|------|
| [`Proof.lean`](Proof.lean) | Thin active-proof alias; currently imports `Proof_Fourier.lean`. |
| [`Proof_Fourier.lean`](Proof_Fourier.lean) | Route A umbrella for the Fourier-positive proof and public wrappers. |
| [`Proof_Cayley.lean`](Proof_Cayley.lean) | Route B umbrella for the compact-Cayley proof. |
| [`Basic.lean`](Basic.lean), [`Sidon.lean`](Sidon.lean) | Shared finite-combinatorial API and Sidon lemmas. |
| [`CompactCayley/Axiom.lean`](CompactCayley/Axiom.lean) | Route B trust boundary, `compact_cayley_clique`. |
| [`CompactCayley/Internal.lean`](CompactCayley/Internal.lean) | Finite tuple-to-clique endpoint for opening the compact-Cayley axiom. |
| [`CompactCayley/Application.lean`](CompactCayley/Application.lean) | Shared finite Cayley/Fourier and greedy Sidon lemmas; no Route B axiom import. |
| [`CompactCayley/RouteB.lean`](CompactCayley/RouteB.lean) | Route B downstream theorem, isolated behind `compact_cayley_clique`. |
| [`FourierPositive/Axiom.lean`](FourierPositive/Axiom.lean) | Route A trust boundary, `finite_fourier_avoidance_exists`. |
| [`FourierPositive/Application.lean`](FourierPositive/Application.lean) | Route A forbidden-set setup, Fourier lower-bound bridge, and downstream theorem. |
| [`Continuous.lean`](Continuous.lean) | Continuous Haar/null-set endpoints used when opening the compactness arguments. |
| [`FCWrapper.lean`](FCWrapper.lean) | Public `Set ℕ` theorem and FC-style `erdos_42` wrapper. |
| [`FC.lean`](FC.lean) | Formal-conjectures-shaped RHS with equivalence to `FCWrapper.lean`. |
| [`proof.pdf`](proof.pdf) | Harjas / GPT-5.5 Pro, *A Fourier-Compactness Proof of Erdős Problem 42*, corrected version, 27 April 2026. |
| [`proof_combined_42_43.pdf`](proof_combined_42_43.pdf) | Kevin Barreto, *Sidon Difference Avoidance*, 29 April 2026 — combines #42 + #43. |
| [`proof_ulam_note.pdf`](proof_ulam_note.pdf) | natso26 / Tao, *A Fourier-positive proof of Erdős Problem 42*, draft note, 30 April 2026 — the cleanest exposition; we follow this layout. |
| [`informal.md`](informal.md) | Human-readable proof outline matching `proof_ulam_note.pdf`. |
| [`forum_thread.md`](forum_thread.md) | Snapshot of the forum thread (relevant comments + links). |
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target — public theorems with `sorry` bodies. |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P42.Proof
lake build Erdos.P42.Proof_Fourier
lake build Erdos.P42.Proof_Cayley
```

**Online:** [live.lean-lang.org against Mathlib v4.27.0](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP42%2FProof.lean)

## Current state

Route A is wired through the public FC-style statement. `lake build
Erdos.P42.Proof` builds the active umbrella without executable `sorry` warnings.
The public theorem depends on Mathlib foundations plus
`finite_fourier_avoidance_exists`; it no longer depends on
`compact_cayley_clique`. The finite allowed/forbidden-difference Fourier
calculations and the elementary Sidon-size-over-prime smallness bound are proved.

| Theorem | Status |
|---|---|
| `compact_cayley_clique` | theorem-shaped axiom, matching compact PDF Theorem 2.1 with a real normalized Fourier predicate |
| `allowedDiffs_fourier_upper` | proved finite Fourier calculation for `T_A = ZMod p \ ((A - A) ∪ {0})` |
| `sidon_card_minus_one_div_prime_eventually_small` | proved elementary `|A| = O(sqrt N)` bound used to make `( |A|-1 ) / p ≤ ε` |
| `CompactCayley.cliqueKernelDensity_re_pos_iff_exists_clique` | proved finite endpoint: positive ordered `K_ℓ` Cayley density is equivalent to an actual `ℓ`-clique |
| `CompactCayley.theorem_1_1_from_compact_cayley` | preserved Route B downstream theorem over `Finset ℤ`, isolated in `CompactCayley/RouteB.lean` |
| `isSidonInt_of_isSidon` | proved bridge from bounded `Set ℕ` Sidon sets to `Finset ℤ` |
| `theorem_1_1` | proved public `Set ℕ` statement from Route A |
| `erdos_42` | proved FC-style wrapper under `answer := True` |
| `FormalConjecturesShape.erdos42RHS_iff_localRHS` | proved equivalence between the local wrapper RHS and the upstream-shaped RHS |
| `FormalConjecturesShape.erdos_42` | proved formal-conjectures-shaped theorem under `answer := True`, with FC's `∃ᵉ` represented by `ExplicitExists` |
| `FourierUpperIndicator` / `FourierLowerIndicator` | concrete normalized `ZMod.dft` predicates in `FourierAPI.lean` |
| `indicatorC_eq_sum_normalizedDftCoeff` | proved normalized finite Fourier inversion for indicator kernels |
| `tao_continuous_avoidance` | proved continuous null-set endpoint, including the Haar shear/Fubini step |
| `continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup` | proved compact-forcing endpoint: a kernel vanishing exactly on a proper closed subgroup has positive continuous `K_M` density |
| `FourierPositive.finite_fourier_avoidance_exists` | theorem-shaped Route A axiom, matching the existence form of the Green-Tao/Fourier-positive finite avoidance theorem |
| `FourierPositive.forbiddenDiffSetMod_symmetric`, `zero_mem_forbiddenDiffSetMod`, `forbiddenDiffSetMod_card_le` | proved finite forbidden-set setup for `F_A = A - A mod p` |
| `FourierPositive.sidon_forbidden_fourier_lower` | proved normalized Fourier lower bound for `F_A`; axiom audit reports only Mathlib foundations |
| `FourierPositive.theorem_1_1_from_finite_fourier_avoidance` | proved downstream over `Finset ℤ` from `finite_fourier_avoidance_exists` and greedy Sidon extraction |

Route A builds with:

```
lake build Erdos.P42.Proof_Fourier
lake build Erdos.P42.FourierPositive.Application
```

It is imported by the active umbrella `Erdos.P42.Proof`. Route B builds
separately with:

```
lake build Erdos.P42.Proof_Cayley
```

## Target trust boundary

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Extra axioms (target) |
|---|---|
| `theorem_1_1`, `erdos_42` via Route A | `finite_fourier_avoidance_exists` |
| Preserved Route B theorem | `compact_cayley_clique` |
| Route A finite setup lemmas | none beyond Mathlib foundations |
| Route B finite setup lemmas | none beyond Mathlib foundations |

`#print axioms Erdos42.theorem_1_1` and `#print axioms Erdos42.erdos_42`
currently report Mathlib foundations plus `finite_fourier_avoidance_exists`.
The internal finite endpoint
`Erdos42.CompactCayley.cliqueKernelDensity_re_pos_iff_exists_clique` reports
only Mathlib foundations. The continuous endpoints
`Erdos42.tao_continuous_avoidance` and
`Erdos42.continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup` also report
only Mathlib foundations. For Route A, the finite forbidden-set lemmas through
`Erdos42.FourierPositive.sidon_forbidden_fourier_lower` also report only Mathlib
foundations.

## Comparison with Sedov's `M = 3` formalization

Daniil Sedov's [github.com/Gusarich/erdos42](https://github.com/Gusarich/erdos42) handles the **special case `M = 3`** via a sum-free 2/5-trichotomy axiom (Balogh-Liu-Sharifzadeh-Treglown, 2014). Our target is the **general `M`** case via the Fourier-compactness route.

The two approaches are independent — Sedov's axiom is a finite Ramsey/sum-free statement; ours is Green-Tao analytic. There's no direct sharing of code or lemmas, but Sedov's `IsSidon` API and `(A − A) ∩ (B − B) ⊆ {0}` lemmas may be re-usable.

## Alignment with the informal proof

[`proof_ulam_note.pdf`](proof_ulam_note.pdf) is the canonical reference for
Route A; we audit `Proof_Fourier.lean` and `FourierPositive/Application.lean`
against it section-by-section. The compact-Cayley PDF is tracked separately by
`Proof_Cayley.lean`.

Notable encoding choices:
* **Sidon sets** use Mathlib's `IsSidon` (or the FC skeleton's `IsMaximalSidonSetIn` + `IsSidon`, whichever lands cleanest).
* **Fourier transform on `𝔽_p`** uses `ZMod p` + Mathlib's `AddChar` / `Real.fourierIntegral` infrastructure where applicable.
* **Compact abelian groups** in Layer 1 use Mathlib's `CompactAddCommGroup` + `Pontryagin` API.
* **The "almost every" in Layer 1** is `MeasureTheory.AEStrongly` over Haar measure.

## Relationship to `formal-conjectures`

Upstream
[`FormalConjectures/ErdosProblems/42.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/42.lean)
states `erdos_42 : answer(sorry) ↔ ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ A …`. We discharge this under `answer := True`.

The FC file also provides `IsMaximalSidonSetIn`, `IsSidon`, and basic worked examples (`{1, 2, 4}` is maximal Sidon in `[4]`, etc.) which we will reuse where applicable.
