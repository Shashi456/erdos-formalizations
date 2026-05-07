# Erdős Problem 42 — Sidon difference avoidance

> [erdosproblems.com/42](https://www.erdosproblems.com/42)
>
> ⚠️ **In progress.** The compact-Cayley route now proves the public #42
> wrapper modulo the theorem-shaped compact-Cayley clique axiom. The finite
> allowed-difference Fourier estimate is proved. The alternate Fourier-positive
> route now has a theorem-shaped scaffold with explicit remaining placeholders.
> See
> [§ Current state](#current-state).

For every `M ≥ 1`, every sufficiently large `N`, and every non-empty Sidon set `A ⊆ {1, …, N}`, there is another Sidon set `B ⊆ {1, …, N}` of size `M` with

```
(A − A) ∩ (B − B) = {0}.
```

Erdős's #42, [`[Er95]`]. The active Lean route follows the compact Cayley
lemma proof from `erdos42_compact_sidon_clean.pdf`: a dense Cayley graph on
`ZMod p` with small Fourier upper bias has large cliques, and the downstream
Sidon extraction is finite combinatorics. The older Fourier-positive /
Green-Tao `U²` route remains as a separate scaffold.

## Files

| File | What |
|------|------|
| [`Proof.lean`](Proof.lean) | Cayley-route umbrella importing the modules used by the public proof. |
| [`Basic.lean`](Basic.lean), [`Sidon.lean`](Sidon.lean) | Shared finite-combinatorial API and Sidon lemmas. |
| [`CompactCayley/Axiom.lean`](CompactCayley/Axiom.lean) | Route B trust boundary, `compact_cayley_clique`. |
| [`CompactCayley/Internal.lean`](CompactCayley/Internal.lean) | Finite tuple-to-clique endpoint for opening the compact-Cayley axiom. |
| [`CompactCayley/Application.lean`](CompactCayley/Application.lean) | Downstream Cayley application over `Finset ℤ`. |
| [`FourierPositive/Axiom.lean`](FourierPositive/Axiom.lean) | Route A trust boundary, `finite_fourier_avoidance`. |
| [`FourierPositive/Application.lean`](FourierPositive/Application.lean) | Route A forbidden-set scaffold and finite Fourier lower-bound bridge. |
| [`Continuous.lean`](Continuous.lean) | Continuous Haar/null-set endpoints used when opening the compactness arguments. |
| [`FCWrapper.lean`](FCWrapper.lean) | Public `Set ℕ` theorem and FC-style `erdos_42` wrapper. |
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
```

**Online:** [live.lean-lang.org against Mathlib v4.27.0](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP42%2FProof.lean)

## Current state

The compact-Cayley route is wired through the public FC-style statement.
`lake build Erdos.P42.Proof` builds the Cayley-route umbrella without executable
`sorry` warnings. The theorem depends on Mathlib foundations plus the
`compact_cayley_clique` route axiom. The finite allowed-difference Fourier
calculation and the elementary Sidon-size-over-prime smallness bound are proved.

| Theorem | Status |
|---|---|
| `compact_cayley_clique` | theorem-shaped axiom, matching compact PDF Theorem 2.1 with a real normalized Fourier predicate |
| `allowedDiffs_fourier_upper` | proved finite Fourier calculation for `T_A = ZMod p \ ((A - A) ∪ {0})` |
| `sidon_card_minus_one_div_prime_eventually_small` | proved elementary `|A| = O(sqrt N)` bound used to make `( |A|-1 ) / p ≤ ε` |
| `CompactCayley.cliqueKernelDensity_re_pos_iff_exists_clique` | proved finite endpoint: positive ordered `K_ℓ` Cayley density is equivalent to an actual `ℓ`-clique |
| `CompactCayley.theorem_1_1_from_compact_cayley` | proved downstream over `Finset ℤ` |
| `isSidonInt_of_isSidon` | proved bridge from bounded `Set ℕ` Sidon sets to `Finset ℤ` |
| `theorem_1_1` | proved public `Set ℕ` statement from the Cayley route |
| `erdos_42` | proved FC-style wrapper under `answer := True` |
| `FourierUpperIndicator` / `FourierLowerIndicator` | concrete normalized `ZMod.dft` predicates in `FourierAPI.lean` |
| `indicatorC_eq_sum_normalizedDftCoeff` | proved normalized finite Fourier inversion for indicator kernels |
| `tao_continuous_avoidance` | proved continuous null-set endpoint, including the Haar shear/Fubini step |
| `continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup` | proved compact-forcing endpoint: a kernel vanishing exactly on a proper closed subgroup has positive continuous `K_M` density |
| `FourierPositive.finite_fourier_avoidance` | theorem-shaped Route A axiom, matching the Green-Tao/Fourier-positive finite avoidance theorem |
| `FourierPositive.forbiddenDiffSetMod_symmetric`, `zero_mem_forbiddenDiffSetMod`, `forbiddenDiffSetMod_card_le` | proved finite forbidden-set setup for `F_A = A - A mod p` |
| `FourierPositive.sidon_forbidden_fourier_lower` | proved normalized Fourier lower bound for `F_A`; axiom audit reports only Mathlib foundations |
| `FourierPositive.non_sidon_ordered_tuple_bound` | theorem-shaped local scaffold axiom for the bad ordered-tuple count |
| `FourierPositive.theorem_1_1_from_finite_fourier_avoidance` | theorem-shaped local scaffold axiom for the final Route A asymptotic/tuple-selection assembly |

Route A builds independently with:

```
lake build Erdos.P42.FourierPositive.Application
```

It is not imported by the Cayley-route umbrella `Erdos.P42.Proof`.

## Target trust boundary

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Extra axioms (target) |
|---|---|
| `theorem_1_1`, `erdos_42` via Route B | `compact_cayley_clique` |
| Route A finite setup lemmas | none beyond Mathlib foundations |
| Route A scaffold endpoint | `finite_fourier_avoidance`, `non_sidon_ordered_tuple_bound`, `theorem_1_1_from_finite_fourier_avoidance` |

`#print axioms Erdos42.theorem_1_1` and `#print axioms Erdos42.erdos_42`
currently report Mathlib foundations plus `compact_cayley_clique`. The
internal finite endpoint
`Erdos42.CompactCayley.cliqueKernelDensity_re_pos_iff_exists_clique` reports
only Mathlib foundations. The continuous endpoints
`Erdos42.tao_continuous_avoidance` and
`Erdos42.continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup` also report
only Mathlib foundations. For Route A, the finite forbidden-set lemmas through
`Erdos42.FourierPositive.sidon_forbidden_fourier_lower` also report only Mathlib
foundations; the two local scaffold endpoints are intentionally explicit axioms.

## Comparison with Sedov's `M = 3` formalization

Daniil Sedov's [github.com/Gusarich/erdos42](https://github.com/Gusarich/erdos42) handles the **special case `M = 3`** via a sum-free 2/5-trichotomy axiom (Balogh-Liu-Sharifzadeh-Treglown, 2014). Our target is the **general `M`** case via the Fourier-compactness route.

The two approaches are independent — Sedov's axiom is a finite Ramsey/sum-free statement; ours is Green-Tao analytic. There's no direct sharing of code or lemmas, but Sedov's `IsSidon` API and `(A − A) ∩ (B − B) ⊆ {0}` lemmas may be re-usable.

## Alignment with the informal proof

[`proof_ulam_note.pdf`](proof_ulam_note.pdf) is the canonical reference; we audit `Proof.lean` against it section-by-section.

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
