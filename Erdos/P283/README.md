# Erdős Problems 283 + 351 — Polynomial Egyptian sums

> [erdosproblems.com/283](https://www.erdosproblems.com/283) ·
> [erdosproblems.com/351](https://www.erdosproblems.com/351)
>
> ⚠️ **In progress.** §1 (Egyptian switches) is complete and axiom-free.
> Theorem 1 (§2) and the density sub-lemma `exists_large_correction_denominator`
> remain `sorry`. The Corollary 7 zero and negative-leading cases are proved;
> the positive-leading case awaits Theorem 1. See [§ Current state](#current-state).

The May 3 2026 proof (GPT-5.5 Pro, cleaned up by Liam Price; Kevin Barreto
noticed #351 follows) resolves both problems simultaneously.

**Erdős #283.** For every `p ∈ ℚ[x]` integer-valued on ℤ with positive leading
coefficient and no fixed divisor, every sufficiently large integer `m` is
expressible as `p(n_1) + ⋯ + p(n_k)` with distinct `n_i` satisfying
`1/n_1 + ⋯ + 1/n_k = 1`. The proof in fact holds for any rational `α > 0`
in place of `1` — this is **Theorem 1** in the PDF.

**Erdős #351.** For non-zero `p ∈ ℚ[x]` with positive leading coefficient,
the set `{ p(n) + 1/n : n ∈ ℕ }` is strongly complete. **Corollary 7** in
the PDF.

The proof combines the **Roth-Szekeres-Graham theorem** on complete
polynomial sequences with reciprocal-preserving switches (the identity
`1/x = 1/(2x) + 1/(3x) + 1/(6x)`) and a finite congruence correction.

## Files

The Lean proof is split across 10 modules (formerly a single `Proof.lean`).
The umbrella file `Proof.lean` re-exports everything for convenience.

| File | What |
|------|------|
| [`Basic.lean`](Basic.lean) | Foundational defs: `IsEgyptianPattern`, `IntValued`, `intEval`, `NoFixedDivisor`, `HasIntegralMultiple`, `IntValued.{add, sub, sum}`, the RSG axiom, `FS`. |
| [`Egyptian.lean`](Egyptian.lean) | §1 Lemmas 3 + 4 (`egyptian_expansion`, `egyptian_pattern_with_period`) + greedy helpers. |
| [`PolynomialPeriod.lean`](PolynomialPeriod.lean) | §1 Lemma 5 (polynomial periodicity). |
| [`Switching.lean`](Switching.lean) | §1 `switchingPoly`, exact natDegree/leadingCoeff formulas, Lemma 6 (`switching_values_span_top`), `IntValued.comp_nat_mul_X`, `switchingPoly_intValued`. |
| [`MainSlots.lean`](MainSlots.lean) | §2 construction objects: `P=36`, `u`, `D`, `tau`, `E0`, `A`, `Dpoly`, `theta`, telescoping, leading coeff equalities. |
| [`Collision.lean`](Collision.lean) | §2 valuation profiles (`u_coprime_six`, `D_coprime_six`, `main_valuation_profile`, `tau_valuation_profile`, `filler_v2_at_least_three`). |
| [`Corrections.lean`](Corrections.lean) | §2 correction-slot subset-sum residue cover + density argument (`exists_large_correction_denominator` is the remaining sorry). |
| [`Theorem1.lean`](Theorem1.lean) | §2 main theorem. |
| [`Corollary351.lean`](Corollary351.lean) | §3 Corollary 7 (zero, positive-leading, negative-leading cases). |
| [`FC.lean`](FC.lean) | §4 `formal-conjectures` upstream wrappers `Erdos283.erdos_283` and `Erdos351.erdos_351`. |
| [`Proof.lean`](Proof.lean) | Umbrella — imports all of the above. |
| [`proof.pdf`](proof.pdf) | GPT-5.5 Pro + Liam Price, *Polynomial Egyptian Sums*, 3 May 2026. |
| [`informal.md`](informal.md) | Human-readable proof outline matching the PDF section-by-section. |
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target — public theorems with `sorry` bodies. |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P283.Proof
```

**Online (no Lake required):** open in
[live.lean-lang.org against Mathlib v4.27.0](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP283%2FProof.lean).

## Current state

Theorem statements wired to FC's
[`erdos_283`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/283.lean)
and
[`erdos_351`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/351.lean)
(matching the upstream `answer(sorry) ↔ …` shape).

Per-file sorry counts:

| File | Sorries |
|---|---|
| `Basic.lean` | 0 |
| `Egyptian.lean` | 0 |
| `PolynomialPeriod.lean` | 0 |
| `Switching.lean` | 0 |
| `MainSlots.lean` | 0 |
| `Collision.lean` | 0 |
| `Corrections.lean` | 1 (`exists_large_correction_denominator`) |
| `Theorem1.lean` | 1 (`theorem_1`) |
| `Corollary351.lean` | 1 (`corollary_7_pos_leading`; the zero and negative cases are proven) |
| `FC.lean` | 2 (`erdos_283`, `erdos_351` — both transitively depend on Theorem 1) |

Per-theorem status:

| Theorem | Status |
|---|---|
| `roth_szekeres_graham` (axiom — Graham 1964 / Roth-Szekeres 1954) | postulated |
| Lemma 3 (`egyptian_expansion`, axiom-free) | ✅ proved |
| Lemma 4 (`egyptian_pattern_with_period`, axiom-free) | ✅ proved |
| Lemma 5 (`polynomial_periodicity`, axiom-free) | ✅ proved |
| Lemma 6 (`switching_values_span_top`, axiom-free) | ✅ proved |
| `switchingPoly_natDegree_eq`, `switchingPoly_leadingCoeff_eq` | ✅ proved |
| `IntValued.{add, sub, sum, comp_nat_mul_X}`, `switchingPoly_intValued`, `A_intValued` | ✅ proved |
| `D_recip`, `main_telescoping`, `isEgyptianPattern_E0`, `A_leadingCoeff_eq`, `theta_gt_one`, `Dpoly_eval_at_succ` | ✅ proved |
| `u_coprime_six`, `D_coprime_six`, `main_valuation_profile`, `tau_valuation_profile`, `filler_v2_at_least_three` | ✅ proved |
| `duplicated_generators_subset_sum_all_residues` | ✅ proved |
| `exists_large_correction_denominator` (density / sieve argument) | `sorry` |
| `theorem_1` (main, depends on `roth_szekeres_graham`) | `sorry` |
| `corollary_7_zero` (`p = 0` case via Lemma 3) | ✅ proved |
| `corollary_7_pos_leading` (positive lead coeff; depends on Theorem 1) | `sorry` |
| `not_strongly_complete_of_neg_leadingCoeff` | ✅ proved |
| `Erdos283.erdos_283` (FC iff form) | `sorry` |
| `Erdos351.erdos_351` (FC iff form) | `sorry` |

## Target trust boundary

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Extra axioms (target) |
|---|---|
| Lemmas 3-6 | (none — Egyptian-fraction combinatorics) |
| Theorem 1 (main), Corollary 7, `erdos_283`, `erdos_351` | `roth_szekeres_graham` |

`roth_szekeres_graham` is Graham's complete-polynomial-values theorem
(*Duke Math. J.* 1964), with Roth-Szekeres (*Quart. J. Math.* 1954) as
the asymptotic input. Both are classical and unconditional; Mathlib has
surrounding analytic-number-theory infrastructure but not this named
result.

## Alignment with the informal proof

[`proof.pdf`](proof.pdf) is the GPT-5.5 Pro / Liam Price PDF the
formalization is based on. We split it into the §1 Egyptian switches
(four lemmas), §2 main proof, and Corollary 7 derivation; each section
will be audited independently against `Proof.lean`.

Notable encoding choices:
* **Polynomials** use `Polynomial ℚ` (we cast to `Polynomial ℤ` where
  the integer-valued / fixed-divisor predicates apply).
* **Egyptian patterns** are `Finset ℕ` with the predicate
  `∀ e ∈ E, e ≥ 2 ∧ ∑_{e ∈ E} (1 : ℚ) / e = 1`.
* **Collision avoidance** uses `Nat.padicValNat 2` and `Nat.padicValNat 3`
  for the `(v_2, v_3)` argument.
* **The `Fin (k+1) → ℤ` indexing** in FC's `Erdos283.Condition` is
  preserved; an internal `Finset ℤ` form is bridged at the end.

## Relationship to `formal-conjectures`

* Upstream
  [`FormalConjectures/ErdosProblems/283.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/283.lean)
  states `erdos_283 : answer(sorry) ↔ ∀ p : ℤ[X], Condition p`. We discharge
  this under `answer := True`.
* Upstream
  [`FormalConjectures/ErdosProblems/351.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/351.lean)
  states `erdos_351 : answer(sorry) ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff → HasCompleteImage P`.
  We discharge this under `answer := True`.
