# Erdős Problems 283 + 351 — Polynomial Egyptian sums

> [erdosproblems.com/283](https://www.erdosproblems.com/283) ·
> [erdosproblems.com/351](https://www.erdosproblems.com/351)
>
> ✅ **Complete modulo the stated trust boundary.** No executable `sorry` or
> `admit` remains in the P283 development. The only non-Mathlib postulate is
> the Roth-Szekeres-Graham theorem recorded in `Basic.lean`.
>
> Lemmas 3-6, switching polynomial, qPoly + asymptotics, valuation profiles,
> telescoping, density argument via pigeonhole, finite-window RSG conversion,
> correction/filler data, the final §2 interval assembly, all Corollary 7
> cases, and the FC wrappers are fully proven.
> See [§ Current state](#current-state).

The May 3 2026 proof (GPT-5.5 Pro, cleaned up by Liam Price; Kevin Barreto
noticed #351 follows) resolves both problems simultaneously.

**Erdős #283.** For every `p ∈ ℚ[x]` integer-valued on ℤ with positive leading
coefficient and no fixed divisor, every sufficiently large integer `m` is
expressible as `p(n_1) + ⋯ + p(n_k)` with distinct `n_i` satisfying
`1/n_1 + ⋯ + 1/n_k = 1`. The proof in fact holds for any rational `α > 0`
in place of `1` — this is **Theorem 1** in the PDF.

**Erdős #351.** The set `{ p(n) + 1/n : n ∈ ℕ }` is strongly complete iff
`p = 0` or `p` has positive leading coefficient (negative leading coefficient
is impossible — the set is bounded above). The corrected **Corollary 7** in
the PDF, formalized as `corollary_7` and `not_strongly_complete_of_neg_leadingCoeff`.

The narrower upstream `formal-conjectures` target asks only the nonconstant
positive-leading case; the broader corrected statement is what we actually
prove.

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
| [`Switching.lean`](Switching.lean) | §1 `switchingPoly`, exact natDegree/leadingCoeff formulas, Lemma 6 (`switching_values_span_top`), `IntValued.comp_nat_mul_X`, `switchingPoly_intValued`, `intEval_switchingPoly_nat`, `scaledPatternDenoms`. |
| [`MainSlots.lean`](MainSlots.lean) | §2 construction objects: `P=36`, `u`, `D`, `tau`, `E0`, `A`, `Dpoly`, `theta`, telescoping, leading coeff equalities. |
| [`Collision.lean`](Collision.lean) | §2 valuation profiles (`u_coprime_six`, `D_coprime_six`, `main_valuation_profile`, `tau_valuation_profile`, `filler_v2_at_least_three`). |
| [`Corrections.lean`](Corrections.lean) | §2 correction-slot subset-sum residue cover + density argument (`exists_large_correction_denominator`). |
| [`Theorem1.lean`](Theorem1.lean) | §2 main theorem. |
| [`Corollary351.lean`](Corollary351.lean) | §3 Corollary 7 (zero, positive-leading, negative-leading cases). |
| [`FC.lean`](FC.lean) | §4 `formal-conjectures` upstream wrappers `Erdos283.erdos_283` and `Erdos351.erdos_351`. |
| [`Proof.lean`](Proof.lean) | Umbrella — imports all of the above. |
| [`proof.pdf`](proof.pdf) | GPT-5.5 Pro + Liam Price, *Polynomial Egyptian Sums*, 3 May 2026. |
| [`informal.md`](informal.md) | Human-readable proof outline matching the PDF section-by-section. |
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target/spec surface. |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P283.Proof
```

**Online:** unlike #694 and #750, P283 is split across 10 modules with
project-local imports (`import Erdos.P283.Theorem1`, etc.). The browser
build at `live.lean-lang.org` resolves only `import Mathlib` and cannot see
project-local modules, so the umbrella `Proof.lean` here cannot be loaded
directly — clone the repo and `lake build` instead.

A single-file flat version (concatenating all 10 modules into one
`import Mathlib` file) would be ~10 000 lines and is not currently
maintained; if there's demand we can generate one. Individual modules can
be browsed on GitHub.

`lake build Erdos.P283.Proof` succeeds with **zero P283 lint warnings**.
Public-API hypotheses that the current proof body doesn't use (e.g. `hm` in
`polynomial_periodicity`, `h_nonconst`/`h_lead_pos` in `switching_values_span_top`)
are kept named for documentation and have local `set_option
linter.unusedVariables false in` annotations.

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
| `Corrections.lean` | 0 |
| `Theorem1.lean` | 0 |
| `Corollary351.lean` | 0 |
| `FC.lean` | 0 (`erdos_283`, `erdos_351` bridges complete) |

**Total: 0 executable sorries remaining in P283.**

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
| `lambdaConst`, `muConst`, `lambdaConst_lt_muConst`, `muConst_lt_a_theta_P`, positivity | ✅ proved |
| `Dpoly_natDegree`, `Dpoly_leadingCoeff`, `Dpoly_intValued` | ✅ proved |
| `A_comp_Dpoly_natDegree`, `A_comp_Dpoly_leadingCoeff`, `A_comp_Dpoly_intValued`, positivity, `A_comp_Dpoly_eval_at_succ` | ✅ proved |
| `qPoly`, `qPoly_natDegree`, `qPoly_leadingCoeff`, `qPoly_leadingCoeff_pos`, `qPoly_natDegree_pos`, `qPoly_eval_at_succ` | ✅ proved |
| `MainChoice`, `MainGCDData` records (numerator + gcd-data interface for theorem_1 case neg) | ✅ defined + constructors proven |
| `CorrectionData`, `FillerData` records (correction-slot + filler-denominator interfaces) | ✅ defined |
| `chooseCorrectionData_g_eq_one` (trivial CorrectionData when gcd.g = 1) | ✅ proved |
| `CorrectionResidueData`, `chooseCorrectionResidueData` (finite switching generators + duplicated subset-sum cover) | ✅ proved |
| `exists_correction_slot_congruent`, `exists_correction_slot_for_generator` (single large collision-free correction slot preserving residue) | ✅ proved |
| `exists_ordered_correction_slots`, `exists_recip_sum_lt_of_large`, `chooseCorrectionData_g_ge_two` | ✅ proved |
| `chooseFillerData` — Λ choice + reciprocal sum identity + collision avoidance | ✅ proved |
| `main_window_finite` — finite-window consequence of RSG under the tail-bound hypothesis | ✅ proved |
| `Bstar`, `M0`, `baseInt` bookkeeping definitions; correction subset divisibility/bounds | ✅ defined/proved |
| `IsEgyptianPattern.sum_scaled_recip`, `scaledPatternDenoms_*`, `switchingPoly_eval_nat`, `intEval_switchingPoly_nat`, slot switch p-sum identities | ✅ proved |
| Final denominator index layer (`FinalIndex`, `finalIndexDenom`, `finalIndex_sum`, reciprocal/p-sum splits, witness finalizers) | ✅ proved |
| Attainable-interval algebra core (`main_window_integer_subset`, `select_subsets_from_rsg_interval`, `attainable_interval_core`) | ✅ proved modulo collision/asymptotic hypotheses |
| Collision helpers (`D_strictMono`, `tau_strictMono`, main/tau/filler/correction wrappers, same-block injectivity lemmas) | ✅ proved |
| `u_coprime_six`, `D_coprime_six`, `main_valuation_profile`, `tau_valuation_profile`, `filler_v2_at_least_three` | ✅ proved |
| `duplicated_generators_subset_sum_all_residues` | ✅ proved |
| `exists_large_correction_denominator` (density / sieve argument via pigeonhole) | ✅ proved |
| `theorem_1` constant case (deg p = 0; via Lemma 3 + `NoFixedDivisor` ⇒ `p = 1`) | ✅ proved |
| `theorem_1` polynomial case final assembly (1 ≤ deg p; RSG inputs, correction/filler data, attainable intervals, and interval overlap) | ✅ proved |
| `corollary_7_zero` (`p = 0` case via Lemma 3) | ✅ proved |
| `corollary_7_pos_leading` (positive lead coeff; q := D·p/h reduction + Mahler ℕ→ℤ + MVT eventual injectivity) | ✅ proved |
| `not_strongly_complete_of_neg_leadingCoeff` | ✅ proved |
| `Erdos283.erdos_283` (FC iff form) | ✅ proved |
| `Erdos351.erdos_351` (FC iff form) | ✅ proved |

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

## Verifying with SafeVerify

[SafeVerify](https://github.com/GasStationManager/SafeVerify) replays each
declaration through the kernel via `Environment.replay`, enforces a hard
axiom allow-list, and bans `partial` / `unsafe` constants.

Our proof depends on one named axiom beyond `{propext, Quot.sound,
Classical.choice}` — `PolynomialEgyptianSums.roth_szekeres_graham`.
SafeVerify's default allow-list needs to be extended with this name; the
extension is local to this problem.

**Reproduction** (assumes a clone of SafeVerify pinned to
`leanprover/lean4:v4.27.0` — the same toolchain this repo uses):

```bash
# 1. Build this repo so all P283 oleans exist.
cd erdos-formalizations
lake exe cache get
lake build

# 2. Build the SafeVerify target spec to .olean.
lake env lean -o Erdos/P283/safeverify/Spec.olean Erdos/P283/safeverify/Spec.lean

# 3. In your SafeVerify clone, extend `allowedAxioms` (Main.lean line 355)
#    with the axiom used by this proof:
#
#      allowedAxioms := #[`propext, `Quot.sound, `Classical.choice,
#        `PolynomialEgyptianSums.roth_szekeres_graham]
#
#    Then `lake exe cache get && lake build`.

# 4. Run the check (LEAN_PATH must include this repo's .lake build dir
#    so SafeVerify can resolve `Erdos.P283.Proof`):
cd /path/to/SafeVerify
LEAN_PATH="/path/to/erdos-formalizations/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)" \
  lake exe safe_verify --verbose --disallow-partial \
    /path/to/erdos-formalizations/Erdos/P283/safeverify/Spec.olean \
    /path/to/erdos-formalizations/.lake/build/lib/lean/Erdos/P283/Proof.olean
```

Expected output ends with `SafeVerify check passed.` — verified locally
with the spec covering 21 declarations (definitions + Lemmas 3-5,
`intEval_spec`, `theorem_1`, all three Corollary 7 cases, `corollary_7`
umbrella, FC wrappers `Erdos283.erdos_283` and `Erdos351.erdos_351`).

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
