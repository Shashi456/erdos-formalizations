/-
Erdős Problems 283 + 351 — Polynomial Egyptian sums.

**Umbrella file** that imports the split modules:

  Erdos.P283.Basic              — IntValued / NoFixedDivisor / HasIntegralMultiple,
                                  the `roth_szekeres_graham` axiom.
  Erdos.P283.Egyptian           — Lemmas 3, 4 (Egyptian expansions / patterns).
  Erdos.P283.PolynomialPeriod   — Lemma 5 (polynomial periodicity).
  Erdos.P283.Switching          — switchingPoly + Lemma 6.
  Erdos.P283.MainSlots          — D, u, τ, A, telescoping, q.
  Erdos.P283.Corrections        — correction-slot construction.
  Erdos.P283.Collision          — v₂/v₃ collision avoidance.
  Erdos.P283.Theorem1           — main theorem assembly.
  Erdos.P283.Corollary351       — strong completeness, three cases.
  Erdos.P283.FC                 — formal-conjectures wrappers (Erdos283/Erdos351
                                  namespaces).

Following GPT-5.5 Pro + Liam Price (cleanup) + Kevin Barreto (noticed #351 follows),
*Polynomial Egyptian Sums*, 3 May 2026 — `proof.pdf` in this directory.

Trust boundary beyond Mathlib core (`propext`, `Quot.sound`, `Classical.choice`):
  PolynomialEgyptianSums.roth_szekeres_graham — Graham 1964 / Roth-Szekeres 1954.

This umbrella re-exports the split development. The proof is near completion:
§1 (Lemmas 3-6), all §2 sub-lemmas (asymptotic constants, valuation profiles,
telescoping, switching-polynomial structural facts, rescaled-polynomial
infrastructure, correction-slot residue cover, density argument via pigeonhole),
all three §3 Corollary 7 cases (zero, positive-leading, negative-leading), and
the §4 FC wrappers (`erdos_283`, `erdos_351`) are all proven. Only one sorry
remains:

  `theorem_1` polynomial case (`case neg`) in `Theorem1.lean` — the §2 final
  integrative assembly. All RSG inputs (`md`, `gcd`, `X_q`, `hX_q`) are ready;
  remaining work is the explicit denominator-list construction (correction slot
  selection via `duplicated_generators_subset_sum_all_residues`, main-slot
  switch via the window representation, filler via `egyptian_expansion`),
  StrictMono via collision-profile lemmas, dual sum verification, and the
  asymptotic interval-overlap argument.

  Note: `theorem_1` and `Erdos283.erdos_283` transitively depend on this sorry
  via `sorryAx`. `corollary_7_pos_leading` and `Erdos351.erdos_351` also
  transitively depend on it via the polynomial-case branch.

The full proof is structured around these named interfaces (most proven, one
remaining):

  * `chooseMainChoice` ✓        — J threshold via real-cast + tendsto.
  * `chooseMainGCDData` ✓        — g extraction + gcd-quotient bridge.
  * `main_window_representation` ✓ — direct RSG invocation.
  * `attainable_interval` (TODO)   — every m ∈ I_N representable for parameter N.
  * `intervals_overlap_eventually` (TODO) — overlap of I_N and I_{N+1}.
  * Final assembly                 — pick N, invoke attainable_interval.
-/

import Erdos.P283.Theorem1
import Erdos.P283.Corollary351
import Erdos.P283.FC

/-! ## Axiom audit

The following theorems are fully axiom-free (only `propext`, `Classical.choice`,
`Quot.sound`):

  * `PolynomialEgyptianSums.egyptian_expansion`             (Lemma 3)
  * `PolynomialEgyptianSums.egyptian_pattern_with_period`   (Lemma 4)
  * `PolynomialEgyptianSums.polynomial_periodicity`         (Lemma 5)
  * `PolynomialEgyptianSums.switching_values_span_top`      (Lemma 6)
  * `PolynomialEgyptianSums.exists_large_correction_denominator`
  * `PolynomialEgyptianSums.duplicated_generators_subset_sum_all_residues`
  * `PolynomialEgyptianSums.corollary_7_zero`
  * `PolynomialEgyptianSums.not_strongly_complete_of_neg_leadingCoeff`
  * All §1 structural lemmas (switchingPoly_natDegree_eq, _leadingCoeff_eq,
    intValued closure, etc.)
  * All §2 main-slot infrastructure (D_recip, main_telescoping,
    isEgyptianPattern_E0, A_leadingCoeff_eq, theta_gt_one, qPoly + asymptotic
    constants, Dpoly natDegree/leadingCoeff, A_comp_Dpoly_*)
  * All §2 collision-avoidance lemmas (u_coprime_six, D_coprime_six,
    main_valuation_profile, tau_valuation_profile, filler_v2_at_least_three)
  * `chooseMainChoice`, `chooseMainGCDData`, `qPoly_int_pos_on_pos`
  * Algebra interfaces: `IsEgyptianPattern.sum_scaled_recip`,
    `switchingPoly_eval_nat`

The following depend on the trust-boundary axiom `roth_szekeres_graham`:

  * `PolynomialEgyptianSums.main_window_representation`

The following depend on `roth_szekeres_graham` AND transitively on `sorryAx`
(via the unfinished `theorem_1` `case neg`):

  * `PolynomialEgyptianSums.theorem_1`
  * `PolynomialEgyptianSums.corollary_7_pos_leading`
  * `Erdos283.erdos_283`
  * `Erdos351.erdos_351`

Verify with `#print axioms` — uncomment the block below to inspect at build time.
-/

-- Uncomment to run the axiom audit at build time:
-- #print axioms PolynomialEgyptianSums.egyptian_expansion
-- #print axioms PolynomialEgyptianSums.egyptian_pattern_with_period
-- #print axioms PolynomialEgyptianSums.polynomial_periodicity
-- #print axioms PolynomialEgyptianSums.switching_values_span_top
-- #print axioms PolynomialEgyptianSums.exists_large_correction_denominator
-- #print axioms PolynomialEgyptianSums.corollary_7_zero
-- #print axioms PolynomialEgyptianSums.not_strongly_complete_of_neg_leadingCoeff
-- #print axioms PolynomialEgyptianSums.main_window_representation
-- #print axioms PolynomialEgyptianSums.theorem_1
-- #print axioms PolynomialEgyptianSums.corollary_7_pos_leading
-- #print axioms Erdos283.erdos_283
-- #print axioms Erdos351.erdos_351
