/-
Erdős Problems 283 + 351 — Polynomial Egyptian sums.

**Umbrella file** that imports the split modules:

  Erdos.P283.Basic              — IntValued / NoFixedDivisor / HasIntegralMultiple,
                                  the `roth_szekeres_graham` theorem wrapper.
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
*Polynomial Egyptian Sums*, 3 May 2026 — `compact_cayley_proof.pdf` in this directory.

This umbrella re-exports the split development. The proof is complete with no
problem-specific axioms: `roth_szekeres_graham` is now derived from the
`Erdos.P283.RSG` Graham 1964 formalization. No executable `sorry` or `admit` remains
in the P283 modules.

The full proof is structured around these named interfaces:

  * `chooseMainChoice` ✓        — J threshold via real-cast + tendsto.
  * `chooseMainGCDData` ✓        — g extraction + gcd-quotient bridge.
  * `main_window_representation` ✓ — direct RSG invocation.
  * `main_window_finite` ✓       — finite-window consequence under tail bound.
  * `chooseCorrectionResidueData` ✓ — finite generators + duplicated residue cover.
  * `exists_correction_slot_for_generator` ✓ — one large collision-free correction slot.
  * `chooseCorrectionData_g_ge_two` ✓ — full nontrivial correction-data constructor.
  * `chooseFillerData` ✓         — filler reciprocal identity + collision fields.
  * `attainable_interval` ✓        — every m ∈ I_N representable for parameter N.
  * `intervals_overlap_eventually` ✓ — overlap of I_N and I_{N+1}.
  * Final assembly ✓               — pick N, invoke attainable_interval.
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
    `scaledPatternDenoms_*`, `switchingPoly_eval_nat`, `intEval_switchingPoly_nat`,
    slot switch p-sum identities
  * Correction interfaces: `chooseCorrectionResidueData`,
    `exists_correction_slot_congruent`, `exists_correction_slot_for_generator`,
    `exists_ordered_correction_slots`, `exists_recip_sum_lt_of_large`,
    `chooseCorrectionData_g_ge_two`, `correction_subset_dvd_with_bounds`
  * Final assembly interfaces: `FinalIndex`, `finalIndex_sum`,
    `finalIndex_recip_sum`, `finalIndex_intEval_sum`,
    `witness_from_selected_subsets`, `main_window_integer_subset`,
    `select_subsets_from_rsg_interval`, `attainable_interval_core`,
    `attainable_interval`, `intervals_overlap_eventually`
  * Additional collision helpers: `D_strictMono`, `tau_strictMono`,
    `main_copy_eq_of_eq`, `main_copy_ne_tau`, `filler_ne_tau`,
    `correctionMultiplierMax`, and same-block injectivity lemmas

The following formerly depended on the trust-boundary axiom
`roth_szekeres_graham`; after the RSG formalization they also have only Mathlib
core axioms:

  * `PolynomialEgyptianSums.main_window_representation`
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
