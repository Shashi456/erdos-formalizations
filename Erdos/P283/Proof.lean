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

This umbrella re-exports the split development. The proof is substantially
complete: §1 (Lemmas 3-6), all §2 sub-lemmas (asymptotic constants, valuation
profiles, telescoping, switching-polynomial structural facts, rescaled-polynomial
numerator infrastructure, correction-slot residue cover), §3 Corollary 7's zero
and negative-leading cases, and the §4 FC wrappers (`erdos_283`, `erdos_351`)
are all proven. Three sorries remain, all genuinely substantial:

  1. `theorem_1` polynomial case (`case neg`) in `Theorem1.lean` — the §2
     main-theorem assembly using RSG, correction slots, and intervals.
  2. `exists_large_correction_denominator` in `Corrections.lean` — the
     density / sieve argument for avoiding finitely many forbidden values
     in an arithmetic progression.
  3. `corollary_7_pos_leading` in `Corollary351.lean` — both the constant
     `p = C c, c > 0` case (Euclidean-division reduction to Lemma 3) and the
     polynomial reduction `q := D·p/h` via `theorem_1`.
-/

import Erdos.P283.Theorem1
import Erdos.P283.Corollary351
import Erdos.P283.FC
