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

⚠ This file is currently a scaffold. All proof bodies are `sorry` placeholders;
the structure is designed so each sub-file can be filled in independently.
-/

import Erdos.P283.Theorem1
import Erdos.P283.Corollary351
import Erdos.P283.FC
