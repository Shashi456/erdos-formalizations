/-
Erdős Problem 202 — analytic stub for the dyadic-interval prime cardinality
bound (Chebyshev-style).

# Status

This file isolates the ONE analytic gap from the BFV lower-construction prime
supply in `Erdos/P202/BFV/PrimeIntervals.lean`. The statement here is the
consumer-shaped lower bound used by `lowerQ_card_lower_bound_eventually`.
The body is `sorry`; the proof is a focused upstream-Mathlib subproject.

# Classical content

Chebyshev (1850) proved that there exist absolute constants `c_1, c_2 > 0`
with `c_1 · y / log y ≤ π(y) ≤ c_2 · y / log y`. Subtracting gives, for
some absolute `c > 0`,
  `π(2y) − π(y) ≥ c · y / log y`  for all sufficiently large `y`.

Mathlib `v4.27.0` already has Chebyshev's `θ`-function bounds
(`Nat.theta_le`, `Nat.theta_le_id`, `Nat.id_lt_theta`, etc.) and the
prime-counting function `Nat.primeCounting`. What is NOT packaged is the
Chebyshev-style dyadic-interval lower bound `π(2y) − π(y) ≥ c · y / log y`
nor its `(1 − ε) · y / log y` PNT-strength refinement.

The `(1 − ε)` form below is stronger than Chebyshev: it is true by the prime
number theorem, but for the BFV construction we only need any positive
absolute constant `c`. The current statement keeps the codex-produced
signature for compatibility; a follow-up refactor can weaken to a Chebyshev
constant if PNT is too heavy.

# Where this is consumed

* `Erdos.P202.BFV.PrimeIntervals.dyadicPrimeInterval_card_lower_bound`
* downstream: `Erdos.P202.BFV.LowerConstruction.lowerQ_card_lower_bound_eventually`
  → `Erdos.P202.BFV.LowerBoundInput.bfv_lower_bound_theorem`
  → ultimately replaces `axiom Erdos202.bfv_lower_bound_input`.

# Discharge sketch

To close this `sorry` one needs, in dependency order:

1. Chebyshev (or PNT) lower bound `π(2y) − π(y) ≥ c · y / log y` derived from
   `Nat.theta_le` and `Nat.id_lt_theta`. Standalone Mathlib-PR-style target.
2. Conversion from `π(2y) − π(y)` to the cardinality of
   `dyadicPrimeInterval y = (Finset.Ioc (⌊y⌋) (⌊2y⌋)).filter Nat.Prime`,
   accounting for the floor endpoints. Mechanical once (1) lands.

If the consumer can accept a Chebyshev constant `c` rather than `(1 − ε)`,
the upstream burden drops sharply: no PNT, just Chebyshev's two-sided
`θ`-bounds. The downstream `Lscale (-(1 + ε), N)` swallow the constant.
-/

import Mathlib
import Erdos.P202.BFV.PrimeIntervals

namespace Erdos202

open Filter Finset

/-- **Analytic gap (Chebyshev / PNT-in-short).** Lower bound for the number
of primes in a dyadic interval, in the `(1 − ε)` form used by the BFV
construction.

For every `ε > 0`, eventually in `y : ℝ`,
  `⌊(1 − ε) · y / log y⌋ ≤ (dyadicPrimeInterval y).card`.

The proof comes from Chebyshev's two-sided `θ`-bounds (already in Mathlib);
the `(1 − ε)` factor is PNT-strength and can be weakened to a Chebyshev
constant if needed (the downstream `Lscale` absorbs the difference).

Consumed by `Erdos.P202.BFV.LowerConstruction.lowerQ_card_lower_bound_eventually`. -/
theorem dyadicPrimeInterval_card_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ y : ℝ in atTop,
      Nat.floor (((1 - ε) * y) / Real.log y) ≤
        (dyadicPrimeInterval y).card := by
  sorry

end Erdos202
