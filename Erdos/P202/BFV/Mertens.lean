/-
Erdős Problem 202 — analytic stub for the Mertens / Euler-product estimate.

# Status

This file isolates the ONE analytic gap from the BFV omega-tail proof in
`Erdos/P202/BFV/OmegaTail.lean`. The statement here is the consumer-shaped
weighted-sum bound used by Rankin's inequality. The body is `sorry` and
the proof is a focused upstream-Mathlib subproject (see below).

# Relation to P694's `Erdos694.mertens_product`

The repo's `Erdos/P694/Proof.lean:417` axiomatizes **Mertens' third theorem**
(the product form `∏_{p ≤ y} p/(p-1) ~ e^γ · log y`). What this P202 stub
needs is Mertens' **second** theorem (`∑_{p ≤ y} 1/p ≤ log log y + C`), which
is derivable from Mertens 3rd by taking logs:
  `log ∏_{p ≤ y} (1 - 1/p)^{-1} = ∑_{p ≤ y} (1/p + 1/(2 p²) + …)
                                = ∑_{p ≤ y} 1/p + O(1)`.

So the two stubs are **the same Mertens-axiom family**: discharging P694's
`mertens_product` (or upstreaming it into Mathlib) discharges what P202 needs
modulo a short derivation. A future cleanup should consolidate them into a
single `Erdos/Shared/Mertens.lean` and re-export from both problems.

# Classical content

The intended derivation factors through two classical inputs:

1. **Mertens' second theorem** (1874): there exists `C : ℝ` such that for all
   sufficiently large `N`,
   `∑_{p prime, p ≤ N} (1 / p : ℝ) ≤ Real.log (Real.log N) + C`.
   In Mathlib `v4.27.0`, the prime-counting function `Nat.primeCounting` and
   the Chebyshev `θ`-function are available (`Nat.Prime.theta_le`,
   `Nat.theta_le_id`, etc.), but the Mertens reciprocal-prime sum is NOT
   packaged. The proof is Abel summation against the Chebyshev `θ` bounds.
   (As noted above, this also follows from P694's `mertens_product`.)

2. **Hardy–Ramanujan / sieve identity**: for any `z ≥ 0` and `y ∈ ℕ`,
   `(∑ n ∈ Finset.Icc 1 y, z ^ omega n : ℝ) ≤ y * ∏_{p ≤ y} (1 + z / p)`.
   This is a standard upper-bound sieve and is also currently absent from
   Mathlib for `omega = Nat.factorization.support.card`.

Combining (1) and (2): with `BFVz N := √(log N) / log log N`,
  `∏_{p ≤ N} (1 + BFVz N / p)
     ≤ Real.exp (BFVz N * ∑_{p ≤ N} 1 / p)
     ≤ Real.exp (BFVz N * (Real.log (Real.log N) + C))`,
which is `≤ Real.exp (ε * Zscale N)` eventually for any `ε > 0`, since
`BFVz N · log log N = √(log N) = Zscale N · (1 + o(1)) / √(log log N) = o(Zscale N)`.

# Where this is consumed

* `Erdos.P202.BFV.OmegaExact` → `Erdos.P202.BFV.OmegaCountInput` →
  ultimately replaces `axiom Erdos202.bfv_omega_count_input`.

# Discharge sketch

To close this `sorry` one needs, in dependency order:

1. A Lean-level Mertens reciprocal-prime sum lemma derived from
   `Nat.theta_le` via Abel summation. This is a standalone Mathlib-PR-style
   target (~200–500 lines).
2. The Hardy–Ramanujan sieve identity for `Nat.factorization.support.card`.
3. The Euler-product → exponential bookkeeping (mechanical once 1–2 land).
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- The BFV Rankin parameter `sqrt(log N) / log log N`. -/
noncomputable def BFVz (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ))

/-- **Analytic gap (Mertens + sieve).** Euler-product upper bound for the
weighted omega sum at the BFV scale.

For every `ε > 0`, eventually in `N`, for every `y ≤ N`:
  `∑_{n ≤ y} (BFVz N) ^ omega n ≤ y · exp(ε · Z(N))`.

The proof factors through Mertens' second theorem and the Hardy–Ramanujan
sieve identity (see the file header for details). Mathlib `v4.27.0` does not
package either; this lemma is a named upstream target. -/
theorem omega_weighted_sum_bfvz_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n ∈ Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) * Real.exp (ε * Zscale N) := by
  sorry

end Erdos202
