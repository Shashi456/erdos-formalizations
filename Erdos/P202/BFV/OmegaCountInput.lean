/-
Erdos Problem 202 -- theorem-shaped BFV omega-count input.

This file exposes the theorem name intended to replace
`Erdos202.bfv_omega_count_input` in a later review step.
-/

import Mathlib
import Erdos.P202.BFV.OmegaExact

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- Proven replacement target for `bfv_omega_count_input`.

At present this theorem depends on `bfv_omega_tail_theorem`, whose analytic
Euler-product component is still a `sorry` in `OmegaTail.lean`. -/
theorem bfv_omega_count_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) :=
  bfv_omega_exact_theorem

end Erdos202
