/-
Erdos Problem 202 -- BFV lower-bound theorem.

This file proves the theorem with the same signature as
`Erdos202.bfv_lower_bound_input`, using the source-aligned rooted path lower
construction from `LowerPathConstruction.lean`.
-/

import Mathlib
import Erdos.P202.BFV.LowerPathConstruction

namespace Erdos202

open Filter

/-- BFV lower-bound theorem, matching the old input interface. -/
theorem bfv_lower_bound_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) :=
  lowerPath_f_lower_bound_eventually

end Erdos202
