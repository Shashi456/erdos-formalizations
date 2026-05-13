/-
Erdos Problem 202 -- BFV lower-bound theorem.

This file proves the theorem with the same signature as
`Erdos202.bfv_lower_bound_input`, using the named lower construction from
`LowerConstruction.lean`.
-/

import Mathlib
import Erdos.P202.BFV.LowerConstruction

namespace Erdos202

open Filter

/-- BFV lower-bound theorem, matching the old input axiom's signature. -/
theorem bfv_lower_bound_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  intro ε hε
  filter_upwards [lower_possibleCard ε hε] with N hPossible
  have hceil_le_f :
      Nat.ceil (bfvLowerTarget ε N) ≤ f N :=
    le_f_of_possibleCard hPossible
  have htarget_le_ceil :
      bfvLowerTarget ε N ≤ (Nat.ceil (bfvLowerTarget ε N) : ℝ) :=
    Nat.le_ceil (bfvLowerTarget ε N)
  exact htarget_le_ceil.trans (by exact_mod_cast hceil_le_f)

end Erdos202
