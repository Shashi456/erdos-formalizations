/-
Erdős Problem 202 — Main theorem.

Combines:
  * upper bound from `Optimization.f_upper_bound`
    (Chain inequality + σ optimization, conditional on the BFV inputs and
     the spread-disjointness input);
  * lower bound from `bfv_lower_bound_theorem`.

The historical omega-count and lower-bound input names now point to fully
proved theorems.  The trust boundary is empty beyond Lean core: running
`#print axioms Erdos202.erdos202_main` should print only
`propext`, `Classical.choice`, `Quot.sound`.

This file formalizes the sharp asymptotic for Erdős Problem 202
(PDF Theorem 1.1).  The integral / partial-summation Corollary 1.2
about Erdős Problem 1190 is NOT formalized.

Audit by uncommenting the `#print axioms` block below.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic
import Erdos.P202.SpreadCore
import Erdos.P202.BFVInputs
import Erdos.P202.P202Chain
import Erdos.P202.BFV.LowerBoundInput
import Erdos.P202.P202Optimization

namespace Erdos202

open Filter
open scoped BigOperators

/-- **Conditional Erdős 202 upper bound.** From the BFV pruning theorem layer,
omega-count theorem layer, and spread theorem layer, the upper half of the
asymptotic holds. -/
theorem erdos202_upper_bound_from_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N :=
  f_upper_bound

/-- **Erdős Problem 202 — main theorem.** The sharp BFV asymptotic
`f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`. -/
theorem erdos202_main : Erdos202Statement := by
  intro ε hε
  filter_upwards [bfv_lower_bound_theorem ε hε, f_upper_bound ε hε] with N hLow hUp
  exact ⟨hLow, hUp⟩

/-! ## Axiom audit

The block below audits the public theorem path.  The expected output is
exactly the three Lean foundational axioms `propext`, `Classical.choice`,
and `Quot.sound` — no project-level axioms remain.
-/

-- #print axioms erdos202_upper_bound_from_inputs
-- #print axioms erdos202_main

end Erdos202
