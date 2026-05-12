/-
Erdős Problem 202 — Main theorem.

Combines:
  * upper bound from `Optimization.f_upper_bound`
    (Chain inequality + σ optimization, conditional on the BFV inputs and
     the spread-disjointness input);
  * lower bound from `bfv_lower_bound_input`.

After all sorries are closed, the theorem will depend on three
project-level axioms — `spread_disjointness_input`, `bfv_pruning_input`,
`bfv_omega_count_input`, `bfv_lower_bound_input` — plus Mathlib core
(`propext`, `Classical.choice`, `Quot.sound`).

Audit by uncommenting the `#print axioms` block below.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic
import Erdos.P202.SpreadCore
import Erdos.P202.BFVInputs
import Erdos.P202.P202Chain
import Erdos.P202.P202Optimization

namespace Erdos202

open Filter
open scoped BigOperators

/-- **Conditional Erdős 202 upper bound.** From the four BFV / spread
inputs (the precise theorem-shaped axioms in `BFVInputs.lean` and
`SpreadCore.lean`), the upper half of the asymptotic holds. -/
theorem erdos202_upper_bound_from_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N :=
  f_upper_bound

/-- **Erdős Problem 202 — main theorem.** The sharp BFV asymptotic
`f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`. -/
theorem erdos202_main : Erdos202Statement := by
  intro ε hε
  filter_upwards [bfv_lower_bound_input ε hε, f_upper_bound ε hε] with N hLow hUp
  exact ⟨hLow, hUp⟩

/-! ## Axiom audit

Once all `sorry`s are closed in the supporting files, uncomment the block
below. Expected output (in addition to the standard Mathlib core axioms
`propext`, `Classical.choice`, `Quot.sound`):

  * `Erdos202.spread_disjointness_input`
  * `Erdos202.bfv_pruning_input`
  * `Erdos202.bfv_omega_count_input`
  * `Erdos202.bfv_lower_bound_input`

These four axioms are exactly the trust boundary of the formalization.
-/

-- #print axioms erdos202_upper_bound_from_inputs
-- #print axioms erdos202_main

end Erdos202
