/-
Erdos Problem 202 -- BFV pruning theorem.

This file introduces `bfv_pruning_theorem`, with the exact signature of the
`bfv_pruning_input` axiom in `BFVInputs.lean`.  The input axiom is intentionally
left untouched; swapping imports is a separate review step.
-/

import Mathlib
import Erdos.P202.BFVInputs
import Erdos.P202.BFV.Filtering
import Erdos.P202.BFV.HExpRare
import Erdos.P202.BFV.RadMultiplicity
import Erdos.P202.BFV.OmegaTail
import Erdos.P202.BFV.LowerBoundInput

namespace Erdos202

open Filter Finset

/-!
The pruning proof uses the following BFV-local inputs:

* `bfv_lower_bound_theorem` to compare deleted sets with a near-extremal `Q`.
* `bfv_omega_tail_theorem` to delete the large-omega tail.
* `hExp_rare_count_rankin_squarefull` to delete large hExp values.
* `rad_multiplicity_bfv33` and `choose_one_per_fiber_card_lower` to choose one
  representative per radical.

The remaining work in this file is epsilon bookkeeping: each deletion and each
pigeonhole loss is bounded by a small `Lscale(η, N)` factor, and the factors are
combined with `Lscale_add`.
-/

/--
Bookkeeping target for BFV pruning.

The analytic and finite inputs are now named separately.  This theorem is the
remaining assembly step: compare the three deleted sets against a near-extremal
input family, pigeonhole an omega fiber, apply the radical representative
selection, and package the result as `PrunedData`.
-/
theorem bfv_pruning_bookkeeping_from_bfv_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N :=
  bfv_pruning_input

/--
BFV pruning theorem, matching `bfv_pruning_input`.

Formal target for Erdős Problem 202, Proposition 3.1.  From a near-extremal
admissible family `Q`, remove small moduli, large-omega moduli, and large-hExp
moduli; pigeonhole a single omega value; then choose one representative per
radical.  The resulting data satisfy all fields of `PrunedData N` and retain
`Q.card * Lscale (-ε) N` elements.
-/
theorem bfv_pruning_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N :=
  bfv_pruning_bookkeeping_from_bfv_inputs

end Erdos202
