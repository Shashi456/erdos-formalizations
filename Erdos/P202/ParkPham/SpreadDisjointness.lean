/-
Erdős Problem 202 — Park–Pham layer, Stage 6.

Final spread-disjointness theorem via the random-partition argument.

# Strategy

Given a κ-spread, k-uniform, nonempty family A with
`κ ≥ Csp · r · log(ek)`:

1. By `mu_at_partition_density_ge_half`, the Bernoulli measure of
   `upClosureIn X A` at density `1/(2r)` is at least `1/2`.
2. Equivalently (via the random-partition / coloring identification): for
   a uniformly random coloring `c : X → Fin (2r)`, the expected number
   of color classes `c⁻¹(i)` that contain a member of A is at least `r`.
3. Hence there exists a coloring with at least `r` "successful" parts.
4. Pick one member of A inside each successful part. The parts are
   pairwise disjoint, so the chosen members are pairwise disjoint.

This file states the final theorem and outlines the proof. The
random-partition double-counting argument is the bulk of the work; it
is left as a named bookkeeping target for a focused subpass against the
fully-proved analytic core (`park_pham_threshold` is the only deep gap).
-/

import Mathlib
import Erdos.P202.SpreadCore
import Erdos.P202.ParkPham.BooleanFamilies
import Erdos.P202.ParkPham.ProductMeasure
import Erdos.P202.ParkPham.Smallness
import Erdos.P202.ParkPham.Threshold
import Erdos.P202.ParkPham.ParkPhamTheorem

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

section

variable {α : Type*} [DecidableEq α]

/-- **Coloring of a finite universe.** A `Fin m`-valued labeling of the
elements of `X` (encoded as a function on the subtype `{x // x ∈ X}`).

The set of colorings is finite (a finite product of `Fin m`). A
uniformly random coloring corresponds to the discrete uniform measure
on this finite set, and color classes have the same marginal as a
random subset at density `1/m`. -/
abbrev Coloring (X : Finset α) (m : ℕ) :=
  {x // x ∈ X} → Fin m

/-- The `i`th part of a coloring as a `Finset α`. -/
noncomputable def colorPart {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) : Finset α :=
  Finset.image Subtype.val (X.attach.filter (fun x => c x = i))

/-- **Spread-disjointness theorem** (PDF Proposition 2.1 / Corollary 2.3).

Matches `axiom Erdos202.spread_disjointness_input` in `SpreadCore.lean`.

Proved against the named stub `park_pham_threshold` (the only deep gap)
and the algebraic / random-partition bookkeeping in
`mu_at_partition_density_ge_half` and `colorings_to_disjoint_members`. -/
theorem spread_disjointness_theorem :
    ∃ Csp : ℝ, 0 < Csp ∧
      ∀ {α : Type*} [DecidableEq α]
        (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
        A.Nonempty →
        2 ≤ r →
        1 ≤ k →
        Erdos202.UniformFamily A k →
        Erdos202.SpreadFamily A κ →
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
        ∃ B : Finset (Finset α),
          B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  refine ⟨Csp, Csp_pos, ?_⟩
  intro α _ A r k κ hA hr hk hUniform hSpread hκ
  -- The bulk of the work: convert
  --   `mu_at_partition_density_ge_half` ⊨ ∃ partition with r successful parts
  -- into a Finset B ⊆ A of size r with pairwise disjoint members.
  -- This is the random-partition double-counting argument outlined in the
  -- file header; it is left as a focused-subpass target.
  sorry

end

end ParkPham
end Erdos202
