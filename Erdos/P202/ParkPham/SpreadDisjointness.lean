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

The translation from "muP ≥ 1/2" to "∃ r pairwise-disjoint members"
(steps 2-4) is purely finite/discrete bookkeeping with no analytic
content — it lives entirely above `park_pham_threshold`. We isolate
it as a named theorem-shaped axiom `partition_density_to_disjoint_members`
so that this file proves `spread_disjointness_theorem` cleanly.
-/

import Mathlib
import Erdos.P202.SpreadDefs
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

end

/-- **Random-partition bookkeeping** (Park–Pham PDF Proposition 2.1 / Cor 2.3
final step). Once `muP X (upClosureIn X A) (1/(2r)) ≥ 1/2` is in hand
(via `mu_at_partition_density_ge_half`), the random-partition argument —
viewing the Bernoulli measure as the marginal of a uniform random `2r`-
coloring of `X`, then a double-counting argument over colorings — produces
`r` pairwise-disjoint members of `A`.

This is **purely finite combinatorics** with no analytic content; it
isolates the discrete random-partition translation into a named target
that can be discharged separately from the Park–Pham analytic core
(`park_pham_threshold`).

The proof strategy is:
1. Re-express `muP` as the average over uniform colorings of the
   indicator "some color class contains a member of A".
2. By the `muP ≥ 1/2` hypothesis combined with a union bound over the
   `2r` colors, the expected number of "successful" color classes is at
   least `r`.
3. Pick a coloring witnessing this; pick a member of A inside each
   successful color class; color classes are pairwise disjoint, so the
   picked members are pairwise disjoint. -/
axiom partition_density_to_disjoint_members :
    ∀ {α : Type*} [DecidableEq α]
      (X : Finset α) (A : Finset (Finset α)) (r k : ℕ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      Erdos202.UniformFamily A k →
      (∀ S ∈ A, S ⊆ X) →
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B

section

variable {α : Type*} [DecidableEq α]

/-- **Spread-disjointness theorem** (PDF Proposition 2.1 / Corollary 2.3).

Matches `axiom Erdos202.spread_disjointness_input` in `SpreadCore.lean`.

Proved against the named stubs:
* `park_pham_threshold` (the deep Park–Pham analytic gap)
* `partition_density_to_disjoint_members` (the finite random-partition
  bookkeeping that lifts `muP ≥ 1/2` to `r` pairwise-disjoint members) -/
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
  -- Ground universe: X = ⋃_{S ∈ A} S
  let X : Finset α := A.biUnion id
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hSA x hxS
    exact Finset.mem_biUnion.mpr ⟨S, hSA, hxS⟩
  -- Step 1: muP ≥ 1/2 from the Park–Pham layer.
  have hmu :
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 :=
    mu_at_partition_density_ge_half hA hr hk hUniform hSpread hAX hκ
  -- Step 2: random-partition translation.
  exact partition_density_to_disjoint_members X A r k hA hr hk hUniform hAX hmu

end

end ParkPham
end Erdos202
