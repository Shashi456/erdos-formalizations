/-
Erdős Problem 202 — Park–Pham layer, Stage 4.

# Status

This file isolates the Park–Pham / Kahn–Kalai expectation-threshold theorem
as a single named theorem-shaped axiom. It is **the** big named
analytic-combinatorial gap for Park–Pham; everything else in `ParkPham/`
is proved against this stub.

# Classical content

The Kahn–Kalai expectation-threshold conjecture, proved by Jinyoung Park
and Huy Tuan Pham in 2022 (arXiv:2203.17207), states roughly:

  For every increasing family `U` on a finite ground set `X`, the actual
  threshold `p_c(U)` differs from the expectation threshold `q(U)` by at
  most a logarithmic factor:
        `p_c(U) ≤ C · q(U) · log(ℓ(U))`
  for an absolute constant `C` and a complexity parameter
  `ℓ(U) := max(2, max cardinality of minimal members of U)`.

In the finite form below we phrase the conclusion as: if `q` is an upper
bound on the expectation threshold (in the sense of `qSmallUpper`), then
at density `p = C · q · log(ℓ(U))` the product measure `muP X U p` is at
least `1/2`.

# Shape decision

The constant `C_KK` is exposed as a **top-level** axiom-defined real,
not as an existential `∃ C, ...`. This is deliberate: composing
`Classical.choose` of a universe-polymorphic existential with downstream
`muP X U p` goals blew past 2M heartbeats during `whnf` elaboration on
the previous existential form (see
`feedback_lean_classical_choose_elaboration.md`). Exposing the constant
directly lets downstream consumers reason about it with no
`Classical.choose` overhead.

# Mathlib status

Mathlib `v4.27.0` has no expectation-threshold infrastructure. Discharging
this stub is a substantial standalone subproject — likely a multi-file
formalization following the Park–Pham proof, ultimately a Mathlib-PR-style
target.
-/

import Mathlib
import Erdos.P202.ParkPham.BooleanFamilies
import Erdos.P202.ParkPham.ProductMeasure
import Erdos.P202.ParkPham.Smallness

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

/-- The Park–Pham / Kahn–Kalai expectation-threshold absolute constant.

Exposed as a top-level axiom (not inside an existential) so downstream
composition with `muP`-shaped goals does not trigger `Classical.choose`
elaboration blowup. -/
axiom CKK_const : ℝ

/-- Positivity of the Park–Pham constant. -/
axiom CKK_const_pos : 0 < CKK_const

/-- **Park–Pham expectation-threshold theorem** (Kahn–Kalai conjecture,
arXiv:2203.17207, proved by J. Park and H. T. Pham, 2022).

If `q` upper-bounds the expectation threshold of an increasing family
`U`, then the product measure at any density `p` at or above
`C_KK · q · log(ℓ(U))` is at least `1/2`.

(The "any `p` at or above" form bakes in `muP` monotonicity-in-density for
increasing families — itself a non-trivial FKG-type result — into the
single named stub, so downstream consumers do not need to re-prove it.)

This is the single named upstream-Mathlib target for the Park–Pham layer.
All downstream Park–Pham theorems are proved against this stub. -/
axiom park_pham_threshold :
    ∀ {α : Type*} [DecidableEq α]
      (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
      0 < q → q ≤ 1 →
      0 ≤ p → p ≤ 1 →
      CKK_const * q * Real.log (ell X U) ≤ p →
      IncreasingIn X U →
      qSmallUpper X U q →
      muP X U p ≥ 1 / 2

end ParkPham
end Erdos202
