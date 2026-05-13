/-
Erdős Problem 202 — Park–Pham layer, Stage 3.

The `p`-small predicate underlying the Kahn–Kalai expectation threshold:
a family `U` is `p`-small if some "cover" `G` (a finite family whose
upper closure contains `U`) has total `p`-weight at most `1/2`.

`qSmallUpper X U q` asserts that `U` is NOT `p`-small for any `p > q`,
i.e. the threshold lies in `[0, q]`. This is the form consumed by the
Park–Pham theorem in `Threshold.lean`.
-/

import Mathlib
import Erdos.P202.ParkPham.BooleanFamilies

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- `G` covers `U` inside `X`: every member of `U` contains some member of
`G`. -/
def CoversIn (X : Finset α) (G U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∃ T ∈ G, T ⊆ S

/-- A family `U` is `p`-small inside `X` if there is a cover `G` with
total weight `∑ p^|T|` at most `1/2`. -/
def pSmall (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  ∃ G : Finset (Finset α),
    CoversIn X G U ∧ (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)

/-- `qSmallUpper X U q`: `U` is not `p`-small for any strictly larger `p`. -/
def qSmallUpper (X : Finset α) (U : Finset (Finset α)) (q : ℝ) : Prop :=
  ∀ p : ℝ, q < p → p ≤ 1 → ¬ pSmall X U p

end

end ParkPham
end Erdos202
