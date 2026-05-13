/-
Erdős Problem 202 — Spread / dense-core layer, definitions.

Bare definitions only: `UniformFamily`, `SpreadFamily`,
`PairwiseDisjointMembers`. Split out from `SpreadCore.lean` so the
ParkPham layer can use these definitions without importing the
spread-disjointness axiom/theorem (which would create an import cycle
once `SpreadCore.lean` discharges the axiom against the ParkPham proof).
-/

import Mathlib

namespace Erdos202

open Finset
open scoped BigOperators

/-- A `k`-uniform family: every member has cardinality exactly `k`. -/
def UniformFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ S ∈ A, S.card = k

/-- A `κ`-spread family: for every nonempty `T`, the count of members
containing `T` is at most `|A| / κ^{|T|}`. -/
def SpreadFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (κ : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty →
    ((A.filter fun S => T ⊆ S).card : ℝ) ≤
      (A.card : ℝ) / κ ^ T.card

/-- Members of `B` are pairwise disjoint. -/
def PairwiseDisjointMembers {α : Type*} [DecidableEq α]
    (B : Finset (Finset α)) : Prop :=
  ∀ S ∈ B, ∀ T ∈ B, S ≠ T → Disjoint S T

end Erdos202
