/-
Erdős Problem 202 — Spread / dense-core layer.

The new ingredient in the May 2026 proof is the spread-core lemma replacing
the Erdős–Lovász / minimal-family loss in the BFV descending chain.

This file:
  * states the finite combinatorial spread-disjointness consequence of
    Park–Pham (Kahn–Kalai) as a theorem-shaped axiom;
  * derives the dense-core corollary used downstream.

Park–Pham theorem reference: arXiv:2203.17207. We do NOT formalize the full
expectation-threshold theorem here; we isolate exactly the finite consequence
the descending chain needs.
-/

import Mathlib
import Erdos.P202.P202Basic

namespace Erdos202

open Finset
open scoped BigOperators

universe u

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

/-! ## Spread-disjointness input (theorem interface) -/

/-- **Spread-disjointness input** — the finite consequence of Park–Pham
that the descending chain needs. There exists an absolute constant
`Csp > 0` such that any sufficiently spread `k`-uniform family contains
`r` pairwise disjoint members.

To be discharged by formalizing Park–Pham (Kahn–Kalai expectation-threshold
conjecture, arXiv:2203.17207). Until then this is a project-level axiom. -/
axiom spread_disjointness_input :
  ∃ Csp : ℝ, 0 < Csp ∧
    ∀ {α : Type*} [DecidableEq α]
      (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      UniformFamily A k →
      SpreadFamily A κ →
      Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ PairwiseDisjointMembers B

/-! ## Dense-core corollary -/

/-- **Dense-core corollary** (PDF Corollary 2.2). A non-disjoint uniform
family must concentrate on a small "core" appearing in many members. -/
theorem dense_core_from_spread :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ {α : Type u} [DecidableEq α]
        (A : Finset (Finset α)) (k K : ℕ),
        A.Nonempty →
        1 ≤ k → k ≤ K →
        UniformFamily A k →
        (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
        ∃ C : Finset α,
          C.Nonempty ∧
          ((A.filter fun S => C ⊆ S).card : ℝ) >
            (A.card : ℝ) /
              (C0 * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card := by
  classical
  let Csp : ℝ := Classical.choose (spread_disjointness_input.{u})
  have hspec := Classical.choose_spec (spread_disjointness_input.{u})
  have hCsp_pos : 0 < Csp := hspec.1
  refine ⟨Csp * 2, by positivity, ?_⟩
  intro α _ A k K hA hk_pos hkK hUniform hIntersect
  let κ : ℝ := (Csp * 2) * Real.log (Real.exp 1 * (K : ℝ))
  by_contra hNoCore
  have hSpread : SpreadFamily A κ := by
    intro T hT
    exact le_of_not_gt (by
      intro hgt
      exact hNoCore ⟨T, hT, hgt⟩)
  have hκ : Csp * (2 : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ := by
    have harg_pos : 0 < Real.exp 1 * (k : ℝ) := by positivity
    have harg_le : Real.exp 1 * (k : ℝ) ≤ Real.exp 1 * (K : ℝ) := by
      gcongr
    have hlog_le : Real.log (Real.exp 1 * (k : ℝ)) ≤
        Real.log (Real.exp 1 * (K : ℝ)) :=
      Real.log_le_log harg_pos harg_le
    have hcoef_nonneg : 0 ≤ Csp * 2 := by positivity
    exact mul_le_mul_of_nonneg_left hlog_le hcoef_nonneg
  rcases hspec.2 (A := A) (r := 2) (k := k) (κ := κ)
      hA (by norm_num) hk_pos hUniform hSpread hκ with
    ⟨B, hBA, hBcard, hBdisj⟩
  have hBgt : 1 < B.card := by omega
  rcases Finset.one_lt_card.mp hBgt with ⟨S, hS, T, hT, hST⟩
  exact hIntersect S (hBA hS) T (hBA hT) hST (hBdisj S hS T hT hST)

end Erdos202
