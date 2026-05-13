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
import Erdos.P202.SpreadDefs
import Erdos.P202.ParkPham.SpreadDisjointness

namespace Erdos202

open Finset
open scoped BigOperators

universe u

/-! ## Spread-disjointness (discharged via Park–Pham layer)

Definitions `UniformFamily`, `SpreadFamily`, `PairwiseDisjointMembers`
live in `Erdos.P202.SpreadDefs`. The finite spread-disjointness
consequence of Park–Pham is now proved as
`Erdos202.ParkPham.spread_disjointness_theorem`; the historical name
`spread_disjointness_input` is preserved here as a derived theorem so
downstream consumers (chain, dense-core, optimization) need no edits. -/

/-- **Spread-disjointness input** — preserved name, now a derived theorem
discharging the Park–Pham layer (`spread_disjointness_theorem`).
Trust boundary moves to `CKK_const` + `park_pham_threshold` +
`partition_density_to_disjoint_members`. -/
theorem spread_disjointness_input :
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
        B ⊆ A ∧ B.card = r ∧ PairwiseDisjointMembers B :=
  Erdos202.ParkPham.spread_disjointness_theorem

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
