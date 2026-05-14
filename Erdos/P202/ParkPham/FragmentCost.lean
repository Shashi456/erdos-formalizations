/-
Erdos Problem 202 — Park–Pham layer, fragment cost bookkeeping.

This file connects the fragment infrastructure to the finite cover-cost API.
The key local step in the Park--Vondrak proof is that minimal fragments split
into small and large parts, and cost subadditivity gives

  cost(H) <= cost(S_m(F*(H,W))) + cost(L_m(F*(H,W))).

No probabilistic estimate is used here.
-/

import Mathlib
import Erdos.P202.ParkPham.Fragments
import Erdos.P202.ParkPham.Cost

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- A cover of the minimal fragments is automatically a cover of the original
family, so the original family has no larger cover cost than the minimal
fragment family. -/
lemma coverCost_le_minimalFragments
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α) (p : ℝ) :
    coverCost X H p ≤ coverCost X (minimalFragments H W) p := by
  rcases exists_ground_cover_weight_eq_coverCost X (minimalFragments H W) p with
    ⟨G, hGX, hCover, hEq⟩
  exact (coverCost_le_of_ground_cover hGX hCover.of_minimalFragments).trans_eq
    hEq.symm

/-- The finite cost subadditivity step for the large/small minimal-fragment
split. -/
lemma coverCost_le_small_add_large_minimalFragments
    (X : Finset α) (m : ℕ) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X H p ≤
      coverCost X (smallMinimalFragments m H W) p +
        coverCost X (largeMinimalFragments m H W) p := by
  have htoMin :
      coverCost X H p ≤ coverCost X (minimalFragments H W) p :=
    coverCost_le_minimalFragments X H W p
  have hpartition :
      smallMinimalFragments m H W ∪ largeMinimalFragments m H W =
        minimalFragments H W :=
    small_union_large_minimalFragments m H W
  have hsubadd :
      coverCost X (smallMinimalFragments m H W ∪ largeMinimalFragments m H W) p ≤
        coverCost X (smallMinimalFragments m H W) p +
          coverCost X (largeMinimalFragments m H W) p :=
    coverCost_union_le hp0
  calc
    coverCost X H p ≤ coverCost X (minimalFragments H W) p := htoMin
    _ = coverCost X
          (smallMinimalFragments m H W ∪ largeMinimalFragments m H W) p := by
        rw [hpartition]
    _ ≤ coverCost X (smallMinimalFragments m H W) p +
        coverCost X (largeMinimalFragments m H W) p := hsubadd

lemma largeMinimalFragments_subset_ground
    {X : Finset α} {m : ℕ} {H : Finset (Finset α)} {W T : Finset α}
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hT : T ∈ largeMinimalFragments m H W) :
    T ⊆ X := by
  have hTmin : T ∈ minimalFragments H W :=
    (mem_largeMinimalFragments.mp hT).1
  have hTfrag : T ∈ fragmentFamily H W :=
    minimalFragments_subset_fragmentFamily H W hTmin
  rcases mem_fragmentFamily.mp hTfrag with ⟨S, hS, rfl⟩
  exact (Finset.sdiff_subset : S \ W ⊆ S).trans (hHX S hS)

lemma coverCost_largeMinimalFragments_le_card_mul_pow
    {X : Finset α} {m : ℕ} {H : Finset (Finset α)} {W : Finset α}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    coverCost X (largeMinimalFragments m H W) p ≤
      ((largeMinimalFragments m H W).card : ℝ) * p ^ m := by
  have hcost :
      coverCost X (largeMinimalFragments m H W) p ≤
        coverWeight (largeMinimalFragments m H W) p :=
    coverCost_le_coverWeight_self
      (fun T hT => largeMinimalFragments_subset_ground hHX hT)
  have hweight :
      coverWeight (largeMinimalFragments m H W) p ≤
        ((largeMinimalFragments m H W).card : ℝ) * p ^ m := by
    unfold coverWeight
    calc
      (∑ T ∈ largeMinimalFragments m H W, p ^ T.card)
          ≤ ∑ T ∈ largeMinimalFragments m H W, p ^ m := by
            refine Finset.sum_le_sum ?_
            intro T hT
            exact pow_le_pow_of_le_one hp0 hp1
              (mem_largeMinimalFragments.mp hT).2
      _ = ((largeMinimalFragments m H W).card : ℝ) * p ^ m := by
            rw [Finset.sum_const, nsmul_eq_mul]
  exact hcost.trans hweight

lemma coverCost_largeMinimalFragments_le_source_card_mul_pow
    {X : Finset α} {m : ℕ} {H : Finset (Finset α)} {W : Finset α}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    coverCost X (largeMinimalFragments m H W) p ≤
      (H.card : ℝ) * p ^ m := by
  have hcost :=
    coverCost_largeMinimalFragments_le_card_mul_pow
      (X := X) (m := m) (H := H) (W := W)
      hp0 hp1 hHX
  have hcard :
      ((largeMinimalFragments m H W).card : ℝ) * p ^ m ≤
        (H.card : ℝ) * p ^ m := by
    have hcard_nat := largeMinimalFragments_card_le_card m H W
    have hcard_real :
        ((largeMinimalFragments m H W).card : ℝ) ≤ (H.card : ℝ) := by
      exact_mod_cast hcard_nat
    exact mul_le_mul_of_nonneg_right hcard_real (pow_nonneg hp0 m)
  exact hcost.trans hcard

lemma coverCost_smallMinimalFragments_pos_of_large_cost_lt
    (X : Finset α) (m : ℕ) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hlarge :
      coverCost X (largeMinimalFragments m H W) p < coverCost X H p) :
    0 < coverCost X (smallMinimalFragments m H W) p := by
  have hle := coverCost_le_small_add_large_minimalFragments X m H W hp0
  linarith

lemma smallMinimalFragments_one_card_zero
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ smallMinimalFragments 1 H W) :
    T.card = 0 := by
  exact Nat.lt_one_iff.mp (mem_smallMinimalFragments.mp hT).2

/-- At cutoff `1`, the small-fragment family consists only of `∅`, so
positive cover cost exactly means that some original member is already covered
by `W`. -/
lemma coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) :
    0 < coverCost X (smallMinimalFragments 1 H W) p ↔
      ∃ S ∈ H, S ⊆ W := by
  rw [coverCost_pos_iff_empty_mem_of_forall_card_zero
    (X := X) (U := smallMinimalFragments 1 H W) (p := p) hp0
    (fun T hT => smallMinimalFragments_one_card_zero hT)]
  simp

lemma exists_subset_of_largeMinimalFragments_one_cost_lt
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hlarge :
      coverCost X (largeMinimalFragments 1 H W) p < coverCost X H p) :
    ∃ S ∈ H, S ⊆ W := by
  have hpos :
      0 < coverCost X (smallMinimalFragments 1 H W) p :=
    coverCost_smallMinimalFragments_pos_of_large_cost_lt X 1 H W hp0 hlarge
  exact (coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    X H W hp0).mp hpos

/-- One-step endpoint for the fragment iteration: after exposing `W`, a final
cutoff-`1` small-fragment step with exposure `V` has positive cost exactly
when an original source member is contained in `W ∪ V`. -/
lemma coverCost_smallMinimalFragments_one_minimalFragments_pos_iff_exists_subset_union
    (X : Finset α) (H : Finset (Finset α)) (W V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) :
    0 < coverCost X (smallMinimalFragments 1 (minimalFragments H W) V) p ↔
      ∃ S ∈ H, S ⊆ W ∪ V := by
  rw [coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    X (minimalFragments H W) V hp0]
  exact exists_minimalFragment_subset_iff_source_subset_union

lemma exists_subset_union_of_largeMinimalFragments_one_minimalFragments_cost_lt
    (X : Finset α) (H : Finset (Finset α)) (W V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hlarge :
      coverCost X (largeMinimalFragments 1 (minimalFragments H W) V) p <
        coverCost X (minimalFragments H W) p) :
    ∃ S ∈ H, S ⊆ W ∪ V := by
  have hpos :
      0 < coverCost X (smallMinimalFragments 1 (minimalFragments H W) V) p :=
    coverCost_smallMinimalFragments_pos_of_large_cost_lt
      X 1 (minimalFragments H W) V hp0 hlarge
  exact
    (coverCost_smallMinimalFragments_one_minimalFragments_pos_iff_exists_subset_union
      X H W V hp0).mp hpos

/-- Endpoint for a finite fragment iteration: after a list of exposures `Ws`,
positive final cutoff-`1` small-fragment cost is equivalent to an original
source member being contained in the union of all exposures and the final
exposure `V`. -/
lemma coverCost_smallMinimalFragments_one_iterated_pos_iff_exists_subset_union
    (X : Finset α) (H : Finset (Finset α)) (Ws : List (Finset α))
    (V : Finset α) {p : ℝ} (hp0 : 0 ≤ p) :
    0 < coverCost X (smallMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p ↔
      ∃ S ∈ H, S ⊆ exposureUnion Ws ∪ V := by
  rw [coverCost_smallMinimalFragments_one_pos_iff_exists_subset
    X (iteratedMinimalFragments H Ws) V hp0]
  exact exists_iteratedMinimalFragment_subset_iff_source_subset_union H Ws V

lemma exposureUnion_mem_upClosureIn_of_smallMinimalFragments_one_iterated_pos
    (X : Finset α) (H : Finset (Finset α)) (Ws : List (Finset α))
    (V : Finset α) {p : ℝ} (hp0 : 0 ≤ p)
    (hUnionX : exposureUnion Ws ∪ V ⊆ X)
    (hpos :
      0 < coverCost X (smallMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p) :
    exposureUnion Ws ∪ V ∈ upClosureIn X H := by
  rcases
    (coverCost_smallMinimalFragments_one_iterated_pos_iff_exists_subset_union
      X H Ws V hp0).mp hpos with ⟨S, hS, hSsub⟩
  exact mem_upClosureIn.mpr ⟨hUnionX, S, hS, hSsub⟩

lemma exists_subset_union_of_largeMinimalFragments_one_iterated_cost_lt
    (X : Finset α) (H : Finset (Finset α)) (Ws : List (Finset α))
    (V : Finset α) {p : ℝ} (hp0 : 0 ≤ p)
    (hlarge :
      coverCost X (largeMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p <
        coverCost X (iteratedMinimalFragments H Ws) p) :
    ∃ S ∈ H, S ⊆ exposureUnion Ws ∪ V := by
  have hpos :
      0 < coverCost X
        (smallMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p :=
    coverCost_smallMinimalFragments_pos_of_large_cost_lt
      X 1 (iteratedMinimalFragments H Ws) V hp0 hlarge
  exact
    (coverCost_smallMinimalFragments_one_iterated_pos_iff_exists_subset_union
      X H Ws V hp0).mp hpos

lemma exposureUnion_mem_upClosureIn_of_largeMinimalFragments_one_iterated_cost_lt
    (X : Finset α) (H : Finset (Finset α)) (Ws : List (Finset α))
    (V : Finset α) {p : ℝ} (hp0 : 0 ≤ p)
    (hUnionX : exposureUnion Ws ∪ V ⊆ X)
    (hlarge :
      coverCost X (largeMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p <
        coverCost X (iteratedMinimalFragments H Ws) p) :
    exposureUnion Ws ∪ V ∈ upClosureIn X H := by
  have hpos :
      0 < coverCost X
        (smallMinimalFragments 1 (iteratedMinimalFragments H Ws) V) p :=
    coverCost_smallMinimalFragments_pos_of_large_cost_lt
      X 1 (iteratedMinimalFragments H Ws) V hp0 hlarge
  exact exposureUnion_mem_upClosureIn_of_smallMinimalFragments_one_iterated_pos
    X H Ws V hp0 hUnionX hpos

end

end ParkPham
end Erdos202
