/-
Erdos Problem 202 — Park–Pham layer, finite cover cost.

The Park--Pham/Park--Vondrak proofs use the cost of a family: the minimum
`p`-weight of a cover.  The existing `pSmall` predicate only needs existence
of a cover of weight at most `1/2`; this file packages the corresponding
finite minimum over covers supported on the ground set `X`.
-/

import Mathlib
import Erdos.P202.ParkPham.Smallness

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Covers whose members are all subsets of the finite ground set `X`. -/
noncomputable def groundCoversIn (X : Finset α) (U : Finset (Finset α)) :
    Finset (Finset (Finset α)) :=
  by
    classical
    exact X.powerset.powerset.filter fun G => CoversIn X G U

omit [DecidableEq α] in
/-- The singleton cover `{∅}` covers every family. -/
lemma singleton_empty_covers (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X ({∅} : Finset (Finset α)) U := by
  intro S _hS
  exact ⟨∅, by simp, Finset.empty_subset S⟩

omit [DecidableEq α] in
/-- The finite set of ground-supported covers is nonempty. -/
lemma groundCoversIn_nonempty (X : Finset α) (U : Finset (Finset α)) :
    (groundCoversIn X U).Nonempty := by
  refine ⟨{∅}, ?_⟩
  classical
  rw [groundCoversIn, Finset.mem_filter]
  constructor
  · rw [Finset.mem_powerset]
    intro T hT
    have hT_empty : T = ∅ := by simpa using hT
    subst hT_empty
    exact Finset.mem_powerset.mpr (Finset.empty_subset X)
  · exact singleton_empty_covers X U

omit [DecidableEq α] in
lemma mem_groundCoversIn {X : Finset α} {U G : Finset (Finset α)} :
    G ∈ groundCoversIn X U ↔
      (∀ T ∈ G, T ⊆ X) ∧ CoversIn X G U := by
  classical
  rw [groundCoversIn, Finset.mem_filter]
  constructor
  · intro h
    constructor
    · intro T hTG
      exact Finset.mem_powerset.mp (Finset.mem_powerset.mp h.1 hTG)
    · exact h.2
  · rintro ⟨hGX, hCover⟩
    refine ⟨?_, hCover⟩
    exact Finset.mem_powerset.mpr (by
      intro T hTG
      exact Finset.mem_powerset.mpr (hGX T hTG))

/-- The finite set of cover weights for ground-supported covers. -/
noncomputable def groundCoverWeights (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    Finset ℝ :=
  by
    classical
    exact (groundCoversIn X U).image fun G => coverWeight G p

omit [DecidableEq α] in
lemma groundCoverWeights_nonempty
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    (groundCoverWeights X U p).Nonempty :=
  (groundCoversIn_nonempty X U).image _

/-- The cost of `U` at density `p`: the minimum `p`-weight of a
ground-supported cover. -/
noncomputable def coverCost
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  (groundCoverWeights X U p).min' (groundCoverWeights_nonempty X U p)

omit [DecidableEq α] in
lemma coverCost_le_of_ground_cover
    {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
    (hGX : ∀ T ∈ G, T ⊆ X) (hCover : CoversIn X G U) :
    coverCost X U p ≤ coverWeight G p := by
  unfold coverCost groundCoverWeights
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨G, (mem_groundCoversIn.mpr ⟨hGX, hCover⟩), rfl⟩)

omit [DecidableEq α] in
lemma coverCost_nonneg
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ coverCost X U p := by
  unfold coverCost groundCoverWeights
  refine Finset.le_min' _ _ _ ?_
  intro w hw
  rcases Finset.mem_image.mp hw with ⟨G, _hG, rfl⟩
  unfold coverWeight
  exact Finset.sum_nonneg fun T _ => pow_nonneg hp0 T.card

omit [DecidableEq α] in
lemma exists_ground_cover_weight_eq_coverCost
    (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    ∃ G : Finset (Finset α),
      (∀ T ∈ G, T ⊆ X) ∧
      CoversIn X G U ∧
      coverCost X U p = coverWeight G p := by
  unfold coverCost groundCoverWeights
  have hmem :=
    Finset.min'_mem ((groundCoversIn X U).image fun G => coverWeight G p)
      (groundCoverWeights_nonempty X U p)
  rcases Finset.mem_image.mp hmem with ⟨G, hG, hEq⟩
  rcases mem_groundCoversIn.mp hG with ⟨hGX, hCover⟩
  exact ⟨G, hGX, hCover, hEq.symm⟩

omit [DecidableEq α] in
lemma coverWeight_singleton_empty (p : ℝ) :
    coverWeight ({∅} : Finset (Finset α)) p = 1 := by
  simp [coverWeight]

omit [DecidableEq α] in
lemma coverCost_le_one (X : Finset α) (U : Finset (Finset α)) (p : ℝ) :
    coverCost X U p ≤ 1 := by
  have hle := coverCost_le_of_ground_cover
    (X := X) (U := U) (G := ({∅} : Finset (Finset α))) (p := p)
    (by
      intro T hT
      have hT_empty : T = ∅ := by simpa using hT
      subst hT_empty
      exact Finset.empty_subset X)
    (singleton_empty_covers X U)
  simpa [coverWeight_singleton_empty] using hle

omit [DecidableEq α] in
lemma self_covers (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X U U := by
  intro S hS
  exact ⟨S, hS, subset_refl S⟩

omit [DecidableEq α] in
lemma coverCost_le_coverWeight_self
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ T ∈ U, T ⊆ X) :
    coverCost X U p ≤ coverWeight U p :=
  coverCost_le_of_ground_cover hUX (self_covers X U)

omit [DecidableEq α] in
lemma coverCost_empty_eq_zero
    (X : Finset α) {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X (∅ : Finset (Finset α)) p = 0 := by
  have hle : coverCost X (∅ : Finset (Finset α)) p ≤ 0 := by
    have hcover : CoversIn X (∅ : Finset (Finset α))
        (∅ : Finset (Finset α)) := by
      intro S hS
      simp at hS
    have hground : ∀ T ∈ (∅ : Finset (Finset α)), T ⊆ X := by
      intro T hT
      simp at hT
    simpa [coverWeight] using
      (coverCost_le_of_ground_cover (X := X)
        (U := (∅ : Finset (Finset α)))
        (G := (∅ : Finset (Finset α))) (p := p) hground hcover)
  exact le_antisymm hle (coverCost_nonneg hp0)

omit [DecidableEq α] in
lemma one_le_coverCost_of_empty_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
    1 ≤ coverCost X U p := by
  unfold coverCost groundCoverWeights
  refine Finset.le_min' _ _ _ ?_
  intro w hw
  rcases Finset.mem_image.mp hw with ⟨G, hG, rfl⟩
  rcases mem_groundCoversIn.mp hG with ⟨_hGX, hCover⟩
  rcases hCover ∅ hEmpty with ⟨T, hTG, hTsub⟩
  have hT_empty : T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simpa using hTsub hx
  have hsingle :
      p ^ T.card ≤ coverWeight G p := by
    unfold coverWeight
    exact Finset.single_le_sum
      (s := G) (f := fun S : Finset α => p ^ S.card)
      (fun S _ => pow_nonneg hp0 S.card) hTG
  have hterm : p ^ T.card = 1 := by
    subst hT_empty
    simp
  linarith

omit [DecidableEq α] in
lemma coverCost_eq_one_of_empty_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
    coverCost X U p = 1 :=
  le_antisymm (coverCost_le_one X U p)
    (one_le_coverCost_of_empty_mem hp0 hEmpty)

omit [DecidableEq α] in
lemma eq_empty_of_forall_card_zero_empty_not_mem
    {U : Finset (Finset α)}
    (hcard : ∀ S ∈ U, S.card = 0)
    (hEmpty : (∅ : Finset α) ∉ U) :
    U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hS_empty : S = ∅ := Finset.card_eq_zero.mp (hcard S hS)
  exact hEmpty (by simpa [hS_empty] using hS)

omit [DecidableEq α] in
lemma coverCost_pos_iff_empty_mem_of_forall_card_zero
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p)
    (hcard : ∀ S ∈ U, S.card = 0) :
    0 < coverCost X U p ↔ (∅ : Finset α) ∈ U := by
  constructor
  · intro hpos
    by_contra hEmpty
    have hU_empty : U = ∅ :=
      eq_empty_of_forall_card_zero_empty_not_mem hcard hEmpty
    have hcost : coverCost X U p = 0 := by
      rw [hU_empty]
      exact coverCost_empty_eq_zero X hp0
    linarith
  · intro hEmpty
    rw [coverCost_eq_one_of_empty_mem hp0 hEmpty]
    norm_num

/-- Ground-supported cover cost recovers the existing `pSmall` predicate for
families living inside `X`. -/
theorem pSmall_iff_coverCost_le
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) :
    pSmall X U p ↔ coverCost X U p ≤ (1 / 2 : ℝ) := by
  constructor
  · intro hSmall
    rcases pSmall.exists_ground_cover hp0 hUX hSmall with
      ⟨G, hGX, hCover, hsum⟩
    exact (coverCost_le_of_ground_cover hGX hCover).trans hsum
  · intro hCost
    rcases exists_ground_cover_weight_eq_coverCost X U p with
      ⟨G, _hGX, hCover, hEq⟩
    exact ⟨G, hCover, by simpa [hEq] using hCost⟩

lemma not_pSmall_iff_half_lt_coverCost
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) :
    ¬ pSmall X U p ↔ (1 / 2 : ℝ) < coverCost X U p := by
  rw [pSmall_iff_coverCost_le hp0 hUX]
  exact not_le

omit [DecidableEq α] in
/-- Cover cost is monotone decreasing as the target family shrinks. -/
lemma coverCost_mono_family
    {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (hUV : U ⊆ V) :
    coverCost X U p ≤ coverCost X V p := by
  rcases exists_ground_cover_weight_eq_coverCost X V p with
    ⟨G, hGX, hCoverV, hEq⟩
  have hCoverU : CoversIn X G U := hCoverV.mono_family hUV
  exact (coverCost_le_of_ground_cover hGX hCoverU).trans_eq hEq.symm

/-- Finite subadditivity of cover cost. -/
lemma coverCost_union_le
    {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) :
    coverCost X (U ∪ V) p ≤ coverCost X U p + coverCost X V p := by
  rcases exists_ground_cover_weight_eq_coverCost X U p with
    ⟨G, hGX, hCoverU, hEqG⟩
  rcases exists_ground_cover_weight_eq_coverCost X V p with
    ⟨H, hHX, hCoverV, hEqH⟩
  have hGroundUnion : ∀ T ∈ G ∪ H, T ⊆ X := by
    intro T hT
    rcases Finset.mem_union.mp hT with hTG | hTH
    · exact hGX T hTG
    · exact hHX T hTH
  have hCoverUnion : CoversIn X (G ∪ H) (U ∪ V) :=
    hCoverU.union hCoverV
  calc
    coverCost X (U ∪ V) p ≤ coverWeight (G ∪ H) p :=
      coverCost_le_of_ground_cover hGroundUnion hCoverUnion
    _ ≤ coverWeight G p + coverWeight H p := coverWeight_union_le hp0
    _ = coverCost X U p + coverCost X V p := by
      rw [hEqG, hEqH]

end

end ParkPham
end Erdos202
