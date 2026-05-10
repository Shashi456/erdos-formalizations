/-
Erdős Problem 42 — compact-Cayley route, positive-definite endpoint interface.

In compact-Cayley Lemma 2.7, the Fourier/positive-definite argument is used to
show that the level set `{x | g x = 1}` is a proper closed subgroup.  This file
formalizes the downstream subgroup construction and density conclusion from the
exact closure property that the positive-definite argument must supply.

No new axiom is introduced here: the remaining Route B work is to derive
`LevelOneSubgroupKernel g` from the compact limit's positive Fourier
coefficients.
-/

import Erdos.P42.CompactCayley.ContinuousEndpoint

namespace Erdos42

open MeasureTheory

universe u

/-- Compact-Cayley Lemma 2.7, first branch. If `g 0 < 1`, then the allowed
kernel `1 - g` is positive at zero, hence has positive continuous clique
density by the open-neighbourhood endpoint. -/
theorem continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg0 : g 0 < 1) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_pos_at_zero μ M (fun x => 1 - g x)
    (continuous_const.sub hg_cont) ?_ ?_ ?_
  · intro x
    linarith [hg_le x]
  · intro x
    linarith [hg_nonneg x]
  · linarith

/-- Abstract output of the positive-definite part of compact-Cayley Lemma 2.7:
the level-one set is nonempty and closed under subtraction.

For the eventual full proof, this structure should be produced from the
positive-definite kernel attached to `g`. -/
structure LevelOneSubgroupKernel {G : Type u} [Zero G] [Sub G]
    (g : G → ℝ) : Prop where
  map_zero : g 0 = 1
  sub_mem : ∀ x y : G, g x = 1 → g y = 1 → g (x - y) = 1

/-- A concrete Hilbert-space representation of a real positive-definite kernel:
`g (x - y)` is realized as an inner product of unit vectors.

This is not yet the compact extraction/GNS construction. It is the clean
finite-dimensional-style interface from which the level-one subgroup property
is elementary. -/
structure RealHilbertKernelRepresentation
    {G : Type u} (E : Type*) [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : G → ℝ) where
  vec : G → E
  norm_vec : ∀ x : G, ‖vec x‖ = 1
  inner_sub : ∀ x y : G, inner ℝ (vec x) (vec y) = g (x - y)

lemma RealHilbertKernelRepresentation.vec_eq_zero_of_level_one
    {G : Type u} {E : Type*} [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : G → ℝ} (hrep : RealHilbertKernelRepresentation E g)
    {x : G} (hx : g x = 1) :
    hrep.vec x = hrep.vec 0 := by
  let v : E := hrep.vec x
  let w : E := hrep.vec 0
  have hinner : inner ℝ v w = 1 := by
    calc
      inner ℝ v w = g (x - 0) := by simpa [v, w] using hrep.inner_sub x 0
      _ = g x := by simp
      _ = 1 := hx
  have hnormv : ‖v‖ = 1 := by simpa [v] using hrep.norm_vec x
  have hnormw : ‖w‖ = 1 := by simpa [w] using hrep.norm_vec 0
  have hsquare : ‖v - w‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hinner, hnormv, hnormw]
    norm_num
  have hnorm : ‖v - w‖ = 0 := by
    have hnonneg : 0 ≤ ‖v - w‖ := norm_nonneg _
    nlinarith
  have hsub : v - w = 0 := norm_eq_zero.mp hnorm
  have hvw : v = w := sub_eq_zero.mp hsub
  simp [v, w, hvw]

theorem levelOneSubgroupKernel_of_realHilbertKernelRepresentation
    {G : Type u} {E : Type*} [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : G → ℝ} (hrep : RealHilbertKernelRepresentation E g) :
    LevelOneSubgroupKernel g where
  map_zero := by
    calc
      g 0 = inner ℝ (hrep.vec 0) (hrep.vec 0) := by
        simpa using (hrep.inner_sub 0 0).symm
      _ = ‖hrep.vec 0‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = 1 := by rw [hrep.norm_vec 0]; norm_num
  sub_mem := by
    intro x y hx hy
    have hxvec : hrep.vec x = hrep.vec 0 :=
      hrep.vec_eq_zero_of_level_one hx
    have hyvec : hrep.vec y = hrep.vec 0 :=
      hrep.vec_eq_zero_of_level_one hy
    calc
      g (x - y) = inner ℝ (hrep.vec x) (hrep.vec y) :=
        (hrep.inner_sub x y).symm
      _ = inner ℝ (hrep.vec 0) (hrep.vec 0) := by rw [hxvec, hyvec]
      _ = ‖hrep.vec 0‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = 1 := by rw [hrep.norm_vec 0]; norm_num

/-- The subgroup `{x | g x = 1}` built from the level-one closure property. -/
def levelOneAddSubgroup {G : Type u} [AddCommGroup G]
    (g : G → ℝ) (hg : LevelOneSubgroupKernel g) : AddSubgroup G where
  carrier := {x | g x = 1}
  zero_mem' := hg.map_zero
  add_mem' := by
    intro x y hx hy
    have hneg_y : g (-y) = 1 := by
      simpa using hg.sub_mem 0 y hg.map_zero hy
    simpa [sub_eq_add_neg] using hg.sub_mem x (-y) hx hneg_y
  neg_mem' := by
    intro x hx
    simpa using hg.sub_mem 0 x hg.map_zero hx

lemma mem_levelOneAddSubgroup {G : Type u} [AddCommGroup G]
    {g : G → ℝ} {hg : LevelOneSubgroupKernel g} {x : G} :
    x ∈ levelOneAddSubgroup g hg ↔ g x = 1 := Iff.rfl

lemma levelOneAddSubgroup_isClosed {G : Type u}
    [AddCommGroup G] [TopologicalSpace G]
    {g : G → ℝ} (hg : LevelOneSubgroupKernel g)
    (hg_cont : Continuous g) :
    IsClosed (levelOneAddSubgroup g hg : Set G) := by
  change IsClosed {x | g x = 1}
  simpa using isClosed_singleton.preimage hg_cont

lemma levelOneAddSubgroup_proper_of_exists_ne_one {G : Type u}
    [AddCommGroup G] {g : G → ℝ} (hg : LevelOneSubgroupKernel g)
    (hne : ∃ x : G, g x ≠ 1) :
    (levelOneAddSubgroup g hg : Set G) ≠ Set.univ := by
  rcases hne with ⟨x, hx⟩
  intro htop
  have hxmem : x ∈ (levelOneAddSubgroup g hg : Set G) := by
    rw [htop]
    trivial
  exact hx (mem_levelOneAddSubgroup.mp hxmem)

lemma levelOneAddSubgroup_proper_of_integral_le_one_sub
    {G : Type u} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {g : G → ℝ} (hg : LevelOneSubgroupKernel g)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η) :
    (levelOneAddSubgroup g hg : Set G) ≠ Set.univ := by
  refine levelOneAddSubgroup_proper_of_exists_ne_one hg ?_
  by_contra hnone
  push_neg at hnone
  have hint : (∫ x, g x ∂μ) = 1 := by
    simp [hnone]
  nlinarith

/-- Compact-Cayley Lemma 2.7 after isolating the positive-definite algebraic
input.  Once the positive-definite argument gives `LevelOneSubgroupKernel g`,
continuity gives closedness, the mean bound gives properness, and the
measure-theoretic endpoint yields positive `K_M` density for `1 - g`. -/
theorem continuousCliqueDensity_pos_of_levelOneSubgroupKernel
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg_level : LevelOneSubgroupKernel g)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  let H : AddSubgroup G := levelOneAddSubgroup g hg_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hg_level hg_cont
  have hH_eq : ∀ x : G, x ∈ H ↔ g x = 1 := by
    intro x
    rfl
  have hH_proper : (H : Set G) ≠ Set.univ :=
    levelOneAddSubgroup_proper_of_integral_le_one_sub μ hg_level hη hmean
  exact continuousCliqueDensity_pos_of_one_sub_level_one_proper_subgroup
    μ M g hg_cont.measurable hg_nonneg hg_le H hH_closed hH_eq hH_proper

/-- Compact-Cayley endpoint with the exact null-subgroup hypothesis on the
level-one subgroup.  This avoids connectedness: once the positive-definite
argument gives subgroup closure and the compact-dual algebra gives nullness,
the measure-theoretic clique forcing is immediate. -/
theorem continuousCliqueDensity_pos_of_levelOneSubgroupKernel_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg_level : LevelOneSubgroupKernel g)
    (hμH : μ ((levelOneAddSubgroup g hg_level : AddSubgroup G) : Set G) = 0) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  let H : AddSubgroup G := levelOneAddSubgroup g hg_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hg_level hg_cont
  have hH_eq : ∀ x : G, x ∈ H ↔ g x = 1 := by
    intro x
    rfl
  exact continuousCliqueDensity_pos_of_one_sub_level_one_null_subgroup
    μ M g hg_cont.measurable hg_nonneg hg_le H hH_closed hH_eq hμH

/-- Compact-Cayley endpoint where nullness of the level-one subgroup is proved
from infinite index.  This is often a smaller target for the extraction compact
dual than proving connectedness of the whole dual group. -/
theorem continuousCliqueDensity_pos_of_levelOneSubgroupKernel_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg_level : LevelOneSubgroupKernel g)
    (hH_not_finiteIndex :
      ¬ (levelOneAddSubgroup g hg_level : AddSubgroup G).FiniteIndex) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  let H : AddSubgroup G := levelOneAddSubgroup g hg_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hg_level hg_cont
  exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel_null μ M g
    hg_cont hg_nonneg hg_le hg_level
    (closed_subgroup_haar_null_of_not_finiteIndex μ H hH_closed hH_not_finiteIndex)

/-- Route A weighted endpoint after isolating the positive-definite algebraic
input.  Once the limiting forbidden kernel `f` has level-one subgroup closure,
continuity gives closedness, the mean bound `∫ f ≤ 1 - ρ` gives properness, and
the weighted measure-theoretic endpoint gives a positive avoidance integral
against any vertex weight `u` with `α ≤ ∫ u`, `α > 0`. -/
theorem continuousWeightedAvoidanceDensity_pos_of_levelOneSubgroupKernel
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_cont : Continuous f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (hf_level : LevelOneSubgroupKernel f)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hmean_f : (∫ x, f x ∂μ) ≤ 1 - ρ)
    {α : ℝ} (hα : 0 < α)
    (hmean_u : α ≤ ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u := by
  let H : AddSubgroup G := levelOneAddSubgroup f hf_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hf_level hf_cont
  have hH_eq : ∀ x : G, x ∈ H ↔ f x = 1 := by
    intro x
    rfl
  have hH_proper : (H : Set G) ≠ Set.univ :=
    levelOneAddSubgroup_proper_of_integral_le_one_sub μ hf_level hρ hmean_f
  exact continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_ge
    μ M f u hf_cont.measurable hu_meas hf_nonneg hf_le hu_nonneg hu_le
    H hH_closed hH_eq hH_proper hα hmean_u

/-- Compact-Cayley Lemma 2.7 endpoint in the Hilbert-representation form:
once the positive-definite kernel is represented by unit vectors with
`g (x - y) = ⟪v x, v y⟫`, the level-one subgroup property and the continuous
clique-forcing conclusion are automatic. -/
theorem continuousCliqueDensity_pos_of_realHilbertKernelRepresentation
    {G : Type u} {E : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hrep : RealHilbertKernelRepresentation E g)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel μ M g hg_cont hg_nonneg hg_le
    (levelOneSubgroupKernel_of_realHilbertKernelRepresentation hrep) hη hmean

/-- Compact-Cayley Lemma 2.7 endpoint with the two proof branches exposed:
either `g 0 < 1`, or the positive-definite argument supplies the level-one
subgroup closure property. -/
theorem continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η)
    (hbranch : g 0 < 1 ∨ LevelOneSubgroupKernel g) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  rcases hbranch with hg0 | hg_level
  · exact continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero μ M g hg_cont
      hg_nonneg hg_le hg0
  · exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel μ M g hg_cont
      hg_nonneg hg_le hg_level hη hmean

/-- Two-branch compact-Cayley endpoint using the narrower infinite-index
certificate instead of connectedness. -/
theorem continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hbranch :
      g 0 < 1 ∨
        ∃ hg_level : LevelOneSubgroupKernel g,
          ¬ (levelOneAddSubgroup g hg_level : AddSubgroup G).FiniteIndex) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  rcases hbranch with hg0 | hlevel
  · exact continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero μ M g hg_cont
      hg_nonneg hg_le hg0
  · rcases hlevel with ⟨hg_level, hnot⟩
    exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel_not_finiteIndex
      μ M g hg_cont hg_nonneg hg_le hg_level hnot

/-- Same two-branch endpoint, using a concrete Hilbert-space representation for
the second branch. The remaining Fourier/GNS work can target the `Nonempty`
representation hypothesis directly. -/
theorem continuousCliqueDensity_pos_of_lt_one_or_realHilbertKernelRepresentation
    {G : Type u} {E : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    {η : ℝ} (hη : 0 < η)
    (hmean : (∫ x, g x ∂μ) ≤ 1 - η)
    (hbranch : g 0 < 1 ∨ Nonempty (RealHilbertKernelRepresentation E g)) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel μ M g hg_cont
    hg_nonneg hg_le hη hmean ?_
  exact hbranch.imp id (fun hrep => levelOneSubgroupKernel_of_realHilbertKernelRepresentation hrep.some)

end Erdos42
