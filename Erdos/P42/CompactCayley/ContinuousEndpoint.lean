/-
Erdős Problem 42 — Layer 1 continuous-analogue lemma.

Following Tao's May 2026 forum comment + natso26's clean exposition
(`fourier_positive_ulam_note.pdf`). The geometric core
`closed_proper_subgroup_haar_null` is proved here axiom-free; the main
`tao_continuous_avoidance` lemma is also proved once the standard measurable
group assumptions needed by Mathlib's Haar shear lemmas are available.

This file is shared scaffolding: Route A (Fourier-positive) eventually uses it
as the continuous endpoint of the U²-regularity / counting argument. Route B
(compact Cayley) uses a closely related lemma in its clique-forcing proof
(Lemma 2.7 of the compact Cayley PDF), which is also a candidate destination
for `closed_proper_subgroup_haar_null` once we open that black box.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos42

open Filter Set Finset MeasureTheory
open scoped Pointwise

universe u

/-- A nonnegative integrable real-valued function that is positive almost
everywhere on a probability space has positive integral. -/
lemma integral_pos_of_ae_pos_of_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {F : α → ℝ} (hFint : Integrable F μ)
    (hFnonneg : 0 ≤ᵐ[μ] F) (hFpos : ∀ᵐ x ∂μ, 0 < F x) :
    0 < ∫ x, F x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae hFnonneg hFint]
  have hsupp_ae : ∀ᵐ x ∂μ, x ∈ Function.support F := by
    filter_upwards [hFpos] with x hx
    exact ne_of_gt hx
  have hcompl_zero : μ (Function.support F)ᶜ = 0 := by
    rwa [ae_iff] at hsupp_ae
  by_contra hnot
  have hsupp_zero : μ (Function.support F) = 0 := by
    exact le_antisymm (not_lt.mp hnot) bot_le
  have h_univ_zero : μ (Set.univ : Set α) = 0 := by
    have hcover : (Set.univ : Set α) =
        Function.support F ∪ (Function.support F)ᶜ := by
      ext x
      simp
    refine le_antisymm ?_ bot_le
    calc
      μ (Set.univ : Set α) =
          μ (Function.support F ∪ (Function.support F)ᶜ) := by rw [hcover]
      _ ≤ μ (Function.support F) + μ (Function.support F)ᶜ :=
          measure_union_le _ _
      _ = 0 := by simp [hsupp_zero, hcompl_zero]
  have h_univ_one : μ (Set.univ : Set α) = 1 := measure_univ
  norm_num [h_univ_one] at h_univ_zero

/-- Edge set of `K_M`, oriented by the natural order. This is the continuous
analogue of the finite ordered-clique product in the compact-Cayley proof. -/
def continuousCliqueEdgePairs (M : ℕ) : Finset (Fin M × Fin M) :=
  (Finset.univ : Finset (Fin M × Fin M)).filter (fun e => e.1 < e.2)

/-- Product kernel for the continuous `K_M` Cayley density. -/
noncomputable def continuousCliqueKernel
    {G : Type u} [Sub G] (M : ℕ) (f : G → ℝ) (x : Fin M → G) : ℝ :=
  ∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)

/-- Continuous Cayley `K_M` density associated to a kernel `f`. -/
noncomputable def continuousCliqueDensity
    {G : Type u} [MeasurableSpace G] [Sub G]
    (μ : Measure G) (M : ℕ) (f : G → ℝ) : ℝ :=
  ∫ x : Fin M → G, continuousCliqueKernel M f x ∂Measure.pi (fun _ : Fin M => μ)

/-- A closed proper subgroup of a connected compact abelian Hausdorff group is
Haar-null. Geometric core of Layer 1; no Fourier content.

Argument: assume `μ H ≠ 0`. The cosets of `H` partition `G`, each with the same
measure `μ H` by translation invariance. With finite total measure and a
constant positive contribution, only finitely many cosets exist; hence
`H.FiniteIndex`. A closed finite-index subgroup is open
(`AddSubgroup.isOpen_of_isClosed_of_finiteIndex`). A non-empty clopen subset of
a connected space is the whole space, contradicting `H` proper. -/
theorem closed_proper_subgroup_haar_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_proper : (H : Set G) ≠ Set.univ) :
    μ (H : Set G) = 0 := by
  by_contra hμH_ne
  have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
  obtain ⟨s, hs, _⟩ := H.exists_isComplement_left 0
  have hs_finite : Finite s := by
    rcases finite_or_infinite s with hfin | hinf
    · exact hfin
    · exfalso
      let e : ℕ ↪ s := Infinite.natEmbedding s
      let f : ℕ → Set G := fun n => (e n).val +ᵥ (H : Set G)
      have h_disjoint : Pairwise (fun m n : ℕ => Disjoint (f m) (f n)) := by
        intro m n hmn
        have : (e m).val ≠ (e n).val :=
          fun h => hmn (e.injective (Subtype.ext h))
        exact hs.pairwiseDisjoint_vadd (e m).2 (e n).2 this
      have h_meas : ∀ n : ℕ, MeasurableSet (f n) :=
        fun n => hH_meas.const_vadd _
      have h_const : ∀ n : ℕ, μ (f n) = μ (H : Set G) :=
        fun n => measure_vadd μ (e n).val _
      have h_subset : (⋃ n : ℕ, f n) ⊆ Set.univ := fun _ _ => trivial
      have hμ_iUnion : μ (⋃ n : ℕ, f n) = ∑' n : ℕ, μ (f n) :=
        measure_iUnion h_disjoint h_meas
      have h_top : (∑' _ : ℕ, μ (H : Set G)) = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hμH_ne
      have hμ_top : μ (⋃ n : ℕ, f n) = ⊤ := by
        rw [hμ_iUnion, tsum_congr h_const]; exact h_top
      have hμ_univ_top : μ (Set.univ : Set G) = ⊤ :=
        top_unique (hμ_top ▸ measure_mono h_subset)
      exact absurd hμ_univ_top (ne_of_lt IsFiniteMeasure.measure_univ_lt_top)
  have hH_findex : H.FiniteIndex := hs.finite_left_iff.mp hs_finite
  have hH_open : IsOpen (H : Set G) :=
    AddSubgroup.isOpen_of_isClosed_of_finiteIndex H hH_closed
  exact hH_proper (IsClopen.eq_univ ⟨hH_closed, hH_open⟩ ⟨0, H.zero_mem⟩)

/-- If `H` is Haar-null, then the set of finite tuples whose `i,j` difference
lands in `H` is null. This is the Fubini/shear step used in Tao's continuous
avoidance lemma.

The proof splits off the `i`-th coordinate, evaluates the `j`-th coordinate in
the remaining product, and then uses the Haar-preserving shear
`(x, y) ↦ (x - y, y)` on `G × G`. -/
theorem pi_pair_sub_mem_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {M : ℕ} (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hμH : μ (H : Set G) = 0)
    (i j : Fin M) (hij : i ≠ j) :
    Measure.pi (fun _ : Fin M => μ)
      {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
  cases M with
  | zero =>
      exact Fin.elim0 i
  | succ n =>
      obtain ⟨k, hk⟩ :=
        Fin.exists_succAbove_eq (x := j) (y := i) (by simpa [ne_comm] using hij)
      have hsplit :
          MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) i)
            (Measure.pi (fun _ : Fin (n + 1) => μ))
            (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
        simpa using
          (measurePreserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => G)
            (fun _ : Fin (n + 1) => μ) i)
      have hrest :
          MeasurePreserving (Function.eval k)
            (Measure.pi (fun _ : Fin n => μ)) μ :=
        measurePreserving_eval (fun _ : Fin n => μ) k
      have hpair_after :
          MeasurePreserving
            (Prod.map (fun x : G => x) (Function.eval k))
            (μ.prod (Measure.pi (fun _ : Fin n => μ))) (μ.prod μ) :=
        MeasurePreserving.prod
          (MeasurePreserving.id μ : MeasurePreserving (fun x : G => x) μ μ) hrest
      have hpair :
          MeasurePreserving (fun x : Fin (n + 1) → G => (x i, x j))
            (Measure.pi (fun _ : Fin (n + 1) => μ)) (μ.prod μ) := by
        convert hpair_after.comp hsplit using 1
        ext x
        · simp
        · rw [← hk]
          rfl
      have hdiff_prod :
          MeasurePreserving (fun z : G × G => (z.1 - z.2, z.2))
            (μ.prod μ) (μ.prod μ) := by
        simpa using (measurePreserving_sub_prod (μ := μ) (ν := μ))
      have hdiff :
          MeasurePreserving (fun z : G × G => z.1 - z.2)
            (μ.prod μ) μ := by
        simpa [Function.comp_def] using
          (measurePreserving_fst (μ := μ) (ν := μ)).comp hdiff_prod
      have hmap :
          MeasurePreserving (fun x : Fin (n + 1) → G => x i - x j)
            (Measure.pi (fun _ : Fin (n + 1) => μ)) μ := by
        simpa [Function.comp_def] using hdiff.comp hpair
      have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
      calc
        Measure.pi (fun _ : Fin (n + 1) => μ)
            {x : Fin (n + 1) → G | x i - x j ∈ (H : Set G)}
            = (Measure.map (fun x : Fin (n + 1) → G => x i - x j)
                (Measure.pi (fun _ : Fin (n + 1) => μ))) (H : Set G) := by
              change Measure.pi (fun _ : Fin (n + 1) => μ)
                  ((fun x : Fin (n + 1) → G => x i - x j) ⁻¹' (H : Set G)) = _
              rw [Measure.map_apply hmap.measurable hH_meas]
        _ = μ (H : Set G) := by rw [hmap.map_eq]
        _ = 0 := hμH

/-- Compact-clique-forcing endpoint, case where the zero set is a proper
closed subgroup. If `f ≥ 0` and `f` vanishes exactly on such a subgroup, then
the continuous Cayley `K_M` density is strictly positive.

This is the measure-theoretic part of compact-Cayley Lemma 2.7 after the
Fourier/positive-definite argument has identified the level set
`{x | f x = 0}` as a proper closed subgroup. -/
theorem continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 0)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    0 < continuousCliqueDensity μ M f := by
  have hμH : μ (H : Set G) = 0 :=
    closed_proper_subgroup_haar_null μ H hH_closed hH_proper
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        Measure.pi (fun _ : Fin M => μ)
          {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null :
      Measure.pi (fun _ : Fin M => μ)
        (⋃ (i : Fin M) (j : Fin M) (_ : i < j),
          {x : Fin M → G | x i - x j ∈ (H : Set G)}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have h_ae_avoid : ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
    rw [ae_iff]
    refine measure_mono_null ?_ h_bad_null
    intro x hx
    push_neg at hx
    obtain ⟨i, j, hij, hmem⟩ := hx
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩
  have hkernel_meas :
      Measurable (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    unfold continuousCliqueKernel
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hkernel_nonneg :
      0 ≤ᵐ[Measure.pi (fun _ : Fin M => μ)]
        (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    exact Eventually.of_forall fun x => by
      unfold continuousCliqueKernel
      exact Finset.prod_nonneg fun e _he => hf_nonneg _
  have hkernel_bound :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ),
        ‖continuousCliqueKernel M f x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ continuousCliqueKernel M f x := by
        unfold continuousCliqueKernel
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : continuousCliqueKernel M f x ≤ 1 := by
        unfold continuousCliqueKernel
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int :
      Integrable (fun x : Fin M → G => continuousCliqueKernel M f x)
        (Measure.pi (fun _ : Fin M => μ)) :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hkernel_pos :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ),
        0 < continuousCliqueKernel M f x := by
    filter_upwards [h_ae_avoid] with x hx
    unfold continuousCliqueKernel
    refine Finset.prod_pos ?_
    intro e he
    have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
    have hnot : x e.1 - x e.2 ∉ (H : Set G) := hx e.1 e.2 hlt
    have hne : f (x e.1 - x e.2) ≠ 0 := by
      intro hzero
      exact hnot ((hH_eq (x e.1 - x e.2)).mpr hzero)
    exact lt_of_le_of_ne (hf_nonneg _) hne.symm
  exact integral_pos_of_ae_pos_of_nonneg
    (Measure.pi (fun _ : Fin M => μ)) hkernel_int hkernel_nonneg hkernel_pos

/-- **Tao's continuous-analogue key lemma (May 2026 forum comment).** Let `G` be a
connected compact abelian Hausdorff group with Haar probability measure `μ`, and
let `f : G → ℝ` be measurable with `f ≤ 1` pointwise. Suppose the level set
`{x : f x = 1}` coincides with a closed subgroup `H ≤ G`, and `H` is proper.
Then for almost every `(x₁, …, x_M) ∈ G^M`, `f (x_i − x_j) < 1` for all
`1 ≤ i < j ≤ M`.

The hypothesis "level set is a closed subgroup" is what positive-definiteness of
`f` is used to establish in the original argument; we factor it out so the core
lemma is purely measure-theoretic. -/
theorem tao_continuous_avoidance
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (_hf_meas : Measurable f) (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → f (x i - x j) < 1 := by
  have hμH : μ (H : Set G) = 0 :=
    closed_proper_subgroup_haar_null μ H hH_closed hH_proper
  -- Fubini step (deferred): for each pair `(i, j)` with `i ≠ j`, the set of
  -- M-tuples with `x i - x j ∈ H` has product measure zero. Argument:
  -- translation invariance of `μ` plus `μ ↑H = 0` plus Fubini on the pi
  -- measure (or a measure-preserving "shear" change of variables).
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        Measure.pi (fun _ : Fin M => μ)
          {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null :
      Measure.pi (fun _ : Fin M => μ)
        (⋃ (i : Fin M) (j : Fin M) (_ : i < j),
          {x : Fin M → G | x i - x j ∈ (H : Set G)}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have h_ae_avoid : ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
    rw [ae_iff]
    refine measure_mono_null ?_ h_bad_null
    intro x hx
    push_neg at hx
    obtain ⟨i, j, hij, hmem⟩ := hx
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩
  filter_upwards [h_ae_avoid] with x hx i j hij
  have h_ne_one : f (x i - x j) ≠ 1 := by
    intro heq
    exact hx i j hij ((hH_eq (x i - x j)).mpr heq)
  exact lt_of_le_of_ne (hf_le _) h_ne_one

end Erdos42
