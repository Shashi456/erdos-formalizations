/-
Erdos Problem 42 — Route A compact-model contradiction interface.

This file packages the final contradiction step for opening the Route A
`finite_fourier_avoidance_count` axiom.  It does not construct the compact
model; it proves that any counterexample sequence equipped with the expected
weighted compact model is impossible.  The remaining Route A work is therefore
isolated to constructing this model and proving the weighted counting
convergence field.
-/

import Erdos.P42.FourierPositive.Counting
import Erdos.P42.FourierPositive.CompactDual
import Erdos.P42.CompactCayley.PositiveDefinite

namespace Erdos42.FourierPositive

open Filter MeasureTheory Erdos42
open scoped Topology Classical

universe u

/-- Route A weighted compact model expected from the Fourier-positive
compactness/counting argument.

The finite counterexample sequence supplies `F_n` and `U_n`.  The compact model
supplies a connected compact abelian Haar probability space, a continuous
forbidden limit kernel `f`, a vertex-weight limit `v`, the positive-definite
level-one subgroup closure certificate for `f`, and convergence of finite
weighted avoidance densities to the compact weighted avoidance integral. -/
structure WeightedCompactModel {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ)
    (G : Type u) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] where
  f : G → ℝ
  v : G → ℝ
  hf_cont : Continuous f
  hv_meas : Measurable (α := G) (β := ℝ) v
  hf_nonneg : ∀ x, 0 ≤ f x
  hf_le : ∀ x, f x ≤ 1
  hv_nonneg : ∀ x, 0 ≤ v x
  hv_le : ∀ x, v x ≤ 1
  mean_f_le : (∫ x, f x ∂μ) ≤ 1 - ρ
  mean_v_ge : α ≤ ∫ x, v x ∂μ
  hf_level : LevelOneSubgroupKernel f
  counting_convergence :
    Tendsto
      (fun n =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          finiteAvoidanceDensity (m := m) (S.F n) (S.U n)).re)
      atTop (𝓝 (continuousWeightedAvoidanceDensity μ m f v))

/-- Narrower Route A compact model endpoint.

The connected compact-dual theorem is only used to prove that the level-one
subgroup is Haar-null.  This variant carries that nullness certificate directly,
so future compact-extraction work can target the exact measure-theoretic
property needed by the weighted endpoint. -/
structure WeightedCompactNullModel {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ)
    (G : Type u) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] where
  f : G → ℝ
  v : G → ℝ
  hf_cont : Continuous f
  hv_meas : Measurable (α := G) (β := ℝ) v
  hf_nonneg : ∀ x, 0 ≤ f x
  hf_le : ∀ x, f x ≤ 1
  hv_nonneg : ∀ x, 0 ≤ v x
  hv_le : ∀ x, v x ≤ 1
  mean_f_le : (∫ x, f x ∂μ) ≤ 1 - ρ
  mean_v_ge : α ≤ ∫ x, v x ∂μ
  hf_level : LevelOneSubgroupKernel f
  hf_level_null :
    μ ((levelOneAddSubgroup f hf_level : AddSubgroup G) : Set G) = 0
  counting_convergence :
    Tendsto
      (fun n =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          finiteAvoidanceDensity (m := m) (S.F n) (S.U n)).re)
      atTop (𝓝 (continuousWeightedAvoidanceDensity μ m f v))

/-- Intermediate Route A compact model endpoint.

This version asks for the level-one subgroup to have infinite index.  The
measure-theoretic endpoint converts that finite-index obstruction into
Haar-nullness, so this is often a more algebraic target for the extraction-dual
construction than proving the nullness field directly. -/
structure WeightedCompactInfiniteIndexModel {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ)
    (G : Type u) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] where
  f : G → ℝ
  v : G → ℝ
  hf_cont : Continuous f
  hv_meas : Measurable (α := G) (β := ℝ) v
  hf_nonneg : ∀ x, 0 ≤ f x
  hf_le : ∀ x, f x ≤ 1
  hv_nonneg : ∀ x, 0 ≤ v x
  hv_le : ∀ x, v x ≤ 1
  mean_f_le : (∫ x, f x ∂μ) ≤ 1 - ρ
  mean_v_ge : α ≤ ∫ x, v x ∂μ
  hf_level : LevelOneSubgroupKernel f
  hf_level_not_finiteIndex :
    ¬ (levelOneAddSubgroup f hf_level : AddSubgroup G).FiniteIndex
  counting_convergence :
    Tendsto
      (fun n =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          finiteAvoidanceDensity (m := m) (S.F n) (S.U n)).re)
      atTop (𝓝 (continuousWeightedAvoidanceDensity μ m f v))

/-- Infinite index of the level-one subgroup supplies the nullness certificate
needed by `WeightedCompactNullModel`. -/
def WeightedCompactInfiniteIndexModel.toNullModel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (model : WeightedCompactInfiniteIndexModel S G μ) :
    WeightedCompactNullModel S G μ := by
  refine
    { f := model.f
      v := model.v
      hf_cont := model.hf_cont
      hv_meas := model.hv_meas
      hf_nonneg := model.hf_nonneg
      hf_le := model.hf_le
      hv_nonneg := model.hv_nonneg
      hv_le := model.hv_le
      mean_f_le := model.mean_f_le
      mean_v_ge := model.mean_v_ge
      hf_level := model.hf_level
      hf_level_null := ?_
      counting_convergence := model.counting_convergence }
  let H : AddSubgroup G := levelOneAddSubgroup model.f model.hf_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed model.hf_level model.hf_cont
  exact closed_subgroup_haar_null_of_not_finiteIndex μ H hH_closed
    model.hf_level_not_finiteIndex

/-- Final Route A compactness contradiction:
a counterexample sequence cannot have the expected weighted compact model. -/
theorem FourierAvoidanceCounterSeq.false_of_weightedCompactModel
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hα : 0 < α) (hρ : 0 < ρ) (model : WeightedCompactModel S G μ) : False := by
  have hfinite_zero := S.finiteAvoidanceDensity_re_tendsto_zero
  have hcompact_limit := model.counting_convergence
  have hlimit_eq :
      continuousWeightedAvoidanceDensity μ m model.f model.v = 0 :=
    tendsto_nhds_unique hcompact_limit hfinite_zero
  have hcompact_pos :
      0 < continuousWeightedAvoidanceDensity μ m model.f model.v :=
    continuousWeightedAvoidanceDensity_pos_of_levelOneSubgroupKernel
      μ m model.f model.v model.hf_cont model.hv_meas
      model.hf_nonneg model.hf_le model.hv_nonneg model.hv_le
      model.hf_level hρ model.mean_f_le hα model.mean_v_ge
  linarith

/-- Final Route A compactness contradiction from the narrower null-subgroup
compact model. -/
theorem FourierAvoidanceCounterSeq.false_of_weightedCompactNullModel
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hα : 0 < α) (model : WeightedCompactNullModel S G μ) : False := by
  have hfinite_zero := S.finiteAvoidanceDensity_re_tendsto_zero
  have hcompact_limit := model.counting_convergence
  have hlimit_eq :
      continuousWeightedAvoidanceDensity μ m model.f model.v = 0 :=
    tendsto_nhds_unique hcompact_limit hfinite_zero
  have hcompact_pos :
      0 < continuousWeightedAvoidanceDensity μ m model.f model.v := by
    let H : AddSubgroup G := levelOneAddSubgroup model.f model.hf_level
    have hH_closed : IsClosed (H : Set G) :=
      levelOneAddSubgroup_isClosed model.hf_level model.hf_cont
    have hH_eq : ∀ x : G, x ∈ H ↔ model.f x = 1 := by
      intro x
      rfl
    exact continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup_of_integral_ge
      μ m model.f model.v model.hf_cont.measurable model.hv_meas
      model.hf_nonneg model.hf_le model.hv_nonneg model.hv_le H hH_closed
      hH_eq model.hf_level_null hα model.mean_v_ge
  linarith

/-- Final Route A compactness contradiction from the infinite-index compact
model form. -/
theorem FourierAvoidanceCounterSeq.false_of_weightedCompactInfiniteIndexModel
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hα : 0 < α) (model : WeightedCompactInfiniteIndexModel S G μ) : False :=
  S.false_of_weightedCompactNullModel hα model.toNullModel

/-- Fixed-ambient form: no counterexample sequence can have a weighted compact
model in the same compact group and Haar space.  The eventual extraction theorem
will usually construct the ambient group from the sequence, so the previous
theorem is the more general endpoint; this wrapper is convenient for audits. -/
theorem not_exists_counterSeq_with_weightedCompactModel
    {m : ℕ} {α ρ : ℝ}
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hα : 0 < α) (hρ : 0 < ρ) :
    ¬ ∃ S : FourierAvoidanceCounterSeq m α ρ, Nonempty (WeightedCompactModel S G μ) := by
  rintro ⟨S, model⟩
  exact S.false_of_weightedCompactModel hα hρ model.some

/-- No Route A counterexample sequence can have the narrower null-subgroup
weighted compact model. -/
theorem not_exists_counterSeq_with_weightedCompactNullModel
    {m : ℕ} {α ρ : ℝ}
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    {μ : Measure G} [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hα : 0 < α) :
    ¬ ∃ S : FourierAvoidanceCounterSeq m α ρ,
      Nonempty (WeightedCompactNullModel S G μ) := by
  rintro ⟨S, model⟩
  exact S.false_of_weightedCompactNullModel hα model.some

/-- Sequence-dependent compact-model construction hypothesis.

This is the precise remaining Route A target: every counterexample sequence
should produce some connected compact abelian Haar probability space and a
`WeightedCompactModel` on it.  The theorem below proves that this target implies
the explicit finite Fourier avoidance count statement. -/
def HasWeightedCompactModel {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ) : Prop :=
  ∃ (G : Type u), ∃ (_ : AddCommGroup G), ∃ (_ : TopologicalSpace G),
  ∃ (_ : IsTopologicalAddGroup G), ∃ (_ : CompactSpace G), ∃ (_ : T2Space G),
  ∃ (_ : ConnectedSpace G), ∃ (_ : MeasurableSpace G), ∃ (_ : BorelSpace G),
  ∃ (_ : MeasurableSub₂ G), ∃ (_ : MeasurableAdd₂ G), ∃ (_ : MeasurableNeg G),
  ∃ (μ : Measure G), ∃ (_ : μ.IsAddHaarMeasure), ∃ (_ : IsProbabilityMeasure μ),
    Nonempty (WeightedCompactModel S G μ)

/-- Narrower sequence-dependent compact-model construction target.

Compared with `HasWeightedCompactModel`, this removes the ambient
`ConnectedSpace` requirement and instead requires the exact Haar-null
certificate for the level-one subgroup inside `WeightedCompactNullModel`. -/
def HasWeightedCompactNullModel {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ) : Prop :=
  ∃ (G : Type), ∃ (_ : AddCommGroup G), ∃ (_ : TopologicalSpace G),
  ∃ (_ : IsTopologicalAddGroup G), ∃ (_ : CompactSpace G), ∃ (_ : T2Space G),
  ∃ (_ : MeasurableSpace G), ∃ (_ : BorelSpace G),
  ∃ (_ : MeasurableSub₂ G), ∃ (_ : MeasurableAdd₂ G), ∃ (_ : MeasurableNeg G),
  ∃ (μ : Measure G), ∃ (_ : μ.IsAddHaarMeasure), ∃ (_ : IsProbabilityMeasure μ),
    Nonempty (WeightedCompactNullModel S G μ)

/-- Algebraic sequence-dependent compact-model construction target.

This asks the compact extraction to prove that the level-one subgroup has
infinite index.  `WeightedCompactInfiniteIndexModel.toNullModel` then turns that
into the null-subgroup compact model needed by the continuous endpoint. -/
def HasWeightedCompactInfiniteIndexModel {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ) : Prop :=
  ∃ (G : Type), ∃ (_ : AddCommGroup G), ∃ (_ : TopologicalSpace G),
  ∃ (_ : IsTopologicalAddGroup G), ∃ (_ : CompactSpace G), ∃ (_ : T2Space G),
  ∃ (_ : MeasurableSpace G), ∃ (_ : BorelSpace G),
  ∃ (_ : MeasurableSub₂ G), ∃ (_ : MeasurableAdd₂ G), ∃ (_ : MeasurableNeg G),
  ∃ (μ : Measure G), ∃ (_ : μ.IsAddHaarMeasure), ∃ (_ : IsProbabilityMeasure μ),
    Nonempty (WeightedCompactInfiniteIndexModel S G μ)

/-- The concrete extraction-dual version of the remaining Route A compact-model
target.  This is the shape expected from the large-spectrum compactness
construction after the finite coefficient limits have been stabilized. -/
def HasExtractionWeightedCompactNullModel {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ) : Prop :=
  ∃ data : StableExtendedLargeSpectrumCoeffLimitData S,
    let d := data.toExtendedLargeSpectrumCoeffLimitData
    letI : T2Space (ExtractionCompactAddDual d) :=
      extractionCompactAddDual_t2Space d
    Nonempty
      (WeightedCompactNullModel S
        (ExtractionCompactAddDual d)
        (extractionCompactAddDualHaar d))

/-- Concrete extraction-dual version of the algebraic infinite-index compact
model target. -/
def HasExtractionWeightedCompactInfiniteIndexModel {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ) : Prop :=
  ∃ data : StableExtendedLargeSpectrumCoeffLimitData S,
    let d := data.toExtendedLargeSpectrumCoeffLimitData
    letI : T2Space (ExtractionCompactAddDual d) :=
      extractionCompactAddDual_t2Space d
    Nonempty
      (WeightedCompactInfiniteIndexModel S
        (ExtractionCompactAddDual d)
        (extractionCompactAddDualHaar d))

/-- The algebraic infinite-index compact model is a valid null-model target. -/
theorem hasWeightedCompactNullModel_of_hasWeightedCompactInfiniteIndexModel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (hS : HasWeightedCompactInfiniteIndexModel S) :
    HasWeightedCompactNullModel S := by
  rcases hS with
    ⟨G, instAddCommGroup, instTopologicalSpace, instTopologicalAddGroup,
      instCompactSpace, instT2Space, instMeasurableSpace, instBorelSpace,
      instMeasurableSub₂, instMeasurableAdd₂, instMeasurableNeg,
      μ, instHaar, instProbability, model⟩
  letI : AddCommGroup G := instAddCommGroup
  letI : TopologicalSpace G := instTopologicalSpace
  letI : IsTopologicalAddGroup G := instTopologicalAddGroup
  letI : CompactSpace G := instCompactSpace
  letI : T2Space G := instT2Space
  letI : MeasurableSpace G := instMeasurableSpace
  letI : BorelSpace G := instBorelSpace
  letI : MeasurableSub₂ G := instMeasurableSub₂
  letI : MeasurableAdd₂ G := instMeasurableAdd₂
  letI : MeasurableNeg G := instMeasurableNeg
  letI : μ.IsAddHaarMeasure := instHaar
  letI : IsProbabilityMeasure μ := instProbability
  exact
    ⟨G, instAddCommGroup, instTopologicalSpace, instTopologicalAddGroup,
      instCompactSpace, instT2Space, instMeasurableSpace, instBorelSpace,
      instMeasurableSub₂, instMeasurableAdd₂, instMeasurableNeg,
      μ, instHaar, instProbability, ⟨model.some.toNullModel⟩⟩

/-- A concrete extraction-dual infinite-index compact model is a valid
sequence-dependent infinite-index compact model. -/
theorem hasWeightedCompactInfiniteIndexModel_of_hasExtractionWeightedCompactInfiniteIndexModel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (hS : HasExtractionWeightedCompactInfiniteIndexModel S) :
    HasWeightedCompactInfiniteIndexModel S := by
  rcases hS with ⟨data, model⟩
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  letI : T2Space (ExtractionCompactAddDual d) :=
    extractionCompactAddDual_t2Space d
  refine ⟨ExtractionCompactAddDual d, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, extractionCompactAddDualHaar d, inferInstance, inferInstance, ?_⟩
  · exact extractionCompactAddDual_t2Space d
  · exact model

/-- A compact null-model built on the concrete extraction compact dual is a
valid instance of the abstract sequence-dependent null-model target. -/
theorem hasWeightedCompactNullModel_of_hasExtractionWeightedCompactNullModel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (hS : HasExtractionWeightedCompactNullModel S) :
    HasWeightedCompactNullModel S := by
  rcases hS with ⟨data, model⟩
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  letI : T2Space (ExtractionCompactAddDual d) :=
    extractionCompactAddDual_t2Space d
  refine ⟨ExtractionCompactAddDual d, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, extractionCompactAddDualHaar d, inferInstance, inferInstance, ?_⟩
  · exact extractionCompactAddDual_t2Space d
  · exact model

/-- A concrete extraction-dual infinite-index compact model is sufficient for
the abstract null-model target. -/
theorem hasWeightedCompactNullModel_of_hasExtractionWeightedCompactInfiniteIndexModel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (hS : HasExtractionWeightedCompactInfiniteIndexModel S) :
    HasWeightedCompactNullModel S :=
  hasWeightedCompactNullModel_of_hasWeightedCompactInfiniteIndexModel
    (hasWeightedCompactInfiniteIndexModel_of_hasExtractionWeightedCompactInfiniteIndexModel hS)

/-- If the expected compact model can be constructed for every Route A
counterexample sequence, then the explicit-prime finite Fourier avoidance count
statement follows. -/
theorem finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hmodel : ∀ S : FourierAvoidanceCounterSeq m α ρ, HasWeightedCompactModel S) :
    FiniteFourierAvoidanceCountStatementExplicit m α ρ := by
  by_contra hfail
  obtain ⟨S, _hS⟩ :=
    exists_fourierAvoidanceCounterSeq_of_not_finiteFourierAvoidanceCountStatementExplicit
      (m := m) (α := α) (ρ := ρ) hfail
  rcases hmodel S with
    ⟨G, instAddCommGroup, instTopologicalSpace, instTopologicalAddGroup,
      instCompactSpace, instT2Space, instConnectedSpace, instMeasurableSpace,
      instBorelSpace, instMeasurableSub₂, instMeasurableAdd₂, instMeasurableNeg,
      μ, instHaar, instProbability, model⟩
  letI : AddCommGroup G := instAddCommGroup
  letI : TopologicalSpace G := instTopologicalSpace
  letI : IsTopologicalAddGroup G := instTopologicalAddGroup
  letI : CompactSpace G := instCompactSpace
  letI : T2Space G := instT2Space
  letI : ConnectedSpace G := instConnectedSpace
  letI : MeasurableSpace G := instMeasurableSpace
  letI : BorelSpace G := instBorelSpace
  letI : MeasurableSub₂ G := instMeasurableSub₂
  letI : MeasurableAdd₂ G := instMeasurableAdd₂
  letI : MeasurableNeg G := instMeasurableNeg
  letI : μ.IsAddHaarMeasure := instHaar
  letI : IsProbabilityMeasure μ := instProbability
  exact S.false_of_weightedCompactModel hα hρ model.some

/-- The narrower null-subgroup compact-model construction target is also
sufficient to prove the explicit-prime finite Fourier avoidance count
statement. -/
theorem finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactNullModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α)
    (hmodel : ∀ S : FourierAvoidanceCounterSeq m α ρ, HasWeightedCompactNullModel S) :
    FiniteFourierAvoidanceCountStatementExplicit m α ρ := by
  by_contra hfail
  obtain ⟨S, _hS⟩ :=
    exists_fourierAvoidanceCounterSeq_of_not_finiteFourierAvoidanceCountStatementExplicit
      (m := m) (α := α) (ρ := ρ) hfail
  rcases hmodel S with
    ⟨G, instAddCommGroup, instTopologicalSpace, instTopologicalAddGroup,
      instCompactSpace, instT2Space, instMeasurableSpace, instBorelSpace,
      instMeasurableSub₂, instMeasurableAdd₂, instMeasurableNeg,
      μ, instHaar, instProbability, model⟩
  letI : AddCommGroup G := instAddCommGroup
  letI : TopologicalSpace G := instTopologicalSpace
  letI : IsTopologicalAddGroup G := instTopologicalAddGroup
  letI : CompactSpace G := instCompactSpace
  letI : T2Space G := instT2Space
  letI : MeasurableSpace G := instMeasurableSpace
  letI : BorelSpace G := instBorelSpace
  letI : MeasurableSub₂ G := instMeasurableSub₂
  letI : MeasurableAdd₂ G := instMeasurableAdd₂
  letI : MeasurableNeg G := instMeasurableNeg
  letI : μ.IsAddHaarMeasure := instHaar
  letI : IsProbabilityMeasure μ := instProbability
  exact S.false_of_weightedCompactNullModel hα model.some

/-- The infinite-index compact-model construction target is sufficient to prove
the explicit-prime finite Fourier avoidance count statement. -/
theorem finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactInfiniteIndexModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α)
    (hmodel :
      ∀ S : FourierAvoidanceCounterSeq m α ρ,
        HasWeightedCompactInfiniteIndexModel S) :
    FiniteFourierAvoidanceCountStatementExplicit m α ρ :=
  finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactNullModel
    hα (fun S => hasWeightedCompactNullModel_of_hasWeightedCompactInfiniteIndexModel
      (hmodel S))

/-- The concrete extraction-dual null-model construction target is sufficient
to prove the explicit-prime finite Fourier avoidance count statement. -/
theorem finiteFourierAvoidanceCountStatementExplicit_of_forall_hasExtractionWeightedCompactNullModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α)
    (hmodel :
      ∀ S : FourierAvoidanceCounterSeq m α ρ,
        HasExtractionWeightedCompactNullModel S) :
    FiniteFourierAvoidanceCountStatementExplicit m α ρ :=
  finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactNullModel
    hα (fun S => hasWeightedCompactNullModel_of_hasExtractionWeightedCompactNullModel
      (hmodel S))

/-- The concrete extraction-dual infinite-index compact-model construction
target is sufficient to prove the explicit-prime finite Fourier avoidance count
statement. -/
theorem finiteFourierAvoidanceCountStatementExplicit_of_forall_hasExtractionWeightedCompactInfiniteIndexModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α)
    (hmodel :
      ∀ S : FourierAvoidanceCounterSeq m α ρ,
        HasExtractionWeightedCompactInfiniteIndexModel S) :
    FiniteFourierAvoidanceCountStatementExplicit m α ρ :=
  finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactNullModel
    hα (fun S => hasWeightedCompactNullModel_of_hasExtractionWeightedCompactInfiniteIndexModel
      (hmodel S))

/-- Typeclass-shaped Route A count statement derived from the same
sequence-dependent compact-model construction target.  This has the same
conclusion shape as the current `finite_fourier_avoidance_count` axiom. -/
theorem finite_fourier_avoidance_count_statement_of_forall_hasWeightedCompactModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ)
    (hmodel : ∀ S : FourierAvoidanceCounterSeq m α ρ, HasWeightedCompactModel S) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      c * (p : ℝ) ^ m ≤
        (((Finset.univ : Finset (Fin m → ZMod p)).filter
          (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ) :=
  finite_fourier_avoidance_count_statement_from_explicit
    (finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactModel
      hα hρ hmodel)

/-- Typeclass-shaped Route A count statement derived from the narrower
null-subgroup compact-model construction target. -/
theorem finite_fourier_avoidance_count_statement_of_forall_hasWeightedCompactNullModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α)
    (hmodel : ∀ S : FourierAvoidanceCounterSeq m α ρ, HasWeightedCompactNullModel S) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      c * (p : ℝ) ^ m ≤
        (((Finset.univ : Finset (Fin m → ZMod p)).filter
          (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ) :=
  finite_fourier_avoidance_count_statement_from_explicit
    (finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactNullModel
      hα hmodel)

/-- Typeclass-shaped Route A count statement derived from the infinite-index
compact-model construction target. -/
theorem finite_fourier_avoidance_count_statement_of_forall_hasWeightedCompactInfiniteIndexModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α)
    (hmodel :
      ∀ S : FourierAvoidanceCounterSeq m α ρ,
        HasWeightedCompactInfiniteIndexModel S) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      c * (p : ℝ) ^ m ≤
        (((Finset.univ : Finset (Fin m → ZMod p)).filter
          (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ) :=
  finite_fourier_avoidance_count_statement_from_explicit
    (finiteFourierAvoidanceCountStatementExplicit_of_forall_hasWeightedCompactInfiniteIndexModel
      hα hmodel)

/-- Typeclass-shaped Route A count statement derived from the concrete
extraction-dual null-model construction target.  This is the current narrowest
replacement target for the `finite_fourier_avoidance_count` axiom. -/
theorem finite_fourier_avoidance_count_statement_of_forall_hasExtractionWeightedCompactNullModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α)
    (hmodel :
      ∀ S : FourierAvoidanceCounterSeq m α ρ,
        HasExtractionWeightedCompactNullModel S) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      c * (p : ℝ) ^ m ≤
        (((Finset.univ : Finset (Fin m → ZMod p)).filter
          (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ) :=
  finite_fourier_avoidance_count_statement_from_explicit
    (finiteFourierAvoidanceCountStatementExplicit_of_forall_hasExtractionWeightedCompactNullModel
      hα hmodel)

/-- Typeclass-shaped Route A count statement derived from the concrete
extraction-dual infinite-index compact-model construction target. -/
theorem finite_fourier_avoidance_count_statement_of_forall_hasExtractionWeightedCompactInfiniteIndexModel
    {m : ℕ} {α ρ : ℝ} (hα : 0 < α)
    (hmodel :
      ∀ S : FourierAvoidanceCounterSeq m α ρ,
        HasExtractionWeightedCompactInfiniteIndexModel S) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      c * (p : ℝ) ^ m ≤
        (((Finset.univ : Finset (Fin m → ZMod p)).filter
          (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ) :=
  finite_fourier_avoidance_count_statement_from_explicit
    (finiteFourierAvoidanceCountStatementExplicit_of_forall_hasExtractionWeightedCompactInfiniteIndexModel
      hα hmodel)

end Erdos42.FourierPositive
