/-
Erdos Problem 42 — Route A compact dual skeleton.

The extraction quotient from `ExtractionGroup` is the discrete abelian group
whose Pontryagin dual is the compact group used by the finite-Fourier
compactness argument.  This file only installs the discrete topology and
records the compact-dual interface; the connectedness theorem for torsion-free
discrete duals is a later step.
-/

import Erdos.P42.FourierPositive.ExtractionGroup
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace Erdos42.FourierPositive

open scoped Classical

noncomputable section

instance largeSpectrumIndexCountable : Countable LargeSpectrumIndex := by
  dsimp [LargeSpectrumIndex, LargeSpectrumLabel]
  infer_instance

instance extendedLargeSpectrumIndexCountable :
    Countable ExtendedLargeSpectrumIndex := by
  dsimp [ExtendedLargeSpectrumIndex]
  infer_instance

instance extractionDiscreteGroupTopologicalSpace
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    TopologicalSpace (ExtractionDiscreteGroup data) :=
  ⊥

instance extractionDiscreteGroupDiscreteTopology
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    DiscreteTopology (ExtractionDiscreteGroup data) :=
  ⟨rfl⟩

instance extractionDiscreteGroupInstIsAddTorsionFree
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    IsAddTorsionFree (ExtractionDiscreteGroup data) :=
  extractionDiscreteGroup_isAddTorsionFree data

/-- Multiplicative version of the discrete extraction quotient, for Mathlib's
`PontryaginDual` API. -/
abbrev ExtractionDualDomain
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) : Type :=
  Multiplicative (ExtractionDiscreteGroup data)

/-- Compact dual group attached to the Route A extraction quotient. -/
abbrev ExtractionCompactDual
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) : Type :=
  PontryaginDual (ExtractionDualDomain data)

/-- Additive wrapper around the compact extraction dual.  The continuous
Route A endpoint is stated additively, while Mathlib's `PontryaginDual` API is
multiplicative, so this is the ambient group used for the compact model. -/
abbrev ExtractionCompactAddDual
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) : Type :=
  Additive (ExtractionCompactDual data)

theorem extractionCompactDual_compactSpace
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    CompactSpace (ExtractionCompactDual data) :=
  inferInstance

theorem extractionCompactDual_t2Space
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    T2Space (ExtractionCompactDual data) :=
  inferInstance

theorem extractionCompactDual_isTopologicalGroup
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    IsTopologicalGroup (ExtractionCompactDual data) :=
  inferInstance

instance extractionDiscreteGroupCountable
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    Countable (ExtractionDiscreteGroup data) :=
  (QuotientAddGroup.mk'_surjective (extractionEventualKernel data)).countable

instance extractionDualDomainCountable
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    Countable (ExtractionDualDomain data) :=
  Countable.of_equiv (ExtractionDiscreteGroup data) Multiplicative.ofAdd

instance extractionDualDomainDiscreteTopology
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    DiscreteTopology (ExtractionDualDomain data) :=
  inferInstance

instance extractionDualDomainSecondCountableTopology
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    SecondCountableTopology (ExtractionDualDomain data) := by
  letI : Countable (ExtractionDualDomain data) :=
    extractionDualDomainCountable data
  letI : DiscreteTopology (ExtractionDualDomain data) :=
    extractionDualDomainDiscreteTopology data
  infer_instance

instance extractionCompactDualSecondCountableTopology
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    SecondCountableTopology (ExtractionCompactDual data) := by
  dsimp [ExtractionCompactDual, PontryaginDual]
  exact (ContinuousMonoidHom.isInducing_toContinuousMap
    (ExtractionDualDomain data) Circle).secondCountableTopology

theorem extractionDualDomain_isMulTorsionFree
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    IsMulTorsionFree (ExtractionDualDomain data) :=
  inferInstance

/-- The identity homeomorphism from the multiplicative compact dual to its
additive wrapper. -/
def extractionCompactDualAdditiveHomeomorph
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    ExtractionCompactDual data ≃ₜ ExtractionCompactAddDual data where
  toEquiv := Additive.ofMul
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

theorem extractionCompactAddDual_t2Space
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    T2Space (ExtractionCompactAddDual data) :=
  (extractionCompactDualAdditiveHomeomorph data).t2Space

theorem extractionCompactAddDual_compactSpace
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    CompactSpace (ExtractionCompactAddDual data) :=
  inferInstance

theorem extractionCompactAddDual_isTopologicalAddGroup
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    IsTopologicalAddGroup (ExtractionCompactAddDual data) :=
  inferInstance

instance extractionCompactAddDualSecondCountableTopology
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    SecondCountableTopology (ExtractionCompactAddDual data) :=
  (extractionCompactDualAdditiveHomeomorph data).symm.secondCountableTopology

instance extractionCompactAddDualMeasurableSpace
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    MeasurableSpace (ExtractionCompactAddDual data) :=
  borel (ExtractionCompactAddDual data)

instance extractionCompactAddDualBorelSpace
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    BorelSpace (ExtractionCompactAddDual data) :=
  ⟨rfl⟩

instance extractionCompactAddDualMeasurableAdd₂
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    MeasurableAdd₂ (ExtractionCompactAddDual data) where
  measurable_add := continuous_add.measurable

instance extractionCompactAddDualMeasurableNeg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    MeasurableNeg (ExtractionCompactAddDual data) where
  measurable_neg := continuous_neg.measurable

instance extractionCompactAddDualMeasurableSub₂
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    MeasurableSub₂ (ExtractionCompactAddDual data) where
  measurable_sub := continuous_sub.measurable

/-- The normalized additive Haar probability measure on the compact additive
extraction dual.  It is normalized by taking the whole compact group as the
positive compact set. -/
noncomputable def extractionCompactAddDualHaar
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    MeasureTheory.Measure (ExtractionCompactAddDual data) :=
  MeasureTheory.Measure.addHaarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts (ExtractionCompactAddDual data))

instance extractionCompactAddDualHaar_isAddHaarMeasure
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    (extractionCompactAddDualHaar data).IsAddHaarMeasure := by
  unfold extractionCompactAddDualHaar
  infer_instance

instance extractionCompactAddDualHaar_isProbabilityMeasure
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    MeasureTheory.IsProbabilityMeasure (extractionCompactAddDualHaar data) where
  measure_univ := by
    unfold extractionCompactAddDualHaar
    simpa using
      (MeasureTheory.Measure.addHaarMeasure_self
        (K₀ := (⊤ :
          TopologicalSpace.PositiveCompacts (ExtractionCompactAddDual data))))

end

end Erdos42.FourierPositive
