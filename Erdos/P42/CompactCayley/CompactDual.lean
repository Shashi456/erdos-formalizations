/-
Erdős Problem 42 — compact dual attached to compact-Cayley extraction.

The extraction quotient is a countable discrete torsion-free abelian group.
This file builds its Pontryagin dual, then wraps it additively so the compact
endpoint can use additive notation and Haar probability measure.
-/

import Erdos.P42.CompactCayley.CayleyExtraction
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Haar.Basic

namespace Erdos42.CompactCayley

open scoped Classical

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

instance groupTopologicalSpace (E : CayleyExtraction S) :
    TopologicalSpace E.Group :=
  ⊥

instance groupDiscreteTopology (E : CayleyExtraction S) :
    DiscreteTopology E.Group :=
  ⟨rfl⟩

/-- Multiplicative version of the extraction quotient, for Mathlib's
`PontryaginDual` API. -/
abbrev DualDomain (E : CayleyExtraction S) : Type :=
  Multiplicative E.Group

/-- Compact Pontryagin dual of the extraction quotient. -/
abbrev CompactDual (E : CayleyExtraction S) : Type :=
  PontryaginDual E.DualDomain

/-- Additive wrapper around the compact extraction dual. -/
abbrev CompactAddDual (E : CayleyExtraction S) : Type :=
  Additive E.CompactDual

theorem compactDual_compactSpace (E : CayleyExtraction S) :
    CompactSpace E.CompactDual :=
  inferInstance

theorem compactDual_t2Space (E : CayleyExtraction S) :
    T2Space E.CompactDual :=
  inferInstance

theorem compactDual_isTopologicalGroup (E : CayleyExtraction S) :
    IsTopologicalGroup E.CompactDual :=
  inferInstance

instance dualDomainCountable (E : CayleyExtraction S) :
    Countable E.DualDomain :=
  Countable.of_equiv E.Group Multiplicative.ofAdd

instance dualDomainDiscreteTopology (E : CayleyExtraction S) :
    DiscreteTopology E.DualDomain :=
  inferInstance

instance dualDomainSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.DualDomain := by
  letI : Countable E.DualDomain := dualDomainCountable E
  letI : DiscreteTopology E.DualDomain := dualDomainDiscreteTopology E
  infer_instance

instance compactDualSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.CompactDual := by
  dsimp [CompactDual, PontryaginDual]
  exact (ContinuousMonoidHom.isInducing_toContinuousMap
    E.DualDomain Circle).secondCountableTopology

theorem dualDomain_isMulTorsionFree (E : CayleyExtraction S) :
    IsMulTorsionFree E.DualDomain :=
  inferInstance

/-- Identity homeomorphism from the multiplicative compact dual to its
additive wrapper. -/
def compactDualAdditiveHomeomorph (E : CayleyExtraction S) :
    E.CompactDual ≃ₜ E.CompactAddDual where
  toEquiv := Additive.ofMul
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

theorem compactAddDual_t2Space (E : CayleyExtraction S) :
    T2Space E.CompactAddDual :=
  (E.compactDualAdditiveHomeomorph).t2Space

theorem compactAddDual_compactSpace (E : CayleyExtraction S) :
    CompactSpace E.CompactAddDual :=
  inferInstance

theorem compactAddDual_isTopologicalAddGroup (E : CayleyExtraction S) :
    IsTopologicalAddGroup E.CompactAddDual :=
  inferInstance

instance compactAddDualSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.CompactAddDual :=
  (E.compactDualAdditiveHomeomorph).symm.secondCountableTopology

instance compactAddDualMeasurableSpace (E : CayleyExtraction S) :
    MeasurableSpace E.CompactAddDual :=
  borel E.CompactAddDual

instance compactAddDualBorelSpace (E : CayleyExtraction S) :
    BorelSpace E.CompactAddDual :=
  ⟨rfl⟩

instance compactAddDualMeasurableAdd₂ (E : CayleyExtraction S) :
    MeasurableAdd₂ E.CompactAddDual where
  measurable_add := continuous_add.measurable

instance compactAddDualMeasurableNeg (E : CayleyExtraction S) :
    MeasurableNeg E.CompactAddDual where
  measurable_neg := continuous_neg.measurable

instance compactAddDualMeasurableSub₂ (E : CayleyExtraction S) :
    MeasurableSub₂ E.CompactAddDual where
  measurable_sub := continuous_sub.measurable

/-- Normalized additive Haar probability measure on the compact additive dual. -/
noncomputable def haar (E : CayleyExtraction S) :
    MeasureTheory.Measure E.CompactAddDual :=
  MeasureTheory.Measure.addHaarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts E.CompactAddDual)

instance haar_isAddHaarMeasure (E : CayleyExtraction S) :
    (E.haar).IsAddHaarMeasure := by
  unfold haar
  infer_instance

instance haar_isOpenPosMeasure (E : CayleyExtraction S) :
    (E.haar).IsOpenPosMeasure :=
  inferInstance

instance haar_isProbabilityMeasure (E : CayleyExtraction S) :
    MeasureTheory.IsProbabilityMeasure E.haar where
  measure_univ := by
    unfold haar
    simpa using
      (MeasureTheory.Measure.addHaarMeasure_self
        (K₀ := (⊤ : TopologicalSpace.PositiveCompacts E.CompactAddDual)))

end CayleyExtraction

end

end Erdos42.CompactCayley
