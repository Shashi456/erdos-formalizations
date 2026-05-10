/-
Erdos Problem 42 — Route A trigonometric polynomial skeleton.

This file defines finitely supported Fourier polynomials on the extraction
quotient and their finite cyclic lifts.  The finite lift of a quotient element
uses a chosen representative, so equality with a preferred representative is
recorded as an eventual statement along the extracted subsequence.
-/

import Erdos.P42.FourierPositive.CompactDual

namespace Erdos42.FourierPositive

open Filter Complex
open scoped BigOperators Classical ComplexConjugate Topology

noncomputable section

/-- Trigonometric polynomials on the extraction quotient. -/
abbrev ExtractionTrigPoly
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) : Type :=
  ExtractionDiscreteGroup data →₀ ℂ

/-- Convolution product of extraction trigonometric polynomials, with quotient
frequencies added.  This is kept explicit rather than using the ambient
`Finsupp` multiplication, which is pointwise and not the Fourier product. -/
noncomputable def ExtractionTrigPoly.convMul
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P Q : ExtractionTrigPoly data) : ExtractionTrigPoly data :=
  P.sum fun γ c => Q.sum fun δ d => Finsupp.single (γ + δ) (c * d)

/-- Evaluation of a dual character at a quotient frequency, viewed in `ℂ`. -/
noncomputable def extractionCharacterValue
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactDual data) (γ : ExtractionDiscreteGroup data) : ℂ :=
  (z (Multiplicative.ofAdd γ) : ℂ)

/-- Compact-side evaluation of an extraction trigonometric polynomial. -/
noncomputable def ExtractionTrigPoly.eval
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) (z : ExtractionCompactDual data) : ℂ :=
  P.sum fun γ c => c * extractionCharacterValue z γ

/-- Evaluation of a dual character on the additive compact-dual wrapper used
by the Route A compact model. -/
noncomputable def extractionAddCharacterValue
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data) (γ : ExtractionDiscreteGroup data) : ℂ :=
  extractionCharacterValue z.toMul γ

/-- Additive-wrapper compact-side evaluation of an extraction trigonometric
polynomial. -/
noncomputable def ExtractionTrigPoly.evalAdd
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) (z : ExtractionCompactAddDual data) : ℂ :=
  P.sum fun γ c => c * extractionAddCharacterValue z γ

/-- Chosen finite lift of a quotient frequency to the `n`-th cyclic group. -/
noncomputable def extractionFiniteLiftFreq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S)
    (n : ℕ) (γ : ExtractionDiscreteGroup data) :
    ZMod (S.p (data.φ n)) :=
  extractionFiniteLiftHom data n (Quotient.out γ)

/-- Forbidden-set Fourier coefficient limit attached to a quotient frequency.
It is defined by the chosen quotient representative; this is enough for finite
trigonometric-polynomial convergence, whose statements also use the same
chosen finite lift. -/
noncomputable def StableExtractionCoeffLimitData.fCoeffQ
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    ℂ :=
  data.fCoeffG (Quotient.out γ)

/-- Vertex-weight Fourier coefficient limit attached to a quotient frequency. -/
noncomputable def StableExtractionCoeffLimitData.uCoeffQ
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    ℂ :=
  data.uCoeffG (Quotient.out γ)

lemma StableExtractionCoeffLimitData.fCoeffQ_tendsto
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto
      (fun n =>
        (letI : NeZero (S.p
            (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
            ⟨(S.prime
              (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          normalizedDftCoeff
            (S.F (data.toExtendedLargeSpectrumCoeffLimitData.φ n))
            (extractionFiniteLiftFreq
              data.toExtendedLargeSpectrumCoeffLimitData n γ)))
      atTop (𝓝 (data.fCoeffQ γ)) := by
  simpa [StableExtractionCoeffLimitData.fCoeffQ, extractionFiniteLiftFreq] using
    data.fCoeffG_tendsto (Quotient.out γ)

lemma StableExtractionCoeffLimitData.uCoeffQ_tendsto
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto
      (fun n =>
        (letI : NeZero (S.p
            (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
            ⟨(S.prime
              (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          normalizedDftCoeff
            (S.U (data.toExtendedLargeSpectrumCoeffLimitData.φ n))
            (extractionFiniteLiftFreq
              data.toExtendedLargeSpectrumCoeffLimitData n γ)))
      atTop (𝓝 (data.uCoeffQ γ)) := by
  simpa [StableExtractionCoeffLimitData.uCoeffQ, extractionFiniteLiftFreq] using
    data.uCoeffG_tendsto (Quotient.out γ)

lemma StableExtractionCoeffLimitData.fCoeffQ_nonneg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    0 ≤ (data.fCoeffQ γ).re :=
  data.fCoeffG_nonneg (Quotient.out γ)

lemma StableExtractionCoeffLimitData.fCoeffQ_im_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    (data.fCoeffQ γ).im = 0 :=
  data.fCoeffG_im_eq_zero (Quotient.out γ)

/-- Finite cyclic-side evaluation of an extraction trigonometric polynomial. -/
noncomputable def ExtractionTrigPoly.evalFinite
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) (n : ℕ)
    (x : ZMod (S.p (data.φ n))) : ℂ :=
  letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  P.sum fun γ c =>
    c * ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))

/-- Normalized finite average of a lifted trigonometric polynomial. -/
noncomputable def ExtractionTrigPoly.finiteAverage
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (data.φ n)) => P.evalFinite n x

/-- Abstract compact-side average of an extraction trigonometric polynomial.

For the eventual Haar model this is the integral over the compact dual; at the
purely algebraic trigonometric-polynomial layer it is exactly the
zero-frequency coefficient. -/
noncomputable def ExtractionTrigPoly.compactAverage
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) : ℂ :=
  P (0 : ExtractionDiscreteGroup data)

/-- Finite average of a lifted trigonometric polynomial against the
forbidden-set indicator. -/
noncomputable def ExtractionTrigPoly.forbiddenWeightedFiniteAverage
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData)
    (n : ℕ) : ℂ :=
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  letI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (d.φ n)) =>
    indicatorC (S.F (d.φ n)) x * P.evalFinite n x

/-- Finite average of a lifted trigonometric polynomial against the vertex
weight indicator. -/
noncomputable def ExtractionTrigPoly.vertexWeightedFiniteAverage
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData)
    (n : ℕ) : ℂ :=
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  letI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (d.φ n)) =>
    indicatorC (S.U (d.φ n)) x * P.evalFinite n x

/-- Compact-limit coefficient functional obtained by pairing a trigonometric
polynomial with forbidden-set Fourier coefficient limits. -/
noncomputable def StableExtractionCoeffLimitData.forbiddenCoeffFunctional
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) : ℂ :=
  P.sum fun γ c => c * data.fCoeffQ γ

/-- Compact-limit coefficient functional obtained by pairing a trigonometric
polynomial with vertex-weight Fourier coefficient limits. -/
noncomputable def StableExtractionCoeffLimitData.vertexCoeffFunctional
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) : ℂ :=
  P.sum fun γ c => c * data.uCoeffQ γ

@[simp]
lemma extractionCharacterValue_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactDual data) :
    extractionCharacterValue z (0 : ExtractionDiscreteGroup data) = 1 := by
  simp [extractionCharacterValue]

@[simp]
lemma extractionCharacterValue_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactDual data)
    (γ δ : ExtractionDiscreteGroup data) :
    extractionCharacterValue z (γ + δ) =
      extractionCharacterValue z γ * extractionCharacterValue z δ := by
  simp [extractionCharacterValue]

@[simp]
lemma extractionCharacterValue_neg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactDual data) (γ : ExtractionDiscreteGroup data) :
    extractionCharacterValue z (-γ) =
      (extractionCharacterValue z γ)⁻¹ := by
  simp [extractionCharacterValue]

@[simp]
lemma star_extractionCharacterValue
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
  (z : ExtractionCompactDual data) (γ : ExtractionDiscreteGroup data) :
    star (extractionCharacterValue z γ) = extractionCharacterValue z (-γ) := by
  unfold extractionCharacterValue
  rw [show star (↑(z (Multiplicative.ofAdd γ)) : ℂ) =
      conj (↑(z (Multiplicative.ofAdd γ)) : ℂ) by rfl]
  rw [← Circle.coe_inv_eq_conj]
  simp

lemma extractionCharacterValue_sub
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactDual data)
    (γ δ : ExtractionDiscreteGroup data) :
    extractionCharacterValue z (γ - δ) =
      extractionCharacterValue z γ * star (extractionCharacterValue z δ) := by
  rw [sub_eq_add_neg, extractionCharacterValue_add, star_extractionCharacterValue]

@[simp]
lemma extractionAddCharacterValue_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data) :
    extractionAddCharacterValue z (0 : ExtractionDiscreteGroup data) = 1 := by
  simp [extractionAddCharacterValue]

@[simp]
lemma extractionAddCharacterValue_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data)
    (γ δ : ExtractionDiscreteGroup data) :
    extractionAddCharacterValue z (γ + δ) =
      extractionAddCharacterValue z γ * extractionAddCharacterValue z δ := by
  simp [extractionAddCharacterValue]

@[simp]
lemma extractionAddCharacterValue_neg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data) (γ : ExtractionDiscreteGroup data) :
    extractionAddCharacterValue z (-γ) =
      (extractionAddCharacterValue z γ)⁻¹ := by
  simp [extractionAddCharacterValue]

@[simp]
lemma star_extractionAddCharacterValue
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data) (γ : ExtractionDiscreteGroup data) :
    star (extractionAddCharacterValue z γ) =
      extractionAddCharacterValue z (-γ) := by
  simp [extractionAddCharacterValue, star_extractionCharacterValue]

lemma extractionAddCharacterValue_sub
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data)
    (γ δ : ExtractionDiscreteGroup data) :
    extractionAddCharacterValue z (γ - δ) =
      extractionAddCharacterValue z γ * star (extractionAddCharacterValue z δ) := by
  simpa [extractionAddCharacterValue] using
    extractionCharacterValue_sub z.toMul γ δ

@[simp]
lemma norm_extractionCharacterValue
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactDual data) (γ : ExtractionDiscreteGroup data) :
    ‖extractionCharacterValue z γ‖ = 1 := by
  exact Circle.norm_coe _

@[simp]
lemma norm_extractionAddCharacterValue
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data) (γ : ExtractionDiscreteGroup data) :
    ‖extractionAddCharacterValue z γ‖ = 1 := by
  simp [extractionAddCharacterValue]

lemma ExtractionTrigPoly.eval_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P Q : ExtractionTrigPoly data) (z : ExtractionCompactDual data) :
    ExtractionTrigPoly.eval (P + Q) z =
      ExtractionTrigPoly.eval P z + ExtractionTrigPoly.eval Q z := by
  unfold ExtractionTrigPoly.eval
  let h : ExtractionDiscreteGroup data → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * extractionCharacterValue z γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma ExtractionTrigPoly.evalAdd_eq_eval
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) (z : ExtractionCompactAddDual data) :
    ExtractionTrigPoly.evalAdd P z =
      ExtractionTrigPoly.eval P z.toMul := by
  rfl

lemma ExtractionTrigPoly.evalAdd_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P Q : ExtractionTrigPoly data) (z : ExtractionCompactAddDual data) :
    ExtractionTrigPoly.evalAdd (P + Q) z =
      ExtractionTrigPoly.evalAdd P z + ExtractionTrigPoly.evalAdd Q z := by
  simpa [ExtractionTrigPoly.evalAdd_eq_eval] using
    ExtractionTrigPoly.eval_add P Q z.toMul

@[simp]
lemma ExtractionTrigPoly.eval_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactDual data) :
    ExtractionTrigPoly.eval (0 : ExtractionTrigPoly data) z = 0 := by
  simp [ExtractionTrigPoly.eval]

@[simp]
lemma ExtractionTrigPoly.evalAdd_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data) :
    ExtractionTrigPoly.evalAdd (0 : ExtractionTrigPoly data) z = 0 := by
  simp [ExtractionTrigPoly.evalAdd_eq_eval]

@[simp]
lemma ExtractionTrigPoly.evalFinite_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (n : ℕ) (x : ZMod (S.p (data.φ n))) :
    ExtractionTrigPoly.evalFinite (0 : ExtractionTrigPoly data) n x = 0 := by
  simp [ExtractionTrigPoly.evalFinite]

lemma ExtractionTrigPoly.evalFinite_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P Q : ExtractionTrigPoly data) (n : ℕ)
    (x : ZMod (S.p (data.φ n))) :
    ExtractionTrigPoly.evalFinite (P + Q) n x =
      ExtractionTrigPoly.evalFinite P n x +
        ExtractionTrigPoly.evalFinite Q n x := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  unfold ExtractionTrigPoly.evalFinite
  let h : ExtractionDiscreteGroup data → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

@[simp]
lemma ExtractionTrigPoly.eval_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) (c : ℂ)
    (z : ExtractionCompactDual data) :
    ExtractionTrigPoly.eval (Finsupp.single γ c : ExtractionTrigPoly data) z =
      c * extractionCharacterValue z γ := by
  simp [ExtractionTrigPoly.eval]

@[simp]
lemma ExtractionTrigPoly.evalAdd_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) (c : ℂ)
    (z : ExtractionCompactAddDual data) :
    ExtractionTrigPoly.evalAdd (Finsupp.single γ c : ExtractionTrigPoly data) z =
      c * extractionAddCharacterValue z γ := by
  simp [ExtractionTrigPoly.evalAdd]

@[simp]
lemma ExtractionTrigPoly.eval_single_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (c : ℂ) (z : ExtractionCompactDual data) :
    ExtractionTrigPoly.eval
        (Finsupp.single (0 : ExtractionDiscreteGroup data) c :
          ExtractionTrigPoly data) z = c := by
  simp

@[simp]
lemma ExtractionTrigPoly.evalAdd_single_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (c : ℂ) (z : ExtractionCompactAddDual data) :
    ExtractionTrigPoly.evalAdd
        (Finsupp.single (0 : ExtractionDiscreteGroup data) c :
          ExtractionTrigPoly data) z = c := by
  simp

lemma ExtractionTrigPoly.convMul_single_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ δ : ExtractionDiscreteGroup data) (c d : ℂ) :
    ExtractionTrigPoly.convMul
        (Finsupp.single γ c : ExtractionTrigPoly data)
        (Finsupp.single δ d : ExtractionTrigPoly data) =
      Finsupp.single (γ + δ) (c * d) := by
  simp [ExtractionTrigPoly.convMul]

lemma ExtractionTrigPoly.evalAdd_convMul_single_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ δ : ExtractionDiscreteGroup data) (c d : ℂ)
    (z : ExtractionCompactAddDual data) :
    ExtractionTrigPoly.evalAdd
        (ExtractionTrigPoly.convMul
          (Finsupp.single γ c : ExtractionTrigPoly data)
          (Finsupp.single δ d : ExtractionTrigPoly data)) z =
      ExtractionTrigPoly.evalAdd
          (Finsupp.single γ c : ExtractionTrigPoly data) z *
        ExtractionTrigPoly.evalAdd
          (Finsupp.single δ d : ExtractionTrigPoly data) z := by
  rw [ExtractionTrigPoly.convMul_single_single]
  exact ExtractionTrigPoly.evalAdd_single (γ + δ) (c * d) z |>.trans (by
    simp [extractionAddCharacterValue_add]
    ring)

/-- Each compact-dual character value is continuous as a complex-valued
function. -/
lemma extractionCharacterValue_continuous
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) :
    Continuous (fun z : ExtractionCompactDual data => extractionCharacterValue z γ) := by
  unfold extractionCharacterValue ExtractionCompactDual PontryaginDual
  exact continuous_subtype_val.comp (continuous_eval_const (Multiplicative.ofAdd γ))

/-- Each additive-wrapper compact-dual character value is continuous as a
complex-valued function. -/
lemma extractionAddCharacterValue_continuous
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) :
    Continuous (fun z : ExtractionCompactAddDual data =>
      extractionAddCharacterValue z γ) := by
  simpa [extractionAddCharacterValue] using
    (extractionCharacterValue_continuous (data := data) γ)

/-- Compact-side evaluation of a trigonometric polynomial is continuous. -/
lemma ExtractionTrigPoly.continuous_eval
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) :
    Continuous (fun z : ExtractionCompactDual data => ExtractionTrigPoly.eval P z) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simpa using (continuous_const :
      Continuous (fun _ : ExtractionCompactDual data => (0 : ℂ)))
  · intro P Q hP hQ
    simpa [ExtractionTrigPoly.eval_add] using hP.add hQ
  · intro γ c
    simpa using
      (continuous_const.mul (extractionCharacterValue_continuous (data := data) γ) :
        Continuous fun z : ExtractionCompactDual data => c * extractionCharacterValue z γ)

/-- Additive-wrapper compact-side evaluation of a trigonometric polynomial is
continuous. -/
lemma ExtractionTrigPoly.continuous_evalAdd
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) :
    Continuous (fun z : ExtractionCompactAddDual data => ExtractionTrigPoly.evalAdd P z) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simpa using (continuous_const :
      Continuous (fun _ : ExtractionCompactAddDual data => (0 : ℂ)))
  · intro P Q hP hQ
    simpa [ExtractionTrigPoly.evalAdd_add] using hP.add hQ
  · intro γ c
    simpa using
      (continuous_const.mul (extractionAddCharacterValue_continuous (data := data) γ) :
        Continuous fun z : ExtractionCompactAddDual data =>
          c * extractionAddCharacterValue z γ)

@[simp]
lemma ExtractionTrigPoly.evalFinite_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) (c : ℂ)
    (n : ℕ) (x : ZMod (S.p (data.φ n))) :
    ExtractionTrigPoly.evalFinite
        (Finsupp.single γ c : ExtractionTrigPoly data) n x =
      (letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩;
        c * ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))) := by
  simp [ExtractionTrigPoly.evalFinite]

lemma ExtractionTrigPoly.forbiddenWeightedFiniteAverage_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)
    (c : ℂ) (n : ℕ) :
    ExtractionTrigPoly.forbiddenWeightedFiniteAverage data
        (Finsupp.single γ c :
          ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) n =
      (letI : NeZero (S.p
          (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime
            (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        c * normalizedDftCoeff
          (S.F (data.toExtendedLargeSpectrumCoeffLimitData.φ n))
          (extractionFiniteLiftFreq
            data.toExtendedLargeSpectrumCoeffLimitData n γ)) := by
  classical
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  rw [ExtractionTrigPoly.forbiddenWeightedFiniteAverage]
  change avgZMod
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.F (d.φ n)) x *
          ExtractionTrigPoly.evalFinite
            (Finsupp.single γ c : ExtractionTrigPoly d) n x) =
    c * normalizedDftCoeff (S.F (d.φ n))
      (extractionFiniteLiftFreq d n γ)
  rw [show
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.F (d.φ n)) x *
          ExtractionTrigPoly.evalFinite
            (Finsupp.single γ c : ExtractionTrigPoly d) n x) =
      (fun x : ZMod (S.p (d.φ n)) =>
        c * (ZMod.stdAddChar
          (-(x * extractionFiniteLiftFreq d n γ)) *
            indicatorC (S.F (d.φ n)) x)) by
        funext x
        simp [ExtractionTrigPoly.evalFinite_single]
        ring_nf]
  rw [avgZMod_const_mul]
  congr 1

lemma ExtractionTrigPoly.vertexWeightedFiniteAverage_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)
    (c : ℂ) (n : ℕ) :
    ExtractionTrigPoly.vertexWeightedFiniteAverage data
        (Finsupp.single γ c :
          ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) n =
      (letI : NeZero (S.p
          (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime
            (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        c * normalizedDftCoeff
          (S.U (data.toExtendedLargeSpectrumCoeffLimitData.φ n))
          (extractionFiniteLiftFreq
            data.toExtendedLargeSpectrumCoeffLimitData n γ)) := by
  classical
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  rw [ExtractionTrigPoly.vertexWeightedFiniteAverage]
  change avgZMod
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.U (d.φ n)) x *
          ExtractionTrigPoly.evalFinite
            (Finsupp.single γ c : ExtractionTrigPoly d) n x) =
    c * normalizedDftCoeff (S.U (d.φ n))
      (extractionFiniteLiftFreq d n γ)
  rw [show
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.U (d.φ n)) x *
          ExtractionTrigPoly.evalFinite
            (Finsupp.single γ c : ExtractionTrigPoly d) n x) =
      (fun x : ZMod (S.p (d.φ n)) =>
        c * (ZMod.stdAddChar
          (-(x * extractionFiniteLiftFreq d n γ)) *
            indicatorC (S.U (d.φ n)) x)) by
        funext x
        simp [ExtractionTrigPoly.evalFinite_single]
        ring_nf]
  rw [avgZMod_const_mul]
  congr 1

lemma ExtractionTrigPoly.forbiddenWeightedFiniteAverage_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P Q : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData)
    (n : ℕ) :
    ExtractionTrigPoly.forbiddenWeightedFiniteAverage data (P + Q) n =
      ExtractionTrigPoly.forbiddenWeightedFiniteAverage data P n +
        ExtractionTrigPoly.forbiddenWeightedFiniteAverage data Q n := by
  classical
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  rw [ExtractionTrigPoly.forbiddenWeightedFiniteAverage,
    ExtractionTrigPoly.forbiddenWeightedFiniteAverage,
    ExtractionTrigPoly.forbiddenWeightedFiniteAverage]
  change avgZMod
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.F (d.φ n)) x *
          ExtractionTrigPoly.evalFinite (P + Q) n x) =
    avgZMod
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.F (d.φ n)) x *
          ExtractionTrigPoly.evalFinite P n x) +
      avgZMod
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.F (d.φ n)) x *
          ExtractionTrigPoly.evalFinite Q n x)
  rw [show
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.F (d.φ n)) x *
          ExtractionTrigPoly.evalFinite (P + Q) n x) =
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.F (d.φ n)) x *
          ExtractionTrigPoly.evalFinite P n x +
        indicatorC (S.F (d.φ n)) x *
          ExtractionTrigPoly.evalFinite Q n x) by
        funext x
        rw [ExtractionTrigPoly.evalFinite_add]
        ring]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma ExtractionTrigPoly.vertexWeightedFiniteAverage_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P Q : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData)
    (n : ℕ) :
    ExtractionTrigPoly.vertexWeightedFiniteAverage data (P + Q) n =
      ExtractionTrigPoly.vertexWeightedFiniteAverage data P n +
        ExtractionTrigPoly.vertexWeightedFiniteAverage data Q n := by
  classical
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  rw [ExtractionTrigPoly.vertexWeightedFiniteAverage,
    ExtractionTrigPoly.vertexWeightedFiniteAverage,
    ExtractionTrigPoly.vertexWeightedFiniteAverage]
  change avgZMod
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.U (d.φ n)) x *
          ExtractionTrigPoly.evalFinite (P + Q) n x) =
    avgZMod
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.U (d.φ n)) x *
          ExtractionTrigPoly.evalFinite P n x) +
      avgZMod
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.U (d.φ n)) x *
          ExtractionTrigPoly.evalFinite Q n x)
  rw [show
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.U (d.φ n)) x *
          ExtractionTrigPoly.evalFinite (P + Q) n x) =
      (fun x : ZMod (S.p (d.φ n)) =>
        indicatorC (S.U (d.φ n)) x *
          ExtractionTrigPoly.evalFinite P n x +
        indicatorC (S.U (d.φ n)) x *
          ExtractionTrigPoly.evalFinite Q n x) by
        funext x
        rw [ExtractionTrigPoly.evalFinite_add]
        ring]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

/-- A chosen representative of a quotient class has the same finite lift as any
specified representative eventually. -/
lemma extractionFiniteLiftFreq_mk_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (g : ExtractionFreeGroup) :
    ∀ᶠ n in atTop,
      extractionFiniteLiftFreq data n
          (QuotientAddGroup.mk g : ExtractionDiscreteGroup data) =
        extractionFiniteLiftHom data n g := by
  exact (extractionQuotient_eq_iff_eventually_lift_eq
    (data := data)
    (g := Quotient.out
      (QuotientAddGroup.mk g : ExtractionDiscreteGroup data))
    (h := g)).mp (Quotient.out_eq _)

/-- Generator finite lifts recover their labelled frequencies eventually. -/
lemma extractionFiniteLiftFreq_generator_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (idx : ExtendedLargeSpectrumIndex) :
    ∀ᶠ n in atTop,
      extractionFiniteLiftFreq data n (extractionGenerator data idx) =
        S.extendedLargeSpectrumIndexFreq (data.φ n) idx := by
  filter_upwards
    [extractionFiniteLiftFreq_mk_eventually_eq
      (data := data) (FreeAbelianGroup.of idx)] with n hn
  simpa [extractionGenerator, extractionFiniteLiftHom_apply_of] using hn

/-- Extraction quotient generators corresponding to the `k`-th dyadic large
spectrum labels. -/
noncomputable def extractionLargeSpectrumGeneratorFinset
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) (k : ℕ) :
    Finset (ExtractionDiscreteGroup data) := by
  classical
  exact (Finset.univ : Finset (LargeSpectrumLabel k)).image
    (fun label => extractionGenerator data (some ⟨k, label⟩))

lemma extractionGenerator_mem_extractionLargeSpectrumGeneratorFinset
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (k : ℕ) (label : LargeSpectrumLabel k) :
    extractionGenerator data (some ⟨k, label⟩) ∈
      extractionLargeSpectrumGeneratorFinset data k := by
  classical
  unfold extractionLargeSpectrumGeneratorFinset
  exact Finset.mem_image.mpr ⟨label, Finset.mem_univ _, rfl⟩

lemma extractionLargeSpectrumGeneratorFinset_eventually_represents_largeSpectrumAt
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (k : ℕ) :
    ∀ᶠ n in atTop,
      ∀ r ∈ S.largeSpectrumAt (data.φ n) k,
        ∃ γ ∈ extractionLargeSpectrumGeneratorFinset data k,
          r = extractionFiniteLiftFreq data n γ := by
  classical
  have hlabels' :
      ∀ᶠ n in atTop, ∀ label ∈ (Finset.univ : Finset (LargeSpectrumLabel k)),
        extractionFiniteLiftFreq data n
            (extractionGenerator data (some ⟨k, label⟩)) =
          S.largeSpectrumLabelFreq (data.φ n) k label := by
    rw [(Finset.univ : Finset (LargeSpectrumLabel k)).eventually_all]
    intro label _hlabel
    exact extractionFiniteLiftFreq_generator_eventually_eq
      (data := data) (some ⟨k, label⟩)
  have hlabels :
      ∀ᶠ n in atTop, ∀ label : LargeSpectrumLabel k,
        extractionFiniteLiftFreq data n
            (extractionGenerator data (some ⟨k, label⟩)) =
          S.largeSpectrumLabelFreq (data.φ n) k label := by
    filter_upwards [hlabels'] with n hn label
    exact hn label (Finset.mem_univ label)
  filter_upwards [hlabels] with n hn r hr
  let label : LargeSpectrumLabel k :=
    S.largeSpectrumAtEmbedding (data.φ n) k ⟨r, hr⟩
  let γ : ExtractionDiscreteGroup data :=
    extractionGenerator data (some ⟨k, label⟩)
  refine ⟨γ, extractionGenerator_mem_extractionLargeSpectrumGeneratorFinset
    (data := data) k label, ?_⟩
  have hfreq :
      S.largeSpectrumLabelFreq (data.φ n) k label = r :=
    S.largeSpectrumLabelFreq_embedding r hr
  exact (hn label).trans hfreq |>.symm

lemma extractionFiniteLiftFreq_zero_eventually_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S} :
    ∀ᶠ n in atTop,
      extractionFiniteLiftFreq data n (0 : ExtractionDiscreteGroup data) = 0 := by
  simpa [extractionFiniteLiftFreq] using
    (extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
      (data := data)
      (g := Quotient.out (0 : ExtractionDiscreteGroup data))).mp
      (Quotient.out_eq (0 : ExtractionDiscreteGroup data))

lemma extractionFiniteLiftFreq_add_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ δ : ExtractionDiscreteGroup data) :
    ∀ᶠ n in atTop,
      extractionFiniteLiftFreq data n (γ + δ) =
        extractionFiniteLiftFreq data n γ + extractionFiniteLiftFreq data n δ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (γ + δ)) :
          ExtractionDiscreteGroup data) =
        QuotientAddGroup.mk (Quotient.out γ + Quotient.out δ) := by
    simp [Quotient.out_eq γ, Quotient.out_eq δ]
  filter_upwards
    [(extractionQuotient_eq_iff_eventually_lift_eq
      (data := data)
      (g := Quotient.out (γ + δ))
      (h := Quotient.out γ + Quotient.out δ)).mp hquot] with n hn
  simp [extractionFiniteLiftFreq, map_add, hn]

lemma extractionFiniteLiftFreq_sub_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ δ : ExtractionDiscreteGroup data) :
    ∀ᶠ n in atTop,
      extractionFiniteLiftFreq data n (γ - δ) =
        extractionFiniteLiftFreq data n γ - extractionFiniteLiftFreq data n δ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (γ - δ)) :
          ExtractionDiscreteGroup data) =
        QuotientAddGroup.mk (Quotient.out γ - Quotient.out δ) := by
    simp [Quotient.out_eq γ, Quotient.out_eq δ]
  filter_upwards
    [(extractionQuotient_eq_iff_eventually_lift_eq
      (data := data)
      (g := Quotient.out (γ - δ))
      (h := Quotient.out γ - Quotient.out δ)).mp hquot] with n hn
  simp [extractionFiniteLiftFreq, map_sub, hn]

lemma extractionFiniteLiftFreq_neg_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) :
    ∀ᶠ n in atTop,
      extractionFiniteLiftFreq data n (-γ) =
        -extractionFiniteLiftFreq data n γ := by
  filter_upwards
    [extractionFiniteLiftFreq_sub_eventually_eq
      (data := data) (0 : ExtractionDiscreteGroup data) γ,
     extractionFiniteLiftFreq_zero_eventually_eq_zero (data := data)] with n hsub hzero
  simpa [sub_eq_add_neg, hzero] using hsub

lemma ExtractionTrigPoly.evalFinite_convMul_single_single_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ δ : ExtractionDiscreteGroup data) (c d : ℂ) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (data.φ n)),
        ExtractionTrigPoly.evalFinite
            (ExtractionTrigPoly.convMul
              (Finsupp.single γ c : ExtractionTrigPoly data)
              (Finsupp.single δ d : ExtractionTrigPoly data)) n x =
          ExtractionTrigPoly.evalFinite
              (Finsupp.single γ c : ExtractionTrigPoly data) n x *
            ExtractionTrigPoly.evalFinite
              (Finsupp.single δ d : ExtractionTrigPoly data) n x := by
  filter_upwards
    [extractionFiniteLiftFreq_add_eventually_eq
      (data := data) γ δ] with n hadd x
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  rw [ExtractionTrigPoly.convMul_single_single]
  rw [ExtractionTrigPoly.evalFinite_single]
  rw [ExtractionTrigPoly.evalFinite_single]
  rw [ExtractionTrigPoly.evalFinite_single]
  rw [hadd]
  have hchar :
      ZMod.stdAddChar (-((extractionFiniteLiftFreq data n γ +
          extractionFiniteLiftFreq data n δ) * x)) =
        ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x)) *
          ZMod.stdAddChar (-(extractionFiniteLiftFreq data n δ * x)) := by
    rw [show -((extractionFiniteLiftFreq data n γ +
          extractionFiniteLiftFreq data n δ) * x) =
        -(extractionFiniteLiftFreq data n γ * x) +
          -(extractionFiniteLiftFreq data n δ * x) by ring]
    rw [ZMod.stdAddChar.map_add_eq_mul]
  rw [hchar]
  ring

lemma avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero
    {p : ℕ} [Fact p.Prime] [NeZero p] {r : ZMod p} (hr : r ≠ 0) :
    avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(r * x))) = 0 := by
  unfold avgZMod
  rw [show (∑ x : ZMod p, ZMod.stdAddChar (-(r * x))) = 0 by
    simpa [mul_comm] using
      sum_stdAddChar_neg_mul_eq_zero_of_ne_zero (p := p) (r := r) hr]
  simp

lemma avgZMod_stdAddChar_neg_mul_eq_ite
    {p : ℕ} [Fact p.Prime] [NeZero p] (r : ZMod p) :
    avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(r * x))) =
      if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · subst r
    unfold avgZMod
    have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
    simp [hp]
  · simp [hr, avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero hr]

lemma avgZMod_const {p : ℕ} [NeZero p] (c : ℂ) :
    avgZMod (fun _ : ZMod p => c) = c := by
  unfold avgZMod
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  simp [hp]

@[simp]
lemma avgZMod_zero {p : ℕ} [NeZero p] :
    avgZMod (fun _ : ZMod p => (0 : ℂ)) = 0 := by
  simpa using avgZMod_const (p := p) (0 : ℂ)

lemma avgZMod_add {p : ℕ} [NeZero p] (f g : ZMod p → ℂ) :
    avgZMod (fun x => f x + g x) = avgZMod f + avgZMod g := by
  unfold avgZMod
  simp [Finset.sum_add_distrib, mul_add]

lemma ExtractionTrigPoly.finiteAverage_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P Q : ExtractionTrigPoly data) (n : ℕ) :
    ExtractionTrigPoly.finiteAverage (P + Q) n =
      ExtractionTrigPoly.finiteAverage P n +
        ExtractionTrigPoly.finiteAverage Q n := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  rw [ExtractionTrigPoly.finiteAverage, ExtractionTrigPoly.finiteAverage,
    ExtractionTrigPoly.finiteAverage]
  have hfun :
      (fun x : ZMod (S.p (data.φ n)) =>
        ExtractionTrigPoly.evalFinite (P + Q) n x) =
      (fun x => ExtractionTrigPoly.evalFinite P n x +
        ExtractionTrigPoly.evalFinite Q n x) := by
    funext x
    unfold ExtractionTrigPoly.evalFinite
    let h : ExtractionDiscreteGroup data → ℂ →+ ℂ := fun γ =>
      { toFun := fun c => c * ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))
        map_zero' := by simp
        map_add' := by intro a b; ring }
    change Finsupp.sum (P + Q) (fun γ c => h γ c) =
      Finsupp.sum P (fun γ c => h γ c) +
        Finsupp.sum Q (fun γ c => h γ c)
    rw [Finsupp.sum_hom_add_index]
  rw [hfun, avgZMod_add]

@[simp]
lemma ExtractionTrigPoly.compactAverage_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S} :
    ExtractionTrigPoly.compactAverage
      (0 : ExtractionTrigPoly data) = 0 := by
  simp [ExtractionTrigPoly.compactAverage]

lemma ExtractionTrigPoly.compactAverage_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P Q : ExtractionTrigPoly data) :
    ExtractionTrigPoly.compactAverage (P + Q) =
      ExtractionTrigPoly.compactAverage P +
        ExtractionTrigPoly.compactAverage Q := by
  simp [ExtractionTrigPoly.compactAverage]

@[simp]
lemma ExtractionTrigPoly.compactAverage_single_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (c : ℂ) :
    ExtractionTrigPoly.compactAverage
        (Finsupp.single (0 : ExtractionDiscreteGroup data) c :
          ExtractionTrigPoly data) = c := by
  simp [ExtractionTrigPoly.compactAverage]

@[simp]
lemma ExtractionTrigPoly.compactAverage_single_ne_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {γ : ExtractionDiscreteGroup data} (hγ : γ ≠ 0) (c : ℂ) :
    ExtractionTrigPoly.compactAverage
        (Finsupp.single γ c : ExtractionTrigPoly data) = 0 := by
  exact Finsupp.single_eq_of_ne (Ne.symm hγ)

lemma ExtractionTrigPoly.finiteAverage_single_eq_coeff_of_lift_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) (c : ℂ) (n : ℕ)
    (hγ : extractionFiniteLiftFreq data n γ = 0) :
    ExtractionTrigPoly.finiteAverage
        (Finsupp.single γ c : ExtractionTrigPoly data) n = c := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  rw [ExtractionTrigPoly.finiteAverage]
  simp [ExtractionTrigPoly.evalFinite_single, hγ, avgZMod_const]

lemma ExtractionTrigPoly.finiteAverage_single_eq_zero_of_lift_ne_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) (c : ℂ) (n : ℕ)
    (hγ : extractionFiniteLiftFreq data n γ ≠ 0) :
    ExtractionTrigPoly.finiteAverage
        (Finsupp.single γ c : ExtractionTrigPoly data) n = 0 := by
  haveI : Fact (S.p (data.φ n)).Prime := ⟨S.prime (data.φ n)⟩
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  rw [ExtractionTrigPoly.finiteAverage]
  simp [ExtractionTrigPoly.evalFinite_single, avgZMod_const_mul,
    avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero hγ]

lemma ExtractionTrigPoly.normalizedDftFunction_evalFinite_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (γ : ExtractionDiscreteGroup data) (c : ℂ) (n : ℕ)
    [Fact (S.p (data.φ n)).Prime] [NeZero (S.p (data.φ n))]
    (r : ZMod (S.p (data.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (data.φ n)) =>
          ExtractionTrigPoly.evalFinite
            (Finsupp.single γ c : ExtractionTrigPoly data) n x) r =
      if r + extractionFiniteLiftFreq data n γ = 0 then c else 0 := by
  rw [normalizedDftFunction_eq_avgZMod]
  simp [ExtractionTrigPoly.evalFinite_single]
  calc
    avgZMod
        (fun x : ZMod (S.p (data.φ n)) =>
          ZMod.stdAddChar (-(x * r)) *
            (c * ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))))
        =
      avgZMod
        (fun x : ZMod (S.p (data.φ n)) =>
          c * ZMod.stdAddChar
            (-((r + extractionFiniteLiftFreq data n γ) * x))) := by
          congr 1
          funext x
          calc
            ZMod.stdAddChar (-(x * r)) *
                (c * ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x)))
                =
              c * (ZMod.stdAddChar (-(x * r)) *
                ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))) := by
                ring
            _ =
              c * ZMod.stdAddChar
                (-((r + extractionFiniteLiftFreq data n γ) * x)) := by
                congr 1
                rw [← ZMod.stdAddChar.map_add_eq_mul]
                congr 1
                ring
    _ =
      c * avgZMod
        (fun x : ZMod (S.p (data.φ n)) =>
          ZMod.stdAddChar
            (-((r + extractionFiniteLiftFreq data n γ) * x))) := by
          rw [avgZMod_const_mul]
    _ = if r + extractionFiniteLiftFreq data n γ = 0 then c else 0 := by
          rw [avgZMod_stdAddChar_neg_mul_eq_ite]
          by_cases h : r + extractionFiniteLiftFreq data n γ = 0 <;> simp [h]

lemma ExtractionTrigPoly.normalizedDftFunction_evalFinite
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) (n : ℕ)
    [Fact (S.p (data.φ n)).Prime] [NeZero (S.p (data.φ n))]
    (r : ZMod (S.p (data.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (data.φ n)) =>
          ExtractionTrigPoly.evalFinite P n x) r =
      P.sum fun γ c =>
        if r + extractionFiniteLiftFreq data n γ = 0 then c else 0 := by
  classical
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [normalizedDftFunction_zero_fun]
  · intro P Q hP hQ
    have hfun :
      (fun x : ZMod (S.p (data.φ n)) =>
          ExtractionTrigPoly.evalFinite (P + Q) n x) =
        fun x =>
          ExtractionTrigPoly.evalFinite P n x +
            ExtractionTrigPoly.evalFinite Q n x := by
      funext x
      exact ExtractionTrigPoly.evalFinite_add P Q n x
    rw [hfun]
    rw [normalizedDftFunction_add, hP, hQ]
    let h : ExtractionDiscreteGroup data → ℂ →+ ℂ := fun γ =>
      { toFun := fun c => if r + extractionFiniteLiftFreq data n γ = 0 then c else 0
        map_zero' := by by_cases hγ : r + extractionFiniteLiftFreq data n γ = 0 <;> simp [hγ]
        map_add' := by
          intro a b
          by_cases hγ : r + extractionFiniteLiftFreq data n γ = 0 <;> simp [hγ] }
    change Finsupp.sum P (fun γ c => h γ c) +
        Finsupp.sum Q (fun γ c => h γ c) =
      Finsupp.sum (P + Q) (fun γ c => h γ c)
    rw [Finsupp.sum_hom_add_index]
  · intro γ c
    simpa using
      ExtractionTrigPoly.normalizedDftFunction_evalFinite_single
        (data := data) γ c n r

lemma ExtractionTrigPoly.sum_if_neg_lift_add_eq_zero_eq_apply_of_injOn
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (P : ExtractionTrigPoly data) (n : ℕ)
    (γ : ExtractionDiscreteGroup data)
    (hinj :
      Set.InjOn
        (fun δ : ExtractionDiscreteGroup data =>
          extractionFiniteLiftFreq data n δ)
        {δ : ExtractionDiscreteGroup data | δ ∈ insert γ P.support}) :
    P.sum (fun δ c =>
        if -extractionFiniteLiftFreq data n γ +
            extractionFiniteLiftFreq data n δ = 0
        then c else 0) =
      P γ := by
  classical
  unfold Finsupp.sum
  rw [Finset.sum_eq_single γ]
  · simp
  · intro δ hδ hδγ
    have hnot :
        ¬ (-extractionFiniteLiftFreq data n γ +
            extractionFiniteLiftFreq data n δ = 0) := by
      intro hzero
      have heq : extractionFiniteLiftFreq data n δ =
          extractionFiniteLiftFreq data n γ := by
        have h := congrArg
          (fun z : ZMod (S.p (data.φ n)) =>
            z + extractionFiniteLiftFreq data n γ) hzero
        simpa [add_comm, add_left_comm, add_assoc] using h
      exact hδγ (hinj
        (Finset.mem_insert.mpr (Or.inr hδ))
        (Finset.mem_insert_self γ P.support)
        heq)
    simp [hnot]
  · intro hγ
    have hpγ : P γ = 0 := Finsupp.notMem_support_iff.mp hγ
    simp [hpγ]

lemma ExtractionTrigPoly.finiteAverage_single_zero_eventually_eq_coeff
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (c : ℂ) :
    ∀ᶠ n in atTop,
      ExtractionTrigPoly.finiteAverage
          (Finsupp.single (0 : ExtractionDiscreteGroup data) c :
            ExtractionTrigPoly data) n = c := by
  filter_upwards [extractionFiniteLiftFreq_zero_eventually_eq_zero
    (data := data)] with n hn
  exact ExtractionTrigPoly.finiteAverage_single_eq_coeff_of_lift_eq_zero
    (0 : ExtractionDiscreteGroup data) c n hn

lemma ExtractionTrigPoly.finiteAverage_single_none_eventually_eq_coeff
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (c : ℂ) :
    ∀ᶠ n in atTop,
      ExtractionTrigPoly.finiteAverage
          (Finsupp.single (extractionGenerator data none) c :
            ExtractionTrigPoly data) n = c := by
  simpa [extractionGenerator_none_eq_zero] using
    ExtractionTrigPoly.finiteAverage_single_zero_eventually_eq_coeff
      (data := data) c

lemma StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteLiftFreq_eventually_ne_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    {γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData}
    (hγ : γ ≠ 0) :
    ∀ᶠ n in atTop,
      extractionFiniteLiftFreq data.toExtendedLargeSpectrumCoeffLimitData n γ ≠ 0 := by
  rcases data.finiteLift_eventually_stable (Quotient.out γ) with hzero | hnonzero
  · have hγ0 : γ = 0 := by
      have hmk :
          (QuotientAddGroup.mk (Quotient.out γ) :
              ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) = 0 :=
        (extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
          (data := data.toExtendedLargeSpectrumCoeffLimitData)).mpr hzero
      simpa [Quotient.out_eq γ] using hmk
    exact (hγ hγ0).elim
  · simpa [extractionFiniteLiftFreq] using hnonzero

lemma StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteLiftFreq_eventually_injOn_finset
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) :
    ∀ᶠ n in atTop,
      Set.InjOn
        (fun γ =>
          extractionFiniteLiftFreq data.toExtendedLargeSpectrumCoeffLimitData n γ)
        (Q : Set (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) := by
  classical
  have hpairs :
      ∀ᶠ n in atTop, ∀ pair ∈ Q.product Q,
        pair.1 ≠ pair.2 →
          extractionFiniteLiftFreq data.toExtendedLargeSpectrumCoeffLimitData n pair.1 ≠
            extractionFiniteLiftFreq data.toExtendedLargeSpectrumCoeffLimitData n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair hmem
    by_cases hp : pair.1 = pair.2
    · exact Eventually.of_forall fun _ hne => (hne hp).elim
    · have hsub_ne : pair.1 - pair.2 ≠
          (0 : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :=
        sub_ne_zero.mpr hp
      filter_upwards
        [data.extractionFiniteLiftFreq_eventually_ne_zero hsub_ne,
          extractionFiniteLiftFreq_sub_eventually_eq
            (data := data.toExtendedLargeSpectrumCoeffLimitData) pair.1 pair.2] with n hne hsub _hp hfreq
      exact hne (by rw [hsub, hfreq, sub_self])
  filter_upwards [hpairs] with n hn
  intro γ hγ δ hδ heq
  by_contra hne
  exact hn (γ, δ) (Finset.mem_product.mpr ⟨hγ, hδ⟩) hne heq

lemma StableExtendedLargeSpectrumCoeffLimitData.finiteAverage_single_eq_zero_eventually_of_ne_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    {γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData}
    (hγ : γ ≠ 0) (c : ℂ) :
    ∀ᶠ n in atTop,
      ExtractionTrigPoly.finiteAverage
          (Finsupp.single γ c :
            ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) n = 0 := by
  filter_upwards [data.extractionFiniteLiftFreq_eventually_ne_zero hγ] with n hn
  exact ExtractionTrigPoly.finiteAverage_single_eq_zero_of_lift_ne_zero γ c n hn

/-- Along a relation-stable extraction subsequence, the finite average of any
lifted trigonometric polynomial is eventually its zero-frequency coefficient. -/
lemma StableExtendedLargeSpectrumCoeffLimitData.finiteAverage_eventually_eq_zeroCoeff
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    ∀ᶠ n in atTop,
      ExtractionTrigPoly.finiteAverage P n =
        P (0 : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [ExtractionTrigPoly.finiteAverage]
  · intro P Q hP hQ
    filter_upwards [hP, hQ] with n hp hq
    rw [ExtractionTrigPoly.finiteAverage_add, hp, hq]
    rfl
  · intro γ c
    by_cases hγ : γ = 0
    · subst hγ
      simpa [Finsupp.single_eq_same] using
        ExtractionTrigPoly.finiteAverage_single_zero_eventually_eq_coeff
          (data := data.toExtendedLargeSpectrumCoeffLimitData) c
    · filter_upwards [data.finiteAverage_single_eq_zero_eventually_of_ne_zero hγ c] with n hn
      rw [hn]
      exact (Finsupp.single_eq_of_ne (Ne.symm hγ) :
        (Finsupp.single γ c :
          ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData)
            (0 : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) = 0).symm

/-- Along a relation-stable extraction subsequence, finite averages of lifted
trigonometric polynomials converge to the zero-frequency coefficient. -/
lemma StableExtendedLargeSpectrumCoeffLimitData.finiteAverage_tendsto_zeroCoeff
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto (fun n =>
      ExtractionTrigPoly.finiteAverage P n) atTop
        (𝓝 (P (0 :
          ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))) := by
  have h :
      (fun _ : ℕ =>
        P (0 : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) =ᶠ[atTop]
        fun n => ExtractionTrigPoly.finiteAverage P n := by
    filter_upwards [data.finiteAverage_eventually_eq_zeroCoeff P] with n hn
    exact hn.symm
  exact tendsto_const_nhds.congr' h

/-- Relation-stable finite averages converge to the abstract compact average
of the extraction trigonometric polynomial. -/
lemma StableExtendedLargeSpectrumCoeffLimitData.finiteAverage_tendsto_compactAverage
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto (fun n =>
      ExtractionTrigPoly.finiteAverage P n) atTop
        (𝓝 (ExtractionTrigPoly.compactAverage P)) := by
  simpa [ExtractionTrigPoly.compactAverage] using
    data.finiteAverage_tendsto_zeroCoeff P

lemma StableExtractionCoeffLimitData.forbiddenCoeffFunctional_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P Q : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    data.forbiddenCoeffFunctional (P + Q) =
      data.forbiddenCoeffFunctional P + data.forbiddenCoeffFunctional Q := by
  unfold StableExtractionCoeffLimitData.forbiddenCoeffFunctional
  let h :
      ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData →
        ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * data.fCoeffQ γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma StableExtractionCoeffLimitData.vertexCoeffFunctional_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P Q : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    data.vertexCoeffFunctional (P + Q) =
      data.vertexCoeffFunctional P + data.vertexCoeffFunctional Q := by
  unfold StableExtractionCoeffLimitData.vertexCoeffFunctional
  let h :
      ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData →
        ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * data.uCoeffQ γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

@[simp]
lemma StableExtractionCoeffLimitData.forbiddenCoeffFunctional_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S) :
    data.forbiddenCoeffFunctional
      (0 : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) = 0 := by
  simp [StableExtractionCoeffLimitData.forbiddenCoeffFunctional]

@[simp]
lemma StableExtractionCoeffLimitData.vertexCoeffFunctional_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S) :
    data.vertexCoeffFunctional
      (0 : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) = 0 := by
  simp [StableExtractionCoeffLimitData.vertexCoeffFunctional]

lemma StableExtractionCoeffLimitData.forbiddenCoeffFunctional_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)
    (c : ℂ) :
    data.forbiddenCoeffFunctional
        (Finsupp.single γ c :
          ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) =
      c * data.fCoeffQ γ := by
  simp [StableExtractionCoeffLimitData.forbiddenCoeffFunctional]

lemma StableExtractionCoeffLimitData.vertexCoeffFunctional_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)
    (c : ℂ) :
    data.vertexCoeffFunctional
        (Finsupp.single γ c :
          ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) =
      c * data.uCoeffQ γ := by
  simp [StableExtractionCoeffLimitData.vertexCoeffFunctional]

lemma StableExtractionCoeffLimitData.forbiddenWeightedFiniteAverage_tendsto_coeffFunctional
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto
      (fun n => ExtractionTrigPoly.forbiddenWeightedFiniteAverage data P n)
      atTop (𝓝 (data.forbiddenCoeffFunctional P)) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [ExtractionTrigPoly.forbiddenWeightedFiniteAverage,
      StableExtractionCoeffLimitData.forbiddenCoeffFunctional]
  · intro P Q hP hQ
    rw [data.forbiddenCoeffFunctional_add P Q]
    exact (hP.add hQ).congr' (Filter.Eventually.of_forall fun n => by
      exact (ExtractionTrigPoly.forbiddenWeightedFiniteAverage_add
        data P Q n).symm)
  · intro γ c
    rw [data.forbiddenCoeffFunctional_single γ c]
    have hcoeff := data.fCoeffQ_tendsto γ
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have hmul := hc.mul hcoeff
    exact hmul.congr' (Filter.Eventually.of_forall fun n => by
      exact (ExtractionTrigPoly.forbiddenWeightedFiniteAverage_single
        data γ c n).symm)

lemma StableExtractionCoeffLimitData.vertexWeightedFiniteAverage_tendsto_coeffFunctional
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto
      (fun n => ExtractionTrigPoly.vertexWeightedFiniteAverage data P n)
      atTop (𝓝 (data.vertexCoeffFunctional P)) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [ExtractionTrigPoly.vertexWeightedFiniteAverage,
      StableExtractionCoeffLimitData.vertexCoeffFunctional]
  · intro P Q hP hQ
    rw [data.vertexCoeffFunctional_add P Q]
    exact (hP.add hQ).congr' (Filter.Eventually.of_forall fun n => by
      exact (ExtractionTrigPoly.vertexWeightedFiniteAverage_add
        data P Q n).symm)
  · intro γ c
    rw [data.vertexCoeffFunctional_single γ c]
    have hcoeff := data.uCoeffQ_tendsto γ
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have hmul := hc.mul hcoeff
    exact hmul.congr' (Filter.Eventually.of_forall fun n => by
      exact (ExtractionTrigPoly.vertexWeightedFiniteAverage_single
        data γ c n).symm)

end

end Erdos42.FourierPositive
