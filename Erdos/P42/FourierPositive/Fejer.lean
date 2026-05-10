/-
Erdos Problem 42 — Route A Fejer kernels on the extraction model.

This file introduces the compact-dual and finite-cyclic Fejer kernels attached
to a finite frequency set in the extraction quotient.  These kernels are the
named smoothing objects used later in the weighted counting-convergence proof.
-/

import Erdos.P42.FourierPositive.TrigPolynomial

namespace Erdos42.FourierPositive

open Filter Complex
open scoped BigOperators Classical ComplexConjugate Topology

noncomputable section

/-- Compact-dual Fejer kernel associated to a finite frequency set. -/
noncomputable def extractionCompactFejerKernel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (z : ExtractionCompactDual data) : ℂ :=
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q, extractionCharacterValue z γ) *
      star (∑ γ ∈ Q, extractionCharacterValue z γ))

/-- Compact-dual Fejer kernel on the additive wrapper used by Route A's
continuous compact model. -/
noncomputable def extractionCompactAddFejerKernel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (z : ExtractionCompactAddDual data) : ℂ :=
  extractionCompactFejerKernel Q z.toMul

/-- Finite cyclic lift of the Fejer kernel associated to a finite frequency
set in the extraction quotient. -/
noncomputable def extractionFiniteFejerKernel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    (x : ZMod (S.p (data.φ n))) : ℂ :=
  letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q, ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))) *
      star (∑ γ ∈ Q, ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))))

/-- Normalized finite average of the finite cyclic Fejer kernel. -/
noncomputable def extractionFiniteFejerKernelAverage
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (data.φ n)) =>
    extractionFiniteFejerKernel Q n x

/-- Finite Fejer-smoothed forbidden kernel
`1_{F_n} * K_{n,Q}`, using normalized convolution on `ZMod p`. -/
noncomputable def extractionFiniteSmoothedForbiddenKernel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ) :
    ZMod (S.p (data.φ n)) → ℂ :=
  letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  avgConvolution (indicatorC (S.F (data.φ n)))
    (extractionFiniteFejerKernel Q n)

/-- One Fourier mode appearing in a Fejer kernel expansion. -/
noncomputable def extractionFejerTerm
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (pair : ExtractionDiscreteGroup data × ExtractionDiscreteGroup data) :
    ExtractionTrigPoly data :=
  Finsupp.single (pair.1 - pair.2) ((Q.card : ℂ)⁻¹)

/-- The Fejer kernel as a trigonometric polynomial on the extraction compact
dual. -/
noncomputable def extractionFejerTrigPoly
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) :
    ExtractionTrigPoly data :=
  ∑ pair ∈ Q.product Q, extractionFejerTerm Q pair

@[simp]
lemma extractionCompactFejerKernel_empty
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactDual data) :
    extractionCompactFejerKernel (∅ : Finset (ExtractionDiscreteGroup data)) z = 0 := by
  simp [extractionCompactFejerKernel]

@[simp]
lemma extractionCompactAddFejerKernel_empty
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (z : ExtractionCompactAddDual data) :
    extractionCompactAddFejerKernel
        (∅ : Finset (ExtractionDiscreteGroup data)) z = 0 := by
  simp [extractionCompactAddFejerKernel]

@[simp]
lemma extractionFiniteFejerKernel_empty
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (n : ℕ) (x : ZMod (S.p (data.φ n))) :
    extractionFiniteFejerKernel (∅ : Finset (ExtractionDiscreteGroup data)) n x = 0 := by
  simp [extractionFiniteFejerKernel]

@[simp]
lemma extractionFejerTrigPoly_empty
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S} :
    extractionFejerTrigPoly
        (∅ : Finset (ExtractionDiscreteGroup data)) =
      (0 : ExtractionTrigPoly data) := by
  simp [extractionFejerTrigPoly]

lemma extractionFejerTerm_eval
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (pair : ExtractionDiscreteGroup data × ExtractionDiscreteGroup data)
    (z : ExtractionCompactDual data) :
    ExtractionTrigPoly.eval (extractionFejerTerm Q pair) z =
      (Q.card : ℂ)⁻¹ * extractionCharacterValue z (pair.1 - pair.2) := by
  simp [extractionFejerTerm]

lemma extractionFejerTerm_evalFinite
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (pair : ExtractionDiscreteGroup data × ExtractionDiscreteGroup data)
    (n : ℕ) [NeZero (S.p (data.φ n))]
    (x : ZMod (S.p (data.φ n))) :
    ExtractionTrigPoly.evalFinite (extractionFejerTerm Q pair) n x =
      (Q.card : ℂ)⁻¹ *
        ZMod.stdAddChar
          (-(extractionFiniteLiftFreq data n (pair.1 - pair.2) * x)) := by
  simp [extractionFejerTerm, ExtractionTrigPoly.evalFinite]

lemma stdAddChar_sub_fejer
    {p : ℕ} [NeZero p] (r s x : ZMod p) :
    ZMod.stdAddChar (-((r - s) * x)) =
      ZMod.stdAddChar (-(r * x)) *
        star (ZMod.stdAddChar (-(s * x))) := by
  have hstar : star (ZMod.stdAddChar (-(s * x))) =
      ZMod.stdAddChar (s * x) := by
    have h := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (s * x)
    simp [h]
  rw [hstar]
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

lemma sum_product_const_mul_star
    {ι : Type*} (Q : Finset ι) (a : ι → ℂ) (c : ℂ) :
  (∑ x ∈ Q.product Q, c * (a x.1 * star (a x.2))) =
      c * ((∑ x ∈ Q, a x) * star (∑ y ∈ Q, a y)) := by
  have hstar : star (∑ y ∈ Q, a y) = ∑ y ∈ Q, star (a y) := by
    simp
  rw [hstar]
  change (∑ x ∈ Q ×ˢ Q, c * (a x.1 * star (a x.2))) =
    c * ((∑ x ∈ Q, a x) * ∑ y ∈ Q, star (a y))
  rw [Finset.sum_product]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [← Finset.mul_sum]

lemma extractionFejerTrigPoly_eval
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (z : ExtractionCompactDual data) :
    ExtractionTrigPoly.eval (extractionFejerTrigPoly Q) z =
      extractionCompactFejerKernel Q z := by
  unfold extractionFejerTrigPoly
  let ev : ExtractionTrigPoly data →+ ℂ :=
    { toFun := fun P => ExtractionTrigPoly.eval P z
      map_zero' := by simp
      map_add' := by intro P R; exact ExtractionTrigPoly.eval_add P R z }
  change ev (∑ pair ∈ Q.product Q, extractionFejerTerm Q pair) =
    extractionCompactFejerKernel Q z
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        ExtractionTrigPoly.eval (extractionFejerTerm Q pair) z) =
      extractionCompactFejerKernel Q z
  simp_rw [extractionFejerTerm_eval, extractionCharacterValue_sub]
  unfold extractionCompactFejerKernel
  exact sum_product_const_mul_star Q
    (fun γ => extractionCharacterValue z γ) ((Q.card : ℂ)⁻¹)

lemma extractionFejerTrigPoly_evalAdd
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (z : ExtractionCompactAddDual data) :
    ExtractionTrigPoly.evalAdd (extractionFejerTrigPoly Q) z =
      extractionCompactAddFejerKernel Q z := by
  simpa [ExtractionTrigPoly.evalAdd_eq_eval, extractionCompactAddFejerKernel] using
    extractionFejerTrigPoly_eval Q z.toMul

lemma extractionFejerTrigPoly_compactAverage_eq_one_of_nonempty
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (hQ : Q ≠ ∅) :
    ExtractionTrigPoly.compactAverage (extractionFejerTrigPoly Q) = 1 := by
  classical
  have hcard_ne : (Q.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr
      (Finset.nonempty_iff_ne_empty.mpr hQ))
  unfold ExtractionTrigPoly.compactAverage extractionFejerTrigPoly extractionFejerTerm
  rw [Finsupp.finset_sum_apply]
  change (∑ i ∈ Q ×ˢ Q,
    (Finsupp.single (i.1 - i.2) ((Q.card : ℂ)⁻¹) :
      ExtractionTrigPoly data)
      (0 : ExtractionDiscreteGroup data)) = 1
  rw [Finset.sum_product]
  simp [Finsupp.single_apply, sub_eq_zero, hcard_ne]

lemma extractionFejerTrigPoly_apply_sum
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (γ : ExtractionDiscreteGroup data) :
    (extractionFejerTrigPoly Q) γ =
      ∑ pair ∈ Q.product Q,
        if pair.1 - pair.2 = γ then (Q.card : ℂ)⁻¹ else 0 := by
  unfold extractionFejerTrigPoly extractionFejerTerm
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

lemma extractionFejerTrigPoly_apply_filter_card
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (γ : ExtractionDiscreteGroup data) :
    (extractionFejerTrigPoly Q) γ =
      (((Q.product Q).filter (fun pair => pair.1 - pair.2 = γ)).card : ℂ) *
        (Q.card : ℂ)⁻¹ := by
  rw [extractionFejerTrigPoly_apply_sum]
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- Abstract finite-frequency Fejer coefficient bound.  Later Følner-box
choices will prove this for the finite large-spectrum set; keeping it as a
local predicate avoids baking the Følner construction into the counting layer. -/
def ExtractionFejerCoeffBound
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q B : Finset (ExtractionDiscreteGroup data)) (M : ℝ) : Prop :=
  ∀ γ ∈ B, ‖1 - (extractionFejerTrigPoly Q) γ‖ ≤ M

/-- Concrete pair-count version of the Fejer coefficient bound.  For a finite
frequency set `Q`, the coefficient at `γ` is the normalized number of pairs
`(q₁,q₂) ∈ Q × Q` with `q₁ - q₂ = γ`. -/
def ExtractionFejerPairCoeffBound
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q B : Finset (ExtractionDiscreteGroup data)) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    ‖1 -
      ((((Q.product Q).filter (fun pair => pair.1 - pair.2 = γ)).card : ℂ) *
        (Q.card : ℂ)⁻¹)‖ ≤ M

/-- Real-ratio version of the pair-count Fejer coefficient bound.  This is the
shape produced by Følner overlap estimates. -/
def ExtractionFejerPairCoeffRealBound
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q B : Finset (ExtractionDiscreteGroup data)) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    |1 -
      (((Q.product Q).filter (fun pair => pair.1 - pair.2 = γ)).card : ℝ) /
        (Q.card : ℝ)| ≤ M

/-- Fejer coefficient bound on the negatives of a finite set of frequencies.
This is the form used for positive finite lifts because the DFT formula for the
finite Fejer kernel recovers the compact coefficient at the negative
frequency. -/
def ExtractionFejerNegCoeffBound
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q B : Finset (ExtractionDiscreteGroup data)) (M : ℝ) : Prop :=
  ∀ γ ∈ B, ‖1 - (extractionFejerTrigPoly Q) (-γ)‖ ≤ M

lemma extractionFejerCoeffBound_of_pairCoeffBound
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {Q B : Finset (ExtractionDiscreteGroup data)} {M : ℝ}
    (hM : ExtractionFejerPairCoeffBound Q B M) :
    ExtractionFejerCoeffBound Q B M := by
  intro γ hγ
  rw [extractionFejerTrigPoly_apply_filter_card]
  exact hM γ hγ

lemma extractionFejerPairCoeffBound_of_realBound
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {Q B : Finset (ExtractionDiscreteGroup data)} {M : ℝ}
    (hM : ExtractionFejerPairCoeffRealBound Q B M) :
    ExtractionFejerPairCoeffBound Q B M := by
  intro γ hγ
  let fiber :=
    (Q.product Q).filter (fun pair : ExtractionDiscreteGroup data ×
      ExtractionDiscreteGroup data => pair.1 - pair.2 = γ)
  have hcast :
      ((fiber.card : ℂ) * (Q.card : ℂ)⁻¹) =
        (((fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    have hfiber : (fiber.card : ℂ) = ((fiber.card : ℝ) : ℂ) := by
      norm_num
    have hQ : (Q.card : ℂ) = ((Q.card : ℝ) : ℂ) := by
      norm_num
    rw [hfiber, hQ, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rw [hcast]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  change ‖(((1 : ℝ) -
      (fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ)‖ ≤ M
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hM γ hγ

lemma extractionFejerCoeffBound_of_pairCoeffRealBound
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {Q B : Finset (ExtractionDiscreteGroup data)} {M : ℝ}
    (hM : ExtractionFejerPairCoeffRealBound Q B M) :
    ExtractionFejerCoeffBound Q B M :=
  extractionFejerCoeffBound_of_pairCoeffBound
    (extractionFejerPairCoeffBound_of_realBound hM)

lemma extractionFejerNegCoeffBound_of_coeffBound_neg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {Q B : Finset (ExtractionDiscreteGroup data)} {M : ℝ}
    (hM : ExtractionFejerCoeffBound Q (B.image Neg.neg) M) :
    ExtractionFejerNegCoeffBound Q B M := by
  intro γ hγ
  exact hM (-γ) (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)

lemma extractionFejerNegCoeffBound_of_pairCoeffRealBound_neg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {Q B : Finset (ExtractionDiscreteGroup data)} {M : ℝ}
    (hM : ExtractionFejerPairCoeffRealBound Q (B.image Neg.neg) M) :
    ExtractionFejerNegCoeffBound Q B M :=
  extractionFejerNegCoeffBound_of_coeffBound_neg
    (extractionFejerCoeffBound_of_pairCoeffRealBound hM)

lemma extractionFejerPairFilter_card_le
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (γ : ExtractionDiscreteGroup data) :
    ((Q.product Q).filter (fun pair => pair.1 - pair.2 = γ)).card ≤
      Q.card := by
  classical
  let fiber :=
    (Q.product Q).filter (fun pair : ExtractionDiscreteGroup data ×
      ExtractionDiscreteGroup data => pair.1 - pair.2 = γ)
  have hmaps : ∀ pair ∈ fiber, pair.1 ∈ Q := by
    intro pair hpair
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).1
  have hinj : (fiber : Set (ExtractionDiscreteGroup data ×
      ExtractionDiscreteGroup data)).InjOn (fun pair => pair.1) := by
    intro pair hpair pair' hpair' hfirst
    have hdiff : pair.1 - pair.2 = γ :=
      (Finset.mem_filter.mp hpair).2
    have hdiff' : pair'.1 - pair'.2 = γ :=
      (Finset.mem_filter.mp hpair').2
    have hsub : pair.1 - pair.2 = pair.1 - pair'.2 := by
      simpa [hfirst] using hdiff.trans hdiff'.symm
    have hsecond : pair.2 = pair'.2 := by
      simpa [sub_eq_sub_iff_add_eq_add] using hsub
    exact Prod.ext hfirst hsecond
  simpa [fiber] using
    Finset.card_le_card_of_injOn (fun pair : ExtractionDiscreteGroup data ×
      ExtractionDiscreteGroup data => pair.1) hmaps hinj

lemma StableExtendedLargeSpectrumCoeffLimitData.extractionFejerTrigPoly_evalFinite_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)),
        ExtractionTrigPoly.evalFinite
            (extractionFejerTrigPoly Q) n x =
          extractionFiniteFejerKernel Q n x := by
  classical
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  have hpairs :
      ∀ᶠ n in atTop,
        ∀ pair ∈ Q.product Q,
          extractionFiniteLiftFreq d n (pair.1 - pair.2) =
            extractionFiniteLiftFreq d n pair.1 -
              extractionFiniteLiftFreq d n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hpair
    exact extractionFiniteLiftFreq_sub_eventually_eq
      (data := d) pair.1 pair.2
  filter_upwards [hpairs] with n hn x
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  unfold extractionFejerTrigPoly
  let ev : ExtractionTrigPoly d →+ ℂ :=
    { toFun := fun P => ExtractionTrigPoly.evalFinite P n x
      map_zero' := by simp
      map_add' := by
        intro P R
        rw [ExtractionTrigPoly.evalFinite]
        rw [ExtractionTrigPoly.evalFinite]
        rw [ExtractionTrigPoly.evalFinite]
        let h : ExtractionDiscreteGroup d → ℂ →+ ℂ := fun γ =>
          { toFun := fun c =>
              c * ZMod.stdAddChar (-(extractionFiniteLiftFreq d n γ * x))
            map_zero' := by simp
            map_add' := by intro a b; ring }
        change Finsupp.sum (P + R) (fun γ c => h γ c) =
          Finsupp.sum P (fun γ c => h γ c) +
            Finsupp.sum R (fun γ c => h γ c)
        rw [Finsupp.sum_hom_add_index] }
  change ev (∑ pair ∈ Q.product Q, extractionFejerTerm Q pair) =
    extractionFiniteFejerKernel Q n x
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        ExtractionTrigPoly.evalFinite (extractionFejerTerm Q pair) n x) =
      extractionFiniteFejerKernel Q n x
  simp_rw [extractionFejerTerm_evalFinite]
  calc
    (∑ pair ∈ Q.product Q,
        (Q.card : ℂ)⁻¹ *
          ZMod.stdAddChar
            (-(extractionFiniteLiftFreq d n (pair.1 - pair.2) * x))) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            (ZMod.stdAddChar (-(extractionFiniteLiftFreq d n pair.1 * x)) *
              star (ZMod.stdAddChar
                (-(extractionFiniteLiftFreq d n pair.2 * x)))) := by
      refine Finset.sum_congr rfl ?_
      intro pair hpair
      rw [hn pair hpair]
      rw [stdAddChar_sub_fejer]
    _ = extractionFiniteFejerKernel Q n x := by
      unfold extractionFiniteFejerKernel
      exact sum_product_const_mul_star Q
        (fun γ => ZMod.stdAddChar (-(extractionFiniteLiftFreq d n γ * x)))
        ((Q.card : ℂ)⁻¹)

lemma StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteFejerKernelAverage_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) :
    ∀ᶠ n in atTop,
      extractionFiniteFejerKernelAverage Q n =
        ExtractionTrigPoly.finiteAverage (extractionFejerTrigPoly Q) n := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  filter_upwards
    [data.extractionFejerTrigPoly_evalFinite_eventually_eq Q] with n hn
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  unfold extractionFiniteFejerKernelAverage ExtractionTrigPoly.finiteAverage
  apply congrArg (fun f : ZMod (S.p (d.φ n)) → ℂ => avgZMod f)
  funext x
  exact (hn x).symm

lemma StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteFejerKernelAverage_tendsto_compactAverage
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) :
    Tendsto (fun n =>
      extractionFiniteFejerKernelAverage Q n) atTop
        (𝓝 (ExtractionTrigPoly.compactAverage (extractionFejerTrigPoly Q))) := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  have h :
      (fun n => ExtractionTrigPoly.finiteAverage
        (extractionFejerTrigPoly Q) n) =ᶠ[atTop]
        fun n => extractionFiniteFejerKernelAverage Q n := by
    filter_upwards
      [data.extractionFiniteFejerKernelAverage_eventually_eq Q] with n hn
    exact hn.symm
  exact (data.finiteAverage_tendsto_compactAverage
    (extractionFejerTrigPoly Q)).congr' h

lemma StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteFejerKernelAverage_tendsto_one
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (hQ : Q ≠ ∅) :
    Tendsto (fun n =>
      extractionFiniteFejerKernelAverage Q n) atTop (𝓝 (1 : ℂ)) := by
  simpa [extractionFejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ] using
    data.extractionFiniteFejerKernelAverage_tendsto_compactAverage Q

lemma StableExtendedLargeSpectrumCoeffLimitData.normalizedDftFunction_extractionFiniteFejerKernel_eventually_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)),
        (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          normalizedDftFunction (extractionFiniteFejerKernel Q n) r) =
          (extractionFejerTrigPoly Q).sum fun γ c =>
            if r + extractionFiniteLiftFreq
                data.toExtendedLargeSpectrumCoeffLimitData n γ = 0
            then c else 0 := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  filter_upwards
    [data.extractionFejerTrigPoly_evalFinite_eventually_eq Q] with n hn r
  haveI : Fact (S.p (d.φ n)).Prime := ⟨S.prime (d.φ n)⟩
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  have hfun :
      extractionFiniteFejerKernel Q n =
        fun x : ZMod (S.p (d.φ n)) =>
          ExtractionTrigPoly.evalFinite (extractionFejerTrigPoly Q) n x := by
    funext x
    exact (hn x).symm
  rw [hfun]
  exact ExtractionTrigPoly.normalizedDftFunction_evalFinite
    (data := d) (extractionFejerTrigPoly Q) n r

lemma StableExtendedLargeSpectrumCoeffLimitData.normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_eq_coeff
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
        ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        normalizedDftFunction (extractionFiniteFejerKernel Q n)
          (-extractionFiniteLiftFreq
            data.toExtendedLargeSpectrumCoeffLimitData n γ)) =
        (extractionFejerTrigPoly Q) γ := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  let P : ExtractionTrigPoly d := extractionFejerTrigPoly Q
  filter_upwards
    [data.normalizedDftFunction_extractionFiniteFejerKernel_eventually_eq Q,
      data.extractionFiniteLiftFreq_eventually_injOn_finset
        (insert γ P.support)] with n hfourier hinj
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  rw [hfourier (-extractionFiniteLiftFreq d n γ)]
  exact ExtractionTrigPoly.sum_if_neg_lift_add_eq_zero_eq_apply_of_injOn
    (data := d) P n γ hinj

lemma StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_le
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)
    {M : ℝ}
    (hM : ‖1 - (extractionFejerTrigPoly Q) γ‖ ≤ M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
        ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n)
          (-extractionFiniteLiftFreq
            data.toExtendedLargeSpectrumCoeffLimitData n γ)‖) ≤ M := by
  filter_upwards
    [data.normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_eq_coeff
      Q γ] with n hn
  rw [hn]
  exact hM

lemma StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_le
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)
    {M : ℝ}
    (hM : ‖1 - (extractionFejerTrigPoly Q) (-γ)‖ ≤ M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
        ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n)
          (extractionFiniteLiftFreq
            data.toExtendedLargeSpectrumCoeffLimitData n γ)‖) ≤ M := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  filter_upwards
    [data.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_le
      Q (-γ) hM,
     extractionFiniteLiftFreq_neg_eventually_eq (data := d) γ] with n hbound hneg
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  have hfreq :
      -extractionFiniteLiftFreq d n (-γ) =
        extractionFiniteLiftFreq d n γ := by
    rw [hneg]
    simp
  change ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n)
      (extractionFiniteLiftFreq d n γ)‖ ≤ M
  rw [← hfreq]
  exact hbound

lemma StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_le_on_finset
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q B : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    {M : ℝ}
    (hM : ExtractionFejerCoeffBound Q B M) :
    ∀ᶠ n in atTop,
      ∀ γ ∈ B,
        (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n)
            (-extractionFiniteLiftFreq
              data.toExtendedLargeSpectrumCoeffLimitData n γ)‖) ≤ M := by
  rw [B.eventually_all]
  intro γ hγ
  exact
    data.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_le
      Q γ (hM γ hγ)

lemma StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_le_on_finset
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q B : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    {M : ℝ}
    (hM : ExtractionFejerNegCoeffBound Q B M) :
    ∀ᶠ n in atTop,
      ∀ γ ∈ B,
        (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n)
            (extractionFiniteLiftFreq
              data.toExtendedLargeSpectrumCoeffLimitData n γ)‖) ≤ M := by
  rw [B.eventually_all]
  intro γ hγ
  exact
    data.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_le
      Q γ (hM γ hγ)

lemma StableExtendedLargeSpectrumCoeffLimitData.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_on_largeSpectrumAt_eventually_le
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (k : ℕ) {M : ℝ}
    (hM : ExtractionFejerNegCoeffBound Q
      (extractionLargeSpectrumGeneratorFinset
        data.toExtendedLargeSpectrumCoeffLimitData k) M) :
    ∀ᶠ n in atTop,
      ∀ r ∈ S.largeSpectrumAt
          (data.toExtendedLargeSpectrumCoeffLimitData.φ n) k,
        (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖) ≤ M := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  filter_upwards
    [extractionLargeSpectrumGeneratorFinset_eventually_represents_largeSpectrumAt
      (data := d) k,
     data.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_le_on_finset
      Q (extractionLargeSpectrumGeneratorFinset d k) hM] with n hrep hbound r hr
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  rcases hrep r hr with ⟨γ, hγ, hγr⟩
  rw [hγr]
  exact hbound γ hγ

lemma StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteFejerKernelAverage_eventually_eq_one
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop,
      extractionFiniteFejerKernelAverage Q n = 1 := by
  let P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData :=
    extractionFejerTrigPoly Q
  filter_upwards
    [data.extractionFiniteFejerKernelAverage_eventually_eq Q,
      data.finiteAverage_eventually_eq_zeroCoeff P] with n hkernel hpoly
  rw [hkernel, hpoly]
  exact extractionFejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ

/-- Compact Fejer kernels are continuous. -/
lemma extractionCompactFejerKernel_continuous
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) :
    Continuous (fun z : ExtractionCompactDual data =>
      extractionCompactFejerKernel Q z) := by
  unfold extractionCompactFejerKernel
  exact continuous_const.mul
    (((continuous_finset_sum _ fun γ _ =>
      extractionCharacterValue_continuous (data := data) γ).mul
        ((continuous_finset_sum _ fun γ _ =>
      extractionCharacterValue_continuous (data := data) γ).star)))

/-- Additive-wrapper compact Fejer kernels are continuous. -/
lemma extractionCompactAddFejerKernel_continuous
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) :
    Continuous (fun z : ExtractionCompactAddDual data =>
      extractionCompactAddFejerKernel Q z) := by
  simpa [extractionCompactAddFejerKernel] using
    (extractionCompactFejerKernel_continuous (data := data) Q)

lemma extractionCompactFejerKernel_re_nonneg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (z : ExtractionCompactDual data) :
    0 ≤ (extractionCompactFejerKernel Q z).re := by
  unfold extractionCompactFejerKernel
  set w : ℂ := ∑ γ ∈ Q, extractionCharacterValue z γ
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma extractionCompactAddFejerKernel_re_nonneg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (z : ExtractionCompactAddDual data) :
    0 ≤ (extractionCompactAddFejerKernel Q z).re := by
  simpa [extractionCompactAddFejerKernel] using
    extractionCompactFejerKernel_re_nonneg Q z.toMul

lemma extractionCompactFejerKernel_im_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (z : ExtractionCompactDual data) :
    (extractionCompactFejerKernel Q z).im = 0 := by
  unfold extractionCompactFejerKernel
  set w : ℂ := ∑ γ ∈ Q, extractionCharacterValue z γ
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

lemma extractionCompactAddFejerKernel_im_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (z : ExtractionCompactAddDual data) :
    (extractionCompactAddFejerKernel Q z).im = 0 := by
  simpa [extractionCompactAddFejerKernel] using
    extractionCompactFejerKernel_im_eq_zero Q z.toMul

lemma extractionFiniteFejerKernel_re_nonneg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    (x : ZMod (S.p (data.φ n))) :
    0 ≤ (extractionFiniteFejerKernel Q n x).re := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  unfold extractionFiniteFejerKernel
  set w : ℂ :=
    ∑ γ ∈ Q, ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))
  change 0 ≤ (((Q.card : ℂ)⁻¹) * (w * star w)).re
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma extractionFiniteFejerKernel_im_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    (x : ZMod (S.p (data.φ n))) :
    (extractionFiniteFejerKernel Q n x).im = 0 := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  unfold extractionFiniteFejerKernel
  set w : ℂ :=
    ∑ γ ∈ Q, ZMod.stdAddChar (-(extractionFiniteLiftFreq data n γ * x))
  change (((Q.card : ℂ)⁻¹) * (w * star w)).im = 0
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

lemma norm_normalizedDftFunction_extractionFiniteFejerKernel_le_one_of_average_eq_one
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    (havg : extractionFiniteFejerKernelAverage Q n = 1)
    (r : ZMod (S.p (data.φ n))) :
    (letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩;
      ‖normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖) ≤ 1 := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  have hK_avg :
      avgZMod (extractionFiniteFejerKernel Q n) = 1 := by
    simpa [extractionFiniteFejerKernelAverage] using havg
  exact norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one
    (extractionFiniteFejerKernel Q n)
    (fun y => extractionFiniteFejerKernel_re_nonneg Q n y)
    (fun y => extractionFiniteFejerKernel_im_eq_zero Q n y)
    hK_avg r

lemma norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_le_two_of_average_eq_one
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    (havg : extractionFiniteFejerKernelAverage Q n = 1)
    (r : ZMod (S.p (data.φ n))) :
    (letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩;
      ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖) ≤ 2 := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  calc
    ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖
        ≤ ‖(1 : ℂ)‖ +
            ‖normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ :=
          norm_sub_le _ _
    _ ≤ 1 + 1 := by
          exact add_le_add (by simp)
            (norm_normalizedDftFunction_extractionFiniteFejerKernel_le_one_of_average_eq_one
              Q n havg r)
    _ = 2 := by norm_num

lemma normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    [NeZero (S.p (data.φ n))]
    (r : ZMod (S.p (data.φ n))) :
    normalizedDftFunction (extractionFiniteSmoothedForbiddenKernel Q n) r =
      normalizedDftCoeff (S.F (data.φ n)) r *
        normalizedDftFunction (extractionFiniteFejerKernel Q n) r := by
  unfold extractionFiniteSmoothedForbiddenKernel normalizedDftCoeff
  exact normalizedDftFunction_avgConvolution
    (indicatorC (S.F (data.φ n))) (extractionFiniteFejerKernel Q n) r

lemma StableExtractionCoeffLimitData.normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_eq_coeff
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
        ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        normalizedDftFunction (extractionFiniteFejerKernel Q n)
          (extractionFiniteLiftFreq
            data.toExtendedLargeSpectrumCoeffLimitData n γ)) =
        (extractionFejerTrigPoly Q) (-γ) := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  filter_upwards
    [StableExtendedLargeSpectrumCoeffLimitData.normalizedDftFunction_extractionFiniteFejerKernel_at_lift_eventually_eq_coeff
        (data := data.toStableExtendedLargeSpectrumCoeffLimitData) Q (-γ),
     extractionFiniteLiftFreq_neg_eventually_eq (data := d) γ] with n hcoeff hneg
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  have hfreq :
      -extractionFiniteLiftFreq d n (-γ) =
        extractionFiniteLiftFreq d n γ := by
    rw [hneg]
    simp
  rw [← hfreq]
  exact hcoeff

lemma StableExtractionCoeffLimitData.normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_at_lift_tendsto
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto
      (fun n =>
        (letI : NeZero (S.p
            (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
            ⟨(S.prime
              (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          normalizedDftFunction (extractionFiniteSmoothedForbiddenKernel Q n)
            (extractionFiniteLiftFreq
              data.toExtendedLargeSpectrumCoeffLimitData n γ)))
      atTop
      (𝓝 (data.fCoeffQ γ * (extractionFejerTrigPoly Q) (-γ))) := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  have hF := data.fCoeffQ_tendsto γ
  have hK :
      Tendsto (fun _n : ℕ => (extractionFejerTrigPoly Q) (-γ))
        atTop (𝓝 ((extractionFejerTrigPoly Q) (-γ))) :=
    tendsto_const_nhds
  have hprod := hF.mul hK
  refine hprod.congr' ?_
  filter_upwards
    [data.normalizedDftFunction_extractionFiniteFejerKernel_at_pos_lift_eventually_eq_coeff
      Q γ] with n hKcoeff
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  rw [normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel Q n
    (extractionFiniteLiftFreq d n γ)]
  rw [hKcoeff]

/-- Compact-side trigonometric polynomial representing the fixed-`Q`
Fejer-smoothed forbidden limit.

With the finite evaluation convention used in `ExtractionTrigPoly`, the
coefficient at `γ` corresponds to the finite Fourier coefficient at
`-lift(γ)`, hence the `fCoeffQ (-γ)` factor. -/
noncomputable def StableExtractionCoeffLimitData.compactSmoothedForbiddenTrigPoly
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) :
    ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData :=
  ∑ γ ∈ (extractionFejerTrigPoly Q).support,
    Finsupp.single γ ((extractionFejerTrigPoly Q) γ * data.fCoeffQ (-γ))

/-- Finite average pairing the Fejer-smoothed forbidden kernel with a lifted
trigonometric polynomial. -/
noncomputable def extractionFiniteSmoothedForbiddenWeightedAverage
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (P : ExtractionTrigPoly data) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (data.φ n)) =>
    extractionFiniteSmoothedForbiddenKernel Q n x *
      P.evalFinite n x

/-- Coefficient functional that is the fixed-`Q` limit of
`extractionFiniteSmoothedForbiddenWeightedAverage`. -/
noncomputable def StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) : ℂ :=
  P.sum fun γ c =>
    c * (data.fCoeffQ γ * (extractionFejerTrigPoly Q) (-γ))

lemma StableExtractionCoeffLimitData.compactSmoothedForbiddenTrigPoly_apply
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    data.compactSmoothedForbiddenTrigPoly Q γ =
      (extractionFejerTrigPoly Q) γ * data.fCoeffQ (-γ) := by
  classical
  unfold StableExtractionCoeffLimitData.compactSmoothedForbiddenTrigPoly
  rw [Finsupp.finset_sum_apply]
  by_cases hγ : γ ∈ (extractionFejerTrigPoly Q).support
  · rw [Finset.sum_eq_single γ]
    · simp
    · intro δ hδ hδγ
      exact Finsupp.single_eq_of_ne (Ne.symm hδγ)
    · intro hnot
      exact (hnot hγ).elim
  · have hzero : (extractionFejerTrigPoly Q) γ = 0 :=
      Finsupp.notMem_support_iff.mp hγ
    rw [Finset.sum_eq_zero]
    · rw [hzero]
      simp
    · intro δ hδ
      have hδγ : δ ≠ γ := by
        intro h
        subst h
        exact hγ hδ
      exact Finsupp.single_eq_of_ne (Ne.symm hδγ)

lemma StableExtractionCoeffLimitData.normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_at_neg_lift_tendsto_compactCoeff
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto
      (fun n =>
        (letI : NeZero (S.p
            (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
            ⟨(S.prime
              (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          normalizedDftFunction (extractionFiniteSmoothedForbiddenKernel Q n)
            (-extractionFiniteLiftFreq
              data.toExtendedLargeSpectrumCoeffLimitData n γ)))
      atTop (𝓝 (data.compactSmoothedForbiddenTrigPoly Q γ)) := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  have ht := data.normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_at_lift_tendsto
    Q (-γ)
  have htarget :
      data.fCoeffQ (-γ) * (extractionFejerTrigPoly Q) γ =
        data.compactSmoothedForbiddenTrigPoly Q γ := by
    rw [data.compactSmoothedForbiddenTrigPoly_apply Q γ]
    ring
  have ht' :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p
              (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
              ⟨(S.prime
                (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
            normalizedDftFunction (extractionFiniteSmoothedForbiddenKernel Q n)
              (-extractionFiniteLiftFreq
              data.toExtendedLargeSpectrumCoeffLimitData n γ)))
        atTop (𝓝 (data.fCoeffQ (-γ) * (extractionFejerTrigPoly Q) γ)) := by
    have heq :
        (fun n =>
          (letI : NeZero (S.p (d.φ n)) :=
              ⟨(S.prime (d.φ n)).ne_zero⟩;
            normalizedDftFunction (extractionFiniteSmoothedForbiddenKernel Q n)
              (extractionFiniteLiftFreq d n (-γ)))) =ᶠ[atTop]
        (fun n =>
          (letI : NeZero (S.p (d.φ n)) :=
              ⟨(S.prime (d.φ n)).ne_zero⟩;
            normalizedDftFunction (extractionFiniteSmoothedForbiddenKernel Q n)
              (-extractionFiniteLiftFreq d n γ))) := by
      filter_upwards [extractionFiniteLiftFreq_neg_eventually_eq (data := d) γ] with n hneg
      haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
      rw [hneg]
    have ht'' := ht.congr' heq
    simpa [d] using ht''
  simpa [htarget] using ht'

lemma extractionFiniteSmoothedForbiddenWeightedAverage_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (P R : ExtractionTrigPoly data) (n : ℕ) :
    extractionFiniteSmoothedForbiddenWeightedAverage Q (P + R) n =
      extractionFiniteSmoothedForbiddenWeightedAverage Q P n +
        extractionFiniteSmoothedForbiddenWeightedAverage Q R n := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  unfold extractionFiniteSmoothedForbiddenWeightedAverage
  rw [show
      (fun x : ZMod (S.p (data.φ n)) =>
        extractionFiniteSmoothedForbiddenKernel Q n x *
          ExtractionTrigPoly.evalFinite (P + R) n x) =
      (fun x : ZMod (S.p (data.φ n)) =>
        extractionFiniteSmoothedForbiddenKernel Q n x *
          ExtractionTrigPoly.evalFinite P n x +
        extractionFiniteSmoothedForbiddenKernel Q n x *
          ExtractionTrigPoly.evalFinite R n x) by
        funext x
        rw [ExtractionTrigPoly.evalFinite_add]
        ring]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma extractionFiniteSmoothedForbiddenWeightedAverage_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data))
    (γ : ExtractionDiscreteGroup data) (c : ℂ) (n : ℕ) :
    extractionFiniteSmoothedForbiddenWeightedAverage Q
        (Finsupp.single γ c : ExtractionTrigPoly data) n =
      (letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩;
        c * normalizedDftFunction
          (extractionFiniteSmoothedForbiddenKernel Q n)
          (extractionFiniteLiftFreq data n γ)) := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  unfold extractionFiniteSmoothedForbiddenWeightedAverage
  change avgZMod
      (fun x : ZMod (S.p (data.φ n)) =>
        extractionFiniteSmoothedForbiddenKernel Q n x *
          ExtractionTrigPoly.evalFinite
            (Finsupp.single γ c : ExtractionTrigPoly data) n x) =
    c * normalizedDftFunction
      (extractionFiniteSmoothedForbiddenKernel Q n)
      (extractionFiniteLiftFreq data n γ)
  rw [show
      (fun x : ZMod (S.p (data.φ n)) =>
        extractionFiniteSmoothedForbiddenKernel Q n x *
          ExtractionTrigPoly.evalFinite
            (Finsupp.single γ c : ExtractionTrigPoly data) n x) =
      (fun x : ZMod (S.p (data.φ n)) =>
        c * (ZMod.stdAddChar
          (-(x * extractionFiniteLiftFreq data n γ)) *
            extractionFiniteSmoothedForbiddenKernel Q n x)) by
        funext x
        simp [ExtractionTrigPoly.evalFinite_single]
        ring_nf]
  rw [avgZMod_const_mul]
  congr 1

lemma StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional_add
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (P R : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    data.smoothedForbiddenCoeffFunctional Q (P + R) =
      data.smoothedForbiddenCoeffFunctional Q P +
        data.smoothedForbiddenCoeffFunctional Q R := by
  unfold StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional
  let h :
      ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData →
        ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c *
        (data.fCoeffQ γ * (extractionFejerTrigPoly Q) (-γ))
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + R) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum R (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

@[simp]
lemma StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)) :
    data.smoothedForbiddenCoeffFunctional Q
      (0 : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) = 0 := by
  simp [StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional]

lemma StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional_single
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (γ : ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData)
    (c : ℂ) :
    data.smoothedForbiddenCoeffFunctional Q
        (Finsupp.single γ c :
          ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) =
      c * (data.fCoeffQ γ * (extractionFejerTrigPoly Q) (-γ)) := by
  simp [StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional]

lemma StableExtractionCoeffLimitData.extractionFiniteSmoothedForbiddenWeightedAverage_tendsto_coeffFunctional
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtractionCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (P : ExtractionTrigPoly data.toExtendedLargeSpectrumCoeffLimitData) :
    Tendsto
      (fun n =>
        extractionFiniteSmoothedForbiddenWeightedAverage Q P n)
      atTop (𝓝 (data.smoothedForbiddenCoeffFunctional Q P)) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [extractionFiniteSmoothedForbiddenWeightedAverage,
      StableExtractionCoeffLimitData.smoothedForbiddenCoeffFunctional]
  · intro P R hP hR
    rw [data.smoothedForbiddenCoeffFunctional_add Q P R]
    exact (hP.add hR).congr' (Filter.Eventually.of_forall fun n => by
      exact (extractionFiniteSmoothedForbiddenWeightedAverage_add
        Q P R n).symm)
  · intro γ c
    rw [data.smoothedForbiddenCoeffFunctional_single Q γ c]
    have hcoeff :=
      data.normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_at_lift_tendsto
        Q γ
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have hmul := hc.mul hcoeff
    exact hmul.congr' (Filter.Eventually.of_forall fun n => by
      exact (extractionFiniteSmoothedForbiddenWeightedAverage_single
        Q γ c n).symm)

lemma norm_normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_le_fejer
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    [NeZero (S.p (data.φ n))]
    (r : ZMod (S.p (data.φ n))) :
    ‖normalizedDftFunction (extractionFiniteSmoothedForbiddenKernel Q n) r‖ ≤
      ‖normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ := by
  rw [normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel Q n r]
  calc
    ‖normalizedDftCoeff (S.F (data.φ n)) r *
        normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖
        = ‖normalizedDftCoeff (S.F (data.φ n)) r‖ *
            ‖normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ := by
          rw [norm_mul]
    _ ≤ 1 * ‖normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ :=
          mul_le_mul_of_nonneg_right
            (norm_normalizedDftCoeff_indicator_le_one (S.F (data.φ n)) r)
            (norm_nonneg _)
    _ = ‖normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ := by
          simp

lemma normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    [NeZero (S.p (data.φ n))]
    (r : ZMod (S.p (data.φ n))) :
    normalizedDftFunction
        (fun z : ZMod (S.p (data.φ n)) =>
          indicatorC (S.F (data.φ n)) z -
            extractionFiniteSmoothedForbiddenKernel Q n z) r =
      normalizedDftCoeff (S.F (data.φ n)) r *
        (1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r) := by
  rw [normalizedDftFunction_sub, normalizedDftCoeff,
    normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel Q n r]
  change normalizedDftFunction (indicatorC (S.F (data.φ n))) r -
      normalizedDftFunction (indicatorC (S.F (data.φ n))) r *
        normalizedDftFunction (extractionFiniteFejerKernel Q n) r =
    normalizedDftFunction (indicatorC (S.F (data.φ n))) r *
      (1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r)
  ring

lemma norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_le
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    [NeZero (S.p (data.φ n))]
    (r : ZMod (S.p (data.φ n))) :
    ‖normalizedDftFunction
        (fun z : ZMod (S.p (data.φ n)) =>
          indicatorC (S.F (data.φ n)) z -
            extractionFiniteSmoothedForbiddenKernel Q n z) r‖ ≤
      ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ := by
  rw [normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel Q n r]
  calc
    ‖normalizedDftCoeff (S.F (data.φ n)) r *
        (1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r)‖
        = ‖normalizedDftCoeff (S.F (data.φ n)) r‖ *
            ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ := by
          rw [norm_mul]
    _ ≤ 1 * ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ :=
          mul_le_mul_of_nonneg_right
            (norm_normalizedDftCoeff_indicator_le_one (S.F (data.φ n)) r)
            (norm_nonneg _)
    _ = ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ := by
          simp

lemma norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_le_of_notMem_largeSpectrumAt
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n k : ℕ)
    (havg : extractionFiniteFejerKernelAverage Q n = 1)
    {r : ZMod (S.p (data.φ n))}
    (hr : r ∉ S.largeSpectrumAt (data.φ n) k) :
    (letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩;
      ‖normalizedDftFunction
        (fun z : ZMod (S.p (data.φ n)) =>
          indicatorC (S.F (data.φ n)) z -
            extractionFiniteSmoothedForbiddenKernel Q n z) r‖) ≤
      2 * (((2 : ℝ) ^ k)⁻¹) := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  have hF :
      ‖normalizedDftFunction (indicatorC (S.F (data.φ n))) r‖ ≤
        (((2 : ℝ) ^ k)⁻¹) :=
    S.norm_normalizedDftFunction_le_of_notMem_largeSpectrumAt hr
  have hK :
      ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ ≤ 2 :=
    norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_le_two_of_average_eq_one
      Q n havg r
  rw [normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel Q n r]
  calc
    ‖normalizedDftCoeff (S.F (data.φ n)) r *
        (1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r)‖
        = ‖normalizedDftFunction (indicatorC (S.F (data.φ n))) r‖ *
            ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ := by
          rw [normalizedDftCoeff, norm_mul]
    _ ≤ (((2 : ℝ) ^ k)⁻¹) * 2 := by
          exact mul_le_mul hF hK (norm_nonneg _)
            (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k))
    _ = 2 * (((2 : ℝ) ^ k)⁻¹) := by ring

lemma norm_normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_sub_indicatorC_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    [NeZero (S.p (data.φ n))]
    (r : ZMod (S.p (data.φ n))) :
    ‖normalizedDftFunction
        (fun z : ZMod (S.p (data.φ n)) =>
          extractionFiniteSmoothedForbiddenKernel Q n z -
            indicatorC (S.F (data.φ n)) z) r‖ =
      ‖normalizedDftFunction
        (fun z : ZMod (S.p (data.φ n)) =>
          indicatorC (S.F (data.φ n)) z -
            extractionFiniteSmoothedForbiddenKernel Q n z) r‖ := by
  have hfun :
      (fun z : ZMod (S.p (data.φ n)) =>
          extractionFiniteSmoothedForbiddenKernel Q n z -
            indicatorC (S.F (data.φ n)) z) =
        fun z : ZMod (S.p (data.φ n)) =>
          -(indicatorC (S.F (data.φ n)) z -
            extractionFiniteSmoothedForbiddenKernel Q n z) := by
    funext z
    ring
  rw [hfun, normalizedDftFunction_neg, norm_neg]

lemma StableExtendedLargeSpectrumCoeffLimitData.norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_on_largeSpectrumAt_eventually_le
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (k : ℕ) {M : ℝ}
    (hM : ExtractionFejerNegCoeffBound Q
      (extractionLargeSpectrumGeneratorFinset
        data.toExtendedLargeSpectrumCoeffLimitData k) M) :
    ∀ᶠ n in atTop,
      ∀ r ∈ S.largeSpectrumAt
          (data.toExtendedLargeSpectrumCoeffLimitData.φ n) k,
        (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          ‖normalizedDftFunction
            (fun z : ZMod (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) =>
              indicatorC (S.F (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) z -
                extractionFiniteSmoothedForbiddenKernel Q n z) r‖) ≤ M := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  filter_upwards
    [data.norm_one_sub_normalizedDftFunction_extractionFiniteFejerKernel_on_largeSpectrumAt_eventually_le
      Q k hM] with n hlarge r hr
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  exact
    (norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_le
      Q n r).trans (hlarge r hr)

lemma StableExtendedLargeSpectrumCoeffLimitData.weightedSpectralBound_extractionFiniteSmoothedForbiddenKernel_sub_indicatorC_eventually
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (hQ : Q ≠ ∅) (k : ℕ) {M : ℝ}
    (hM : ExtractionFejerNegCoeffBound Q
      (extractionLargeSpectrumGeneratorFinset
        data.toExtendedLargeSpectrumCoeffLimitData k) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
        ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        WeightedSpectralBound
          (fun z : ZMod (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) =>
            extractionFiniteSmoothedForbiddenKernel Q n z -
              indicatorC (S.F (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) z)
          (max M (2 * (((2 : ℝ) ^ k)⁻¹)))) := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  filter_upwards
    [data.norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_on_largeSpectrumAt_eventually_le
      Q k hM,
     data.extractionFiniteFejerKernelAverage_eventually_eq_one Q hQ] with n hlarge havg
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  intro r
  rw [norm_normalizedDftFunction_extractionFiniteSmoothedForbiddenKernel_sub_indicatorC_eq
    Q n r]
  by_cases hr : r ∈ S.largeSpectrumAt (d.φ n) k
  · exact (hlarge r hr).trans (le_max_left _ _)
  · exact
      (norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_le_of_notMem_largeSpectrumAt
        Q n k havg hr).trans (le_max_right _ _)

lemma StableExtendedLargeSpectrumCoeffLimitData.norm_finiteKernelAvoidanceDensity_extractionFiniteSmoothedForbiddenKernel_sub_finiteAvoidanceDensity_eventually_le
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (hQ : Q ≠ ∅) (k : ℕ) {M : ℝ}
    (hM : ExtractionFejerNegCoeffBound Q
      (extractionLargeSpectrumGeneratorFinset
        data.toExtendedLargeSpectrumCoeffLimitData k) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
        ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        ‖finiteKernelAvoidanceDensity (m := m)
            (extractionFiniteSmoothedForbiddenKernel Q n)
            (indicatorC (S.U (data.toExtendedLargeSpectrumCoeffLimitData.φ n))) -
          finiteAvoidanceDensity (m := m)
            (S.F (data.toExtendedLargeSpectrumCoeffLimitData.φ n))
            (S.U (data.toExtendedLargeSpectrumCoeffLimitData.φ n))‖) ≤
        ((pairEdgePairs m).card : ℝ) *
          ((2 ^ (pairEdgePairs m).card : ℕ) : ℝ) *
            (max M (2 * (((2 : ℝ) ^ k)⁻¹))) := by
  let d := data.toExtendedLargeSpectrumCoeffLimitData
  filter_upwards
    [data.extractionFiniteFejerKernelAverage_eventually_eq_one Q hQ,
     data.weightedSpectralBound_extractionFiniteSmoothedForbiddenKernel_sub_indicatorC_eventually
      Q hQ k hM] with n havg hspec
  haveI : NeZero (S.p (d.φ n)) := ⟨(S.prime (d.φ n)).ne_zero⟩
  have hlow_nonneg : 0 ≤ 2 * (((2 : ℝ) ^ k)⁻¹) := by
    positivity
  have hmax_nonneg : 0 ≤ max M (2 * (((2 : ℝ) ^ k)⁻¹)) :=
    hlow_nonneg.trans (le_max_right M (2 * (((2 : ℝ) ^ k)⁻¹)))
  have hsmoothed_norm :
      ∀ z : ZMod (S.p (d.φ n)),
        ‖extractionFiniteSmoothedForbiddenKernel Q n z‖ ≤ 1 := by
    have hK_avg :
        avgZMod (extractionFiniteFejerKernel Q n) = 1 := by
      simpa [extractionFiniteFejerKernelAverage] using havg
    exact norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
      (S.F (d.φ n)) (extractionFiniteFejerKernel Q n)
      (fun y => extractionFiniteFejerKernel_re_nonneg Q n y)
      (fun y => extractionFiniteFejerKernel_im_eq_zero Q n y)
      hK_avg
  exact
    norm_finiteKernelAvoidanceDensity_sub_finiteAvoidanceDensity_le_spectral_closed
      (F := S.F (d.φ n)) (U := S.U (d.φ n))
      (g := extractionFiniteSmoothedForbiddenKernel Q n)
      hmax_nonneg hsmoothed_norm hspec

lemma StableExtendedLargeSpectrumCoeffLimitData.norm_finiteKernelAvoidanceDensity_extractionFiniteSmoothedForbiddenKernel_sub_finiteAvoidanceDensity_eventually_le_of_pairCoeffRealBound_neg
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (hQ : Q ≠ ∅) (k : ℕ) {M : ℝ}
    (hM : ExtractionFejerPairCoeffRealBound Q
      ((extractionLargeSpectrumGeneratorFinset
        data.toExtendedLargeSpectrumCoeffLimitData k).image Neg.neg) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
        ⟨(S.prime (data.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
        ‖finiteKernelAvoidanceDensity (m := m)
            (extractionFiniteSmoothedForbiddenKernel Q n)
            (indicatorC (S.U (data.toExtendedLargeSpectrumCoeffLimitData.φ n))) -
          finiteAvoidanceDensity (m := m)
            (S.F (data.toExtendedLargeSpectrumCoeffLimitData.φ n))
            (S.U (data.toExtendedLargeSpectrumCoeffLimitData.φ n))‖) ≤
        ((pairEdgePairs m).card : ℝ) *
          ((2 ^ (pairEdgePairs m).card : ℕ) : ℝ) *
            (max M (2 * (((2 : ℝ) ^ k)⁻¹))) :=
  data.norm_finiteKernelAvoidanceDensity_extractionFiniteSmoothedForbiddenKernel_sub_finiteAvoidanceDensity_eventually_le
    Q hQ k (extractionFejerNegCoeffBound_of_pairCoeffRealBound_neg hM)

lemma weightedSpectralBound_extractionFiniteSmoothedForbiddenKernel_sub_indicatorC
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    [NeZero (S.p (data.φ n))] {M : ℝ}
    (hM : ∀ r : ZMod (S.p (data.φ n)),
      ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ ≤ M) :
    WeightedSpectralBound
      (fun z : ZMod (S.p (data.φ n)) =>
        extractionFiniteSmoothedForbiddenKernel Q n z -
          indicatorC (S.F (data.φ n)) z) M := by
  intro r
  have hfun :
      (fun z : ZMod (S.p (data.φ n)) =>
        extractionFiniteSmoothedForbiddenKernel Q n z -
          indicatorC (S.F (data.φ n)) z) =
      fun z : ZMod (S.p (data.φ n)) =>
        -(indicatorC (S.F (data.φ n)) z -
          extractionFiniteSmoothedForbiddenKernel Q n z) := by
    funext z
    ring
  rw [hfun, normalizedDftFunction_neg, norm_neg]
  exact (norm_normalizedDftFunction_indicator_sub_extractionFiniteSmoothedForbiddenKernel_le
    Q n r).trans (hM r)

lemma extractionFiniteSmoothedForbiddenKernel_norm_le_one_of_average_eq_one
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    (havg : extractionFiniteFejerKernelAverage Q n = 1) :
    ∀ x : ZMod (S.p (data.φ n)),
      ‖extractionFiniteSmoothedForbiddenKernel Q n x‖ ≤ 1 := by
  haveI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
  have hK_avg :
      avgZMod (extractionFiniteFejerKernel Q n) = 1 := by
    simpa [extractionFiniteFejerKernelAverage] using havg
  exact norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
    (S.F (data.φ n)) (extractionFiniteFejerKernel Q n)
    (fun y => extractionFiniteFejerKernel_re_nonneg Q n y)
    (fun y => extractionFiniteFejerKernel_im_eq_zero Q n y)
    hK_avg

/-- Fejer smoothing changes the finite Route A avoidance density by at most
the generic weighted-counting spectral error.  This is the finite half of the
Fejer smoothing step in the Route A compactness proof. -/
lemma norm_finiteKernelAvoidanceDensity_extractionFiniteSmoothedForbiddenKernel_sub_finiteAvoidanceDensity_le
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (Q : Finset (ExtractionDiscreteGroup data)) (n : ℕ)
    [NeZero (S.p (data.φ n))]
    (U : Finset (ZMod (S.p (data.φ n)))) {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (havg : extractionFiniteFejerKernelAverage Q n = 1)
    (hM : ∀ r : ZMod (S.p (data.φ n)),
      ‖1 - normalizedDftFunction (extractionFiniteFejerKernel Q n) r‖ ≤ M) :
    ‖finiteKernelAvoidanceDensity (m := m)
        (extractionFiniteSmoothedForbiddenKernel Q n) (indicatorC U) -
        finiteAvoidanceDensity (m := m) (S.F (data.φ n)) U‖ ≤
      ((pairEdgePairs m).card : ℝ) *
        ((2 ^ (pairEdgePairs m).card : ℕ) : ℝ) * M := by
  exact
    norm_finiteKernelAvoidanceDensity_sub_finiteAvoidanceDensity_le_spectral_closed
      (F := S.F (data.φ n)) (U := U)
      hMnonneg
      (extractionFiniteSmoothedForbiddenKernel_norm_le_one_of_average_eq_one
        Q n havg)
      (weightedSpectralBound_extractionFiniteSmoothedForbiddenKernel_sub_indicatorC
        Q n hM)

lemma StableExtendedLargeSpectrumCoeffLimitData.extractionFiniteSmoothedForbiddenKernel_norm_le_one_eventually
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (Q : Finset
      (ExtractionDiscreteGroup data.toExtendedLargeSpectrumCoeffLimitData))
    (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (data.toExtendedLargeSpectrumCoeffLimitData.φ n)),
        ‖extractionFiniteSmoothedForbiddenKernel Q n x‖ ≤ 1 := by
  filter_upwards [data.extractionFiniteFejerKernelAverage_eventually_eq_one Q hQ]
    with n havg x
  exact extractionFiniteSmoothedForbiddenKernel_norm_le_one_of_average_eq_one
    Q n havg x

end

end Erdos42.FourierPositive
