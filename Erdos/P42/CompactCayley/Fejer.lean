/-
Erdős Problem 42 — Fejér kernels for compact-Cayley extraction.
-/

import Erdos.P42.CompactCayley.PairOverlap
import Erdos.P42.CompactCayley.TrigPolynomial

namespace Erdos42.CompactCayley

open Filter Complex
open scoped BigOperators Classical ComplexConjugate Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Compact-dual Fejér kernel associated to a finite frequency set. -/
noncomputable def compactFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactDual) : ℂ :=
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q, E.characterValue z γ) *
      star (∑ γ ∈ Q, E.characterValue z γ))

/-- Compact-dual Fejér kernel on the additive wrapper. -/
noncomputable def compactAddFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) : ℂ :=
  E.compactFejerKernel Q z.toMul

/-- Finite cyclic lift of the Fejér kernel. -/
noncomputable def finiteFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))) *
      star (∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))))

/-- Finite cyclic lift of the compact-phase shifted Fejér kernel. -/
noncomputable def shiftedFiniteFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q,
        E.addCharacterValue z γ *
          ZMod.stdAddChar (-(E.lift n γ * x))) *
      star (∑ γ ∈ Q,
        E.addCharacterValue z γ *
          ZMod.stdAddChar (-(E.lift n γ * x))))

/-- Normalized finite average of the finite cyclic Fejér kernel. -/
noncomputable def finiteFejerKernelAverage
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) => E.finiteFejerKernel Q n x

/-- One Fourier mode in the Fejér expansion. -/
noncomputable def fejerTerm
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (pair : E.Group × E.Group) : E.TrigPoly :=
  Finsupp.single (pair.1 - pair.2) ((Q.card : ℂ)⁻¹)

/-- The Fejér kernel as a trigonometric polynomial. -/
noncomputable def fejerTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) : E.TrigPoly :=
  ∑ pair ∈ Q.product Q, E.fejerTerm Q pair

/-- One Fourier mode in the Fejér expansion, modulated by a compact-dual point.

For fixed `z`, the resulting polynomial is the Fejér kernel translated by `z`
on the compact side; on the finite side it remains a squared magnitude because
the factors `E.addCharacterValue z γ` are unit phases. -/
noncomputable def shiftedFejerTerm
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) : E.TrigPoly :=
  Finsupp.single (pair.1 - pair.2)
    ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2))

/-- The compact-phase shifted Fejér polynomial. -/
noncomputable def shiftedFejerTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    E.TrigPoly :=
  ∑ pair ∈ Q.product Q, E.shiftedFejerTerm Q z pair

lemma fejerTerm_evalFinite
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (pair : E.Group × E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (E.fejerTerm Q pair) n x =
      (Q.card : ℂ)⁻¹ *
        ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x)) := by
  simp [fejerTerm, TrigPoly.evalFinite]

lemma fejerTerm_evalAdd
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (pair : E.Group × E.Group) (z : E.CompactAddDual) :
    TrigPoly.evalAdd (E.fejerTerm Q pair) z =
      (Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2) := by
  simp [fejerTerm]

lemma shiftedFejerTerm_evalFinite
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (E.shiftedFejerTerm Q z pair) n x =
      ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2)) *
        ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x)) := by
  rw [shiftedFejerTerm, TrigPoly.evalFinite_single]

lemma shiftedFejerTerm_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) (γ : E.Group) :
    (E.shiftedFejerTerm Q z pair) γ =
      (E.fejerTerm Q pair γ) * E.addCharacterValue z γ := by
  by_cases h : pair.1 - pair.2 = γ
  · subst h
    simp [shiftedFejerTerm, fejerTerm]
  · simp [shiftedFejerTerm, fejerTerm, h]

lemma shiftedFejerTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (γ : E.Group) :
    E.shiftedFejerTrigPoly Q z γ =
      (E.fejerTrigPoly Q γ) * E.addCharacterValue z γ := by
  classical
  unfold shiftedFejerTrigPoly fejerTrigPoly
  rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply]
  simp_rw [E.shiftedFejerTerm_apply Q z]
  rw [Finset.sum_mul]

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

lemma fejerTrigPoly_compactAverage_eq_one_of_nonempty
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    TrigPoly.compactAverage (E.fejerTrigPoly Q) = 1 := by
  classical
  have hcard_ne : (Q.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr
      (Finset.nonempty_iff_ne_empty.mpr hQ))
  unfold TrigPoly.compactAverage fejerTrigPoly fejerTerm
  rw [Finsupp.finset_sum_apply]
  change (∑ i ∈ Q ×ˢ Q,
    (Finsupp.single (i.1 - i.2) ((Q.card : ℂ)⁻¹) :
      E.TrigPoly) (0 : E.Group)) = 1
  rw [Finset.sum_product]
  simp [Finsupp.single_apply, sub_eq_zero, hcard_ne]

lemma shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) = 1 := by
  unfold TrigPoly.compactAverage
  rw [E.shiftedFejerTrigPoly_apply Q z 0]
  have hfejer0 : (E.fejerTrigPoly Q) (0 : E.Group) = 1 := by
    simpa [TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  rw [hfejer0]
  simp

lemma fejerTrigPoly_evalAdd_eq_compactAddFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd (E.fejerTrigPoly Q) z =
      E.compactAddFejerKernel Q z := by
  classical
  unfold fejerTrigPoly
  let ev : E.TrigPoly →+ ℂ :=
    { toFun := fun P => TrigPoly.evalAdd P z
      map_zero' := by simp
      map_add' := by
        intro P R
        exact TrigPoly.evalAdd_add P R z }
  change ev (∑ pair ∈ Q.product Q, E.fejerTerm Q pair) =
    E.compactAddFejerKernel Q z
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        TrigPoly.evalAdd (E.fejerTerm Q pair) z) =
      E.compactAddFejerKernel Q z
  simp_rw [E.fejerTerm_evalAdd]
  calc
    (∑ pair ∈ Q.product Q,
        (Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2)) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            (E.addCharacterValue z pair.1 *
              star (E.addCharacterValue z pair.2)) := by
      refine Finset.sum_congr rfl ?_
      intro pair _hpair
      rw [E.addCharacterValue_sub]
    _ = E.compactAddFejerKernel Q z := by
      unfold compactAddFejerKernel compactFejerKernel addCharacterValue
      exact sum_product_const_mul_star Q
        (fun γ => E.characterValue z.toMul γ)
        ((Q.card : ℂ)⁻¹)

lemma integral_compactAddFejerKernel_eq_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∫ z : E.CompactAddDual, E.compactAddFejerKernel Q z ∂E.haar = 1 := by
  rw [show
      (fun z : E.CompactAddDual => E.compactAddFejerKernel Q z) =
        fun z => TrigPoly.evalAdd (E.fejerTrigPoly Q) z by
      funext z
      exact (E.fejerTrigPoly_evalAdd_eq_compactAddFejerKernel Q z).symm]
  rw [TrigPoly.integral_evalAdd_eq_compactAverage E]
  exact E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ

lemma integral_compactAddFejerKernel_eq_one_of_separating
    (E : CayleyExtraction S)
    (_hsep :
      ∀ γ : E.Group, γ ≠ 0 →
        ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1)
    (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∫ z : E.CompactAddDual, E.compactAddFejerKernel Q z ∂E.haar = 1 :=
  E.integral_compactAddFejerKernel_eq_one Q hQ

lemma fejerTrigPoly_apply_sum
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) γ =
      ∑ pair ∈ Q.product Q,
        if pair.1 - pair.2 = γ then (Q.card : ℂ)⁻¹ else 0 := by
  unfold fejerTrigPoly fejerTerm
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

lemma fejerTrigPoly_apply_filter_card
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) γ =
      ((pairFiber Q γ).card : ℂ) *
        (Q.card : ℂ)⁻¹ := by
  rw [E.fejerTrigPoly_apply_sum Q γ]
  rw [← Finset.sum_filter]
  have hfilter :
      (Q.product Q).filter (fun pair : E.Group × E.Group =>
        pair.1 - pair.2 = γ) = pairFiber Q γ := by
    ext pair
    simp [pairFiber]
  rw [hfilter]
  simp [mul_comm]

lemma pairFiber_card_neg
    (E : CayleyExtraction S)
    (Q : Finset E.Group) (γ : E.Group) :
    (pairFiber Q (-γ)).card = (pairFiber Q γ).card := by
  classical
  refine Finset.card_bij (fun pair _hpair => (pair.2, pair.1)) ?mem ?inj ?surj
  · intro pair hpair
    have hmem :
        pair ∈ (Q.product Q).filter
          (fun pair : E.Group × E.Group => pair.1 - pair.2 = -γ) := by
      simpa [pairFiber] using hpair
    have hprod := (Finset.mem_filter.mp hmem).1
    have hprod' : (pair.2, pair.1) ∈ Q.product Q :=
      Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hprod).2, (Finset.mem_product.mp hprod).1⟩
    have hdiff := (Finset.mem_filter.mp hmem).2
    have hdiff' : pair.2 - pair.1 = γ := by
      calc
        pair.2 - pair.1 = -(pair.1 - pair.2) := by rw [neg_sub]
        _ = γ := by rw [hdiff]; simp
    have hfilter' :
        (pair.2, pair.1) ∈ (Q.product Q).filter
          (fun pair : E.Group × E.Group => pair.1 - pair.2 = γ) :=
      Finset.mem_filter.mpr ⟨hprod', hdiff'⟩
    simpa [pairFiber] using hfilter'
  · intro a ha b hb hswap
    exact Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)
  · intro pair hpair
    refine ⟨(pair.2, pair.1), ?_, ?_⟩
    · have hmem :
          pair ∈ (Q.product Q).filter
            (fun pair : E.Group × E.Group => pair.1 - pair.2 = γ) := by
        simpa [pairFiber] using hpair
      have hprod := (Finset.mem_filter.mp hmem).1
      have hprod' : (pair.2, pair.1) ∈ Q.product Q :=
        Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hprod).2, (Finset.mem_product.mp hprod).1⟩
      have hdiff := (Finset.mem_filter.mp hmem).2
      have hdiff' : pair.2 - pair.1 = -γ := by
        calc
          pair.2 - pair.1 = -(pair.1 - pair.2) := by rw [neg_sub]
          _ = -γ := by rw [hdiff]
      have hfilter' :
          (pair.2, pair.1) ∈ (Q.product Q).filter
            (fun pair : E.Group × E.Group => pair.1 - pair.2 = -γ) :=
        Finset.mem_filter.mpr ⟨hprod', hdiff'⟩
      simpa [pairFiber] using hfilter'
    · rfl

lemma fejerTrigPoly_apply_neg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) (-γ) = (E.fejerTrigPoly Q) γ := by
  rw [E.fejerTrigPoly_apply_filter_card Q (-γ),
    E.fejerTrigPoly_apply_filter_card Q γ, E.pairFiber_card_neg Q γ]

lemma fejerTrigPoly_apply_re_eq_pairRatio
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).re =
      ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) := by
  let fiber := pairFiber Q γ
  rw [E.fejerTrigPoly_apply_filter_card]
  change (((fiber.card : ℂ) * (Q.card : ℂ)⁻¹).re) =
    (fiber.card : ℝ) / (Q.card : ℝ)
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
  simp

lemma fejerTrigPoly_apply_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).im = 0 := by
  let fiber := pairFiber Q γ
  rw [E.fejerTrigPoly_apply_filter_card]
  change (((fiber.card : ℂ) * (Q.card : ℂ)⁻¹).im) = 0
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
  simp

lemma fejerTrigPoly_apply_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    0 ≤ ((E.fejerTrigPoly Q) γ).re := by
  rw [E.fejerTrigPoly_apply_re_eq_pairRatio]
  positivity

lemma fejerTrigPoly_apply_re_le_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).re ≤ 1 := by
  rw [E.fejerTrigPoly_apply_re_eq_pairRatio]
  exact div_le_one_of_le₀
    (by exact_mod_cast PairCoeffRealBound.pairFilter_card_le Q γ)
    (Nat.cast_nonneg Q.card)

/-- Abstract finite-frequency Fejér coefficient bound. -/
def FejerCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B, ‖1 - (E.fejerTrigPoly Q) γ‖ ≤ M

/-- Pair-count form of the Fejér coefficient bound. -/
def FejerPairCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    ‖1 -
      (((pairFiber Q γ).card : ℂ) *
        (Q.card : ℂ)⁻¹)‖ ≤ M

/-- Real-ratio form of the pair-count Fejér coefficient bound, as produced by
Følner overlap estimates. -/
def FejerPairCoeffRealBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  PairCoeffRealBound Q B M

/-- Lower-overlap form of the Fejér coefficient bound.  This is the shape
normally produced by a Følner-set estimate. -/
def FejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  PairCoeffLowerBound Q B M

/-- Fejér coefficient bound on negative frequencies, the form used by the
finite DFT formula at positive extracted lifts. -/
def FejerNegCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B, ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M

lemma fejerCoeffBound_of_pairCoeffBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffBound Q B M) :
    E.FejerCoeffBound Q B M := by
  intro γ hγ
  rw [E.fejerTrigPoly_apply_filter_card]
  exact hM γ hγ

lemma fejerPairCoeffBound_of_realBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffRealBound Q B M) :
    E.FejerPairCoeffBound Q B M := by
  intro γ hγ
  let fiber := pairFiber Q γ
  have hcast :
      ((fiber.card : ℂ) * (Q.card : ℂ)⁻¹) =
        (((fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    have hfiber : (fiber.card : ℂ) = ((fiber.card : ℝ) : ℂ) := by
      norm_num
    have hQ : (Q.card : ℂ) = ((Q.card : ℝ) : ℂ) := by
      norm_num
    rw [hfiber, hQ, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  change ‖1 - (fiber.card : ℂ) * (Q.card : ℂ)⁻¹‖ ≤ M
  rw [hcast]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa [fiber, FejerPairCoeffRealBound, PairCoeffRealBound] using hM γ hγ

lemma fejerCoeffBound_of_pairCoeffRealBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffRealBound Q B M) :
    E.FejerCoeffBound Q B M :=
  E.fejerCoeffBound_of_pairCoeffBound
    (E.fejerPairCoeffBound_of_realBound hM)

lemma fejerNegCoeffBound_of_coeffBound_neg
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerCoeffBound Q (B.image Neg.neg) M) :
    E.FejerNegCoeffBound Q B M := by
  intro γ hγ
  exact hM (-γ) (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)

lemma fejerNegCoeffBound_of_pairCoeffRealBound_neg
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffRealBound Q (B.image Neg.neg) M) :
    E.FejerNegCoeffBound Q B M :=
  E.fejerNegCoeffBound_of_coeffBound_neg
    (E.fejerCoeffBound_of_pairCoeffRealBound hM)

lemma fejerPairFilter_card_le
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (pairFiber Q γ).card ≤ Q.card :=
  PairCoeffRealBound.pairFilter_card_le Q γ

lemma fejerPairCoeffRealBound_of_lowerBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q B M) :
    E.FejerPairCoeffRealBound Q B M :=
  PairCoeffRealBound.of_lowerBound hQ hM

lemma fejerCoeffBound_of_pairCoeffLowerBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q B M) :
    E.FejerCoeffBound Q B M :=
  E.fejerCoeffBound_of_pairCoeffRealBound
    (E.fejerPairCoeffRealBound_of_lowerBound hQ hM)

lemma fejerNegCoeffBound_of_pairCoeffLowerBound_neg
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q (B.image Neg.neg) M) :
    E.FejerNegCoeffBound Q B M :=
  E.fejerNegCoeffBound_of_coeffBound_neg
    (E.fejerCoeffBound_of_pairCoeffLowerBound hQ hM)

lemma fejerTrigPoly_evalFinite_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x =
          E.finiteFejerKernel Q n x := by
  classical
  have hpairs :
      ∀ᶠ n in atTop,
        ∀ pair ∈ Q.product Q,
          E.lift n (pair.1 - pair.2) =
            E.lift n pair.1 - E.lift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hpair
    exact E.data.finiteLift_sub_eventually_eq pair.1 pair.2
  filter_upwards [hpairs] with n hn x
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold fejerTrigPoly
  let ev : E.TrigPoly →+ ℂ :=
    { toFun := fun P => TrigPoly.evalFinite P n x
      map_zero' := by simp
      map_add' := by
        intro P R
        exact TrigPoly.evalFinite_add P R n x }
  change ev (∑ pair ∈ Q.product Q, E.fejerTerm Q pair) =
    E.finiteFejerKernel Q n x
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        TrigPoly.evalFinite (E.fejerTerm Q pair) n x) =
      E.finiteFejerKernel Q n x
  simp_rw [E.fejerTerm_evalFinite]
  calc
    (∑ pair ∈ Q.product Q,
        (Q.card : ℂ)⁻¹ *
          ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x))) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            (ZMod.stdAddChar (-(E.lift n pair.1 * x)) *
              star (ZMod.stdAddChar (-(E.lift n pair.2 * x)))) := by
      refine Finset.sum_congr rfl ?_
      intro pair hpair
      rw [hn pair hpair]
      rw [stdAddChar_sub_fejer]
    _ = E.finiteFejerKernel Q n x := by
      unfold finiteFejerKernel
      exact sum_product_const_mul_star Q
        (fun γ => ZMod.stdAddChar (-(E.lift n γ * x)))
        ((Q.card : ℂ)⁻¹)

lemma shiftedFejerTrigPoly_evalFinite_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        TrigPoly.evalFinite (E.shiftedFejerTrigPoly Q z) n x =
          E.shiftedFiniteFejerKernel Q z n x := by
  classical
  have hpairs :
      ∀ᶠ n in atTop,
        ∀ pair ∈ Q.product Q,
          E.lift n (pair.1 - pair.2) =
            E.lift n pair.1 - E.lift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hpair
    exact E.data.finiteLift_sub_eventually_eq pair.1 pair.2
  filter_upwards [hpairs] with n hn x
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold shiftedFejerTrigPoly
  let ev : E.TrigPoly →+ ℂ :=
    { toFun := fun P => TrigPoly.evalFinite P n x
      map_zero' := by simp
      map_add' := by
        intro P R
        exact TrigPoly.evalFinite_add P R n x }
  change ev (∑ pair ∈ Q.product Q, E.shiftedFejerTerm Q z pair) =
    E.shiftedFiniteFejerKernel Q z n x
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        TrigPoly.evalFinite (E.shiftedFejerTerm Q z pair) n x) =
      E.shiftedFiniteFejerKernel Q z n x
  simp_rw [E.shiftedFejerTerm_evalFinite]
  calc
    (∑ pair ∈ Q.product Q,
        ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2)) *
          ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x))) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            ((E.addCharacterValue z pair.1 *
                ZMod.stdAddChar (-(E.lift n pair.1 * x))) *
              star (E.addCharacterValue z pair.2 *
                ZMod.stdAddChar (-(E.lift n pair.2 * x)))) := by
      refine Finset.sum_congr rfl ?_
      intro pair hpair
      rw [hn pair hpair]
      rw [E.addCharacterValue_sub, stdAddChar_sub_fejer]
      rw [star_mul]
      ring
    _ = E.shiftedFiniteFejerKernel Q z n x := by
      unfold shiftedFiniteFejerKernel
      exact sum_product_const_mul_star Q
        (fun γ =>
          E.addCharacterValue z γ *
            ZMod.stdAddChar (-(E.lift n γ * x)))
        ((Q.card : ℂ)⁻¹)

lemma finiteFejerKernelAverage_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      E.finiteFejerKernelAverage Q n =
        TrigPoly.finiteAverage (E.fejerTrigPoly Q) n := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernelAverage TrigPoly.finiteAverage
  apply congrArg (fun f : ZMod (S.p (E.φ n)) → ℂ => avgZMod f)
  funext x
  exact (hn x).symm

lemma finiteFejerKernelAverage_tendsto_compactAverage
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Tendsto (fun n => E.finiteFejerKernelAverage Q n) atTop
      (𝓝 (TrigPoly.compactAverage (E.fejerTrigPoly Q))) := by
  have h :
      (fun n => TrigPoly.finiteAverage (E.fejerTrigPoly Q) n) =ᶠ[atTop]
        fun n => E.finiteFejerKernelAverage Q n := by
    filter_upwards [E.finiteFejerKernelAverage_eventually_eq Q] with n hn
    exact hn.symm
  exact (TrigPoly.finiteAverage_tendsto_compactAverage E
    (E.fejerTrigPoly Q)).congr' h

lemma finiteFejerKernelAverage_tendsto_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    Tendsto (fun n => E.finiteFejerKernelAverage Q n) atTop (𝓝 (1 : ℂ)) := by
  simpa [E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ] using
    E.finiteFejerKernelAverage_tendsto_compactAverage Q

lemma normalizedDftFunction_finiteFejerKernel_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (S.p (E.φ n)),
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteFejerKernel Q n) r) =
          (E.fejerTrigPoly Q).sum fun γ c =>
            if r + E.lift n γ = 0 then c else 0 := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn r
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  have hfun :
      E.finiteFejerKernel Q n =
        fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (E.fejerTrigPoly Q) n x := by
    funext x
    exact (hn x).symm
  rw [hfun]
  exact TrigPoly.normalizedDftFunction_evalFinite
    (E := E) (E.fejerTrigPoly Q) n r

lemma normalizedDftFunction_finiteFejerKernel_at_neg_lift_eventually_eq_coeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteFejerKernel Q n) (-E.lift n γ)) =
        (E.fejerTrigPoly Q) γ := by
  let P : E.TrigPoly := E.fejerTrigPoly Q
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_eventually_eq Q,
      E.data.finiteLift_eventually_injOn_finset (insert γ P.support)] with n hfourier hinj
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [hfourier (-E.lift n γ)]
  exact TrigPoly.sum_if_neg_lift_add_eq_zero_eq_apply_of_injOn
    (E := E) P n γ hinj

lemma normalizedDftFunction_finiteFejerKernel_at_lift_eventually_eq_coeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteFejerKernel Q n) (E.lift n γ)) =
        (E.fejerTrigPoly Q) (-γ) := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_at_neg_lift_eventually_eq_coeff
        Q (-γ),
      E.data.finiteLift_neg_eventually_eq γ] with n hcoeff hneg
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  have hfreq : -E.lift n (-γ) = E.lift n γ := by
    simp [lift, hneg]
  rw [← hfreq]
  exact hcoeff

lemma norm_one_sub_normalizedDftFunction_finiteFejerKernel_at_lift_eventually_le
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group)
    {M : ℝ} (hM : ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) (E.lift n γ)‖) ≤ M := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_at_lift_eventually_eq_coeff
      Q γ] with n hn
  rw [hn]
  exact hM

lemma finiteFejerKernelAverage_eventually_eq_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop, E.finiteFejerKernelAverage Q n = 1 := by
  let P : E.TrigPoly := E.fejerTrigPoly Q
  filter_upwards
    [E.finiteFejerKernelAverage_eventually_eq Q,
      TrigPoly.finiteAverage_eventually_eq_zeroCoeff E P] with n hkernel hpoly
  rw [hkernel, hpoly]
  exact E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ

lemma compactFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactDual) :
    0 ≤ (E.compactFejerKernel Q z).re := by
  unfold compactFejerKernel
  set w : ℂ := ∑ γ ∈ Q, E.characterValue z γ
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma compactFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactDual) :
    (E.compactFejerKernel Q z).im = 0 := by
  unfold compactFejerKernel
  set w : ℂ := ∑ γ ∈ Q, E.characterValue z γ
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

lemma compactAddFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) :
    0 ≤ (E.compactAddFejerKernel Q z).re := by
  simpa [compactAddFejerKernel] using E.compactFejerKernel_re_nonneg Q z.toMul

lemma compactAddFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) :
    (E.compactAddFejerKernel Q z).im = 0 := by
  simpa [compactAddFejerKernel] using E.compactFejerKernel_im_eq_zero Q z.toMul

lemma finiteFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) :
    0 ≤ (E.finiteFejerKernel Q n x).re := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernel
  set w : ℂ := ∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))
  change 0 ≤ (((Q.card : ℂ)⁻¹) * (w * star w)).re
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma finiteFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) :
    (E.finiteFejerKernel Q n x).im = 0 := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernel
  set w : ℂ := ∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))
  change (((Q.card : ℂ)⁻¹) * (w * star w)).im = 0
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

lemma shiftedFiniteFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    0 ≤ (E.shiftedFiniteFejerKernel Q z n x).re := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold shiftedFiniteFejerKernel
  set w : ℂ := ∑ γ ∈ Q,
    E.addCharacterValue z γ * ZMod.stdAddChar (-(E.lift n γ * x))
  change 0 ≤ (((Q.card : ℂ)⁻¹) * (w * star w)).re
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma shiftedFiniteFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    (E.shiftedFiniteFejerKernel Q z n x).im = 0 := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold shiftedFiniteFejerKernel
  set w : ℂ := ∑ γ ∈ Q,
    E.addCharacterValue z γ * ZMod.stdAddChar (-(E.lift n γ * x))
  change (((Q.card : ℂ)⁻¹) * (w * star w)).im = 0
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

end CayleyExtraction

end

end Erdos42.CompactCayley
