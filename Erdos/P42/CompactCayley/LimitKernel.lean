/-
Erdős Problem 42 — first compact-limit kernel coefficient layer.

This file defines the complement coefficients
`gCoeff 0 = 1 - a(0).re`, `gCoeff γ = -a(γ).re` for nonzero `γ`, where
`a` is the extracted Cayley Fourier coefficient limit.  The summability and
continuous Fourier-series construction are later steps.
-/

import Erdos.P42.CompactCayley.Folner
import Erdos.P42.CompactCayley.Smoothing
import Erdos.P42.CompactCayley.PositiveDefinite
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Erdos42.CompactCayley

open Filter Erdos42 MeasureTheory
open scoped Classical Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

lemma coeff_norm_le_one (E : CayleyExtraction S) (γ : E.Group) :
    ‖E.coeff γ‖ ≤ 1 := by
  have hlim :=
    (continuous_norm.tendsto (E.coeff γ)).comp (E.coeff_tendsto γ)
  have hbound :
      ∀ᶠ n in atTop,
        ‖(letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ))‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      simpa [CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
        normalizedDftCoeff] using
        (S.toFourierSeq).norm_coeff_le_one (E.φ n) (E.lift n γ))
  exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds hbound

lemma coeff_zero_re_le_one (E : CayleyExtraction S) :
    (E.coeff (0 : E.Group)).re ≤ 1 := by
  exact (Complex.re_le_norm (E.coeff (0 : E.Group))).trans
    (E.coeff_norm_le_one 0)

lemma coeff_zero_re_nonneg (E : CayleyExtraction S) :
    0 ≤ (E.coeff (0 : E.Group)).re := by
  have hlim :=
    Complex.continuous_re.tendsto (E.coeff (0 : E.Group)) |>.comp
      (E.coeff_tendsto (0 : E.Group))
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            (normalizedDftCoeff (S.T (E.φ n)) (E.lift n 0)).re) := by
    filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hn
    letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    have hp_pos : 0 < (S.p (E.φ n) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (S.prime (E.φ n)).ne_zero
    have hcard_nonneg :
        0 ≤ ((S.T (E.φ n)).card : ℝ) / (S.p (E.φ n) : ℝ) := by
      positivity
    simpa [lift, hn, normalizedDftCoeff_zero_eq_card_div,
      Complex.ofReal_div] using hcard_nonneg
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hnonneg

/-- Complement Fourier coefficients for the compact limit kernel `g = 1 - f`. -/
noncomputable def gCoeff (E : CayleyExtraction S) (γ : E.Group) : ℝ :=
  if γ = 0 then 1 - (E.coeff (0 : E.Group)).re else -(E.coeff γ).re

lemma gCoeff_zero (E : CayleyExtraction S) :
    E.gCoeff 0 = 1 - (E.coeff (0 : E.Group)).re := by
  simp [gCoeff]

lemma gCoeff_of_ne_zero (E : CayleyExtraction S)
    {γ : E.Group} (hγ : γ ≠ 0) :
    E.gCoeff γ = -(E.coeff γ).re := by
  simp [gCoeff, hγ]

lemma gCoeff_nonneg (E : CayleyExtraction S) (γ : E.Group) :
    0 ≤ E.gCoeff γ := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [E.gCoeff_zero]
    linarith [E.coeff_zero_re_le_one]
  · rw [E.gCoeff_of_ne_zero hγ]
    exact neg_nonneg.mpr (E.coeff_nonpos_of_ne_zero hγ)

lemma gCoeff_zero_le_one_sub_eta (E : CayleyExtraction S) :
    E.gCoeff 0 ≤ 1 - η := by
  rw [E.gCoeff_zero]
  linarith [E.coeff_zero_ge_eta]

lemma gCoeff_neg_eq (E : CayleyExtraction S) (γ : E.Group) :
    E.gCoeff (-γ) = E.gCoeff γ := by
  by_cases hγ : γ = 0
  · subst hγ
    simp
  · have hneg : -γ ≠ 0 := neg_ne_zero.mpr hγ
    rw [E.gCoeff_of_ne_zero hneg, E.gCoeff_of_ne_zero hγ, E.coeff_neg_eq γ]

lemma gCoeff_le_one (E : CayleyExtraction S) (γ : E.Group) :
    E.gCoeff γ ≤ 1 := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [E.gCoeff_zero]
    linarith [E.coeff_zero_re_nonneg]
  · rw [E.gCoeff_of_ne_zero hγ]
    have hneg_re_le_norm : -(E.coeff γ).re ≤ ‖E.coeff γ‖ := by
      have h := (abs_le.mp (Complex.abs_re_le_norm (E.coeff γ))).1
      linarith
    exact hneg_re_le_norm.trans (E.coeff_norm_le_one γ)

lemma gCoeff_le_norm_coeff_of_ne_zero
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    E.gCoeff γ ≤ ‖E.coeff γ‖ := by
  rw [E.gCoeff_of_ne_zero hγ]
  have h := (abs_le.mp (Complex.abs_re_le_norm (E.coeff γ))).1
  linarith

lemma ne_zero_of_not_mem_largeSpectrumGenerators
    (E : CayleyExtraction S) (q : ℕ+) {γ : E.Group}
    (hγ : γ ∉ E.data.largeSpectrumGenerators q) :
    γ ≠ 0 := by
  intro hzero
  subst hzero
  exact hγ (E.data.zero_mem_largeSpectrumGenerators q)

lemma gCoeff_le_inv_of_not_mem_largeSpectrumGenerators
    (E : CayleyExtraction S) (q : ℕ+) {γ : E.Group}
    (hγ : γ ∉ E.data.largeSpectrumGenerators q) :
    E.gCoeff γ ≤ ((q : ℝ)⁻¹ : ℝ) := by
  exact (E.gCoeff_le_norm_coeff_of_ne_zero
      (E.ne_zero_of_not_mem_largeSpectrumGenerators q hγ)).trans
    (E.coeff_norm_le_inv_of_not_mem_largeSpectrumGenerators q hγ)

lemma sum_gCoeff_le_card_mul_inv_of_forall_not_mem_largeSpectrumGenerators
    (E : CayleyExtraction S) (q : ℕ+) (A : Finset E.Group)
    (hA : ∀ γ ∈ A, γ ∉ E.data.largeSpectrumGenerators q) :
    (∑ γ ∈ A, E.gCoeff γ) ≤
      (A.card : ℝ) * ((q : ℝ)⁻¹ : ℝ) := by
  calc
    (∑ γ ∈ A, E.gCoeff γ)
        ≤ ∑ γ ∈ A, ((q : ℝ)⁻¹ : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          exact E.gCoeff_le_inv_of_not_mem_largeSpectrumGenerators q (hA γ hγ)
    _ = (A.card : ℝ) * ((q : ℝ)⁻¹ : ℝ) := by
          simp [mul_comm]

lemma sum_gCoeff_sdiff_largeSpectrumGenerators_le_card_mul_inv
    (E : CayleyExtraction S) (q : ℕ+) (A : Finset E.Group) :
    (∑ γ ∈ A \ E.data.largeSpectrumGenerators q, E.gCoeff γ) ≤
      ((A \ E.data.largeSpectrumGenerators q).card : ℝ) *
        ((q : ℝ)⁻¹ : ℝ) :=
  E.sum_gCoeff_le_card_mul_inv_of_forall_not_mem_largeSpectrumGenerators q
    (A \ E.data.largeSpectrumGenerators q) (by
      intro γ hγ hmem
      exact (Finset.mem_sdiff.mp hγ).2 hmem)

lemma sum_gCoeff_largeSpectrumGenerators_le_card
    (E : CayleyExtraction S) (q : ℕ+) :
    (∑ γ ∈ E.data.largeSpectrumGenerators q, E.gCoeff γ) ≤
      (E.data.largeSpectrumGenerators q).card := by
  calc
    (∑ γ ∈ E.data.largeSpectrumGenerators q, E.gCoeff γ)
        ≤ ∑ γ ∈ E.data.largeSpectrumGenerators q, (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro γ _hγ
          exact E.gCoeff_le_one γ
    _ = (E.data.largeSpectrumGenerators q).card := by simp

lemma sum_gCoeff_largeSpectrumGenerators_le_quad
    (E : CayleyExtraction S) (q : ℕ+) :
    (∑ γ ∈ E.data.largeSpectrumGenerators q, E.gCoeff γ) ≤
      ((q : ℕ) ^ 2 + 2 : ℕ) := by
  exact (E.sum_gCoeff_largeSpectrumGenerators_le_card q).trans
    (by exact_mod_cast E.data.largeSpectrumGenerators_card_le q)

lemma one_sub_indicatorCoeffFunctional_fejer_re_le_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re ≤ 1 := by
  have htendsto :=
    E.finiteComplementFejerAverage_tendsto_one_sub_indicatorCoeffFunctional Q hQ
  have htendsto_re :=
    Complex.continuous_re.tendsto
      (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)) |>.comp htendsto
  exact le_of_tendsto_of_tendsto htendsto_re tendsto_const_nhds
    (E.finiteComplementFejerAverage_re_le_one_eventually Q hQ)

lemma indicatorCoeffFunctional_fejer_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    0 ≤ (TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re := by
  have h := E.one_sub_indicatorCoeffFunctional_fejer_re_le_one Q hQ
  have h' :
      1 - (TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re ≤ 1 := by
    simpa using h
  linarith

lemma one_sub_indicatorCoeffFunctional_fejer_re_eq_sum_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re =
      ∑ γ ∈ (E.fejerTrigPoly Q).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ := by
  classical
  let P : E.TrigPoly := E.fejerTrigPoly Q
  have hP0 : P (0 : E.Group) = 1 := by
    simpa [P, TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  have h0mem : (0 : E.Group) ∈ P.support := by
    rw [Finsupp.mem_support_iff]
    rw [hP0]
    norm_num
  have hindicator_re :
      (TrigPoly.indicatorCoeffFunctional P).re =
        ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
    unfold TrigPoly.indicatorCoeffFunctional
    rw [Finsupp.sum]
    simp [Complex.re_sum]
  have hsum_if :
      (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : E.Group)]
    · simp
    · intro γ hγ hγ_ne
      simp [hγ_ne]
    · intro hnot
      exact False.elim (hnot h0mem)
  have hpoint :
      ∀ γ ∈ P.support,
        ((P γ).re * E.gCoeff γ) =
          (if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re := by
    intro γ _hγ
    have hP_im : (P γ).im = 0 := by
      simpa [P] using E.fejerTrigPoly_apply_im_eq_zero Q γ
    have hcoeff_im : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
    have hmul_re : (P γ * E.coeff γ).re = (P γ).re * (E.coeff γ).re := by
      rw [Complex.mul_re, hP_im, hcoeff_im]
      ring
    by_cases hγ0 : γ = 0
    · subst hγ0
      have hP0_re : (P (0 : E.Group)).re = 1 := by
        rw [hP0]
        simp
      rw [E.gCoeff_zero, hmul_re, hP0_re]
      simp
    · rw [E.gCoeff_of_ne_zero hγ0, hmul_re]
      simp [hγ0]
  calc
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re
        = 1 - (TrigPoly.indicatorCoeffFunctional P).re := by
            simp [P]
    _ = (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) -
          ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
            rw [hsum_if, hindicator_re]
    _ = ∑ γ ∈ P.support,
          (((if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ γ ∈ P.support, (P γ).re * E.gCoeff γ := by
            refine Finset.sum_congr rfl ?_
            intro γ hγ
            exact (hpoint γ hγ).symm
    _ = ∑ γ ∈ (E.fejerTrigPoly Q).support,
          ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ := by
            simp [P]

lemma shiftedFejer_complementFunctional_re_eq_sum_gCoeff_mul_character_re
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re =
      ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re := by
  classical
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let K : E.TrigPoly := E.fejerTrigPoly Q
  have hP0 : P (0 : E.Group) = 1 := by
    simpa [P, TrigPoly.compactAverage] using
      E.shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty Q z hQ
  have hK0 : K (0 : E.Group) = 1 := by
    simpa [K, TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  have h0mem : (0 : E.Group) ∈ P.support := by
    rw [Finsupp.mem_support_iff]
    rw [hP0]
    norm_num
  have hindicator_re :
      (TrigPoly.indicatorCoeffFunctional P).re =
        ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
    unfold TrigPoly.indicatorCoeffFunctional
    rw [Finsupp.sum]
    simp [Complex.re_sum]
  have hsum_if :
      (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : E.Group)]
    · simp
    · intro γ hγ hγ_ne
      simp [hγ_ne]
    · intro hnot
      exact False.elim (hnot h0mem)
  have hpoint :
      ∀ γ ∈ P.support,
        ((K γ).re * E.gCoeff γ * (E.addCharacterValue z γ).re) =
          (if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re := by
    intro γ _hγ
    have hP_apply :
        P γ = K γ * E.addCharacterValue z γ := by
      simpa [P, K] using E.shiftedFejerTrigPoly_apply Q z γ
    have hK_im : (K γ).im = 0 := by
      simpa [K] using E.fejerTrigPoly_apply_im_eq_zero Q γ
    have hcoeff_im : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
    have hmul_re :
        (P γ * E.coeff γ).re =
          (K γ).re * (E.addCharacterValue z γ).re * (E.coeff γ).re := by
      rw [hP_apply]
      simp [Complex.mul_re, Complex.mul_im, hK_im, hcoeff_im,
        mul_left_comm, mul_comm]
    by_cases hγ0 : γ = 0
    · subst hγ0
      have hK0_re : (K (0 : E.Group)).re = 1 := by
        rw [hK0]
        simp
      rw [E.gCoeff_zero, hmul_re, hK0_re]
      simp
    · rw [E.gCoeff_of_ne_zero hγ0, hmul_re]
      simp [hγ0]
      ring
  calc
    (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re
        = 1 - (TrigPoly.indicatorCoeffFunctional P).re := by
            simp [P, E.shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty Q z hQ]
    _ = (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) -
          ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
            rw [hsum_if, hindicator_re]
    _ = ∑ γ ∈ P.support,
          (((if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ γ ∈ P.support,
          (K γ).re * E.gCoeff γ * (E.addCharacterValue z γ).re := by
            refine Finset.sum_congr rfl ?_
            intro γ hγ
            exact (hpoint γ hγ).symm
    _ = ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
          ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re := by
            simp [P, K]

lemma sum_gCoeff_le_of_fejerCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ} (hM_lt : M < 1)
    (hcoeff :
      ∀ γ ∈ B, 1 - M ≤ ((E.fejerTrigPoly Q) γ).re) :
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 := by
  classical
  let P : E.TrigPoly := E.fejerTrigPoly Q
  have hpos : 0 < 1 - M := by linarith
  have hBsupport : B ⊆ P.support := by
    intro γ hγ
    have hre_pos : 0 < (P γ).re := by
      exact lt_of_lt_of_le hpos (by simpa [P] using hcoeff γ hγ)
    by_contra hnot
    have hzero : P γ = 0 := Finsupp.notMem_support_iff.mp hnot
    rw [hzero] at hre_pos
    norm_num at hre_pos
  calc
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ)
        = ∑ γ ∈ B, (1 - M) * E.gCoeff γ := by
            rw [Finset.mul_sum]
    _ ≤ ∑ γ ∈ B, (P γ).re * E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ hγ
            exact mul_le_mul_of_nonneg_right
              (by simpa [P] using hcoeff γ hγ) (E.gCoeff_nonneg γ)
    _ ≤ ∑ γ ∈ P.support, (P γ).re * E.gCoeff γ := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hBsupport (by
              intro γ _hγP _hγB
              exact mul_nonneg
                (by simpa [P] using E.fejerTrigPoly_apply_re_nonneg Q γ)
                (E.gCoeff_nonneg γ))
    _ = (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re := by
            rw [E.one_sub_indicatorCoeffFunctional_fejer_re_eq_sum_gCoeff Q hQ]
    _ ≤ 1 := E.one_sub_indicatorCoeffFunctional_fejer_re_le_one Q hQ

lemma sum_gCoeff_le_of_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ} (hM_lt : M < 1)
    (hcoeff : E.FejerPairCoeffLowerBound Q B M) :
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 :=
  E.sum_gCoeff_le_of_fejerCoeffLowerBound Q B hQ hM_lt (by
    intro γ hγ
    rw [E.fejerTrigPoly_apply_re_eq_pairRatio Q γ]
    exact hcoeff γ hγ)

lemma sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M)
    (B : Finset E.Group) :
    (∑ γ ∈ B, E.gCoeff γ) ≤ 1 := by
  classical
  by_contra hnot
  have hsum_gt : 1 < ∑ γ ∈ B, E.gCoeff γ := lt_of_not_ge hnot
  let A : ℝ := ∑ γ ∈ B, E.gCoeff γ
  let M : ℝ := (A - 1) / (2 * A)
  have hA_pos : 0 < A := by
    exact lt_trans zero_lt_one hsum_gt
  have hM_pos : 0 < M := by
    dsimp [M]
    have hnum : 0 < A - 1 := by
      simpa [A] using sub_pos.mpr hsum_gt
    have hden : 0 < 2 * A := by positivity
    exact div_pos hnum hden
  have hM_lt : M < 1 := by
    dsimp [M]
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    field_simp [hA_ne]
    nlinarith [hA_pos]
  obtain ⟨Q, hQ, hlower⟩ := hfejer B M hM_pos
  have hbound :
      (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 :=
    E.sum_gCoeff_le_of_fejerPairCoeffLowerBound Q B hQ hM_lt hlower
  have hprod_gt : 1 < (1 - M) * (∑ γ ∈ B, E.gCoeff γ) := by
    have hcalc : (1 - M) * A = (A + 1) / 2 := by
      dsimp [M]
      have hA_ne : A ≠ 0 := ne_of_gt hA_pos
      field_simp [hA_ne]
      ring
    have hA_gt : 1 < A := by simpa [A] using hsum_gt
    change 1 < (1 - M) * A
    rw [hcalc]
    nlinarith
  exact not_le_of_gt hprod_gt hbound

lemma summable_gCoeff_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M) :
    Summable E.gCoeff :=
  summable_of_sum_le (fun γ => E.gCoeff_nonneg γ)
    (fun B => E.sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound hfejer B)

lemma tsum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M) :
    (∑' γ : E.Group, E.gCoeff γ) ≤ 1 := by
  have hsum : Summable E.gCoeff :=
    E.summable_gCoeff_of_forall_fejerPairCoeffLowerBound hfejer
  exact le_of_tendsto_of_tendsto hsum.hasSum tendsto_const_nhds
    (Filter.Eventually.of_forall
      (fun B => E.sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound hfejer B))

lemma summable_gCoeff (E : CayleyExtraction S) :
    Summable E.gCoeff :=
  E.summable_gCoeff_of_forall_fejerPairCoeffLowerBound
    (fun B _ hM => E.exists_fejerPairCoeffLowerBound B hM)

lemma tsum_gCoeff_le_one (E : CayleyExtraction S) :
    (∑' γ : E.Group, E.gCoeff γ) ≤ 1 :=
  E.tsum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (fun B _ hM => E.exists_fejerPairCoeffLowerBound B hM)

/-- Complex Fourier-series term for the complement kernel. -/
noncomputable def gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) : ℂ :=
  (E.gCoeff γ : ℂ) * E.addCharacterValue z γ

/-- Complex Fourier series for the compact complement kernel.  The definition
is meaningful without proving summability, but all analytic use below is under
an explicit `Summable E.gCoeff` hypothesis. -/
noncomputable def gComplex
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℂ :=
  ∑' γ : E.Group, E.gComplexTerm γ z

/-- Real-valued compact complement kernel, obtained as the real part of the
complex Fourier series. -/
noncomputable def gReal
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℝ :=
  (E.gComplex z).re

/-- Allowed compact kernel `f = 1 - g`. -/
noncomputable def fReal
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℝ :=
  1 - E.gReal z

lemma norm_gComplexTerm_le_gCoeff
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) :
    ‖E.gComplexTerm γ z‖ ≤ E.gCoeff γ := by
  rw [gComplexTerm, norm_mul, E.norm_addCharacterValue]
  simp [Real.norm_eq_abs, abs_of_nonneg (E.gCoeff_nonneg γ)]

lemma norm_gComplexTerm_eq_gCoeff
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) :
    ‖E.gComplexTerm γ z‖ = E.gCoeff γ := by
  rw [gComplexTerm, norm_mul, E.norm_addCharacterValue]
  simp [Real.norm_eq_abs, abs_of_nonneg (E.gCoeff_nonneg γ)]

lemma gComplexTerm_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactAddDual => E.gComplexTerm γ z) := by
  exact continuous_const.mul (E.addCharacterValue_continuous γ)

lemma star_gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) :
    star (E.gComplexTerm γ z) = E.gComplexTerm (-γ) z := by
  unfold gComplexTerm
  simp [E.star_addCharacterValue, E.gCoeff_neg_eq γ, mul_comm]

lemma gComplexTerm_integrable
    (E : CayleyExtraction S) (γ : E.Group) :
    Integrable (fun z : E.CompactAddDual => E.gComplexTerm γ z) E.haar :=
  (E.gComplexTerm_continuous γ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_norm_gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) :
    ∫ z : E.CompactAddDual, ‖E.gComplexTerm γ z‖ ∂E.haar =
      E.gCoeff γ := by
  simp [E.norm_gComplexTerm_eq_gCoeff γ]

lemma integral_gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) :
    ∫ z : E.CompactAddDual, E.gComplexTerm γ z ∂E.haar =
      if γ = 0 then (E.gCoeff γ : ℂ) else 0 := by
  unfold gComplexTerm
  rw [integral_const_mul, E.integral_addCharacterValue]
  by_cases hγ : γ = 0 <;> simp [hγ]

lemma gComplex_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.gComplex := by
  unfold gComplex
  exact continuous_tsum
    (fun γ => E.gComplexTerm_continuous γ)
    hsum
    (fun γ z => E.norm_gComplexTerm_le_gCoeff γ z)

lemma gReal_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.gReal :=
  Complex.continuous_re.comp (E.gComplex_continuous hsum)

lemma fReal_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.fReal :=
  continuous_const.sub (E.gReal_continuous hsum)

lemma star_gComplex
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    star (E.gComplex z) = E.gComplex z := by
  unfold gComplex
  calc
    star (∑' γ : E.Group, E.gComplexTerm γ z)
        = ∑' γ : E.Group, star (E.gComplexTerm γ z) := by
          simpa using
            (Complex.conj_tsum (fun γ : E.Group => E.gComplexTerm γ z))
    _ = ∑' γ : E.Group, E.gComplexTerm (-γ) z := by
          exact tsum_congr fun γ => E.star_gComplexTerm γ z
    _ = ∑' γ : E.Group, E.gComplexTerm γ z := by
          exact (Equiv.neg E.Group).tsum_eq (fun γ : E.Group =>
            E.gComplexTerm γ z)

lemma gComplex_im_eq_zero
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    (E.gComplex z).im = 0 :=
  Complex.conj_eq_iff_im.mp (E.star_gComplex z)

lemma gComplex_zero_eq_tsum_gCoeff
    (E : CayleyExtraction S) :
    E.gComplex (0 : E.CompactAddDual) =
      ((∑' γ : E.Group, E.gCoeff γ) : ℂ) := by
  unfold gComplex gComplexTerm
  simp

lemma gReal_zero_eq_tsum_gCoeff
    (E : CayleyExtraction S) :
    E.gReal (0 : E.CompactAddDual) =
      ∑' γ : E.Group, E.gCoeff γ := by
  unfold gReal
  rw [E.gComplex_zero_eq_tsum_gCoeff]
  rw [← Complex.ofReal_tsum (fun γ : E.Group => E.gCoeff γ)]
  simp

lemma gComplex_integrable
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Integrable E.gComplex E.haar :=
  (E.gComplex_continuous hsum).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma gReal_integrable
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Integrable E.gReal E.haar :=
  (E.gComplex_integrable hsum).re

lemma fReal_integrable
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Integrable E.fReal E.haar :=
  (integrable_const (1 : ℝ)).sub (E.gReal_integrable hsum)

lemma integral_gComplex
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    ∫ z : E.CompactAddDual, E.gComplex z ∂E.haar =
      (E.gCoeff 0 : ℂ) := by
  have hterm_int :
      ∀ γ : E.Group,
        Integrable (fun z : E.CompactAddDual => E.gComplexTerm γ z) E.haar :=
    fun γ => E.gComplexTerm_integrable γ
  have hnorm_sum :
      Summable
        (fun γ : E.Group =>
          ∫ z : E.CompactAddDual, ‖E.gComplexTerm γ z‖ ∂E.haar) := by
    simpa [E.integral_norm_gComplexTerm] using hsum
  unfold gComplex
  rw [← integral_tsum_of_summable_integral_norm hterm_int hnorm_sum]
  calc
    (∑' γ : E.Group,
        ∫ z : E.CompactAddDual, E.gComplexTerm γ z ∂E.haar)
        =
      ∑' γ : E.Group, if γ = 0 then (E.gCoeff γ : ℂ) else 0 := by
        exact tsum_congr fun γ => E.integral_gComplexTerm γ
    _ = (E.gCoeff 0 : ℂ) := by
        rw [tsum_eq_single (0 : E.Group)]
        · simp
        · intro γ hγ
          simp [hγ]

lemma integral_gReal
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    ∫ z : E.CompactAddDual, E.gReal z ∂E.haar =
      E.gCoeff 0 := by
  unfold gReal
  have hre :=
    integral_re (μ := E.haar) (f := E.gComplex)
      (E.gComplex_integrable hsum)
  rw [E.integral_gComplex hsum] at hre
  simpa using hre

lemma integral_fReal_eq_coeff_zero_re
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    ∫ z : E.CompactAddDual, E.fReal z ∂E.haar =
      (E.coeff (0 : E.Group)).re := by
  unfold fReal
  rw [integral_sub (integrable_const (1 : ℝ)) (E.gReal_integrable hsum)]
  rw [E.integral_gReal hsum, E.gCoeff_zero]
  simp

lemma integral_fReal_ge_eta
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    η ≤ ∫ z : E.CompactAddDual, E.fReal z ∂E.haar := by
  rw [E.integral_fReal_eq_coeff_zero_re hsum]
  exact E.coeff_zero_ge_eta

lemma integral_gReal_le_one_sub_eta
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    ∫ z : E.CompactAddDual, E.gReal z ∂E.haar ≤ 1 - η := by
  rw [E.integral_gReal hsum]
  exact E.gCoeff_zero_le_one_sub_eta

lemma addCharacterValue_re_le_one
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    (E.addCharacterValue z γ).re ≤ 1 := by
  exact (Complex.re_le_norm (E.addCharacterValue z γ)).trans
    (by simp)

lemma neg_one_le_addCharacterValue_re
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    -1 ≤ (E.addCharacterValue z γ).re := by
  have h_abs :
      |(E.addCharacterValue z γ).re| ≤ (1 : ℝ) := by
    simpa [E.norm_addCharacterValue z γ] using
      Complex.abs_re_le_norm (E.addCharacterValue z γ)
  exact (abs_le.mp h_abs).1

lemma shiftedFejer_weighted_gCoeff_character_sum_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    0 ≤
      ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re := by
  have h := E.shiftedFejer_complementFunctional_re_nonneg Q z
  rwa [E.shiftedFejer_complementFunctional_re_eq_sum_gCoeff_mul_character_re
    Q z hQ] at h

lemma sum_gCoeff_mul_character_re_ge_neg_of_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (z : E.CompactAddDual)
    {M : ℝ} (hQ : Q ≠ ∅) (hM_lt : M < 1)
    (hlower : E.FejerPairCoeffLowerBound Q B M) :
    - (∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support \ B, E.gCoeff γ) -
        M * (∑ γ ∈ B, E.gCoeff γ) ≤
      ∑ γ ∈ B, E.gCoeff γ * (E.addCharacterValue z γ).re := by
  classical
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let K : E.TrigPoly := E.fejerTrigPoly Q
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  let w : E.Group → ℝ := fun γ => (K γ).re
  have hBsupport : B ⊆ P.support := by
    intro γ hγ
    have hratio :
        1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) :=
      hlower γ hγ
    have hw_pos : 0 < w γ := by
      have hpos : 0 < 1 - M := by linarith
      exact lt_of_lt_of_le hpos (by
        simpa [w, K, E.fejerTrigPoly_apply_re_eq_pairRatio Q γ] using hratio)
    have hK_ne : K γ ≠ 0 := by
      intro hzero
      have : w γ = 0 := by simp [w, hzero]
      linarith
    have hchar_ne : E.addCharacterValue z γ ≠ 0 := by
      intro hzero
      have hnorm := E.norm_addCharacterValue z γ
      rw [hzero] at hnorm
      norm_num at hnorm
    rw [Finsupp.mem_support_iff]
    rw [show P γ = K γ * E.addCharacterValue z γ by
      simpa [P, K] using E.shiftedFejerTrigPoly_apply Q z γ]
    exact mul_ne_zero hK_ne hchar_ne
  have hweighted :
      0 ≤ ∑ γ ∈ P.support, w γ * a γ := by
    simpa [P, K, w, a, mul_assoc] using
      E.shiftedFejer_weighted_gCoeff_character_sum_nonneg Q z hQ
  have hsplit :
      ∑ γ ∈ P.support, w γ * a γ =
        (∑ γ ∈ P.support \ B, w γ * a γ) +
          ∑ γ ∈ B, w γ * a γ := by
    exact (Finset.sum_sdiff hBsupport).symm
  have htail_le :
      (∑ γ ∈ P.support \ B, w γ * a γ) ≤
        ∑ γ ∈ P.support \ B, E.gCoeff γ := by
    refine Finset.sum_le_sum ?_
    intro γ _hγ
    have hw_nonneg : 0 ≤ w γ := by
      simpa [w, K] using E.fejerTrigPoly_apply_re_nonneg Q γ
    have hw_le_one : w γ ≤ 1 := by
      simpa [w, K] using E.fejerTrigPoly_apply_re_le_one Q γ
    have ha_le : a γ ≤ E.gCoeff γ := by
      dsimp [a]
      simpa using
        mul_le_mul_of_nonneg_left
          (E.addCharacterValue_re_le_one z γ) (E.gCoeff_nonneg γ)
    have hwg_le : w γ * E.gCoeff γ ≤ E.gCoeff γ := by
      nlinarith [hw_nonneg, hw_le_one, E.gCoeff_nonneg γ]
    exact (mul_le_mul_of_nonneg_left ha_le hw_nonneg).trans hwg_le
  have hB_le :
      (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) ≤
        ∑ γ ∈ B, a γ := by
    calc
      (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ)
          = ∑ γ ∈ B, (w γ * a γ - M * E.gCoeff γ) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ γ ∈ B, a γ := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          have hratio :
              1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) :=
            hlower γ hγ
          have hw_lower : 1 - M ≤ w γ := by
            simpa [w, K, E.fejerTrigPoly_apply_re_eq_pairRatio Q γ] using
              hratio
          have hw_le_one : w γ ≤ 1 := by
            simpa [w, K] using E.fejerTrigPoly_apply_re_le_one Q γ
          have hone_minus_nonneg : 0 ≤ 1 - w γ := by linarith
          have hone_minus_le : 1 - w γ ≤ M := by linarith
          have ha_ge_neg : -E.gCoeff γ ≤ a γ := by
            dsimp [a]
            have hg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
            have hre := E.neg_one_le_addCharacterValue_re z γ
            calc
              -E.gCoeff γ = E.gCoeff γ * (-1) := by ring
              _ ≤ E.gCoeff γ * (E.addCharacterValue z γ).re :=
                  mul_le_mul_of_nonneg_left hre hg
          have herror :
              -M * E.gCoeff γ ≤ (1 - w γ) * a γ := by
            have hleft :
                -(1 - w γ) * E.gCoeff γ ≤ (1 - w γ) * a γ := by
              calc
                -(1 - w γ) * E.gCoeff γ
                    = (1 - w γ) * (-E.gCoeff γ) := by ring
                _ ≤ (1 - w γ) * a γ :=
                    mul_le_mul_of_nonneg_left ha_ge_neg hone_minus_nonneg
            have hright :
                -M * E.gCoeff γ ≤ -(1 - w γ) * E.gCoeff γ := by
              have hmul :
                  (1 - w γ) * E.gCoeff γ ≤ M * E.gCoeff γ :=
                mul_le_mul_of_nonneg_right hone_minus_le
                  (E.gCoeff_nonneg γ)
              linarith
            exact hright.trans hleft
          nlinarith
  have hB_lower :
      - (∑ γ ∈ P.support \ B, E.gCoeff γ) ≤
        ∑ γ ∈ B, w γ * a γ := by
    have hweighted_split :
        0 ≤ (∑ γ ∈ P.support \ B, w γ * a γ) +
              ∑ γ ∈ B, w γ * a γ := by
      simpa [hsplit] using hweighted
    linarith
  have hmain :
      - (∑ γ ∈ P.support \ B, E.gCoeff γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) ≤
        (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) := by
    linarith
  exact hmain.trans (by simpa [a] using hB_le)

lemma addCharacterValue_eq_one_of_re_eq_one
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group)
    (hre : (E.addCharacterValue z γ).re = 1) :
    E.addCharacterValue z γ = 1 := by
  have hnormSq : Complex.normSq (E.addCharacterValue z γ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, E.norm_addCharacterValue]
    norm_num
  have him : (E.addCharacterValue z γ).im = 0 := by
    rw [Complex.normSq_apply, hre] at hnormSq
    nlinarith [sq_nonneg (E.addCharacterValue z γ).im]
  apply Complex.ext
  · simp [hre]
  · simp [him]

lemma summable_gCoeff_mul_character_re
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    Summable fun γ : E.Group =>
      E.gCoeff γ * (E.addCharacterValue z γ).re := by
  refine hsum.of_norm_bounded ?_
  intro γ
  have hcoeff_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
  have hre_abs : |(E.addCharacterValue z γ).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
      (by simp)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoeff_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hre_abs hcoeff_nonneg]

lemma gReal_eq_tsum_gCoeff_mul_character_re
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    E.gReal z =
      ∑' γ : E.Group, E.gCoeff γ * (E.addCharacterValue z γ).re := by
  have hterm : Summable fun γ : E.Group => E.gComplexTerm γ z :=
    hsum.of_norm_bounded (fun γ => E.norm_gComplexTerm_le_gCoeff γ z)
  unfold gReal gComplex
  rw [Complex.re_tsum hterm]
  refine tsum_congr ?_
  intro γ
  simp [gComplexTerm, Complex.mul_re]

lemma fReal_eq_coeff_zero_sub_tsum_nonzero_gCoeff
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    E.fReal z =
      (E.coeff (0 : E.Group)).re -
        ∑' γ : E.Group,
          if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re := by
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  have hsumA : Summable a := by
    simpa [a] using E.summable_gCoeff_mul_character_re E.summable_gCoeff z
  have hsplit := hsumA.tsum_eq_add_tsum_ite (0 : E.Group)
  have hzero : a 0 = E.gCoeff 0 := by
    simp [a]
  unfold fReal
  rw [E.gReal_eq_tsum_gCoeff_mul_character_re E.summable_gCoeff z]
  change 1 - (∑' γ : E.Group, a γ) =
    (E.coeff (0 : E.Group)).re -
      ∑' γ : E.Group, if γ = 0 then 0 else a γ
  rw [hsplit, hzero, E.gCoeff_zero]
  ring

lemma compactSmoothReal_eq_coeff_zero_sub_sum_nonzero_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (A : Finset E.Group)
    (hA0 : (0 : E.Group) ∈ A)
    (hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A) :
    E.compactSmoothReal Q z =
      (E.coeff (0 : E.Group)).re -
        ∑ γ ∈ A,
          if γ = 0 then 0
          else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re := by
  classical
  rw [E.compactSmoothReal_eq_sum_of_support_subset Q z A hAsupport]
  let t : E.Group → ℝ :=
    fun γ => (E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
      (E.addCharacterValue z γ).re
  let b : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re
  have ht0 : t 0 = (E.coeff (0 : E.Group)).re := by
    have hK0c : E.fejerTrigPoly Q (0 : E.Group) = 1 := by
      simpa [TrigPoly.compactAverage] using
        E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
    simp [t, hK0c]
  have ht_ne : ∀ γ ∈ A \ ({0} : Finset E.Group), t γ = -b γ := by
    intro γ hγ
    have hne : γ ≠ 0 := by
      intro hzero
      exact (Finset.mem_sdiff.mp hγ).2 (by simp [hzero])
    simp [t, b, hne, E.gCoeff_of_ne_zero hne, mul_assoc]
  have hsum_t :
      (∑ γ ∈ A, t γ) =
        (E.coeff (0 : E.Group)).re +
          ∑ γ ∈ A \ ({0} : Finset E.Group), -b γ := by
    rw [Finset.sum_eq_add_sum_diff_singleton hA0 t, ht0]
    congr 1
    exact Finset.sum_congr rfl ht_ne
  have hsum_b :
      (∑ γ ∈ A, b γ) =
        ∑ γ ∈ A \ ({0} : Finset E.Group), b γ := by
    rw [Finset.sum_eq_add_sum_diff_singleton hA0 b]
    simp [b]
  change (∑ γ ∈ A, t γ) =
    (E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ
  rw [hsum_t, hsum_b]
  rw [Finset.sum_neg_distrib]
  ring

lemma abs_compactSmoothReal_sub_fReal_le_of_tsum_tail
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (A : Finset E.Group)
    (hA0 : (0 : E.Group) ∈ A)
    (hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A)
    {M δ : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ∀ γ ∈ A, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M)
    (htail :
      |(∑ γ ∈ A,
          if γ = 0 then 0
          else E.gCoeff γ * (E.addCharacterValue z γ).re) -
        ∑' γ : E.Group,
          if γ = 0 then 0
          else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤ δ) :
    |E.compactSmoothReal Q z - E.fReal z| ≤
      δ + M * ∑ γ ∈ A, E.gCoeff γ := by
  classical
  let a : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else E.gCoeff γ * (E.addCharacterValue z γ).re
  let b : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re
  have hcompact :
      E.compactSmoothReal Q z =
        (E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ := by
    simpa [b] using
      E.compactSmoothReal_eq_coeff_zero_sub_sum_nonzero_gCoeff
        Q hQ z A hA0 hAsupport
  have hf :
      E.fReal z =
        (E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ := by
    simpa [a] using E.fReal_eq_coeff_zero_sub_tsum_nonzero_gCoeff z
  have htail' : |(∑ γ ∈ A, a γ) - ∑' γ : E.Group, a γ| ≤ δ := by
    simpa [a] using htail
  have hfinite :
      |(∑ γ ∈ A, a γ) - ∑ γ ∈ A, b γ| ≤
        M * ∑ γ ∈ A, E.gCoeff γ := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ γ ∈ A, (a γ - b γ)|
          ≤ ∑ γ ∈ A, |a γ - b γ| := by
            exact Finset.abs_sum_le_sum_abs (fun γ => a γ - b γ) A
      _ ≤ ∑ γ ∈ A, M * E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ hγ
            by_cases hzero : γ = 0
            · simpa [a, b, hzero] using
                mul_nonneg hM_nonneg (E.gCoeff_nonneg γ)
            · have hK_abs : |1 - (E.fejerTrigPoly Q γ).re| ≤ M := by
                have hre :
                    |(1 - E.fejerTrigPoly Q γ).re| ≤
                      ‖1 - E.fejerTrigPoly Q γ‖ :=
                  Complex.abs_re_le_norm _
                have hnorm := hclose γ hγ
                have hrewrite :
                    (1 - E.fejerTrigPoly Q γ).re =
                      1 - (E.fejerTrigPoly Q γ).re := by simp
                simpa [hrewrite] using hre.trans hnorm
              have hchar_abs :
                  |(E.addCharacterValue z γ).re| ≤ 1 :=
                (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
                  (by simp [E.norm_addCharacterValue z γ])
              have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
              have hdiff :
                  a γ - b γ =
                    (1 - (E.fejerTrigPoly Q γ).re) *
                      E.gCoeff γ * (E.addCharacterValue z γ).re := by
                simp [a, b, hzero, mul_assoc]
                ring
              calc
                |a γ - b γ|
                    = |(1 - (E.fejerTrigPoly Q γ).re) *
                        E.gCoeff γ * (E.addCharacterValue z γ).re| := by
                          rw [hdiff]
                _ = |1 - (E.fejerTrigPoly Q γ).re| *
                    E.gCoeff γ * |(E.addCharacterValue z γ).re| := by
                      rw [abs_mul, abs_mul, abs_of_nonneg hg_nonneg]
                _ ≤ M * E.gCoeff γ * 1 := by
                          exact mul_le_mul
                            (mul_le_mul hK_abs le_rfl hg_nonneg hM_nonneg)
                            hchar_abs
                            (abs_nonneg _)
                            (mul_nonneg hM_nonneg hg_nonneg)
                _ = M * E.gCoeff γ := by ring
      _ = M * ∑ γ ∈ A, E.gCoeff γ := by
            rw [Finset.mul_sum]
  rw [hcompact, hf]
  have hdecomp :
      ((E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ) -
          ((E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ) =
        ((∑' γ : E.Group, a γ) - ∑ γ ∈ A, a γ) +
          ((∑ γ ∈ A, a γ) - ∑ γ ∈ A, b γ) := by
    ring
  rw [hdecomp]
  calc
    |((∑' γ : E.Group, a γ) - ∑ γ ∈ A, a γ) +
        ((∑ γ ∈ A, a γ) - ∑ γ ∈ A, b γ)|
        ≤ |(∑' γ : E.Group, a γ) - ∑ γ ∈ A, a γ| +
          |(∑ γ ∈ A, a γ) - ∑ γ ∈ A, b γ| := abs_add_le _ _
    _ ≤ δ + M * ∑ γ ∈ A, E.gCoeff γ := by
      have htail_sym :
          |(∑' γ : E.Group, a γ) - ∑ γ ∈ A, a γ| ≤ δ := by
        simpa [abs_sub_comm] using htail'
      exact add_le_add htail_sym hfinite

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_tsum_compl
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤
      ∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ := by
  classical
  let a : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else E.gCoeff γ * (E.addCharacterValue z γ).re
  have ha_bound : ∀ γ : E.Group, ‖a γ‖ ≤ E.gCoeff γ := by
    intro γ
    by_cases hzero : γ = 0
    · simpa [a, hzero] using E.gCoeff_nonneg γ
    · have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
        (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
          (by simp [E.norm_addCharacterValue z γ])
      have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
      simpa [a, hzero, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hg_nonneg] using
        mul_le_of_le_one_right hg_nonneg hchar_abs
  have hsumA : Summable a := by
    exact E.summable_gCoeff.of_norm_bounded ha_bound
  have hsplit := hsumA.sum_add_tsum_compl (s := A)
  have htail_eq :
      (∑ γ ∈ A, a γ) - ∑' γ : E.Group, a γ =
        - ∑' γ : ↑((↑A : Set E.Group)ᶜ), a γ := by
    rw [← hsplit]
    ring
  have hsub_g :
      Summable (fun γ : ↑((↑A : Set E.Group)ᶜ) => E.gCoeff γ) :=
    E.summable_gCoeff.subtype _
  have hnorm_summable :
      Summable (fun γ : ↑((↑A : Set E.Group)ᶜ) => ‖a γ‖) := by
    refine hsub_g.of_norm_bounded ?_
    intro γ
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a γ))] using
      ha_bound (γ : E.Group)
  have htail_norm :
      ‖∑' γ : ↑((↑A : Set E.Group)ᶜ), a γ‖ ≤
        ∑' γ : ↑((↑A : Set E.Group)ᶜ), ‖a γ‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have htail_norm_le_g :
      (∑' γ : ↑((↑A : Set E.Group)ᶜ), ‖a γ‖) ≤
        ∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ := by
    refine Summable.tsum_le_tsum ?_ hnorm_summable hsub_g
    intro γ
    exact ha_bound (γ : E.Group)
  simpa [a, htail_eq, Real.norm_eq_abs] using htail_norm.trans htail_norm_le_g

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_gCoeff_tail
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ := by
  have htail :=
    E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_tsum_compl A z
  have hsplit := E.summable_gCoeff.sum_add_tsum_compl (s := A)
  have htail_eq :
      (∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ) =
        (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ := by
    rw [← hsplit]
    ring
  simpa [htail_eq] using htail

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_of_gCoeff_tail
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) {δ : ℝ}
    (htail :
      |(∑ γ ∈ A, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤ δ := by
  have h :=
    E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_gCoeff_tail A z
  have htail_upper :
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ ≤ δ := by
    have hle := (abs_le.mp htail).1
    linarith
  exact h.trans htail_upper

lemma abs_compactSmoothReal_sub_fReal_le_of_gCoeff_tail
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (A : Finset E.Group)
    (hA0 : (0 : E.Group) ∈ A)
    (hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A)
    {M δ : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ∀ γ ∈ A, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M)
    (hg_tail :
      |(∑ γ ∈ A, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    |E.compactSmoothReal Q z - E.fReal z| ≤
      δ + M * ∑ γ ∈ A, E.gCoeff γ := by
  exact E.abs_compactSmoothReal_sub_fReal_le_of_tsum_tail Q hQ z A hA0
    hAsupport hM_nonneg hclose
    (E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_of_gCoeff_tail A z
      hg_tail)

lemma sum_gCoeff_sdiff_le_of_gCoeff_tail
    (E : CayleyExtraction S) (B A : Finset E.Group) {δ : ℝ}
    (hg_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    (∑ γ ∈ A \ B, E.gCoeff γ) ≤ δ := by
  classical
  let c : E.Group → ℝ := fun γ => if γ ∈ B then 0 else E.gCoeff γ
  have hc_nonneg : ∀ γ, 0 ≤ c γ := by
    intro γ
    by_cases hγ : γ ∈ B
    · simp [c, hγ]
    · simp [c, hγ, E.gCoeff_nonneg γ]
  have hc_bound : ∀ γ, ‖c γ‖ ≤ E.gCoeff γ := by
    intro γ
    by_cases hγ : γ ∈ B
    · simp [c, hγ, E.gCoeff_nonneg γ]
    · simp [c, hγ, Real.norm_eq_abs,
        abs_of_nonneg (E.gCoeff_nonneg γ)]
  have hc : Summable c := E.summable_gCoeff.of_norm_bounded hc_bound
  have hsum_sdiff :
      (∑ γ ∈ A \ B, E.gCoeff γ) = ∑ γ ∈ A \ B, c γ := by
    refine Finset.sum_congr rfl ?_
    intro γ hγ
    have hnot : γ ∉ B := (Finset.mem_sdiff.mp hγ).2
    simp [c, hnot]
  have hle_tsum :
      (∑ γ ∈ A \ B, c γ) ≤ ∑' γ : E.Group, c γ :=
    hc.sum_le_tsum (A \ B) (fun γ _hγ => hc_nonneg γ)
  have hsumB_c : (∑ γ ∈ B, c γ) = 0 := by
    rw [Finset.sum_eq_zero]
    intro γ hγ
    simp [c, hγ]
  have hcompl_c :
      (∑' γ : ↑((↑B : Set E.Group)ᶜ), c γ) =
        ∑' γ : ↑((↑B : Set E.Group)ᶜ), E.gCoeff γ := by
    refine tsum_congr ?_
    intro γ
    have hnot : (γ : E.Group) ∉ B := by
      exact γ.property
    simp [c, hnot]
  have hc_split := hc.sum_add_tsum_compl (s := B)
  have hg_split := E.summable_gCoeff.sum_add_tsum_compl (s := B)
  have htail_c :
      (∑' γ : E.Group, c γ) =
        (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ := by
    calc
      (∑' γ : E.Group, c γ)
          = (∑ γ ∈ B, c γ) +
              ∑' γ : ↑((↑B : Set E.Group)ᶜ), c γ := by
            exact hc_split.symm
      _ = ∑' γ : ↑((↑B : Set E.Group)ᶜ), E.gCoeff γ := by
            rw [hsumB_c, zero_add, hcompl_c]
      _ = (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ := by
            rw [← hg_split]
            ring
  have htail_upper :
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ ≤ δ := by
    have hle := (abs_le.mp hg_tail).1
    linarith
  rw [hsum_sdiff]
  exact hle_tsum.trans (by simpa [htail_c] using htail_upper)

lemma abs_fejer_nonzero_gCoeff_character_re_le_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) (γ : E.Group) :
    |(if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re)| ≤ E.gCoeff γ := by
  by_cases hzero : γ = 0
  · simpa [hzero] using E.gCoeff_nonneg γ
  · have hK_nonneg : 0 ≤ (E.fejerTrigPoly Q γ).re :=
      E.fejerTrigPoly_apply_re_nonneg Q γ
    have hK_le : (E.fejerTrigPoly Q γ).re ≤ 1 :=
      E.fejerTrigPoly_apply_re_le_one Q γ
    have hK_abs_le : |(E.fejerTrigPoly Q γ).re| ≤ 1 := by
      simpa [abs_of_nonneg hK_nonneg] using hK_le
    have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
    have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
      (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
        (by simp [E.norm_addCharacterValue z γ])
    calc
      |(if γ = 0 then 0
        else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re)|
          = |(E.fejerTrigPoly Q γ).re| * E.gCoeff γ *
              |(E.addCharacterValue z γ).re| := by
                simp [hzero, abs_mul, abs_of_nonneg hK_nonneg,
                  abs_of_nonneg hg_nonneg]
      _ ≤ 1 * E.gCoeff γ * 1 := by
            exact mul_le_mul
              (mul_le_mul hK_abs_le le_rfl hg_nonneg zero_le_one)
              hchar_abs
              (abs_nonneg _)
              (mul_nonneg zero_le_one hg_nonneg)
      _ = E.gCoeff γ := by ring

lemma abs_nonzero_gCoeff_character_re_sub_fejer_le
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) (γ : E.Group)
    {M : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ‖1 - E.fejerTrigPoly Q γ‖ ≤ M) :
    |(if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      (if γ = 0 then 0
        else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re)| ≤ M * E.gCoeff γ := by
  by_cases hzero : γ = 0
  · simpa [hzero] using mul_nonneg hM_nonneg (E.gCoeff_nonneg γ)
  · have hK_abs : |1 - (E.fejerTrigPoly Q γ).re| ≤ M := by
      have hre :
          |(1 - E.fejerTrigPoly Q γ).re| ≤
            ‖1 - E.fejerTrigPoly Q γ‖ :=
        Complex.abs_re_le_norm _
      have hrewrite :
          (1 - E.fejerTrigPoly Q γ).re =
            1 - (E.fejerTrigPoly Q γ).re := by simp
      simpa [hrewrite] using hre.trans hclose
    have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
      (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
        (by simp [E.norm_addCharacterValue z γ])
    have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
    have hdiff :
        (if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re) -
          (if γ = 0 then 0
            else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
              (E.addCharacterValue z γ).re) =
        (1 - (E.fejerTrigPoly Q γ).re) *
          E.gCoeff γ * (E.addCharacterValue z γ).re := by
      simp [hzero, mul_assoc]
      ring
    calc
      |(if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re) -
        (if γ = 0 then 0
          else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re)|
          = |(1 - (E.fejerTrigPoly Q γ).re) *
              E.gCoeff γ * (E.addCharacterValue z γ).re| := by
                rw [hdiff]
      _ = |1 - (E.fejerTrigPoly Q γ).re| *
            E.gCoeff γ * |(E.addCharacterValue z γ).re| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hg_nonneg]
      _ ≤ M * E.gCoeff γ * 1 := by
            exact mul_le_mul
              (mul_le_mul hK_abs le_rfl hg_nonneg hM_nonneg)
              hchar_abs
              (abs_nonneg _)
              (mul_nonneg hM_nonneg hg_nonneg)
      _ = M * E.gCoeff γ := by ring

lemma abs_compactSmoothReal_sub_fReal_le_of_core_fejer_and_gCoeff_tail
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (B : Finset E.Group)
    (hB0 : (0 : E.Group) ∈ B)
    {M δ : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M)
    (hg_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    |E.compactSmoothReal Q z - E.fReal z| ≤
      2 * δ + M * ∑ γ ∈ B, E.gCoeff γ := by
  classical
  let A : Finset E.Group := B ∪ (E.compactSmoothTrigPoly Q).support
  let a : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else E.gCoeff γ * (E.addCharacterValue z γ).re
  let b : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re
  have hBsubA : B ⊆ A := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inl hγ)
  have hA0 : (0 : E.Group) ∈ A := hBsubA hB0
  have hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inr hγ)
  have hcompact :
      E.compactSmoothReal Q z =
        (E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ := by
    simpa [b] using
      E.compactSmoothReal_eq_coeff_zero_sub_sum_nonzero_gCoeff
        Q hQ z A hA0 hAsupport
  have hf :
      E.fReal z =
        (E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ := by
    simpa [a] using E.fReal_eq_coeff_zero_sub_tsum_nonzero_gCoeff z
  have hsplit_b :
      (∑ γ ∈ A, b γ) =
        (∑ γ ∈ B, b γ) + ∑ γ ∈ A \ B, b γ := by
    have h := Finset.sum_sdiff (s₁ := B) (s₂ := A) (f := b) hBsubA
    rw [← h]
    ring
  have htail_signed :
      |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| ≤ δ := by
    have h :=
      E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_of_gCoeff_tail B z
        hg_tail
    simpa [a, abs_sub_comm] using h
  have hcore :
      |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| ≤
        M * ∑ γ ∈ B, E.gCoeff γ := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ γ ∈ B, (a γ - b γ)|
          ≤ ∑ γ ∈ B, |a γ - b γ| := by
            exact Finset.abs_sum_le_sum_abs (fun γ => a γ - b γ) B
      _ ≤ ∑ γ ∈ B, M * E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ hγ
            simpa [a, b] using
              E.abs_nonzero_gCoeff_character_re_sub_fejer_le Q z γ
                hM_nonneg (hclose γ hγ)
      _ = M * ∑ γ ∈ B, E.gCoeff γ := by
            rw [Finset.mul_sum]
  have hextra :
      |∑ γ ∈ A \ B, b γ| ≤ δ := by
    calc
      |∑ γ ∈ A \ B, b γ|
          ≤ ∑ γ ∈ A \ B, |b γ| := by
            exact Finset.abs_sum_le_sum_abs b (A \ B)
      _ ≤ ∑ γ ∈ A \ B, E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ _hγ
            simpa [b] using
              E.abs_fejer_nonzero_gCoeff_character_re_le_gCoeff Q z γ
      _ ≤ δ := E.sum_gCoeff_sdiff_le_of_gCoeff_tail B A hg_tail
  rw [hcompact, hf, hsplit_b]
  have hdecomp :
      ((E.coeff (0 : E.Group)).re -
          ((∑ γ ∈ B, b γ) + ∑ γ ∈ A \ B, b γ)) -
        ((E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ) =
      ((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
        ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
          ∑ γ ∈ A \ B, b γ := by
    ring
  rw [hdecomp]
  calc
    |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
        ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
          ∑ γ ∈ A \ B, b γ|
        ≤ |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
            |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| +
              |∑ γ ∈ A \ B, b γ| := by
          calc
            |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
                  ∑ γ ∈ A \ B, b γ|
                = |(((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                    ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ)) +
                    (-(∑ γ ∈ A \ B, b γ))| := by ring_nf
            _ ≤ |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                    ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ)| +
                  |-(∑ γ ∈ A \ B, b γ)| := abs_add_le _ _
            _ ≤ (|(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
                    |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ|) +
                  |∑ γ ∈ A \ B, b γ| := by
                    simpa [abs_neg] using
                      add_le_add_right
                        (abs_add_le
                          ((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ)
                          ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ))
                        |∑ γ ∈ A \ B, b γ|
            _ = |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
                    |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| +
                  |∑ γ ∈ A \ B, b γ| := by ring
    _ ≤ δ + M * ∑ γ ∈ B, E.gCoeff γ + δ := by
          exact add_le_add (add_le_add htail_signed hcore) hextra
    _ = 2 * δ + M * ∑ γ ∈ B, E.gCoeff γ := by ring

theorem exists_compactSmoothReal_uniform_close
    (E : CayleyExtraction S) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      ∀ z : E.CompactAddDual,
        |E.compactSmoothReal Q z - E.fReal z| ≤ ε := by
  classical
  let δ : ℝ := ε / 4
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let Gtot : ℝ := ∑' γ : E.Group, E.gCoeff γ
  have htail_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := by
    have h := (Metric.tendsto_nhds.mp E.summable_gCoeff.hasSum δ hδ_pos)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, Gtot] using hB
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp htail_event
  let B : Finset E.Group := insert 0 B₀
  have hB_ge : B ≥ B₀ := by
    intro γ hγ
    exact Finset.mem_insert.mpr (Or.inr hγ)
  have hB_tail_lt : |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ :=
    hB₀ B hB_ge
  have hB_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ := by
    simpa [Gtot] using le_of_lt hB_tail_lt
  have hB0 : (0 : E.Group) ∈ B := Finset.mem_insert_self _ _
  let SB : ℝ := ∑ γ ∈ B, E.gCoeff γ
  have hSB_nonneg : 0 ≤ SB := by
    dsimp [SB]
    exact Finset.sum_nonneg fun γ _hγ => E.gCoeff_nonneg γ
  let M : ℝ := δ / (SB + 1)
  have hden_pos : 0 < SB + 1 := by
    nlinarith
  have hM_pos : 0 < M := by
    dsimp [M]
    exact div_pos hδ_pos hden_pos
  obtain ⟨Q, hQ, hlower⟩ := E.exists_fejerPairCoeffLowerBound B hM_pos
  have hclose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M :=
    E.fejerCoeffBound_of_pairCoeffLowerBound hQ hlower
  refine ⟨Q, hQ, ?_⟩
  intro z
  have hmain :=
    E.abs_compactSmoothReal_sub_fReal_le_of_core_fejer_and_gCoeff_tail
      Q hQ z B hB0 (le_of_lt hM_pos) hclose hB_tail
  have hM_mul : M * SB ≤ δ := by
    dsimp [M]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    nlinarith
  calc
    |E.compactSmoothReal Q z - E.fReal z|
        ≤ 2 * δ + M * ∑ γ ∈ B, E.gCoeff γ := hmain
    _ = 2 * δ + M * SB := by rfl
    _ ≤ 2 * δ + δ := by
          nlinarith
    _ ≤ ε := by
          dsimp [δ]
          nlinarith

theorem exists_compactSmoothReal_uniform_close_and_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Bextra : Finset E.Group)
    {ε Mlarge : ℝ} (hε : 0 < ε) (hMlarge : 0 < Mlarge) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      E.FejerPairCoeffLowerBound Q Bextra Mlarge ∧
      ∀ z : E.CompactAddDual,
        |E.compactSmoothReal Q z - E.fReal z| ≤ ε := by
  classical
  let δ : ℝ := ε / 4
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let Gtot : ℝ := ∑' γ : E.Group, E.gCoeff γ
  have htail_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := by
    have h := (Metric.tendsto_nhds.mp E.summable_gCoeff.hasSum δ hδ_pos)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, Gtot] using hB
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp htail_event
  let Bcore : Finset E.Group := insert 0 B₀
  let B : Finset E.Group := Bcore ∪ Bextra
  have hB_ge : B ≥ B₀ := by
    intro γ hγ
    exact Finset.mem_union_left Bextra (Finset.mem_insert.mpr (Or.inr hγ))
  have hB_tail_lt : |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ :=
    hB₀ B hB_ge
  have hB_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ := by
    simpa [Gtot] using le_of_lt hB_tail_lt
  have hB0 : (0 : E.Group) ∈ B := by
    exact Finset.mem_union_left Bextra (Finset.mem_insert_self _ _)
  let SB : ℝ := ∑ γ ∈ B, E.gCoeff γ
  have hSB_nonneg : 0 ≤ SB := by
    dsimp [SB]
    exact Finset.sum_nonneg fun γ _hγ => E.gCoeff_nonneg γ
  let Mapprox : ℝ := δ / (SB + 1)
  have hden_pos : 0 < SB + 1 := by
    nlinarith
  have hMapprox_pos : 0 < Mapprox := by
    dsimp [Mapprox]
    exact div_pos hδ_pos hden_pos
  let Mchoose : ℝ := min Mapprox Mlarge
  have hMchoose_pos : 0 < Mchoose := by
    dsimp [Mchoose]
    exact lt_min hMapprox_pos hMlarge
  obtain ⟨Q, hQ, hlower⟩ := E.exists_fejerPairCoeffLowerBound B hMchoose_pos
  have hchoose_le_approx : Mchoose ≤ Mapprox := by
    dsimp [Mchoose]
    exact min_le_left _ _
  have hchoose_le_large : Mchoose ≤ Mlarge := by
    dsimp [Mchoose]
    exact min_le_right _ _
  have hclose_choose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ Mchoose :=
    E.fejerCoeffBound_of_pairCoeffLowerBound hQ hlower
  have hclose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ Mapprox := by
    intro γ hγ
    exact (hclose_choose γ hγ).trans hchoose_le_approx
  have hBextra :
      E.FejerPairCoeffLowerBound Q Bextra Mlarge := by
    intro γ hγ
    have hγB : γ ∈ B := Finset.mem_union_right Bcore hγ
    have hlow := hlower γ hγB
    have hle : 1 - Mlarge ≤ 1 - Mchoose := by linarith
    exact hle.trans hlow
  refine ⟨Q, hQ, hBextra, ?_⟩
  intro z
  have hmain :=
    E.abs_compactSmoothReal_sub_fReal_le_of_core_fejer_and_gCoeff_tail
      Q hQ z B hB0 (le_of_lt hMapprox_pos) hclose hB_tail
  have hM_mul : Mapprox * SB ≤ δ := by
    dsimp [Mapprox]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    nlinarith
  calc
    |E.compactSmoothReal Q z - E.fReal z|
        ≤ 2 * δ + Mapprox * ∑ γ ∈ B, E.gCoeff γ := hmain
    _ = 2 * δ + Mapprox * SB := by rfl
    _ ≤ 2 * δ + δ := by
          nlinarith
    _ ≤ ε := by
          dsimp [δ]
          nlinarith

lemma gReal_nonneg (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, 0 ≤ E.gReal z := by
  intro z
  rw [E.gReal_eq_tsum_gCoeff_mul_character_re E.summable_gCoeff z]
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  let T : ℝ := ∑' γ : E.Group, a γ
  change 0 ≤ T
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  have hsumA : Summable a := by
    simpa [a] using E.summable_gCoeff_mul_character_re E.summable_gCoeff z
  have hsumG : Summable E.gCoeff := E.summable_gCoeff
  let Gtot : ℝ := ∑' γ : E.Group, E.gCoeff γ
  have hA_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, a γ) - T| < δ := by
    have h := (Metric.tendsto_nhds.mp hsumA.hasSum δ hδ)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, T] using hB
  have hG_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := by
    have h := (Metric.tendsto_nhds.mp hsumG.hasSum δ hδ)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, Gtot] using hB
  obtain ⟨B, hB⟩ :=
    (Filter.eventually_atTop.mp (hA_event.and hG_event))
  have hB_self := hB B (le_rfl : B ≥ B)
  have hA_B : |(∑ γ ∈ B, a γ) - T| < δ := hB_self.1
  have hG_B : |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := hB_self.2
  let GB : ℝ := ∑ γ ∈ B, E.gCoeff γ
  have hGB_nonneg : 0 ≤ GB := by
    dsimp [GB]
    exact Finset.sum_nonneg (fun γ _hγ => E.gCoeff_nonneg γ)
  let M : ℝ := δ / ((GB + 1) * (δ + 1))
  have hden_pos : 0 < (GB + 1) * (δ + 1) := by positivity
  have hM_pos : 0 < M := by
    dsimp [M]
    exact div_pos hδ hden_pos
  have hM_lt : M < 1 := by
    dsimp [M]
    rw [div_lt_iff₀ hden_pos]
    nlinarith [hGB_nonneg, hδ]
  have hMGB_le : M * GB ≤ δ := by
    dsimp [M]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    have hden_ge : GB ≤ (GB + 1) * (δ + 1) := by
      nlinarith [hGB_nonneg, hδ]
    exact mul_le_mul_of_nonneg_left hden_ge (le_of_lt hδ)
  obtain ⟨Q, hQ, hlower⟩ := E.exists_fejerPairCoeffLowerBound B hM_pos
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let C : Finset E.Group := P.support \ B
  let D : Finset E.Group := B ∪ C
  have hD_ge : D ≥ B := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inl hγ)
  have hD_close := hB D hD_ge
  have hG_D : |(∑ γ ∈ D, E.gCoeff γ) - Gtot| < δ := hD_close.2
  have hdisj : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro γ hγB hγC
    exact (Finset.mem_sdiff.mp hγC).2 hγB
  have hsumD :
      (∑ γ ∈ D, E.gCoeff γ) =
        (∑ γ ∈ B, E.gCoeff γ) + ∑ γ ∈ C, E.gCoeff γ := by
    dsimp [D]
    rw [Finset.sum_union hdisj]
  have hC_lt : (∑ γ ∈ C, E.gCoeff γ) < 2 * δ := by
    have hD_upper : (∑ γ ∈ D, E.gCoeff γ) - Gtot < δ :=
      (abs_sub_lt_iff.mp hG_D).1
    have hB_lower : Gtot - (∑ γ ∈ B, E.gCoeff γ) < δ :=
      (abs_sub_lt_iff.mp hG_B).2
    linarith
  have hfinite :=
    E.sum_gCoeff_mul_character_re_ge_neg_of_fejerPairCoeffLowerBound
      Q B z hQ hM_lt hlower
  have hsumB_lower : -(3 * δ) < ∑ γ ∈ B, a γ := by
    dsimp [C, P, a, GB] at hfinite hC_lt hMGB_le
    nlinarith
  have hT_lower : -(4 * δ) < T := by
    have hA_lower : (∑ γ ∈ B, a γ) - T < δ :=
      (abs_sub_lt_iff.mp hA_B).1
    nlinarith
  have hδ_eq : 4 * δ = ε := by
    dsimp [δ]
    ring
  linarith

lemma norm_gComplex_le_tsum_gCoeff
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    ‖E.gComplex z‖ ≤ ∑' γ : E.Group, E.gCoeff γ := by
  have hnorm_summable :
      Summable fun γ : E.Group => ‖E.gComplexTerm γ z‖ := by
    simpa [E.norm_gComplexTerm_eq_gCoeff] using hsum
  unfold gComplex
  calc
    ‖∑' γ : E.Group, E.gComplexTerm γ z‖
        ≤ ∑' γ : E.Group, ‖E.gComplexTerm γ z‖ :=
      norm_tsum_le_tsum_norm hnorm_summable
    _ = ∑' γ : E.Group, E.gCoeff γ := by
      exact tsum_congr fun γ => E.norm_gComplexTerm_eq_gCoeff γ z

lemma gReal_le_tsum_gCoeff
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    E.gReal z ≤ ∑' γ : E.Group, E.gCoeff γ := by
  unfold gReal
  exact (Complex.re_le_norm (E.gComplex z)).trans
    (E.norm_gComplex_le_tsum_gCoeff hsum z)

lemma gReal_le_one (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, E.gReal z ≤ 1 := by
  intro z
  exact (E.gReal_le_tsum_gCoeff E.summable_gCoeff z).trans
    E.tsum_gCoeff_le_one

lemma fReal_nonneg (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, 0 ≤ E.fReal z := by
  intro z
  unfold fReal
  linarith [E.gReal_le_one z]

lemma fReal_le_one (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, E.fReal z ≤ 1 := by
  intro z
  unfold fReal
  linarith [E.gReal_nonneg z]

lemma levelOne_character_eq_one_of_gReal_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff)
    (htsum : (∑' γ : E.Group, E.gCoeff γ) = 1)
    {x : E.CompactAddDual} (hx : E.gReal x = 1)
    {γ : E.Group} (hγ : 0 < E.gCoeff γ) :
    E.addCharacterValue x γ = 1 := by
  classical
  have hre_le : ∀ δ : E.Group, (E.addCharacterValue x δ).re ≤ 1 :=
    fun δ => E.addCharacterValue_re_le_one x δ
  have hmul_summable := E.summable_gCoeff_mul_character_re hsum x
  have hdef_nonneg :
      ∀ δ : E.Group,
        0 ≤ E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re := by
    intro δ
    have hcoeff_nonneg : 0 ≤ E.gCoeff δ := E.gCoeff_nonneg δ
    have hfactor_nonneg : 0 ≤ 1 - (E.addCharacterValue x δ).re := by
      linarith [hre_le δ]
    nlinarith [mul_nonneg hcoeff_nonneg hfactor_nonneg]
  let dNN : E.Group → NNReal := fun δ =>
    ⟨E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re,
      hdef_nonneg δ⟩
  have hdef_summable :
      Summable fun δ : E.Group =>
        (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re) := by
    exact hsum.sub hmul_summable
  have hdNN_summable : Summable dNN := by
    rw [← NNReal.summable_coe]
    simpa [dNN] using hdef_summable
  have hdef_tsum_zero :
      (∑' δ : E.Group,
        (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re)) = 0 := by
    have hsub :=
      hsum.hasSum.sub hmul_summable.hasSum
    have hsub_tsum :
        (∑' δ : E.Group,
          (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re)) =
          (∑' δ : E.Group, E.gCoeff δ) -
            (∑' δ : E.Group,
              E.gCoeff δ * (E.addCharacterValue x δ).re) := by
      exact hsub.tsum_eq
    rw [hsub_tsum]
    rw [htsum, ← E.gReal_eq_tsum_gCoeff_mul_character_re hsum x, hx]
    ring
  have hdNN_tsum_zero : (∑' δ : E.Group, dNN δ) = 0 := by
    apply NNReal.eq
    rw [NNReal.coe_tsum]
    simpa [dNN] using hdef_tsum_zero
  by_contra hne
  have hre_lt : (E.addCharacterValue x γ).re < 1 := by
    have hle := hre_le γ
    by_contra hnot
    have hre_eq : (E.addCharacterValue x γ).re = 1 := le_antisymm hle (not_lt.mp hnot)
    exact hne (E.addCharacterValue_eq_one_of_re_eq_one x γ hre_eq)
  have hdNN_pos : 0 < dNN γ := by
    rw [show dNN γ =
        ⟨E.gCoeff γ - E.gCoeff γ * (E.addCharacterValue x γ).re,
          hdef_nonneg γ⟩ by rfl]
    rw [← NNReal.coe_pos]
    change 0 < E.gCoeff γ - E.gCoeff γ * (E.addCharacterValue x γ).re
    nlinarith [mul_lt_mul_of_pos_left hre_lt hγ]
  have htsum_pos : 0 < ∑' δ : E.Group, dNN δ :=
    NNReal.tsum_pos hdNN_summable γ hdNN_pos
  exact (ne_of_gt htsum_pos) hdNN_tsum_zero

/-- Conditional level-one subgroup closure for the compact complement kernel.

The remaining positive-definite equality case has to prove `hchars`: if
`gReal x = 1`, then every character with positive coefficient is trivial at
`x`.  Once that is known, closure under subtraction is just character algebra
and termwise equality of the Fourier series. -/
lemma levelOneSubgroupKernel_gReal_of_levelOne_chars
    (E : CayleyExtraction S)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1)
    (hchars :
      ∀ x : E.CompactAddDual, E.gReal x = 1 →
        ∀ γ : E.Group, 0 < E.gCoeff γ →
          E.addCharacterValue x γ = 1) :
    LevelOneSubgroupKernel E.gReal where
  map_zero := hg0
  sub_mem := by
    intro x y hx hy
    have hcomplex :
        E.gComplex (x - y) = E.gComplex (0 : E.CompactAddDual) := by
      unfold gComplex
      refine tsum_congr ?_
      intro γ
      by_cases hpos : 0 < E.gCoeff γ
      · have hxγ : E.addCharacterValue x γ = 1 := hchars x hx γ hpos
        have hyγ : E.addCharacterValue y γ = 1 := hchars y hy γ hpos
        have hxyγ : E.addCharacterValue (x - y) γ = 1 := by
          rw [sub_eq_add_neg, E.addCharacterValue_add_point,
            E.addCharacterValue_neg_point, hxγ, hyγ]
          simp
        unfold gComplexTerm
        simp [hxyγ]
      · have hzero : E.gCoeff γ = 0 :=
          le_antisymm (not_lt.mp hpos) (E.gCoeff_nonneg γ)
        simp [gComplexTerm, hzero]
    change (E.gComplex (x - y)).re = 1
    rw [hcomplex]
    simpa [gReal] using hg0

lemma levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    LevelOneSubgroupKernel E.gReal := by
  have htsum : (∑' γ : E.Group, E.gCoeff γ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  exact E.levelOneSubgroupKernel_gReal_of_levelOne_chars hg0
    (fun x hx γ hpos =>
      E.levelOne_character_eq_one_of_gReal_eq_one hsum htsum hx hpos)

lemma exists_ne_zero_gCoeff_pos_of_gReal_zero_eq_one
    (E : CayleyExtraction S) (hη : 0 < η)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    ∃ γ : E.Group, γ ≠ 0 ∧ 0 < E.gCoeff γ := by
  classical
  by_contra hnone
  push_neg at hnone
  have hzero_nonzero : ∀ γ : E.Group, γ ≠ 0 → E.gCoeff γ = 0 := by
    intro γ hγ
    exact le_antisymm (hnone γ hγ) (E.gCoeff_nonneg γ)
  have htsum_single :
      (∑' γ : E.Group, E.gCoeff γ) = E.gCoeff 0 := by
    exact tsum_eq_single (0 : E.Group) (by
      intro γ hγ
      exact hzero_nonzero γ hγ)
  have htsum_one :
      (∑' γ : E.Group, E.gCoeff γ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  have hcoeff_zero_one : E.gCoeff 0 = 1 := by
    rw [← htsum_single, htsum_one]
  have hle := E.gCoeff_zero_le_one_sub_eta
  nlinarith

lemma levelOneAddSubgroup_gReal_not_finiteIndex_of_gReal_zero_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff) (hη : 0 < η)
    {hg_level : LevelOneSubgroupKernel E.gReal}
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    ¬ (levelOneAddSubgroup E.gReal hg_level :
      AddSubgroup E.CompactAddDual).FiniteIndex := by
  classical
  intro hfinite
  let H : AddSubgroup E.CompactAddDual :=
    levelOneAddSubgroup E.gReal hg_level
  obtain ⟨γ, hγ_ne, hγ_pos⟩ :=
    E.exists_ne_zero_gCoeff_pos_of_gReal_zero_eq_one hη hg0
  have htsum :
      (∑' δ : E.Group, E.gCoeff δ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  have hchar_on_H :
      ∀ x : E.CompactAddDual, x ∈ H → E.addCharacterValue x γ = 1 := by
    intro x hx
    exact E.levelOne_character_eq_one_of_gReal_eq_one hsum htsum
      (mem_levelOneAddSubgroup.mp hx) hγ_pos
  let N : ℕ := Nat.factorial H.index
  have hN_pos : 0 < N := Nat.factorial_pos H.index
  have hN_mem_H : ∀ x : E.CompactAddDual, N • x ∈ H := by
    intro x
    exact AddSubgroup.nsmul_mem_of_index_ne_zero_of_dvd
      (H := H) hfinite.index_ne_zero x
      (n := N) (fun m hm_pos hm_le => Nat.dvd_factorial hm_pos hm_le)
  have hchar_nsmul_all :
      ∀ x : E.CompactAddDual, E.addCharacterValue x (N • γ) = 1 := by
    intro x
    have hxchar : E.addCharacterValue (N • x) γ = 1 :=
      hchar_on_H (N • x) (hN_mem_H x)
    rw [E.addCharacterValue_nsmul_point] at hxchar
    rw [E.addCharacterValue_nsmul_frequency]
    exact hxchar
  have hNγ_zero : N • γ = 0 := by
    by_contra hNγ_ne
    rcases E.exists_dual_point_ne_one hNγ_ne with ⟨x, hx⟩
    exact hx (hchar_nsmul_all x)
  have hγ_zero : γ = 0 := by
    have hinj := nsmul_right_injective (M := E.Group) (Nat.ne_of_gt hN_pos)
    exact hinj (by simpa using hNγ_zero)
  exact hγ_ne hγ_zero

lemma fReal_nonneg_of_gReal_le_one
    (E : CayleyExtraction S)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1) :
    ∀ x : E.CompactAddDual, 0 ≤ E.fReal x := by
  intro x
  unfold fReal
  linarith [hg_le x]

lemma fReal_le_one_of_gReal_nonneg
    (E : CayleyExtraction S)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x) :
    ∀ x : E.CompactAddDual, E.fReal x ≤ 1 := by
  intro x
  unfold fReal
  linarith [hg_nonneg x]

theorem compact_limit_cliqueDensity_pos_of_gReal_bounds
    (E : CayleyExtraction S)
    (_hℓ : 2 ≤ ℓ) (hη : 0 < η)
    [ConnectedSpace E.CompactAddDual]
    (hsum : Summable E.gCoeff)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal := by
  classical
  letI : CompactSpace E.CompactAddDual := E.compactAddDual_compactSpace
  letI : T2Space E.CompactAddDual := E.compactAddDual_t2Space
  letI : IsTopologicalAddGroup E.CompactAddDual :=
    E.compactAddDual_isTopologicalAddGroup
  have hbranch :
      E.gReal (0 : E.CompactAddDual) < 1 ∨
        LevelOneSubgroupKernel E.gReal := by
    by_cases hlt : E.gReal (0 : E.CompactAddDual) < 1
    · exact Or.inl hlt
    · have hg0 : E.gReal (0 : E.CompactAddDual) = 1 :=
        le_antisymm (hg_le 0) (not_lt.mp hlt)
      exact Or.inr (E.levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one hsum hg0)
  simpa [fReal] using
    continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel
      E.haar ℓ E.gReal (E.gReal_continuous hsum)
      hg_nonneg hg_le hη (E.integral_gReal_le_one_sub_eta hsum) hbranch

/-- Variant of `compact_limit_cliqueDensity_pos_of_gReal_bounds` that replaces
connectedness of the whole compact dual by the exact infinite-index certificate
for every level-one subgroup structure on `E.gReal`. -/
theorem compact_limit_cliqueDensity_pos_of_gReal_bounds_not_finiteIndex
    (E : CayleyExtraction S)
    (_hℓ : 2 ≤ ℓ) (_hη : 0 < η)
    (hsum : Summable E.gCoeff)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1)
    (hlevel_not_finiteIndex :
      ∀ hg_level : LevelOneSubgroupKernel E.gReal,
        ¬ (levelOneAddSubgroup E.gReal hg_level :
          AddSubgroup E.CompactAddDual).FiniteIndex) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal := by
  classical
  letI : CompactSpace E.CompactAddDual := E.compactAddDual_compactSpace
  letI : T2Space E.CompactAddDual := E.compactAddDual_t2Space
  letI : IsTopologicalAddGroup E.CompactAddDual :=
    E.compactAddDual_isTopologicalAddGroup
  have hbranch :
      E.gReal (0 : E.CompactAddDual) < 1 ∨
        ∃ hg_level : LevelOneSubgroupKernel E.gReal,
          ¬ (levelOneAddSubgroup E.gReal hg_level :
            AddSubgroup E.CompactAddDual).FiniteIndex := by
    by_cases hlt : E.gReal (0 : E.CompactAddDual) < 1
    · exact Or.inl hlt
    · have hg0 : E.gReal (0 : E.CompactAddDual) = 1 :=
        le_antisymm (hg_le 0) (not_lt.mp hlt)
      let hg_level : LevelOneSubgroupKernel E.gReal :=
        E.levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one hsum hg0
      exact Or.inr ⟨hg_level, hlevel_not_finiteIndex hg_level⟩
  simpa [fReal] using
    continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel_not_finiteIndex
      E.haar ℓ E.gReal (E.gReal_continuous hsum)
      hg_nonneg hg_le hbranch

/-- Compact positive clique-density endpoint with connectedness replaced by the
finite-index contradiction proved from extraction torsion-freeness and the mean
gap.  The remaining analytic input is the pointwise bound `0 ≤ gReal ≤ 1` and
summability of `gCoeff`. -/
theorem compact_limit_cliqueDensity_pos_of_gReal_bounds_infiniteIndex
    (E : CayleyExtraction S)
    (_hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (hsum : Summable E.gCoeff)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal := by
  classical
  letI : CompactSpace E.CompactAddDual := E.compactAddDual_compactSpace
  letI : T2Space E.CompactAddDual := E.compactAddDual_t2Space
  letI : IsTopologicalAddGroup E.CompactAddDual :=
    E.compactAddDual_isTopologicalAddGroup
  have hbranch :
      E.gReal (0 : E.CompactAddDual) < 1 ∨
        ∃ hg_level : LevelOneSubgroupKernel E.gReal,
          ¬ (levelOneAddSubgroup E.gReal hg_level :
            AddSubgroup E.CompactAddDual).FiniteIndex := by
    by_cases hlt : E.gReal (0 : E.CompactAddDual) < 1
    · exact Or.inl hlt
    · have hg0 : E.gReal (0 : E.CompactAddDual) = 1 :=
        le_antisymm (hg_le 0) (not_lt.mp hlt)
      let hg_level : LevelOneSubgroupKernel E.gReal :=
        E.levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one hsum hg0
      have hnot :
          ¬ (levelOneAddSubgroup E.gReal hg_level :
            AddSubgroup E.CompactAddDual).FiniteIndex :=
        E.levelOneAddSubgroup_gReal_not_finiteIndex_of_gReal_zero_eq_one
          hsum hη hg0
      exact Or.inr ⟨hg_level, hnot⟩
  simpa [fReal] using
    continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel_not_finiteIndex
      E.haar ℓ E.gReal (E.gReal_continuous hsum)
      hg_nonneg hg_le hbranch

/-- Compact positive clique-density endpoint with summability and the upper
pointwise bound already discharged. -/
theorem compact_limit_cliqueDensity_pos_of_gReal_nonneg
    (E : CayleyExtraction S)
    (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal :=
  E.compact_limit_cliqueDensity_pos_of_gReal_bounds_infiniteIndex
    hℓ hη E.summable_gCoeff hg_nonneg E.gReal_le_one

/-- Compact positive clique-density endpoint for the compact-Cayley extraction
kernel, with all pointwise bounds discharged. -/
theorem compact_limit_cliqueDensity_pos
    (E : CayleyExtraction S)
    (hℓ : 2 ≤ ℓ) (hη : 0 < η) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal :=
  E.compact_limit_cliqueDensity_pos_of_gReal_nonneg hℓ hη E.gReal_nonneg

theorem compactSmoothReal_cliqueDensity_pos_of_close
    (E : CayleyExtraction S) (Q : Finset E.Group) {κ : ℝ}
    (hκ_nonneg : 0 ≤ κ) (hκ_le_one : κ ≤ 1)
    (hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ)
    (hmargin :
      (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card <
        continuousCliqueDensity E.haar ℓ E.fReal) :
    0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let C : ℝ := (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
    (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  have hf_abs : ∀ z : E.CompactAddDual, |E.fReal z| ≤ 2 := by
    intro z
    have hnonneg := E.fReal_nonneg z
    have hle := E.fReal_le_one z
    rw [abs_of_nonneg hnonneg]
    linarith
  have hs_abs : ∀ z : E.CompactAddDual, |E.compactSmoothReal Q z| ≤ 2 := by
    intro z
    have hf_abs_one : |E.fReal z| ≤ 1 := by
      have hnonneg := E.fReal_nonneg z
      have hle := E.fReal_le_one z
      rw [abs_of_nonneg hnonneg]
      exact hle
    have hclose' : |E.compactSmoothReal Q z - E.fReal z| ≤ κ := by
      simpa [abs_sub_comm] using hclose z
    calc
      |E.compactSmoothReal Q z|
          = |(E.compactSmoothReal Q z - E.fReal z) + E.fReal z| := by ring_nf
      _ ≤ |E.compactSmoothReal Q z - E.fReal z| + |E.fReal z| := abs_add_le _ _
      _ ≤ κ + 1 := add_le_add hclose' hf_abs_one
      _ ≤ 2 := by linarith
  have hdiff :=
    continuousCliqueDensity_lipschitz_sup_two_pow
      E.haar ℓ
      (E.fReal_continuous E.summable_gCoeff).measurable
      (E.compactSmoothReal_continuous Q).measurable
      hf_abs hs_abs hκ_nonneg hclose
  have hlow :
      continuousCliqueDensity E.haar ℓ E.fReal -
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) ≤ C := by
    exact (le_abs_self _).trans (by simpa [C] using hdiff)
  have hC_lt :
      C < continuousCliqueDensity E.haar ℓ E.fReal := by
    simpa [C] using hmargin
  linarith

theorem compactSmoothReal_cliqueDensity_ge_sub_error_of_close
    (E : CayleyExtraction S) (Q : Finset E.Group) {κ : ℝ}
    (hκ_nonneg : 0 ≤ κ) (hκ_le_one : κ ≤ 1)
    (hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ) :
    continuousCliqueDensity E.haar ℓ E.fReal -
        ((((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card) ≤
      continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let C : ℝ := (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
    (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  have hf_abs : ∀ z : E.CompactAddDual, |E.fReal z| ≤ 2 := by
    intro z
    have hnonneg := E.fReal_nonneg z
    have hle := E.fReal_le_one z
    rw [abs_of_nonneg hnonneg]
    linarith
  have hs_abs : ∀ z : E.CompactAddDual, |E.compactSmoothReal Q z| ≤ 2 := by
    intro z
    have hf_abs_one : |E.fReal z| ≤ 1 := by
      have hnonneg := E.fReal_nonneg z
      have hle := E.fReal_le_one z
      rw [abs_of_nonneg hnonneg]
      exact hle
    have hclose' : |E.compactSmoothReal Q z - E.fReal z| ≤ κ := by
      simpa [abs_sub_comm] using hclose z
    calc
      |E.compactSmoothReal Q z|
          = |(E.compactSmoothReal Q z - E.fReal z) + E.fReal z| := by ring_nf
      _ ≤ |E.compactSmoothReal Q z - E.fReal z| + |E.fReal z| := abs_add_le _ _
      _ ≤ κ + 1 := add_le_add hclose' hf_abs_one
      _ ≤ 2 := by linarith
  have hdiff :=
    continuousCliqueDensity_lipschitz_sup_two_pow
      E.haar ℓ
      (E.fReal_continuous E.summable_gCoeff).measurable
      (E.compactSmoothReal_continuous Q).measurable
      hf_abs hs_abs hκ_nonneg hclose
  have hlow :
      continuousCliqueDensity E.haar ℓ E.fReal -
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) ≤ C := by
    exact (le_abs_self _).trans (by simpa [C] using hdiff)
  have htarget :
      continuousCliqueDensity E.haar ℓ E.fReal - C ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    linarith
  simpa [C] using htarget

theorem exists_compactSmoothReal_cliqueDensity_pos
    (E : CayleyExtraction S) (hℓ : 2 ≤ ℓ) (hη : 0 < η) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let ρ : ℝ := continuousCliqueDensity E.haar ℓ E.fReal
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact E.compact_limit_cliqueDensity_pos hℓ hη
  let edgeCount : ℝ := ((continuousCliqueEdgePairs ℓ).card : ℝ)
  let P : ℝ := (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  let A : ℝ := (edgeCount + 1) * (P + 1)
  have hedge_nonneg : 0 ≤ edgeCount := by
    dsimp [edgeCount]
    exact Nat.cast_nonneg _
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    nlinarith
  let κ : ℝ := min 1 (ρ / (2 * A))
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact lt_min zero_lt_one (div_pos hρ_pos (mul_pos two_pos hA_pos))
  have hκ_nonneg : 0 ≤ κ := le_of_lt hκ_pos
  have hκ_le_one : κ ≤ 1 := by
    dsimp [κ]
    exact min_le_left _ _
  obtain ⟨Q, hQ, hclose₀⟩ := E.exists_compactSmoothReal_uniform_close hκ_pos
  have hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ := by
    intro z
    simpa [abs_sub_comm] using hclose₀ z
  have hκA_le : κ * A ≤ ρ / 2 := by
    have hκ_le : κ ≤ ρ / (2 * A) := by
      dsimp [κ]
      exact min_le_right _ _
    calc
      κ * A ≤ (ρ / (2 * A)) * A :=
        mul_le_mul_of_nonneg_right hκ_le (le_of_lt hA_pos)
      _ = ρ / 2 := by
        field_simp [ne_of_gt hA_pos]
  have hedgeP_le_A : edgeCount * P ≤ A := by
    dsimp [A]
    nlinarith
  have hmargin :
      (edgeCount * κ) * P < ρ := by
    have hC_le : (edgeCount * κ) * P ≤ κ * A := by
      have h := mul_le_mul_of_nonneg_left hedgeP_le_A hκ_nonneg
      nlinarith
    nlinarith
  refine ⟨Q, hQ, ?_⟩
  exact E.compactSmoothReal_cliqueDensity_pos_of_close Q
    hκ_nonneg hκ_le_one hclose (by
      simpa [edgeCount, P, ρ] using hmargin)

theorem exists_compactSmoothReal_cliqueDensity_pos_and_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (Bextra : Finset E.Group) {Mlarge : ℝ} (hMlarge : 0 < Mlarge) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      E.FejerPairCoeffLowerBound Q Bextra Mlarge ∧
      0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) ∧
      continuousCliqueDensity E.haar ℓ E.fReal / 2 ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let ρ : ℝ := continuousCliqueDensity E.haar ℓ E.fReal
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact E.compact_limit_cliqueDensity_pos hℓ hη
  let edgeCount : ℝ := ((continuousCliqueEdgePairs ℓ).card : ℝ)
  let P : ℝ := (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  let A : ℝ := (edgeCount + 1) * (P + 1)
  have hedge_nonneg : 0 ≤ edgeCount := by
    dsimp [edgeCount]
    exact Nat.cast_nonneg _
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    nlinarith
  let κ : ℝ := min 1 (ρ / (2 * A))
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact lt_min zero_lt_one (div_pos hρ_pos (mul_pos two_pos hA_pos))
  have hκ_nonneg : 0 ≤ κ := le_of_lt hκ_pos
  have hκ_le_one : κ ≤ 1 := by
    dsimp [κ]
    exact min_le_left _ _
  obtain ⟨Q, hQ, hBextra, hclose₀⟩ :=
    E.exists_compactSmoothReal_uniform_close_and_fejerPairCoeffLowerBound
      Bextra hκ_pos hMlarge
  have hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ := by
    intro z
    simpa [abs_sub_comm] using hclose₀ z
  have hκA_le : κ * A ≤ ρ / 2 := by
    have hκ_le : κ ≤ ρ / (2 * A) := by
      dsimp [κ]
      exact min_le_right _ _
    calc
      κ * A ≤ (ρ / (2 * A)) * A :=
        mul_le_mul_of_nonneg_right hκ_le (le_of_lt hA_pos)
      _ = ρ / 2 := by
        field_simp [ne_of_gt hA_pos]
  have hedgeP_le_A : edgeCount * P ≤ A := by
    dsimp [A]
    nlinarith
  have hmargin :
      (edgeCount * κ) * P < ρ := by
    have hC_le : (edgeCount * κ) * P ≤ κ * A := by
      have h := mul_le_mul_of_nonneg_left hedgeP_le_A hκ_nonneg
      nlinarith
    nlinarith
  have hge :
      continuousCliqueDensity E.haar ℓ E.fReal / 2 ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    have hlower :=
      E.compactSmoothReal_cliqueDensity_ge_sub_error_of_close Q
        hκ_nonneg hκ_le_one hclose
    have hC_le :
        (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
            (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card ≤
          ρ / 2 := by
      have hC_le_A : (edgeCount * κ) * P ≤ κ * A := by
        have h := mul_le_mul_of_nonneg_left hedgeP_le_A hκ_nonneg
        nlinarith
      simpa [edgeCount, P] using hC_le_A.trans hκA_le
    dsimp [ρ] at hC_le
    linarith
  have hpos :
      0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) :=
    lt_of_lt_of_le (half_pos hρ_pos) (by simpa [ρ] using hge)
  refine ⟨Q, hQ, hBextra, hpos, hge⟩

end CayleyExtraction

end

end Erdos42.CompactCayley
