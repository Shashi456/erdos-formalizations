/-
Erdős Problem 42 — finite Fejér smoothing for compact-Cayley extraction.
-/

import Erdos.P42.CompactCayley.Fejer

namespace Erdos42.CompactCayley

open Filter Complex MeasureTheory
open scoped BigOperators Classical Topology

noncomputable section

/-- Normalized convolution on `ZMod p`. -/
noncomputable def avgConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun x => avgZMod fun y => f (x - y) * g y

lemma stdAddChar_neg_mul_split_sub
    {p : ℕ} [NeZero p] (x y r : ZMod p) :
    ZMod.stdAddChar (-(x * r)) =
      ZMod.stdAddChar (-((x - y) * r)) *
        ZMod.stdAddChar (-(y * r)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

lemma normalizedDftFunction_eq_avgZMod {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      avgZMod fun x : ZMod p => ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction_eq_sum]
  rfl

lemma avgZMod_comm {p : ℕ} [NeZero p] (F : ZMod p → ZMod p → ℂ) :
    avgZMod (fun x => avgZMod fun y => F x y) =
      avgZMod (fun y => avgZMod fun x => F x y) := by
  unfold avgZMod
  calc
    ((p : ℂ)⁻¹) * ∑ x : ZMod p, ((p : ℂ)⁻¹) * ∑ y : ZMod p, F x y
        = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) *
            ∑ x : ZMod p, ∑ y : ZMod p, F x y := by
          rw [← Finset.mul_sum]
          ring
    _ = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) *
          ∑ y : ZMod p, ∑ x : ZMod p, F x y := by
          rw [Finset.sum_comm]
    _ = ((p : ℂ)⁻¹) * ∑ y : ZMod p, ((p : ℂ)⁻¹) *
          ∑ x : ZMod p, F x y := by
          rw [← Finset.mul_sum]
          ring

lemma avgZMod_sub_right {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (y : ZMod p) :
    avgZMod (fun x => f (x - y)) = avgZMod f := by
  unfold avgZMod
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Fintype.sum_equiv (Equiv.addRight (-y)) _ _ ?_
  intro x
  simp [sub_eq_add_neg]

lemma avgZMod_re {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (avgZMod f).re = ((p : ℝ)⁻¹) * ∑ x : ZMod p, (f x).re := by
  unfold avgZMod
  rw [show ((p : ℂ)⁻¹) = (((p : ℝ)⁻¹ : ℝ) : ℂ) by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]]
  simp [Complex.mul_re]

lemma avgZMod_re_le {p : ℕ} [NeZero p] {f g : ZMod p → ℂ}
    (h : ∀ x, (f x).re ≤ (g x).re) :
    (avgZMod f).re ≤ (avgZMod g).re := by
  rw [avgZMod_re f, avgZMod_re g]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun x _hx => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg p))

/-- Normalized DFT sends normalized convolution to pointwise multiplication. -/
lemma normalizedDftFunction_avgConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (avgConvolution f g) r =
      normalizedDftFunction f r * normalizedDftFunction g r := by
  classical
  rw [normalizedDftFunction_eq_avgZMod]
  unfold avgConvolution
  calc
    avgZMod
        (fun x : ZMod p =>
          ZMod.stdAddChar (-(x * r)) *
            avgZMod (fun y : ZMod p => f (x - y) * g y))
        =
      avgZMod
        (fun x : ZMod p =>
          avgZMod
            (fun y : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))) := by
          congr 1
          funext x
          rw [avgZMod_const_mul]
    _ =
      avgZMod
        (fun y : ZMod p =>
          avgZMod
            (fun x : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))) := by
          exact avgZMod_comm
            (fun x y : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))
    _ =
      avgZMod
        (fun y : ZMod p =>
          normalizedDftFunction f r *
            (ZMod.stdAddChar (-(y * r)) * g y)) := by
          congr 1
          funext y
          calc
            avgZMod
                (fun x : ZMod p =>
                  ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))
                =
              avgZMod
                (fun x : ZMod p =>
                  (ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) *
                    (ZMod.stdAddChar (-(y * r)) * g y)) := by
                congr 1
                funext x
                rw [stdAddChar_neg_mul_split_sub x y r]
                ring
            _ =
              avgZMod
                (fun x : ZMod p =>
                  ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) *
                (ZMod.stdAddChar (-(y * r)) * g y) := by
                rw [avgZMod_mul_const]
            _ =
              normalizedDftFunction f r *
                (ZMod.stdAddChar (-(y * r)) * g y) := by
                have hshift :
                    avgZMod
                        (fun x : ZMod p =>
                          ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) =
                      normalizedDftFunction f r := by
                  rw [avgZMod_sub_right
                    (fun z : ZMod p => ZMod.stdAddChar (-(z * r)) * f z) y]
                  rw [← normalizedDftFunction_eq_avgZMod]
                rw [hshift]
    _ = normalizedDftFunction f r * normalizedDftFunction g r := by
          rw [avgZMod_const_mul]
          rw [← normalizedDftFunction_eq_avgZMod]

lemma norm_normalizedDftFunction_le_norm_average
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (r : ZMod p) :
    ‖normalizedDftFunction f r‖ ≤
      ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ := by
  rw [normalizedDftFunction_eq_avgZMod]
  unfold avgZMod
  calc
    ‖((p : ℂ)⁻¹) *
        ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x‖
        = ‖((p : ℂ)⁻¹)‖ *
            ‖∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x‖ := by
          rw [norm_mul]
    _ ≤ ‖((p : ℂ)⁻¹)‖ *
        ∑ x : ZMod p, ‖ZMod.stdAddChar (-(x * r)) * f x‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖((p : ℂ)⁻¹)‖ * ∑ x : ZMod p, ‖f x‖ := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [norm_mul, AddChar.norm_apply, one_mul]
    _ = ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ := by
          rw [norm_inv, Complex.norm_natCast]

lemma norm_avgConvolution_indicator_le_of_kernel_norm_average_le_one
    {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (K : ZMod p → ℂ)
    (hK_norm_avg : ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ ≤ 1) :
    ∀ x : ZMod p, ‖avgConvolution (indicatorC T) K x‖ ≤ 1 := by
  intro x
  unfold avgConvolution avgZMod
  have hsum :
      ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖ ≤
        ∑ y : ZMod p, ‖K y‖ := by
    calc
      ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖
          ≤ ∑ y : ZMod p, ‖indicatorC T (x - y) * K y‖ := norm_sum_le _ _
      _ ≤ ∑ y : ZMod p, ‖K y‖ := by
          refine Finset.sum_le_sum ?_
          intro y _hy
          rw [norm_mul]
          have hind : ‖indicatorC T (x - y)‖ ≤ 1 := by
            classical
            by_cases h : x - y ∈ T
            · simp [indicatorC, h]
            · simp [indicatorC, h]
          exact mul_le_of_le_one_left (norm_nonneg _) hind
  calc
    ‖(↑p)⁻¹ * ∑ y : ZMod p, indicatorC T (x - y) * K y‖
        = ‖((p : ℂ)⁻¹)‖ *
            ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖ := by
          rw [norm_mul]
    _ ≤ ‖((p : ℂ)⁻¹)‖ * ∑ y : ZMod p, ‖K y‖ :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ := by
          rw [norm_inv, Complex.norm_natCast]
    _ ≤ 1 := hK_norm_avg

lemma kernel_norm_average_eq_one_of_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1) :
    ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ = 1 := by
  have hsum_eq :
      (∑ y : ZMod p, K y) =
        ((∑ y : ZMod p, (K y).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.re_sum]
    · simp [Complex.im_sum, hK_im]
  have havg_re :
      ((p : ℝ)⁻¹) * ∑ y : ZMod p, (K y).re = 1 := by
    have h := congrArg Complex.re hK_avg
    unfold avgZMod at h
    rw [hsum_eq] at h
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv] at h
    simpa [Complex.ofReal_mul] using h
  calc
    ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖
        = ((p : ℝ)⁻¹) * ∑ y : ZMod p, (K y).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro y _hy
          have hnorm := (Complex.abs_re_eq_norm).mpr (hK_im y)
          rw [← hnorm, abs_of_nonneg (hK_nonneg y)]
    _ = 1 := havg_re

lemma norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1) :
    ∀ x : ZMod p, ‖avgConvolution (indicatorC T) K x‖ ≤ 1 :=
  norm_avgConvolution_indicator_le_of_kernel_norm_average_le_one T K
    ((kernel_norm_average_eq_one_of_real_nonneg_avg_one
      K hK_nonneg hK_im hK_avg).le)

lemma norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1)
    (r : ZMod p) :
    ‖normalizedDftFunction K r‖ ≤ 1 :=
  (norm_normalizedDftFunction_le_norm_average K r).trans_eq
    (kernel_norm_average_eq_one_of_real_nonneg_avg_one
      K hK_nonneg hK_im hK_avg)

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Finite Fejér-smoothed Cayley allowed kernel `1_T * K_Q`. -/
noncomputable def finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    ZMod (S.p (E.φ n)) → ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgConvolution (indicatorC (S.T (E.φ n))) (E.finiteFejerKernel Q n)

/-- Finite average of the complement indicator `1 - 1_T` weighted by a Fejér
kernel.  This is the finite inequality input for summability of `gCoeff`. -/
noncomputable def finiteComplementFejerAverage
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    (1 - indicatorC (S.T (E.φ n)) x) * E.finiteFejerKernel Q n x

/-- Finite average of the complement indicator `1 - 1_T` weighted by an
arbitrary lifted trigonometric polynomial. -/
noncomputable def finiteComplementWeightedAverage
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    (1 - indicatorC (S.T (E.φ n)) x) * TrigPoly.evalFinite P n x

lemma finiteComplementWeightedAverage_eventually_eq
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    ∀ᶠ n in atTop,
      E.finiteComplementWeightedAverage P n =
        TrigPoly.finiteAverage P n -
          TrigPoly.indicatorWeightedFiniteAverage P n := by
  filter_upwards with n
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementWeightedAverage TrigPoly.finiteAverage
    TrigPoly.indicatorWeightedFiniteAverage
  calc
    avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        (1 - indicatorC (S.T (E.φ n)) x) * TrigPoly.evalFinite P n x)
        =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x -
          indicatorC (S.T (E.φ n)) x * TrigPoly.evalFinite P n x) := by
        congr 1
        funext x
        ring
    _ =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x) -
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x * TrigPoly.evalFinite P n x) := by
        unfold avgZMod
        rw [Finset.sum_sub_distrib]
        ring

lemma finiteComplementWeightedAverage_tendsto
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto
      (fun n => E.finiteComplementWeightedAverage P n)
      atTop
      (𝓝 (TrigPoly.compactAverage P -
        TrigPoly.indicatorCoeffFunctional P)) := by
  have hdiff :=
    (TrigPoly.finiteAverage_tendsto_compactAverage E P).sub
      (TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional E P)
  exact hdiff.congr'
    (by
      filter_upwards [E.finiteComplementWeightedAverage_eventually_eq P] with n hn
      exact hn.symm)

lemma finiteComplementWeightedAverage_re_nonneg
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    (hP : ∀ x : ZMod (S.p (E.φ n)),
      0 ≤ (TrigPoly.evalFinite P n x).re) :
    0 ≤ (E.finiteComplementWeightedAverage P n).re := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [finiteComplementWeightedAverage, avgZMod_re]
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
  refine Finset.sum_nonneg ?_
  intro x _hx
  by_cases hx : x ∈ S.T (E.φ n)
  · simp [indicatorC, hx]
  · simpa [indicatorC, hx] using hP x

lemma shiftedFejer_complementFunctional_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    0 ≤
      (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re := by
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  have htendsto :=
    E.finiteComplementWeightedAverage_tendsto P
  have htendsto_re :=
    Complex.continuous_re.tendsto
      (TrigPoly.compactAverage P - TrigPoly.indicatorCoeffFunctional P) |>.comp
      htendsto
  have hnonneg :
      ∀ᶠ n in atTop, 0 ≤ (E.finiteComplementWeightedAverage P n).re := by
    filter_upwards [E.shiftedFejerTrigPoly_evalFinite_eventually_eq Q z] with n hn
    exact E.finiteComplementWeightedAverage_re_nonneg P n (by
      intro x
      simpa [P, hn x] using E.shiftedFiniteFejerKernel_re_nonneg Q z n x)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htendsto_re hnonneg

lemma finiteComplementFejerAverage_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      E.finiteComplementFejerAverage Q n =
        TrigPoly.finiteAverage (E.fejerTrigPoly Q) n -
          TrigPoly.indicatorWeightedFiniteAverage (E.fejerTrigPoly Q) n := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementFejerAverage TrigPoly.finiteAverage
    TrigPoly.indicatorWeightedFiniteAverage
  calc
    avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        (1 - indicatorC (S.T (E.φ n)) x) *
          E.finiteFejerKernel Q n x)
        =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x -
          indicatorC (S.T (E.φ n)) x *
            TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) := by
        congr 1
        funext x
        rw [hn x]
        ring
    _ =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) -
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) := by
        unfold avgZMod
        rw [Finset.sum_sub_distrib]
        ring

lemma finiteComplementFejerAverage_tendsto
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Tendsto
      (fun n => E.finiteComplementFejerAverage Q n)
      atTop
      (𝓝 (TrigPoly.compactAverage (E.fejerTrigPoly Q) -
        TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q))) := by
  have hdiff :=
    (TrigPoly.finiteAverage_tendsto_compactAverage E
      (E.fejerTrigPoly Q)).sub
      (TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional E
        (E.fejerTrigPoly Q))
  exact hdiff.congr'
    (by
      filter_upwards [E.finiteComplementFejerAverage_eventually_eq Q] with n hn
      exact hn.symm)

lemma finiteComplementFejerAverage_tendsto_one_sub_indicatorCoeffFunctional
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    Tendsto
      (fun n => E.finiteComplementFejerAverage Q n)
      atTop
      (𝓝 (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q))) := by
  simpa [E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ] using
    E.finiteComplementFejerAverage_tendsto Q

lemma finiteComplementFejerAverage_re_le_fejerAverage_re
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    (E.finiteComplementFejerAverage Q n).re ≤
      (E.finiteFejerKernelAverage Q n).re := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementFejerAverage finiteFejerKernelAverage
  refine avgZMod_re_le ?_
  intro x
  by_cases hx : x ∈ S.T (E.φ n)
  · simp [indicatorC, hx, E.finiteFejerKernel_re_nonneg Q n x]
  · simp [indicatorC, hx]

lemma finiteComplementFejerAverage_re_le_one_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop,
      (E.finiteComplementFejerAverage Q n).re ≤ 1 := by
  filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg
  exact (E.finiteComplementFejerAverage_re_le_fejerAverage_re Q n).trans_eq
    (by simp [havg])

lemma finiteSmooth_norm_le_one_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop,
      ∀ z : ZMod (S.p (E.φ n)), ‖E.finiteSmooth Q n z‖ ≤ 1 := by
  filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg z
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  refine norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
    (S.T (E.φ n)) (E.finiteFejerKernel Q n)
    (E.finiteFejerKernel_re_nonneg Q n)
    (E.finiteFejerKernel_im_eq_zero Q n) ?_ z
  simpa [finiteFejerKernelAverage] using havg

lemma normalizedDftFunction_finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction (E.finiteSmooth Q n) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        normalizedDftFunction (E.finiteFejerKernel Q n) r := by
  unfold finiteSmooth
  rw [normalizedDftFunction_avgConvolution]
  rfl

/-- For a fixed finite polynomial `P`, weight its lifted finite Fourier
coefficients by the finite indicator coefficients of the extracted cyclic
model. This is the finite polynomial model for Fejér smoothing. -/
noncomputable def finiteDftWeightedTrigPoly
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) : E.TrigPoly :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  P.sum fun γ c =>
    Finsupp.single γ
      (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)

lemma finiteDftWeightedTrigPoly_add
    (E : CayleyExtraction S) (P R : E.TrigPoly) (n : ℕ) :
    E.finiteDftWeightedTrigPoly (P + R) n =
      E.finiteDftWeightedTrigPoly P n +
        E.finiteDftWeightedTrigPoly R n := by
  classical
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteDftWeightedTrigPoly
  let h : E.Group → ℂ →+ E.TrigPoly := fun γ =>
    { toFun := fun c =>
        Finsupp.single γ
          (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)
      map_zero' := by simp
      map_add' := by
        intro a b
        rw [mul_add, Finsupp.single_add] }
  change Finsupp.sum (P + R) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum R (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma finiteDftWeightedTrigPoly_single
    (E : CayleyExtraction S) (γ : E.Group) (c : ℂ) (n : ℕ) :
    E.finiteDftWeightedTrigPoly (Finsupp.single γ c : E.TrigPoly) n =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        Finsupp.single γ
          (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)) := by
  classical
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteDftWeightedTrigPoly
  rw [Finsupp.sum_single_index]
  simp

lemma finiteDftWeightedTrigPoly_apply
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) (γ : E.Group) :
    E.finiteDftWeightedTrigPoly P n γ =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * P γ) := by
  classical
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [finiteDftWeightedTrigPoly]
  · intro P R hP hR
    rw [E.finiteDftWeightedTrigPoly_add P R n]
    simp [hP, hR, mul_add]
  · intro δ c
    rw [E.finiteDftWeightedTrigPoly_single δ c n]
    by_cases hδγ : δ = γ
    · subst hδγ
      simp
    · have hleft :
          (Finsupp.single δ
            (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n δ) * c) :
              E.TrigPoly) γ = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hδγ)
      have hright : (Finsupp.single δ c : E.TrigPoly) γ = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hδγ)
      rw [hleft, hright]
      simp

lemma normalizedDftFunction_evalFinite_finiteDftWeightedTrigPoly
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n) n x) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        (P.sum fun γ c => if r + E.lift n γ = 0 then c else 0) := by
  classical
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [finiteDftWeightedTrigPoly, normalizedDftFunction_zero_fun]
  · intro P R hP hR
    rw [E.finiteDftWeightedTrigPoly_add P R n]
    have hfun :
        (fun x : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n +
              E.finiteDftWeightedTrigPoly R n) n x) =
          fun x =>
            TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n) n x +
              TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly R n) n x := by
      funext x
      exact TrigPoly.evalFinite_add
        (E.finiteDftWeightedTrigPoly P n)
        (E.finiteDftWeightedTrigPoly R n) n x
    rw [hfun, normalizedDftFunction_add, hP, hR]
    let h : E.Group → ℂ →+ ℂ := fun γ =>
      { toFun := fun c => if r + E.lift n γ = 0 then c else 0
        map_zero' := by by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ]
        map_add' := by
          intro a b
          by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ] }
    change normalizedDftCoeff (S.T (E.φ n)) r *
        Finsupp.sum P (fun γ c => h γ c) +
        normalizedDftCoeff (S.T (E.φ n)) r *
          Finsupp.sum R (fun γ c => h γ c) =
      normalizedDftCoeff (S.T (E.φ n)) r *
        Finsupp.sum (P + R) (fun γ c => h γ c)
    rw [Finsupp.sum_hom_add_index]
    ring
  · intro γ c
    rw [E.finiteDftWeightedTrigPoly_single γ c n]
    rw [TrigPoly.normalizedDftFunction_evalFinite_single]
    by_cases hγ : r + E.lift n γ = 0
    · have hr : r = -E.lift n γ := eq_neg_of_add_eq_zero_left hγ
      simp [hr]
    · simp [hγ]

/-- The finite trigonometric polynomial whose lifted evaluation is eventually
the fixed-`Q` finite Fejér-smoothed kernel. -/
noncomputable def finiteSmoothModelTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : E.TrigPoly :=
  E.finiteDftWeightedTrigPoly (E.fejerTrigPoly Q) n

lemma finiteSmoothModelTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) (γ : E.Group) :
    E.finiteSmoothModelTrigPoly Q n γ =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) *
          (E.fejerTrigPoly Q) γ) := by
  simp [finiteSmoothModelTrigPoly, E.finiteDftWeightedTrigPoly_apply]

lemma finiteSmooth_eq_evalFinite_finiteSmoothModelTrigPoly_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        E.finiteSmooth Q n x =
          TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n x := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_eventually_eq Q] with n hK x
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [function_eq_sum_normalizedDftFunction (p := S.p (E.φ n))
      (E.finiteSmooth Q n) x]
  rw [function_eq_sum_normalizedDftFunction (p := S.p (E.φ n))
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n x) x]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  congr 1
  rw [E.normalizedDftFunction_finiteSmooth Q n r, hK r]
  rw [finiteSmoothModelTrigPoly,
    E.normalizedDftFunction_evalFinite_finiteDftWeightedTrigPoly
      (E.fejerTrigPoly Q) n r]

lemma normalizedDftFunction_indicator_sub_finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun z : ZMod (S.p (E.φ n)) =>
          indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r) := by
  rw [normalizedDftFunction_sub, E.normalizedDftFunction_finiteSmooth Q n r]
  simp [normalizedDftCoeff]
  ring

lemma normalizedDftFunction_finiteSmooth_at_lift_tendsto
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteSmooth Q n) (E.lift n γ))
      atTop
      (𝓝 (E.coeff γ * (E.fejerTrigPoly Q) (-γ))) := by
  have hT := E.coeff_tendsto γ
  have hK :
      Tendsto (fun _n : ℕ => (E.fejerTrigPoly Q) (-γ))
        atTop (𝓝 ((E.fejerTrigPoly Q) (-γ))) :=
    tendsto_const_nhds
  have hprod := hT.mul hK
  refine hprod.congr' ?_
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_at_lift_eventually_eq_coeff
      Q γ] with n hKcoeff
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [E.normalizedDftFunction_finiteSmooth Q n (E.lift n γ)]
  rw [hKcoeff]

/-- Compact-side trigonometric polynomial whose coefficients match the
fixed-`Q` Fejér-smoothed Cayley limit. -/
noncomputable def compactSmoothTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) : E.TrigPoly :=
  ∑ γ ∈ (E.fejerTrigPoly Q).support,
    Finsupp.single γ ((E.fejerTrigPoly Q) γ * E.coeff (-γ))

lemma compactSmoothTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    E.compactSmoothTrigPoly Q γ =
      (E.fejerTrigPoly Q) γ * E.coeff (-γ) := by
  classical
  unfold compactSmoothTrigPoly
  rw [Finsupp.finset_sum_apply]
  by_cases hγ : γ ∈ (E.fejerTrigPoly Q).support
  · rw [Finset.sum_eq_single γ]
    · simp
    · intro δ hδ hδγ
      exact Finsupp.single_eq_of_ne (Ne.symm hδγ)
    · intro hnot
      exact (hnot hγ).elim
  · have hzero : (E.fejerTrigPoly Q) γ = 0 :=
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

lemma finiteSmoothModelTrigPoly_apply_tendsto_compactSmoothTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    Tendsto
      (fun n => E.finiteSmoothModelTrigPoly Q n γ)
      atTop (𝓝 (E.compactSmoothTrigPoly Q γ)) := by
  have hcoeff := E.coeff_tendsto (-γ)
  have hcoeff' :
      Tendsto
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ))
        atTop (𝓝 (E.coeff (-γ))) := by
    refine hcoeff.congr' ?_
    filter_upwards [E.data.finiteLift_neg_eventually_eq γ] with n hneg
    haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    simp [lift, hneg]
  have hconst :
      Tendsto (fun _n : ℕ => (E.fejerTrigPoly Q) γ)
        atTop (𝓝 ((E.fejerTrigPoly Q) γ)) :=
    tendsto_const_nhds
  have hprod := hcoeff'.mul hconst
  have htarget :
      E.coeff (-γ) * (E.fejerTrigPoly Q γ) =
        E.compactSmoothTrigPoly Q γ := by
    rw [E.compactSmoothTrigPoly_apply Q γ]
    ring
  have hprod' := hprod.congr' (by
    filter_upwards with n
    exact (E.finiteSmoothModelTrigPoly_apply Q n γ).symm)
  simpa [htarget] using hprod'

/-- Compact finite-Fejér smoothing of the limiting allowed kernel, represented
by the fixed trigonometric polynomial whose coefficients are the limits of the
finite smoothed kernels. -/
noncomputable def compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.CompactAddDual → ℂ :=
  fun z => TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z

noncomputable def compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.CompactAddDual → ℝ :=
  fun z => (E.compactSmooth Q z).re

lemma TrigPoly.evalAdd_im_eq_zero_of_apply_neg_eq_self
    (E : CayleyExtraction S) (P : E.TrigPoly)
    (hneg : ∀ γ : E.Group, P (-γ) = P γ)
    (him : ∀ γ : E.Group, (P γ).im = 0)
    (z : E.CompactAddDual) :
    (TrigPoly.evalAdd P z).im = 0 := by
  classical
  have hsupport_neg : ∀ {γ : E.Group}, γ ∈ P.support → -γ ∈ P.support := by
    intro γ hγ
    rw [Finsupp.mem_support_iff] at hγ ⊢
    intro hzero
    have hPγ : P γ = 0 := by
      rw [← hneg γ, hzero]
    exact hγ hPγ
  have hsum :
      TrigPoly.evalAdd P z =
        ∑ γ ∈ P.support, P γ * E.addCharacterValue z γ := by
    unfold TrigPoly.evalAdd
    rw [Finsupp.sum_of_support_subset
      (f := P) (s := P.support) (by intro γ hγ; exact hγ)]
    intro γ _hγ
    simp
  have hstar : star (TrigPoly.evalAdd P z) = TrigPoly.evalAdd P z := by
    calc
      star (TrigPoly.evalAdd P z)
          = ∑ γ ∈ P.support, star (P γ * E.addCharacterValue z γ) := by
            rw [hsum]
            simp
      _ = ∑ γ ∈ P.support, P (-γ) * E.addCharacterValue z (-γ) := by
            refine Finset.sum_congr rfl ?_
            intro γ _hγ
            have hreal : star (P γ) = P γ := by
              simpa using (Complex.conj_eq_iff_im.mpr (him γ))
            rw [star_mul, E.star_addCharacterValue, hreal, ← hneg γ]
            ring
      _ = ∑ γ ∈ P.support, P γ * E.addCharacterValue z γ := by
            refine Finset.sum_bij (fun γ _hγ => -γ) ?mem ?inj ?surj ?eq
            · intro γ hγ
              exact hsupport_neg hγ
            · intro a _ha b _hb h
              exact neg_inj.mp h
            · intro b hb
              refine ⟨-b, hsupport_neg hb, ?_⟩
              simp
            · intro γ hγ
              simp
      _ = TrigPoly.evalAdd P z := hsum.symm
  exact Complex.conj_eq_iff_im.mp hstar

lemma compactSmoothTrigPoly_apply_neg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    E.compactSmoothTrigPoly Q (-γ) = E.compactSmoothTrigPoly Q γ := by
  rw [E.compactSmoothTrigPoly_apply Q (-γ),
    E.compactSmoothTrigPoly_apply Q γ,
    E.fejerTrigPoly_apply_neg Q γ]
  simp [E.coeff_neg_eq γ]

lemma compactSmoothTrigPoly_apply_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.compactSmoothTrigPoly Q γ).im = 0 := by
  rw [E.compactSmoothTrigPoly_apply Q γ]
  have hK : ((E.fejerTrigPoly Q) γ).im = 0 :=
    E.fejerTrigPoly_apply_im_eq_zero Q γ
  have hcoeff : (E.coeff (-γ)).im = 0 := E.coeff_im_eq_zero (-γ)
  simp [Complex.mul_im, hK, hcoeff]

lemma compactSmooth_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    (E.compactSmooth Q z).im = 0 := by
  exact TrigPoly.evalAdd_im_eq_zero_of_apply_neg_eq_self E
    (E.compactSmoothTrigPoly Q)
    (E.compactSmoothTrigPoly_apply_neg Q)
    (E.compactSmoothTrigPoly_apply_im_eq_zero Q) z

lemma compactSmooth_eq_ofReal_compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    E.compactSmooth Q z = (E.compactSmoothReal Q z : ℂ) := by
  apply Complex.ext
  · simp [compactSmoothReal]
  · simp [compactSmoothReal, E.compactSmooth_im_eq_zero Q z]

lemma compactSmooth_continuous
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Continuous (E.compactSmooth Q) :=
  TrigPoly.continuous_evalAdd E (E.compactSmoothTrigPoly Q)

lemma compactSmoothReal_continuous
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Continuous (E.compactSmoothReal Q) :=
  Complex.continuous_re.comp (E.compactSmooth_continuous Q)

lemma compactSmoothReal_eq_sum_support
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    E.compactSmoothReal Q z =
      ∑ γ ∈ (E.compactSmoothTrigPoly Q).support,
        ((E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
          (E.addCharacterValue z γ).re) := by
  classical
  have hsum :
      TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z =
        ∑ γ ∈ (E.compactSmoothTrigPoly Q).support,
          E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ := by
    unfold TrigPoly.evalAdd
    rw [Finsupp.sum_of_support_subset
      (f := E.compactSmoothTrigPoly Q)
      (s := (E.compactSmoothTrigPoly Q).support) (by intro γ hγ; exact hγ)]
    intro γ _hγ
    simp
  unfold compactSmoothReal compactSmooth
  rw [hsum]
  change Complex.reAddGroupHom
      (∑ γ ∈ (E.compactSmoothTrigPoly Q).support,
        E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  change (E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ).re =
    (E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
      (E.addCharacterValue z γ).re
  rw [E.compactSmoothTrigPoly_apply Q γ, E.coeff_neg_eq γ]
  have hKim : ((E.fejerTrigPoly Q) γ).im = 0 :=
    E.fejerTrigPoly_apply_im_eq_zero Q γ
  have hAim : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
  simp [Complex.mul_re, Complex.mul_im, hKim, hAim, mul_assoc]

lemma compactSmoothReal_eq_sum_of_support_subset
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (A : Finset E.Group) (hA : (E.compactSmoothTrigPoly Q).support ⊆ A) :
    E.compactSmoothReal Q z =
      ∑ γ ∈ A,
        ((E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
          (E.addCharacterValue z γ).re) := by
  classical
  have hsum :
      TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z =
        ∑ γ ∈ A,
          E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ := by
    unfold TrigPoly.evalAdd
    rw [Finsupp.sum_of_support_subset
      (f := E.compactSmoothTrigPoly Q) (s := A) hA]
    intro γ _hγ
    simp
  unfold compactSmoothReal compactSmooth
  rw [hsum]
  change Complex.reAddGroupHom
      (∑ γ ∈ A,
        E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  change (E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ).re =
    (E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
      (E.addCharacterValue z γ).re
  rw [E.compactSmoothTrigPoly_apply Q γ, E.coeff_neg_eq γ]
  have hKim : ((E.fejerTrigPoly Q) γ).im = 0 :=
    E.fejerTrigPoly_apply_im_eq_zero Q γ
  have hAim : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
  simp [Complex.mul_re, Complex.mul_im, hKim, hAim, mul_assoc]

lemma integral_compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∫ z : E.CompactAddDual, E.compactSmooth Q z ∂E.haar =
      E.compactSmoothTrigPoly Q 0 := by
  simp [compactSmooth, TrigPoly.integral_evalAdd_eq_compactAverage,
    TrigPoly.compactAverage]

lemma integral_compactSmooth_eq_coeff_zero_of_nonempty
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∫ z : E.CompactAddDual, E.compactSmooth Q z ∂E.haar =
      E.coeff 0 := by
  rw [E.integral_compactSmooth Q]
  rw [E.compactSmoothTrigPoly_apply Q 0]
  have hfejer0 : (E.fejerTrigPoly Q) (0 : E.Group) = 1 :=
    E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  simp [hfejer0]

lemma normalizedDftFunction_finiteSmooth_at_neg_lift_tendsto_compactCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteSmooth Q n) (-E.lift n γ))
      atTop (𝓝 (E.compactSmoothTrigPoly Q γ)) := by
  have ht := E.normalizedDftFunction_finiteSmooth_at_lift_tendsto Q (-γ)
  have htarget :
      E.coeff (-γ) * (E.fejerTrigPoly Q) γ =
        E.compactSmoothTrigPoly Q γ := by
    rw [E.compactSmoothTrigPoly_apply Q γ]
    ring
  have ht' :
      Tendsto
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteSmooth Q n) (-E.lift n γ))
        atTop (𝓝 (E.coeff (-γ) * (E.fejerTrigPoly Q) γ)) := by
    have heq :
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteSmooth Q n) (E.lift n (-γ))) =ᶠ[atTop]
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteSmooth Q n) (-E.lift n γ)) := by
      filter_upwards [E.data.finiteLift_neg_eventually_eq γ] with n hneg
      haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      simp [lift, hneg]
    have ht_simplified :
        Tendsto
          (fun n =>
            letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            normalizedDftFunction (E.finiteSmooth Q n) (E.lift n (-γ)))
          atTop (𝓝 (E.coeff (-γ) * (E.fejerTrigPoly Q) γ)) := by
      simpa using ht
    exact ht_simplified.congr' heq
  simpa [htarget] using ht'

/-- Finite average pairing the smoothed Cayley kernel with a lifted fixed
trigonometric polynomial. -/
noncomputable def finiteSmoothWeightedAverage
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    E.finiteSmooth Q n x * P.evalFinite n x

/-- Coefficient functional that is the fixed-`Q` limit of
`finiteSmoothWeightedAverage`. -/
noncomputable def smoothedCoeffFunctional
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P : E.TrigPoly) : ℂ :=
  P.sum fun γ c => c * (E.coeff γ * (E.fejerTrigPoly Q) (-γ))

lemma finiteSmoothWeightedAverage_add
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P R : E.TrigPoly) (n : ℕ) :
    E.finiteSmoothWeightedAverage Q (P + R) n =
      E.finiteSmoothWeightedAverage Q P n +
        E.finiteSmoothWeightedAverage Q R n := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteSmoothWeightedAverage
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        E.finiteSmooth Q n x * TrigPoly.evalFinite (P + R) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        E.finiteSmooth Q n x * TrigPoly.evalFinite P n x +
        E.finiteSmooth Q n x * TrigPoly.evalFinite R n x) by
        funext x
        rw [TrigPoly.evalFinite_add]
        ring]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma finiteSmoothWeightedAverage_single
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (γ : E.Group) (c : ℂ) (n : ℕ) :
    E.finiteSmoothWeightedAverage Q
        (Finsupp.single γ c : E.TrigPoly) n =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        c * normalizedDftFunction (E.finiteSmooth Q n) (E.lift n γ)) := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteSmoothWeightedAverage
  change avgZMod
      (fun x : ZMod (S.p (E.φ n)) =>
        E.finiteSmooth Q n x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
    c * normalizedDftFunction (E.finiteSmooth Q n) (E.lift n γ)
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        E.finiteSmooth Q n x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        c * (ZMod.stdAddChar (-(x * E.lift n γ)) *
          E.finiteSmooth Q n x)) by
        funext x
        simp [TrigPoly.evalFinite_single]
        ring_nf]
  rw [avgZMod_const_mul]
  rw [normalizedDftFunction_eq_avgZMod]

lemma smoothedCoeffFunctional_add
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P R : E.TrigPoly) :
    E.smoothedCoeffFunctional Q (P + R) =
      E.smoothedCoeffFunctional Q P +
        E.smoothedCoeffFunctional Q R := by
  unfold smoothedCoeffFunctional
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * (E.coeff γ * (E.fejerTrigPoly Q) (-γ))
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + R) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum R (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

@[simp]
lemma smoothedCoeffFunctional_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.smoothedCoeffFunctional Q (0 : E.TrigPoly) = 0 := by
  simp [smoothedCoeffFunctional]

lemma smoothedCoeffFunctional_single
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (γ : E.Group) (c : ℂ) :
    E.smoothedCoeffFunctional Q (Finsupp.single γ c : E.TrigPoly) =
      c * (E.coeff γ * (E.fejerTrigPoly Q) (-γ)) := by
  simp [smoothedCoeffFunctional]

lemma compactSmooth_mul_evalAdd_integrable
    (E : CayleyExtraction S) (Q : Finset E.Group) (P : E.TrigPoly) :
    Integrable
      (fun z : E.CompactAddDual =>
        E.compactSmooth Q z * TrigPoly.evalAdd P z) E.haar :=
  ((E.compactSmooth_continuous Q).mul
      (TrigPoly.continuous_evalAdd E P)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma smoothedCoeffFunctional_eq_integral_compactSmooth_mul_evalAdd
    (E : CayleyExtraction S) (Q : Finset E.Group) (P : E.TrigPoly) :
    E.smoothedCoeffFunctional Q P =
      ∫ z : E.CompactAddDual,
        E.compactSmooth Q z * TrigPoly.evalAdd P z ∂E.haar := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [smoothedCoeffFunctional]
  · intro P R hP hR
    rw [E.smoothedCoeffFunctional_add Q P R, hP, hR]
    rw [show
        (fun z : E.CompactAddDual =>
            E.compactSmooth Q z * TrigPoly.evalAdd (P + R) z) =
          fun z =>
            E.compactSmooth Q z * TrigPoly.evalAdd P z +
              E.compactSmooth Q z * TrigPoly.evalAdd R z by
        funext z
        rw [TrigPoly.evalAdd_add]
        ring]
    rw [integral_add (E.compactSmooth_mul_evalAdd_integrable Q P)
      (E.compactSmooth_mul_evalAdd_integrable Q R)]
  · intro γ c
    rw [E.smoothedCoeffFunctional_single Q γ c]
    rw [show
        (fun z : E.CompactAddDual =>
            E.compactSmooth Q z *
              TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z) =
          fun z =>
            c * (TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z *
              E.addCharacterValue z γ) by
        funext z
        simp [compactSmooth]
        ring]
    rw [integral_const_mul]
    rw [TrigPoly.integral_evalAdd_mul_char E (E.compactSmoothTrigPoly Q) γ]
    rw [E.compactSmoothTrigPoly_apply Q (-γ)]
    have hnegneg : (-(-γ) : E.Group) = γ := by simp
    rw [hnegneg]
    ring

lemma finiteSmoothWeightedAverage_tendsto_coeffFunctional
    (E : CayleyExtraction S) (Q : Finset E.Group) (P : E.TrigPoly) :
    Tendsto
      (fun n => E.finiteSmoothWeightedAverage Q P n)
      atTop (𝓝 (E.smoothedCoeffFunctional Q P)) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · rw [E.smoothedCoeffFunctional_zero Q]
    have hzero :
        (fun n => E.finiteSmoothWeightedAverage Q (0 : E.TrigPoly) n) =
          fun _n => (0 : ℂ) := by
      funext n
      haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      simp [finiteSmoothWeightedAverage, avgZMod]
    rw [hzero]
    exact tendsto_const_nhds
  · intro P R hP hR
    rw [E.smoothedCoeffFunctional_add Q P R]
    exact (hP.add hR).congr' (Filter.Eventually.of_forall fun n => by
      exact (E.finiteSmoothWeightedAverage_add Q P R n).symm)
  · intro γ c
    rw [E.smoothedCoeffFunctional_single Q γ c]
    have hcoeff := E.normalizedDftFunction_finiteSmooth_at_lift_tendsto Q γ
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have hmul := hc.mul hcoeff
    exact hmul.congr' (Filter.Eventually.of_forall fun n => by
      exact (E.finiteSmoothWeightedAverage_single Q γ c n).symm)

lemma finiteSmoothWeightedAverage_tendsto_integral_compactSmooth_mul_evalAdd
    (E : CayleyExtraction S) (Q : Finset E.Group) (P : E.TrigPoly) :
    Tendsto
      (fun n => E.finiteSmoothWeightedAverage Q P n)
      atTop
      (𝓝 (∫ z : E.CompactAddDual,
        E.compactSmooth Q z * TrigPoly.evalAdd P z ∂E.haar)) := by
  simpa [E.smoothedCoeffFunctional_eq_integral_compactSmooth_mul_evalAdd Q P]
    using E.finiteSmoothWeightedAverage_tendsto_coeffFunctional Q P

/-- Fejér smoothing is spectrally close to the original indicator once the
chosen Fejér polynomial is close to `1` on the extracted large-spectrum
generators.  The small-spectrum branch gives the explicit `2 / q` term. -/
lemma spectralBound_indicator_sub_finiteSmooth_eventually
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM : ∀ γ ∈ E.data.largeSpectrumGenerators q,
      ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) := by
  classical
  have hcovered := E.eventually_largeSpectrum_covered q
  have hfejerLarge :
      ∀ᶠ n in atTop,
        ∀ γ ∈ E.data.largeSpectrumGenerators q,
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n)
              (E.lift n γ)‖) ≤ M := by
    rw [(E.data.largeSpectrumGenerators q).eventually_all]
    intro γ hγ
    exact E.norm_one_sub_normalizedDftFunction_finiteFejerKernel_at_lift_eventually_le
      Q γ (hM γ hγ)
  have hfejerNorm :
      ∀ᶠ n in atTop,
        ∀ r : ZMod (S.p (E.φ n)),
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            ‖normalizedDftFunction (E.finiteFejerKernel Q n) r‖) ≤ 1 := by
    filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg r
    haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    refine norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one
      (E.finiteFejerKernel Q n)
      (E.finiteFejerKernel_re_nonneg Q n)
      (E.finiteFejerKernel_im_eq_zero Q n) ?_ r
    simpa [finiteFejerKernelAverage] using havg
  filter_upwards [hcovered, hfejerLarge, hfejerNorm] with n hncover hnlarge hnnorm
  intro r
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [E.normalizedDftFunction_indicator_sub_finiteSmooth Q n r]
  by_cases hsmall :
      ‖normalizedDftCoeff (S.T (E.φ n)) r‖ ≤ ((q : ℝ)⁻¹ : ℝ)
  · have h1K :
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ ≤
          (2 : ℝ) := by
      calc
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖
            ≤ ‖(1 : ℂ)‖ +
                ‖normalizedDftFunction (E.finiteFejerKernel Q n) r‖ :=
              norm_sub_le _ _
        _ ≤ 1 + 1 := by
              exact add_le_add (by norm_num) (hnnorm r)
        _ = (2 : ℝ) := by norm_num
    calc
      ‖normalizedDftCoeff (S.T (E.φ n)) r *
          (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r)‖
          =
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ *
          ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ := by
          rw [norm_mul]
      _ ≤ ((q : ℝ)⁻¹ : ℝ) * 2 := by
          exact mul_le_mul hsmall h1K (norm_nonneg _) (by positivity)
      _ = 2 * ((q : ℝ)⁻¹ : ℝ) := by ring
      _ ≤ max (2 * ((q : ℝ)⁻¹ : ℝ)) M := le_max_left _ _
  · have hlarge :
        ((q : ℝ)⁻¹ : ℝ) <
          ‖normalizedDftCoeff (S.T (E.φ n)) r‖ := lt_of_not_ge hsmall
    rcases hncover r (by simpa using hlarge) with ⟨γ, hγ, hγr⟩
    have hK :
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ ≤ M := by
      simpa [hγr] using hnlarge γ hγ
    have hcoef_le :
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ ≤ 1 := by
      simpa [CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
        normalizedDftCoeff] using
        (S.toFourierSeq).norm_coeff_le_one (E.φ n) r
    calc
      ‖normalizedDftCoeff (S.T (E.φ n)) r *
          (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r)‖
          =
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ *
          ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ := by
          rw [norm_mul]
      _ ≤ 1 * M := by
          exact mul_le_mul hcoef_le hK (norm_nonneg _) (by norm_num)
      _ = M := by ring
      _ ≤ max (2 * ((q : ℝ)⁻¹ : ℝ)) M := le_max_right _ _

lemma spectralBound_indicator_sub_finiteSmooth_eventually_of_negCoeffBound
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM : E.FejerNegCoeffBound Q (E.data.largeSpectrumGenerators q) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) :=
  E.spectralBound_indicator_sub_finiteSmooth_eventually q Q hQ hM

lemma spectralBound_indicator_sub_finiteSmooth_eventually_of_lowerBound_neg
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM :
      E.FejerPairCoeffLowerBound Q
        ((E.data.largeSpectrumGenerators q).image Neg.neg) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) :=
  E.spectralBound_indicator_sub_finiteSmooth_eventually_of_negCoeffBound q Q hQ
    (E.fejerNegCoeffBound_of_pairCoeffLowerBound_neg hQ hM)

end CayleyExtraction

end

end Erdos42.CompactCayley
