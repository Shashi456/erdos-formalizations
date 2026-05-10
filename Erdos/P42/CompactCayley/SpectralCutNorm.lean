/-
Erdős Problem 42 — compact-Cayley route, Lemma 2.5 finite spectral layer.

The compact-Cayley proof's Lemma 2.5 is the finite statement that the Cayley
cut norm of a kernel `a(x-y)` is controlled by the largest Fourier coefficient
of `a`.  This file starts that route with the concrete finite objects and the
Fourier expansion of the Cayley kernel. It deliberately introduces no new
assumptions; the operator-norm/Cauchy-Schwarz estimate builds on these
definitions.
-/

import Erdos.P42.Shared.FiniteFourier
import Mathlib.Data.Real.Sqrt

namespace Erdos42.CompactCayley

open scoped BigOperators ZMod

/-- Normalized average over `ZMod p`. -/
noncomputable def avgZMod {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℂ :=
  ((p : ℂ)⁻¹) * ∑ x : ZMod p, f x

lemma avgZMod_sum {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (F : ι → ZMod p → ℂ) :
    avgZMod (fun x => ∑ i : ι, F i x) = ∑ i : ι, avgZMod (F i) := by
  classical
  unfold avgZMod
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

lemma avgZMod_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) :
    avgZMod (fun x => c * f x) = c * avgZMod f := by
  unfold avgZMod
  rw [← Finset.mul_sum]
  ring

lemma avgZMod_mul_const {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (c : ℂ) :
    avgZMod (fun x => f x * c) = avgZMod f * c := by
  unfold avgZMod
  rw [← Finset.sum_mul]
  ring

/-- The finite Cayley cut functional attached to the kernel `a(x-y)` and two
test functions.  Lemma 2.5 takes a supremum of `‖cayleyCutFunctional a φ ψ‖`
over tests bounded by `1`. -/
noncomputable def cayleyCutFunctional {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) : ℂ :=
  avgZMod fun x => avgZMod fun y => a (x - y) * φ x * ψ y

/-- The Cayley convolution operator `Aψ(x) = E_y a(x-y)ψ(y)` from the proof of
compact-Cayley Lemma 2.5. -/
noncomputable def cayleyConvolution {p : ℕ} [NeZero p]
    (a ψ : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  avgZMod fun y => a (x - y) * ψ y

lemma cayleyCutFunctional_eq_avg_convolution {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    cayleyCutFunctional a φ ψ =
      avgZMod fun x => cayleyConvolution a ψ x * φ x := by
  unfold cayleyCutFunctional cayleyConvolution
  congr 1
  funext x
  rw [← avgZMod_mul_const]
  congr 1
  funext y
  ring

/-- The left test Fourier factor appearing after expanding the Cayley kernel. -/
noncomputable def leftFourierTest {p : ℕ} [NeZero p]
    (φ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  avgZMod fun x => ZMod.stdAddChar (r * x) * φ x

/-- The right test Fourier factor appearing after expanding the Cayley kernel. -/
noncomputable def rightFourierTest {p : ℕ} [NeZero p]
    (ψ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  avgZMod fun y => ZMod.stdAddChar (-(r * y)) * ψ y

lemma rightFourierTest_eq_normalizedDftFunction {p : ℕ} [NeZero p]
    (ψ : ZMod p → ℂ) (r : ZMod p) :
    rightFourierTest ψ r = normalizedDftFunction ψ r := by
  dsimp [rightFourierTest, avgZMod]
  rw [normalizedDftFunction_eq_sum (p := p) ψ r]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [mul_comm r y]

lemma leftFourierTest_eq_normalizedDftFunction_neg {p : ℕ} [NeZero p]
    (φ : ZMod p → ℂ) (r : ZMod p) :
    leftFourierTest φ r = normalizedDftFunction φ (-r) := by
  dsimp [leftFourierTest, avgZMod]
  rw [normalizedDftFunction_eq_sum (p := p) φ (-r)]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro x _
  congr 1
  simp [mul_comm]

lemma sum_sq_norm_rightFourierTest_eq_normalizedDftFunction
    {p : ℕ} [NeZero p] (ψ : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) =
      ∑ r : ZMod p, ‖normalizedDftFunction ψ r‖ ^ 2 := by
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [rightFourierTest_eq_normalizedDftFunction]

lemma sum_sq_norm_leftFourierTest_eq_normalizedDftFunction
    {p : ℕ} [NeZero p] (φ : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) =
      ∑ r : ZMod p, ‖normalizedDftFunction φ r‖ ^ 2 := by
  classical
  calc
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) =
        ∑ r : ZMod p, ‖normalizedDftFunction φ (-r)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [leftFourierTest_eq_normalizedDftFunction_neg]
    _ = ∑ r : ZMod p, ‖normalizedDftFunction φ r‖ ^ 2 := by
          refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
          intro r
          simp

lemma star_stdAddChar_neg_mul {p : ℕ} [NeZero p] (x r : ZMod p) :
    (starRingEnd ℂ) (ZMod.stdAddChar (-(x * r))) =
      ZMod.stdAddChar (x * r) := by
  have h := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (x * r)
  simp [h]

lemma star_normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    (starRingEnd ℂ) (normalizedDftFunction f r) =
      ((p : ℂ)⁻¹) *
        ∑ x : ZMod p, ZMod.stdAddChar (x * r) * (starRingEnd ℂ) (f x) := by
  rw [normalizedDftFunction_eq_sum]
  simp [map_sum, star_stdAddChar_neg_mul, mul_comm]

lemma avg_stdAddChar_mul_star_eq_star_normalizedDftFunction
    {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (r : ZMod p) :
    avgZMod (fun x => ZMod.stdAddChar (r * x) * (starRingEnd ℂ) (g x)) =
      (starRingEnd ℂ) (normalizedDftFunction g r) := by
  rw [star_normalizedDftFunction, avgZMod]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [mul_comm r x]

/-- Parseval cross identity in normalized-average form. -/
lemma avg_mul_star_eq_sum_normalizedDftFunction {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    avgZMod (fun x => f x * (starRingEnd ℂ) (g x)) =
      ∑ r : ZMod p,
        normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction g r) := by
  classical
  calc
    avgZMod (fun x => f x * (starRingEnd ℂ) (g x)) =
        avgZMod
          (fun x =>
            (∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r) *
              (starRingEnd ℂ) (g x)) := by
          congr 1
          funext x
          rw [← function_eq_sum_normalizedDftFunction (p := p) f x]
    _ = avgZMod
          (fun x =>
            ∑ r : ZMod p,
              normalizedDftFunction f r *
                (ZMod.stdAddChar (r * x) * (starRingEnd ℂ) (g x))) := by
          congr 1
          funext x
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro r _
          ring
    _ = ∑ r : ZMod p,
        normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction g r) := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul, avg_stdAddChar_mul_star_eq_star_normalizedDftFunction]

/-- Parseval in the normalized convention used here. -/
lemma sum_sq_norm_normalizedDftFunction_eq_avg
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2) =
      ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  have hcomplex :
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, (‖f x‖ : ℂ) ^ 2 =
        ∑ r : ZMod p, (‖normalizedDftFunction f r‖ : ℂ) ^ 2 := by
    calc
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, (‖f x‖ : ℂ) ^ 2 =
          avgZMod (fun x => f x * (starRingEnd ℂ) (f x)) := by
            unfold avgZMod
            apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [← Complex.mul_conj']
      _ = ∑ r : ZMod p,
          normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction f r) :=
            avg_mul_star_eq_sum_normalizedDftFunction f f
      _ = ∑ r : ZMod p, (‖normalizedDftFunction f r‖ : ℂ) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [Complex.mul_conj']
  simpa [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_natCast] using hcomplex.symm

lemma sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {f : ZMod p → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    (∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2) ≤ 1 := by
  classical
  rw [sum_sq_norm_normalizedDftFunction_eq_avg]
  have hsum : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ) := by
    calc
      (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ ∑ _x : ZMod p, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro x _
        have hx_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have hx_le : ‖f x‖ ^ 2 ≤ (1 : ℝ) := by
          nlinarith [hf x]
        exact hx_le
      _ = (p : ℝ) := by simp [ZMod.card]
  have hp_nonneg : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  calc
    ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ ^ 2
        ≤ ((p : ℝ)⁻¹) * (p : ℝ) := mul_le_mul_of_nonneg_left hsum hp_nonneg
    _ = 1 := inv_mul_cancel₀ hp_ne

lemma sum_sq_norm_rightFourierTest_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {ψ : ZMod p → ℂ}
    (hψ : ∀ y, ‖ψ y‖ ≤ 1) :
    (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) ≤ 1 := by
  rw [sum_sq_norm_rightFourierTest_eq_normalizedDftFunction]
  exact sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hψ

lemma sum_sq_norm_leftFourierTest_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {φ : ZMod p → ℂ}
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) ≤ 1 := by
  rw [sum_sq_norm_leftFourierTest_eq_normalizedDftFunction]
  exact sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hφ

lemma stdAddChar_mul_sub {p : ℕ} [NeZero p] (r x y : ZMod p) :
    ZMod.stdAddChar (r * (x - y)) =
      ZMod.stdAddChar (r * x) * ZMod.stdAddChar (-(r * y)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

lemma sum_stdAddChar_mul_eq_zero_of_ne_zero
    {p : ℕ} [NeZero p] {t : ZMod p} (ht : t ≠ 0) :
    ∑ r : ZMod p, ZMod.stdAddChar (r * t) = 0 := by
  classical
  have hnontrivial :
      AddChar.mulShift (ZMod.stdAddChar (N := p)) t ≠ 1 :=
    (ZMod.isPrimitive_stdAddChar p) ht
  have hsum :
      ∑ r : ZMod p, AddChar.mulShift (ZMod.stdAddChar (N := p)) t r = 0 :=
    AddChar.sum_eq_zero_of_ne_one hnontrivial
  simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Orthogonality of the standard additive characters on `ZMod p`, in the
summation direction needed for Parseval. -/
lemma sum_stdAddChar_mul_sub_eq_card_if {p : ℕ} [NeZero p] (x y : ZMod p) :
    ∑ r : ZMod p, ZMod.stdAddChar (r * (x - y)) =
      if x = y then (p : ℂ) else 0 := by
  classical
  by_cases hxy : x = y
  · simp [hxy, ZMod.card]
  · have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
    simp [hxy, sum_stdAddChar_mul_eq_zero_of_ne_zero (p := p) hsub]

/-- Characters diagonalize the finite Cayley convolution operator. -/
lemma cayleyConvolution_stdAddChar {p : ℕ} [NeZero p]
    (a : ZMod p → ℂ) (r x : ZMod p) :
    cayleyConvolution a (fun y => ZMod.stdAddChar (r * y)) x =
      normalizedDftFunction a r * ZMod.stdAddChar (r * x) := by
  classical
  unfold cayleyConvolution avgZMod
  rw [normalizedDftFunction_eq_sum]
  have hchange :
      (∑ y : ZMod p, a (x - y) * ZMod.stdAddChar (r * y)) =
        ∑ z : ZMod p, a z * ZMod.stdAddChar (r * (x - z)) := by
    refine Fintype.sum_equiv (Equiv.subLeft x) _ _ ?_
    intro y
    simp [Equiv.subLeft_apply]
  rw [hchange]
  calc
    ((p : ℂ)⁻¹) * (∑ z : ZMod p, a z * ZMod.stdAddChar (r * (x - z))) =
        ((p : ℂ)⁻¹) *
          (ZMod.stdAddChar (r * x) *
            ∑ z : ZMod p, ZMod.stdAddChar (-(z * r)) * a z) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [stdAddChar_mul_sub]
          have hrz : -(r * z) = -(z * r) := by ring
          rw [hrz]
          ring
    _ = (((p : ℂ)⁻¹) * ∑ z : ZMod p, ZMod.stdAddChar (-(z * r)) * a z) *
          ZMod.stdAddChar (r * x) := by
          ring

/-- Fourier diagonalization of the Cayley convolution operator on an arbitrary
test function. -/
lemma cayleyConvolution_eq_fourier_sum {p : ℕ} [NeZero p]
    (a ψ : ZMod p → ℂ) (x : ZMod p) :
    cayleyConvolution a ψ x =
      ∑ r : ZMod p,
        normalizedDftFunction ψ r * normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) := by
  classical
  unfold cayleyConvolution
  simp_rw [function_eq_sum_normalizedDftFunction (p := p) ψ]
  calc
    avgZMod
        (fun y : ZMod p =>
          a (x - y) *
            ∑ r : ZMod p, ZMod.stdAddChar (r * y) * normalizedDftFunction ψ r) =
        avgZMod
          (fun y : ZMod p =>
            ∑ r : ZMod p,
              normalizedDftFunction ψ r *
                (a (x - y) * ZMod.stdAddChar (r * y))) := by
          congr 1
          funext y
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          ring
    _ = ∑ r : ZMod p,
        normalizedDftFunction ψ r * normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul]
          change normalizedDftFunction ψ r *
              cayleyConvolution a (fun y => ZMod.stdAddChar (r * y)) x =
            normalizedDftFunction ψ r * normalizedDftFunction a r *
              ZMod.stdAddChar (r * x)
          rw [cayleyConvolution_stdAddChar]
          ring

/-- Fourier inversion applied to the Cayley kernel `a(x-y)`, in the exact
factorized form used by the spectral-cut argument. -/
lemma cayleyKernel_eq_fourier_sum {p : ℕ} [NeZero p]
    (a : ZMod p → ℂ) (x y : ZMod p) :
    a (x - y) =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) *
          ZMod.stdAddChar (-(r * y)) := by
  calc
    a (x - y) =
        ∑ r : ZMod p, ZMod.stdAddChar (r * (x - y)) *
          normalizedDftFunction a r := by
          exact function_eq_sum_normalizedDftFunction (p := p) a (x - y)
    _ = ∑ r : ZMod p,
        normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) *
          ZMod.stdAddChar (-(r * y)) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [stdAddChar_mul_sub]
          ring

/-- The same kernel expansion with the two test functions multiplied in. -/
lemma cayleyKernel_mul_tests_eq_fourier_sum {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) (x y : ZMod p) :
    a (x - y) * φ x * ψ y =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          (ZMod.stdAddChar (r * x) * φ x) *
          (ZMod.stdAddChar (-(r * y)) * ψ y) := by
  rw [cayleyKernel_eq_fourier_sum (p := p) a x y]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

/-- The double-average Cayley cut functional factors through the normalized
Fourier coefficients of the kernel and the two test Fourier factors.  This is
the algebraic core of the spectral cut-norm bound in compact-Cayley Lemma 2.5. -/
lemma cayleyCutFunctional_eq_fourier_sum {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    cayleyCutFunctional a φ ψ =
      ∑ r : ZMod p,
        normalizedDftFunction a r * leftFourierTest φ r * rightFourierTest ψ r := by
  classical
  unfold cayleyCutFunctional
  simp_rw [cayleyKernel_mul_tests_eq_fourier_sum (p := p) a φ ψ]
  calc
    avgZMod
        (fun x : ZMod p =>
          avgZMod
            (fun y : ZMod p =>
              ∑ r : ZMod p,
                normalizedDftFunction a r *
                  (ZMod.stdAddChar (r * x) * φ x) *
                  (ZMod.stdAddChar (-(r * y)) * ψ y))) =
        avgZMod
          (fun x : ZMod p =>
            ∑ r : ZMod p,
              normalizedDftFunction a r *
                (ZMod.stdAddChar (r * x) * φ x) *
                rightFourierTest ψ r) := by
          congr 1
          funext x
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul]
          simp [rightFourierTest, mul_assoc]
    _ = ∑ r : ZMod p,
        normalizedDftFunction a r * leftFourierTest φ r * rightFourierTest ψ r := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_mul_const, avgZMod_const_mul]
          simp [leftFourierTest, mul_assoc]

/-- Immediate `L¹` Fourier bound for the Cayley cut functional.  Lemma 2.5
will sharpen this to the spectral supremum under `‖φ‖∞, ‖ψ‖∞ ≤ 1`, using the
Hilbert-space/operator-norm argument from the compact-Cayley PDF. -/
lemma norm_cayleyCutFunctional_le_fourier_l1 {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    ‖cayleyCutFunctional a φ ψ‖ ≤
      ∑ r : ZMod p,
        ‖normalizedDftFunction a r‖ * ‖leftFourierTest φ r‖ *
          ‖rightFourierTest ψ r‖ := by
  rw [cayleyCutFunctional_eq_fourier_sum]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro r _
  rw [norm_mul, norm_mul]

/-- Cauchy-Schwarz sharpening of the Fourier `L¹` bound, assuming the two
test-factor Fourier `L²` sums are at most `1`.  This is the finite analytic
core that remains after Parseval supplies those two `L²` hypotheses from
`‖φ‖∞, ‖ψ‖∞ ≤ 1`. -/
lemma norm_cayleyCutFunctional_le_spectral_of_fourier_l2
    {p : ℕ} [NeZero p] (a φ ψ : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M)
    (hMnonneg : 0 ≤ M)
    (hφ2 : (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) ≤ 1)
    (hψ2 : (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) ≤ 1) :
    ‖cayleyCutFunctional a φ ψ‖ ≤ M := by
  classical
  let L : ZMod p → ℝ := fun r => ‖leftFourierTest φ r‖
  let R : ZMod p → ℝ := fun r => ‖rightFourierTest ψ r‖
  have h_l1 :
      ‖cayleyCutFunctional a φ ψ‖ ≤ ∑ r : ZMod p,
        ‖normalizedDftFunction a r‖ * L r * R r := by
    simpa [L, R, mul_assoc] using norm_cayleyCutFunctional_le_fourier_l1 a φ ψ
  have h_by_M :
      ∑ r : ZMod p, ‖normalizedDftFunction a r‖ * L r * R r ≤
        ∑ r : ZMod p, M * (L r * R r) := by
    refine Finset.sum_le_sum ?_
    intro r _
    have hLR : 0 ≤ L r * R r := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖normalizedDftFunction a r‖ * L r * R r =
          ‖normalizedDftFunction a r‖ * (L r * R r) := by ring
      _ ≤ M * (L r * R r) := mul_le_mul_of_nonneg_right (hM r) hLR
  have hcs :
      ∑ r : ZMod p, L r * R r ≤
        Real.sqrt (∑ r : ZMod p, L r ^ 2) *
          Real.sqrt (∑ r : ZMod p, R r ^ 2) := by
    simpa [L, R] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ZMod p)) L R)
  have hsqrtL : Real.sqrt (∑ r : ZMod p, L r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa [L] using hφ2
  have hsqrtR : Real.sqrt (∑ r : ZMod p, R r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa [R] using hψ2
  have hsqrt_nonneg_L : 0 ≤ Real.sqrt (∑ r : ZMod p, L r ^ 2) := Real.sqrt_nonneg _
  have hsqrt_nonneg_R : 0 ≤ Real.sqrt (∑ r : ZMod p, R r ^ 2) := Real.sqrt_nonneg _
  have hprod :
      Real.sqrt (∑ r : ZMod p, L r ^ 2) *
          Real.sqrt (∑ r : ZMod p, R r ^ 2) ≤ 1 := by
    nlinarith
  have hsumLR : ∑ r : ZMod p, L r * R r ≤ 1 := hcs.trans hprod
  calc
    ‖cayleyCutFunctional a φ ψ‖
        ≤ ∑ r : ZMod p, ‖normalizedDftFunction a r‖ * L r * R r := h_l1
    _ ≤ ∑ r : ZMod p, M * (L r * R r) := h_by_M
    _ = M * ∑ r : ZMod p, L r * R r := by rw [Finset.mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hsumLR hMnonneg
    _ = M := by ring

/-- Finite spectral cut-norm control for one pair of bounded test functions.

This is the usable Lemma 2.5 core for the compact-Cayley route: if every
normalized Fourier coefficient of the Cayley kernel `a` has norm at most `M`,
then every double average against tests bounded by `1` has norm at most `M`. -/
lemma norm_cayleyCutFunctional_le_spectral
    {p : ℕ} [NeZero p] (a φ ψ : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M)
    (hMnonneg : 0 ≤ M)
    (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hψ : ∀ y, ‖ψ y‖ ≤ 1) :
    ‖cayleyCutFunctional a φ ψ‖ ≤ M := by
  exact norm_cayleyCutFunctional_le_spectral_of_fourier_l2 a φ ψ hM hMnonneg
    (sum_sq_norm_leftFourierTest_le_one_of_norm_le_one hφ)
    (sum_sq_norm_rightFourierTest_le_one_of_norm_le_one hψ)

/-- Predicate form of the spectral coefficient bound. -/
def SpectralBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) : Prop :=
  ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M

/-- Predicate form of the Cayley cut-norm bound: every double average against
tests bounded by `1` has norm at most `M`. -/
def CayleyCutBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) : Prop :=
  ∀ φ ψ : ZMod p → ℂ,
    (∀ x, ‖φ x‖ ≤ 1) → (∀ y, ‖ψ y‖ ≤ 1) →
      ‖cayleyCutFunctional a φ ψ‖ ≤ M

/-- Compact-Cayley Lemma 2.5 in predicate form. -/
theorem cayleyCutBound_of_spectralBound
    {p : ℕ} [NeZero p] (a : ZMod p → ℂ) {M : ℝ}
    (hMnonneg : 0 ≤ M) (hM : SpectralBound a M) :
    CayleyCutBound a M := by
  intro φ ψ hφ hψ
  exact norm_cayleyCutFunctional_le_spectral a φ ψ hM hMnonneg hφ hψ

end Erdos42.CompactCayley
