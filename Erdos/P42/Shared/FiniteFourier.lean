/-
Erdős Problem 42 — finite-Fourier predicates used by the route-axioms.

These predicates use Mathlib's discrete Fourier transform on `ZMod p`. The
transform `ZMod.dft` is unnormalized, so `normalizedDftCoeff` multiplies by
`p⁻¹`, matching the averaged Fourier coefficients in the compact-Cayley and
Fourier-positive notes.

`FourierLowerIndicator` is used by Route A: lower bound `Re ≥ -ε`.
`FourierUpperIndicator` is used by Route B: upper bound `Re ≤ ε` at
nontrivial characters.
-/

import Erdos.P42.Shared.Common
import Mathlib.Analysis.Fourier.ZMod

namespace Erdos42

open scoped BigOperators ZMod

/-- Complex-valued indicator of a finite set in `ZMod p`. -/
noncomputable def indicatorC {p : ℕ} (T : Finset (ZMod p)) : ZMod p → ℂ :=
  fun x => if x ∈ T then 1 else 0

/-- Normalized DFT coefficient of an arbitrary complex-valued function on
`ZMod p`. This is the common finite-Fourier primitive needed for both axiom
removal projects; `normalizedDftCoeff` is the indicator-specialized version. -/
noncomputable def normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  ((p : ℂ)⁻¹) * (ZMod.dft f r)

/-- Normalized DFT coefficient of the indicator of `T`.

Mathlib's `ZMod.dft` is the counting-measure transform
`∑ x, stdAddChar (-(x * r)) • f x`; the compact-Cayley statements use the
averaged coefficient, hence the factor `(p : ℂ)⁻¹`. -/
noncomputable def normalizedDftCoeff {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) : ℂ :=
  normalizedDftFunction (indicatorC T) r

/-- Normalized Fourier *lower* bound: every character of `ZMod p` evaluated on
`1_F` has real part `≥ -ε`. Used by Route A (Fourier-positive). -/
def FourierLowerIndicator {p : ℕ} [NeZero p] (F : Finset (ZMod p)) (ε : ℝ) : Prop :=
  ∀ r : ZMod p, -(ε : ℝ) ≤ (normalizedDftCoeff F r).re

/-- Normalized Fourier *upper* bound: every nontrivial character of `ZMod p`
evaluated on `1_T` has real part `≤ ε`. Used by Route B (compact Cayley). -/
def FourierUpperIndicator {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (ε : ℝ) : Prop :=
  ∀ r : ZMod p, r ≠ 0 → (normalizedDftCoeff T r).re ≤ ε

lemma normalizedDftFunction_eq_sum {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction, ZMod.dft_apply]
  simp [smul_eq_mul]

lemma normalizedDftFunction_zero_eq_average {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) :
    normalizedDftFunction f 0 =
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, f x := by
  rw [normalizedDftFunction_eq_sum]
  simp

@[simp] lemma normalizedDftFunction_zero_fun {p : ℕ} [NeZero p]
    (r : ZMod p) :
    normalizedDftFunction (fun _ : ZMod p => 0) r = 0 := by
  rw [normalizedDftFunction_eq_sum]
  simp

lemma normalizedDftFunction_add {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => f x + g x) r =
      normalizedDftFunction f r + normalizedDftFunction g r := by
  rw [normalizedDftFunction_eq_sum, normalizedDftFunction_eq_sum,
    normalizedDftFunction_eq_sum]
  simp [mul_add, Finset.sum_add_distrib]

lemma normalizedDftFunction_neg {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => -f x) r =
      - normalizedDftFunction f r := by
  rw [normalizedDftFunction_eq_sum, normalizedDftFunction_eq_sum]
  simp [Finset.mul_sum]

lemma normalizedDftFunction_sub {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => f x - g x) r =
      normalizedDftFunction f r - normalizedDftFunction g r := by
  simp [sub_eq_add_neg, normalizedDftFunction_add, normalizedDftFunction_neg]

lemma normalizedDftFunction_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => c * f x) r =
      c * normalizedDftFunction f r := by
  rw [normalizedDftFunction_eq_sum, normalizedDftFunction_eq_sum]
  simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma normalizedDftCoeff_eq_sum {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) :
    normalizedDftCoeff T r =
      ((p : ℂ)⁻¹) * ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) := by
  classical
  rw [normalizedDftCoeff, normalizedDftFunction_eq_sum]
  simp [indicatorC]

lemma normalizedDftCoeff_zero_eq_card_div {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) :
    normalizedDftCoeff T 0 = (T.card : ℂ) / (p : ℂ) := by
  rw [normalizedDftCoeff_eq_sum]
  simp [div_eq_inv_mul]

/-- Fourier inversion in the normalized convention, for arbitrary functions. -/
lemma function_eq_sum_normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x =
      ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r := by
  classical
  have h :=
    congrFun (LinearEquiv.symm_apply_apply (ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ))
      f) x
  calc
    f x =
        ((p : ℂ)⁻¹) * ∑ r : ZMod p,
          ZMod.stdAddChar (r * x) * ZMod.dft f r := by
          simpa [ZMod.invDFT_apply, smul_eq_mul] using h.symm
    _ = ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r := by
          simp [normalizedDftFunction, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Fourier inversion in the normalization used by the compact-Cayley route. -/
lemma indicatorC_eq_sum_normalizedDftCoeff {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (x : ZMod p) :
    indicatorC T x =
      ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftCoeff T r := by
  simpa [normalizedDftCoeff] using
    function_eq_sum_normalizedDftFunction (p := p) (indicatorC T) x

lemma sum_stdAddChar_neg_mul_eq_zero_of_ne_zero
    {p : ℕ} [Fact p.Prime] [NeZero p] {r : ZMod p} (hr : r ≠ 0) :
    ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) = 0 := by
  classical
  have hnontrivial :
      AddChar.mulShift (ZMod.stdAddChar (N := p)) (-r) ≠ 1 :=
    (ZMod.isPrimitive_stdAddChar p) (by simpa using neg_ne_zero.mpr hr)
  have hsum :
      ∑ x : ZMod p, AddChar.mulShift (ZMod.stdAddChar (N := p)) (-r) x = 0 :=
    AddChar.sum_eq_zero_of_ne_one hnontrivial
  simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

lemma sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) =
      ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
  classical
  refine Finset.sum_bij (fun x hx => -x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (hT x).mp hx
  · intro x₁ hx₁ x₂ hx₂ h
    exact neg_injective h
  · intro y hy
    refine ⟨-y, ?_, ?_⟩
    · have hy' : - -y ∈ T := by simpa using hy
      exact (hT (-y)).mpr hy'
    · simp
  · intro x hx
    simp

lemma star_sum_stdAddChar_neg_mul_eq_self_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (starRingEnd ℂ) (∑ x ∈ T, ZMod.stdAddChar (-(x * r))) =
      ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) := by
  classical
  calc
    (starRingEnd ℂ) (∑ x ∈ T, ZMod.stdAddChar (-(x * r)))
        = ∑ x ∈ T, (starRingEnd ℂ) (ZMod.stdAddChar (-(x * r))) := by
          rw [map_sum]
    _ = ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hchar := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (x * r)
          simp [hchar] at *
    _ = ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) :=
          (sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric hT r).symm

lemma star_normalizedDftCoeff_eq_self_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (starRingEnd ℂ) (normalizedDftCoeff T r) = normalizedDftCoeff T r := by
  rw [normalizedDftCoeff_eq_sum]
  simp [star_sum_stdAddChar_neg_mul_eq_self_of_symmetric hT r]

lemma normalizedDftCoeff_im_eq_zero_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (normalizedDftCoeff T r).im = 0 := by
  have h := congrArg Complex.im (star_normalizedDftCoeff_eq_self_of_symmetric hT r)
  simp at h
  linarith

lemma normalizedDftCoeff_neg_eq_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    normalizedDftCoeff T (-r) = normalizedDftCoeff T r := by
  rw [normalizedDftCoeff_eq_sum, normalizedDftCoeff_eq_sum]
  congr 1
  calc
    (∑ x ∈ T, ZMod.stdAddChar (-(x * -r))) =
        ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          congr 1
          ring
    _ = ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) :=
          (sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric hT r).symm

end Erdos42
