/-
Erdős Problem 42 — trigonometric polynomials for compact-Cayley extraction.

This is the finite-support Fourier-polynomial interface on the extraction
quotient, together with finite cyclic lifts and the zero-frequency finite
average convergence that follows from relation-stable quotient lifts.
-/

import Erdos.P42.CompactCayley.Characters
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace Erdos42.CompactCayley

open Filter Complex MeasureTheory
open scoped BigOperators Classical ComplexConjugate Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Finitely supported Fourier polynomials on the extraction quotient. -/
abbrev TrigPoly (E : CayleyExtraction S) : Type :=
  E.Group →₀ ℂ

/-- Compact-dual evaluation of an extraction trigonometric polynomial. -/
noncomputable def TrigPoly.eval
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactDual) : ℂ :=
  P.sum fun γ c => c * E.characterValue z γ

/-- Additive-wrapper compact-dual evaluation. -/
noncomputable def TrigPoly.evalAdd
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactAddDual) : ℂ :=
  P.sum fun γ c => c * E.addCharacterValue z γ

/-- Finite cyclic lift of a trigonometric polynomial. -/
noncomputable def TrigPoly.evalFinite
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  P.sum fun γ c => c * ZMod.stdAddChar (-(E.lift n γ * x))

/-- Normalized finite average of a lifted trigonometric polynomial. -/
noncomputable def TrigPoly.finiteAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) => P.evalFinite n x

/-- Finite average of a lifted trigonometric polynomial against the Cayley-set
indicator. -/
noncomputable def TrigPoly.indicatorWeightedFiniteAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    indicatorC (S.T (E.φ n)) x * P.evalFinite n x

/-- Abstract compact average, represented algebraically by the zero-frequency
coefficient. -/
noncomputable def TrigPoly.compactAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) : ℂ :=
  P (0 : E.Group)

/-- Compact-limit coefficient functional obtained by pairing a trigonometric
polynomial with the extracted Cayley Fourier coefficient limits. -/
noncomputable def TrigPoly.indicatorCoeffFunctional
    {E : CayleyExtraction S} (P : E.TrigPoly) : ℂ :=
  P.sum fun γ c => c * E.coeff γ

lemma TrigPoly.evalAdd_eq_eval
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactAddDual) :
    TrigPoly.evalAdd P z = TrigPoly.eval P z.toMul := by
  rfl

lemma TrigPoly.eval_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (z : E.CompactDual) :
    TrigPoly.eval (P + Q) z =
      TrigPoly.eval P z + TrigPoly.eval Q z := by
  unfold TrigPoly.eval
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * E.characterValue z γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma TrigPoly.evalAdd_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (z : E.CompactAddDual) :
    TrigPoly.evalAdd (P + Q) z =
      TrigPoly.evalAdd P z + TrigPoly.evalAdd Q z := by
  simpa [TrigPoly.evalAdd_eq_eval] using
    TrigPoly.eval_add P Q z.toMul

@[simp]
lemma TrigPoly.eval_zero
    {E : CayleyExtraction S} (z : E.CompactDual) :
    TrigPoly.eval (0 : E.TrigPoly) z = 0 := by
  simp [TrigPoly.eval]

@[simp]
lemma TrigPoly.evalAdd_zero
    {E : CayleyExtraction S} (z : E.CompactAddDual) :
    TrigPoly.evalAdd (0 : E.TrigPoly) z = 0 := by
  simp [TrigPoly.evalAdd_eq_eval]

@[simp]
lemma TrigPoly.eval_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (z : E.CompactDual) :
    TrigPoly.eval (Finsupp.single γ c : E.TrigPoly) z =
      c * E.characterValue z γ := by
  simp [TrigPoly.eval]

@[simp]
lemma TrigPoly.evalAdd_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z =
      c * E.addCharacterValue z γ := by
  simp [TrigPoly.evalAdd]

@[simp]
lemma TrigPoly.eval_single_zero
    {E : CayleyExtraction S} (c : ℂ) (z : E.CompactDual) :
    TrigPoly.eval
        (Finsupp.single (0 : E.Group) c : E.TrigPoly) z = c := by
  simp

@[simp]
lemma TrigPoly.evalAdd_single_zero
    {E : CayleyExtraction S} (c : ℂ) (z : E.CompactAddDual) :
    TrigPoly.evalAdd
        (Finsupp.single (0 : E.Group) c : E.TrigPoly) z = c := by
  simp

lemma TrigPoly.continuous_eval
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Continuous (fun z : E.CompactDual => TrigPoly.eval P z) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simpa using (continuous_const :
      Continuous (fun _ : E.CompactDual => (0 : ℂ)))
  · intro P Q hP hQ
    simpa [TrigPoly.eval_add] using hP.add hQ
  · intro γ c
    simpa using
      (continuous_const.mul (E.characterValue_continuous γ) :
        Continuous fun z : E.CompactDual => c * E.characterValue z γ)

lemma TrigPoly.continuous_evalAdd
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Continuous (fun z : E.CompactAddDual => TrigPoly.evalAdd P z) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simpa using (continuous_const :
      Continuous (fun _ : E.CompactAddDual => (0 : ℂ)))
  · intro P Q hP hQ
    simpa [TrigPoly.evalAdd_add] using hP.add hQ
  · intro γ c
    simpa using
      (continuous_const.mul (E.addCharacterValue_continuous γ) :
        Continuous fun z : E.CompactAddDual => c * E.addCharacterValue z γ)

lemma TrigPoly.integrable_evalAdd
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Integrable (fun z : E.CompactAddDual => TrigPoly.evalAdd P z) E.haar :=
  (TrigPoly.continuous_evalAdd E P).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma TrigPoly.integral_evalAdd_eq_compactAverage
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    ∫ z : E.CompactAddDual, TrigPoly.evalAdd P z ∂E.haar =
      TrigPoly.compactAverage P := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [TrigPoly.compactAverage]
  · intro P Q hP hQ
    rw [show
        (fun z : E.CompactAddDual => TrigPoly.evalAdd (P + Q) z) =
          fun z => TrigPoly.evalAdd P z + TrigPoly.evalAdd Q z by
        funext z
        exact TrigPoly.evalAdd_add P Q z]
    rw [integral_add (TrigPoly.integrable_evalAdd E P)
      (TrigPoly.integrable_evalAdd E Q), hP, hQ]
    simp [TrigPoly.compactAverage]
  · intro γ c
    by_cases hγ : γ = 0
    · subst γ
      simp [TrigPoly.compactAverage]
    · rw [show
          (fun z : E.CompactAddDual =>
              TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z) =
            fun z => c * E.addCharacterValue z γ by
          funext z
          simp]
      rw [integral_const_mul]
      rw [E.integral_addCharacterValue]
      simp [hγ, TrigPoly.compactAverage, Finsupp.single_eq_of_ne (Ne.symm hγ)]

lemma TrigPoly.integrable_evalAdd_mul_char
    (E : CayleyExtraction S) (P : E.TrigPoly) (γ : E.Group) :
    Integrable
      (fun z : E.CompactAddDual =>
        TrigPoly.evalAdd P z * E.addCharacterValue z γ) E.haar :=
  ((TrigPoly.continuous_evalAdd E P).mul
      (E.addCharacterValue_continuous γ)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma TrigPoly.integral_evalAdd_mul_char
    (E : CayleyExtraction S) (P : E.TrigPoly) (γ : E.Group) :
    ∫ z : E.CompactAddDual,
        TrigPoly.evalAdd P z * E.addCharacterValue z γ ∂E.haar =
      P (-γ) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp
  · intro P Q hP hQ
    rw [show
        (fun z : E.CompactAddDual =>
            TrigPoly.evalAdd (P + Q) z * E.addCharacterValue z γ) =
          fun z =>
            TrigPoly.evalAdd P z * E.addCharacterValue z γ +
              TrigPoly.evalAdd Q z * E.addCharacterValue z γ by
        funext z
        rw [TrigPoly.evalAdd_add]
        ring]
    rw [integral_add (TrigPoly.integrable_evalAdd_mul_char E P γ)
      (TrigPoly.integrable_evalAdd_mul_char E Q γ), hP, hQ]
    simp
  · intro δ c
    rw [show
        (fun z : E.CompactAddDual =>
            TrigPoly.evalAdd (Finsupp.single δ c : E.TrigPoly) z *
              E.addCharacterValue z γ) =
          fun z => c * E.addCharacterValue z (δ + γ) by
        funext z
        simp only [TrigPoly.evalAdd_single]
        rw [mul_assoc]
        rw [← E.addCharacterValue_add]]
    rw [integral_const_mul, E.integral_addCharacterValue]
    by_cases hδγ : δ + γ = 0
    · have hδ : δ = -γ := by
        exact eq_neg_of_add_eq_zero_left hδγ
      subst δ
      simp
    · have hδ : δ ≠ -γ := by
        intro h
        subst h
        exact hδγ (by simp)
      rw [Finsupp.single_eq_of_ne (Ne.symm hδ)]
      simp [hδγ]

lemma TrigPoly.integral_evalAdd_eq_compactAverage_of_separating
    (E : CayleyExtraction S)
    (_hsep :
      ∀ γ : E.Group, γ ≠ 0 →
        ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1)
    (P : E.TrigPoly) :
    ∫ z : E.CompactAddDual, TrigPoly.evalAdd P z ∂E.haar =
      TrigPoly.compactAverage P :=
  TrigPoly.integral_evalAdd_eq_compactAverage E P

@[simp]
lemma TrigPoly.evalFinite_zero
    {E : CayleyExtraction S} (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (0 : E.TrigPoly) n x = 0 := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  simp [TrigPoly.evalFinite]

@[simp]
lemma TrigPoly.evalFinite_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (Finsupp.single γ c : E.TrigPoly) n x =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        c * ZMod.stdAddChar (-(E.lift n γ * x))) := by
  simp [TrigPoly.evalFinite]

lemma TrigPoly.evalFinite_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (P + Q) n x =
      TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  classical
  unfold TrigPoly.evalFinite
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * ZMod.stdAddChar (-(E.lift n γ * x))
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma TrigPoly.finiteAverage_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (n : ℕ) :
    TrigPoly.finiteAverage (P + Q) n =
      TrigPoly.finiteAverage P n + TrigPoly.finiteAverage Q n := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.finiteAverage
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (P + Q) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x) by
        funext x
        exact TrigPoly.evalFinite_add P Q n x]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma TrigPoly.indicatorWeightedFiniteAverage_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (n : ℕ) :
    TrigPoly.indicatorWeightedFiniteAverage (P + Q) n =
      TrigPoly.indicatorWeightedFiniteAverage P n +
        TrigPoly.indicatorWeightedFiniteAverage Q n := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.indicatorWeightedFiniteAverage
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite (P + Q) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite P n x +
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite Q n x) by
        funext x
        rw [TrigPoly.evalFinite_add]
        ring]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

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

lemma normalizedDftFunction_eq_avgZMod {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      avgZMod fun x : ZMod p => ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction_eq_sum]
  rfl

lemma TrigPoly.finiteAverage_single_eq_coeff_of_lift_eq_zero
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    (hγ : E.lift n γ = 0) :
    TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = c := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [TrigPoly.finiteAverage]
  simp [TrigPoly.evalFinite_single, hγ, avgZMod_const]

lemma TrigPoly.finiteAverage_single_eq_zero_of_lift_ne_zero
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    (hγ : E.lift n γ ≠ 0) :
    TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = 0 := by
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [TrigPoly.finiteAverage]
  simp [TrigPoly.evalFinite_single, avgZMod_const_mul,
    avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero hγ]

lemma TrigPoly.normalizedDftFunction_evalFinite_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (Finsupp.single γ c : E.TrigPoly) n x) r =
      if r + E.lift n γ = 0 then c else 0 := by
  rw [normalizedDftFunction_eq_avgZMod]
  simp [TrigPoly.evalFinite_single]
  calc
    avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          ZMod.stdAddChar (-(x * r)) *
            (c * ZMod.stdAddChar (-(E.lift n γ * x))))
        =
      avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          c * ZMod.stdAddChar (-((r + E.lift n γ) * x))) := by
          congr 1
          funext x
          calc
            ZMod.stdAddChar (-(x * r)) *
                (c * ZMod.stdAddChar (-(E.lift n γ * x)))
                =
              c * (ZMod.stdAddChar (-(x * r)) *
                ZMod.stdAddChar (-(E.lift n γ * x))) := by
                ring
            _ =
              c * ZMod.stdAddChar (-((r + E.lift n γ) * x)) := by
                congr 1
                rw [← ZMod.stdAddChar.map_add_eq_mul]
                congr 1
                ring
    _ =
      c * avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          ZMod.stdAddChar (-((r + E.lift n γ) * x))) := by
          rw [avgZMod_const_mul]
    _ = if r + E.lift n γ = 0 then c else 0 := by
          rw [avgZMod_stdAddChar_neg_mul_eq_ite]
          by_cases h : r + E.lift n γ = 0 <;> simp [h]

lemma TrigPoly.indicatorWeightedFiniteAverage_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ) :
    TrigPoly.indicatorWeightedFiniteAverage
        (Finsupp.single γ c : E.TrigPoly) n =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        c * normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)) := by
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.indicatorWeightedFiniteAverage
  change avgZMod
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
    c * normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        c * (ZMod.stdAddChar (-(x * E.lift n γ)) *
          indicatorC (S.T (E.φ n)) x)) by
        funext x
        simp [TrigPoly.evalFinite_single]
        ring_nf]
  rw [avgZMod_const_mul]
  congr 1

lemma TrigPoly.indicatorCoeffFunctional_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) :
    TrigPoly.indicatorCoeffFunctional (P + Q) =
      TrigPoly.indicatorCoeffFunctional P +
        TrigPoly.indicatorCoeffFunctional Q := by
  unfold TrigPoly.indicatorCoeffFunctional
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * E.coeff γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

@[simp]
lemma TrigPoly.indicatorCoeffFunctional_zero
    {E : CayleyExtraction S} :
    TrigPoly.indicatorCoeffFunctional (0 : E.TrigPoly) = 0 := by
  simp [TrigPoly.indicatorCoeffFunctional]

lemma TrigPoly.indicatorCoeffFunctional_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) :
    TrigPoly.indicatorCoeffFunctional
        (Finsupp.single γ c : E.TrigPoly) =
      c * E.coeff γ := by
  simp [TrigPoly.indicatorCoeffFunctional]

lemma TrigPoly.normalizedDftFunction_evalFinite
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite P n x) r =
      P.sum fun γ c => if r + E.lift n γ = 0 then c else 0 := by
  classical
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [normalizedDftFunction_zero_fun]
  · intro P Q hP hQ
    have hfun :
      (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (P + Q) n x) =
        fun x =>
          TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x := by
      funext x
      exact TrigPoly.evalFinite_add P Q n x
    rw [hfun]
    rw [normalizedDftFunction_add, hP, hQ]
    let h : E.Group → ℂ →+ ℂ := fun γ =>
      { toFun := fun c => if r + E.lift n γ = 0 then c else 0
        map_zero' := by by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ]
        map_add' := by
          intro a b
          by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ] }
    change Finsupp.sum P (fun γ c => h γ c) +
        Finsupp.sum Q (fun γ c => h γ c) =
      Finsupp.sum (P + Q) (fun γ c => h γ c)
    rw [Finsupp.sum_hom_add_index]
  · intro γ c
    simpa using TrigPoly.normalizedDftFunction_evalFinite_single
      (E := E) γ c n r

lemma TrigPoly.sum_if_neg_lift_add_eq_zero_eq_apply_of_injOn
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    (γ : E.Group)
    (hinj :
      Set.InjOn
        (fun δ : E.Group => E.lift n δ)
        {δ : E.Group | δ ∈ insert γ P.support}) :
    P.sum (fun δ c =>
        if -E.lift n γ + E.lift n δ = 0 then c else 0) =
      P γ := by
  classical
  unfold Finsupp.sum
  rw [Finset.sum_eq_single γ]
  · simp
  · intro δ hδ hδγ
    have hnot : ¬ (-E.lift n γ + E.lift n δ = 0) := by
      intro hzero
      have heq : E.lift n δ = E.lift n γ := by
        have h := congrArg (fun z : ZMod (S.p (E.φ n)) => z + E.lift n γ) hzero
        simpa [add_comm, add_left_comm, add_assoc] using h
      exact hδγ (hinj
        (Finset.mem_insert.mpr (Or.inr hδ))
        (Finset.mem_insert_self γ P.support)
        heq)
    simp [hnot]
  · intro hγ
    have hpγ : P γ = 0 := Finsupp.notMem_support_iff.mp hγ
    simp [hpγ]

lemma TrigPoly.finiteAverage_single_zero_eventually_eq_coeff
    (E : CayleyExtraction S) (c : ℂ) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage
          (Finsupp.single (0 : E.Group) c : E.TrigPoly) n = c := by
  filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hn
  exact TrigPoly.finiteAverage_single_eq_coeff_of_lift_eq_zero
    (E := E) (0 : E.Group) c n hn

lemma finiteLift_eventually_ne_zero
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    ∀ᶠ n in atTop, E.lift n γ ≠ 0 :=
  E.data.finiteLift_eventually_ne_zero hγ

lemma TrigPoly.finiteAverage_single_eq_zero_eventually_of_ne_zero
    (E : CayleyExtraction S) {γ : E.Group}
    (hγ : γ ≠ 0) (c : ℂ) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = 0 := by
  filter_upwards [E.finiteLift_eventually_ne_zero hγ] with n hn
  exact TrigPoly.finiteAverage_single_eq_zero_of_lift_ne_zero
    (E := E) γ c n hn

/-- Along relation-stable extraction data, finite averages of lifted
trigonometric polynomials are eventually their zero-frequency coefficient. -/
lemma TrigPoly.finiteAverage_eventually_eq_zeroCoeff
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage P n = P (0 : E.Group) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [TrigPoly.finiteAverage, avgZMod]
  · intro P Q hP hQ
    filter_upwards [hP, hQ] with n hp hq
    rw [TrigPoly.finiteAverage_add, hp, hq]
    rfl
  · intro γ c
    by_cases hγ : γ = 0
    · subst hγ
      simpa [Finsupp.single_eq_same] using
        TrigPoly.finiteAverage_single_zero_eventually_eq_coeff E c
    · filter_upwards
        [TrigPoly.finiteAverage_single_eq_zero_eventually_of_ne_zero E hγ c] with n hn
      rw [hn]
      exact (Finsupp.single_eq_of_ne (Ne.symm hγ) :
        (Finsupp.single γ c : E.TrigPoly) (0 : E.Group) = 0).symm

lemma TrigPoly.finiteAverage_tendsto_zeroCoeff
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto (fun n => TrigPoly.finiteAverage P n) atTop
      (𝓝 (P (0 : E.Group))) := by
  have h :
      (fun _ : ℕ => P (0 : E.Group)) =ᶠ[atTop]
        fun n => TrigPoly.finiteAverage P n := by
    filter_upwards [TrigPoly.finiteAverage_eventually_eq_zeroCoeff E P] with n hn
    exact hn.symm
  exact tendsto_const_nhds.congr' h

lemma TrigPoly.finiteAverage_tendsto_compactAverage
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto (fun n => TrigPoly.finiteAverage P n) atTop
      (𝓝 (TrigPoly.compactAverage P)) := by
  simpa [TrigPoly.compactAverage] using
    TrigPoly.finiteAverage_tendsto_zeroCoeff E P

lemma TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto
      (fun n => TrigPoly.indicatorWeightedFiniteAverage P n)
      atTop (𝓝 (TrigPoly.indicatorCoeffFunctional P)) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [TrigPoly.indicatorWeightedFiniteAverage,
      TrigPoly.indicatorCoeffFunctional, avgZMod]
  · intro P Q hP hQ
    rw [TrigPoly.indicatorCoeffFunctional_add P Q]
    exact (hP.add hQ).congr' (Filter.Eventually.of_forall fun n => by
      exact (TrigPoly.indicatorWeightedFiniteAverage_add P Q n).symm)
  · intro γ c
    rw [TrigPoly.indicatorCoeffFunctional_single γ c]
    have hcoeff := E.coeff_tendsto γ
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have hmul := hc.mul hcoeff
    exact hmul.congr' (Filter.Eventually.of_forall fun n => by
      exact (TrigPoly.indicatorWeightedFiniteAverage_single γ c n).symm)

end CayleyExtraction

end

end Erdos42.CompactCayley
