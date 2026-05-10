/-
Erdős Problem 42 — characters on the compact-Cayley compact dual.
-/

import Erdos.P42.CompactCayley.CompactDual
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.MeasureTheory.Group.Integral

namespace Erdos42.CompactCayley

open MeasureTheory
open scoped Classical ComplexConjugate Topology

noncomputable section

/-- The rational character module target `ℚ / ℤ`, embedded in the usual unit
circle. -/
noncomputable def ratAddCircleToCircleAdditive :
    AddCircle (1 : ℚ) →+ Additive Circle := by
  let f : ℚ →+ Additive Circle :=
    { toFun := fun q =>
        Additive.ofMul
          (AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ))))
      map_zero' := by
        simp
      map_add' := by
        intro a b
        ext
        simp [Rat.cast_add, AddCircle.toCircle_add] }
  refine QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ)) f ?_
  intro x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  change
    Additive.ofMul
        (AddCircle.toCircle
          ((((k • (1 : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ)))) = 0
  rw [ofMul_eq_zero]
  have hzero :
      (((k : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  simpa using congrArg (fun y : AddCircle (1 : ℝ) => AddCircle.toCircle y) hzero

lemma ratAddCircleToCircleAdditive_eq_zero
    {x : AddCircle (1 : ℚ)}
    (hx : ratAddCircleToCircleAdditive x = 0) :
    x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
      change ratAddCircleToCircleAdditive ((q : AddCircle (1 : ℚ))) = 0 at hx
      have hcircle :
          AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ))) = 1 := by
        have hx' :
            Additive.ofMul
              (AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ)))) = 0 := by
          simpa [ratAddCircleToCircleAdditive] using hx
        exact ofMul_eq_zero.mp hx'
      have hreal :
          (((q : ℝ) : AddCircle (1 : ℝ))) = 0 :=
        (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero)
          (by simpa using hcircle)
      rw [AddCircle.coe_eq_zero_iff] at hreal ⊢
      rcases hreal with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Rat.cast_injective (α := ℝ)
      simpa using hk

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Evaluation of a compact-dual character at an extraction quotient
frequency, viewed in `ℂ`. -/
noncomputable def characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) : ℂ :=
  (z (Multiplicative.ofAdd γ) : ℂ)

/-- Character evaluation on the additive compact-dual wrapper. -/
noncomputable def addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) : ℂ :=
  E.characterValue z.toMul γ

@[simp]
lemma characterValue_zero
    (E : CayleyExtraction S) (z : E.CompactDual) :
    E.characterValue z (0 : E.Group) = 1 := by
  simp [characterValue]

@[simp]
lemma characterValue_add
    (E : CayleyExtraction S) (z : E.CompactDual)
    (γ δ : E.Group) :
    E.characterValue z (γ + δ) =
      E.characterValue z γ * E.characterValue z δ := by
  simp [characterValue]

@[simp]
lemma characterValue_neg
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    E.characterValue z (-γ) = (E.characterValue z γ)⁻¹ := by
  simp [characterValue]

@[simp]
lemma star_characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    star (E.characterValue z γ) = E.characterValue z (-γ) := by
  unfold characterValue
  rw [show star (↑(z (Multiplicative.ofAdd γ)) : ℂ) =
      conj (↑(z (Multiplicative.ofAdd γ)) : ℂ) by rfl]
  rw [← Circle.coe_inv_eq_conj]
  simp

lemma characterValue_sub
    (E : CayleyExtraction S) (z : E.CompactDual)
    (γ δ : E.Group) :
    E.characterValue z (γ - δ) =
      E.characterValue z γ * star (E.characterValue z δ) := by
  rw [sub_eq_add_neg, characterValue_add, star_characterValue]

@[simp]
lemma characterValue_one_point
    (E : CayleyExtraction S) (γ : E.Group) :
    E.characterValue (1 : E.CompactDual) γ = 1 := by
  rfl

@[simp]
lemma characterValue_mul_point
    (E : CayleyExtraction S) (z w : E.CompactDual) (γ : E.Group) :
    E.characterValue (z * w) γ =
      E.characterValue z γ * E.characterValue w γ := by
  rfl

@[simp]
lemma characterValue_inv_point
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    E.characterValue z⁻¹ γ = (E.characterValue z γ)⁻¹ := by
  rfl

@[simp]
lemma addCharacterValue_zero
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    E.addCharacterValue z (0 : E.Group) = 1 := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_add
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ δ : E.Group) :
    E.addCharacterValue z (γ + δ) =
      E.addCharacterValue z γ * E.addCharacterValue z δ := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_neg
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue z (-γ) = (E.addCharacterValue z γ)⁻¹ := by
  simp [addCharacterValue]

@[simp]
lemma star_addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    star (E.addCharacterValue z γ) = E.addCharacterValue z (-γ) := by
  simp [addCharacterValue, star_characterValue]

lemma addCharacterValue_sub
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ δ : E.Group) :
    E.addCharacterValue z (γ - δ) =
      E.addCharacterValue z γ * star (E.addCharacterValue z δ) := by
  simpa [addCharacterValue] using E.characterValue_sub z.toMul γ δ

@[simp]
lemma addCharacterValue_zero_point
    (E : CayleyExtraction S) (γ : E.Group) :
    E.addCharacterValue (0 : E.CompactAddDual) γ = 1 := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_add_point
    (E : CayleyExtraction S) (z w : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue (z + w) γ =
      E.addCharacterValue z γ * E.addCharacterValue w γ := by
  simp [addCharacterValue]

lemma addCharacterValue_nsmul_frequency
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ : E.Group) (n : ℕ) :
    E.addCharacterValue z (n • γ) =
      (E.addCharacterValue z γ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, E.addCharacterValue_add, ih, pow_succ]

lemma addCharacterValue_nsmul_point
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ : E.Group) (n : ℕ) :
    E.addCharacterValue (n • z) γ =
      (E.addCharacterValue z γ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, E.addCharacterValue_add_point, ih, pow_succ]

@[simp]
lemma addCharacterValue_neg_point
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue (-z) γ = (E.addCharacterValue z γ)⁻¹ := by
  simp [addCharacterValue]

@[simp]
lemma norm_characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    ‖E.characterValue z γ‖ = 1 :=
  Circle.norm_coe _

@[simp]
lemma norm_addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    ‖E.addCharacterValue z γ‖ = 1 := by
  simp [addCharacterValue]

lemma characterValue_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactDual => E.characterValue z γ) := by
  unfold characterValue CompactDual PontryaginDual
  exact continuous_subtype_val.comp (continuous_eval_const (Multiplicative.ofAdd γ))

lemma addCharacterValue_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactAddDual => E.addCharacterValue z γ) := by
  simpa [addCharacterValue] using E.characterValue_continuous γ

@[simp]
lemma integral_addCharacterValue_zero
    (E : CayleyExtraction S) :
    ∫ z : E.CompactAddDual,
        E.addCharacterValue z (0 : E.Group) ∂E.haar = 1 := by
  simp

/-- Haar orthogonality for a character once a point where it is nontrivial has
been supplied.  The separate Pontryagin-dual separation theorem should provide
this witness for every nonzero extraction frequency. -/
lemma integral_addCharacterValue_eq_zero_of_exists_ne_one
    (E : CayleyExtraction S) (γ : E.Group)
    (hne : ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar = 0 := by
  classical
  rcases hne with ⟨y, hy⟩
  let I : ℂ :=
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar
  have htrans :
      (∫ z : E.CompactAddDual,
          E.addCharacterValue (y + z) γ ∂E.haar) = I := by
    simpa [I] using
      (integral_add_left_eq_self
        (μ := E.haar)
        (fun z : E.CompactAddDual => E.addCharacterValue z γ) y)
  have hleft :
      (∫ z : E.CompactAddDual,
          E.addCharacterValue (y + z) γ ∂E.haar) =
        E.addCharacterValue y γ * I := by
    simp_rw [E.addCharacterValue_add_point y]
    simp [I, integral_const_mul]
  have hscalar : E.addCharacterValue y γ * I = I := by
    rw [← hleft, htrans]
  have hzero : (E.addCharacterValue y γ - 1) * I = 0 := by
    calc
      (E.addCharacterValue y γ - 1) * I =
          E.addCharacterValue y γ * I - I := by ring
      _ = I - I := by rw [hscalar]
      _ = 0 := by ring
  have hfactor : E.addCharacterValue y γ - 1 ≠ 0 := sub_ne_zero.mpr hy
  exact (mul_eq_zero.mp hzero).resolve_left hfactor

lemma integral_addCharacterValue_eq_if_of_separating
    (E : CayleyExtraction S)
    (hsep :
      ∀ γ : E.Group, γ ≠ 0 →
        ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1)
    (γ : E.Group) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar =
      if γ = 0 then 1 else 0 := by
  by_cases hγ : γ = 0
  · subst γ
    simp
  · simp [hγ, E.integral_addCharacterValue_eq_zero_of_exists_ne_one γ (hsep γ hγ)]

lemma exists_dual_point_ne_one
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ :=
    CharacterModule.exists_character_apply_ne_zero_of_ne_zero
      (A := E.Group) (a := γ) hγ
  let ψ : E.Group →+ Additive Circle :=
    ratAddCircleToCircleAdditive.comp c
  have hψ : ψ γ ≠ 0 := by
    intro hzero
    exact hc (ratAddCircleToCircleAdditive_eq_zero hzero)
  let mψ : E.DualDomain →* Circle :=
    AddMonoidHom.toMultiplicativeLeft ψ
  let z : E.CompactDual :=
    { toMonoidHom := mψ
      continuous_toFun := continuous_of_discreteTopology }
  refine ⟨Additive.ofMul z, ?_⟩
  intro htriv
  have hcircle : (ψ γ).toMul = 1 := by
    apply Subtype.ext
    simpa [addCharacterValue, characterValue, z, mψ, ψ] using htriv
  exact hψ (toMul_eq_one.mp hcircle)

lemma integral_addCharacterValue
    (E : CayleyExtraction S) (γ : E.Group) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar =
      if γ = 0 then 1 else 0 :=
  E.integral_addCharacterValue_eq_if_of_separating
    (fun _ hγ => E.exists_dual_point_ne_one hγ) γ

end CayleyExtraction

end

end Erdos42.CompactCayley
