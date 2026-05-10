/-
Erdős Problem 42 — Layer 1 continuous-analogue lemma.

Following Tao's May 2026 forum comment + natso26's clean exposition
(`fourier_positive_ulam_note.pdf`). The geometric core
`closed_proper_subgroup_haar_null` is proved here axiom-free; the main
`tao_continuous_avoidance` lemma is also proved once the standard measurable
group assumptions needed by Mathlib's Haar shear lemmas are available.

This file is shared scaffolding: Route A (Fourier-positive) eventually uses it
as the continuous endpoint of the U²-regularity / counting argument. Route B
(compact Cayley) uses a closely related lemma in its clique-forcing proof
(Lemma 2.7 of the compact Cayley PDF), which is also a candidate destination
for `closed_proper_subgroup_haar_null` once we open that black box.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos42

open Filter Set Finset MeasureTheory
open scoped Pointwise Topology

universe u

/-- A nonnegative integrable real-valued function that is positive almost
everywhere on a probability space has positive integral. -/
lemma integral_pos_of_ae_pos_of_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {F : α → ℝ} (hFint : Integrable F μ)
    (hFnonneg : 0 ≤ᵐ[μ] F) (hFpos : ∀ᵐ x ∂μ, 0 < F x) :
    0 < ∫ x, F x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae hFnonneg hFint]
  have hsupp_ae : ∀ᵐ x ∂μ, x ∈ Function.support F := by
    filter_upwards [hFpos] with x hx
    exact ne_of_gt hx
  have hcompl_zero : μ (Function.support F)ᶜ = 0 := by
    rwa [ae_iff] at hsupp_ae
  by_contra hnot
  have hsupp_zero : μ (Function.support F) = 0 := by
    exact le_antisymm (not_lt.mp hnot) bot_le
  have h_univ_zero : μ (Set.univ : Set α) = 0 := by
    have hcover : (Set.univ : Set α) =
        Function.support F ∪ (Function.support F)ᶜ := by
      ext x
      simp
    refine le_antisymm ?_ bot_le
    calc
      μ (Set.univ : Set α) =
          μ (Function.support F ∪ (Function.support F)ᶜ) := by rw [hcover]
      _ ≤ μ (Function.support F) + μ (Function.support F)ᶜ :=
          measure_union_le _ _
      _ = 0 := by simp [hsupp_zero, hcompl_zero]
  have h_univ_one : μ (Set.univ : Set α) = 1 := measure_univ
  norm_num [h_univ_one] at h_univ_zero

/-- Edge set of `K_M`, oriented by the natural order. This is the continuous
analogue of the finite ordered-clique product in the compact-Cayley proof. -/
def continuousCliqueEdgePairs (M : ℕ) : Finset (Fin M × Fin M) :=
  (Finset.univ : Finset (Fin M × Fin M)).filter (fun e => e.1 < e.2)

/-- Product kernel for the continuous `K_M` Cayley density. -/
noncomputable def continuousCliqueKernel
    {G : Type u} [Sub G] (M : ℕ) (f : G → ℝ) (x : Fin M → G) : ℝ :=
  ∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)

/-- Continuous Cayley `K_M` density associated to a kernel `f`. -/
noncomputable def continuousCliqueDensity
    {G : Type u} [MeasurableSpace G] [Sub G]
    (μ : Measure G) (M : ℕ) (f : G → ℝ) : ℝ :=
  ∫ x : Fin M → G, continuousCliqueKernel M f x ∂Measure.pi (fun _ : Fin M => μ)

lemma abs_prod_sub_prod_le_sum_abs
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf_nonneg : ∀ i ∈ s, 0 ≤ f i)
    (hf_le : ∀ i ∈ s, f i ≤ 1)
    (hg_nonneg : ∀ i ∈ s, 0 ≤ g i)
    (hg_le : ∀ i ∈ s, g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      ∑ i ∈ s, |f i - g i| := by
  classical
  revert hf_nonneg hf_le hg_nonneg hg_le
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih hf_nonneg hf_le hg_nonneg hg_le
    have hf_nonneg_s : ∀ i ∈ s, 0 ≤ f i := by
      intro i hi
      exact hf_nonneg i (by simp [hi])
    have hf_le_s : ∀ i ∈ s, f i ≤ 1 := by
      intro i hi
      exact hf_le i (by simp [hi])
    have hg_nonneg_s : ∀ i ∈ s, 0 ≤ g i := by
      intro i hi
      exact hg_nonneg i (by simp [hi])
    have hg_le_s : ∀ i ∈ s, g i ≤ 1 := by
      intro i hi
      exact hg_le i (by simp [hi])
    have htail := ih hf_nonneg_s hf_le_s hg_nonneg_s hg_le_s
    let Pf : ℝ := ∏ i ∈ s, f i
    let Pg : ℝ := ∏ i ∈ s, g i
    have hfa_abs : |f a| ≤ 1 := by
      have hfa_nonneg : 0 ≤ f a := hf_nonneg a (by simp [ha])
      simpa [abs_of_nonneg hfa_nonneg] using hf_le a (by simp [ha])
    have hPg_nonneg : 0 ≤ Pg := by
      dsimp [Pg]
      exact Finset.prod_nonneg fun i hi => hg_nonneg_s i hi
    have hPg_le : Pg ≤ 1 := by
      dsimp [Pg]
      exact Finset.prod_le_one
        (fun i hi => hg_nonneg_s i hi) (fun i hi => hg_le_s i hi)
    have hPg_abs : |Pg| ≤ 1 := by
      simpa [abs_of_nonneg hPg_nonneg] using hPg_le
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hdecomp : f a * Pf - g a * Pg =
        f a * (Pf - Pg) + (f a - g a) * Pg := by ring
    calc
      |f a * Pf - g a * Pg|
          = |f a * (Pf - Pg) + (f a - g a) * Pg| := by rw [hdecomp]
      _ ≤ |f a * (Pf - Pg)| + |(f a - g a) * Pg| := abs_add_le _ _
      _ = |f a| * |Pf - Pg| + |f a - g a| * |Pg| := by
            rw [abs_mul, abs_mul]
      _ ≤ 1 * |Pf - Pg| + |f a - g a| * 1 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hfa_abs (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hPg_abs (abs_nonneg _))
      _ ≤ 1 * (∑ i ∈ s, |f i - g i|) + |f a - g a| * 1 := by
            have hfirst :
                1 * |Pf - Pg| ≤ 1 * (∑ i ∈ s, |f i - g i|) :=
              mul_le_mul_of_nonneg_left (by simpa [Pf, Pg] using htail)
                zero_le_one
            nlinarith
      _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

lemma abs_prod_sub_prod_le_sum_abs_mul_two_pow
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf_abs : ∀ i ∈ s, |f i| ≤ 2)
    (hg_abs : ∀ i ∈ s, |g i| ≤ 2) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      (∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card := by
  classical
  revert hf_abs hg_abs
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih hf_abs hg_abs
    have hf_abs_s : ∀ i ∈ s, |f i| ≤ 2 := by
      intro i hi
      exact hf_abs i (by simp [hi])
    have hg_abs_s : ∀ i ∈ s, |g i| ≤ 2 := by
      intro i hi
      exact hg_abs i (by simp [hi])
    have htail := ih hf_abs_s hg_abs_s
    let Pf : ℝ := ∏ i ∈ s, f i
    let Pg : ℝ := ∏ i ∈ s, g i
    have hfa_abs : |f a| ≤ 2 := hf_abs a (by simp [ha])
    have hPg_abs : |Pg| ≤ (2 : ℝ) ^ s.card := by
      dsimp [Pg]
      rw [abs_prod]
      calc
        ∏ i ∈ s, |g i| ≤ ∏ _i ∈ s, (2 : ℝ) := by
          exact Finset.prod_le_prod
            (fun i _hi => abs_nonneg (g i))
            (fun i hi => hg_abs_s i hi)
        _ = (2 : ℝ) ^ s.card := by simp
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ s.card := by positivity
    have hpow_succ_ge : (2 : ℝ) ^ s.card ≤ (2 : ℝ) ^ (insert a s).card := by
      rw [Finset.card_insert_of_notMem ha]
      rw [pow_succ]
      nlinarith [show 0 ≤ (2 : ℝ) ^ s.card by positivity]
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hdecomp : f a * Pf - g a * Pg =
        f a * (Pf - Pg) + (f a - g a) * Pg := by ring
    calc
      |f a * Pf - g a * Pg|
          = |f a * (Pf - Pg) + (f a - g a) * Pg| := by rw [hdecomp]
      _ ≤ |f a * (Pf - Pg)| + |(f a - g a) * Pg| := abs_add_le _ _
      _ = |f a| * |Pf - Pg| + |f a - g a| * |Pg| := by
            rw [abs_mul, abs_mul]
      _ ≤ 2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card) +
            |f a - g a| * ((2 : ℝ) ^ s.card) := by
            exact add_le_add
              (mul_le_mul hfa_abs htail (abs_nonneg _) zero_le_two)
              (mul_le_mul_of_nonneg_left hPg_abs (abs_nonneg _))
      _ ≤ 2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card) +
            |f a - g a| * ((2 : ℝ) ^ (insert a s).card) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_left hpow_succ_ge (abs_nonneg _))
                (2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card))
      _ = (|f a - g a| + ∑ i ∈ s, |f i - g i|) *
            (2 : ℝ) ^ (insert a s).card := by
            rw [Finset.card_insert_of_notMem ha, pow_succ]
            ring

lemma abs_continuousCliqueKernel_sub_le_card_mul
    {G : Type u} [Sub G] (M : ℕ) {f g : G → ℝ} {δ : ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hclose : ∀ x, |f x - g x| ≤ δ)
    (x : Fin M → G) :
    |continuousCliqueKernel M f x - continuousCliqueKernel M g x| ≤
      ((continuousCliqueEdgePairs M).card : ℝ) * δ := by
  unfold continuousCliqueKernel
  calc
    |(∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)) -
        ∏ e ∈ continuousCliqueEdgePairs M, g (x e.1 - x e.2)|
        ≤ ∑ e ∈ continuousCliqueEdgePairs M,
            |f (x e.1 - x e.2) - g (x e.1 - x e.2)| := by
          exact abs_prod_sub_prod_le_sum_abs (continuousCliqueEdgePairs M)
            (fun e => f (x e.1 - x e.2))
            (fun e => g (x e.1 - x e.2))
            (fun e _he => hf_nonneg _)
            (fun e _he => hf_le _)
            (fun e _he => hg_nonneg _)
            (fun e _he => hg_le _)
    _ ≤ ∑ _e ∈ continuousCliqueEdgePairs M, δ := by
          exact Finset.sum_le_sum fun e _he => hclose (x e.1 - x e.2)
    _ = ((continuousCliqueEdgePairs M).card : ℝ) * δ := by simp

lemma abs_continuousCliqueKernel_sub_le_card_mul_two_pow
    {G : Type u} [Sub G] (M : ℕ) {f g : G → ℝ} {δ : ℝ}
    (hf_abs : ∀ x, |f x| ≤ 2)
    (hg_abs : ∀ x, |g x| ≤ 2)
    (hclose : ∀ x, |f x - g x| ≤ δ)
    (x : Fin M → G) :
    |continuousCliqueKernel M f x - continuousCliqueKernel M g x| ≤
      (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
        (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
  unfold continuousCliqueKernel
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
    positivity
  calc
    |(∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)) -
        ∏ e ∈ continuousCliqueEdgePairs M, g (x e.1 - x e.2)|
        ≤ (∑ e ∈ continuousCliqueEdgePairs M,
            |f (x e.1 - x e.2) - g (x e.1 - x e.2)|) *
            (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
          exact abs_prod_sub_prod_le_sum_abs_mul_two_pow
            (continuousCliqueEdgePairs M)
            (fun e => f (x e.1 - x e.2))
            (fun e => g (x e.1 - x e.2))
            (fun e _he => hf_abs _)
            (fun e _he => hg_abs _)
    _ ≤ (∑ _e ∈ continuousCliqueEdgePairs M, δ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
          exact mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum fun e _he => hclose (x e.1 - x e.2))
            hpow_nonneg
    _ = (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp

lemma continuousCliqueDensity_lipschitz_sup
    {G : Type u} [MeasurableSpace G] [Sub G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] (M : ℕ)
    {f g : G → ℝ} {δ : ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hδ_nonneg : 0 ≤ δ)
    (hclose : ∀ x, |f x - g x| ≤ δ) :
    |continuousCliqueDensity μ M f - continuousCliqueDensity μ M g| ≤
      ((continuousCliqueEdgePairs M).card : ℝ) * δ := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  let Kf : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M f x
  let Kg : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M g x
  have hKf_meas : Measurable Kf := by
    dsimp [Kf, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hKg_meas : Measurable Kg := by
    dsimp [Kg, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hg_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hKf_bound : ∀ᵐ x ∂μM, ‖Kf x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ Kf x := by
        dsimp [Kf, continuousCliqueKernel]
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : Kf x ≤ 1 := by
        dsimp [Kf, continuousCliqueKernel]
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hKg_bound : ∀ᵐ x ∂μM, ‖Kg x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ Kg x := by
        dsimp [Kg, continuousCliqueKernel]
        exact Finset.prod_nonneg fun e _he => hg_nonneg _
      have hle : Kg x ≤ 1 := by
        dsimp [Kg, continuousCliqueKernel]
        exact Finset.prod_le_one (fun e _he => hg_nonneg _) (fun e _he => hg_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hKf_int : Integrable Kf μM :=
    Integrable.of_bound hKf_meas.aestronglyMeasurable 1 hKf_bound
  have hKg_int : Integrable Kg μM :=
    Integrable.of_bound hKg_meas.aestronglyMeasurable 1 hKg_bound
  let C : ℝ := ((continuousCliqueEdgePairs M).card : ℝ) * δ
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg _) hδ_nonneg
  have hdiff_bound : ∀ᵐ x ∂μM, ‖Kf x - Kg x‖ ≤ C := by
    exact Eventually.of_forall fun x => by
      simpa [Kf, Kg, C, Real.norm_eq_abs] using
        abs_continuousCliqueKernel_sub_le_card_mul M
          hf_nonneg hf_le hg_nonneg hg_le hclose x
  have hμM_real : μM.real Set.univ = 1 := by
    haveI : IsProbabilityMeasure μM := inferInstance
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  unfold continuousCliqueDensity
  change |∫ x, Kf x ∂μM - ∫ x, Kg x ∂μM| ≤ C
  rw [← integral_sub hKf_int hKg_int]
  calc
    |∫ x, Kf x - Kg x ∂μM|
        = ‖∫ x, Kf x - Kg x ∂μM‖ := by
            simp [Real.norm_eq_abs]
    _ ≤ C * μM.real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const hdiff_bound
    _ = C := by rw [hμM_real, mul_one]

lemma continuousCliqueDensity_lipschitz_sup_two_pow
    {G : Type u} [MeasurableSpace G] [Sub G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] (M : ℕ)
    {f g : G → ℝ} {δ : ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_abs : ∀ x, |f x| ≤ 2)
    (hg_abs : ∀ x, |g x| ≤ 2)
    (hδ_nonneg : 0 ≤ δ)
    (hclose : ∀ x, |f x - g x| ≤ δ) :
    |continuousCliqueDensity μ M f - continuousCliqueDensity μ M g| ≤
      (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
        (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  let Kf : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M f x
  let Kg : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M g x
  have hKf_meas : Measurable Kf := by
    dsimp [Kf, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hKg_meas : Measurable Kg := by
    dsimp [Kg, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hg_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  let B : ℝ := (2 : ℝ) ^ (continuousCliqueEdgePairs M).card
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hKf_bound : ∀ᵐ x ∂μM, ‖Kf x‖ ≤ B := by
    exact Eventually.of_forall fun x => by
      dsimp [Kf, continuousCliqueKernel, B]
      rw [abs_prod]
      calc
        ∏ e ∈ continuousCliqueEdgePairs M, |f (x e.1 - x e.2)|
            ≤ ∏ _e ∈ continuousCliqueEdgePairs M, (2 : ℝ) := by
              exact Finset.prod_le_prod
                (fun e _he => abs_nonneg (f (x e.1 - x e.2)))
                (fun e _he => hf_abs _)
        _ = (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp
  have hKg_bound : ∀ᵐ x ∂μM, ‖Kg x‖ ≤ B := by
    exact Eventually.of_forall fun x => by
      dsimp [Kg, continuousCliqueKernel, B]
      rw [abs_prod]
      calc
        ∏ e ∈ continuousCliqueEdgePairs M, |g (x e.1 - x e.2)|
            ≤ ∏ _e ∈ continuousCliqueEdgePairs M, (2 : ℝ) := by
              exact Finset.prod_le_prod
                (fun e _he => abs_nonneg (g (x e.1 - x e.2)))
                (fun e _he => hg_abs _)
        _ = (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp
  have hKf_int : Integrable Kf μM :=
    Integrable.of_bound hKf_meas.aestronglyMeasurable B hKf_bound
  have hKg_int : Integrable Kg μM :=
    Integrable.of_bound hKg_meas.aestronglyMeasurable B hKg_bound
  let C : ℝ := (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
    (2 : ℝ) ^ (continuousCliqueEdgePairs M).card
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ_nonneg) (by positivity)
  have hdiff_bound : ∀ᵐ x ∂μM, ‖Kf x - Kg x‖ ≤ C := by
    exact Eventually.of_forall fun x => by
      simpa [Kf, Kg, C, Real.norm_eq_abs] using
        abs_continuousCliqueKernel_sub_le_card_mul_two_pow M
          hf_abs hg_abs hclose x
  have hμM_real : μM.real Set.univ = 1 := by
    haveI : IsProbabilityMeasure μM := inferInstance
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  unfold continuousCliqueDensity
  change |∫ x, Kf x ∂μM - ∫ x, Kg x ∂μM| ≤ C
  rw [← integral_sub hKf_int hKg_int]
  calc
    |∫ x, Kf x - Kg x ∂μM|
        = ‖∫ x, Kf x - Kg x ∂μM‖ := by
            simp [Real.norm_eq_abs]
    _ ≤ C * μM.real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const hdiff_bound
    _ = C := by rw [hμM_real, mul_one]

/-- Route A weighted continuous avoidance kernel:
`∏ᵢ u(xᵢ) * ∏_{i<j} (1 - f(xᵢ - xⱼ))`.

In the Fourier-positive route, `f` is the compact-limit forbidden kernel and
`u` is the compact-limit dense vertex weight. -/
noncomputable def continuousWeightedAvoidanceKernel
    {G : Type u} [Sub G] (M : ℕ) (f u : G → ℝ) (x : Fin M → G) : ℝ :=
  (∏ i : Fin M, u (x i)) *
    ∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2))

/-- Route A weighted continuous avoidance density. -/
noncomputable def continuousWeightedAvoidanceDensity
    {G : Type u} [MeasurableSpace G] [Sub G]
    (μ : Measure G) (M : ℕ) (f u : G → ℝ) : ℝ :=
  ∫ x : Fin M → G, continuousWeightedAvoidanceKernel M f u x
    ∂Measure.pi (fun _ : Fin M => μ)

/-- If the continuous clique kernel is strictly positive on a nonempty open box,
then its continuous Cayley density is strictly positive.

This is the topological-measure endpoint for the `g(0) < 1` case of the compact
Cayley clique-forcing lemma: continuity gives a small open neighbourhood on
which every clique edge receives positive weight, and Haar open-positivity turns
that box into positive measure. -/
theorem continuousCliqueDensity_pos_of_pos_on_open_pi
    {G : Type u} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Sub G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (U : Set G) (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hposU : ∀ x : Fin M → G, x ∈ Set.univ.pi (fun _ : Fin M => U) →
      0 < continuousCliqueKernel M f x) :
    0 < continuousCliqueDensity μ M f := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  have hkernel_meas : Measurable (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    unfold continuousCliqueKernel
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hkernel_nonneg :
      0 ≤ᵐ[μM] (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    exact Eventually.of_forall fun x => by
      unfold continuousCliqueKernel
      exact Finset.prod_nonneg fun e _he => hf_nonneg _
  have hkernel_bound :
      ∀ᵐ x ∂μM, ‖continuousCliqueKernel M f x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ continuousCliqueKernel M f x := by
        unfold continuousCliqueKernel
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : continuousCliqueKernel M f x ≤ 1 := by
        unfold continuousCliqueKernel
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int : Integrable (fun x : Fin M → G => continuousCliqueKernel M f x) μM :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hpi_pos : 0 < μM (Set.univ.pi (fun _ : Fin M => U)) := by
    dsimp [μM]
    rw [Measure.pi_pi]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr
      (fun i _hi => ne_of_gt (hUopen.measure_pos μ hUnonempty))
  have hpi_subset_support :
      Set.univ.pi (fun _ : Fin M => U) ⊆
        Function.support (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    intro x hx
    exact ne_of_gt (hposU x hx)
  have hsupport_pos :
      0 < μM (Function.support (fun x : Fin M → G => continuousCliqueKernel M f x)) :=
    lt_of_lt_of_le hpi_pos (measure_mono hpi_subset_support)
  rw [continuousCliqueDensity]
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hkernel_nonneg hkernel_int).mpr
    hsupport_pos

/-- Compact-Cayley Lemma 2.7, open-neighbourhood case. If the continuous
allowed kernel is positive at zero, then it is positive on a small open
neighbourhood of zero. Shrinking the neighbourhood in the two coordinates makes
every clique edge difference land there, so the continuous `K_M` density is
positive.

This proves the `g(0) < 1` branch after setting `f = 1 - g`. -/
theorem continuousCliqueDensity_pos_of_pos_at_zero
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (f : G → ℝ) (hf_cont : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hzero : 0 < f 0) :
    0 < continuousCliqueDensity μ M f := by
  let V : Set G := {x | 0 < f x}
  have hVopen : IsOpen V := by
    exact isOpen_lt continuous_const hf_cont
  have hVmem : V ∈ 𝓝 (0 : G) := hVopen.mem_nhds hzero
  have hVmem' : V ∈ 𝓝 (((0 : G), (0 : G)).1 - ((0 : G), (0 : G)).2) := by
    simpa using hVmem
  have hpre : (fun z : G × G => z.1 - z.2) ⁻¹' V ∈ 𝓝 ((0 : G), (0 : G)) := by
    simpa using (continuous_fst.sub continuous_snd).continuousAt hVmem'
  rcases mem_nhds_prod_iff'.mp hpre with
    ⟨U₁, U₂, hU₁open, hU₁zero, hU₂open, hU₂zero, hUsub⟩
  let U : Set G := U₁ ∩ U₂
  have hUopen : IsOpen U := hU₁open.inter hU₂open
  have hUnonempty : U.Nonempty := ⟨0, hU₁zero, hU₂zero⟩
  refine continuousCliqueDensity_pos_of_pos_on_open_pi μ M f hf_cont.measurable hf_nonneg
    hf_le U hUopen hUnonempty ?_
  intro x hx
  unfold continuousCliqueKernel
  refine Finset.prod_pos ?_
  intro e he
  have hx₁ : x e.1 ∈ U := hx e.1 (by simp)
  have hx₂ : x e.2 ∈ U := hx e.2 (by simp)
  have hpair : (x e.1, x e.2) ∈ U₁ ×ˢ U₂ := ⟨hx₁.1, hx₂.2⟩
  exact hUsub hpair

/-- A closed proper subgroup of a connected compact abelian Hausdorff group is
Haar-null. Geometric core of Layer 1; no Fourier content.

Argument: assume `μ H ≠ 0`. The cosets of `H` partition `G`, each with the same
measure `μ H` by translation invariance. With finite total measure and a
constant positive contribution, only finitely many cosets exist; hence
`H.FiniteIndex`. A closed finite-index subgroup is open
(`AddSubgroup.isOpen_of_isClosed_of_finiteIndex`). A non-empty clopen subset of
a connected space is the whole space, contradicting `H` proper. -/
theorem closed_proper_subgroup_haar_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_proper : (H : Set G) ≠ Set.univ) :
    μ (H : Set G) = 0 := by
  by_contra hμH_ne
  have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
  obtain ⟨s, hs, _⟩ := H.exists_isComplement_left 0
  have hs_finite : Finite s := by
    rcases finite_or_infinite s with hfin | hinf
    · exact hfin
    · exfalso
      let e : ℕ ↪ s := Infinite.natEmbedding s
      let f : ℕ → Set G := fun n => (e n).val +ᵥ (H : Set G)
      have h_disjoint : Pairwise (fun m n : ℕ => Disjoint (f m) (f n)) := by
        intro m n hmn
        have : (e m).val ≠ (e n).val :=
          fun h => hmn (e.injective (Subtype.ext h))
        exact hs.pairwiseDisjoint_vadd (e m).2 (e n).2 this
      have h_meas : ∀ n : ℕ, MeasurableSet (f n) :=
        fun n => hH_meas.const_vadd _
      have h_const : ∀ n : ℕ, μ (f n) = μ (H : Set G) :=
        fun n => measure_vadd μ (e n).val _
      have h_subset : (⋃ n : ℕ, f n) ⊆ Set.univ := fun _ _ => trivial
      have hμ_iUnion : μ (⋃ n : ℕ, f n) = ∑' n : ℕ, μ (f n) :=
        measure_iUnion h_disjoint h_meas
      have h_top : (∑' _ : ℕ, μ (H : Set G)) = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hμH_ne
      have hμ_top : μ (⋃ n : ℕ, f n) = ⊤ := by
        rw [hμ_iUnion, tsum_congr h_const]; exact h_top
      have hμ_univ_top : μ (Set.univ : Set G) = ⊤ :=
        top_unique (hμ_top ▸ measure_mono h_subset)
      exact absurd hμ_univ_top (ne_of_lt IsFiniteMeasure.measure_univ_lt_top)
  have hH_findex : H.FiniteIndex := hs.finite_left_iff.mp hs_finite
  have hH_open : IsOpen (H : Set G) :=
    AddSubgroup.isOpen_of_isClosed_of_finiteIndex H hH_closed
  exact hH_proper (IsClopen.eq_univ ⟨hH_closed, hH_open⟩ ⟨0, H.zero_mem⟩)

/-- A closed subgroup of infinite index is Haar-null.

This is the finite-index half of `closed_proper_subgroup_haar_null`, isolated
for compact duals where proving connectedness is overkill. Positive Haar
measure for `H` forces only finitely many cosets by the same disjoint-coset
counting argument used above. -/
theorem closed_subgroup_haar_null_of_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_not_finiteIndex : ¬ H.FiniteIndex) :
    μ (H : Set G) = 0 := by
  by_contra hμH_ne
  have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
  obtain ⟨s, hs, _⟩ := H.exists_isComplement_left 0
  have hs_finite : Finite s := by
    rcases finite_or_infinite s with hfin | hinf
    · exact hfin
    · exfalso
      let e : ℕ ↪ s := Infinite.natEmbedding s
      let f : ℕ → Set G := fun n => (e n).val +ᵥ (H : Set G)
      have h_disjoint : Pairwise (fun m n : ℕ => Disjoint (f m) (f n)) := by
        intro m n hmn
        have : (e m).val ≠ (e n).val :=
          fun h => hmn (e.injective (Subtype.ext h))
        exact hs.pairwiseDisjoint_vadd (e m).2 (e n).2 this
      have h_meas : ∀ n : ℕ, MeasurableSet (f n) :=
        fun n => hH_meas.const_vadd _
      have h_const : ∀ n : ℕ, μ (f n) = μ (H : Set G) :=
        fun n => measure_vadd μ (e n).val _
      have h_subset : (⋃ n : ℕ, f n) ⊆ Set.univ := fun _ _ => trivial
      have hμ_iUnion : μ (⋃ n : ℕ, f n) = ∑' n : ℕ, μ (f n) :=
        measure_iUnion h_disjoint h_meas
      have h_top : (∑' _ : ℕ, μ (H : Set G)) = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hμH_ne
      have hμ_top : μ (⋃ n : ℕ, f n) = ⊤ := by
        rw [hμ_iUnion, tsum_congr h_const]; exact h_top
      have hμ_univ_top : μ (Set.univ : Set G) = ⊤ :=
        top_unique (hμ_top ▸ measure_mono h_subset)
      exact absurd hμ_univ_top (ne_of_lt IsFiniteMeasure.measure_univ_lt_top)
  exact hH_not_finiteIndex (hs.finite_left_iff.mp hs_finite)

/-- If `H` is Haar-null, then the set of finite tuples whose `i,j` difference
lands in `H` is null. This is the Fubini/shear step used in Tao's continuous
avoidance lemma.

The proof splits off the `i`-th coordinate, evaluates the `j`-th coordinate in
the remaining product, and then uses the Haar-preserving shear
`(x, y) ↦ (x - y, y)` on `G × G`. -/
theorem pi_pair_sub_mem_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {M : ℕ} (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hμH : μ (H : Set G) = 0)
    (i j : Fin M) (hij : i ≠ j) :
    Measure.pi (fun _ : Fin M => μ)
      {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
  cases M with
  | zero =>
      exact Fin.elim0 i
  | succ n =>
      obtain ⟨k, hk⟩ :=
        Fin.exists_succAbove_eq (x := j) (y := i) (by simpa [ne_comm] using hij)
      have hsplit :
          MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) i)
            (Measure.pi (fun _ : Fin (n + 1) => μ))
            (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
        simpa using
          (measurePreserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => G)
            (fun _ : Fin (n + 1) => μ) i)
      have hrest :
          MeasurePreserving (Function.eval k)
            (Measure.pi (fun _ : Fin n => μ)) μ :=
        measurePreserving_eval (fun _ : Fin n => μ) k
      have hpair_after :
          MeasurePreserving
            (Prod.map (fun x : G => x) (Function.eval k))
            (μ.prod (Measure.pi (fun _ : Fin n => μ))) (μ.prod μ) :=
        MeasurePreserving.prod
          (MeasurePreserving.id μ : MeasurePreserving (fun x : G => x) μ μ) hrest
      have hpair :
          MeasurePreserving (fun x : Fin (n + 1) → G => (x i, x j))
            (Measure.pi (fun _ : Fin (n + 1) => μ)) (μ.prod μ) := by
        convert hpair_after.comp hsplit using 1
        ext x
        · simp
        · rw [← hk]
          rfl
      have hdiff_prod :
          MeasurePreserving (fun z : G × G => (z.1 - z.2, z.2))
            (μ.prod μ) (μ.prod μ) := by
        simpa using (measurePreserving_sub_prod (μ := μ) (ν := μ))
      have hdiff :
          MeasurePreserving (fun z : G × G => z.1 - z.2)
            (μ.prod μ) μ := by
        simpa [Function.comp_def] using
          (measurePreserving_fst (μ := μ) (ν := μ)).comp hdiff_prod
      have hmap :
          MeasurePreserving (fun x : Fin (n + 1) → G => x i - x j)
            (Measure.pi (fun _ : Fin (n + 1) => μ)) μ := by
        simpa [Function.comp_def] using hdiff.comp hpair
      have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
      calc
        Measure.pi (fun _ : Fin (n + 1) => μ)
            {x : Fin (n + 1) → G | x i - x j ∈ (H : Set G)}
            = (Measure.map (fun x : Fin (n + 1) → G => x i - x j)
                (Measure.pi (fun _ : Fin (n + 1) => μ))) (H : Set G) := by
              change Measure.pi (fun _ : Fin (n + 1) => μ)
                  ((fun x : Fin (n + 1) → G => x i - x j) ⁻¹' (H : Set G)) = _
              rw [Measure.map_apply hmap.measurable hH_meas]
        _ = μ (H : Set G) := by rw [hmap.map_eq]
        _ = 0 := hμH

/-- Compact-clique-forcing endpoint, case where the zero set is a proper
closed subgroup. If `f ≥ 0` and `f` vanishes exactly on such a subgroup, then
the continuous Cayley `K_M` density is strictly positive.

This is the measure-theoretic part of compact-Cayley Lemma 2.7 after the
Fourier/positive-definite argument has identified the level set
`{x | f x = 0}` as a proper closed subgroup. -/
theorem continuousCliqueDensity_pos_of_zeroLevel_null_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 0)
    (hμH : μ (H : Set G) = 0) :
    0 < continuousCliqueDensity μ M f := by
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        Measure.pi (fun _ : Fin M => μ)
          {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null :
      Measure.pi (fun _ : Fin M => μ)
        (⋃ (i : Fin M) (j : Fin M) (_ : i < j),
          {x : Fin M → G | x i - x j ∈ (H : Set G)}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have h_ae_avoid : ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
    rw [ae_iff]
    refine measure_mono_null ?_ h_bad_null
    intro x hx
    push_neg at hx
    obtain ⟨i, j, hij, hmem⟩ := hx
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩
  have hkernel_meas :
      Measurable (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    unfold continuousCliqueKernel
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hkernel_nonneg :
      0 ≤ᵐ[Measure.pi (fun _ : Fin M => μ)]
        (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    exact Eventually.of_forall fun x => by
      unfold continuousCliqueKernel
      exact Finset.prod_nonneg fun e _he => hf_nonneg _
  have hkernel_bound :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ),
        ‖continuousCliqueKernel M f x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ continuousCliqueKernel M f x := by
        unfold continuousCliqueKernel
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : continuousCliqueKernel M f x ≤ 1 := by
        unfold continuousCliqueKernel
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int :
      Integrable (fun x : Fin M → G => continuousCliqueKernel M f x)
        (Measure.pi (fun _ : Fin M => μ)) :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hkernel_pos :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ),
        0 < continuousCliqueKernel M f x := by
    filter_upwards [h_ae_avoid] with x hx
    unfold continuousCliqueKernel
    refine Finset.prod_pos ?_
    intro e he
    have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
    have hnot : x e.1 - x e.2 ∉ (H : Set G) := hx e.1 e.2 hlt
    have hne : f (x e.1 - x e.2) ≠ 0 := by
      intro hzero
      exact hnot ((hH_eq (x e.1 - x e.2)).mpr hzero)
    exact lt_of_le_of_ne (hf_nonneg _) hne.symm
  exact integral_pos_of_ae_pos_of_nonneg
    (Measure.pi (fun _ : Fin M => μ)) hkernel_int hkernel_nonneg hkernel_pos

theorem continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 0)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    0 < continuousCliqueDensity μ M f := by
  have hμH : μ (H : Set G) = 0 :=
    closed_proper_subgroup_haar_null μ H hH_closed hH_proper
  exact continuousCliqueDensity_pos_of_zeroLevel_null_subgroup μ M f
    hf_meas hf_nonneg hf_le H hH_closed hH_eq hμH

/-- Compact-Cayley Lemma 2.7 endpoint after the positive-definite argument has
identified the level set `{x | g x = 1}` as a Haar-null closed subgroup.
Applying the zero-level null-subgroup theorem to `f = 1 - g` gives positive
continuous clique density for the allowed kernel. -/
theorem continuousCliqueDensity_pos_of_one_sub_level_one_null_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_meas : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ g x = 1)
    (hμH : μ (H : Set G) = 0) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_zeroLevel_null_subgroup μ M
    (fun x => 1 - g x) ?_ ?_ ?_ H hH_closed ?_ hμH
  · exact measurable_const.sub hg_meas
  · intro x
    linarith [hg_le x]
  · intro x
    linarith [hg_nonneg x]
  · intro x
    constructor
    · intro hx
      have hg : g x = 1 := (hH_eq x).mp hx
      linarith
    · intro hzero
      exact (hH_eq x).mpr (by linarith)

/-- Version of the compact-Cayley level-one endpoint where the level-one
subgroup is known to have infinite index.  The general Haar theorem converts
that algebraic hypothesis into nullness. -/
theorem continuousCliqueDensity_pos_of_one_sub_level_one_not_finiteIndex_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_meas : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ g x = 1)
    (hH_not_finiteIndex : ¬ H.FiniteIndex) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) :=
  continuousCliqueDensity_pos_of_one_sub_level_one_null_subgroup μ M g
    hg_meas hg_nonneg hg_le H hH_closed hH_eq
    (closed_subgroup_haar_null_of_not_finiteIndex μ H hH_closed hH_not_finiteIndex)

/-- Compact-Cayley Lemma 2.7 endpoint after the positive-definite argument has
identified the level set `{x | g x = 1}` as a proper closed subgroup.  Applying
the previous theorem to `f = 1 - g` gives positive continuous clique density
for the allowed kernel. -/
theorem continuousCliqueDensity_pos_of_one_sub_level_one_proper_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_meas : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ g x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_zeroLevel_proper_subgroup μ M
    (fun x => 1 - g x) ?_ ?_ ?_ H hH_closed ?_ hH_proper
  · exact measurable_const.sub hg_meas
  · intro x
    linarith [hg_le x]
  · intro x
    linarith [hg_nonneg x]
  · intro x
    constructor
    · intro hx
      have hg : g x = 1 := (hH_eq x).mp hx
      linarith
    · intro hzero
      exact (hH_eq x).mpr (by linarith)

/-- Route A weighted endpoint after the positive-definite argument identifies
the level set `{x | f x = 1}` as a proper closed subgroup.

If `u` is positive on a set of positive Haar measure, then almost every tuple in
that positive-measure vertex box avoids the subgroup in every pairwise
difference.  On that set all vertex factors `u(xᵢ)` and edge factors
`1 - f(xᵢ - xⱼ)` are strictly positive, so the weighted avoidance integral is
strictly positive. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hμH : μ (H : Set G) = 0)
    (hu_pos_set : 0 < μ {x : G | 0 < u x}) :
    0 < continuousWeightedAvoidanceDensity μ M f u := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  let S : Set G := {x : G | 0 < u x}
  let Bad : Set (Fin M → G) :=
    ⋃ (i : Fin M) (j : Fin M) (_ : i < j),
      {x : Fin M → G | x i - x j ∈ (H : Set G)}
  let K : (Fin M → G) → ℝ := fun x => continuousWeightedAvoidanceKernel M f u x
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        μM {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    dsimp [μM]
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null : μM Bad = 0 := by
    dsimp [Bad, μM]
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have hkernel_meas : Measurable K := by
    dsimp [K, continuousWeightedAvoidanceKernel]
    refine
      ((Finset.univ : Finset (Fin M)).measurable_prod
        (fun i _hi => hu_meas.comp (measurable_pi_apply i))).mul ?_
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact measurable_const.sub
      (hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2)))
  have hkernel_nonneg : 0 ≤ᵐ[μM] K := by
    exact Eventually.of_forall fun x => by
      dsimp [K, continuousWeightedAvoidanceKernel]
      refine mul_nonneg ?_ ?_
      · exact Finset.prod_nonneg fun i _hi => hu_nonneg _
      · exact Finset.prod_nonneg fun e _he => by linarith [hf_le (x e.1 - x e.2)]
  have hkernel_bound : ∀ᵐ x ∂μM, ‖K x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hv_nonneg : 0 ≤ ∏ i : Fin M, u (x i) :=
        Finset.prod_nonneg fun i _hi => hu_nonneg _
      have hv_le : (∏ i : Fin M, u (x i)) ≤ 1 :=
        Finset.prod_le_one (fun i _hi => hu_nonneg _) (fun i _hi => hu_le _)
      have he_nonneg :
          0 ≤ ∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2)) :=
        Finset.prod_nonneg fun e _he => by linarith [hf_le (x e.1 - x e.2)]
      have he_le :
          (∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2))) ≤ 1 :=
        Finset.prod_le_one
          (fun e _he => by linarith [hf_le (x e.1 - x e.2)])
          (fun e _he => by linarith [hf_nonneg (x e.1 - x e.2)])
      have hnonneg : 0 ≤ K x := by
        dsimp [K, continuousWeightedAvoidanceKernel]
        exact mul_nonneg hv_nonneg he_nonneg
      have hle : K x ≤ 1 := by
        dsimp [K, continuousWeightedAvoidanceKernel]
        calc
          (∏ i : Fin M, u (x i)) *
              ∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2))
              ≤ 1 * 1 := mul_le_mul hv_le he_le he_nonneg (by norm_num)
          _ = 1 := by norm_num
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int : Integrable K μM :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hpiS_pos : 0 < μM (Set.univ.pi (fun _ : Fin M => S)) := by
    dsimp [μM, S]
    rw [Measure.pi_pi]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr
      (fun _i _hi => ne_of_gt hu_pos_set)
  have hpiS_subset : Set.univ.pi (fun _ : Fin M => S) ⊆ Function.support K ∪ Bad := by
    intro x hxS
    by_cases hxBad : x ∈ Bad
    · exact Or.inr hxBad
    · refine Or.inl ?_
      have havoid :
          ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
        intro i j hij hmem
        exact hxBad (Set.mem_iUnion.mpr
          ⟨i, Set.mem_iUnion.mpr
            ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩)
      have hv_pos : 0 < ∏ i : Fin M, u (x i) := by
        refine Finset.prod_pos ?_
        intro i _hi
        exact hxS i (by simp)
      have he_pos :
          0 < ∏ e ∈ continuousCliqueEdgePairs M, (1 - f (x e.1 - x e.2)) := by
        refine Finset.prod_pos ?_
        intro e he
        have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
        have hnot : x e.1 - x e.2 ∉ (H : Set G) := havoid e.1 e.2 hlt
        have hne : f (x e.1 - x e.2) ≠ 1 := by
          intro hone
          exact hnot ((hH_eq (x e.1 - x e.2)).mpr hone)
        have hlt_one : f (x e.1 - x e.2) < 1 :=
          lt_of_le_of_ne (hf_le (x e.1 - x e.2)) hne
        linarith
      exact ne_of_gt (by
        dsimp [K, continuousWeightedAvoidanceKernel]
        exact mul_pos hv_pos he_pos)
  have hsupport_pos : 0 < μM (Function.support K) := by
    by_contra hnot
    have hsupport_zero : μM (Function.support K) = 0 :=
      le_antisymm (not_lt.mp hnot) bot_le
    have hpiS_zero : μM (Set.univ.pi (fun _ : Fin M => S)) = 0 := by
      refine le_antisymm ?_ bot_le
      calc
        μM (Set.univ.pi (fun _ : Fin M => S)) ≤ μM (Function.support K ∪ Bad) :=
          measure_mono hpiS_subset
        _ ≤ μM (Function.support K) + μM Bad := measure_union_le _ _
        _ = 0 := by simp [hsupport_zero, h_bad_null]
    exact (ne_of_gt hpiS_pos) hpiS_zero
  rw [continuousWeightedAvoidanceDensity]
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hkernel_nonneg hkernel_int).mpr
    hsupport_pos

/-- Route A weighted endpoint after the positive-definite argument identifies
the level set `{x | f x = 1}` as a proper closed subgroup of a connected compact
group.  This wrapper proves Haar-nullness from connectedness and then applies
the sharper null-subgroup endpoint. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ)
    (hu_pos_set : 0 < μ {x : G | 0 < u x}) :
    0 < continuousWeightedAvoidanceDensity μ M f u :=
  continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed hH_eq
    (closed_proper_subgroup_haar_null μ H hH_closed hH_proper) hu_pos_set

/-- Integral-positive version of
`continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup`.

This is the narrow Route A endpoint: the level-one subgroup is assumed
Haar-null directly, avoiding a separate connectedness hypothesis. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup_of_integral_pos
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hμH : μ (H : Set G) = 0)
    (hu_integral_pos : 0 < ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u := by
  have hu_bound : ∀ᵐ x ∂μ, ‖u x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hu_nonneg x)] using hu_le x
  have hu_int : Integrable u μ :=
    Integrable.of_bound hu_meas.aestronglyMeasurable 1 hu_bound
  have hsupp_pos : 0 < μ (Function.support u) :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun x => hu_nonneg x) hu_int).mp hu_integral_pos
  have hsupp_subset : Function.support u ⊆ {x : G | 0 < u x} := by
    intro x hx
    exact lt_of_le_of_ne (hu_nonneg x) hx.symm
  have hu_pos_set : 0 < μ {x : G | 0 < u x} :=
    lt_of_lt_of_le hsupp_pos (measure_mono hsupp_subset)
  exact continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed
    hH_eq hμH hu_pos_set

/-- Route A null-subgroup endpoint with the usual compact-model lower bound
`α ≤ ∫ u`, `α > 0`. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup_of_integral_ge
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hμH : μ (H : Set G) = 0)
    {α : ℝ} (hα : 0 < α) (hmean_u : α ≤ ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u :=
  continuousWeightedAvoidanceDensity_pos_of_level_one_null_subgroup_of_integral_pos μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed hH_eq hμH
    (lt_of_lt_of_le hα hmean_u)

/-- Integral-positive version of
`continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup`.

This is closer to the Route A compact model: the dense vertex weight satisfies
`∫ u > 0`, hence `{x | 0 < u x}` has positive Haar measure. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_pos
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ)
    (hu_integral_pos : 0 < ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u := by
  have hu_bound : ∀ᵐ x ∂μ, ‖u x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hu_nonneg x)] using hu_le x
  have hu_int : Integrable u μ :=
    Integrable.of_bound hu_meas.aestronglyMeasurable 1 hu_bound
  have hsupp_pos : 0 < μ (Function.support u) :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun x => hu_nonneg x) hu_int).mp hu_integral_pos
  have hsupp_subset : Function.support u ⊆ {x : G | 0 < u x} := by
    intro x hx
    exact lt_of_le_of_ne (hu_nonneg x) hx.symm
  have hu_pos_set : 0 < μ {x : G | 0 < u x} :=
    lt_of_lt_of_le hsupp_pos (measure_mono hsupp_subset)
  exact continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed
    hH_eq hH_proper hu_pos_set

/-- Route A endpoint with the usual compact-model lower bound
`α ≤ ∫ u`, `α > 0`. -/
theorem continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_ge
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f u : G → ℝ) (hf_meas : Measurable f) (hu_meas : Measurable u)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_le : ∀ x, u x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ)
    {α : ℝ} (hα : 0 < α) (hmean_u : α ≤ ∫ x, u x ∂μ) :
    0 < continuousWeightedAvoidanceDensity μ M f u :=
  continuousWeightedAvoidanceDensity_pos_of_level_one_proper_subgroup_of_integral_pos μ M
    f u hf_meas hu_meas hf_nonneg hf_le hu_nonneg hu_le H hH_closed hH_eq hH_proper
    (lt_of_lt_of_le hα hmean_u)

/-- **Tao's continuous-analogue key lemma (May 2026 forum comment).** Let `G` be a
connected compact abelian Hausdorff group with Haar probability measure `μ`, and
let `f : G → ℝ` be measurable with `f ≤ 1` pointwise. Suppose the level set
`{x : f x = 1}` coincides with a closed subgroup `H ≤ G`, and `H` is proper.
Then for almost every `(x₁, …, x_M) ∈ G^M`, `f (x_i − x_j) < 1` for all
`1 ≤ i < j ≤ M`.

The hypothesis "level set is a closed subgroup" is what positive-definiteness of
`f` is used to establish in the original argument; we factor it out so the core
lemma is purely measure-theoretic. -/
theorem tao_continuous_avoidance
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (_hf_meas : Measurable f) (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → f (x i - x j) < 1 := by
  have hμH : μ (H : Set G) = 0 :=
    closed_proper_subgroup_haar_null μ H hH_closed hH_proper
  -- Fubini step (deferred): for each pair `(i, j)` with `i ≠ j`, the set of
  -- M-tuples with `x i - x j ∈ H` has product measure zero. Argument:
  -- translation invariance of `μ` plus `μ ↑H = 0` plus Fubini on the pi
  -- measure (or a measure-preserving "shear" change of variables).
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        Measure.pi (fun _ : Fin M => μ)
          {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null :
      Measure.pi (fun _ : Fin M => μ)
        (⋃ (i : Fin M) (j : Fin M) (_ : i < j),
          {x : Fin M → G | x i - x j ∈ (H : Set G)}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have h_ae_avoid : ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
    rw [ae_iff]
    refine measure_mono_null ?_ h_bad_null
    intro x hx
    push_neg at hx
    obtain ⟨i, j, hij, hmem⟩ := hx
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩
  filter_upwards [h_ae_avoid] with x hx i j hij
  have h_ne_one : f (x i - x j) ≠ 1 := by
    intro heq
    exact hx i j hij ((hH_eq (x i - x j)).mpr heq)
  exact lt_of_le_of_ne (hf_le _) h_ne_one

end Erdos42
