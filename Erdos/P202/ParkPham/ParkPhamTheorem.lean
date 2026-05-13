/-
Erdős Problem 202 — Park–Pham layer, Stage 5.

Consequences of the Park–Pham threshold theorem for spread families:

1. `pSmall_mono_density`: `pSmall` decreases monotonically as `p` decreases.
2. `qSmallUpper_of_not_pSmall`: lifting `¬ pSmall at p₀` to
   `qSmallUpper X U p₀`.
3. `not_pSmall_of_spread`: the counting argument showing that the upper
   closure of a `κ`-spread family is not `p`-small at `p = κ⁻¹`. **Proved.**
4. `mu_at_partition_density_ge_half`: chains (3), (2), and
   `park_pham_threshold` to get `muP ≥ 1/2` at density `1/(2r)` when
   `κ ≥ Csp · r · log(ek)`. **Stated; body is a short bookkeeping argument
   left for a focused subpass.**
-/

import Mathlib
import Erdos.P202.ParkPham.BooleanFamilies
import Erdos.P202.ParkPham.ProductMeasure
import Erdos.P202.ParkPham.Smallness
import Erdos.P202.ParkPham.Threshold

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- `pSmall` is monotone in `p`: if `U` is `p`-small and `0 ≤ p₀ ≤ p ≤ 1`,
then `U` is `p₀`-small (the same cover works). -/
lemma pSmall_mono_density {X : Finset α} {U : Finset (Finset α)}
    {p₀ p : ℝ} (h0 : 0 ≤ p₀) (hle : p₀ ≤ p)
    (hSmall : pSmall X U p) : pSmall X U p₀ := by
  classical
  rcases hSmall with ⟨G, hCover, hsum⟩
  refine ⟨G, hCover, le_trans ?_ hsum⟩
  refine Finset.sum_le_sum ?_
  intro T _
  exact pow_le_pow_left₀ h0 hle T.card

/-- If `U` is not `p`-small at `p = p₀`, then it is not `p`-small for any
`p > p₀` with `p ≤ 1`. This is the `qSmallUpper` form. -/
lemma qSmallUpper_of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {p₀ : ℝ} (hp₀_nonneg : 0 ≤ p₀)
    (h : ¬ pSmall X U p₀) :
    qSmallUpper X U p₀ := by
  intro p hgt _
  intro hSmall
  exact h (pSmall_mono_density hp₀_nonneg hgt.le hSmall)

/-! ## Counting argument: spread families are not small -/

/-- If `A` is a `κ`-spread nonempty `k`-uniform family with `k ≥ 1` and
`1 < κ`, then `upClosureIn X A` is not `p`-small at `p = κ⁻¹`. -/
theorem not_pSmall_of_spread
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (hk : 1 ≤ k)
    (hUniform : Erdos202.UniformFamily A k)
    (hSpread : Erdos202.SpreadFamily A κ)
    (hκ : 1 < κ)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ¬ pSmall X (upClosureIn X A) (κ⁻¹) := by
  classical
  intro hSmall
  rcases hSmall with ⟨G, hCover, hsum⟩
  have hκ_pos : 0 < κ := by linarith
  have hAcard_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  -- Step 1: every S ∈ A is covered by some T ∈ G.
  have hCoverA : ∀ S ∈ A, ∃ T ∈ G, T ⊆ S := by
    intro S hSA
    have hSup : S ∈ upClosureIn X A :=
      mem_upClosureIn.mpr ⟨hAX S hSA, S, hSA, subset_refl _⟩
    exact hCover S hSup
  -- Step 2: A ⊆ ⋃_T∈G {S ∈ A : T ⊆ S}.
  have hAcover : A ⊆ G.biUnion fun T => A.filter fun S => T ⊆ S := by
    intro S hSA
    rcases hCoverA S hSA with ⟨T, hTG, hTS⟩
    exact Finset.mem_biUnion.mpr ⟨T, hTG, Finset.mem_filter.mpr ⟨hSA, hTS⟩⟩
  have hAcardle_nat :
      A.card ≤ ∑ T ∈ G, (A.filter fun S => T ⊆ S).card :=
    (Finset.card_le_card hAcover).trans Finset.card_biUnion_le
  have hAcardle :
      (A.card : ℝ) ≤ ∑ T ∈ G, ((A.filter fun S => T ⊆ S).card : ℝ) := by
    have h := hAcardle_nat
    have : ((A.card : ℕ) : ℝ) ≤
        (((∑ T ∈ G, (A.filter fun S => T ⊆ S).card : ℕ) : ℝ)) := by
      exact_mod_cast h
    rw [Nat.cast_sum] at this
    exact this
  -- Step 3: per-term bound using spread.
  have hbound : ∀ T ∈ G,
      ((A.filter fun S => T ⊆ S).card : ℝ) ≤ (A.card : ℝ) * (κ ^ T.card)⁻¹ := by
    intro T _
    by_cases hTne : T.Nonempty
    · have := hSpread T hTne
      rw [div_eq_mul_inv] at this
      exact this
    · have heq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
      subst heq
      have hfilter_eq : (A.filter fun S => (∅ : Finset α) ⊆ S) = A := by
        apply Finset.filter_eq_self.mpr
        intro S _
        exact Finset.empty_subset S
      rw [hfilter_eq]
      simp
  -- Step 4: sum.
  have hAsum :
      (A.card : ℝ) ≤ ∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹ :=
    hAcardle.trans (Finset.sum_le_sum hbound)
  -- Convert RHS into |A| * Σ (κ⁻¹)^|T|.
  have hkey :
      (∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹) =
        (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro T _
    rw [← inv_pow]
  rw [hkey] at hAsum
  -- Step 5: divide by |A|.
  have hsum_ge_one : (1 : ℝ) ≤ ∑ T ∈ G, (κ⁻¹) ^ T.card := by
    have hAsum' : (A.card : ℝ) * 1 ≤
        (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
      simpa using hAsum
    exact le_of_mul_le_mul_left hAsum' hAcard_pos
  -- Step 6: but hsum says the sum is ≤ 1/2 < 1. Contradiction.
  linarith

/-! ## Main consequence: muP ≥ 1/2 at partition density

The chain is:
1. `not_pSmall_of_spread` gives `¬ pSmall X (upClosureIn X A) (1/κ)`.
2. `qSmallUpper_of_not_pSmall` lifts to `qSmallUpper X U (1/κ)`.
3. `park_pham_threshold` gives `muP ≥ 1/2` at any density
   `≥ CKK · (1/κ) · log(ell U)`.
4. From `κ ≥ Csp · r · log(ek)` and `ell U ≤ max 2 k ≤ ek`, derive
   `CKK · (1/κ) · log(ell U) ≤ 1/(2r)` with `Csp := max 10 (8 · CKK)`.

The bookkeeping in step 4 is purely algebraic (log inequalities and a few
positivity arguments). Left as a named-target body for a focused subpass;
this is the only sorry in `ParkPham/` outside `Threshold.lean`. -/

/-- The Park–Pham constant for our application. -/
noncomputable def Csp : ℝ :=
  max 10 (8 * Classical.choose park_pham_threshold.{0})

lemma Csp_pos : 0 < Csp := by
  unfold Csp
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  norm_num

lemma Csp_ge_ten : (10 : ℝ) ≤ Csp := le_max_left _ _

lemma Csp_ge_two_CKK :
    2 * Classical.choose park_pham_threshold.{0} ≤ Csp := by
  unfold Csp
  refine le_trans ?_ (le_max_right _ _)
  have hCKK_pos : 0 < Classical.choose park_pham_threshold.{0} :=
    (Classical.choose_spec park_pham_threshold).1
  linarith

/-- Helper: universe-monomorphic density bound. Takes `CKK` as an opaque
real parameter so elaboration doesn't drag `Classical.choose` through. -/
private lemma density_bound_from_kappa_aux
    (CKK : ℝ) (hCKK_pos : 0 < CKK) (hCsp_ge_2CKK : 2 * CKK ≤ Csp)
    {ell_real κ : ℝ} {r k : ℕ}
    (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hell_real_pos : 0 < ell_real)
    (hell_ge_one : 1 ≤ ell_real)
    (hell_le_ek : ell_real ≤ Real.exp 1 * (k : ℝ))
    (hκ_pos : 0 < κ)
    (hκ : Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    CKK * κ⁻¹ * Real.log ell_real ≤ (1 : ℝ) / (2 * (r : ℝ)) := by
  have hr_real_ge_two : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hk_real_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hek_pos : 0 < Real.exp 1 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk_real_ge_one
    positivity
  have hlog_ek_pos : 0 < Real.log (Real.exp 1 * (k : ℝ)) := by
    have he : (1 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have hek_ge_e : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
      nlinarith [Real.exp_pos (1 : ℝ)]
    refine Real.log_pos ?_
    linarith
  have hlog_ell_le : Real.log ell_real ≤ Real.log (Real.exp 1 * (k : ℝ)) :=
    Real.log_le_log hell_real_pos hell_le_ek
  have hlog_ell_nonneg : 0 ≤ Real.log ell_real := Real.log_nonneg hell_ge_one
  have h2CKKr_nn : 0 ≤ 2 * CKK * (r : ℝ) := by positivity
  have hκ_lower : 2 * CKK * (r : ℝ) * Real.log ell_real ≤ κ := by
    have s1 : 2 * CKK * (r : ℝ) * Real.log ell_real ≤
        2 * CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ell_le h2CKKr_nn
    have s2 : 2 * CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
      have hrlog_nn : 0 ≤ (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
        positivity
      nlinarith
    linarith
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have hLHS_eq : CKK * κ⁻¹ * Real.log ell_real =
      CKK * Real.log ell_real / κ := by ring
  rw [hLHS_eq, div_le_div_iff₀ hκ_pos h2r_pos]
  have heq : CKK * Real.log ell_real * (2 * (r : ℝ)) =
      2 * CKK * (r : ℝ) * Real.log ell_real := by ring
  rw [heq, one_mul]
  exact hκ_lower

/-- **Partition-density lower bound.** Body is `sorry` — the full proof
chains `not_pSmall_of_spread`, `qSmallUpper_of_not_pSmall`,
`density_bound_from_kappa_aux` (algebraic core, proved above), and the
`park_pham_threshold` stub. Composing them in a single tactic block
triggered a `whnf` timeout >2M heartbeats during elaboration of the
universe-polymorphic `Classical.choose park_pham_threshold` against the
`muP X (upClosureIn X A) ...` goal. A focused subpass that restructures
the threshold's existential (e.g. takes CKK as an explicit input) is the
cleanest closure path; all the analytical content is already in
`density_bound_from_kappa_aux`. -/
theorem mu_at_partition_density_ge_half
    {X : Finset α} {A : Finset (Finset α)} {r k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hUniform : Erdos202.UniformFamily A k)
    (hSpread : Erdos202.SpreadFamily A κ)
    (hAX : ∀ S ∈ A, S ⊆ X)
    (hκ : Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 := by
  sorry

end

end ParkPham
end Erdos202
