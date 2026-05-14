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
   `κ ≥ Csp · r · log(ek)`. **Proved against the threshold package.**
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

/-! ## Counting argument: spread families are not small -/

/-- If `A` is a `κ`-spread nonempty `k`-uniform family with `k ≥ 1` and
`1 < κ`, then `upClosureIn X A` is not `p`-small at `p = κ⁻¹`. -/
theorem not_pSmall_of_spread
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (_hk : 1 ≤ k)
    (_hUniform : Erdos202.UniformFamily A k)
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
positivity arguments). It is isolated behind the named Park--Pham threshold
target for a focused subpass. -/

/-- The spread-disjointness constant produced from a Park–Pham threshold
constant. -/
noncomputable def CspOf (CKK : ℝ) : ℝ :=
  max 10 (8 * CKK)

lemma CspOf_pos (CKK : ℝ) : 0 < CspOf CKK := by
  unfold CspOf
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  norm_num

lemma CspOf_ge_ten (CKK : ℝ) : (10 : ℝ) ≤ CspOf CKK := le_max_left _ _

lemma CspOf_ge_two_CKK {CKK : ℝ} (hCKK_pos : 0 < CKK) :
    2 * CKK ≤ CspOf CKK := by
  unfold CspOf
  refine le_trans ?_ (le_max_right _ _)
  linarith

/-- Helper: universe-monomorphic density bound. Takes `CKK` as an opaque
real parameter so elaboration doesn't drag `Classical.choose` through. -/
private lemma density_bound_from_kappa_aux
    (CKK Csp : ℝ) (hCKK_pos : 0 < CKK) (hCsp_ge_2CKK : 2 * CKK ≤ Csp)
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

/-- **Partition-density lower bound, parameterized by a Park–Pham threshold
constant and theorem.** Chains `not_pSmall_of_spread`,
`qSmallUpper_of_not_pSmall`, `density_bound_from_kappa_aux`, and the supplied
threshold theorem. -/
theorem mu_at_partition_density_ge_half_of_threshold
    (CKK : ℝ) (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2)
    {X : Finset α} {A : Finset (Finset α)} {r k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hUniform : Erdos202.UniformFamily A k)
    (hSpread : Erdos202.SpreadFamily A κ)
    (hAX : ∀ S ∈ A, S ⊆ X)
    (hκ : CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 := by
  set U := upClosureIn X A with hU_def
  -- Reals from naturals
  have hr_real_ge_two : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hk_real_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by linarith
  -- e > 2 and log(e·k) ≥ 1
  have he_gt_two : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hek_pos : (0 : ℝ) < Real.exp 1 * (k : ℝ) := by positivity
  have hek_ge_e : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
    have h1 : Real.exp 1 * 1 ≤ Real.exp 1 * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk_real_ge_one he_pos.le
    simpa using h1
  have hlog_ek_ge_one : (1 : ℝ) ≤ Real.log (Real.exp 1 * (k : ℝ)) := by
    have h := Real.log_le_log he_pos hek_ge_e
    simpa [Real.log_exp] using h
  -- κ ≥ 20 > 1
  have hCsp_ge_ten : (10 : ℝ) ≤ CspOf CKK := CspOf_ge_ten CKK
  have hCsp_pos : 0 < CspOf CKK := CspOf_pos CKK
  have hbase_ge_20 :
      (20 : ℝ) ≤ CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
    have h1 : (10 : ℝ) * 2 ≤ CspOf CKK * (r : ℝ) :=
      mul_le_mul hCsp_ge_ten hr_real_ge_two (by norm_num) hCsp_pos.le
    have h2 :
        CspOf CKK * (r : ℝ) * 1 ≤
          CspOf CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ek_ge_one (by positivity)
    linarith
  have hκ_ge_20 : (20 : ℝ) ≤ κ := le_trans hbase_ge_20 hκ
  have hκ_pos : 0 < κ := by linarith
  have hκ_gt_one : 1 < κ := by linarith
  have hκ_ge_one : (1 : ℝ) ≤ κ := hκ_gt_one.le
  have hκ_inv_pos : (0 : ℝ) < κ⁻¹ := inv_pos.mpr hκ_pos
  have hκ_inv_le_one : κ⁻¹ ≤ 1 := by
    have h := inv_anti₀ (by linarith : (0 : ℝ) < 1) hκ_ge_one
    simpa using h
  -- Increasing + not p-small + qSmallUpper
  have hIncr : IncreasingIn X U := increasingIn_upClosureIn X A
  have hUXU : ∀ S ∈ U, S ⊆ X := by
    intro S hS
    have hS' : S ∈ upClosureIn X A := by simpa [hU_def] using hS
    exact (mem_upClosureIn.mp hS').1
  have hNotSmall : ¬ pSmall X U (κ⁻¹) :=
    not_pSmall_of_spread hA hk hUniform hSpread hκ_gt_one hAX
  have hqSmall : qSmallUpper X U (κ⁻¹) :=
    qSmallUpper_of_not_pSmall hκ_inv_pos.le hNotSmall
  -- ell bounds
  have hell_pos_nat : 0 < ell X U := ell_pos X U
  have hell_real_pos : (0 : ℝ) < (ell X U : ℝ) := by exact_mod_cast hell_pos_nat
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    have h := two_le_ell X U
    have h1 : 1 ≤ ell X U := le_trans (by norm_num) h
    exact_mod_cast h1
  have hell_le_max : ell X U ≤ max 2 k := ell_upClosure_le hUniform hAX
  have hmax_le_ek : ((max 2 k : ℕ) : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
    rcases Nat.lt_or_ge k 2 with hk2 | h2k
    · interval_cases k
      · have : (max 2 1 : ℕ) = 2 := by decide
        rw [this]
        have : ((2 : ℕ) : ℝ) = 2 := by norm_num
        rw [this]
        linarith
    · have hmax : max 2 k = k := max_eq_right h2k
      rw [hmax]
      have he_ge_one : (1 : ℝ) ≤ Real.exp 1 := by linarith
      nlinarith
  have hell_real_le_ek : (ell X U : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
    have h1 : ((ell X U : ℕ) : ℝ) ≤ ((max 2 k : ℕ) : ℝ) := by exact_mod_cast hell_le_max
    exact h1.trans hmax_le_ek
  -- Density bound: CKK * κ⁻¹ * log(ell U) ≤ 1/(2r)
  have h_density_bound :
      CKK * κ⁻¹ * Real.log (ell X U) ≤ (1 : ℝ) / (2 * (r : ℝ)) :=
    density_bound_from_kappa_aux CKK (CspOf CKK) hCKK_pos
      (CspOf_ge_two_CKK hCKK_pos)
      hr hk hell_real_pos hell_ge_one hell_real_le_ek hκ_pos hκ
  -- Density at-or-above-threshold positivity bounds
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have h_p_nn : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)) := by positivity
  have h_p_le_one : (1 : ℝ) / (2 * (r : ℝ)) ≤ 1 := by
    rw [div_le_one h2r_pos]
    linarith
  -- Apply the Park–Pham threshold theorem.
  have hgoal :
      muP X U ((1 : ℝ) / (2 * (r : ℝ))) ≥ 1 / 2 :=
    hThreshold X U (κ⁻¹) ((1 : ℝ) / (2 * (r : ℝ)))
      hκ_inv_pos hκ_inv_le_one h_p_nn h_p_le_one h_density_bound hUXU hIncr hqSmall
  simpa [hU_def] using hgoal

end

end ParkPham
end Erdos202
