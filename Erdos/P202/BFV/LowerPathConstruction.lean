/-
Erdos Problem 202 -- BFV lower construction, source-aligned rooted path family.

This file builds on `LowerPathScales.lean` and defines the finite objects for
the BFV-compatible lower-bound refactor.  It is intentionally not wired into
`LowerBoundInput.lean` yet: the live lower theorem still uses
`LowerConstruction.lean`.  The point here is to grow a fully proved replacement
around the corrected path scales.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.BFV.Chebyshev
import Erdos.P202.BFV.PrimeIntervals
import Erdos.P202.BFV.LowerPathScales

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Path choices and moduli -/

/-- Root block index for the source-aligned path construction. -/
def lowerPathZeroIndex (N : ℕ) : lowerPathIndex N :=
  ⟨0, Nat.succ_pos _⟩

/-- Non-root path blocks.  The lower family fixes a small common root factor and
varies over these tail blocks. -/
abbrev lowerPathTailIndex (N : ℕ) : Type :=
  {i : lowerPathIndex N // i ≠ lowerPathZeroIndex N}

/-- The `k`th varying path block, i.e. block number `k+1`. -/
def lowerPathTailBlock (N : ℕ) (k : Fin (lowerPathR N)) :
    lowerPathTailIndex N :=
  ⟨k.succ, by
    intro h
    have hval := congrArg Fin.val h
    simp [lowerPathZeroIndex, Fin.val_succ] at hval⟩

lemma lowerPathTailBlock_surjective (N : ℕ) :
    Function.Surjective (lowerPathTailBlock N) := by
  intro i
  have hi0 : i.1 ≠ 0 := by
    intro h
    exact i.2 (by simpa [lowerPathZeroIndex] using h)
  refine ⟨i.1.pred hi0, ?_⟩
  apply Subtype.ext
  exact Fin.succ_pred i.1 hi0

lemma lowerPathTailBlock_injective (N : ℕ) :
    Function.Injective (lowerPathTailBlock N) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg (fun x : lowerPathTailIndex N => x.1.1) hij
  simpa [lowerPathTailBlock] using hval

noncomputable def lowerPathTailBlockEquiv (N : ℕ) :
    Fin (lowerPathR N) ≃ lowerPathTailIndex N :=
  Equiv.ofBijective (lowerPathTailBlock N)
    ⟨lowerPathTailBlock_injective N, lowerPathTailBlock_surjective N⟩

lemma lowerPathTailIndex_card (N : ℕ) :
    Fintype.card (lowerPathTailIndex N) = lowerPathR N := by
  exact (Fintype.card_congr (lowerPathTailBlockEquiv N).symm).trans
    (Fintype.card_fin (lowerPathR N))

/-- The `i`th dyadic prime block for the source-aligned path construction. -/
noncomputable def lowerPathPrimeInterval (N : ℕ) (i : lowerPathIndex N) :
    Finset ℕ :=
  dyadicPrimeInterval (lowerPathY N i)

/-- Small shared root factor at the first path scale.

Using `floor Y_0 + 1` keeps this file total.  The later BFV proof only needs a
common factor coprime to every tail prime; primality of the root is not needed
for the CRT construction. -/
noncomputable def lowerPathP0 (N : ℕ) : ℕ :=
  Nat.floor (lowerPathY N (lowerPathZeroIndex N)) + 1

lemma lowerPathP0_pos (N : ℕ) : 0 < lowerPathP0 N := by
  simp [lowerPathP0]

/-- A choice of one prime from every non-root path block. -/
abbrev LowerPathPrimeChoice (N : ℕ) : Type :=
  (i : lowerPathTailIndex N) → {p : ℕ // p ∈ lowerPathPrimeInterval N i.1}

lemma lowerPathTailBlock_ext {N : ℕ} {P P' : LowerPathPrimeChoice N}
    (h : ∀ k : Fin (lowerPathR N),
      P (lowerPathTailBlock N k) = P' (lowerPathTailBlock N k)) :
    P = P' := by
  funext i
  rcases lowerPathTailBlock_surjective N i with ⟨k, rfl⟩
  exact h k

/-- All source-aligned path choices. -/
noncomputable def lowerPathChoices (N : ℕ) :
    Finset (LowerPathPrimeChoice N) :=
  Fintype.piFinset fun i : lowerPathTailIndex N =>
    (lowerPathPrimeInterval N i.1).attach

lemma lowerPathChoices_card (N : ℕ) :
    (lowerPathChoices N).card =
      ∏ i : lowerPathTailIndex N, (lowerPathPrimeInterval N i.1).card := by
  simp [lowerPathChoices, Fintype.card_piFinset]

noncomputable def lowerPathPrimeFloorProduct (η : ℝ) (N : ℕ) : ℕ :=
  ∏ i : lowerPathTailIndex N,
    Nat.floor (((1 - η) * lowerPathY N i.1) /
      Real.log (lowerPathY N i.1))

/-- The `η` value whose coefficient `1 - η` is the Chebyshev dyadic-prime
constant proved in `BFV/Chebyshev.lean`. -/
noncomputable def lowerPathChebEta : ℝ :=
  1 - dyadicPrimeIntervalConstant

lemma lowerPath_one_sub_chebEta :
    1 - lowerPathChebEta = dyadicPrimeIntervalConstant := by
  simp [lowerPathChebEta]

lemma dyadicPrimeIntervalConstant_lt_one :
    dyadicPrimeIntervalConstant < 1 := by
  have hlog4_le : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  unfold dyadicPrimeIntervalConstant
  nlinarith

lemma lowerPathChebEta_pos : 0 < lowerPathChebEta := by
  unfold lowerPathChebEta
  linarith [dyadicPrimeIntervalConstant_lt_one]

noncomputable def lowerPathDenominatorConstant : ℝ :=
  4 / dyadicPrimeIntervalConstant

lemma lowerPathDenominatorConstant_pos : 0 < lowerPathDenominatorConstant := by
  unfold lowerPathDenominatorConstant
  exact div_pos (by norm_num) dyadicPrimeIntervalConstant_pos

noncomputable def lowerPathRealPrimeProduct (N : ℕ) : ℝ :=
  ∏ i : lowerPathTailIndex N,
    (((dyadicPrimeIntervalConstant * lowerPathY N i.1) /
      Real.log (lowerPathY N i.1)) / 2)

noncomputable def lowerPathRealDenominator (N : ℕ) : ℝ :=
  (2 * lowerPathY N (lowerPathZeroIndex N)) *
    ∏ i : lowerPathTailIndex N,
      lowerPathDenominatorConstant * Real.log (lowerPathY N i.1)

lemma lowerPath_half_le_floor_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  have hx_floor : x < (Nat.floor x : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hx_half_le_sub : x / 2 ≤ x - 1 := by linarith
  linarith

lemma lowerPath_two_le_half_mul_div_log_of_ge_64 {y : ℝ} (hy : 64 ≤ y) :
    2 ≤ ((1 / 2 : ℝ) * y) / Real.log y := by
  have hy_nonneg : 0 ≤ y := by linarith
  have hy_pos : 0 < y := by linarith
  have hy_gt_one : 1 < y := by linarith
  have hlog_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hlog_le : Real.log y ≤ 2 * Real.sqrt y := by
    have h :=
      Real.log_le_rpow_div (x := y) (ε := (1 / 2 : ℝ)) hy_nonneg (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    calc
      Real.log y ≤ Real.sqrt y / (1 / 2 : ℝ) := h
      _ = 2 * Real.sqrt y := by ring
  have hsqrt_ge : 8 ≤ Real.sqrt y := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 8) hy_nonneg).2 ?_
    norm_num
    exact hy
  have hsqrt_sq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy_nonneg
  have hfourlog : 4 * Real.log y ≤ y := by
    nlinarith
  have hden_pos : 0 < 2 * Real.log y := by positivity
  have hmain : 2 ≤ y / (2 * Real.log y) :=
    (le_div_iff₀ hden_pos).2 (by nlinarith [hfourlog])
  calc
    2 ≤ y / (2 * Real.log y) := hmain
    _ = ((1 / 2 : ℝ) * y) / Real.log y := by
          field_simp [hlog_pos.ne']

lemma lowerPath_two_le_cheb_mul_div_log_of_ge {y : ℝ}
    (hy : (4 / dyadicPrimeIntervalConstant) ^ 2 ≤ y) :
    2 ≤ (dyadicPrimeIntervalConstant * y) / Real.log y := by
  have hc : 0 < dyadicPrimeIntervalConstant := dyadicPrimeIntervalConstant_pos
  have hc_lt_one : dyadicPrimeIntervalConstant < 1 :=
    dyadicPrimeIntervalConstant_lt_one
  have hfour_le : (4 : ℝ) ≤ 4 / dyadicPrimeIntervalConstant := by
    rw [le_div_iff₀ hc]
    nlinarith
  have hbase_nonneg : 0 ≤ 4 / dyadicPrimeIntervalConstant := by positivity
  have hy_ge16 : (16 : ℝ) ≤ y := by
    have hsq :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hfour_le 2
    norm_num at hsq
    exact hsq.trans hy
  have hy_nonneg : 0 ≤ y := by linarith
  have hy_gt_one : 1 < y := by linarith
  have hlog_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hlog_le : Real.log y ≤ 2 * Real.sqrt y := by
    have h :=
      Real.log_le_rpow_div (x := y) (ε := (1 / 2 : ℝ)) hy_nonneg (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    calc
      Real.log y ≤ Real.sqrt y / (1 / 2 : ℝ) := h
      _ = 2 * Real.sqrt y := by ring
  have hsqrt_ge : 4 / dyadicPrimeIntervalConstant ≤ Real.sqrt y := by
    exact (Real.le_sqrt hbase_nonneg hy_nonneg).2 hy
  have hfour_le_csqrt : 4 ≤ dyadicPrimeIntervalConstant * Real.sqrt y := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt_ge hc.le
    field_simp [hc.ne'] at hmul
    exact hmul
  have hfour_sqrt_le_cy :
      4 * Real.sqrt y ≤ dyadicPrimeIntervalConstant * y := by
    calc
      4 * Real.sqrt y ≤
          (dyadicPrimeIntervalConstant * Real.sqrt y) * Real.sqrt y := by
            exact mul_le_mul_of_nonneg_right hfour_le_csqrt (Real.sqrt_nonneg y)
      _ = dyadicPrimeIntervalConstant * y := by
            rw [mul_assoc, ← sq, Real.sq_sqrt hy_nonneg]
  have htwo_log_le : 2 * Real.log y ≤ dyadicPrimeIntervalConstant * y := by
    calc
      2 * Real.log y ≤ 4 * Real.sqrt y := by nlinarith
      _ ≤ dyadicPrimeIntervalConstant * y := hfour_sqrt_le_cy
  exact (le_div_iff₀ hlog_pos).2 htwo_log_le

theorem lowerPathPrimeFloorProduct_floor_loss_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealPrimeProduct N ≤
        (lowerPathPrimeFloorProduct lowerPathChebEta N : ℝ) := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge
        ((4 / dyadicPrimeIntervalConstant) ^ 2)] with N hgap hY0
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  unfold lowerPathPrimeFloorProduct
  unfold lowerPathRealPrimeProduct
  rw [Nat.cast_prod]
  exact Finset.prod_le_prod
    (fun i _hi => by
      have hzero_le_i :
          lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
        lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
      have hY0' :
          (4 / dyadicPrimeIntervalConstant) ^ 2 ≤
            lowerPathY N (lowerPathZeroIndex N) := by
        simpa [lowerPathZeroIndex] using hY0
      have hfactor :
          2 ≤ (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
              Real.log (lowerPathY N i.1) :=
        lowerPath_two_le_cheb_mul_div_log_of_ge (hY0'.trans hzero_le_i)
      positivity)
    (fun i _hi => by
      have hzero_le_i :
          lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
        lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
      have hY0' :
          (4 / dyadicPrimeIntervalConstant) ^ 2 ≤
            lowerPathY N (lowerPathZeroIndex N) := by
        simpa [lowerPathZeroIndex] using hY0
      have hfactor :
          2 ≤ (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
              Real.log (lowerPathY N i.1) :=
        lowerPath_two_le_cheb_mul_div_log_of_ge (hY0'.trans hzero_le_i)
      rw [show ((1 - lowerPathChebEta) * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1) =
          (dyadicPrimeIntervalConstant * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1) by
              rw [lowerPath_one_sub_chebEta]]
      exact lowerPath_half_le_floor_of_two_le hfactor)

lemma lowerPathY_dyadic_tail_product_eq {N : ℕ} (hNpos : 0 < (N : ℝ)) :
    (2 * lowerPathY N (lowerPathZeroIndex N)) *
        (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
      = (N : ℝ) := by
  let g : lowerPathIndex N → ℝ := fun i => (2 : ℝ) * lowerPathY N i
  have hsplit := Fintype.prod_eq_mul_prod_compl (lowerPathZeroIndex N) g
  have htail_prod :
      (∏ i ∈ ({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ, g i) =
        ∏ i : lowerPathTailIndex N, g i.1 := by
    exact Finset.prod_subtype
      (({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ)
      (by intro x; simp)
      g
  calc
    (2 * lowerPathY N (lowerPathZeroIndex N)) *
        (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
        = ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := by
          simpa [g, htail_prod] using hsplit.symm
    _ = (N : ℝ) := lowerPathY_dyadic_product_eq hNpos

lemma lowerPathRealPrimeProduct_mul_denominator_eq {N : ℕ}
    (hNpos : 0 < (N : ℝ))
    (hlog : ∀ i : lowerPathTailIndex N,
      Real.log (lowerPathY N i.1) ≠ 0) :
    lowerPathRealPrimeProduct N * lowerPathRealDenominator N = (N : ℝ) := by
  have htail :
      lowerPathRealPrimeProduct N *
          (∏ i : lowerPathTailIndex N,
            lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
        =
          ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by
    unfold lowerPathRealPrimeProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _hi
    have hlogi := hlog i
    dsimp [lowerPathDenominatorConstant]
    field_simp [hlogi, dyadicPrimeIntervalConstant_pos.ne']
    ring
  calc
      lowerPathRealPrimeProduct N *
        lowerPathRealDenominator N
        = (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathRealPrimeProduct N *
              ∏ i : lowerPathTailIndex N,
                lowerPathDenominatorConstant * Real.log (lowerPathY N i.1)) := by
          unfold lowerPathRealDenominator
          ring
    _ = (2 * lowerPathY N (lowerPathZeroIndex N)) *
          ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by rw [htail]
    _ = (N : ℝ) := lowerPathY_dyadic_tail_product_eq hNpos

lemma lowerPathRealDenominator_pos {N : ℕ}
    (hlog_pos : ∀ i : lowerPathTailIndex N,
      0 < Real.log (lowerPathY N i.1)) :
    0 < lowerPathRealDenominator N := by
  unfold lowerPathRealDenominator
  exact mul_pos
    (mul_pos (by norm_num) (Real.exp_pos _))
    (Finset.prod_pos (fun i _hi =>
      mul_pos lowerPathDenominatorConstant_pos (hlog_pos i)))

theorem lowerPathRealDenominator_le_simple_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealDenominator N ≤
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge 64,
      eventually_lowerPathLogScale_le_Zscale,
      eventually_Zscale_pos] with N hgap hY0 hscale_le hZpos
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hlog_nonneg : ∀ i : lowerPathTailIndex N,
      0 ≤ Real.log (lowerPathY N i.1) := by
    intro i
    have hzero_le_i :
        lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
      lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
    have hY0' : (64 : ℝ) ≤ lowerPathY N (lowerPathZeroIndex N) := by
      simpa [lowerPathZeroIndex] using hY0
    exact (Real.log_pos (by linarith [hY0'.trans hzero_le_i])).le
  have hprod :
      (∏ i : lowerPathTailIndex N,
          lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
        ≤ (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
    calc
      (∏ i : lowerPathTailIndex N,
          lowerPathDenominatorConstant * Real.log (lowerPathY N i.1))
          ≤ ∏ _i : lowerPathTailIndex N,
              lowerPathDenominatorConstant * Zscale N := by
            exact Finset.prod_le_prod
              (fun i _hi => mul_nonneg lowerPathDenominatorConstant_pos.le
                (hlog_nonneg i))
              (fun i _hi => by
                have hlog_eq :
                    Real.log (lowerPathY N i.1) = lowerPathLogScale N i.1 := by
                  rw [lowerPathY, Real.log_exp]
                rw [hlog_eq]
                exact mul_le_mul_of_nonneg_left (hscale_le i.1)
                  lowerPathDenominatorConstant_pos.le)
      _ = (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N := by
            rw [Finset.prod_const]
            have hcard :
                (Finset.univ : Finset (lowerPathTailIndex N)).card = lowerPathR N := by
              exact lowerPathTailIndex_card N
            rw [hcard]
  unfold lowerPathRealDenominator
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

theorem lowerPathPrimeInterval_card_lower_bound_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathTailIndex N,
        Nat.floor (((1 - lowerPathChebEta) * lowerPathY N i.1) /
            Real.log (lowerPathY N i.1)) ≤
          (lowerPathPrimeInterval N i.1).card := by
  rcases eventually_atTop.1
      dyadicPrimeInterval_card_lower_bound with
    ⟨Y, hY⟩
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge Y] with N hgap hY0 i
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hzero_le_i :
      lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
    lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hY0' : Y ≤ lowerPathY N (lowerPathZeroIndex N) := by
    simpa [lowerPathZeroIndex] using hY0
  simpa [lowerPathPrimeInterval, lowerPath_one_sub_chebEta] using
    hY (lowerPathY N i.1) (hY0'.trans hzero_le_i)

theorem lowerPathChoices_card_ge_prime_floor_product_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathPrimeFloorProduct lowerPathChebEta N ≤
        (lowerPathChoices N).card := by
  filter_upwards [lowerPathPrimeInterval_card_lower_bound_eventually] with N hblock
  rw [lowerPathChoices_card]
  unfold lowerPathPrimeFloorProduct
  exact Finset.prod_le_prod
    (fun i _hi => Nat.zero_le _)
    (fun i _hi => hblock i)

/-- The modulus attached to a source-aligned path choice. -/
noncomputable def lowerPathModulus (N : ℕ) (P : LowerPathPrimeChoice N) : ℕ :=
  lowerPathP0 N * ∏ i : lowerPathTailIndex N, (P i).1

/-- The finite source-aligned lower family of moduli. -/
noncomputable def lowerPathQ (N : ℕ) : Finset ℕ :=
  (lowerPathChoices N).image (lowerPathModulus N)

lemma lowerPathModulus_pos (N : ℕ) (P : LowerPathPrimeChoice N) :
    0 < lowerPathModulus N P := by
  unfold lowerPathModulus
  exact mul_pos (lowerPathP0_pos N) (Finset.prod_pos (fun i _hi => by
    have hp : Nat.Prime (P i).1 := (mem_dyadicPrimeInterval.1 (P i).2).2.2
    exact hp.pos))

lemma lowerPathRootFactor_le_two_mul_lowerPathY {N : ℕ}
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) :
    (lowerPathP0 N : ℝ) ≤ 2 * lowerPathY N (lowerPathZeroIndex N) := by
  have hY0_nonneg : 0 ≤ lowerPathY N (lowerPathZeroIndex N) := (Real.exp_pos _).le
  have hfloor :
      ((Nat.floor (lowerPathY N (lowerPathZeroIndex N)) : ℕ) : ℝ) ≤
        lowerPathY N (lowerPathZeroIndex N) :=
    Nat.floor_le hY0_nonneg
  rw [lowerPathP0]
  norm_num
  linarith

/-- If the small root scale is at least `1`, every source-aligned path modulus
lies in `[1, N]`. -/
lemma lowerPathModulus_le_N_of_root_scale {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) (P : LowerPathPrimeChoice N) :
    lowerPathModulus N P ≤ N := by
  classical
  have hroot := lowerPathRootFactor_le_two_mul_lowerPathY (N := N) hY0
  have htail :
      ((∏ i : lowerPathTailIndex N, (P i).1 : ℕ) : ℝ) ≤
        ∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1 := by
    rw [Nat.cast_prod]
    exact Finset.prod_le_prod
      (fun i _hi => by positivity)
      (fun i _hi => by
        have hmem : (P i).1 ∈ lowerPathPrimeInterval N i.1 := (P i).2
        have hle_nat : (P i).1 ≤ Nat.floor (2 * lowerPathY N i.1) :=
          (mem_dyadicPrimeInterval.1 hmem).2.1
        have hnonneg : 0 ≤ 2 * lowerPathY N i.1 := by
          exact mul_nonneg (by norm_num) (Real.exp_pos _).le
        exact le_trans (by exact_mod_cast hle_nat)
          (Nat.floor_le hnonneg))
  have hprod_split :
      (2 : ℝ) * lowerPathY N (lowerPathZeroIndex N) *
          (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1)
        =
      ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := by
    let f : lowerPathIndex N → ℝ := fun i => (2 : ℝ) * lowerPathY N i
    have hsplit := Fintype.prod_eq_mul_prod_compl (lowerPathZeroIndex N) f
    have htail_prod :
        (∏ i ∈ ({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ, f i) =
          ∏ i : lowerPathTailIndex N, f i.1 := by
      exact Finset.prod_subtype
        (({lowerPathZeroIndex N} : Finset (lowerPathIndex N))ᶜ)
        (by intro x; simp)
        f
    simpa [f, htail_prod] using hsplit.symm
  have hreal :
      (lowerPathModulus N P : ℝ) ≤ (N : ℝ) := by
    rw [lowerPathModulus, Nat.cast_mul]
    calc
      (lowerPathP0 N : ℝ) * ((∏ i : lowerPathTailIndex N, (P i).1 : ℕ) : ℝ)
          ≤ (2 * lowerPathY N (lowerPathZeroIndex N)) *
              (∏ i : lowerPathTailIndex N, (2 : ℝ) * lowerPathY N i.1) := by
            exact mul_le_mul hroot htail (by positivity) (by positivity)
      _ = ∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i := hprod_split
      _ = (N : ℝ) := lowerPathY_dyadic_product_eq hNpos
  exact_mod_cast hreal

lemma lowerPathQ_moduli_in_range_of_root_scale {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N)) :
    ∀ q ∈ lowerPathQ N, 1 ≤ q ∧ q ≤ N := by
  intro q hq
  rcases Finset.mem_image.1 hq with ⟨P, _hP, rfl⟩
  exact ⟨lowerPathModulus_pos N P, lowerPathModulus_le_N_of_root_scale hNpos hY0 P⟩

theorem lowerPathQ_moduli_in_range_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ q ∈ lowerPathQ N, 1 ≤ q ∧ q ≤ N := by
  filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_lowerPathY_zero_ge_one] with N hNpos_nat hY0
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  exact lowerPathQ_moduli_in_range_of_root_scale hNpos hY0

/-! ## Eventual separation and root coprimality -/

/-- The source-aligned path prime blocks are eventually pairwise disjoint. -/
theorem lowerPathPrimeIntervals_pairwise_disjoint :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerPathIndex N, i ≠ j →
        Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j) := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two] with N hgap
  intro i j hij
  have hijval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hijval with hlt | hgt
  · have hsep : 2 * lowerPathY N i < lowerPathY N j :=
      lowerPathY_dyadic_lt_of_lt_index hgap hlt
    have hfloor : Nat.floor (2 * lowerPathY N i) ≤ Nat.floor (lowerPathY N j) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerPathY N i))
            (Nat.floor (2 * lowerPathY N i)))
          (Finset.Ioc (Nat.floor (lowerPathY N j))
            (Nat.floor (2 * lowerPathY N j))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPathPrimeInterval, dyadicPrimeInterval] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)
  · have hsep : 2 * lowerPathY N j < lowerPathY N i :=
      lowerPathY_dyadic_lt_of_lt_index hgap hgt
    have hfloor : Nat.floor (2 * lowerPathY N j) ≤ Nat.floor (lowerPathY N i) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerPathY N j))
            (Nat.floor (2 * lowerPathY N j)))
          (Finset.Ioc (Nat.floor (lowerPathY N i))
            (Nat.floor (2 * lowerPathY N i))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPathPrimeInterval, dyadicPrimeInterval, disjoint_comm] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)

lemma lowerPathDyadicPrimeInterval_card_le_primeCounting (y : ℝ) :
    (dyadicPrimeInterval y).card ≤ Nat.primeCounting (Nat.floor (2 * y)) := by
  classical
  have hsub :
      dyadicPrimeInterval y ⊆
        (Finset.range (Nat.floor (2 * y) + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range]
    have hp' := mem_dyadicPrimeInterval.1 hp
    exact ⟨Nat.lt_succ_of_le hp'.2.1, hp'.2.2⟩
  have hcard := Finset.card_le_card hsub
  simpa [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range] using hcard

lemma lowerPathPrimeInterval_adjacent_card_le_floor_prev_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerPathIndex N, j.1 = i.1 + 1 →
        (lowerPathPrimeInterval N j).card ≤ Nat.floor (lowerPathY N i) := by
  classical
  let B : ℝ := (Real.log 4 + 1) * 2
  have hBpos : 0 < B := by
    dsimp [B]
    have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    positivity
  rcases eventually_atTop.1
      (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one) with
    ⟨X, hcheb⟩
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPath_adjacent_ratio_le_logscale_zero B,
      eventually_lowerPath_adjacent_ratio_le_logscale_zero (Real.log (max X 1))] with
    N hgap_gt hratioB hratioX
  intro i j hij
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    exact hlog_two_nonneg.trans hgap_gt.le
  have hexpgap_ge_one : 1 ≤ Real.exp (lowerPathLogGap N) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 hgap_nonneg
  have hzero_le_j_scale :
      lowerPathLogScale N (lowerPathZeroIndex N) ≤ lowerPathLogScale N j :=
    lowerPathLogScale_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hzero_le_j :
      lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N j :=
    lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
  have hYj_eq :
      lowerPathY N j = lowerPathY N i * Real.exp (lowerPathLogGap N) :=
    lowerPathY_adjacent_eq_mul_exp_gap hij
  have hlog_max_nonneg : 0 ≤ Real.log (max X 1) :=
    Real.log_nonneg (le_max_right X 1)
  have hlogmax_le_scale0 :
      Real.log (max X 1) ≤ lowerPathLogScale N (lowerPathZeroIndex N) := by
    calc
      Real.log (max X 1)
          ≤ Real.log (max X 1) * Real.exp (lowerPathLogGap N) := by
            exact le_mul_of_one_le_right hlog_max_nonneg hexpgap_ge_one
      _ ≤ lowerPathLogScale N (lowerPathZeroIndex N) := hratioX
  have hmax_pos : 0 < max X 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right X 1)
  have hmax_le_Y0 : max X 1 ≤ lowerPathY N (lowerPathZeroIndex N) := by
    rw [lowerPathY]
    exact (Real.log_le_iff_le_exp hmax_pos).1 hlogmax_le_scale0
  have hX_le_arg : X ≤ 2 * lowerPathY N j := by
    have hX_le_j : X ≤ lowerPathY N j :=
      (le_max_left X 1).trans (hmax_le_Y0.trans hzero_le_j)
    have hj_nonneg : 0 ≤ lowerPathY N j := (Real.exp_pos _).le
    nlinarith
  have hcheb_arg := hcheb (2 * lowerPathY N j) hX_le_arg
  have hcard_pc :
      ((lowerPathPrimeInterval N j).card : ℝ) ≤
        (Nat.primeCounting (Nat.floor (2 * lowerPathY N j)) : ℝ) := by
    exact_mod_cast lowerPathDyadicPrimeInterval_card_le_primeCounting (lowerPathY N j)
  have hlog_arg_eq :
      Real.log (2 * lowerPathY N j) =
        Real.log 2 + lowerPathLogScale N j := by
    rw [lowerPathY, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp]
  have hlog_arg_ge_Bexp :
      B * Real.exp (lowerPathLogGap N) ≤ Real.log (2 * lowerPathY N j) := by
    calc
      B * Real.exp (lowerPathLogGap N)
          ≤ lowerPathLogScale N (lowerPathZeroIndex N) := hratioB
      _ ≤ lowerPathLogScale N j := hzero_le_j_scale
      _ ≤ Real.log (2 * lowerPathY N j) := by
            rw [hlog_arg_eq]
            have hlog_two_nonneg : 0 ≤ Real.log 2 :=
              Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
            linarith
  have hlog_arg_pos : 0 < Real.log (2 * lowerPathY N j) :=
    (mul_pos hBpos (Real.exp_pos _)).trans_le hlog_arg_ge_Bexp
  have hnum_eq :
      (Real.log 4 + 1) * (2 * lowerPathY N j) =
        (B * Real.exp (lowerPathLogGap N)) * lowerPathY N i := by
    rw [hYj_eq]
    dsimp [B]
    ring
  have hquot_le :
      (Real.log 4 + 1) * (2 * lowerPathY N j) / Real.log (2 * lowerPathY N j)
        ≤ lowerPathY N i := by
    rw [div_le_iff₀ hlog_arg_pos]
    have hi_nonneg : 0 ≤ lowerPathY N i := (Real.exp_pos _).le
    calc
      (Real.log 4 + 1) * (2 * lowerPathY N j)
          = (B * Real.exp (lowerPathLogGap N)) * lowerPathY N i := hnum_eq
      _ ≤ Real.log (2 * lowerPathY N j) * lowerPathY N i := by
            exact mul_le_mul_of_nonneg_right hlog_arg_ge_Bexp hi_nonneg
      _ = lowerPathY N i * Real.log (2 * lowerPathY N j) := by ring
  have hcard_real : ((lowerPathPrimeInterval N j).card : ℝ) ≤ lowerPathY N i := by
    exact hcard_pc.trans (hcheb_arg.trans hquot_le)
  exact Nat.le_floor hcard_real

/-- Unique factorization plus disjoint source-aligned prime blocks makes the
path modulus map injective. -/
theorem lowerPathModulus_injective_eventually :
    ∀ᶠ N : ℕ in atTop,
      Set.InjOn (lowerPathModulus N)
        (↑(lowerPathChoices N) : Set (LowerPathPrimeChoice N)) := by
  filter_upwards [lowerPathPrimeIntervals_pairwise_disjoint] with N hdisj
  intro P _hP P' _hP' heq
  have htail_eq :
      (∏ i : lowerPathTailIndex N, (P i).1) =
        ∏ i : lowerPathTailIndex N, (P' i).1 := by
    have hp0 : lowerPathP0 N ≠ 0 := (lowerPathP0_pos N).ne'
    exact mul_left_cancel₀ hp0 (by simpa [lowerPathModulus] using heq)
  funext i
  apply Subtype.ext
  let p : ℕ := (P i).1
  have hpPrime : Nat.Prime p := (mem_dyadicPrimeInterval.1 (P i).2).2.2
  have hp_dvd_left : p ∣ ∏ k : lowerPathTailIndex N, (P k).1 := by
    unfold p
    exact Finset.dvd_prod_of_mem
      (fun k : lowerPathTailIndex N => (P k).1) (Finset.mem_univ i)
  have hp_dvd_prod : p ∣ ∏ k : lowerPathTailIndex N, (P' k).1 := by
    rwa [htail_eq] at hp_dvd_left
  rcases (hpPrime.prime.dvd_finset_prod_iff (S := Finset.univ)
      (fun k : lowerPathTailIndex N => (P' k).1)).1 hp_dvd_prod with
    ⟨j, _hj, hp_dvd_pj⟩
  have hpjPrime : Nat.Prime (P' j).1 := (mem_dyadicPrimeInterval.1 (P' j).2).2.2
  have hp_eq_pj : p = (P' j).1 :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hpjPrime).1 hp_dvd_pj
  have hji : j = i := by
    by_contra hne
    have hne' : i.1 ≠ j.1 := by
      intro h
      exact hne (Subtype.ext h.symm)
    have hp_mem_i : p ∈ lowerPathPrimeInterval N i.1 := (P i).2
    have hp_mem_j : p ∈ lowerPathPrimeInterval N j.1 := by
      simp [p, hp_eq_pj, (P' j).2]
    exact Finset.disjoint_left.1 (hdisj i.1 j.1 hne') hp_mem_i hp_mem_j
  subst hji
  simpa [p] using hp_eq_pj

lemma lowerPathQ_card_eq_lowerPathChoices_card_of_injective {N : ℕ}
    (hinj : Set.InjOn (lowerPathModulus N)
      (↑(lowerPathChoices N) : Set (LowerPathPrimeChoice N))) :
    (lowerPathQ N).card = (lowerPathChoices N).card := by
  simpa [lowerPathQ] using Finset.card_image_of_injOn (s := lowerPathChoices N)
    (f := lowerPathModulus N) hinj

theorem lowerPathQ_card_ge_prime_floor_product_eventually :
    ∀ᶠ N : ℕ in atTop,
      lowerPathPrimeFloorProduct lowerPathChebEta N ≤ (lowerPathQ N).card := by
  filter_upwards [lowerPathModulus_injective_eventually,
      lowerPathChoices_card_ge_prime_floor_product_eventually] with
    N hinj hchoices
  rwa [lowerPathQ_card_eq_lowerPathChoices_card_of_injective hinj]

lemma lowerPath_root_coprime_tail_prime {N : ℕ}
    (hgap : Real.log 2 < lowerPathLogGap N)
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N))
    (i : lowerPathTailIndex N) (p : ℕ)
    (hp : p ∈ lowerPathPrimeInterval N i.1) :
    Nat.Coprime (lowerPathP0 N) p := by
  have hroot_le :
      (lowerPathP0 N : ℝ) ≤ 2 * lowerPathY N (lowerPathZeroIndex N) :=
    lowerPathRootFactor_le_two_mul_lowerPathY hY0
  have hi_pos : 0 < i.1.1 := by
    by_contra hnot
    have hzero : i.1.1 = 0 := Nat.eq_zero_of_not_pos hnot
    exact i.2 (Fin.ext hzero)
  have hsep :
      2 * lowerPathY N (lowerPathZeroIndex N) < lowerPathY N i.1 :=
    lowerPathY_dyadic_lt_of_lt_index hgap (by
      simpa [lowerPathZeroIndex] using hi_pos)
  have hp_floor : Nat.floor (lowerPathY N i.1) < p := by
    exact (mem_dyadicPrimeInterval.1 hp).1
  have hy_lt_p : lowerPathY N i.1 < (p : ℝ) := by
    have hy_floor : lowerPathY N i.1 < (Nat.floor (lowerPathY N i.1) : ℝ) + 1 :=
      Nat.lt_floor_add_one (lowerPathY N i.1)
    have hfloor_succ_le : Nat.floor (lowerPathY N i.1) + 1 ≤ p :=
      Nat.succ_le_of_lt hp_floor
    exact hy_floor.trans_le (by exact_mod_cast hfloor_succ_le)
  have hp0_lt_p_real : (lowerPathP0 N : ℝ) < (p : ℝ) :=
    hroot_le.trans_lt (hsep.trans hy_lt_p)
  have hp0_lt_p : lowerPathP0 N < p := by
    exact_mod_cast hp0_lt_p_real
  have hpprime : Nat.Prime p := (mem_dyadicPrimeInterval.1 hp).2.2
  exact (Nat.coprime_of_lt_prime (lowerPathP0_pos N).ne' hp0_lt_p hpprime).symm

theorem lowerPath_root_coprime_tail_prime_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
        p ∈ lowerPathPrimeInterval N i.1 →
          Nat.Coprime (lowerPathP0 N) p := by
  filter_upwards [eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge_one] with N hgap hY0 i p hp
  exact lowerPath_root_coprime_tail_prime hgap hY0 i p hp

/-! ## CRT modulus skeleton -/

/-- The common root or one selected tail prime, used as a CRT modulus. -/
abbrev lowerPathCRTIndex (N : ℕ) : Type :=
  Option (Fin (lowerPathR N))

/-- CRT modulus attached to a root/tail coordinate. -/
noncomputable def lowerPathCRTModulus (N : ℕ) (P : LowerPathPrimeChoice N) :
    lowerPathCRTIndex N → ℕ
  | none => lowerPathP0 N
  | some k => (P (lowerPathTailBlock N k)).1

lemma lowerPathCRTModulus_ne_zero (N : ℕ) (P : LowerPathPrimeChoice N)
    (i : lowerPathCRTIndex N) :
    lowerPathCRTModulus N P i ≠ 0 := by
  cases i with
  | none => exact (lowerPathP0_pos N).ne'
  | some k =>
      have hp : Nat.Prime (P (lowerPathTailBlock N k)).1 :=
        (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N k)).2).2.2
      exact hp.ne_zero

lemma lowerPathCRTModulus_dvd_lowerPathModulus (N : ℕ) (P : LowerPathPrimeChoice N)
    (i : lowerPathCRTIndex N) :
    lowerPathCRTModulus N P i ∣ lowerPathModulus N P := by
  cases i with
  | none =>
      rw [lowerPathCRTModulus, lowerPathModulus]
      exact dvd_mul_right _ _
  | some k =>
      rw [lowerPathCRTModulus, lowerPathModulus]
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem (fun i : lowerPathTailIndex N => (P i).1)
          (Finset.mem_univ (lowerPathTailBlock N k)))
        (lowerPathP0 N)

lemma lowerPathCRTModuli_pairwise_coprime {N : ℕ}
    (P : LowerPathPrimeChoice N)
    (hroot : ∀ i : lowerPathTailIndex N, Nat.Coprime (lowerPathP0 N) (P i).1)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    Set.Pairwise (↑(Finset.univ : Finset (lowerPathCRTIndex N)) :
      Set (lowerPathCRTIndex N))
      (fun i j => Nat.Coprime (lowerPathCRTModulus N P i)
        (lowerPathCRTModulus N P j)) := by
  intro i _hi j _hj hij
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some k =>
          exact hroot (lowerPathTailBlock N k)
  | some k =>
      cases j with
      | none =>
          exact (hroot (lowerPathTailBlock N k)).symm
      | some l =>
          have hkl : k ≠ l := by
            intro h
            exact hij (by simp [h])
          have hblock_ne :
              (lowerPathTailBlock N k).1 ≠ (lowerPathTailBlock N l).1 := by
            intro hblock
            apply hkl
            apply Fin.ext
            have hval := congrArg Fin.val hblock
            simp [lowerPathTailBlock, Fin.val_succ] at hval
            omega
          have hp : Nat.Prime (P (lowerPathTailBlock N k)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N k)).2).2.2
          have hq : Nat.Prime (P (lowerPathTailBlock N l)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerPathTailBlock N l)).2).2.2
          have hpq_ne : (P (lowerPathTailBlock N k)).1 ≠
              (P (lowerPathTailBlock N l)).1 := by
            intro hpq
            have hmem_l :
                (P (lowerPathTailBlock N k)).1 ∈
                  lowerPathPrimeInterval N (lowerPathTailBlock N l).1 := by
              simp [hpq, (P (lowerPathTailBlock N l)).2]
            exact Finset.disjoint_left.1
              (hdisj (lowerPathTailBlock N k).1 (lowerPathTailBlock N l).1 hblock_ne)
              (P (lowerPathTailBlock N k)).2 hmem_l
          exact (Nat.coprime_primes hp hq).2 hpq_ne

/-! ## CRT targets and residues -/

/-- Finite CRT in the integer `Int.ModEq` form used for path residue
assignments.  This local copy keeps the path scaffold independent of the old
`LowerConstruction.lean` file. -/
theorem lowerPath_int_modEq_crt_finset_exists {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (b : ι → ℤ)
    (hm : ∀ i ∈ s, m i ≠ 0)
    (hcop : Set.Pairwise (↑s : Set ι)
      (fun i j => Nat.Coprime (m i) (m j))) :
    ∃ a : ℤ, ∀ i ∈ s, a ≡ b i [ZMOD (m i : ℤ)] := by
  classical
  set aN : ι → ℕ := fun i => ((b i) % (m i : ℤ)).toNat with haN
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset aN m s hm hcop
  refine ⟨(k : ℤ), ?_⟩
  intro i hi
  have hm_ne : m i ≠ 0 := hm i hi
  have hm_int_ne : (m i : ℤ) ≠ 0 := by exact_mod_cast hm_ne
  have hmod_nonneg : 0 ≤ (b i) % (m i : ℤ) := Int.emod_nonneg _ hm_int_ne
  have h_aN_eq : (aN i : ℤ) = (b i) % (m i : ℤ) := by
    simp [haN, Int.toNat_of_nonneg hmod_nonneg]
  have hk_nat : k ≡ aN i [MOD m i] := hk i hi
  have hk_int : (k : ℤ) ≡ (aN i : ℤ) [ZMOD ((m i : ℕ) : ℤ)] :=
    Int.natCast_modEq_iff.mpr hk_nat
  have h_aN_modEq_b : (aN i : ℤ) ≡ b i [ZMOD (m i : ℤ)] := by
    rw [h_aN_eq]
    exact (Int.emod_emod_of_dvd (b i) dvd_rfl :
      (b i) % (m i : ℤ) % (m i : ℤ) = b i % (m i : ℤ))
  exact hk_int.trans h_aN_modEq_b

/-- Encode an element of a finite set into a natural residue below `m`,
assuming the set has at most `m` elements. -/
noncomputable def lowerPathFinsetCode (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) : ℕ :=
  (Fin.castLE h ((Finset.equivFin s) x)).1

lemma lowerPathFinsetCode_lt (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) :
    lowerPathFinsetCode s m h x < m :=
  (Fin.castLE h ((Finset.equivFin s) x)).2

lemma lowerPathFinsetCode_injective (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m) :
    Function.Injective (lowerPathFinsetCode s m h) := by
  intro x y hxy
  have hfin :
      Fin.castLE h ((Finset.equivFin s) x) =
        Fin.castLE h ((Finset.equivFin s) y) :=
    Fin.ext hxy
  exact (Finset.equivFin s).injective (Fin.castLE_injective h hfin)

lemma lowerPath_nat_eq_of_int_modEq_of_lt {m a b : ℕ}
    (ha : a < m) (hb : b < m)
    (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (m : ℤ)]) :
    a = b := by
  exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h) ha hb

/-- Capacity hypotheses needed by the source-aligned path CRT tree.  These are
the finite targets eventually supplied by prime-counting upper bounds and the
path scale separation. -/
structure LowerPathEncodingCapacity (N : ℕ) : Prop where
  root :
    ∀ hR : 0 < lowerPathR N,
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1).card ≤
        lowerPathP0 N
  next :
    ∀ k : Fin (lowerPathR N), ∀ hnext : k.1 + 1 < lowerPathR N,
      ∀ p : ℕ, p ∈ lowerPathPrimeInterval N (lowerPathTailBlock N k).1 →
        (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1).card ≤
          p
  root_coprime :
    ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
      p ∈ lowerPathPrimeInterval N i.1 →
        Nat.Coprime (lowerPathP0 N) p

lemma lowerPathEncodingCapacity_of_adjacent_card_le {N : ℕ}
    (hadj : ∀ i j : lowerPathIndex N, j.1 = i.1 + 1 →
      (lowerPathPrimeInterval N j).card ≤ Nat.floor (lowerPathY N i))
    (hrootcop : ∀ i : lowerPathTailIndex N, ∀ p : ℕ,
      p ∈ lowerPathPrimeInterval N i.1 →
        Nat.Coprime (lowerPathP0 N) p) :
    LowerPathEncodingCapacity N := by
  constructor
  · intro hR
    have hidx :
        ((lowerPathTailBlock N ⟨0, hR⟩).1).1 =
          (lowerPathZeroIndex N).1 + 1 := by
      simp [lowerPathTailBlock, lowerPathZeroIndex]
    have hcard := hadj (lowerPathZeroIndex N) (lowerPathTailBlock N ⟨0, hR⟩).1 hidx
    exact hcard.trans (by simp [lowerPathP0])
  · intro k hnext p hp
    have hidx :
        ((lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1).1 =
          ((lowerPathTailBlock N k).1).1 + 1 := by
      simp [lowerPathTailBlock, Fin.val_succ]
    have hcard := hadj (lowerPathTailBlock N k).1
      (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1 hidx
    have hp_floor :
        Nat.floor (lowerPathY N (lowerPathTailBlock N k).1) < p :=
      (mem_dyadicPrimeInterval.1 hp).1
    exact hcard.trans (Nat.le_of_lt hp_floor)
  · exact hrootcop

noncomputable def lowerPathRootCode (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) : ℕ :=
  if hR : 0 < lowerPathR N then
    lowerPathFinsetCode
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1)
      (lowerPathP0 N) (hcap.root hR) (P (lowerPathTailBlock N ⟨0, hR⟩))
  else
    0

noncomputable def lowerPathStepCode (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) (k : Fin (lowerPathR N)) : ℕ :=
  if hnext : k.1 + 1 < lowerPathR N then
    lowerPathFinsetCode
      (lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1)
      (P (lowerPathTailBlock N k)).1
      (hcap.next k hnext (P (lowerPathTailBlock N k)).1
        (P (lowerPathTailBlock N k)).2)
      (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
  else
    0

noncomputable def lowerPathCRTTarget (N : ℕ) (hcap : LowerPathEncodingCapacity N)
    (P : LowerPathPrimeChoice N) : lowerPathCRTIndex N → ℤ
  | none => lowerPathRootCode N hcap P
  | some k => lowerPathStepCode N hcap P k

noncomputable def lowerPathResidueForChoice {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (P : LowerPathPrimeChoice N) : ℤ :=
  Classical.choose (lowerPath_int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerPathCRTIndex N)))
    (m := lowerPathCRTModulus N P)
    (b := lowerPathCRTTarget N hcap P)
    (by intro i _hi; exact lowerPathCRTModulus_ne_zero N P i)
    (lowerPathCRTModuli_pairwise_coprime P
      (fun i => hcap.root_coprime i (P i).1 (P i).2) hdisj))

lemma lowerPathResidueForChoice_spec {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (P : LowerPathPrimeChoice N) (i : lowerPathCRTIndex N) :
    lowerPathResidueForChoice hcap hdisj P ≡
      lowerPathCRTTarget N hcap P i [ZMOD (lowerPathCRTModulus N P i : ℤ)] :=
  Classical.choose_spec (lowerPath_int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerPathCRTIndex N)))
    (m := lowerPathCRTModulus N P)
    (b := lowerPathCRTTarget N hcap P)
    (by intro i _hi; exact lowerPathCRTModulus_ne_zero N P i)
    (lowerPathCRTModuli_pairwise_coprime P
      (fun i => hcap.root_coprime i (P i).1 (P i).2) hdisj)) i (Finset.mem_univ i)

/-- A canonical preimage choice for a modulus in `lowerPathQ`. -/
lemma lowerPathChoiceOfQ_exists (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    ∃ P ∈ lowerPathChoices N, lowerPathModulus N P = q.1 := by
  have hq : q.1 ∈ lowerPathQ N := q.2
  change q.1 ∈ (lowerPathChoices N).image (lowerPathModulus N) at hq
  exact Finset.mem_image.1 hq

noncomputable def lowerPathChoiceOfQ (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    LowerPathPrimeChoice N :=
  Classical.choose (lowerPathChoiceOfQ_exists N q)

lemma lowerPathChoiceOfQ_mem (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    lowerPathChoiceOfQ N q ∈ lowerPathChoices N :=
  (Classical.choose_spec (lowerPathChoiceOfQ_exists N q)).1

lemma lowerPathChoiceOfQ_modulus (N : ℕ) (q : {q : ℕ // q ∈ lowerPathQ N}) :
    lowerPathModulus N (lowerPathChoiceOfQ N q) = q.1 :=
  (Classical.choose_spec (lowerPathChoiceOfQ_exists N q)).2

noncomputable def lowerPathResidueAssignment {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    ResidueAssignment (lowerPathQ N) :=
  fun q => lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)

lemma lowerPathResidueAssignment_modEq_target {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j))
    (q : {q : ℕ // q ∈ lowerPathQ N}) (i : lowerPathCRTIndex N) {n : ℤ}
    (hn : n ∈ residueClass q.1 (lowerPathResidueAssignment hcap hdisj q)) :
    n ≡ lowerPathCRTTarget N hcap (lowerPathChoiceOfQ N q) i
      [ZMOD (lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i : ℤ)] := by
  have hnq :
      n ≡ lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)
        [ZMOD (q.1 : ℤ)] := by
    simpa [residueClass, lowerPathResidueAssignment] using hn
  have hn_lower :
      n ≡ lowerPathResidueForChoice hcap hdisj (lowerPathChoiceOfQ N q)
        [ZMOD (lowerPathModulus N (lowerPathChoiceOfQ N q) : ℤ)] := by
    simpa [lowerPathChoiceOfQ_modulus N q] using hnq
  have hdivNat :
      lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i ∣
        lowerPathModulus N (lowerPathChoiceOfQ N q) :=
    lowerPathCRTModulus_dvd_lowerPathModulus N (lowerPathChoiceOfQ N q) i
  have hdivInt :
      (lowerPathCRTModulus N (lowerPathChoiceOfQ N q) i : ℤ) ∣
        (lowerPathModulus N (lowerPathChoiceOfQ N q) : ℤ) := by
    exact_mod_cast hdivNat
  exact (Int.ModEq.of_dvd hdivInt hn_lower).trans
    (lowerPathResidueForChoice_spec hcap hdisj (lowerPathChoiceOfQ N q) i)

lemma lowerPathRootCode_eq_of_modEq {N : ℕ} (hcap : LowerPathEncodingCapacity N)
    (P P' : LowerPathPrimeChoice N) (hR : 0 < lowerPathR N)
    (hmod : (lowerPathRootCode N hcap P : ℤ) ≡
      (lowerPathRootCode N hcap P' : ℤ) [ZMOD (lowerPathP0 N : ℤ)]) :
    P (lowerPathTailBlock N ⟨0, hR⟩) = P' (lowerPathTailBlock N ⟨0, hR⟩) := by
  let s := lowerPathPrimeInterval N (lowerPathTailBlock N ⟨0, hR⟩).1
  let m := lowerPathP0 N
  let hcard := hcap.root hR
  have hltP :
      lowerPathRootCode N hcap P < lowerPathP0 N := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard (P (lowerPathTailBlock N ⟨0, hR⟩))
  have hltP' :
      lowerPathRootCode N hcap P' < lowerPathP0 N := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard (P' (lowerPathTailBlock N ⟨0, hR⟩))
  have hcode_eq : lowerPathRootCode N hcap P = lowerPathRootCode N hcap P' :=
    lowerPath_nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      lowerPathFinsetCode s m hcard (P (lowerPathTailBlock N ⟨0, hR⟩)) =
        lowerPathFinsetCode s m hcard (P' (lowerPathTailBlock N ⟨0, hR⟩)) := by
    simpa [lowerPathRootCode, hR, s, m, hcard] using hcode_eq
  exact lowerPathFinsetCode_injective s m hcard hcode_eq'

lemma lowerPathStepCode_eq_of_modEq {N : ℕ} (hcap : LowerPathEncodingCapacity N)
    (P P' : LowerPathPrimeChoice N) (k : Fin (lowerPathR N))
    (hnext : k.1 + 1 < lowerPathR N)
    (hprev : P (lowerPathTailBlock N k) = P' (lowerPathTailBlock N k))
    (hmod : (lowerPathStepCode N hcap P k : ℤ) ≡
      (lowerPathStepCode N hcap P' k : ℤ)
        [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)]) :
    P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩) =
      P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩) := by
  let s := lowerPathPrimeInterval N (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩).1
  let m := (P (lowerPathTailBlock N k)).1
  let hcard :=
    hcap.next k hnext (P (lowerPathTailBlock N k)).1 (P (lowerPathTailBlock N k)).2
  have hltP :
      lowerPathStepCode N hcap P k < (P (lowerPathTailBlock N k)).1 := by
    simpa [lowerPathStepCode, hnext, s, m, hcard] using
      lowerPathFinsetCode_lt s m hcard
        (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
  have hltP' :
      lowerPathStepCode N hcap P' k < (P (lowerPathTailBlock N k)).1 := by
    have hcard' :=
      hcap.next k hnext (P' (lowerPathTailBlock N k)).1 (P' (lowerPathTailBlock N k)).2
    have hlt' :
        lowerPathStepCode N hcap P' k < (P' (lowerPathTailBlock N k)).1 := by
      simpa [lowerPathStepCode, hnext] using
        lowerPathFinsetCode_lt s (P' (lowerPathTailBlock N k)).1 hcard'
          (P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩))
    simpa [hprev] using hlt'
  have hcode_eq : lowerPathStepCode N hcap P k = lowerPathStepCode N hcap P' k :=
    lowerPath_nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      lowerPathFinsetCode s m hcard
          (P (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩)) =
        lowerPathFinsetCode s m hcard
          (P' (lowerPathTailBlock N ⟨k.1 + 1, hnext⟩)) := by
    simpa [lowerPathStepCode, hnext, s, m, hcard] using hcode_eq
  exact lowerPathFinsetCode_injective s m hcard hcode_eq'

lemma lowerPathResidueAssignment_pairwise_disjoint_of_capacity {N : ℕ}
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    PairwiseDisjointResidues (lowerPathQ N) (lowerPathResidueAssignment hcap hdisj) := by
  intro q r hqr
  rw [Set.disjoint_left]
  intro z hzq hzr
  let P := lowerPathChoiceOfQ N q
  let P' := lowerPathChoiceOfQ N r
  have hP_eq : P = P' := by
    by_cases hR : 0 < lowerPathR N
    · have hq0 := lowerPathResidueAssignment_modEq_target hcap hdisj q none hzq
      have hr0 := lowerPathResidueAssignment_modEq_target hcap hdisj r none hzr
      have hroot_mod :
          (lowerPathCRTTarget N hcap P none) ≡
            (lowerPathCRTTarget N hcap P' none)
              [ZMOD (lowerPathP0 N : ℤ)] := by
        simpa [P, P', lowerPathCRTModulus] using hq0.symm.trans hr0
      have hzero :
          P (lowerPathTailBlock N ⟨0, hR⟩) =
            P' (lowerPathTailBlock N ⟨0, hR⟩) := by
        exact lowerPathRootCode_eq_of_modEq hcap P P' hR
          (by simpa [lowerPathCRTTarget] using hroot_mod)
      have hall :
          ∀ n : ℕ, ∀ hn : n < lowerPathR N,
            P (lowerPathTailBlock N ⟨n, hn⟩) =
              P' (lowerPathTailBlock N ⟨n, hn⟩) := by
        intro n
        induction n with
        | zero =>
            intro hn
            simpa using hzero
        | succ n ih =>
            intro hn
            have hprev_lt : n < lowerPathR N := Nat.lt_of_succ_lt hn
            have hprev := ih hprev_lt
            let k : Fin (lowerPathR N) := ⟨n, hprev_lt⟩
            have hqk := lowerPathResidueAssignment_modEq_target hcap hdisj q (some k) hzq
            have hrk := lowerPathResidueAssignment_modEq_target hcap hdisj r (some k) hzr
            have hstep_mod :
                (lowerPathCRTTarget N hcap P (some k)) ≡
                  (lowerPathCRTTarget N hcap P' (some k))
                    [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)] := by
              have hrk' :
                  z ≡ lowerPathCRTTarget N hcap P' (some k)
                    [ZMOD ((P (lowerPathTailBlock N k)).1 : ℤ)] := by
                have hprev_val :
                    (lowerPathChoiceOfQ N r (lowerPathTailBlock N k)).1 =
                      (lowerPathChoiceOfQ N q (lowerPathTailBlock N k)).1 := by
                  dsimp [P, P'] at hprev
                  exact congrArg Subtype.val hprev.symm
                simpa [P, P', lowerPathCRTModulus, hprev_val] using hrk
              simpa [P, P', lowerPathCRTModulus] using hqk.symm.trans hrk'
            exact lowerPathStepCode_eq_of_modEq hcap P P' k hn hprev
              (by simpa [lowerPathCRTTarget] using hstep_mod)
      exact lowerPathTailBlock_ext (fun k => hall k.1 k.2)
    · apply lowerPathTailBlock_ext
      intro k
      have hk : k.1 < lowerPathR N := k.2
      exact False.elim (hR (lt_of_le_of_lt (Nat.zero_le k.1) hk))
  have hqval : q.1 = r.1 := by
    calc
      q.1 = lowerPathModulus N P := (lowerPathChoiceOfQ_modulus N q).symm
      _ = lowerPathModulus N P' := by rw [hP_eq]
      _ = r.1 := lowerPathChoiceOfQ_modulus N r
  exact hqr (Subtype.ext hqval)

/-- Finite admissibility package for the source-aligned path family.  The
remaining work before this can replace the old lower construction is to prove
the hypotheses eventually from the path scale algebra and prime-counting
estimates. -/
theorem lowerPathQ_admissible_of_capacity {N : ℕ}
    (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerPathY N (lowerPathZeroIndex N))
    (hcap : LowerPathEncodingCapacity N)
    (hdisj : ∀ i j : lowerPathIndex N, i ≠ j →
      Disjoint (lowerPathPrimeInterval N i) (lowerPathPrimeInterval N j)) :
    Admissible N (lowerPathQ N) := by
  constructor
  · exact lowerPathQ_moduli_in_range_of_root_scale hNpos hY0
  · exact ⟨lowerPathResidueAssignment hcap hdisj,
      lowerPathResidueAssignment_pairwise_disjoint_of_capacity hcap hdisj⟩

theorem lowerPathQ_admissible_eventually_of_capacity :
    ∀ᶠ N : ℕ in atTop,
      LowerPathEncodingCapacity N → Admissible N (lowerPathQ N) := by
  filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_lowerPathY_zero_ge_one,
      lowerPathPrimeIntervals_pairwise_disjoint] with N hNpos_nat hY0 hdisj hcap
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  exact lowerPathQ_admissible_of_capacity hNpos hY0 hcap hdisj

theorem lowerPathEncodingCapacity_eventually :
    ∀ᶠ N : ℕ in atTop, LowerPathEncodingCapacity N := by
  filter_upwards [lowerPathPrimeInterval_adjacent_card_le_floor_prev_eventually,
      lowerPath_root_coprime_tail_prime_eventually] with N hadj hrootcop
  exact lowerPathEncodingCapacity_of_adjacent_card_le hadj hrootcop

theorem lowerPathQ_admissible_eventually :
    ∀ᶠ N : ℕ in atTop, Admissible N (lowerPathQ N) := by
  filter_upwards [lowerPathQ_admissible_eventually_of_capacity,
      lowerPathEncodingCapacity_eventually] with N hadm hcap
  exact hadm hcap

/-! ## From the source-aligned path family to lower-bound input -/

lemma lowerPath_admissible_mono {N : ℕ} {Q Q' : Finset ℕ}
    (hQ : Admissible N Q) (hsub : Q' ⊆ Q) :
    Admissible N Q' := by
  constructor
  · intro q hq
    exact hQ.1 q (hsub hq)
  · rcases hQ.2 with ⟨a, ha⟩
    exact ⟨restrictAssignment a hsub, PairwiseDisjointResidues.mono ha hsub⟩

lemma lowerPath_possibleCard_of_admissible_card_le {N r : ℕ} {Q : Finset ℕ}
    (hQ : Admissible N Q) (hr : r ≤ Q.card) :
    PossibleCard N r := by
  classical
  rcases Finset.exists_subset_card_eq (s := Q) hr with ⟨Q', hsub, hcard⟩
  exact ⟨Q', lowerPath_admissible_mono hQ hsub, hcard⟩

theorem lowerPath_possibleCard_eventually_of_floor_product
    (ε : ℝ)
    (hfloor :
      ∀ᶠ N : ℕ in atTop,
        Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
          lowerPathPrimeFloorProduct lowerPathChebEta N) :
    ∀ᶠ N : ℕ in atTop,
      PossibleCard N (Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N)) := by
  filter_upwards [lowerPathQ_admissible_eventually,
      lowerPathQ_card_ge_prime_floor_product_eventually,
      hfloor] with N hadm hfloor_le_Q htarget_le_floor
  exact lowerPath_possibleCard_of_admissible_card_le hadm
    (htarget_le_floor.trans hfloor_le_Q)

theorem lowerPath_floor_product_lower_bound_eventually_of_real_product
    (ε : ℝ)
    (hreal :
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N) :
    ∀ᶠ N : ℕ in atTop,
      Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
        lowerPathPrimeFloorProduct lowerPathChebEta N := by
  filter_upwards [hreal, lowerPathPrimeFloorProduct_floor_loss_eventually] with
    N htarget hfloor
  exact Nat.ceil_le.2 (htarget.trans hfloor)

theorem lowerPath_real_product_lower_bound_eventually_of_denominator_bound
    (ε : ℝ) (_hε : 0 < ε)
    (hden :
      ∀ᶠ N : ℕ in atTop,
        lowerPathRealDenominator N ≤ Lscale (1 + ε) N) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N := by
  filter_upwards [Filter.eventually_gt_atTop 0,
      eventually_lowerPathLogGap_gt_log_two,
      eventually_lowerPathY_zero_ge 64,
      hden] with N hNpos_nat hgap hY0 hden_le
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hNnonneg : 0 ≤ (N : ℝ) := hNpos.le
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
  have hlog_pos : ∀ i : lowerPathTailIndex N,
      0 < Real.log (lowerPathY N i.1) := by
    intro i
    have hzero_le_i :
        lowerPathY N (lowerPathZeroIndex N) ≤ lowerPathY N i.1 :=
      lowerPathY_le_of_index_le hgap_nonneg (by simp [lowerPathZeroIndex])
    have hY0' : (64 : ℝ) ≤ lowerPathY N (lowerPathZeroIndex N) := by
      simpa [lowerPathZeroIndex] using hY0
    exact Real.log_pos (by linarith [hY0'.trans hzero_le_i])
  have hden_pos : 0 < lowerPathRealDenominator N :=
    lowerPathRealDenominator_pos hlog_pos
  have hid :
      lowerPathRealPrimeProduct N * lowerPathRealDenominator N = (N : ℝ) :=
    lowerPathRealPrimeProduct_mul_denominator_eq hNpos
      (fun i => (hlog_pos i).ne')
  have hleft_mul :
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N ≤
        (N : ℝ) := by
    calc
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N
          ≤ ((N : ℝ) * Lscale (-(1 + ε)) N) * Lscale (1 + ε) N := by
            exact mul_le_mul_of_nonneg_left hden_le
              (mul_nonneg hNnonneg (Lscale_nonneg _ _))
      _ = (N : ℝ) * (Lscale (-(1 + ε)) N * Lscale (1 + ε) N) := by ring
      _ = (N : ℝ) := by
            rw [Lscale_neg_mul]
            ring
  have hmul :
      ((N : ℝ) * Lscale (-(1 + ε)) N) * lowerPathRealDenominator N ≤
        lowerPathRealPrimeProduct N * lowerPathRealDenominator N := by
    simpa [hid] using hleft_mul
  exact le_of_mul_le_mul_right hmul hden_pos

theorem lowerPath_denominator_bound_eventually_of_simple_bound
    (ε : ℝ)
    (hsimple :
      ∀ᶠ N : ℕ in atTop,
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
              Lscale (1 + ε) N) :
    ∀ᶠ N : ℕ in atTop,
      lowerPathRealDenominator N ≤ Lscale (1 + ε) N := by
  filter_upwards [lowerPathRealDenominator_le_simple_eventually,
      hsimple] with N hden_simple hsimple_N
  exact hden_simple.trans hsimple_N

lemma eventually_log_const_mul_Zscale_le
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (C * Zscale N) ≤
        ((1 + δ) / 2) * Real.log (Real.log (N : ℝ)) := by
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_const_mul_sqrt_loglog_le_mul_loglog C (δ / 2) hC hδ2,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with
    N hNlarge_nat hlog_extra hYge_one
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set Y := Real.log (Real.log (N : ℝ))
  have hY_pos : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using hYge_one)
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hZeq := Zscale_eq_exp_half_loglog_mul_sqrt_loglog hNlarge
  calc
    Real.log (C * Zscale N)
        = Real.log (Real.exp (Y / 2) * (C * Real.sqrt Y)) := by
            congr 1
            rw [hZeq]
            ring
    _ = Y / 2 + Real.log (C * Real.sqrt Y) := by
            rw [Real.log_mul (Real.exp_ne_zero _)
              (mul_pos hC hsqrt_pos).ne', Real.log_exp]
    _ ≤ Y / 2 + (δ / 2) * Y := by
            have hlog_extraY :
                Real.log (C * Real.sqrt Y) ≤ (δ / 2) * Y := by
              simpa [Y] using hlog_extra
            nlinarith
    _ = ((1 + δ) / 2) * Y := by ring

lemma eventually_lowerPathR_mul_log_constZ_le_mul_Zscale
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (lowerPathR N : ℝ) * Real.log (C * Zscale N) ≤
        (1 + δ) * Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_const_mul_Zscale_le C δ hC hδ,
      eventually_Zscale_ge_const_path (1 / C)] with N hNlarge_nat hlog_le hZge
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hY_nonneg : 0 ≤ Y := by
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    have hlog_gt_one : 1 < Real.log (N : ℝ) :=
      (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
    exact (Real.log_pos hlog_gt_one).le
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hr_le : (lowerPathR N : ℝ) ≤ 2 * M := by
    dsimp [lowerPathR, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hbase_ge_one : 1 ≤ C * Zscale N := by
    have hmul := mul_le_mul_of_nonneg_left hZge hC.le
    have hone : (1 : ℝ) = C * (1 / C) := by
      field_simp [hC.ne']
    nlinarith
  have hlog_nonneg : 0 ≤ Real.log (C * Zscale N) :=
    Real.log_nonneg hbase_ge_one
  calc
    (lowerPathR N : ℝ) * Real.log (C * Zscale N)
        ≤ (2 * M) * Real.log (C * Zscale N) := by
            exact mul_le_mul_of_nonneg_right hr_le hlog_nonneg
    _ ≤ (2 * M) * (((1 + δ) / 2) * Y) := by
            exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = (1 + δ) * (M * Y) := by ring
    _ = (1 + δ) * Zscale N := by rw [hMY]

theorem lowerPath_simple_denominator_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
            Lscale (1 + ε) N := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Zscale_ge_const_path (3 * Real.log 2 / ε),
      eventually_lowerPathLogScale_zero_le_mul_Zscale (ε / 3) hε3,
      eventually_lowerPathR_mul_log_constZ_le_mul_Zscale
        lowerPathDenominatorConstant (ε / 3)
        lowerPathDenominatorConstant_pos hε3,
      eventually_Zscale_pos] with N hNlarge_nat hZconst hroot hmain hZpos
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hbase_pos : 0 < lowerPathDenominatorConstant * Zscale N :=
    mul_pos lowerPathDenominatorConstant_pos hZpos
  have hpow :
      (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N =
        Real.exp ((lowerPathR N : ℝ) *
          Real.log (lowerPathDenominatorConstant * Zscale N)) := by
    calc
      (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N
          = (Real.exp (Real.log
              (lowerPathDenominatorConstant * Zscale N))) ^ lowerPathR N := by
              rw [Real.exp_log hbase_pos]
      _ = Real.exp ((lowerPathR N : ℝ) *
          Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [← Real.exp_nat_mul]
  have hprod_eq :
      (2 * lowerPathY N (lowerPathZeroIndex N)) *
          (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N =
        Real.exp
          (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
            (lowerPathR N : ℝ) *
              Real.log (lowerPathDenominatorConstant * Zscale N)) := by
    rw [lowerPathY, hpow]
    calc
      (2 * Real.exp (lowerPathLogScale N (lowerPathZeroIndex N))) *
          Real.exp ((lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N))
          = Real.exp (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N)) *
              Real.exp ((lowerPathR N : ℝ) *
                Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp
          (Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
            (lowerPathR N : ℝ) *
              Real.log (lowerPathDenominatorConstant * Zscale N)) := by
              rw [← Real.exp_add]
  have hconst : Real.log 2 ≤ (ε / 3) * Zscale N := by
    have hmul := mul_le_mul_of_nonneg_left hZconst hε.le
    have hthree :
        3 * Real.log 2 ≤ ε * Zscale N := by
      calc
        3 * Real.log 2 = ε * (3 * Real.log 2 / ε) := by
            field_simp [hε.ne']
        _ ≤ ε * Zscale N := hmul
    nlinarith
  have hexponent :
      Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
          (lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N) ≤
        (1 + ε) * Zscale N := by
    have hroot_zero :
        lowerPathLogScale N (lowerPathZeroIndex N) ≤ (ε / 3) * Zscale N := by
      simpa [lowerPathZeroIndex] using hroot
    calc
      Real.log 2 + lowerPathLogScale N (lowerPathZeroIndex N) +
          (lowerPathR N : ℝ) *
            Real.log (lowerPathDenominatorConstant * Zscale N)
          ≤ (ε / 3) * Zscale N + (ε / 3) * Zscale N +
              (1 + ε / 3) * Zscale N := by
              nlinarith [hconst, hroot_zero, hmain]
      _ = (1 + ε) * Zscale N := by ring
  rw [hprod_eq, Lscale]
  exact Real.exp_le_exp.2 hexponent

theorem lowerPath_f_lower_bound_eventually_of_floor_product
    (hfloor :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤
          lowerPathPrimeFloorProduct lowerPathChebEta N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  intro ε hε
  filter_upwards [
      lowerPath_possibleCard_eventually_of_floor_product
        ε (hfloor ε hε)] with N hPossible
  have hceil_le_f :
      Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) ≤ f N :=
    le_f_of_possibleCard hPossible
  have htarget_le_ceil :
      (N : ℝ) * Lscale (-(1 + ε)) N ≤
        (Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N) : ℝ) :=
    Nat.le_ceil ((N : ℝ) * Lscale (-(1 + ε)) N)
  exact htarget_le_ceil.trans (by exact_mod_cast hceil_le_f)

theorem lowerPath_f_lower_bound_eventually_of_real_product
    (hreal :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (N : ℝ) * Lscale (-(1 + ε)) N ≤ lowerPathRealPrimeProduct N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_floor_product
    (fun ε hε => lowerPath_floor_product_lower_bound_eventually_of_real_product
      ε (hreal ε hε))

theorem lowerPath_f_lower_bound_eventually_of_denominator_bound
    (hden :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        lowerPathRealDenominator N ≤ Lscale (1 + ε) N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_real_product
    (fun ε hε => lowerPath_real_product_lower_bound_eventually_of_denominator_bound
      ε hε (hden ε hε))

theorem lowerPath_f_lower_bound_eventually_of_simple_bound
    (hsimple :
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (2 * lowerPathY N (lowerPathZeroIndex N)) *
            (lowerPathDenominatorConstant * Zscale N) ^ lowerPathR N ≤
              Lscale (1 + ε) N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  exact lowerPath_f_lower_bound_eventually_of_denominator_bound
    (fun ε hε => lowerPath_denominator_bound_eventually_of_simple_bound
      ε (hsimple ε hε))

theorem lowerPath_f_lower_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) :=
  lowerPath_f_lower_bound_eventually_of_simple_bound
    lowerPath_simple_denominator_bound_eventually

end Erdos202
