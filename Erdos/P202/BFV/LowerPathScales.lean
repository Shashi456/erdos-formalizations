/-
Erdos Problem 202 -- BFV lower construction, source-aligned path scales.

This file is a non-consuming scaffold for replacing the current fixed-root
lower construction in `LowerConstruction.lean`.  The key point is the BFV
source scale:

* roughly `2 * M(N)` prime blocks;
* logarithmic gap about `(1 / 2) * log log N - sqrt (log log N)`;
* exact normalization `prod_i (2 * Y_i) = N`.

The existing rooted construction fixes a whole root block and is too small for
the lower-bound target.  These path scales are the product/capacity side of the
BFV Section 2 construction, isolated so the later refactor can proceed without
destabilizing the current proof path.
-/

import Mathlib
import Erdos.P202.P202Basic

namespace Erdos202

open Filter Finset
open Asymptotics
open scoped BigOperators

/-! ## Source-aligned path parameters -/

/-- BFV path depth, approximately `2 * M(N)`. -/
noncomputable def lowerPathR (N : ℕ) : ℕ :=
  Nat.floor (2 * Mscale N)

/-- Path block indices `{0, ..., lowerPathR N}`. -/
abbrev lowerPathIndex (N : ℕ) : Type :=
  Fin (lowerPathR N + 1)

/-- Source-aligned logarithmic gap between consecutive prime blocks.

Eventually this is larger than `log 2`, so dyadic intervals are disjoint; it
is also small enough relative to the block logarithms to support the BFV
encoding inequality `|block_{i+1}| <= p_i`. -/
noncomputable def lowerPathLogGap (N : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) -
    Real.sqrt (Real.log (Real.log (N : ℝ)))

/-- Product-normalized initial log scale. -/
noncomputable def lowerPathLogBase (N : ℕ) : ℝ :=
  (Real.log (N : ℝ) - ((lowerPathR N : ℝ) + 1) * Real.log 2 -
      lowerPathLogGap N * ((lowerPathR N : ℝ) * ((lowerPathR N : ℝ) + 1) / 2)) /
    ((lowerPathR N : ℝ) + 1)

/-- Logarithmic scale of the `i`th source-aligned path block. -/
noncomputable def lowerPathLogScale (N : ℕ) (i : lowerPathIndex N) : ℝ :=
  lowerPathLogBase N + (i.1 : ℝ) * lowerPathLogGap N

/-- Real prime scale of the `i`th source-aligned path block. -/
noncomputable def lowerPathY (N : ℕ) (i : lowerPathIndex N) : ℝ :=
  Real.exp (lowerPathLogScale N i)

lemma lowerPathLogScale_sub (N : ℕ) (i j : lowerPathIndex N) :
    lowerPathLogScale N i - lowerPathLogScale N j =
      ((i.1 : ℝ) - (j.1 : ℝ)) * lowerPathLogGap N := by
  simp [lowerPathLogScale]
  ring

lemma lowerPathIndex_sum_val (N : ℕ) :
    (∑ i : lowerPathIndex N, (i.1 : ℝ)) =
      (lowerPathR N : ℝ) * ((lowerPathR N : ℝ) + 1) / 2 := by
  let r := lowerPathR N
  change (∑ i : Fin (r + 1), (i.1 : ℝ)) = (r : ℝ) * ((r : ℝ) + 1) / 2
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ x ∈ Finset.range (r + 1), if h : x < r + 1 then (x : ℝ) else 0)
        = ∑ x ∈ Finset.range (r + 1), (x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.mem_range.mp hx]
    _ = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
          have hnat : (∑ i ∈ Finset.range (r + 1), i) * 2 = (r + 1) * r := by
            simpa using Finset.sum_range_id_mul_two (r + 1)
          have hreal :
              ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2 =
                ((r + 1) * r : ℕ) := by
            exact_mod_cast hnat
          rw [← Nat.cast_sum]
          calc
            ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ)
                = (((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2) / 2 := by
                    ring
            _ = (((r + 1) * r : ℕ) : ℝ) / 2 := by rw [hreal]
            _ = (r : ℝ) * ((r : ℝ) + 1) / 2 := by
                    norm_num
                    ring

lemma lowerPathLogScale_sum (N : ℕ) :
    (∑ i : lowerPathIndex N, lowerPathLogScale N i) =
      Real.log (N : ℝ) - ((lowerPathR N : ℝ) + 1) * Real.log 2 := by
  have hcard : ((Finset.univ : Finset (lowerPathIndex N)).card : ℝ) =
      (lowerPathR N : ℝ) + 1 := by
    simp [lowerPathIndex]
  have hsum := lowerPathIndex_sum_val N
  simp [lowerPathLogScale, lowerPathLogBase]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
  rw [hsum, hcard]
  have hden : (lowerPathR N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The source-aligned scales are normalized at the dyadic upper endpoints:
`prod_i (2 * Y_i) = N`. -/
lemma lowerPathY_dyadic_product_eq {N : ℕ} (hNpos : 0 < (N : ℝ)) :
    (∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i) = (N : ℝ) := by
  calc
    (∏ i : lowerPathIndex N, (2 : ℝ) * lowerPathY N i)
        = ∏ i : lowerPathIndex N,
            Real.exp (Real.log 2 + lowerPathLogScale N i) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [lowerPathY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (∑ i : lowerPathIndex N,
            (Real.log 2 + lowerPathLogScale N i)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (Real.log (N : ℝ)) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            lowerPathLogScale_sum]
          have hcard : ((Finset.univ : Finset (lowerPathIndex N)).card : ℝ) =
              (lowerPathR N : ℝ) + 1 := by
            simp [lowerPathIndex]
          rw [hcard]
          ring
    _ = (N : ℝ) := Real.exp_log hNpos

lemma eventually_lowerPathLogGap_gt_log_two :
    ∀ᶠ N : ℕ in atTop, Real.log 2 < lowerPathLogGap N := by
  filter_upwards [eventually_sqrt_loglog_ge 4,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 0] with N hsqrt hloglog_nonneg
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg Y
  have hY_eq : Y = s ^ 2 := by
    calc
      Y = Real.sqrt Y * Real.sqrt Y := by
            rw [Real.mul_self_sqrt hloglog_nonneg]
      _ = s ^ 2 := by
            simp [s, sq]
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hmain : Real.log 2 < (1 / 2 : ℝ) * Y - s := by
    rw [hY_eq]
    nlinarith
  simpa [lowerPathLogGap, Y, s] using hmain

lemma lowerPathY_dyadic_lt_of_lt_index {N : ℕ} {i j : lowerPathIndex N}
    (hgap : Real.log 2 < lowerPathLogGap N) (hij : i.1 < j.1) :
    2 * lowerPathY N i < lowerPathY N j := by
  have hsucc : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.2 hij
  have hdiff_real : 1 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
    have hsuccR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hsucc
    linarith
  have hgap_pos : 0 < lowerPathLogGap N :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hgap
  have hmain :
      Real.log 2 + lowerPathLogScale N i < lowerPathLogScale N j := by
    have hsub := lowerPathLogScale_sub N j i
    have hmul : Real.log 2 < ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
      calc
        Real.log 2 < lowerPathLogGap N := hgap
        _ ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
          nlinarith
    nlinarith
  calc
    2 * lowerPathY N i
        = Real.exp (Real.log 2 + lowerPathLogScale N i) := by
            rw [lowerPathY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ < Real.exp (lowerPathLogScale N j) := Real.exp_lt_exp.2 hmain
    _ = lowerPathY N j := by rw [lowerPathY]

lemma lowerPathLogScale_le_of_index_le {N : ℕ} {i j : lowerPathIndex N}
    (hgap_nonneg : 0 ≤ lowerPathLogGap N) (hij : i.1 ≤ j.1) :
    lowerPathLogScale N i ≤ lowerPathLogScale N j := by
  have hsub := lowerPathLogScale_sub N j i
  have hdiff_nonneg : 0 ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerPathLogGap N := by
    have hidx : 0 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
      exact sub_nonneg.2 (by exact_mod_cast hij)
    exact mul_nonneg hidx hgap_nonneg
  nlinarith

lemma lowerPathY_le_of_index_le {N : ℕ} {i j : lowerPathIndex N}
    (hgap_nonneg : 0 ≤ lowerPathLogGap N) (hij : i.1 ≤ j.1) :
    lowerPathY N i ≤ lowerPathY N j :=
  Real.exp_le_exp.2 (lowerPathLogScale_le_of_index_le hgap_nonneg hij)

lemma lowerPathY_adjacent_eq_mul_exp_gap {N : ℕ} {i j : lowerPathIndex N}
    (hij : j.1 = i.1 + 1) :
    lowerPathY N j = lowerPathY N i * Real.exp (lowerPathLogGap N) := by
  have hsub := lowerPathLogScale_sub N j i
  have hscale : lowerPathLogScale N j = lowerPathLogScale N i + lowerPathLogGap N := by
    have hdiff : ((j.1 : ℝ) - (i.1 : ℝ)) = 1 := by
      rw [hij]
      norm_num
    rw [hdiff, one_mul] at hsub
    linarith
  rw [lowerPathY, lowerPathY, hscale, Real.exp_add]

/-! ## Startup scale estimates -/

lemma eventually_loglog_cubed_le_log :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) ^ 3 ≤ Real.log (N : ℝ) := by
  have hsmall_real :
      (fun x : ℝ => Real.log x ^ 3) =o[atTop] fun x : ℝ => x :=
    Real.isLittleO_pow_log_id_atTop
  have hlog_atTop :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 3) =o[atTop]
        fun N : ℕ => Real.log (N : ℝ) :=
    hsmall_real.comp_tendsto hlog_atTop
  filter_upwards [isLittleO_iff.mp hsmall zero_lt_one,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsmallN hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hleft_norm :
      ‖Real.log (Real.log (N : ℝ)) ^ 3‖ =
        Real.log (Real.log (N : ℝ)) ^ 3 := by
    rw [Real.norm_of_nonneg]
    positivity
  have hright_norm : ‖Real.log (N : ℝ)‖ = Real.log (N : ℝ) := by
    rw [Real.norm_of_nonneg hlog_pos.le]
  simpa [hleft_norm, hright_norm] using hsmallN

lemma eventually_loglog_le_Mscale :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) ≤ Mscale N := by
  filter_upwards [eventually_loglog_cubed_le_log,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hcube hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hquot_nonneg :
      0 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
    div_nonneg hlog_pos.le hloglog_pos.le
  rw [Mscale]
  refine (Real.le_sqrt hloglog_pos.le hquot_nonneg).2 ?_
  rw [sq]
  exact (le_div_iff₀ hloglog_pos).2 (by
    simpa [pow_succ, pow_two, mul_assoc] using hcube)

lemma lowerPathLogScale_zero_eq (N : ℕ) :
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ =
      Real.log (N : ℝ) / ((lowerPathR N : ℝ) + 1) -
        Real.log 2 - lowerPathLogGap N * (lowerPathR N : ℝ) / 2 := by
  have hden : (lowerPathR N : ℝ) + 1 ≠ 0 := by positivity
  simp [lowerPathLogScale, lowerPathLogBase]
  field_simp [hden]

lemma lowerPathLogScale_zero_nonneg_of_loglog_le_Mscale {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    0 ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hloglog_ge
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hM_ge_one : 1 ≤ M := by
    have : (1 : ℝ) ≤ Y := by linarith
    exact this.trans hY_le_M
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hden_pos : 0 < r + 1 := by positivity
  have hden_le : r + 1 ≤ 2 * M + 1 := by linarith
  have htwoM1_pos : 0 < 2 * M + 1 := by positivity
  have hMll : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMll]
    ring
  have hdiv_ge :
      M ^ 2 * Y / (2 * M + 1) ≤ Real.log (N : ℝ) / (r + 1) := by
    rw [hlog_eq]
    exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    rw [hgap_eq]
    nlinarith [hs_sq]
  have hgap_le : lowerPathLogGap N ≤ Y / 2 - s := by
    rw [hgap_eq]
  have hgap_r_le :
      lowerPathLogGap N * r / 2 ≤ M * (Y / 2 - s) := by
    rw [hgap_eq]
    have hgap0 : 0 ≤ Y / 2 - s := by
      nlinarith [hs_sq]
    nlinarith
  have hfrac_le_M :
      M * Y / (2 * (2 * M + 1)) ≤ M := by
    have hden2_pos : 0 < 2 * (2 * M + 1) := by positivity
    rw [div_le_iff₀ hden2_pos]
    nlinarith
  have hcore :
      1 ≤ M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) := by
    have hrewrite :
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) =
          M * s - M * Y / (2 * (2 * M + 1)) := by
      field_simp [htwoM1_pos.ne']
      ring
    rw [hrewrite]
    calc
      (1 : ℝ) ≤ M := hM_ge_one
      _ ≤ M * s - M * Y / (2 * (2 * M + 1)) := by
            have hMs_ge_twoM : 2 * M ≤ M * s := by nlinarith
            nlinarith
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  rw [lowerPathLogScale_zero_eq]
  calc
    0 ≤
        (M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s)) - Real.log 2 := by
          linarith
    _ ≤ Real.log (N : ℝ) / (r + 1) - Real.log 2 -
        lowerPathLogGap N * r / 2 := by
          nlinarith

lemma lowerPathLogScale_zero_ge_half_M_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 ≤
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hloglog_ge
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Mscale_nonneg N
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hden_pos : 0 < r + 1 := by positivity
  have hden_le : r + 1 ≤ 2 * M + 1 := by linarith
  have htwoM1_pos : 0 < 2 * M + 1 := by positivity
  have hMll : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMll]
    ring
  have hdiv_ge :
      M ^ 2 * Y / (2 * M + 1) ≤ Real.log (N : ℝ) / (r + 1) := by
    rw [hlog_eq]
    exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_r_le :
      lowerPathLogGap N * r / 2 ≤ M * (Y / 2 - s) := by
    rw [hgap_eq]
    have hgap0 : 0 ≤ Y / 2 - s := by
      nlinarith [hs_sq]
    nlinarith
  have hcore :
      M * s / 2 + Real.log 2 ≤
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) := by
    have hrewrite :
        M ^ 2 * Y / (2 * M + 1) - M * (Y / 2 - s) =
          M * s - M * Y / (2 * (2 * M + 1)) := by
      field_simp [htwoM1_pos.ne']
      ring
    rw [hrewrite]
    have hfrac_le_M :
        M * Y / (2 * (2 * M + 1)) ≤ M := by
      have hden2_pos : 0 < 2 * (2 * M + 1) := by positivity
      rw [div_le_iff₀ hden2_pos]
      nlinarith
    have hlog_two_le_one : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hM_ge_one : 1 ≤ M := by
      have hY_ge_one : (1 : ℝ) ≤ Y := by linarith
      exact hY_ge_one.trans hY_le_M
    have hMs_big : M + M * s / 2 + 1 ≤ M * s := by
      nlinarith
    nlinarith
  rw [lowerPathLogScale_zero_eq]
  dsimp [M, Y, s, r] at hcore hdiv_ge hgap_r_le ⊢
  nlinarith

lemma Mscale_mul_sqrt_loglog_eq_exp_half_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ)) :
    Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) =
      Real.exp (Real.log (Real.log (N : ℝ)) / 2) := by
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hleft_nonneg :
      0 ≤ Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    exact mul_nonneg (Mscale_nonneg N) (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ Real.exp (Y / 2) := (Real.exp_pos _).le
  have hsq_left :
      (Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 =
        Real.log (N : ℝ) := by
    have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
    have hMZ := Mscale_mul_Zscale_eq_log hNlarge
    have hsqrt_sq :
        Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 =
          Real.log (Real.log (N : ℝ)) :=
      Real.sq_sqrt (by simpa [Y] using hY_nonneg)
    calc
      (Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2
          = Mscale N ^ 2 * Real.log (Real.log (N : ℝ)) := by
              rw [mul_pow, hsqrt_sq]
      _ = Mscale N * (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
      _ = Mscale N * Zscale N := by rw [hMll]
      _ = Real.log (N : ℝ) := hMZ
  have hsq_right :
      (Real.exp (Y / 2)) ^ 2 = Real.log (N : ℝ) := by
    calc
      (Real.exp (Y / 2)) ^ 2 = Real.exp Y := by
        rw [sq, ← Real.exp_add]
        ring_nf
      _ = Real.log (N : ℝ) := by
        dsimp [Y]
        rw [Real.exp_log hlog_pos]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (hsq_left.trans hsq_right.symm) |>.elim
    (fun h => h)
    (fun h => by nlinarith)

lemma eventually_lowerPath_adjacent_ratio_le_logscale_zero (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.exp (lowerPathLogGap N) ≤
        lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  let A : ℝ := max (2 * |C|) 1
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop (Real.log A),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hs hloglog hloglog_le_M
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC_le_A_half : C ≤ A / 2 := by
    have h : 2 * C ≤ 2 * |C| := by nlinarith [le_abs_self C]
    have hA : 2 * |C| ≤ A := le_max_left _ _
    linarith
  have hA_le_exp_s : A ≤ Real.exp s := by
    exact (Real.log_le_iff_le_exp hA_pos).1 (by simpa [s, Y] using hs)
  have hCexp_neg_le_half : C * Real.exp (-s) ≤ 1 / 2 := by
    have hC_le_exp_half : C ≤ Real.exp s / 2 := hC_le_A_half.trans (by linarith)
    have hexp_pos : 0 < Real.exp s := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hC_le_exp_half (Real.exp_pos (-s)).le
    have hcancel : Real.exp s / 2 * Real.exp (-s) = (1 : ℝ) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      simp
    linarith
  have hMs_eq := Mscale_mul_sqrt_loglog_eq_exp_half_loglog hNlarge
  have hscale_lower :=
    lowerPathLogScale_zero_ge_half_M_mul_sqrt_loglog hNlarge hloglog hloglog_le_M
  have hgap_eq :
      lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have htarget :
      C * Real.exp (lowerPathLogGap N) ≤
        Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 := by
    rw [hgap_eq]
    calc
      C * Real.exp (Y / 2 - s)
          = C * Real.exp (-s) * Real.exp (Y / 2) := by
              rw [show Y / 2 - s = -s + Y / 2 by ring, Real.exp_add]
              ring
      _ ≤ (1 / 2) * Real.exp (Y / 2) := by
              exact mul_le_mul_of_nonneg_right hCexp_neg_le_half (Real.exp_pos _).le
      _ = Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) / 2 := by
              rw [hMs_eq]
              simp [Y]
              ring
  exact htarget.trans hscale_lower

lemma eventually_lowerPathY_zero_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ lowerPathY N ⟨0, Nat.succ_pos _⟩ := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hloglog hloglog_le_M
  rw [lowerPathY, Real.one_le_exp_iff]
  exact lowerPathLogScale_zero_nonneg_of_loglog_le_Mscale
    (lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat))
    hloglog hloglog_le_M

lemma eventually_lowerPathLogScale_zero_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      A ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := by
  by_cases hA : A ≤ 0
  · filter_upwards [eventually_lowerPathY_zero_ge_one] with N hY
    rw [lowerPathY, Real.one_le_exp_iff] at hY
    exact hA.trans hY
  · have hApos : 0 < A := lt_of_not_ge hA
    filter_upwards [eventually_lowerPath_adjacent_ratio_le_logscale_zero A,
        eventually_lowerPathLogGap_gt_log_two] with N hscale hgap
    have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
      exact (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hgap.le
    have hexp_ge_one : 1 ≤ Real.exp (lowerPathLogGap N) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 hgap_nonneg
    calc
      A ≤ A * Real.exp (lowerPathLogGap N) := by
            exact le_mul_of_one_le_right hApos.le hexp_ge_one
      _ ≤ lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ := hscale

lemma eventually_lowerPathY_zero_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ lowerPathY N ⟨0, Nat.succ_pos _⟩ := by
  by_cases hA : 0 < A
  · filter_upwards [eventually_lowerPathLogScale_zero_ge (Real.log A)] with N hscale
    rw [lowerPathY]
    exact (Real.log_le_iff_le_exp hA).1 hscale
  · exact Filter.Eventually.of_forall fun N =>
      (le_of_not_gt hA).trans (Real.exp_pos _).le

lemma eventually_lowerPathLogScale_le_Zscale :
    ∀ᶠ N : ℕ in atTop,
      ∀ i : lowerPathIndex N, lowerPathLogScale N i ≤ Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 4] with N hNlarge_nat hloglog_ge i
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hY_ge : 4 ≤ Y := by
    simpa [Y] using hloglog_ge
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hZ_pos : 0 < Zscale N := by
    rw [← Mscale_mul_loglog_eq_Zscale hNlarge]
    simpa [M, Y] using mul_pos hM_pos hY_pos
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hr_le : r ≤ 2 * M := by
    dsimp [r, M]
    exact Nat.floor_le (by positivity : 0 ≤ 2 * Mscale N)
  have hr_plus_gt : 2 * M < r + 1 := by
    have hlt := Nat.lt_floor_add_one (2 * Mscale N)
    dsimp [r, M]
    exact_mod_cast hlt
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hden_pos : 0 < r + 1 := by positivity
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    have htmp : 0 ≤ (1 / 2 : ℝ) * Y - Real.sqrt Y := by
      have hsqrt_sq := Real.sq_sqrt hY_nonneg
      nlinarith [Real.sqrt_nonneg Y, hY_ge]
    simpa [lowerPathLogGap, Y] using htmp
  have hgap_le : lowerPathLogGap N ≤ Y / 2 := by
    have htmp : (1 / 2 : ℝ) * Y - Real.sqrt Y ≤ Y / 2 := by
      nlinarith [Real.sqrt_nonneg Y]
    simpa [lowerPathLogGap, Y] using htmp
  have hdiv_le : Real.log (N : ℝ) / (r + 1) ≤ Zscale N / 2 := by
    rw [← hMZ]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hgap_r_le : lowerPathLogGap N * r / 2 ≤ Zscale N / 2 := by
    nlinarith
  have hidx_le : (i.1 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast Nat.le_of_lt_succ i.2
  have hscale_eq :
      lowerPathLogScale N i =
        Real.log (N : ℝ) / (r + 1) - Real.log 2 -
          lowerPathLogGap N * r / 2 +
          (i.1 : ℝ) * lowerPathLogGap N := by
    rw [lowerPathLogScale, lowerPathLogBase]
    dsimp [r]
    field_simp [show r + 1 ≠ 0 by positivity]
  have htail :
      -lowerPathLogGap N * r / 2 + (i.1 : ℝ) * lowerPathLogGap N
        ≤ lowerPathLogGap N * r / 2 := by
    nlinarith
  have hlog_two_nonneg : 0 ≤ Real.log 2 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  rw [hscale_eq]
  nlinarith

lemma lowerPathLogScale_zero_le_two_M_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hloglog_ge : 16 ≤ Real.log (Real.log (N : ℝ)))
    (hloglog_le_M : Real.log (Real.log (N : ℝ)) ≤ Mscale N) :
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ ≤
      2 * Mscale N * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  set r : ℝ := (lowerPathR N : ℝ)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hY_pos : 0 < Y := by
    dsimp [Y]
    exact Real.log_pos hlog_gt_one
  have hY_nonneg : 0 ≤ Y := hY_pos.le
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg Y
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_nonneg
  have hY_ge : 16 ≤ Y := by
    simpa [Y] using hloglog_ge
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hY_pos
  have hs_ge_four : 4 ≤ s := by
    refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) hY_nonneg).2 ?_
    norm_num
    exact hY_ge
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hY_le_M : Y ≤ M := by
    simpa [Y, M] using hloglog_le_M
  have hs_le_M : s ≤ M := by
    have hM_ge_one : 1 ≤ M := by nlinarith
    have hs_sq_le_M_sq : s ^ 2 ≤ M ^ 2 := by
      rw [hs_sq]
      nlinarith
    exact (sq_le_sq₀ hs_nonneg hM_nonneg).1 hs_sq_le_M_sq
  have hMZ : M * Zscale N = Real.log (N : ℝ) := by
    dsimp [M]
    exact Mscale_mul_Zscale_eq_log hNlarge
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hlog_eq : Real.log (N : ℝ) = M ^ 2 * Y := by
    rw [← hMZ, ← hMY]
    ring
  have hr_plus_gt : 2 * M < r + 1 := by
    have hlt := Nat.lt_floor_add_one (2 * Mscale N)
    dsimp [r, M] at hlt ⊢
    exact_mod_cast hlt
  have hr_lower : 2 * M - 1 ≤ r := by linarith
  have hden_pos : 0 < r + 1 := by positivity
  have hgap_eq : lowerPathLogGap N = Y / 2 - s := by
    rw [lowerPathLogGap]
    dsimp [Y, s]
    ring
  have hgap_nonneg : 0 ≤ lowerPathLogGap N := by
    rw [hgap_eq]
    nlinarith [hs_sq, hs_ge_four]
  have hscale_eq :
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ =
        Real.log (N : ℝ) / (r + 1) - Real.log 2 -
          lowerPathLogGap N * r / 2 := by
    exact lowerPathLogScale_zero_eq N
  have hdiv_le : Real.log (N : ℝ) / (r + 1) ≤ M * Y / 2 := by
    rw [hlog_eq]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hsub_le :
      -(Y / 2 - s) * r / 2 ≤ -(Y / 2 - s) * (2 * M - 1) / 2 := by
    have hgap0 : 0 ≤ Y / 2 - s := by
      simpa [hgap_eq] using hgap_nonneg
    nlinarith
  rw [hscale_eq, hgap_eq]
  have hlog_two_nonneg : 0 ≤ Real.log 2 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  calc
    Real.log (N : ℝ) / (r + 1) - Real.log 2 - (Y / 2 - s) * r / 2
        ≤ M * Y / 2 - (Y / 2 - s) * (2 * M - 1) / 2 := by
          nlinarith
    _ = M * s + Y / 4 - s / 2 := by ring
    _ ≤ 2 * M * s := by
          nlinarith

lemma eventually_lowerPathLogScale_zero_le_mul_Zscale
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      lowerPathLogScale N ⟨0, Nat.succ_pos _⟩ ≤ δ * Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop (2 / δ),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 16,
      eventually_loglog_le_Mscale] with N hNlarge_nat hs hloglog hloglog_le_M
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set M := Mscale N
  set Y := Real.log (Real.log (N : ℝ))
  set s := Real.sqrt Y
  have hY_pos : 0 < Y := by
    dsimp [Y]
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    exact Real.log_pos ((Real.lt_log_iff_exp_lt hNpos).2 hNlarge)
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Mscale_pos_of_exp_one_lt_nat hNlarge
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hY_pos
  have hMY : M * Y = Zscale N := by
    dsimp [M, Y]
    exact Mscale_mul_loglog_eq_Zscale hNlarge
  have hs_sq : s ^ 2 = Y := by
    dsimp [s]
    exact Real.sq_sqrt hY_pos.le
  have hroot :=
    lowerPathLogScale_zero_le_two_M_mul_sqrt_loglog hNlarge hloglog hloglog_le_M
  have htwo_le : 2 ≤ δ * s := by
    have hs' : 2 / δ ≤ s := by simpa [s, Y] using hs
    have htmp : 2 ≤ s * δ := (div_le_iff₀ hδ).1 hs'
    nlinarith
  have hmain : 2 * M * s ≤ δ * (M * Y) := by
    have htwo_mul_s : 2 * s ≤ δ * Y := by
      calc
        2 * s ≤ (δ * s) * s := mul_le_mul_of_nonneg_right htwo_le hs_pos.le
        _ = δ * Y := by rw [← hs_sq]; ring
    have hmul := mul_le_mul_of_nonneg_left htwo_mul_s hM_pos.le
    nlinarith
  calc
    lowerPathLogScale N ⟨0, Nat.succ_pos _⟩
        ≤ 2 * M * s := hroot
    _ ≤ δ * (M * Y) := hmain
    _ = δ * Zscale N := by rw [hMY]

lemma eventually_Zscale_ge_const_path (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Zscale N := by
  let B : ℝ := max A 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hBnonneg : 0 ≤ B := hBpos.le
  filter_upwards [eventually_Mscale_ge 1 zero_lt_one,
      eventually_sqrt_loglog_ge (Real.sqrt B),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hM hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsq :
      (Real.sqrt B) ^ 2 ≤
        (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg B) hsqrt 2
  have hloglog_ge_B : B ≤ Real.log (Real.log (N : ℝ)) := by
    simpa [Real.sq_sqrt hBnonneg, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZ := Mscale_mul_loglog_eq_Zscale hNlarge
  have hB_le_Z : B ≤ Zscale N := by
    rw [← hZ]
    nlinarith [hM, hloglog_ge_B, hBpos.le]
  exact (le_max_left A 1).trans hB_le_Z

lemma eventually_log_loglog_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (Real.log (N : ℝ))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) =o[atTop]
        fun N : ℕ => Real.log (Real.log (N : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_loglog_nat_atTop
  filter_upwards [isLittleO_iff.mp hsmall hδ,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with N hsmallN hYge_one
  have hYpos : 0 < Real.log (Real.log (N : ℝ)) := zero_lt_one.trans_le hYge_one
  have hlogY_nonneg : 0 ≤ Real.log (Real.log (Real.log (N : ℝ))) :=
    Real.log_nonneg hYge_one
  have hleft_norm :
      ‖Real.log (Real.log (Real.log (N : ℝ)))‖ =
        Real.log (Real.log (Real.log (N : ℝ))) := by
    rw [Real.norm_of_nonneg hlogY_nonneg]
  have hright_norm :
      ‖Real.log (Real.log (N : ℝ))‖ =
        Real.log (Real.log (N : ℝ)) := by
    rw [Real.norm_of_nonneg hYpos.le]
  simpa [hleft_norm, hright_norm] using hsmallN

lemma eventually_log_const_mul_sqrt_loglog_le_mul_loglog
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (A * Real.sqrt (Real.log (Real.log (N : ℝ)))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  let C : ℝ := max (2 * Real.log A / δ) 1
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [tendsto_loglog_nat_atTop.eventually_ge_atTop C,
      eventually_log_loglog_le_mul_loglog (δ / 2) hδ2] with N hYgeC hlogY
  set Y := Real.log (Real.log (N : ℝ))
  have hC_ge_main : 2 * Real.log A / δ ≤ C := le_max_left _ _
  have hY_ge_main : 2 * Real.log A / δ ≤ Y := hC_ge_main.trans hYgeC
  have hY_ge_one : 1 ≤ Y := (le_max_right _ _).trans hYgeC
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY_ge_one
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hconst : Real.log A ≤ (δ / 2) * Y := by
    have hmul := mul_le_mul_of_nonneg_right hY_ge_main hδ2.le
    field_simp [hδ.ne'] at hmul
    linarith
  have hlogsqrt : Real.log (Real.sqrt Y) = Real.log Y / 2 :=
    Real.log_sqrt hY_pos.le
  calc
    Real.log (A * Real.sqrt Y)
        = Real.log A + Real.log (Real.sqrt Y) := by
            rw [Real.log_mul hA.ne' hsqrt_pos.ne']
    _ = Real.log A + Real.log Y / 2 := by rw [hlogsqrt]
    _ ≤ (δ / 2) * Y + (δ / 2) * Y / 2 := by
            have hhalf : Real.log Y / 2 ≤ ((δ / 2) * Y) / 2 := by
              exact div_le_div_of_nonneg_right hlogY (by norm_num)
            nlinarith
    _ ≤ δ * Y := by nlinarith

lemma Zscale_eq_exp_half_loglog_mul_sqrt_loglog {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ)) :
    Zscale N =
      Real.exp (Real.log (Real.log (N : ℝ)) / 2) *
        Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  set Y := Real.log (Real.log (N : ℝ))
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_eq : Real.log (N : ℝ) = Real.exp Y := by
    dsimp [Y]
    rw [Real.exp_log hlog_pos]
  have hsqrt_log :
      Real.sqrt (Real.log (N : ℝ)) = Real.exp (Y / 2) := by
    rw [hlog_eq, ← Real.exp_half]
  rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge, hsqrt_log]

lemma eventually_log_eight_mul_Zscale_le
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (8 * Zscale N) ≤
        ((1 + δ) / 2) * Real.log (Real.log (N : ℝ)) := by
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_const_mul_sqrt_loglog_le_mul_loglog 8 (δ / 2)
        (by norm_num) hδ2,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with
    N hNlarge_nat hlog_extra hYge_one
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  set Y := Real.log (Real.log (N : ℝ))
  have hY_pos : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using hYge_one)
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hZeq := Zscale_eq_exp_half_loglog_mul_sqrt_loglog hNlarge
  calc
    Real.log (8 * Zscale N)
        = Real.log (Real.exp (Y / 2) * (8 * Real.sqrt Y)) := by
            congr 1
            rw [hZeq]
            ring
    _ = Y / 2 + Real.log (8 * Real.sqrt Y) := by
            rw [Real.log_mul (Real.exp_ne_zero _) (mul_pos (by norm_num) hsqrt_pos).ne',
              Real.log_exp]
    _ ≤ Y / 2 + (δ / 2) * Y := by
            have hlog_extraY :
                Real.log (8 * Real.sqrt Y) ≤ (δ / 2) * Y := by
              simpa [Y] using hlog_extra
            nlinarith
    _ = ((1 + δ) / 2) * Y := by ring

lemma eventually_lowerPathR_mul_log_eightZ_le_mul_Zscale
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (lowerPathR N : ℝ) * Real.log (8 * Zscale N) ≤
        (1 + δ) * Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_log_eight_mul_Zscale_le δ hδ,
      eventually_Zscale_ge_const_path (1 / 8)] with N hNlarge_nat hlog_le hZge
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
  have hbase_ge_one : 1 ≤ 8 * Zscale N := by nlinarith
  have hlog_nonneg : 0 ≤ Real.log (8 * Zscale N) :=
    Real.log_nonneg hbase_ge_one
  calc
    (lowerPathR N : ℝ) * Real.log (8 * Zscale N)
        ≤ (2 * M) * Real.log (8 * Zscale N) := by
            exact mul_le_mul_of_nonneg_right hr_le hlog_nonneg
    _ ≤ (2 * M) * (((1 + δ) / 2) * Y) := by
            exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
    _ = (1 + δ) * (M * Y) := by ring
    _ = (1 + δ) * Zscale N := by rw [hMY]

end Erdos202
