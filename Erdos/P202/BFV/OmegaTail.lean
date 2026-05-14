/-
Erdos Problem 202 -- BFV omega-tail estimates.

This file contains the elementary Rankin counting step used before the
BFV/Hardy-Ramanujan analytic input.  The Euler-product estimate is proved in
`Erdos.P202.BFV.Mertens`.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic
import Erdos.P202.BFV.Mertens

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Rankin's inequality for omega tails

The BFV Rankin parameter `BFVz N := √(log N) / log log N` lives in
`Erdos.P202.BFV.Mertens`, alongside the weighted omega-sum estimate consumed
below. -/

lemma card_le_floor_of_natCast_le {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hm : (m : ℝ) ≤ x) : m ≤ Nat.floor x :=
  (Nat.le_floor_iff hx).2 hm

/-- Rankin's inequality:
`#{n ≤ y : t ≤ omega n} * z^t ≤ sum_{n≤y} z^(omega n)` for `z ≥ 1`. -/
lemma rankin_omega_tail_sum_le (y t : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
      ≤ ∑ n ∈ Finset.Icc 1 y, z ^ omega n := by
  classical
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  calc
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
        = ∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ≤ omega n), z ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ≤ omega n), z ^ omega n := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact pow_le_pow_right₀ hz (Finset.mem_filter.1 hn).2
    _ ≤ ∑ n ∈ Finset.Icc 1 y, z ^ omega n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro n _hnIcc hnNotFilter
          exact pow_nonneg hz0 (omega n)

/-- A Rankin wrapper that turns an upper bound for the weighted omega sum into
a real-valued bound for the tail count. -/
lemma omega_tail_card_real_le_of_sum_le
    (y t : ℕ) {z B : ℝ} (hz : 1 ≤ z)
    (hSum : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B) :
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ)
      ≤ (y : ℝ) * B / z ^ t := by
  classical
  have hzpow_pos : 0 < z ^ t := pow_pos (zero_lt_one.trans_le hz) t
  have htail := rankin_omega_tail_sum_le y t hz
  have hmul_le : (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
      ≤ (y : ℝ) * B :=
    htail.trans hSum
  exact (le_div_iff₀ hzpow_pos).2 hmul_le

/-- A floor-valued version of `omega_tail_card_real_le_of_sum_le`. -/
lemma omega_tail_card_le_floor_of_sum_le
    (y t : ℕ) {z B X : ℝ} (hz : 1 ≤ z)
    (hX : 0 ≤ X)
    (hSum : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B)
    (hRankinTarget : (y : ℝ) * B / z ^ t ≤ X) :
    ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card ≤ Nat.floor X := by
  refine card_le_floor_of_natCast_le hX ?_
  exact (omega_tail_card_real_le_of_sum_le y t hz hSum).trans hRankinTarget

/-! ## BFV analytic omega tail -/

private lemma tendsto_logloglog_div_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
        Real.log (Real.log (N : ℝ))) atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        fun x : ℝ => Real.log x :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact hsmall.tendsto_div_nhds_zero
  exact hreal.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma eventually_logloglog_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (Real.log (N : ℝ))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        Real.log (Real.log (Real.log (N : ℝ))) /
          Real.log (Real.log (N : ℝ)) < δ :=
    tendsto_logloglog_div_loglog_nat_atTop.eventually_lt_const hδ
  filter_upwards [hsmall, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hsmallN hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  exact ((div_lt_iff₀ hloglog_pos).1 hsmallN).le

private lemma BFVz_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < BFVz N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [BFVz]
  exact div_pos (Real.sqrt_pos.2 hlog_pos) hloglog_pos

private lemma eventually_BFVz_log_lower
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)) ≤ Real.log (BFVz N) := by
  filter_upwards [eventually_logloglog_le_mul_loglog δ hδ,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlll hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hsqrt_pos : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 hlog_pos
  have hlog_BFVz :
      Real.log (BFVz N) =
        Real.log (Real.log (N : ℝ)) / 2 -
          Real.log (Real.log (Real.log (N : ℝ))) := by
    rw [BFVz, Real.log_div hsqrt_pos.ne' hloglog_pos.ne',
      Real.log_sqrt hlog_nonneg]
  rw [hlog_BFVz]
  nlinarith

private lemma eventually_BFVz_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ BFVz N := by
  filter_upwards [eventually_BFVz_log_lower ((1 : ℝ) / 4) (by norm_num),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlog_lower hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hzpos : 0 < BFVz N := BFVz_pos_of_exp_one_lt_nat hNlarge
  have hlog_nonneg : 0 ≤ Real.log (BFVz N) := by
    nlinarith
  have hone : Real.exp 0 ≤ BFVz N :=
    (Real.le_log_iff_exp_le hzpos).1 hlog_nonneg
  simpa using hone

private lemma eventually_rankin_factor_le
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ t : ℕ, (t : ℝ) ≤ 3 * Mscale N →
        Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          ≤ Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
  let δ : ℝ := ε / 6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [eventually_BFVz_log_lower δ hδ,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlog_lower hNlarge_nat t ht
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hZnonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hzpos : 0 < BFVz N := BFVz_pos_of_exp_one_lt_nat hNlarge
  have hLL :
      Real.log (Real.log (N : ℝ)) = Zscale N / Mscale N :=
    (Zscale_div_Mscale_eq_loglog hNlarge).symm
  have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
  have hlog_mul :
      (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
        ≤ (t : ℝ) * Real.log (BFVz N) :=
    mul_le_mul_of_nonneg_left hlog_lower ht_nonneg
  have ht_div_le : (t : ℝ) / Mscale N ≤ 3 := by
    exact (div_le_iff₀ hMpos).2 (by simpa [mul_comm] using ht)
  have hdelta_div : δ * ((t : ℝ) / Mscale N) ≤ ε / 2 := by
    calc
      δ * ((t : ℝ) / Mscale N) ≤ δ * 3 := by
        exact mul_le_mul_of_nonneg_left ht_div_le hδ.le
      _ = ε / 2 := by
        dsimp [δ]
        ring
  have hexp_le :
      (ε / 2) * Zscale N - (t : ℝ) * Real.log (BFVz N)
        ≤ (-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N := by
    have hmain :
        (ε / 2) * Zscale N -
            (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
          ≤ (-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N := by
      rw [hLL]
      have hdeltaZ :
          (δ * ((t : ℝ) / Mscale N)) * Zscale N ≤ (ε / 2) * Zscale N :=
        mul_le_mul_of_nonneg_right hdelta_div hZnonneg
      have hrewrite :
          (t : ℝ) * (((1 : ℝ) / 2 - δ) * (Zscale N / Mscale N)) =
            (((1 : ℝ) / 2 - δ) * ((t : ℝ) / Mscale N)) * Zscale N := by
        field_simp [hMpos.ne']
      rw [hrewrite]
      nlinarith
    nlinarith
  have hzpow :
      (BFVz N) ^ t = Real.exp ((t : ℝ) * Real.log (BFVz N)) := by
    calc
      (BFVz N) ^ t = (Real.exp (Real.log (BFVz N))) ^ t := by
        rw [Real.exp_log hzpos]
      _ = Real.exp ((t : ℝ) * Real.log (BFVz N)) := by
        rw [← Real.exp_nat_mul]
  rw [hzpow, ← Real.exp_sub]
  exact Real.exp_le_exp.2 hexp_le

/-- BFV omega-tail estimate, in the explicit epsilon form used by the exact
counting step.

The Euler-product bound is consumed from `Erdos.P202.BFV.Mertens`
(`omega_weighted_sum_bfvz_bound`); see that file for the analytic gap. -/
theorem bfv_omega_tail_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y t : ℕ, y ≤ N → (t : ℝ) ≤ 3 * Mscale N →
        let α : ℝ := (t : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-α / 2 + ε) * Zscale N)) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [omega_weighted_sum_bfvz_bound (ε / 2) hε2,
      eventually_rankin_factor_le ε hε, eventually_BFVz_ge_one]
    with N hWeighted hRankin hBFVz_ge_one
  intro y t hy ht
  dsimp only
  refine omega_tail_card_le_floor_of_sum_le (y := y) (t := t)
    (z := BFVz N) (B := Real.exp ((ε / 2) * Zscale N))
    (X := (y : ℝ) *
      Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N))
    hBFVz_ge_one ?_ (hWeighted y hy) ?_
  · positivity
  · have hy_nonneg : 0 ≤ (y : ℝ) := by positivity
    calc
      (y : ℝ) * Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          = (y : ℝ) *
              (Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t) := by
              ring
      _ ≤ (y : ℝ) *
              Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
              exact mul_le_mul_of_nonneg_left (hRankin t ht) hy_nonneg

end Erdos202
