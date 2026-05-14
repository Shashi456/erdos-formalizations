/-
Erdős Problem 202 — Main theorem.

Combines:
  * upper bound from `Optimization.f_upper_bound`
    (Chain inequality + σ optimization, conditional on the BFV inputs and
     the spread-disjointness input);
  * lower bound from `bfv_lower_bound_theorem`.

The historical omega-count and lower-bound input names now point to fully
proved theorems.  The trust boundary is empty beyond Lean core: running
`#print axioms Erdos202.erdos202_main` should print only
`propext`, `Classical.choice`, `Quot.sound`.

This file formalizes the sharp asymptotic for Erdős Problem 202
(PDF Theorem 1.1).  The integral / partial-summation Corollary 1.2 about
Erdős Problem 1190 is formalized separately as `Erdos202.erdos1190_main`
in `Erdos/P1190/Proof.lean` (the P1190 directory has its own SafeVerify
contract); the legacy compatibility import `Erdos.P202.P1190` re-exports it.

Audit by uncommenting the `#print axioms` block below.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic
import Erdos.P202.SpreadCore
import Erdos.P202.BFVInputs
import Erdos.P202.P202Chain
import Erdos.P202.BFV.LowerBoundInput
import Erdos.P202.P202Optimization

namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

/-- **Conditional Erdős 202 upper bound.** From the BFV pruning theorem layer,
omega-count theorem layer, and spread theorem layer, the upper half of the
asymptotic holds. -/
theorem erdos202_upper_bound_from_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N :=
  f_upper_bound

/-- **Erdős Problem 202 — main theorem.** The sharp BFV asymptotic
`f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`. -/
theorem erdos202_main : Erdos202Statement := by
  intro ε hε
  filter_upwards [bfv_lower_bound_theorem ε hε, f_upper_bound ε hε] with N hLow hUp
  exact ⟨hLow, hUp⟩

/-! ## Real-variable formulation -/

private noncomputable def Zreal (x : ℝ) : ℝ :=
  Real.sqrt (Real.log x * Real.log (Real.log x))

private lemma zscale_floor_isEquivalent_zreal :
    (fun x : ℝ => Zscale (Nat.floor x)) ~[atTop] (fun x : ℝ => Zreal x) := by
  let fp : ℝ → ℝ := fun x =>
    Real.log (((Nat.floor x : ℕ) : ℝ)) *
      Real.log (Real.log (((Nat.floor x : ℕ) : ℝ)))
  let gp : ℝ → ℝ := fun x => Real.log x * Real.log (Real.log x)
  have hfloor : (fun x : ℝ => ((Nat.floor x : ℕ) : ℝ)) ~[atTop] (fun x : ℝ => x) :=
    Asymptotics.isEquivalent_nat_floor
  have hlog :
      (fun x : ℝ => Real.log (((Nat.floor x : ℕ) : ℝ))) ~[atTop]
        (fun x : ℝ => Real.log x) :=
    hfloor.log tendsto_id
  have hloglog :
      (fun x : ℝ => Real.log (Real.log (((Nat.floor x : ℕ) : ℝ)))) ~[atTop]
        (fun x : ℝ => Real.log (Real.log x)) :=
    hlog.log Real.tendsto_log_atTop
  have hprod :
      (fun x : ℝ =>
          Real.log (((Nat.floor x : ℕ) : ℝ)) *
            Real.log (Real.log (((Nat.floor x : ℕ) : ℝ)))) ~[atTop]
        (fun x : ℝ => Real.log x * Real.log (Real.log x)) :=
    hlog.mul hloglog
  have hgp_pos : ∀ᶠ x : ℝ in atTop, 0 < gp x := by
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have hxpos : 0 < x := (Real.exp_pos 1).trans hx
    have hlog_gt_one : 1 < Real.log x := (Real.lt_log_iff_exp_lt hxpos).2 hx
    exact mul_pos (zero_lt_one.trans hlog_gt_one) (Real.log_pos hlog_gt_one)
  have hfp_pos : ∀ᶠ x : ℝ in atTop, 0 < fp x := by
    filter_upwards [((tendsto_nat_floor_atTop (α := ℝ)).eventually_gt_atTop
      (Nat.ceil (Real.exp 1)))] with x hx
    have hfloor_large : Real.exp 1 < (((Nat.floor x : ℕ) : ℝ)) :=
      lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hx)
    have hfloor_pos : 0 < (((Nat.floor x : ℕ) : ℝ)) := (Real.exp_pos 1).trans hfloor_large
    have hlog_gt_one : 1 < Real.log (((Nat.floor x : ℕ) : ℝ)) :=
      (Real.lt_log_iff_exp_lt hfloor_pos).2 hfloor_large
    exact mul_pos (zero_lt_one.trans hlog_gt_one) (Real.log_pos hlog_gt_one)
  have hfp_eq : fp =ᶠ[atTop] fun x => max (fp x) 0 := by
    filter_upwards [hfp_pos] with x hx
    simp [max_eq_left hx.le]
  have hgp_eq : gp =ᶠ[atTop] fun x => max (gp x) 0 := by
    filter_upwards [hgp_pos] with x hx
    simp [max_eq_left hx.le]
  have hprod' : fp ~[atTop] gp := by
    simpa [fp, gp] using hprod
  have hmax :
      (fun x => max (fp x) 0) ~[atTop] (fun x => max (gp x) 0) :=
    hfp_eq.symm.isEquivalent.trans (hprod'.trans hgp_eq.isEquivalent)
  have hsqrtmax :
      (fun x => (max (fp x) 0) ^ (1 / 2 : ℝ)) ~[atTop]
        (fun x => (max (gp x) 0) ^ (1 / 2 : ℝ)) :=
    Asymptotics.IsEquivalent.rpow (fun x => le_max_right (gp x) 0) hmax
  have hsource :
      (fun x : ℝ => Zscale (Nat.floor x)) =ᶠ[atTop]
        (fun x => (max (fp x) 0) ^ (1 / 2 : ℝ)) := by
    filter_upwards [hfp_pos] with x hx
    simp [Zscale, fp, Real.sqrt_eq_rpow, max_eq_left hx.le]
  have htarget :
      (fun x : ℝ => Zreal x) =ᶠ[atTop]
        (fun x => (max (gp x) 0) ^ (1 / 2 : ℝ)) := by
    filter_upwards [hgp_pos] with x hx
    simp [Zreal, gp, Real.sqrt_eq_rpow, max_eq_left hx.le]
  exact hsource.isEquivalent.trans (hsqrtmax.trans htarget.symm.isEquivalent)

private lemma tendsto_zscale_floor_div_zreal :
    Tendsto (fun x : ℝ => Zscale (Nat.floor x) / Zreal x) atTop (nhds 1) := by
  have hz_ne : ∀ᶠ x : ℝ in atTop, Zreal x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have hxpos : 0 < x := (Real.exp_pos 1).trans hx
    have hlog_gt_one : 1 < Real.log x := (Real.lt_log_iff_exp_lt hxpos).2 hx
    have hprod_pos : 0 < Real.log x * Real.log (Real.log x) :=
      mul_pos (zero_lt_one.trans hlog_gt_one) (Real.log_pos hlog_gt_one)
    exact ne_of_gt (by simpa [Zreal] using Real.sqrt_pos.2 hprod_pos)
  exact (isEquivalent_iff_tendsto_one hz_ne).1 zscale_floor_isEquivalent_zreal

private lemma tendsto_zreal_atTop : Tendsto Zreal atTop atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hprod :
      Tendsto (fun x : ℝ => Real.log x * Real.log (Real.log x)) atTop atTop :=
    hlog.atTop_mul_atTop₀ hloglog
  exact Real.tendsto_sqrt_atTop.comp hprod

private lemma eventually_floor_bounds :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ Nat.floor x ∧ x ≤ 2 * (((Nat.floor x : ℕ) : ℝ)) ∧
        (((Nat.floor x : ℕ) : ℝ)) ≤ x := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx_nonneg : 0 ≤ x := by linarith
  have hfloor_ge : 1 ≤ Nat.floor x := by
    have hx_ge_one : (1 : ℝ) ≤ x := by linarith
    exact (Nat.le_floor_iff hx_nonneg).2 (by simpa using hx_ge_one)
  have hx_lt : x < (((Nat.floor x : ℕ) : ℝ)) + 1 := Nat.lt_floor_add_one x
  have hfloor_real_ge : (1 : ℝ) ≤ (((Nat.floor x : ℕ) : ℝ)) := by exact_mod_cast hfloor_ge
  have hfloor_le : (((Nat.floor x : ℕ) : ℝ)) ≤ x := Nat.floor_le hx_nonneg
  constructor
  · exact hfloor_ge
  constructor
  · linarith
  · exact hfloor_le

private lemma erdos202_real_bounds_lt_one (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 1) :
    ∀ᶠ x : ℝ in atTop,
      x * Real.exp (-(1 + ε) * Zreal x) ≤ (fReal x : ℝ) ∧
      (fReal x : ℝ) ≤ x * Real.exp (-(1 - ε) * Zreal x) := by
  have hδ : 0 < ε / 4 := by positivity
  have hnat_floor :
      ∀ᶠ x : ℝ in atTop,
        (((Nat.floor x : ℕ) : ℝ) * Lscale (-(1 + ε / 4)) (Nat.floor x) ≤
            (f (Nat.floor x) : ℝ) ∧
          (f (Nat.floor x) : ℝ) ≤
            (((Nat.floor x : ℕ) : ℝ) * Lscale (-(1 - ε / 4)) (Nat.floor x))) :=
    (tendsto_nat_floor_atTop (α := ℝ)).eventually (erdos202_main (ε / 4) hδ)
  have hz_pos : ∀ᶠ x : ℝ in atTop, 0 < Zreal x := by
    filter_upwards [tendsto_zreal_atTop.eventually_gt_atTop 0] with x hx
    exact hx
  have hz_large :
      ∀ᶠ x : ℝ in atTop, Real.log 2 / (ε / 4) ≤ Zreal x :=
    tendsto_zreal_atTop.eventually_ge_atTop (Real.log 2 / (ε / 4))
  have hratio_up :
      ∀ᶠ x : ℝ in atTop, Zscale (Nat.floor x) ≤ (1 + ε / 4) * Zreal x := by
    have hconst : (1 : ℝ) < 1 + ε / 4 := by linarith
    filter_upwards [tendsto_zscale_floor_div_zreal.eventually_lt_const hconst, hz_pos] with x hx hZ
    exact ((div_lt_iff₀ hZ).1 hx).le
  have hratio_low :
      ∀ᶠ x : ℝ in atTop, (1 - ε / 4) * Zreal x ≤ Zscale (Nat.floor x) := by
    have hconst : 1 - ε / 4 < (1 : ℝ) := by linarith
    filter_upwards [Tendsto.eventually_const_lt hconst tendsto_zscale_floor_div_zreal, hz_pos]
      with x hx hZ
    exact ((lt_div_iff₀ hZ).1 hx).le
  filter_upwards [hnat_floor, eventually_floor_bounds, hz_pos, hz_large, hratio_up, hratio_low]
    with x hnat hfloor hZpos hZlarge hZu hZl
  rcases hnat with ⟨hLowNat, hUpNat⟩
  rcases hfloor with ⟨_hfloor_one, hx_le_two_floor, hfloor_le_x⟩
  have hx_nonneg : 0 ≤ x := by
    have hfloor_nonneg : (0 : ℝ) ≤ (((Nat.floor x : ℕ) : ℝ)) := by positivity
    exact hfloor_nonneg.trans hfloor_le_x
  have hZnonneg : 0 ≤ Zreal x := hZpos.le
  have hlog2_le : Real.log 2 ≤ (ε / 4) * Zreal x := by
    have h := (div_le_iff₀ hδ).1 hZlarge
    nlinarith
  constructor
  · have hcoeff :
        ε / 4 + (1 + ε / 4) * (1 + ε / 4) ≤ 1 + ε := by
      nlinarith [hε.le, hεlt.le]
    have harg :
        Real.log 2 - (1 + ε) * Zreal x ≤
          -(1 + ε / 4) * Zscale (Nat.floor x) := by
      have hmain :
          Real.log 2 + (1 + ε / 4) * Zscale (Nat.floor x) ≤
            (1 + ε) * Zreal x := by
        calc
          Real.log 2 + (1 + ε / 4) * Zscale (Nat.floor x)
              ≤ (ε / 4) * Zreal x +
                  (1 + ε / 4) * ((1 + ε / 4) * Zreal x) := by
                have hcoef_nonneg : 0 ≤ 1 + ε / 4 := by positivity
                exact add_le_add hlog2_le (mul_le_mul_of_nonneg_left hZu hcoef_nonneg)
          _ = (ε / 4 + (1 + ε / 4) * (1 + ε / 4)) * Zreal x := by ring
          _ ≤ (1 + ε) * Zreal x := by
                exact mul_le_mul_of_nonneg_right hcoeff hZnonneg
      linarith
    have hexp :
        2 * Real.exp (-(1 + ε) * Zreal x) ≤
          Real.exp (-(1 + ε / 4) * Zscale (Nat.floor x)) := by
      calc
        2 * Real.exp (-(1 + ε) * Zreal x)
            = Real.exp (Real.log 2 - (1 + ε) * Zreal x) := by
                calc
                  2 * Real.exp (-(1 + ε) * Zreal x)
                      = Real.exp (Real.log 2) * Real.exp (-(1 + ε) * Zreal x) := by
                          rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
                  _ = Real.exp (Real.log 2 + (-(1 + ε) * Zreal x)) := by
                          rw [Real.exp_add]
                  _ = Real.exp (Real.log 2 - (1 + ε) * Zreal x) := by ring_nf
        _ ≤ Real.exp (-(1 + ε / 4) * Zscale (Nat.floor x)) :=
              Real.exp_le_exp.2 harg
    calc
      x * Real.exp (-(1 + ε) * Zreal x)
          ≤ (2 * (((Nat.floor x : ℕ) : ℝ))) *
              Real.exp (-(1 + ε) * Zreal x) := by
            exact mul_le_mul_of_nonneg_right hx_le_two_floor (Real.exp_pos _).le
      _ = (((Nat.floor x : ℕ) : ℝ)) *
            (2 * Real.exp (-(1 + ε) * Zreal x)) := by ring
      _ ≤ (((Nat.floor x : ℕ) : ℝ)) *
            Real.exp (-(1 + ε / 4) * Zscale (Nat.floor x)) := by
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (((Nat.floor x : ℕ) : ℝ)) * Lscale (-(1 + ε / 4)) (Nat.floor x) := by
            simp [Lscale]
      _ ≤ (fReal x : ℝ) := by
            simpa [fReal] using hLowNat
  · have hcoeff :
        (1 - ε) ≤ (1 - ε / 4) * (1 - ε / 4) := by
      nlinarith [hε.le, hεlt.le]
    have harg :
        -(1 - ε / 4) * Zscale (Nat.floor x) ≤ -(1 - ε) * Zreal x := by
      have hcoef_nonneg : 0 ≤ 1 - ε / 4 := by nlinarith [hεlt.le]
      have hmain :
          (1 - ε) * Zreal x ≤ (1 - ε / 4) * Zscale (Nat.floor x) := by
        calc
          (1 - ε) * Zreal x
              ≤ ((1 - ε / 4) * (1 - ε / 4)) * Zreal x := by
                    exact mul_le_mul_of_nonneg_right hcoeff hZnonneg
          _ = (1 - ε / 4) * ((1 - ε / 4) * Zreal x) := by ring
          _ ≤ (1 - ε / 4) * Zscale (Nat.floor x) := by
                    exact mul_le_mul_of_nonneg_left hZl hcoef_nonneg
      linarith
    have hexp :
        Real.exp (-(1 - ε / 4) * Zscale (Nat.floor x)) ≤
          Real.exp (-(1 - ε) * Zreal x) :=
      Real.exp_le_exp.2 harg
    calc
      (fReal x : ℝ)
          ≤ (((Nat.floor x : ℕ) : ℝ) *
              Lscale (-(1 - ε / 4)) (Nat.floor x)) := by
            simpa [fReal] using hUpNat
      _ = (((Nat.floor x : ℕ) : ℝ) *
              Real.exp (-(1 - ε / 4) * Zscale (Nat.floor x))) := by
            simp [Lscale]
      _ ≤ x * Real.exp (-(1 - ε / 4) * Zscale (Nat.floor x)) := by
            exact mul_le_mul_of_nonneg_right hfloor_le_x (Real.exp_pos _).le
      _ ≤ x * Real.exp (-(1 - ε) * Zreal x) := by
            exact mul_le_mul_of_nonneg_left hexp hx_nonneg

/-- **Real-variable Erdős 202 — main theorem.**  This is the PDF-style
formulation obtained from `erdos202_main` by the standard floor transfer
`fReal x = f(⌊x⌋)`. -/
theorem erdos202_real_main : HasErdos202RealAsymptotic := by
  intro ε hε
  by_cases hlt : ε < 1
  · simpa [HasErdos202RealAsymptotic, Zreal] using erdos202_real_bounds_lt_one ε hε hlt
  · have hge : (1 : ℝ) ≤ ε := le_of_not_gt hlt
    have hhalf :
        ∀ᶠ x : ℝ in atTop,
          x * Real.exp (-(1 + (1 / 2 : ℝ)) * Zreal x) ≤ (fReal x : ℝ) ∧
          (fReal x : ℝ) ≤ x * Real.exp (-(1 - (1 / 2 : ℝ)) * Zreal x) :=
      erdos202_real_bounds_lt_one (1 / 2) (by norm_num) (by norm_num)
    filter_upwards [hhalf, eventually_floor_bounds] with x hhalf hfloor
    rcases hhalf with ⟨hLowHalf, _hUpHalf⟩
    rcases hfloor with ⟨_hfloor_one, _hx_le_two_floor, hfloor_le_x⟩
    have hx_nonneg : 0 ≤ x := by
      have hfloor_nonneg : (0 : ℝ) ≤ (((Nat.floor x : ℕ) : ℝ)) := by positivity
      exact hfloor_nonneg.trans hfloor_le_x
    have hZnonneg : 0 ≤ Zreal x := by
      simp [Zreal]
    constructor
    · have harg :
          -(1 + ε) * Zreal x ≤ -(1 + (1 / 2 : ℝ)) * Zreal x := by
        have hcoef : (1 + (1 / 2 : ℝ)) ≤ 1 + ε := by linarith
        have hmul : (1 + (1 / 2 : ℝ)) * Zreal x ≤ (1 + ε) * Zreal x :=
          mul_le_mul_of_nonneg_right hcoef hZnonneg
        linarith
      calc
        x * Real.exp (-(1 + ε) * Zreal x)
            ≤ x * Real.exp (-(1 + (1 / 2 : ℝ)) * Zreal x) := by
              exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 harg) hx_nonneg
        _ ≤ (fReal x : ℝ) := hLowHalf
    · have hf_le_floor : (fReal x : ℝ) ≤ (((Nat.floor x : ℕ) : ℝ)) := by
        exact_mod_cast (f_le (Nat.floor x))
      have hfactor_ge_one :
          1 ≤ Real.exp (-(1 - ε) * Zreal x) := by
        have harg_nonneg : 0 ≤ -(1 - ε) * Zreal x := by
          have hcoef_nonneg : 0 ≤ -(1 - ε) := by linarith
          exact mul_nonneg hcoef_nonneg hZnonneg
        exact Real.one_le_exp harg_nonneg
      calc
        (fReal x : ℝ) ≤ (((Nat.floor x : ℕ) : ℝ)) := hf_le_floor
        _ ≤ x := hfloor_le_x
        _ = x * 1 := by ring
        _ ≤ x * Real.exp (-(1 - ε) * Zreal x) := by
              exact mul_le_mul_of_nonneg_left hfactor_ge_one hx_nonneg

/-! ## Axiom audit

The block below audits the public theorem path.  The expected output is
exactly the three Lean foundational axioms `propext`, `Classical.choice`,
and `Quot.sound` — no project-level axioms remain.
-/

-- #print axioms erdos202_upper_bound_from_inputs
-- #print axioms erdos202_main
-- #print axioms erdos202_real_main

end Erdos202
