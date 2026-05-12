/-
Erdős Problem 202 — Final optimization layer.

Converts the chain inequality into the upper bound `f(N) ≤ N · L(-(1-ε), N)`.

Key explicit replacements (versus the PDF):

  * `(π²/6)`-constants → `2`, via the elementary `∑_{ν=1}^m 1/ν² ≤ 2`.
  * `T = ∑ W_{r-1}` is bounded by `R K - R(R-1)/2` (no informal `O(R)`).
  * The single inequality `c σ - c²/4 ≤ σ²` is a square-completion.

The `o(1)` of the PDF is replaced by an explicit `η`-quantifier:
"for every `η > 0`, eventually `1 - η ≤ c σ_N - c²/4 + η`".
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Chain

namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

/-! ## §1 Explicit elementary inequalities -/

/-- The crude `∑_{ν=1}^m 1/ν² ≤ 2` replacing Basel. -/
lemma sum_inv_sq_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤
        2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
        cases hm
    | succ m ih =>
        cases m with
        | zero =>
            norm_num
        | succ m =>
            rw [Finset.sum_range_succ]
            have ih' : ∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2)
                ≤ 2 - 1 / ((m + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                  1 / ((m + 1 : ℕ) : ℝ) -
                    1 / (((m + 1 : ℕ) : ℝ) + 1) := by
              have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
              have hm2 : 0 < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hm1.ne', hm2.ne']
              ring_nf
              nlinarith [show 0 ≤ (m : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2))
                  + 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2
                  ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ))
                      + (1 / ((m + 1 : ℕ) : ℝ) -
                        1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
                    gcongr
              _ = 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    exact (hstrong m hm1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
      linarith)

/-- `c σ - c² / 4 ≤ σ²` for any reals `c`, `σ`. Square-completion. -/
lemma quad_bound (c σ : ℝ) : c * σ - c ^ 2 / 4 ≤ σ ^ 2 := by
  nlinarith [sq_nonneg (c / 2 - σ)]

private lemma log_chain_quadratic_algebra
    (M R K σ ε : ℝ) (hM : M ≠ 0) :
    R * σ + R * (-(K / M) / 2 + ε) +
        (2 * R * K - R * (R - 1)) / (4 * M) =
      R * σ - (R * (R - 1)) / (4 * M) + R * ε := by
  field_simp [hM]
  ring

private lemma one_sub_two_div_eq (M : ℝ) (hM : M ≠ 0) :
    1 - 2 / M = (M - 2) / M := by
  field_simp [hM]

private lemma log_chain_shape_algebra
    (M R σ ε sqrtE lambdaE : ℝ) (hM : M ≠ 0) :
    (R * σ - (R * (R - 1)) / (4 * M) + R * ε + sqrtE + lambdaE) / M =
      (R / M) * σ - (R / M) ^ 2 / 4 + (R / M) / (4 * M) + (R / M) * ε +
        sqrtE / M + lambdaE / M := by
  field_simp [hM]
  ring

private lemma eventually_log_const_mul_le_mul_self
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log (A * x) ≤ δ * x := by
  have hAtop : Tendsto (fun x : ℝ => A * x) atTop atTop :=
    tendsto_id.const_mul_atTop hA
  have hsmallA :
      (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => A * x :=
    Real.isLittleO_log_id_atTop.comp_tendsto hAtop
  have hbig : (fun x : ℝ => A * x) =O[atTop] fun x : ℝ => x :=
    isBigO_const_mul_self A (fun x : ℝ => x) atTop
  have hsmall : (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => x :=
    hsmallA.trans_isBigO hbig
  filter_upwards [isLittleO_iff.mp hsmall hδ, eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  calc
    Real.log (A * x) ≤ ‖Real.log (A * x)‖ := le_abs_self _
    _ ≤ δ * ‖x‖ := hx
    _ = δ * x := by rw [Real.norm_of_nonneg hxpos.le]

private lemma eventually_log_chainLambda_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ D : PrunedData N,
        Real.log (chainLambda D) ≤ δ * Real.log (Real.log (N : ℝ)) := by
  let B : ℝ := |Real.log (3 * Real.exp 1)| + 1
  let A : ℝ := 2 * denseCoreConstant * B
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos (mul_pos (by norm_num) denseCoreConstant_pos) hBpos
  have hlogA_real := eventually_log_const_mul_le_mul_self A δ hApos hδ
  have hlogA :
      ∀ᶠ N : ℕ in atTop,
        Real.log (A * Real.log (Real.log (N : ℝ))) ≤
          δ * Real.log (Real.log (N : ℝ)) :=
    tendsto_loglog_nat_atTop.eventually hlogA_real
  filter_upwards [hlogA, eventually_Mscale_le_log, eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hlogA_N hMle hsqrtloglog hNlarge_nat D
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.one_le_sqrt]
    exact hsqrtloglog
  have hKle_log : (D.K : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    nlinarith [D.K_bound, hMle]
  have hKpos_real : 0 < (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_pos : 0 < Real.exp 1 * (D.K : ℝ) :=
    mul_pos (Real.exp_pos 1) hKpos_real
  have harg_le :
      Real.exp 1 * (D.K : ℝ) ≤ Real.exp 1 * (3 * Real.log (N : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hKle_log (Real.exp_pos 1).le
  have hlog_arg_le :
      Real.log (Real.exp 1 * (D.K : ℝ)) ≤
        Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) :=
    Real.log_le_log harg_pos harg_le
  have hlog_three_pos : 0 < 3 * Real.exp 1 := by positivity
  have hlog_rhs :
      Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) =
        Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := by
    have hmul :
        Real.exp 1 * (3 * Real.log (N : ℝ)) =
          (3 * Real.exp 1) * Real.log (N : ℝ) := by ring
    rw [hmul, Real.log_mul hlog_three_pos.ne' hlog_pos.ne']
  have hlog_part_le :
      Real.log (Real.exp 1 * (D.K : ℝ)) ≤
        B * Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log (Real.exp 1 * (D.K : ℝ))
          ≤ Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) := hlog_arg_le
      _ = Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := hlog_rhs
      _ ≤ B * Real.log (Real.log (N : ℝ)) := by
            dsimp [B]
            have hconst_le : Real.log (3 * Real.exp 1) ≤ |Real.log (3 * Real.exp 1)| :=
              le_abs_self _
            have hconst_mul :
                |Real.log (3 * Real.exp 1)| ≤
                  |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) :=
              le_mul_of_one_le_right (abs_nonneg _) hloglog_ge_one
            calc
              Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ))
                  ≤ |Real.log (3 * Real.exp 1)| + Real.log (Real.log (N : ℝ)) := by
                    exact add_le_add hconst_le le_rfl
              _ ≤ |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) +
                    Real.log (Real.log (N : ℝ)) := by
                    exact add_le_add hconst_mul le_rfl
              _ = (|Real.log (3 * Real.exp 1)| + 1) *
                    Real.log (Real.log (N : ℝ)) := by ring
  have hLambda_le :
      chainLambda D ≤ A * Real.log (Real.log (N : ℝ)) := by
    rw [chainLambda, chainKappa]
    calc
      2 * (denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ)))
          = 2 * denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ)) := by ring
      _ ≤ 2 * denseCoreConstant * (B * Real.log (Real.log (N : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hlog_part_le
              (mul_nonneg (by norm_num) denseCoreConstant_pos.le)
      _ = A * Real.log (Real.log (N : ℝ)) := by
            dsimp [A]
            ring
  exact (Real.log_le_log (chainLambda_pos D) hLambda_le).trans hlogA_N

private lemma coeff_sum_two (R : ℕ) :
    (∑ j : Fin R, (R - j.1)) * 2 = R * (R + 1) := by
  rw [Fin.sum_univ_eq_sum_range]
  have hreflect :
      (∑ x ∈ Finset.range R, (R - x)) =
        ∑ x ∈ Finset.range R, (x + 1) := by
    rw [← Finset.sum_range_reflect (fun x => x + 1) R]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    omega
  rw [hreflect]
  have hsumadd :
      (∑ x ∈ Finset.range R, (x + 1)) =
        (∑ x ∈ Finset.range R, x) + R := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    simp
  rw [hsumadd]
  have hid := Finset.sum_range_id_mul_two R
  by_cases hR : R = 0
  · simp [hR]
  · apply Nat.cast_injective (R := ℤ)
    push_cast
    have hcast_sub : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by
      omega
    have hidz : ((∑ i ∈ Finset.range R, (i : ℕ) : ℕ) : ℤ) * 2 =
        (R : ℤ) * ((R : ℤ) - 1) := by
      have hid' : (((∑ i ∈ Finset.range R, i) * 2 : ℕ) : ℤ) =
          ((R * (R - 1) : ℕ) : ℤ) := by
        exact_mod_cast hid
      simpa [Nat.cast_mul, hcast_sub] using hid'
    ring_nf at hidz ⊢
    nlinarith

/-- The `T`-bound: if `R, K ≥ 0` with `R ≤ K` and weights `w_j ≥ 1` summing
to `K`, then `T = ∑ (R - j + 1) w_j ≤ R K - R (R - 1) / 2`. Discrete; no
asymptotics. -/
lemma chain_T_bound
    {R K : ℕ} (hRK : R ≤ K)
    (w : Fin R → ℕ) (hw_pos : ∀ j, 1 ≤ w j)
    (hw_sum : (∑ j, w j) = K) :
    (∑ j : Fin R, (R - j.1) * w j) * 2 ≤ 2 * R * K - R * (R - 1) := by
  let u : Fin R → ℕ := fun j => w j - 1
  let c : Fin R → ℕ := fun j => R - j.1
  have hw_decomp : ∀ j, w j = u j + 1 := by
    intro j
    simp [u, Nat.sub_add_cancel (hw_pos j)]
  have hsum_u_add : (∑ j, u j) + R = K := by
    calc
      (∑ j, u j) + R = (∑ j, u j) + ∑ _j : Fin R, 1 := by simp
      _ = ∑ j : Fin R, (u j + 1) := by rw [Finset.sum_add_distrib]
      _ = ∑ j : Fin R, w j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hw_decomp j]
      _ = K := hw_sum
  have hsum_u : ∑ j, u j = K - R := by omega
  have hmain_sum :
      (∑ j : Fin R, c j * w j) =
        (∑ j : Fin R, c j * u j) + ∑ j : Fin R, c j := by
    calc
      (∑ j : Fin R, c j * w j)
          = ∑ j : Fin R, c j * (u j + 1) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [hw_decomp j]
      _ = ∑ j : Fin R, (c j * u j + c j) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [Nat.mul_add, Nat.mul_one]
      _ = (∑ j : Fin R, c j * u j) + ∑ j : Fin R, c j := by
              rw [Finset.sum_add_distrib]
  have hweighted :
      ∑ j : Fin R, c j * u j ≤ R * (∑ j : Fin R, u j) := by
    calc
      ∑ j : Fin R, c j * u j ≤ ∑ j : Fin R, R * u j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact Nat.mul_le_mul_right (u j) (Nat.sub_le R j.1)
      _ = R * (∑ j : Fin R, u j) := by
        rw [Finset.mul_sum]
  have hS_le :
      (∑ j : Fin R, c j * w j) ≤ R * (K - R) + ∑ j : Fin R, c j := by
    rw [hmain_sum]
    have hweighted' : ∑ j : Fin R, c j * u j ≤ R * (K - R) := by
      simpa [hsum_u] using hweighted
    exact Nat.add_le_add_right hweighted' _
  have hcoeff : (∑ j : Fin R, c j) * 2 = R * (R + 1) := by
    simpa [c] using coeff_sum_two R
  have hadd :
      ((∑ j : Fin R, c j * w j) * 2) + R * (R - 1) ≤ 2 * R * K := by
    have h2 : (∑ j : Fin R, c j * w j) * 2
        ≤ (R * (K - R) + ∑ j : Fin R, c j) * 2 :=
      Nat.mul_le_mul_right 2 hS_le
    have hbound :
        (R * (K - R) + ∑ j : Fin R, c j) * 2 + R * (R - 1) = 2 * R * K := by
      by_cases hR0 : R = 0
      · subst R
        simp [c]
      · apply Nat.cast_injective (R := ℤ)
        push_cast
        have hKsub : ((K - R : ℕ) : ℤ) = (K : ℤ) - (R : ℤ) := by
          omega
        have hRsub : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by
          omega
        have hcoeffz : (((∑ j : Fin R, c j) * 2 : ℕ) : ℤ) =
            ((R * (R + 1) : ℕ) : ℤ) := by
          exact_mod_cast hcoeff
        rw [hKsub, hRsub]
        push_cast at hcoeffz
        ring_nf at hcoeffz ⊢
        nlinarith
    exact (Nat.add_le_add_right h2 _).trans_eq hbound
  simpa [c] using Nat.le_sub_of_add_le hadd

/-! ## §2 The σ-bookkeeping -/

/-- `σ_N = log(N / |Q'|) / Z(N)`. The shape parameter that the
optimization shows must satisfy `σ_N ≥ 1 - O(η)` eventually. -/
noncomputable def sigmaN (N : ℕ) (Qcard : ℕ) : ℝ :=
  Real.log ((N : ℝ) / (Qcard : ℝ)) / Zscale N

lemma sigmaN_nonneg {N Qcard : ℕ}
    (hQpos : 0 < Qcard) (hQleN : Qcard ≤ N) (hZ : 0 < Zscale N) :
    0 ≤ sigmaN N Qcard := by
  have hQpos_real : 0 < (Qcard : ℝ) := Nat.cast_pos.mpr hQpos
  have hQleN_real : (Qcard : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hQleN
  have hone : 1 ≤ (N : ℝ) / (Qcard : ℝ) :=
    (one_le_div hQpos_real).2 hQleN_real
  rw [sigmaN]
  exact div_nonneg (Real.log_nonneg hone) hZ.le

private lemma product_lower_of_chain_stop {N : ℕ} {D : PrunedData N}
    {S : ChainState N D}
    (hStop : (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) :
    (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) := by
  rcases hStop with hProd | hW
  · exact hProd
  · exact S.productP_lower_of_W_eq_K hW

private lemma one_sub_le_of_sq_lower
    {η δ σ : ℝ} (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (hδ_le : δ ≤ η) (hσ_nonneg : 0 ≤ σ)
    (hsq : 1 - δ ≤ σ ^ 2) :
    1 - η ≤ σ := by
  have hone_sub_nonneg : 0 ≤ 1 - η := by linarith
  have hsquare_left : (1 - η) ^ 2 ≤ 1 - δ := by
    have hsq_le_linear : (1 - η) ^ 2 ≤ 1 - η := by
      nlinarith [hη_nonneg, hη_le_one]
    linarith
  have hsquare : (1 - η) ^ 2 ≤ σ ^ 2 := hsquare_left.trans hsq
  exact (sq_le_sq₀ hone_sub_nonneg hσ_nonneg).1 hsquare

lemma card_le_of_sigma_lower {η : ℝ} {N Qcard : ℕ}
    (hN : 0 < N) (hQ : 0 < Qcard) (hZ : 0 < Zscale N)
    (hsigma : 1 - η ≤ sigmaN N Qcard) :
    (Qcard : ℝ) ≤ (N : ℝ) * Lscale (-(1 - η)) N := by
  have hQreal : 0 < (Qcard : ℝ) := by exact_mod_cast hQ
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hratio_pos : 0 < (N : ℝ) / (Qcard : ℝ) := div_pos hNreal hQreal
  have hlog :
      (1 - η) * Zscale N ≤ Real.log ((N : ℝ) / (Qcard : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hsigma hZ.le
    rw [sigmaN, div_mul_cancel₀ _ hZ.ne'] at hmul
    exact hmul
  have hexp_le_ratio :
      Real.exp ((1 - η) * Zscale N) ≤ (N : ℝ) / (Qcard : ℝ) :=
    (Real.le_log_iff_exp_le hratio_pos).1 hlog
  have hmulQ :
      (Qcard : ℝ) * Real.exp ((1 - η) * Zscale N) ≤ (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hexp_le_ratio hQreal.le
    rw [div_mul_cancel₀ _ hQreal.ne'] at hmul
    simpa [mul_comm] using hmul
  have hcancel :
      Real.exp ((1 - η) * Zscale N) *
          Real.exp (-((1 - η) * Zscale N)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    (Qcard : ℝ)
        = ((Qcard : ℝ) * Real.exp ((1 - η) * Zscale N)) *
            Real.exp (-((1 - η) * Zscale N)) := by
          rw [mul_assoc, hcancel, mul_one]
    _ ≤ (N : ℝ) * Real.exp (-((1 - η) * Zscale N)) := by
          exact mul_le_mul_of_nonneg_right hmulQ (Real.exp_pos _).le
    _ = (N : ℝ) * Lscale (-(1 - η)) N := by
          rw [Lscale]
          congr 1
          ring_nf

set_option maxHeartbeats 2000000

/-- **Sigma lower bound** (PDF Section 5). For every `η > 0`, eventually
any pruned family with cardinality `Qcard` derived from a chain with
parameters `(c, d) ∈ [0, 3]²` satisfies `1 - η ≤ c σ_N - c² / 4 + η`,
hence `σ_N ≥ 1 - O(η)`. -/
theorem sigma_lower_bound :
    ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
      ∀ Qcard : ℕ, 1 ≤ Qcard →
        (∃ D : PrunedData N, D.Q.card = Qcard) →
        1 - η ≤ sigmaN N Qcard := by
  intro η hη
  let ε : ℝ := η / 8
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  filter_upwards [bfv_omega_count_input ε hε,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge (8 / η) (by positivity),
      eventually_sqrt_loglog_ge (96 / η),
      eventually_log_chainLambda_le_mul_loglog (η / 144) (by positivity)] with
    N hCount hNlarge_nat hMlarge hSqrtLogLogLarge hLogLambdaSmall
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hZpos : 0 < Zscale N := Zscale_pos_of_exp_one_lt_nat hNlarge
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hMZ : Mscale N * Zscale N = Real.log (N : ℝ) :=
    Mscale_mul_Zscale_eq_log hNlarge
  have hZdivM : Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) :=
    Zscale_div_Mscale_eq_loglog hNlarge
  intro Qcard _hQcard hD
  rcases hD with ⟨D, hDcard⟩
  have hsigma_nonneg : 0 ≤ sigmaN N Qcard := by
    have hQleN : Qcard ≤ N := by
      rw [← hDcard]
      exact D.card_le_N
    exact sigmaN_nonneg (Nat.succ_le_iff.mp _hQcard) hQleN hZpos
  rcases chain_inequality N D ε hε hCount with
    ⟨R, S, hR, hRpos, hRle, hStop, hBlocks, hProdUpper⟩
  have hProdLower : (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) :=
    product_lower_of_chain_stop hStop
  have hProdUpperBound : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S := by
    simpa [chainProductBoundWithLosses, hR] using hProdUpper
  have hLogProduct :
      Real.log ((N : ℝ) * Lscale (-2) N) ≤
        Real.log (chainProductBoundWithLosses ε S) := by
    have hLowerPos : 0 < (N : ℝ) * Lscale (-2) N := by
      exact mul_pos (by exact_mod_cast D.N_pos) (Lscale_pos (-2) N)
    exact Real.log_le_log hLowerPos (hProdLower.trans hProdUpperBound)
  have hLogProductExpanded :
      Real.log (N : ℝ) - 2 * Zscale N ≤
        Real.log (chainProductBoundWithLosses ε S) := by
    have hLogLower :
        Real.log ((N : ℝ) * Lscale (-2) N) =
          Real.log (N : ℝ) - 2 * Zscale N := by
      rw [log_nat_mul_Lscale D.N_pos (-2)]
      ring
    rwa [hLogLower] at hLogProduct
  have hLogChainExpanded :
      Real.log (N : ℝ) - 2 * Zscale N ≤
        (R : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
          (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
          ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
          2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
          ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
    rw [log_chainProductBoundWithLosses ε S] at hLogProductExpanded
    simpa [hR] using hLogProductExpanded
  have hSigmaLog :
      Real.log ((N : ℝ) / (D.Q.card : ℝ)) =
        sigmaN N Qcard * Zscale N := by
    rw [sigmaN, ← hDcard]
    field_simp [hZpos.ne']
  have hLogChainNormalized :
      Mscale N - 2 ≤
        (R : ℝ) * sigmaN N Qcard +
          (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
          ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
          (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
          (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N := by
    have hExpandedSigma :
        Real.log (N : ℝ) - 2 * Zscale N ≤
          (R : ℝ) * (sigmaN N Qcard * Zscale N) +
            (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
            ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
            2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
            ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
      simpa [hSigmaLog] using hLogChainExpanded
    have h :
        (Mscale N - 2) * Zscale N ≤
          ((R : ℝ) * sigmaN N Qcard +
            (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
            ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
            (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
            (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N) *
              Zscale N := by
      calc
        (Mscale N - 2) * Zscale N
            = Real.log (N : ℝ) - 2 * Zscale N := by
                rw [← hMZ]
                ring
        _ ≤ (R : ℝ) * (sigmaN N Qcard * Zscale N) +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ))) +
              2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
              ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) :=
            hExpandedSigma
        _ = ((R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
              (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
              (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) /
                Zscale N) * Zscale N := by
            rw [← hZdivM]
            field_simp [hMpos.ne', hZpos.ne']
    have hdiv := div_le_div_of_nonneg_right h hZpos.le
    field_simp [hZpos.ne'] at hdiv
    field_simp [hMpos.ne']
    nlinarith [hdiv, hMpos]
  have hTbasic : chainT S ≤ S.r * D.K := S.chainT_le_r_mul_K
  have hTbasicR : chainT S ≤ R * D.K := by
    simpa [hR] using hTbasic
  have hTquad : ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) :=
    S.chainT_add_W_real_quadratic_bound hBlocks
  have hTquadK : ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1) := by
    have hWle : (S.W : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast S.W_le_K
    have hRnonneg : 0 ≤ (R : ℝ) := by positivity
    rw [← hR]
    nlinarith [hTquad, hWle, hRnonneg]
  have hTterm :
      ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) ≤
        (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
          (4 * Mscale N) := by
    calc
      ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N)
          = (((chainT S + S.W : ℕ) : ℝ) * 2) * (1 / (4 * Mscale N)) := by
              field_simp [hMpos.ne']
              ring
      _ ≤ (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) *
            (1 / (4 * Mscale N)) := by
              exact mul_le_mul_of_nonneg_right hTquadK (by positivity)
      _ = (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
            (4 * Mscale N) := by ring
  let sqrtE : ℝ := (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N
  let lambdaE : ℝ :=
    (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N
  have hLogChainQuadratic :
      Mscale N - 2 ≤
        (R : ℝ) * sigmaN N Qcard -
          ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
          (R : ℝ) * ε + sqrtE + lambdaE := by
    calc
      Mscale N - 2
          ≤ (R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
              sqrtE + lambdaE :=
            hLogChainNormalized
      _ ≤ (R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
                (4 * Mscale N) + sqrtE + lambdaE := by
            let A : ℝ :=
              (R : ℝ) * sigmaN N Qcard +
                (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε)
            let B : ℝ := sqrtE + lambdaE
            have hmid :
                A + ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) ≤
                  A + (2 * (R : ℝ) * (D.K : ℝ) -
                    (R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) :=
              by
                have hmid' := add_le_add_left hTterm A
                linarith
            have hmidB := add_le_add_right hmid B
            dsimp [A, B] at hmidB
            linarith
      _ = (R : ℝ) * sigmaN N Qcard -
            ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
            (R : ℝ) * ε + sqrtE + lambdaE := by
            have hbase :
                (R : ℝ) * sigmaN N Qcard +
                    (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
                    (2 * (R : ℝ) * (D.K : ℝ) -
                        (R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) =
                  (R : ℝ) * sigmaN N Qcard -
                    ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
                    (R : ℝ) * ε :=
              log_chain_quadratic_algebra (Mscale N) (R : ℝ) (D.K : ℝ)
                (sigmaN N Qcard) ε hMpos.ne'
            rw [hbase]
  let c : ℝ := (R : ℝ) / Mscale N
  have hc_pos : 0 < c := by
    dsimp [c]
    have hRpos_real : 0 < (R : ℝ) := by exact_mod_cast hRpos
    exact div_pos hRpos_real hMpos
  have hc_le_three : c ≤ 3 := by
    dsimp [c]
    have hRleK_real : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hRle
    have hRle3M : (R : ℝ) ≤ 3 * Mscale N := hRleK_real.trans D.K_bound
    exact (div_le_iff₀ hMpos).2 hRle3M
  let sqrtLoss : ℝ := sqrtE / Mscale N
  let lambdaLoss : ℝ := lambdaE / Mscale N
  have hLogChainShape :
      (Mscale N - 2) / Mscale N ≤
        c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
          sqrtLoss + lambdaLoss := by
    have hdiv := div_le_div_of_nonneg_right hLogChainQuadratic hMpos.le
    calc
      (Mscale N - 2) / Mscale N
          ≤ ((R : ℝ) * sigmaN N Qcard -
            ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
            (R : ℝ) * ε + sqrtE + lambdaE) / Mscale N := hdiv
      _ = c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
            sqrtLoss + lambdaLoss := by
              dsimp [c, sqrtLoss, lambdaLoss]
              exact log_chain_shape_algebra (Mscale N) (R : ℝ) (sigmaN N Qcard)
                ε sqrtE lambdaE hMpos.ne'
  have hsigma_sq_shape :
      (Mscale N - 2) / Mscale N ≤
        (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
          sqrtLoss + lambdaLoss := by
    calc
      (Mscale N - 2) / Mscale N
          ≤ c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss :=
            hLogChainShape
      _ ≤ (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss := by
            simpa [add_assoc] using
              add_le_add_right (quad_bound c (sigmaN N Qcard))
                (c / (4 * Mscale N) + c * ε + sqrtLoss + lambdaLoss)
  have hsigma_sq_shape_three :
      (Mscale N - 2) / Mscale N ≤
        (sigmaN N Qcard) ^ 2 + 3 / (4 * Mscale N) + 3 * ε +
          sqrtLoss + lambdaLoss := by
    have hsmall1 : c / (4 * Mscale N) ≤ 3 / (4 * Mscale N) := by
      exact div_le_div_of_nonneg_right hc_le_three (by positivity)
    have hsmall2 : c * ε ≤ 3 * ε :=
      mul_le_mul_of_nonneg_right hc_le_three hε.le
    calc
      (Mscale N - 2) / Mscale N
          ≤ (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss :=
            hsigma_sq_shape
      _ ≤ (sigmaN N Qcard) ^ 2 + 3 / (4 * Mscale N) + 3 * ε +
              sqrtLoss + lambdaLoss := by
            have herr :
                c / (4 * Mscale N) + c * ε ≤
                  3 / (4 * Mscale N) + 3 * ε :=
              add_le_add hsmall1 hsmall2
            linarith
  have hsigma_sq_lower :
      1 - (2 / Mscale N + 3 / (4 * Mscale N) + 3 * ε +
          sqrtLoss + lambdaLoss) ≤
        (sigmaN N Qcard) ^ 2 := by
    have hleft : (Mscale N - 2) / Mscale N = 1 - 2 / Mscale N :=
      (one_sub_two_div_eq (Mscale N) hMpos.ne').symm
    linarith [hsigma_sq_shape_three, hleft]
  by_cases hη_big : 1 ≤ η
  · have htarget : 1 - η ≤ 0 := by linarith
    exact htarget.trans hsigma_nonneg
  have hη_le_one : η ≤ 1 := le_of_lt (not_le.mp hη_big)
  let δN : ℝ :=
    2 / Mscale N + 3 / (4 * Mscale N) + 3 * ε + sqrtLoss + lambdaLoss
  have hfinish_of_error (hδN : δN ≤ η) : 1 - η ≤ sigmaN N Qcard := by
    exact one_sub_le_of_sq_lower hη.le hη_le_one hδN hsigma_nonneg (by
      simpa [δN] using hsigma_sq_lower)
  have hδN_le : δN ≤ η := by
    have hApos : 0 < (8 : ℝ) / η := by positivity
    have hinvM_raw : 1 / Mscale N ≤ 1 / (8 / η) :=
      one_div_le_one_div_of_le hApos hMlarge
    have hinvM : 1 / Mscale N ≤ η / 8 := by
      convert hinvM_raw using 1
      field_simp [hη.ne']
    dsimp [δN, ε]
    have hterm1 : 2 / Mscale N ≤ η / 4 := by
      have hmul := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ (2 : ℝ) by norm_num)
      convert hmul using 1 <;> ring
    have hterm2 : 3 / (4 * Mscale N) ≤ 3 * η / 32 := by
      have hmul := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ (3 / 4 : ℝ) by norm_num)
      convert hmul using 1
      · field_simp [hMpos.ne']
      · ring
    have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
      Real.log_pos ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hNlarge)).2 hNlarge)
    have hsqrtlog_pos : 0 < Real.sqrt (Real.log (N : ℝ)) := by
      have hlog_pos : 0 < Real.log (N : ℝ) :=
        zero_lt_one.trans ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hNlarge)).2 hNlarge)
      rw [Real.sqrt_pos]
      exact hlog_pos
    have hsqrtloglog_pos :
        0 < Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      have hlarge_pos : 0 < (96 : ℝ) / η := by positivity
      exact hlarge_pos.trans_le hSqrtLogLogLarge
    have hRle3M : (R : ℝ) ≤ 3 * Mscale N := by
      have hRleK_real : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hRle
      exact hRleK_real.trans D.K_bound
    have hsqrtLoss_le : sqrtLoss ≤ η / 16 := by
      have hfactor_nonneg :
          0 ≤ 2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N) := by
        positivity
      calc
        sqrtLoss
            = (R : ℝ) *
                (2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N)) := by
              dsimp [sqrtLoss, sqrtE]
              field_simp [hZpos.ne', hMpos.ne']
        _ ≤ (3 * Mscale N) *
              (2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N)) := by
              exact mul_le_mul_of_nonneg_right hRle3M hfactor_nonneg
        _ = 6 / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
              rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
              field_simp [hMpos.ne', hsqrtlog_pos.ne', hsqrtloglog_pos.ne']
              ring
        _ ≤ 6 / (96 / η) := by
              exact div_le_div_of_nonneg_left (by norm_num)
                (by positivity) hSqrtLogLogLarge
        _ = η / 16 := by
              field_simp [hη.ne']
              ring
    have hTplus_le_RK :
        (((chainT S + S.W : ℕ) : ℝ)) ≤ (R : ℝ) * (D.K : ℝ) := by
      have hRge_one_real : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRpos
      have hquad_nonneg : 0 ≤ (R : ℝ) * ((R : ℝ) - 1) := by
        nlinarith [hRge_one_real]
      have hT2_le_2RK :
          (((chainT S + S.W : ℕ) : ℝ) * 2) ≤
            2 * (R : ℝ) * (D.K : ℝ) := by
        nlinarith [hTquadK, hquad_nonneg]
      nlinarith
    have hTplus_le_9M2 :
        (((chainT S + S.W : ℕ) : ℝ)) ≤ 9 * (Mscale N) ^ 2 := by
      have hKle3M : (D.K : ℝ) ≤ 3 * Mscale N := D.K_bound
      have hRnonneg : 0 ≤ (R : ℝ) := by positivity
      have hKnonneg : 0 ≤ (D.K : ℝ) := by positivity
      have hRK_le : (R : ℝ) * (D.K : ℝ) ≤ (3 * Mscale N) * (3 * Mscale N) :=
        mul_le_mul hRle3M hKle3M hKnonneg (by positivity)
      nlinarith [hTplus_le_RK, hRK_le]
    have hlambdaLog_le :
        Real.log (chainLambda D) ≤
          (η / 144) * Real.log (Real.log (N : ℝ)) :=
      hLogLambdaSmall D
    have hlambdaLoss_le : lambdaLoss ≤ η / 16 := by
      have hcoef_nonneg :
          0 ≤ (η / 144) * Real.log (Real.log (N : ℝ)) := by positivity
      have hTnonneg : 0 ≤ (((chainT S + S.W : ℕ) : ℝ)) := by positivity
      have hnum_le :
          (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) ≤
            (9 * (Mscale N) ^ 2) *
              ((η / 144) * Real.log (Real.log (N : ℝ))) := by
        have hlog_scaled :
            (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) ≤
              (((chainT S + S.W : ℕ) : ℝ) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hlambdaLog_le hTnonneg
        have hT_scaled :
            (((chainT S + S.W : ℕ) : ℝ) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) ≤
              (9 * (Mscale N) ^ 2) *
                ((η / 144) * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hTplus_le_9M2 hcoef_nonneg
        exact hlog_scaled.trans hT_scaled
      have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
      calc
        lambdaLoss
            = (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) /
                (Zscale N * Mscale N) := by
              dsimp [lambdaLoss, lambdaE]
              field_simp [hZpos.ne', hMpos.ne']
        _ ≤ ((9 * (Mscale N) ^ 2) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) /
                (Zscale N * Mscale N) := by
              exact div_le_div_of_nonneg_right hnum_le
                (mul_nonneg hZpos.le hMpos.le)
        _ = η / 16 := by
              rw [← hMll]
              field_simp [hMpos.ne', hloglog_pos.ne']
              ring
    have hmain_le :
        2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8) ≤
          (23 / 32) * η := by
      calc
        2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8)
          ≤ η / 4 + 3 * η / 32 + 3 * (η / 8) := by
            gcongr
        _ = (23 / 32) * η := by ring
    calc
      2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8) + sqrtLoss + lambdaLoss
          ≤ (23 / 32) * η + η / 16 + η / 16 := by
            linarith [hmain_le, hsqrtLoss_le, hlambdaLoss_le]
      _ = (27 / 32) * η := by ring
      _ ≤ η := by
            exact mul_le_of_le_one_left hη.le (by norm_num)
  exact hfinish_of_error hδN_le

/-! ## §3 The upper bound -/

/-- **Upper bound for f.** From the chain inequality and σ-optimization,
`f(N) ≤ N · L(-(1 - ε), N)` for every `ε > 0`, eventually. -/
theorem f_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N := by
  intro ε hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have h2δ : 2 * δ ≤ ε := by
    dsimp [δ]
    linarith
  filter_upwards [bfv_pruning_input δ hδ, sigma_lower_bound δ hδ,
      eventually_Zscale_pos] with N hPrune hSigma hZ
  classical
  rcases exists_admissible_card_f N with ⟨Q, hQadm, hQcard⟩
  rcases hQadm.2 with ⟨a, ha⟩
  have hQlarge : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-δ) N := by
    rw [hQcard]
    calc
      (f N : ℝ) * Lscale (-δ) N ≤ (f N : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left (Lscale_neg_le_one hδ.le N) (by positivity)
      _ = (f N : ℝ) := by ring
  rcases hPrune Q a hQadm.1 ha hQlarge with ⟨D, hDlower⟩
  have hSigmaD :
      1 - δ ≤ sigmaN N D.Q.card :=
    hSigma D.Q.card (Nat.succ_le_of_lt D.card_pos) ⟨D, rfl⟩
  have hDupper :
      (D.Q.card : ℝ) ≤ (N : ℝ) * Lscale (-(1 - δ)) N :=
    card_le_of_sigma_lower D.N_pos D.card_pos hZ hSigmaD
  have hf_to_D :
      (f N : ℝ) ≤ (D.Q.card : ℝ) * Lscale δ N := by
    calc
      (f N : ℝ)
          = ((f N : ℝ) * Lscale (-δ) N) * Lscale δ N := by
              rw [mul_assoc, Lscale_neg_mul, mul_one]
      _ ≤ (D.Q.card : ℝ) * Lscale δ N := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [hQcard] using hDlower) (Lscale_nonneg δ N)
  calc
    (f N : ℝ) ≤ (D.Q.card : ℝ) * Lscale δ N := hf_to_D
    _ ≤ ((N : ℝ) * Lscale (-(1 - δ)) N) * Lscale δ N := by
          exact mul_le_mul_of_nonneg_right hDupper (Lscale_nonneg δ N)
    _ = (N : ℝ) * (Lscale (-(1 - δ)) N * Lscale δ N) := by ring
    _ = (N : ℝ) * Lscale (-(1 - δ) + δ) N := by
          rw [Lscale_add]
    _ = (N : ℝ) * Lscale (-(1 - 2 * δ)) N := by
          congr 1
          congr 1
          ring
    _ ≤ (N : ℝ) * Lscale (-(1 - ε)) N := by
          exact mul_le_mul_of_nonneg_left
            (Lscale_mono_in_alpha (by linarith) N) (by positivity)

end Erdos202
