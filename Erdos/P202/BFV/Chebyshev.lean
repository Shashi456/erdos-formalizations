/-
Erdős Problem 202 — Chebyshev-style dyadic-interval prime cardinality bound.

# Status

This file proves the prime-supply theorem consumed by the BFV lower path
construction.  The lower bound has a fixed positive Chebyshev constant, which
is enough for the `Lscale (-(1 + ε), N)` BFV lower-bound target.

# Classical content

Chebyshev (1850) proved that there exist absolute constants `c_1, c_2 > 0`
with `c_1 · y / log y ≤ π(y) ≤ c_2 · y / log y`. Subtracting gives, for
some absolute `c > 0`,
  `π(2y) − π(y) ≥ c · y / log y`  for all sufficiently large `y`.

Mathlib `v4.27.0` already has Chebyshev's `θ`-function bounds
(`Nat.theta_le`, `Nat.theta_le_id`, `Nat.id_lt_theta`, etc.) and the
prime-counting function `Nat.primeCounting`. What is NOT packaged is the
Chebyshev-style dyadic-interval lower bound `π(2y) − π(y) ≥ c · y / log y`
nor its `(1 − ε) · y / log y` PNT-strength refinement.

The earlier `(1 - ε)` PNT-strength target has been replaced by the fixed
positive constant `dyadicPrimeIntervalConstant = log 4 / 16`.  The proof below
uses central-binomial/Bertrand-style estimates rather than PNT.

# Where this is consumed

* `Erdos.P202.BFV.Chebyshev.dyadicPrimeInterval_card_lower_bound`
* downstream: `Erdos.P202.BFV.LowerPathConstruction.lowerPath_f_lower_bound_eventually`
  → `Erdos.P202.BFV.LowerBoundInput.bfv_lower_bound_theorem`
  → supplies the historical `Erdos202.bfv_lower_bound_input` interface.
-/

import Mathlib
import Erdos.P202.BFV.PrimeIntervals

namespace Erdos202

open Filter Finset

/-- Central-binomial upper bound with the actual number of primes in `(n, 2n]`
kept as a factor.  This is the quantitative version of the Bertrand proof:
Mathlib's `centralBinom_le_of_no_bertrand_prime` is the special case where
that interval has cardinality zero. -/
theorem centralBinom_le_mul_pow_dyadicPrimeInterval_card (n : ℕ)
    (hn : 2 < n) :
    n.centralBinom ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
        (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  classical
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt hn
  have n2_pos : 1 ≤ 2 * n := mul_pos (by norm_num : 0 < 2) n_pos
  let S : Finset ℕ := (Finset.range (2 * n + 1)).filter Nat.Prime
  let f : ℕ → ℕ := fun p => p ^ n.centralBinom.factorization p
  let A : Finset ℕ := S.filter (fun p => p ≤ Nat.sqrt (2 * n))
  let B : Finset ℕ := S.filter (fun p => ¬ p ≤ Nat.sqrt (2 * n))
  let B₁ : Finset ℕ := B.filter (fun p => p ≤ 2 * n / 3)
  let B₂ : Finset ℕ := B.filter (fun p => ¬ p ≤ 2 * n / 3)
  let C : Finset ℕ := B₂.filter (fun p => p ≤ n)
  let D : Finset ℕ := B₂.filter (fun p => ¬ p ≤ n)
  have hfilter :
      (∏ p ∈ S, f p) =
        ∏ p ∈ Finset.range (2 * n + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _hp h => ?_
    contrapose! h
    dsimp [f]
    rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, pow_zero]
  have hfull : n.centralBinom = ∏ p ∈ S, f p := by
    calc
      n.centralBinom = ∏ p ∈ Finset.range (2 * n + 1), f p := by
        simpa [f] using (Nat.prod_pow_factorization_centralBinom n).symm
      _ = ∏ p ∈ S, f p := hfilter.symm
  have hsplitA :
      (∏ p ∈ S, f p) = (∏ p ∈ A, f p) * (∏ p ∈ B, f p) := by
    simpa [A, B] using
      (Finset.prod_filter_mul_prod_filter_not S
        (fun p => p ≤ Nat.sqrt (2 * n)) f).symm
  have hsplitB :
      (∏ p ∈ B, f p) = (∏ p ∈ B₁, f p) * (∏ p ∈ B₂, f p) := by
    simpa [B₁, B₂] using
      (Finset.prod_filter_mul_prod_filter_not B
        (fun p => p ≤ 2 * n / 3) f).symm
  have hsplitC :
      (∏ p ∈ B₂, f p) = (∏ p ∈ C, f p) * (∏ p ∈ D, f p) := by
    simpa [C, D] using
      (Finset.prod_filter_mul_prod_filter_not B₂
        (fun p => p ≤ n) f).symm
  have hsmall : (∏ p ∈ A, f p) ≤ (2 * n) ^ Nat.sqrt (2 * n) := by
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ 2 * n)).trans ?_
    · exact Nat.pow_factorization_choose_le (mul_pos (by norm_num : 0 < 2) n_pos)
    have hcard : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun p hp => ?_).trans hcard.le)
    obtain ⟨hpS, hple⟩ := Finset.mem_filter.1 hp
    obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
    exact Finset.mem_Icc.mpr ⟨hpprime.one_lt.le, hple⟩
  have hmid : (∏ p ∈ B₁, f p) ≤ 4 ^ (2 * n / 3) := by
    refine le_trans ?_ (primorial_le_4_pow (2 * n / 3))
    have htoP : (∏ p ∈ B₁, f p) ≤ ∏ p ∈ B₁, p := by
      refine Finset.prod_le_prod' fun p hp => ?_
      obtain ⟨hpB, _hple_mid⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpS, hp_not_small⟩ := Finset.mem_filter.1 hpB
      obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
      dsimp [f]
      refine (pow_right_mono₀ hpprime.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one
        (Nat.sqrt_lt'.mp (Nat.lt_of_not_ge hp_not_small))
    refine htoP.trans ?_
    unfold primorial
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro p hp
      obtain ⟨hpB, hple_mid⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpS, _hp_not_small⟩ := Finset.mem_filter.1 hpB
      obtain ⟨_hrange, hpprime⟩ := Finset.mem_filter.1 hpS
      exact Finset.mem_filter.2
        ⟨Finset.mem_range.2 (Nat.lt_succ_iff.2 hple_mid), hpprime⟩
    · intro p hpT _hpnot
      exact (Finset.mem_filter.1 hpT).2.one_lt.le
  have hgap : (∏ p ∈ C, f p) = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    obtain ⟨hpB₂, hple_n⟩ := Finset.mem_filter.1 hp
    obtain ⟨_hpB, hp_not_mid⟩ := Finset.mem_filter.1 hpB₂
    have htwo_lt_three :
        2 * n < 3 * p := by
      have hlt : 2 * n / 3 < p := Nat.lt_of_not_ge hp_not_mid
      have h := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).1 hlt
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hfac0 :
        n.centralBinom.factorization p = 0 :=
      Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hple_n htwo_lt_three
    simp [f, hfac0]
  have hDsub : D ⊆ (Finset.Ioc n (2 * n)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpB₂, hp_not_le_n⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpB, _hp_not_mid⟩ := Finset.mem_filter.1 hpB₂
    obtain ⟨hpS, _hp_not_small⟩ := Finset.mem_filter.1 hpB
    obtain ⟨hrange, hpprime⟩ := Finset.mem_filter.1 hpS
    have hle_two : p ≤ 2 * n := by
      exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hrange)
    have hn_lt : n < p := Nat.lt_of_not_ge hp_not_le_n
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hn_lt, hle_two⟩, hpprime⟩
  have hinterval :
      (∏ p ∈ D, f p) ≤
        (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
    refine (Finset.prod_le_prod' fun p _hp => (?_ : f p ≤ 2 * n)).trans ?_
    · exact Nat.pow_factorization_choose_le (mul_pos (by norm_num : 0 < 2) n_pos)
    rw [Finset.prod_const]
    exact pow_right_mono₀ n2_pos (Finset.card_le_card hDsub)
  calc
    n.centralBinom = ∏ p ∈ S, f p := hfull
    _ = (∏ p ∈ A, f p) *
          ((∏ p ∈ B₁, f p) * ((∏ p ∈ C, f p) * (∏ p ∈ D, f p))) := by
            rw [hsplitA, hsplitB, hsplitC]
    _ = (∏ p ∈ A, f p) * ((∏ p ∈ B₁, f p) * (∏ p ∈ D, f p)) := by
            rw [hgap]
            simp
    _ ≤ (2 * n) ^ Nat.sqrt (2 * n) *
          (4 ^ (2 * n / 3) *
            (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card) := by
            gcongr
    _ = (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
          (2 * n) ^ ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
            ac_rfl

lemma dyadicPrimeInterval_nat_card_mul_log_lower_of_estimates
    (n : ℕ) (hn4 : 4 ≤ n)
    (hlogn : Real.log (n : ℝ) ≤ (Real.log 4 / 24) * (n : ℝ))
    (hsqrtlog :
      Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        (Real.log 4 / 24) * (n : ℝ)) :
    (Real.log 4 / 4) * (n : ℝ) ≤
      (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) *
        Real.log (2 * (n : ℝ)) := by
  classical
  let K : ℕ := ((Finset.Ioc n (2 * n)).filter Nat.Prime).card
  have hn2 : 2 < n := by omega
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn4
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have h2n_pos_real : 0 < (2 * (n : ℝ)) := by positivity
  have h2n_cast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_num
  have hn_ge_four_real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hlog2n_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hcentral :=
    centralBinom_le_mul_pow_dyadicPrimeInterval_card n hn2
  have hfour : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n hn4
  have hlt_nat :
      4 ^ n <
        n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
          (2 * n) ^ K) := by
    exact hfour.trans_le (Nat.mul_le_mul_left n hcentral)
  have hlt_real :
      (4 : ℝ) ^ n <
        (n : ℝ) *
          (((2 * (n : ℝ)) ^ Nat.sqrt (2 * n)) *
            ((4 : ℝ) ^ (2 * n / 3)) *
            ((2 * (n : ℝ)) ^ K)) := by
    exact_mod_cast hlt_nat
  have hlog_le := Real.log_le_log (by positivity : (0 : ℝ) < (4 : ℝ) ^ n) hlt_real.le
  have hlog_expand :
      Real.log
        ((n : ℝ) *
          (((2 * (n : ℝ)) ^ Nat.sqrt (2 * n)) *
            ((4 : ℝ) ^ (2 * n / 3)) *
            ((2 * (n : ℝ)) ^ K)))
        =
        Real.log (n : ℝ) +
          (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) +
          ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    rw [Real.log_mul hn_pos.ne']
    · rw [Real.log_mul]
      · rw [Real.log_mul]
        · rw [Real.log_pow, Real.log_pow, Real.log_pow]
          ring
        · exact pow_ne_zero _ h2n_pos_real.ne'
        · exact pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)
      · exact mul_ne_zero (pow_ne_zero _ h2n_pos_real.ne')
          (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0))
      · exact pow_ne_zero _ h2n_pos_real.ne'
    · exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ h2n_pos_real.ne')
          (pow_ne_zero _ (by norm_num : (4 : ℝ) ≠ 0)))
        (pow_ne_zero _ h2n_pos_real.ne')
  have hlog_main :
      (n : ℝ) * Real.log 4 ≤
        Real.log (n : ℝ) +
          (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) +
          ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    have hleft : Real.log ((4 : ℝ) ^ n) = (n : ℝ) * Real.log 4 := by
      rw [Real.log_pow]
    linarith
  have hsqrt_cast :
      (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    rw [← h2n_cast]
    exact_mod_cast Real.nat_sqrt_le_real_sqrt
  have hsqrt_term :
      (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) ≤
        Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hsqrt_cast hlog2n_nonneg
  have hdiv_term :
      ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 ≤
        ((2 : ℝ) * (n : ℝ) / 3) * Real.log 4 := by
    have hdiv : ((2 * n / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / 3 :=
      Nat.cast_div_le.trans_eq (by norm_num)
    rw [h2n_cast] at hdiv
    exact mul_le_mul_of_nonneg_right hdiv hlog4_pos.le
  have hmain' :
      (n : ℝ) * Real.log 4 ≤
        Real.log (n : ℝ) +
          Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) +
          ((2 : ℝ) * (n : ℝ) / 3) * Real.log 4 +
          (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    linarith
  have hsmall_sum :
      Real.log (n : ℝ) +
        Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        (Real.log 4 / 12) * (n : ℝ) := by
    linarith
  have hresult :
      (Real.log 4 / 4) * (n : ℝ) ≤
        (K : ℝ) * Real.log (2 * (n : ℝ)) := by
    nlinarith
  simpa [K] using hresult

lemma eventually_log_nat_le_const_mul_self (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ δ * (n : ℝ) := by
  have hsmall :
      (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
        fun n : ℕ => (n : ℝ) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ] with n hn
  have hright_norm : ‖(n : ℝ)‖ = (n : ℝ) := by
    exact Real.norm_of_nonneg (Nat.cast_nonneg n)
  have hlog_le_norm :
      Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := by
    simpa [Real.norm_eq_abs] using le_abs_self (Real.log (n : ℝ))
  calc
    Real.log (n : ℝ) ≤ ‖Real.log (n : ℝ)‖ := hlog_le_norm
    _ ≤ δ * ‖(n : ℝ)‖ := hn
    _ = δ * (n : ℝ) := by rw [hright_norm]

lemma eventually_sqrt_two_mul_log_two_mul_le_const_mul_self
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) ≤
        δ * (n : ℝ) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have htwo_atTop :
      Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      tendsto_natCast_atTop_atTop
  have hsmall :
      (fun n : ℕ => Real.log (2 * (n : ℝ))) =o[atTop]
        fun n : ℕ => Real.sqrt (2 * (n : ℝ)) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)).comp_tendsto
          htwo_atTop
    simpa [Real.sqrt_eq_rpow, mul_comm, mul_left_comm, mul_assoc] using h
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ2] with n hn
  set x : ℝ := 2 * (n : ℝ)
  have hx_nonneg : 0 ≤ x := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_norm : ‖Real.sqrt x‖ = Real.sqrt x :=
    Real.norm_of_nonneg hsqrt_nonneg
  have hlog_le : Real.log x ≤ (δ / 2) * Real.sqrt x := by
    have hlog_le_norm : Real.log x ≤ ‖Real.log x‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (Real.log x)
    calc
      Real.log x ≤ ‖Real.log x‖ := hlog_le_norm
      _ ≤ (δ / 2) * ‖Real.sqrt x‖ := by simpa [x] using hn
      _ = (δ / 2) * Real.sqrt x := by rw [hsqrt_norm]
  calc
    Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ))
        = Real.sqrt x * Real.log x := by simp [x]
    _ ≤ Real.sqrt x * ((δ / 2) * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left hlog_le hsqrt_nonneg
    _ = (δ / 2) * (Real.sqrt x) ^ 2 := by ring
    _ = (δ / 2) * x := by rw [Real.sq_sqrt hx_nonneg]
    _ = δ * (n : ℝ) := by simp [x]; ring

theorem dyadicPrimeInterval_nat_card_lower_bound_eventually :
    ∀ᶠ n : ℕ in atTop,
      Nat.floor (((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ))) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card := by
  filter_upwards [
      Filter.eventually_ge_atTop 4,
      eventually_log_nat_le_const_mul_self (Real.log 4 / 24)
        (by positivity),
      eventually_sqrt_two_mul_log_two_mul_le_const_mul_self
        (Real.log 4 / 24) (by positivity)] with n hn4 hlogn hsqrtlog
  have hmul :=
    dyadicPrimeInterval_nat_card_mul_log_lower_of_estimates n hn4 hlogn hsqrtlog
  have hlog_pos : 0 < Real.log (2 * (n : ℝ)) := by
    have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    exact Real.log_pos (by nlinarith)
  have hdiv :
      ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) ≤
        (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) := by
    exact (div_le_iff₀ hlog_pos).2 hmul
  exact Nat.floor_le_of_le hdiv

/-- A fixed Chebyshev constant supplied by the elementary central-binomial
argument above.  The value is intentionally conservative; the BFV lower
construction only needs some positive absolute constant. -/
noncomputable def dyadicPrimeIntervalConstant : ℝ :=
  Real.log 4 / 16

lemma dyadicPrimeIntervalConstant_pos : 0 < dyadicPrimeIntervalConstant := by
  unfold dyadicPrimeIntervalConstant
  positivity

/-- Chebyshev-strength lower bound for the number of primes in a dyadic
interval.  This is weaker than the PNT-strength `(1 - ε)` estimate, but it is
enough for the BFV lower construction because a fixed constant per block is
only an `L(o(1), N)` loss. -/
theorem dyadicPrimeInterval_card_lower_bound :
    ∀ᶠ y : ℝ in atTop,
      Nat.floor (dyadicPrimeIntervalConstant * y / Real.log y) ≤
        (dyadicPrimeInterval y).card := by
  rcases eventually_atTop.1 dyadicPrimeInterval_nat_card_lower_bound_eventually with
    ⟨N0, hN0⟩
  filter_upwards [Filter.eventually_ge_atTop (max 8 (N0 + 1 : ℕ) : ℝ)] with y hy
  classical
  let n : ℕ := Nat.floor y
  have hy_ge8 : (8 : ℝ) ≤ y := (le_max_left _ _).trans hy
  have hy_ge2 : (2 : ℝ) ≤ y := by linarith
  have hy_pos : 0 < y := by linarith
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hn_floor_le : (n : ℝ) ≤ y := by
    simpa [n] using Nat.floor_le hy_nonneg
  have hn_large : N0 ≤ n := by
    have hN0y : ((N0 + 1 : ℕ) : ℝ) ≤ y := by
      exact (le_max_right (8 : ℝ) (N0 + 1 : ℕ)).trans hy
    have hN0_le_floor : (N0 + 1 : ℕ) ≤ n := by
      exact Nat.le_floor hN0y
    exact (Nat.le_succ N0).trans hN0_le_floor
  have hn_ge4_nat : 4 ≤ n := by
    have h4y : (4 : ℝ) ≤ y := by linarith
    exact Nat.le_floor h4y
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 4) hn_ge4_nat
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hnat_bound :
      Nat.floor (((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ))) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card :=
    hN0 n hn_large
  have hn_lower : y / 2 ≤ (n : ℝ) := by
    have hfloor_gt : y < (n : ℝ) + 1 := by
      simpa [n] using Nat.lt_floor_add_one y
    linarith
  have hlog_y_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog2n_pos : 0 < Real.log (2 * (n : ℝ)) := by
    exact Real.log_pos (by nlinarith)
  have hlog2n_le : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log y := by
    have h2n_pos : 0 < 2 * (n : ℝ) := by positivity
    have h2n_le_y_sq : 2 * (n : ℝ) ≤ y ^ 2 := by
      have h2n_le_2y : 2 * (n : ℝ) ≤ 2 * y := by nlinarith
      have h2y_le_y_sq : 2 * y ≤ y ^ 2 := by
        nlinarith [mul_self_nonneg (y - 1)]
      exact h2n_le_2y.trans h2y_le_y_sq
    calc
      Real.log (2 * (n : ℝ)) ≤ Real.log (y ^ 2) :=
        Real.log_le_log h2n_pos h2n_le_y_sq
      _ = 2 * Real.log y := by
        rw [Real.log_pow]
        norm_num
  have htarget_le_nat_arg :
      dyadicPrimeIntervalConstant * y / Real.log y ≤
        ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) := by
    have hnum :
        dyadicPrimeIntervalConstant * y ≤
          ((Real.log 4 / 4) * (n : ℝ)) / 2 := by
      unfold dyadicPrimeIntervalConstant
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4), hn_lower]
    have hstep1 :
        dyadicPrimeIntervalConstant * y / Real.log y ≤
          (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y :=
      div_le_div_of_nonneg_right hnum hlog_y_pos.le
    have hstep2 :
        (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y =
          ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) := by
      field_simp [hlog_y_pos.ne']
    have hnum_nonneg : 0 ≤ (Real.log 4 / 4) * (n : ℝ) := by positivity
    have hstep3 :
        ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) ≤
          ((Real.log 4 / 4) * (n : ℝ)) /
            Real.log (2 * (n : ℝ)) := by
      exact div_le_div_of_nonneg_left hnum_nonneg hlog2n_pos hlog2n_le
    calc
      dyadicPrimeIntervalConstant * y / Real.log y
          ≤ (((Real.log 4 / 4) * (n : ℝ)) / 2) / Real.log y := hstep1
      _ = ((Real.log 4 / 4) * (n : ℝ)) / (2 * Real.log y) := hstep2
      _ ≤ ((Real.log 4 / 4) * (n : ℝ)) /
          Real.log (2 * (n : ℝ)) := hstep3
  have hfloor_le_nat :
      Nat.floor (dyadicPrimeIntervalConstant * y / Real.log y) ≤
        ((Finset.Ioc n (2 * n)).filter Nat.Prime).card :=
    (Nat.floor_le_floor htarget_le_nat_arg).trans hnat_bound
  have hsubset :
      ((Finset.Ioc n (2 * n)).filter Nat.Prime) ⊆ dyadicPrimeInterval y := by
    intro p hp
    obtain ⟨hpIoc, hpprime⟩ := Finset.mem_filter.1 hp
    obtain ⟨hnp, hp2n⟩ := Finset.mem_Ioc.1 hpIoc
    have h2floor_le : 2 * n ≤ Nat.floor (2 * y) := by
      have hcast : ((2 * n : ℕ) : ℝ) ≤ 2 * y := by
        norm_num
        nlinarith [hn_floor_le]
      exact Nat.le_floor hcast
    exact (mem_dyadicPrimeInterval.2
      ⟨by simpa [n] using hnp, hp2n.trans h2floor_le, hpprime⟩)
  exact hfloor_le_nat.trans (Finset.card_le_card hsubset)

end Erdos202
