/-
Erdős Problem 202 — Mertens / Euler-product estimate.

# Status

This file proves the consumer-shaped weighted-sum bound used by the BFV
omega-tail proof in `Erdos/P202/BFV/OmegaTail.lean`.

# Relation to P694's `Erdos694.mertens_product`

The repo's `Erdos/P694/Proof.lean:417` axiomatizes **Mertens' third theorem**
(the product form `∏_{p ≤ y} p/(p-1) ~ e^γ · log y`). P202 only needs a weak
Mertens-style upper bound `∑_{p ≤ y} 1/p = O(log log y)`, proved below from
Mathlib's Chebyshev upper bound for `Nat.primeCounting`. The sharp Mertens
second theorem is also derivable from Mertens 3rd by taking logs:
  `log ∏_{p ≤ y} (1 - 1/p)^{-1} = ∑_{p ≤ y} (1/p + 1/(2 p²) + …)
                                = ∑_{p ≤ y} 1/p + O(1)`.

P694's sharper product-form Mertens input remains a separate issue, but P202 no
longer depends on it.

# Classical content

The finite Hardy-Ramanujan sieve bookkeeping is proved in this file, as is the
weak reciprocal-prime upper bound:

* **A Mertens-type upper bound**: there exist constants `A > 0` and `C` such
   that for all sufficiently large `N`,
   `∑_{p prime, p ≤ N} (1 / p : ℝ) ≤ A * Real.log (Real.log N) + C`.
   Mertens' second theorem gives the sharp `A = 1`.  For this P202 consumer,
   any fixed `A` is enough because `BFVz N * log log N = sqrt(log N) = o(Z(N))`.
   In Mathlib `v4.27.0`, the prime-counting function `Nat.primeCounting` and
   Chebyshev's upper bound on it are available; the dyadic summation below
   packages them into the reciprocal-prime bound needed here.

Combining the proved finite sieve below with this Mertens input: with
`BFVz N := √(log N) / log log N`,
  `∏_{p ≤ N} (1 + BFVz N / p)
     ≤ Real.exp (BFVz N * ∑_{p ≤ N} 1 / p)
     ≤ Real.exp (BFVz N * (A * Real.log (Real.log N) + C))`,
which is `≤ Real.exp (ε * Zscale N)` eventually for any `ε > 0`, since
`BFVz N · log log N = √(log N) = Zscale N / √(log log N) = o(Zscale N)`.

# Where this is consumed

* `Erdos.P202.BFV.OmegaExact` → `Erdos.P202.BFV.OmegaCountInput` →
  supplies the historical `Erdos202.bfv_omega_count_input` interface.

-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- The BFV Rankin parameter `sqrt(log N) / log log N`. -/
noncomputable def BFVz (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ))

lemma finite_euler_product_one_add_le_exp_sum
    (s : Finset ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hpos : ∀ p ∈ s, 0 < (p : ℝ)) :
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ)) ≤
      Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) := by
  calc
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ))
        ≤ s.prod (fun p : ℕ => Real.exp (z / (p : ℝ))) := by
          exact Finset.prod_le_prod
            (s := s)
            (f := fun p : ℕ => (1 : ℝ) + z / (p : ℝ))
            (g := fun p : ℕ => Real.exp (z / (p : ℝ)))
            (fun p hp => by
              have hp_nonneg : 0 ≤ (p : ℝ) := (hpos p hp).le
              positivity)
            (fun p hp => by
              have h := Real.add_one_le_exp (z / (p : ℝ))
              linarith)
    _ = Real.exp (s.sum (fun p : ℕ => z / (p : ℝ))) := by
          rw [← Real.exp_sum]
    _ = Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring

private lemma primeSupport_eq_primeFactors (n : ℕ) :
    primeSupport n = n.primeFactors := by
  unfold primeSupport
  rw [Nat.support_factorization]

private lemma rad_eq_prod_primeFactors (n : ℕ) :
    rad n = ∏ p ∈ n.primeFactors, p := by
  unfold rad
  rw [primeSupport_eq_primeFactors]

private lemma rad_squarefree (n : ℕ) : Squarefree (rad n) := by
  rw [rad_eq_prod_primeFactors]
  classical
  have hprod_ne : (∏ p ∈ n.primeFactors, p) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
  refine (Nat.squarefree_iff_factorization_le_one hprod_ne).2 ?_
  intro q
  by_cases hq : q ∈ n.primeFactors
  · have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    rw [Nat.factorization_prod]
    · rw [Finsupp.finset_sum_apply]
      calc
        ∑ x ∈ n.primeFactors, x.factorization q
            = q.factorization q := by
                refine Finset.sum_eq_single q ?_ ?_
                · intro x hx hxq
                  have hxprime : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
                  rw [← pow_one x, hxprime.factorization_pow]
                  simp [hxq]
                · intro hnot
                  exact (hnot hq).elim
        _ = 1 := by
                rw [← pow_one q, hqprime.factorization_pow]
                simp
        _ ≤ 1 := le_rfl
    · intro x hx
      exact (Nat.prime_of_mem_primeFactors hx).ne_zero
  · rw [Nat.factorization_prod]
    · rw [Finsupp.finset_sum_apply]
      calc
        ∑ x ∈ n.primeFactors, x.factorization q = 0 := by
          refine Finset.sum_eq_zero ?_
          intro x hx
          have hxprime : Nat.Prime x := Nat.prime_of_mem_primeFactors hx
          rw [← pow_one x, hxprime.factorization_pow]
          have hxq : x ≠ q := by
            intro h
            exact hq (h ▸ hx)
          simp [hxq]
        _ ≤ 1 := by norm_num
    · intro x hx
      exact (Nat.prime_of_mem_primeFactors hx).ne_zero

private lemma rad_dvd_self (n : ℕ) : rad n ∣ n := by
  rw [rad_eq_prod_primeFactors]
  exact Nat.prod_primeFactors_dvd n

private lemma primeSupport_rad (n : ℕ) :
    primeSupport (rad n) = primeSupport n := by
  calc
    primeSupport (rad n) = (rad n).primeFactors := primeSupport_eq_primeFactors _
    _ = (∏ p ∈ n.primeFactors, p).primeFactors := by rw [rad_eq_prod_primeFactors]
    _ = n.primeFactors := by
      exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
    _ = primeSupport n := (primeSupport_eq_primeFactors n).symm

private lemma omega_rad (n : ℕ) : omega (rad n) = omega n := by
  unfold omega
  rw [primeSupport_rad]

lemma zpow_omega_le_squarefree_divisor_sum
    (z : ℝ) (hz : 0 ≤ z) {n : ℕ} (hn : n ≠ 0) :
    z ^ omega n ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d := by
  classical
  have hmem : rad n ∈ n.divisors.filter Squarefree := by
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨rad_dvd_self n, hn⟩, rad_squarefree n⟩
  have hnonneg :
      ∀ d ∈ n.divisors.filter Squarefree, 0 ≤ z ^ omega d := by
    intro d hd
    exact pow_nonneg hz _
  have hsingle :
      z ^ omega (rad n) ≤ ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d :=
    Finset.single_le_sum hnonneg hmem
  simpa [omega_rad] using hsingle

lemma card_Icc_filter_dvd_le_div (y d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d := by
  classical
  calc
    ((Finset.Icc 1 y).filter fun n => d ∣ n).card
        ≤ (Finset.Icc 1 (y / d)).card := by
          refine Finset.card_le_card_of_injOn
            (s := (Finset.Icc 1 y).filter fun n => d ∣ n)
            (t := Finset.Icc 1 (y / d))
            (fun n : ℕ => n / d) ?_ ?_
          · intro n hn
            have hn' : n ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hn
            rw [Finset.mem_filter] at hn'
            have hnIcc := Finset.mem_Icc.mp hn'.1
            have hdn : d ∣ n := hn'.2
            have htarget : n / d ∈ Finset.Icc 1 (y / d) := by
              rw [Finset.mem_Icc]
              refine ⟨?_, Nat.div_le_div_right hnIcc.2⟩
              exact Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hnIcc.1 hdn) hd)
            simpa using htarget
          · intro a ha b hb hab
            have ha' : a ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using ha
            have hb' : b ∈ (Finset.Icc 1 y).filter fun n => d ∣ n := by
              simpa using hb
            rw [Finset.mem_filter] at ha'
            rw [Finset.mem_filter] at hb'
            have hda : d ∣ a := ha'.2
            have hdb : d ∣ b := hb'.2
            have hab' : a / d = b / d := by simpa using hab
            calc
              a = a / d * d := (Nat.div_mul_cancel hda).symm
              _ = b / d * d := by rw [hab']
              _ = b := Nat.div_mul_cancel hdb
    _ = y / d := by simp

lemma omega_weighted_sum_le_squarefree_multiple_sum
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
        (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) * z ^ omega d := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n)
        ≤ ∑ n ∈ Finset.Icc 1 y,
            ∑ d ∈ (n.divisors.filter Squarefree), z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact zpow_omega_le_squarefree_divisor_sum z hz
            (by
              have hnIcc := Finset.mem_Icc.mp hn
              exact Nat.ne_of_gt hnIcc.1)
    _ ≤ ∑ n ∈ Finset.Icc 1 y,
            ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ d ∣ n),
              z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter] at hd ⊢
            have hddiv : d ∈ n.divisors := hd.1
            have hdsq : Squarefree d := hd.2
            have hnIcc := Finset.mem_Icc.mp hn
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
            have hddvd : d ∣ n := (Nat.mem_divisors.mp hddiv).1
            have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnIcc.1
            have hdle : d ≤ y := (Nat.le_of_dvd hnpos hddvd).trans hnIcc.2
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩, hdsq, hddvd⟩
          · intro d hd _hnot
            exact pow_nonneg hz _
    _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
          (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) * z ^ omega d := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : Squarefree d
          · calc
              (∑ x ∈ Finset.Icc 1 y, if Squarefree d ∧ d ∣ x then z ^ omega d else 0)
                  = ∑ x ∈ Finset.Icc 1 y, if d ∣ x then z ^ omega d else 0 := by
                    simp [hsq]
              _ = ∑ x ∈ (Finset.Icc 1 y).filter (fun x => d ∣ x), z ^ omega d := by
                    rw [Finset.sum_filter]
              _ = (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
                    z ^ omega d := by
                    simp [Finset.sum_const, nsmul_eq_mul]
              _ = if Squarefree d then
                    (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
                      z ^ omega d
                  else 0 := by
                    simp [hsq]
          · simp [hsq]

lemma omega_weighted_sum_le_squarefree_recip_sum
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      (y : ℝ) *
        ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n)
        ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) *
              z ^ omega d :=
          omega_weighted_sum_le_squarefree_multiple_sum y z hz
    _ ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            ((y : ℝ) / (d : ℝ)) * z ^ omega d := by
          refine Finset.sum_le_sum ?_
          intro d hd
          rw [Finset.mem_filter] at hd
          have hdIcc := Finset.mem_Icc.mp hd.1
          have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
          have hcard_nat :
              ((Finset.Icc 1 y).filter fun n => d ∣ n).card ≤ y / d :=
            card_Icc_filter_dvd_le_div y d hdpos
          have hcard_real :
              (((Finset.Icc 1 y).filter fun n => d ∣ n).card : ℝ) ≤
                (y : ℝ) / (d : ℝ) := by
            exact (Nat.cast_le.mpr hcard_nat).trans Nat.cast_div_le
          exact mul_le_mul_of_nonneg_right hcard_real (pow_nonneg hz _)
    _ = ∑ d ∈ (Finset.Icc 1 y).filter Squarefree,
            (y : ℝ) * (z ^ omega d / (d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_filter] at hd
          have hdIcc := Finset.mem_Icc.mp hd.1
          have hdne : (d : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1))
          field_simp [hdne]
    _ = (y : ℝ) *
          ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ) := by
          rw [Finset.mul_sum]

lemma squarefree_zpow_omega_div_eq_primeSupport_prod
    (z : ℝ) {d : ℕ} (hsq : Squarefree d) :
    z ^ omega d / (d : ℝ) =
      ∏ p ∈ primeSupport d, z / (p : ℝ) := by
  classical
  have hprod_nat : ∏ p ∈ primeSupport d, p = d := by
    rw [primeSupport_eq_primeFactors]
    exact Nat.prod_primeFactors_of_squarefree hsq
  have hprod_real : (d : ℝ) = ∏ p ∈ primeSupport d, (p : ℝ) := by
    calc
      (d : ℝ) = ((∏ p ∈ primeSupport d, p : ℕ) : ℝ) := by
        exact_mod_cast hprod_nat.symm
      _ = ∏ p ∈ primeSupport d, (p : ℝ) := by
        norm_num
  have hpow : z ^ omega d = ∏ p ∈ primeSupport d, z := by
    simp [omega, Finset.prod_const]
  calc
    z ^ omega d / (d : ℝ)
        = (∏ p ∈ primeSupport d, z) / (∏ p ∈ primeSupport d, (p : ℝ)) := by
          rw [hpow, hprod_real]
    _ = ∏ p ∈ primeSupport d, z / (p : ℝ) := by
          rw [Finset.prod_div_distrib]

private lemma primeSupport_subset_primesUpTo_of_le
    {d y : ℕ} (hd1 : 1 ≤ d) (hdy : d ≤ y) :
    primeSupport d ⊆ (Finset.Icc 1 y).filter Nat.Prime := by
  intro p hp
  rw [Finset.mem_filter]
  have hpPrime : Nat.Prime p := prime_of_mem_primeSupport hp
  have hp_pf : p ∈ d.primeFactors := by
    simpa [primeSupport_eq_primeFactors] using hp
  have hpdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp_pf
  have hp_le_d : p ≤ d :=
    Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hd1) hpdvd
  exact ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hp_le_d.trans hdy⟩, hpPrime⟩

lemma squarefree_recip_sum_le_euler_product
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ)) ≤
      ((Finset.Icc 1 y).filter Nat.Prime).prod
        (fun p => (1 : ℝ) + z / (p : ℝ)) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 y).filter Squarefree
  let P : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
  let term : Finset ℕ → ℝ := fun T => (∏ p ∈ T, z / (p : ℝ))
  have hinj :
      ∀ d ∈ S, ∀ e ∈ S, primeSupport d = primeSupport e → d = e := by
    intro d hd e he hsupport
    simp [S] at hd he
    have hdprod : ∏ p ∈ primeSupport d, p = d := by
      rw [primeSupport_eq_primeFactors]
      exact Nat.prod_primeFactors_of_squarefree hd.2
    have heprod : ∏ p ∈ primeSupport e, p = e := by
      rw [primeSupport_eq_primeFactors]
      exact Nat.prod_primeFactors_of_squarefree he.2
    calc
      d = ∏ p ∈ primeSupport d, p := hdprod.symm
      _ = ∏ p ∈ primeSupport e, p := by rw [hsupport]
      _ = e := heprod
  have himage_subset : S.image primeSupport ⊆ P.powerset := by
    intro T hT
    rw [Finset.mem_powerset]
    rcases Finset.mem_image.mp hT with ⟨d, hdS, rfl⟩
    simp [S] at hdS
    have hdIcc := hdS.1
    exact primeSupport_subset_primesUpTo_of_le hdIcc.1 hdIcc.2
  have hterm_nonneg :
      ∀ T ∈ P.powerset, 0 ≤ term T := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    refine Finset.prod_nonneg ?_
    intro p hpT
    have hpP : p ∈ P := hT hpT
    simp [P] at hpP
    have hpPrime : Nat.Prime p := hpP.2
    exact div_nonneg hz (by exact_mod_cast hpPrime.pos.le)
  calc
    (∑ d ∈ (Finset.Icc 1 y).filter Squarefree, z ^ omega d / (d : ℝ))
        = ∑ d ∈ S, term (primeSupport d) := by
          apply Finset.sum_congr
          · simp [S]
          · intro d hd
            simp [S] at hd
            exact squarefree_zpow_omega_div_eq_primeSupport_prod z hd.2
    _ = ∑ T ∈ S.image primeSupport, term T := by
          rw [Finset.sum_image]
          intro d hd e he hsupport
          exact hinj d hd e he hsupport
    _ ≤ ∑ T ∈ P.powerset, term T := by
          exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset
            (by
              intro T hTP _hnot
              exact hterm_nonneg T hTP)
    _ = P.prod (fun p => (1 : ℝ) + z / (p : ℝ)) := by
          rw [Finset.prod_one_add]
    _ = ((Finset.Icc 1 y).filter Nat.Prime).prod
          (fun p => (1 : ℝ) + z / (p : ℝ)) := by
          rfl

lemma omega_weighted_sum_le_euler_product
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤
      (y : ℝ) *
        ((Finset.Icc 1 y).filter Nat.Prime).prod
          (fun p => (1 : ℝ) + z / (p : ℝ)) := by
  exact (omega_weighted_sum_le_squarefree_recip_sum y z hz).trans
    (mul_le_mul_of_nonneg_left
      (squarefree_recip_sum_le_euler_product y z hz)
      (by positivity))

lemma eventually_primeCounting_nat_le_const_log :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ B * (n : ℝ) / Real.log (n : ℝ) := by
  refine ⟨Real.log 4 + 1, ?_, ?_⟩
  · have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · have hreal :
        ∀ᶠ x : ℝ in atTop,
          (Nat.primeCounting (Nat.floor x) : ℝ) ≤
            (Real.log 4 + 1) * x / Real.log x :=
      Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one
    have hnat := tendsto_natCast_atTop_atTop.eventually hreal
    filter_upwards [hnat] with n hn
    simpa using hn

lemma one_div_nat_succ_le_log_succ_sub_log {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m + 1 : ℕ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hsuccpos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have h :=
    Real.one_sub_inv_le_log_of_pos
      (div_pos hsuccpos hmpos)
  rw [Real.log_div hsuccpos.ne' hmpos.ne'] at h
  have hleft :
      1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) =
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    field_simp [hmpos.ne', hsuccpos.ne']
    norm_num
  calc
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ)
        = 1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) := hleft.symm
    _ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := h

lemma harmonic_Icc_one_le_one_add_log (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) ≤
      1 + Real.log (m : ℝ) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp
      · have hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
        have htop_not : m + 1 ∉ Finset.Icc 1 m := by
          simp
        have hIcc :
            Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext k
          simp
          omega
        have hterm := one_div_nat_succ_le_log_succ_sub_log (m := m) hm
        calc
          (∑ k ∈ Finset.Icc 1 (m + 1), (1 : ℝ) / (k : ℝ))
              = (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / (k : ℝ)) +
                  (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                    rw [hIcc, Finset.sum_insert htop_not]
                    ring
          _ ≤ (1 + Real.log (m : ℝ)) +
                (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right ih ((1 : ℝ) / ((m + 1 : ℕ) : ℝ))
          _ ≤ 1 + Real.log (((m + 1 : ℕ) : ℝ)) := by
                  linarith
          _ = 1 + Real.log ((Nat.succ m : ℕ) : ℝ) := by
                  rfl

lemma primeCounting_eq_card_Icc_filter_prime (n : ℕ) :
    ((Finset.Icc 1 n).filter Nat.Prime).card = Nat.primeCounting n := by
  have hset :
      (Finset.Icc 1 n).filter Nat.Prime =
        (Finset.range (n + 1)).filter Nat.Prime := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      have hpIcc := Finset.mem_Icc.mp hp.1
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpIcc.2), hp.2⟩
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_Icc.mpr
        ⟨hp.2.one_le, Nat.le_of_lt_succ (Finset.mem_range.mp hp.1)⟩, hp.2⟩
  calc
    ((Finset.Icc 1 n).filter Nat.Prime).card
        = ((Finset.range (n + 1)).filter Nat.Prime).card := by rw [hset]
    _ = Nat.count Nat.Prime (n + 1) := by
          exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm
    _ = Nat.primeCounting n := rfl

lemma reciprocal_prime_sum_Ico_pow_two_le (k : ℕ) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
  classical
  let S := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime
  have hdenpos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hpoint : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ 1 / ((2 ^ k : ℕ) : ℝ) := by
    intro p hp
    simp [S] at hp
    have hlow_nat : 2 ^ k ≤ p := hp.1.1
    have hlow : (((2 ^ k : ℕ) : ℝ)) ≤ (p : ℝ) := by exact_mod_cast hlow_nat
    exact one_div_le_one_div_of_le hdenpos hlow
  have hcard_le :
      S.card ≤ Nat.primeCounting (2 ^ (k + 1)) := by
    rw [← primeCounting_eq_card_Icc_filter_prime]
    refine Finset.card_le_card ?_
    intro p hp
    simp [S] at hp
    rw [Finset.mem_filter]
    have hpIco := hp.1
    have hpPrime : Nat.Prime p := hp.2
    exact ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hpIco.2.le⟩, hpPrime⟩
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ))
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
    _ ≤ ∑ p ∈ S, (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          exact Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) hdenpos.le

lemma reciprocal_prime_sum_Ico_pow_two_le_of_primeCounting_bound
    (B : ℝ) {k : ℕ}
    (hπ : (Nat.primeCounting (2 ^ (k + 1)) : ℝ) ≤
      B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
        Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) :
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
  have hdenpos : 0 < (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  calc
    (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ))
        ≤ (Nat.primeCounting (2 ^ (k + 1)) : ℝ) /
            ((2 ^ k : ℕ) : ℝ) :=
          reciprocal_prime_sum_Ico_pow_two_le k
    _ ≤ (B * (((2 ^ (k + 1) : ℕ) : ℝ)) /
          Real.log (((2 ^ (k + 1) : ℕ) : ℝ))) /
            ((2 ^ k : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right hπ hdenpos.le
    _ = (2 * B / Real.log 2) / ((k + 1 : ℕ) : ℝ) := by
          have hpow_succ :
              (((2 ^ (k + 1) : ℕ) : ℝ)) =
                (2 : ℝ) * (((2 ^ k : ℕ) : ℝ)) := by
            norm_num [pow_succ, mul_comm]
          have hlog_pow :
              Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) =
                ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
            rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by norm_num]
            rw [Real.log_pow]
          rw [hlog_pow, hpow_succ]
          field_simp [hdenpos.ne', hlog2pos.ne', hkpos.ne']

lemma eventually_reciprocal_prime_sum_Ico_pow_two_le_const :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k : ℕ in atTop,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ) := by
  rcases eventually_primeCounting_nat_le_const_log with ⟨B, hBpos, hBbound⟩
  refine ⟨2 * B / Real.log 2, ?_, ?_⟩
  · positivity
  · have hpw : Tendsto (fun k : ℕ => 2 ^ (k + 1)) atTop atTop := by
      exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
        (tendsto_add_atTop_nat 1)
    have hBpow := hpw.eventually hBbound
    filter_upwards [hBpow] with k hk
    exact reciprocal_prime_sum_Ico_pow_two_le_of_primeCounting_bound B hk

lemma reciprocal_prime_sum_Ico_pow_two_le_const_global :
    ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ) := by
  classical
  rcases eventually_reciprocal_prime_sum_Ico_pow_two_le_const with
    ⟨D, hDpos, hDevent⟩
  rcases eventually_atTop.1 hDevent with ⟨K, hK⟩
  let block : ℕ → ℝ := fun k =>
    ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ)
  let extra : ℝ := ∑ k ∈ Finset.Icc 0 K, ((k + 1 : ℕ) : ℝ) * block k
  refine ⟨D + extra + 1, ?_, ?_⟩
  · have hextra_nonneg : 0 ≤ extra := by
      refine Finset.sum_nonneg ?_
      intro k hk
      exact mul_nonneg (by positivity)
        (by
          refine Finset.sum_nonneg ?_
          intro p hp
          exact div_nonneg zero_le_one (by positivity))
    linarith
  · intro k
    have hdenpos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
    by_cases hlarge : K ≤ k
    · have hDle : D ≤ D + extra + 1 := by
        have hextra_nonneg : 0 ≤ extra := by
          refine Finset.sum_nonneg ?_
          intro j hj
          exact mul_nonneg (by positivity)
            (by
              refine Finset.sum_nonneg ?_
              intro p hp
              exact div_nonneg zero_le_one (by positivity))
        linarith
      calc
        block k ≤ D / ((k + 1 : ℕ) : ℝ) := hK k hlarge
        _ ≤ (D + extra + 1) / ((k + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right hDle hdenpos.le
    · have hkle : k ≤ K := Nat.le_of_not_ge hlarge
      have hk_mem : k ∈ Finset.Icc 0 K := by
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, hkle⟩
      have hterm_nonneg :
          ∀ j ∈ Finset.Icc 0 K, 0 ≤ ((j + 1 : ℕ) : ℝ) * block j := by
        intro j hj
        exact mul_nonneg (by positivity)
          (by
            refine Finset.sum_nonneg ?_
            intro p hp
            exact div_nonneg zero_le_one (by positivity))
      have hsingle :
          ((k + 1 : ℕ) : ℝ) * block k ≤ extra :=
        Finset.single_le_sum hterm_nonneg hk_mem
      have hmul :
          block k * ((k + 1 : ℕ) : ℝ) ≤ D + extra + 1 := by
        calc
          block k * ((k + 1 : ℕ) : ℝ)
              = ((k + 1 : ℕ) : ℝ) * block k := by ring
          _ ≤ extra := hsingle
          _ ≤ D + extra + 1 := by linarith
      exact (le_div_iff₀ hdenpos).2 hmul

lemma reciprocal_prime_sum_le_dyadic_harmonic
    (D : ℝ)
    (hD : ∀ k : ℕ,
      (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) ≤
        D / ((k + 1 : ℕ) : ℝ))
    (N : ℕ) :
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
      ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  let T : Finset ℕ := Finset.Icc 0 (Nat.log 2 N)
  have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ T := by
    intro p hp
    simp [S, T] at hp ⊢
    exact Nat.log_mono_right hp.1.2
  have hdecomp :
      ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) :=
    Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℕ => (1 : ℝ) / (p : ℝ))
  have hfiber_le :
      ∀ k ∈ T,
        (∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
            (1 : ℝ) / (p : ℝ)) ≤
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) := by
    intro k hk
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      simp [S] at hp ⊢
      have hpPrime : Nat.Prime p := hp.1.2
      have hpne : p ≠ 0 := hpPrime.ne_zero
      have hlog : Nat.log 2 p = k := hp.2
      exact ⟨⟨by simpa [hlog] using Nat.pow_log_le_self 2 hpne,
        by simpa [hlog, Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self Nat.one_lt_two p⟩, hpPrime⟩
    · intro p hp _hnot
      exact div_nonneg zero_le_one (by positivity)
  have hsum_blocks :
      ∑ k ∈ T,
        (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ))
        ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := by
    exact Finset.sum_le_sum (fun k hk => hD k)
  have hsum_shift :
      (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
    have himage :
        T.image (fun k : ℕ => k + 1) = Finset.Icc 1 (Nat.log 2 N + 1) := by
      ext j
      simp [T]
    have hinj : Set.InjOn (fun k : ℕ => k + 1) T := by
      intro a ha b hb hab
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hab)
    have hsum_image :
        (∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ))
          = ∑ k ∈ T, (1 : ℝ) / (((fun k : ℕ => k + 1) k : ℕ) : ℝ) := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    calc
      (∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ))
          = ∑ j ∈ T.image (fun k : ℕ => k + 1), (1 : ℝ) / (j : ℝ) := by
            exact hsum_image.symm
      _ = ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
            rw [himage]
  calc
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
    _ = ∑ k ∈ T, ∑ p ∈ S.filter (fun p => Nat.log 2 p = k),
          (1 : ℝ) / (p : ℝ) := hdecomp.symm
    _ ≤ ∑ k ∈ T,
          (∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ)) :=
          Finset.sum_le_sum hfiber_le
    _ ≤ ∑ k ∈ T, D / ((k + 1 : ℕ) : ℝ) := hsum_blocks
    _ = D * ∑ k ∈ T, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = D * ∑ j ∈ Finset.Icc 1 (Nat.log 2 N + 1), (1 : ℝ) / (j : ℝ) := by
          rw [hsum_shift]
    _ ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (harmonic_Icc_one_le_one_add_log (Nat.log 2 N + 1))
            (by
              have hD0 := hD 0
              have hblock0_nonneg :
                  0 ≤
                    (∑ p ∈ (Finset.Ico (2 ^ 0) (2 ^ (0 + 1))).filter Nat.Prime,
                      (1 : ℝ) / (p : ℝ)) := by
                refine Finset.sum_nonneg ?_
                intro p hp
                exact div_nonneg zero_le_one (by positivity)
              have hden : (((0 + 1 : ℕ) : ℝ)) = 1 := by norm_num
              nlinarith [hD0, hblock0_nonneg])

lemma eventually_one_add_log_nat_log_le_two_loglog :
    ∀ᶠ N : ℕ in atTop,
      1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
        ≤ 2 * Real.log (Real.log (N : ℝ)) := by
  let C : ℝ := 2 / Real.log 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by positivity
  have hloglog_large :
      ∀ᶠ N : ℕ in atTop,
        1 + Real.log C ≤ Real.log (Real.log (N : ℝ)) :=
    tendsto_loglog_nat_atTop.eventually_ge_atTop (1 + Real.log C)
  filter_upwards [hloglog_large,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hll_large hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog2_lt_one : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 Real.exp_one_gt_two
  have hlog2_le_logN : Real.log 2 ≤ Real.log (N : ℝ) := by linarith
  have hquot_ge_one : 1 ≤ Real.log (N : ℝ) / Real.log 2 := by
    have : (1 : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      simpa using hlog2_le_logN
    exact (le_div_iff₀ hlog2pos).2 this
  have hlog_nat_le :
      ((Nat.log 2 N : ℕ) : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb N
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  have hnatlog_add_le :
      (((Nat.log 2 N + 1 : ℕ) : ℝ)) ≤ C * Real.log (N : ℝ) := by
    calc
      (((Nat.log 2 N + 1 : ℕ) : ℝ))
          = ((Nat.log 2 N : ℕ) : ℝ) + 1 := by norm_num
      _ ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
      _ ≤ Real.log (N : ℝ) / Real.log 2 +
            Real.log (N : ℝ) / Real.log 2 := by linarith
      _ = C * Real.log (N : ℝ) := by
            dsimp [C]
            ring
  have hleft_pos : 0 < (((Nat.log 2 N + 1 : ℕ) : ℝ)) := by positivity
  have hright_pos : 0 < C * Real.log (N : ℝ) := mul_pos hCpos hlogpos
  have hlog_bound :
      Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
        ≤ Real.log C + Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))
          ≤ Real.log (C * Real.log (N : ℝ)) :=
            Real.log_le_log hleft_pos hnatlog_add_le
      _ = Real.log C + Real.log (Real.log (N : ℝ)) := by
            rw [Real.log_mul hCpos.ne' hlogpos.ne']
  linarith

/-- A constant-coefficient reciprocal-prime Mertens upper bound.

This proof is intentionally non-sharp: Chebyshev's upper bound for
`Nat.primeCounting` gives an `O(1/k)` estimate on dyadic prime blocks, and the
dyadic harmonic sum is `O(log log N)`. -/
theorem reciprocal_prime_sum_mertens :
    ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter Nat.Prime).sum
          (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        ≤ A * Real.log (Real.log (N : ℝ)) + C := by
  rcases reciprocal_prime_sum_Ico_pow_two_le_const_global with ⟨D, hDpos, hD⟩
  refine ⟨2 * D, 0, by positivity, ?_⟩
  filter_upwards [eventually_one_add_log_nat_log_le_two_loglog] with N hloglog
  calc
    (((Finset.Icc 1 N).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        ≤ D * (1 + Real.log (((Nat.log 2 N + 1 : ℕ) : ℝ))) :=
          reciprocal_prime_sum_le_dyadic_harmonic D hD N
    _ ≤ D * (2 * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hloglog hDpos.le
    _ = (2 * D) * Real.log (Real.log (N : ℝ)) + 0 := by ring

/-- **Analytic gap (Mertens + sieve).** Euler-product upper bound for the
weighted omega sum before the final BFV scale simplification.

This packages the classical sieve inequality together with Mertens' reciprocal
prime sum in the form
`∑ z^ω(n) ≤ y * exp(z * (log log N + C))`, specialized to `z = BFVz N`.
The proof is the analytic-number-theory target described in the file header. -/
theorem omega_weighted_sum_euler_mertens :
    ∃ A C : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n ∈ Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) *
              Real.exp (BFVz N *
                (A * Real.log (Real.log (N : ℝ)) + C)) := by
  rcases reciprocal_prime_sum_mertens with ⟨A, C, hA, hMertens⟩
  refine ⟨A, C, hA, ?_⟩
  filter_upwards [hMertens,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hMertensN hNlarge_nat
  intro y hy
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hz_nonneg : 0 ≤ BFVz N := by
    rw [BFVz]
    exact div_nonneg (Real.sqrt_nonneg _) hloglog_pos.le
  let Py : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
  let PN : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime
  have hPy_subset : Py ⊆ PN := by
    intro p hp
    simp [Py, PN] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hy⟩, hp.2⟩
  have hsum_y_le_N :
      Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
        PN.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hPy_subset
      (by
        intro p hpN _hpnot
        simp [PN] at hpN
        exact div_nonneg zero_le_one (by exact_mod_cast hpN.2.pos.le))
  have hsum_y_bound :
      Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)) ≤
        A * Real.log (Real.log (N : ℝ)) + C := by
    exact hsum_y_le_N.trans (by simpa [PN] using hMertensN)
  have hpos_p : ∀ p ∈ Py, 0 < (p : ℝ) := by
    intro p hp
    simp [Py] at hp
    exact_mod_cast hp.2.pos
  have hprod_exp :
      Py.prod (fun p : ℕ => (1 : ℝ) + BFVz N / (p : ℝ)) ≤
        Real.exp (BFVz N *
          Py.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) :=
    finite_euler_product_one_add_le_exp_sum Py hz_nonneg hpos_p
  have hprod_bound :
      Py.prod (fun p : ℕ => (1 : ℝ) + BFVz N / (p : ℝ)) ≤
        Real.exp (BFVz N *
          (A * Real.log (Real.log (N : ℝ)) + C)) := by
    exact hprod_exp.trans
      (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left hsum_y_bound hz_nonneg))
  exact (omega_weighted_sum_le_euler_product y (BFVz N) hz_nonneg).trans
    (mul_le_mul_of_nonneg_left (by simpa [Py] using hprod_bound) (by positivity))

lemma BFVz_linear_loglog_exponent_le_Zscale
    (A C ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      BFVz N * (A * Real.log (Real.log (N : ℝ)) + C) ≤ ε * Zscale N := by
  let R : ℝ := max (4 * (A + 1) / ε) (max 1 |C|)
  filter_upwards [eventually_sqrt_loglog_ge R,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsqrtlog_nonneg : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  have hA1_pos : 0 < A + 1 := by linarith
  have hR_ge_main : 4 * (A + 1) / ε ≤ R := le_max_left _ _
  have hR_ge_one : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR_ge_abs : |C| ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hsqrt_ge_main :
      4 * (A + 1) / ε ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_main.trans hsqrt
  have hsqrt_ge_one : 1 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_one.trans hsqrt
  have hsqrt_ge_abs : |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_abs.trans hsqrt
  have hloglog_ge_abs : |C| ≤ Real.log (Real.log (N : ℝ)) := by
    calc
      |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) := hsqrt_ge_abs
      _ ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 := by
            nlinarith [sq_nonneg (Real.sqrt (Real.log (Real.log (N : ℝ))) - 1)]
      _ = Real.log (Real.log (N : ℝ)) := Real.sq_sqrt hloglog_nonneg
  have hmain_sqrt :
      2 * (A + 1) ≤
        ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    have hfour :
        4 * (A + 1) ≤
          ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      simpa [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hε).1 hsqrt_ge_main
    linarith
  have hBFVz_nonneg : 0 ≤ BFVz N := by
    rw [BFVz]
    exact div_nonneg hsqrtlog_nonneg hloglog_nonneg
  have hlinear_le :
      A * Real.log (Real.log (N : ℝ)) + C ≤
        (A + 1) * Real.log (Real.log (N : ℝ)) := by
    calc
      A * Real.log (Real.log (N : ℝ)) + C
          ≤ A * Real.log (Real.log (N : ℝ)) + |C| := by
            nlinarith [le_abs_self C]
      _ ≤ A * Real.log (Real.log (N : ℝ)) +
            Real.log (Real.log (N : ℝ)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hloglog_ge_abs
                (A * Real.log (Real.log (N : ℝ)))
      _ = (A + 1) * Real.log (Real.log (N : ℝ)) := by ring
  have hwith_bound :
      BFVz N * (A * Real.log (Real.log (N : ℝ)) + C) ≤
        BFVz N * ((A + 1) * Real.log (Real.log (N : ℝ))) :=
    mul_le_mul_of_nonneg_left hlinear_le hBFVz_nonneg
  have hZeq := Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge
  have hbound :
      BFVz N * ((A + 1) * Real.log (Real.log (N : ℝ))) ≤
        ε * Zscale N := by
    rw [BFVz, hZeq]
    calc
      Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
          ((A + 1) * Real.log (Real.log (N : ℝ)))
          = (A + 1) * Real.sqrt (Real.log (N : ℝ)) := by
            field_simp [hloglog_pos.ne']
      _ ≤ ε * (Real.sqrt (Real.log (N : ℝ)) *
            Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
            calc
              (A + 1) * Real.sqrt (Real.log (N : ℝ))
                  ≤ (ε * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
                      Real.sqrt (Real.log (N : ℝ)) := by
                        exact mul_le_mul_of_nonneg_right
                          (by linarith [hmain_sqrt]) hsqrtlog_nonneg
              _ = ε * (Real.sqrt (Real.log (N : ℝ)) *
                    Real.sqrt (Real.log (Real.log (N : ℝ)))) := by ring
  exact hwith_bound.trans hbound

lemma BFVz_mertens_exponent_le_Zscale (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      BFVz N * (Real.log (Real.log (N : ℝ)) + C) ≤ ε * Zscale N := by
  let R : ℝ := max (4 / ε) (max 1 |C|)
  filter_upwards [eventually_sqrt_loglog_ge R,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsqrtlog_nonneg : 0 ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_nonneg _
  have hsqrtloglog_nonneg : 0 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    Real.sqrt_nonneg _
  have hR_ge_four : 4 / ε ≤ R := le_max_left _ _
  have hR_ge_one : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hR_ge_abs : |C| ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hsqrt_ge_four : 4 / ε ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_four.trans hsqrt
  have hsqrt_ge_one : 1 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_one.trans hsqrt
  have hsqrt_ge_abs : |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    hR_ge_abs.trans hsqrt
  have hloglog_ge_abs : |C| ≤ Real.log (Real.log (N : ℝ)) := by
    calc
      |C| ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) := hsqrt_ge_abs
      _ ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) ^ 2 := by
            nlinarith [sq_nonneg (Real.sqrt (Real.log (Real.log (N : ℝ))) - 1)]
      _ = Real.log (Real.log (N : ℝ)) := Real.sq_sqrt hloglog_nonneg
  have htwo_le_eps_sqrt : 2 ≤ ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    have hfour : 4 ≤ ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      simpa [mul_comm] using (div_le_iff₀ hε).1 hsqrt_ge_four
    linarith
  have hBFVz_nonneg : 0 ≤ BFVz N := by
    rw [BFVz]
    exact div_nonneg hsqrtlog_nonneg hloglog_nonneg
  have hwith_abs :
      BFVz N * (Real.log (Real.log (N : ℝ)) + C) ≤
        BFVz N * (Real.log (Real.log (N : ℝ)) + |C|) := by
    have hsum_abs :
        Real.log (Real.log (N : ℝ)) + C ≤
          Real.log (Real.log (N : ℝ)) + |C| := by
      nlinarith [le_abs_self C]
    exact mul_le_mul_of_nonneg_left hsum_abs hBFVz_nonneg
  have hZeq := Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge
  have hbound_abs :
      BFVz N * (Real.log (Real.log (N : ℝ)) + |C|) ≤ ε * Zscale N := by
    rw [BFVz, hZeq]
    calc
      Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
          (Real.log (Real.log (N : ℝ)) + |C|)
          ≤ Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) *
              (2 * Real.log (Real.log (N : ℝ))) := by
                have hsum_le :
                    Real.log (Real.log (N : ℝ)) + |C| ≤
                      2 * Real.log (Real.log (N : ℝ)) := by linarith
                exact mul_le_mul_of_nonneg_left hsum_le
                  (div_nonneg hsqrtlog_nonneg hloglog_nonneg)
      _ = 2 * Real.sqrt (Real.log (N : ℝ)) := by
            field_simp [hloglog_pos.ne']
      _ ≤ ε * (Real.sqrt (Real.log (N : ℝ)) *
            Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
            calc
              2 * Real.sqrt (Real.log (N : ℝ))
                  ≤ (ε * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
                      Real.sqrt (Real.log (N : ℝ)) := by
                        exact mul_le_mul_of_nonneg_right htwo_le_eps_sqrt
                          hsqrtlog_nonneg
              _ = ε * (Real.sqrt (Real.log (N : ℝ)) *
                    Real.sqrt (Real.log (Real.log (N : ℝ)))) := by ring
  exact hwith_abs.trans hbound_abs

/-- Euler-product upper bound for the weighted omega sum at the BFV scale.

For every `ε > 0`, eventually in `N`, for every `y ≤ N`:
  `∑_{n ≤ y} (BFVz N) ^ omega n ≤ y · exp(ε · Z(N))`.

The analytic input is `omega_weighted_sum_euler_mertens`; this theorem proves
the remaining scale algebra at `z = BFVz N`. -/
theorem omega_weighted_sum_bfvz_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n ∈ Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) * Real.exp (ε * Zscale N) := by
  intro ε hε
  rcases omega_weighted_sum_euler_mertens with ⟨A, C, hA, hC⟩
  filter_upwards [hC, BFVz_linear_loglog_exponent_le_Zscale A C ε hA hε]
    with N hAnalytic hExp y hy
  have hExp_le :
      Real.exp (BFVz N * (A * Real.log (Real.log (N : ℝ)) + C)) ≤
        Real.exp (ε * Zscale N) :=
    Real.exp_le_exp.2 hExp
  exact (hAnalytic y hy).trans
    (mul_le_mul_of_nonneg_left hExp_le (by positivity))

end Erdos202
