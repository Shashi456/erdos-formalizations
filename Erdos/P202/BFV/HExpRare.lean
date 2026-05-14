/-
Erdos Problem 202 -- rarity of large hExp values in BFV pruning.

The paper-shaped BFV Lemma 3.2 estimate is isolated as a named theorem stub.
The super-`L` consumer form used by pruning is proved from that estimate by
explicit scale algebra.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic
import Erdos.P202.BFV.Mertens
import Erdos.P202.BFV.RadMultiplicity
import Erdos.P202.BFV.LowerPathScales

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- The hExp cutoff used in BFV Proposition 3.1. -/
noncomputable def hExpCutoff (N : ℕ) : ℝ :=
  Real.exp (Real.sqrt (Real.log (N : ℝ)))

lemma hExp_prime_pow {p e : ℕ} (hp : Nat.Prime p) :
    hExp (p ^ e) = if e = 0 then 1 else e := by
  by_cases he : e = 0
  · simp [he, hExp_one]
  · unfold hExp primeSupport
    rw [hp.factorization_pow]
    rw [Finsupp.support_single_ne_zero p he]
    rw [if_neg he]
    change (∏ q ∈ ({p} : Finset ℕ), Finsupp.single p e q) = e
    simp

noncomputable def hExpMomentTerm (s n : ℕ) : ℝ :=
  if n = 0 then 0 else (hExp n : ℝ) ^ s / (n : ℝ)

lemma hExpMomentTerm_nonneg (s n : ℕ) :
    0 ≤ hExpMomentTerm s n := by
  by_cases hn : n = 0
  · simp [hExpMomentTerm, hn]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp [hExpMomentTerm, hn]
    exact div_nonneg (by positivity) hnpos.le

lemma hExpMomentTerm_one (s : ℕ) : hExpMomentTerm s 1 = 1 := by
  simp [hExpMomentTerm, hExp_one]

lemma hExpMomentTerm_prime_pow {s p e : ℕ} (hp : Nat.Prime p) :
    hExpMomentTerm s (p ^ e) =
      if e = 0 then 1 else ((e : ℝ) ^ s / (p : ℝ) ^ e) := by
  by_cases he : e = 0
  · rw [he, pow_zero, hExpMomentTerm_one]
    simp
  · simp [hExpMomentTerm, hExp_prime_pow hp, he, hp.ne_zero, Nat.cast_pow]

lemma hExpMomentTerm_mul_of_coprime
    (s : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    hExpMomentTerm s (m * n) =
      hExpMomentTerm s m * hExpMomentTerm s n := by
  by_cases hmn : m * n = 0
  · rcases hcop.eq_of_mul_eq_zero hmn with h | h
    · rcases h with ⟨hm, hn⟩
      simp [hExpMomentTerm, hm, hn]
    · rcases h with ⟨hm, hn⟩
      simp [hExpMomentTerm, hm, hn]
  · have hm : m ≠ 0 := left_ne_zero_of_mul hmn
    have hn : n ≠ 0 := right_ne_zero_of_mul hmn
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp [hExpMomentTerm, hmn, hm, hn, hExp_mul_of_coprime hcop,
      Nat.cast_mul, mul_pow]
    field_simp [hmreal, hnreal]

def squarefullSupport (n : ℕ) : Finset ℕ :=
  (primeSupport n).filter fun p => 2 ≤ n.factorization p

def squarefullKernel (n : ℕ) : ℕ :=
  exactBlock (squarefullSupport n) n

def IsSquarefull (n : ℕ) : Prop :=
  ∀ p ∈ primeSupport n, 2 ≤ n.factorization p

instance instDecidablePredIsSquarefull : DecidablePred IsSquarefull := by
  intro n
  unfold IsSquarefull
  infer_instance

lemma squarefullSupport_subset (n : ℕ) :
    squarefullSupport n ⊆ primeSupport n := by
  intro p hp
  exact (Finset.mem_filter.1 hp).1

lemma prime_of_mem_squarefullSupport {n p : ℕ}
    (hp : p ∈ squarefullSupport n) : Nat.Prime p :=
  prime_of_mem_primeSupport (squarefullSupport_subset n hp)

lemma squarefullKernel_dvd (n : ℕ) : squarefullKernel n ∣ n := by
  simp [squarefullKernel, exactBlock_dvd]

lemma squarefullKernel_ne_zero {n : ℕ} (hn : n ≠ 0) :
    squarefullKernel n ≠ 0 := by
  exact (Nat.pos_of_dvd_of_pos (squarefullKernel_dvd n)
    (Nat.pos_of_ne_zero hn)).ne'

lemma primeSupport_squarefullKernel {n : ℕ} :
    primeSupport (squarefullKernel n) = squarefullSupport n := by
  by_cases hn : n = 0
  · simp [squarefullKernel, squarefullSupport, primeSupport, exactBlock, hn]
  · exact primeSupport_exactBlock
      (fun p hp => prime_of_mem_squarefullSupport hp)
      (squarefullSupport_subset n)

lemma squarefullKernel_isSquarefull (n : ℕ) :
    IsSquarefull (squarefullKernel n) := by
  intro p hp
  rw [primeSupport_squarefullKernel] at hp
  have hp' := Finset.mem_filter.1 hp
  change 2 ≤ (exactBlock (squarefullSupport n) n).factorization p
  rw [factorization_exactBlock_of_mem
    (C := squarefullSupport n)
    (q := n)
    (p := p)
    (fun r hr => prime_of_mem_squarefullSupport hr)
    hp]
  exact hp'.2

lemma isSquarefull_mul_iff_of_coprime {m n : ℕ}
    (hcop : Nat.Coprime m n) :
    IsSquarefull (m * n) ↔ IsSquarefull m ∧ IsSquarefull n := by
  constructor
  · intro hmn
    constructor
    · intro p hp
      have hp_prod : p ∈ primeSupport (m * n) := by
        rw [primeSupport_mul_of_coprime hcop]
        exact Finset.mem_union_left _ hp
      have htwo := hmn p hp_prod
      have hpnot : p ∉ primeSupport n :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
      have hnzero : n.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      rw [Nat.factorization_mul_of_coprime hcop] at htwo
      simpa [Finsupp.add_apply, hnzero] using htwo
    · intro p hp
      have hp_prod : p ∈ primeSupport (m * n) := by
        rw [primeSupport_mul_of_coprime hcop]
        exact Finset.mem_union_right _ hp
      have htwo := hmn p hp_prod
      have hpnot : p ∉ primeSupport m :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
      have hmzero : m.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      rw [Nat.factorization_mul_of_coprime hcop] at htwo
      simpa [Finsupp.add_apply, hmzero] using htwo
  · rintro ⟨hm, hn⟩ p hp
    rw [primeSupport_mul_of_coprime hcop] at hp
    rw [Nat.factorization_mul_of_coprime hcop]
    rcases Finset.mem_union.1 hp with hp | hp
    · have hpnot : p ∉ primeSupport n :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
      have hnzero : n.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      simpa [Finsupp.add_apply, hnzero] using hm p hp
    · have hpnot : p ∉ primeSupport m :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
      have hmzero : m.factorization p = 0 := by
        unfold primeSupport at hpnot
        exact Finsupp.notMem_support_iff.1 hpnot
      simpa [Finsupp.add_apply, hmzero, add_comm] using hn p hp

lemma hExp_squarefullKernel_eq (n : ℕ) :
    hExp (squarefullKernel n) = hExp n := by
  by_cases hn : n = 0
  · simp [squarefullKernel, squarefullSupport, primeSupport, exactBlock, hExp, hn]
  · unfold hExp
    rw [primeSupport_squarefullKernel]
    have hprod :
        (∏ p ∈ primeSupport n, n.factorization p) =
          ∏ p ∈ squarefullSupport n, n.factorization p := by
      refine (Finset.prod_subset (squarefullSupport_subset n) ?_).symm
      intro p hpPrime hpNot
      have hpos : 1 ≤ n.factorization p := by
        unfold primeSupport at hpPrime
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero
          (Finsupp.mem_support_iff.1 hpPrime))
      have hnot_two : ¬ 2 ≤ n.factorization p := by
        intro htwo
        exact hpNot (Finset.mem_filter.2 ⟨hpPrime, htwo⟩)
      omega
    rw [hprod]
    apply Finset.prod_congr rfl
    intro p hp
    change (exactBlock (squarefullSupport n) n).factorization p =
      n.factorization p
    rw [factorization_exactBlock_of_mem
      (C := squarefullSupport n)
      (q := n)
      (p := p)
      (fun r hr => prime_of_mem_squarefullSupport hr)
      hp]

lemma squarefullKernel_mem_divisors {n : ℕ} (hn : n ≠ 0) :
    squarefullKernel n ∈ n.divisors := by
  exact Nat.mem_divisors.2
    ⟨squarefullKernel_dvd n, hn⟩

lemma hExp_pow_le_squarefull_divisor_sum (s : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (hExp n : ℝ) ^ s ≤
      ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s := by
  classical
  have hmem :
      squarefullKernel n ∈ n.divisors.filter IsSquarefull := by
    exact Finset.mem_filter.2
      ⟨squarefullKernel_mem_divisors hn, squarefullKernel_isSquarefull n⟩
  have hterm :
      (hExp (squarefullKernel n) : ℝ) ^ s = (hExp n : ℝ) ^ s := by
    rw [hExp_squarefullKernel_eq]
  calc
    (hExp n : ℝ) ^ s = (hExp (squarefullKernel n) : ℝ) ^ s := hterm.symm
    _ ≤ ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s :=
        Finset.single_le_sum
          (fun d _hd => pow_nonneg (by positivity : 0 ≤ (hExp d : ℝ)) s)
          hmem

lemma nat_pow_le_factorial_mul_exp_quarter (s e : ℕ) :
    ((e : ℝ) ^ s) ≤
      (4 : ℝ) ^ s * (s.factorial : ℝ) * Real.exp ((e : ℝ) / 4) := by
  have hx : 0 ≤ (e : ℝ) / 4 := by positivity
  have h := Real.pow_div_factorial_le_exp ((e : ℝ) / 4) hx s
  have hfac : ((s.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero s
  have h1 :
      ((e : ℝ) / 4) ^ s ≤
        (s.factorial : ℝ) * Real.exp ((e : ℝ) / 4) := by
    have hmul := mul_le_mul_of_nonneg_left h
      (by positivity : 0 ≤ (s.factorial : ℝ))
    field_simp [hfac] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  calc
    (e : ℝ) ^ s = (4 : ℝ) ^ s * ((e : ℝ) / 4) ^ s := by
      rw [div_pow]
      field_simp
    _ ≤ (4 : ℝ) ^ s *
          ((s.factorial : ℝ) * Real.exp ((e : ℝ) / 4)) := by
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (4 : ℝ) ^ s * (s.factorial : ℝ) *
          Real.exp ((e : ℝ) / 4) := by
      ring

lemma exp_quarter_lt_two : Real.exp ((1 : ℝ) / 4) < 2 := by
  have hpow_lt : Real.exp ((1 : ℝ) / 4) ^ 4 < (2 : ℝ) ^ 4 := by
    calc
      Real.exp ((1 : ℝ) / 4) ^ 4 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < 3 := Real.exp_one_lt_three
      _ < (2 : ℝ) ^ 4 := by norm_num
  by_contra hnot
  have hge : (2 : ℝ) ≤ Real.exp ((1 : ℝ) / 4) := le_of_not_gt hnot
  have hpow_ge :
      (2 : ℝ) ^ 4 ≤ Real.exp ((1 : ℝ) / 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hge 4
  exact not_lt_of_ge hpow_ge hpow_lt

lemma exp_quarter_div_two_lt_one : Real.exp ((1 : ℝ) / 4) / 2 < 1 := by
  nlinarith [exp_quarter_lt_two]

lemma exp_quarter_lt_three_halves :
    Real.exp ((1 : ℝ) / 4) < 3 / 2 := by
  have hpow_lt : Real.exp ((1 : ℝ) / 4) ^ 4 < ((3 : ℝ) / 2) ^ 4 := by
    calc
      Real.exp ((1 : ℝ) / 4) ^ 4 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < 3 := Real.exp_one_lt_three
      _ < ((3 : ℝ) / 2) ^ 4 := by norm_num
  by_contra hnot
  have hge : (3 : ℝ) / 2 ≤ Real.exp ((1 : ℝ) / 4) := le_of_not_gt hnot
  have hpow_ge :
      ((3 : ℝ) / 2) ^ 4 ≤ Real.exp ((1 : ℝ) / 4) ^ 4 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2) hge 4
  exact not_lt_of_ge hpow_ge hpow_lt

lemma exp_quarter_div_two_le_three_quarters :
    Real.exp ((1 : ℝ) / 4) / 2 ≤ 3 / 4 := by
  nlinarith [exp_quarter_lt_three_halves]

lemma hExp_large_rankin_sum_le
    (N s : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (((Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)).card : ℝ) * H ^ s
      ≤ ∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s := by
  classical
  let Bad := (Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)
  have hpoint :
      ∀ n ∈ Bad, H ^ s ≤ (hExp n : ℝ) ^ s := by
    intro n hn
    exact pow_le_pow_left₀ hH (le_of_lt (Finset.mem_filter.1 hn).2) s
  calc
    (((Finset.Icc 1 N).filter fun n => H < (hExp n : ℝ)).card : ℝ) * H ^ s
        = ∑ n ∈ Bad, H ^ s := by
            simp [Bad, mul_comm]
    _ ≤ ∑ n ∈ Bad, (hExp n : ℝ) ^ s := by
            exact Finset.sum_le_sum (fun n hn => hpoint n hn)
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
              (by
                intro n _hn _hnot
                positivity)

lemma hExp_pow_le_divisor_sum (s : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (hExp n : ℝ) ^ s ≤
      ∑ d ∈ n.divisors, (hExp d : ℝ) ^ s := by
  classical
  have hnmem : n ∈ n.divisors := Nat.mem_divisors_self n hn
  exact Finset.single_le_sum
    (fun d _hd => pow_nonneg (by positivity : 0 ≤ (hExp d : ℝ)) s)
    hnmem

lemma hExp_moment_sum_le_divisor_multiple_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      ∑ d ∈ Finset.Icc 1 N,
        (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
          (hExp d : ℝ) ^ s := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ n.divisors, (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnIcc := Finset.mem_Icc.mp hn
          exact hExp_pow_le_divisor_sum s
            (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1))
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n),
              (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter]
            have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
            have hnIcc := Finset.mem_Icc.mp hn
            have hdle : d ≤ N :=
              (Nat.le_of_dvd
                (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1) hdn).trans hnIcc.2
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩, hdn⟩
          · intro d _hd _hnot
            positivity
    _ = ∑ d ∈ Finset.Icc 1 N,
          (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
            (hExp d : ℝ) ^ s := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          calc
            (∑ x ∈ Finset.Icc 1 N,
                if d ∣ x then (hExp d : ℝ) ^ s else 0)
                =
              ∑ x ∈ Finset.Icc 1 N,
                if d ∣ x then (hExp d : ℝ) ^ s else 0 := by
                rfl
            _ = ∑ x ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
                  (hExp d : ℝ) ^ s := by
                rw [Finset.sum_filter]
            _ = (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
                  (hExp d : ℝ) ^ s := by
                simp [Finset.sum_const, nsmul_eq_mul]

lemma hExp_moment_sum_le_recip_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      (N : ℝ) *
        ∑ d ∈ Finset.Icc 1 N, (hExp d : ℝ) ^ s / (d : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ d ∈ Finset.Icc 1 N,
            (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
              (hExp d : ℝ) ^ s :=
          hExp_moment_sum_le_divisor_multiple_sum N s
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
            ((N : ℝ) / (d : ℝ)) * (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro d hd
          have hdIcc := Finset.mem_Icc.mp hd
          have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
          have hcard_nat :
              ((Finset.Icc 1 N).filter fun n => d ∣ n).card ≤ N / d := by
            exact card_Icc_filter_dvd_le_div N d hdpos
          have hcard_real :
              (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) ≤
                (N : ℝ) / (d : ℝ) := by
            exact (Nat.cast_le.mpr hcard_nat).trans Nat.cast_div_le
          exact mul_le_mul_of_nonneg_right hcard_real (by positivity)
    _ = ∑ d ∈ Finset.Icc 1 N,
          (N : ℝ) * ((hExp d : ℝ) ^ s / (d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdIcc := Finset.mem_Icc.mp hd
          have hdne : (d : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1))
          field_simp [hdne]
    _ = (N : ℝ) *
          ∑ d ∈ Finset.Icc 1 N, (hExp d : ℝ) ^ s / (d : ℝ) := by
          rw [Finset.mul_sum]

lemma hExp_moment_sum_le_squarefull_divisor_multiple_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      ∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then
          (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
            (hExp d : ℝ) ^ s
        else 0 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ n.divisors.filter IsSquarefull, (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnIcc := Finset.mem_Icc.mp hn
          exact hExp_pow_le_squarefull_divisor_sum s
            (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1))
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ (Finset.Icc 1 N).filter
                (fun d => d ∣ n ∧ IsSquarefull d),
              (hExp d : ℝ) ^ s := by
          refine Finset.sum_le_sum ?_
          intro n hn
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            rw [Finset.mem_filter]
            rw [Finset.mem_filter] at hd
            have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd.1
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd.1
            have hnIcc := Finset.mem_Icc.mp hn
            have hdle : d ≤ N :=
              (Nat.le_of_dvd
                (lt_of_lt_of_le Nat.zero_lt_one hnIcc.1) hdn).trans hnIcc.2
            exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hdpos, hdle⟩,
              hdn, hd.2⟩
          · intro d _hd _hnot
            positivity
    _ = ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then
            (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
              (hExp d : ℝ) ^ s
          else 0 := by
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            calc
              (∑ x ∈ Finset.Icc 1 N,
                  if d ∣ x then (hExp d : ℝ) ^ s else 0)
                  = ∑ x ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
                      (hExp d : ℝ) ^ s := by
                    rw [Finset.sum_filter]
              _ = (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
                    (hExp d : ℝ) ^ s := by
                    simp [Finset.sum_const, nsmul_eq_mul]
          · simp [hsq]

lemma hExp_moment_sum_le_squarefull_recip_sum (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      (N : ℝ) *
        ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ ∑ d ∈ Finset.Icc 1 N,
            if IsSquarefull d then
              (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) *
                (hExp d : ℝ) ^ s
            else 0 :=
          hExp_moment_sum_le_squarefull_divisor_multiple_sum N s
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
          if IsSquarefull d then
            ((N : ℝ) / (d : ℝ)) * (hExp d : ℝ) ^ s
          else 0 := by
          refine Finset.sum_le_sum ?_
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            have hdIcc := Finset.mem_Icc.mp hd
            have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
            have hcard_nat :
                ((Finset.Icc 1 N).filter fun n => d ∣ n).card ≤ N / d := by
              exact card_Icc_filter_dvd_le_div N d hdpos
            have hcard_real :
                (((Finset.Icc 1 N).filter fun n => d ∣ n).card : ℝ) ≤
                  (N : ℝ) / (d : ℝ) := by
              exact (Nat.cast_le.mpr hcard_nat).trans Nat.cast_div_le
            exact mul_le_mul_of_nonneg_right hcard_real (by positivity)
          · simp [hsq]
    _ = ∑ d ∈ Finset.Icc 1 N,
          (N : ℝ) *
            (if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hsq : IsSquarefull d
          · simp [hsq]
            have hdIcc := Finset.mem_Icc.mp hd
            have hdne : (d : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1))
            field_simp [hdne]
          · simp [hsq]
    _ = (N : ℝ) *
          ∑ d ∈ Finset.Icc 1 N,
            if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 := by
          rw [Finset.mul_sum]

noncomputable def squarefullMomentTerm (s n : ℕ) : ℝ :=
  if IsSquarefull n then hExpMomentTerm s n else 0

lemma squarefullMomentTerm_nonneg (s n : ℕ) :
    0 ≤ squarefullMomentTerm s n := by
  unfold squarefullMomentTerm
  by_cases hsq : IsSquarefull n <;> simp [hsq, hExpMomentTerm_nonneg]

lemma one_isSquarefull : IsSquarefull 1 := by
  intro p hp
  simp [primeSupport] at hp

lemma squarefullMomentTerm_one (s : ℕ) :
    squarefullMomentTerm s 1 = 1 := by
  simp [squarefullMomentTerm, one_isSquarefull, hExpMomentTerm_one]

lemma not_isSquarefull_prime {p : ℕ} (hp : Nat.Prime p) :
    ¬ IsSquarefull p := by
  intro hsq
  have hmem : p ∈ primeSupport p := by
    unfold primeSupport
    rw [Finsupp.mem_support_iff]
    exact Nat.Prime.factorization_self hp ▸ one_ne_zero
  have htwo := hsq p hmem
  rw [Nat.Prime.factorization_self hp] at htwo
  omega

lemma squarefullMomentTerm_prime_pow {s p e : ℕ} (hp : Nat.Prime p) :
    squarefullMomentTerm s (p ^ e) =
      if e = 0 then 1
      else if e = 1 then 0
      else ((e : ℝ) ^ s / (p : ℝ) ^ e) := by
  by_cases he0 : e = 0
  · subst e
    simp [squarefullMomentTerm, one_isSquarefull, hExpMomentTerm_one]
  · by_cases he1 : e = 1
    · subst e
      simp [squarefullMomentTerm, not_isSquarefull_prime hp]
    · have hsq : IsSquarefull (p ^ e) := by
        intro q hq
        have hqprime : Nat.Prime q := prime_of_mem_primeSupport hq
        have hqeq : q = p := by
          have hfac_ne : (p ^ e).factorization q ≠ 0 := by
            unfold primeSupport at hq
            exact Finsupp.mem_support_iff.1 hq
          rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
            nsmul_eq_mul] at hfac_ne
          have hpq_ne : p.factorization q ≠ 0 := by
            intro hpq
            simp [hpq] at hfac_ne
          exact (hp.eq_of_factorization_pos hpq_ne).symm
        subst q
        rw [Nat.factorization_pow_self hp]
        omega
      simp [squarefullMomentTerm, hExpMomentTerm_prime_pow hp, he0, he1, hsq]

lemma squarefullMomentTerm_mul_of_coprime
    (s : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    squarefullMomentTerm s (m * n) =
      squarefullMomentTerm s m * squarefullMomentTerm s n := by
  by_cases hm : IsSquarefull m
  · by_cases hn : IsSquarefull n
    · have hmn : IsSquarefull (m * n) :=
        (isSquarefull_mul_iff_of_coprime hcop).2 ⟨hm, hn⟩
      simp [squarefullMomentTerm, hm, hn, hmn,
        hExpMomentTerm_mul_of_coprime s hcop]
    · have hmn : ¬ IsSquarefull (m * n) := by
        intro h
        exact hn ((isSquarefull_mul_iff_of_coprime hcop).1 h).2
      simp [squarefullMomentTerm, hn, hmn]
  · have hmn : ¬ IsSquarefull (m * n) := by
      intro h
      exact hm ((isSquarefull_mul_iff_of_coprime hcop).1 h).1
    simp [squarefullMomentTerm, hm, hmn]

lemma squarefullMomentTerm_prime_pow_summable
    (s p : ℕ) (hp : Nat.Prime p) :
    Summable (fun e : ℕ => ‖squarefullMomentTerm s (p ^ e)‖) := by
  have hp_real_gt_one : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hp_real_pos : 0 < (p : ℝ) := zero_lt_one.trans hp_real_gt_one
  have hr : ‖((p : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hp_real_pos]
    exact inv_lt_one_of_one_lt₀ hp_real_gt_one
  have hgeom :
      Summable fun e : ℕ =>
        ‖(((e : ℝ) ^ s) * ((p : ℝ)⁻¹) ^ e : ℝ)‖ :=
    summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) s hr
  refine hgeom.congr_atTop ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with e he
  have he0 : e ≠ 0 := by omega
  have he1 : e ≠ 1 := by omega
  rw [squarefullMomentTerm_prime_pow hp]
  simp [he0, he1, div_eq_mul_inv, inv_pow]

lemma squarefullMomentTerm_prime_pow_le_factorial_exp
    {s p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
    squarefullMomentTerm s (p ^ e) ≤
      ((4 : ℝ) ^ s * (s.factorial : ℝ) *
        Real.exp ((e : ℝ) / 4)) / (p : ℝ) ^ e := by
  have he0 : e ≠ 0 := by omega
  have he1 : e ≠ 1 := by omega
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_pos : 0 < (p : ℝ) ^ e := pow_pos hp_real_pos e
  rw [squarefullMomentTerm_prime_pow hp]
  simp [he0, he1]
  exact div_le_div_of_nonneg_right
    (nat_pow_le_factorial_mul_exp_quarter s e) hp_pos.le

lemma exp_e_div_four_le_three_halves_pow (e : ℕ) :
    Real.exp ((e : ℝ) / 4) ≤ ((3 : ℝ) / 2) ^ e := by
  calc
    Real.exp ((e : ℝ) / 4) = Real.exp ((1 : ℝ) / 4) ^ e := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ((3 : ℝ) / 2) ^ e :=
      pow_le_pow_left₀ (Real.exp_pos _).le
        (le_of_lt exp_quarter_lt_three_halves) e

lemma squarefullMomentTerm_prime_pow_le_geo
    {s p e : ℕ} (hp : Nat.Prime p) (he : 2 ≤ e) :
    squarefullMomentTerm s (p ^ e) ≤
      (4 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2) *
        ((3 : ℝ) / 4) ^ e := by
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden_pos : 0 < (p : ℝ) ^ e := pow_pos hp_real_pos e
  have hden2_pos : 0 < (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2) := by positivity
  have hp_pow_ge :
      (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2) ≤ (p : ℝ) ^ e := by
    calc
      (p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)
          ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ (e - 2) := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp_two (e - 2))
              (by positivity)
      _ = (p : ℝ) ^ e := by
            rw [← pow_add]
            congr 1
            omega
  have hstep1 :
      squarefullMomentTerm s (p ^ e) ≤
        A * Real.exp ((e : ℝ) / 4) / (p : ℝ) ^ e := by
    simpa [A, mul_assoc] using
      squarefullMomentTerm_prime_pow_le_factorial_exp (s := s) hp he
  have hstep2 :
      A * Real.exp ((e : ℝ) / 4) / (p : ℝ) ^ e ≤
        A * Real.exp ((e : ℝ) / 4) /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) := by
    exact div_le_div_of_nonneg_left
      (mul_nonneg hA_nonneg (Real.exp_pos _).le)
      hden2_pos hp_pow_ge
  have hstep3 :
      A * Real.exp ((e : ℝ) / 4) /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) ≤
        A * ((3 : ℝ) / 2) ^ e /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_e_div_four_le_three_halves_pow e) hA_nonneg)
      hden2_pos.le
  have hidentity :
      A * ((3 : ℝ) / 2) ^ e /
          ((p : ℝ) ^ 2 * (2 : ℝ) ^ (e - 2)) =
        (4 * A / (p : ℝ) ^ 2) * ((3 : ℝ) / 4) ^ e := by
    have h2pos : (0 : ℝ) < 2 ^ (e - 2) := by positivity
    have hp2pos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    rw [show e = 2 + (e - 2) by omega]
    rw [pow_add, pow_add]
    norm_num
    field_simp [hp2pos.ne', h2pos.ne']
    have hmul :
        ((3 : ℝ) / 4) ^ (e - 2) * 2 ^ (e - 2) =
          ((3 : ℝ) / 2) ^ (e - 2) := by
      rw [← mul_pow]
      norm_num
    rw [← hmul]
    ring_nf
  exact hstep1.trans (hstep2.trans (hstep3.trans_eq hidentity))

lemma squarefullMomentTerm_prime_pow_tsum_le
    (s p : ℕ) (hp : Nat.Prime p) :
    (∑' e : ℕ, squarefullMomentTerm s (p ^ e)) ≤
      1 + 16 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2 := by
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  let C : ℝ := 4 * A / (p : ℝ) ^ 2
  let g : ℕ → ℝ := fun e => (if e = 0 then 1 else 0) + C * ((3 : ℝ) / 4) ^ e
  have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hlhs : Summable fun e : ℕ => squarefullMomentTerm s (p ^ e) :=
    (squarefullMomentTerm_prime_pow_summable s p hp).of_norm
  have hsingle : Summable fun e : ℕ => if e = 0 then (1 : ℝ) else 0 :=
    (hasSum_single (0 : ℕ)
      (f := fun e : ℕ => if e = 0 then (1 : ℝ) else 0)
      (by intro e he; simp [he])).summable
  have hgeo : Summable fun e : ℕ => C * ((3 : ℝ) / 4) ^ e :=
    (summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 : ℝ) / 4 < 1)).mul_left C
  have hg : Summable g := hsingle.add hgeo
  have hpoint :
      ∀ e : ℕ, squarefullMomentTerm s (p ^ e) ≤ g e := by
    intro e
    by_cases he0 : e = 0
    · subst e
      change squarefullMomentTerm s 1 ≤ g 0
      rw [squarefullMomentTerm_one]
      simp [g]
      exact hC_nonneg
    · by_cases he1 : e = 1
      · subst e
        rw [squarefullMomentTerm_prime_pow hp]
        simp [g]
        dsimp [C]
        positivity
      · have he2 : 2 ≤ e := by omega
        have h := squarefullMomentTerm_prime_pow_le_geo
          (s := s) (p := p) (e := e) hp he2
        simpa [g, C, A, he0] using h
  calc
    (∑' e : ℕ, squarefullMomentTerm s (p ^ e))
        ≤ ∑' e : ℕ, g e := hlhs.tsum_le_tsum hpoint hg
    _ = 1 + C * (∑' e : ℕ, ((3 : ℝ) / 4) ^ e) := by
          dsimp [g]
          rw [hsingle.tsum_add hgeo]
          rw [tsum_eq_single (0 : ℕ)
            (f := fun e : ℕ => if e = 0 then (1 : ℝ) else 0)]
          · rw [tsum_mul_left]
            simp
          · intro e he
            simp [he]
    _ = 1 + 16 * A / (p : ℝ) ^ 2 := by
          rw [tsum_geometric_of_lt_one
            (by norm_num : (0 : ℝ) ≤ 3 / 4)
            (by norm_num : (3 : ℝ) / 4 < 1)]
          dsimp [C]
          norm_num
          ring
    _ = 1 + 16 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) / (p : ℝ) ^ 2 := by
          rfl

lemma sum_Icc_inv_sq_le_two_bfv (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 2 := by
  classical
  have hIcc :
      Finset.Icc 1 N = (Finset.range N).image (fun ν : ℕ => ν + 1) := by
    ext d
    constructor
    · intro hd
      have hdIcc := Finset.mem_Icc.mp hd
      exact Finset.mem_image.2
        ⟨d - 1, Finset.mem_range.2 (Nat.sub_one_lt_of_le hdIcc.1 hdIcc.2),
          by omega⟩
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨ν, hν, rfl⟩
      exact Finset.mem_Icc.2
        ⟨by omega, Nat.succ_le_iff.2 (Finset.mem_range.1 hν)⟩
  rw [hIcc]
  rw [Finset.sum_image]
  ·
    simpa using sum_inv_sq_le_two_bfv N
  · intro a _ha b _hb h
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)

lemma primes_Icc_inv_sq_sum_le_two_bfv (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset Nat.Prime (Finset.Icc 1 N))
    (by
      intro p _hp _hnot
      positivity)).trans (sum_Icc_inv_sq_le_two_bfv N)

lemma finite_euler_product_one_add_sq_le_exp_sum
    (s : Finset ℕ) {z : ℝ} (hz : 0 ≤ z) :
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2) ≤
      Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) := by
  calc
    s.prod (fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2)
        ≤ s.prod (fun p : ℕ => Real.exp (z / (p : ℝ) ^ 2)) := by
          exact Finset.prod_le_prod
            (s := s)
            (f := fun p : ℕ => (1 : ℝ) + z / (p : ℝ) ^ 2)
            (g := fun p : ℕ => Real.exp (z / (p : ℝ) ^ 2))
            (fun p hp => by
              positivity)
            (fun p hp => by
              have h := Real.add_one_le_exp (z / (p : ℝ) ^ 2)
              linarith)
    _ = Real.exp (s.sum (fun p : ℕ => z / (p : ℝ) ^ 2)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (z * s.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring

lemma finite_squarefull_eulerProduct_le
    (N s : ℕ) :
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
      ≤ Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
  classical
  let P := (Finset.Icc 1 N).filter Nat.Prime
  let A : ℝ := (4 : ℝ) ^ s * (s.factorial : ℝ)
  let z : ℝ := 16 * A
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hz_nonneg : 0 ≤ z := by
    dsimp [z]
    positivity
  have hlocal :
      ∀ p ∈ P,
        (∑' e : ℕ, squarefullMomentTerm s (p ^ e)) ≤
          (1 : ℝ) + z / (p : ℝ) ^ 2 := by
    intro p hp
    have hpprime : Nat.Prime p := (Finset.mem_filter.1 hp).2
    simpa [z, A] using squarefullMomentTerm_prime_pow_tsum_le s p hpprime
  calc
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
        = P.prod fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
          change (P.filter Nat.Prime).prod
              (fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e)) =
            P.prod (fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
          rw [Finset.filter_true_of_mem]
          intro p hp
          exact (Finset.mem_filter.1 hp).2
    _ ≤ P.prod fun p => (1 : ℝ) + z / (p : ℝ) ^ 2 := by
          exact Finset.prod_le_prod
            (s := P)
            (f := fun p => ∑' e : ℕ, squarefullMomentTerm s (p ^ e))
            (g := fun p => (1 : ℝ) + z / (p : ℝ) ^ 2)
            (fun p hp => by
              have hsum_nonneg :
                  0 ≤ ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
                exact tsum_nonneg (fun e => squarefullMomentTerm_nonneg s (p ^ e))
              exact hsum_nonneg)
            hlocal
    _ ≤ Real.exp (z * P.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ) ^ 2)) :=
          finite_euler_product_one_add_sq_le_exp_sum P hz_nonneg
    _ ≤ Real.exp (z * 2) := by
          exact Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left
              (by
                simpa [P] using primes_Icc_inv_sq_sum_le_two_bfv N)
              hz_nonneg)
    _ = Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
          congr 1
          dsimp [z, A]
          ring

lemma eventually_log_const_mul_sqrt_loglog_le_mul_sqrt_loglog
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (A * Real.sqrt (Real.log (Real.log (N : ℝ)))) ≤
        δ * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hsmall :
      (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) =o[atTop]
        fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ))) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)).comp_tendsto
          tendsto_loglog_nat_atTop
    simpa [Real.sqrt_eq_rpow] using h
  filter_upwards [Asymptotics.isLittleO_iff.mp hsmall hδ2,
      eventually_sqrt_loglog_ge (2 * |Real.log A| / δ),
      tendsto_loglog_nat_atTop.eventually_ge_atTop 1] with
    N hlog_small hsqrt_large hY_large
  set Y := Real.log (Real.log (N : ℝ))
  have hY_pos : 0 < Y := zero_lt_one.trans_le (by simpa [Y] using hY_large)
  have hsqrt_pos : 0 < Real.sqrt Y := Real.sqrt_pos.2 hY_pos
  have hlogY_nonneg : 0 ≤ Real.log Y := Real.log_nonneg (by simpa [Y] using hY_large)
  have hleft_norm :
      ‖Real.log Y‖ = Real.log Y := by
    rw [Real.norm_of_nonneg hlogY_nonneg]
  have hright_norm :
      ‖Real.sqrt Y‖ = Real.sqrt Y := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  have hlogY_le : Real.log Y ≤ (δ / 2) * Real.sqrt Y := by
    simpa [Y, hleft_norm, hright_norm] using hlog_small
  have hconst : Real.log A ≤ (δ / 2) * Real.sqrt Y := by
    have hmul : 2 * |Real.log A| ≤ δ * Real.sqrt Y :=
      by simpa [mul_comm] using (div_le_iff₀ hδ).1 hsqrt_large
    have hlogA_le_abs : Real.log A ≤ |Real.log A| := le_abs_self _
    linarith
  have hlogsqrt : Real.log (Real.sqrt Y) = Real.log Y / 2 :=
    Real.log_sqrt hY_pos.le
  calc
    Real.log (A * Real.sqrt Y)
        = Real.log A + Real.log (Real.sqrt Y) := by
            rw [Real.log_mul hA.ne' hsqrt_pos.ne']
    _ = Real.log A + Real.log Y / 2 := by rw [hlogsqrt]
    _ ≤ (δ / 2) * Real.sqrt Y + ((δ / 2) * Real.sqrt Y) / 2 := by
            have hhalf : Real.log Y / 2 ≤ ((δ / 2) * Real.sqrt Y) / 2 := by
              exact div_le_div_of_nonneg_right hlogY_le (by norm_num)
            nlinarith
    _ ≤ δ * Real.sqrt Y := by nlinarith

lemma eventually_squarefull_moment_factor_le_Zscale
    (B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      let s : ℕ := Nat.ceil (B * Real.sqrt (Real.log (Real.log (N : ℝ))))
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Zscale N := by
  let B' : ℝ := B + 1
  let C : ℝ := 4 * B'
  have hB' : 0 < B' := by dsimp [B']; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < (1 / (12 * B') : ℝ) := by positivity
  filter_upwards [eventually_log_const_mul_sqrt_loglog_le_mul_sqrt_loglog
      C (1 / (12 * B')) hC hδ,
      eventually_sqrt_loglog_ge (max 1 (1 / B)),
      tendsto_loglog_nat_atTop.eventually_ge_atTop (max 1 (12 * Real.log 32)),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hlogC hsqrt_large hY_large hNlarge_nat
  set Y := Real.log (Real.log (N : ℝ))
  set R := Real.sqrt Y
  set s : ℕ := Nat.ceil (B * R)
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hY_ge_one : 1 ≤ Y := (le_max_left _ _).trans (by simpa [Y] using hY_large)
  have hY_ge_log32 : 12 * Real.log 32 ≤ Y :=
    (le_max_right _ _).trans (by simpa [Y] using hY_large)
  have hY_pos : 0 < Y := zero_lt_one.trans_le hY_ge_one
  have hR_pos : 0 < R := by simpa [R] using Real.sqrt_pos.2 hY_pos
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hR_ge_one : 1 ≤ R := by
    have hsquares :
        (1 : ℝ) ^ 2 ≤ R ^ 2 := by
      simpa [R, Real.sq_sqrt hY_pos.le] using hY_ge_one
    have habs : |(1 : ℝ)| ≤ |R| := sq_le_sq.mp hsquares
    simpa [abs_of_nonneg hR_nonneg] using habs
  have hBR_nonneg : 0 ≤ B * R := by positivity
  have hs_le : (s : ℝ) ≤ B' * R := by
    have hsceil : (s : ℝ) ≤ B * R + 1 := by
      dsimp [s]
      exact (Nat.ceil_lt_add_one hBR_nonneg).le
    have hone_le_R : (1 : ℝ) ≤ R := hR_ge_one
    dsimp [B']
    nlinarith
  have hfour_s_le : (4 : ℝ) * (s : ℝ) ≤ C * R := by
    dsimp [C]
    nlinarith [hs_le, hR_nonneg]
  have hC_R_pos : 0 < C * R := mul_pos hC hR_pos
  have hC_R_ge_one : 1 ≤ C * R := by
    have hC_ge_one_or : 0 < C := hC
    nlinarith [hC_ge_one_or, hR_ge_one]
  have hlogC_nonneg : 0 ≤ Real.log (C * R) :=
    Real.log_nonneg hC_R_ge_one
  have hs_log_le :
      (s : ℝ) * Real.log (C * R) ≤ Y / 12 := by
    have hlogC' :
        Real.log (C * R) ≤ (1 / (12 * B')) * R := by
      simpa [C, Y, R] using hlogC
    calc
      (s : ℝ) * Real.log (C * R)
          ≤ (B' * R) * Real.log (C * R) := by
            exact mul_le_mul_of_nonneg_right hs_le hlogC_nonneg
      _ ≤ (B' * R) * ((1 / (12 * B')) * R) := by
            exact mul_le_mul_of_nonneg_left hlogC' (by positivity)
      _ = Y / 12 := by
            have hRsq : R ^ 2 = Y := by
              simpa [R] using Real.sq_sqrt hY_pos.le
            have hcoef : B' * (1 / (12 * B')) = (1 / 12 : ℝ) := by
              have hden : (12 : ℝ) * B' ≠ 0 :=
                mul_ne_zero (by norm_num) hB'.ne'
              apply (mul_right_injective₀ hden)
              calc
                (12 * B') * (B' * (1 / (12 * B'))) = B' := by
                  rw [div_eq_mul_inv]
                  rw [show (12 * B') * (B' * (1 * (12 * B')⁻¹)) =
                    B' * ((12 * B') * (12 * B')⁻¹) by ring]
                  rw [mul_inv_cancel₀ hden, mul_one]
                _ = (12 * B') * (1 / 12 : ℝ) := by
                  rw [div_eq_mul_inv]
                  rw [show (12 * B') * (1 * 12⁻¹) =
                    B' * (12 * 12⁻¹) by ring]
                  rw [mul_inv_cancel₀ (by norm_num : (12 : ℝ) ≠ 0), mul_one]
            calc
              (B' * R) * ((1 / (12 * B')) * R)
                  = (B' * (1 / (12 * B'))) * R ^ 2 := by ring
              _ = (1 / 12 : ℝ) * Y := by rw [hcoef, hRsq]
              _ = Y / 12 := by ring
  have hfac :
      ((s.factorial : ℕ) : ℝ) ≤ (s : ℝ) ^ s := by
    exact_mod_cast Nat.factorial_le_pow s
  have hmoment_le_pow :
      (4 : ℝ) ^ s * (s.factorial : ℝ) ≤ ((4 : ℝ) * (s : ℝ)) ^ s := by
    calc
      (4 : ℝ) ^ s * (s.factorial : ℝ)
          ≤ (4 : ℝ) ^ s * (s : ℝ) ^ s := by
            exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = ((4 : ℝ) * (s : ℝ)) ^ s := by rw [mul_pow]
  have hbase_le :
      ((4 : ℝ) * (s : ℝ)) ^ s ≤ (C * R) ^ s := by
    exact pow_le_pow_left₀ (by positivity) hfour_s_le s
  have hpow_exp :
      (C * R) ^ s ≤ Real.exp (Y / 12) := by
    have hpow_eq :
        (C * R) ^ s = Real.exp ((s : ℝ) * Real.log (C * R)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hC_R_pos]
      ring_nf
    rw [hpow_eq]
    exact Real.exp_le_exp.2 hs_log_le
  have hthirtytwo :
      (32 : ℝ) ≤ Real.exp (Y / 12) := by
    have hlog32 : Real.log 32 ≤ Y / 12 := by nlinarith
    calc
      (32 : ℝ) = Real.exp (Real.log 32) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 32)]
      _ ≤ Real.exp (Y / 12) := Real.exp_le_exp.2 hlog32
  have hmain :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Real.exp (Y / 6) := by
    calc
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
          ≤ Real.exp (Y / 12) * Real.exp (Y / 12) := by
            exact mul_le_mul hthirtytwo (hmoment_le_pow.trans (hbase_le.trans hpow_exp))
              (by positivity) (by positivity)
      _ = Real.exp (Y / 6) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hZeq := Zscale_eq_exp_half_loglog_mul_sqrt_loglog hNlarge
  calc
    32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
        ≤ Real.exp (Y / 6) := hmain
    _ ≤ Real.exp (Y / 2) * R := by
          have hexp : Real.exp (Y / 6) ≤ Real.exp (Y / 2) :=
            Real.exp_le_exp.2 (by nlinarith)
          exact hexp.trans (by
            calc
              Real.exp (Y / 2) ≤ Real.exp (Y / 2) * R := by
                nlinarith [Real.exp_pos (Y / 2), hR_ge_one])
    _ = Zscale N := by
          rw [hZeq]

lemma squarefullMoment_eulerProduct_hasSum (N s : ℕ) :
    HasSum
      (fun m : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) =>
        squarefullMomentTerm s m)
      (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
        ∑' e : ℕ, squarefullMomentTerm s (p ^ e)) := by
  exact (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := squarefullMomentTerm s)
    (squarefullMomentTerm_one s)
    (fun {m n} hcop => squarefullMomentTerm_mul_of_coprime s hcop)
    (fun {p} hp => squarefullMomentTerm_prime_pow_summable s p hp)
    ((Finset.Icc 1 N).filter Nat.Prime)).2

lemma squarefull_mem_factored_primes_Icc {N d : ℕ}
    (hd : d ∈ Finset.Icc 1 N) :
    d ∈ Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) := by
  rw [Nat.mem_factoredNumbers']
  intro p hp hpd
  have hdIcc := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hdIcc.1
  have hple : p ≤ N := (Nat.le_of_dvd hdpos hpd).trans hdIcc.2
  exact Finset.mem_filter.2
    ⟨Finset.mem_Icc.2 ⟨Nat.succ_le_of_lt hp.pos, hple⟩, hp⟩

lemma squarefullMomentTerm_eq_of_squarefull_Icc
    {N d s : ℕ} (hd : d ∈ Finset.Icc 1 N) (hsq : IsSquarefull d) :
    squarefullMomentTerm s d = (hExp d : ℝ) ^ s / (d : ℝ) := by
  have hdIcc := Finset.mem_Icc.mp hd
  have hdne : d ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hdIcc.1)
  simp [squarefullMomentTerm, hExpMomentTerm, hsq, hdne]

noncomputable def squarefullFactoredFinset (N : ℕ) :
    Finset (Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime)) :=
  ((Finset.Icc 1 N).filter IsSquarefull).attach.image
    (fun d =>
      (⟨d.1, squarefull_mem_factored_primes_Icc
        (Finset.mem_filter.1 d.2).1⟩ :
        Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime)))

lemma squarefull_recip_sum_eq_factoredFinset_sum (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      =
    ∑ x ∈ squarefullFactoredFinset N, squarefullMomentTerm s x := by
  classical
  unfold squarefullFactoredFinset
  rw [Finset.sum_image]
  · rw [Finset.sum_attach]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    exact (squarefullMomentTerm_eq_of_squarefull_Icc
      (N := N) (d := d) (s := s)
      (Finset.mem_filter.1 hd).1
      (Finset.mem_filter.1 hd).2).symm
  · intro a _ha b _hb hab
    apply Subtype.ext
    exact congrArg
      (fun x : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime) =>
        (x : ℕ)) hab

lemma squarefull_recip_sum_le_factored_tsum (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      ≤
    ∑' m : Nat.factoredNumbers ((Finset.Icc 1 N).filter Nat.Prime),
      squarefullMomentTerm s m := by
  rw [squarefull_recip_sum_eq_factoredFinset_sum]
  exact (squarefullMoment_eulerProduct_hasSum N s).summable.sum_le_tsum
    (squarefullFactoredFinset N)
    (fun x _hx => squarefullMomentTerm_nonneg s x)

lemma squarefull_recip_sum_le_eulerProduct (N s : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0)
      ≤
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
      ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
  rw [← (squarefullMoment_eulerProduct_hasSum N s).tsum_eq]
  exact squarefull_recip_sum_le_factored_tsum N s

lemma hExp_moment_sum_le_squarefull_eulerProduct (N s : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
      (N : ℝ) *
        ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
          ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
  calc
    (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
        ≤ (N : ℝ) *
            ∑ d ∈ Finset.Icc 1 N,
              if IsSquarefull d then (hExp d : ℝ) ^ s / (d : ℝ) else 0 :=
          hExp_moment_sum_le_squarefull_recip_sum N s
    _ ≤ (N : ℝ) *
        ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
          ∑' e : ℕ, squarefullMomentTerm s (p ^ e) := by
          exact mul_le_mul_of_nonneg_left
            (squarefull_recip_sum_le_eulerProduct N s)
            (by positivity)

lemma hExp_rare_count_rankin_real_bound (N s : ℕ) :
    (((Finset.Icc 1 N).filter
        (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
      ≤ (N : ℝ) *
          Real.exp
            (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
              - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
  have hH_nonneg : 0 ≤ hExpCutoff N := by
    unfold hExpCutoff
    positivity
  have hRankin :=
    hExp_large_rankin_sum_le (N := N) (s := s) (H := hExpCutoff N) hH_nonneg
  have hMoment :
      (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s) ≤
        (N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
    calc
      (∑ n ∈ Finset.Icc 1 N, (hExp n : ℝ) ^ s)
          ≤ (N : ℝ) *
              ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime with Nat.Prime p,
                ∑' e : ℕ, squarefullMomentTerm s (p ^ e) :=
            hExp_moment_sum_le_squarefull_eulerProduct N s
      _ ≤ (N : ℝ) *
            Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) := by
            exact mul_le_mul_of_nonneg_left
              (finite_squarefull_eulerProduct_le N s)
              (by positivity)
  have hCombined :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ) *
          hExpCutoff N ^ s
        ≤ (N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))) :=
    hRankin.trans hMoment
  have hHpow :
      hExpCutoff N ^ s =
        Real.exp ((s : ℝ) * Real.sqrt (Real.log (N : ℝ))) := by
    unfold hExpCutoff
    rw [← Real.exp_nat_mul]
  have hHpow_pos :
      0 < hExpCutoff N ^ s := by
    rw [hHpow]
    positivity
  have hdiv :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
        ≤ ((N : ℝ) *
          Real.exp (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)))) /
            hExpCutoff N ^ s := by
    exact (le_div_iff₀ hHpow_pos).2 hCombined
  refine hdiv.trans_eq ?_
  rw [hHpow]
  rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
  congr 1

/--
BFV Lemma 3.2, in the explicit super-`L` form needed for pruning.

The proof is a Rankin moment estimate.  At moment order
`s = ceil((A+2) * sqrt(log log N))`, the cutoff contributes
`exp(-s * sqrt(log N))`, while the squarefull Euler product contributes only
`exp(o(Zscale N))`; the explicit helper above packages that as
`32 * 4^s * s! <= Zscale N`.
-/
theorem hExp_rare_count_rankin_squarefull :
    ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) := by
  intro A hA
  let B : ℝ := A + 2
  have hB : 0 < B := by dsimp [B]; linarith
  filter_upwards [eventually_squarefull_moment_factor_le_Zscale B hB,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hfactor hNlarge_nat
  let s : ℕ := Nat.ceil (B * Real.sqrt (Real.log (Real.log (N : ℝ))))
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
    have hlog_gt_one : 1 < Real.log (N : ℝ) :=
      (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
    exact (zero_lt_one.trans hlog_gt_one).le
  have hZ_nonneg : 0 ≤ Zscale N := by
    rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
    positivity
  have hfactor' :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ)) ≤ Zscale N := by
    simpa [s, B] using hfactor
  have hs_ge :
      B * Real.sqrt (Real.log (Real.log (N : ℝ))) ≤ (s : ℝ) := by
    dsimp [s]
    exact Nat.le_ceil _
  have hs_cutoff :
      B * Zscale N ≤ (s : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
    rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
    calc
      B * (Real.sqrt (Real.log (N : ℝ)) *
          Real.sqrt (Real.log (Real.log (N : ℝ))))
          = (B * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
              Real.sqrt (Real.log (N : ℝ)) := by ring
      _ ≤ (s : ℝ) * Real.sqrt (Real.log (N : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg _)
  have hexponent :
      32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
          - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))
        ≤ -A * Zscale N := by
    have hstep :
        32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
            - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))
          ≤ Zscale N - B * Zscale N := by
      nlinarith [hfactor', hs_cutoff]
    have htarget : Zscale N - B * Zscale N ≤ -A * Zscale N := by
      dsimp [B]
      nlinarith [hZ_nonneg]
    exact hstep.trans htarget
  have hreal :
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
        ≤ (N : ℝ) * Lscale (-A) N := by
    calc
      (((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card : ℝ)
          ≤ (N : ℝ) *
              Real.exp
                (32 * ((4 : ℝ) ^ s * (s.factorial : ℝ))
                  - (s : ℝ) * Real.sqrt (Real.log (N : ℝ))) :=
            hExp_rare_count_rankin_real_bound N s
      _ ≤ (N : ℝ) * Lscale (-A) N := by
            rw [Lscale]
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.2 hexponent) hN_nonneg
  exact Nat.le_floor hreal

/-- BFV Lemma 3.2 in the super-`L` consumer form used by pruning. -/
theorem hExp_rare_count_superL :
    ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) :=
  hExp_rare_count_rankin_squarefull

/-- A subset version of the hExp rarity estimate. -/
theorem hExp_rare_subset_count
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ,
        S ⊆ Finset.Icc 1 N →
        (S.filter fun n => hExpCutoff N < (hExp n : ℝ)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-A) N) := by
  filter_upwards [hExp_rare_count_superL A hA] with N hN S hS
  exact (Finset.card_le_card (by
    intro n hn
    exact Finset.mem_filter.2
      ⟨hS (Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2⟩)).trans hN

end Erdos202
