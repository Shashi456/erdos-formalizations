/-
Erdős Problem 202 — Arithmetic layer.

Project-local definitions of `omega`, `rad`, `h(n) = ∏ p^{vₚ(n)} factors`,
and the exact prime-power block `exactBlock C q = ∏_{p ∈ C} p^{vₚ(q)}`.

All built on top of `Nat.factorization` to avoid drift between
`Nat.primeFactorsList`, `padicValNat`, and `multiplicity`.
-/

import Mathlib
import Erdos.P202.P202Basic

namespace Erdos202

open Finset
open scoped BigOperators

/-- The (multi-) set of prime divisors of `n`, as a `Finset`. Equal to
`n.factorization.support` for `n ≠ 0`. -/
def primeSupport (n : ℕ) : Finset ℕ :=
  n.factorization.support

/-- Number of distinct prime factors. Standard `ω(n)`. -/
def omega (n : ℕ) : ℕ :=
  (primeSupport n).card

/-- Radical of `n`: product of distinct prime divisors. -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, p

/-- BFV's `h(n)`: product of the prime *exponents* in the factorization of `n`.
Note: this is NOT the radical and is NOT `n` itself; it is the auxiliary
quantity that BFV pruning bounds by `exp(sqrt(log x))` on the surviving
moduli. -/
def hExp (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, n.factorization p

/-- The exact prime-power block of `q` along the prime set `C`:
`exactBlock C q = ∏_{p ∈ C} p^{vₚ(q)}`. -/
def exactBlock (C : Finset ℕ) (q : ℕ) : ℕ :=
  ∏ p ∈ C, p ^ q.factorization p

/-! ## Basic API -/

lemma hExp_pos (n : ℕ) : 0 < hExp n := by
  unfold hExp primeSupport
  exact Finset.prod_pos (fun _p hp =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp))

lemma hExp_one_le (n : ℕ) : 1 ≤ hExp n :=
  hExp_pos n

lemma hExp_one : hExp 1 = 1 := by
  simp [hExp, primeSupport]

lemma hExp_inv_sq_pos (n : ℕ) : 0 < (1 : ℝ) / ((hExp n : ℝ) ^ 2) := by
  have hn : 0 < (hExp n : ℝ) := by exact_mod_cast hExp_pos n
  positivity

lemma hExp_inv_sq_le_one (n : ℕ) : (1 : ℝ) / ((hExp n : ℝ) ^ 2) ≤ 1 := by
  have hn : 1 ≤ (hExp n : ℝ) := by exact_mod_cast hExp_one_le n
  have hpos : 0 < ((hExp n : ℝ) ^ 2) := by positivity
  field_simp [hpos.ne']
  nlinarith [sq_nonneg ((hExp n : ℝ) - 1)]

lemma prime_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) : Nat.Prime p := by
  unfold primeSupport at hp
  rw [Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

lemma mem_primeSupport_of_prime_dvd {n p : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpn : p ∣ n) : p ∈ primeSupport n := by
  unfold primeSupport
  rw [Finsupp.mem_support_iff]
  exact hp.factorization_pos_of_dvd hn hpn |>.ne'

lemma coprime_of_disjoint_primeSupport {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hdisj : Disjoint (primeSupport m) (primeSupport n)) :
    Nat.Coprime m n := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpm hpn
  exact (Finset.disjoint_left.1 hdisj)
    (mem_primeSupport_of_prime_dvd hp hm hpm)
    (mem_primeSupport_of_prime_dvd hp hn hpn)

lemma primeSupport_disjoint_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    Disjoint (primeSupport m) (primeSupport n) := by
  rw [Finset.disjoint_left]
  intro p hpm hpn
  have hp : Nat.Prime p := prime_of_mem_primeSupport hpm
  have hpdm : p ∣ m := Nat.dvd_of_factorization_pos (by
    unfold primeSupport at hpm
    exact Finsupp.mem_support_iff.1 hpm)
  have hpdn : p ∣ n := Nat.dvd_of_factorization_pos (by
    unfold primeSupport at hpn
    exact Finsupp.mem_support_iff.1 hpn)
  have hp1 : p ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hpdm hpdn
  exact hp.not_dvd_one hp1

lemma primeSupport_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    primeSupport (m * n) = primeSupport m ∪ primeSupport n := by
  unfold primeSupport
  rw [Nat.factorization_mul_of_coprime hcop]
  exact Finsupp.support_add_eq (primeSupport_disjoint_of_coprime hcop)

lemma omega_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    omega (m * n) = omega m + omega n := by
  unfold omega
  rw [primeSupport_mul_of_coprime hcop]
  exact Finset.card_union_of_disjoint (primeSupport_disjoint_of_coprime hcop)

lemma hExp_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    hExp (m * n) = hExp m * hExp n := by
  unfold hExp
  rw [primeSupport_mul_of_coprime hcop]
  rw [Finset.prod_union (primeSupport_disjoint_of_coprime hcop)]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hpnot : p ∉ primeSupport n :=
      (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
    have hnzero : n.factorization p = 0 := by
      unfold primeSupport at hpnot
      exact Finsupp.notMem_support_iff.1 hpnot
    rw [Nat.factorization_mul_of_coprime hcop]
    simp [hnzero]
  · apply Finset.prod_congr rfl
    intro p hp
    have hpnot : p ∉ primeSupport m :=
      (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
    have hmzero : m.factorization p = 0 := by
      unfold primeSupport at hpnot
      exact Finsupp.notMem_support_iff.1 hpnot
    rw [Nat.factorization_mul_of_coprime hcop]
    simp [hmzero]

lemma exactBlock_congr_on {C : Finset ℕ} {m n : ℕ}
    (h : ∀ p ∈ C, m.factorization p = n.factorization p) :
    exactBlock C m = exactBlock C n := by
  unfold exactBlock
  apply Finset.prod_congr rfl
  intro p hp
  rw [h p hp]

lemma exactBlock_dvd (C : Finset ℕ) (q : ℕ) : exactBlock C q ∣ q := by
  by_cases hq : q = 0
  · simp [hq]
  · nth_rw 2 [← Nat.factorization_prod_pow_eq_self hq]
    unfold exactBlock
    have hfilter :
        (∏ p ∈ C, p ^ q.factorization p) =
          ∏ p ∈ C.filter (fun p => p ∈ q.factorization.support),
            p ^ q.factorization p := by
      refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
      intro p hpC hpNot
      have hpnotmem : p ∉ q.factorization.support := by
        intro hp
        exact hpNot (Finset.mem_filter.2 ⟨hpC, hp⟩)
      have hzero : q.factorization p = 0 := by
        by_contra hne
        exact hpnotmem (Finsupp.mem_support_iff.2 hne)
      simp [hzero]
    rw [hfilter]
    exact Finset.prod_dvd_prod_of_subset
      (C.filter (fun p => p ∈ q.factorization.support))
      q.factorization.support
      (fun p => p ^ q.factorization p)
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)

lemma factorization_exactBlock_of_mem {C : Finset ℕ} {q p : ℕ}
    (hC : ∀ r ∈ C, Nat.Prime r) (hpC : p ∈ C) :
    (exactBlock C q).factorization p = q.factorization p := by
  unfold exactBlock
  have hprod_ne : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
    intro x hx
    exact pow_ne_zero _ (hC x hx).ne_zero
  rw [Nat.factorization_prod hprod_ne, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single p]
  · rw [(hC p hpC).factorization_pow, Finsupp.single_eq_same]
  · intro x hx hxp
    rw [(hC x hx).factorization_pow]
    exact Finsupp.single_eq_of_ne hxp.symm
  · intro hpnot
    exact (hpnot hpC).elim

lemma primeSupport_exactBlock {C : Finset ℕ} {q : ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p)
    (hCq : C ⊆ primeSupport q) :
    primeSupport (exactBlock C q) = C := by
  unfold primeSupport exactBlock
  ext p
  have hprod_ne : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
    intro x hx
    exact pow_ne_zero _ (hC x hx).ne_zero
  rw [Nat.factorization_prod hprod_ne, Finsupp.mem_support_iff]
  constructor
  · intro hsum
    by_contra hpC
    apply hsum
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero_iff]
    intro x hx
    have hxne : x ≠ p := by
      intro hxp
      exact hpC (hxp ▸ hx)
    rw [(hC x hx).factorization_pow]
    exact Finsupp.single_eq_of_ne hxne.symm
  · intro hpC
    have hp : Nat.Prime p := hC p hpC
    have hqpos : q.factorization p ≠ 0 := Finsupp.mem_support_iff.1 (hCq hpC)
    intro hsum
    rw [Finsupp.finset_sum_apply] at hsum
    have hterm := (Finset.sum_eq_zero_iff.mp hsum) p hpC
    rw [hp.factorization_pow, Finsupp.single_eq_same] at hterm
    exact hqpos hterm

lemma omega_exactBlock {C : Finset ℕ} {q : ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p)
    (hCq : C ⊆ primeSupport q) :
    omega (exactBlock C q) = C.card := by
  simp [omega, primeSupport_exactBlock hC hCq]

lemma hExp_exactBlock_le_hExp (C : Finset ℕ) (q : ℕ) :
    hExp (exactBlock C q) ≤ hExp q := by
  by_cases hq : q = 0
  · simp [hExp, primeSupport, exactBlock, hq]
  · have hdvd : exactBlock C q ∣ q := exactBlock_dvd C q
    have hdne : exactBlock C q ≠ 0 := by
      exact (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)).ne'
    have hlefac : (exactBlock C q).factorization ≤ q.factorization :=
      (Nat.factorization_le_iff_dvd hdne hq).2 hdvd
    have hsub : primeSupport (exactBlock C q) ⊆ primeSupport q := by
      intro p hp
      unfold primeSupport at hp ⊢
      rw [Finsupp.mem_support_iff] at hp ⊢
      exact (Nat.pos_of_ne_zero hp).trans_le (hlefac p) |>.ne'
    unfold hExp
    have hprod1 :
        (∏ p ∈ primeSupport (exactBlock C q), (exactBlock C q).factorization p)
          ≤ ∏ p ∈ primeSupport (exactBlock C q), q.factorization p := by
      exact Finset.prod_le_prod' (fun p _hp => hlefac p)
    have hprod2 :
        (∏ p ∈ primeSupport (exactBlock C q), q.factorization p)
          ≤ ∏ p ∈ primeSupport q, q.factorization p := by
      exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _hpnot => by
        unfold primeSupport at hp
        rw [Finsupp.mem_support_iff] at hp
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
    exact hprod1.trans hprod2

lemma hExp_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    hExp m ≤ hExp n := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hlefac : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hmn
  have hsub : primeSupport m ⊆ primeSupport n := by
    intro p hp
    unfold primeSupport at hp ⊢
    rw [Finsupp.mem_support_iff] at hp ⊢
    exact (Nat.pos_of_ne_zero hp).trans_le (hlefac p) |>.ne'
  unfold hExp
  have hprod1 :
      (∏ p ∈ primeSupport m, m.factorization p)
        ≤ ∏ p ∈ primeSupport m, n.factorization p := by
    exact Finset.prod_le_prod' (fun p _hp => hlefac p)
  have hprod2 :
      (∏ p ∈ primeSupport m, n.factorization p)
        ≤ ∏ p ∈ primeSupport n, n.factorization p := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _hpnot => by
      unfold primeSupport at hp
      rw [Finsupp.mem_support_iff] at hp
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
  exact hprod1.trans hprod2

/-- The "remaining support" after removing a fixed product `P`. Used in the
chain construction: `A(q) = primeSupport (q / P)`. -/
def remainingSupport (P q : ℕ) : Finset ℕ :=
  primeSupport (q / P)

lemma primeSupport_subset_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    primeSupport m ⊆ primeSupport n := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hle : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hmn
  intro p hp
  unfold primeSupport at hp ⊢
  rw [Finsupp.mem_support_iff] at hp ⊢
  intro hnzero
  exact hp (Nat.eq_zero_of_le_zero (by simpa [hnzero] using hle p))

lemma omega_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    omega m ≤ omega n := by
  unfold omega
  exact Finset.card_le_card (primeSupport_subset_of_dvd hmn hn)

lemma primeSupport_div_subset_of_dvd {P q : ℕ} (hPq : P ∣ q) (hq : q ≠ 0) :
    primeSupport (q / P) ⊆ primeSupport q :=
  primeSupport_subset_of_dvd (by
    refine ⟨P, ?_⟩
    exact (Nat.div_mul_cancel hPq).symm) hq

lemma primeSupport_eq_union_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0) :
    primeSupport q = primeSupport P ∪ primeSupport (q / P) := by
  ext p
  unfold primeSupport
  rw [Finset.mem_union]
  simp only [Finsupp.mem_support_iff]
  constructor
  · intro hqfac
    by_cases hPfac : P.factorization p = 0
    · right
      have hdivfac :
          (q / P).factorization p = q.factorization p - P.factorization p := by
        rw [Nat.factorization_div hPq]
        rfl
      rw [hdivfac, hPfac, Nat.sub_zero]
      exact hqfac
    · exact Or.inl hPfac
  · rintro (hPfac | hdivfac)
    · have hle : P.factorization ≤ q.factorization :=
        (Nat.factorization_le_iff_dvd hP hq).2 hPq
      intro hqzero
      exact hPfac (Nat.eq_zero_of_le_zero (by simpa [hqzero] using hle p))
    · have hmem : p ∈ primeSupport (q / P) := by
        unfold primeSupport
        rw [Finsupp.mem_support_iff]
        exact hdivfac
      have hmemq := primeSupport_div_subset_of_dvd hPq hq hmem
      unfold primeSupport at hmemq
      rwa [Finsupp.mem_support_iff] at hmemq

lemma mem_remainingSupport_iff_factorization_lt {P q p : ℕ} (hPq : P ∣ q) :
    p ∈ remainingSupport P q ↔ P.factorization p < q.factorization p := by
  unfold remainingSupport primeSupport
  rw [Finsupp.mem_support_iff, Nat.factorization_div hPq]
  exact Nat.sub_ne_zero_iff_lt

lemma omega_eq_add_omega_div_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
    (hdisj : Disjoint (primeSupport P) (primeSupport (q / P))) :
    omega q = omega P + omega (q / P) := by
  unfold omega
  rw [primeSupport_eq_union_of_dvd hPq hP hq, Finset.card_union_of_disjoint hdisj]

lemma omega_div_eq_sub_omega_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
    (hdisj : Disjoint (primeSupport P) (primeSupport (q / P))) :
    omega (q / P) = omega q - omega P := by
  have hsum := omega_eq_add_omega_div_of_dvd hPq hP hq hdisj
  omega

lemma eq_one_of_omega_eq_zero {n : ℕ} (hn : n ≠ 0) (hω : omega n = 0) :
    n = 1 := by
  have hsupp : primeSupport n = ∅ := by
    have hcard : (primeSupport n).card = 0 := by simpa [omega] using hω
    exact Finset.card_eq_zero.mp hcard
  unfold primeSupport at hsupp
  have hprod_eq_one : n.factorization.prod (fun p e => p ^ e) = 1 := by
    unfold Finsupp.prod
    rw [hsupp]
    simp
  have hprod := Nat.factorization_prod_pow_eq_self hn
  rw [← hprod]
  exact hprod_eq_one

lemma gcd_dvd_of_disjoint_remainingSupport {P q r : ℕ}
    (hPq : P ∣ q) (hPr : P ∣ r)
    (hP : P ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hdisj : Disjoint (remainingSupport P q) (remainingSupport P r)) :
    Nat.gcd q r ∣ P := by
  rw [← Nat.factorization_le_iff_dvd (by
      intro hg
      exact hq (Nat.gcd_eq_zero_iff.mp hg).1) hP]
  rw [Nat.factorization_gcd hq hr]
  intro p
  rw [Finsupp.inf_apply]
  have hPq_fac : P.factorization p ≤ q.factorization p :=
    (Nat.factorization_le_iff_dvd hP hq).2 hPq p
  have hPr_fac : P.factorization p ≤ r.factorization p :=
    (Nat.factorization_le_iff_dvd hP hr).2 hPr p
  by_cases hqextra : P.factorization p < q.factorization p
  · have hrnot : ¬ P.factorization p < r.factorization p := by
      intro hrextra
      exact (Finset.disjoint_left.1 hdisj)
        ((mem_remainingSupport_iff_factorization_lt hPq).2 hqextra)
        ((mem_remainingSupport_iff_factorization_lt hPr).2 hrextra)
    have hrle : r.factorization p ≤ P.factorization p := le_of_not_gt hrnot
    exact le_trans (min_le_right _ _) hrle
  · have hqle : q.factorization p ≤ P.factorization p := le_of_not_gt hqextra
    exact le_trans (min_le_left _ _) hqle

end Erdos202
