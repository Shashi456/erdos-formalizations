/-
Erdos Problem 202 -- radical multiplicity in BFV pruning.

For fixed radical, fixed omega, and bounded `hExp`, BFV Lemma 3.3 gives a
finite multiplicity bound.  This is a finite combinatorial theorem, but the
full exponent-vector encoding is kept isolated here so the final pruning file
only consumes a single clean interface.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic

namespace Erdos202

open Finset
open scoped BigOperators

/--
Finite reciprocal-square bound used in the exponent-vector count.

This is the local BFV copy of the elementary estimate
`∑_{m=1}^H 1 / m^2 ≤ 2`.  It is duplicated here rather than importing
`P202Optimization`, which depends on the BFV input layer.
-/
lemma sum_inv_sq_le_two_bfv (H : ℕ) :
    (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have hstrong : ∀ H : ℕ, 1 ≤ H →
      (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤
        2 - 1 / (H : ℝ) := by
    intro H hH
    induction H with
    | zero =>
        cases hH
    | succ H ih =>
        cases H with
        | zero =>
            norm_num
        | succ H =>
            rw [Finset.sum_range_succ]
            have ih' :
                (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  ≤ 2 - 1 / ((H + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2 ≤
                  1 / ((H + 1 : ℕ) : ℝ) -
                    1 / (((H + 1 + 1 : ℕ) : ℝ)) := by
              have hcast :
                  (((H + 1 + 1 : ℕ) : ℝ)) = ((H + 1 : ℕ) : ℝ) + 1 := by
                norm_num
              rw [hcast]
              have hH1 : 0 < ((H + 1 : ℕ) : ℝ) := by positivity
              have hH2 : 0 < ((H + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hH1.ne', hH2.ne']
              ring_nf
              nlinarith [show 0 ≤ (H : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  + 1 / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2
                  ≤ (2 - 1 / ((H + 1 : ℕ) : ℝ))
                      + (1 / ((H + 1 : ℕ) : ℝ) -
                        1 / (((H + 1 + 1 : ℕ) : ℝ))) := by
                    gcongr
              _ = 2 - 1 / ((H + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hH : H = 0
  · simp [hH]
  · have hH1 : 1 ≤ H := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hH)
    exact (hstrong H hH1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (H : ℝ) := by positivity
      linarith)

private lemma one_div_sq_nat_prod_bfv {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
      ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
  simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]

lemma rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  exact Finset.prod_pos (fun p hp => (prime_of_mem_primeSupport hp).pos)

lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 :=
  (rad_pos n).ne'

lemma primeSupport_rad_of_ne_zero {n : ℕ} (_hn : n ≠ 0) :
    primeSupport (rad n) = primeSupport n := by
  classical
  ext p
  constructor
  · intro hpRad
    have hp : Nat.Prime p := prime_of_mem_primeSupport hpRad
    have hpdvd : p ∣ rad n := Nat.dvd_of_factorization_pos (by
      unfold primeSupport at hpRad
      exact Finsupp.mem_support_iff.1 hpRad)
    unfold rad at hpdvd
    rcases (hp.prime.dvd_finset_prod_iff
        (S := primeSupport n) (fun x : ℕ => x)).1 hpdvd with ⟨q, hq, hpq⟩
    have hqprime : Nat.Prime q := prime_of_mem_primeSupport hq
    have hqp : q = p := (hqprime.dvd_iff_eq hp.ne_one).1 hpq
    simpa [hqp] using hq
  · intro hpN
    have hp : Nat.Prime p := prime_of_mem_primeSupport hpN
    have hpdvd : p ∣ rad n := by
      unfold rad
      exact Finset.dvd_prod_of_mem (fun x : ℕ => x) hpN
    exact mem_primeSupport_of_prime_dvd hp (rad_ne_zero n) hpdvd

lemma primeSupport_eq_of_rad_eq {q r : ℕ} (hq : q ≠ 0) (hqr : rad q = r) :
    primeSupport q = primeSupport r := by
  rw [← primeSupport_rad_of_ne_zero hq, hqr]

private lemma factorization_le_hExp_of_mem {q p : ℕ} (hp : p ∈ primeSupport q) :
    q.factorization p ≤ hExp q := by
  have hdvd : q.factorization p ∣ hExp q := by
    unfold hExp
    exact Finset.dvd_prod_of_mem (fun x : ℕ => q.factorization x) hp
  exact Nat.le_of_dvd (hExp_pos q) hdvd

private lemma rad_multiplicity_weight_sum_le
    (S : Finset ℕ) (C : Finset ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hSupp : ∀ q ∈ S, primeSupport q = C)
    (hHbound : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ C.card := by
  classical
  let Index := {p : ℕ // p ∈ C}
  let E : Finset (Index → ℕ) :=
    Fintype.piFinset fun _ : Index => Finset.range (Nat.floor H)
  let vec : ℕ → Index → ℕ := fun q p => q.factorization p.1 - 1
  let term : (Index → ℕ) → ℝ :=
    fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
  have hH_nonneg : 0 ≤ H := by
    linarith
  have hvec_mem : ∀ q ∈ S, vec q ∈ E := by
    intro q hqS
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    have hsupport : primeSupport q = C := hSupp q hqS
    have hpSupport : p.1 ∈ primeSupport q := by
      simp [hsupport, p.2]
    have hfac_pos : 1 ≤ q.factorization p.1 := by
      unfold primeSupport at hpSupport
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
    have hfac_le_hExp : q.factorization p.1 ≤ hExp q :=
      factorization_le_hExp_of_mem hpSupport
    have hfac_le_H : ((q.factorization p.1 : ℕ) : ℝ) ≤ H := by
      have hfac_le_hExp_real :
          ((q.factorization p.1 : ℕ) : ℝ) ≤ (hExp q : ℝ) := by
        exact_mod_cast hfac_le_hExp
      exact hfac_le_hExp_real.trans (hHbound q hqS)
    have hfac_floor : q.factorization p.1 ≤ Nat.floor H :=
      (Nat.le_floor_iff hH_nonneg).2 hfac_le_H
    dsimp [vec]
    omega
  have hvec_inj : Set.InjOn vec S := by
    intro q hqS q' hq'S hqq'
    apply Nat.eq_of_factorization_eq (hSpos q hqS) (hSpos q' hq'S)
    intro p
    by_cases hp : p ∈ C
    · have hcoord := congrFun hqq' ⟨p, hp⟩
      dsimp [vec] at hcoord
      have hsupport : primeSupport q = C := hSupp q hqS
      have hsupport' : primeSupport q' = C := hSupp q' hq'S
      have hfac_pos : 1 ≤ q.factorization p := by
        have hpSupport : p ∈ primeSupport q := by simpa [hsupport] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      have hfac_pos' : 1 ≤ q'.factorization p := by
        have hpSupport : p ∈ primeSupport q' := by simpa [hsupport'] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      omega
    · have hpq : p ∉ primeSupport q := by simpa [hSupp q hqS] using hp
      have hpq' : p ∉ primeSupport q' := by simpa [hSupp q' hq'S] using hp
      rw [Finsupp.notMem_support_iff.1 hpq, Finsupp.notMem_support_iff.1 hpq']
  have hterm_eq :
      ∀ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2) = term (vec q) := by
    intro q hqS
    have hsupport : primeSupport q = C := hSupp q hqS
    have hhexp :
        hExp q = ∏ p : Index, q.factorization p.1 := by
      calc
        hExp q = ∏ p ∈ C, q.factorization p := by
          simp [hExp, hsupport]
        _ = ∏ p : Index, q.factorization p.1 := by
          rw [Finset.prod_coe_sort]
    have hsucc : ∀ p : Index, vec q p + 1 = q.factorization p.1 := by
      intro p
      have hpSupport : p.1 ∈ primeSupport q := by simp [hsupport, p.2]
      have hpos : 1 ≤ q.factorization p.1 := by
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      dsimp [vec]
      omega
    rw [hhexp, one_div_sq_nat_prod_bfv]
    dsimp [term]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [hsucc p]
  calc
    (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2))
        = ∑ q ∈ S, term (vec q) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hterm_eq q hq
    _ = ∑ e ∈ S.image vec, term e := by
            rw [Finset.sum_image]
            intro q hq q' hq' hEq
            exact hvec_inj hq hq' hEq
    _ ≤ ∑ e ∈ E, term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro e he
                rcases Finset.mem_image.mp he with ⟨q, hq, rfl⟩
                exact hvec_mem q hq)
              (by
                intro e _heE _heNot
                dsimp [term]
                positivity)
    _ = ∏ _p : Index,
          ∑ ν ∈ Finset.range (Nat.floor H),
            (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2) := by
            change
              (∑ e ∈ Fintype.piFinset
                  (fun _ : Index => Finset.range (Nat.floor H)),
                ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)) =
              ∏ _p : Index,
                ∑ ν ∈ Finset.range (Nat.floor H),
                  (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)
            exact
              (Finset.sum_prod_piFinset
                (ι := Index) (κ := ℕ) (R := ℝ)
                (s := Finset.range (Nat.floor H))
                (g := fun _p ν => (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)))
    _ ≤ ∏ _p : Index, (2 : ℝ) := by
            exact Finset.prod_le_prod
              (s := (Finset.univ : Finset Index))
              (fun _p _hp => by positivity)
              (fun _p _hp => by
                exact sum_inv_sq_le_two_bfv (Nat.floor H))
    _ = (2 : ℝ) ^ C.card := by
            simp [Index]

/--
BFV Lemma 3.3 multiplicity bound.

For a fixed radical `r`, fixed `omega = K`, and `hExp ≤ H`, the possible
moduli are encoded by exponent vectors on the `K` primes in the radical.  BFV
counts those vectors by
`H^2 * (∑_{ν≥1} ν⁻²)^K ≤ H^2 * 2^K`.

The remaining formal work is finite: construct the exponent-vector injection
from `Nat.factorization`, prove the product bound from `hExp`, and apply
`sum_inv_sq_le_two_bfv`.  No analytic number theory is hidden in this target.
-/
theorem rad_multiplicity_bfv33
    (S : Finset ℕ) (r K : ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hS : ∀ q ∈ S, rad q = r ∧ omega q = K ∧ (hExp q : ℝ) ≤ H) :
    (S.card : ℝ) ≤ H ^ 2 * (2 : ℝ) ^ K := by
  classical
  by_cases hSne : S.Nonempty
  · rcases hSne with ⟨q0, hq0S⟩
    let C : Finset ℕ := primeSupport r
    have hSupp : ∀ q ∈ S, primeSupport q = C := by
      intro q hq
      exact primeSupport_eq_of_rad_eq (hSpos q hq) (hS q hq).1
    have hCcard : C.card = K := by
      have homega := (hS q0 hq0S).2.1
      unfold omega at homega
      rw [hSupp q0 hq0S] at homega
      exact homega
    have hWeighted :
        (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ K := by
      simpa [C, hCcard] using
        rad_multiplicity_weight_sum_le S C H hH hSpos hSupp
          (fun q hq => (hS q hq).2.2)
    have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
    have hHsq_pos : 0 < H ^ 2 := by positivity
    have hTermLower :
        ∀ q ∈ S, (1 : ℝ) / (H ^ 2) ≤
          (1 : ℝ) / ((hExp q : ℝ) ^ 2) := by
      intro q hq
      have hExp_nonneg : 0 ≤ (hExp q : ℝ) := by positivity
      have hExp_pos : 0 < (hExp q : ℝ) := by exact_mod_cast hExp_pos q
      have hExp_le : (hExp q : ℝ) ≤ H := (hS q hq).2.2
      have hsq_le : (hExp q : ℝ) ^ 2 ≤ H ^ 2 := by
        nlinarith [sq_nonneg (H - (hExp q : ℝ))]
      exact one_div_le_one_div_of_le (by positivity) hsq_le
    have hCardScaled :
        (S.card : ℝ) * ((1 : ℝ) / (H ^ 2)) ≤ (2 : ℝ) ^ K := by
      calc
        (S.card : ℝ) * ((1 : ℝ) / (H ^ 2))
            = ∑ _q ∈ S, ((1 : ℝ) / (H ^ 2)) := by
                simp
        _ ≤ ∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2) := by
                exact Finset.sum_le_sum hTermLower
        _ ≤ (2 : ℝ) ^ K := hWeighted
    have hmul := mul_le_mul_of_nonneg_right hCardScaled hHsq_pos.le
    field_simp [hHsq_pos.ne'] at hmul
    nlinarith
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hSne
    have hnonneg : 0 ≤ H ^ 2 * (2 : ℝ) ^ K := by positivity
    simpa [hEmpty] using hnonneg

end Erdos202
