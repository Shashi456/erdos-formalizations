/-
Erdős Problems 283 + 351 — §2 collision avoidance via 2-adic / 3-adic valuations.

For all sufficiently large `N`, all denominators that may appear after any
collection of switches are pairwise distinct. The argument uses
`(v₂(d), v₃(d))` valuation profiles:

  D j        : (0, 0)        u_j is coprime to 6
  2 D j      : (1, 0)
  3 D j      : (0, 1)
  6 D j      : (1, 1)
  τ_N        : (2, 2)        τ_N = 36 u_{N+1}
  Λ f        : v₂ ≥ 3        (we choose 8 ∣ Λ)
  c_ν, e c_ν : avoided by construction during correction-slot setup

The pairwise-distinctness theorem `all_denominators_distinct_after_switches`
is the goal; sub-lemmas formalize the per-pair valuation argument.
-/

import Erdos.P283.Basic
import Erdos.P283.MainSlots

namespace PolynomialEgyptianSums

open Nat

/-- `u j = 36 j + 1` is coprime to `6`. -/
lemma u_coprime_six (j : ℕ) : Nat.Coprime (u j) 6 := by
  unfold u P
  rw [show 36 * j + 1 = 1 + 6 * (6 * j) from by ring]
  rw [Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left 6

/-- `D j = u j · u (j+1)` is coprime to `6`. -/
lemma D_coprime_six (j : ℕ) : Nat.Coprime (D j) 6 := by
  unfold D
  exact (u_coprime_six j).mul_left (u_coprime_six (j + 1))

/-- For `h ∈ {1, 2, 3, 6}`, `(v₂(h · D j), v₃(h · D j))` is `(0,0), (1,0), (0,1),
(1,1)` respectively. -/
lemma main_valuation_profile (j : ℕ) :
    (padicValNat 2 (1 * D j), padicValNat 3 (1 * D j)) = (0, 0) ∧
    (padicValNat 2 (2 * D j), padicValNat 3 (2 * D j)) = (1, 0) ∧
    (padicValNat 2 (3 * D j), padicValNat 3 (3 * D j)) = (0, 1) ∧
    (padicValNat 2 (6 * D j), padicValNat 3 (6 * D j)) = (1, 1) := by
  have hD_ne : D j ≠ 0 := by unfold D u P; positivity
  have hcop := D_coprime_six j
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2_ndvd : ¬ (2 : ℕ) ∣ D j := by
    have h2cop : Nat.Coprime (D j) 2 := by
      have h6 : (2 : ℕ) ∣ 6 := by norm_num
      exact hcop.coprime_dvd_right h6
    have h2cop' : Nat.Coprime 2 (D j) := h2cop.symm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h2cop'
  have h3_ndvd : ¬ (3 : ℕ) ∣ D j := by
    have h3cop : Nat.Coprime (D j) 3 := by
      have h6 : (3 : ℕ) ∣ 6 := by norm_num
      exact hcop.coprime_dvd_right h6
    have h3cop' : Nat.Coprime 3 (D j) := h3cop.symm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3cop'
  have h2D : padicValNat 2 (D j) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h2_ndvd))
  have h3D : padicValNat 3 (D j) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h3_ndvd))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- h = 1
    rw [one_mul]
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨h2D, h3D⟩
  · -- h = 2
    have e2 : padicValNat 2 (2 * D j) = 1 := by
      rw [padicValNat.mul (by norm_num) hD_ne, h2D, add_zero, padicValNat_self]
    have e3 : padicValNat 3 (2 * D j) = 0 := by
      apply padicValNat.eq_zero_iff.mpr
      refine Or.inr (Or.inr ?_)
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h2 | h2
      · norm_num at h2
      · exact h3_ndvd h2
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨e2, e3⟩
  · -- h = 3
    have e2 : padicValNat 2 (3 * D j) = 0 := by
      apply padicValNat.eq_zero_iff.mpr
      refine Or.inr (Or.inr ?_)
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h2 | h2
      · norm_num at h2
      · exact h2_ndvd h2
    have e3 : padicValNat 3 (3 * D j) = 1 := by
      rw [padicValNat.mul (by norm_num) hD_ne, h3D, add_zero, padicValNat_self]
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨e2, e3⟩
  · -- h = 6
    have h6_eq : (6 : ℕ) = 2 * 3 := by norm_num
    have e2 : padicValNat 2 (6 * D j) = 1 := by
      rw [show (6 : ℕ) * D j = 2 * (3 * D j) from by ring]
      rw [padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hD_ne)]
      rw [padicValNat_self]
      have : padicValNat 2 (3 * D j) = 0 := by
        apply padicValNat.eq_zero_iff.mpr
        refine Or.inr (Or.inr ?_)
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h2 | h2
        · norm_num at h2
        · exact h2_ndvd h2
      omega
    have e3 : padicValNat 3 (6 * D j) = 1 := by
      rw [show (6 : ℕ) * D j = 3 * (2 * D j) from by ring]
      rw [padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hD_ne)]
      rw [padicValNat_self]
      have : padicValNat 3 (2 * D j) = 0 := by
        apply padicValNat.eq_zero_iff.mpr
        refine Or.inr (Or.inr ?_)
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h2 | h2
        · norm_num at h2
        · exact h3_ndvd h2
      omega
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨e2, e3⟩

/-- `τ_N = 36 · u_{N+1}` has valuation profile `(2, 2)`. -/
lemma tau_valuation_profile (N : ℕ) :
    padicValNat 2 (tau N) = 2 ∧ padicValNat 3 (tau N) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu_ne : u (N + 1) ≠ 0 := by unfold u P; positivity
  have hcop := u_coprime_six (N + 1)
  have h2_ndvd : ¬ (2 : ℕ) ∣ u (N + 1) := by
    have h2cop : Nat.Coprime (u (N + 1)) 2 := by
      have h6 : (2 : ℕ) ∣ 6 := by norm_num
      exact hcop.coprime_dvd_right h6
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h2cop.symm
  have h3_ndvd : ¬ (3 : ℕ) ∣ u (N + 1) := by
    have h3cop : Nat.Coprime (u (N + 1)) 3 := by
      have h6 : (3 : ℕ) ∣ 6 := by norm_num
      exact hcop.coprime_dvd_right h6
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3cop.symm
  have h2u : padicValNat 2 (u (N + 1)) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h2_ndvd))
  have h3u : padicValNat 3 (u (N + 1)) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h3_ndvd))
  -- tau N = P * u (N+1) = 36 * u (N+1)
  have htau_eq : tau N = 2^2 * (3^2 * u (N + 1)) := by
    unfold tau P; ring
  refine ⟨?_, ?_⟩
  · rw [htau_eq]
    rw [padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hu_ne)]
    rw [padicValNat.prime_pow]
    have h32u : padicValNat 2 (3^2 * u (N + 1)) = 0 := by
      apply padicValNat.eq_zero_iff.mpr
      refine Or.inr (Or.inr ?_)
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h2 | h2
      · have : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        norm_num at this
      · exact h2_ndvd h2
    omega
  · have htau_eq3 : tau N = 3^2 * (2^2 * u (N + 1)) := by
      unfold tau P; ring
    rw [htau_eq3]
    rw [padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hu_ne)]
    rw [padicValNat.prime_pow]
    have h22u : padicValNat 3 (2^2 * u (N + 1)) = 0 := by
      apply padicValNat.eq_zero_iff.mpr
      refine Or.inr (Or.inr ?_)
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h2 | h2
      · have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
        norm_num at this
      · exact h3_ndvd h2
    omega

/-- For `8 ∣ Λ`, `Λ ≥ 1`, and `f ≥ 1`, `v₂(Λ f) ≥ 3`. -/
lemma filler_v2_at_least_three (Λ f : ℕ) (hΛ : 8 ∣ Λ) (hΛpos : 1 ≤ Λ) (hf : 1 ≤ f) :
    3 ≤ padicValNat 2 (Λ * f) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : (2 : ℕ) ^ 3 ∣ Λ * f := by
    have h8eq : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [h8eq]
    exact dvd_mul_of_dvd_left hΛ f
  have hne : Λ * f ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  exact (padicValNat_dvd_iff_le hne).mp h8

/-! ## Collision avoidance master lemma

For all sufficiently large `N`, given the collection of all main-slot copies
(`h · D j` for `h ∈ {1,2,3,6}`, `J ≤ j ≤ N`), the endpoint `τ_N`, the
correction denominators (and their `e ∈ G_ν` multiples), and the filler
denominators `Λ f`, all values are pairwise distinct.

Full statement deferred — assembled inside `Theorem1.lean`. -/

end PolynomialEgyptianSums
