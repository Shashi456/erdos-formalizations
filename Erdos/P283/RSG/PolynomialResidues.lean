/-
Copyright (c) 2026

Denominator-clearing and residue lemmas for Graham's complete polynomial
sequence theorem.
-/

import Mathlib

namespace Erdos.P283.RSG

open Polynomial

/-! ## Denominator clearing -/

/-- `B p(x) ∈ ℤ[x]`: there is an integer-coefficient polynomial whose rational
coefficient map is `B * p`. -/
def HasIntegralMultiple (B : ℕ) (p : ℚ[X]) : Prop :=
  ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) = Polynomial.C (B : ℚ) * p

/-- Every rational polynomial has a positive integral multiple. -/
theorem exists_integral_multiple (p : ℚ[X]) :
    ∃ B : ℕ, 1 ≤ B ∧ HasIntegralMultiple B p := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨B₁, hB₁, P₁, hP₁⟩ := hp
      obtain ⟨B₂, hB₂, P₂, hP₂⟩ := hq
      refine ⟨B₁ * B₂, ?_, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr
          (mul_ne_zero (Nat.one_le_iff_ne_zero.mp hB₁) (Nat.one_le_iff_ne_zero.mp hB₂))
      · refine ⟨Polynomial.C (B₂ : ℤ) * P₁ + Polynomial.C (B₁ : ℤ) * P₂, ?_⟩
        simp [Polynomial.map_add, Polynomial.map_mul, hP₁, hP₂]
        ring
  | monomial n c =>
      refine ⟨c.den, c.den_pos, Polynomial.monomial n c.num, ?_⟩
      rw [Polynomial.map_monomial, Polynomial.C_mul_monomial]
      congr 1
      show (c.num : ℚ) = (c.den : ℚ) * c
      have h : (c.num : ℚ) / (c.den : ℚ) = c := c.num_div_den
      field_simp at h
      linarith

/-! ## Polynomial congruences -/

/-- Integer-coefficient polynomial evaluation respects integer congruence. -/
lemma int_poly_eval_congr (P : ℤ[X]) {M x y : ℤ}
    (hxy : x ≡ y [ZMOD M]) :
    (P.eval x : ℤ) ≡ P.eval y [ZMOD M] := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval_add, Polynomial.eval_add]
      exact hp.add hq
  | monomial n c =>
      rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
      exact (Int.ModEq.refl c).mul (hxy.pow n)

/-- Denominator-cleared periodicity for rational polynomial values, stated only
for inputs where the rational values are represented by integers. -/
theorem polynomial_periodicity_of_integral_values
    (p : ℚ[X])
    (B : ℕ) (hBpos : 1 ≤ B) (hB : HasIntegralMultiple B p)
    (m : ℕ) (_hm : 1 ≤ m) (x y : ℤ) (zx zy : ℤ)
    (hzx : (zx : ℚ) = p.eval (x : ℚ))
    (hzy : (zy : ℚ) = p.eval (y : ℚ))
    (hxy : x ≡ y [ZMOD ((m * B : ℕ) : ℤ)]) :
    zx ≡ zy [ZMOD ((m : ℕ) : ℤ)] := by
  obtain ⟨R, hR⟩ := hB
  have h_R_congr : R.eval x ≡ R.eval y [ZMOD ((m * B : ℕ) : ℤ)] :=
    int_poly_eval_congr R hxy
  have h_R_eval : ∀ z : ℤ, ((R.eval z : ℤ) : ℚ) = (B : ℚ) * p.eval (z : ℚ) := by
    intro z
    have h1 : ((R.map (Int.castRingHom ℚ)).eval ((z : ℤ) : ℚ)) =
        (Polynomial.C (B : ℚ) * p).eval ((z : ℚ)) := by
      rw [hR]
    rw [Polynomial.eval_map, Polynomial.eval_mul, Polynomial.eval_C] at h1
    have h2 : Polynomial.eval₂ (Int.castRingHom ℚ) ((z : ℤ) : ℚ) R =
        ((R.eval z : ℤ) : ℚ) :=
      Polynomial.eval₂_at_apply (Int.castRingHom ℚ) z
    rw [h2] at h1
    exact h1
  have h_R_x : R.eval x = (B : ℤ) * zx := by
    have h1 := h_R_eval x
    have : ((R.eval x : ℤ) : ℚ) = (((B : ℤ) * zx : ℤ) : ℚ) := by
      push_cast
      rw [h1, ← hzx]
    exact_mod_cast this
  have h_R_y : R.eval y = (B : ℤ) * zy := by
    have h1 := h_R_eval y
    have : ((R.eval y : ℤ) : ℚ) = (((B : ℤ) * zy : ℤ) : ℚ) := by
      push_cast
      rw [h1, ← hzy]
    exact_mod_cast this
  rw [h_R_x, h_R_y] at h_R_congr
  have hBpos_int : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hBpos
  have hBne : (B : ℤ) ≠ 0 := ne_of_gt hBpos_int
  have h_dvd : ((m * B : ℕ) : ℤ) ∣ (B : ℤ) * zy - (B : ℤ) * zx :=
    Int.modEq_iff_dvd.mp h_R_congr
  have h_dvd' : ((m * B : ℕ) : ℤ) ∣ (B : ℤ) * (zy - zx) := by
    have heq : (B : ℤ) * zy - (B : ℤ) * zx = (B : ℤ) * (zy - zx) := by ring
    rwa [heq] at h_dvd
  have hmB : ((m * B : ℕ) : ℤ) = (B : ℤ) * (m : ℤ) := by
    push_cast
    ring
  rw [hmB] at h_dvd'
  have h_m_dvd : (m : ℤ) ∣ zy - zx :=
    (mul_dvd_mul_iff_left hBne).mp h_dvd'
  exact Int.modEq_iff_dvd.mpr h_m_dvd

/-! ## Infinitely many nonzero prime residues -/

/-- If every prime misses at least one positive integer value of `p`, then every
prime misses arbitrarily late positive integer values of `p`. This is the
denominator-clearing periodicity step in Graham's residue-cover argument. -/
theorem infinite_nondivisibility_of_no_fixed_prime
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (h_gcd_one :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ n : ℕ, 1 ≤ n ∧ ∃ z : ℤ,
          (z : ℚ) = p.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z)) :
    ∀ ℓ : ℕ, ℓ.Prime →
      ∀ N : ℕ, ∃ n ≥ N,
        ∃ z : ℤ, (z : ℚ) = p.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z) := by
  intro ℓ hℓ N
  obtain ⟨B, hBpos, hB⟩ := exists_integral_multiple p
  obtain ⟨n₀, hn₀, z₀, hz₀, hz₀_ndvd⟩ := h_gcd_one ℓ hℓ
  let step : ℕ := ℓ * B
  let n : ℕ := n₀ + (N + 1) * step
  have hstep_pos : 0 < step := by
    exact Nat.mul_pos hℓ.pos (lt_of_lt_of_le Nat.zero_lt_one hBpos)
  have hn_pos : 1 ≤ n := by
    dsimp [n]
    exact hn₀.trans (Nat.le_add_right _ _)
  have hn_ge : N ≤ n := by
    have hmul : N + 1 ≤ (N + 1) * step :=
      Nat.le_mul_of_pos_right _ hstep_pos
    have hN_mul : N ≤ (N + 1) * step :=
      (Nat.le_succ N).trans hmul
    dsimp [n]
    exact hN_mul.trans (Nat.le_add_left _ _)
  obtain ⟨z, _hz_pos, hz⟩ := h_int_pos n hn_pos
  refine ⟨n, hn_ge, z, hz, ?_⟩
  have hxy : (n : ℤ) ≡ (n₀ : ℤ) [ZMOD ((ℓ * B : ℕ) : ℤ)] := by
    refine Int.modEq_iff_dvd.mpr ?_
    refine ⟨-((N + 1 : ℕ) : ℤ), ?_⟩
    dsimp [n, step]
    ring
  have hz_int : (z : ℚ) = p.eval (((n : ℤ) : ℚ)) := by
    simpa using hz
  have hz₀_int : (z₀ : ℚ) = p.eval (((n₀ : ℤ) : ℚ)) := by
    simpa using hz₀
  have hper : z ≡ z₀ [ZMOD ((ℓ : ℕ) : ℤ)] :=
    polynomial_periodicity_of_integral_values p B hBpos hB ℓ hℓ.one_le
      (n : ℤ) (n₀ : ℤ) z z₀ hz_int hz₀_int hxy
  intro hz_dvd
  have hdiff : (ℓ : ℤ) ∣ z₀ - z := hper.dvd
  have hz₀_dvd : (ℓ : ℤ) ∣ z₀ := by
    have hsum : (ℓ : ℤ) ∣ (z₀ - z) + z := dvd_add hdiff hz_dvd
    simpa [sub_eq_add_neg, add_assoc] using hsum
  exact hz₀_ndvd hz₀_dvd

end Erdos.P283.RSG
