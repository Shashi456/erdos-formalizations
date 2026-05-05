/-
Erdős Problems 283 + 351 — §1 Egyptian switches, Lemma 5 (polynomial periodicity).

  * `int_poly_eval_congr` — `x ≡ y (mod M) → P.eval x ≡ P.eval y (mod M)` for
                            `P : ℤ[X]`.
  * `polynomial_periodicity` — Lemma 5 for ℚ-polynomials with integral multiple.

The proof goes via denominator clearing: pick `B` with `B p ∈ ℤ[X]`, get the
ℤ-version periodicity, and divide back by `B` using integer-valuedness.

All axiom-free.
-/

import Erdos.P283.Basic

namespace PolynomialEgyptianSums

open Polynomial

/-- For an integer-coefficient polynomial `P : ℤ[X]` and integers `x ≡ y (mod M)`,
`P.eval x ≡ P.eval y (mod M)`. Standard polynomial congruence. -/
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

/-- **Lemma 5 (PDF §1).** If `B p(x) ∈ ℤ[x]` and `x ≡ y (mod m B)`, then
`p(x) ≡ p(y) (mod m)`. So `m B` is a period of the integer values of `p` modulo
`m`. -/
theorem polynomial_periodicity
    (p : ℚ[X]) (hp_int : IntValued p)
    (B : ℕ) (hBpos : 1 ≤ B) (hB : HasIntegralMultiple B p)
    (m : ℕ) (hm : 1 ≤ m) (x y : ℤ)
    (hxy : x ≡ y [ZMOD ((m * B : ℕ) : ℤ)]) :
    intEval p hp_int x ≡ intEval p hp_int y [ZMOD ((m : ℕ) : ℤ)] := by
  obtain ⟨R, hR⟩ := hB
  -- R.eval x ≡ R.eval y (mod m * B).
  have h_R_congr : R.eval x ≡ R.eval y [ZMOD ((m * B : ℕ) : ℤ)] :=
    int_poly_eval_congr R hxy
  -- (R.eval z : ℚ) = B * p.eval z for all z.
  have h_R_eval : ∀ z : ℤ, ((R.eval z : ℤ) : ℚ) = (B : ℚ) * p.eval (z : ℚ) := by
    intro z
    have h1 : ((R.map (Int.castRingHom ℚ)).eval ((z : ℤ) : ℚ)) =
        (Polynomial.C (B : ℚ) * p).eval ((z : ℚ)) := by
      rw [hR]
    rw [Polynomial.eval_map, Polynomial.eval_mul, Polynomial.eval_C] at h1
    -- h1 : eval₂ (Int.castRingHom ℚ) (↑z) R = ↑B * eval ↑z p
    -- Polynomial.eval₂_at_apply : eval₂ f (f r) p = f (eval r p), so with f = Int.castRingHom ℚ,
    -- eval₂ (Int.castRingHom ℚ) ((z : ℤ) : ℚ) R = ((R.eval z : ℤ) : ℚ).
    have h2 : Polynomial.eval₂ (Int.castRingHom ℚ) ((z : ℤ) : ℚ) R = ((R.eval z : ℤ) : ℚ) :=
      Polynomial.eval₂_at_apply (Int.castRingHom ℚ) z
    rw [h2] at h1
    exact h1
  -- Hence R.eval z = B * intEval p hp_int z (in ℤ) via Int.cast injectivity into ℚ.
  have h_R_int_eval : ∀ z : ℤ, R.eval z = (B : ℤ) * intEval p hp_int z := by
    intro z
    have h1 := h_R_eval z
    have h2 := intEval_spec p hp_int z
    have : ((R.eval z : ℤ) : ℚ) = (((B : ℤ) * intEval p hp_int z : ℤ) : ℚ) := by
      push_cast
      rw [h1, ← h2]
    exact_mod_cast this
  rw [h_R_int_eval x, h_R_int_eval y] at h_R_congr
  -- h_R_congr : (B : ℤ) * intEval p hp_int x ≡ (B : ℤ) * intEval p hp_int y [ZMOD (m * B : ℤ)]
  -- Goal: intEval p hp_int x ≡ intEval p hp_int y [ZMOD m]
  -- Use: m * B ∣ B * (a - b) ↔ m ∣ (a - b), with B > 0.
  have hBpos_int : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hBpos
  have hBne : (B : ℤ) ≠ 0 := ne_of_gt hBpos_int
  -- Convert h_R_congr to divisibility form.
  have h_dvd : ((m * B : ℕ) : ℤ) ∣
      ((B : ℤ) * intEval p hp_int y - (B : ℤ) * intEval p hp_int x) :=
    Int.modEq_iff_dvd.mp h_R_congr
  -- Rewrite as ((m * B : ℕ) : ℤ) ∣ (B : ℤ) * (intEval p hp_int y - intEval p hp_int x).
  have h_dvd' : ((m * B : ℕ) : ℤ) ∣
      (B : ℤ) * (intEval p hp_int y - intEval p hp_int x) := by
    have heq : (B : ℤ) * intEval p hp_int y - (B : ℤ) * intEval p hp_int x =
        (B : ℤ) * (intEval p hp_int y - intEval p hp_int x) := by ring
    rwa [heq] at h_dvd
  -- ((m * B : ℕ) : ℤ) = (B : ℤ) * (m : ℤ).
  have hmB : ((m * B : ℕ) : ℤ) = (B : ℤ) * (m : ℤ) := by push_cast; ring
  rw [hmB] at h_dvd'
  -- (B : ℤ) * (m : ℤ) ∣ (B : ℤ) * (a - b) ↔ (m : ℤ) ∣ (a - b) (using B ≠ 0).
  have h_m_dvd : (m : ℤ) ∣ (intEval p hp_int y - intEval p hp_int x) :=
    (mul_dvd_mul_iff_left hBne).mp h_dvd'
  exact Int.modEq_iff_dvd.mpr h_m_dvd

end PolynomialEgyptianSums
