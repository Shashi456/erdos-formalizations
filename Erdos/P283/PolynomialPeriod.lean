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
  sorry

/-- **Lemma 5 (PDF §1).** If `B p(x) ∈ ℤ[x]` and `x ≡ y (mod m B)`, then
`p(x) ≡ p(y) (mod m)`. So `m B` is a period of the integer values of `p` modulo
`m`. -/
theorem polynomial_periodicity
    (p : ℚ[X]) (hp_int : IntValued p)
    (B : ℕ) (hBpos : 1 ≤ B) (hB : HasIntegralMultiple B p)
    (m : ℕ) (hm : 1 ≤ m) (x y : ℤ)
    (hxy : x ≡ y [ZMOD ((m * B : ℕ) : ℤ)]) :
    intEval p hp_int x ≡ intEval p hp_int y [ZMOD ((m : ℕ) : ℤ)] := by
  sorry

end PolynomialEgyptianSums
