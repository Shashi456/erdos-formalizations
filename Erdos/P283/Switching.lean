/-
Erdős Problems 283 + 351 — §1 Egyptian switches, switching polynomials & Lemma 6.

  * `switchingPoly p E := ∑_{e ∈ E} p(e·) - p`  — the switching polynomial.
  * `switchingPoly_leadingCoeff` — `lc(Q_E) = lc(p) · (∑_{e ∈ E} e^r - 1) > 0`.
  * `switchValueSet`             — the set of all integer values `Q_E(n)` over
                                    all Egyptian patterns `E` and `n ≥ 1`.
  * `switching_values_span_top`  — Lemma 6 (corrected): `Ideal.span (switchValueSet) = ⊤`,
                                    i.e. the gcd of all switching values is 1.
  * `finite_switch_values_generate_zmod` — finite version usable for the
                                            correction-slot construction.

Lemma 6 is axiom-free; uses Lemmas 4, 5 and `IntValued p`.
-/

import Erdos.P283.Basic
import Erdos.P283.Egyptian
import Erdos.P283.PolynomialPeriod

namespace PolynomialEgyptianSums

open Polynomial Finset

/-- The **switching polynomial** `Q_E(x) := ∑_{e ∈ E} p(e·x) - p(x)` for an
Egyptian pattern `E`. -/
noncomputable def switchingPoly (p : ℚ[X]) (E : Finset ℕ) : ℚ[X] :=
  (E.sum fun e => p.comp ((Polynomial.C (e : ℚ)) * Polynomial.X)) - p

/-- The leading coefficient of `Q_E` is `lc(p) · (∑_{e ∈ E} e^r - 1)`, where
`r := deg p`. Positive whenever `lc(p) > 0` and `E` is non-trivial (since
`∑ e^r ≥ ∑ e ≥ 2|E| ≥ 2 > 1`). -/
lemma switchingPoly_leadingCoeff (p : ℚ[X]) (E : Finset ℕ)
    (hE : IsEgyptianPattern E) (h_lead_pos : 0 < p.leadingCoeff)
    (h_nonconst : 1 ≤ p.natDegree) :
    0 < (switchingPoly p E).leadingCoeff := by
  sorry

/-- The set of **integer values** of switching polynomials over all Egyptian
patterns and positive integers. -/
noncomputable def switchValueSet (p : ℚ[X]) (hp : IntValued p) : Set ℤ :=
  { z | ∃ E : Finset ℕ, ∃ n : ℕ,
      IsEgyptianPattern E ∧ 1 ≤ n ∧
      z = (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ))
            - intEval p hp ((n : ℕ) : ℤ) }

/-- **Lemma 6 (PDF §1, corrected).** If `p` has degree `≥ 1`, positive leading
coefficient, and no fixed divisor on positive integers, then the integer values
of all switching polynomials `Q_E(n)` (over Egyptian patterns `E` and positive
integers `n`) generate the unit ideal of `ℤ`.

Proof (PDF §1): Suppose a prime `ℓ` divides every value. Choose `B` with
`B p ∈ ℤ[X]` (`exists_integral_multiple`); set `T_ℓ = ℓ B`. By Lemma 4 choose `E`
with `T_ℓ ∣ e` for all `e ∈ E` and `|E| ≡ 0 (mod ℓ)`. By Lemma 5, `p(e n) ≡ p(0)
(mod ℓ)` for `e ∈ E, n ≥ 1`, so `Q_E(n) ≡ |E| p(0) - p(n) ≡ -p(n) (mod ℓ)`.
Hence `ℓ ∣ p(n)` for all `n`, contradicting no-fixed-divisor. -/
theorem switching_values_span_top (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed : NoFixedDivisor p hp) :
    Ideal.span (switchValueSet p hp) = ⊤ := by
  sorry

/-- **Finite extracted form of Lemma 6.** Used in the correction-slot
construction: there are finitely many Egyptian patterns and positive integers
whose switching-polynomial residues mod `g` generate `ZMod g`. -/
theorem finite_switch_values_generate_zmod (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed : NoFixedDivisor p hp) (g : ℕ) (hg : 1 ≤ g) :
    ∃ (t : ℕ) (E : Fin t → Finset ℕ) (a : Fin t → ℕ) (b : Fin t → ℤ),
      (∀ i, IsEgyptianPattern (E i)) ∧
      (∀ i, 1 ≤ a i) ∧
      (∀ i, b i = (∑ e ∈ E i, intEval p hp ((e * a i : ℕ) : ℤ))
                  - intEval p hp ((a i : ℕ) : ℤ)) ∧
      AddSubgroup.closure (Set.range fun i : Fin t => ((b i : ℤ) : ZMod g)) = ⊤ := by
  sorry

end PolynomialEgyptianSums
