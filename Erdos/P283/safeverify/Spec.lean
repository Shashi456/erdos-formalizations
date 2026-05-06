/-
SafeVerify target for Erdős Problems 283 + 351.

Enumerates the public theorems and the supporting definitions that the P283
development provides. The bodies in this file are `sorry` *by design* —
SafeVerify only inspects signatures here; the actual proofs live in the
split modules under `Erdos.P283.*` (and `Erdos.P283.RSG.*`), where they are
sorry-free. SafeVerify replays both files and checks the submission's
matching declarations only depend on the allow-list:

  Mathlib core (`propext`, `Classical.choice`, `Quot.sound`)

The former `PolynomialEgyptianSums.roth_szekeres_graham` trust boundary is now
proved in `Erdos.P283.RSG.graham_complete_polynomial_values`, so no
problem-specific axiom needs to be added to the SafeVerify allow-list. The
RSG theorem is included in the spec below so SafeVerify also checks its
axiom dependencies. Reproduction recipe in `../README.md` §
"Verifying with SafeVerify".

Lemmas 3-6 (egyptian_expansion, egyptian_pattern_with_period,
polynomial_periodicity, switching_values_span_top), Theorem 1, Corollary 7,
the FC wrappers, and `Erdos.P283.RSG.graham_complete_polynomial_values` all
have only Mathlib core axioms.
-/

import Mathlib

/-! ## §0 Roth-Szekeres-Graham (Graham 1964) -/

namespace Erdos.P283.RSG

open Polynomial

/-- **Graham's complete polynomial values theorem (1964).** Formerly the
trust-boundary axiom `PolynomialEgyptianSums.roth_szekeres_graham`; now
proved in `Erdos/P283/RSG/PolynomialValues.lean`. Stated for a rational
polynomial taking positive integer values on `ℕ_{≥1}`, with no fixed prime
divisor. -/
theorem graham_complete_polynomial_values
    (f : ℚ[X])
    (h_nonconst : 0 < f.natDegree)
    (h_lead_pos : 0 < f.leadingCoeff)
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = f.eval (n : ℚ))
    (h_gcd_one :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ n : ℕ, 1 ≤ n ∧ ∃ z : ℤ,
          (z : ℚ) = f.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z)) :
    ∃ X_f : ℤ, ∀ X : ℤ, X_f ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, f.eval ((i + 1 : ℕ) : ℚ) := sorry

end Erdos.P283.RSG

namespace PolynomialEgyptianSums

open Polynomial Filter

/-- Egyptian pattern: `E ⊆ {2, 3, …}` with `∑_{e ∈ E} 1/e = 1`. -/
def IsEgyptianPattern (E : Finset ℕ) : Prop := sorry

/-- A rational polynomial takes integer values on every integer. -/
def IntValued (p : ℚ[X]) : Prop := sorry

/-- The integer value of an integer-valued polynomial. -/
noncomputable def intEval (p : ℚ[X]) (hp : IntValued p) (z : ℤ) : ℤ := sorry

/-- `intEval` returns the integer cast of the polynomial's rational value. -/
lemma intEval_spec (p : ℚ[X]) (hp : IntValued p) (z : ℤ) :
    ((intEval p hp z : ℤ) : ℚ) = p.eval (z : ℚ) := sorry

/-- No fixed divisor on positive integers: no `d ≥ 2` divides every `p(n)` for `n ≥ 1`. -/
def NoFixedDivisor (p : ℚ[X]) (hp : IntValued p) : Prop := sorry

/-- `B p(x) ∈ ℤ[x]`: there is an integer-coefficient polynomial whose ℚ-cast equals
`B p`. Used in Lemma 5 (polynomial periodicity). -/
def HasIntegralMultiple (B : ℕ) (p : ℚ[X]) : Prop := sorry

/-- The image set `A_p = { p(n) + 1/n : n ∈ ℕ }`. -/
def imageSet (p : ℚ[X]) : Set ℚ := sorry

/-- Strong completeness of a subset of ℚ: every sufficiently large natural number
is a finite subset-sum from `A \ B` for any finite `B`. -/
def IsStronglyComplete (A : Set ℚ) : Prop := sorry

/-! ## §1 Egyptian switches (axiom-free) -/

theorem egyptian_expansion (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ E : Finset ℕ,
      E.card = k ∧ (∀ e ∈ E, L < e) ∧ R = ∑ e ∈ E, (1 : ℚ) / e := sorry

theorem egyptian_pattern_with_period (T M : ℕ) (hT : 1 ≤ T) (hM : 1 ≤ M)
    (ρ : ZMod M) :
    ∃ E : Finset ℕ, IsEgyptianPattern E ∧ (∀ e ∈ E, T ∣ e) ∧
      (E.card : ZMod M) = ρ := sorry

theorem polynomial_periodicity (p : ℚ[X]) (hp_int : IntValued p)
    (B : ℕ) (hBpos : 1 ≤ B) (hB : HasIntegralMultiple B p)
    (m : ℕ) (hm : 1 ≤ m) (x y : ℤ)
    (hxy : x ≡ y [ZMOD ((m * B : ℕ) : ℤ)]) :
    intEval p hp_int x ≡ intEval p hp_int y [ZMOD ((m : ℕ) : ℤ)] := sorry

/-! ## §2 Main theorem -/

/-- **Theorem 1 (PDF Theorem 1).** For `α ∈ ℚ_{>0}`, `L ≥ 1`, and `p ∈ ℚ[x]`
integer-valued with positive leading coefficient and no fixed divisor on
positive integers, all sufficiently large integers `m` admit an expression as
`∑ p(n_i)` with distinct `L < n_1 < ⋯ < n_k` and `∑ 1/n_i = α`. -/
theorem theorem_1 (α : ℚ) (hα : 0 < α) (L : ℕ) (hL : 1 ≤ L) (p : ℚ[X])
    (hp : IntValued p) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : NoFixedDivisor p hp) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
        StrictMono n ∧ (L < n 0) ∧
        (α = ∑ i, (1 : ℚ) / (n i)) ∧
        ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := sorry

/-! ## §3 Corollary 7 -/

/-- The `p = 0` case is axiom-free (uses only Lemma 3). -/
theorem corollary_7_zero : IsStronglyComplete (imageSet (0 : ℚ[X])) := sorry

/-- The negative-leading case is axiom-free. -/
theorem not_strongly_complete_of_neg_leadingCoeff
    (p : ℚ[X]) (hp : p.leadingCoeff < 0) :
    ¬ IsStronglyComplete (imageSet p) := sorry

/-- The positive-leading case. -/
theorem corollary_7_pos_leading (p : ℚ[X]) (h_lead_pos : 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := sorry

/-- Combined Corollary 7: `p = 0` or positive leading coefficient ⇒ strong completeness. -/
theorem corollary_7 (p : ℚ[X]) (h : p = 0 ∨ 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := sorry

end PolynomialEgyptianSums

/-! ## §4 formal-conjectures upstream wrappers -/

namespace Erdos283

open Filter Polynomial Finset

/-- The condition appearing in FC's `erdos_283` for an integer polynomial. -/
def Condition (p : ℤ[X]) : Prop := sorry

/-- **`formal-conjectures` upstream form for #283** under `answer := True`. -/
theorem erdos_283 :
    True ↔ ∀ p : ℤ[X], Condition p := sorry

end Erdos283

namespace Erdos351

open Polynomial

/-- FC-named alias for `imageSet`. -/
def imageSet (P : ℚ[X]) : Set ℚ := sorry

/-- FC-named alias for `IsStronglyComplete (imageSet P)`. -/
def HasCompleteImage (P : ℚ[X]) : Prop := sorry

/-- **`formal-conjectures` upstream form for #351** under `answer := True`. -/
theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      HasCompleteImage P := sorry

end Erdos351
