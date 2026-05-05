/-
Erdős Problems 283 + 351 — Foundational definitions.

Predicates and helpers used throughout the formalization:

  * `IsEgyptianPattern E` — `E ⊆ {2, 3, …}` with `∑_{e ∈ E} 1/e = 1`.
  * `IntValued p`         — `p : ℚ[X]` takes integer values on ℤ.
  * `intEval p hp z`      — extract the integer value (via `Classical.choose`).
  * `NoFixedDivisor p hp` — no `d ≥ 2` divides every `p(n)` for `n ≥ 1`.
  * `HasIntegralMultiple B p` — `B p(x) ∈ ℤ[x]` (denominator-cleared form).
  * `FS s`                — finite subset sums of a sequence (used by RSG).
  * `roth_szekeres_graham` — the trust-boundary axiom (with integer-divisibility
                              gcd hypothesis, fixed from earlier scaffold).

This file is imported by every other P283 file.
-/

import Mathlib

namespace PolynomialEgyptianSums

open Polynomial Filter

/-! ## Egyptian patterns -/

/-- `E ⊆ {2, 3, …}` is an **Egyptian pattern** if `∑_{e ∈ E} 1/e = 1`. Used
throughout the proof for the switch identity and the residue-correction trick. -/
def IsEgyptianPattern (E : Finset ℕ) : Prop :=
  (∀ e ∈ E, 2 ≤ e) ∧ (∑ e ∈ E, (1 : ℚ) / (e : ℚ)) = 1

/-! ## Integer-valued polynomials -/

/-- `p : ℚ[X]` takes integer values on every `z ∈ ℤ`. -/
def IntValued (p : ℚ[X]) : Prop :=
  ∀ z : ℤ, ∃ k : ℤ, (k : ℚ) = p.eval (z : ℚ)

/-- The integer value of an integer-valued polynomial at `z ∈ ℤ`. -/
noncomputable def intEval (p : ℚ[X]) (hp : IntValued p) (z : ℤ) : ℤ :=
  (hp z).choose

/-- The defining specification of `intEval`. -/
lemma intEval_spec (p : ℚ[X]) (hp : IntValued p) (z : ℤ) :
    ((intEval p hp z : ℤ) : ℚ) = p.eval (z : ℚ) :=
  (hp z).choose_spec

/-! ## Fixed-divisor predicate -/

/-- The polynomial `p` has **no fixed divisor** on the positive integers if no
`d ≥ 2` divides every `p(n)` for `n ≥ 1`. -/
def NoFixedDivisor (p : ℚ[X]) (hp : IntValued p) : Prop :=
  ∀ d : ℕ, 2 ≤ d → ¬ (∀ n : ℕ, 1 ≤ n → (d : ℤ) ∣ intEval p hp (n : ℤ))

/-! ## Integral multiples (denominator clearing) -/

/-- `B p(x) ∈ ℤ[x]`: there is an integer-coefficient polynomial whose ℚ-cast equals
`B p`. (Used in Lemma 5 to upgrade integer-valuedness to actual integer
coefficients after scaling.) -/
def HasIntegralMultiple (B : ℕ) (p : ℚ[X]) : Prop :=
  ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) = Polynomial.C (B : ℚ) * p

/-- Every rational polynomial has an integral multiple. (Routine denominator
clearing: take `B` = lcm of the denominators of the coefficients.) -/
theorem exists_integral_multiple (p : ℚ[X]) :
    ∃ B : ℕ, 1 ≤ B ∧ HasIntegralMultiple B p := by
  sorry

/-! ## Roth–Szekeres–Graham (axiom) -/

/-- The set of finite subset sums of a sequence `s : ℕ → ℤ`. -/
def FS (s : ℕ → ℤ) : Set ℤ := { x | ∃ I : Finset ℕ, x = ∑ i ∈ I, s i }

/-- **Roth–Szekeres–Graham theorem.** For a non-constant polynomial `f ∈ ℚ[x]`
with positive leading coefficient that takes positive integer values on
`ℕ_{>0}`, with `gcd{f(n) : n ≥ 1} = 1` (encoded as: no prime `ℓ` divides every
integer value), all sufficiently large integers `X` admit an expression
`X = ∑_{i ∈ I} f(i + 1)` for some finite `I ⊆ ℕ`.

Classical (Graham 1964 / Roth-Szekeres 1954); Mathlib has surrounding analytic
NT infrastructure but not this named result. We postulate it as the single
trust-boundary axiom for the polynomial-Egyptian-sums proof. -/
axiom roth_szekeres_graham (f : ℚ[X])
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
        (X : ℚ) = ∑ i ∈ I, f.eval ((i + 1 : ℕ) : ℚ)

end PolynomialEgyptianSums
