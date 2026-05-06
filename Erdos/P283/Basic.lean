/-
Erdős Problems 283 + 351 — Foundational definitions.

Predicates and helpers used throughout the formalization:

  * `IsEgyptianPattern E` — `E ⊆ {2, 3, …}` with `∑_{e ∈ E} 1/e = 1`.
  * `IntValued p`         — `p : ℚ[X]` takes integer values on ℤ.
  * `intEval p hp z`      — extract the integer value (via `Classical.choose`).
  * `NoFixedDivisor p hp` — no `d ≥ 2` divides every `p(n)` for `n ≥ 1`.
  * `HasIntegralMultiple B p` — `B p(x) ∈ ℤ[x]` (denominator-cleared form).
  * `FS s`                — finite subset sums of a sequence (used by RSG).
  * `roth_szekeres_graham` — Graham's complete-polynomial-values theorem,
                              supplied by `Erdos.P283.RSG`.

This file is imported by every other P283 file.
-/

import Mathlib
import Erdos.P283.RSG.PolynomialValues

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

/-! ### Closure of `IntValued` -/

lemma IntValued.add {p q : ℚ[X]} (hp : IntValued p) (hq : IntValued q) :
    IntValued (p + q) := by
  intro z
  obtain ⟨a, ha⟩ := hp z
  obtain ⟨b, hb⟩ := hq z
  refine ⟨a + b, ?_⟩
  rw [Polynomial.eval_add, ← ha, ← hb]
  push_cast; ring

lemma IntValued.sub {p q : ℚ[X]} (hp : IntValued p) (hq : IntValued q) :
    IntValued (p - q) := by
  intro z
  obtain ⟨a, ha⟩ := hp z
  obtain ⟨b, hb⟩ := hq z
  refine ⟨a - b, ?_⟩
  rw [Polynomial.eval_sub, ← ha, ← hb]
  push_cast; ring

lemma IntValued.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X])
    (hf : ∀ i ∈ s, IntValued (f i)) :
    IntValued (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z
    refine ⟨0, ?_⟩
    simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine IntValued.add (hf a (Finset.mem_insert_self a s)) ?_
    apply ih
    intro i hi
    exact hf i (Finset.mem_insert_of_mem hi)

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
clearing: take `B` = product of the denominators of the coefficients.) -/
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

/-! ## Roth–Szekeres–Graham -/

/-- The set of finite subset sums of a sequence `s : ℕ → ℤ`. -/
def FS (s : ℕ → ℤ) : Set ℤ := { x | ∃ I : Finset ℕ, x = ∑ i ∈ I, s i }

/-- **Roth–Szekeres–Graham theorem.** For a non-constant polynomial `f ∈ ℚ[x]`
with positive leading coefficient that takes positive integer values on
`ℕ_{>0}`, with `gcd{f(n) : n ≥ 1} = 1` (encoded as: no prime `ℓ` divides every
integer value), all sufficiently large integers `X` admit an expression
`X = ∑_{i ∈ I} f(i + 1)` for some finite `I ⊆ ℕ`.

Classical (Graham 1964 / Roth-Szekeres 1954). This theorem is proved in the
new `Erdos.P283.RSG` scaffold and re-exported here in the exact shape used by the
polynomial-Egyptian-sums proof. -/
theorem roth_szekeres_graham (f : ℚ[X])
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
        (X : ℚ) = ∑ i ∈ I, f.eval ((i + 1 : ℕ) : ℚ) :=
  Erdos.P283.RSG.graham_complete_polynomial_values
    f h_nonconst h_lead_pos h_int_pos h_gcd_one

end PolynomialEgyptianSums
