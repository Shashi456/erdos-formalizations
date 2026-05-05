/-
Erdős Problems 283 + 351 — §2 main-slot construction.

The explicit family of denominators that powers Theorem 1:

  P := 36
  u j := P j + 1
  D j := u j · u (j+1)
  τ N := P · u (N+1)
  E0 := {2, 3, 6}
  A p := switchingPoly p E0  (= p(2x) + p(3x) + p(6x) - p(x))

Telescoping identity:

  ∑_{j=J}^N 1/D j = 1/(P u_J) - 1/τ_N

The fixed divisor `g := gcd { A(D j) : j ≥ J }` is then extracted as the
nonnegative generator of an `Ideal.span` over ℤ, and we form

  Dpoly p J x  := (P (J + x - 1) + 1)(P (J + x) + 1)
  q p J        := (A p) ∘ Dpoly p J / g

with the goal of applying `roth_szekeres_graham` to `q`.

This file declares the construction objects and proves the supporting
lemmas; the `theorem_1` assembly lives in `Theorem1.lean`.
-/

import Erdos.P283.Basic
import Erdos.P283.Switching

namespace PolynomialEgyptianSums

open Polynomial Finset

/-- The constant `P = 36 = 2² · 3²`, chosen so that `u j = P j + 1` is coprime to
`6`, giving the v₂/v₃ valuation profiles needed for collision avoidance. -/
def P : ℕ := 36

/-- `u j := P j + 1`. -/
def u (j : ℕ) : ℕ := P * j + 1

/-- `D j := u j · u (j+1)`, the main-slot denominators. Telescopes via
`1/D j = (1/P) · (1/u_j - 1/u_{j+1})`. -/
def D (j : ℕ) : ℕ := u j * u (j + 1)

/-- `τ N := P · u (N+1)`. The "endpoint" denominator that closes the telescoping
sum and provides a (v₂, v₃) = (2, 2) signature distinct from main slots. -/
def tau (N : ℕ) : ℕ := P * u (N + 1)

/-- The base Egyptian pattern `{2, 3, 6}` underlying the `1/x = 1/(2x) + 1/(3x)
+ 1/(6x)` switch identity. -/
def E0 : Finset ℕ := {2, 3, 6}

/-- The switching polynomial of the base pattern: `A p (x) = p(2x) + p(3x) +
p(6x) - p(x)`. -/
noncomputable def A (p : ℚ[X]) : ℚ[X] := switchingPoly p E0

/-! ## Reciprocal identity (the heart of telescoping) -/

/-- `1/D j = (1/P) · (1/u j - 1/u (j+1))`. -/
lemma D_recip (j : ℕ) :
    (1 : ℚ) / (D j : ℚ) =
      (1 / (P : ℚ)) * ((1 / (u j : ℚ)) - (1 / (u (j + 1) : ℚ))) := by
  unfold D u P
  push_cast
  have hu1 : (36 * (j : ℚ) + 1) ≠ 0 := ne_of_gt (by positivity)
  have hu2 : (36 * ((j : ℚ) + 1) + 1) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The telescoping sum `∑_{j=J}^N 1/D j = 1/(P u_J) - 1/τ_N`. -/
lemma main_telescoping (J N : ℕ) (hJN : J ≤ N) :
    (∑ j ∈ Finset.Icc J N, (1 : ℚ) / (D j : ℚ)) =
      1 / ((P : ℚ) * (u J : ℚ)) - 1 / (tau N : ℚ) := by
  have hP_ne : (P : ℚ) ≠ 0 := by unfold P; norm_num
  have hu_pos : ∀ k : ℕ, (0 : ℚ) < (u k : ℚ) := by
    intro k; unfold u; push_cast; positivity
  have hu_ne : ∀ k : ℕ, (u k : ℚ) ≠ 0 := fun k => ne_of_gt (hu_pos k)
  let f : ℕ → ℚ := fun i => -1 / ((P : ℚ) * (u i : ℚ))
  have hD_eq : ∀ j, (1 : ℚ) / (D j : ℚ) = f (j + 1) - f j := by
    intro j
    rw [D_recip]
    show (1 / (P : ℚ)) * (1 / (u j : ℚ) - 1 / (u (j + 1) : ℚ)) =
        -1 / ((P : ℚ) * (u (j + 1) : ℚ)) - -1 / ((P : ℚ) * (u j : ℚ))
    field_simp
    ring
  calc (∑ j ∈ Finset.Icc J N, (1 : ℚ) / (D j : ℚ))
      = ∑ j ∈ Finset.Icc J N, (f (j + 1) - f j) :=
        Finset.sum_congr rfl (fun j _ => hD_eq j)
    _ = ∑ j ∈ Finset.Ico J (N + 1), (f (j + 1) - f j) := by
        rw [show (Finset.Icc J N) = Finset.Ico J (N + 1) from
              (Finset.Ico_add_one_right_eq_Icc J N).symm]
    _ = f (N + 1) - f J := Finset.sum_Ico_sub f (by omega : J ≤ N + 1)
    _ = 1 / ((P : ℚ) * (u J : ℚ)) - 1 / (tau N : ℚ) := by
        show -1 / ((P : ℚ) * (u (N + 1) : ℚ)) - -1 / ((P : ℚ) * (u J : ℚ)) =
            1 / ((P : ℚ) * (u J : ℚ)) - 1 / (tau N : ℚ)
        unfold tau
        push_cast
        field_simp
        ring

/-! ## E0 is an Egyptian pattern -/

/-- `E0 = {2, 3, 6}` is an Egyptian pattern (`1/2 + 1/3 + 1/6 = 1`). -/
lemma isEgyptianPattern_E0 : IsEgyptianPattern E0 := by
  refine ⟨?_, ?_⟩
  · intro e he
    fin_cases he <;> norm_num
  · show ∑ e ∈ E0, (1 : ℚ) / (e : ℚ) = 1
    rw [show (E0 : Finset ℕ) = insert 2 (insert 3 ({6} : Finset ℕ)) from rfl]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    norm_num

/-! ## Leading coefficient of A and the constant Θ

The asymptotic comparison in Theorem 1 needs the *exact* leading coefficient of
`A p`, not just positivity. Specifically, `lc(A p) = lc(p) · (Θ_r) > 0` where
`Θ_r := 2^r + 3^r + 6^r − 1`. -/

/-- `Θ r := 2^r + 3^r + 6^r - 1`. Used in the main-theorem asymptotics:
`λ = a P^{2r}` and `a Θ_r P^{2r}` bracket the rescaled-polynomial leading term. -/
def theta (r : ℕ) : ℚ := (2 : ℚ)^r + (3 : ℚ)^r + (6 : ℚ)^r - 1

/-- `1 < Θ r` for `r ≥ 1`. (At `r = 1`: `Θ = 2 + 3 + 6 - 1 = 10`.) -/
lemma theta_gt_one (r : ℕ) (hr : 1 ≤ r) : 1 < theta r := by
  unfold theta
  have h2 : (2 : ℚ) ≤ (2 : ℚ) ^ r := by
    calc (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
    _ ≤ (2 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have h3 : (3 : ℚ) ≤ (3 : ℚ) ^ r := by
    calc (3 : ℚ) = (3 : ℚ) ^ 1 := by norm_num
    _ ≤ (3 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have h6 : (6 : ℚ) ≤ (6 : ℚ) ^ r := by
    calc (6 : ℚ) = (6 : ℚ) ^ 1 := by norm_num
    _ ≤ (6 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  linarith

/-- `theta r = ∑ e ∈ E0, e^r - 1`. -/
lemma theta_eq_sum (r : ℕ) :
    theta r = (∑ e ∈ E0, ((e : ℚ) ^ r)) - 1 := by
  unfold theta E0
  rw [show ({2, 3, 6} : Finset ℕ) = insert 2 (insert 3 ({6} : Finset ℕ)) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  push_cast; ring

/-- The natDegree of `A p` equals `natDegree p` whenever `lc(p) > 0` and
`1 ≤ natDegree p`. -/
lemma A_natDegree_eq (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (A p).natDegree = p.natDegree := by
  unfold A
  exact switchingPoly_natDegree_eq p E0 isEgyptianPattern_E0 h_lead_pos h_nonconst

/-- Exact leading-coefficient formula:
`lc(A p) = lc(p) · Θ_r` where `r = natDegree p`. -/
lemma A_leadingCoeff_eq (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (A p).leadingCoeff = p.leadingCoeff * theta p.natDegree := by
  unfold A
  rw [switchingPoly_leadingCoeff_eq p E0 isEgyptianPattern_E0 h_lead_pos h_nonconst,
      theta_eq_sum]

/-- The leading coefficient of `A p = switchingPoly p {2, 3, 6}` is
`lc(p) · (2^r + 3^r + 6^r - 1) > 0` when `lc(p) > 0` and `r := deg p ≥ 1`. -/
lemma A_leadingCoeff (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < (A p).leadingCoeff := by
  unfold A
  exact switchingPoly_leadingCoeff p E0 isEgyptianPattern_E0 h_lead_pos h_nonconst

/-- `A p` is integer-valued whenever `p` is. -/
lemma A_intValued (p : ℚ[X]) (hp : IntValued p) : IntValued (A p) :=
  switchingPoly_intValued p hp E0

/-! ## The set of main-slot increments -/

/-- The set of integer values `A(D j)` for `j ≥ J`. Used to define `g`. -/
noncomputable def mainValueSet (p : ℚ[X]) (hp : IntValued p) (hA : IntValued (A p))
    (J : ℕ) : Set ℤ :=
  { z | ∃ j : ℕ, J ≤ j ∧ z = intEval (A p) hA ((D j : ℕ) : ℤ) }

/-! ## The polynomial `Dpoly` and rescaled `q` -/

/-- `Dpoly p J x := (P(J + x - 1) + 1)(P(J + x) + 1)`, a polynomial of degree 2
with leading coefficient `P²`. Substituting `t ≥ 1` gives `D (J + t - 1)`.

Defined with explicit ℚ-subtraction inside `ℚ[X]` (not Nat subtraction) so the
formula matches the paper for every `J`, including `J = 0`. -/
noncomputable def Dpoly (J : ℕ) : ℚ[X] :=
  (Polynomial.C (P : ℚ) *
      (Polynomial.C (J : ℚ) + Polynomial.X - Polynomial.C (1 : ℚ)) + 1) *
  (Polynomial.C (P : ℚ) *
      (Polynomial.C (J : ℚ) + Polynomial.X) + 1)

/-- `Dpoly J` applied at `t : ℕ` (with `1 ≤ t`) gives `D (J + t - 1)`. -/
lemma Dpoly_eval_at_succ (J t : ℕ) (ht : 1 ≤ t) :
    (Dpoly J).eval (t : ℚ) = (D (J + t - 1) : ℚ) := by
  have h_pos : 1 ≤ J + t := by omega
  have h_succ : J + t - 1 + 1 = J + t := by omega
  have h_cast : ((J + t - 1 : ℕ) : ℚ) = (J : ℚ) + (t : ℚ) - 1 := by
    rw [Nat.cast_sub h_pos]; push_cast; ring
  unfold Dpoly D u
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
             Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  rw [h_succ]
  push_cast
  rw [h_cast]

/- The rescaled polynomial `q := A ∘ Dpoly / g`, where `g` is the (positive)
generator of the ideal spanned by the main-value set. Definition deferred —
depends on the choice of `g` from `Ideal.span (mainValueSet …)`; constructed
inside `Theorem1.lean`. -/

end PolynomialEgyptianSums
