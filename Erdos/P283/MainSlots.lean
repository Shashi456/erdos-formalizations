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

/-- `u j = 36j + 1` is strictly increasing. -/
lemma u_strictMono : StrictMono u := by
  intro a b h
  unfold u P
  omega

/-- Main denominators are positive. -/
lemma D_pos (j : ℕ) : 0 < D j := by
  unfold D u P
  positivity

/-- Endpoint denominators are positive. -/
lemma tau_pos (N : ℕ) : 0 < tau N := by
  unfold tau u P
  positivity

/-- `D j = u_j u_{j+1}` is strictly increasing. -/
lemma D_strictMono : StrictMono D := by
  intro a b h
  unfold D u P
  nlinarith [h]

/-- `D` is injective. -/
lemma D_injective : Function.Injective D :=
  D_strictMono.injective

/-- `τ N = 36 u_{N+1}` is strictly increasing. -/
lemma tau_strictMono : StrictMono tau := by
  intro a b h
  unfold tau u P
  omega

/-- `τ` is injective. -/
lemma tau_injective : Function.Injective tau :=
  tau_strictMono.injective

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

/-! ## Asymptotic constants for Theorem 1

`λ`, `μ`, `aΘP^{2r}` bracket the rescaled-polynomial leading term. Theorem 1's
attainable-interval / overlap argument needs `λ < μ < a Θ_r P^{2r}`; the
midpoint choice `μ := a P^{2r} (1 + Θ_r) / 2` works in ℚ. -/

/-- `λ p := lc(p) · P^{2r}` where `r = natDegree p`. The interval-step
constant: `B_{N+1} − B_N = λ N^{2r} + O(N^{2r-1})`. -/
def lambdaConst (p : ℚ[X]) : ℚ :=
  p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree))

/-- `μ p := lc(p) · P^{2r} · (1 + Θ_r) / 2`. The strict mid-constant
between `λ p` and `lc(p) · Θ_r · P^{2r}`. Used as the upper-edge slope of
attainable intervals so consecutive intervals overlap. -/
def muConst (p : ℚ[X]) : ℚ :=
  p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) *
    ((1 + theta p.natDegree) / 2)

/-- `λ p < μ p` whenever `lc(p) > 0` and `1 ≤ natDegree p`. -/
lemma lambdaConst_lt_muConst (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    lambdaConst p < muConst p := by
  unfold lambdaConst muConst
  have hθ : 1 < theta p.natDegree := theta_gt_one _ h_nonconst
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  have hap : 0 < p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) :=
    mul_pos h_lead_pos hP
  have h_factor : 1 < (1 + theta p.natDegree) / 2 := by linarith
  -- aP^{2r} < aP^{2r} * ((1+Θ)/2)
  calc p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree))
      = p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) * 1 := by ring
    _ < p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) *
          ((1 + theta p.natDegree) / 2) :=
        mul_lt_mul_of_pos_left h_factor hap

/-- `μ p < lc(p) · Θ_r · P^{2r}` whenever `lc(p) > 0` and `1 ≤ natDegree p`. -/
lemma muConst_lt_a_theta_P (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    muConst p < p.leadingCoeff * theta p.natDegree *
      ((P : ℚ) ^ (2 * p.natDegree)) := by
  unfold muConst
  have hθ : 1 < theta p.natDegree := theta_gt_one _ h_nonconst
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  have hap : 0 < p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) :=
    mul_pos h_lead_pos hP
  -- (1+Θ)/2 < Θ ↔ 1+Θ < 2Θ ↔ 1 < Θ
  have h_factor : (1 + theta p.natDegree) / 2 < theta p.natDegree := by linarith
  calc p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) *
        ((1 + theta p.natDegree) / 2)
      < p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) * theta p.natDegree :=
        mul_lt_mul_of_pos_left h_factor hap
    _ = p.leadingCoeff * theta p.natDegree *
          ((P : ℚ) ^ (2 * p.natDegree)) := by ring

/-- `0 < λ p` whenever `lc(p) > 0`. -/
lemma lambdaConst_pos (p : ℚ[X]) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < lambdaConst p := by
  unfold lambdaConst
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  exact mul_pos h_lead_pos hP

/-- `0 < μ p` whenever `lc(p) > 0` and `1 ≤ natDegree p`. -/
lemma muConst_pos (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < muConst p :=
  lt_trans (lambdaConst_pos p h_lead_pos)
    (lambdaConst_lt_muConst p h_nonconst h_lead_pos)

/-! ## The set of main-slot increments -/

/-- The set of integer values `A(D j)` for `j ≥ J`. Used to define `g`. The
`IntValued (A p)` witness is derived automatically via `A_intValued` so
callers only need `hp : IntValued p`. -/
noncomputable def mainValueSet (p : ℚ[X]) (hp : IntValued p) (J : ℕ) : Set ℤ :=
  { z | ∃ j : ℕ, J ≤ j ∧ z = intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) }

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

/-! ### `Dpoly` natDegree and leadingCoeff -/

/-- `Dpoly J` factors as `(C P · X + C ((P : ℚ)·(J-1) + 1)) · (C P · X + C ((P : ℚ)·J + 1))`. -/
lemma Dpoly_eq_linear_mul (J : ℕ) :
    Dpoly J =
      (Polynomial.C (P : ℚ) * Polynomial.X + Polynomial.C ((P : ℚ) * ((J : ℚ) - 1) + 1)) *
      (Polynomial.C (P : ℚ) * Polynomial.X + Polynomial.C ((P : ℚ) * (J : ℚ) + 1)) := by
  unfold Dpoly
  simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_1]
  ring

/-- `Dpoly J` has natDegree exactly 2. -/
lemma Dpoly_natDegree (J : ℕ) : (Dpoly J).natDegree = 2 := by
  have hP_ne : (P : ℚ) ≠ 0 := by unfold P; norm_num
  rw [Dpoly_eq_linear_mul]
  rw [Polynomial.natDegree_mul]
  · rw [Polynomial.natDegree_linear hP_ne, Polynomial.natDegree_linear hP_ne]
  · -- first factor ≠ 0
    intro h
    have := Polynomial.natDegree_linear (a := (P : ℚ))
        (b := (P : ℚ) * ((J : ℚ) - 1) + 1) hP_ne
    rw [h] at this; simp at this
  · -- second factor ≠ 0
    intro h
    have := Polynomial.natDegree_linear (a := (P : ℚ))
        (b := (P : ℚ) * (J : ℚ) + 1) hP_ne
    rw [h] at this; simp at this

/-- `Dpoly J` has leading coefficient `P²`. -/
lemma Dpoly_leadingCoeff (J : ℕ) : (Dpoly J).leadingCoeff = (P : ℚ) ^ 2 := by
  have hP_ne : (P : ℚ) ≠ 0 := by unfold P; norm_num
  rw [Dpoly_eq_linear_mul, Polynomial.leadingCoeff_mul]
  rw [Polynomial.leadingCoeff_linear hP_ne, Polynomial.leadingCoeff_linear hP_ne]
  ring

/-! ### Composition `(A p) ∘ (Dpoly J)`

The rescaled polynomial in Theorem 1 is `q := (A p).comp (Dpoly J) / g` where
`g` is the gcd of the main-slot values. Before dividing by `g`, we have:

  * natDegree `(A p).comp (Dpoly J) = 2 r` where `r = natDegree p`
  * leadingCoeff `(A p).comp (Dpoly J) = lc(p) · Θ_r · P^{2r}`

These follow from `Polynomial.natDegree_comp` and `Polynomial.leadingCoeff_comp`,
combined with `A_natDegree_eq`, `A_leadingCoeff_eq`, `Dpoly_natDegree`,
`Dpoly_leadingCoeff`. -/

/-- natDegree of the composition. -/
lemma A_comp_Dpoly_natDegree (p : ℚ[X]) (J : ℕ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    ((A p).comp (Dpoly J)).natDegree = 2 * p.natDegree := by
  rw [Polynomial.natDegree_comp, A_natDegree_eq p h_nonconst h_lead_pos,
      Dpoly_natDegree]
  ring

/-- `Dpoly J` is integer-valued (its coefficients are rationals but evaluate to ℤ
on ℤ inputs since each linear factor is `P·X + integer`). -/
lemma Dpoly_intValued (J : ℕ) : IntValued (Dpoly J) := by
  intro z
  refine ⟨((P : ℤ) * (z + (J : ℤ) - 1) + 1) * ((P : ℤ) * (z + (J : ℤ)) + 1), ?_⟩
  unfold Dpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
             Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  push_cast
  ring

/-- The composition `(A p).comp (Dpoly J)` is integer-valued whenever `p` is. -/
lemma A_comp_Dpoly_intValued (p : ℚ[X]) (hp : IntValued p) (J : ℕ) :
    IntValued ((A p).comp (Dpoly J)) := by
  intro z
  obtain ⟨k_D, hk_D⟩ := Dpoly_intValued J z
  obtain ⟨k_A, hk_A⟩ := A_intValued p hp k_D
  refine ⟨k_A, ?_⟩
  rw [Polynomial.eval_comp, ← hk_D, hk_A]

/-- Leading coefficient of the composition: `lc(p) · Θ_r · P^{2r}`. -/
lemma A_comp_Dpoly_leadingCoeff (p : ℚ[X]) (J : ℕ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    ((A p).comp (Dpoly J)).leadingCoeff =
      p.leadingCoeff * theta p.natDegree * ((P : ℚ) ^ (2 * p.natDegree)) := by
  have hP_ne : (P : ℚ) ≠ 0 := by unfold P; norm_num
  rw [Polynomial.leadingCoeff_comp ?_, A_leadingCoeff_eq p h_nonconst h_lead_pos,
      Dpoly_leadingCoeff, A_natDegree_eq p h_nonconst h_lead_pos]
  · -- Goal: lc(p) * Θ * (P²)^r = lc(p) * Θ * P^{2r}
    rw [← pow_mul]
  · -- Goal: (Dpoly J).natDegree ≠ 0
    rw [Dpoly_natDegree]; norm_num

/-- `0 < ((A p).comp (Dpoly J)).natDegree` whenever `1 ≤ p.natDegree`,
`lc(p) > 0`. (RSG's `0 < f.natDegree` hypothesis after `g`-division.) -/
lemma A_comp_Dpoly_natDegree_pos (p : ℚ[X]) (J : ℕ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < ((A p).comp (Dpoly J)).natDegree := by
  rw [A_comp_Dpoly_natDegree p J h_nonconst h_lead_pos]
  omega

/-- `0 < ((A p).comp (Dpoly J)).leadingCoeff` whenever `1 ≤ p.natDegree`,
`lc(p) > 0`. (RSG's `0 < f.leadingCoeff` hypothesis after `g`-division.) -/
lemma A_comp_Dpoly_leadingCoeff_pos (p : ℚ[X]) (J : ℕ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < ((A p).comp (Dpoly J)).leadingCoeff := by
  rw [A_comp_Dpoly_leadingCoeff p J h_nonconst h_lead_pos]
  have hθ : 0 < theta p.natDegree := by
    have := theta_gt_one _ h_nonconst; linarith
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  positivity

/-- `(A p).comp (Dpoly J)` evaluated at a positive integer `t` equals the
integer value `intEval (A p) (D (J + t - 1))`. This is the bridge between the
rescaled polynomial (used by RSG) and the main-slot value set used to define
the gcd `g`. -/
lemma A_comp_Dpoly_eval_at_succ (p : ℚ[X]) (hp : IntValued p) (J t : ℕ)
    (ht : 1 ≤ t) :
    ((A p).comp (Dpoly J)).eval (t : ℚ) =
      ((intEval (A p) (A_intValued p hp) ((D (J + t - 1) : ℕ) : ℤ) : ℤ) : ℚ) := by
  rw [Polynomial.eval_comp, Dpoly_eval_at_succ J t ht]
  rw [intEval_spec (A p) (A_intValued p hp) ((D (J + t - 1) : ℕ) : ℤ)]
  push_cast
  rfl

/-! ## The rescaled polynomial `qPoly`

`qPoly p J g := (A p) ∘ (Dpoly J) / g`, where `g` will be the gcd of
`(A p).intEval (D j)` for `j ≥ J` (constructed inside `Theorem1.lean`'s
case-neg). The structural facts below cover the post-division layer:
natDegree, leadingCoeff (with explicit `1/g`), and positivity. The RSG-input
predicates (positivity at positive integers + no-prime-fixed-divisor for the
quotient values) live in `Theorem1.lean` since they require `J` and the
ideal/gcd construction. -/

/-- The divided rescaled polynomial `qPoly p J g := (1/g) · (A p ∘ Dpoly J)`. -/
noncomputable def qPoly (p : ℚ[X]) (J g : ℕ) : ℚ[X] :=
  Polynomial.C ((g : ℚ)⁻¹) * ((A p).comp (Dpoly J))

/-- natDegree of `qPoly` is `2 r` (scalar `1/g ≠ 0` doesn't change degree). -/
lemma qPoly_natDegree (p : ℚ[X]) (J g : ℕ) (hg : 1 ≤ g)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (qPoly p J g).natDegree = 2 * p.natDegree := by
  unfold qPoly
  rw [Polynomial.natDegree_C_mul, A_comp_Dpoly_natDegree p J h_nonconst h_lead_pos]
  exact inv_ne_zero (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hg))

/-- Leading coefficient of `qPoly`: `lc(p) · Θ_r · P^{2r} / g`. -/
lemma qPoly_leadingCoeff (p : ℚ[X]) (J g : ℕ) (hg : 1 ≤ g)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (qPoly p J g).leadingCoeff =
      p.leadingCoeff * theta p.natDegree *
        ((P : ℚ) ^ (2 * p.natDegree)) / (g : ℚ) := by
  unfold qPoly
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      A_comp_Dpoly_leadingCoeff p J h_nonconst h_lead_pos]
  have hg_ne : (g : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hg)
  field_simp

/-- `0 < (qPoly p J g).leadingCoeff` whenever `1 ≤ g`, `1 ≤ p.natDegree`,
`lc(p) > 0`. RSG's `0 < f.leadingCoeff` hypothesis. -/
lemma qPoly_leadingCoeff_pos (p : ℚ[X]) (J g : ℕ) (hg : 1 ≤ g)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < (qPoly p J g).leadingCoeff := by
  rw [qPoly_leadingCoeff p J g hg h_nonconst h_lead_pos]
  have hθ : 0 < theta p.natDegree := by
    have := theta_gt_one _ h_nonconst; linarith
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  have hg_pos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  positivity

/-- `0 < (qPoly p J g).natDegree`. RSG's `0 < f.natDegree` hypothesis. -/
lemma qPoly_natDegree_pos (p : ℚ[X]) (J g : ℕ) (hg : 1 ≤ g)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < (qPoly p J g).natDegree := by
  rw [qPoly_natDegree p J g hg h_nonconst h_lead_pos]; omega

/-- `qPoly p J g` evaluated at `t : ℕ` (with `1 ≤ t`) equals `intEval (A p) at
D (J + t - 1)` divided by `g`. Direct corollary of `A_comp_Dpoly_eval_at_succ`. -/
lemma qPoly_eval_at_succ (p : ℚ[X]) (hp : IntValued p) (J g t : ℕ)
    (ht : 1 ≤ t) :
    (qPoly p J g).eval (t : ℚ) =
      ((intEval (A p) (A_intValued p hp)
        ((D (J + t - 1) : ℕ) : ℤ) : ℤ) : ℚ) / (g : ℚ) := by
  unfold qPoly
  rw [Polynomial.eval_mul, Polynomial.eval_C,
      A_comp_Dpoly_eval_at_succ p hp J t ht]
  ring

/-! ### RSG-indexing note

`roth_szekeres_graham` returns subset sums of `f.eval ((i + 1 : ℕ) : ℚ)` indexed
by `i : ℕ`. Substituting `t := i + 1` into `qPoly_eval_at_succ` gives:

  `(qPoly p J g).eval ((i + 1 : ℕ) : ℚ) = (intEval (A p) (D (J + i))) / g`

so the natural index correspondence in the window-representation is `i ↦ J + i`,
*not* `t ↦ J + t - 1`. The latter is internal to `Dpoly_eval_at_succ`'s proof. -/

end PolynomialEgyptianSums
