/-
SafeVerify target for Erdős Problems 283 + 351.

Public-theorem signatures with `sorry` bodies. The actual proofs live in
`Proof.lean` (currently scaffolded with internal sorries; this Spec is the
external contract).

Trust boundary: Mathlib core + Erdos283.roth_szekeres_graham (Graham 1964 /
Roth-Szekeres 1954).
-/

import Mathlib

namespace Erdos283

open Filter Polynomial Finset

universe u

def imageSet (p : ℚ[X]) : Set ℚ := sorry
def IsStronglyComplete (A : Set ℚ) : Prop := sorry
def FC_Condition_283 (p : ℤ[X]) : Prop := sorry

theorem theorem_1 (α : ℚ) (hα : 0 < α) (L : ℕ) (hL : 1 ≤ L) (p : ℚ[X])
    (h_int : ∀ n : ℤ, ∃ k : ℤ, (k : ℚ) = p.eval (n : ℚ))
    (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : ∀ d : ℕ, 2 ≤ d →
      ¬ ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, (k * (d : ℤ) : ℚ) = p.eval (n : ℚ)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
        StrictMono n ∧ (L < n 0) ∧
        (α = ∑ i, (1 : ℚ) / (n i)) ∧
        ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := sorry

theorem corollary_7 (p : ℚ[X]) (h : p = 0 ∨ 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := sorry

theorem erdos_283 :
    True ↔ ∀ p : ℤ[X], FC_Condition_283 p := sorry

theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      IsStronglyComplete (imageSet P) := sorry

end Erdos283
