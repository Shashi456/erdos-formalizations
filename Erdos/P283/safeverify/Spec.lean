/-
SafeVerify target for Erdős Problems 283 + 351.

Public-theorem signatures bridged to the internal `PolynomialEgyptianSums`
namespace. The actual proofs live in the split modules under `Erdos.P283.*`;
this Spec is the external contract.

Trust boundary: Mathlib core + PolynomialEgyptianSums.roth_szekeres_graham
(Graham 1964 / Roth-Szekeres 1954).
-/

import Erdos.P283.Proof

namespace SafeVerify

open Filter Polynomial Finset

/-- The image set `{p(n) + 1/n : n ∈ ℕ}` for `p ∈ ℚ[x]`. -/
def imageSet (p : ℚ[X]) : Set ℚ := PolynomialEgyptianSums.imageSet p

/-- Strong completeness: for any finite forbidden set, eventually every large
`m` is a finite subset-sum from `A \ B`. -/
def IsStronglyComplete (A : Set ℚ) : Prop :=
  PolynomialEgyptianSums.IsStronglyComplete A

/-- FC's Condition for #283 — re-exported from `Erdos.P283.FC`. -/
def FC_Condition_283 (p : ℤ[X]) : Prop := Erdos283.Condition p

/-- **Theorem 1** (PDF Theorem 1, SafeVerify form).

Bridges from the SafeVerify-style hypothesis form (naked existentials over `k`
witnessing the integer-valued and no-fixed-divisor conditions) to the internal
`PolynomialEgyptianSums.theorem_1`.

The hypothesis equivalences:
  * `h_int : ∀ n : ℤ, ∃ k : ℤ, (k : ℚ) = p.eval n`  ↔  `IntValued p`.
  * `h_no_fixed_div`  ↔  `NoFixedDivisor p hp` (witnessing existential
    `∃ k : ℤ, (k * d : ℚ) = p.eval n` is exactly `(d : ℤ) ∣ intEval p hp n`). -/
theorem theorem_1 (α : ℚ) (hα : 0 < α) (L : ℕ) (hL : 1 ≤ L) (p : ℚ[X])
    (h_int : ∀ n : ℤ, ∃ k : ℤ, (k : ℚ) = p.eval (n : ℚ))
    (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : ∀ d : ℕ, 2 ≤ d →
      ¬ ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, (k * (d : ℤ) : ℚ) = p.eval (n : ℚ)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
        StrictMono n ∧ (L < n 0) ∧
        (α = ∑ i, (1 : ℚ) / (n i)) ∧
        ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  have hp : PolynomialEgyptianSums.IntValued p := h_int
  have hnf : PolynomialEgyptianSums.NoFixedDivisor p hp := by
    intro d hd hdvd
    apply h_no_fixed_div d hd
    intro n hn
    obtain ⟨c, hc⟩ := hdvd n hn
    refine ⟨c, ?_⟩
    have h_spec := PolynomialEgyptianSums.intEval_spec p hp (n : ℤ)
    rw [hc] at h_spec
    push_cast at h_spec ⊢
    linarith
  exact PolynomialEgyptianSums.theorem_1 α hα L hL p hp h_lead_pos hnf

/-- **Corollary 7** (PDF, SafeVerify form): `imageSet p` is strongly complete
when `p = 0` or `p` has positive leading coefficient. Direct re-export of
`PolynomialEgyptianSums.corollary_7`. -/
theorem corollary_7 (p : ℚ[X]) (h : p = 0 ∨ 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) :=
  PolynomialEgyptianSums.corollary_7 p h

/-- **Erdős #283** (FC iff form): re-exported from `Erdos.P283.FC`. -/
theorem erdos_283 :
    True ↔ ∀ p : ℤ[X], FC_Condition_283 p :=
  Erdos283.erdos_283

/-- **Erdős #351** (FC iff form): re-exported from `Erdos.P283.FC`. -/
theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      IsStronglyComplete (imageSet P) :=
  Erdos351.erdos_351

end SafeVerify
