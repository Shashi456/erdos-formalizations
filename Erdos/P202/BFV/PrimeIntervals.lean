/-
Erdos Problem 202 -- prime supply for the BFV lower construction.

This file defines the `dyadicPrimeInterval` used by the explicit lower
construction. The analytic lower bound on its cardinality lives in
`Erdos.P202.BFV.Chebyshev` (a named stub); this file is sorry-free.
-/

import Mathlib

namespace Erdos202

open Filter Finset

/-! ## Dyadic prime intervals -/

/-- The primes in the dyadic interval `(y, 2y]`, represented with natural
floor endpoints.  This is the finite set used by the BFV construction. -/
noncomputable def dyadicPrimeInterval (y : ℝ) : Finset ℕ :=
  (Finset.Ioc (Nat.floor y) (Nat.floor (2 * y))).filter Nat.Prime

lemma mem_dyadicPrimeInterval {y : ℝ} {p : ℕ} :
    p ∈ dyadicPrimeInterval y ↔
      Nat.floor y < p ∧ p ≤ Nat.floor (2 * y) ∧ Nat.Prime p := by
  simp [dyadicPrimeInterval, and_assoc]

end Erdos202
