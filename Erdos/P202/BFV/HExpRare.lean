/-
Erdos Problem 202 -- rarity of large hExp values in BFV pruning.

The main theorem in this file is the formal BFV Lemma 3.2 input used by the
pruning argument.  The analytic Rankin/squarefull estimate is isolated as a
named axiom.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic

namespace Erdos202

open Filter Finset

/-- The hExp cutoff used in BFV Proposition 3.1. -/
noncomputable def hExpCutoff (N : ℕ) : ℝ :=
  Real.exp (Real.sqrt (Real.log (N : ℝ)))

/--
BFV Lemma 3.2, in the explicit form needed for pruning.

Classical reference: Bourgain--Filaseta--Verstraëten, Lemma 3.2.  The intended
formal proof is a Rankin argument for
`∑_{n≤N} h(n)^s`, splitting the squarefree prime support from the squarefull
exponent contribution, and bounding the resulting Euler products by Chebyshev
and elementary convergent `∑ m⁻²` estimates.  Mathlib v4.27.0 does not appear
to provide this packaged h-function moment estimate, so this theorem is left as
the named analytic target for a focused subpass.
-/
axiom hExp_rare_count_rankin_squarefull :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-(1 / 6) + ε) N)

/-- A subset version of the hExp rarity estimate. -/
theorem hExp_rare_subset_count
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ,
        S ⊆ Finset.Icc 1 N →
        (S.filter fun n => hExpCutoff N < (hExp n : ℝ)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-(1 / 6) + ε) N) := by
  filter_upwards [hExp_rare_count_rankin_squarefull ε hε] with N hN S hS
  exact (Finset.card_le_card (by
    intro n hn
    exact Finset.mem_filter.2
      ⟨hS (Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2⟩)).trans hN

end Erdos202
