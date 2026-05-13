/-
Erdos Problem 202 -- radical multiplicity in BFV pruning.

For fixed radical, fixed omega, and bounded `hExp`, BFV Lemma 3.3 gives a
finite multiplicity bound.  This is a finite combinatorial theorem, but the
full exponent-vector encoding is kept isolated as a named axiom so the final
pruning file only consumes a single clean interface.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic

namespace Erdos202

open Finset
open scoped BigOperators

/--
Finite reciprocal-square bound used in the exponent-vector count.

This is the local BFV copy of the elementary estimate
`∑_{m=1}^H 1 / m^2 ≤ 2`.  It is duplicated here rather than importing
`P202Optimization`, which depends on the BFV input layer.
-/
lemma sum_inv_sq_le_two_bfv (H : ℕ) :
    (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have hstrong : ∀ H : ℕ, 1 ≤ H →
      (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤
        2 - 1 / (H : ℝ) := by
    intro H hH
    induction H with
    | zero =>
        cases hH
    | succ H ih =>
        cases H with
        | zero =>
            norm_num
        | succ H =>
            rw [Finset.sum_range_succ]
            have ih' :
                (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  ≤ 2 - 1 / ((H + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2 ≤
                  1 / ((H + 1 : ℕ) : ℝ) -
                    1 / (((H + 1 + 1 : ℕ) : ℝ)) := by
              have hcast :
                  (((H + 1 + 1 : ℕ) : ℝ)) = ((H + 1 : ℕ) : ℝ) + 1 := by
                norm_num
              rw [hcast]
              have hH1 : 0 < ((H + 1 : ℕ) : ℝ) := by positivity
              have hH2 : 0 < ((H + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hH1.ne', hH2.ne']
              ring_nf
              nlinarith [show 0 ≤ (H : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  + 1 / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2
                  ≤ (2 - 1 / ((H + 1 : ℕ) : ℝ))
                      + (1 / ((H + 1 : ℕ) : ℝ) -
                        1 / (((H + 1 + 1 : ℕ) : ℝ))) := by
                    gcongr
              _ = 2 - 1 / ((H + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hH : H = 0
  · simp [hH]
  · have hH1 : 1 ≤ H := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hH)
    exact (hstrong H hH1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (H : ℝ) := by positivity
      linarith)

/--
BFV Lemma 3.3 multiplicity bound.

For a fixed radical `r`, fixed `omega = K`, and `hExp ≤ H`, the possible
moduli are encoded by exponent vectors on the `K` primes in the radical.  BFV
counts those vectors by
`H^2 * (∑_{ν≥1} ν⁻²)^K ≤ H^2 * 2^K`.

The remaining formal work is finite: construct the exponent-vector injection
from `Nat.factorization`, prove the product bound from `hExp`, and apply
`sum_inv_sq_le_two_bfv`.  No analytic number theory is hidden in this target.
-/
axiom rad_multiplicity_bfv33
    (S : Finset ℕ) (r K : ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hS : ∀ q ∈ S, rad q = r ∧ omega q = K ∧ (hExp q : ℝ) ≤ H) :
    (S.card : ℝ) ≤ H ^ 2 * (2 : ℝ) ^ K

end Erdos202
