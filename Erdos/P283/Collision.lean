/-
Erdős Problems 283 + 351 — §2 collision avoidance via 2-adic / 3-adic valuations.

For all sufficiently large `N`, all denominators that may appear after any
collection of switches are pairwise distinct. The argument uses
`(v₂(d), v₃(d))` valuation profiles:

  D j        : (0, 0)        u_j is coprime to 6
  2 D j      : (1, 0)
  3 D j      : (0, 1)
  6 D j      : (1, 1)
  τ_N        : (2, 2)        τ_N = 36 u_{N+1}
  Λ f        : v₂ ≥ 3        (we choose 8 ∣ Λ)
  c_ν, e c_ν : avoided by construction during correction-slot setup

The pairwise-distinctness theorem `all_denominators_distinct_after_switches`
is the goal; sub-lemmas formalize the per-pair valuation argument.
-/

import Erdos.P283.Basic
import Erdos.P283.MainSlots

namespace PolynomialEgyptianSums

open Nat

/-- `u j = 36 j + 1` is coprime to `6`. -/
lemma u_coprime_six (j : ℕ) : Nat.Coprime (u j) 6 := by
  sorry

/-- `D j = u j · u (j+1)` is coprime to `6`. -/
lemma D_coprime_six (j : ℕ) : Nat.Coprime (D j) 6 := by
  sorry

/-- For `h ∈ {1, 2, 3, 6}`, `(v₂(h · D j), v₃(h · D j))` is `(0,0), (1,0), (0,1),
(1,1)` respectively. -/
lemma main_valuation_profile (j : ℕ) :
    (padicValNat 2 (1 * D j), padicValNat 3 (1 * D j)) = (0, 0) ∧
    (padicValNat 2 (2 * D j), padicValNat 3 (2 * D j)) = (1, 0) ∧
    (padicValNat 2 (3 * D j), padicValNat 3 (3 * D j)) = (0, 1) ∧
    (padicValNat 2 (6 * D j), padicValNat 3 (6 * D j)) = (1, 1) := by
  sorry

/-- `τ_N = 36 · u_{N+1}` has valuation profile `(2, 2)`. -/
lemma tau_valuation_profile (N : ℕ) :
    padicValNat 2 (tau N) = 2 ∧ padicValNat 3 (tau N) = 2 := by
  sorry

/-- For `8 ∣ Λ` and `f ≥ 1`, `v₂(Λ f) ≥ 3`. -/
lemma filler_v2_at_least_three (Λ f : ℕ) (hΛ : 8 ∣ Λ) (hf : 1 ≤ f) :
    3 ≤ padicValNat 2 (Λ * f) := by
  sorry

/-! ## Collision avoidance master lemma

For all sufficiently large `N`, given the collection of all main-slot copies
(`h · D j` for `h ∈ {1,2,3,6}`, `J ≤ j ≤ N`), the endpoint `τ_N`, the
correction denominators (and their `e ∈ G_ν` multiples), and the filler
denominators `Λ f`, all values are pairwise distinct.

Full statement deferred — assembled inside `Theorem1.lean`. -/

end PolynomialEgyptianSums
