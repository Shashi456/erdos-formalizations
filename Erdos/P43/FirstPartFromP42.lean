/-
Erdős Problem 43, Part 1 — direct corollary of #42.

The first part of #43 asks whether `binomial(|A|, 2) + binomial(|B|, 2)` is
bounded above by `binomial(f(N), 2) + O(1)` over Sidon `A, B ⊆ [1, N]` with
`(A − A) ∩ (B − B) = {0}`. Tao's first remark on the #42 thread observes that
a positive answer to #42 immediately gives a *negative* answer here: pick `A`
of maximum Sidon size `f(N)`, then apply #42 with any `M` to get a `B` of size
`M`, and the two contribute `binomial(f(N), 2) + binomial(M, 2)`, which can
exceed `binomial(f(N), 2) + C` for any constant `C` (take `M` with
`binomial(M, 2) > C`).

Following the combined PDF Section 4 corollary statement.
-/

import Erdos.P42.FC.Local
import Erdos.P43.Basic

namespace Erdos43

open Filter Set
open scoped Pointwise

/-- **Erdős #43, first part — negative answer from #42.** For every constant
`C`, eventually in `N` there exist Sidon `A, B ⊆ [1, N]` with no nonzero
common difference whose `binomial(_, 2)` sum exceeds `binomial(f(N), 2) + C`. -/
theorem p43_first_part_false_from_p42 :
    ∀ C : ℕ, ∀ᶠ N in atTop,
      ∃ A B : Set ℕ,
        A ⊆ Set.Icc 1 N ∧ B ⊆ Set.Icc 1 N ∧
        Erdos42.IsSidon A ∧ Erdos42.IsSidon B ∧
        ((A - A) ∩ (B - B) : Set ℕ) = {0} ∧
        Nat.choose (sidonNumber N) 2 + C <
          Nat.choose A.ncard 2 + Nat.choose B.ncard 2 := by
  sorry

end Erdos43
