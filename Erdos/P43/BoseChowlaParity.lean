/-
Erdős Problem 43, Part 2 — equal-cardinality Bose-Chowla parity construction.

Combined PDF Section 4: for every `ε > 0`, infinitely many `N` admit Sidon
`A, B ⊆ [1, N]` of equal cardinality with `(A − A) ∩ (B − B) = {0}` and
`(1 − ε) · binomial(f(N), 2) ≤ binomial(|A|, 2) + binomial(|B|, 2)`.

Construction: take `q` prime power, work in `ZMod (q² − 1)` with the
Bose-Chowla Sidon set, split by parity of residues, prove the split is
nearly balanced, halve into `[1, N]` with `N = (q² − 1) / 2`. This gives
two Sidon sets of nearly equal cardinality with disjoint nonzero differences.

The live #43 thread reports a Lean formalization of this construction
(Erdős-Turán upper bound + Bose-Chowla, by Aristotle/Harmonic). The intent of
this scaffold is to either port that proof or develop one in-house.
-/

import Erdos.P43.Basic

namespace Erdos43

open Filter
open scoped Pointwise

/-- **Erdős #43, second part — equal-cardinality construction.**
Epsilon-style statement (avoiding raw `o(1)` notation): for every `ε > 0`,
infinitely many `N` admit equal-size Sidon `A, B ⊆ [1, N]` with disjoint
nonzero differences whose joint pair-count is `≥ (1 − ε) · binomial(f(N), 2)`. -/
theorem p43_second_part_epsilon :
    ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N in atTop,
        ∃ A B : Set ℕ,
          A ⊆ Set.Icc 1 N ∧ B ⊆ Set.Icc 1 N ∧
          Erdos42.IsSidon A ∧ Erdos42.IsSidon B ∧
          A.ncard = B.ncard ∧
          ((A - A) ∩ (B - B) : Set ℕ) = {0} ∧
          (1 - ε) * (Nat.choose (sidonNumber N) 2 : ℝ) ≤
            (Nat.choose A.ncard 2 + Nat.choose B.ncard 2 : ℝ) := by
  sorry

end Erdos43
