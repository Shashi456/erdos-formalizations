/-
Erdős Problem 42 — Route A trust boundary: finite Fourier avoidance theorem.

Combined-PDF / Ulam-note finite theorem: for fixed `m, α, ρ`, there exist
`ε, p₀` such that for every prime `p ≥ p₀`, every symmetric `F ⊆ ZMod p`
containing `0` with density `≤ 1 − ρ` and Fourier *lower* bound `≥ −ε` and
every `U ⊆ ZMod p` of density `≥ α`, there is an ordered `m`-tuple in `U^m`
whose pairwise differences all avoid `F`.

Mathematically: classical, via Green-Tao `U²` regularity + complexity-1
counting. The downstream Lean proof of #42 is then elementary combinatorics,
the Sidon Fourier estimate, and greedy Sidon extraction.
-/

import Erdos.P42.Basic
import Erdos.P42.FourierAPI

namespace Erdos42

open Finset
open scoped Classical

namespace FourierPositive

/-- An ordered tuple in `U^m` whose pairwise differences avoid `F`. -/
def AvoidsForbiddenDiffs {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) (x : Fin m → ZMod p) : Prop :=
  (∀ i, x i ∈ U) ∧
    ∀ i j : Fin m, i ≠ j → x i - x j ∉ F

/-- **Existence-only finite Fourier avoidance theorem.**

This is the Route A trust boundary. It is the weaker form of the combined
PDF / Ulam-note counting theorem actually needed downstream: apply it with
`m = greedySidonThreshold M` and then extract a Sidon subset greedily. -/
axiom finite_fourier_avoidance_exists
    (m : ℕ) (α ρ : ℝ)
    (_hm : 1 ≤ m) (_hα : 0 < α) (_hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      ∃ x : Fin m → ZMod p, AvoidsForbiddenDiffs F U x

end FourierPositive

end Erdos42
