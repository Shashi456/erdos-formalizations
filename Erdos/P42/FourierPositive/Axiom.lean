/-
Erdős Problem 42 — Route A trust boundary: finite Fourier avoidance theorem.

Combined-PDF / Ulam-note finite theorem: for fixed `m, α, ρ`, there exist
`ε, c, p₀` such that for every prime `p ≥ p₀`, every symmetric `F ⊆ ZMod p`
containing `0` with density `≤ 1 − ρ` and Fourier *lower* bound `≥ −ε` and
every `U ⊆ ZMod p` of density `≥ α`, there are `≥ c · p^m` ordered `m`-tuples
in `U^m` whose pairwise differences all avoid `F`.

Mathematically: classical, via Green-Tao `U²` regularity + complexity-1
counting. The downstream Lean proof of #42 is then elementary combinatorics +
Sidon Fourier estimate + non-Sidon-tuple discard.
-/

import Erdos.P42.Basic
import Erdos.P42.FourierAPI

namespace Erdos42

open Finset

namespace FourierPositive

/-- **Finite Fourier avoidance theorem (combined PDF / Ulam note).**
Trust boundary for Route A. For every `m ≥ 1` and densities `α, ρ > 0`,
there exist `ε, c > 0` and `p₀` such that for every prime `p ≥ p₀`, every
symmetric `F ⊆ ZMod p` containing `0` with `|F| ≤ (1−ρ)p` and Fourier lower
bound `≥ −ε`, and every `U ⊆ ZMod p` with `|U| ≥ αp`, the number of ordered
`m`-tuples `x : Fin m → ZMod p` taking values in `U` and avoiding `F` in all
pairwise differences is at least `c · p^m`. -/
axiom finite_fourier_avoidance
    (m : ℕ) (α ρ : ℝ)
    (_hm : 1 ≤ m) (_hα : 0 < α) (_hρ : 0 < ρ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      c * (p : ℝ) ^ m ≤
        ((Finset.univ : Finset (Fin m → ZMod p)).filter
          (fun x =>
            (∀ i, x i ∈ U) ∧
            ∀ i j : Fin m, i ≠ j → x i - x j ∉ F)).card

end FourierPositive

end Erdos42
