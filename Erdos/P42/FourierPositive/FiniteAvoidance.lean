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

import Erdos.P42.Shared.Common
import Erdos.P42.Shared.FiniteFourier

namespace Erdos42

open Finset
open scoped Classical

namespace FourierPositive

/-- An ordered tuple in `U^m` whose pairwise differences avoid `F`. -/
def AvoidsForbiddenDiffs {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) (x : Fin m → ZMod p) : Prop :=
  (∀ i, x i ∈ U) ∧
    ∀ i j : Fin m, i ≠ j → x i - x j ∉ F

/-- **Counting finite Fourier avoidance theorem.**

This is the Route A trust boundary in the form closest to the combined
PDF / Ulam-note statement: under the density and one-sided Fourier hypotheses,
there are at least `c * p^m` ordered avoiding tuples. The downstream #42 proof
only needs existence; `finite_fourier_avoidance_exists` below derives that
weaker interface from this count statement. -/
axiom finite_fourier_avoidance_count
    (m : ℕ) (α ρ : ℝ)
    (_hm : 1 ≤ m) (_hα : 0 < α) (_hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      c * (p : ℝ) ^ m ≤
        (((Finset.univ : Finset (Fin m → ZMod p)).filter
          (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ)

/-- Existence-only finite Fourier avoidance, derived from the count version.

This is the interface used by the #42 downstream proof. Keeping it as a theorem
rather than an axiom makes the stronger count statement the only Route A
analytic trust boundary. -/
theorem finite_fourier_avoidance_exists
    (m : ℕ) (α ρ : ℝ)
    (hm : 1 ≤ m) (hα : 0 < α) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      ∃ x : Fin m → ZMod p, AvoidsForbiddenDiffs F U x := by
  classical
  obtain ⟨ε, hε, c, hc, p₀, hcount⟩ :=
    finite_fourier_avoidance_count m α ρ hm hα hρ
  refine ⟨ε, hε, p₀, ?_⟩
  intro p hp hp₀ F U hFsym hFzero hFdense hUdense hFourier
  have hcnt :=
    hcount p hp₀ F U hFsym hFzero hFdense hUdense hFourier
  let S : Finset (Fin m → ZMod p) :=
    (Finset.univ : Finset (Fin m → ZMod p)).filter
      (fun x => AvoidsForbiddenDiffs F U x)
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hleft_pos : 0 < c * (p : ℝ) ^ m := by
    exact mul_pos hc (pow_pos hp_pos m)
  have hScard_pos_real : 0 < (S.card : ℝ) := by
    exact lt_of_lt_of_le hleft_pos (by simpa [S] using hcnt)
  have hScard_pos : 0 < S.card := by exact_mod_cast hScard_pos_real
  obtain ⟨x, hxS⟩ := Finset.card_pos.mp hScard_pos
  refine ⟨x, ?_⟩
  simpa [S] using hxS

end FourierPositive

end Erdos42
