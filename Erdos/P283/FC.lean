/-
Erdős Problems 283 + 351 — `formal-conjectures` upstream wrappers.

This file lives in *separate* namespaces (`Erdos283`, `Erdos351`) from the core
proof in `PolynomialEgyptianSums`, to avoid future name collisions when
`formal-conjectures` is imported alongside.

Bridges between our internal forms and FC's literal syntax:

  * `Erdos283.Condition`           — FC's per-polynomial condition (sentinel
                                      `n 0 = 0`, sums over `Finset.Icc 1 (Fin.last k)`).
  * `Erdos283.erdos_283`           — `True ↔ ∀ p : ℤ[X], Condition p`
                                      under `answer := True`.
  * `Erdos351.HasCompleteImage`    — strong completeness of `imageSet`.
  * `Erdos351.erdos_351`           — `True ↔ ∀ P : ℚ[X], 0 < P.natDegree →
                                      0 < P.leadingCoeff → HasCompleteImage P`
                                      under `answer := True`.
-/

import Erdos.P283.Theorem1
import Erdos.P283.Corollary351

/-! ## #283 wrapper -/

namespace Erdos283

open Filter Polynomial Finset

/-- The condition appearing in FC's `erdos_283` for an integer polynomial. -/
def Condition (p : ℤ[X]) : Prop :=
  p.leadingCoeff > 0 → ¬ (∃ d ≥ 2, ∀ n ≥ 1, d ∣ p.eval n) →
    ∀ᶠ m in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
      1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
      m = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i)

/-- **`formal-conjectures` upstream form for #283** under `answer := True`.

Bridges from `PolynomialEgyptianSums.theorem_1` (with `α = 1`, `L = 1`, `p`
coerced from `ℤ[X]` to `ℚ[X]`) to FC's sentinel-indexed `Fin (k+1) → ℤ` form. -/
theorem erdos_283 :
    True ↔ ∀ p : ℤ[X], Condition p := by
  sorry

end Erdos283

/-! ## #351 wrapper -/

namespace Erdos351

open Polynomial

/-- FC-named alias for `imageSet`. -/
def imageSet (P : ℚ[X]) : Set ℚ := PolynomialEgyptianSums.imageSet P

/-- FC-named alias for `IsStronglyComplete (imageSet P)`. -/
def HasCompleteImage (P : ℚ[X]) : Prop :=
  PolynomialEgyptianSums.IsStronglyComplete (imageSet P)

/-- **`formal-conjectures` upstream form for #351** under `answer := True`.

Direct from `PolynomialEgyptianSums.corollary_7_pos_leading`. -/
theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      HasCompleteImage P := by
  sorry

end Erdos351
