/-
SafeVerify target for Erdős Problem 694.

Enumerates the four public theorems and the `R` definition that Proof.lean
must provide, with `sorry` bodies. SafeVerify replays both files and checks
the submission's matching declarations only depend on the allow-list:

  Mathlib core (propext, Classical.choice, Quot.sound)
  + Erdos694.mertens_product   -- Mertens' product theorem (1874)
  + Erdos694.linnik_dvd        -- Linnik's theorem, divisibility form (1944)

The two extra axiom names are local to this problem; reproduction recipe
in ../README.md "Verifying with SafeVerify".
-/

import Mathlib

namespace Erdos694

open Filter Topology

noncomputable def R (x : ℕ) : ℝ := sorry

theorem totient_fibre_extremes :
    Tendsto
      (fun x : ℕ => R x /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := sorry

theorem erdos_694_asymptotic :
    Tendsto
      (fun x : ℕ => R x /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := sorry

theorem permanence_step (a b r : ℕ)
    (hab : Nat.totient a = Nat.totient b) (hr : Nat.Prime r)
    (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b) :
    Nat.totient (r * a) = Nat.totient (r * b) := sorry

theorem infinitely_many_collisions (a b : ℕ) (hb : 1 ≤ b) (hgt : b < a)
    (hab : Nat.totient a = Nat.totient b) :
    {N : ℕ | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧
      y < x ∧ b * x ≥ a * y}.Infinite := sorry

end Erdos694
