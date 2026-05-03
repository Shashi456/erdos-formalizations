/-
SafeVerify target for Erdős Problem 694.

This file enumerates the four public theorems we claim — plus the
auxiliary `R` definition they rely on — with `sorry` bodies. SafeVerify
then checks that `Erdos/P694/Proof.lean` provides matching declarations
that depend only on:

  Mathlib core (propext, Classical.choice, Quot.sound)
  + Erdos694.mertens_product
  + Erdos694.linnik_dvd

(The two extra named axioms are added to SafeVerify's `allowedAxioms`
list at SafeVerify/Main.lean:355.)
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
