/-
Erdos Problem 202 -- exact omega-count reduction.

This file reduces an exact omega level to the omega-tail estimate from
`OmegaTail.lean` and performs the scale algebra for the BFV `W` factor.
-/

import Mathlib
import Erdos.P202.BFV.OmegaTail

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Exact omega levels are bounded by omega tails -/

lemma omega_exact_filter_subset_tail (y t : ℕ) :
    (Finset.Icc 1 y).filter (fun n => omega n = t)
      ⊆ (Finset.Icc 1 y).filter (fun n => t ≤ omega n) := by
  intro n hn
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2.ge⟩

lemma omega_exact_card_le_tail_card (y t : ℕ) :
    ((Finset.Icc 1 y).filter (fun n => omega n = t)).card
      ≤ ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card :=
  Finset.card_le_card (omega_exact_filter_subset_tail y t)

/-! ## BFV scale algebra -/

private lemma exact_target_eq_tail_target {N y K W : ℕ} (ε : ℝ)
    (hN : Real.exp 1 < (N : ℝ)) (hWK : W ≤ K) :
    (y : ℝ) *
        Real.exp ((-(((K - W : ℕ) : ℝ) / Mscale N) / 2 + ε) * Zscale N)
      =
    (y : ℝ) *
        Real.exp ((-((K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hN
  have hZdivM : Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) :=
    Zscale_div_Mscale_eq_loglog hN
  have hcast : (((K - W : ℕ) : ℝ)) = (K : ℝ) - (W : ℝ) := by
    exact_mod_cast (Nat.cast_sub hWK : ((K - W : ℕ) : ℝ) = (K : ℝ) - (W : ℝ))
  have hexp :
      ((-(((K - W : ℕ) : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        =
      ((-((K : ℝ) / Mscale N) / 2 + ε) * Zscale N) +
        (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
    rw [hcast, ← hZdivM]
    field_simp [hMpos.ne']
    ring
  rw [hexp, Real.exp_add]
  ring

/-! ## Exact BFV omega count -/

/-- Exact omega count, derived from `bfv_omega_tail_theorem`.

The statement matches the BFV input shape except for the theorem name. -/
theorem bfv_omega_exact_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  intro ε hε
  filter_upwards [bfv_omega_tail_theorem ε hε,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hTail hNlarge_nat
  intro y K W hy hWK hK
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hExactTail := omega_exact_card_le_tail_card y (K - W)
  have ht_le_K_real : ((K - W : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.sub_le K W
  have ht_bound : ((K - W : ℕ) : ℝ) ≤ 3 * Mscale N := ht_le_K_real.trans hK
  have hTailApplied := hTail y (K - W) hy ht_bound
  have htarget :=
    exact_target_eq_tail_target (N := N) (y := y) (K := K) (W := W) ε hNlarge hWK
  dsimp only at hTailApplied ⊢
  exact hExactTail.trans (by simpa [htarget] using hTailApplied)

end Erdos202
