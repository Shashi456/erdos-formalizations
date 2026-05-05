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
  refine ⟨fun _ p => ?_, fun _ => trivial⟩
  unfold Condition
  intro hlc hnf
  rw [Filter.eventually_atTop]
  -- Coerce `p : ℤ[X]` to `pℚ : ℚ[X]`.
  set pℚ : ℚ[X] := p.map (Int.castRingHom ℚ) with hpℚ
  -- `pℚ` is integer-valued: at any integer `z`, `pℚ.eval (z : ℚ) = (p.eval z : ℤ → ℚ)`.
  have hp_int : PolynomialEgyptianSums.IntValued pℚ := by
    intro z
    refine ⟨Polynomial.eval z p, ?_⟩
    show ((Polynomial.eval z p : ℤ) : ℚ) = pℚ.eval ((z : ℤ) : ℚ)
    rw [hpℚ, Polynomial.eval_map]
    rw [show ((z : ℤ) : ℚ) = (Int.castRingHom ℚ) z from rfl]
    rw [Polynomial.eval₂_at_apply]
    simp
  -- `pℚ.leadingCoeff = (p.leadingCoeff : ℤ → ℚ) > 0`.
  have hlc_pℚ : 0 < pℚ.leadingCoeff := by
    rw [hpℚ]
    rw [Polynomial.leadingCoeff_map_of_injective (f := Int.castRingHom ℚ) Int.cast_injective]
    show 0 < ((p.leadingCoeff : ℤ) : ℚ)
    exact_mod_cast hlc
  -- `intEval pℚ hp_int z = p.eval z` (as ℤ).
  have h_intEval_eq : ∀ z : ℤ,
      PolynomialEgyptianSums.intEval pℚ hp_int z = Polynomial.eval z p := by
    intro z
    have h1 := PolynomialEgyptianSums.intEval_spec pℚ hp_int z
    have h2 : ((Polynomial.eval z p : ℤ) : ℚ) = pℚ.eval ((z : ℤ) : ℚ) := by
      rw [hpℚ, Polynomial.eval_map]
      rw [show ((z : ℤ) : ℚ) = (Int.castRingHom ℚ) z from rfl]
      rw [Polynomial.eval₂_at_apply]
      simp
    have h3 :
        ((PolynomialEgyptianSums.intEval pℚ hp_int z : ℤ) : ℚ)
          = ((Polynomial.eval z p : ℤ) : ℚ) := by
      rw [h1, h2]
    exact_mod_cast h3
  -- `NoFixedDivisor pℚ hp_int` from `hnf` (FC's no-fixed-divisor on ℤ).
  have hnf_pℚ : PolynomialEgyptianSums.NoFixedDivisor pℚ hp_int := by
    intro d hd hdvd
    apply hnf
    refine ⟨(d : ℤ), by exact_mod_cast hd, ?_⟩
    intro n hn
    obtain ⟨n_nat, hn_eq⟩ : ∃ n_nat : ℕ, (n_nat : ℤ) = n := ⟨n.toNat, by omega⟩
    have h1n : 1 ≤ n_nat := by omega
    have hdvd1 := hdvd n_nat h1n
    rw [h_intEval_eq, hn_eq] at hdvd1
    exact hdvd1
  -- Apply `theorem_1` with `α = 1`, `L = 1`.
  obtain ⟨m₀, hm₀⟩ := PolynomialEgyptianSums.theorem_1 1 (by norm_num) 1 (le_refl 1) pℚ
    hp_int hlc_pℚ hnf_pℚ
  refine ⟨m₀, fun m hm => ?_⟩
  -- `m : ℤ` from `Filter.atTop` over ℤ; coerce to ℕ via `m.toNat`.
  have hm_cast : (m.toNat : ℤ) = m := by omega
  obtain ⟨k, n_int, hStrict, hLb, hsum_recip, hsum_p⟩ := hm₀ m.toNat (by omega)
  -- Build `n_FC : Fin (k+1+1) → ℤ` as `Fin.cons 0 (fun i => (n_int i : ℕ → ℤ))`.
  refine ⟨k + 1, by omega, Fin.cons 0 (fun i : Fin (k + 1) => (n_int i : ℤ)), ?_, ?_, ?_, ?_⟩
  · -- Sentinel: `n_FC 0 = 0`.
    rfl
  · -- `StrictMono n_FC`: case-split on `i, j` via `Fin.cases`.
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd hij (lt_irrefl _)
      | succ j' =>
        rw [Fin.cons_zero, Fin.cons_succ]
        have h1 : n_int 0 ≤ n_int j' := hStrict.monotone (Fin.zero_le _)
        have h2 : 1 < n_int j' := lt_of_lt_of_le hLb h1
        have h3 : 0 < n_int j' := by omega
        exact_mod_cast h3
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ j' =>
        rw [Fin.cons_succ, Fin.cons_succ]
        have hij' : i' < j' := Fin.succ_lt_succ_iff.mp hij
        exact_mod_cast hStrict hij'
  · -- Reciprocal sum: `1 = ∑ i ∈ Icc 1 (Fin.last (k+1)), 1 / n_FC i`.
    -- Re-index `Icc 1 (Fin.last (k+1)) = image Fin.succ univ`, then use `Fin.cons_succ`.
    have h_eq : Finset.Icc (1 : Fin (k + 1 + 1)) (Fin.last (k + 1)) =
        Finset.image Fin.succ (Finset.univ : Finset (Fin (k + 1))) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro ⟨h1, h2⟩
        obtain ⟨v, hv⟩ := i
        simp [Fin.le_def, Fin.val_last] at h1 h2
        refine ⟨⟨v - 1, ?_⟩, ?_⟩
        · simp; omega
        · ext; simp; omega
      · rintro ⟨j, rfl⟩
        obtain ⟨w, hw⟩ := j
        refine ⟨?_, ?_⟩
        · simp [Fin.le_def]
        · simp [Fin.le_def, Fin.val_last]; omega
    rw [h_eq]
    rw [Finset.sum_image (fun a _ b _ h => Fin.succ_injective _ h)]
    simp_rw [Fin.cons_succ]
    convert hsum_recip using 1
  · -- Polynomial sum: `m = ∑ i ∈ Icc 1 (Fin.last (k+1)), p.eval (n_FC i)`.
    have h_eq : Finset.Icc (1 : Fin (k + 1 + 1)) (Fin.last (k + 1)) =
        Finset.image Fin.succ (Finset.univ : Finset (Fin (k + 1))) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro ⟨h1, h2⟩
        obtain ⟨v, hv⟩ := i
        simp [Fin.le_def, Fin.val_last] at h1 h2
        refine ⟨⟨v - 1, ?_⟩, ?_⟩
        · simp; omega
        · ext; simp; omega
      · rintro ⟨j, rfl⟩
        obtain ⟨w, hw⟩ := j
        refine ⟨?_, ?_⟩
        · simp [Fin.le_def]
        · simp [Fin.le_def, Fin.val_last]; omega
    rw [h_eq]
    rw [Finset.sum_image (fun a _ b _ h => Fin.succ_injective _ h)]
    simp_rw [Fin.cons_succ]
    -- Bridge `pℚ.eval ((z : ℕ → ℚ)) = ((p.eval (z : ℕ → ℤ) : ℤ → ℚ))`.
    have h_eval : ∀ z : ℕ,
        pℚ.eval ((z : ℕ) : ℚ) = ((Polynomial.eval (z : ℤ) p : ℤ) : ℚ) := by
      intro z
      rw [hpℚ, Polynomial.eval_map]
      rw [show ((z : ℕ) : ℚ) = (Int.castRingHom ℚ) (z : ℤ) from rfl]
      rw [Polynomial.eval₂_at_apply]
      simp
    -- Cast `hsum_p` over to the ℤ-valued sum.
    have h_rat : (m : ℚ) =
        ∑ i : Fin (k + 1), ((Polynomial.eval ((n_int i : ℤ) : ℤ) p : ℤ) : ℚ) := by
      rw [show (m : ℚ) = ((m.toNat : ℕ) : ℚ) by exact_mod_cast hm_cast.symm]
      rw [hsum_p]
      apply Finset.sum_congr rfl
      intro i _
      rw [h_eval]
    have h_int : (m : ℚ) =
        ((∑ i : Fin (k + 1), Polynomial.eval ((n_int i : ℤ) : ℤ) p : ℤ) : ℚ) := by
      rw [h_rat]; push_cast; rfl
    exact_mod_cast h_int

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
  refine ⟨fun _ P _ hlc => ?_, fun _ => trivial⟩
  exact PolynomialEgyptianSums.corollary_7_pos_leading P hlc

end Erdos351
