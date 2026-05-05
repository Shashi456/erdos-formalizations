/-
Erdős Problems 283 + 351 — §3 Corollary 7 (strong completeness, #351).

Three cases:

  * `corollary_7_zero`             — `p = 0`: every positive integer is a sum
                                      of distinct unit reciprocals (Lemma 3).
  * `corollary_7_pos_leading`      — `p ≠ 0` with positive leading coefficient:
                                      reduce to integer polynomial `q := Dp/h`,
                                      apply `theorem_1` for each residue
                                      `r ∈ {1, …, h}`.
  * `not_strongly_complete_of_neg_leadingCoeff` — `p` has negative leading
                                                   coefficient: bounded above,
                                                   so not strongly complete
                                                   (optional; FC #351 doesn't
                                                   need it).
-/

import Erdos.P283.Basic
import Erdos.P283.Egyptian
import Erdos.P283.Theorem1

namespace PolynomialEgyptianSums

open Polynomial Filter

/-- The set `A_p = { p(n) + 1/n : n ∈ ℕ }` for `p ∈ ℚ[x]`. (Note: `1/0 = 0` in
`ℚ`, so `A_p` includes `p(0)` — harmless per the FC convention.) -/
def imageSet (p : ℚ[X]) : Set ℚ :=
  Set.range (fun (n : ℕ) ↦ p.eval (n : ℚ) + 1 / (n : ℚ))

/-- `A ⊆ ℚ` is **strongly complete** if every sufficiently large natural number
is a finite subset-sum of `A \ B` for any finite `B`. -/
def IsStronglyComplete (A : Set ℚ) : Prop :=
  ∀ B : Finset ℚ,
    ∀ᶠ (m : ℕ) in Filter.atTop,
      ((m : ℕ) : ℚ) ∈ { ∑ x ∈ X, x | (X : Finset ℚ) (_ : (↑X : Set ℚ) ⊆ A \ ↑B) }

/-! ## Case `p = 0` -/

/-- **Corollary 7, case `p = 0`.** `A_0 = {1/n : n ∈ ℕ}` is strongly complete:
every positive integer is a sum of distinct unit reciprocals (Lemma 3). -/
theorem corollary_7_zero : IsStronglyComplete (imageSet (0 : ℚ[X])) := by
  classical
  intro B
  rw [Filter.eventually_atTop]
  -- Pick `L` large enough that `1/e ∉ B` for all `e > L`.
  set L := (insert 0 (B.image (fun b => b.den))).max'
    (Finset.insert_nonempty 0 _) with hL_def
  have hL_avoid : ∀ e : ℕ, L < e → (1 : ℚ) / e ∉ B := by
    intro e he hb
    have he_pos : 1 ≤ e := by omega
    have h_den : ((1 : ℚ) / e).den = e := by
      rw [one_div, Rat.inv_natCast_den_of_pos he_pos]
    have h_mem_image : e ∈ B.image (fun b => b.den) := by
      rw [Finset.mem_image]
      exact ⟨(1 : ℚ) / e, hb, h_den⟩
    have h_mem_insert : e ∈ (insert 0 (B.image (fun b => b.den))) := by
      rw [Finset.mem_insert]; exact Or.inr h_mem_image
    have h_le : e ≤ L := Finset.le_max' _ e h_mem_insert
    omega
  -- For `m ≥ 1`, apply Lemma 3 with `R = m` and our `L`.
  refine ⟨1, ?_⟩
  intro m hm
  have hm_pos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  obtain ⟨K, hK⟩ := egyptian_expansion (m : ℚ) hm_pos L
  obtain ⟨E, _hE_card, hE_lb, hE_sum⟩ := hK K (le_refl K)
  -- Build `X = E.image (fun e => 1/e)`.
  refine ⟨E.image (fun e : ℕ => (1 : ℚ) / (e : ℚ)), ?_, ?_⟩
  · -- ↑X ⊆ imageSet 0 \ ↑B
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have he_lb := hE_lb e he
    refine ⟨?_, ?_⟩
    · -- 1/e ∈ imageSet 0 since (0 : ℚ[X]).eval e + 1/e = 1/e
      refine ⟨e, ?_⟩
      simp [Polynomial.eval_zero]
    · exact hL_avoid e he_lb
  · -- ∑ x ∈ X, x = ↑m
    have h_inj : Set.InjOn (fun e : ℕ => (1 : ℚ) / (e : ℚ)) (E : Set ℕ) := by
      intro a ha b hb hab
      have ha_pos : 1 ≤ a := by have := hE_lb a ha; omega
      have hb_pos : 1 ≤ b := by have := hE_lb b hb; omega
      simp only [one_div] at hab
      have h1 : (a : ℚ) = (b : ℚ) := inv_inj.mp hab
      exact_mod_cast h1
    rw [Finset.sum_image h_inj]
    exact hE_sum.symm

/-! ## Case positive leading coefficient -/

/-- **Corollary 7, positive-leading case.** For `p ≠ 0` with positive leading
coefficient, `A_p` is strongly complete. The proof reduces to `theorem_1` via
`q := Dp/h` (denominator-cleared, fixed-divisor-removed) for each residue
`r ∈ {1, …, h}`. -/
theorem corollary_7_pos_leading (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := by
  sorry

/-! ## Case negative leading coefficient (impossibility) -/

/-- For `p` with **negative** leading coefficient, `A_p` is *not* strongly
complete: only finitely many elements of `A_p` are positive, so subset sums are
bounded. (Not needed for FC #351; included for the corrected mathematical
statement.) -/
theorem not_strongly_complete_of_neg_leadingCoeff
    (p : ℚ[X]) (hp : p.leadingCoeff < 0) :
    ¬ IsStronglyComplete (imageSet p) := by
  sorry

/-! ## Combined corollary 7 statement -/

/-- **Corollary 7 (PDF, combined).** If `p = 0` or `p ≠ 0` with positive leading
coefficient, `A_p = {p(n) + 1/n}` is strongly complete. -/
theorem corollary_7 (p : ℚ[X])
    (h : p = 0 ∨ (1 ≤ p.natDegree ∧ 0 < p.leadingCoeff)) :
    IsStronglyComplete (imageSet p) := by
  rcases h with rfl | ⟨hd, hl⟩
  · exact corollary_7_zero
  · exact corollary_7_pos_leading p hd hl

end PolynomialEgyptianSums
