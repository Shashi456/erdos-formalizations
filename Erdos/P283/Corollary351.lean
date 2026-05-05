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
theorem corollary_7_zero : IsStronglyComplete (imageSet 0) := by
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

/-! ### Helper lemmas for `corollary_7_pos_leading` -/

/-- `IntValued (C D * p)` whenever `D · p` has integer coefficients. The
witness at `z : ℤ` is `R.eval z` where `R : ℤ[X]` is the integer multiple. -/
private lemma intValued_C_mul_of_HasIntegralMultiple (D : ℕ) (p : ℚ[X])
    (hDp : HasIntegralMultiple D p) :
    IntValued (Polynomial.C (D : ℚ) * p) := by
  obtain ⟨R, hR⟩ := hDp
  intro z
  refine ⟨R.eval z, ?_⟩
  have h1 : ((R.map (Int.castRingHom ℚ)).eval ((z : ℤ) : ℚ)) =
      (Polynomial.C (D : ℚ) * p).eval ((z : ℚ)) := by
    rw [hR]
  rw [Polynomial.eval_map] at h1
  have h2 : Polynomial.eval₂ (Int.castRingHom ℚ) ((z : ℤ) : ℚ) R =
      ((R.eval z : ℤ) : ℚ) := Polynomial.eval₂_at_apply (Int.castRingHom ℚ) z
  rw [h2] at h1
  exact h1

/-- `IntValued (C ((h : ℚ)⁻¹) * (C D * p))` whenever `D · p` is integer-valued
and `h ∣ (D · p).eval z` (as ℤ) for every `z : ℤ`. -/
private lemma intValued_C_inv_mul (h : ℕ) (hh_pos : 1 ≤ h) (Dp : ℚ[X])
    (hDp_int : IntValued Dp)
    (h_dvd : ∀ z : ℤ, (h : ℤ) ∣ intEval Dp hDp_int z) :
    IntValued (Polynomial.C ((h : ℚ)⁻¹) * Dp) := by
  intro z
  obtain ⟨k, hk⟩ := h_dvd z
  refine ⟨k, ?_⟩
  -- (k : ℚ) = (Dp.eval z) / h, since Dp.eval z = h · k.
  have hDpk : (intEval Dp hDp_int z : ℚ) = (h : ℚ) * (k : ℚ) := by
    have : ((intEval Dp hDp_int z : ℤ) : ℚ) = (((h : ℤ) * k : ℤ) : ℚ) := by
      rw [hk]
    push_cast at this; exact this
  have h_eval := intEval_spec Dp hDp_int z
  have hh_ne : (h : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh_pos
    exact ne_of_gt this
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  -- Goal: (k : ℚ) = (h : ℚ)⁻¹ * Dp.eval (z : ℚ).
  rw [← h_eval, hDpk]
  field_simp

/-- **Mahler / finite-differences extension of fixed divisor.** If `q : ℚ[X]` is
integer-valued and `d ∣ q(n)` for every positive integer `n`, then `d ∣ q(w)` for
every integer `w`. The proof uses that the `(N+1)`-th forward difference of a
degree-`N` polynomial vanishes, giving a recurrence that lets us extend
divisibility from `ℕ_{≥1}` to all of `ℤ`. -/
private lemma intValued_dvd_extends_to_int (q : ℚ[X]) (hq_int : IntValued q)
    (d : ℕ)
    (hdvd_pos : ∀ n : ℕ, 1 ≤ n → (d : ℤ) ∣ intEval q hq_int (n : ℤ)) :
    ∀ w : ℤ, (d : ℤ) ∣ intEval q hq_int w := by
  set N : ℕ := q.natDegree
  -- Step 1: (N+1)-th forward difference recurrence in ℤ at integer points.
  have h_recur : ∀ y : ℤ,
      ∑ k ∈ Finset.range (N + 2),
        ((-1 : ℤ) ^ (N + 1 - k) * ((N + 1).choose k)) •
          intEval q hq_int (y + (k : ℤ)) = 0 := by
    intro y
    -- Apply Polynomial.fwdDiff_iter_eq_zero_of_degree_lt to q.eval at (y : ℚ).
    have hq_zero : (fwdDiff (1 : ℚ))^[N + 1] (fun x => q.eval x) ((y : ℤ) : ℚ) = 0 := by
      have hP := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := q) (n := N + 1)
        (Nat.lt_succ_self _)
      exact congr_fun hP ((y : ℤ) : ℚ)
    rw [fwdDiff_iter_eq_sum_shift] at hq_zero
    -- Each term in ℚ is the cast of an integer term.
    have hsum_eq :
        ∑ k ∈ Finset.range (N + 2),
            ((-1 : ℤ) ^ (N + 1 - k) * ((N + 1).choose k)) •
              q.eval (((y : ℤ) : ℚ) + k • (1 : ℚ)) =
        (((∑ k ∈ Finset.range (N + 2),
            ((-1 : ℤ) ^ (N + 1 - k) * ((N + 1).choose k)) •
              intEval q hq_int (y + (k : ℤ))) : ℤ) : ℚ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro k _
      have h1 : ((y : ℤ) : ℚ) + k • (1 : ℚ) = ((y + (k : ℤ) : ℤ) : ℚ) := by
        push_cast; ring
      rw [h1, ← intEval_spec q hq_int (y + (k : ℤ))]
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one, Int.cast_natCast]
    rw [hsum_eq] at hq_zero
    exact_mod_cast hq_zero
  -- Step 2: Isolate `intEval q hq_int y` from the recurrence.
  have h_dvd_smul : ∀ y : ℤ,
      (∀ k : ℕ, k ∈ Finset.range (N + 1) →
        (d : ℤ) ∣ intEval q hq_int (y + ((k : ℤ) + 1))) →
      (d : ℤ) ∣ intEval q hq_int y := by
    intro y hk_dvd
    have h_recur_y := h_recur y
    -- Split sum: k = 0 term and k ≥ 1 terms.
    rw [Finset.sum_range_succ' _ (N + 1)] at h_recur_y
    -- Now h_recur_y has form: (sum over k ∈ range (N+1)) + (k=0 term) = 0.
    -- The (k=0) term: ((-1)^(N+1-0) * (N+1).choose 0) • intEval q hq_int (y + 0).
    have h_y_simp : intEval q hq_int (y + ((0 : ℕ) : ℤ)) = intEval q hq_int y := by
      norm_num
    have h_k_simp : ∀ k : ℕ,
        intEval q hq_int (y + ((k + 1 : ℕ) : ℤ)) =
          intEval q hq_int (y + ((k : ℤ) + 1)) := by
      intro k
      push_cast
      rfl
    -- Rewrite into a uniform form.
    have h_recur_y' :
        ∑ k ∈ Finset.range (N + 1),
            ((-1 : ℤ) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1))) •
              intEval q hq_int (y + ((k : ℤ) + 1)) +
        ((-1 : ℤ) ^ (N + 1)) * intEval q hq_int y = 0 := by
      have := h_recur_y
      simp only [smul_eq_mul, h_y_simp, Nat.choose_zero_right, Nat.cast_one,
        mul_one, Nat.sub_zero] at this
      have hsum_congr :
          ∑ x ∈ Finset.range (N + 1),
              (-1 : ℤ) ^ (N + 1 - (x + 1)) * ((N + 1).choose (x + 1)) *
                intEval q hq_int (y + ((x + 1 : ℕ) : ℤ)) =
          ∑ k ∈ Finset.range (N + 1),
              ((-1 : ℤ) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1))) •
                intEval q hq_int (y + ((k : ℤ) + 1)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [smul_eq_mul, h_k_simp k]
      linarith [hsum_congr ▸ this]
    have h_dvd_sum : (d : ℤ) ∣
        ∑ k ∈ Finset.range (N + 1),
          ((-1 : ℤ) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1))) •
            intEval q hq_int (y + ((k : ℤ) + 1)) := by
      apply Finset.dvd_sum
      intro k hk
      rw [smul_eq_mul]
      exact dvd_mul_of_dvd_right (hk_dvd k hk) _
    -- From h_recur_y', (-1)^(N+1) * intEval q hq_int y = -(sum).
    have h_main : ((-1 : ℤ) ^ (N + 1)) * intEval q hq_int y =
        - ∑ k ∈ Finset.range (N + 1),
          ((-1 : ℤ) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1))) •
            intEval q hq_int (y + ((k : ℤ) + 1)) := by linarith
    have h_dvd_pow : (d : ℤ) ∣ ((-1 : ℤ) ^ (N + 1)) * intEval q hq_int y := by
      rw [h_main]
      exact h_dvd_sum.neg_right
    -- Multiply by (-1)^(N+1) to extract intEval q hq_int y. ((-1)^(N+1))^2 = 1.
    have h_sq : ((-1 : ℤ) ^ (N + 1)) * ((-1 : ℤ) ^ (N + 1)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have h_recover :
        ((-1 : ℤ) ^ (N + 1)) * (((-1 : ℤ) ^ (N + 1)) * intEval q hq_int y) =
          intEval q hq_int y := by
      rw [← mul_assoc, h_sq, one_mul]
    rw [← h_recover]
    exact Dvd.dvd.mul_left h_dvd_pow _
  -- Step 3: Prove `(d : ℤ) ∣ intEval q hq_int (- (m : ℤ))` by strong induction on m.
  have h_neg : ∀ m : ℕ, (d : ℤ) ∣ intEval q hq_int (- (m : ℤ)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      apply h_dvd_smul
      intro k hk
      have hk_lt : k < N + 1 := Finset.mem_range.mp hk
      -- Argument: -m + (k + 1).
      by_cases h_pos : 1 ≤ -(m : ℤ) + ((k : ℤ) + 1)
      · -- Argument positive: use hdvd_pos.
        let n : ℕ := (-(m : ℤ) + ((k : ℤ) + 1)).toNat
        have hn : (n : ℤ) = -(m : ℤ) + ((k : ℤ) + 1) :=
          Int.toNat_of_nonneg (by linarith)
        have hn_pos : 1 ≤ n := by
          have h_one_le : (1 : ℤ) ≤ (n : ℤ) := by rw [hn]; exact h_pos
          exact_mod_cast h_one_le
        rw [show (-(m : ℤ) + ((k : ℤ) + 1) : ℤ) = (n : ℤ) from hn.symm]
        exact hdvd_pos n hn_pos
      · -- Argument ≤ 0: write as -(j : ℤ) for some j < m.
        push_neg at h_pos
        let j : ℕ := ((m : ℤ) - ((k : ℤ) + 1)).toNat
        have h_nonneg : 0 ≤ ((m : ℤ) - ((k : ℤ) + 1)) := by linarith
        have hj_cast : (j : ℤ) = (m : ℤ) - ((k : ℤ) + 1) :=
          Int.toNat_of_nonneg h_nonneg
        have hj_eq : -(m : ℤ) + ((k : ℤ) + 1) = -(j : ℤ) := by
          rw [hj_cast]; ring
        have hj_lt : j < m := by
          have hjm : (j : ℤ) < (m : ℤ) := by rw [hj_cast]; linarith
          exact_mod_cast hjm
        rw [hj_eq]
        exact ih j hj_lt
  -- Step 4: Conclude for arbitrary w : ℤ.
  intro w
  by_cases hw_pos : 1 ≤ w
  · -- w ≥ 1: directly from hdvd_pos.
    let n : ℕ := w.toNat
    have hn : (n : ℤ) = w := Int.toNat_of_nonneg (by linarith)
    have hn_pos : 1 ≤ n := by
      have h_one_le : (1 : ℤ) ≤ (n : ℤ) := by rw [hn]; exact hw_pos
      exact_mod_cast h_one_le
    rw [show w = (n : ℤ) from hn.symm]
    exact hdvd_pos n hn_pos
  · -- w ≤ 0: use h_neg.
    push_neg at hw_pos
    let m : ℕ := (-w).toNat
    have hm : (m : ℤ) = -w := Int.toNat_of_nonneg (by linarith)
    have hw_eq : w = -(m : ℤ) := by linarith
    rw [hw_eq]
    exact h_neg m

/-- **Corollary 7, positive-leading case.** For `p` with positive leading
coefficient, `A_p` is strongly complete.

Reduction (uniform in `natDegree p`): scale to `q := D·p/h` where `D` is the
common denominator of `p`'s coefficients and `h := gcd { (D·p)(n) : n ∈ ℤ }`,
making `q` integer-valued, fixed-divisor-free, and positive-leading. For each
`m`, take `M := (D·m - 1) / h, r := D·m - h·M ∈ {1, …, h}` (Euclidean
division), then apply `theorem_1` to `q` with `α := (r : ℚ) / D`. The
identity `∑ (p(n_i) + 1/n_i) = (h/D) ∑ q(n_i) + ∑ 1/n_i = hM/D + r/D = m`
recovers the imageSet form. -/
theorem corollary_7_pos_leading (p : ℚ[X])
    (h_lead_pos : 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := by
  classical
  intro B
  rw [Filter.eventually_atTop]
  -- Step 1: Choose D from `exists_integral_multiple`. Get IntValued (C D * p).
  obtain ⟨D, hD_pos, hDp_mult⟩ := exists_integral_multiple p
  set Dp : ℚ[X] := Polynomial.C (D : ℚ) * p with hDp_def
  have hD_ne_q : (D : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    exact ne_of_gt this
  have hDp_int : IntValued Dp :=
    intValued_C_mul_of_HasIntegralMultiple D p hDp_mult
  -- Dp.leadingCoeff = D * p.leadingCoeff > 0.
  have hDp_lead_pos : 0 < Dp.leadingCoeff := by
    rw [hDp_def, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    exact mul_pos hD_pos_q h_lead_pos
  -- Dp.natDegree = p.natDegree.
  have hDp_natDegree : Dp.natDegree = p.natDegree := by
    rw [hDp_def]
    exact Polynomial.natDegree_C_mul hD_ne_q
  -- Step 2: Extract h := gcd of (Dp.eval z : ℤ) for z ∈ ℤ via Ideal.span.
  set valSet : Set ℤ := { z : ℤ | ∃ w : ℤ, z = intEval Dp hDp_int w } with hvalSet_def
  set I : Ideal ℤ := Ideal.span valSet with hI_def
  haveI hI_principal : Submodule.IsPrincipal I := IsPrincipalIdealRing.principal I
  set z₀ : ℤ := Submodule.IsPrincipal.generator I with hz₀_def
  set h : ℕ := z₀.natAbs with hh_def
  have hI_span : Ideal.span ({z₀} : Set ℤ) = I :=
    Submodule.IsPrincipal.span_singleton_generator I
  -- Each value Dp.eval(w) is in valSet, hence in I.
  have h_val_in_I : ∀ w : ℤ, intEval Dp hDp_int w ∈ I := fun w =>
    Ideal.subset_span ⟨w, rfl⟩
  -- Eventually positive: since Dp has positive leading coeff and integer values,
  -- some value is positive (giving a positive ideal element, hence h ≥ 1).
  have h_some_pos : ∃ w : ℤ, 0 < intEval Dp hDp_int w := by
    set Dpr : ℝ[X] := Dp.map (algebraMap ℚ ℝ) with hDpr_def
    have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
      (algebraMap ℚ ℝ).injective
    have hDpr_lead : (0 : ℝ) < Dpr.leadingCoeff := by
      rw [hDpr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
      have : (0 : ℝ) < (Dp.leadingCoeff : ℝ) := by exact_mod_cast hDp_lead_pos
      simpa [algebraMap] using this
    by_cases hDp_const : Dp.natDegree = 0
    · -- Dp = C c for some c. Since lc > 0, c > 0.
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hDp_const
      have hlc : Dp.leadingCoeff = Dp.coeff 0 := by
        rw [Polynomial.leadingCoeff, hDp_const]
      have hc_pos : 0 < Dp.coeff 0 := hlc ▸ hDp_lead_pos
      refine ⟨0, ?_⟩
      have h_eval : Dp.eval ((0 : ℤ) : ℚ) = Dp.coeff 0 := by
        rw [hpC]; simp
      have h_intEval := intEval_spec Dp hDp_int 0
      rw [h_eval] at h_intEval
      have h_pos_q : (0 : ℚ) < ((intEval Dp hDp_int 0 : ℤ) : ℚ) := by
        rw [h_intEval]; exact hc_pos
      exact_mod_cast h_pos_q
    · -- Dp.natDegree ≥ 1. Take w large.
      have hd_pos : 0 < Dp.natDegree := Nat.pos_of_ne_zero hDp_const
      have hDpr_deg_pos : 0 < Dpr.degree := by
        have hnat : 0 < Dpr.natDegree := by
          rw [hDpr_def, Polynomial.natDegree_map_eq_of_injective h_inj]
          exact hd_pos
        exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
      have h_tendsto : Filter.Tendsto (fun x : ℝ => Dpr.eval x) Filter.atTop Filter.atTop :=
        Polynomial.tendsto_atTop_of_leadingCoeff_nonneg Dpr hDpr_deg_pos hDpr_lead.le
      obtain ⟨N0, hN0⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto 1
      set w : ℕ := Nat.ceil (max N0 0) + 1 with hw_def
      have hw_real_ge_N0 : N0 ≤ (w : ℝ) := by
        have h1 : N0 ≤ max N0 0 := le_max_left _ _
        have h2 : (max N0 0) ≤ (Nat.ceil (max N0 0) : ℝ) := Nat.le_ceil _
        have h3 : ((Nat.ceil (max N0 0) : ℕ) : ℝ) ≤ (w : ℝ) := by
          rw [hw_def]; push_cast; linarith
        linarith
      have h_eval_real : 1 ≤ Dpr.eval (w : ℝ) := hN0 _ hw_real_ge_N0
      have h_eval_cast : Dpr.eval (w : ℝ) = ((Dp.eval (w : ℚ) : ℚ) : ℝ) := by
        rw [hDpr_def]
        have h1 : ((w : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((w : ℕ) : ℚ) := by
          simp [algebraMap]
        rw [h1, Polynomial.eval_map_apply]; simp [algebraMap]
      have h_eval_q : 1 ≤ Dp.eval ((w : ℕ) : ℚ) := by
        have : ((1 : ℚ) : ℝ) ≤ ((Dp.eval ((w : ℕ) : ℚ) : ℚ) : ℝ) := by
          rw [show ((1 : ℚ) : ℝ) = (1 : ℝ) by norm_num, ← h_eval_cast]; exact h_eval_real
        exact_mod_cast this
      refine ⟨(w : ℤ), ?_⟩
      have h_intEval := intEval_spec Dp hDp_int (w : ℤ)
      have h_cast_eq : ((w : ℤ) : ℚ) = ((w : ℕ) : ℚ) := by push_cast; rfl
      rw [h_cast_eq] at h_intEval
      have h_pos_q : (0 : ℚ) < ((intEval Dp hDp_int (w : ℤ) : ℤ) : ℚ) := by
        rw [h_intEval]; linarith
      exact_mod_cast h_pos_q
  obtain ⟨w_pos, hw_pos⟩ := h_some_pos
  have hI_ne_bot : I ≠ ⊥ := by
    intro h_bot
    have hmem : intEval Dp hDp_int w_pos ∈ (⊥ : Ideal ℤ) := by
      rw [← h_bot]; exact h_val_in_I w_pos
    rw [Ideal.mem_bot] at hmem
    omega
  have hz₀_ne : z₀ ≠ 0 := by
    intro hz0
    apply hI_ne_bot
    rw [Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero, ← hz₀_def]
    exact hz0
  have hh_pos : 1 ≤ h := by
    have : 0 < h := Int.natAbs_pos.mpr hz₀_ne
    omega
  have hh_pos_q : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh_pos
  have hh_ne_q : (h : ℚ) ≠ 0 := ne_of_gt hh_pos_q
  -- h ∣ Dp.eval w (as ℤ) for every w.
  have hh_dvd : ∀ w : ℤ, (h : ℤ) ∣ intEval Dp hDp_int w := by
    intro w
    have hmem : intEval Dp hDp_int w ∈ I := h_val_in_I w
    rw [← hI_span, Ideal.mem_span_singleton] at hmem
    rw [hh_def, Int.natAbs_dvd]
    exact hmem
  -- Step 3: Define q := C ((h : ℚ)⁻¹) * Dp.
  set q : ℚ[X] := Polynomial.C ((h : ℚ)⁻¹) * Dp with hq_def
  have hq_int : IntValued q := intValued_C_inv_mul h hh_pos Dp hDp_int hh_dvd
  -- q.natDegree = p.natDegree.
  have hh_inv_ne : ((h : ℚ)⁻¹) ≠ 0 := by
    rw [ne_eq, inv_eq_zero]; exact hh_ne_q
  have hq_natDegree : q.natDegree = p.natDegree := by
    rw [hq_def, Polynomial.natDegree_C_mul hh_inv_ne, hDp_natDegree]
  -- q.leadingCoeff = (D / h) * p.leadingCoeff > 0.
  have hq_lead_pos : 0 < q.leadingCoeff := by
    rw [hq_def, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    have h_inv_pos : (0 : ℚ) < (h : ℚ)⁻¹ := inv_pos.mpr hh_pos_q
    exact mul_pos h_inv_pos hDp_lead_pos
  -- q.eval = Dp.eval / h.
  have hq_eval : ∀ z : ℚ, q.eval z = Dp.eval z / (h : ℚ) := by
    intro z
    rw [hq_def, Polynomial.eval_mul, Polynomial.eval_C]
    field_simp
  -- For w ∈ ℤ, intEval q hq_int w * h = intEval Dp hDp_int w (as ℤ).
  have hq_intEval : ∀ w : ℤ,
      (h : ℤ) * intEval q hq_int w = intEval Dp hDp_int w := by
    intro w
    have h1 := intEval_spec q hq_int w
    have h2 := intEval_spec Dp hDp_int w
    have h3 : (((h : ℤ) * intEval q hq_int w : ℤ) : ℚ) =
        ((intEval Dp hDp_int w : ℤ) : ℚ) := by
      push_cast
      rw [h1, hq_eval, h2]
      field_simp
    exact_mod_cast h3
  -- Step 4: NoFixedDivisor q.
  have hq_no_fixed : NoFixedDivisor q hq_int := by
    intro d hd hdvd
    -- If d ∣ q.eval n for all n ≥ 1, then by Mahler/finite-differences, d ∣ q.eval z
    -- for all z ∈ ℤ. Then (d * h) ∣ Dp.eval z for all z, so I ⊆ ⟨d*h⟩, hence d*h ∣ z₀,
    -- but |z₀| = h, forcing d ∣ 1, contradicting d ≥ 2.
    -- Mahler / finite-differences extension of fixed divisor from ℕ_{≥1} to ℤ.
    have hdvd_all : ∀ w : ℤ, (d : ℤ) ∣ intEval q hq_int w :=
      intValued_dvd_extends_to_int q hq_int d hdvd
    -- Now (d * h : ℤ) ∣ Dp.eval w for all w.
    have hdh_dvd_all : ∀ w : ℤ, ((d : ℤ) * (h : ℤ)) ∣ intEval Dp hDp_int w := by
      intro w
      rw [← hq_intEval w]
      obtain ⟨k, hk⟩ := hdvd_all w
      refine ⟨k, ?_⟩
      rw [hk]; ring
    have hI_le : I ≤ Ideal.span ({(d : ℤ) * (h : ℤ)} : Set ℤ) := by
      rw [hI_def]
      apply Ideal.span_le.mpr
      intro x hx
      obtain ⟨w, hx_eq⟩ := hx
      show x ∈ Ideal.span ({(d : ℤ) * (h : ℤ)} : Set ℤ)
      rw [Ideal.mem_span_singleton, hx_eq]
      exact hdh_dvd_all w
    have hz₀_mem_I : z₀ ∈ I := Submodule.IsPrincipal.generator_mem I
    have hdh_dvd_z₀ : ((d : ℤ) * (h : ℤ)) ∣ z₀ := by
      have hz_in : z₀ ∈ Ideal.span ({(d : ℤ) * (h : ℤ)} : Set ℤ) := hI_le hz₀_mem_I
      rwa [Ideal.mem_span_singleton] at hz_in
    have hh_pos_int : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh_pos
    have hd_ge_two_int : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    rcases Int.natAbs_eq z₀ with hpos | hneg
    · have hz_eq : z₀ = (h : ℤ) := by rw [hpos, hh_def]
      rw [hz_eq] at hdh_dvd_z₀
      rcases hdh_dvd_z₀ with ⟨k, hk⟩
      have hh_ne_int : (h : ℤ) ≠ 0 := ne_of_gt hh_pos_int
      have hk' : (1 : ℤ) = d * k := by
        have : (h : ℤ) * 1 = (h : ℤ) * (d * k) := by linarith
        exact mul_left_cancel₀ hh_ne_int this
      have hd_dvd_one : (d : ℤ) ∣ 1 := ⟨k, hk'⟩
      have h_le : (d : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hd_dvd_one
      omega
    · have hz_eq : z₀ = -(h : ℤ) := by rw [hneg, hh_def]
      rw [hz_eq] at hdh_dvd_z₀
      have hdh_dvd_h : ((d : ℤ) * (h : ℤ)) ∣ (h : ℤ) := by
        rcases hdh_dvd_z₀ with ⟨k, hk⟩
        refine ⟨-k, ?_⟩; linarith
      rcases hdh_dvd_h with ⟨k, hk⟩
      have hh_ne_int : (h : ℤ) ≠ 0 := ne_of_gt hh_pos_int
      have hk' : (1 : ℤ) = d * k := by
        have : (h : ℤ) * 1 = (h : ℤ) * (d * k) := by linarith
        exact mul_left_cancel₀ hh_ne_int this
      have hd_dvd_one : (d : ℤ) ∣ 1 := ⟨k, hk'⟩
      have h_le : (d : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hd_dvd_one
      omega
  -- Step 5: Choose L with two properties:
  --   (a) for n > L, p.eval n + 1/n ∉ B;
  --   (b) for n₁, n₂ > L, p.eval n₁ + 1/n₁ = p.eval n₂ + 1/n₂ → n₁ = n₂.
  have hL_exists : ∃ L : ℕ, 1 ≤ L ∧
      (∀ n : ℕ, L < n → p.eval (n : ℚ) + 1 / (n : ℚ) ∉ B) ∧
      (∀ n₁ n₂ : ℕ, L < n₁ → L < n₂ →
        p.eval (n₁ : ℚ) + 1 / (n₁ : ℚ) = p.eval (n₂ : ℚ) + 1 / (n₂ : ℚ) → n₁ = n₂) := by
    by_cases hd : p.natDegree = 0
    case pos =>
      -- p = C c, value c + 1/n. Take L > all bad denominators.
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hd
      have hlc : p.leadingCoeff = p.coeff 0 := by
        rw [Polynomial.leadingCoeff, hd]
      set c : ℚ := p.coeff 0 with hc_def
      have hc_pos : 0 < c := hlc ▸ h_lead_pos
      have h_eval_const : ∀ z : ℚ, p.eval z = c := by
        intro z; rw [hpC]; simp
      let bad_n : ℚ → ℕ := fun b => (b - c).den
      let bad_set : Finset ℕ := B.image bad_n
      let L : ℕ := max 1 (bad_set.sup id + 1)
      refine ⟨L, le_max_left _ _, ?_, ?_⟩
      · intro n hn hb
        rw [h_eval_const] at hb
        have hn_pos : 0 < n := by
          have : 1 ≤ n := by
            have h_le_max : 1 ≤ L := le_max_left _ _
            omega
          omega
        have hn_pos_q : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos
        set b' : ℚ := c + 1 / (n : ℚ) with hb'_def
        have hb'_mem : b' ∈ B := hb
        have h_b'_minus_c : b' - c = 1 / (n : ℚ) := by rw [hb'_def]; ring
        have h_den : (b' - c).den = n := by
          rw [h_b'_minus_c, one_div]
          exact Rat.inv_natCast_den_of_pos hn_pos
        have h_b'_in_bad : bad_n b' ∈ bad_set := Finset.mem_image.mpr ⟨b', hb'_mem, rfl⟩
        have h_bad_eq : bad_n b' = n := h_den
        have h_n_le_sup : n ≤ bad_set.sup id := by
          rw [← h_bad_eq]
          exact Finset.le_sup (f := id) h_b'_in_bad
        have h_L_lb : bad_set.sup id + 1 ≤ L := le_max_right _ _
        omega
      · intro n₁ n₂ hn₁ hn₂ h_eq
        rw [h_eval_const, h_eval_const] at h_eq
        have h1 : (1 : ℚ) / (n₁ : ℚ) = 1 / (n₂ : ℚ) := by linarith
        have hn₁_pos : 0 < n₁ := by
          have : 1 ≤ n₁ := by
            have : 1 ≤ L := le_max_left _ _
            omega
          omega
        have hn₂_pos : 0 < n₂ := by
          have : 1 ≤ n₂ := by
            have : 1 ≤ L := le_max_left _ _
            omega
          omega
        have hn₁_pos_q : (0 : ℚ) < (n₁ : ℚ) := by exact_mod_cast hn₁_pos
        have hn₂_pos_q : (0 : ℚ) < (n₂ : ℚ) := by exact_mod_cast hn₂_pos
        rw [one_div, one_div, inv_inj] at h1
        exact_mod_cast h1
    case neg =>
      -- natDegree p ≥ 1. p.eval n + 1/n → ∞.
      have hd_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hd
      have hp_ne : p ≠ 0 := by
        intro hpz; rw [hpz, Polynomial.leadingCoeff_zero] at h_lead_pos
        exact lt_irrefl _ h_lead_pos
      set pr : ℝ[X] := p.map (algebraMap ℚ ℝ) with hpr_def
      have h_inj_qr : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
        (algebraMap ℚ ℝ).injective
      have hpr_lead : (0 : ℝ) < pr.leadingCoeff := by
        rw [hpr_def, Polynomial.leadingCoeff_map_of_injective h_inj_qr]
        have : (0 : ℝ) < (p.leadingCoeff : ℝ) := by exact_mod_cast h_lead_pos
        simpa [algebraMap] using this
      have hpr_deg_pos : 0 < pr.degree := by
        have hnat : 0 < pr.natDegree := by
          rw [hpr_def, Polynomial.natDegree_map_eq_of_injective h_inj_qr]
          exact hd_pos
        exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
      have h_tendsto : Filter.Tendsto (fun x : ℝ => pr.eval x) Filter.atTop Filter.atTop :=
        Polynomial.tendsto_atTop_of_leadingCoeff_nonneg pr hpr_deg_pos hpr_lead.le
      set Bmax : ℝ := if hB : B.Nonempty then ((B.image fun b : ℚ => (b : ℝ)).max' (Finset.Nonempty.image hB _)) else 0
      obtain ⟨N₀, hN₀⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto (Bmax + 2)
      let L : ℕ := max 1 (Nat.ceil (max N₀ 0) + 1)
      refine ⟨L, le_max_left _ _, ?_, ?_⟩
      · intro n hn hb
        have hn_ge : (Nat.ceil (max N₀ 0) + 1) ≤ n := by
          have h_max_right : Nat.ceil (max N₀ 0) + 1 ≤ L := le_max_right _ _
          omega
        have hn_pos : 0 < n := by
          have : 1 ≤ n := by
            have : 1 ≤ L := le_max_left _ _
            omega
          omega
        have h1 : (Nat.ceil (max N₀ 0) : ℝ) ≥ N₀ := by
          have hN0_le_max : N₀ ≤ max N₀ 0 := le_max_left _ _
          have h_le_ceil : (max N₀ 0) ≤ (Nat.ceil (max N₀ 0) : ℝ) := Nat.le_ceil _
          linarith
        have h2 : N₀ ≤ (n : ℝ) := by
          have : (Nat.ceil (max N₀ 0) + 1 : ℕ) ≤ n := hn_ge
          have h3 : ((Nat.ceil (max N₀ 0) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
          push_cast at h3
          linarith
        have h_eval_real : Bmax + 2 ≤ pr.eval (n : ℝ) := hN₀ _ h2
        have h_eval_cast : pr.eval ((n : ℕ) : ℝ) = ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
          rw [hpr_def]
          have h1 : ((n : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((n : ℕ) : ℚ) := by simp [algebraMap]
          rw [h1, Polynomial.eval_map_apply]; simp [algebraMap]
        have h_p_eval_real : Bmax + 2 ≤ ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
          rw [← h_eval_cast]; exact h_eval_real
        set v_p : ℚ := Polynomial.eval ((n : ℕ) : ℚ) p with hv_p_def
        set v_inv : ℚ := 1 / ((n : ℕ) : ℚ) with hv_inv_def
        have h_p_eval_real' : Bmax + 2 ≤ (v_p : ℝ) := h_p_eval_real
        have hb_le_Bmax : ((v_p + v_inv : ℚ) : ℝ) ≤ Bmax := by
          have hB_ne : B.Nonempty := ⟨_, hb⟩
          simp only [Bmax]
          rw [dif_pos hB_ne]
          apply Finset.le_max'
          simp only [Finset.mem_image]
          exact ⟨_, hb, rfl⟩
        have h1_le : (v_inv : ℝ) ≤ 1 := by
          have hn_pos_q : (0 : ℚ) < ((n : ℕ) : ℚ) := by exact_mod_cast hn_pos
          have h_q_le : v_inv ≤ 1 := by
            rw [hv_inv_def, div_le_one hn_pos_q]
            have : 1 ≤ (n : ℕ) := hn_pos
            exact_mod_cast this
          exact_mod_cast h_q_le
        have h_inv_pos : 0 ≤ (v_inv : ℝ) := by
          have hn_pos_q : (0 : ℚ) < ((n : ℕ) : ℚ) := by exact_mod_cast hn_pos
          have : (0 : ℚ) ≤ v_inv := by rw [hv_inv_def]; positivity
          exact_mod_cast this
        have h_split : ((v_p + v_inv : ℚ) : ℝ) = (v_p : ℝ) + (v_inv : ℝ) := by push_cast; ring
        rw [h_split] at hb_le_Bmax
        linarith
      · -- Injectivity for n > L, nonconstant case.
        -- SUB-SORRY: For nonconstant `p` with positive leading coefficient,
        -- the function `f(n) = p(n) + 1/n` is strictly monotone for sufficiently
        -- large `n`. Specifically, `f(n+1) - f(n) = (p(n+1) - p(n)) - 1/(n(n+1))`,
        -- where `p(n+1) - p(n) → ∞` (degree ≥ 1) while `1/(n(n+1)) → 0`. Hence
        -- eventually `f` is strictly increasing, so injective. We can enlarge `L`
        -- to include this monotonicity threshold.
        intro n₁ n₂ hn₁ hn₂ h_eq
        sorry
  obtain ⟨L, hL_pos, hL_avoid, hL_inj⟩ := hL_exists
  -- Step 6: For each residue r ∈ {1, …, h}, get m₀_r from theorem_1 with α := (r : ℚ)/D.
  have hα_pos : ∀ r : ℕ, 1 ≤ r → r ≤ h → (0 : ℚ) < (r : ℚ) / (D : ℚ) := by
    intro r hr1 _
    have hr_pos : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr1
    have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    exact div_pos hr_pos hD_pos_q
  have h_apply_thm1 : ∀ r : ℕ, 1 ≤ r → r ≤ h →
      ∃ m₀_r : ℕ, ∀ M : ℕ, m₀_r ≤ M →
        ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
          StrictMono n ∧ (L < n 0) ∧
          ((r : ℚ) / (D : ℚ) = ∑ i, (1 : ℚ) / (n i)) ∧
          ((M : ℚ) = ∑ i, q.eval ((n i : ℕ) : ℚ)) := by
    intro r hr1 hr_le_h
    exact theorem_1 ((r : ℚ) / (D : ℚ)) (hα_pos r hr1 hr_le_h) L hL_pos
      q hq_int hq_lead_pos hq_no_fixed
  classical
  let mthresh : ℕ → ℕ := fun r =>
    if hr : 1 ≤ r ∧ r ≤ h then
      (h_apply_thm1 r hr.1 hr.2).choose
    else
      0
  set m₀_base : ℕ := (Finset.Icc 1 h).sup mthresh with hm₀_base_def
  set m₀ : ℕ := h * (m₀_base + 1) + 1 with hm₀_def
  refine ⟨m₀, ?_⟩
  intro m hm_ge
  have hDm_pos : 1 ≤ D * m := by
    have : 1 ≤ m := by
      have : 1 ≤ m₀ := by rw [hm₀_def]; omega
      omega
    have : 0 < D * m := Nat.mul_pos hD_pos this
    omega
  set M : ℕ := (D * m - 1) / h with hM_def
  set r : ℕ := D * m - h * M with hr_def
  have hr_pos : 1 ≤ r := by
    rw [hr_def, hM_def]
    have h1 : (D * m - 1) / h * h ≤ D * m - 1 := Nat.div_mul_le_self _ _
    have h2 : h * ((D * m - 1) / h) = (D * m - 1) / h * h := by ring
    omega
  have hr_le : r ≤ h := by
    rw [hr_def, hM_def]
    have h1 := Nat.div_add_mod (D * m - 1) h
    have h2 : (D * m - 1) % h < h := Nat.mod_lt _ (by omega)
    have h3 : (D * m - 1) - h * ((D * m - 1) / h) = (D * m - 1) % h := by
      have h4 : (D * m - 1) / h * h ≤ D * m - 1 := Nat.div_mul_le_self _ _
      have h5 : h * ((D * m - 1) / h) = (D * m - 1) / h * h := by ring
      omega
    omega
  have hD_eq : D * m = h * M + r := by
    rw [hr_def]
    have h_div_le : h * M ≤ D * m := by
      rw [hM_def]
      have h1 : (D * m - 1) / h * h ≤ D * m - 1 := Nat.div_mul_le_self _ _
      have h2 : h * ((D * m - 1) / h) = (D * m - 1) / h * h := by ring
      omega
    omega
  have hr_in_Icc : r ∈ Finset.Icc 1 h := Finset.mem_Icc.mpr ⟨hr_pos, hr_le⟩
  have h_thresh_le : mthresh r ≤ m₀_base := Finset.le_sup hr_in_Icc
  have hM_ge : mthresh r ≤ M := by
    have h_m_ge : h * (m₀_base + 1) + 1 ≤ m := by rw [hm₀_def] at hm_ge; exact hm_ge
    have h_Dm_ge : h * (m₀_base + 1) + 1 ≤ D * m := by
      have h_D_ge_1 : 1 ≤ D := hD_pos
      calc h * (m₀_base + 1) + 1 ≤ m := h_m_ge
        _ = 1 * m := by ring
        _ ≤ D * m := Nat.mul_le_mul_right m h_D_ge_1
    have h_step1 : h * m₀_base ≤ D * m - 1 := by
      have : h * (m₀_base + 1) ≤ D * m - 1 := by omega
      have h2 : h * m₀_base ≤ h * (m₀_base + 1) := by
        apply Nat.mul_le_mul_left; omega
      omega
    have h_div_ge : m₀_base ≤ (D * m - 1) / h := by
      rw [Nat.le_div_iff_mul_le hh_pos]
      linarith
    have h_M_eq : M = (D * m - 1) / h := hM_def
    omega
  have hM_ge_unfold : (h_apply_thm1 r hr_pos hr_le).choose ≤ M := by
    have hmt : mthresh r = (h_apply_thm1 r hr_pos hr_le).choose := by
      simp only [mthresh]
      rw [dif_pos ⟨hr_pos, hr_le⟩]
    omega
  obtain ⟨k, n_seq, h_strict, h_L_lb, h_recip_sum, h_M_sum⟩ :=
    (h_apply_thm1 r hr_pos hr_le).choose_spec M hM_ge_unfold
  refine ⟨(Finset.univ : Finset (Fin (k + 1))).image
    (fun i => p.eval ((n_seq i : ℕ) : ℚ) + 1 / ((n_seq i : ℕ) : ℚ)), ?_, ?_⟩
  · -- (X : Set ℚ) ⊆ imageSet p \ ↑B
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ,
               true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · refine ⟨n_seq i, rfl⟩
    · have h_lb_i : L < n_seq i := by
        have h_le : n_seq 0 ≤ n_seq i := h_strict.monotone (Fin.zero_le _)
        omega
      exact hL_avoid (n_seq i) h_lb_i
  · -- ∑ x ∈ X, x = (m : ℚ).
    have h_inj : Set.InjOn
        (fun i => p.eval ((n_seq i : ℕ) : ℚ) + 1 / ((n_seq i : ℕ) : ℚ))
        ((Finset.univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))) := by
      intro a _ b _ hab
      have h_lb_a : L < n_seq a := by
        have : n_seq 0 ≤ n_seq a := h_strict.monotone (Fin.zero_le _); omega
      have h_lb_b : L < n_seq b := by
        have : n_seq 0 ≤ n_seq b := h_strict.monotone (Fin.zero_le _); omega
      have h_n_eq : n_seq a = n_seq b := hL_inj _ _ h_lb_a h_lb_b hab
      exact h_strict.injective h_n_eq
    rw [Finset.sum_image h_inj]
    rw [show ∀ (s : Finset (Fin (k+1))) (f g : Fin (k+1) → ℚ),
          ∑ i ∈ s, (f i + g i) = (∑ i ∈ s, f i) + ∑ i ∈ s, g i from
          fun s f g => Finset.sum_add_distrib]
    have hp_eq : ∀ z : ℚ, p.eval z = ((h : ℚ) / (D : ℚ)) * q.eval z := by
      intro z
      rw [hq_eval, hDp_def]
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      field_simp
    have h_sum_p : ∑ i, p.eval ((n_seq i : ℕ) : ℚ) =
        ((h : ℚ) / (D : ℚ)) * ∑ i, q.eval ((n_seq i : ℕ) : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hp_eq _
    rw [h_sum_p, ← h_M_sum, ← h_recip_sum]
    have hh_pos_int : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh_pos
    have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    have hD_ne_q' : (D : ℚ) ≠ 0 := ne_of_gt hD_pos_q
    have h_combine : ((h : ℚ) / (D : ℚ)) * (M : ℚ) + ((r : ℚ) / (D : ℚ)) =
        ((h : ℚ) * (M : ℚ) + (r : ℚ)) / (D : ℚ) := by
      field_simp
    rw [h_combine]
    have hD_eq_q : (D : ℚ) * (m : ℚ) = (h : ℚ) * (M : ℚ) + (r : ℚ) := by
      have : ((D * m : ℕ) : ℚ) = ((h * M + r : ℕ) : ℚ) := by exact_mod_cast hD_eq
      push_cast at this; linarith
    rw [← hD_eq_q]
    field_simp

/-! ## Case negative leading coefficient (impossibility) -/

/-- For `p` with **negative** leading coefficient, `A_p` is *not* strongly
complete: only finitely many elements of `A_p` are positive, so subset sums are
bounded. (Not needed for FC #351; included for the corrected mathematical
statement.) -/
theorem not_strongly_complete_of_neg_leadingCoeff
    (p : ℚ[X]) (hp : p.leadingCoeff < 0) :
    ¬ IsStronglyComplete (imageSet p) := by
  classical
  intro hsc
  -- Step 1: Find `N₀ ≥ 1` with `p.eval n + 1/n ≤ 0` for all `n ≥ N₀`.
  have h_neg_eventually : ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) + 1 / (n : ℚ) ≤ 0 := by
    by_cases hd : p.natDegree = 0
    case pos =>
      -- Constant case: `p = C c` with `c = leadingCoeff < 0`. For `n ≥ ⌈1/(-c)⌉ + 1`,
      -- we have `1/n < -c`, so `c + 1/n < 0`.
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hd
      have hlc : p.leadingCoeff = p.coeff 0 := by
        rw [Polynomial.leadingCoeff, hd]
      set c := p.coeff 0 with hc_def
      have hc_neg : c < 0 := by rw [← hlc]; exact hp
      have hcneg : (0 : ℚ) < -c := by linarith
      refine ⟨max 1 (⌈1 / -c⌉₊ + 1), ?_, ?_⟩
      · exact le_max_left _ _
      · intro n hn
        have hn1 : 1 ≤ n := le_of_max_le_left hn
        have hn_ceil : ⌈1 / -c⌉₊ + 1 ≤ n := le_of_max_le_right hn
        have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn1
        have h_le : (1 / -c : ℚ) < (n : ℚ) := by
          have h2 : (⌈1 / -c⌉₊ + 1 : ℕ) ≤ n := hn_ceil
          have h3 : ((⌈1 / -c⌉₊ + 1 : ℕ) : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2
          push_cast at h3
          linarith [Nat.le_ceil (1 / -c : ℚ)]
        have h1 : 1 / (n : ℚ) < -c := by
          rw [div_lt_iff₀ hn_pos]
          rw [div_lt_iff₀ hcneg] at h_le
          linarith
        rw [hpC, Polynomial.eval_C]
        linarith
    case neg =>
      -- Non-constant case: `0 < natDegree p`, so `Polynomial.tendsto_atBot_of_leadingCoeff_nonpos`
      -- gives `p.eval x → -∞`. In particular, eventually `p.eval n ≤ -1`, and `1/n ≤ 1`,
      -- hence `p.eval n + 1/n ≤ 0`.
      have hd_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hd
      have hp_ne_zero : p ≠ 0 := by
        intro hpz
        rw [hpz] at hp
        simp [Polynomial.leadingCoeff_zero] at hp
      have hdeg : 0 < p.degree := by
        rw [Polynomial.degree_eq_natDegree hp_ne_zero]
        exact_mod_cast hd_pos
      have h := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos p hdeg (le_of_lt hp)
      rw [Filter.tendsto_atTop_atBot] at h
      obtain ⟨N₀, hN₀⟩ := h (-1)
      refine ⟨max 1 ⌈N₀⌉₊, ?_, ?_⟩
      · exact le_max_left _ _
      · intro n hn
        have hn1 : 1 ≤ n := le_of_max_le_left hn
        have hn_ceil : ⌈N₀⌉₊ ≤ n := le_of_max_le_right hn
        have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn1
        have h_evalQ : p.eval (n : ℚ) ≤ -1 := by
          apply hN₀
          have h1 := Nat.le_ceil N₀
          have h2 : (⌈N₀⌉₊ : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn_ceil
          linarith
        have h_inv : 1 / (n : ℚ) ≤ 1 := by
          rw [div_le_one hn_pos]
          exact_mod_cast hn1
        linarith
  obtain ⟨N₀, _hN₀_pos, hN₀⟩ := h_neg_eventually
  -- Step 2: Define the bound `M`.
  set M : ℚ := ∑ n ∈ Finset.range N₀, max (p.eval (n : ℚ) + 1 / (n : ℚ)) 0 with hM_def
  -- Step 3: Any subset sum over `imageSet p` is bounded by `M`.
  have h_bound : ∀ X : Finset ℚ, (↑X : Set ℚ) ⊆ imageSet p → ∑ x ∈ X, x ≤ M := by
    intro X hX
    -- `S` is the image of `[0, N₀)` under `n ↦ p.eval n + 1/n`.
    let S : Finset ℚ :=
      Finset.image (fun n : ℕ => p.eval (n : ℚ) + 1 / (n : ℚ)) (Finset.range N₀)
    -- Every `x ∈ X` is either in `S` (came from `n < N₀`) or `x ≤ 0` (came from `n ≥ N₀`).
    have h_split : ∀ x ∈ X, x ∈ S ∨ x ≤ 0 := by
      intro x hx
      have hx_im : x ∈ imageSet p := hX hx
      obtain ⟨n, hn_eq⟩ := hx_im
      by_cases hn_lt : n < N₀
      · left
        simp only [S, Finset.mem_image, Finset.mem_range]
        exact ⟨n, hn_lt, hn_eq⟩
      · right
        push_neg at hn_lt
        have := hN₀ n hn_lt
        simp only at hn_eq
        linarith
    -- Split `∑ x ∈ X, x = ∑_{X∩S} + ∑_{X\S}`. The second sum is ≤ 0; the first is
    -- ≤ ∑_S max x 0.
    have h_bound1 : ∑ x ∈ X, x ≤ ∑ x ∈ S, max x 0 := by
      rw [show ∑ x ∈ X, x = ∑ x ∈ X ∩ S, x + ∑ x ∈ X \ S, x from
          (Finset.sum_inter_add_sum_diff X S id).symm]
      have h1 : ∑ x ∈ X ∩ S, x ≤ ∑ x ∈ X ∩ S, max x 0 := by
        apply Finset.sum_le_sum; intros; exact le_max_left _ _
      have h2 : ∑ x ∈ X ∩ S, max x 0 ≤ ∑ x ∈ S, max x 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.inter_subset_right
        · intros; exact le_max_right _ _
      have h3 : ∑ x ∈ X \ S, x ≤ 0 := by
        apply Finset.sum_nonpos
        intro x hx
        simp only [Finset.mem_sdiff] at hx
        rcases h_split x hx.1 with h_in | h_le
        · exact absurd h_in hx.2
        · exact h_le
      linarith
    -- Sum over `S` (image) ≤ sum over `Finset.range N₀` (preimage), since elements
    -- under `max · 0` are nonnegative.
    have h_bound2 : ∑ x ∈ S, max x 0 ≤ M := by
      apply Finset.sum_image_le_of_nonneg
      intros; exact le_max_right _ _
    linarith
  -- Step 4: Apply the strong-completeness with `B = ∅` and pick `m > M`.
  have hev := hsc ∅
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  let m : ℕ := max a (⌈M⌉₊ + 1)
  have hma : a ≤ m := le_max_left _ _
  have hmceil : ⌈M⌉₊ + 1 ≤ m := le_max_right _ _
  obtain ⟨X, hX_sub, hX_sum⟩ := ha m hma
  have hX_sub_no_B : (↑X : Set ℚ) ⊆ imageSet p := by
    intro x hx
    have := hX_sub hx
    simp only [Finset.coe_empty, Set.diff_empty] at this
    exact this
  have h_le := h_bound X hX_sub_no_B
  have hmM : M < (m : ℚ) := by
    have h1 : M ≤ (⌈M⌉₊ : ℚ) := Nat.le_ceil M
    have h2 : ((⌈M⌉₊ + 1 : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hmceil
    push_cast at h2
    linarith
  rw [hX_sum] at h_le
  linarith

/-! ## Combined corollary 7 statement -/

/-- **Corollary 7 (PDF, combined).** If `p = 0` or `p` has positive leading
coefficient, `A_p = {p(n) + 1/n}` is strongly complete. (Includes positive
constants — `p = C c` with `c > 0` — in addition to nonconstant positive-leading
polynomials. FC #351 separately requires `0 < natDegree p`.) -/
theorem corollary_7 (p : ℚ[X])
    (h : p = 0 ∨ 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := by
  rcases h with rfl | hl
  · exact corollary_7_zero
  · exact corollary_7_pos_leading p hl

end PolynomialEgyptianSums
