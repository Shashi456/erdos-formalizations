/-
Erdős Problems 283 + 351 — §2 main theorem assembly.

`theorem_1`: For `α ∈ ℚ_{>0}`, `L ≥ 1`, and `p ∈ ℚ[x]` integer-valued, with
positive leading coefficient and no fixed divisor on positive integers, all
sufficiently large integers `m` admit an expression `m = ∑ p(n_i)` with
distinct `L < n_1 < ⋯ < n_k` and `∑ 1/n_i = α`.

Sub-results:
  * `main_window_representation` — multiples of `g` in `[M_0, μ N^{2r}]` are
    subset sums of `A(D j)`, by RSG applied to `q := A ∘ Dpoly / g`.
  * `attainable_interval` — every integer in `[B_N + B_* + M_0, B_N + μ N^{2r}]`
    is an attainable p-sum.
  * `B_diff_tendsto` — `(B_{N+1} - B_N) / N^{2r} → λ` (for explicit `λ`).
  * `intervals_overlap_eventually` — consecutive intervals overlap for large `N`.

The RSG input is supplied by the proved `roth_szekeres_graham` wrapper in
`Basic.lean`.
-/

import Erdos.P283.Basic
import Erdos.P283.Egyptian
import Erdos.P283.PolynomialPeriod
import Erdos.P283.Switching
import Erdos.P283.MainSlots
import Erdos.P283.Corrections
import Erdos.P283.Collision

namespace PolynomialEgyptianSums

open Filter Polynomial Finset

/-! ## Construction-data records

The non-constant branch of `theorem_1` constructs auxiliary data in two
phases. Splitting them into records keeps the proof modular and makes the
RSG inputs explicit. -/

/-- **First phase**: choose `J` so that the asymptotic threshold conditions
hold. The key facts are:
  * `1 ≤ J`,
  * `A(D j) > 0` for all `j ≥ J` (positivity past the leading-coefficient
    threshold of `A p`),
  * `1/(P u_J) < α` (the telescoping head leaves room for filler),
  * `L < D J` and `L < τ J` (denominator threshold respected). -/
structure MainChoice (α : ℚ) (L : ℕ) (p : ℚ[X]) (hp : IntValued p) : Type where
  J : ℕ
  hJ_pos : 1 ≤ J
  hA_pos :
    ∀ j : ℕ, J ≤ j →
      0 < intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)
  hleft_small :
    (1 : ℚ) / ((P : ℚ) * (u J : ℚ)) < α
  hD_gt_L : L < D J
  htau_base_gt_L : L < tau J

/-- **Second phase**: extract the gcd `g` of `A(D j)` values for `j ≥ J`,
along with the no-prime-fixed-divisor RSG hypothesis for the quotient
polynomial `qPoly p md.J g`. The `hg_no_prime_fixed_quot` field is the key
RSG bridge: it says that for every prime `ℓ`, some quotient value
`(qPoly p md.J g).eval (t : ℚ) ≠ 0 (mod ℓ)` for `t ≥ 1`. -/
structure MainGCDData
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (md : MainChoice α L p hp) : Type where
  g : ℕ
  hg_pos : 1 ≤ g
  hg_dvd :
    ∀ j : ℕ, md.J ≤ j →
      (g : ℤ) ∣
        intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)
  hg_no_prime_fixed_quot :
    ∀ ℓ : ℕ, ℓ.Prime →
      ∃ t : ℕ, 1 ≤ t ∧ ∃ z : ℤ,
        (z : ℚ) = (qPoly p md.J g).eval (t : ℚ) ∧
        ¬ ((ℓ : ℤ) ∣ z)

/-- Constructor for `MainChoice`: under the standard hypotheses (positive
leading coefficient + nonconstant), there exists `J ≥ 1` satisfying all the
threshold conditions of `MainChoice`. -/
lemma chooseMainChoice (α : ℚ) (hα : 0 < α) (L : ℕ) (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    Nonempty (MainChoice α L p hp) := by
  -- Cast `A p : ℚ[X]` to a real polynomial to apply the asymptotic lemma.
  set Ar : ℝ[X] := (A p).map (algebraMap ℚ ℝ) with hAr_def
  have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
    (algebraMap ℚ ℝ).injective
  have hAr_natDegree : Ar.natDegree = p.natDegree := by
    rw [hAr_def, Polynomial.natDegree_map_eq_of_injective h_inj,
        A_natDegree_eq p h_nonconst h_lead_pos]
  have hAr_lead : (0 : ℝ) < Ar.leadingCoeff := by
    rw [hAr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
    have hpos : (0 : ℚ) < (A p).leadingCoeff := A_leadingCoeff p h_nonconst h_lead_pos
    have : (0 : ℝ) < ((A p).leadingCoeff : ℝ) := by exact_mod_cast hpos
    simpa [algebraMap] using this
  have hAr_deg_pos : 0 < Ar.degree := by
    have hnat : 0 < Ar.natDegree := by
      rw [hAr_natDegree]; exact h_nonconst
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
  -- `Ar.eval` tends to `+∞` at `+∞`.
  have h_tendsto : Filter.Tendsto (fun x : ℝ => Ar.eval x) Filter.atTop Filter.atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg Ar hAr_deg_pos hAr_lead.le
  -- Get a real threshold N₀ : ℝ such that x ≥ N₀ ⇒ Ar.eval x ≥ 1.
  have hN0 : ∃ N0 : ℝ, ∀ x : ℝ, N0 ≤ x → 1 ≤ Ar.eval x :=
    Filter.tendsto_atTop_atTop.mp h_tendsto 1
  obtain ⟨N0, hN0_le⟩ := hN0
  -- We need a natural-number threshold M such that for j ≥ M, (D j : ℝ) ≥ N0.
  -- `D j = (36j+1)(36(j+1)+1) ≥ j`, so M := ⌈N0⌉₊ + 1 works.
  set M_real : ℕ := Nat.ceil (max N0 0) with hM_real_def
  have hM_real_ge : (M_real : ℝ) ≥ N0 := by
    have hN0_le_max : N0 ≤ max N0 0 := le_max_left _ _
    have h_le_ceil : (max N0 0) ≤ (Nat.ceil (max N0 0) : ℝ) := Nat.le_ceil _
    linarith
  -- We also want a lower bound for `1 / (P · u_J) < α`.
  -- u_J = 36J + 1, P = 36, so P · u_J = 36(36J+1) ≥ 36J ≥ J.
  -- We need 1 / (P · u_J) < α, i.e., (P · u_J) · α > 1.
  -- Since P · u_J ≥ J, sufficient that J · α > 1, i.e., J > 1/α.
  set M_alpha : ℕ := Nat.ceil ((1 : ℚ) / α) + 1 with hM_alpha_def
  -- Final J: max of all thresholds, plus extra to ensure all conditions.
  set J : ℕ := max (max M_real M_alpha) (max (L + 1) 1) with hJ_def
  refine ⟨{ J := J, hJ_pos := ?_, hA_pos := ?_, hleft_small := ?_,
            hD_gt_L := ?_, htau_base_gt_L := ?_ }⟩
  · -- 1 ≤ J
    have : 1 ≤ max (L + 1) 1 := le_max_right _ _
    exact le_trans this (le_max_right _ _)
  · -- ∀ j ≥ J, 0 < intEval (A p) (D j : ℤ)
    intro j hj
    -- D j ≥ j ≥ J ≥ M_real, so (D j : ℝ) ≥ N0, so Ar.eval (D j) ≥ 1.
    have hj_ge_M_real : M_real ≤ j := by
      have h1 : M_real ≤ max M_real M_alpha := le_max_left _ _
      have h2 : max M_real M_alpha ≤ J := by
        rw [hJ_def]; exact le_max_left _ _
      omega
    -- D j ≥ j: in fact much bigger, but j is enough.
    have hDj_ge_j : j ≤ D j := by
      unfold D u P
      have h2 : 1 ≤ 36 * (j + 1) + 1 := by omega
      have h3 : j ≤ (36 * j + 1) := by omega
      calc j ≤ 36 * j + 1 := h3
        _ ≤ (36 * j + 1) * (36 * (j + 1) + 1) := Nat.le_mul_of_pos_right _ h2
    have hDj_ge_M_real : M_real ≤ D j := le_trans hj_ge_M_real hDj_ge_j
    have hDj_real_ge_N0 : N0 ≤ ((D j : ℕ) : ℝ) := by
      have : ((M_real : ℕ) : ℝ) ≤ ((D j : ℕ) : ℝ) := by exact_mod_cast hDj_ge_M_real
      linarith
    -- Ar.eval ((D j : ℕ) : ℝ) ≥ 1.
    have h_eval_real : 1 ≤ Ar.eval ((D j : ℕ) : ℝ) := hN0_le _ hDj_real_ge_N0
    -- Convert: Ar.eval ((D j : ℕ) : ℝ) = ((A p).eval ((D j : ℕ) : ℚ) : ℝ).
    have h_eval_cast :
        Ar.eval ((D j : ℕ) : ℝ) = (((A p).eval ((D j : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [hAr_def]
      have h1 : ((D j : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((D j : ℕ) : ℚ) := by
        simp [algebraMap]
      rw [h1, Polynomial.eval_map_apply]
      simp [algebraMap]
    -- So 1 ≤ (A p).eval ((D j : ℕ) : ℚ) (in ℝ, hence ℚ).
    have h_eval_q : 1 ≤ (A p).eval ((D j : ℕ) : ℚ) := by
      have : ((1 : ℚ) : ℝ) ≤ ((((A p).eval ((D j : ℕ) : ℚ)) : ℚ) : ℝ) := by
        rw [show ((1 : ℚ) : ℝ) = (1 : ℝ) by norm_num]
        rw [← h_eval_cast]; exact h_eval_real
      exact_mod_cast this
    -- intEval is positive iff its rational version is.
    have h_intEval_eq :
        ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ) =
          (A p).eval ((D j : ℕ) : ℚ) := by
      rw [intEval_spec]
      push_cast
      rfl
    have h_pos_q : 0 < (A p).eval ((D j : ℕ) : ℚ) := by linarith
    have h_pos_int : (0 : ℚ) < ((intEval (A p) (A_intValued p hp)
        ((D j : ℕ) : ℤ) : ℤ) : ℚ) := by rw [h_intEval_eq]; exact h_pos_q
    exact_mod_cast h_pos_int
  · -- 1 / (P · u_J) < α
    -- Since J ≥ M_alpha = ⌈1/α⌉ + 1 > 1/α, we have α · J > 1, and
    -- P · u_J ≥ u_J ≥ J + 1 > J, so α · P · u_J > 1.
    have hJ_ge_M_alpha : M_alpha ≤ J := by
      have h1 : M_alpha ≤ max M_real M_alpha := le_max_right _ _
      have h2 : max M_real M_alpha ≤ J := by
        rw [hJ_def]; exact le_max_left _ _
      omega
    have hP_ge_one : (1 : ℚ) ≤ (P : ℚ) := by unfold P; norm_num
    have huJ_ge : (J + 1 : ℚ) ≤ (u J : ℚ) := by
      unfold u P; push_cast; linarith
    have huJ_pos : (0 : ℚ) < (u J : ℚ) := by unfold u P; push_cast; positivity
    have hPuJ_pos : (0 : ℚ) < ((P : ℚ) * (u J : ℚ)) := by
      have hP_pos : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
      exact mul_pos hP_pos huJ_pos
    rw [div_lt_iff₀ hPuJ_pos]
    -- J > 1/α (strictly).
    have hJ_alpha_strict : (1 : ℚ) / α < (J : ℚ) := by
      have h_ceil_ge : ((1 : ℚ) / α) ≤ (Nat.ceil ((1 : ℚ) / α) : ℚ) := Nat.le_ceil _
      have hM_alpha_le_J : ((M_alpha : ℕ) : ℚ) ≤ (J : ℚ) := by exact_mod_cast hJ_ge_M_alpha
      rw [hM_alpha_def] at hM_alpha_le_J
      push_cast at hM_alpha_le_J
      linarith
    -- Hence α · J > 1.
    have h_alpha_J : (1 : ℚ) < α * (J : ℚ) := by
      have hα_ne : α ≠ 0 := ne_of_gt hα
      have h_eq : α * (1 / α) = 1 := by field_simp
      nlinarith [hα, hJ_alpha_strict]
    -- P · u_J ≥ J: u_J ≥ J + 1 > J, and P ≥ 1.
    have hJ_le_PuJ : (J : ℚ) ≤ (P : ℚ) * (u J : ℚ) := by
      have hJ_le_uJ : (J : ℚ) ≤ (u J : ℚ) := by linarith
      calc (J : ℚ) ≤ (u J : ℚ) := hJ_le_uJ
        _ = 1 * (u J : ℚ) := by ring
        _ ≤ (P : ℚ) * (u J : ℚ) := mul_le_mul_of_nonneg_right hP_ge_one huJ_pos.le
    have h_step : α * (J : ℚ) ≤ α * ((P : ℚ) * (u J : ℚ)) :=
      mul_le_mul_of_nonneg_left hJ_le_PuJ hα.le
    linarith [h_alpha_J, h_step]
  · -- L < D J
    have hJ_ge_L1 : L + 1 ≤ J := by
      have h1 : L + 1 ≤ max (L + 1) 1 := le_max_left _ _
      have h2 : max (L + 1) 1 ≤ J := by rw [hJ_def]; exact le_max_right _ _
      omega
    -- D J ≥ J ≥ L + 1 > L.
    have hJ_le_DJ : J ≤ D J := by
      unfold D u P
      have h2 : 1 ≤ 36 * (J + 1) + 1 := by omega
      have h3 : J ≤ (36 * J + 1) := by omega
      calc J ≤ 36 * J + 1 := h3
        _ ≤ (36 * J + 1) * (36 * (J + 1) + 1) := Nat.le_mul_of_pos_right _ h2
    omega
  · -- L < tau J
    have hJ_ge_L1 : L + 1 ≤ J := by
      have h1 : L + 1 ≤ max (L + 1) 1 := le_max_left _ _
      have h2 : max (L + 1) 1 ≤ J := by rw [hJ_def]; exact le_max_right _ _
      omega
    -- tau J = P · u (J+1) = 36 · (36(J+1)+1) ≥ J+1 ≥ L+1 > L.
    have hJ_le_tau : J ≤ tau J := by
      unfold tau u P
      -- tau J = 36 · (36(J+1)+1) ≥ 36 · (J+1) ≥ J+1 > J
      have hJ1 : J + 1 ≤ 36 * (J + 1) + 1 := by omega
      calc J ≤ J + 1 := by omega
        _ ≤ 36 * (J + 1) + 1 := hJ1
        _ = 1 * (36 * (J + 1) + 1) := by ring
        _ ≤ 36 * (36 * (J + 1) + 1) := by
            apply Nat.mul_le_mul_right; omega
    omega

set_option linter.unusedVariables false in
/-- Constructor for `MainGCDData`: given a fixed `MainChoice md` (so `J` is
chosen and `A(D j) > 0` for `j ≥ J`), extract the gcd `g` of the integer
values `A(D j) : j ≥ J` (as the natAbs of the generator of
`Ideal.span (mainValueSet p hp md.J)`), prove `1 ≤ g` and divisibility,
and prove the no-prime-fixed-divisor RSG hypothesis for the quotient
values. -/
lemma chooseMainGCDData {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (md : MainChoice α L p hp) :
    Nonempty (MainGCDData p hp md) := by
  classical
  -- The ideal we extract a generator from.
  set I : Ideal ℤ := Ideal.span (mainValueSet p hp md.J) with hI_def
  -- ℤ is a PID, so I is principal.
  haveI hI_principal : Submodule.IsPrincipal I := IsPrincipalIdealRing.principal I
  set z : ℤ := Submodule.IsPrincipal.generator I with hz_def
  set g : ℕ := z.natAbs with hg_def
  -- Span = ⟨z⟩.
  have hI_span : Ideal.span ({z} : Set ℤ) = I :=
    Submodule.IsPrincipal.span_singleton_generator I
  -- The value at j = md.J is in mainValueSet, hence in I, and is positive.
  have hA_J_pos : 0 < intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ) :=
    md.hA_pos md.J (le_refl _)
  have hA_J_in_set :
      intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ)
        ∈ mainValueSet p hp md.J := ⟨md.J, le_refl _, rfl⟩
  have hA_J_in_I :
      intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ) ∈ I :=
    Ideal.subset_span hA_J_in_set
  -- I ≠ ⊥ since it contains a positive integer.
  have hI_ne_bot : I ≠ ⊥ := by
    intro h_bot
    have : intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ) = 0 := by
      have hmem : intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ) ∈ (⊥ : Ideal ℤ) := by
        rw [← h_bot]; exact hA_J_in_I
      simpa [Ideal.mem_bot] using hmem
    omega
  -- Hence z ≠ 0, so g ≥ 1.
  have hz_ne_zero : z ≠ 0 := by
    intro hz0
    apply hI_ne_bot
    rw [Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero, ← hz_def]
    exact hz0
  have hg_pos : 1 ≤ g := by
    have : 0 < g := Int.natAbs_pos.mpr hz_ne_zero
    omega
  -- Divisibility: for j ≥ md.J, intEval (A p) (D j) ∈ I, hence z ∣ it, hence g ∣ it.
  have hg_dvd :
      ∀ j : ℕ, md.J ≤ j →
        (g : ℤ) ∣ intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) := by
    intro j hj
    have hmem : intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) ∈ I :=
      Ideal.subset_span ⟨j, hj, rfl⟩
    rw [← hI_span, Ideal.mem_span_singleton] at hmem
    -- z ∣ value, hence (z.natAbs : ℤ) ∣ value.
    rw [hg_def, Int.natAbs_dvd]
    exact hmem
  -- Step 4: no-prime-fixed-quot. Use that g ∈ I (the generator) is a finite ℤ-combo
  -- of values from mainValueSet. Dividing by g yields 1 = ∑ cᵢ (sᵢ/g), so any prime
  -- dividing every quotient would divide 1 — contradiction.
  have hg_no_prime_fixed_quot :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ t : ℕ, 1 ≤ t ∧ ∃ z' : ℤ,
          (z' : ℚ) = (qPoly p md.J g).eval (t : ℚ) ∧
          ¬ ((ℓ : ℤ) ∣ z') := by
    intro ℓ hℓ
    -- We argue by contradiction: assume ℓ divides every quotient (qPoly).eval(t).
    by_contra h_no
    push_neg at h_no
    -- After negating ∃ t, ∃ z', ..., we get ∀ t ≥ 1, ∀ z', if (z' = ...) then ℓ ∣ z'.
    have hℓ_dvd_quot : ∀ t : ℕ, 1 ≤ t → ∀ z' : ℤ,
        (z' : ℚ) = (qPoly p md.J g).eval (t : ℚ) → (ℓ : ℤ) ∣ z' := h_no
    -- The key idea: derive (ℓ * g : ℤ) ∣ a for every a ∈ mainValueSet,
    -- hence (ℓ * g : ℤ) ∣ z (the principal generator). But z.natAbs = g, so |z| = g,
    -- so ℓ * g ∣ ±g, forcing ℓ ∣ 1, contradiction.
    -- For each j ≥ md.J, ℓ * g ∣ intEval (A p) (D j).
    have hℓg_dvd : ∀ j : ℕ, md.J ≤ j →
        ((ℓ : ℤ) * (g : ℤ)) ∣ intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) := by
      intro j hj
      -- t := j - md.J + 1
      set t : ℕ := j - md.J + 1 with ht_def
      have ht_pos : 1 ≤ t := by omega
      have ht_eq : md.J + t - 1 = j := by omega
      -- Quotient value as integer:
      have hg_dvd_j := hg_dvd j hj
      obtain ⟨q, hq⟩ := hg_dvd_j
      -- (q : ℚ) = (qPoly).eval (t : ℚ)
      have hq_eq_eval : (q : ℚ) = (qPoly p md.J g).eval (t : ℚ) := by
        rw [qPoly_eval_at_succ p hp md.J g t ht_pos, ht_eq]
        rw [hq]
        push_cast
        have hg_ne : (g : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mp hg_pos)
        field_simp
      -- ℓ ∣ q.
      have hℓ_dvd_q : (ℓ : ℤ) ∣ q := hℓ_dvd_quot t ht_pos q hq_eq_eval
      -- So ℓ * g ∣ g * q = intEval (A p) (D j).
      obtain ⟨q', hq'⟩ := hℓ_dvd_q
      refine ⟨q', ?_⟩
      rw [hq, hq']
      ring
    -- Hence I ⊆ ⟨ℓ * g⟩.
    have hI_le : I ≤ Ideal.span ({(ℓ : ℤ) * (g : ℤ)} : Set ℤ) := by
      rw [hI_def]
      apply Ideal.span_le.mpr
      intro x hx
      obtain ⟨j, hj, hx_eq⟩ := hx
      have : x ∈ Ideal.span ({(ℓ : ℤ) * (g : ℤ)} : Set ℤ) := by
        rw [Ideal.mem_span_singleton, hx_eq]
        exact hℓg_dvd j hj
      exact this
    -- z ∈ I ⊆ ⟨ℓ * g⟩, so ℓ * g ∣ z.
    have hz_mem_I : z ∈ I := Submodule.IsPrincipal.generator_mem I
    have hℓg_dvd_z : ((ℓ : ℤ) * (g : ℤ)) ∣ z := by
      have hz_in : z ∈ Ideal.span ({(ℓ : ℤ) * (g : ℤ)} : Set ℤ) := hI_le hz_mem_I
      rwa [Ideal.mem_span_singleton] at hz_in
    -- (g : ℤ) = z.natAbs, so |z| = g, so z = ±g. Hence ℓ * g ∣ ±g, so ℓ ∣ 1.
    have hg_eq_natAbs : (g : ℤ) = z.natAbs := by rw [hg_def]
    -- z = g or z = -g.
    rcases Int.natAbs_eq z with hpos | hneg
    · -- z = z.natAbs = g
      have hz_eq_g : z = (g : ℤ) := by rw [hpos, hg_eq_natAbs]
      rw [hz_eq_g] at hℓg_dvd_z
      -- (ℓ * g : ℤ) ∣ (g : ℤ).
      have hg_pos_int : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hg_pos
      have : (ℓ : ℤ) ∣ 1 := by
        rcases hℓg_dvd_z with ⟨k, hk⟩
        -- (g : ℤ) = ℓ * g * k = g * (ℓ * k), cancel g.
        have hg_ne : (g : ℤ) ≠ 0 := ne_of_gt hg_pos_int
        have hk' : (1 : ℤ) = ℓ * k := by
          have : (g : ℤ) * 1 = (g : ℤ) * (ℓ * k) := by linarith
          exact (mul_left_cancel₀ hg_ne this)
        exact ⟨k, hk'⟩
      -- ℓ prime, so ℓ ≥ 2, so ℓ ∤ 1.
      have hℓ_ge_two : 2 ≤ ℓ := hℓ.two_le
      have h_le : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) this
      have h_ℓ_ge2_int : (2 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ_ge_two
      omega
    · -- z = -z.natAbs = -g
      have hz_eq_neg_g : z = -(g : ℤ) := by rw [hneg, hg_eq_natAbs]
      rw [hz_eq_neg_g] at hℓg_dvd_z
      have hg_pos_int : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hg_pos
      have hℓg_dvd_g : ((ℓ : ℤ) * (g : ℤ)) ∣ (g : ℤ) := by
        rcases hℓg_dvd_z with ⟨k, hk⟩
        refine ⟨-k, ?_⟩
        linarith
      have hℓ_dvd_one : (ℓ : ℤ) ∣ 1 := by
        rcases hℓg_dvd_g with ⟨k, hk⟩
        have hg_ne : (g : ℤ) ≠ 0 := ne_of_gt hg_pos_int
        have hk' : (1 : ℤ) = ℓ * k := by
          have : (g : ℤ) * 1 = (g : ℤ) * (ℓ * k) := by linarith
          exact (mul_left_cancel₀ hg_ne this)
        exact ⟨k, hk'⟩
      have hℓ_ge_two : 2 ≤ ℓ := hℓ.two_le
      have h_le : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hℓ_dvd_one
      have h_ℓ_ge2_int : (2 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ_ge_two
      omega
  exact ⟨{ g := g, hg_pos := hg_pos, hg_dvd := hg_dvd,
           hg_no_prime_fixed_quot := hg_no_prime_fixed_quot }⟩

/-- Helper: `qPoly` takes positive integer values on `n ≥ 1` whenever
`MainChoice` and `MainGCDData` are constructed. Combines `md.hA_pos` (positivity
of `A(D j)`) with `gcd.hg_dvd` (divisibility by `g`) and `qPoly_eval_at_succ`. -/
lemma qPoly_int_pos_on_pos {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (md : MainChoice α L p hp) (gcd : MainGCDData p hp md) :
    ∀ n : ℕ, 1 ≤ n →
      ∃ z : ℤ, 0 < z ∧ (z : ℚ) = (qPoly p md.J gcd.g).eval (n : ℚ) := by
  intro n hn
  -- Set j := md.J + n - 1 so that md.J ≤ j.
  set j : ℕ := md.J + n - 1 with hj_def
  have hjJ : md.J ≤ j := by omega
  -- val := intEval (A p) (D j) is positive.
  set val : ℤ := intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) with hval_def
  have hval_pos : 0 < val := md.hA_pos j hjJ
  -- (gcd.g : ℤ) divides val.
  have hg_dvd_val : (gcd.g : ℤ) ∣ val := gcd.hg_dvd j hjJ
  -- gcd.g is positive (as ℤ).
  have hg_pos_int : (0 : ℤ) < (gcd.g : ℤ) := by exact_mod_cast gcd.hg_pos
  have hg_ne_int : (gcd.g : ℤ) ≠ 0 := ne_of_gt hg_pos_int
  have hg_ne_q : (gcd.g : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp gcd.hg_pos)
  -- Extract z such that val = gcd.g * z.
  obtain ⟨z, hz⟩ := hg_dvd_val
  refine ⟨z, ?_, ?_⟩
  · -- 0 < z. From 0 < val = gcd.g * z and 0 < gcd.g.
    have h1 : 0 < (gcd.g : ℤ) * z := by rw [← hz]; exact hval_pos
    exact Int.pos_of_mul_pos_right h1 hg_pos_int
  · -- (z : ℚ) = (qPoly).eval (n : ℚ).
    -- qPoly_eval_at_succ p hp md.J gcd.g n hn :
    --   (qPoly p md.J gcd.g).eval (n : ℚ) =
    --     ((intEval (A p) (D (md.J + n - 1)) : ℤ) : ℚ) / (gcd.g : ℚ).
    rw [qPoly_eval_at_succ p hp md.J gcd.g n hn]
    -- Now goal: (z : ℚ) = (val : ℚ) / (gcd.g : ℚ), where val = gcd.g * z.
    show (z : ℚ) = ((intEval (A p) (A_intValued p hp)
        ((D (md.J + n - 1) : ℕ) : ℤ) : ℤ) : ℚ) / (gcd.g : ℚ)
    -- Rewrite via val = gcd.g * z.
    have hval_eq : (val : ℚ) = (gcd.g : ℚ) * (z : ℚ) := by
      have : ((val : ℤ) : ℚ) = (((gcd.g : ℤ) * z : ℤ) : ℚ) := by
        rw [hz]
      push_cast at this
      exact this
    -- val on the goal is exactly the intEval expression with j = md.J + n - 1.
    show (z : ℚ) = (val : ℚ) / (gcd.g : ℚ)
    rw [hval_eq]
    field_simp

/-- **Window representation (PDF §2).** Apply Roth–Szekeres–Graham to
`qPoly p md.J gcd.g`. Every sufficiently large integer `X` is a finite subset
sum of `qPoly`-values evaluated at `(i + 1 : ℕ)` for `i : ℕ`. -/
lemma main_window_representation {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (md : MainChoice α L p hp) (gcd : MainGCDData p hp md) :
    ∃ X_q : ℤ, ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ) := by
  exact roth_szekeres_graham (qPoly p md.J gcd.g)
    (qPoly_natDegree_pos p md.J gcd.g gcd.hg_pos h_nonconst h_lead_pos)
    (qPoly_leadingCoeff_pos p md.J gcd.g gcd.hg_pos h_nonconst h_lead_pos)
    (qPoly_int_pos_on_pos p hp md gcd)
    gcd.hg_no_prime_fixed_quot

/-- **Finite-window consequence of RSG.** If the RSG quotient sum for `X` cannot
use any index beyond `N - J` because every such term is already larger than
`X`, then `g · X` is a subset sum of the finite main-window values
`A(D j)`, `J ≤ j ≤ N`.

The eventual asymptotic proof supplies the `h_tail` hypothesis. Keeping it as
an explicit hypothesis isolates the purely algebraic/indexing part of the
main theorem assembly. -/
lemma main_window_finite {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (md : MainChoice α L p hp) (gcd : MainGCDData p hp md)
    (X_q X : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (hX_ge : X_q ≤ X) (N : ℕ) (hJN : md.J ≤ N)
    (h_tail : ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ)) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc md.J N ∧
      ((gcd.g : ℚ) * (X : ℚ)) =
        ∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ) := by
  classical
  obtain ⟨I, hI⟩ := hX_q X hX_ge
  let qv : ℕ → ℚ := fun i => (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ)
  have hqv_nonneg : ∀ i : ℕ, 0 ≤ qv i := by
    intro i
    obtain ⟨z, hz_pos, hz_eq⟩ :=
      qPoly_int_pos_on_pos p hp md gcd (i + 1) (by omega : 1 ≤ i + 1)
    have : (0 : ℚ) < qv i := by
      dsimp [qv]
      rw [← hz_eq]
      exact_mod_cast hz_pos
    exact this.le
  have hI_bound : ∀ i ∈ I, i ≤ N - md.J := by
    intro i hi
    by_contra hle
    have hlt : N - md.J < i := Nat.lt_of_not_ge hle
    have htail_i := h_tail i hlt
    have hqi_le_sum : qv i ≤ ∑ k ∈ I, qv k :=
      Finset.single_le_sum (fun k _ => hqv_nonneg k) hi
    have hsum_eq : ∑ k ∈ I, qv k = (X : ℚ) := by
      dsimp [qv]
      exact hI.symm
    change (X : ℚ) < qv i at htail_i
    linarith
  let S : Finset ℕ := I.image (fun i => md.J + i)
  refine ⟨S, ?_, ?_⟩
  · intro j hj
    simp only [S, Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact Finset.mem_Icc.mpr ⟨by omega, by
      have hi_bound := hI_bound i hi
      omega⟩
  · have hg_ne_q : (gcd.g : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp gcd.hg_pos)
    have hterm : ∀ i ∈ I,
        (gcd.g : ℚ) * qv i =
          ((intEval (A p) (A_intValued p hp) ((D (md.J + i) : ℕ) : ℤ) : ℤ) : ℚ) := by
      intro i _
      dsimp [qv]
      rw [qPoly_eval_at_succ p hp md.J gcd.g (i + 1) (by omega : 1 ≤ i + 1)]
      have hidx : md.J + (i + 1) - 1 = md.J + i := by omega
      rw [hidx]
      field_simp
    calc
      ((gcd.g : ℚ) * (X : ℚ))
          = (gcd.g : ℚ) * ∑ i ∈ I, qv i := by
              rw [hI]
      _ = ∑ i ∈ I,
            ((intEval (A p) (A_intValued p hp) ((D (md.J + i) : ℕ) : ℤ) : ℚ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm i hi
      _ = ∑ j ∈ I.image (fun i => md.J + i),
            ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℚ)) := by
              rw [Finset.sum_image]
              intro a _ b _ hab
              exact Nat.add_left_cancel hab
      _ = ∑ j ∈ S,
            ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℚ)) := rfl

/-! ### Construction-data records: corrections and fillers

These records package the correction-slot and filler-denominator data for
the non-constant branch of `theorem_1`. Together with `MainChoice` and
`MainGCDData` (above), they form the four structural pieces needed for the
final assembly. -/

/-- Correction-slot data: for each `gcd : MainGCDData md`, choose finite
correction denominators `c_ν` with patterns `G_ν` and switch increments
`b_ν := Q_{G_ν}(c_ν)` such that:
  * Each `c_ν > L`, distinct, collision-free with main slots.
  * The integer values `b_ν` cover all residues mod `gcd.g` as subset sums.
  * The reciprocal sum ∑_ν 1/c_ν is small (less than α/2).
  * Each `b_ν > 0`. -/
structure CorrectionData {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) : Type where
  t : ℕ
  G : Fin t → Finset ℕ
  c : Fin t → ℕ
  hG : ∀ ν, IsEgyptianPattern (G ν)
  b : Fin t → ℤ
  hb_def : ∀ ν, b ν =
    intEval (switchingPoly p (G ν))
      (switchingPoly_intValued p hp (G ν)) ((c ν : ℕ) : ℤ)
  hb_pos : ∀ ν, 0 < b ν
  c_gt_L : ∀ ν, L < c ν
  C0_lt :
    (∑ ν : Fin t, (1 : ℚ) / (c ν : ℚ)) <
      α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ))
  residue_cover :
    ∀ r : ZMod gcd.g,
      ∃ T : Finset (Fin t), r = ∑ ν ∈ T, ((b ν : ℤ) : ZMod gcd.g)
  no_corr_collision :
    ∀ ν μ, ν ≠ μ →
      ∀ e ∈ insert 1 (G ν), ∀ e' ∈ insert 1 (G μ),
        e * c ν ≠ e' * c μ
  no_main_collision :
    ∀ ν j, md.J ≤ j →
      ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ), ∀ e ∈ insert 1 (G ν),
        e * c ν ≠ h * D j

/-- Finite residue-generator data extracted from Lemma 6 before choosing the
actual large correction denominators. Duplicating each generator `g - 1` times
already gives subset sums for every residue modulo `g`. -/
structure CorrectionResidueData {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) : Type where
  w : ℕ
  G : Fin w → Finset ℕ
  a : Fin w → ℕ
  b : Fin w → ℤ
  hG : ∀ i, IsEgyptianPattern (G i)
  ha_pos : ∀ i, 1 ≤ a i
  hb_def : ∀ i, b i =
    (∑ e ∈ G i, intEval p hp (((e * a i : ℕ) : ℕ) : ℤ)) -
      intEval p hp ((a i : ℕ) : ℤ)
  residue_cover :
    ∀ r : ZMod gcd.g,
      ∃ T : Finset (Fin w × Fin (gcd.g - 1)),
        r = ∑ σ ∈ T, ((b σ.1 : ℤ) : ZMod gcd.g)

/-- Extract finite switching-value generators and duplicate them enough times
to cover every residue class modulo `g`. This is the residue-combinatorial
front half of the `g ≥ 2` correction-slot constructor. -/
lemma chooseCorrectionResidueData
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : NoFixedDivisor p hp) :
    Nonempty (CorrectionResidueData p hp gcd) := by
  classical
  obtain ⟨w, G, a, b, hG, ha, hb, hgen⟩ :=
    finite_switch_values_generate_zmod p hp h_nonconst h_lead_pos
      h_no_fixed_div gcd.g gcd.hg_pos
  refine ⟨{
    w := w
    G := G
    a := a
    b := b
    hG := hG
    ha_pos := ha
    hb_def := hb
    residue_cover := ?_
  }⟩
  exact duplicated_generators_subset_sum_all_residues gcd.hg_pos
    (fun i : Fin w => ((b i : ℤ) : ZMod gcd.g)) hgen

/-- Trivial CorrectionData when `gcd.g = 1`: take `t := 0` (no correction slots).
All `Fin 0` quantifiers are vacuously true; the residue cover is automatic
because `ZMod 1` is a subsingleton. -/
lemma chooseCorrectionData_g_eq_one
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (hg1 : gcd.g = 1) :
    Nonempty (CorrectionData p hp gcd) := by
  refine ⟨{
    t := 0
    G := Fin.elim0
    c := Fin.elim0
    hG := fun ν => ν.elim0
    b := Fin.elim0
    hb_def := fun ν => ν.elim0
    hb_pos := fun ν => ν.elim0
    c_gt_L := fun ν => ν.elim0
    C0_lt := ?_
    residue_cover := ?_
    no_corr_collision := ?_
    no_main_collision := ?_
  }⟩
  · -- Sum over Fin 0 is 0; positive residual gap from `md.hleft_small`.
    simp
    have h := md.hleft_small
    rw [one_div, mul_inv] at h
    linarith
  · -- ZMod 1: every element is 0; pick T := ∅.
    intro r
    refine ⟨∅, ?_⟩
    have hsub : Subsingleton (ZMod gcd.g) := by
      rw [hg1]; infer_instance
    have hzero : (∑ ν ∈ (∅ : Finset (Fin 0)), ((Fin.elim0 ν : ℤ) : ZMod gcd.g)) = 0 := by
      simp
    rw [hzero]
    exact Subsingleton.elim r 0
  · intro ν _ _ _ _ _ _; exact ν.elim0
  · intro ν _ _ _ _ _ _; exact ν.elim0

lemma exists_correction_slot_congruent
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (Gν : Finset ℕ) (hGν : IsEgyptianPattern Gν)
    (aσ lower : ℕ) (forbiddenFinite : Finset ℕ) :
    ∃ c : ℕ,
      lower < c ∧ L < c ∧
      0 < intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((c : ℕ) : ℤ) ∧
      ((intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((c : ℕ) : ℤ) : ℤ) : ZMod gcd.g) =
        ((intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((aσ : ℕ) : ℤ) : ℤ) : ZMod gcd.g) ∧
      (∀ e ∈ insert 1 Gν, e * c ∉ forbiddenFinite) ∧
      (∀ j, md.J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ insert 1 Gν, e * c ≠ h * D j) := by
  classical
  set Q : ℚ[X] := switchingPoly p Gν with hQ_def
  set hQint : IntValued Q := switchingPoly_intValued p hp Gν with hQint_def
  obtain ⟨B, hBpos, hBint⟩ := exists_integral_multiple Q
  set Tg : ℕ := gcd.g * B with hTg_def
  have hTg : 1 ≤ Tg := by
    rw [hTg_def]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Nat.one_le_iff_ne_zero.mp gcd.hg_pos)
        (Nat.one_le_iff_ne_zero.mp hBpos))
  have hQpos : 0 < (switchingPoly p Gν).leadingCoeff :=
    switchingPoly_leadingCoeff p Gν hGν h_lead_pos h_nonconst
  obtain ⟨c, hc_mod, hc_lower, hc_L, hc_pos, hc_fin, hc_main⟩ :=
    exists_large_correction_denominator p hp Tg aσ md.J L lower Gν hGν hQpos
      forbiddenFinite hTg
  have hxy : ((c : ℕ) : ℤ) ≡ ((aσ : ℕ) : ℤ)
      [ZMOD (((gcd.g * B : ℕ) : ℕ) : ℤ)] := by
    have hnat : c ≡ aσ [MOD gcd.g * B] := by
      simpa [hTg_def] using hc_mod
    exact Int.natCast_modEq_iff.mpr hnat
  have hper := polynomial_periodicity Q hQint B hBpos hBint gcd.g gcd.hg_pos
    ((c : ℕ) : ℤ) ((aσ : ℕ) : ℤ) hxy
  have hres :
      ((intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((c : ℕ) : ℤ) : ℤ) : ZMod gcd.g) =
        ((intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((aσ : ℕ) : ℤ) : ℤ) : ZMod gcd.g) := by
    exact (ZMod.intCast_eq_intCast_iff _ _ gcd.g).mpr (by
      simpa [Q, hQint, hQ_def, hQint_def] using hper)
  exact ⟨c, hc_lower, hc_L, hc_pos, hres, hc_fin, hc_main⟩

lemma exists_correction_slot_for_generator
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (Gσ : Finset ℕ) (hGσ : IsEgyptianPattern Gσ) (aσ : ℕ) (bσ : ℤ)
    (hbσ : bσ =
      (∑ e ∈ Gσ, intEval p hp (((e * aσ : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((aσ : ℕ) : ℤ))
    (lower : ℕ) (forbiddenFinite : Finset ℕ) :
    ∃ c : ℕ, ∃ b : ℤ,
      b = intEval (switchingPoly p Gσ) (switchingPoly_intValued p hp Gσ)
            ((c : ℕ) : ℤ) ∧
      0 < b ∧ lower < c ∧ L < c ∧
      ((b : ℤ) : ZMod gcd.g) = ((bσ : ℤ) : ZMod gcd.g) ∧
      (∀ e ∈ insert 1 Gσ, e * c ∉ forbiddenFinite) ∧
      (∀ j, md.J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ insert 1 Gσ, e * c ≠ h * D j) := by
  obtain ⟨c, hc_lower, hc_L, hc_pos, hc_res, hc_fin, hc_main⟩ :=
    exists_correction_slot_congruent p hp gcd h_nonconst h_lead_pos Gσ hGσ
      aσ lower forbiddenFinite
  let b : ℤ := intEval (switchingPoly p Gσ) (switchingPoly_intValued p hp Gσ)
    ((c : ℕ) : ℤ)
  refine ⟨c, b, rfl, hc_pos, hc_lower, hc_L, ?_, hc_fin, hc_main⟩
  have ha_eq :
      intEval (switchingPoly p Gσ) (switchingPoly_intValued p hp Gσ)
        ((aσ : ℕ) : ℤ) = bσ := by
    rw [hbσ]
    exact intEval_switchingPoly_nat p hp Gσ aσ
  simpa [b, ha_eq] using hc_res

/-- Sequentially choose a finite family of correction slots, each avoiding all
previous correction multiples and every main-slot multiple. This is the
collision-avoidance core of the `g ≥ 2` `CorrectionData` constructor. -/
lemma exists_ordered_correction_slots
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (t : ℕ) (G : Fin t → Finset ℕ) (hG : ∀ ν, IsEgyptianPattern (G ν))
    (a : Fin t → ℕ) (b₀ : Fin t → ℤ)
    (hb₀ : ∀ ν, b₀ ν =
      (∑ e ∈ G ν, intEval p hp (((e * a ν : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((a ν : ℕ) : ℤ))
    (lower : ℕ) :
    ∃ c : Fin t → ℕ, ∃ b : Fin t → ℤ,
      (∀ ν, b ν =
        intEval (switchingPoly p (G ν)) (switchingPoly_intValued p hp (G ν))
          ((c ν : ℕ) : ℤ)) ∧
      (∀ ν, 0 < b ν) ∧
      (∀ ν, lower < c ν) ∧
      (∀ ν, L < c ν) ∧
      (∀ ν, ((b ν : ℤ) : ZMod gcd.g) = ((b₀ ν : ℤ) : ZMod gcd.g)) ∧
      (∀ ν μ, ν ≠ μ →
        ∀ e ∈ insert 1 (G ν), ∀ e' ∈ insert 1 (G μ),
          e * c ν ≠ e' * c μ) ∧
      (∀ ν j, md.J ≤ j →
        ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ), ∀ e ∈ insert 1 (G ν),
          e * c ν ≠ h * D j) := by
  classical
  induction t with
  | zero =>
      refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
  | succ n ih =>
      let G_old : Fin n → Finset ℕ := fun ν => G ν.castSucc
      let a_old : Fin n → ℕ := fun ν => a ν.castSucc
      let b_old_target : Fin n → ℤ := fun ν => b₀ ν.castSucc
      have hG_old : ∀ ν, IsEgyptianPattern (G_old ν) := fun ν => hG ν.castSucc
      have hb_old_target : ∀ ν, b_old_target ν =
          (∑ e ∈ G_old ν, intEval p hp (((e * a_old ν : ℕ) : ℕ) : ℤ)) -
            intEval p hp ((a_old ν : ℕ) : ℤ) := by
        intro ν
        exact hb₀ ν.castSucc
      obtain ⟨c_old, b_old, hb_def_old, hb_pos_old, hc_lower_old, hc_L_old,
        hb_res_old, hcorr_old, hmain_old⟩ :=
        ih G_old hG_old a_old b_old_target hb_old_target
      let forbiddenFinite : Finset ℕ :=
        (Finset.univ : Finset (Fin n)).biUnion fun ν =>
          (insert 1 (G ν.castSucc)).image fun e => e * c_old ν
      obtain ⟨c_last, b_last, hb_last_def, hb_last_pos, hc_last_lower, hc_last_L,
        hb_last_res, hlast_finite, hlast_main⟩ :=
        exists_correction_slot_for_generator p hp gcd h_nonconst h_lead_pos
          (G (Fin.last n)) (hG (Fin.last n)) (a (Fin.last n)) (b₀ (Fin.last n))
          (hb₀ (Fin.last n)) lower forbiddenFinite
      let c : Fin (n + 1) → ℕ := Fin.snoc c_old c_last
      let b : Fin (n + 1) → ℤ := Fin.snoc b_old b_last
      refine ⟨c, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simp [c, b, hb_last_def]
        · simp [c, b, G_old, hb_def_old ν]
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simpa [b] using hb_last_pos
        · simpa [b] using hb_pos_old ν
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simpa [c] using hc_last_lower
        · simpa [c] using hc_lower_old ν
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simpa [c] using hc_last_L
        · simpa [c] using hc_L_old ν
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simpa [b] using hb_last_res
        · simpa [b, b_old_target] using hb_res_old ν
      · intro ν μ
        refine Fin.lastCases ?_ (fun ν' => ?_) ν
        · refine Fin.lastCases ?_ (fun μ' => ?_) μ
          · intro hne e he e' he' h_eq
            exact (hne rfl).elim
          · intro hne e he e' he' h_eq
            simp [c] at h_eq
            have hmem : e' * c_old μ' ∈ forbiddenFinite := by
              dsimp [forbiddenFinite]
              refine Finset.mem_biUnion.mpr ⟨μ', Finset.mem_univ μ', ?_⟩
              exact Finset.mem_image.mpr ⟨e', he', rfl⟩
            exact hlast_finite e he (by rwa [h_eq])
        · refine Fin.lastCases ?_ (fun μ' => ?_) μ
          · intro hne e he e' he' h_eq
            simp [c] at h_eq
            have hmem : e * c_old ν' ∈ forbiddenFinite := by
              dsimp [forbiddenFinite]
              refine Finset.mem_biUnion.mpr ⟨ν', Finset.mem_univ ν', ?_⟩
              exact Finset.mem_image.mpr ⟨e, he, rfl⟩
            exact hlast_finite e' he' (by rwa [← h_eq])
          · intro hne e he e' he' h_eq
            simp [c] at h_eq
            have hne_old : ν' ≠ μ' := by
              intro h
              apply hne
              simp [h]
            exact hcorr_old ν' μ' hne_old e he e' he' h_eq
      · intro ν j hj h hh
        refine Fin.lastCases ?_ (fun ν' => ?_) ν
        · intro e he
          simpa [c] using hlast_main j hj h hh e he
        · intro e he
          simpa [c, G_old] using hmain_old ν' j hj h hh e he

lemma exists_recip_sum_lt_of_large (t : ℕ) {η : ℚ} (hη : 0 < η) :
    ∃ lower : ℕ, ∀ c : Fin t → ℕ,
      (∀ ν, lower < c ν) →
      (∑ ν : Fin t, (1 : ℚ) / (c ν : ℚ)) < η := by
  classical
  let K : ℕ := Nat.ceil ((t : ℚ) / η) + 1
  refine ⟨K, ?_⟩
  intro c hc
  have hK_pos_nat : 0 < K := by
    dsimp [K]
    omega
  have hK_pos : (0 : ℚ) < (K : ℚ) := by exact_mod_cast hK_pos_nat
  have hK_gt : (t : ℚ) / η < (K : ℚ) := by
    have hle : (t : ℚ) / η ≤ (Nat.ceil ((t : ℚ) / η) : ℚ) :=
      Nat.le_ceil _
    have hlt : (Nat.ceil ((t : ℚ) / η) : ℚ) < (K : ℚ) := by
      dsimp [K]
      exact_mod_cast Nat.lt_succ_self (Nat.ceil ((t : ℚ) / η))
    exact lt_of_le_of_lt hle hlt
  have ht_div_K_lt : (t : ℚ) / (K : ℚ) < η := by
    have ht_lt : (t : ℚ) < (K : ℚ) * η := (div_lt_iff₀ hη).mp hK_gt
    rw [div_lt_iff₀ hK_pos]
    nlinarith [ht_lt]
  have hsum_le :
      (∑ ν : Fin t, (1 : ℚ) / (c ν : ℚ)) ≤
        ∑ _ν : Fin t, (1 : ℚ) / (K : ℚ) := by
    apply Finset.sum_le_sum
    intro ν _
    have hK_le_c_nat : K ≤ c ν := le_of_lt (hc ν)
    have hK_le_c : (K : ℚ) ≤ (c ν : ℚ) := by exact_mod_cast hK_le_c_nat
    exact one_div_le_one_div_of_le hK_pos hK_le_c
  have hconst :
      (∑ _ν : Fin t, (1 : ℚ) / (K : ℚ)) = (t : ℚ) / (K : ℚ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  exact lt_of_le_of_lt (by simpa [hconst] using hsum_le) ht_div_K_lt

lemma chooseCorrectionData_g_ge_two
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : NoFixedDivisor p hp) (_hg2 : 2 ≤ gcd.g) :
    Nonempty (CorrectionData p hp gcd) := by
  classical
  obtain ⟨rd⟩ :=
    chooseCorrectionResidueData p hp gcd h_nonconst h_lead_pos h_no_fixed_div
  let ι : Type := Fin rd.w × Fin (gcd.g - 1)
  let t : ℕ := Fintype.card ι
  let enc : ι ≃ Fin t := Fintype.equivFin ι
  let dec : Fin t → ι := enc.symm
  let G : Fin t → Finset ℕ := fun ν => rd.G ((dec ν).1)
  let a : Fin t → ℕ := fun ν => rd.a ((dec ν).1)
  let b₀ : Fin t → ℤ := fun ν => rd.b ((dec ν).1)
  have hG : ∀ ν, IsEgyptianPattern (G ν) := by
    intro ν
    exact rd.hG ((dec ν).1)
  have hb₀ : ∀ ν, b₀ ν =
      (∑ e ∈ G ν, intEval p hp (((e * a ν : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((a ν : ℕ) : ℤ) := by
    intro ν
    exact rd.hb_def ((dec ν).1)
  set η : ℚ := α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    linarith [md.hleft_small]
  obtain ⟨lower, hlower⟩ := exists_recip_sum_lt_of_large t hη_pos
  obtain ⟨c, b, hb_def, hb_pos, hc_lower, hc_L, hb_res, hcorr, hmain⟩ :=
    exists_ordered_correction_slots p hp gcd h_nonconst h_lead_pos
      t G hG a b₀ hb₀ lower
  refine ⟨{
    t := t
    G := G
    c := c
    hG := hG
    b := b
    hb_def := hb_def
    hb_pos := hb_pos
    c_gt_L := hc_L
    C0_lt := ?_
    residue_cover := ?_
    no_corr_collision := hcorr
    no_main_collision := hmain
  }⟩
  · rw [hη_def] at hlower
    exact hlower c hc_lower
  · intro r
    obtain ⟨T, hT⟩ := rd.residue_cover r
    refine ⟨T.image enc, ?_⟩
    rw [Finset.sum_image]
    · rw [hT]
      apply Finset.sum_congr rfl
      intro σ _
      have hres := hb_res (enc σ)
      simpa [b₀, dec, enc] using hres.symm
    · intro σ _ τ _ hστ
      exact enc.injective hστ

/-- Filler-denominator data: a finite set `F` of natural numbers and a scaling
factor `Λ` (with `8 ∣ Λ`, `Λ > L`, `Λ` larger than all correction denominators)
such that `∑_{f ∈ F} 1/(Λ f) = R₀` for the residual reciprocal mass
`R₀ := α - 1/(P u_J) - C₀`. -/
structure FillerData {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) : Type where
  Λ : ℕ
  hΛ_div_8 : 8 ∣ Λ
  hΛ_gt_L : L < Λ
  hΛ_gt_corr : ∀ ν : Fin corr.t, corr.c ν < Λ
  F : Finset ℕ
  hF_pos : ∀ f ∈ F, 1 ≤ f
  hF_distinct_from_main_corr :
    -- Each Λ * f differs from any main slot multiple or correction-slot multiple
    (∀ f ∈ F, ∀ j, md.J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
      Λ * f ≠ h * D j) ∧
    (∀ f ∈ F, ∀ ν : Fin corr.t, ∀ e ∈ insert 1 (corr.G ν),
      Λ * f ≠ e * corr.c ν)
  hF_recip :
    (∑ f ∈ F, (1 : ℚ) / ((Λ * f : ℕ) : ℚ)) =
      α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) -
      (∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ))

/-- Constructor for FillerData via `egyptian_expansion`. The construction:
choose `Λ` large enough (multiple of 8, exceeding `L` and all `c_ν`, plus
collision-avoidance margins). Then apply `egyptian_expansion` to the residual
mass `Λ * R₀` to get an Egyptian set of denominators of the form `Λ * f`. -/
lemma chooseFillerData
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) :
    Nonempty (FillerData p hp corr) := by
  -- Step 1: Compute residual mass R₀ in ℚ.
  set R0 : ℚ := α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) -
    (∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ)) with hR0_def
  -- R₀ > 0 from corr.C0_lt.
  have hR0_pos : 0 < R0 := by rw [hR0_def]; linarith [corr.C0_lt]
  -- Step 2: Pick Λ as a multiple of 8 large enough.
  -- We need: 8 ∣ Λ, Λ > L, and Λ larger than every correction denominator
  -- after every possible pattern multiplier.
  set corrMax : ℕ := (Finset.univ : Finset (Fin corr.t)).sup
    (fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν)) with hcorrMax_def
  set Λ : ℕ := 8 * (L + corrMax + 2) with hΛ_def
  have hΛ_div_8 : 8 ∣ Λ := by rw [hΛ_def]; exact ⟨_, rfl⟩
  have hΛ_pos : 1 ≤ Λ := by rw [hΛ_def]; omega
  have hΛ_gt_L : L < Λ := by rw [hΛ_def]; omega
  have hΛ_gt_corr : ∀ ν : Fin corr.t, corr.c ν < Λ := by
    intro ν
    have h_inner : corr.c ν ≤ (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) := by
      have h := Finset.le_sup (f := fun e => e * corr.c ν)
        (Finset.mem_insert_self 1 (corr.G ν))
      simp only [one_mul] at h; exact h
    have h_outer : (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) ≤ corrMax := by
      rw [hcorrMax_def]
      exact Finset.le_sup (f := fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν))
        (Finset.mem_univ ν)
    have h_le : corr.c ν ≤ corrMax := le_trans h_inner h_outer
    rw [hΛ_def]; omega
  -- Step 3: Apply egyptian_expansion to R₀ at threshold 0.
  -- We get K : ℕ such that for all k ≥ K, ∃ E with |E| = k, ∀ e ∈ E, 0 < e,
  -- and R₀ = ∑ 1/e.
  obtain ⟨K, hK⟩ := egyptian_expansion R0 hR0_pos 0
  obtain ⟨E_full, _hE_card, hE_lb, hE_sum⟩ := hK K (le_refl K)
  -- Each e ∈ E_full satisfies 0 < e ⇒ e ≥ 1.
  have hE_pos : ∀ e ∈ E_full, 1 ≤ e := fun e he => Nat.one_le_iff_ne_zero.mpr
    (fun h0 => by have := hE_lb e he; omega)
  -- Step 4: Define F such that for each e ∈ E_full, the denominator is Λ * f
  -- where f := e (just rename). But we need 1/(Λ*f) = R₀, which would require
  -- Λ * f = e for ∑ 1/e. We don't have that directly. Instead:
  -- ∑ 1/e = R₀ ⇒ Λ * ∑ 1/e = Λ * R₀, but we need ∑ 1/(Λ*f) = R₀.
  -- This requires f := e/Λ, i.e., Λ ∣ e.
  -- So we instead apply egyptian_expansion to R₀ with denominators ≥ Λ,
  -- then set f := e/Λ. But the reciprocal sum identity wants
  -- ∑ 1/(Λ*f) = R₀ ⇒ (1/Λ) ∑ 1/f = R₀, so ∑ 1/f = Λ R₀.
  -- Apply egyptian_expansion to (Λ R₀) instead, with threshold 0:
  obtain ⟨K', hK'⟩ := egyptian_expansion ((Λ : ℚ) * R0)
    (by have hΛ_q : (0 : ℚ) < (Λ : ℚ) := by exact_mod_cast hΛ_pos
        exact mul_pos hΛ_q hR0_pos) 0
  obtain ⟨F0, _hF0_card, hF0_lb, hF0_sum⟩ := hK' K' (le_refl K')
  have hF0_pos : ∀ f ∈ F0, 1 ≤ f := fun f hf => Nat.one_le_iff_ne_zero.mpr
    (fun h0 => by have := hF0_lb f hf; omega)
  -- Now F := F0; verify ∑_{f ∈ F0} 1/(Λ*f) = R₀.
  have hΛ_q_ne : (Λ : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (Λ : ℚ) := by exact_mod_cast hΛ_pos
    exact ne_of_gt this
  have h_recip : (∑ f ∈ F0, (1 : ℚ) / ((Λ * f : ℕ) : ℚ)) = R0 := by
    have h1 : (∑ f ∈ F0, (1 : ℚ) / ((Λ * f : ℕ) : ℚ)) =
        (1 / (Λ : ℚ)) * ∑ f ∈ F0, (1 : ℚ) / (f : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      have hf_pos := hF0_pos f hf
      have hf_q_ne : (f : ℚ) ≠ 0 := by
        have : (0 : ℚ) < (f : ℚ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hf_pos)
        exact ne_of_gt this
      push_cast
      field_simp
    rw [h1, ← hF0_sum]
    field_simp
  refine ⟨{
    Λ := Λ
    hΛ_div_8 := hΛ_div_8
    hΛ_gt_L := hΛ_gt_L
    hΛ_gt_corr := hΛ_gt_corr
    F := F0
    hF_pos := hF0_pos
    hF_distinct_from_main_corr := ?_
    hF_recip := h_recip
  }⟩
  refine ⟨?_, ?_⟩
  · -- Filler denominators have `v₂ ≥ 3`, while main-slot denominators have
    -- `v₂ ∈ {0, 1}`.
    intro f hf j _ h hh h_eq
    have hf_pos := hF0_pos f hf
    have hfill_v2 : 3 ≤ padicValNat 2 (Λ * f) :=
      filler_v2_at_least_three Λ f hΛ_div_8 hΛ_pos hf_pos
    obtain ⟨hv1, hv2, hv3, hv6⟩ := main_valuation_profile j
    have hmain_v2 : padicValNat 2 (h * D j) ≤ 1 := by
      rw [show ({1, 2, 3, 6} : Finset ℕ) =
        insert 1 (insert 2 (insert 3 ({6} : Finset ℕ))) from rfl] at hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · rw [one_mul]
        have hv : padicValNat 2 (D j) = 0 := by
          have := congrArg Prod.fst hv1
          simpa using this
        rw [hv]
        norm_num
      · rcases Finset.mem_insert.mp hh with rfl | hh
        · have hv : padicValNat 2 (2 * D j) = 1 := by
            have := congrArg Prod.fst hv2
            simpa using this
          rw [hv]
        · rcases Finset.mem_insert.mp hh with rfl | hh
          · have hv : padicValNat 2 (3 * D j) = 0 := by
              have := congrArg Prod.fst hv3
              simpa using this
            rw [hv]
            norm_num
          · have h6 : h = 6 := by simpa using hh
            subst h
            have hv : padicValNat 2 (6 * D j) = 1 := by
              have := congrArg Prod.fst hv6
              simpa using this
            rw [hv]
    have hmain_v2_eq : padicValNat 2 (Λ * f) = padicValNat 2 (h * D j) := by
      rw [h_eq]
    omega
  · -- `Λ` is larger than every correction multiple `e * cν`, while
    -- `Λ * f ≥ Λ` because all filler factors are positive.
    intro f hf ν e he h_eq
    have hf_pos := hF0_pos f hf
    have hΛ_le : Λ ≤ Λ * f := by
      calc Λ = Λ * 1 := by ring
        _ ≤ Λ * f := Nat.mul_le_mul_left Λ hf_pos
    have h_inner : e * corr.c ν ≤
        (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) :=
      Finset.le_sup (f := fun e => e * corr.c ν) he
    have h_outer :
        (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) ≤ corrMax := by
      rw [hcorrMax_def]
      exact Finset.le_sup (f := fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν))
        (Finset.mem_univ ν)
    have hec_le : e * corr.c ν ≤ corrMax := le_trans h_inner h_outer
    have hcorr_lt : corrMax < Λ := by rw [hΛ_def]; omega
    have : Λ * f < Λ := by
      rw [h_eq]
      exact lt_of_le_of_lt hec_le hcorr_lt
    exact (not_lt_of_ge hΛ_le) this

/-! ### Bookkeeping for the final interval assembly -/

/-- `B_*`: the total correction increment obtained by switching every
correction slot. This is the harmless finite offset in the lower edge of the
attainable interval. -/
noncomputable def Bstar {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) : ℤ :=
  ∑ ν : Fin corr.t, corr.b ν

lemma Bstar_nonneg {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) :
    0 ≤ Bstar p hp corr := by
  unfold Bstar
  exact Finset.sum_nonneg (fun ν _ => (corr.hb_pos ν).le)

/-- Use the correction-slot subset-sum cover to choose a subset whose increment
puts an arbitrary integer `z` into the `g`-divisible residue class. -/
lemma correction_subset_dvd {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (z : ℤ) :
    ∃ T : Finset (Fin corr.t),
      (gcd.g : ℤ) ∣ z - ∑ ν ∈ T, corr.b ν := by
  classical
  obtain ⟨T, hT⟩ := corr.residue_cover (z : ZMod gcd.g)
  refine ⟨T, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hT]
  simp

lemma correction_subset_sum_nonneg {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t)) :
    0 ≤ ∑ ν ∈ T, corr.b ν := by
  exact Finset.sum_nonneg (fun ν _ => (corr.hb_pos ν).le)

lemma correction_subset_sum_le_Bstar {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t)) :
    (∑ ν ∈ T, corr.b ν) ≤ Bstar p hp corr := by
  unfold Bstar
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun ν _ _ => (corr.hb_pos ν).le)

lemma correction_subset_dvd_with_bounds {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd) (z : ℤ) :
    ∃ T : Finset (Fin corr.t),
      (gcd.g : ℤ) ∣ z - ∑ ν ∈ T, corr.b ν ∧
      0 ≤ ∑ ν ∈ T, corr.b ν ∧
      (∑ ν ∈ T, corr.b ν) ≤ Bstar p hp corr := by
  obtain ⟨T, hT⟩ := correction_subset_dvd p hp corr z
  exact ⟨T, hT, correction_subset_sum_nonneg p hp corr T,
    correction_subset_sum_le_Bstar p hp corr T⟩

/-- `M₀ := max 0 (g · X_q)`, the nonnegative RSG lower offset measured in the
undivided main-slot scale. -/
def M0 {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) (X_q : ℤ) : ℤ :=
  max 0 ((gcd.g : ℤ) * X_q)

lemma M0_nonneg {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) (X_q : ℤ) :
    0 ≤ M0 p hp gcd X_q := by
  unfold M0
  exact le_max_left _ _

lemma M0_ge_g_mul_Xq {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) (X_q : ℤ) :
    ((gcd.g : ℤ) * X_q) ≤ M0 p hp gcd X_q := by
  unfold M0
  exact le_max_right _ _

/-- The base integer p-sum `B_N`, before any main or correction switch:
main denominators `D j`, endpoint `τ_N`, all correction denominators, and all
filler denominators. -/
noncomputable def baseInt {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr) (N : ℕ) : ℤ :=
  (∑ j ∈ Finset.Icc md.J N, intEval p hp ((D j : ℕ) : ℤ)) +
  intEval p hp ((tau N : ℕ) : ℤ) +
  (∑ ν : Fin corr.t, intEval p hp ((corr.c ν : ℕ) : ℤ)) +
  (∑ f ∈ fill.F, intEval p hp (((fill.Λ * f : ℕ) : ℤ)))

lemma baseInt_succ_eq {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} (hJN : md.J ≤ N + 1) :
    baseInt p hp corr fill (N + 1) =
      baseInt p hp corr fill N +
        intEval p hp ((D (N + 1) : ℕ) : ℤ) +
        intEval p hp ((tau (N + 1) : ℕ) : ℤ) -
        intEval p hp ((tau N : ℕ) : ℤ) := by
  unfold baseInt
  rw [Finset.sum_Icc_succ_top hJN]
  ring

noncomputable def upperInt (p : ℚ[X]) (N : ℕ) : ℤ :=
  ⌊(muConst p) * (N : ℚ) ^ (2 * p.natDegree)⌋

noncomputable def lowerInt {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (X_q : ℤ) (N : ℕ) : ℤ :=
  baseInt p hp corr fill N + Bstar p hp corr + M0 p hp gcd X_q

noncomputable def upperEdge {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N : ℕ) : ℤ :=
  baseInt p hp corr fill N + upperInt p N

noncomputable def tauPoly : ℚ[X] :=
  Polynomial.C ((P : ℚ) ^ 2) * Polynomial.X +
    Polynomial.C ((P : ℚ) * ((P : ℚ) + 1))

noncomputable def tauNextPoly : ℚ[X] :=
  Polynomial.C ((P : ℚ) ^ 2) * Polynomial.X +
    Polynomial.C ((P : ℚ) * (2 * (P : ℚ) + 1))

noncomputable def baseStepPoly (p : ℚ[X]) : ℚ[X] :=
  p.comp (Dpoly 2) + (p.comp tauNextPoly - p.comp tauPoly)

lemma tauPoly_eval_nat (N : ℕ) :
    tauPoly.eval (N : ℚ) = (tau N : ℚ) := by
  norm_num [tauPoly, tau, u, P]
  ring

lemma tauNextPoly_eval_nat (N : ℕ) :
    tauNextPoly.eval (N : ℚ) = (tau (N + 1) : ℚ) := by
  norm_num [tauNextPoly, tau, u, P]
  ring

lemma tauPoly_natDegree : tauPoly.natDegree = 1 := by
  unfold tauPoly
  exact Polynomial.natDegree_linear (by unfold P; norm_num : ((P : ℚ) ^ 2) ≠ 0)

lemma tauNextPoly_natDegree : tauNextPoly.natDegree = 1 := by
  unfold tauNextPoly
  exact Polynomial.natDegree_linear (by unfold P; norm_num : ((P : ℚ) ^ 2) ≠ 0)

lemma Dpoly_two_eval_nat {N : ℕ} (hN : 1 ≤ N) :
    (Dpoly 2).eval (N : ℚ) = (D (N + 1) : ℚ) := by
  rw [Dpoly_eval_at_succ 2 N hN]
  have hidx : 2 + N - 1 = N + 1 := by omega
  rw [hidx]

lemma baseStepPoly_eval_nat (p : ℚ[X]) (hp : IntValued p)
    {N : ℕ} (hN : 1 ≤ N) :
    (baseStepPoly p).eval (N : ℚ) =
      ((intEval p hp ((D (N + 1) : ℕ) : ℤ) : ℤ) : ℚ) +
      ((intEval p hp ((tau (N + 1) : ℕ) : ℤ) : ℤ) : ℚ) -
      ((intEval p hp ((tau N : ℕ) : ℤ) : ℤ) : ℚ) := by
  unfold baseStepPoly
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_comp]
  rw [Dpoly_two_eval_nat hN, tauNextPoly_eval_nat, tauPoly_eval_nat]
  rw [intEval_spec p hp ((D (N + 1) : ℕ) : ℤ)]
  rw [intEval_spec p hp ((tau (N + 1) : ℕ) : ℤ)]
  rw [intEval_spec p hp ((tau N : ℕ) : ℤ)]
  push_cast
  ring

lemma p_comp_Dpoly_two_natDegree (p : ℚ[X]) :
    (p.comp (Dpoly 2)).natDegree = 2 * p.natDegree := by
  rw [Polynomial.natDegree_comp, Dpoly_natDegree]
  ring

lemma p_comp_Dpoly_two_leadingCoeff (p : ℚ[X])
    (_h_lead_pos : 0 < p.leadingCoeff) :
    (p.comp (Dpoly 2)).leadingCoeff = lambdaConst p := by
  unfold lambdaConst
  rw [Polynomial.leadingCoeff_comp ?_, Dpoly_leadingCoeff]
  · rw [← pow_mul]
  · rw [Dpoly_natDegree]
    norm_num

lemma p_comp_tauPoly_natDegree_le (p : ℚ[X]) :
    (p.comp tauPoly).natDegree ≤ p.natDegree := by
  have h := Polynomial.natDegree_comp_le (p := p) (q := tauPoly)
  rw [tauPoly_natDegree] at h
  simpa using h

lemma p_comp_tauNextPoly_natDegree_le (p : ℚ[X]) :
    (p.comp tauNextPoly).natDegree ≤ p.natDegree := by
  have h := Polynomial.natDegree_comp_le (p := p) (q := tauNextPoly)
  rw [tauNextPoly_natDegree] at h
  simpa using h

lemma baseStepPoly_natDegree_eq (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) :
    (baseStepPoly p).natDegree = 2 * p.natDegree := by
  unfold baseStepPoly
  have hD : (p.comp (Dpoly 2)).natDegree = 2 * p.natDegree :=
    p_comp_Dpoly_two_natDegree p
  have hQle :
      (p.comp tauNextPoly - p.comp tauPoly).natDegree ≤ p.natDegree := by
    exact le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le (p_comp_tauNextPoly_natDegree_le p) (p_comp_tauPoly_natDegree_le p))
  have hQlt :
      (p.comp tauNextPoly - p.comp tauPoly).natDegree <
        (p.comp (Dpoly 2)).natDegree := by
    rw [hD]
    omega
  exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hQlt).trans hD

lemma baseStepPoly_leadingCoeff_eq (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (baseStepPoly p).leadingCoeff = lambdaConst p := by
  unfold baseStepPoly
  have hD : (p.comp (Dpoly 2)).natDegree = 2 * p.natDegree :=
    p_comp_Dpoly_two_natDegree p
  have hQle :
      (p.comp tauNextPoly - p.comp tauPoly).natDegree ≤ p.natDegree := by
    exact le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le (p_comp_tauNextPoly_natDegree_le p) (p_comp_tauPoly_natDegree_le p))
  have hQlt_nat :
      (p.comp tauNextPoly - p.comp tauPoly).natDegree <
        (p.comp (Dpoly 2)).natDegree := by
    rw [hD]
    omega
  have hQlt_deg :
      (p.comp tauNextPoly - p.comp tauPoly).degree <
        (p.comp (Dpoly 2)).degree :=
    Polynomial.degree_lt_degree hQlt_nat
  rw [Polynomial.leadingCoeff_add_of_degree_lt' hQlt_deg]
  exact p_comp_Dpoly_two_leadingCoeff p h_lead_pos

/-- If the leading coefficient of a rational polynomial is strictly below `c`,
then eventually its values are below `c N^d`, provided its natural degree is
exactly `d > 0`. -/
lemma polynomial_eventually_le_const_mul_pow (R : ℚ[X]) {d : ℕ} {c : ℚ}
    (hd_pos : 0 < d) (hdeg : R.natDegree = d)
    (hlead : R.leadingCoeff < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      R.eval (N : ℚ) ≤ c * (N : ℚ) ^ d := by
  classical
  let Xd : ℚ[X] := Polynomial.X ^ d
  have hR_ne : R ≠ 0 := by
    intro hR
    rw [hR, Polynomial.natDegree_zero] at hdeg
    omega
  have hdeg_degree : R.degree = Xd.degree := by
    rw [Polynomial.degree_eq_natDegree hR_ne, hdeg]
    dsimp [Xd]
    rw [Polynomial.degree_X_pow]
  have ht :
      Tendsto (fun x : ℚ => R.eval x / Xd.eval x) atTop
        (nhds (R.leadingCoeff / Xd.leadingCoeff)) :=
    Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq R Xd hdeg_degree
  have hlead_ratio : R.leadingCoeff / Xd.leadingCoeff = R.leadingCoeff := by
    dsimp [Xd]
    rw [Polynomial.leadingCoeff_X_pow]
    simp
  rw [hlead_ratio] at ht
  have ht_nat :
      Tendsto (fun N : ℕ => R.eval (N : ℚ) / Xd.eval (N : ℚ)) atTop
        (nhds R.leadingCoeff) :=
    ht.comp tendsto_natCast_atTop_atTop
  have hevent :
      ∀ᶠ N : ℕ in atTop,
        R.eval (N : ℚ) / Xd.eval (N : ℚ) < c :=
    ht_nat.eventually (eventually_lt_nhds hlead)
  rw [eventually_atTop] at hevent
  obtain ⟨N₁, hN₁⟩ := hevent
  refine ⟨max N₁ 1, ?_⟩
  intro N hN
  have hN₁N : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have h1N : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hratio := hN₁ N hN₁N
  have hXd_eval : Xd.eval (N : ℚ) = (N : ℚ) ^ d := by
    simp [Xd]
  have hNq_pos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast h1N
  have hden_pos : 0 < Xd.eval (N : ℚ) := by
    rw [hXd_eval]
    exact pow_pos hNq_pos d
  have hlt : R.eval (N : ℚ) < c * Xd.eval (N : ℚ) :=
    (div_lt_iff₀ hden_pos).mp hratio
  rw [hXd_eval] at hlt
  exact le_of_lt hlt

/-- Lower-bound companion to `polynomial_eventually_le_const_mul_pow`. -/
lemma const_mul_pow_eventually_le_polynomial (R : ℚ[X]) {d : ℕ} {c : ℚ}
    (hd_pos : 0 < d) (hdeg : R.natDegree = d)
    (hc_lt_lead : c < R.leadingCoeff) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℚ) ^ d ≤ R.eval (N : ℚ) := by
  have hneg_deg : (-R).natDegree = d := by
    rw [Polynomial.natDegree_neg, hdeg]
  have hneg_lead : (-R).leadingCoeff < -c := by
    rw [Polynomial.leadingCoeff_neg]
    linarith
  obtain ⟨N₀, hN₀⟩ :=
    polynomial_eventually_le_const_mul_pow (-R) hd_pos hneg_deg hneg_lead
  refine ⟨N₀, ?_⟩
  intro N hN
  have h := hN₀ N hN
  rw [Polynomial.eval_neg] at h
  linarith

/-- Since `(N - J + 1) / N → 1`, any strict coefficient gap `β < c`
eventually gives `β N^d < c (N - J + 1)^d`. -/
lemma shifted_power_eventually_mul_lt (J d : ℕ) {β c : ℚ}
    (_hd_pos : 0 < d) (hβ_pos : 0 < β) (hβc : β < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      β * (N : ℚ) ^ d < c * ((N - J + 1 : ℕ) : ℚ) ^ d := by
  classical
  let A : ℚ[X] := (Polynomial.X - Polynomial.C ((J : ℚ) - 1)) ^ d
  let Xd : ℚ[X] := Polynomial.X ^ d
  have hc_pos : 0 < c := lt_trans hβ_pos hβc
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hA_monic : A.Monic := by
    dsimp [A]
    exact (Polynomial.monic_X_sub_C ((J : ℚ) - 1)).pow d
  have hA_natDegree : A.natDegree = d := by
    dsimp [A]
    rw [(Polynomial.monic_X_sub_C ((J : ℚ) - 1)).natDegree_pow,
      Polynomial.natDegree_X_sub_C]
    ring
  have hdeg_degree : A.degree = Xd.degree := by
    rw [Polynomial.degree_eq_natDegree hA_monic.ne_zero, hA_natDegree]
    dsimp [Xd]
    rw [Polynomial.degree_X_pow]
  have ht :
      Tendsto (fun x : ℚ => A.eval x / Xd.eval x) atTop
        (nhds (A.leadingCoeff / Xd.leadingCoeff)) :=
    Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq A Xd hdeg_degree
  have hlead_ratio : A.leadingCoeff / Xd.leadingCoeff = 1 := by
    have hA_lc : A.leadingCoeff = 1 := hA_monic.leadingCoeff
    dsimp [Xd]
    rw [hA_lc, Polynomial.leadingCoeff_X_pow]
    simp
  rw [hlead_ratio] at ht
  have ht_nat :
      Tendsto (fun N : ℕ => A.eval (N : ℚ) / Xd.eval (N : ℚ)) atTop
        (nhds (1 : ℚ)) :=
    ht.comp tendsto_natCast_atTop_atTop
  have hβ_div_c_lt_one : β / c < 1 := by
    rw [div_lt_one₀ hc_pos]
    exact hβc
  have hevent :
      ∀ᶠ N : ℕ in atTop,
        β / c < A.eval (N : ℚ) / Xd.eval (N : ℚ) :=
    ht_nat.eventually (eventually_gt_nhds hβ_div_c_lt_one)
  rw [eventually_atTop] at hevent
  obtain ⟨N₁, hN₁⟩ := hevent
  refine ⟨max (max N₁ 1) J, ?_⟩
  intro N hN
  have hN₁N : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have h1N : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hJN : J ≤ N := le_trans (le_max_right _ _) hN
  have hratio := hN₁ N hN₁N
  have hXd_eval : Xd.eval (N : ℚ) = (N : ℚ) ^ d := by
    simp [Xd]
  have hA_eval : A.eval (N : ℚ) = ((N - J + 1 : ℕ) : ℚ) ^ d := by
    dsimp [A]
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have harg : (N : ℚ) - ((J : ℚ) - 1) = ((N - J + 1 : ℕ) : ℚ) := by
      have harg_int :
          (N : ℤ) - ((J : ℤ) - 1) = ((N - J + 1 : ℕ) : ℤ) := by
        omega
      exact_mod_cast harg_int
    rw [harg]
  have hNq_pos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast h1N
  have hden_pos : 0 < Xd.eval (N : ℚ) := by
    rw [hXd_eval]
    exact pow_pos hNq_pos d
  rw [lt_div_iff₀ hden_pos] at hratio
  have hmul := mul_lt_mul_of_pos_left hratio hc_pos
  have hleft :
      c * ((β / c) * Xd.eval (N : ℚ)) =
        β * Xd.eval (N : ℚ) := by
    field_simp [hc_ne]
  rw [hleft, hXd_eval, hA_eval] at hmul
  exact hmul

lemma baseStepPoly_add_const_natDegree_eq (p : ℚ[X]) (C : ℤ)
    (h_nonconst : 1 ≤ p.natDegree) :
    (baseStepPoly p + Polynomial.C (C : ℚ)).natDegree =
      2 * p.natDegree := by
  have hbase : (baseStepPoly p).natDegree = 2 * p.natDegree :=
    baseStepPoly_natDegree_eq p h_nonconst
  have hconst_lt :
      (Polynomial.C (C : ℚ)).natDegree < (baseStepPoly p).natDegree := by
    rw [hbase]
    simp
    omega
  exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hconst_lt).trans hbase

lemma baseStepPoly_add_const_leadingCoeff_eq (p : ℚ[X]) (C : ℤ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (baseStepPoly p + Polynomial.C (C : ℚ)).leadingCoeff =
      lambdaConst p := by
  have hbase : (baseStepPoly p).natDegree = 2 * p.natDegree :=
    baseStepPoly_natDegree_eq p h_nonconst
  have hconst_lt_nat :
      (Polynomial.C (C : ℚ)).natDegree < (baseStepPoly p).natDegree := by
    rw [hbase]
    simp
    omega
  have hconst_lt_deg :
      (Polynomial.C (C : ℚ)).degree < (baseStepPoly p).degree :=
    Polynomial.degree_lt_degree hconst_lt_nat
  rw [Polynomial.leadingCoeff_add_of_degree_lt' hconst_lt_deg]
  exact baseStepPoly_leadingCoeff_eq p h_nonconst h_lead_pos

lemma baseStep_eventually_le_upperInt {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (X_q : ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      intEval p hp ((D (N + 1) : ℕ) : ℤ) +
          intEval p hp ((tau (N + 1) : ℕ) : ℤ) -
          intEval p hp ((tau N : ℕ) : ℤ) +
          (Bstar p hp corr + M0 p hp gcd X_q) ≤ upperInt p N := by
  let C : ℤ := Bstar p hp corr + M0 p hp gcd X_q
  let R : ℚ[X] := baseStepPoly p + Polynomial.C (C : ℚ)
  have hd_pos : 0 < 2 * p.natDegree := by omega
  have hRdeg : R.natDegree = 2 * p.natDegree := by
    dsimp [R]
    exact baseStepPoly_add_const_natDegree_eq p C h_nonconst
  have hRlead : R.leadingCoeff < muConst p := by
    dsimp [R]
    rw [baseStepPoly_add_const_leadingCoeff_eq p C h_nonconst h_lead_pos]
    exact lambdaConst_lt_muConst p h_nonconst h_lead_pos
  obtain ⟨N₀, hN₀⟩ :=
    polynomial_eventually_le_const_mul_pow R hd_pos hRdeg hRlead
  refine ⟨max N₀ 1, ?_⟩
  intro N hN
  have hN₀N : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN_pos : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hpoly := hN₀ N hN₀N
  have hR_eval :
      R.eval (N : ℚ) =
        ((intEval p hp ((D (N + 1) : ℕ) : ℤ) +
          intEval p hp ((tau (N + 1) : ℕ) : ℤ) -
          intEval p hp ((tau N : ℕ) : ℤ) + C : ℤ) : ℚ) := by
    dsimp [R, C]
    rw [Polynomial.eval_add, Polynomial.eval_C, baseStepPoly_eval_nat p hp hN_pos]
    push_cast
    ring
  unfold upperInt
  exact Int.le_floor.mpr (by
    rw [← hR_eval]
    exact hpoly)

lemma intervals_overlap_eventually {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (X_q : ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      lowerInt p hp corr fill X_q (N + 1) ≤
        upperEdge p hp corr fill N + 1 := by
  obtain ⟨Ns, hNs⟩ :=
    baseStep_eventually_le_upperInt p hp h_nonconst h_lead_pos corr X_q
  refine ⟨max Ns md.J, ?_⟩
  intro N hN
  have hNsN : Ns ≤ N := le_trans (le_max_left _ _) hN
  have hJN : md.J ≤ N + 1 := by
    have : md.J ≤ N := le_trans (le_max_right _ _) hN
    omega
  have hstep := hNs N hNsN
  rw [lowerInt, upperEdge, baseInt_succ_eq p hp corr fill hJN]
  linarith

lemma qPoly_tail_eventually {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (X_q : ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ upperInt p N →
        ∀ i : ℕ, N - md.J < i →
          (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ) := by
  classical
  let q : ℚ[X] := qPoly p md.J gcd.g
  let d : ℕ := 2 * p.natDegree
  let beta : ℚ := muConst p / (gcd.g : ℚ)
  have hd_pos : 0 < d := by
    dsimp [d]
    omega
  have hgq_pos : (0 : ℚ) < (gcd.g : ℚ) := by exact_mod_cast gcd.hg_pos
  have hbeta_pos : 0 < beta := by
    dsimp [beta]
    exact div_pos (muConst_pos p h_nonconst h_lead_pos) hgq_pos
  have hqdeg : q.natDegree = d := by
    dsimp [q, d]
    exact qPoly_natDegree p md.J gcd.g gcd.hg_pos h_nonconst h_lead_pos
  have hbeta_lt_qlead : beta < q.leadingCoeff := by
    dsimp [beta, q]
    rw [qPoly_leadingCoeff p md.J gcd.g gcd.hg_pos h_nonconst h_lead_pos]
    exact div_lt_div_of_pos_right
      (muConst_lt_a_theta_P p h_nonconst h_lead_pos) hgq_pos
  let c : ℚ := (beta + q.leadingCoeff) / 2
  have hbeta_lt_c : beta < c := by
    dsimp [c]
    linarith
  have hc_lt_qlead : c < q.leadingCoeff := by
    dsimp [c]
    linarith
  have hc_pos : 0 < c := lt_trans hbeta_pos hbeta_lt_c
  obtain ⟨Nq, hNq⟩ :=
    const_mul_pow_eventually_le_polynomial q hd_pos hqdeg hc_lt_qlead
  obtain ⟨Ns, hNs⟩ :=
    shifted_power_eventually_mul_lt md.J d hd_pos hbeta_pos hbeta_lt_c
  refine ⟨max Ns (Nq + md.J), ?_⟩
  intro N hN X _hX_ge hXU i hi
  have hNsN : Ns ≤ N := le_trans (le_max_left _ _) hN
  have hNqJ : Nq + md.J ≤ N := le_trans (le_max_right _ _) hN
  have hNq_base : Nq ≤ N - md.J + 1 := by omega
  have hbase_i1 : N - md.J + 1 ≤ i + 1 := by omega
  have hNq_i1 : Nq ≤ i + 1 := le_trans hNq_base hbase_i1
  have hq_lower := hNq (i + 1) hNq_i1
  have hshift := hNs N hNsN
  have hupper_le :
      (upperInt p N : ℚ) ≤ muConst p * (N : ℚ) ^ d := by
    dsimp [d]
    unfold upperInt
    exact Int.floor_le _
  have hgX_le_upper :
      (gcd.g : ℚ) * (X : ℚ) ≤ (upperInt p N : ℚ) := by
    exact_mod_cast hXU
  have hgX_le_mu :
      (gcd.g : ℚ) * (X : ℚ) ≤ muConst p * (N : ℚ) ^ d :=
    le_trans hgX_le_upper hupper_le
  have hbeta_mul_eq :
      beta * (N : ℚ) ^ d =
        (muConst p * (N : ℚ) ^ d) / (gcd.g : ℚ) := by
    dsimp [beta]
    ring
  have hX_le_beta : (X : ℚ) ≤ beta * (N : ℚ) ^ d := by
    rw [hbeta_mul_eq, le_div_iff₀ hgq_pos]
    calc
      (X : ℚ) * (gcd.g : ℚ) = (gcd.g : ℚ) * (X : ℚ) := by ring
      _ ≤ muConst p * (N : ℚ) ^ d := hgX_le_mu
  have hbase_i1_q :
      ((N - md.J + 1 : ℕ) : ℚ) ≤ ((i + 1 : ℕ) : ℚ) := by
    exact_mod_cast hbase_i1
  have hpow_le :
      ((N - md.J + 1 : ℕ) : ℚ) ^ d ≤
        ((i + 1 : ℕ) : ℚ) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase_i1_q d
  have hc_mul_le :
      c * ((N - md.J + 1 : ℕ) : ℚ) ^ d ≤
        c * ((i + 1 : ℕ) : ℚ) ^ d :=
    mul_le_mul_of_nonneg_left hpow_le hc_pos.le
  calc
    (X : ℚ) ≤ beta * (N : ℚ) ^ d := hX_le_beta
    _ < c * ((N - md.J + 1 : ℕ) : ℚ) ^ d := hshift
    _ ≤ c * ((i + 1 : ℕ) : ℚ) ^ d := hc_mul_le
    _ ≤ q.eval ((i + 1 : ℕ) : ℚ) := hq_lower

lemma upperInt_unbounded (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (N₀ : ℕ) :
    ∀ M : ℤ, ∃ N, N₀ ≤ N ∧ M ≤ upperInt p N := by
  intro M
  have hpow_ne : 2 * p.natDegree ≠ 0 := by omega
  have hμ_pos : 0 < muConst p := muConst_pos p h_nonconst h_lead_pos
  have ht_q :
      Tendsto (fun x : ℚ => muConst p * x ^ (2 * p.natDegree))
        atTop atTop :=
    tendsto_const_mul_pow_atTop hpow_ne hμ_pos
  have ht_nat :
      Tendsto (fun N : ℕ => muConst p * (N : ℚ) ^ (2 * p.natDegree))
        atTop atTop :=
    ht_q.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.tendsto_atTop_atTop.mp ht_nat ((M : ℚ) + 1)
  refine ⟨max N₀ N₁, le_max_left _ _, ?_⟩
  have hlarge :
      (M : ℚ) + 1 ≤
        muConst p * ((max N₀ N₁ : ℕ) : ℚ) ^ (2 * p.natDegree) :=
    hN₁ (max N₀ N₁) (le_max_right _ _)
  unfold upperInt
  exact Int.le_floor.mpr (by linarith)

lemma intEval_nonneg_eventually (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → 0 ≤ intEval p hp ((n : ℕ) : ℤ) := by
  set pr : ℝ[X] := p.map (algebraMap ℚ ℝ) with hpr_def
  have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
    (algebraMap ℚ ℝ).injective
  have hpr_natDegree : pr.natDegree = p.natDegree := by
    rw [hpr_def, Polynomial.natDegree_map_eq_of_injective h_inj]
  have hpr_deg_pos : 0 < pr.degree := by
    have hnat : 0 < pr.natDegree := by
      rw [hpr_natDegree]
      exact h_nonconst
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
  have hpr_lead_pos : 0 < pr.leadingCoeff := by
    rw [hpr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
    have : (0 : ℝ) < (p.leadingCoeff : ℝ) := by
      exact_mod_cast h_lead_pos
    simpa [algebraMap] using this
  have h_tendsto : Tendsto (fun x : ℝ => pr.eval x) atTop atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg pr hpr_deg_pos hpr_lead_pos.le
  obtain ⟨R, hR⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto 0
  refine ⟨Nat.ceil (max R 0), ?_⟩
  intro n hn
  have hR_le_n : R ≤ (n : ℝ) := by
    have hR_le_ceil : R ≤ (Nat.ceil (max R 0) : ℝ) := by
      exact le_trans (le_max_left _ _) (Nat.le_ceil _)
    have hceil_le_n : (Nat.ceil (max R 0) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact le_trans hR_le_ceil hceil_le_n
  have h_eval_real : 0 ≤ pr.eval ((n : ℕ) : ℝ) := hR _ hR_le_n
  have h_eval_cast :
      pr.eval ((n : ℕ) : ℝ) = ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [hpr_def]
    have hn_cast : ((n : ℕ) : ℝ) =
        (algebraMap ℚ ℝ) ((n : ℕ) : ℚ) := by
      simp [algebraMap]
    rw [hn_cast, Polynomial.eval_map_apply]
    simp [algebraMap]
  have h_eval_q : 0 ≤ p.eval ((n : ℕ) : ℚ) := by
    have : (0 : ℝ) ≤ ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [← h_eval_cast]
      exact h_eval_real
    exact_mod_cast this
  have h_intEval_eq :
      ((intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) =
        p.eval ((n : ℕ) : ℚ) := by
    rw [intEval_spec]
    push_cast
    rfl
  have : (0 : ℚ) ≤ ((intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) := by
    rw [h_intEval_eq]
    exact h_eval_q
  exact_mod_cast this

lemma intEval_eventually_ge (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (M : ℤ) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → M ≤ intEval p hp ((n : ℕ) : ℤ) := by
  set pr : ℝ[X] := p.map (algebraMap ℚ ℝ) with hpr_def
  have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
    (algebraMap ℚ ℝ).injective
  have hpr_natDegree : pr.natDegree = p.natDegree := by
    rw [hpr_def, Polynomial.natDegree_map_eq_of_injective h_inj]
  have hpr_deg_pos : 0 < pr.degree := by
    have hnat : 0 < pr.natDegree := by
      rw [hpr_natDegree]
      exact h_nonconst
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
  have hpr_lead_pos : 0 < pr.leadingCoeff := by
    rw [hpr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
    have : (0 : ℝ) < (p.leadingCoeff : ℝ) := by
      exact_mod_cast h_lead_pos
    simpa [algebraMap] using this
  have h_tendsto : Tendsto (fun x : ℝ => pr.eval x) atTop atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg pr hpr_deg_pos hpr_lead_pos.le
  obtain ⟨R, hR⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto (M : ℝ)
  refine ⟨Nat.ceil (max R 0), ?_⟩
  intro n hn
  have hR_le_n : R ≤ (n : ℝ) := by
    have hR_le_ceil : R ≤ (Nat.ceil (max R 0) : ℝ) := by
      exact le_trans (le_max_left _ _) (Nat.le_ceil _)
    have hceil_le_n : (Nat.ceil (max R 0) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact le_trans hR_le_ceil hceil_le_n
  have h_eval_real : (M : ℝ) ≤ pr.eval ((n : ℕ) : ℝ) := hR _ hR_le_n
  have h_eval_cast :
      pr.eval ((n : ℕ) : ℝ) = ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [hpr_def]
    have hn_cast : ((n : ℕ) : ℝ) =
        (algebraMap ℚ ℝ) ((n : ℕ) : ℚ) := by
      simp [algebraMap]
    rw [hn_cast, Polynomial.eval_map_apply]
    simp [algebraMap]
  have h_eval_q : (M : ℚ) ≤ p.eval ((n : ℕ) : ℚ) := by
    have : ((M : ℚ) : ℝ) ≤ ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [← h_eval_cast]
      exact_mod_cast h_eval_real
    exact_mod_cast this
  have h_intEval_eq :
      ((intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) =
        p.eval ((n : ℕ) : ℚ) := by
    rw [intEval_spec]
    push_cast
    rfl
  have : (M : ℚ) ≤ ((intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) := by
    rw [h_intEval_eq]
    exact h_eval_q
  exact_mod_cast this

lemma self_le_D (j : ℕ) : j ≤ D j := by
  unfold D u P
  nlinarith [Nat.zero_le j]

lemma self_le_tau (N : ℕ) : N ≤ tau N := by
  unfold tau u P
  nlinarith [Nat.zero_le N]

lemma baseInt_nonneg_eventually {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 ≤ baseInt p hp corr fill N := by
  classical
  obtain ⟨Kp, hKp⟩ := intEval_nonneg_eventually p hp h_nonconst h_lead_pos
  let f : ℕ → ℤ := fun j => intEval p hp ((D j : ℕ) : ℤ)
  let mainK : ℤ := ∑ j ∈ Finset.Icc md.J Kp, f j
  let corrBase : ℤ := ∑ ν : Fin corr.t, intEval p hp ((corr.c ν : ℕ) : ℤ)
  let fillBase : ℤ := ∑ x ∈ fill.F, intEval p hp (((fill.Λ * x : ℕ) : ℤ))
  let C : ℤ := mainK + corrBase + fillBase
  obtain ⟨Kτ, hKτ⟩ := intEval_eventually_ge p hp h_nonconst h_lead_pos (-C)
  refine ⟨max Kp Kτ, ?_⟩
  intro N hN
  have hKpN : Kp ≤ N := le_trans (le_max_left _ _) hN
  have hKτN : Kτ ≤ N := le_trans (le_max_right _ _) hN
  have hmain_ge :
      mainK ≤ ∑ j ∈ Finset.Icc md.J N, f j := by
    dsimp [mainK]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, le_trans (Finset.mem_Icc.mp hj).2 hKpN⟩
    · intro j hjN hjnot
      have hj_bounds := Finset.mem_Icc.mp hjN
      have hKp_lt_j : Kp < j := by
        by_contra hnotlt
        have hj_le_Kp : j ≤ Kp := le_of_not_gt hnotlt
        exact hjnot (Finset.mem_Icc.mpr ⟨hj_bounds.1, hj_le_Kp⟩)
      dsimp [f]
      exact hKp (D j) (le_trans (le_of_lt hKp_lt_j) (self_le_D j))
  have hKτ_tau : Kτ ≤ tau N := le_trans hKτN (self_le_tau N)
  have htau_ge :
      -C ≤ intEval p hp ((tau N : ℕ) : ℤ) :=
    hKτ (tau N) hKτ_tau
  unfold baseInt
  dsimp [C, mainK, corrBase, fillBase, f] at hmain_ge htau_ge ⊢
  linarith

lemma upperEdge_unbounded {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N₀ : ℕ) :
    ∀ M : ℤ, ∃ N, N₀ ≤ N ∧ M ≤ upperEdge p hp corr fill N := by
  obtain ⟨Nb, hNb⟩ :=
    baseInt_nonneg_eventually p hp h_nonconst h_lead_pos corr fill
  intro M
  obtain ⟨N, hN, hupper⟩ :=
    upperInt_unbounded p h_nonconst h_lead_pos (max N₀ Nb) M
  refine ⟨N, le_trans (le_max_left _ _) hN, ?_⟩
  have hb : 0 ≤ baseInt p hp corr fill N :=
    hNb N (le_trans (le_max_right _ _) hN)
  unfold upperEdge
  linarith

lemma main_slot_switch_intEval_sum (p : ℚ[X]) (hp : IntValued p) (j : ℕ) :
    (∑ n ∈ scaledPatternDenoms E0 (D j), intEval p hp ((n : ℕ) : ℤ)) -
        intEval p hp ((D j : ℕ) : ℤ) =
      intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) := by
  have hD_pos : 0 < D j := by
    unfold D u P
    positivity
  change
    (∑ n ∈ scaledPatternDenoms E0 (D j), intEval p hp ((n : ℕ) : ℤ)) -
        intEval p hp ((D j : ℕ) : ℤ) =
      intEval (switchingPoly p E0) (switchingPoly_intValued p hp E0)
        ((D j : ℕ) : ℤ)
  exact scaledPatternDenoms_intEval_sum_sub p hp E0 hD_pos

lemma correction_slot_switch_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (ν : Fin corr.t) (hc : 0 < corr.c ν) :
    (∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
        intEval p hp ((n : ℕ) : ℤ)) -
        intEval p hp ((corr.c ν : ℕ) : ℤ) =
      corr.b ν := by
  rw [corr.hb_def ν]
  exact scaledPatternDenoms_intEval_sum_sub p hp (corr.G ν) hc

/-! ### Explicit final denominator blocks

The final construction starts with one denominator for each main slot and
correction slot, then replaces selected slots by their Egyptian-pattern
multiples. These definitions keep the concrete final `Finset ℕ` separate from
the indexed sum identities below. -/

def mainUnswitchedDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc md.J N \ S).image D

def mainSwitchedDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (_md : MainChoice α L p hp) (_N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.biUnion fun j => scaledPatternDenoms E0 (D j)

def mainDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  mainUnswitchedDenoms md N S ∪ mainSwitchedDenoms md N S ∪ {tau N}

def correctionUnswitchedDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) : Finset ℕ :=
  ((Finset.univ : Finset (Fin corr.t)) \ T).image corr.c

def correctionSwitchedDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) : Finset ℕ :=
  T.biUnion fun ν => scaledPatternDenoms (corr.G ν) (corr.c ν)

def correctionDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) : Finset ℕ :=
  correctionUnswitchedDenoms corr T ∪ correctionSwitchedDenoms corr T

def fillerDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} (fill : FillerData p hp corr) :
    Finset ℕ :=
  fill.F.image fun f => fill.Λ * f

def finalDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N : ℕ) (S : Finset ℕ) (T : Finset (Fin corr.t)) : Finset ℕ :=
  mainDenoms md N S ∪ correctionDenoms corr T ∪ fillerDenoms fill

abbrev MainUnswitchedIndex {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ) :=
  {j : ℕ // j ∈ Finset.Icc md.J N \ S}

noncomputable instance mainUnswitchedIndexFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ) :
    Fintype (MainUnswitchedIndex md N S) :=
  Fintype.ofFinset (Finset.Icc md.J N \ S) (by intro x; rfl)

abbrev MainSwitchSlotIndex (S : Finset ℕ) :=
  {j : ℕ // j ∈ S}

noncomputable instance mainSwitchSlotIndexFintype (S : Finset ℕ) :
    Fintype (MainSwitchSlotIndex S) :=
  Fintype.ofFinset S (by intro x; rfl)

abbrev MainSwitchedIndex (S : Finset ℕ) :=
  Sigma fun j : MainSwitchSlotIndex S =>
    {n : ℕ // n ∈ scaledPatternDenoms E0 (D j.1)}

noncomputable instance mainSwitchedIndexFiberFintype (S : Finset ℕ)
    (j : MainSwitchSlotIndex S) :
    Fintype {n : ℕ // n ∈ scaledPatternDenoms E0 (D j.1)} :=
  Fintype.ofFinset (scaledPatternDenoms E0 (D j.1)) (by intro x; rfl)

abbrev CorrectionUnswitchedIndex {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :=
  {ν : Fin corr.t // ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T}

noncomputable instance correctionUnswitchedIndexFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t)) :
    Fintype (CorrectionUnswitchedIndex corr T) :=
  Fintype.ofFinset ((Finset.univ : Finset (Fin corr.t)) \ T)
    (by intro x; rfl)

abbrev CorrectionSwitchSlotIndex {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :=
  {ν : Fin corr.t // ν ∈ T}

noncomputable instance correctionSwitchSlotIndexFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t)) :
    Fintype (CorrectionSwitchSlotIndex corr T) :=
  Fintype.ofFinset T (by intro x; rfl)

abbrev CorrectionSwitchedIndex {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :=
  Sigma fun ν : CorrectionSwitchSlotIndex corr T =>
    {n : ℕ // n ∈ scaledPatternDenoms (corr.G ν.1) (corr.c ν.1)}

noncomputable instance correctionSwitchedIndexFiberFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t))
    (ν : CorrectionSwitchSlotIndex corr T) :
    Fintype {n : ℕ // n ∈ scaledPatternDenoms (corr.G ν.1) (corr.c ν.1)} :=
  Fintype.ofFinset (scaledPatternDenoms (corr.G ν.1) (corr.c ν.1))
    (by intro x; rfl)

abbrev FillerIndex {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} (fill : FillerData p hp corr) :=
  {f : ℕ // f ∈ fill.F}

noncomputable instance fillerIndexFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} (fill : FillerData p hp corr) :
    Fintype (FillerIndex fill) :=
  Fintype.ofFinset fill.F (by intro x; rfl)

abbrev FinalIndex {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N : ℕ) (S : Finset ℕ) (T : Finset (Fin corr.t)) :=
  ((MainUnswitchedIndex md N S ⊕ MainSwitchedIndex S) ⊕ PUnit.{1}) ⊕
    ((CorrectionUnswitchedIndex corr T ⊕ CorrectionSwitchedIndex corr T) ⊕
      FillerIndex fill)

def finalIndexDenom {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} {fill : FillerData p hp corr}
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)} :
    FinalIndex corr fill N S T → ℕ
  | Sum.inl (Sum.inl (Sum.inl j)) => D j.1
  | Sum.inl (Sum.inl (Sum.inr sw)) => sw.2.1
  | Sum.inl (Sum.inr _) => tau N
  | Sum.inr (Sum.inl (Sum.inl ν)) => corr.c ν.1
  | Sum.inr (Sum.inl (Sum.inr sw)) => sw.2.1
  | Sum.inr (Sum.inr f) => fill.Λ * f.1

def correctionMultiplierMax {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd) : ℕ :=
  (Finset.univ : Finset (Fin corr.t)).sup fun ν =>
    (insert 1 (corr.G ν)).sup fun e => e * corr.c ν

lemma correctionMultiplierMax_lt_tau_eventually {α : ℚ} {L : ℕ}
    {p : ℚ[X]} {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      correctionMultiplierMax corr < tau N := by
  refine ⟨correctionMultiplierMax corr + 1, ?_⟩
  intro N hN
  unfold tau u P
  nlinarith [Nat.zero_le N, hN]

lemma correction_multiple_le_max {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (ν : Fin corr.t) {e : ℕ} (he : e ∈ insert 1 (corr.G ν)) :
    e * corr.c ν ≤ correctionMultiplierMax corr := by
  unfold correctionMultiplierMax
  have h_inner :
      e * corr.c ν ≤ (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) :=
    Finset.le_sup (f := fun e => e * corr.c ν) he
  have h_outer :
      (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) ≤
        (Finset.univ : Finset (Fin corr.t)).sup
          (fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν)) :=
    Finset.le_sup
      (f := fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν))
      (Finset.mem_univ ν)
  exact le_trans h_inner h_outer

lemma correction_multiple_ne_tau_of_max_lt {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    {N : ℕ} (hτ : correctionMultiplierMax corr < tau N)
    (ν : Fin corr.t) {e : ℕ} (he : e ∈ insert 1 (corr.G ν)) :
    e * corr.c ν ≠ tau N := by
  intro h
  have hle := correction_multiple_le_max corr ν he
  omega

lemma main_copy_ne_correction {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (ν : Fin corr.t) {j h e : ℕ} (hj : md.J ≤ j)
    (hh : h ∈ ({1, 2, 3, 6} : Finset ℕ))
    (he : e ∈ insert 1 (corr.G ν)) :
    h * D j ≠ e * corr.c ν := by
  intro h_eq
  exact corr.no_main_collision ν j hj h hh e he h_eq.symm

lemma filler_ne_main_copy {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} {corr : CorrectionData p hp gcd}
    (fill : FillerData p hp corr) {f j h : ℕ}
    (hf : f ∈ fill.F) (hj : md.J ≤ j)
    (hh : h ∈ ({1, 2, 3, 6} : Finset ℕ)) :
    fill.Λ * f ≠ h * D j :=
  fill.hF_distinct_from_main_corr.1 f hf j hj h hh

lemma filler_ne_correction {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} {corr : CorrectionData p hp gcd}
    (fill : FillerData p hp corr) {f : ℕ}
    (hf : f ∈ fill.F) (ν : Fin corr.t) {e : ℕ}
    (he : e ∈ insert 1 (corr.G ν)) :
    fill.Λ * f ≠ e * corr.c ν :=
  fill.hF_distinct_from_main_corr.2 f hf ν e he

lemma mainSwitchedIndex_denom_injective (S : Finset ℕ) :
    Function.Injective (fun sw : MainSwitchedIndex S => sw.2.1) := by
  intro a b hab
  rcases a with ⟨⟨ja, hjaS⟩, ⟨na, hna⟩⟩
  rcases b with ⟨⟨jb, hjbS⟩, ⟨nb, hnb⟩⟩
  dsimp at hab ⊢
  simp only [scaledPatternDenoms, Finset.mem_image] at hna hnb
  obtain ⟨ea, hea, hea_eq⟩ := hna
  obtain ⟨eb, heb, heb_eq⟩ := hnb
  have hea_main : ea ∈ ({1, 2, 3, 6} : Finset ℕ) := by
    fin_cases hea <;> simp
  have heb_main : eb ∈ ({1, 2, 3, 6} : Finset ℕ) := by
    fin_cases heb <;> simp
  have hmul : ea * D ja = eb * D jb := by
    rw [hea_eq, heb_eq]
    exact hab
  have hcopy := main_copy_eq_of_eq hea_main heb_main hmul
  have hjab : ja = jb := hcopy.2
  subst jb
  subst nb
  rfl

lemma mainUnswitchedIndex_denom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} (md : MainChoice α L p hp) (N : ℕ)
    (S : Finset ℕ) :
    Function.Injective (fun j : MainUnswitchedIndex md N S => D j.1) := by
  intro a b hab
  apply Subtype.ext
  exact D_injective hab

lemma fillerIndex_denom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} {corr : CorrectionData p hp gcd}
    (fill : FillerData p hp corr) :
    Function.Injective (fun f : FillerIndex fill => fill.Λ * f.1) := by
  intro a b hab
  apply Subtype.ext
  have hΛ_pos : 0 < fill.Λ := lt_of_le_of_lt (Nat.zero_le L) fill.hΛ_gt_L
  exact Nat.mul_left_cancel hΛ_pos hab

lemma correctionUnswitchedIndex_denom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :
    Function.Injective (fun ν : CorrectionUnswitchedIndex corr T => corr.c ν.1) := by
  intro a b hab
  by_cases hν : a.1 = b.1
  · exact Subtype.ext hν
  · exfalso
    have hne := corr.no_corr_collision a.1 b.1 hν
      1 (Finset.mem_insert_self 1 (corr.G a.1))
      1 (Finset.mem_insert_self 1 (corr.G b.1))
    apply hne
    simpa using hab

lemma correctionSwitchedIndex_denom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :
    Function.Injective (fun sw : CorrectionSwitchedIndex corr T => sw.2.1) := by
  intro a b hab
  rcases a with ⟨⟨νa, hνaT⟩, ⟨na, hna⟩⟩
  rcases b with ⟨⟨νb, hνbT⟩, ⟨nb, hnb⟩⟩
  dsimp at hab ⊢
  simp only [scaledPatternDenoms, Finset.mem_image] at hna hnb
  obtain ⟨ea, hea, hea_eq⟩ := hna
  obtain ⟨eb, heb, heb_eq⟩ := hnb
  by_cases hν : νa = νb
  · subst νb
    subst nb
    rfl
  · exfalso
    have hmul : ea * corr.c νa = eb * corr.c νb := by
      rw [hea_eq, heb_eq]
      exact hab
    exact corr.no_corr_collision νa νb hν ea (Finset.mem_insert_of_mem hea)
      eb (Finset.mem_insert_of_mem heb) hmul

lemma mainSwitchedIndex_copy (S : Finset ℕ) (sw : MainSwitchedIndex S) :
    ∃ h : ℕ, h ∈ E0 ∧ h ∈ ({1, 2, 3, 6} : Finset ℕ) ∧
      sw.2.1 = h * D sw.1.1 := by
  have hn := sw.2.2
  simp only [scaledPatternDenoms, Finset.mem_image] at hn
  obtain ⟨h, hhE, hhn⟩ := hn
  refine ⟨h, hhE, ?_, hhn.symm⟩
  fin_cases hhE <;> simp

lemma correctionSwitchedIndex_copy {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) (sw : CorrectionSwitchedIndex corr T) :
    ∃ e : ℕ, e ∈ corr.G sw.1.1 ∧ e ∈ insert 1 (corr.G sw.1.1) ∧
      sw.2.1 = e * corr.c sw.1.1 := by
  have hn := sw.2.2
  simp only [scaledPatternDenoms, Finset.mem_image] at hn
  obtain ⟨e, heG, hen⟩ := hn
  exact ⟨e, heG, Finset.mem_insert_of_mem heG, hen.symm⟩

lemma finalIndexDenom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (fill : FillerData p hp corr) {N : ℕ} {S : Finset ℕ}
    {T : Finset (Fin corr.t)}
    (hS : S ⊆ Finset.Icc md.J N)
    (hτ : correctionMultiplierMax corr < tau N) :
    Function.Injective
      (finalIndexDenom :
        FinalIndex corr fill N S T → ℕ) := by
  classical
  intro a b hab
  rcases a with (((aj | asw) | atau) | ((acu | acsw) | af))
  <;> rcases b with (((bj | bsw) | btau) | ((bcu | bcsw) | bf))
  <;> dsimp [finalIndexDenom] at hab ⊢
  · congr
    apply Subtype.ext
    exact D_injective hab
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S bsw
    have hcopy := main_copy_eq_of_eq (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      hh (by simpa [hval] using hab : 1 * D aj.1 = h * D bsw.1.1)
    have haj_notS : aj.1 ∉ S := (Finset.mem_sdiff.mp aj.2).2
    exact haj_notS (by simpa [← hcopy.2] using bsw.1.2)
  · exfalso
    exact main_copy_ne_tau (h := 1) (j := aj.1) (N := N)
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa using hab)
  · exfalso
    have hajJ : md.J ≤ aj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp aj.2).1).1
    exact main_copy_ne_correction corr bcu.1 (j := aj.1) (h := 1) (e := 1)
      hajJ (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (Finset.mem_insert_self 1 (corr.G bcu.1)) (by simpa using hab)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T bcsw
    have hajJ : md.J ≤ aj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp aj.2).1).1
    exact main_copy_ne_correction corr bcsw.1.1 (j := aj.1) (h := 1) (e := e)
      hajJ (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ)) he
      (by simpa [hval] using hab)
  · exfalso
    have hajJ : md.J ≤ aj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp aj.2).1).1
    exact filler_ne_main_copy fill bf.2 hajJ
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa using hab.symm)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S asw
    have hcopy := main_copy_eq_of_eq hh
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa [hval] using hab : h * D asw.1.1 = 1 * D bj.1)
    have hbj_notS : bj.1 ∉ S := (Finset.mem_sdiff.mp bj.2).2
    exact hbj_notS (by simpa [hcopy.2] using asw.1.2)
  · congr
    exact mainSwitchedIndex_denom_injective S hab
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S asw
    exact main_copy_ne_tau (h := h) (j := asw.1.1) (N := N) hh
      (by simpa [hval] using hab)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S asw
    have haswJ : md.J ≤ asw.1.1 := (Finset.mem_Icc.mp (hS asw.1.2)).1
    exact main_copy_ne_correction corr bcu.1 (j := asw.1.1) (h := h) (e := 1)
      haswJ hh (Finset.mem_insert_self 1 (corr.G bcu.1))
      (by simpa [hval] using hab)
  · exfalso
    obtain ⟨h, _hhE, hh, hval_main⟩ := mainSwitchedIndex_copy S asw
    obtain ⟨e, _heG, he, hval_corr⟩ := correctionSwitchedIndex_copy corr T bcsw
    have haswJ : md.J ≤ asw.1.1 := (Finset.mem_Icc.mp (hS asw.1.2)).1
    exact main_copy_ne_correction corr bcsw.1.1 (j := asw.1.1) (h := h) (e := e)
      haswJ hh he (by simpa [hval_main, hval_corr] using hab)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S asw
    have haswJ : md.J ≤ asw.1.1 := (Finset.mem_Icc.mp (hS asw.1.2)).1
    exact filler_ne_main_copy fill bf.2 haswJ hh
      (by simpa [hval] using hab.symm)
  · exfalso
    exact main_copy_ne_tau (h := 1) (j := bj.1) (N := N)
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa using hab.symm)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S bsw
    exact main_copy_ne_tau (h := h) (j := bsw.1.1) (N := N) hh
      (by simpa [hval] using hab.symm)
  · exfalso
    exact correction_multiple_ne_tau_of_max_lt corr hτ bcu.1
      (Finset.mem_insert_self 1 (corr.G bcu.1)) (by simpa using hab.symm)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T bcsw
    exact correction_multiple_ne_tau_of_max_lt corr hτ bcsw.1.1 he
      (by simpa [hval] using hab.symm)
  · exfalso
    have hΛ_pos : 1 ≤ fill.Λ :=
      Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le L) fill.hΛ_gt_L)
    exact filler_ne_tau fill.hΛ_div_8 hΛ_pos (fill.hF_pos bf.1 bf.2)
      (by simpa using hab.symm)
  · exfalso
    have hbjJ : md.J ≤ bj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp bj.2).1).1
    exact main_copy_ne_correction corr acu.1 (j := bj.1) (h := 1) (e := 1)
      hbjJ (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (Finset.mem_insert_self 1 (corr.G acu.1)) (by simpa using hab.symm)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S bsw
    have hbswJ : md.J ≤ bsw.1.1 := (Finset.mem_Icc.mp (hS bsw.1.2)).1
    exact main_copy_ne_correction corr acu.1 (j := bsw.1.1) (h := h) (e := 1)
      hbswJ hh (Finset.mem_insert_self 1 (corr.G acu.1))
      (by simpa [hval] using hab.symm)
  · exfalso
    exact correction_multiple_ne_tau_of_max_lt corr hτ acu.1
      (Finset.mem_insert_self 1 (corr.G acu.1)) (by simpa using hab)
  · congr
    exact correctionUnswitchedIndex_denom_injective corr T hab
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T bcsw
    by_cases hν : acu.1 = bcsw.1.1
    · have hacu_notT : acu.1 ∉ T := (Finset.mem_sdiff.mp acu.2).2
      exact hacu_notT (by simpa [← hν] using bcsw.1.2)
    · exact corr.no_corr_collision acu.1 bcsw.1.1 hν 1
        (Finset.mem_insert_self 1 (corr.G acu.1)) e he
        (by simpa [hval] using hab)
  · exfalso
    exact filler_ne_correction fill bf.2 acu.1
      (Finset.mem_insert_self 1 (corr.G acu.1)) (by simpa using hab.symm)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T acsw
    have hbjJ : md.J ≤ bj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp bj.2).1).1
    exact main_copy_ne_correction corr acsw.1.1 (j := bj.1) (h := 1) (e := e)
      hbjJ (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ)) he
      (by simpa [hval] using hab.symm)
  · exfalso
    obtain ⟨e, _heG, he, hval_corr⟩ := correctionSwitchedIndex_copy corr T acsw
    obtain ⟨h, _hhE, hh, hval_main⟩ := mainSwitchedIndex_copy S bsw
    have hbswJ : md.J ≤ bsw.1.1 := (Finset.mem_Icc.mp (hS bsw.1.2)).1
    exact main_copy_ne_correction corr acsw.1.1 (j := bsw.1.1) (h := h) (e := e)
      hbswJ hh he (by simpa [hval_corr, hval_main] using hab.symm)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T acsw
    exact correction_multiple_ne_tau_of_max_lt corr hτ acsw.1.1 he
      (by simpa [hval] using hab)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T acsw
    by_cases hν : acsw.1.1 = bcu.1
    · have hbcu_notT : bcu.1 ∉ T := (Finset.mem_sdiff.mp bcu.2).2
      exact hbcu_notT (by simpa [hν] using acsw.1.2)
    · exact corr.no_corr_collision acsw.1.1 bcu.1 hν e he 1
        (Finset.mem_insert_self 1 (corr.G bcu.1))
        (by simpa [hval] using hab)
  · congr
    exact correctionSwitchedIndex_denom_injective corr T hab
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T acsw
    exact filler_ne_correction fill bf.2 acsw.1.1 he
      (by simpa [hval] using hab.symm)
  · exfalso
    have hbjJ : md.J ≤ bj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp bj.2).1).1
    exact filler_ne_main_copy fill af.2 hbjJ
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa using hab)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S bsw
    have hbswJ : md.J ≤ bsw.1.1 := (Finset.mem_Icc.mp (hS bsw.1.2)).1
    exact filler_ne_main_copy fill af.2 hbswJ hh
      (by simpa [hval] using hab)
  · exfalso
    have hΛ_pos : 1 ≤ fill.Λ :=
      Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le L) fill.hΛ_gt_L)
    exact filler_ne_tau fill.hΛ_div_8 hΛ_pos (fill.hF_pos af.1 af.2)
      (by simpa using hab)
  · exfalso
    exact filler_ne_correction fill af.2 bcu.1
      (Finset.mem_insert_self 1 (corr.G bcu.1)) (by simpa using hab)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T bcsw
    exact filler_ne_correction fill af.2 bcsw.1.1 he
      (by simpa [hval] using hab)
  · congr
    exact fillerIndex_denom_injective fill hab

lemma mainUnswitchedIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ j : MainUnswitchedIndex md N S, f j.1) =
      ∑ j ∈ Finset.Icc md.J N \ S, f j := by
  rw [← Finset.sum_attach (Finset.Icc md.J N \ S) f]
  rfl

lemma mainSwitchedIndex_sum (S : Finset ℕ)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ sw : MainSwitchedIndex S, f sw.2.1) =
      ∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), f n := by
  rw [← Finset.univ_sigma_univ]
  rw [Finset.sum_sigma]
  rw [← Finset.sum_attach S
    (fun j => ∑ n ∈ scaledPatternDenoms E0 (D j), f n)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_attach (scaledPatternDenoms E0 (D j.1)) f]
  rfl

lemma correctionUnswitchedIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) {M : Type*} [AddCommMonoid M]
    (f : Fin corr.t → M) :
    (∑ ν : CorrectionUnswitchedIndex corr T, f ν.1) =
      ∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T, f ν := by
  rw [← Finset.sum_attach ((Finset.univ : Finset (Fin corr.t)) \ T) f]
  rfl

lemma correctionSwitchedIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) :
    (∑ sw : CorrectionSwitchedIndex corr T, f sw.2.1) =
      ∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν), f n := by
  rw [← Finset.univ_sigma_univ]
  rw [Finset.sum_sigma]
  rw [← Finset.sum_attach T
    (fun ν => ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν), f n)]
  apply Finset.sum_congr rfl
  intro ν _
  rw [← Finset.sum_attach (scaledPatternDenoms (corr.G ν.1) (corr.c ν.1)) f]
  rfl

lemma fillerIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} (fill : FillerData p hp corr)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ x : FillerIndex fill, f x.1) =
      ∑ x ∈ fill.F, f x := by
  rw [← Finset.sum_attach fill.F f]
  rfl

lemma finalIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N : ℕ) (S : Finset ℕ) (T : Finset (Fin corr.t))
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ i : FinalIndex corr fill N S T, f (finalIndexDenom i)) =
      ((∑ j ∈ Finset.Icc md.J N \ S, f (D j)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), f n) +
        f (tau N)) +
      ((∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T, f (corr.c ν)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν), f n)) +
      (∑ x ∈ fill.F, f (fill.Λ * x)) := by
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp only [finalIndexDenom]
  rw [mainUnswitchedIndex_sum md N S (fun x => f (D x))]
  rw [mainSwitchedIndex_sum S f]
  rw [show (∑ _x : PUnit, f (tau N)) = f (tau N) by simp]
  rw [correctionUnswitchedIndex_sum corr T (fun ν => f (corr.c ν))]
  rw [correctionSwitchedIndex_sum corr T f]
  rw [fillerIndex_sum fill (fun x => f (fill.Λ * x))]
  ac_rfl

lemma main_indexed_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) {N : ℕ} {S : Finset ℕ}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N) :
    (∑ j ∈ Finset.Icc md.J N \ S, (1 : ℚ) / (D j : ℚ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), (1 : ℚ) / (n : ℚ)) +
        (1 : ℚ) / (tau N : ℚ) =
      (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) := by
  have hD_pos : ∀ j : ℕ, 0 < D j := by
    intro j
    unfold D u P
    positivity
  calc
    (∑ j ∈ Finset.Icc md.J N \ S, (1 : ℚ) / (D j : ℚ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), (1 : ℚ) / (n : ℚ)) +
        (1 : ℚ) / (tau N : ℚ)
        = (∑ j ∈ Finset.Icc md.J N \ S, (1 : ℚ) / (D j : ℚ)) +
            (∑ j ∈ S, (1 : ℚ) / (D j : ℚ)) +
            (1 : ℚ) / (tau N : ℚ) := by
              congr 2
              apply Finset.sum_congr rfl
              intro j _
              exact scaledPatternDenoms_sum_recip isEgyptianPattern_E0 (hD_pos j)
    _ = (∑ j ∈ Finset.Icc md.J N, (1 : ℚ) / (D j : ℚ)) +
            (1 : ℚ) / (tau N : ℚ) := by
              rw [Finset.sum_sdiff hS]
    _ = (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) := by
              rw [main_telescoping md.J N hJN]
              ring

lemma main_indexed_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (md : MainChoice α L p hp) {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc md.J N) :
    (∑ j ∈ Finset.Icc md.J N \ S, intEval p hp ((D j : ℕ) : ℤ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j),
          intEval p hp ((n : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ) =
      (∑ j ∈ Finset.Icc md.J N, intEval p hp ((D j : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ) +
        (∑ j ∈ S,
          intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)) := by
  let base : ℕ → ℤ := fun j => intEval p hp ((D j : ℕ) : ℤ)
  let inc : ℕ → ℤ := fun j =>
    intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)
  have hswitch : ∀ j ∈ S,
      (∑ n ∈ scaledPatternDenoms E0 (D j), intEval p hp ((n : ℕ) : ℤ)) =
        base j + inc j := by
    intro j _
    have h := main_slot_switch_intEval_sum p hp j
    dsimp [base, inc]
    omega
  calc
    (∑ j ∈ Finset.Icc md.J N \ S, intEval p hp ((D j : ℕ) : ℤ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j),
          intEval p hp ((n : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ)
        = (∑ j ∈ Finset.Icc md.J N \ S, base j) +
            (∑ j ∈ S, (base j + inc j)) +
            intEval p hp ((tau N : ℕ) : ℤ) := by
              congr 2
              apply Finset.sum_congr rfl
              intro j hj
              exact hswitch j hj
    _ = (∑ j ∈ Finset.Icc md.J N, base j) +
          intEval p hp ((tau N : ℕ) : ℤ) +
          (∑ j ∈ S, inc j) := by
            rw [Finset.sum_add_distrib]
            have hbase :
                (∑ j ∈ Finset.Icc md.J N \ S, base j) +
                  (∑ j ∈ S, base j) =
                    ∑ j ∈ Finset.Icc md.J N, base j :=
              Finset.sum_sdiff hS
            linarith
    _ = (∑ j ∈ Finset.Icc md.J N, intEval p hp ((D j : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ) +
        (∑ j ∈ S,
          intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)) := rfl

lemma correction_indexed_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    {T : Finset (Fin corr.t)} (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
        (1 : ℚ) / (corr.c ν : ℚ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          (1 : ℚ) / (n : ℚ)) =
      ∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ) := by
  calc
    (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
        (1 : ℚ) / (corr.c ν : ℚ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          (1 : ℚ) / (n : ℚ))
        = (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
            (1 : ℚ) / (corr.c ν : ℚ)) +
            (∑ ν ∈ T, (1 : ℚ) / (corr.c ν : ℚ)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro ν _
              exact scaledPatternDenoms_sum_recip (corr.hG ν) (hcorr_pos ν)
    _ = ∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ) := by
              rw [Finset.sum_sdiff (Finset.subset_univ T)]

lemma correction_indexed_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    {T : Finset (Fin corr.t)} (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
        intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          intEval p hp ((n : ℕ) : ℤ)) =
      (∑ ν : Fin corr.t, intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, corr.b ν) := by
  let base : Fin corr.t → ℤ := fun ν => intEval p hp ((corr.c ν : ℕ) : ℤ)
  let inc : Fin corr.t → ℤ := fun ν => corr.b ν
  have hswitch : ∀ ν ∈ T,
      (∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          intEval p hp ((n : ℕ) : ℤ)) =
        base ν + inc ν := by
    intro ν _
    have h := correction_slot_switch_intEval_sum p hp corr ν (hcorr_pos ν)
    dsimp [base, inc]
    omega
  calc
    (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
        intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          intEval p hp ((n : ℕ) : ℤ))
        = (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T, base ν) +
            (∑ ν ∈ T, (base ν + inc ν)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro ν hν
              exact hswitch ν hν
    _ = (∑ ν : Fin corr.t, base ν) + (∑ ν ∈ T, inc ν) := by
            rw [Finset.sum_add_distrib]
            have hbase :
                (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T, base ν) +
                  (∑ ν ∈ T, base ν) =
                    ∑ ν : Fin corr.t, base ν :=
              Finset.sum_sdiff (Finset.subset_univ T)
            linarith
    _ = (∑ ν : Fin corr.t, intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, corr.b ν) := rfl

lemma filler_indexed_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} {corr : CorrectionData p hp gcd}
    (fill : FillerData p hp corr) :
    (∑ f ∈ fill.F, (1 : ℚ) / ((fill.Λ * f : ℕ) : ℚ)) =
      α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) -
      (∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ)) :=
  fill.hF_recip

lemma indexed_total_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N)
    (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    ((∑ j ∈ Finset.Icc md.J N \ S, (1 : ℚ) / (D j : ℚ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), (1 : ℚ) / (n : ℚ)) +
        (1 : ℚ) / (tau N : ℚ)) +
      ((∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
          (1 : ℚ) / (corr.c ν : ℚ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          (1 : ℚ) / (n : ℚ))) +
      (∑ f ∈ fill.F, (1 : ℚ) / ((fill.Λ * f : ℕ) : ℚ)) =
      α := by
  rw [main_indexed_recip_sum md hJN hS]
  rw [correction_indexed_recip_sum corr hcorr_pos]
  rw [filler_indexed_recip_sum fill]
  ring

lemma indexed_total_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hS : S ⊆ Finset.Icc md.J N) (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    ((∑ j ∈ Finset.Icc md.J N \ S, intEval p hp ((D j : ℕ) : ℤ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j),
          intEval p hp ((n : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ)) +
      ((∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
          intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          intEval p hp ((n : ℕ) : ℤ))) +
      (∑ f ∈ fill.F, intEval p hp (((fill.Λ * f : ℕ) : ℤ))) =
      baseInt p hp corr fill N +
        (∑ j ∈ S, intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)) +
        (∑ ν ∈ T, corr.b ν) := by
  rw [main_indexed_intEval_sum p hp md hS]
  rw [correction_indexed_intEval_sum p hp corr hcorr_pos]
  unfold baseInt
  ring

lemma finalIndex_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N)
    (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    (∑ i : FinalIndex corr fill N S T,
      (1 : ℚ) / (finalIndexDenom i : ℚ)) = α := by
  rw [finalIndex_sum corr fill N S T (fun n => (1 : ℚ) / (n : ℚ))]
  exact indexed_total_recip_sum corr fill hJN hS hcorr_pos

lemma finalIndex_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hS : S ⊆ Finset.Icc md.J N) (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    (∑ i : FinalIndex corr fill N S T,
      intEval p hp ((finalIndexDenom i : ℕ) : ℤ)) =
      baseInt p hp corr fill N +
        (∑ j ∈ S, intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)) +
        (∑ ν ∈ T, corr.b ν) := by
  rw [finalIndex_sum corr fill N S T
    (fun n => intEval p hp ((n : ℕ) : ℤ))]
  exact indexed_total_intEval_sum p hp corr fill hS hcorr_pos

lemma intEval_fintype_sum_cast (p : ℚ[X]) (hp : IntValued p)
    {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    ((∑ i : ι, intEval p hp ((d i : ℕ) : ℤ) : ℤ) : ℚ) =
      ∑ i : ι, p.eval ((d i : ℕ) : ℚ) := by
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [intEval_spec]
  rfl

lemma select_correction_and_main_subsets {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (fill : FillerData p hp corr) (X_q : ℤ) (N : ℕ) (U m : ℤ)
    (hlo :
      baseInt p hp corr fill N + Bstar p hp corr +
        M0 p hp gcd X_q ≤ m)
    (hhi : m ≤ baseInt p hp corr fill N + U)
    (hwindow : ∀ M : ℤ,
      M0 p hp gcd X_q ≤ M →
      M ≤ U →
      (gcd.g : ℤ) ∣ M →
      ∃ S : Finset ℕ, S ⊆ Finset.Icc md.J N ∧
        (M : ℚ) =
          ∑ j ∈ S,
            ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) :
    ∃ T : Finset (Fin corr.t), ∃ S : Finset ℕ,
      S ⊆ Finset.Icc md.J N ∧
      (m : ℚ) =
        (baseInt p hp corr fill N : ℚ) +
        (∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) +
        (∑ ν ∈ T, ((corr.b ν : ℤ) : ℚ)) := by
  classical
  obtain ⟨T, hT_dvd, hT_nonneg, hT_le⟩ :=
    correction_subset_dvd_with_bounds p hp corr (m - baseInt p hp corr fill N)
  set Δ : ℤ := ∑ ν ∈ T, corr.b ν with hΔ_def
  set M : ℤ := m - baseInt p hp corr fill N - Δ with hM_def
  have hM_dvd : (gcd.g : ℤ) ∣ M := by
    simpa [M, hM_def, Δ, hΔ_def, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hT_dvd
  have hM_lo : M0 p hp gcd X_q ≤ M := by
    rw [hM_def, hΔ_def]
    linarith [hlo, hT_le]
  have hM_hi : M ≤ U := by
    rw [hM_def, hΔ_def]
    linarith [hhi, hT_nonneg]
  obtain ⟨S, hS, hSsum⟩ := hwindow M hM_lo hM_hi hM_dvd
  refine ⟨T, S, hS, ?_⟩
  rw [← hSsum]
  rw [hM_def, hΔ_def]
  push_cast
  ring

lemma main_window_integer_subset {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (X_q : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (N : ℕ) (hJN : md.J ≤ N)
    (U : ℤ)
    (h_tail : ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ U →
      ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (M : ℤ) (hM0 : M0 p hp gcd X_q ≤ M) (hMle : M ≤ U)
    (hdiv : (gcd.g : ℤ) ∣ M) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc md.J N ∧
      (M : ℚ) =
        ∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ) := by
  obtain ⟨X, hX⟩ := hdiv
  have hg_pos_int : (0 : ℤ) < (gcd.g : ℤ) := by
    exact_mod_cast gcd.hg_pos
  have hX_ge : X_q ≤ X := by
    have hle_gXq : ((gcd.g : ℤ) * X_q) ≤ M :=
      le_trans (M0_ge_g_mul_Xq p hp gcd X_q) hM0
    rw [hX] at hle_gXq
    nlinarith
  have hX_le_U : ((gcd.g : ℤ) * X) ≤ U := by
    rw [← hX]
    exact hMle
  obtain ⟨S, hS, hSsum⟩ :=
    main_window_finite p hp md gcd X_q X hX_q hX_ge N hJN
      (h_tail X hX_ge hX_le_U)
  refine ⟨S, hS, ?_⟩
  rw [← hSsum]
  rw [hX]
  push_cast
  ring

lemma select_subsets_from_rsg_interval {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (fill : FillerData p hp corr) (X_q : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (N : ℕ) (U m : ℤ) (hJN : md.J ≤ N)
    (h_tail : ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ U →
      ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (hlo :
      baseInt p hp corr fill N + Bstar p hp corr +
        M0 p hp gcd X_q ≤ m)
    (hhi : m ≤ baseInt p hp corr fill N + U) :
    ∃ T : Finset (Fin corr.t), ∃ S : Finset ℕ,
      S ⊆ Finset.Icc md.J N ∧
      (m : ℚ) =
        (baseInt p hp corr fill N : ℚ) +
        (∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) +
        (∑ ν ∈ T, ((corr.b ν : ℤ) : ℚ)) := by
  apply select_correction_and_main_subsets p hp corr fill X_q N U m hlo hhi
  intro M hM0 hMle hdiv
  exact main_window_integer_subset p hp gcd X_q hX_q N hJN U h_tail M hM0 hMle hdiv

lemma intEval_finset_sum_cast (p : ℚ[X]) (hp : IntValued p) (E : Finset ℕ) :
    ((∑ n ∈ E, intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) =
      ∑ n ∈ E, p.eval ((n : ℕ) : ℚ) := by
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [intEval_spec]
  rfl

lemma witness_of_denominator_finset (α : ℚ) (L m : ℕ) (p : ℚ[X])
    (E : Finset ℕ) (hE_nonempty : E.Nonempty)
    (hE_gt_L : ∀ n ∈ E, L < n)
    (hrecip : α = ∑ n ∈ E, (1 : ℚ) / (n : ℚ))
    (hsum : (m : ℚ) = ∑ n ∈ E, p.eval ((n : ℕ) : ℚ)) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  classical
  let c : ℕ := E.card
  have hc_pos : 1 ≤ c := by
    dsimp [c]
    exact Finset.card_pos.mpr hE_nonempty
  let g : Fin c ↪o ℕ := E.orderEmbOfFin (by rfl : E.card = c)
  have hc_succ : c - 1 + 1 = c := Nat.sub_add_cancel hc_pos
  refine ⟨c - 1, fun i => g (Fin.cast hc_succ i), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply g.strictMono
    exact Fin.cast_lt_cast hc_succ |>.mpr hij
  · have h0_mem : g (Fin.cast hc_succ 0) ∈ E :=
      E.orderEmbOfFin_mem (by rfl : E.card = c) _
    exact hE_gt_L _ h0_mem
  · rw [hrecip]
    have h_image : Finset.image (⇑g) Finset.univ = E :=
      E.image_orderEmbOfFin_univ (by rfl : E.card = c)
    rw [← h_image]
    rw [Finset.sum_image (fun a _ b _ hab => g.injective hab)]
    symm
    apply Finset.sum_equiv (Fin.castOrderIso hc_succ).toEquiv
    · intro i
      simp
    · intro i _
      rfl
  · rw [hsum]
    have h_image : Finset.image (⇑g) Finset.univ = E :=
      E.image_orderEmbOfFin_univ (by rfl : E.card = c)
    rw [← h_image]
    rw [Finset.sum_image (fun a _ b _ hab => g.injective hab)]
    symm
    apply Finset.sum_equiv (Fin.castOrderIso hc_succ).toEquiv
    · intro i
      simp
    · intro i _
      rfl

lemma witness_of_fintype_denominators (α : ℚ) (L m : ℕ) (p : ℚ[X])
    {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℕ)
    (hd_inj : Function.Injective d) (hd_gt_L : ∀ i, L < d i)
    (hrecip : α = ∑ i : ι, (1 : ℚ) / (d i : ℚ))
    (hsum : (m : ℚ) = ∑ i : ι, p.eval ((d i : ℕ) : ℚ)) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  classical
  let E : Finset ℕ := Finset.univ.image d
  have hE_nonempty : E.Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨d i, by simp [E]⟩
  have hE_gt_L : ∀ n ∈ E, L < n := by
    intro n hn
    simp [E] at hn
    obtain ⟨i, _, rfl⟩ := hn
    exact hd_gt_L i
  have hE_recip : α = ∑ n ∈ E, (1 : ℚ) / (n : ℚ) := by
    rw [hrecip]
    dsimp [E]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hd_inj hab
  have hE_sum : (m : ℚ) = ∑ n ∈ E, p.eval ((n : ℕ) : ℚ) := by
    rw [hsum]
    dsimp [E]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hd_inj hab
  exact witness_of_denominator_finset α L m p E hE_nonempty hE_gt_L hE_recip hE_sum

lemma witness_from_selected_subsets {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (fill : FillerData p hp corr) {N m : ℕ}
    {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N)
    (hcorr_pos : ∀ ν, 0 < corr.c ν)
    (hden_inj :
      Function.Injective
        (finalIndexDenom :
          FinalIndex corr fill N S T → ℕ))
    (hden_gt_L :
      ∀ i : FinalIndex corr fill N S T, L < finalIndexDenom i)
    (hpsum :
      (m : ℚ) =
        (baseInt p hp corr fill N : ℚ) +
        (∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) +
        (∑ ν ∈ T, ((corr.b ν : ℤ) : ℚ))) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  classical
  haveI : Nonempty (FinalIndex corr fill N S T) :=
    ⟨Sum.inl (Sum.inr PUnit.unit)⟩
  have hrecip : α = ∑ i : FinalIndex corr fill N S T,
      (1 : ℚ) / (finalIndexDenom i : ℚ) := by
    exact (finalIndex_recip_sum corr fill hJN hS hcorr_pos).symm
  have hp_eval_sum :
      (m : ℚ) = ∑ i : FinalIndex corr fill N S T,
        p.eval ((finalIndexDenom i : ℕ) : ℚ) := by
    rw [← intEval_fintype_sum_cast p hp
      (finalIndexDenom : FinalIndex corr fill N S T → ℕ)]
    rw [finalIndex_intEval_sum p hp corr fill hS hcorr_pos]
    push_cast
    exact hpsum
  exact witness_of_fintype_denominators α L m p
    (finalIndexDenom : FinalIndex corr fill N S T → ℕ)
    hden_inj hden_gt_L hrecip hp_eval_sum

lemma finalIndex_denoms_gt_L {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N) :
    ∀ i : FinalIndex corr fill N S T, L < finalIndexDenom i := by
  intro i
  rcases i with (((j | sw) | tauIdx) | ((ν | csw) | f))
  · -- Unswitched main denominator `D j`.
    have hj_mem : j.1 ∈ Finset.Icc md.J N := by
      exact (Finset.mem_sdiff.mp j.2).1
    have hjJ : md.J ≤ j.1 := (Finset.mem_Icc.mp hj_mem).1
    have hDj_ge : D md.J ≤ D j.1 := D_strictMono.monotone hjJ
    exact lt_of_lt_of_le md.hD_gt_L hDj_ge
  · -- Switched main denominator `n ∈ {2D j,3D j,6D j}`.
    have hj_mem : sw.1.1 ∈ Finset.Icc md.J N := hS sw.1.2
    have hjJ : md.J ≤ sw.1.1 := (Finset.mem_Icc.mp hj_mem).1
    have hDj_ge : D md.J ≤ D sw.1.1 := D_strictMono.monotone hjJ
    have hDj_gt : L < D sw.1.1 := lt_of_lt_of_le md.hD_gt_L hDj_ge
    have hn_mem := sw.2.2
    simp only [scaledPatternDenoms, Finset.mem_image] at hn_mem
    obtain ⟨e, he, heq⟩ := hn_mem
    have he_one : 1 ≤ e := by
      have he_two := (isEgyptianPattern_E0.1 e he)
      omega
    change L < sw.2.1
    rw [← heq]
    calc
      L < D sw.1.1 := hDj_gt
      _ = 1 * D sw.1.1 := by ring
      _ ≤ e * D sw.1.1 := Nat.mul_le_mul_right _ he_one
  · -- Endpoint `τ N`.
    have htau_ge : tau md.J ≤ tau N := tau_strictMono.monotone hJN
    exact lt_of_lt_of_le md.htau_base_gt_L htau_ge
  · -- Unswitched correction denominator `cν`.
    exact corr.c_gt_L ν.1
  · -- Switched correction denominator `n ∈ scaledPatternDenoms Gν cν`.
    have hc_gt : L < corr.c csw.1.1 := corr.c_gt_L csw.1.1
    have hn_mem := csw.2.2
    simp only [scaledPatternDenoms, Finset.mem_image] at hn_mem
    obtain ⟨e, he, heq⟩ := hn_mem
    have he_one : 1 ≤ e := by
      have he_two := (corr.hG csw.1.1).1 e he
      omega
    change L < csw.2.1
    rw [← heq]
    calc
      L < corr.c csw.1.1 := hc_gt
      _ = 1 * corr.c csw.1.1 := by ring
      _ ≤ e * corr.c csw.1.1 := Nat.mul_le_mul_right _ he_one
  · -- Filler denominator `Λ f`.
    have hf_one : 1 ≤ f.1 := fill.hF_pos f.1 f.2
    calc
      L < fill.Λ := fill.hΛ_gt_L
      _ = fill.Λ * 1 := by ring
      _ ≤ fill.Λ * f.1 := Nat.mul_le_mul_left _ hf_one

lemma attainable_interval_core {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (X_q : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (N m : ℕ) (U : ℤ) (hJN : md.J ≤ N)
    (h_tail : ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ U →
      ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (hlo :
      baseInt p hp corr fill N + Bstar p hp corr +
        M0 p hp gcd X_q ≤ (m : ℤ))
    (hhi : (m : ℤ) ≤ baseInt p hp corr fill N + U)
    (hcollision : ∀ (T : Finset (Fin corr.t)) (S : Finset ℕ),
      S ⊆ Finset.Icc md.J N →
      Function.Injective
        (finalIndexDenom :
          FinalIndex corr fill N S T → ℕ)) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  classical
  obtain ⟨T, S, hS, hpsum⟩ :=
    select_subsets_from_rsg_interval p hp corr fill X_q hX_q N U (m : ℤ)
      hJN h_tail hlo hhi
  have hcorr_pos : ∀ ν, 0 < corr.c ν := by
    intro ν
    exact lt_of_le_of_lt (Nat.zero_le L) (corr.c_gt_L ν)
  have hpsum_nat :
      (m : ℚ) =
        (baseInt p hp corr fill N : ℚ) +
        (∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) +
        (∑ ν ∈ T, ((corr.b ν : ℤ) : ℚ)) := by
    exact_mod_cast hpsum
  exact witness_from_selected_subsets p hp corr fill hJN hS hcorr_pos
    (hcollision T S hS) (finalIndex_denoms_gt_L corr fill hJN hS) hpsum_nat

lemma attainable_interval {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (X_q : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (N m : ℕ) (U : ℤ) (hJN : md.J ≤ N)
    (hτ : correctionMultiplierMax corr < tau N)
    (h_tail : ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ U →
      ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (hlo :
      baseInt p hp corr fill N + Bstar p hp corr +
        M0 p hp gcd X_q ≤ (m : ℤ))
    (hhi : (m : ℤ) ≤ baseInt p hp corr fill N + U) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  exact attainable_interval_core p hp corr fill X_q hX_q N m U hJN h_tail hlo hhi
    (fun T S hS => finalIndexDenom_injective corr fill hS hτ)

lemma integer_intervals_cover_tail (lo hi : ℕ → ℤ) (N₀ : ℕ)
    (hoverlap : ∀ N, N₀ ≤ N → lo (N + 1) ≤ hi N + 1)
    (hhi_unbounded : ∀ m : ℤ, ∃ N, N₀ ≤ N ∧ m ≤ hi N) :
    ∀ m : ℤ, lo N₀ ≤ m →
      ∃ N, N₀ ≤ N ∧ lo N ≤ m ∧ m ≤ hi N := by
  classical
  intro m hmlo
  let P : ℕ → Prop := fun N => N₀ ≤ N ∧ m ≤ hi N
  have hP : ∃ N, P N := hhi_unbounded m
  let N : ℕ := Nat.find hP
  have hN : P N := Nat.find_spec hP
  by_cases hbase : N = N₀
  · refine ⟨N, hN.1, ?_, hN.2⟩
    simpa [hbase] using hmlo
  · have hN₀_lt : N₀ < N := lt_of_le_of_ne hN.1 (Ne.symm hbase)
    let K : ℕ := N - 1
    have hK_succ : K + 1 = N := by
      dsimp [K]
      have hN_pos : 0 < N := lt_of_le_of_lt (Nat.zero_le N₀) hN₀_lt
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hN_pos)
    have hK_lt : K < N := by
      rw [← hK_succ]
      exact Nat.lt_succ_self K
    have hK_ge : N₀ ≤ K := by
      rw [← hK_succ] at hN₀_lt
      omega
    have hnotK : ¬ P K := Nat.find_min hP hK_lt
    have hhiK_lt : hi K < m := by
      by_contra hle
      push_neg at hle
      exact hnotK ⟨hK_ge, hle⟩
    have hloN : lo N ≤ hi K + 1 := by
      rw [← hK_succ]
      exact hoverlap K hK_ge
    have hle_m : hi K + 1 ≤ m := by omega
    refine ⟨N, hN.1, ?_, hN.2⟩
    exact le_trans hloN hle_m

/-! ### Quotient-gcd bridge reference statement

If `g` is the positive generator of `Ideal.span (mainValueSet p hp md.J)`,
then the quotient values `(qPoly p md.J g).eval (t : ℚ)` (for `t ≥ 1`)
generate the unit ideal in `ℤ`. Equivalently, no prime `ℓ` divides every
quotient value.

Mathematically: `g = gcd { A(D j) : j ≥ J }` by construction. Dividing the
spanning set by `g` gives values whose gcd is 1, so no prime divides them
all. RSG's `h_gcd_one` hypothesis is exactly this.

The full proof is implemented in `chooseMainGCDData`; the definition below
keeps the target statement shape available by name. -/
section MainQuotBridge

variable {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)

/-- Statement-shape for the quotient-gcd bridge proved inside
`chooseMainGCDData`. -/
def mainQuot_no_prime_fixed_stmt (md : MainChoice α L p hp) (g : ℕ)
    (_ : 1 ≤ g) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime →
    ∃ t : ℕ, 1 ≤ t ∧ ∃ z : ℤ,
      (z : ℚ) = (qPoly p md.J g).eval (t : ℚ) ∧
      ¬ ((ℓ : ℤ) ∣ z)

end MainQuotBridge

set_option linter.unusedVariables false in
/-- **Main theorem (PDF Theorem 1).** For `α ∈ ℚ_{>0}`, `L ≥ 1`, and a polynomial
`p ∈ ℚ[x]` integer-valued with positive leading coefficient and no fixed
divisor on positive integers, all sufficiently large integers `m` admit an
expression as `∑ p(n_i)` with distinct `L < n_1 < ⋯ < n_k` and `∑ 1/n_i = α`.

The proof combines:
  * `egyptian_expansion` (Lemma 3) for filler denominators
  * `egyptian_pattern_with_period` (Lemma 4) used by Lemma 6
  * `polynomial_periodicity` (Lemma 5) used by Lemma 6 and the correction slots
  * `switching_values_span_top` (Lemma 6) for the residue-correction trick
  * `roth_szekeres_graham` applied to `q := A ∘ Dpoly / g`
  * Telescoping `D j` reciprocals via `main_telescoping`
  * Collision avoidance via `padicValNat` profiles

with the explicit constants `P := 36`, `D j := u j · u (j+1)`, `u j := P j + 1`,
`τ N := P u_{N+1}`, `E0 := {2, 3, 6}`, `A := switchingPoly p E0`. -/
theorem theorem_1 (α : ℚ) (hα : 0 < α) (L : ℕ) (hL : 1 ≤ L) (p : ℚ[X])
    (hp : IntValued p)
    (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : NoFixedDivisor p hp) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
        StrictMono n ∧ (L < n 0) ∧
        (α = ∑ i, (1 : ℚ) / (n i)) ∧
        ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  by_cases hd : p.natDegree = 0
  case pos =>
    -- CONSTANT CASE: p = C c with c = 1 (forced by NoFixedDivisor).
    -- Reduce to egyptian_expansion.
    -- Step 1: p = C (p.coeff 0).
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
    -- Step 2: leading coefficient is p.coeff 0.
    have h_lead_eq : p.leadingCoeff = p.coeff 0 := by
      rw [Polynomial.leadingCoeff, hd]
    have h_c_pos : 0 < p.coeff 0 := h_lead_eq ▸ h_lead_pos
    set c : ℚ := p.coeff 0 with hc_def
    -- Step 3: p.eval z = c for all z.
    have h_eval_const : ∀ z : ℚ, p.eval z = c := by
      intro z; rw [hpC]; simp
    -- Step 4: extract integer value c_int with (c_int : ℚ) = c.
    obtain ⟨c_int, hc_int⟩ := hp 0
    have h_eval_zero : p.eval ((0 : ℤ) : ℚ) = c := h_eval_const _
    have hc_int_eq : (c_int : ℚ) = c := by rw [hc_int, h_eval_zero]
    have h_intEval_const : ∀ z : ℤ, intEval p hp z = c_int := by
      intro z
      have h1 : ((intEval p hp z : ℤ) : ℚ) = p.eval (z : ℚ) := intEval_spec p hp z
      have h2 : p.eval ((z : ℤ) : ℚ) = c := h_eval_const _
      have h3 : ((intEval p hp z : ℤ) : ℚ) = (c_int : ℚ) := by rw [h1, h2, hc_int_eq]
      exact_mod_cast h3
    have h_c_int_pos : 0 < c_int := by
      have : (0 : ℚ) < (c_int : ℚ) := by rw [hc_int_eq]; exact h_c_pos
      exact_mod_cast this
    -- Step 5: c_int = 1, forced by NoFixedDivisor.
    have h_c_int_one : c_int = 1 := by
      by_contra h_ne
      have h_ge_two : 2 ≤ c_int := by
        rcases lt_or_ge c_int 2 with hlt | hge
        · interval_cases c_int
          · exact absurd rfl h_ne
        · exact hge
      set d : ℕ := c_int.toNat with hd_def
      have hd_eq : (d : ℤ) = c_int := Int.toNat_of_nonneg (le_of_lt h_c_int_pos)
      have hd_ge : 2 ≤ d := by
        have : (2 : ℤ) ≤ (d : ℤ) := by rw [hd_eq]; exact h_ge_two
        exact_mod_cast this
      apply h_no_fixed_div d hd_ge
      intro n _
      rw [h_intEval_const n, hd_eq]
    -- Step 6: p.eval z = 1 for all z (rational).
    have h_eval_one : ∀ z : ℚ, p.eval z = 1 := by
      intro z
      rw [h_eval_const z, ← hc_int_eq, h_c_int_one]
      simp
    -- Step 7: get K from egyptian_expansion.
    obtain ⟨K, hK⟩ := egyptian_expansion α hα L
    refine ⟨max K 1, ?_⟩
    intro m hm
    have hmK : K ≤ m := le_of_max_le_left hm
    have hm1 : 1 ≤ m := le_of_max_le_right hm
    obtain ⟨E, hE_card, hE_lb, hE_sum⟩ := hK m hmK
    -- Step 8: enumerate E as a strictly monotone function Fin m → ℕ.
    let g : Fin m ↪o ℕ := E.orderEmbOfFin hE_card
    -- We need a function Fin (k + 1) → ℕ with k = m - 1 such that k + 1 = m.
    have hm_succ : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    refine ⟨m - 1, fun i => g (Fin.cast hm_succ i), ?_, ?_, ?_, ?_⟩
    · -- StrictMono
      intro i j hij
      apply g.strictMono
      exact Fin.cast_lt_cast hm_succ |>.mpr hij
    · -- L < n 0
      have h0_in : g (Fin.cast hm_succ 0) ∈ E := E.orderEmbOfFin_mem hE_card _
      exact hE_lb _ h0_in
    · -- α = ∑ i, 1 / n i
      rw [hE_sum]
      -- Sum over Fin (m - 1 + 1) of 1 / g (Fin.cast hm_succ i) equals sum over E of 1 / e.
      have h_image : Finset.image (⇑g) Finset.univ = E :=
        E.image_orderEmbOfFin_univ hE_card
      rw [← h_image]
      rw [Finset.sum_image (fun a _ b _ hab => g.injective hab)]
      -- Reindex from Fin m to Fin (m - 1 + 1) using the equivalence Fin.cast hm_succ.symm.
      symm
      apply Finset.sum_equiv (Fin.castOrderIso hm_succ).toEquiv
      · intro i; simp
      · intro i _; rfl
    · -- m = ∑ i, p.eval (n i)
      simp only [h_eval_one]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [hm_succ]
      simp
  case neg =>
    -- POLYNOMIAL CASE: 1 ≤ p.natDegree (since hd : p.natDegree ≠ 0).
    have h_nonconst : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hd
    -- Step 1: choose J via chooseMainChoice (asymptotic threshold).
    obtain ⟨md⟩ := chooseMainChoice α hα L p hp h_nonconst h_lead_pos
    -- Step 2: extract g via chooseMainGCDData (gcd of A(D j) values + bridge).
    obtain ⟨gcd⟩ := chooseMainGCDData p hp h_nonconst h_lead_pos md
    -- Step 3: apply RSG to qPoly to get the window representation.
    obtain ⟨X_q, hX_q⟩ := main_window_representation p hp h_nonconst h_lead_pos md gcd
    -- Step 4: choose correction data. The `g = 1` branch is empty; for
    -- `g ≥ 2` use finite switching generators, duplicated subset sums, and
    -- large collision-free denominators.
    have hcorr_nonempty : Nonempty (CorrectionData p hp gcd) := by
      by_cases hg1 : gcd.g = 1
      · exact chooseCorrectionData_g_eq_one p hp gcd hg1
      · have hg2 : 2 ≤ gcd.g := by
          have hgpos := gcd.hg_pos
          omega
        exact chooseCorrectionData_g_ge_two p hp gcd h_nonconst h_lead_pos
          h_no_fixed_div hg2
    obtain ⟨corr⟩ := hcorr_nonempty
    -- Step 5: choose the fixed filler denominators after the correction mass.
    obtain ⟨fill⟩ := chooseFillerData p hp corr
    obtain ⟨Nτ, hNτ⟩ := correctionMultiplierMax_lt_tau_eventually corr
    obtain ⟨Nt, hNt⟩ := qPoly_tail_eventually p hp h_nonconst h_lead_pos gcd X_q
    obtain ⟨No, hNo⟩ :=
      intervals_overlap_eventually p hp h_nonconst h_lead_pos corr fill X_q
    let Nbase : ℕ := max (max (max md.J Nτ) Nt) No
    have hJ_base : md.J ≤ Nbase := by
      dsimp [Nbase]
      omega
    have hτ_base : Nτ ≤ Nbase := by
      dsimp [Nbase]
      omega
    have ht_base : Nt ≤ Nbase := by
      dsimp [Nbase]
      omega
    have ho_base : No ≤ Nbase := by
      dsimp [Nbase]
      omega
    have hoverlap :
        ∀ N : ℕ, Nbase ≤ N →
          lowerInt p hp corr fill X_q (N + 1) ≤
            upperEdge p hp corr fill N + 1 := by
      intro N hN
      exact hNo N (le_trans ho_base hN)
    have hunbounded :
        ∀ M : ℤ, ∃ N, Nbase ≤ N ∧ M ≤ upperEdge p hp corr fill N :=
      upperEdge_unbounded p hp h_nonconst h_lead_pos corr fill Nbase
    let m₀ : ℕ := (lowerInt p hp corr fill X_q Nbase).toNat
    refine ⟨m₀, ?_⟩
    intro m hm
    have hmlo_base :
        lowerInt p hp corr fill X_q Nbase ≤ (m : ℤ) := by
      have hlo_toNat :
          lowerInt p hp corr fill X_q Nbase ≤ (m₀ : ℤ) := by
        dsimp [m₀]
        exact Int.self_le_toNat _
      exact le_trans hlo_toNat (by exact_mod_cast hm)
    obtain ⟨N, hNbase, hlo, hhi⟩ :=
      integer_intervals_cover_tail
        (fun N => lowerInt p hp corr fill X_q N)
        (fun N => upperEdge p hp corr fill N)
        Nbase hoverlap hunbounded (m : ℤ) hmlo_base
    have hJN : md.J ≤ N := le_trans hJ_base hNbase
    have hτN : correctionMultiplierMax corr < tau N :=
      hNτ N (le_trans hτ_base hNbase)
    have htailN :
        ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ upperInt p N →
          ∀ i : ℕ, N - md.J < i →
            (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ) :=
      hNt N (le_trans ht_base hNbase)
    exact attainable_interval p hp corr fill X_q hX_q N m (upperInt p N)
      hJN hτN htailN
      (by simpa [lowerInt] using hlo)
      (by simpa [upperEdge] using hhi)

end PolynomialEgyptianSums
