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

Trust boundary: `roth_szekeres_graham` (Basic.lean) only.
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

/-! ### Quotient-gcd bridge (sketch — full proof forthcoming)

The most important missing bridge for theorem_1's case neg: if `g` is the
positive generator of `Ideal.span (mainValueSet p hp md.J)`, then the
quotient values `(qPoly p md.J g).eval (t : ℚ)` (for `t ≥ 1`) generate the
unit ideal in `ℤ`. Equivalently, no prime `ℓ` divides every quotient value.

Mathematically: `g = gcd { A(D j) : j ≥ J }` by construction. Dividing the
spanning set by `g` gives values whose gcd is 1, so no prime divides them
all. RSG's `h_gcd_one` hypothesis is exactly this.

The full proof uses `Ideal.span` over ℤ (a PID), the principal-ideal
generator decomposition, and a transport from "gcd of values is `g`" to
"gcd of `value/g` is 1". For now declared as a sketch hypothesis used by the
`MainGCDData` constructor; the constructor itself is forthcoming. -/
section MainQuotBridge

variable {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)

/-- Stub statement-shape for the quotient-gcd bridge. The substance lives
in the forthcoming `MainGCDData` constructor; this `def` records the target
shape so callers can refer to it by name. -/
def mainQuot_no_prime_fixed_stmt (md : MainChoice α L p hp) (g : ℕ)
    (_ : 1 ≤ g) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime →
    ∃ t : ℕ, 1 ≤ t ∧ ∃ z : ℤ,
      (z : ℚ) = (qPoly p md.J g).eval (t : ℚ) ∧
      ¬ ((ℓ : ℤ) ∣ z)

end MainQuotBridge

/-- **Main theorem (PDF Theorem 1).** For `α ∈ ℚ_{>0}`, `L ≥ 1`, and a polynomial
`p ∈ ℚ[x]` integer-valued with positive leading coefficient and no fixed
divisor on positive integers, all sufficiently large integers `m` admit an
expression as `∑ p(n_i)` with distinct `L < n_1 < ⋯ < n_k` and `∑ 1/n_i = α`.

The proof combines:
  * `egyptian_expansion` (Lemma 3) for filler denominators
  * `egyptian_pattern_with_period` (Lemma 4) used by Lemma 6
  * `polynomial_periodicity` (Lemma 5) used by Lemma 6 and the correction slots
  * `switching_values_span_top` (Lemma 6) for the residue-correction trick
  * `roth_szekeres_graham` (axiom) applied to `q := A ∘ Dpoly / g`
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
    sorry

end PolynomialEgyptianSums
