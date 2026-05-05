/-
Erdős Problems 283 + 351 — §1 Egyptian switches, switching polynomials & Lemma 6.

  * `switchingPoly p E := ∑_{e ∈ E} p(e·) - p`  — the switching polynomial.
  * `switchingPoly_leadingCoeff` — `lc(Q_E) = lc(p) · (∑_{e ∈ E} e^r - 1) > 0`.
  * `switchValueSet`             — the set of all integer values `Q_E(n)` over
                                    all Egyptian patterns `E` and `n ≥ 1`.
  * `switching_values_span_top`  — Lemma 6 (corrected): `Ideal.span (switchValueSet) = ⊤`,
                                    i.e. the gcd of all switching values is 1.
  * `finite_switch_values_generate_zmod` — finite version usable for the
                                            correction-slot construction.

Lemma 6 is axiom-free; uses Lemmas 4, 5 and `IntValued p`.
-/

import Erdos.P283.Basic
import Erdos.P283.Egyptian
import Erdos.P283.PolynomialPeriod

namespace PolynomialEgyptianSums

open Polynomial Finset

/-- The **switching polynomial** `Q_E(x) := ∑_{e ∈ E} p(e·x) - p(x)` for an
Egyptian pattern `E`. -/
noncomputable def switchingPoly (p : ℚ[X]) (E : Finset ℕ) : ℚ[X] :=
  (E.sum fun e => p.comp ((Polynomial.C (e : ℚ)) * Polynomial.X)) - p

/-- The leading coefficient of `Q_E` is `lc(p) · (∑_{e ∈ E} e^r - 1)`, where
`r := deg p`. Positive whenever `lc(p) > 0` and `E` is non-trivial (since
`∑ e^r ≥ ∑ e ≥ 2|E| ≥ 2 > 1`). -/
lemma switchingPoly_leadingCoeff (p : ℚ[X]) (E : Finset ℕ)
    (hE : IsEgyptianPattern E) (h_lead_pos : 0 < p.leadingCoeff)
    (h_nonconst : 1 ≤ p.natDegree) :
    0 < (switchingPoly p E).leadingCoeff := by
  classical
  obtain ⟨h2, hsum⟩ := hE
  -- E is nonempty since otherwise ∑ 1/e = 0 ≠ 1.
  have hne : E.Nonempty := by
    rcases Finset.eq_empty_or_nonempty E with h | h
    · rw [h, Finset.sum_empty] at hsum
      norm_num at hsum
    · exact h
  -- p ≠ 0 since natDegree ≥ 1.
  have hp_ne : p ≠ 0 := by
    intro h
    rw [h] at h_nonconst
    simp at h_nonconst
  set r := p.natDegree with hr_def
  -- Each q_e := p.comp (C e * X) has natDegree r and leadingCoeff = lc(p) * e^r.
  have h_nat_deg : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = r := by
    intro e he
    have he_ne : (e : ℚ) ≠ 0 := by
      have := h2 e he
      exact_mod_cast (by omega : e ≠ 0)
    rw [Polynomial.natDegree_comp]
    rw [Polynomial.natDegree_C_mul_X (e : ℚ) he_ne]
    ring
  have h_lc : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff =
        p.leadingCoeff * ((e : ℚ) ^ r) := by
    intro e he
    have he_ne : (e : ℚ) ≠ 0 := by
      have := h2 e he
      exact_mod_cast (by omega : e ≠ 0)
    have h_deg : (Polynomial.C (e : ℚ) * Polynomial.X).natDegree = 1 :=
      Polynomial.natDegree_C_mul_X (e : ℚ) he_ne
    rw [Polynomial.leadingCoeff_comp (by rw [h_deg]; norm_num)]
    rw [Polynomial.leadingCoeff_C_mul_X]
  -- Each q_e ≠ 0 since natDegree = r ≥ 1.
  have h_q_e_ne : ∀ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X) ≠ 0 := by
    intro e he h_eq
    have : (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = 0 := by
      rw [h_eq]; simp
    rw [h_nat_deg e he] at this
    omega
  -- Each q_e has degree exactly r in WithBot ℕ.
  have h_q_e_deg : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = (r : WithBot ℕ) := by
    intro e he
    rw [Polynomial.degree_eq_natDegree (h_q_e_ne e he)]
    rw [h_nat_deg e he]
  -- ∑ e^r ≥ 2 (since each e^r ≥ 2 and E.card ≥ 1).
  have h_sum_pow_ge : (2 : ℚ) ≤ (∑ e ∈ E, ((e : ℚ) ^ r)) := by
    have h_card_pos : 1 ≤ E.card := Finset.card_pos.mpr hne
    have step : ∀ e ∈ E, (2 : ℚ) ≤ ((e : ℚ) ^ r) := by
      intro e he
      have he2 : (2 : ℚ) ≤ e := by exact_mod_cast h2 e he
      have hr_le : 1 ≤ r := h_nonconst
      calc (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
      _ ≤ (2 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr_le
      _ ≤ (e : ℚ) ^ r := pow_le_pow_left₀ (by norm_num) he2 _
    have hsum2 : (∑ _ ∈ E, (2 : ℚ)) ≤ (∑ e ∈ E, ((e : ℚ) ^ r)) :=
      Finset.sum_le_sum step
    have hsum2_eq : (∑ _ ∈ E, (2 : ℚ)) = 2 * E.card := by
      rw [Finset.sum_const]; ring
    rw [hsum2_eq] at hsum2
    have h_card_q : (1 : ℚ) ≤ E.card := by exact_mod_cast h_card_pos
    linarith
  -- Sum of leading coefficients is positive (so nonzero).
  have h_sum_lc_pos : 0 <
      ∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
    have h_eq :
        (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) =
        ∑ e ∈ E, p.leadingCoeff * ((e : ℚ) ^ r) :=
      Finset.sum_congr rfl h_lc
    rw [h_eq, ← Finset.mul_sum]
    apply mul_pos h_lead_pos
    linarith
  have h_sum_lc_ne :
      (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) ≠ 0 :=
    ne_of_gt h_sum_lc_pos
  -- Sum's leadingCoeff = ∑ leadingCoeff(q_e) = lc(p) · ∑ e^r.
  have h_sum_lc_eq :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        = ∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff :=
    Polynomial.leadingCoeff_sum_of_degree_eq h_q_e_deg h_sum_lc_ne
  -- Sum has natDegree exactly r.
  have h_sum_natDegree :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = r := by
    have h_le :
        (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree ≤ r := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      rw [h_nat_deg i hi]
    apply le_antisymm h_le
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.finset_sum_coeff]
    have h_coeff_eq : ∀ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).coeff r =
        (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
      intro e he
      rw [show (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff = _ from rfl,
          Polynomial.leadingCoeff, h_nat_deg e he]
    rw [Finset.sum_congr rfl h_coeff_eq]
    exact h_sum_lc_ne
  -- Sum's leadingCoeff = lc(p) · ∑ e^r.
  have h_sum_lc_val :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        = p.leadingCoeff * ∑ e ∈ E, ((e : ℚ) ^ r) := by
    rw [h_sum_lc_eq]
    have h_eq :
        (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) =
        ∑ e ∈ E, p.leadingCoeff * ((e : ℚ) ^ r) :=
      Finset.sum_congr rfl h_lc
    rw [h_eq, ← Finset.mul_sum]
  -- Sum and p have the same degree r in WithBot ℕ.
  have h_sum_deg :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = (r : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree, h_sum_natDegree]
    intro h
    rw [h] at h_sum_natDegree
    simp at h_sum_natDegree
    omega
  have h_p_deg : p.degree = (r : WithBot ℕ) :=
    Polynomial.degree_eq_natDegree hp_ne
  -- Leading coefficients differ since ∑ e^r ≥ 2 > 1.
  have h_p_lc_ne : p.leadingCoeff ≠ 0 := ne_of_gt h_lead_pos
  have h_lc_diff :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        ≠ p.leadingCoeff := by
    rw [h_sum_lc_val]
    intro h_eq
    have : p.leadingCoeff * (∑ e ∈ E, ((e : ℚ) ^ r) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h2
    · exact h_p_lc_ne h1
    · linarith
  unfold switchingPoly
  have h_deg_eq :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = p.degree := by
    rw [h_sum_deg, h_p_deg]
  rw [Polynomial.leadingCoeff_sub_of_degree_eq h_deg_eq h_lc_diff]
  rw [h_sum_lc_val]
  have h_rewrite :
      p.leadingCoeff * ∑ e ∈ E, ((e : ℚ) ^ r) - p.leadingCoeff
        = p.leadingCoeff * ((∑ e ∈ E, ((e : ℚ) ^ r)) - 1) := by ring
  rw [h_rewrite]
  apply mul_pos h_lead_pos
  linarith

/-- The set of **integer values** of switching polynomials over all Egyptian
patterns and positive integers. -/
noncomputable def switchValueSet (p : ℚ[X]) (hp : IntValued p) : Set ℤ :=
  { z | ∃ E : Finset ℕ, ∃ n : ℕ,
      IsEgyptianPattern E ∧ 1 ≤ n ∧
      z = (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ))
            - intEval p hp ((n : ℕ) : ℤ) }

/-- **Lemma 6 (PDF §1, corrected).** If `p` has degree `≥ 1`, positive leading
coefficient, and no fixed divisor on positive integers, then the integer values
of all switching polynomials `Q_E(n)` (over Egyptian patterns `E` and positive
integers `n`) generate the unit ideal of `ℤ`.

Proof (PDF §1): Suppose a prime `ℓ` divides every value. Choose `B` with
`B p ∈ ℤ[X]` (`exists_integral_multiple`); set `T_ℓ = ℓ B`. By Lemma 4 choose `E`
with `T_ℓ ∣ e` for all `e ∈ E` and `|E| ≡ 0 (mod ℓ)`. By Lemma 5, `p(e n) ≡ p(0)
(mod ℓ)` for `e ∈ E, n ≥ 1`, so `Q_E(n) ≡ |E| p(0) - p(n) ≡ -p(n) (mod ℓ)`.
Hence `ℓ ∣ p(n)` for all `n`, contradicting no-fixed-divisor. -/
theorem switching_values_span_top (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed : NoFixedDivisor p hp) :
    Ideal.span (switchValueSet p hp) = ⊤ := by
  classical
  by_contra h_top
  -- Step 1: Extract a prime ℓ : ℕ such that ℓ ∣ z for every z ∈ switchValueSet.
  obtain ⟨M, hM_max, hM_le⟩ := Ideal.exists_le_maximal _ h_top
  haveI hM_prime : M.IsPrime := hM_max.isPrime
  haveI hM_principal : Submodule.IsPrincipal M := IsPrincipalIdealRing.principal M
  -- ℤ is not a field, so the maximal ideal M ≠ ⊥.
  have h_field : ¬ IsField ℤ := by
    intro h
    haveI := h.toField
    have h2 : (2 : ℤ) ≠ 0 := by norm_num
    obtain ⟨a, ha⟩ := h.mul_inv_cancel h2
    have : (2 : ℤ) ∣ 1 := ⟨a, ha.symm⟩
    omega
  have hM_ne_bot : M ≠ ⊥ := by
    intro h_bot
    rw [h_bot] at hM_max
    exact h_field (Ring.isField_iff_maximal_bot.mpr hM_max)
  -- The generator a is prime, and a.natAbs = ℓ is a prime natural.
  set a := Submodule.IsPrincipal.generator M with ha_def
  have ha : Prime a := Submodule.IsPrincipal.prime_generator_of_isPrime M hM_ne_bot
  have ha_nat : a.natAbs.Prime := Int.prime_iff_natAbs_prime.mp ha
  set ℓ := a.natAbs with hℓ_def
  have hℓ_prime : ℓ.Prime := ha_nat
  -- ℓ divides every z in the switching-value set.
  have hℓ_dvd : ∀ z ∈ switchValueSet p hp, (ℓ : ℤ) ∣ z := by
    intro z hz
    have hz_M : z ∈ M := hM_le (Ideal.subset_span hz)
    have ha_eq : Ideal.span ({a} : Set ℤ) = M :=
      Submodule.IsPrincipal.span_singleton_generator M
    rw [← ha_eq] at hz_M
    rw [Ideal.mem_span_singleton] at hz_M
    rcases Int.natAbs_eq a with heq | heq
    · rw [← heq]; exact hz_M
    · rw [heq] at hz_M; exact (Int.neg_dvd.mp hz_M)
  -- Step 2: Get B with B p ∈ ℤ[X].
  obtain ⟨B, hB_pos, hB_int⟩ := exists_integral_multiple p
  -- Step 3: Apply egyptian_pattern_with_period with T = ℓ * B, M = ℓ, ρ = 0.
  have hℓ_pos : 1 ≤ ℓ := hℓ_prime.one_lt.le
  have hℓ_ge_two : 2 ≤ ℓ := hℓ_prime.two_le
  have hT_pos : 1 ≤ ℓ * B :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  obtain ⟨E, hE_pat, hE_dvd, hE_card⟩ :=
    egyptian_pattern_with_period (ℓ * B) ℓ hT_pos hℓ_pos (0 : ZMod ℓ)
  -- E.card ≡ 0 (mod ℓ).
  have h_card_dvd : (ℓ : ℤ) ∣ (E.card : ℤ) := by
    have hcard : (E.card : ZMod ℓ) = 0 := hE_card
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact_mod_cast hcard
  -- Step 4: For every n ≥ 1, derive ℓ ∣ intEval p n.
  have h_div : ∀ n : ℕ, 1 ≤ n → (ℓ : ℤ) ∣ intEval p hp (n : ℤ) := by
    intro n hn
    set Qn : ℤ :=
      (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) - intEval p hp ((n : ℕ) : ℤ) with hQn_def
    have hQ_in : Qn ∈ switchValueSet p hp := ⟨E, n, hE_pat, hn, rfl⟩
    have hℓ_dvd_Qn : (ℓ : ℤ) ∣ Qn := hℓ_dvd Qn hQ_in
    -- For each e ∈ E, intEval p (e * n) ≡ intEval p 0 (mod ℓ) by polynomial_periodicity.
    have h_each : ∀ e ∈ E,
        intEval p hp ((e * n : ℕ) : ℤ) ≡ intEval p hp 0 [ZMOD (ℓ : ℤ)] := by
      intro e he
      have hdvd : (ℓ * B) ∣ e := hE_dvd e he
      have h_eq_zmod : ((e * n : ℕ) : ℤ) ≡ (0 : ℤ) [ZMOD ((ℓ * B : ℕ) : ℤ)] := by
        rw [Int.modEq_zero_iff_dvd]
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨(k * n : ℕ), ?_⟩
        have h_e_int : (e : ℤ) = ((ℓ * B * k : ℕ) : ℤ) := by exact_mod_cast hk
        push_cast
        push_cast at h_e_int
        rw [h_e_int]
        ring
      have h_per := polynomial_periodicity p hp B hB_pos hB_int ℓ hℓ_pos
        ((e * n : ℕ) : ℤ) (0 : ℤ) h_eq_zmod
      exact_mod_cast h_per
    -- Sum congruence: ∑_e intEval p (e * n) ≡ ∑_e intEval p 0 = E.card * intEval p 0 (mod ℓ).
    have h_sum_congr :
        (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) ≡
        (∑ _ ∈ E, intEval p hp 0) [ZMOD (ℓ : ℤ)] :=
      Int.ModEq.sum h_each
    have h_const_sum :
        (∑ _ ∈ E, intEval p hp 0) = (E.card : ℤ) * intEval p hp 0 := by
      rw [Finset.sum_const]
      ring
    rw [h_const_sum] at h_sum_congr
    -- E.card * intEval p 0 ≡ 0 (mod ℓ).
    have h_const_zero :
        (E.card : ℤ) * intEval p hp 0 ≡ 0 [ZMOD (ℓ : ℤ)] := by
      rw [Int.modEq_zero_iff_dvd]
      exact Dvd.dvd.mul_right h_card_dvd _
    have h_sum_zero :
        (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) ≡ 0 [ZMOD (ℓ : ℤ)] :=
      h_sum_congr.trans h_const_zero
    have h_dvd_sum :
        (ℓ : ℤ) ∣ (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) := by
      rw [Int.modEq_zero_iff_dvd] at h_sum_zero
      exact h_sum_zero
    -- ℓ ∣ Qn = sum - intEval p n, and ℓ ∣ sum, so ℓ ∣ intEval p n.
    have h_diff : intEval p hp ((n : ℕ) : ℤ) =
        (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) - Qn := by
      change intEval p hp ((n : ℕ) : ℤ) =
        (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) -
          ((∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) - intEval p hp ((n : ℕ) : ℤ))
      ring
    show (ℓ : ℤ) ∣ intEval p hp ((n : ℕ) : ℤ)
    rw [h_diff]
    exact dvd_sub h_dvd_sum hℓ_dvd_Qn
  -- Apply NoFixedDivisor at d = ℓ.
  exact h_no_fixed ℓ hℓ_ge_two h_div

/-- **Finite extracted form of Lemma 6.** Used in the correction-slot
construction: there are finitely many Egyptian patterns and positive integers
whose switching-polynomial residues mod `g` generate `ZMod g`. -/
theorem finite_switch_values_generate_zmod (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed : NoFixedDivisor p hp) (g : ℕ) (hg : 1 ≤ g) :
    ∃ (t : ℕ) (E : Fin t → Finset ℕ) (a : Fin t → ℕ) (b : Fin t → ℤ),
      (∀ i, IsEgyptianPattern (E i)) ∧
      (∀ i, 1 ≤ a i) ∧
      (∀ i, b i = (∑ e ∈ E i, intEval p hp ((e * a i : ℕ) : ℤ))
                  - intEval p hp ((a i : ℕ) : ℤ)) ∧
      AddSubgroup.closure (Set.range fun i : Fin t => ((b i : ℤ) : ZMod g)) = ⊤ := by
  classical
  haveI hg_neZero : NeZero g := ⟨Nat.one_le_iff_ne_zero.mp hg⟩
  -- Step 1: span = ⊤ ⟹ 1 ∈ span ⟹ a finite ℤ-combination summing to 1.
  have h_top := switching_values_span_top p hp h_nonconst h_lead_pos h_no_fixed
  have h1 : (1 : ℤ) ∈ Ideal.span (switchValueSet p hp) := by rw [h_top]; trivial
  obtain ⟨c, t_set, h_t_sub, _h_supp, h_sum⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp h1
  -- Each z ∈ t_set lies in switchValueSet, so (E_z, n_z) data exists.
  have h_each : ∀ z ∈ t_set, ∃ E : Finset ℕ, ∃ n : ℕ,
      IsEgyptianPattern E ∧ 1 ≤ n ∧
      z = (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ))
            - intEval p hp ((n : ℕ) : ℤ) := fun z hz => h_t_sub hz
  -- Convert the Finset t_set to an indexed Fin t form via `t_set.equivFin`.
  set t : ℕ := t_set.card with ht_def
  let φ : Fin t → ℤ := fun i => t_set.equivFin.symm i
  have h_φ_mem : ∀ i, φ i ∈ t_set := fun i => (t_set.equivFin.symm i).property
  let data : Fin t → (Finset ℕ × ℕ) := fun i =>
    let h := h_each (φ i) (h_φ_mem i)
    let E := h.choose
    let rest := h.choose_spec
    let n := rest.choose
    ⟨E, n⟩
  let E : Fin t → Finset ℕ := fun i => (data i).1
  let aᵢ : Fin t → ℕ := fun i => (data i).2
  let b : Fin t → ℤ := fun i => φ i
  -- Extract the three properties via `Classical.choose_spec`.
  have hpat : ∀ i, IsEgyptianPattern (E i) := by
    intro i
    have h := h_each (φ i) (h_φ_mem i)
    obtain ⟨pat, _, _⟩ := h.choose_spec.choose_spec
    exact pat
  have han : ∀ i, 1 ≤ aᵢ i := by
    intro i
    have h := h_each (φ i) (h_φ_mem i)
    obtain ⟨_, han, _⟩ := h.choose_spec.choose_spec
    exact han
  have hb_eq : ∀ i, b i = (∑ e ∈ E i, intEval p hp ((e * aᵢ i : ℕ) : ℤ)) -
      intEval p hp ((aᵢ i : ℕ) : ℤ) := by
    intro i
    have h := h_each (φ i) (h_φ_mem i)
    obtain ⟨_, _, hb⟩ := h.choose_spec.choose_spec
    exact hb
  refine ⟨t, E, aᵢ, b, hpat, han, hb_eq, ?_⟩
  -- Closure equals ⊤ iff every element of `ZMod g` lies in it.
  rw [AddSubgroup.eq_top_iff']
  intro x
  -- Step: 1 ∈ closure {(b i : ZMod g)}: cast h_sum down to ZMod g and assemble.
  have h_one_in : (1 : ZMod g) ∈
      AddSubgroup.closure (Set.range fun i : Fin t => ((b i : ℤ) : ZMod g)) := by
    have h_sum_zmod : (1 : ZMod g) = ∑ a ∈ t_set, c a • ((a : ZMod g)) := by
      have h := congr_arg (Int.cast : ℤ → ZMod g) h_sum
      push_cast at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro a _
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [h_sum_zmod]
    apply AddSubgroup.sum_mem
    intro a ha
    apply zsmul_mem
    apply AddSubgroup.subset_closure
    refine ⟨t_set.equivFin ⟨a, ha⟩, ?_⟩
    show ((b (t_set.equivFin ⟨a, ha⟩) : ℤ) : ZMod g) = ((a : ℤ) : ZMod g)
    have h_b_eq : b (t_set.equivFin ⟨a, ha⟩) = (a : ℤ) := by
      show (t_set.equivFin.symm (t_set.equivFin ⟨a, ha⟩) : ℤ) = (a : ℤ)
      simp
    rw [h_b_eq]
  -- Every x = (ZMod.val x) • 1 ∈ closure.
  have h_x_eq : x = (ZMod.val x : ℤ) • (1 : ZMod g) := by
    rw [zsmul_one]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [h_x_eq]
  exact zsmul_mem h_one_in _

end PolynomialEgyptianSums
