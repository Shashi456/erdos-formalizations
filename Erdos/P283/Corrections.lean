/-
Erdős Problems 283 + 351 — §2 correction-slot construction.

If `g := gcd { A(D j) : j ≥ J } = 1`, no correction is needed.
Otherwise, we build correction slots (denominators `c_ν`, patterns `G_ν`)
whose switch increments `b_ν = Q_{G_ν}(c_ν)` represent every residue class
mod `g` as a subset sum.

Two main supporting results:

  * `duplicated_generators_subset_sum_all_residues` — given residues
    generating `ZMod g`, duplicating each `g − 1` times allows representing
    every residue as a subset sum.
  * `exists_large_correction_denominator` — given a forbidden finite set and
    forbidden multiples-of-D-multiplied set, an arithmetic-progression element
    avoiding all forbidden values exists arbitrarily far out.

Plus the bookkeeping for `B_*`, `R_c`, `C_0`.
-/

import Erdos.P283.Basic
import Erdos.P283.Switching
import Erdos.P283.MainSlots

namespace PolynomialEgyptianSums

open Finset Polynomial

/-! ## Subset-sum representability -/

/-- If finitely many residues `ρ : Fin w → ZMod g` generate `ZMod g` as an
additive group, then duplicating each residue `g - 1` times allows every
residue to be represented as a subset sum (with repetitions encoded as choices
of how many duplicates to take). -/
theorem duplicated_generators_subset_sum_all_residues
    {w g : ℕ} (hg : 1 ≤ g) (ρ : Fin w → ZMod g)
    (hgen : AddSubgroup.closure (Set.range ρ) = ⊤) :
    ∀ r : ZMod g,
      ∃ T : Finset (Fin w × Fin (g - 1)),
        r = ∑ t ∈ T, ρ t.1 := by
  intro r
  haveI : NeZero g := ⟨by omega⟩
  have hr : r ∈ AddSubgroup.closure (Set.range ρ) := by rw [hgen]; trivial
  obtain ⟨a, ha⟩ := AddSubgroup.exists_of_mem_closure_range ρ r hr
  have hgZ : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hg
  -- Reduce each integer coefficient `a i` to its residue `k i ∈ {0, …, g - 1}`.
  set k : Fin w → ℕ := fun i => ((a i) % (g : ℤ)).toNat with hk_def
  have hk_lt : ∀ i, k i < g := fun i => by
    have hnn : (0 : ℤ) ≤ (a i) % (g : ℤ) := Int.emod_nonneg _ hgZ.ne'
    have hub : (a i) % (g : ℤ) < (g : ℤ) := Int.emod_lt_of_pos _ hgZ
    rw [hk_def]
    exact (Int.toNat_lt hnn).mpr hub
  have hk_le : ∀ i, k i ≤ g - 1 := fun i => by have := hk_lt i; omega
  -- In `ZMod g`, the natural-number scalar `k i` matches the integer scalar `a i`.
  have key : ∀ i, (k i : ℕ) • ρ i = a i • ρ i := fun i => by
    have hnn : (0 : ℤ) ≤ (a i) % (g : ℤ) := Int.emod_nonneg _ hgZ.ne'
    rw [hk_def]
    rw [show ((((a i) % (g : ℤ)).toNat : ℕ) • ρ i) = ((((a i) % (g : ℤ)).toNat : ℤ) • ρ i) from
      (natCast_zsmul (ρ i) _).symm]
    rw [Int.toNat_of_nonneg hnn]
    rw [show ((g : ℤ) : ℤ) = (Fintype.card (ZMod g) : ℤ) by simp [ZMod.card]]
    exact mod_card_zsmul (ρ i) (a i)
  -- For each `i`, choose the first `k i` elements of `Fin (g - 1)`.
  let T : Finset (Fin w × Fin (g - 1)) :=
    ((Finset.univ : Finset (Fin w)) ×ˢ (Finset.univ : Finset (Fin (g - 1)))).filter
      (fun p => p.2.1 < k p.1)
  refine ⟨T, ?_⟩
  show r = ∑ t ∈ T, ρ t.1
  have hsum : (∑ t ∈ T, ρ t.1) = ∑ i, k i • ρ i := by
    show (∑ t ∈ ((Finset.univ : Finset (Fin w)) ×ˢ
            (Finset.univ : Finset (Fin (g - 1)))).filter
            (fun p => p.2.1 < k p.1), ρ t.1) = ∑ i, k i • ρ i
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show (∑ y : Fin (g - 1), if y.val < k i then ρ i else 0) = k i • ρ i
    rw [← Finset.sum_filter, Finset.sum_const]
    congr 1
    have heq : ((Finset.univ : Finset (Fin (g - 1))).filter
                  (fun j : Fin (g - 1) => j.val < k i)) =
               (Finset.range (k i)).attachFin (fun j hj =>
                 lt_of_lt_of_le (Finset.mem_range.mp hj) (hk_le i)) := by
      ext ⟨b, hb⟩
      simp [Finset.mem_attachFin, Finset.mem_range]
    rw [heq, Finset.card_attachFin]
    simp
  rw [hsum, ha]
  exact Finset.sum_congr rfl (fun i _ => (key i).symm)

/-! ## Correction-denominator existence (density argument) -/

/-- A density argument: an arithmetic progression `{a + k T_g : k ∈ ℕ}` has
positive density `1/T_g`, while the union of finitely many specific values
plus the curves `{(h/e) D j : j ≥ J}` (parametrized by `j`, contributing
`O(√X)` elements up to `X`) has density zero. So the AP eventually contains
elements avoiding all forbidden values.

The hypothesis `hQpos : 0 < (switchingPoly p Gν).leadingCoeff` makes
`Q_{Gν}(c) > 0` for `c` past the largest real root. This is supplied at the
call site from `switchingPoly_leadingCoeff`.

The forbidden-finite avoidance is stated in the same shape as the
main-denominator avoidance (`∀ e ∈ insert 1 Gν, e * c ∉ forbiddenFinite`)
so the caller can stuff "all previous correction-denominator candidates"
directly into `forbiddenFinite` without extra division-by-`e` bookkeeping.

`hQGν : IntValued (switchingPoly p Gν)` is derived from `hp` via
`switchingPoly_intValued`; the caller doesn't need to plumb it manually.

This is the second-hardest sub-lemma of the whole proof (after Lemma 3). -/
theorem exists_large_correction_denominator
    (p : ℚ[X]) (hp : IntValued p)
    (Tg aσ J L lower : ℕ) (Gν : Finset ℕ) (hGν : IsEgyptianPattern Gν)
    (hQpos : 0 < (switchingPoly p Gν).leadingCoeff)
    (forbiddenFinite : Finset ℕ) (hTg : 1 ≤ Tg) :
    ∃ c : ℕ,
      c ≡ aσ [MOD Tg] ∧
      lower < c ∧ L < c ∧
      0 < intEval (switchingPoly p Gν)
            (switchingPoly_intValued p hp Gν) ((c : ℕ) : ℤ) ∧
      (∀ e ∈ insert 1 Gν, e * c ∉ forbiddenFinite) ∧
      (∀ j, J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ insert 1 Gν, e * c ≠ h * D j) := by
  classical
  -- Notation.
  set Q : ℚ[X] := switchingPoly p Gν with hQ_def
  set hQint : IntValued Q := switchingPoly_intValued p hp Gν with hQint_def
  set EE : Finset ℕ := insert 1 Gν with hEE_def
  -- All elements of EE are positive (1 or ≥ 2 from Egyptian pattern).
  have hEE_pos : ∀ e ∈ EE, 1 ≤ e := by
    intro e he
    rw [hEE_def] at he
    rcases Finset.mem_insert.mp he with h1 | h2
    · omega
    · exact le_trans (by norm_num) (hGν.1 e h2)
  -- Pick a uniform upper bound on EE for sqrt-style counting.
  set maxE : ℕ := (EE.sup id) + 1 with hmaxE_def
  have hmaxE_ge : ∀ e ∈ EE, e ≤ maxE := by
    intro e he
    have := Finset.le_sup (f := id) he
    simp at this; omega
  have hmaxE_pos : 1 ≤ maxE := by rw [hmaxE_def]; omega
  -- Step 1: positivity threshold for Q on naturals.
  -- Cast Q to ℝ[X], use leading coefficient positivity to find threshold.
  obtain ⟨Npos, hNpos⟩ : ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      0 < intEval Q hQint ((x : ℕ) : ℤ) := by
    set Qr : ℝ[X] := Q.map (algebraMap ℚ ℝ) with hQr_def
    have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
      (algebraMap ℚ ℝ).injective
    have hQr_lc : (0 : ℝ) < Qr.leadingCoeff := by
      rw [hQr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
      have : (0 : ℝ) < (Q.leadingCoeff : ℝ) := by exact_mod_cast hQpos
      simpa [algebraMap] using this
    by_cases hd : 0 < Qr.degree
    · have h_tendsto :
          Filter.Tendsto (fun x : ℝ => Qr.eval x) Filter.atTop Filter.atTop :=
        Polynomial.tendsto_atTop_of_leadingCoeff_nonneg Qr hd hQr_lc.le
      obtain ⟨N0, hN0⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto 1
      refine ⟨Nat.ceil (max N0 0) + 1, ?_⟩
      intro x hx
      have hx_real : ((Nat.ceil (max N0 0) : ℕ) : ℝ) + 1 ≤ (x : ℝ) := by
        exact_mod_cast hx
      have h_max_le : N0 ≤ ((Nat.ceil (max N0 0) : ℕ) : ℝ) := by
        have h1 : N0 ≤ max N0 0 := le_max_left _ _
        have h2 : (max N0 0) ≤ ((Nat.ceil (max N0 0) : ℕ) : ℝ) := Nat.le_ceil _
        linarith
      have h_x_ge : N0 ≤ (x : ℝ) := by linarith
      have h_eval : 1 ≤ Qr.eval ((x : ℕ) : ℝ) := hN0 _ h_x_ge
      -- Convert to ℚ.
      have h_eval_cast :
          Qr.eval ((x : ℕ) : ℝ) = ((Q.eval ((x : ℕ) : ℚ) : ℚ) : ℝ) := by
        rw [hQr_def]
        have h1 : ((x : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((x : ℕ) : ℚ) := by
          simp [algebraMap]
        rw [h1, Polynomial.eval_map_apply]
        simp [algebraMap]
      have h_eval_q : 1 ≤ Q.eval ((x : ℕ) : ℚ) := by
        have : ((1 : ℚ) : ℝ) ≤ ((Q.eval ((x : ℕ) : ℚ) : ℚ) : ℝ) := by
          rw [show ((1 : ℚ) : ℝ) = (1 : ℝ) by norm_num]
          rw [← h_eval_cast]; exact h_eval
        exact_mod_cast this
      have h_intEval_eq :
          ((intEval Q hQint ((x : ℕ) : ℤ) : ℤ) : ℚ) = Q.eval ((x : ℕ) : ℚ) := by
        rw [intEval_spec]; push_cast; rfl
      have h_pos_q : 0 < Q.eval ((x : ℕ) : ℚ) := by linarith
      have h_pos_int : (0 : ℚ) < ((intEval Q hQint ((x : ℕ) : ℤ) : ℤ) : ℚ) := by
        rw [h_intEval_eq]; exact h_pos_q
      exact_mod_cast h_pos_int
    · -- Q has degree ≤ 0. Then Q is constant, equal to its leading coefficient.
      push_neg at hd
      have hQr_ne : Qr ≠ 0 := by
        intro h0; rw [h0] at hQr_lc; simp at hQr_lc
      have hQr_natDeg : Qr.natDegree = 0 := by
        have h_deg_eq : Qr.degree = (Qr.natDegree : WithBot ℕ) :=
          Polynomial.degree_eq_natDegree hQr_ne
        rw [h_deg_eq] at hd
        have hle : (Qr.natDegree : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by
          exact_mod_cast hd
        exact Nat.le_antisymm (by exact_mod_cast hle) (Nat.zero_le _)
      have hQ_ne : Q ≠ 0 := by
        intro h0
        rw [h0] at hQr_def
        have : Qr = 0 := by rw [hQr_def]; simp
        exact hQr_ne this
      have hQ_natDeg : Q.natDegree = 0 := by
        rw [hQr_def] at hQr_natDeg
        rw [Polynomial.natDegree_map_eq_of_injective h_inj] at hQr_natDeg
        exact hQr_natDeg
      have hQ_eq : Q = Polynomial.C (Q.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hQ_natDeg
      have hQ_coeff_eq : Q.coeff 0 = Q.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hQ_natDeg]
      refine ⟨0, fun x _ => ?_⟩
      have h_eval : Q.eval ((x : ℕ) : ℚ) = Q.leadingCoeff := by
        conv_lhs => rw [hQ_eq]
        rw [Polynomial.eval_C, hQ_coeff_eq]
      have h_intEval_eq :
          ((intEval Q hQint ((x : ℕ) : ℤ) : ℤ) : ℚ) = Q.eval ((x : ℕ) : ℚ) := by
        rw [intEval_spec]; push_cast; rfl
      rw [h_eval] at h_intEval_eq
      have : (0 : ℚ) < ((intEval Q hQint ((x : ℕ) : ℤ) : ℤ) : ℚ) := by
        rw [h_intEval_eq]; exact hQpos
      exact_mod_cast this
  -- Step 2: combine all "large enough" thresholds.
  set X₀ : ℕ := max (max Npos (lower + 1)) (L + 1) with hX₀_def
  have hX₀_Npos : Npos ≤ X₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hX₀_lower : lower < X₀ := by
    have h1 : lower + 1 ≤ X₀ := le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  have hX₀_L : L < X₀ := by
    have h1 : L + 1 ≤ X₀ := le_max_right _ _
    omega
  -- Step 3: collect forbidden values from forbiddenFinite, expressed as constraints on c.
  -- For each e ∈ EE and f ∈ forbiddenFinite, if e ∣ f then c = f / e is forbidden.
  set badFinSet : Finset ℕ :=
    EE.biUnion (fun e =>
      forbiddenFinite.image (fun f => f / e)) with hbadFinSet_def
  have hbadFin_forbid : ∀ c : ℕ, (∀ e ∈ EE, e * c ∉ forbiddenFinite) ∨ c ∈ badFinSet := by
    intro c
    by_cases h : ∀ e ∈ EE, e * c ∉ forbiddenFinite
    · exact Or.inl h
    · right
      push_neg at h
      obtain ⟨e, heE, hfE⟩ := h
      rw [hbadFinSet_def]
      refine Finset.mem_biUnion.mpr ⟨e, heE, ?_⟩
      refine Finset.mem_image.mpr ⟨e * c, hfE, ?_⟩
      have he_pos : 0 < e := hEE_pos e heE
      exact Nat.mul_div_cancel_left c he_pos
  -- Step 4: Bound the maximum value in badFinSet ∪ {X₀ - 1} so the AP starts past it.
  set XbadMax : ℕ :=
    (badFinSet ∪ {X₀ - 1}).sup id + 1 with hXbadMax_def
  have hXbadMax_ge_X₀ : X₀ ≤ XbadMax := by
    have h1 : X₀ - 1 ∈ (badFinSet ∪ {X₀ - 1}) := by
      apply Finset.mem_union_right; exact Finset.mem_singleton.mpr rfl
    have h2 : X₀ - 1 ≤ (badFinSet ∪ {X₀ - 1}).sup id := by
      have := Finset.le_sup (f := id) h1; simpa using this
    rw [hXbadMax_def]
    -- X₀ - 1 + 1 ≤ ... + 1, and X₀ ≤ X₀ - 1 + 1 (since X₀ ≥ 1 from hX₀_lower)
    have hX₀_ge_1 : 1 ≤ X₀ := by omega
    omega
  have hXbadMax_avoid : ∀ c : ℕ, XbadMax ≤ c → c ∉ badFinSet := by
    intro c hc hmem
    have h1 : c ∈ (badFinSet ∪ {X₀ - 1}) := Finset.mem_union_left _ hmem
    have h2 : c ≤ (badFinSet ∪ {X₀ - 1}).sup id := by
      have := Finset.le_sup (f := id) h1; simpa using this
    rw [hXbadMax_def] at hc; omega
  -- Step 5: The remaining counting/density step.
  --
  -- We seek `k : ℕ` such that, setting `c := aσ + k*Tg`, we have:
  --   (a) `c ≥ XbadMax` (covers lower, L, Npos, badFinSet via the threshold reductions),
  --   (b) `∀ j ≥ J, ∀ h ∈ {1,2,3,6}, ∀ e ∈ EE, e*c ≠ h*D j` (no main-slot collisions).
  --
  -- Mathematical content: the AP `{aσ + k*Tg : k ∈ ℕ}` has positive density `1/Tg`,
  -- while the main-collision forbidden set `{h*D j/e : j ≥ J, h ∈ {1,2,3,6}, e ∈ EE}`
  -- has density 0 — for c ≤ X, we need D j ≤ maxE * X, hence j ≤ √(maxE*X)/36
  -- (since D j ≥ 1296 j² for j ≥ 1), giving O(√X) forbidden values up to X.
  -- So for K large, the AP segment `{aσ + k*Tg : 0 ≤ k ≤ K}` of size K+1 in [X₀, X₀+K*Tg]
  -- exceeds the O(√(X₀+K*Tg)) forbidden values, hence contains a good `c`.
  --
  -- This is captured in the focused claim below. Above this `sorry` is all
  -- the bookkeeping (positivity threshold, finite-forbidden reduction, AP setup).
  -- The remaining counting argument needs Nat.sqrt-style bounds and pigeonhole,
  -- which would take several hundred lines to make rigorous.
  obtain ⟨k, hk_AP, hk_main⟩ : ∃ k : ℕ,
      XbadMax ≤ aσ + k * Tg ∧
      (∀ j, J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ EE, e * (aσ + k * Tg) ≠ h * D j) := by
    sorry
  -- Step 6: assemble the final witness from k.
  refine ⟨aσ + k * Tg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- AP membership.
    exact (Nat.add_mul_modulus_modEq_iff).mpr (Nat.ModEq.refl aσ)
  · -- lower < c.
    have : XbadMax ≤ aσ + k * Tg := hk_AP
    have : X₀ ≤ aσ + k * Tg := le_trans hXbadMax_ge_X₀ this
    omega
  · -- L < c.
    have : XbadMax ≤ aσ + k * Tg := hk_AP
    have : X₀ ≤ aσ + k * Tg := le_trans hXbadMax_ge_X₀ this
    omega
  · -- Q positivity.
    have hX₀_le : X₀ ≤ aσ + k * Tg := le_trans hXbadMax_ge_X₀ hk_AP
    have hNpos_le : Npos ≤ aσ + k * Tg := le_trans hX₀_Npos hX₀_le
    exact hNpos (aσ + k * Tg) hNpos_le
  · -- Avoid forbiddenFinite.
    rcases hbadFin_forbid (aσ + k * Tg) with h | h
    · -- Goal: ∀ e ∈ insert 1 Gν, e * (aσ + k*Tg) ∉ forbiddenFinite. Note EE = insert 1 Gν.
      intro e he
      have heE : e ∈ EE := by rw [hEE_def]; exact he
      exact h e heE
    · exfalso; exact hXbadMax_avoid (aσ + k * Tg) hk_AP h
  · -- Avoid main collisions.
    intro j hj h hh e he
    have heE : e ∈ EE := by rw [hEE_def]; exact he
    exact hk_main j hj h hh e heE

/-! ## Correction slots (assembled)

The full correction-slot setup. Given `g ≥ 1` and the data needed for
`finite_switch_values_generate_zmod`, produce the list of correction
denominators `c_ν`, patterns `G_ν`, and increments `b_ν` such that:

  * `b_ν > 0` (positivity of `Q_{G_ν}`)
  * `b_ν ≡ ρ_σ (mod g)` for the assigned residue
  * Reciprocal sum `C_0 := ∑_ν 1/c_ν < δ` (made small by choosing `c_ν` large)
  * Subset sums of `{b_ν}` represent every residue mod `g`
  * No collisions with main slots, between correction slots, etc.

Statement deferred — assembled inside `Theorem1.lean`. -/

end PolynomialEgyptianSums
