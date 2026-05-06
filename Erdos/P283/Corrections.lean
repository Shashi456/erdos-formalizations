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

section ExistsLargeCorrectionDenominator
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

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
  -- The focused claim below packages the final pigeonhole step after the
  -- bookkeeping reductions: positivity threshold, finite-forbidden reduction,
  -- and AP setup.
  obtain ⟨k, hk_AP, hk_main⟩ : ∃ k : ℕ,
      XbadMax ≤ aσ + k * Tg ∧
      (∀ j, J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ EE, e * (aσ + k * Tg) ≠ h * D j) := by
    -- Pigeonhole. The AP segment {aσ + k*Tg : kStart ≤ k ≤ kStart + N} (size N+1)
    -- must exceed the count of "bad" k's: those with e*(aσ + k*Tg) = h*D j for
    -- some h ∈ {1,2,3,6}, e ∈ EE, j ≥ J.
    --
    -- Bound on bad k's: any j contributing such a k must satisfy
    --   D j = e*(aσ+k*Tg)/h ≤ maxE * UpperC, where UpperC = aσ + (kStart+N)*Tg.
    -- Since D j ≥ (j+1)² (as D j = (36j+1)(36j+37) ≥ (j+1)·1 = j+1 ≥ ... wait
    -- D j ≥ (j+1)²? Actually D j ≥ 36j+1 ≥ j+1 always; for the sqrt bound, we
    -- use D j ≥ j+1 only.
    --
    -- Crude (linear) bound: count of j ≥ J with D j ≤ M is at most M
    -- (since D j ≥ j+1 means j ≤ M-1 ≤ M). With this, the bound is:
    --   |bad k's| ≤ 4 * card(EE) * M
    -- which grows linearly. We can't beat AP linear growth this way.
    --
    -- Hence we use the sqrt bound: D j ≥ (j+1)² for j ≥ 0 (since D j =
    -- (36j+1)(36(j+1)+1) ≥ (j+1)(j+1) when 36j+1 ≥ j+1 [iff 35j ≥ 0] and
    -- 36(j+1)+1 ≥ j+1 [iff 35(j+1) ≥ 0], both trivially true).
    -- Hence j+1 ≤ Nat.sqrt(M) (where M = max value of D j).
    classical
    set HE_set : Finset (ℕ × ℕ) := (({1,2,3,6} : Finset ℕ) ×ˢ EE) with hHE_def
    -- Choose kStart so that the AP starts past XbadMax.
    set kStart : ℕ := XbadMax + 1 with hkStart_def
    have hkStart_AP : ∀ k : ℕ, kStart ≤ k → XbadMax ≤ aσ + k * Tg := by
      intro k hk
      have : kStart ≤ k * 1 := by simpa using hk
      have h1 : kStart ≤ k * Tg := by
        calc kStart ≤ k * 1 := this
          _ ≤ k * Tg := Nat.mul_le_mul_left k hTg
      omega
    -- Constant for pigeonhole: each j contributes ≤ |HE_set| bad k's.
    set HEcard : ℕ := HE_set.card with hHEcard_def
    -- Crude size choice.
    -- We need N + 1 > HEcard * (Nat.sqrt(maxE * (aσ + (kStart+N)*Tg)) + 1).
    -- Trick: ensure Nat.sqrt(maxE * (aσ + (kStart+N)*Tg)) ≤ N/(HEcard+1) - 1 (roughly).
    -- Concretely, pick N = (HEcard+1)² * maxE * Tg * 4 + (HEcard+1) * (aσ + kStart*Tg) * 4 + 100.
    set Cbig : ℕ := HEcard + 1 with hCbig_def
    have hCbig_ge : 1 ≤ Cbig := by rw [hCbig_def]; omega
    set baseShift : ℕ := aσ + kStart * Tg with hbaseShift_def
    -- Choose N huge enough that the pigeonhole works.
    -- N = 100 * Cbig² * T + 100, where T = maxE * baseShift + maxE * Tg + 1.
    set N : ℕ := 100 * Cbig * Cbig * (maxE * baseShift + maxE * Tg + 1) + 100 with hN_def
    -- Upper bound on c we'll consider.
    set UpperC : ℕ := aσ + (kStart + N) * Tg with hUpperC_def
    have hUpperC_eq : UpperC = baseShift + N * Tg := by
      rw [hUpperC_def, hbaseShift_def]; ring
    -- The relevant j-range: j ∈ [J, Jbound) where Jbound = Nat.sqrt(maxE * UpperC) + 2.
    set Jbound : ℕ := Nat.sqrt (maxE * UpperC) + 2 with hJbound_def
    -- All j ≥ Jbound have D j > maxE * UpperC, hence e*(aσ + k*Tg) ≠ h*D j for k ≤ kStart+N.
    have hD_lower : ∀ j : ℕ, (j + 1) * (j + 1) ≤ D j := by
      intro j
      unfold D u P
      -- D j = (36j+1) * (36(j+1)+1) ≥ (j+1)*(j+1)
      have h1 : j + 1 ≤ 36 * j + 1 := by omega
      have h2 : j + 1 ≤ 36 * (j + 1) + 1 := by omega
      exact Nat.mul_le_mul h1 h2
    -- For j ≥ Jbound, D j > maxE * UpperC.
    have hD_big : ∀ j : ℕ, Jbound ≤ j → maxE * UpperC < D j := by
      intro j hj
      have h1 : (j + 1) * (j + 1) ≤ D j := hD_lower j
      have hj_lower : Nat.sqrt (maxE * UpperC) + 2 ≤ j := by rw [hJbound_def] at hj; exact hj
      -- (Nat.sqrt(maxE*UpperC) + 1)² > maxE * UpperC
      have h2 : maxE * UpperC < (Nat.sqrt (maxE * UpperC) + 1) * (Nat.sqrt (maxE * UpperC) + 1) := by
        have h := Nat.lt_succ_sqrt (maxE * UpperC)
        -- h : maxE * UpperC < (maxE*UpperC).sqrt.succ * (maxE*UpperC).sqrt.succ
        show maxE * UpperC < (Nat.sqrt (maxE * UpperC) + 1) * (Nat.sqrt (maxE * UpperC) + 1)
        convert h using 2 <;> rfl
      have h3 : (Nat.sqrt (maxE * UpperC) + 1) * (Nat.sqrt (maxE * UpperC) + 1) ≤ (j + 1) * (j + 1) := by
        have hjp : Nat.sqrt (maxE * UpperC) + 1 ≤ j + 1 := by omega
        exact Nat.mul_le_mul hjp hjp
      omega
    -- Define the "bad k" finset within our range.
    set badK_finset : Finset ℕ :=
      (Finset.Ico J Jbound).biUnion (fun j =>
        HE_set.filter (fun he => he.1 * D j ≥ he.2 * aσ ∧ he.2 ∣ (he.1 * D j - he.2 * aσ) ∧ he.2 * Tg ∣ (he.1 * D j - he.2 * aσ))
          |>.image (fun he => (he.1 * D j - he.2 * aσ) / (he.2 * Tg))) with hbadK_def
    -- Key: any k that is "bad" with some j in the relevant range is in badK_finset.
    -- More precisely: if e*(aσ + k*Tg) = h*D j for j ≥ J, h ∈ HE, e ∈ EE, and k ≤ kStart+N,
    -- then j < Jbound, and k ∈ badK_finset.
    have hbadK_contains : ∀ k : ℕ, k ≤ kStart + N →
        (∃ j h e, J ≤ j ∧ h ∈ ({1,2,3,6} : Finset ℕ) ∧ e ∈ EE ∧
          e * (aσ + k * Tg) = h * D j) →
        k ∈ badK_finset := by
      intro k hk_le ⟨j, h, e, hjJ, hh, he, heq⟩
      -- Step 1: j < Jbound.
      have hcle : aσ + k * Tg ≤ UpperC := by
        rw [hUpperC_def]
        have : k * Tg ≤ (kStart + N) * Tg := Nat.mul_le_mul_right Tg hk_le
        omega
      have he_pos : 1 ≤ e := hEE_pos e he
      have he_le : e ≤ maxE := hmaxE_ge e he
      -- e*(aσ + k*Tg) = h * D j ⇒ D j = h⁻¹ * e * (...) ≤ maxE * UpperC (since h ≥ 1)
      have hh_pos : 1 ≤ h := by
        rcases Finset.mem_insert.mp hh with rfl | h2
        · omega
        · rcases Finset.mem_insert.mp h2 with rfl | h3
          · omega
          · rcases Finset.mem_insert.mp h3 with rfl | h4
            · omega
            · simp at h4; omega
      have hD_bound : D j ≤ maxE * UpperC := by
        have h1 : h * D j = e * (aσ + k * Tg) := heq.symm
        have h2 : e * (aσ + k * Tg) ≤ maxE * UpperC :=
          le_trans (Nat.mul_le_mul he_le hcle) (le_refl _)
        have h3 : 1 * D j ≤ h * D j := Nat.mul_le_mul_right _ hh_pos
        have h4 : D j ≤ h * D j := by simpa using h3
        omega
      have hj_lt : j < Jbound := by
        by_contra hj_ge
        push_neg at hj_ge
        exact absurd (hD_big j hj_ge) (not_lt.mpr hD_bound)
      -- Step 2: k ∈ badK_finset.
      rw [hbadK_def]
      refine Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩
      · exact Finset.mem_Ico.mpr ⟨hjJ, hj_lt⟩
      -- Now k ∈ HE_set.filter(...).image(...).
      refine Finset.mem_image.mpr ⟨(h, e), ?_, ?_⟩
      · rw [Finset.mem_filter]
        -- Goals are about (h, e).1 = h and (h, e).2 = e; simplify pair projections.
        simp only [Prod.fst, Prod.snd]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hHE_def]; exact Finset.mem_product.mpr ⟨hh, he⟩
        · -- h * D j ≥ e * aσ since h * D j = e * (aσ + k * Tg) ≥ e * aσ.
          have h0 : e * (aσ + k * Tg) ≥ e * aσ := Nat.mul_le_mul_left e (Nat.le_add_right aσ (k * Tg))
          omega
        · -- e ∣ (h * D j - e * aσ) = e * k * Tg.
          have : h * D j - e * aσ = e * (k * Tg) := by
            have h2 : e * aσ + e * (k * Tg) = h * D j := by
              have := heq
              linarith [Nat.mul_add e aσ (k*Tg)]
            omega
          rw [this]; exact ⟨k * Tg, rfl⟩
        · -- e * Tg ∣ (h * D j - e * aσ).
          have : h * D j - e * aσ = e * (k * Tg) := by
            have h2 : e * aσ + e * (k * Tg) = h * D j := by
              have := heq
              linarith [Nat.mul_add e aσ (k*Tg)]
            omega
          rw [this]
          -- e * Tg ∣ e * (k * Tg) = e * Tg * k
          refine ⟨k, ?_⟩; ring
      · -- the image element equals k
        simp only [Prod.fst, Prod.snd]
        have : h * D j - e * aσ = e * (k * Tg) := by
          have h2 : e * aσ + e * (k * Tg) = h * D j := by
            have := heq
            linarith [Nat.mul_add e aσ (k * Tg)]
          omega
        rw [this]
        -- (e * (k * Tg)) / (e * Tg) = k.
        have he_pos' : 0 < e := he_pos
        have hTg_pos : 0 < Tg := hTg
        have heTg_pos : 0 < e * Tg := Nat.mul_pos he_pos' hTg_pos
        have h_eq : e * (k * Tg) = (e * Tg) * k := by ring
        rw [h_eq, Nat.mul_div_cancel_left _ heTg_pos]
    -- Bound on cardinality: badK_finset has card ≤ (Jbound - J) * HEcard.
    have hbadK_card : badK_finset.card ≤ (Jbound - J) * HEcard := by
      rw [hbadK_def]
      calc ((Finset.Ico J Jbound).biUnion (fun j =>
              HE_set.filter (fun he => he.1 * D j ≥ he.2 * aσ ∧ he.2 ∣ (he.1 * D j - he.2 * aσ) ∧ he.2 * Tg ∣ (he.1 * D j - he.2 * aσ))
                |>.image (fun he => (he.1 * D j - he.2 * aσ) / (he.2 * Tg)))).card
          ≤ ∑ j ∈ Finset.Ico J Jbound, (HE_set.filter _ |>.image _).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ j ∈ Finset.Ico J Jbound, HEcard := by
            apply Finset.sum_le_sum
            intro j _
            exact le_trans (Finset.card_image_le) (Finset.card_filter_le _ _)
        _ = (Finset.Ico J Jbound).card * HEcard := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (Jbound - J) * HEcard := by
            have : (Finset.Ico J Jbound).card ≤ Jbound - J := by
              rw [Nat.card_Ico]
            exact Nat.mul_le_mul_right _ this
    -- AP segment finset.
    set APseg : Finset ℕ := Finset.Icc kStart (kStart + N) with hAPseg_def
    have hAPseg_card : APseg.card = N + 1 := by
      rw [hAPseg_def, Nat.card_Icc]; omega
    -- Pigeonhole: APseg.card > badK_finset.card means ∃ k ∈ APseg, k ∉ badK_finset.
    have hcard_lt : badK_finset.card < APseg.card := by
      rw [hAPseg_card]
      -- Need: badK_finset.card < N + 1.
      have hbk_le : badK_finset.card ≤ Jbound * HEcard :=
        le_trans hbadK_card (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      -- Goal: badK_finset.card < N + 1. Since HEcard < Cbig, suffices Jbound * Cbig ≤ N,
      -- i.e., Nat.sqrt(maxE * UpperC) + 2 ≤ N / Cbig, i.e., Nat.sqrt(maxE * UpperC) * Cbig + 2 * Cbig ≤ N.
      -- Squaring: (Nat.sqrt(maxE * UpperC) * Cbig)² ≤ maxE * UpperC * Cbig² ≤ ?
      -- maxE * UpperC = maxE * baseShift + maxE * Tg * N.
      -- maxE * UpperC * Cbig² ≤ N²/16 if maxE * baseShift * Cbig² ≤ N²/32 and maxE * Tg * N * Cbig² ≤ N²/32.
      -- Second: maxE * Tg * Cbig² ≤ N/32, which holds since N ≥ 16 * Cbig² * maxE * Tg.
      -- First: maxE * baseShift * Cbig² ≤ N²/32. Since N ≥ 16 * Cbig² * maxE * baseShift, N² ≥ 256 * Cbig⁴ * (maxE*baseShift)².
      -- Need 256 * Cbig⁴ * (maxE*baseShift)² ≥ 32 * maxE * baseShift * Cbig², i.e., 8 * Cbig² * maxE * baseShift ≥ 1, ✓.
      -- So Nat.sqrt(maxE * UpperC) * Cbig ≤ N/4 (approximately).
      -- Then Jbound * Cbig = (Nat.sqrt + 2) * Cbig ≤ N/4 + 2 * Cbig ≤ N/4 + N/8 < N (for N large enough).
      have hsqUC : Nat.sqrt (maxE * UpperC) * Nat.sqrt (maxE * UpperC) ≤ maxE * UpperC := Nat.sqrt_le _
      have hUpperC_eq2 : maxE * UpperC = maxE * baseShift + maxE * Tg * N := by
        rw [hUpperC_eq]; ring
      -- Strategy: prove (Nat.sqrt(maxE * UpperC) + 2) * Cbig ≤ N by squaring.
      -- We use: a ≤ b ↔ a * a ≤ b * b for naturals (when b ≥ 0, which is always).
      -- Actually use: (a ≤ b) follows from (a * a ≤ b * b) when b ≥ a.
      -- Cleanest: prove via Nat.le_sqrt. We have ((Nat.sqrt(M) + 2) * Cbig)² ≤ ((sqrt(M))*Cbig + 2*Cbig)²
      -- ≤ ((sqrt(M))*Cbig)² + 2*((sqrt(M))*Cbig)*(2*Cbig) + (2*Cbig)²
      -- = SS²*Cbig² + 4*SS*Cbig² + 4*Cbig²
      -- ≤ M*Cbig² + 4*M*Cbig² + 4*Cbig² (using SS ≤ M when M ≥ 1, else SS = 0)
      -- ... hmm.
      -- OK let me take a direct path using polynomial inequalities.
      set T : ℕ := maxE * baseShift + maxE * Tg + 1 with hT_def
      have hT_ge : 1 ≤ T := by rw [hT_def]; omega
      have hN_def2 : N = 100 * Cbig * Cbig * T + 100 := by
        rw [hN_def, hT_def]
      -- maxE * UpperC ≤ T * (N + 1). Detailed: maxE * baseShift ≤ T * 1, maxE * Tg ≤ T, so maxE * Tg * N ≤ T * N.
      have hUpperC_T : maxE * UpperC ≤ T * (N + 1) := by
        rw [hUpperC_eq2, hT_def]
        have h1 : maxE * baseShift ≤ (maxE * baseShift + maxE * Tg + 1) := by omega
        have h2 : maxE * Tg ≤ (maxE * baseShift + maxE * Tg + 1) := by omega
        have h3 : maxE * Tg * N ≤ (maxE * baseShift + maxE * Tg + 1) * N :=
          Nat.mul_le_mul_right N h2
        calc maxE * baseShift + maxE * Tg * N
            ≤ (maxE * baseShift + maxE * Tg + 1) + (maxE * baseShift + maxE * Tg + 1) * N := by omega
          _ = (maxE * baseShift + maxE * Tg + 1) * (N + 1) := by ring
      -- Substantial bound: SS² ≤ M ≤ T * (N + 1).
      set SS : ℕ := Nat.sqrt (maxE * UpperC) with hSS_def
      have hSSsq : SS * SS ≤ T * (N + 1) := le_trans hsqUC hUpperC_T
      -- We want (SS + 2) * Cbig ≤ N. Since both sides are naturals, suffices ((SS+2)*Cbig)² ≤ N².
      -- ((SS+2)*Cbig)² = (SS+2)² * Cbig² = (SS² + 4*SS + 4) * Cbig².
      -- We have SS² ≤ T*(N+1) and SS ≤ T*(N+1) (as shown below).
      -- So ((SS+2)*Cbig)² ≤ (5*T*(N+1) + 4) * Cbig².
      -- Need (5*T*(N+1) + 4) * Cbig² ≤ N².
      -- Expand: 5 * T * Cbig² * (N+1) + 4 * Cbig² ≤ N².
      -- We have: T * Cbig² ≤ N/100 (since 100 * T * Cbig² ≤ N).
      -- So 5 * T * Cbig² * (N+1) ≤ N/100 * 5 * (N+1) ≤ N² * 5/100 + 5N/100 ≤ N²/20 + N/20.
      -- And 4 * Cbig² ≤ 4 * Cbig² * T * 100 ≤ N (since 100*Cbig²*T ≤ N), so 4 * Cbig² ≤ N ≤ N²/20 (for N ≥ 20).
      -- Total: ≤ N²/20 + N/20 + N²/20 = 2*N²/20 + N/20 ≤ N²/10 + N/20 ≤ N²/2 ≤ N². ✓
      have hSS_le_TN : SS ≤ T * (N + 1) := by
        rcases Nat.eq_zero_or_pos SS with h0 | hpos
        · rw [h0]; exact Nat.zero_le _
        · -- SS² ≤ T*(N+1), and SS ≤ SS² when SS ≥ 1.
          have : SS * 1 ≤ SS * SS := Nat.mul_le_mul_left SS hpos
          rw [Nat.mul_one] at this
          exact le_trans this hSSsq
      have hT_Cbig_le_N : 100 * (Cbig * Cbig * T) ≤ N := by
        have : 100 * (Cbig * Cbig * T) = 100 * Cbig * Cbig * T := by ring
        rw [this, hN_def2]; omega
      -- Auxiliary: T * Cbig² * (N+1) ≤ T * Cbig² * N + T * Cbig².
      -- 100 * T * Cbig² ≤ N, so T * Cbig² ≤ N / 100, so 100 * T * Cbig² ≤ N.
      have hT_Cbig_N : T * Cbig * Cbig ≤ N := by
        have : T * Cbig * Cbig ≤ 100 * T * Cbig * Cbig := by
          have : 1 ≤ 100 := by norm_num
          calc T * Cbig * Cbig = 1 * (T * Cbig * Cbig) := (one_mul _).symm
            _ ≤ 100 * (T * Cbig * Cbig) := Nat.mul_le_mul_right _ this
            _ = 100 * T * Cbig * Cbig := by ring
        have h2 : 100 * T * Cbig * Cbig = 100 * (Cbig * Cbig * T) := by ring
        omega
      -- The big inequality, proved by nlinarith.
      have hkey : (SS + 2) * Cbig ≤ N := by
        -- We use: a ≤ b ↔ a*a ≤ b*b (for a, b nat, equivalent direction).
        -- Suffices: ((SS+2)*Cbig)² ≤ N².
        -- ((SS+2)*Cbig)² = (SS² + 4 SS + 4) * Cbig²
        -- Use SS² ≤ T(N+1), SS ≤ T(N+1).
        -- ≤ (5T(N+1) + 4) * Cbig²
        -- = 5 * T * Cbig² * N + 5 * T * Cbig² + 4 * Cbig².
        -- Each term controlled.
        have hsq_le : ((SS + 2) * Cbig) * ((SS + 2) * Cbig) ≤ N * N := by
          -- LHS = (SS + 2)^2 * Cbig^2 = (SS² + 4 SS + 4) * Cbig²
          have hLHS : ((SS + 2) * Cbig) * ((SS + 2) * Cbig) =
              SS * SS * (Cbig * Cbig) + 4 * SS * (Cbig * Cbig) + 4 * (Cbig * Cbig) := by ring
          rw [hLHS]
          -- Bound each term.
          have hb1 : SS * SS * (Cbig * Cbig) ≤ T * (N + 1) * (Cbig * Cbig) :=
            Nat.mul_le_mul_right _ hSSsq
          have hb2 : 4 * SS * (Cbig * Cbig) ≤ 4 * (T * (N + 1)) * (Cbig * Cbig) := by
            have : 4 * SS ≤ 4 * (T * (N + 1)) := Nat.mul_le_mul_left 4 hSS_le_TN
            exact Nat.mul_le_mul_right _ this
          -- Sum: ≤ 5 * T * (N + 1) * Cbig² + 4 * Cbig².
          have hsum_le : SS * SS * (Cbig * Cbig) + 4 * SS * (Cbig * Cbig) + 4 * (Cbig * Cbig) ≤
              5 * (T * (N + 1)) * (Cbig * Cbig) + 4 * (Cbig * Cbig) := by
            have : SS * SS * (Cbig * Cbig) + 4 * SS * (Cbig * Cbig) ≤
                T * (N + 1) * (Cbig * Cbig) + 4 * (T * (N + 1)) * (Cbig * Cbig) := by
              omega
            have h2 : T * (N + 1) * (Cbig * Cbig) + 4 * (T * (N + 1)) * (Cbig * Cbig) =
                5 * (T * (N + 1)) * (Cbig * Cbig) := by ring
            omega
          -- Final: 5 * T * (N+1) * Cbig² + 4 * Cbig² ≤ N².
          -- Expand: 5 * T * Cbig² * N + 5 * T * Cbig² + 4 * Cbig² ≤ N².
          -- T * Cbig² ≤ N (from hT_Cbig_N), so 5 * T * Cbig² * N ≤ 5 * N² and 5 * T * Cbig² ≤ 5 * N.
          -- 4 * Cbig² ≤ 4 * (T * Cbig²) ≤ 4 * N (using T ≥ 1). Wait, 4 * Cbig² ≤ 4 * Cbig² * T = 4 * (T * Cbig²) ≤ 4 * N.
          -- Sum: 5N² + 5N + 4N = 5N² + 9N. We need ≤ N². NOPE. So 100 not big enough.
          -- WAIT: I need to use that 100 * T * Cbig² ≤ N, NOT just T * Cbig² ≤ N.
          -- So T * Cbig² ≤ N/100. So 5 * T * Cbig² * N ≤ 5N²/100 = N²/20.
          -- Hmm but I wrote hT_Cbig_N : T * Cbig² ≤ N. Looser.
          -- Let me get a tighter bound.
          have hT_Cbig_N_tight : 100 * (T * (Cbig * Cbig)) ≤ N := by
            have h1 : 100 * (T * (Cbig * Cbig)) = 100 * (Cbig * Cbig * T) := by ring
            rw [h1]; exact hT_Cbig_le_N
          -- Now: 5 * T * (N+1) * Cbig² + 4 * Cbig²
          --    = 5 * T * Cbig² * N + 5 * T * Cbig² + 4 * Cbig².
          -- Bound 5 * T * Cbig² * N ≤ 5 * N * N / 100 = N²/20 ≤ N².
          -- Bound 5 * T * Cbig² ≤ 5 * N / 100 ≤ N.
          -- Bound 4 * Cbig² ≤ 4 * (T * Cbig²) ≤ 4 * N / 100 ≤ N.
          -- Sum: N²/20 + N + N ≤ N² (for N large).
          -- Concrete: N²/20 + 2N ≤ N² requires N²/20 - N² + 2N ≤ 0, i.e., -19N²/20 + 2N ≤ 0,
          -- i.e., 2N ≤ 19N²/20, i.e., 40 ≤ 19N, i.e., N ≥ 40/19 ≈ 2.1. Easy since N ≥ 100.
          -- Use nlinarith.
          have hN_100 : 100 ≤ N := by rw [hN_def2]; omega
          -- Let Y := T * (Cbig * Cbig). Have: 100 * Y ≤ N.
          -- Cbig * Cbig ≤ Y (since T ≥ 1).
          have hCsq_le_Y : Cbig * Cbig ≤ T * (Cbig * Cbig) := by
            calc Cbig * Cbig = 1 * (Cbig * Cbig) := (one_mul _).symm
              _ ≤ T * (Cbig * Cbig) := Nat.mul_le_mul_right _ hT_ge
          -- Rewrite LHS in terms of Y.
          -- 5 * (T * (N + 1)) * (Cbig * Cbig) = 5 * (T * (Cbig * Cbig)) * (N + 1)
          --                                  = 5 * Y * N + 5 * Y.
          -- 4 * (Cbig * Cbig) ≤ 4 * Y.
          -- So total ≤ 5*Y*N + 5*Y + 4*Y = 5*Y*N + 9*Y.
          have hLHS_le : 5 * (T * (N + 1)) * (Cbig * Cbig) + 4 * (Cbig * Cbig) ≤
              5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig)) := by
            have h1 : 5 * (T * (N + 1)) * (Cbig * Cbig) =
                5 * (T * (Cbig * Cbig)) * N + 5 * (T * (Cbig * Cbig)) := by ring
            have h2 : 4 * (Cbig * Cbig) ≤ 4 * (T * (Cbig * Cbig)) := by
              apply Nat.mul_le_mul_left; exact hCsq_le_Y
            omega
          -- Now: 5*Y*N + 9*Y ≤ N².
          -- Multiply 100*Y ≤ N by N: 100*Y*N ≤ N*N. So 5*Y*N ≤ N*N/20 ≤ N*N.
          -- Multiply 100*Y ≤ N by 1: 100*Y ≤ N. So 9*Y ≤ 9*N/100 ≤ N (for N ≥ 9*N/100 iff N ≥ 0).
          -- 5*Y*N + 9*Y ≤ ?
          -- Concrete: 100 * (5*Y*N + 9*Y) = 500*Y*N + 900*Y. And 500*Y*N ≤ 5*N*N (mult both sides by 5N), 900*Y ≤ 9*N.
          -- So 100 * (5*Y*N + 9*Y) ≤ 5*N*N + 9*N.
          -- And we want 5*Y*N + 9*Y ≤ N*N. Equivalent to 100*(5*Y*N+9*Y) ≤ 100*N*N.
          -- Have 100*(5*Y*N+9*Y) ≤ 5*N²+9*N. And 5*N²+9*N ≤ 100*N² iff 95N² ≥ 9N iff N(95N-9) ≥ 0 ✓.
          have hY_bound : 5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig)) ≤ N * N := by
            -- 100 * (5*Y*N + 9*Y) ≤ 5*N² + 9*N ≤ 100*N² (for N ≥ 1).
            -- Step 1: 100 * Y * N ≤ N * N (from 100 * Y ≤ N).
            have step1 : 100 * (T * (Cbig * Cbig)) * N ≤ N * N := by
              have := Nat.mul_le_mul_right N hT_Cbig_N_tight
              linarith
            -- Step 2: 5 * Y * N ≤ N * N (since 5 ≤ 100).
            have step2 : 5 * (T * (Cbig * Cbig)) * N ≤ N * N := by
              have h : 5 * (T * (Cbig * Cbig)) * N ≤ 100 * (T * (Cbig * Cbig)) * N := by
                have : (5 : ℕ) ≤ 100 := by norm_num
                nlinarith
              linarith
            -- Step 3: 9 * Y ≤ N (from 100 * Y ≤ N and 9 ≤ 100).
            have step3 : 9 * (T * (Cbig * Cbig)) ≤ N := by
              have : 9 * (T * (Cbig * Cbig)) ≤ 100 * (T * (Cbig * Cbig)) := by
                have : (9 : ℕ) ≤ 100 := by norm_num
                nlinarith
              linarith
            -- Step 4: combine. Need 5*Y*N + 9*Y ≤ N². Use step2 + step3, but they're separate bounds.
            -- 5*Y*N + 9*Y ≤ N*N + N. We need ≤ N*N. Hmm, off by N.
            -- BUT step2 actually gives 5*Y*N ≤ N²/20, which gives lots of room. Let me use a tighter form.
            -- Tighter: from 100 * Y ≤ N, we get 5 * Y ≤ N/20. So 5*Y*N + 9*Y = Y * (5N + 9) ≤ ?
            -- Y * (5N + 9). 100 * Y * (5N + 9) ≤ N * (5N + 9) = 5*N² + 9*N.
            -- We want Y*(5N+9) ≤ N². Equivalent: 100 * Y * (5N+9) ≤ 100 * N². Have ≤ 5N²+9N. Need ≤ 100 N². ✓.
            have step4 : 100 * (5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig))) ≤ 5 * (N * N) + 9 * N := by
              -- = 500 * Y * N + 900 * Y. Bound each.
              -- 500 * Y * N = 5 * (100 * Y * N) ≤ 5 * (N * N) = 5*N².
              -- 900 * Y = 9 * (100 * Y) ≤ 9 * N.
              have ha : 500 * (T * (Cbig * Cbig)) * N ≤ 5 * (N * N) := by
                have : 5 * (100 * (T * (Cbig * Cbig)) * N) = 500 * (T * (Cbig * Cbig)) * N := by ring
                have h2 := Nat.mul_le_mul_left 5 step1
                linarith
              have hb : 900 * (T * (Cbig * Cbig)) ≤ 9 * N := by
                have : 9 * (100 * (T * (Cbig * Cbig))) = 900 * (T * (Cbig * Cbig)) := by ring
                have h2 := Nat.mul_le_mul_left 9 hT_Cbig_N_tight
                linarith
              -- 100 * (5*Y*N + 9*Y) = 500 * Y * N + 900 * Y ≤ 5*N² + 9*N.
              have hexpand : 100 * (5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig))) =
                  500 * (T * (Cbig * Cbig)) * N + 900 * (T * (Cbig * Cbig)) := by ring
              linarith
            -- Now 5 * N² + 9 * N ≤ 100 * N² for N ≥ 1.
            have step5 : 5 * (N * N) + 9 * N ≤ 100 * (N * N) := by
              have h1 : 9 * N ≤ 95 * (N * N) := by
                -- 9 N ≤ 95 N² iff 9 ≤ 95 N iff N ≥ 9/95 ≈ 0.1. Since N ≥ 100, easy.
                have hN_le_NN : N ≤ N * N := by
                  rcases Nat.eq_zero_or_pos N with hn | hp
                  · rw [hn]
                  · calc N = N * 1 := (Nat.mul_one _).symm
                      _ ≤ N * N := Nat.mul_le_mul_left _ hp
                have h2 : 9 * N ≤ 9 * (N * N) := Nat.mul_le_mul_left 9 hN_le_NN
                have h3 : 9 * (N * N) ≤ 95 * (N * N) :=
                  Nat.mul_le_mul_right _ (by norm_num : (9 : ℕ) ≤ 95)
                linarith
              linarith
            -- Combine: 100 * (5 Y N + 9 Y) ≤ 5N² + 9N ≤ 100 N², so 5YN + 9Y ≤ N².
            have h6 : 100 * (5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig))) ≤ 100 * (N * N) :=
              le_trans step4 step5
            exact Nat.le_of_mul_le_mul_left h6 (by norm_num : 0 < 100)
          linarith
        -- Convert ((SS+2)*Cbig)² ≤ N² to (SS+2)*Cbig ≤ N.
        have hh : (SS + 2) * Cbig ≤ N := by
          rw [show N * N = N ^ 2 from by ring,
              show ((SS + 2) * Cbig) * ((SS + 2) * Cbig) = ((SS + 2) * Cbig) ^ 2 from by ring] at hsq_le
          have := (Nat.pow_le_pow_iff_left (n := 2) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq_le
          exact this
        exact hh
      have hbk_lt : badK_finset.card < N + 1 := by
        have h1 : Jbound = Nat.sqrt (maxE * UpperC) + 2 := hJbound_def
        have h2 : Jbound * HEcard ≤ Jbound * Cbig := by
          apply Nat.mul_le_mul_left
          rw [hCbig_def]; omega
        have h3 : Jbound * Cbig ≤ N := by rw [h1]; exact hkey
        omega
      exact hbk_lt
    obtain ⟨k, hk_mem, hk_notin⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
    rw [hAPseg_def] at hk_mem
    have hk_ge : kStart ≤ k := (Finset.mem_Icc.mp hk_mem).1
    have hk_le : k ≤ kStart + N := (Finset.mem_Icc.mp hk_mem).2
    refine ⟨k, hkStart_AP k hk_ge, ?_⟩
    intro j hjJ h hh e he heq
    apply hk_notin
    exact hbadK_contains k hk_le ⟨j, h, e, hjJ, hh, he, heq⟩
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
end ExistsLargeCorrectionDenominator

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
