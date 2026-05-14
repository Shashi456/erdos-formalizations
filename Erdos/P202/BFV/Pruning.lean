/-
Erdos Problem 202 -- BFV pruning theorem.

This file proves `bfv_pruning_theorem`, the pruning interface consumed by the
upper-bound argument.
-/

import Mathlib
import Erdos.P202.BFVInputs
import Erdos.P202.BFV.Filtering
import Erdos.P202.BFV.HExpRare
import Erdos.P202.BFV.RadMultiplicity
import Erdos.P202.BFV.OmegaTail
import Erdos.P202.BFV.LowerBoundInput

namespace Erdos202

open Filter Finset

lemma eventually_Zscale_ge_const (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Zscale N := by
  let B : ℝ := max A 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hBnonneg : 0 ≤ B := hBpos.le
  filter_upwards [eventually_Mscale_ge 1 zero_lt_one,
      eventually_sqrt_loglog_ge (Real.sqrt B),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hM hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsq :
      (Real.sqrt B) ^ 2 ≤
        (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg B) hsqrt 2
  have hloglog_ge_B : B ≤ Real.log (Real.log (N : ℝ)) := by
    simpa [Real.sq_sqrt hBnonneg, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZ := Mscale_mul_loglog_eq_Zscale hNlarge
  have hB_le_Z : B ≤ Zscale N := by
    rw [← hZ]
    nlinarith [hM, hloglog_ge_B, hBpos.le]
  exact (le_max_left A 1).trans hB_le_Z

lemma eventually_Lscale_neg_le_const {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Lscale (-A) N ≤ c := by
  filter_upwards [eventually_Zscale_ge_const ((-Real.log c) / A)] with N hZ
  rw [Lscale]
  exact (Real.le_log_iff_exp_le hc).1 (by
    have hmul : -Real.log c ≤ A * Zscale N := by
      simpa [mul_comm] using (div_le_iff₀ hA).1 hZ
    nlinarith)

lemma eventually_const_le_Lscale {A C : ℝ} (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, C ≤ Lscale A N := by
  by_cases hC : C ≤ 0
  · filter_upwards with N
    exact hC.trans (Lscale_nonneg A N)
  · have hCpos : 0 < C := lt_of_not_ge hC
    filter_upwards [eventually_Zscale_ge_const (Real.log C / A)] with N hZ
    rw [Lscale]
    exact (Real.log_le_iff_le_exp hCpos).1 (by
      have hmul : Real.log C ≤ A * Zscale N := by
        simpa [mul_comm] using (div_le_iff₀ hA).1 hZ
      exact hmul)

lemma eventually_const_mul_Zscale_le_Lscale {C η : ℝ}
    (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, C * Zscale N ≤ Lscale η N := by
  have hηsq_pos : 0 < η ^ 2 := sq_pos_of_pos hη
  filter_upwards [eventually_Zscale_ge_const (4 * C / η ^ 2)] with N hZlarge
  let x : ℝ := η * Zscale N / 2
  have hZ_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hfactor : 2 * C / η ≤ x := by
    dsimp [x]
    rw [div_le_iff₀ hη]
    have hmul' : 4 * C ≤ η ^ 2 * Zscale N := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hηsq_pos).1 hZlarge
    have hmul'' : 4 * C ≤ η * (η * Zscale N) := by
      simpa [pow_two, mul_assoc] using hmul'
    nlinarith
  have hCZ_eq : C * Zscale N = (2 * C / η) * x := by
    dsimp [x]
    field_simp [hη.ne']
  have hCZ_le_xsq : C * Zscale N ≤ x ^ 2 := by
    rw [hCZ_eq, pow_two]
    exact mul_le_mul_of_nonneg_right hfactor hx_nonneg
  have hx_le_exp : x ≤ Real.exp x := by
    calc
      x ≤ 1 + x := by linarith
      _ ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hxsq_le : x ^ 2 ≤ Real.exp (2 * x) := by
    calc
      x ^ 2 = x * x := by ring
      _ ≤ Real.exp x * Real.exp x := by
            exact mul_le_mul hx_le_exp hx_le_exp hx_nonneg (Real.exp_pos x).le
      _ = Real.exp (2 * x) := by
            rw [← Real.exp_add]
            ring_nf
  calc
    C * Zscale N ≤ x ^ 2 := hCZ_le_xsq
    _ ≤ Real.exp (2 * x) := hxsq_le
    _ = Lscale η N := by
          dsimp [x, Lscale]
          congr 1
          ring

lemma eventually_Mscale_le_Zscale :
    ∀ᶠ N : ℕ in atTop, Mscale N ≤ Zscale N := by
  filter_upwards [eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    have hsq :
        (1 : ℝ) ^ 2 ≤
          (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hsqrt 2
    simpa [Real.sq_sqrt hloglog_nonneg] using hsq
  rw [← Mscale_mul_loglog_eq_Zscale hNlarge]
  exact le_mul_of_one_le_right (Mscale_nonneg N) hloglog_ge_one

lemma eventually_floor_threeM_succ_le_Lscale
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      ((Nat.floor (3 * Mscale N) + 1 : ℕ) : ℝ) ≤ Lscale η N := by
  filter_upwards [eventually_Mscale_le_Zscale,
      eventually_Zscale_ge_const 1,
      eventually_const_mul_Zscale_le_Lscale (C := 4) (by norm_num) hη] with
    N hMleZ hZge h4Z
  have hfloor :
      ((Nat.floor (3 * Mscale N) : ℕ) : ℝ) ≤ 3 * Mscale N := by
    exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
  calc
    ((Nat.floor (3 * Mscale N) + 1 : ℕ) : ℝ)
        = ((Nat.floor (3 * Mscale N) : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ 3 * Mscale N + 1 := by linarith
    _ ≤ 3 * Zscale N + Zscale N := by nlinarith
    _ = 4 * Zscale N := by ring
    _ ≤ Lscale η N := h4Z

lemma q_card_lower_from_bfv_lower
    {ε η : ℝ} {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ)) :
    (N : ℝ) * Lscale (-(1 + η + ε)) N ≤ (Q.card : ℝ) := by
  calc
    (N : ℝ) * Lscale (-(1 + η + ε)) N
        = ((N : ℝ) * Lscale (-(1 + η)) N) * Lscale (-ε) N := by
            rw [show -(1 + η + ε) = -(1 + η) + -ε by ring, Lscale_add]
            ring
    _ ≤ (f N : ℝ) * Lscale (-ε) N := by
          exact mul_le_mul_of_nonneg_right hf (Lscale_nonneg (-ε) N)
    _ ≤ (Q.card : ℝ) := hQ

lemma eventually_nat_mul_Lscale_neg_gt_one (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, 1 < (N : ℝ) * Lscale (-A) N := by
  let B : ℝ := max (A + 1) 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right (A + 1) 1)
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge B hBpos] with N hN hM
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
  have hNposNat : 0 < N := by
    exact Nat.pos_of_ne_zero (by
      intro h0
      have : ((N : ℕ) : ℝ) = 0 := by simp [h0]
      linarith [show (0 : ℝ) < Real.exp 1 from Real.exp_pos 1])
  have hZpos : 0 < Zscale N := Zscale_pos_of_exp_one_lt_nat hNlarge
  have hMgeA1 : A + 1 ≤ Mscale N := (le_max_left (A + 1) 1).trans hM
  have hlog_eq : Real.log ((N : ℝ) * Lscale (-A) N) =
      Real.log (N : ℝ) + (-A) * Zscale N :=
    log_nat_mul_Lscale hNposNat (-A)
  have hMZ := Mscale_mul_Zscale_eq_log hNlarge
  have hlog_pos :
      0 < Real.log ((N : ℝ) * Lscale (-A) N) := by
    rw [hlog_eq, ← hMZ]
    have hdiff : 1 ≤ Mscale N - A := by linarith
    nlinarith
  have htarget_nonneg : 0 ≤ (N : ℝ) * Lscale (-A) N :=
    mul_nonneg (by positivity) (Lscale_nonneg (-A) N)
  exact (Real.log_pos_iff htarget_nonneg).1 hlog_pos

lemma omega_pos_of_one_lt {n : ℕ} (hn : 1 < n) : 1 ≤ omega n := by
  by_contra h
  have homega : omega n = 0 := by omega
  have hnne : n ≠ 0 := by omega
  have hnone : n = 1 := eq_one_of_omega_eq_zero hnne homega
  omega

lemma eventually_omega_pos_of_modulus_lower :
    ∀ᶠ N : ℕ in atTop,
      ∀ q : ℕ, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) → 1 ≤ omega q := by
  filter_upwards [eventually_nat_mul_Lscale_neg_gt_one 2] with N hlarge q hq
  have hq_gt_one_real : (1 : ℝ) < (q : ℝ) := hlarge.trans_le hq
  have hq_gt_one : 1 < q := by exact_mod_cast hq_gt_one_real
  exact omega_pos_of_one_lt hq_gt_one

lemma nat_mul_Lscale_neg_le_fraction_of_nat_mul_Lscale_neg
    {A B δ : ℝ} (hAB : B + δ ≤ A) (N : ℕ) :
    (N : ℝ) * Lscale (-A) N ≤
      Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) := by
  have hmono : Lscale (-A) N ≤ Lscale (-(B + δ)) N := by
    exact Lscale_mono_in_alpha (by linarith) N
  calc
    (N : ℝ) * Lscale (-A) N
        ≤ (N : ℝ) * Lscale (-(B + δ)) N := by
          exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) := by
          rw [show -(B + δ) = -B + -δ by ring, Lscale_add]
          ring

lemma nat_mul_Lscale_neg_le_fraction_of_card
    {A B δ : ℝ} (hAB : B + δ ≤ A) {N : ℕ} {Q : Finset ℕ}
    (hQ : (N : ℝ) * Lscale (-B) N ≤ (Q.card : ℝ)) :
    (N : ℝ) * Lscale (-A) N ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  calc
    (N : ℝ) * Lscale (-A) N
        ≤ Lscale (-δ) N * ((N : ℝ) * Lscale (-B) N) :=
          nat_mul_Lscale_neg_le_fraction_of_nat_mul_Lscale_neg hAB N
    _ ≤ Lscale (-δ) N * (Q.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hQ (Lscale_nonneg (-δ) N)

lemma floor_nat_mul_Lscale_neg_le_fraction_of_card
    {A B δ : ℝ} (hAB : B + δ ≤ A) {N : ℕ} {Q : Finset ℕ}
    (hQ : (N : ℝ) * Lscale (-B) N ≤ (Q.card : ℝ)) :
    (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have htarget_nonneg :
      0 ≤ (N : ℝ) * Lscale (-A) N :=
    mul_nonneg (by positivity) (Lscale_nonneg (-A) N)
  exact (Nat.floor_le htarget_nonneg).trans
    (nat_mul_Lscale_neg_le_fraction_of_card hAB hQ)

lemma floor_nat_mul_Lscale_neg_le_near_extremal_fraction
    {A ε η δ : ℝ} (hAB : 1 + η + ε + δ ≤ A)
    {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ)) :
    (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hQlower :
      (N : ℝ) * Lscale (-(1 + η + ε)) N ≤ (Q.card : ℝ) :=
    q_card_lower_from_bfv_lower hQ hf
  exact floor_nat_mul_Lscale_neg_le_fraction_of_card
    (A := A) (B := 1 + η + ε) (δ := δ) (by linarith) hQlower

lemma card_filter_natCast_lt_le_floor {S : Finset ℕ} {X : ℝ}
    (hX : 0 ≤ X) (hpos : ∀ n ∈ S, 1 ≤ n) :
    (S.filter (fun n : ℕ => (n : ℝ) < X)).card ≤ Nat.floor X := by
  classical
  have hsub :
      (S.filter (fun n : ℕ => (n : ℝ) < X)) ⊆ Finset.Icc 1 (Nat.floor X) := by
    intro n hn
    have hnS : n ∈ S := (Finset.mem_filter.1 hn).1
    have hnlt : (n : ℝ) < X := (Finset.mem_filter.1 hn).2
    exact Finset.mem_Icc.2 ⟨hpos n hnS, (Nat.le_floor_iff hX).2 hnlt.le⟩
  have hcard := Finset.card_le_card hsub
  have hIcc_le : (Finset.Icc 1 (Nat.floor X)).card ≤ Nat.floor X := by
    rw [Nat.card_Icc]
    omega
  exact hcard.trans hIcc_le

lemma small_moduli_in_admissible_count
    {N : ℕ} {Q : Finset ℕ}
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) :
    (Q.filter (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card
      ≤ Nat.floor ((N : ℝ) * Lscale (-2) N) := by
  exact card_filter_natCast_lt_le_floor
    (mul_nonneg (by positivity) (Lscale_nonneg (-2) N))
    (fun q hq => (hRange q hq).1)

lemma small_moduli_count_le_near_extremal_fraction
    {ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ 2)
    {N : ℕ} {Q : Finset ℕ}
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ)) :
    ((Q.filter
        (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount := small_moduli_in_admissible_count (N := N) (Q := Q) hRange
  have hcount_real :
      (((Q.filter
        (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-2) N) : ℝ) := by
    exact_mod_cast hcount
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := 2) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma hExp_bad_count_le_near_extremal_fraction
    {A ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ A)
    {N : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ))
    (hRare :
      (Q.filter fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N)) :
    (((Q.filter
        fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card : ℕ) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount_real :
      (((Q.filter
        fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) := by
    exact_mod_cast hRare
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := A) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma omega_tail_subset_count
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ,
        Q ⊆ Finset.Icc 1 N →
        ∀ t : ℕ, (t : ℝ) ≤ 3 * Mscale N →
          let α : ℝ := (t : ℝ) / Mscale N
          (Q.filter fun q => t ≤ omega q).card
            ≤ Nat.floor
                ((N : ℝ) * Real.exp ((-α / 2 + ε) * Zscale N)) := by
  filter_upwards [bfv_omega_tail_theorem ε hε] with N htail Q hQ t ht
  have hsub :
      (Q.filter fun q => t ≤ omega q) ⊆
        (Finset.Icc 1 N).filter fun q => t ≤ omega q := by
    intro q hq
    exact Finset.mem_filter.2
      ⟨hQ (Finset.mem_filter.1 hq).1, (Finset.mem_filter.1 hq).2⟩
  exact (Finset.card_le_card hsub).trans (htail N t le_rfl ht)

lemma omega_bad_count_le_near_extremal_fraction
    {A ε η δ : ℝ} (hmargin : 1 + η + ε + δ ≤ A)
    {N t : ℕ} {Q : Finset ℕ}
    (hQ : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N)
    (hf : (N : ℝ) * Lscale (-(1 + η)) N ≤ (f N : ℝ))
    (hTail :
      (Q.filter fun q : ℕ => t ≤ omega q).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N)) :
    (((Q.filter fun q : ℕ => t ≤ omega q).card : ℕ) : ℝ) ≤
      Lscale (-δ) N * (Q.card : ℝ) := by
  have hcount_real :
      (((Q.filter fun q : ℕ => t ≤ omega q).card : ℕ) : ℝ) ≤
        (Nat.floor ((N : ℝ) * Lscale (-A) N) : ℝ) := by
    exact_mod_cast hTail
  exact hcount_real.trans
    (floor_nat_mul_Lscale_neg_le_near_extremal_fraction
      (A := A) (ε := ε) (η := η) (δ := δ) hmargin hQ hf)

lemma omega_floor_threeM_tail_subset_count :
    ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ,
        Q ⊆ Finset.Icc 1 N →
          (Q.filter
              (fun q : ℕ => Nat.floor (3 * Mscale N) ≤ omega q)).card
            ≤ Nat.floor ((N : ℝ) * Lscale (-(4 / 3)) N) := by
  have hτ : (0 : ℝ) < 1 / 24 := by norm_num
  filter_upwards [omega_tail_subset_count (1 / 24) hτ,
      eventually_Mscale_ge 4 (by norm_num),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N htail hMge hNlarge_nat Q hQ
  let t : ℕ := Nat.floor (3 * Mscale N)
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hZnonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have ht_le : (t : ℝ) ≤ 3 * Mscale N := by
    dsimp [t]
    exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
  have ht_count := htail Q hQ t ht_le
  have ht_lower : 3 * Mscale N - 1 < (t : ℝ) := by
    have hlt : 3 * Mscale N < (t : ℝ) + 1 := by
      dsimp [t]
      exact Nat.lt_floor_add_one (3 * Mscale N)
    linarith
  have halpha_lower : (11 / 4 : ℝ) ≤ (t : ℝ) / Mscale N := by
    have hdiv : (3 * Mscale N - 1) / Mscale N < (t : ℝ) / Mscale N :=
      div_lt_div_of_pos_right ht_lower hMpos
    have hM_inv : 1 / Mscale N ≤ (1 / 4 : ℝ) := by
      exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hMge)
    have hthree_sub : (11 / 4 : ℝ) ≤ 3 - 1 / Mscale N := by
      linarith
    have hdiv_eq : (3 * Mscale N - 1) / Mscale N = 3 - 1 / Mscale N := by
      field_simp [hMpos.ne']
    linarith
  have hexp_scale :
      (N : ℝ) *
          Real.exp ((-((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ)) *
            Zscale N)
        ≤ (N : ℝ) * Lscale (-(4 / 3)) N := by
    have hcoeff :
        -((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ) ≤ -(4 / 3 : ℝ) := by
      nlinarith
    have hexp :
        Real.exp ((-((t : ℝ) / Mscale N) / 2 + (1 / 24 : ℝ)) *
            Zscale N)
          ≤ Lscale (-(4 / 3)) N := by
      rw [Lscale]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hcoeff hZnonneg)
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  exact ht_count.trans (Nat.floor_mono hexp_scale)

lemma eventually_radical_multiplicity_ceiling_le_Lscale
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ 3 * Mscale N →
        (Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K) : ℝ) ≤
          Lscale ε N := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_nonneg : 0 ≤ Real.log 2 := hlog2_pos.le
  let Clog : ℝ := 9 * Real.log 2 / ε
  have hClog_pos : 0 < Clog := by
    dsimp [Clog]
    positivity
  filter_upwards [eventually_Zscale_ge_const (3 * Real.log 2 / ε),
      eventually_sqrt_loglog_ge (6 / ε),
      eventually_sqrt_loglog_ge (Real.sqrt Clog),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hZconst hsqrtloglog hsqrtClog hNlarge_nat K hK
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsqrtlog_nonneg : 0 ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_nonneg _
  have hsqrtloglog_nonneg :
      0 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    Real.sqrt_nonneg _
  have hloglog_ge_Clog : Clog ≤ Real.log (Real.log (N : ℝ)) := by
    have hsq :
        (Real.sqrt Clog) ^ 2 ≤
          (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg Clog) hsqrtClog 2
    simpa [Real.sq_sqrt hClog_pos.le, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZsqrt := Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge
  have hZloglog := Mscale_mul_loglog_eq_Zscale hNlarge
  let a : ℝ := (ε / 3) * Zscale N
  have htwo : (2 : ℝ) ≤ Real.exp a := by
    have hlog_le : Real.log 2 ≤ a := by
      dsimp [a]
      have hzmul : 3 * Real.log 2 ≤ ε * Zscale N := by
        simpa [mul_comm] using (div_le_iff₀ hε).1 hZconst
      nlinarith
    exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).1 hlog_le
  have hHsq : hExpCutoff N ^ 2 ≤ Real.exp a := by
    have hcoeff : 2 ≤ (ε / 3) *
        Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      have hmul : 6 ≤ ε * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
        simpa [mul_comm] using (div_le_iff₀ hε).1 hsqrtloglog
      nlinarith
    have hexp_arg :
        2 * Real.sqrt (Real.log (N : ℝ)) ≤ a := by
      dsimp [a]
      rw [hZsqrt]
      calc
        2 * Real.sqrt (Real.log (N : ℝ))
            ≤ ((ε / 3) * Real.sqrt (Real.log (Real.log (N : ℝ)))) *
                Real.sqrt (Real.log (N : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hcoeff hsqrtlog_nonneg
        _ = (ε / 3) *
              (Real.sqrt (Real.log (N : ℝ)) *
                Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
              ring
    have hHsq_eq :
        hExpCutoff N ^ 2 = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
      simp [hExpCutoff, pow_two, ← Real.exp_add, two_mul]
    rw [hHsq_eq]
    exact Real.exp_le_exp.2 hexp_arg
  have hpow : (2 : ℝ) ^ K ≤ Real.exp a := by
    have hlog_le : Real.log ((2 : ℝ) ^ K) ≤ a := by
      rw [Real.log_pow]
      dsimp [a]
      rw [← hZloglog]
      calc
        (K : ℝ) * Real.log 2
            ≤ (3 * Mscale N) * Real.log 2 := by
              exact mul_le_mul_of_nonneg_right hK hlog2_nonneg
        _ = Mscale N * (3 * Real.log 2) := by ring
        _ ≤ Mscale N * ((ε / 3) *
              Real.log (Real.log (N : ℝ))) := by
              have hmain : 3 * Real.log 2 ≤ (ε / 3) *
                  Real.log (Real.log (N : ℝ)) := by
                dsimp [Clog] at hloglog_ge_Clog
                have hmul : 9 * Real.log 2 ≤
                    ε * Real.log (Real.log (N : ℝ)) := by
                  simpa [mul_comm] using (div_le_iff₀ hε).1 hloglog_ge_Clog
                nlinarith
              exact mul_le_mul_of_nonneg_left hmain (Mscale_nonneg N)
        _ = (ε / 3) *
              (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
        _ = ε / 3 * (Mscale N * Real.log (Real.log (N : ℝ))) := by ring
    exact (Real.log_le_iff_le_exp (by positivity : 0 < (2 : ℝ) ^ K)).1 hlog_le
  let X : ℝ := hExpCutoff N ^ 2 * (2 : ℝ) ^ K
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hH_ge_one : 1 ≤ hExpCutoff N := by
    rw [show (1 : ℝ) = Real.exp 0 by simp, hExpCutoff]
    exact Real.exp_le_exp.2 (Real.sqrt_nonneg _)
  have hHsq_ge_one : 1 ≤ hExpCutoff N ^ 2 := by
    nlinarith [hH_ge_one]
  have hpow_ge_one : 1 ≤ (2 : ℝ) ^ K := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hX_ge_one : 1 ≤ X := by
    dsimp [X]
    nlinarith [mul_le_mul hHsq_ge_one hpow_ge_one
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ hExpCutoff N ^ 2)]
  have hceil_le : (Nat.ceil X : ℝ) ≤ 2 * X := by
    have hceil_lt : (Nat.ceil X : ℝ) < X + 1 := Nat.ceil_lt_add_one hX_nonneg
    linarith
  have htwoX : 2 * X ≤ Lscale ε N := by
    dsimp [X]
    calc
      2 * (hExpCutoff N ^ 2 * (2 : ℝ) ^ K)
          ≤ Real.exp a * (Real.exp a * Real.exp a) := by
            nlinarith [htwo, hHsq, hpow,
              Real.exp_pos a, hX_nonneg]
      _ = Real.exp (3 * a) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
      _ = Lscale ε N := by
            dsimp [a, Lscale]
            congr 1
            ring
  exact hceil_le.trans htwoX

lemma card_lower_of_mul_factor_le_Lscale
    {S S' : Finset ℕ} {C N : ℕ} {η : ℝ}
    (hcard : S.card ≤ C * S'.card)
    (hC : (C : ℝ) ≤ Lscale η N) :
    (S.card : ℝ) * Lscale (-η) N ≤ (S'.card : ℝ) := by
  have hcard_real : (S.card : ℝ) ≤ (C : ℝ) * (S'.card : ℝ) := by
    exact_mod_cast hcard
  have hfactor :
      (C : ℝ) * (S'.card : ℝ) ≤
        Lscale η N * (S'.card : ℝ) := by
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  have hmain : (S.card : ℝ) ≤ Lscale η N * (S'.card : ℝ) :=
    hcard_real.trans hfactor
  calc
    (S.card : ℝ) * Lscale (-η) N
        ≤ (Lscale η N * (S'.card : ℝ)) * Lscale (-η) N := by
          exact mul_le_mul_of_nonneg_right hmain (Lscale_nonneg (-η) N)
    _ = (S'.card : ℝ) * (Lscale η N * Lscale (-η) N) := by ring
    _ = (S'.card : ℝ) := by
          rw [show Lscale η N * Lscale (-η) N = 1 by
            rw [mul_comm, Lscale_neg_mul]]
          ring

lemma prunedData_of_subset {N : ℕ} {Q S : Finset ℕ} (a : ResidueAssignment Q)
    (hsub : S ⊆ Q)
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hDisj : PairwiseDisjointResidues Q a)
    (hSnonempty : S.Nonempty)
    (K : ℕ)
    (hKpos : 1 ≤ K)
    (hModLower : ∀ q ∈ S, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ))
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ hExpCutoff N)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hKbound : (K : ℝ) ≤ 3 * Mscale N)
    (hRadInj : ∀ q ∈ S, ∀ r ∈ S, rad q = rad r → q = r) :
    ∃ D : PrunedData N, D.Q = S ∧ D.K = K ∧
      (D.Q.card : ℝ) = (S.card : ℝ) := by
  let aS : ResidueAssignment S := restrictAssignment a hsub
  have hAdmissible : Admissible N S := by
    constructor
    · intro q hq
      exact hRange q (hsub hq)
    · exact ⟨aS, PairwiseDisjointResidues.mono hDisj hsub⟩
  refine ⟨{
      Q := S
      Q_nonempty := hSnonempty
      a := aS
      admissible := hAdmissible
      pairwise_disjoint := PairwiseDisjointResidues.mono hDisj hsub
      K := K
      K_pos := hKpos
      modulus_lower := hModLower
      modulus_upper := ?_
      hExp_bound := ?_
      omega_eq := hOmega
      K_bound := hKbound
      rad_injective := hRadInj
    }, rfl, rfl, rfl⟩
  · intro q hq
    exact (hRange q (hsub hq)).2
  · intro q hq
    simpa [hExpCutoff] using hHExp q hq

lemma rad_fiber_card_le_ceiling {S : Finset ℕ} {K : ℕ} {H : ℝ}
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    ∀ r ∈ S.image rad,
      (S.filter fun q => rad q = r).card ≤ Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) := by
  intro r hr
  let F : Finset ℕ := S.filter fun q => rad q = r
  have hFpos : ∀ q ∈ F, q ≠ 0 := by
    intro q hq
    exact hSpos q (Finset.mem_filter.1 hq).1
  have hF :
      ∀ q ∈ F, rad q = r ∧ omega q = K ∧ (hExp q : ℝ) ≤ H := by
    intro q hq
    exact ⟨(Finset.mem_filter.1 hq).2,
      hOmega q (Finset.mem_filter.1 hq).1,
      hHExp q (Finset.mem_filter.1 hq).1⟩
  have hreal := rad_multiplicity_bfv33 F r K H hH hFpos hF
  have hceil : H ^ 2 * (2 : ℝ) ^ K ≤
      (Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

lemma choose_rad_representatives {S : Finset ℕ} {K : ℕ} {H : ℝ}
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hOmega : ∀ q ∈ S, omega q = K)
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    ∃ S' : Finset ℕ,
      S' ⊆ S ∧
      (∀ q ∈ S', ∀ r ∈ S', rad q = rad r → q = r) ∧
      S.card ≤ Nat.ceil (H ^ 2 * (2 : ℝ) ^ K) * S'.card := by
  exact choose_one_per_fiber_card_lower S rad
    (Nat.ceil (H ^ 2 * (2 : ℝ) ^ K))
    (rad_fiber_card_le_ceiling hH hSpos hOmega hHExp)

lemma exists_prunedData_after_radical_selection
    {N K : ℕ} {Q S : Finset ℕ} (a : ResidueAssignment Q)
    (hsub : S ⊆ Q)
    (hRange : ∀ q ∈ Q, 1 ≤ q ∧ q ≤ N)
    (hDisj : PairwiseDisjointResidues Q a)
    (hSnonempty : S.Nonempty)
    (hKpos : 1 ≤ K)
    (hKbound : (K : ℝ) ≤ 3 * Mscale N)
    (hH : 1 ≤ hExpCutoff N)
    (hModLower : ∀ q ∈ S, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ))
    (hHExp : ∀ q ∈ S, (hExp q : ℝ) ≤ hExpCutoff N)
    (hOmega : ∀ q ∈ S, omega q = K) :
    ∃ D : PrunedData N,
      S.card ≤ Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K) * D.Q.card := by
  have hSpos : ∀ q ∈ S, q ≠ 0 := by
    intro q hq
    have hqpos : 1 ≤ q := (hRange q (hsub hq)).1
    omega
  rcases choose_rad_representatives
      (S := S) (K := K) (H := hExpCutoff N)
      hH hSpos hOmega hHExp with
    ⟨S', hS'sub, hRadInj, hCard⟩
  have hS'nonempty : S'.Nonempty := by
    by_contra hnone
    have hS'empty : S' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hnone
    have hSpos_card : 0 < S.card := hSnonempty.card_pos
    have hle0 : S.card ≤ 0 := by
      simpa [hS'empty] using hCard
    exact (Nat.lt_irrefl 0) (hSpos_card.trans_le hle0)
  rcases prunedData_of_subset (N := N) (Q := Q) (S := S') a
      (fun q hq => hsub (hS'sub hq))
      hRange hDisj hS'nonempty K hKpos
      (fun q hq => hModLower q (hS'sub hq))
      (fun q hq => hHExp q (hS'sub hq))
      (fun q hq => hOmega q (hS'sub hq))
      hKbound
      (fun q hq r hr hrad => hRadInj q hq r hr hrad) with
    ⟨D, hDQ, _hDK, hDcard⟩
  refine ⟨D, ?_⟩
  simpa [hDQ] using hCard

lemma exists_omega_fiber_large (S : Finset ℕ) (T : ℕ)
    (_hS : S.Nonempty) (hOmegaLe : ∀ q ∈ S, omega q ≤ T) :
    ∃ K : ℕ,
      K ≤ T ∧ S.card ≤ (T + 1) * (S.filter fun q => omega q = K).card := by
  classical
  have hBne : (Finset.range (T + 1)).Nonempty := by
    exact ⟨0, by simp⟩
  have hB : ∀ q ∈ S, omega q ∈ Finset.range (T + 1) := by
    intro q hq
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hOmegaLe q hq)
  rcases exists_fiber_card_mul_range_card_ge S (Finset.range (T + 1)) omega hBne hB with
    ⟨K, hKmem, hK⟩
  refine ⟨K, ?_, ?_⟩
  · exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hKmem)
  · simpa [Finset.card_range] using hK

theorem bfv_pruning_small_epsilon_theorem :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N := by
  intro ε hε hεle
  let μ : ℝ := ε / 24
  have hμ : 0 < μ := by
    dsimp [μ]
    positivity
  have hε3 : 0 < ε / 3 := by positivity
  have hmargin_small : 1 + μ + ε + μ ≤ 2 := by
    dsimp [μ]
    nlinarith
  have hmargin_omega : 1 + μ + ε + μ ≤ (4 / 3 : ℝ) := by
    dsimp [μ]
    nlinarith
  filter_upwards [bfv_lower_bound_theorem μ hμ,
      hExp_rare_subset_count 2 (by norm_num),
      omega_floor_threeM_tail_subset_count,
      eventually_floor_threeM_succ_le_Lscale (ε / 3) hε3,
      eventually_radical_multiplicity_ceiling_le_Lscale (ε / 3) hε3,
      eventually_Lscale_neg_le_const (A := μ) (c := 1 / 6) hμ (by norm_num),
      eventually_Lscale_neg_le_const (A := ε / 3) (c := 1 / 2) hε3 (by norm_num),
      eventually_nat_mul_Lscale_neg_gt_one (1 + μ + ε),
      eventually_omega_pos_of_modulus_lower] with
    N hf hHrare hOmegaRare hPigeonLoss hRadLoss hBadTiny hDelTargetTiny hQlowerOne hOmegaPos
    Q a hRange hDisj hQlarge
  classical
  let T : ℕ := Nat.floor (3 * Mscale N)
  let BadSmall : Finset ℕ :=
    Q.filter (fun q : ℕ => (q : ℝ) < (N : ℝ) * Lscale (-2) N)
  let BadOmega : Finset ℕ :=
    Q.filter (fun q : ℕ => T ≤ omega q)
  let BadH : Finset ℕ :=
    Q.filter (fun q : ℕ => hExpCutoff N < (hExp q : ℝ))
  let Good : Finset ℕ := Q \ (BadSmall ∪ BadOmega ∪ BadH)
  have hQsubset : Q ⊆ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.2 (hRange q hq)
  have hfQlower :
      (N : ℝ) * Lscale (-(1 + μ + ε)) N ≤ (Q.card : ℝ) :=
    q_card_lower_from_bfv_lower hQlarge hf
  have hQcard_gt_one : (1 : ℝ) < (Q.card : ℝ) :=
    hQlowerOne.trans_le hfQlower
  have hBadSmall_sub : BadSmall ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hBadOmega_sub : BadOmega ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hBadH_sub : BadH ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hSmall_small : (BadSmall.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    simpa [BadSmall] using
      small_moduli_count_le_near_extremal_fraction
        (ε := ε) (η := μ) (δ := μ) hmargin_small hRange hQlarge hf
  have hOmega_tail :
      (BadOmega.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    have hTail :
        (Q.filter (fun q : ℕ => T ≤ omega q)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-(4 / 3)) N) := by
      simpa [T] using hOmegaRare Q hQsubset
    simpa [BadOmega] using
      omega_bad_count_le_near_extremal_fraction
        (A := 4 / 3) (ε := ε) (η := μ) (δ := μ)
        hmargin_omega hQlarge hf hTail
  have hH_tail : (BadH.card : ℝ) ≤ Lscale (-μ) N * (Q.card : ℝ) := by
    have hRareQ :
        (Q.filter fun q : ℕ => hExpCutoff N < (hExp q : ℝ)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-2) N) :=
      hHrare Q hQsubset
    simpa [BadH] using
      hExp_bad_count_le_near_extremal_fraction
        (A := 2) (ε := ε) (η := μ) (δ := μ)
        hmargin_small hQlarge hf hRareQ
  have hGood_large_raw :
      (Good.card : ℝ) ≥
        (1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N)) *
          (Q.card : ℝ) := by
    simpa [Good] using
      filter_large_of_three_bad_small Q BadSmall BadOmega BadH
        hBadSmall_sub hBadOmega_sub hBadH_sub
        hSmall_small hOmega_tail hH_tail
  have hGood_large :
      (Q.card : ℝ) * Lscale (-(ε / 3)) N ≤ (Good.card : ℝ) := by
    have hcoeff :
        Lscale (-(ε / 3)) N ≤
          1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N) := by
      linarith [hBadTiny, hDelTargetTiny]
    calc
      (Q.card : ℝ) * Lscale (-(ε / 3)) N
          ≤ (Q.card : ℝ) *
              (1 - (Lscale (-μ) N + Lscale (-μ) N + Lscale (-μ) N)) := by
            exact mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ ≤ (Good.card : ℝ) := by
            simpa [mul_comm] using hGood_large_raw
  have hGood_nonempty : Good.Nonempty := by
    have hpos : 0 < (Good.card : ℝ) := by
      have hLpos : 0 < Lscale (-(ε / 3)) N := Lscale_pos _ _
      exact lt_of_lt_of_le (mul_pos (lt_trans zero_lt_one hQcard_gt_one) hLpos)
        hGood_large
    exact Finset.card_pos.1 (by exact_mod_cast hpos)
  have hGood_sub_Q : Good ⊆ Q := by
    intro q hq
    exact Finset.mem_sdiff.1 hq |>.1
  have hGood_modLower :
      ∀ q ∈ Good, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadSmall := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    exact le_of_not_gt (by
      intro hlt
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hlt⟩))
  have hGood_hExp :
      ∀ q ∈ Good, (hExp q : ℝ) ≤ hExpCutoff N := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadH := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    exact le_of_not_gt (by
      intro hlt
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hlt⟩))
  have hGood_omega_le : ∀ q ∈ Good, omega q ≤ T := by
    intro q hq
    have hqQ : q ∈ Q := hGood_sub_Q hq
    have hnot : q ∉ BadOmega := by
      have hnotUnion : q ∉ BadSmall ∪ BadOmega ∪ BadH :=
        (Finset.mem_sdiff.1 hq).2
      intro hbad
      exact hnotUnion (by simp [hbad])
    have hnotle : ¬ T ≤ omega q := by
      intro hle
      exact hnot (Finset.mem_filter.2 ⟨hqQ, hle⟩)
    omega
  rcases exists_omega_fiber_large Good T hGood_nonempty hGood_omega_le with
    ⟨K, hKleT, hGood_le_fiber⟩
  let Fiber : Finset ℕ := Good.filter fun q : ℕ => omega q = K
  have hFiber_large :
      (Good.card : ℝ) * Lscale (-(ε / 3)) N ≤ (Fiber.card : ℝ) := by
    simpa [Fiber, T] using
      card_lower_of_mul_factor_le_Lscale
        (S := Good) (S' := Good.filter fun q : ℕ => omega q = K)
        (C := T + 1) (N := N) (η := ε / 3)
        hGood_le_fiber hPigeonLoss
  have hFiber_nonempty : Fiber.Nonempty := by
    have hpos : 0 < (Fiber.card : ℝ) := by
      exact lt_of_lt_of_le
        (mul_pos
          (lt_of_lt_of_le
            (mul_pos (lt_trans zero_lt_one hQcard_gt_one) (Lscale_pos _ _))
            hGood_large)
          (Lscale_pos _ _))
        hFiber_large
    exact Finset.card_pos.1 (by exact_mod_cast hpos)
  have hFiber_sub_Q : Fiber ⊆ Q := by
    intro q hq
    exact hGood_sub_Q (Finset.mem_filter.1 hq).1
  have hFiber_modLower :
      ∀ q ∈ Fiber, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ) := by
    intro q hq
    exact hGood_modLower q (Finset.mem_filter.1 hq).1
  have hFiber_hExp :
      ∀ q ∈ Fiber, (hExp q : ℝ) ≤ hExpCutoff N := by
    intro q hq
    exact hGood_hExp q (Finset.mem_filter.1 hq).1
  have hFiber_omega : ∀ q ∈ Fiber, omega q = K := by
    intro q hq
    exact (Finset.mem_filter.1 hq).2
  have hKbound : (K : ℝ) ≤ 3 * Mscale N := by
    have hT_le : (T : ℝ) ≤ 3 * Mscale N := by
      dsimp [T]
      exact Nat.floor_le (mul_nonneg (by norm_num) (Mscale_nonneg N))
    have hKleTreal : (K : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast hKleT
    exact hKleTreal.trans hT_le
  have hKpos : 1 ≤ K := by
    rcases hFiber_nonempty with ⟨q, hq⟩
    have hOmegaQ : 1 ≤ omega q :=
      hOmegaPos q (hFiber_modLower q hq)
    rw [hFiber_omega q hq] at hOmegaQ
    exact hOmegaQ
  have hCutoff_one : 1 ≤ hExpCutoff N := by
    rw [show (1 : ℝ) = Real.exp 0 by simp, hExpCutoff]
    exact Real.exp_le_exp.2 (Real.sqrt_nonneg _)
  rcases exists_prunedData_after_radical_selection (N := N) (K := K)
      (Q := Q) (S := Fiber) a hFiber_sub_Q hRange hDisj
      hFiber_nonempty hKpos hKbound hCutoff_one
      hFiber_modLower hFiber_hExp hFiber_omega with
    ⟨D, hFiber_le_D⟩
  have hD_from_fiber :
      (Fiber.card : ℝ) * Lscale (-(ε / 3)) N ≤ (D.Q.card : ℝ) := by
    exact card_lower_of_mul_factor_le_Lscale
      (S := Fiber) (S' := D.Q)
      (C := Nat.ceil (hExpCutoff N ^ 2 * (2 : ℝ) ^ K))
      (N := N) (η := ε / 3) hFiber_le_D (hRadLoss K hKbound)
  refine ⟨D, ?_⟩
  have hLsplit :
      Lscale (-ε) N =
        Lscale (-(ε / 3)) N * Lscale (-(ε / 3)) N *
          Lscale (-(ε / 3)) N := by
    calc
      Lscale (-ε) N
          = Lscale (-(ε / 3) + -(ε / 3) + -(ε / 3)) N := by
              congr 1
              ring
      _ = Lscale (-(ε / 3) + -(ε / 3)) N *
            Lscale (-(ε / 3)) N := by
              rw [Lscale_add]
      _ = Lscale (-(ε / 3)) N * Lscale (-(ε / 3)) N *
            Lscale (-(ε / 3)) N := by
              rw [Lscale_add]
  calc
    (Q.card : ℝ) * Lscale (-ε) N
        = (((Q.card : ℝ) * Lscale (-(ε / 3)) N) *
            Lscale (-(ε / 3)) N) * Lscale (-(ε / 3)) N := by
          rw [hLsplit]
          ring
    _ ≤ ((Good.card : ℝ) * Lscale (-(ε / 3)) N) *
          Lscale (-(ε / 3)) N := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hGood_large (Lscale_nonneg _ _))
            (Lscale_nonneg _ _)
    _ ≤ (Fiber.card : ℝ) * Lscale (-(ε / 3)) N := by
          exact mul_le_mul_of_nonneg_right hFiber_large (Lscale_nonneg _ _)
    _ ≤ (D.Q.card : ℝ) := hD_from_fiber

/-!
The pruning proof uses the following BFV-local inputs:

* `bfv_lower_bound_theorem` to compare deleted sets with a near-extremal `Q`.
* `bfv_omega_tail_theorem` to delete the large-omega tail.
* `hExp_rare_count_rankin_squarefull` to delete large hExp values.
* `rad_multiplicity_bfv33` and `choose_one_per_fiber_card_lower` to choose one
  representative per radical.

The remaining work in this file is epsilon bookkeeping: each deletion and each
pigeonhole loss is bounded by a small `Lscale(η, N)` factor, and the factors are
combined with `Lscale_add`.
-/

/--
Bookkeeping target for BFV pruning.

The analytic and finite inputs are now named separately.  This theorem is the
remaining assembly step: compare the three deleted sets against a near-extremal
input family, pigeonhole an omega fiber, apply the radical representative
selection, and package the result as `PrunedData`.
-/
theorem bfv_pruning_bookkeeping_from_bfv_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N :=
  by
    intro ε hε
    by_cases hsmall : ε ≤ 1 / 4
    · exact bfv_pruning_small_epsilon_theorem ε hε hsmall
    · have hquarter_pos : (0 : ℝ) < 1 / 4 := by norm_num
      have hquarter_le : (1 / 4 : ℝ) ≤ ε := le_of_lt (lt_of_not_ge hsmall)
      filter_upwards [bfv_pruning_small_epsilon_theorem (1 / 4) hquarter_pos le_rfl]
        with N hPruneQuarter Q a hRange hDisj _hQlarge
      rcases exists_admissible_card_f N with ⟨Q₀, hQ₀adm, hQ₀card⟩
      rcases hQ₀adm.2 with ⟨a₀, ha₀⟩
      have hQ₀large :
          (Q₀.card : ℝ) ≥ (f N : ℝ) * Lscale (-(1 / 4 : ℝ)) N := by
        rw [hQ₀card]
        calc
          (f N : ℝ) * Lscale (-(1 / 4 : ℝ)) N
              ≤ (f N : ℝ) * 1 := by
                exact mul_le_mul_of_nonneg_left
                  (Lscale_neg_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4) N)
                  (by positivity)
          _ = (f N : ℝ) := by ring
      rcases hPruneQuarter Q₀ a₀ hQ₀adm.1 ha₀ hQ₀large with ⟨D, hD⟩
      refine ⟨D, ?_⟩
      have hQleF : Q.card ≤ f N :=
        le_f_of_possibleCard ⟨Q, ⟨hRange, ⟨a, hDisj⟩⟩, rfl⟩
      have hLmono : Lscale (-ε) N ≤ Lscale (-(1 / 4 : ℝ)) N :=
        Lscale_mono_in_alpha (by linarith) N
      calc
        (Q.card : ℝ) * Lscale (-ε) N
            ≤ (f N : ℝ) * Lscale (-ε) N := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hQleF)
                (Lscale_nonneg (-ε) N)
        _ ≤ (f N : ℝ) * Lscale (-(1 / 4 : ℝ)) N := by
              exact mul_le_mul_of_nonneg_left hLmono (by positivity)
        _ = (Q₀.card : ℝ) * Lscale (-(1 / 4 : ℝ)) N := by rw [hQ₀card]
        _ ≤ (D.Q.card : ℝ) := hD

/--
BFV pruning theorem.

Formal target for Erdős Problem 202, Proposition 3.1. From a near-extremal
admissible family `Q`, remove small moduli, large-omega moduli, and large-hExp
moduli; pigeonhole a single omega value; then choose one representative per
radical.  The resulting data satisfy all fields of `PrunedData N` and retain
`Q.card * Lscale (-ε) N` elements.
-/
theorem bfv_pruning_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N :=
  bfv_pruning_bookkeeping_from_bfv_inputs

end Erdos202
