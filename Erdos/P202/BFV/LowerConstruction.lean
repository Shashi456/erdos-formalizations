/-
Erdos Problem 202 -- BFV lower construction skeleton.

This file names the explicit lower-family objects used by the
de la Bretèche–Ford–Vandehey construction: dyadic prime choices, their
product moduli, the finite modulus family, and the theorem targets asserting
injectivity, size, modulus bounds, and CRT residue disjointness.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.BFV.PrimeIntervals
import Erdos.P202.BFV.Chebyshev
import Erdos.P202.BFV.LowerPathConstruction

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Parameters and prime choices -/

/-- BFV lower-construction depth, `r = floor M(N)`. -/
noncomputable def lowerR (N : ℕ) : ℕ :=
  Nat.floor (Mscale N)

/-- The index set `{0, ..., r}` for the BFV prime blocks. -/
abbrev lowerIndex (N : ℕ) : Type :=
  Fin (lowerR N + 1)

/-- The root block index in the BFV lower construction. -/
def lowerZeroIndex (N : ℕ) : lowerIndex N :=
  ⟨0, Nat.succ_pos _⟩

/-- The non-root blocks.  The lower family varies only over these blocks; the
root block contributes a fixed shared factor used for CRT-disjointness. -/
abbrev lowerTailIndex (N : ℕ) : Type :=
  {i : lowerIndex N // i ≠ lowerZeroIndex N}

/-- The `k`th varying block, viewed as block number `k+1` in `{0, ..., r}`. -/
def lowerTailBlock (N : ℕ) (k : Fin (lowerR N)) : lowerTailIndex N :=
  ⟨k.succ, by
    intro h
    have hval := congrArg Fin.val h
    simp [lowerZeroIndex, Fin.val_succ] at hval⟩

lemma lowerTailBlock_surjective (N : ℕ) :
    Function.Surjective (lowerTailBlock N) := by
  intro i
  have hi0 : i.1 ≠ 0 := by
    intro h
    exact i.2 (by simpa [lowerZeroIndex] using h)
  refine ⟨i.1.pred hi0, ?_⟩
  apply Subtype.ext
  exact Fin.succ_pred i.1 hi0


/-- Logarithmic gap between consecutive lower-construction prime blocks.

The extra `1 / log log N` is only a separation margin: eventually
`exp(lowerLogGap N) > 2`, so the dyadic intervals `(Y_i, 2Y_i]` are disjoint.
Its total contribution is `o(Zscale N)`. -/
noncomputable def lowerLogGap (N : ℕ) : ℝ :=
  Real.log 2 + 1 / Real.log (Real.log (N : ℝ))

/-- Product-normalized central log scale.

The subtraction of `(r+1) log 2` compensates for the dyadic upper endpoints:
if `Y_i = exp(lowerLogScale N i)`, then the centered offsets below sum to zero,
so formally `∏ᵢ (2 * Y_i) = N`.  This fixes the earlier units error where the
product of the selected prime scales was only about `N^(1/2)`. -/
noncomputable def lowerLogBase (N : ℕ) : ℝ :=
  (Real.log (N : ℝ) - ((lowerR N : ℝ) + 1) * Real.log 2) /
    ((lowerR N : ℝ) + 1)

/-- Corrected logarithmic scale for the `i`th BFV lower prime block.

The scales are centered around `log N / (r+1)`, with consecutive log-gap
`lowerLogGap N`.  Thus the blocks are geometrically separated while their total
product remains at the full `N` scale. -/
noncomputable def lowerLogScale (N : ℕ) (i : lowerIndex N) : ℝ :=
  lowerLogBase N + (((i.1 : ℝ) - (lowerR N : ℝ) / 2) * lowerLogGap N)

lemma lowerLogScale_sub (N : ℕ) (i j : lowerIndex N) :
    lowerLogScale N i - lowerLogScale N j =
      ((i.1 : ℝ) - (j.1 : ℝ)) * lowerLogGap N := by
  simp [lowerLogScale]
  ring

lemma lowerLogGap_gt_log_two_of_exp_one_lt_nat {N : ℕ}
    (hN : Real.exp 1 < (N : ℝ)) :
    Real.log 2 < lowerLogGap N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hrecip_pos : 0 < (1 : ℝ) / Real.log (Real.log (N : ℝ)) := by
    positivity
  simp [lowerLogGap]
  linarith

lemma eventually_lowerLogGap_gt_log_two :
    ∀ᶠ N : ℕ in atTop, Real.log 2 < lowerLogGap N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hN
  exact lowerLogGap_gt_log_two_of_exp_one_lt_nat
    (lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN))

/-- A concrete product-normalized exponentially spaced scale for the `i`th
dyadic prime block.

The final BFV proof needs only eventual disjointness and product estimates for
these named scales; those hard estimates are isolated below. -/
noncomputable def lowerY (N : ℕ) (i : lowerIndex N) : ℝ :=
  Real.exp (lowerLogScale N i)

lemma lowerY_dyadic_lt_of_lt_index {N : ℕ} {i j : lowerIndex N}
    (hgap : Real.log 2 < lowerLogGap N) (hij : i.1 < j.1) :
    2 * lowerY N i < lowerY N j := by
  have hsucc : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.2 hij
  have hdiff_real : 1 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
    have hsuccR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hsucc
    linarith
  have hgap_pos : 0 < lowerLogGap N :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hgap
  have hmain :
      Real.log 2 + lowerLogScale N i < lowerLogScale N j := by
    have hsub := lowerLogScale_sub N j i
    have hmul : Real.log 2 < ((j.1 : ℝ) - (i.1 : ℝ)) * lowerLogGap N := by
      calc
        Real.log 2 < lowerLogGap N := hgap
        _ ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerLogGap N := by
          nlinarith
    nlinarith
  calc
    2 * lowerY N i
        = Real.exp (Real.log 2 + lowerLogScale N i) := by
            rw [lowerY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ < Real.exp (lowerLogScale N j) := Real.exp_lt_exp.2 hmain
    _ = lowerY N j := by rw [lowerY]

lemma lowerIndex_sum_centered (N : ℕ) :
    (∑ i : lowerIndex N, ((i.1 : ℝ) - (lowerR N : ℝ) / 2)) = 0 := by
  let r := lowerR N
  change (∑ i : Fin (r + 1), ((i.1 : ℝ) - (r : ℝ) / 2)) = 0
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ x ∈ Finset.range (r + 1),
        if h : x < r + 1 then (x : ℝ) - (r : ℝ) / 2 else 0)
        = ∑ x ∈ Finset.range (r + 1), ((x : ℝ) - (r : ℝ) / 2) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.mem_range.mp hx]
    _ = 0 := by
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_const, nsmul_eq_mul]
          let S : ℝ := ∑ x ∈ Finset.range (r + 1), (x : ℝ)
          have hnat : (∑ i ∈ Finset.range (r + 1), i) * 2 = (r + 1) * r := by
            simpa using (Finset.sum_range_id_mul_two (r + 1))
          have hS2 : S * 2 = ((r + 1 : ℕ) * r : ℝ) := by
            dsimp [S]
            rw [← Nat.cast_sum]
            exact_mod_cast hnat
          have hcard : ((Finset.range (r + 1)).card : ℝ) = r + 1 := by simp
          rw [hcard]
          dsimp [S] at hS2 ⊢
          norm_num at hS2 ⊢
          nlinarith

lemma lowerLogScale_sum (N : ℕ) :
    (∑ i : lowerIndex N, lowerLogScale N i) =
      Real.log (N : ℝ) - ((lowerR N : ℝ) + 1) * Real.log 2 := by
  have hcenter := lowerIndex_sum_centered N
  have hcard : ((Finset.univ : Finset (lowerIndex N)).card : ℝ) =
      (lowerR N : ℝ) + 1 := by
    simp [lowerIndex]
  simp [lowerLogScale, lowerLogBase]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  rw [hcenter]
  rw [zero_mul, add_zero]
  rw [hcard]
  have hden : (lowerR N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]

lemma lowerY_dyadic_product_eq {N : ℕ} (hNpos : 0 < (N : ℝ)) :
    (∏ i : lowerIndex N, (2 : ℝ) * lowerY N i) = (N : ℝ) := by
  calc
    (∏ i : lowerIndex N, (2 : ℝ) * lowerY N i)
        = ∏ i : lowerIndex N, Real.exp (Real.log 2 + lowerLogScale N i) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [lowerY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (∑ i : lowerIndex N, (Real.log 2 + lowerLogScale N i)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (Real.log (N : ℝ)) := by
          congr 1
          rw [Finset.sum_add_distrib]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [lowerLogScale_sum]
          have hcard : ((Finset.univ : Finset (lowerIndex N)).card : ℝ) =
              (lowerR N : ℝ) + 1 := by
            simp [lowerIndex]
          rw [hcard]
          ring
    _ = (N : ℝ) := Real.exp_log hNpos

/-- Natural floor endpoint for the `i`th scale. -/
noncomputable def lowerYNat (N : ℕ) (i : lowerIndex N) : ℕ :=
  Nat.floor (lowerY N i)

/-- The `i`th dyadic prime block in the lower construction. -/
noncomputable def lowerPrimeInterval (N : ℕ) (i : lowerIndex N) : Finset ℕ :=
  dyadicPrimeInterval (lowerY N i)

lemma dyadicPrimeInterval_card_le_primeCounting (y : ℝ) :
    (dyadicPrimeInterval y).card ≤ Nat.primeCounting (Nat.floor (2 * y)) := by
  classical
  have hsub :
      dyadicPrimeInterval y ⊆
        (Finset.range (Nat.floor (2 * y) + 1)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range]
    have hp' := mem_dyadicPrimeInterval.1 hp
    exact ⟨Nat.lt_succ_of_le hp'.2.1, hp'.2.2⟩
  have hcard := Finset.card_le_card hsub
  simpa [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range] using hcard

/-- Deterministic shared root factor at the block-0 scale.

The original full Cartesian-product family is not CRT-disjoint: two choices
that differ in every coordinate have coprime moduli.  The lower construction
therefore fixes a common root factor and varies only over the remaining blocks.
Using `⌊Y_0⌋ + 1` rather than a chosen prime keeps the family total and avoids
adding an extra nonemptiness dependency; primality of the common factor is not
needed for the CRT-disjointness mechanism. -/
noncomputable def lowerP0 (N : ℕ) : ℕ :=
  Nat.floor (lowerY N (lowerZeroIndex N)) + 1

lemma lowerP0_pos (N : ℕ) : 0 < lowerP0 N := by
  simp [lowerP0]

/-- A choice of one prime from every BFV lower block. -/
abbrev LowerPrimeChoice (N : ℕ) : Type :=
  (i : lowerTailIndex N) → {p : ℕ // p ∈ lowerPrimeInterval N i.1}

lemma lowerTailBlock_ext {N : ℕ} {P P' : LowerPrimeChoice N}
    (h : ∀ k : Fin (lowerR N), P (lowerTailBlock N k) = P' (lowerTailBlock N k)) :
    P = P' := by
  funext i
  rcases lowerTailBlock_surjective N i with ⟨k, rfl⟩
  exact h k

/-- All prime-choice tuples. -/
noncomputable def lowerChoices (N : ℕ) : Finset (LowerPrimeChoice N) :=
  Fintype.piFinset fun i : lowerTailIndex N => (lowerPrimeInterval N i.1).attach

lemma lowerChoices_card (N : ℕ) :
    (lowerChoices N).card =
      ∏ i : lowerTailIndex N, (lowerPrimeInterval N i.1).card := by
  simp [lowerChoices, Fintype.card_piFinset]

/-- The modulus attached to a prime-choice tuple. -/
noncomputable def lowerModulus (N : ℕ) (P : LowerPrimeChoice N) : ℕ :=
  lowerP0 N * ∏ i : lowerTailIndex N, (P i).1

lemma lowerModulus_pos (N : ℕ) (P : LowerPrimeChoice N) :
    0 < lowerModulus N P := by
  unfold lowerModulus
  exact mul_pos (lowerP0_pos N) (Finset.prod_pos (fun i _hi => by
    have hp : Nat.Prime (P i).1 := (mem_dyadicPrimeInterval.1 (P i).2).2.2
    exact hp.pos))

lemma lowerRootFactor_le_two_mul_lowerY {N : ℕ}
    (hY0 : 1 ≤ lowerY N (lowerZeroIndex N)) :
    (lowerP0 N : ℝ) ≤ 2 * lowerY N (lowerZeroIndex N) := by
  have hY0_nonneg : 0 ≤ lowerY N (lowerZeroIndex N) := (Real.exp_pos _).le
  have hfloor :
      ((Nat.floor (lowerY N (lowerZeroIndex N)) : ℕ) : ℝ) ≤
        lowerY N (lowerZeroIndex N) :=
    Nat.floor_le hY0_nonneg
  rw [lowerP0]
  norm_num
  linarith

lemma lowerModulus_le_N_of_root_scale {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerY N (lowerZeroIndex N)) (P : LowerPrimeChoice N) :
    lowerModulus N P ≤ N := by
  classical
  have hroot := lowerRootFactor_le_two_mul_lowerY (N := N) hY0
  have htail :
      ((∏ i : lowerTailIndex N, (P i).1 : ℕ) : ℝ) ≤
        ∏ i : lowerTailIndex N, (2 : ℝ) * lowerY N i.1 := by
    rw [Nat.cast_prod]
    exact Finset.prod_le_prod
      (fun i _hi => by positivity)
      (fun i _hi => by
        have hmem : (P i).1 ∈ lowerPrimeInterval N i.1 := (P i).2
        have hle_nat : (P i).1 ≤ Nat.floor (2 * lowerY N i.1) :=
          (mem_dyadicPrimeInterval.1 hmem).2.1
        have hnonneg : 0 ≤ 2 * lowerY N i.1 := by
          exact mul_nonneg (by norm_num) (Real.exp_pos _).le
        exact le_trans (by exact_mod_cast hle_nat)
          (Nat.floor_le hnonneg))
  have hprod_split :
      (2 : ℝ) * lowerY N (lowerZeroIndex N) *
          (∏ i : lowerTailIndex N, (2 : ℝ) * lowerY N i.1)
        =
      ∏ i : lowerIndex N, (2 : ℝ) * lowerY N i := by
    let f : lowerIndex N → ℝ := fun i => (2 : ℝ) * lowerY N i
    have hsplit := Fintype.prod_eq_mul_prod_compl (lowerZeroIndex N) f
    have htail_prod :
        (∏ i ∈ ({lowerZeroIndex N} : Finset (lowerIndex N))ᶜ, f i) =
          ∏ i : lowerTailIndex N, f i.1 := by
      exact Finset.prod_subtype
        (({lowerZeroIndex N} : Finset (lowerIndex N))ᶜ)
        (by intro x; simp)
        f
    simpa [f, htail_prod] using hsplit.symm
  have hreal :
      (lowerModulus N P : ℝ) ≤ (N : ℝ) := by
    rw [lowerModulus, Nat.cast_mul]
    calc
      (lowerP0 N : ℝ) * ((∏ i : lowerTailIndex N, (P i).1 : ℕ) : ℝ)
          ≤ (2 * lowerY N (lowerZeroIndex N)) *
              (∏ i : lowerTailIndex N, (2 : ℝ) * lowerY N i.1) := by
            exact mul_le_mul hroot htail (by positivity) (by positivity)
      _ = ∏ i : lowerIndex N, (2 : ℝ) * lowerY N i := hprod_split
      _ = (N : ℝ) := lowerY_dyadic_product_eq hNpos
  exact_mod_cast hreal

lemma lowerLogScale_zero_nonneg_of_scale {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hMge : 1 ≤ Mscale N)
    (hloglog_ge : 4 ≤ Real.log (Real.log (N : ℝ))) :
    0 ≤ lowerLogScale N (lowerZeroIndex N) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := by
    have hone_lt_N : (1 : ℝ) < (N : ℝ) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.2 zero_lt_one
        _ < (N : ℝ) := hNlarge
    exact Real.log_pos hone_lt_N
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) := by linarith
  have hMpos : 0 < Mscale N := lt_of_lt_of_le zero_lt_one hMge
  have hM_nonneg : 0 ≤ Mscale N := hMpos.le
  have hZ_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hfloor_le :
      ((lowerR N : ℕ) : ℝ) ≤ Mscale N := by
    exact Nat.floor_le (Mscale_nonneg N)
  have hden_pos : 0 < ((lowerR N : ℕ) : ℝ) + 1 := by positivity
  have hden_le : ((lowerR N : ℕ) : ℝ) + 1 ≤ 2 * Mscale N := by
    nlinarith
  have htwoM_pos : 0 < 2 * Mscale N := by positivity
  have hdiv_ge :
      Zscale N / 2 ≤ Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) := by
    have hmain :
        Real.log (N : ℝ) / (2 * Mscale N) ≤
          Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) :=
      div_le_div_of_nonneg_left hlog_nonneg hden_pos hden_le
    have hrewrite :
        Real.log (N : ℝ) / (2 * Mscale N) = Zscale N / 2 := by
      have hMZ := Mscale_mul_Zscale_eq_log hNlarge
      field_simp [hMpos.ne']
      nlinarith
    simpa [hrewrite] using hmain
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hrecip_le_one :
      1 / Real.log (Real.log (N : ℝ)) ≤ 1 := by
    exact (div_le_iff₀ hloglog_pos).2 (by linarith)
  have hgap_le_two : lowerLogGap N ≤ 2 := by
    have hrecip_inv_le_one :
        (Real.log (Real.log (N : ℝ)))⁻¹ ≤ 1 := by
      simpa [one_div] using hrecip_le_one
    rw [lowerLogGap]
    linarith
  have hgap_nonneg : 0 ≤ lowerLogGap N := by
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hrecip_nonneg : 0 ≤ (Real.log (Real.log (N : ℝ)))⁻¹ :=
      inv_nonneg.2 hloglog_pos.le
    have hrecip_nonneg_div :
        0 ≤ 1 / Real.log (Real.log (N : ℝ)) := by
      simpa [one_div] using hrecip_nonneg
    rw [lowerLogGap]
    linarith
  have hgap_term :
      ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N ≤ Mscale N := by
    have hmul :
        ((lowerR N : ℕ) : ℝ) * lowerLogGap N ≤ Mscale N * 2 :=
      mul_le_mul hfloor_le hgap_le_two hgap_nonneg hM_nonneg
    nlinarith
  have hbad_le :
      Real.log 2 + ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N ≤ 2 * Mscale N := by
    nlinarith
  have hZ_large : 2 * Mscale N ≤ Zscale N / 2 := by
    have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
    rw [← hMll]
    nlinarith
  have hbad_le_Z : Real.log 2 + ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N ≤
      Zscale N / 2 := le_trans hbad_le hZ_large
  have hbase_eq :
      lowerLogBase N =
        Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) - Real.log 2 := by
    have hden_ne : ((lowerR N : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    simp [lowerLogBase]
    field_simp [hden_ne]
  have hscale_eq :
      lowerLogScale N (lowerZeroIndex N) =
        Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) -
          (Real.log 2 + ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N) := by
    simp [lowerLogScale, hbase_eq, lowerZeroIndex]
    ring
  rw [hscale_eq]
  nlinarith

lemma lowerLogGap_le_two_of_loglog_ge_four {N : ℕ}
    (hloglog_ge : 4 ≤ Real.log (Real.log (N : ℝ))) :
    lowerLogGap N ≤ 2 := by
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) := by linarith
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hrecip_le_one :
      1 / Real.log (Real.log (N : ℝ)) ≤ 1 := by
    exact (div_le_iff₀ hloglog_pos).2 (by linarith)
  rw [lowerLogGap]
  linarith

lemma Mscale_le_lowerLogScale_zero_of_scale {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hMge : 1 ≤ Mscale N)
    (hloglog_ge : 6 ≤ Real.log (Real.log (N : ℝ))) :
    Mscale N ≤ lowerLogScale N (lowerZeroIndex N) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := by
    have hone_lt_N : (1 : ℝ) < (N : ℝ) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.2 zero_lt_one
        _ < (N : ℝ) := hNlarge
    exact Real.log_pos hone_lt_N
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) := by linarith
  have hMpos : 0 < Mscale N := lt_of_lt_of_le zero_lt_one hMge
  have hM_nonneg : 0 ≤ Mscale N := hMpos.le
  have hfloor_le :
      ((lowerR N : ℕ) : ℝ) ≤ Mscale N := by
    exact Nat.floor_le (Mscale_nonneg N)
  have hden_pos : 0 < ((lowerR N : ℕ) : ℝ) + 1 := by positivity
  have hden_le : ((lowerR N : ℕ) : ℝ) + 1 ≤ 2 * Mscale N := by
    nlinarith
  have hdiv_ge :
      Zscale N / 2 ≤ Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) := by
    have hmain :
        Real.log (N : ℝ) / (2 * Mscale N) ≤
          Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) :=
      div_le_div_of_nonneg_left hlog_nonneg hden_pos hden_le
    have hrewrite :
        Real.log (N : ℝ) / (2 * Mscale N) = Zscale N / 2 := by
      have hMZ := Mscale_mul_Zscale_eq_log hNlarge
      field_simp [hMpos.ne']
      nlinarith
    simpa [hrewrite] using hmain
  have hgap_le_two : lowerLogGap N ≤ 2 :=
    lowerLogGap_le_two_of_loglog_ge_four (by linarith : 4 ≤ Real.log (Real.log (N : ℝ)))
  have hgap_nonneg : 0 ≤ lowerLogGap N := by
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hrecip_nonneg : 0 ≤ (1 : ℝ) / Real.log (Real.log (N : ℝ)) := by
      positivity
    rw [lowerLogGap]
    linarith
  have hgap_term :
      ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N ≤ Mscale N := by
    have hmul :
        ((lowerR N : ℕ) : ℝ) * lowerLogGap N ≤ Mscale N * 2 :=
      mul_le_mul hfloor_le hgap_le_two hgap_nonneg hM_nonneg
    nlinarith
  have hbad_le :
      Real.log 2 + ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N ≤ 2 * Mscale N := by
    have hlog_two_le_one : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    nlinarith
  have hbase_eq :
      lowerLogBase N =
        Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) - Real.log 2 := by
    have hden_ne : ((lowerR N : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    simp [lowerLogBase]
    field_simp [hden_ne]
  have hscale_eq :
      lowerLogScale N (lowerZeroIndex N) =
        Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) -
          (Real.log 2 + ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N) := by
    simp [lowerLogScale, hbase_eq, lowerZeroIndex]
    ring
  have hscale_lower :
      Zscale N / 2 - 2 * Mscale N ≤ lowerLogScale N (lowerZeroIndex N) := by
    rw [hscale_eq]
    nlinarith
  have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
  have hZ_large : 6 * Mscale N ≤ Zscale N := by
    rw [← hMll]
    nlinarith
  have hM_le : Mscale N ≤ Zscale N / 2 - 2 * Mscale N := by
    nlinarith
  exact hM_le.trans hscale_lower

lemma eventually_lowerY_zero_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ lowerY N (lowerZeroIndex N) := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge 1 zero_lt_one,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 4] with N hN hM hloglog
  rw [lowerY, Real.one_le_exp_iff]
  exact lowerLogScale_zero_nonneg_of_scale
    (lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)) hM hloglog

lemma eventually_lowerLogScale_zero_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ lowerLogScale N (lowerZeroIndex N) := by
  let B : ℝ := max A 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge B hBpos,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 6] with N hN hM hloglog
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
  have hMone : 1 ≤ Mscale N := (le_max_right A 1).trans hM
  have hscale := Mscale_le_lowerLogScale_zero_of_scale hNlarge hMone hloglog
  exact (le_max_left A 1).trans (hM.trans hscale)

lemma eventually_lowerY_zero_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ lowerY N (lowerZeroIndex N) := by
  by_cases hA : 0 < A
  · filter_upwards [eventually_lowerLogScale_zero_ge (Real.log A)] with N hscale
    rw [lowerY]
    exact (Real.log_le_iff_le_exp hA).1 hscale
  · exact Filter.Eventually.of_forall fun N =>
      (le_of_not_gt hA).trans (Real.exp_pos _).le

lemma lowerY_le_of_index_le {N : ℕ} {i j : lowerIndex N}
    (hgap_nonneg : 0 ≤ lowerLogGap N) (hij : i.1 ≤ j.1) :
    lowerY N i ≤ lowerY N j := by
  have hsub := lowerLogScale_sub N j i
  have hdiff_nonneg : 0 ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerLogGap N := by
    have hidx : 0 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
      exact sub_nonneg.2 (by exact_mod_cast hij)
    exact mul_nonneg hidx hgap_nonneg
  have hscale : lowerLogScale N i ≤ lowerLogScale N j := by
    nlinarith
  exact Real.exp_le_exp.2 hscale

lemma lowerY_adjacent_le_exp_two_mul {N : ℕ} {i j : lowerIndex N}
    (hgap_le : lowerLogGap N ≤ 2) (hij : j.1 = i.1 + 1) :
    lowerY N j ≤ Real.exp 2 * lowerY N i := by
  have hsub := lowerLogScale_sub N j i
  have hscale : lowerLogScale N j = lowerLogScale N i + lowerLogGap N := by
    have hdiff : ((j.1 : ℝ) - (i.1 : ℝ)) = 1 := by
      rw [hij]
      norm_num
    nlinarith
  have heq : lowerY N j = lowerY N i * Real.exp (lowerLogGap N) := by
    rw [lowerY, lowerY, hscale, Real.exp_add]
  rw [heq]
  calc
    lowerY N i * Real.exp (lowerLogGap N)
        ≤ lowerY N i * Real.exp 2 := by
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 hgap_le) (Real.exp_pos _).le
    _ = Real.exp 2 * lowerY N i := by ring

lemma lowerPrimeInterval_adjacent_card_le_floor_prev_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerIndex N, j.1 = i.1 + 1 →
        (lowerPrimeInterval N j).card ≤ Nat.floor (lowerY N i) := by
  classical
  let C : ℝ := (Real.log 4 + 1) * (2 * Real.exp 2)
  have hCpos : 0 < C := by
    dsimp [C]
    have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    positivity
  rcases eventually_atTop.1
      (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one) with
    ⟨X, hcheb⟩
  filter_upwards [eventually_lowerLogGap_gt_log_two,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 4,
      eventually_lowerY_zero_ge (max (Real.exp C) (max X 1))] with
    N hgap_gt hloglog hY0large
  intro i j hij
  have hgap_nonneg : 0 ≤ lowerLogGap N := by
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    exact hlog_two_nonneg.trans hgap_gt.le
  have hgap_le_two : lowerLogGap N ≤ 2 :=
    lowerLogGap_le_two_of_loglog_ge_four hloglog
  have hzero_le_i : lowerY N (lowerZeroIndex N) ≤ lowerY N i :=
    lowerY_le_of_index_le hgap_nonneg (by simp [lowerZeroIndex])
  have hzero_le_j : lowerY N (lowerZeroIndex N) ≤ lowerY N j :=
    lowerY_le_of_index_le hgap_nonneg (by simp [lowerZeroIndex])
  have hYj_upper : lowerY N j ≤ Real.exp 2 * lowerY N i :=
    lowerY_adjacent_le_exp_two_mul hgap_le_two hij
  have hX_le_Y0 : X ≤ lowerY N (lowerZeroIndex N) := by
    exact (le_max_left X 1).trans
      ((le_max_right (Real.exp C) (max X 1)).trans hY0large)
  have hExpC_le_Y0 : Real.exp C ≤ lowerY N (lowerZeroIndex N) := by
    exact (le_max_left (Real.exp C) (max X 1)).trans hY0large
  have hX_le_arg : X ≤ 2 * lowerY N j := by
    have hX_le_j : X ≤ lowerY N j := hX_le_Y0.trans hzero_le_j
    have hj_nonneg : 0 ≤ lowerY N j := (Real.exp_pos _).le
    nlinarith
  have hcheb_arg := hcheb (2 * lowerY N j) hX_le_arg
  have hcard_pc :
      ((lowerPrimeInterval N j).card : ℝ) ≤
        (Nat.primeCounting (Nat.floor (2 * lowerY N j)) : ℝ) := by
    exact_mod_cast dyadicPrimeInterval_card_le_primeCounting (lowerY N j)
  have hlog_arg_ge_C : C ≤ Real.log (2 * lowerY N j) := by
    have hExpC_le_arg : Real.exp C ≤ 2 * lowerY N j := by
      have hExpC_le_j : Real.exp C ≤ lowerY N j := hExpC_le_Y0.trans hzero_le_j
      have hj_nonneg : 0 ≤ lowerY N j := (Real.exp_pos _).le
      nlinarith
    have harg_pos : 0 < 2 * lowerY N j := by
      exact mul_pos (by norm_num) (Real.exp_pos _)
    exact (Real.le_log_iff_exp_le harg_pos).2 hExpC_le_arg
  have hlog_arg_pos : 0 < Real.log (2 * lowerY N j) :=
    hCpos.trans_le hlog_arg_ge_C
  have hcoeff_pos : 0 ≤ Real.log 4 + 1 := by
    have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hnum_le :
      (Real.log 4 + 1) * (2 * lowerY N j) ≤ C * lowerY N i := by
    calc
      (Real.log 4 + 1) * (2 * lowerY N j)
          ≤ (Real.log 4 + 1) * (2 * (Real.exp 2 * lowerY N i)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hYj_upper (by norm_num : (0 : ℝ) ≤ 2))
              hcoeff_pos
      _ = C * lowerY N i := by
            dsimp [C]
            ring
  have hquot_le :
      (Real.log 4 + 1) * (2 * lowerY N j) / Real.log (2 * lowerY N j)
        ≤ lowerY N i := by
    rw [div_le_iff₀ hlog_arg_pos]
    have hi_nonneg : 0 ≤ lowerY N i := (Real.exp_pos _).le
    nlinarith
  have hcard_real : ((lowerPrimeInterval N j).card : ℝ) ≤ lowerY N i := by
    exact hcard_pc.trans (hcheb_arg.trans hquot_le)
  exact Nat.le_floor hcard_real

/-- The finite BFV lower family of moduli. -/
noncomputable def lowerQ (N : ℕ) : Finset ℕ :=
  (lowerChoices N).image (lowerModulus N)

/-- A canonical preimage choice for a modulus in `lowerQ`. -/
lemma lowerChoiceOfQ_exists (N : ℕ) (q : {q : ℕ // q ∈ lowerQ N}) :
    ∃ P ∈ lowerChoices N, lowerModulus N P = q.1 := by
  have hq : q.1 ∈ lowerQ N := q.2
  change q.1 ∈ (lowerChoices N).image (lowerModulus N) at hq
  exact Finset.mem_image.1 hq

noncomputable def lowerChoiceOfQ (N : ℕ) (q : {q : ℕ // q ∈ lowerQ N}) :
    LowerPrimeChoice N :=
  Classical.choose (lowerChoiceOfQ_exists N q)

lemma lowerChoiceOfQ_mem (N : ℕ) (q : {q : ℕ // q ∈ lowerQ N}) :
    lowerChoiceOfQ N q ∈ lowerChoices N :=
  (Classical.choose_spec (lowerChoiceOfQ_exists N q)).1

lemma lowerChoiceOfQ_modulus (N : ℕ) (q : {q : ℕ // q ∈ lowerQ N}) :
    lowerModulus N (lowerChoiceOfQ N q) = q.1 :=
  (Classical.choose_spec (lowerChoiceOfQ_exists N q)).2

lemma lowerChoiceOfQ_eq_of_injective {N : ℕ}
    (hinj : Set.InjOn (lowerModulus N) (↑(lowerChoices N) : Set (LowerPrimeChoice N)))
    (q : {q : ℕ // q ∈ lowerQ N}) {P : LowerPrimeChoice N}
    (hP : P ∈ lowerChoices N) (hmod : lowerModulus N P = q.1) :
    lowerChoiceOfQ N q = P := by
  apply hinj (lowerChoiceOfQ_mem N q) hP
  rw [lowerChoiceOfQ_modulus, hmod]

lemma lowerQ_card_eq_lowerChoices_card_of_injective {N : ℕ}
    (hinj : Set.InjOn (lowerModulus N) (↑(lowerChoices N) : Set (LowerPrimeChoice N))) :
    (lowerQ N).card = (lowerChoices N).card := by
  simpa [lowerQ] using Finset.card_image_of_injOn (s := lowerChoices N)
    (f := lowerModulus N) hinj

/-- The real lower-bound target appearing in the final theorem. -/
noncomputable def bfvLowerTarget (ε : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * Lscale (-(1 + ε)) N

/-! ## Generic finite CRT target -/

/-- Finite CRT in the integer `Int.ModEq` form used for residue assignments.

Wraps `Nat.chineseRemainderOfFinset` and bridges to `Int.ModEq` via
`Int.natCast_modEq_iff`. -/
theorem int_modEq_crt_finset_exists {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (b : ι → ℤ)
    (hm : ∀ i ∈ s, m i ≠ 0)
    (hcop : Set.Pairwise (↑s : Set ι)
      (fun i j => Nat.Coprime (m i) (m j))) :
    ∃ a : ℤ, ∀ i ∈ s, a ≡ b i [ZMOD (m i : ℤ)] := by
  classical
  set aN : ι → ℕ := fun i => ((b i) % (m i : ℤ)).toNat with haN
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset aN m s hm hcop
  refine ⟨(k : ℤ), ?_⟩
  intro i hi
  have hm_ne : m i ≠ 0 := hm i hi
  have hm_int_ne : (m i : ℤ) ≠ 0 := by exact_mod_cast hm_ne
  have hmod_nonneg : 0 ≤ (b i) % (m i : ℤ) := Int.emod_nonneg _ hm_int_ne
  have h_aN_eq : (aN i : ℤ) = (b i) % (m i : ℤ) := by
    simp [haN, Int.toNat_of_nonneg hmod_nonneg]
  -- CRT result: k ≡ aN i [MOD m i].
  have hk_nat : k ≡ aN i [MOD m i] := hk i hi
  -- Bridge to Int.ModEq.
  have hk_int : (k : ℤ) ≡ (aN i : ℤ) [ZMOD ((m i : ℕ) : ℤ)] :=
    Int.natCast_modEq_iff.mpr hk_nat
  -- And aN i ≡ b i [ZMOD m i] since (b i % m i) ≡ b i.
  have h_aN_modEq_b : (aN i : ℤ) ≡ b i [ZMOD (m i : ℤ)] := by
    rw [h_aN_eq]
    exact (Int.emod_emod_of_dvd (b i) dvd_rfl :
      (b i) % (m i : ℤ) % (m i : ℤ) = b i % (m i : ℤ))
  exact hk_int.trans h_aN_modEq_b

/-! ## Finite encodings for the CRT tree -/

/-- Encode an element of a finite set into a natural residue below `m`, assuming
the set has at most `m` elements. -/
noncomputable def finsetCode (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) : ℕ :=
  (Fin.castLE h ((Finset.equivFin s) x)).1

lemma finsetCode_lt (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) :
    finsetCode s m h x < m :=
  (Fin.castLE h ((Finset.equivFin s) x)).2

lemma finsetCode_injective (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m) :
    Function.Injective (finsetCode s m h) := by
  intro x y hxy
  have hfin :
      Fin.castLE h ((Finset.equivFin s) x) =
        Fin.castLE h ((Finset.equivFin s) y) :=
    Fin.ext hxy
  exact (Finset.equivFin s).injective (Fin.castLE_injective h hfin)

lemma nat_eq_of_int_modEq_of_lt {m a b : ℕ}
    (ha : a < m) (hb : b < m)
    (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (m : ℤ)]) :
    a = b := by
  exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h) ha hb

/-! ## CRT tree data -/

/-- Capacity hypotheses needed by the rooted CRT tree: the root modulus can
encode the first varying prime, and each chosen prime can encode the next
block.  The final proof supplies these eventually from prime-counting upper
bounds and the scale separation. -/
structure LowerEncodingCapacity (N : ℕ) : Prop where
  root :
    ∀ hR : 0 < lowerR N,
      (lowerPrimeInterval N (lowerTailBlock N ⟨0, hR⟩).1).card ≤ lowerP0 N
  next :
    ∀ k : Fin (lowerR N), ∀ hnext : k.1 + 1 < lowerR N,
      ∀ p : ℕ, p ∈ lowerPrimeInterval N (lowerTailBlock N k).1 →
        (lowerPrimeInterval N (lowerTailBlock N ⟨k.1 + 1, hnext⟩).1).card ≤ p
  root_coprime :
    ∀ k : Fin (lowerR N), ∀ p : ℕ,
      p ∈ lowerPrimeInterval N (lowerTailBlock N k).1 →
        Nat.Coprime (lowerP0 N) p

/-- The root or one selected tail prime, used as a CRT modulus. -/
abbrev lowerCRTIndex (N : ℕ) : Type :=
  Option (Fin (lowerR N))

noncomputable def lowerRootCode (N : ℕ) (hcap : LowerEncodingCapacity N)
    (P : LowerPrimeChoice N) : ℕ :=
  if hR : 0 < lowerR N then
    finsetCode (lowerPrimeInterval N (lowerTailBlock N ⟨0, hR⟩).1)
      (lowerP0 N) (hcap.root hR) (P (lowerTailBlock N ⟨0, hR⟩))
  else
    0

noncomputable def lowerStepCode (N : ℕ) (hcap : LowerEncodingCapacity N)
    (P : LowerPrimeChoice N) (k : Fin (lowerR N)) : ℕ :=
  if hnext : k.1 + 1 < lowerR N then
    finsetCode (lowerPrimeInterval N (lowerTailBlock N ⟨k.1 + 1, hnext⟩).1)
      (P (lowerTailBlock N k)).1
      (hcap.next k hnext (P (lowerTailBlock N k)).1 (P (lowerTailBlock N k)).2)
      (P (lowerTailBlock N ⟨k.1 + 1, hnext⟩))
  else
    0

noncomputable def lowerCRTModulus (N : ℕ) (P : LowerPrimeChoice N) :
    lowerCRTIndex N → ℕ
  | none => lowerP0 N
  | some k => (P (lowerTailBlock N k)).1

noncomputable def lowerCRTTarget (N : ℕ) (hcap : LowerEncodingCapacity N)
    (P : LowerPrimeChoice N) : lowerCRTIndex N → ℤ
  | none => lowerRootCode N hcap P
  | some k => lowerStepCode N hcap P k

lemma lowerCRTModulus_ne_zero (N : ℕ) (P : LowerPrimeChoice N)
    (i : lowerCRTIndex N) :
    lowerCRTModulus N P i ≠ 0 := by
  cases i with
  | none => exact (lowerP0_pos N).ne'
  | some k =>
      have hp : Nat.Prime (P (lowerTailBlock N k)).1 :=
        (mem_dyadicPrimeInterval.1 (P (lowerTailBlock N k)).2).2.2
      exact hp.ne_zero

lemma lowerCRTModulus_dvd_lowerModulus (N : ℕ) (P : LowerPrimeChoice N)
    (i : lowerCRTIndex N) :
    lowerCRTModulus N P i ∣ lowerModulus N P := by
  cases i with
  | none =>
      rw [lowerCRTModulus, lowerModulus]
      exact dvd_mul_right _ _
  | some k =>
      rw [lowerCRTModulus, lowerModulus]
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem (fun i : lowerTailIndex N => (P i).1)
          (Finset.mem_univ (lowerTailBlock N k)))
        (lowerP0 N)

lemma lowerCRTModuli_pairwise_coprime {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j))
    (P : LowerPrimeChoice N) :
    Set.Pairwise (↑(Finset.univ : Finset (lowerCRTIndex N)) : Set (lowerCRTIndex N))
      (fun i j => Nat.Coprime (lowerCRTModulus N P i) (lowerCRTModulus N P j)) := by
  intro i _hi j _hj hij
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some k =>
          exact hcap.root_coprime k (P (lowerTailBlock N k)).1
            (P (lowerTailBlock N k)).2
  | some k =>
      cases j with
      | none =>
          exact (hcap.root_coprime k (P (lowerTailBlock N k)).1
            (P (lowerTailBlock N k)).2).symm
      | some l =>
          have hkl : k ≠ l := by
            intro h
            exact hij (by simp [h])
          have hblock_ne : (lowerTailBlock N k).1 ≠ (lowerTailBlock N l).1 := by
            intro hblock
            apply hkl
            apply Fin.ext
            have hval := congrArg Fin.val hblock
            simp [lowerTailBlock, Fin.val_succ] at hval
            omega
          have hp : Nat.Prime (P (lowerTailBlock N k)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerTailBlock N k)).2).2.2
          have hq : Nat.Prime (P (lowerTailBlock N l)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerTailBlock N l)).2).2.2
          have hpq_ne : (P (lowerTailBlock N k)).1 ≠ (P (lowerTailBlock N l)).1 := by
            intro hpq
            have hmem_l :
                (P (lowerTailBlock N k)).1 ∈
                  lowerPrimeInterval N (lowerTailBlock N l).1 := by
              simp [hpq, (P (lowerTailBlock N l)).2]
            exact Finset.disjoint_left.1
              (hdisj (lowerTailBlock N k).1 (lowerTailBlock N l).1 hblock_ne)
              (P (lowerTailBlock N k)).2 hmem_l
          exact (Nat.coprime_primes hp hq).2 hpq_ne

noncomputable def lowerResidueForChoice {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j))
    (P : LowerPrimeChoice N) : ℤ :=
  Classical.choose (int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerCRTIndex N)))
    (m := lowerCRTModulus N P)
    (b := lowerCRTTarget N hcap P)
    (by intro i _hi; exact lowerCRTModulus_ne_zero N P i)
    (lowerCRTModuli_pairwise_coprime hcap hdisj P))

lemma lowerResidueForChoice_spec {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j))
    (P : LowerPrimeChoice N) (i : lowerCRTIndex N) :
    lowerResidueForChoice hcap hdisj P ≡
      lowerCRTTarget N hcap P i [ZMOD (lowerCRTModulus N P i : ℤ)] :=
  Classical.choose_spec (int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerCRTIndex N)))
    (m := lowerCRTModulus N P)
    (b := lowerCRTTarget N hcap P)
    (by intro i _hi; exact lowerCRTModulus_ne_zero N P i)
    (lowerCRTModuli_pairwise_coprime hcap hdisj P)) i (Finset.mem_univ i)

noncomputable def lowerResidueAssignment {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j)) :
    ResidueAssignment (lowerQ N) :=
  fun q => lowerResidueForChoice hcap hdisj (lowerChoiceOfQ N q)

lemma lowerResidueAssignment_modEq_target {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j))
    (q : {q : ℕ // q ∈ lowerQ N}) (i : lowerCRTIndex N) {n : ℤ}
    (hn : n ∈ residueClass q.1 (lowerResidueAssignment hcap hdisj q)) :
    n ≡ lowerCRTTarget N hcap (lowerChoiceOfQ N q) i
      [ZMOD (lowerCRTModulus N (lowerChoiceOfQ N q) i : ℤ)] := by
  have hnq :
      n ≡ lowerResidueForChoice hcap hdisj (lowerChoiceOfQ N q)
        [ZMOD (q.1 : ℤ)] := by
    simpa [residueClass, lowerResidueAssignment] using hn
  have hn_lower :
      n ≡ lowerResidueForChoice hcap hdisj (lowerChoiceOfQ N q)
        [ZMOD (lowerModulus N (lowerChoiceOfQ N q) : ℤ)] := by
    simpa [lowerChoiceOfQ_modulus N q] using hnq
  have hdivNat :
      lowerCRTModulus N (lowerChoiceOfQ N q) i ∣
        lowerModulus N (lowerChoiceOfQ N q) :=
    lowerCRTModulus_dvd_lowerModulus N (lowerChoiceOfQ N q) i
  have hdivInt :
      (lowerCRTModulus N (lowerChoiceOfQ N q) i : ℤ) ∣
        (lowerModulus N (lowerChoiceOfQ N q) : ℤ) := by
    exact_mod_cast hdivNat
  exact (Int.ModEq.of_dvd hdivInt hn_lower).trans
    (lowerResidueForChoice_spec hcap hdisj (lowerChoiceOfQ N q) i)

lemma lowerRootCode_eq_of_modEq {N : ℕ} (hcap : LowerEncodingCapacity N)
    (P P' : LowerPrimeChoice N) (hR : 0 < lowerR N)
    (hmod : (lowerRootCode N hcap P : ℤ) ≡
      (lowerRootCode N hcap P' : ℤ) [ZMOD (lowerP0 N : ℤ)]) :
    P (lowerTailBlock N ⟨0, hR⟩) = P' (lowerTailBlock N ⟨0, hR⟩) := by
  let s := lowerPrimeInterval N (lowerTailBlock N ⟨0, hR⟩).1
  let m := lowerP0 N
  let hcard := hcap.root hR
  have hltP :
      lowerRootCode N hcap P < lowerP0 N := by
    simpa [lowerRootCode, hR, s, m, hcard] using
      finsetCode_lt s m hcard (P (lowerTailBlock N ⟨0, hR⟩))
  have hltP' :
      lowerRootCode N hcap P' < lowerP0 N := by
    simpa [lowerRootCode, hR, s, m, hcard] using
      finsetCode_lt s m hcard (P' (lowerTailBlock N ⟨0, hR⟩))
  have hcode_eq : lowerRootCode N hcap P = lowerRootCode N hcap P' :=
    nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      finsetCode s m hcard (P (lowerTailBlock N ⟨0, hR⟩)) =
        finsetCode s m hcard (P' (lowerTailBlock N ⟨0, hR⟩)) := by
    simpa [lowerRootCode, hR, s, m, hcard] using hcode_eq
  exact finsetCode_injective s m hcard hcode_eq'

lemma lowerStepCode_eq_of_modEq {N : ℕ} (hcap : LowerEncodingCapacity N)
    (P P' : LowerPrimeChoice N) (k : Fin (lowerR N))
    (hnext : k.1 + 1 < lowerR N)
    (hprev : P (lowerTailBlock N k) = P' (lowerTailBlock N k))
    (hmod : (lowerStepCode N hcap P k : ℤ) ≡
      (lowerStepCode N hcap P' k : ℤ)
        [ZMOD ((P (lowerTailBlock N k)).1 : ℤ)]) :
    P (lowerTailBlock N ⟨k.1 + 1, hnext⟩) =
      P' (lowerTailBlock N ⟨k.1 + 1, hnext⟩) := by
  let s := lowerPrimeInterval N (lowerTailBlock N ⟨k.1 + 1, hnext⟩).1
  let m := (P (lowerTailBlock N k)).1
  let hcard := hcap.next k hnext (P (lowerTailBlock N k)).1 (P (lowerTailBlock N k)).2
  have hltP :
      lowerStepCode N hcap P k < (P (lowerTailBlock N k)).1 := by
    simpa [lowerStepCode, hnext, s, m, hcard] using
      finsetCode_lt s m hcard (P (lowerTailBlock N ⟨k.1 + 1, hnext⟩))
  have hltP' :
      lowerStepCode N hcap P' k < (P (lowerTailBlock N k)).1 := by
    have hcard' :=
      hcap.next k hnext (P' (lowerTailBlock N k)).1 (P' (lowerTailBlock N k)).2
    have hlt' :
        lowerStepCode N hcap P' k < (P' (lowerTailBlock N k)).1 := by
      simpa [lowerStepCode, hnext] using
        finsetCode_lt s (P' (lowerTailBlock N k)).1 hcard'
          (P' (lowerTailBlock N ⟨k.1 + 1, hnext⟩))
    simpa [hprev] using hlt'
  have hcode_eq : lowerStepCode N hcap P k = lowerStepCode N hcap P' k :=
    nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      finsetCode s m hcard (P (lowerTailBlock N ⟨k.1 + 1, hnext⟩)) =
        finsetCode s m hcard (P' (lowerTailBlock N ⟨k.1 + 1, hnext⟩)) := by
    simpa [lowerStepCode, hnext, s, m, hcard] using hcode_eq
  exact finsetCode_injective s m hcard hcode_eq'

lemma lowerResidueAssignment_pairwise_disjoint_of_capacity {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j)) :
    PairwiseDisjointResidues (lowerQ N) (lowerResidueAssignment hcap hdisj) := by
  intro q r hqr
  rw [Set.disjoint_left]
  intro z hzq hzr
  let P := lowerChoiceOfQ N q
  let P' := lowerChoiceOfQ N r
  have hP_eq : P = P' := by
    by_cases hR : 0 < lowerR N
    · have hq0 := lowerResidueAssignment_modEq_target hcap hdisj q none hzq
      have hr0 := lowerResidueAssignment_modEq_target hcap hdisj r none hzr
      have hroot_mod :
          (lowerCRTTarget N hcap P none) ≡
            (lowerCRTTarget N hcap P' none)
              [ZMOD (lowerP0 N : ℤ)] := by
        simpa [P, P', lowerCRTModulus] using hq0.symm.trans hr0
      have hzero :
          P (lowerTailBlock N ⟨0, hR⟩) =
            P' (lowerTailBlock N ⟨0, hR⟩) := by
        exact lowerRootCode_eq_of_modEq hcap P P' hR
          (by simpa [lowerCRTTarget] using hroot_mod)
      have hall :
          ∀ n : ℕ, ∀ hn : n < lowerR N,
            P (lowerTailBlock N ⟨n, hn⟩) =
              P' (lowerTailBlock N ⟨n, hn⟩) := by
        intro n
        induction n with
        | zero =>
            intro hn
            simpa using hzero
        | succ n ih =>
            intro hn
            have hprev_lt : n < lowerR N := Nat.lt_of_succ_lt hn
            have hprev := ih hprev_lt
            let k : Fin (lowerR N) := ⟨n, hprev_lt⟩
            have hqk := lowerResidueAssignment_modEq_target hcap hdisj q (some k) hzq
            have hrk := lowerResidueAssignment_modEq_target hcap hdisj r (some k) hzr
            have hstep_mod :
                (lowerCRTTarget N hcap P (some k)) ≡
                  (lowerCRTTarget N hcap P' (some k))
                    [ZMOD ((P (lowerTailBlock N k)).1 : ℤ)] := by
              have hrk' :
                  z ≡ lowerCRTTarget N hcap P' (some k)
                    [ZMOD ((P (lowerTailBlock N k)).1 : ℤ)] := by
                have hprev_val :
                    (lowerChoiceOfQ N r (lowerTailBlock N k)).1 =
                      (lowerChoiceOfQ N q (lowerTailBlock N k)).1 := by
                  dsimp [P, P'] at hprev
                  exact congrArg Subtype.val hprev.symm
                simpa [P, P', lowerCRTModulus, hprev_val] using hrk
              simpa [P, P', lowerCRTModulus] using hqk.symm.trans hrk'
            exact lowerStepCode_eq_of_modEq hcap P P' k hn hprev
              (by simpa [lowerCRTTarget] using hstep_mod)
      exact lowerTailBlock_ext (fun k => hall k.1 k.2)
    · apply lowerTailBlock_ext
      intro k
      have hk : k.1 < lowerR N := k.2
      exact False.elim (hR (lt_of_le_of_lt (Nat.zero_le k.1) hk))
  have hqval : q.1 = r.1 := by
    calc
      q.1 = lowerModulus N P := (lowerChoiceOfQ_modulus N q).symm
      _ = lowerModulus N P' := by rw [hP_eq]
      _ = r.1 := lowerChoiceOfQ_modulus N r
  exact hqr (Subtype.ext hqval)

/-- Remaining scale/prime-counting bookkeeping for the CRT tree capacity.

This uses Mathlib's Chebyshev upper bound `Chebyshev.eventually_primeCounting_le`,
converted to dyadic blocks, plus the BFV scale separation showing each next
block has fewer primes than the previous block's floor endpoint. -/
theorem lowerEncodingCapacity_eventually_analytic :
    ∀ᶠ N : ℕ in atTop, LowerEncodingCapacity N := by
  filter_upwards [lowerPrimeInterval_adjacent_card_le_floor_prev_eventually,
      eventually_lowerLogGap_gt_log_two,
      eventually_lowerY_zero_ge_one] with N hadj hgap hY0
  have hgap_nonneg : 0 ≤ lowerLogGap N := by
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    exact hlog_two_nonneg.trans hgap.le
  constructor
  · intro hR
    have hidx :
        ((lowerTailBlock N ⟨0, hR⟩).1).1 = (lowerZeroIndex N).1 + 1 := by
      simp [lowerTailBlock, lowerZeroIndex]
    have hcard := hadj (lowerZeroIndex N) (lowerTailBlock N ⟨0, hR⟩).1 hidx
    exact hcard.trans (by simp [lowerP0])
  · intro k hnext p hp
    have hidx :
        ((lowerTailBlock N ⟨k.1 + 1, hnext⟩).1).1 =
          ((lowerTailBlock N k).1).1 + 1 := by
      simp [lowerTailBlock, Fin.val_succ]
    have hcard := hadj (lowerTailBlock N k).1
      (lowerTailBlock N ⟨k.1 + 1, hnext⟩).1 hidx
    have hp_floor :
        Nat.floor (lowerY N (lowerTailBlock N k).1) < p :=
      (mem_dyadicPrimeInterval.1 hp).1
    exact hcard.trans (Nat.le_of_lt hp_floor)
  · intro k p hp
    let tail : lowerIndex N := (lowerTailBlock N k).1
    have hsep : 2 * lowerY N (lowerZeroIndex N) < lowerY N tail :=
      lowerY_dyadic_lt_of_lt_index hgap (by
        dsimp [tail]
        simp [lowerTailBlock, lowerZeroIndex, Fin.val_succ])
    have hroot_le :
        (lowerP0 N : ℝ) ≤ 2 * lowerY N (lowerZeroIndex N) :=
      lowerRootFactor_le_two_mul_lowerY hY0
    have hp_floor : Nat.floor (lowerY N tail) < p := by
      dsimp [tail]
      exact (mem_dyadicPrimeInterval.1 hp).1
    have hy_lt_p : lowerY N tail < (p : ℝ) := by
      have hy_floor : lowerY N tail < (Nat.floor (lowerY N tail) : ℝ) + 1 :=
        Nat.lt_floor_add_one (lowerY N tail)
      have hfloor_succ_le : Nat.floor (lowerY N tail) + 1 ≤ p :=
        Nat.succ_le_of_lt hp_floor
      exact hy_floor.trans_le (by exact_mod_cast hfloor_succ_le)
    have hp0_lt_p_real : (lowerP0 N : ℝ) < (p : ℝ) :=
      hroot_le.trans_lt (hsep.trans hy_lt_p)
    have hp0_lt_p : lowerP0 N < p := by
      exact_mod_cast hp0_lt_p_real
    have hpprime : Nat.Prime p := (mem_dyadicPrimeInterval.1 hp).2.2
    exact (Nat.coprime_of_lt_prime (lowerP0_pos N).ne' hp0_lt_p hpprime).symm

/-- BFV lower-construction capacity, discharged against the named
prime-counting and scale bookkeeping stub
`lowerEncodingCapacity_eventually_analytic`. -/
theorem lowerEncodingCapacity_eventually :
    ∀ᶠ N : ℕ in atTop, LowerEncodingCapacity N :=
  lowerEncodingCapacity_eventually_analytic

/-! ## Lower-family theorem targets -/

/-- The named prime blocks are eventually pairwise disjoint as real dyadic
intervals, after converting through their floor endpoints. -/
theorem lowerPrimeIntervals_pairwise_disjoint :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerIndex N, i ≠ j →
        Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j) := by
  filter_upwards [eventually_lowerLogGap_gt_log_two] with N hgap
  intro i j hij
  have hijval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hijval with hlt | hgt
  · have hsep : 2 * lowerY N i < lowerY N j :=
      lowerY_dyadic_lt_of_lt_index hgap hlt
    have hfloor : Nat.floor (2 * lowerY N i) ≤ Nat.floor (lowerY N j) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerY N i)) (Nat.floor (2 * lowerY N i)))
          (Finset.Ioc (Nat.floor (lowerY N j)) (Nat.floor (2 * lowerY N j))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPrimeInterval, dyadicPrimeInterval] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)
  · have hsep : 2 * lowerY N j < lowerY N i :=
      lowerY_dyadic_lt_of_lt_index hgap hgt
    have hfloor : Nat.floor (2 * lowerY N j) ≤ Nat.floor (lowerY N i) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerY N j)) (Nat.floor (2 * lowerY N j)))
          (Finset.Ioc (Nat.floor (lowerY N i)) (Nat.floor (2 * lowerY N i))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPrimeInterval, dyadicPrimeInterval, disjoint_comm] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)

/-- Unique factorization plus disjoint prime blocks makes the product map from
prime-choice tuples to moduli injective. -/
theorem lowerModulus_injective_eventually :
    ∀ᶠ N : ℕ in atTop,
      Set.InjOn (lowerModulus N) (↑(lowerChoices N) : Set (LowerPrimeChoice N)) := by
  filter_upwards [lowerPrimeIntervals_pairwise_disjoint] with N hdisj
  intro P _hP P' _hP' heq
  have htail_eq :
      (∏ i : lowerTailIndex N, (P i).1) =
        ∏ i : lowerTailIndex N, (P' i).1 := by
    have hp0 : lowerP0 N ≠ 0 := (lowerP0_pos N).ne'
    exact mul_left_cancel₀ hp0 (by simpa [lowerModulus] using heq)
  funext i
  apply Subtype.ext
  let p : ℕ := (P i).1
  have hpPrime : Nat.Prime p := (mem_dyadicPrimeInterval.1 (P i).2).2.2
  have hp_dvd_left : p ∣ ∏ k : lowerTailIndex N, (P k).1 := by
    unfold p
    exact Finset.dvd_prod_of_mem (fun k : lowerTailIndex N => (P k).1) (Finset.mem_univ i)
  have hp_dvd_prod : p ∣ ∏ k : lowerTailIndex N, (P' k).1 := by
    rwa [htail_eq] at hp_dvd_left
  rcases (hpPrime.prime.dvd_finset_prod_iff (S := Finset.univ)
      (fun k : lowerTailIndex N => (P' k).1)).1 hp_dvd_prod with
    ⟨j, _hj, hp_dvd_pj⟩
  have hpjPrime : Nat.Prime (P' j).1 := (mem_dyadicPrimeInterval.1 (P' j).2).2.2
  have hp_eq_pj : p = (P' j).1 :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hpjPrime).1 hp_dvd_pj
  have hji : j = i := by
    by_contra hne
    have hne' : i.1 ≠ j.1 := by
      intro h
      exact hne (Subtype.ext h.symm)
    have hp_mem_i : p ∈ lowerPrimeInterval N i := (P i).2
    have hp_mem_j : p ∈ lowerPrimeInterval N j := by
      simp [p, hp_eq_pj, (P' j).2]
    exact Finset.disjoint_left.1 (hdisj i.1 j.1 hne') hp_mem_i hp_mem_j
  subst hji
  simpa [p] using hp_eq_pj

/-- The BFV product estimate: all constructed moduli are eventually in
`[1, N]`. -/
theorem lowerQ_moduli_in_range_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ q ∈ lowerQ N, 1 ≤ q ∧ q ≤ N := by
  filter_upwards [Filter.eventually_gt_atTop 0, eventually_lowerY_zero_ge_one] with N hN hY0 q hq
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [lowerQ] at hq
  rcases Finset.mem_image.1 hq with ⟨P, _hP, rfl⟩
  exact ⟨Nat.succ_le_of_lt (lowerModulus_pos N P),
    lowerModulus_le_N_of_root_scale hNpos hY0 P⟩

/-- CRT residue choices for the lower family are pairwise disjoint. -/
theorem lowerQ_pairwise_disjoint_residues_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∃ a : ResidueAssignment (lowerQ N),
        PairwiseDisjointResidues (lowerQ N) a := by
  filter_upwards [lowerEncodingCapacity_eventually,
      lowerPrimeIntervals_pairwise_disjoint] with N hcap hdisj
  exact ⟨lowerResidueAssignment hcap hdisj,
    lowerResidueAssignment_pairwise_disjoint_of_capacity hcap hdisj⟩

/-! ## From the explicit family to `PossibleCard` -/

lemma admissible_mono {N : ℕ} {Q Q' : Finset ℕ}
    (hQ : Admissible N Q) (hsub : Q' ⊆ Q) :
    Admissible N Q' := by
  constructor
  · intro q hq
    exact hQ.1 q (hsub hq)
  · rcases hQ.2 with ⟨a, ha⟩
    exact ⟨restrictAssignment a hsub, PairwiseDisjointResidues.mono ha hsub⟩

lemma possibleCard_of_admissible_card_le {N r : ℕ} {Q : Finset ℕ}
    (hQ : Admissible N Q) (hr : r ≤ Q.card) :
    PossibleCard N r := by
  classical
  rcases Finset.exists_subset_card_eq (s := Q) hr with ⟨Q', hsub, hcard⟩
  exact ⟨Q', admissible_mono hQ hsub, hcard⟩

/-- The lower construction gives an admissible family of every required target
size.  The stale full-product cardinality route in this file is deliberately
bypassed: the source-aligned rooted path construction proves the needed lower
bound for `f N`, and `possibleCard_f` supplies an actual extremal admissible
family from which we take a subset. -/
theorem lower_possibleCard :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      PossibleCard N (Nat.ceil (bfvLowerTarget ε N)) := by
  intro ε hε
  filter_upwards [lowerPath_f_lower_bound_eventually ε hε] with N hf_lower
  have hceil_le_f : Nat.ceil (bfvLowerTarget ε N) ≤ f N := by
    apply Nat.ceil_le.2
    simpa [bfvLowerTarget] using hf_lower
  rcases possibleCard_f N with ⟨Q, hQ, hQcard⟩
  exact possibleCard_of_admissible_card_le hQ (by
    simpa [hQcard] using hceil_le_f)

end Erdos202
