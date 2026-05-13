/-
Erdos Problem 202 -- BFV lower construction skeleton.

This file names the explicit lower-family objects used by the
Bourgain--Filaseta--Verstraeten construction: dyadic prime choices, their
product moduli, the finite modulus family, and the theorem targets asserting
injectivity, size, modulus bounds, and CRT residue disjointness.
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.BFV.PrimeIntervals
import Erdos.P202.BFV.Chebyshev

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

/-- A choice of one prime from every BFV lower block. -/
abbrev LowerPrimeChoice (N : ℕ) : Type :=
  (i : lowerIndex N) → {p : ℕ // p ∈ lowerPrimeInterval N i}

/-- All prime-choice tuples. -/
noncomputable def lowerChoices (N : ℕ) : Finset (LowerPrimeChoice N) :=
  Fintype.piFinset fun i : lowerIndex N => (lowerPrimeInterval N i).attach

/-- The modulus attached to a prime-choice tuple. -/
noncomputable def lowerModulus (N : ℕ) (P : LowerPrimeChoice N) : ℕ :=
  ∏ i : lowerIndex N, (P i).1

lemma lowerModulus_pos (N : ℕ) (P : LowerPrimeChoice N) :
    0 < lowerModulus N P := by
  unfold lowerModulus
  exact Finset.prod_pos (fun i _hi => by
    have hp : Nat.Prime (P i).1 := (mem_dyadicPrimeInterval.1 (P i).2).2.2
    exact hp.pos)

lemma lowerModulus_le_N_of_pos {N : ℕ} (hNpos : 0 < (N : ℝ))
    (P : LowerPrimeChoice N) :
    lowerModulus N P ≤ N := by
  have hreal : (lowerModulus N P : ℝ) ≤ (N : ℝ) := by
    calc
      (lowerModulus N P : ℝ)
          = ∏ i : lowerIndex N, ((P i).1 : ℝ) := by
              unfold lowerModulus
              rw [Nat.cast_prod]
      _ ≤ ∏ i : lowerIndex N, (2 : ℝ) * lowerY N i := by
              refine Finset.prod_le_prod (s := Finset.univ) ?h0 ?hle
              · intro i _hi
                positivity
              · intro i _hi
                have hp_le_nat : (P i).1 ≤ Nat.floor (2 * lowerY N i) :=
                  (mem_dyadicPrimeInterval.1 (P i).2).2.1
                have hp_le_floor :
                    ((P i).1 : ℝ) ≤ (Nat.floor (2 * lowerY N i) : ℝ) := by
                  exact_mod_cast hp_le_nat
                have hnonneg : 0 ≤ 2 * lowerY N i := by
                  unfold lowerY
                  positivity
                have hfloor_le :
                    (Nat.floor (2 * lowerY N i) : ℝ) ≤ 2 * lowerY N i :=
                  Nat.floor_le hnonneg
                exact hp_le_floor.trans hfloor_le
      _ = (N : ℝ) := lowerY_dyadic_product_eq hNpos
  exact_mod_cast hreal

/-- The finite BFV lower family of moduli. -/
noncomputable def lowerQ (N : ℕ) : Finset ℕ :=
  (lowerChoices N).image (lowerModulus N)

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
  funext i
  apply Subtype.ext
  let p : ℕ := (P i).1
  have hpPrime : Nat.Prime p := (mem_dyadicPrimeInterval.1 (P i).2).2.2
  have hp_dvd_left : p ∣ lowerModulus N P := by
    unfold lowerModulus p
    exact Finset.dvd_prod_of_mem (fun k : lowerIndex N => (P k).1) (Finset.mem_univ i)
  have hp_dvd_right : p ∣ lowerModulus N P' := by
    rwa [heq] at hp_dvd_left
  have hp_dvd_prod : p ∣ ∏ k : lowerIndex N, (P' k).1 := by
    simpa [lowerModulus] using hp_dvd_right
  rcases (hpPrime.prime.dvd_finset_prod_iff (S := Finset.univ)
      (fun k : lowerIndex N => (P' k).1)).1 hp_dvd_prod with
    ⟨j, _hj, hp_dvd_pj⟩
  have hpjPrime : Nat.Prime (P' j).1 := (mem_dyadicPrimeInterval.1 (P' j).2).2.2
  have hp_eq_pj : p = (P' j).1 :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hpjPrime).1 hp_dvd_pj
  have hji : j = i := by
    by_contra hne
    have hne' : i ≠ j := by
      intro h
      exact hne h.symm
    have hp_mem_i : p ∈ lowerPrimeInterval N i := (P i).2
    have hp_mem_j : p ∈ lowerPrimeInterval N j := by
      simp [p, hp_eq_pj, (P' j).2]
    exact Finset.disjoint_left.1 (hdisj i j hne') hp_mem_i hp_mem_j
  subst hji
  simpa [p] using hp_eq_pj

/-- The BFV product estimate: all constructed moduli are eventually in
`[1, N]`. -/
theorem lowerQ_moduli_in_range_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ q ∈ lowerQ N, 1 ≤ q ∧ q ≤ N := by
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN q hq
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [lowerQ] at hq
  rcases Finset.mem_image.1 hq with ⟨P, _hP, rfl⟩
  exact ⟨Nat.succ_le_of_lt (lowerModulus_pos N P), lowerModulus_le_N_of_pos hNpos P⟩

/-- CRT residue choices for the lower family are pairwise disjoint. -/
theorem lowerQ_pairwise_disjoint_residues_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∃ a : ResidueAssignment (lowerQ N),
        PairwiseDisjointResidues (lowerQ N) a := by
  sorry

/-- Cardinality lower bound for the BFV family, combining dyadic prime supply,
injectivity, and the explicit scale algebra. -/
theorem lowerQ_card_lower_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Nat.ceil (bfvLowerTarget ε N) ≤ (lowerQ N).card := by
  sorry

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

/-- The explicit BFV lower family gives an admissible family of every required
target size. -/
theorem lower_possibleCard :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      PossibleCard N (Nat.ceil (bfvLowerTarget ε N)) := by
  intro ε hε
  filter_upwards [lowerQ_moduli_in_range_eventually,
      lowerQ_pairwise_disjoint_residues_eventually,
      lowerQ_card_lower_bound_eventually ε hε] with N hRange hResidues hCard
  exact possibleCard_of_admissible_card_le
    ⟨hRange, hResidues⟩ hCard

end Erdos202
