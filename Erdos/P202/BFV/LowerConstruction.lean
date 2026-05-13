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

/-- A concrete product-normalized exponentially spaced scale for the `i`th
dyadic prime block.

The final BFV proof needs only eventual disjointness and product estimates for
these named scales; those hard estimates are isolated below. -/
noncomputable def lowerY (N : ℕ) (i : lowerIndex N) : ℝ :=
  Real.exp (lowerLogScale N i)

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
  sorry

/-- Unique factorization plus disjoint prime blocks makes the product map from
prime-choice tuples to moduli injective. -/
theorem lowerModulus_injective_eventually :
    ∀ᶠ N : ℕ in atTop,
      Set.InjOn (lowerModulus N) (↑(lowerChoices N) : Set (LowerPrimeChoice N)) := by
  sorry

/-- The BFV product estimate: all constructed moduli are eventually in
`[1, N]`. -/
theorem lowerQ_moduli_in_range_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ q ∈ lowerQ N, 1 ≤ q ∧ q ≤ N := by
  sorry

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
