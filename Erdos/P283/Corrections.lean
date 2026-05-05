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

This is the second-hardest sub-lemma of the whole proof (after Lemma 3). -/
theorem exists_large_correction_denominator
    (p : ℚ[X]) (hp : IntValued p) (hA : IntValued (A p))
    (Tg aσ J L lower : ℕ) (Gν : Finset ℕ) (hGν : IsEgyptianPattern Gν)
    (hQGν : IntValued (switchingPoly p Gν))
    (forbiddenFinite : Finset ℕ) (hTg : 1 ≤ Tg) :
    ∃ c : ℕ,
      c ≡ aσ [MOD Tg] ∧
      lower < c ∧ L < c ∧
      0 < intEval (switchingPoly p Gν) hQGν ((c : ℕ) : ℤ) ∧
      c ∉ forbiddenFinite ∧
      (∀ j, J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ insert 1 Gν, e * c ≠ h * D j) := by
  sorry

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
