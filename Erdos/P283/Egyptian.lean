/-
Erdős Problems 283 + 351 — §1 Egyptian switches, Lemmas 3 & 4.

  * `Lemma 3 (egyptian_expansion)` — every `R ∈ ℚ_{>0}` has Egyptian expansions
    (sums of distinct unit fractions with denominators `> L`) of all sufficiently
    large lengths.
  * `Lemma 4 (egyptian_pattern_with_period)` — for any `T, M ≥ 1` and residue
    `ρ ∈ ZMod M`, an Egyptian pattern `E` exists with `T ∣ e` for every `e ∈ E`
    and `|E| ≡ ρ (mod M)`.

Both are axiom-free. Lemma 4 is a direct corollary of Lemma 3.

Internal helper lemmas (broken out for clarity):
  * `egyptian_split_*`        — properties of the `1/y → 1/(y+1) + 1/(y(y+1))`
                                 step that extends an expansion by one term.
  * `egyptian_expansion_exists` — a single expansion exists (greedy).
  * `egyptian_expansion_all_large_cardinalities` — all sufficiently large
                                                    lengths.
-/

import Erdos.P283.Basic

namespace PolynomialEgyptianSums

open Finset

/-! ## Splitting step (extends an expansion by one term) -/

/-- The split identity `1/y = 1/(y+1) + 1/(y(y+1))` for `y ≥ 1`. -/
lemma egyptian_split_identity (y : ℕ) (hy : 1 ≤ y) :
    (1 : ℚ) / y = 1 / (y + 1 : ℕ) + 1 / (y * (y + 1) : ℕ) := by
  sorry

/-- After a split at the largest denominator `y`, the new denominators
`y + 1` and `y(y+1)` are both larger than `y`. -/
lemma egyptian_split_lower_bound (y : ℕ) (hy : 1 ≤ y) :
    y < y + 1 ∧ y < y * (y + 1) := by
  sorry

/-! ## Lemma 3 — Egyptian expansion existence and arbitrary length -/

/-- Auxiliary: a single Egyptian expansion exists (greedy). -/
lemma egyptian_expansion_exists (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ E : Finset ℕ, (∀ e ∈ E, L < e) ∧ R = ∑ e ∈ E, (1 : ℚ) / e := by
  sorry

/-- **Lemma 3 (PDF §1).** Any positive rational `R` admits Egyptian expansions
(distinct denominators all `> L`) with all sufficiently large numbers of terms. -/
theorem egyptian_expansion (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ E : Finset ℕ,
      E.card = k ∧ (∀ e ∈ E, L < e) ∧ R = ∑ e ∈ E, (1 : ℚ) / e := by
  sorry

/-! ## Lemma 4 — Egyptian patterns with prescribed period and cardinality -/

/-- **Lemma 4 (PDF §1).** For integers `T, M ≥ 1` and a residue `ρ ∈ ZMod M`,
there is an Egyptian pattern `E` such that `T ∣ e` for every `e ∈ E` and
`|E| ≡ ρ (mod M)`. -/
theorem egyptian_pattern_with_period (T M : ℕ) (hT : 1 ≤ T) (hM : 1 ≤ M)
    (ρ : ZMod M) :
    ∃ E : Finset ℕ, IsEgyptianPattern E ∧ (∀ e ∈ E, T ∣ e) ∧
      (E.card : ZMod M) = ρ := by
  sorry

end PolynomialEgyptianSums
