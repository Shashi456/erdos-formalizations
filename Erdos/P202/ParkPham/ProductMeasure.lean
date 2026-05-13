/-
Erdős Problem 202 — Park–Pham layer, Stage 2.

Finite Bernoulli product measure on subsets of a finite universe `X`,
expressed as a finite sum (no `MeasureTheory`). Used by the expectation-
threshold theorem and the random-partition argument downstream.
-/

import Mathlib
import Erdos.P202.ParkPham.BooleanFamilies

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Bernoulli mass of a subset `S ⊆ X` at density `p`. -/
noncomputable def bernoulliMass (X S : Finset α) (p : ℝ) : ℝ :=
  p ^ S.card * (1 - p) ^ (X.card - S.card)

/-- Bernoulli probability of a family `U` of subsets of `X` at density `p`. -/
noncomputable def muP (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ S ∈ X.powerset.filter (· ∈ U), bernoulliMass X S p

lemma bernoulliMass_nonneg {X S : Finset α} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bernoulliMass X S p := by
  unfold bernoulliMass
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- `muP` is nonnegative for `p ∈ [0, 1]`. -/
lemma muP_nonneg {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ muP X U p := by
  refine Finset.sum_nonneg fun S _ => bernoulliMass_nonneg h0 h1

/-- `muP` is monotone in the family. -/
lemma muP_mono_family {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hUV : U ⊆ V) : muP X U p ≤ muP X V p := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSU⟩
    exact Finset.mem_filter.mpr ⟨hSX, hUV hSU⟩
  · intros
    exact bernoulliMass_nonneg h0 h1

/-- Bernoulli weights sum to 1 over the powerset of any finite set `X`,
for any `p ∈ ℝ`. This is the finite binomial identity. -/
lemma sum_bernoulliMass_eq_one (X : Finset α) {p : ℝ}
    (h : p + (1 - p) = 1) :
    (∑ S ∈ X.powerset, bernoulliMass X S p) = 1 := by
  classical
  -- Group by cardinality and use the binomial theorem.
  have hsum :
      (∑ S ∈ X.powerset, p ^ S.card * (1 - p) ^ (X.card - S.card)) =
        ∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k)) := by
    classical
    rw [Finset.sum_powerset_apply_card
      (f := fun k => p ^ k * (1 - p) ^ (X.card - k))]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [nsmul_eq_mul]
  unfold bernoulliMass
  rw [hsum]
  have hbinom : (p + (1 - p)) ^ X.card =
      ∑ k ∈ Finset.range (X.card + 1),
        p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ) :=
    add_pow p (1 - p) X.card
  have : (p + (1 - p)) ^ X.card = 1 := by rw [h]; exact one_pow _
  rw [this] at hbinom
  -- Reshape RHS to match.
  have hreshape :
      (∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k))) =
        (∑ k ∈ Finset.range (X.card + 1),
          p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hreshape, ← hbinom]

/-- Upper bound: `muP X U p ≤ 1` for `p ∈ [0,1]` (in fact equals 1 minus the
mass on the complement). -/
lemma muP_le_one {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : muP X U p ≤ 1 := by
  have hsum := sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)
  have hsub : muP X U p ≤ ∑ S ∈ X.powerset, bernoulliMass X S p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro S hS; exact (Finset.mem_filter.mp hS).1
    · intros; exact bernoulliMass_nonneg h0 h1
  linarith

/-! ## Marginal at a fixed subset

If `U = upClosureIn X {T₀}` (the upper closure of a single set), then
`muP X U p = p^|T₀|`. This is the "probability that random subset at
density `p` contains `T₀`" identity used by the random-partition argument.
-/

/-- The upper closure of a singleton family `{T₀}` inside `X` is
`{T ⊆ X : T₀ ⊆ T}`. -/
lemma upClosureIn_singleton (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) :
    upClosureIn X {T₀} =
      X.powerset.filter (fun T => T₀ ⊆ T) := by
  classical
  ext T
  constructor
  · intro hT
    rcases mem_upClosureIn.mp hT with ⟨hTX, S, hS, hST⟩
    rcases Finset.mem_singleton.mp hS with rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hST⟩
  · intro hT
    rcases Finset.mem_filter.mp hT with ⟨hTX, hT₀T⟩
    exact mem_upClosureIn.mpr ⟨Finset.mem_powerset.mp hTX, T₀,
      Finset.mem_singleton.mpr rfl, hT₀T⟩

/-- **Marginal identity.** For `T₀ ⊆ X` and `p ∈ [0,1]`,
`muP X (upClosureIn X {T₀}) p = p^|T₀|`. -/
theorem muP_upClosure_single (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    muP X (upClosureIn X {T₀}) p = p ^ T₀.card := by
  classical
  -- Reparametrize: subsets `S ⊆ X` with `T₀ ⊆ S` correspond bijectively
  -- to subsets `S' ⊆ X \ T₀` via `S = T₀ ∪ S'`. The Bernoulli mass factors
  -- as `p^|T₀| · p^|S'| · (1-p)^(|X\T₀|-|S'|)`, and the inner sum is 1.
  set Y : Finset α := X \ T₀ with hY
  have hY_card : Y.card = X.card - T₀.card := by
    simp [hY, Finset.card_sdiff_of_subset hT₀]
  have hT₀_disj_Y : Disjoint T₀ Y := by
    simp [hY, Finset.disjoint_sdiff]
  -- Set up the bijection.
  let f : Finset α → Finset α := fun S' => T₀ ∪ S'
  have hf_inj : Set.InjOn f (↑Y.powerset) := by
    intro S' hS' R' hR' hfeq
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hR'Y : R' ⊆ Y := Finset.mem_powerset.mp hR'
    have hdisj_S' : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hdisj_R' : Disjoint T₀ R' := Finset.disjoint_of_subset_right hR'Y hT₀_disj_Y
    have heq : T₀ ∪ S' = T₀ ∪ R' := hfeq
    -- Use sdiff: S' = (T₀ ∪ S') \ T₀ when T₀ is disjoint from S'.
    have hS'_eq : S' = (T₀ ∪ S') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_S' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxS'
        · exact (hxnT₀ hxT₀).elim
        · exact hxS'
    have hR'_eq : R' = (T₀ ∪ R') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_R' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxR'
        · exact (hxnT₀ hxT₀).elim
        · exact hxR'
    rw [hS'_eq, hR'_eq, heq]
  -- The image of Y.powerset under f is exactly the filter we sum over.
  have him :
      Y.powerset.image f =
        X.powerset.filter (fun T => T ∈ upClosureIn X {T₀}) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_filter,
      mem_upClosureIn, Finset.mem_singleton]
    constructor
    · rintro ⟨S', hS'Y, rfl⟩
      have hS'X : S' ⊆ X := hS'Y.trans Finset.sdiff_subset
      have hfX : T₀ ∪ S' ⊆ X := Finset.union_subset hT₀ hS'X
      refine ⟨hfX, hfX, T₀, rfl, ?_⟩
      exact Finset.subset_union_left
    · rintro ⟨hTX, _, S₀, hS₀eq, hS₀T⟩
      refine ⟨T \ T₀, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnT₀⟩
        exact Finset.mem_sdiff.mpr ⟨hTX hxT, hxnT₀⟩
      · -- f (T \ T₀) = T₀ ∪ (T \ T₀) = T, since T₀ ⊆ T (via S₀ = T₀ ⊆ T).
        have hT₀T : T₀ ⊆ T := by
          have := hS₀T
          rw [hS₀eq] at this
          exact this
        show T₀ ∪ (T \ T₀) = T
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hxT₀ | hxd
          · exact hT₀T hxT₀
          · exact (Finset.mem_sdiff.mp hxd).1
        · intro hxT
          by_cases hxT₀ : x ∈ T₀
          · exact Finset.mem_union.mpr (Or.inl hxT₀)
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxT₀⟩))
  -- Now: muP = Σ_{T in filter} bernoulli T = Σ_{S' ⊆ Y} bernoulli (T₀ ∪ S').
  unfold muP
  rw [← him, Finset.sum_image hf_inj]
  -- bernoulliMass X (T₀ ∪ S') p = p^|T₀ ∪ S'| (1-p)^(|X| - |T₀ ∪ S'|)
  --                              = p^(|T₀| + |S'|) (1-p)^(|Y| - |S'|)
  --                              = p^|T₀| · [p^|S'| (1-p)^(|Y| - |S'|)]
  have hkey :
      ∀ S' ∈ Y.powerset,
        bernoulliMass X (f S') p = p ^ T₀.card * bernoulliMass Y S' p := by
    intro S' hS'
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hdisj : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hcard : (T₀ ∪ S').card = T₀.card + S'.card :=
      Finset.card_union_of_disjoint hdisj
    have hsum_eq : X.card - (T₀.card + S'.card) = Y.card - S'.card := by
      rw [hY_card]; omega
    show p ^ (f S').card * (1 - p) ^ (X.card - (f S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    show p ^ (T₀ ∪ S').card * (1 - p) ^ (X.card - (T₀ ∪ S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    rw [hcard, hsum_eq, pow_add, mul_assoc]
  -- Apply hkey, factor out p^|T₀|, and use sum_bernoulliMass_eq_one on Y.
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have : (∑ S' ∈ Y.powerset, bernoulliMass Y S' p) = 1 :=
    sum_bernoulliMass_eq_one (α := α) Y (p := p) (by ring)
  rw [this, mul_one]

end

end ParkPham
end Erdos202
