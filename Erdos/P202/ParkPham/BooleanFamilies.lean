/-
Erdős Problem 202 — Park–Pham layer, Stage 1.

Finite Boolean families, upper closures, increasing predicate, minimal
members, and the `ell(U)` complexity bound used by the Park–Pham
expectation-threshold theorem.

All definitions live over a finite ground universe `X : Finset α`. We
avoid any general measure theory; subsets of `X` are represented as
`Finset α` filtered by `S ⊆ X`.
-/

import Mathlib
import Erdos.P202.SpreadCore

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- The upper closure of `A` inside the universe `X`: the set of subsets
`T ⊆ X` that contain some member of `A`. -/
def upClosureIn (X : Finset α) (A : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun T => ∃ S ∈ A, S ⊆ T

@[simp]
lemma mem_upClosureIn {X : Finset α} {A : Finset (Finset α)} {T : Finset α} :
    T ∈ upClosureIn X A ↔ T ⊆ X ∧ ∃ S ∈ A, S ⊆ T := by
  simp [upClosureIn, mem_powerset]

/-- A family `U ⊆ X.powerset` is increasing if it is closed under taking
supersets inside `X`. -/
def IncreasingIn (X : Finset α) (U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∀ T : Finset α, T ⊆ X → S ⊆ T → T ∈ U

/-- The upper closure of any family is increasing. -/
lemma increasingIn_upClosureIn (X : Finset α) (A : Finset (Finset α)) :
    IncreasingIn X (upClosureIn X A) := by
  intro S hS T hTX hST
  rcases mem_upClosureIn.mp hS with ⟨_, S₀, hS₀A, hS₀S⟩
  exact mem_upClosureIn.mpr ⟨hTX, S₀, hS₀A, hS₀S.trans hST⟩

/-- Minimal members of `U`: members with no proper subset also in `U`. -/
def minimalMembersIn (X : Finset α) (U : Finset (Finset α)) : Finset (Finset α) :=
  U.filter fun S => ∀ T ∈ U, ¬ T ⊂ S

@[simp]
lemma mem_minimalMembersIn {X : Finset α} {U : Finset (Finset α)} {S : Finset α} :
    S ∈ minimalMembersIn X U ↔ S ∈ U ∧ ∀ T ∈ U, ¬ T ⊂ S := by
  simp [minimalMembersIn]

/-- The complexity parameter `ell(U)`: max card of a minimal member,
clamped at 2 so that `Real.log (ell U) ≥ Real.log 2 > 0`. -/
noncomputable def ell (X : Finset α) (U : Finset (Finset α)) : ℕ :=
  max 2 ((minimalMembersIn X U).sup Finset.card)

lemma two_le_ell (X : Finset α) (U : Finset (Finset α)) : 2 ≤ ell X U :=
  le_max_left _ _

lemma ell_pos (X : Finset α) (U : Finset (Finset α)) : 0 < ell X U :=
  lt_of_lt_of_le (by norm_num) (two_le_ell X U)

/-- Every member of `U` contains a minimal member of `U` (as a subset). -/
lemma exists_minimal_subset
    {X : Finset α} {U : Finset (Finset α)}
    {S : Finset α} (hS : S ∈ U) :
    ∃ T ∈ minimalMembersIn X U, T ⊆ S := by
  classical
  -- Pick T₀ ⊆ S in U with minimum card.
  let candidates : Finset (Finset α) := U.filter fun T => T ⊆ S
  have hSc : S ∈ candidates := by
    simp [candidates, hS, subset_refl]
  rcases candidates.exists_min_image Finset.card ⟨S, hSc⟩ with ⟨T₀, hT₀, hmin⟩
  have hT₀U : T₀ ∈ U := (Finset.mem_filter.mp hT₀).1
  have hT₀S : T₀ ⊆ S := (Finset.mem_filter.mp hT₀).2
  refine ⟨T₀, mem_minimalMembersIn.mpr ⟨hT₀U, ?_⟩, hT₀S⟩
  intro T hTU hT_lt
  -- T ⊂ T₀ ⊆ S, so T ⊆ S, so T ∈ candidates, hence T₀.card ≤ T.card,
  -- contradicting T.card < T₀.card.
  have hTS : T ⊆ S := hT_lt.subset.trans hT₀S
  have hTcand : T ∈ candidates := by
    simp [candidates, hTU, hTS]
  have : T₀.card ≤ T.card := hmin T hTcand
  have hlt : T.card < T₀.card := Finset.card_lt_card hT_lt
  exact absurd this (not_le.mpr hlt)

/-- Minimal members of the upper closure of a `k`-uniform family have card
at most `k`. -/
lemma minimalMembersIn_upClosureIn_card_le
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X)
    {S : Finset α} (hS : S ∈ minimalMembersIn X (upClosureIn X A)) :
    S.card ≤ k := by
  classical
  rcases mem_minimalMembersIn.mp hS with ⟨hSup, hmin⟩
  rcases mem_upClosureIn.mp hSup with ⟨hSX, S₀, hS₀A, hS₀S⟩
  -- S₀ is in the closure (it contains itself), so by minimality of S, S₀ ⊄ S.
  have hS₀_up : S₀ ∈ upClosureIn X A :=
    mem_upClosureIn.mpr ⟨(hAX S₀ hS₀A), S₀, hS₀A, subset_refl _⟩
  have hS₀_not_lt : ¬ S₀ ⊂ S := hmin S₀ hS₀_up
  -- Then S₀ = S (since S₀ ⊆ S and S₀ is not a strict subset).
  have hS₀_eq_S : S₀ = S := by
    by_contra hne
    exact hS₀_not_lt (hS₀S.ssubset_of_ne hne)
  -- Hence S.card = S₀.card = k.
  have : S.card = k := hS₀_eq_S ▸ hUniform S₀ hS₀A
  exact this.le

/-- **`ell` bound.** The complexity parameter of the upper closure of a
`k`-uniform family is at most `max 2 k`. -/
theorem ell_upClosure_le {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ell X (upClosureIn X A) ≤ max 2 k := by
  classical
  have hsup_le : (minimalMembersIn X (upClosureIn X A)).sup Finset.card ≤ k := by
    refine Finset.sup_le ?_
    intro S hS
    exact minimalMembersIn_upClosureIn_card_le hUniform hAX hS
  unfold ell
  exact max_le_max le_rfl hsup_le

end

end ParkPham
end Erdos202
