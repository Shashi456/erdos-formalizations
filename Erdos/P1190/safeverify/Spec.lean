/-
SafeVerify target for Erdős Problem 1190.

The bodies in this file are placeholders by design: SafeVerify compares the
matching declarations in the submitted `.olean` and checks that their axiom
dependencies stay within the allowed core set (`propext`, `Classical.choice`,
`Quot.sound`).
-/

import Mathlib

set_option autoImplicit false

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Shared Problem 202 vocabulary used by the 1190 statement -/

def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

noncomputable def f (_N : ℕ) : ℕ := by
  sorry

noncomputable def Zscale (_N : ℕ) : ℝ := by
  sorry

noncomputable def Lscale (_α : ℝ) (_N : ℕ) : ℝ := by
  sorry

/-! ## Erdős 1190 surface -/

/-- Reciprocal mass of a finite set of moduli. -/
noncomputable def reciprocalSum (Q : Finset ℕ) : ℝ :=
  ∑ q ∈ Q, (q : ℝ)⁻¹

/-- Alias for `reciprocalSum`, matching the shorter roadmap name. -/
noncomputable abbrev recipSum : Finset ℕ → ℝ :=
  reciprocalSum

/-- A 1190-admissible tail family: all moduli are strictly larger than `m`, and
some choice of residue classes modulo those moduli is pairwise disjoint. -/
def TailAdmissible (m : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, m < q) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

/-- Alias for `TailAdmissible`, matching the roadmap name. -/
abbrev AdmissibleAbove : ℕ → Finset ℕ → Prop :=
  TailAdmissible

/-- The set of reciprocal sums appearing in Problem 1190. -/
noncomputable def reciprocalSums1190 (m : ℕ) : Set ℝ :=
  {s : ℝ | ∃ Q : Finset ℕ, TailAdmissible m Q ∧ reciprocalSum Q = s}

/-- Alias for `reciprocalSums1190`, matching the roadmap name. -/
noncomputable abbrev eps1190Set : ℕ → Set ℝ :=
  reciprocalSums1190

/-- Erdős's `ε_m`: the supremum of reciprocal sums over all finite
1190-admissible tail families. -/
noncomputable def epsilon1190 (m : ℕ) : ℝ :=
  sSup (reciprocalSums1190 m)

/-- Alias for `epsilon1190`, matching the roadmap name. -/
noncomputable abbrev eps1190 : ℕ → ℝ :=
  epsilon1190

/-- PDF Corollary 1.2 in epsilon form:
`ε_m = exp(-(1+o(1)) sqrt(log m log log m))`. -/
def HasErdos1190Asymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    Lscale (-(1 + ε)) m ≤ epsilon1190 m ∧
    epsilon1190 m ≤ Lscale (-(1 - ε)) m

/-- Public statement name for Erdős Problem 1190. -/
def Erdos1190Statement : Prop :=
  HasErdos1190Asymptotic

/-- **Erdős Problem 1190 — main theorem.** -/
theorem erdos1190_main : HasErdos1190Asymptotic := by
  sorry

end Erdos202

