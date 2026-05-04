/-
SafeVerify target for Erdős Problem 42.

Public-theorem signatures with `sorry` bodies. The actual proofs live in
`Proof.lean` (currently scaffolded; this Spec is the external contract).

Trust boundary: Mathlib core + two axioms:
  - Erdos42.complexity_one_counting_lemma (Green-Tao 2008)
  - Erdos42.compact_U2_regularity_subsequential_limit (classical compactness)
-/

import Mathlib

namespace Erdos42

open Filter Set

def IsSidon (A : Set ℕ) : Prop := sorry
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop := sorry

theorem theorem_1_1 :
    ∀ M : ℕ, 1 ≤ M → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 N → IsSidon A → A.Nonempty →
        ∃ B : Set ℕ, B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
          ((A - A) ∩ (B - B) : Set ℕ) = {0} := sorry

theorem erdos_42 :
    True ↔ ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
      ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B) : Set ℕ) = {0} := sorry

end Erdos42
