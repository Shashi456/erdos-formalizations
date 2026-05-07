/-
Erdős Problem 42 — formal-conjectures shape wrapper.

The repository does not currently vendor `formal-conjectures`, so this file
mirrors the upstream RHS locally and proves it equivalent to the existing
`FCWrapper.lean` statement. If the FC package is later added as a Lake
dependency, this is the file to replace by an import of
`FormalConjectures.ErdosProblems.42` plus a proof of its exact theorem.
-/

import Erdos.P42.FCWrapper

namespace Erdos42

open Filter Set
open scoped Pointwise

namespace FormalConjecturesShape

universe u

/-! ## Upstream-shaped local aliases -/

/-- Local stand-in for FC's explicit-exists binder `∃ᵉ`.
Semantically this is ordinary existence; FC uses the notation for linting. -/
def ExplicitExists {α : Sort u} (P : α → Prop) : Prop :=
  ∃ x, P x

theorem explicitExists_iff_exists {α : Sort u} {P : α → Prop} :
    ExplicitExists P ↔ ∃ x, P x := by
  rfl

/-- FC-shaped Sidon predicate. This is definitionally equal to `Erdos42.IsSidon`. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

theorem isSidon_iff_local (A : Set ℕ) :
    IsSidon A ↔ Erdos42.IsSidon A := by
  rfl

/-- FC-shaped maximal Sidon predicate. This is definitionally equal to the local
predicate in `FCWrapper.lean`. -/
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Set.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)

theorem isMaximalSidonSetIn_iff_local (A : Set ℕ) (N : ℕ) :
    IsMaximalSidonSetIn A N ↔ Erdos42.IsMaximalSidonSetIn A N := by
  rfl

/-- The upstream FC RHS, with `ExplicitExists` standing in for FC's `∃ᵉ`. -/
def erdos42RHS : Prop :=
  ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
    ExplicitExists fun B : Set ℕ =>
      B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B)) = {0}

/-- The already-proved local RHS from `FCWrapper.lean`. -/
def localRHS : Prop :=
  ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : Erdos42.IsMaximalSidonSetIn A N),
    ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ Erdos42.IsSidon B ∧ B.ncard = M ∧
      ((A - A) ∩ (B - B) : Set ℕ) = {0}

/-- The FC-shaped RHS and our existing local RHS are definitionally equivalent.

This is the key handoff theorem for later replacing the local aliases by the
real `formal-conjectures` imports. -/
theorem erdos42RHS_iff_localRHS :
    erdos42RHS ↔ localRHS := by
  unfold erdos42RHS localRHS ExplicitExists IsMaximalSidonSetIn IsSidon
    Erdos42.IsMaximalSidonSetIn Erdos42.IsSidon
  rfl

/-- **Formal-conjectures shape for #42** under `answer := True`.

This matches the upstream theorem after replacing FC's `answer(sorry)` by
`True` and interpreting FC's `∃ᵉ` as `ExplicitExists`. -/
theorem erdos_42 :
    True ↔ erdos42RHS :=
  Iff.trans Erdos42.erdos_42 erdos42RHS_iff_localRHS.symm

/-- Equivalence between the local FC wrapper theorem and the upstream-shaped
wrapper theorem. -/
theorem erdos_42_iff_local_wrapper :
    (True ↔ erdos42RHS) ↔ (True ↔ localRHS) := by
  rw [erdos42RHS_iff_localRHS]

end FormalConjecturesShape

end Erdos42
