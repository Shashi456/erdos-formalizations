/-
SafeVerify target for Erdős Problem 42 — compact-Cayley route (Route B).

Public-theorem signature with `sorry` body. The actual proof lives in
`Erdos/P42/CompactCayley/Main.lean`; this Spec is the external contract for
Route B.

Route B works over `Finset ℤ` (the natural setting for the analytic proof).
Bridging back to the FC-style `Set ℕ` statement is done in
`Erdos/P42/FC/Local.lean` for Route A; Route B exposes only the working-form
theorem here, which the bridge can apply analogously.

Trust boundary of Route B: Mathlib core +
  - Erdos42.CompactCayley.compact_cayley_clique
-/

import Mathlib

namespace Erdos42

/-- Working-form Sidon predicate over `Finset ℤ` (mirrors `Erdos.P42.Sidon`). -/
def IsSidonInt (A : Finset ℤ) : Prop := sorry

/-- Working-form "no nonzero common difference" predicate. Generic in the
underlying additive type, matching the implementation in `Erdos.P42.Common`. -/
def AvoidsNonzeroDiff {α : Type*} [DecidableEq α] [Zero α] [Sub α]
    (A B : Finset α) : Prop := sorry

namespace CompactCayley

theorem theorem_1_1_from_compact_cayley
    (M : ℕ) (_hM : 1 ≤ M) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) → IsSidonInt A → A.Nonempty →
        ∃ B : Finset ℤ,
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ (N : ℤ)) ∧
          IsSidonInt B ∧ B.card = M ∧
          AvoidsNonzeroDiff A B := sorry

end CompactCayley

end Erdos42
