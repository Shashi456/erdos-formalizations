/-
Erdős Problem 43 — `sidonNumber` and shared definitions.
-/

import Mathlib
import Erdos.P42.Sidon
import Erdos.P42.FCWrapper

namespace Erdos43

open Finset

/-- The Sidon number `f(N)`: maximum cardinality of a Sidon subset of `[1, N]`.

Implemented as the supremum (over all `Finset ℕ` Sidon subsets of `[1, N]`) of
`A.card`. Uses the FC-aligned `Erdos42.IsSidon` predicate over `Set ℕ`,
restricted to `Finset` for boundedness. -/
noncomputable def sidonNumber (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, ↑A ⊆ Set.Icc 1 N ∧ Erdos42.IsSidon (A : Set ℕ) ∧ A.card = k}

end Erdos43
