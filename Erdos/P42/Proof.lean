/-
Erdős Problem 42 — Sidon difference avoidance.

Following Harjas / GPT-5.5 Pro (April 27 2026), with subsequent ideas from Bloom,
Sawin, Tao, and natso26's clean exposition (April 30 2026, `proof_ulam_note.pdf`).

The main result is `Erdos42.theorem_1_1`:

  For every M ≥ 1 there is N₀(M) such that for all N ≥ N₀(M) and every non-empty
  Sidon set A ⊆ {1, …, N}, there is a Sidon set B ⊆ {1, …, N} with |B| = M and
  (A − A) ∩ (B − B) = {0}.

The proof reduces (Layer 3) to a finite Fourier compactness lemma (Layer 2,
`finite_avoidance_lemma`), which in turn passes through Green-Tao U² regularity
+ complexity-1 counting to the continuous-version key lemma (Layer 1,
`tao_continuous_avoidance`) on a connected compact abelian limit group.

Trust boundary beyond Mathlib core (`propext`, `Quot.sound`, `Classical.choice`):
  Erdos42.complexity_one_counting_lemma — Green-Tao 2008.
  Erdos42.compact_U2_regularity_subsequential_limit — classical compactness.

⚠ This file is currently a scaffold. Layer 1 (provable in Mathlib), Layer 2
(uses the two axioms), and Layer 3 (the discrete-to-continuous reduction) are all
placeholders pending implementation.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos42

open Filter Set Finset
open scoped Pointwise

universe u

/-! ## Sidon set predicate (FC-compatible)

We use Mathlib's `Set.IsSidon` if available, with a fallback definition matching
FC's [`FormalConjectures/ErdosProblems/42.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/42.lean):
a set `A ⊆ ℕ` is Sidon iff every non-zero difference is uniquely represented.
-/

/-- `A` is Sidon iff `a₁ + a₂ = a₃ + a₄ → {a₁, a₂} = {a₃, a₄}` for `aᵢ ∈ A`. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-! ## §2. Trust-boundary axioms

Two black-box axioms supporting the discrete-to-continuous reduction.
-/

/-- **Complexity-1 counting lemma (Green-Tao 2008).** For complexity-1 systems of
linear forms (in particular, the family `{x_i − x_j : 1 ≤ i < j ≤ M}`), the count of
configurations on a function `g : 𝔽_p → [0, 1]` is approximately the random expectation
up to lower-order error controlled by the `U²`-norm. Classical, unconditional;
Mathlib has Fourier infrastructure but not yet this named lemma.

Concretely: given `M ≥ 2`, primes `p_n → ∞`, functions `g_n : ZMod p_n → ℝ` with
`0 ≤ g_n ≤ 1`, and a uniform `U²`-norm bound, the average of `∏_{i < j} g_n(x_i − x_j)`
over `x_1, …, x_M ∈ ZMod p_n` matches `(∫ g_n)^{M(M−1)/2}` up to vanishing error. -/
axiom complexity_one_counting_lemma : True

/-- **Compact `U²` regularity / subsequential limit (classical).** Given a sequence of
functions `f_n : ZMod p_n → [0, 1]` with `p_n → ∞`, after passing to a subsequence,
the `f_n` converge in the `U²` (Fourier) sense to a measurable model function on
some connected compact abelian limit group `G`. The non-negativity of Fourier
coefficients passes to the limit, as does the integral. Classical compactness
packaging of `U²` arithmetic regularity (Green-Tao). -/
axiom compact_U2_regularity_subsequential_limit : True

/-! ## §3. Layer 1 — Tao's continuous-analogue key lemma

`tao_continuous_avoidance`. Provable inside Mathlib (Fourier on compact abelian
groups + closed-subgroup measure-zero from connectedness) — currently `sorry`.
-/

/-- **Tao's continuous-analogue key lemma (May 2026 forum comment).** Let `G` be a
connected compact abelian group with Haar probability measure `μ`, and let
`f : G → [0, 1]` be a measurable, positive-definite function (Fourier transform
non-negative) which is not almost-everywhere `1`. Then for almost every
`(x₁, …, x_M) ∈ G^M`, `f(x_i − x_j) < 1` for all `1 ≤ i < j ≤ M`.

Proof sketch (PDF §2 in `proof_ulam_note.pdf`): `f(x) = 1` exactly when `x` is
orthogonal to `supp(\hat{f})`, so the level set `{x : f(x) = 1}` is a closed
subgroup of `G`, proper (since `f ≢ 1`) and not open (since `G` is connected),
hence has measure zero. Apply Fubini. -/
theorem tao_continuous_avoidance : True := trivial

/-! ## §4. Layer 2 — One-sided finite avoidance lemma

`finite_avoidance_lemma`. Compactness packaging of the `U²` regularity + the
continuous lemma. Uses both axioms.
-/

/-- **One-sided finite avoidance lemma (Lemma 2.1 of `proof_ulam_note.pdf`).**
For every `M ≥ 1` and `0 < α₀ ≤ α₁ < 1/2`, there is `p_0` such that the following
holds for every prime `p ≥ p_0`. If `F ⊆ ZMod p` is symmetric with `0 ∈ F`,
`|F| ≤ p / 2`, and `\hat{1_F}(γ) ≥ -o(p)` uniformly, and if `I ⊆ ZMod p` is an
interval `{1, …, L}` with `α₀ p ≤ L ≤ α₁ p`, then with positive probability a
uniform random `M`-tuple `(x_1, …, x_M) ∈ I^M` has `x_i − x_j ∉ F` for all `i < j`. -/
theorem finite_avoidance_lemma (M : ℕ) (_hM : 1 ≤ M) :
    True := trivial

/-! ## §5. Layer 3 — Theorem 1.1 (the Erdős statement)

`theorem_1_1`. Combines Layer 2 with the prime-cyclic-group reduction and the
Sidon Fourier estimate.
-/

/-- **Theorem 1.1 (PDF, the Erdős statement).** For every integer `M ≥ 1`, there is
`N₀ = N₀(M)` such that whenever `N ≥ N₀` and `A ⊆ {1, …, N}` is a non-empty Sidon
set, there is a Sidon set `B ⊆ {1, …, N}` with `|B| = M` and
`(A − A) ∩ (B − B) = {0}`. -/
theorem theorem_1_1 :
    ∀ M : ℕ, 1 ≤ M → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 N → IsSidon A → A.Nonempty →
        ∃ B : Set ℕ, B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
          ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  sorry

/-! ## §6. FC upstream form (`erdos_42`)

The literal FC statement uses `IsMaximalSidonSetIn` and the `∀ᶠ N in atTop` /
`∃ᵉ` shape. We provide the corresponding wrapper.
-/

/-- An auxiliary "maximal Sidon" predicate matching the FC skeleton's
`IsMaximalSidonSetIn`. -/
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Set.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)

/-- **`formal-conjectures` upstream form for #42** under `answer := True`. -/
theorem erdos_42 :
    True ↔ ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
      ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  sorry

/-! ## Audit -/

-- #print axioms theorem_1_1   -- (Mathlib core + 2 axioms)
-- #print axioms erdos_42      -- (Mathlib core + 2 axioms)

end Erdos42
