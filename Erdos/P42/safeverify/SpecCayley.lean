/-
SafeVerify target for Erdos Problem 42 -- compact-Cayley route (Route B).

This is the external contract for the flattened Route B proof in
`Erdos/P42/CompactCayley/Proof.lean`.  It records the public theorem plus the
major internal proof milestones that should replay against the submitted
`.olean`.

Expected trust boundary for this route: Mathlib core only
(`propext`, `Classical.choice`, `Quot.sound`).  The former local axiom
`Erdos42.CompactCayley.compact_cayley_clique` is now one of the checked
theorems, not an allowed axiom.
-/

import Mathlib

namespace Erdos42

open Filter
open scoped Topology

/-! ## Shared vocabulary -/

/-- Difference set of two finite sets. -/
def DiffFinset {α : Type*} [DecidableEq α] [Sub α] (A B : Finset α) :
    Finset α := sorry

/-- A finite set is symmetric under negation. -/
def SymmetricFinset {α : Type*} [Neg α] (S : Finset α) : Prop := sorry

/-- Clique predicate in the Cayley graph with allowed difference set `T`. -/
def CliqueInCayley {p : ℕ} (T C : Finset (ZMod p)) : Prop := sorry

/-- Working-form Sidon predicate over `Finset ℤ`. -/
def IsSidonInt (A : Finset ℤ) : Prop := sorry

/-- Working-form "no nonzero common difference" predicate. -/
def AvoidsNonzeroDiff {α : Type*} [DecidableEq α] [Zero α] [Sub α]
    (A B : Finset α) : Prop := sorry

/-- Complex-valued indicator of a finite set in `ZMod p`. -/
noncomputable def indicatorC {p : ℕ} (T : Finset (ZMod p)) :
    ZMod p → ℂ := sorry

/-- Normalized DFT coefficient of an arbitrary complex-valued function. -/
noncomputable def normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) : ℂ := sorry

/-- Normalized DFT coefficient of an indicator. -/
noncomputable def normalizedDftCoeff {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) : ℂ := sorry

/-- Route B Fourier upper bound at every nontrivial character. -/
def FourierUpperIndicator {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (ε : ℝ) : Prop := sorry

namespace CompactCayley

/-! ## Compact-Cayley theorem shape and countersequence reduction -/

/-- Explicit-prime version of the compact-Cayley clique theorem. -/
def CompactCayleyCliqueStatementExplicit (ℓ : ℕ) (η : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
  ∃ p₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      (letI : NeZero p := ⟨hp.ne_zero⟩; FourierUpperIndicator T ε) →
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C

theorem compactCayleyCliqueStatement_from_explicit
    {ℓ : ℕ} {η : ℝ}
    (h : CompactCayleyCliqueStatementExplicit ℓ η) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      FourierUpperIndicator T ε →
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := sorry

theorem explicit_of_compactCayleyCliqueStatement
    {ℓ : ℕ} {η : ℝ}
    (h : ∃ ε : ℝ, 0 < ε ∧
      ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
      ∀ T : Finset (ZMod p),
        SymmetricFinset T →
        (0 : ZMod p) ∉ T →
        η * (p : ℝ) ≤ (T.card : ℝ) →
        FourierUpperIndicator T ε →
        ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    CompactCayleyCliqueStatementExplicit ℓ η := sorry

/-- A sequence of finite Cayley-graph counterexamples with bias tending to zero. -/
structure CayleyCounterSeq (ℓ : ℕ) (η : ℝ) where
  p : ℕ → ℕ
  prime : ∀ n, (p n).Prime
  p_gt : ∀ n, n < p n
  T : ∀ n, Finset (ZMod (p n))
  T_sym : ∀ n, SymmetricFinset (T n)
  T_zero : ∀ n, (0 : ZMod (p n)) ∉ T n
  T_density : ∀ n, η * (p n : ℝ) ≤ ((T n).card : ℝ)
  eps : ℕ → ℝ
  eps_pos : ∀ n, 0 < eps n
  eps_tendsto_zero : Tendsto eps atTop (𝓝 0)
  T_fourier_upper : ∀ n,
    letI : NeZero (p n) := ⟨(prime n).ne_zero⟩
    FourierUpperIndicator (T n) (eps n)
  no_clique : ∀ n,
    ¬ ∃ C : Finset (ZMod (p n)), C.card = ℓ ∧ CliqueInCayley (T n) C

theorem exists_cayleyCounterSeq_of_not_compactCayleyCliqueStatementExplicit
    {ℓ : ℕ} {η : ℝ}
    (hfail : ¬ CompactCayleyCliqueStatementExplicit ℓ η) :
    ∃ _S : CayleyCounterSeq ℓ η, True := sorry

/-! ## Finite spectral/counting endpoint -/

/-- Spectral coefficient bound used by compact-Cayley Lemma 2.5. -/
def SpectralBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) :
    Prop := sorry

/-- Cayley cut-norm bound used by compact-Cayley Lemma 2.5. -/
def CayleyCutBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) :
    Prop := sorry

theorem cayleyCutBound_of_spectralBound
    {p : ℕ} [NeZero p] (a : ZMod p → ℂ) {M : ℝ}
    (hMnonneg : 0 ≤ M) (hM : SpectralBound a M) :
    CayleyCutBound a M := sorry

/-- Finite `K_ell` Cayley density. -/
noncomputable def finiteCliqueKernelDensity {p ℓ : ℕ} [NeZero p]
    (g : ZMod p → ℂ) : ℂ := sorry

theorem exists_clique_of_spectral_density_transfer_sq
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => indicatorC T z - g z) M)
    (hdensity : ((ℓ * ℓ : ℕ) : ℝ) * M <
      (finiteCliqueKernelDensity (ℓ := ℓ) g).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := sorry

/-! ## Final contradiction -/

-- The extraction package is intentionally not exposed here: its structure type
-- contains the full stable-subsequence implementation data.  The major
-- externally checked milestone is the contradiction theorem below, which is
-- the point where extraction, smoothing, compact density, and finite transfer
-- are all consumed.

theorem CayleyCounterSeq.false
    {ℓ : ℕ} {η : ℝ} (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (S : CayleyCounterSeq ℓ η) :
    False := sorry

/-! ## Public Route B theorems -/

/-- Compact-Cayley clique theorem, formerly the Route B trust-boundary axiom. -/
theorem compact_cayley_clique
    (ℓ : ℕ) (η : ℝ) (_hℓ : 2 ≤ ℓ) (_hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      FourierUpperIndicator T ε →
      ∃ C : Finset (ZMod p),
        C.card = ℓ ∧ CliqueInCayley T C := sorry

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
