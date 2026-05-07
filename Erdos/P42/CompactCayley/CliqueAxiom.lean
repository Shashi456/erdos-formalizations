/-
Erdős Problem 42 — Route B trust boundary: compact Cayley clique theorem.

Theorem 2.1 of `erdos42_compact_sidon_clean.pdf` (Google Drive link in
`forum.md`). A dense symmetric Cayley graph on `ZMod p`, with `0 ∉ T`
and small nontrivial Fourier coefficients (upper bound), contains a clique of
any prescribed size for all sufficiently large primes.

Mathematically: classical, unconditional. The compact-Cayley PDF proves it via
Fourier extraction (Lemma 2.2), equidistribution of finite lifts (2.3), basic
limit properties (2.4), spectral cut-norm control (2.5), counting convergence
(2.6), and clique forcing on connected compact groups (2.7).

This file is the trust boundary for Route B: replace this `axiom` with a
`theorem` once those six lemmas are formalized.
-/

import Erdos.P42.Common
import Erdos.P42.FiniteFourier

namespace Erdos42

/-- A `Finset C` is a clique in the Cayley graph on `ZMod p` with allowed
difference set `T`: every pair of distinct vertices in `C` has its difference
in `T`. -/
def CliqueInCayley {p : ℕ} (T C : Finset (ZMod p)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x - y ∈ T

namespace CompactCayley

/-- **Compact Cayley clique theorem (compact PDF Theorem 2.1).** Trust
boundary for Route B. For every clique size `ℓ ≥ 2` and every density `η > 0`,
there exists `ε > 0` such that for all sufficiently large primes `p`, every
symmetric `T ⊆ ZMod p` with `0 ∉ T`, density `≥ η`, and Fourier upper bound
`≤ ε` (at every nontrivial character) contains an `ℓ`-clique in its Cayley
graph. -/
axiom compact_cayley_clique
    (ℓ : ℕ) (η : ℝ) (_hℓ : 2 ≤ ℓ) (_hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      FourierUpperIndicator T ε →
      ∃ C : Finset (ZMod p),
        C.card = ℓ ∧ CliqueInCayley T C

end CompactCayley

end Erdos42
