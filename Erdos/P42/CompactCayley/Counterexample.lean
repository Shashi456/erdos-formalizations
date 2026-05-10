/-
Erdős Problem 42 — compact-Cayley counterexample sequence.

This is the Route B contradiction skeleton for opening
`compact_cayley_clique`.  It is independent of Route A: if the explicit-prime
compact Cayley statement fails, then one can choose primes `p_n → ∞` and
allowed sets `T_n ⊆ ZMod p_n` with density `η`, zero-free symmetry, Fourier
upper bias tending to zero, and no `K_ℓ` clique.
-/

import Erdos.P42.Shared.FiniteFourier

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

/-- Explicit-prime version of the compact Cayley theorem statement.  This
avoids typeclass binders in the counterexample extraction; it is equivalent in
content to the Route B trust-boundary axiom's statement. -/
def CompactCayleyCliqueStatementExplicit (ℓ : ℕ) (η : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
  ∃ p₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      (letI : NeZero p := ⟨hp.ne_zero⟩; FourierUpperIndicator T ε) →
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C

/-- The explicit-prime compact-Cayley statement implies the original
typeclass-shaped statement used by the Route B trust-boundary axiom. -/
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
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rcases h with ⟨ε, hε, p₀, hp₀⟩
  refine ⟨ε, hε, p₀, ?_⟩
  intro p hpFact hpgt T hsym hzero hdens hfourier
  have hp : p.Prime := Fact.out
  exact hp₀ p hp hpgt T hsym hzero hdens (by simpa using hfourier)

/-- Conversely, the original typeclass-shaped compact-Cayley statement implies
the explicit-prime formulation used for contradiction extraction. -/
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
    CompactCayleyCliqueStatementExplicit ℓ η := by
  rcases h with ⟨ε, hε, p₀, hp₀⟩
  refine ⟨ε, hε, p₀, ?_⟩
  intro p hp hpgt T hsym hzero hdens hfourier
  haveI : Fact p.Prime := ⟨hp⟩
  exact hp₀ p hpgt T hsym hzero hdens (by simpa using hfourier)

/-- A sequence of finite Cayley-graph counterexamples with Fourier upper bias
tending to zero. This is the exact starting point for Lemmas 2.2–2.7 in the
compact-Cayley PDF. -/
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

lemma CayleyCounterSeq.tendsto_p_atTop {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η) :
    Tendsto S.p atTop atTop :=
  tendsto_atTop_mono (fun n => le_of_lt (S.p_gt n)) tendsto_id

lemma CayleyCounterSeq.tendsto_p_natCast_atTop {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η) :
    Tendsto (fun n => (S.p n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp S.tendsto_p_atTop

/-- Failure of the explicit compact-Cayley statement produces the standard
contradiction sequence with `ε_n = 1 / (n + 1)` and `p_n > n`. -/
theorem exists_cayleyCounterSeq_of_not_compactCayleyCliqueStatementExplicit
    {ℓ : ℕ} {η : ℝ}
    (hfail : ¬ CompactCayleyCliqueStatementExplicit ℓ η) :
    ∃ _S : CayleyCounterSeq ℓ η, True := by
  classical
  have hbad : ∀ n : ℕ,
      ∃ p : ℕ, ∃ hp : p.Prime, n < p ∧
      ∃ T : Finset (ZMod p),
        SymmetricFinset T ∧
        (0 : ZMod p) ∉ T ∧
        η * (p : ℝ) ≤ (T.card : ℝ) ∧
        (letI : NeZero p := ⟨hp.ne_zero⟩;
          FourierUpperIndicator T (((n + 1 : ℕ) : ℝ)⁻¹)) ∧
        ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
    intro n
    by_contra hnone
    apply hfail
    refine ⟨(((n + 1 : ℕ) : ℝ)⁻¹), by positivity, n, ?_⟩
    intro p hp hpgt T hsym hzero hdens hfourier
    by_contra hNo
    apply hnone
    exact ⟨p, hp, hpgt, T, hsym, hzero, hdens, hfourier, hNo⟩
  choose p hp hpgt T hsym hzero hdens hfourier hnoclique using hbad
  refine ⟨{
    p := p
    prime := hp
    p_gt := hpgt
    T := T
    T_sym := hsym
    T_zero := hzero
    T_density := hdens
    eps := fun n => (((n + 1 : ℕ) : ℝ)⁻¹)
    eps_pos := by
      intro n
      positivity
    eps_tendsto_zero := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    T_fourier_upper := by
      intro n
      simpa using hfourier n
    no_clique := hnoclique
  }, trivial⟩

end Erdos42.CompactCayley
