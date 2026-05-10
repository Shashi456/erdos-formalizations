/-
Erdős Problem 42 — Fourier-positive counterexample sequence.

This is the Route A contradiction skeleton for opening
`finite_fourier_avoidance_count`.  It is independent of Route B: if the
explicit-prime count theorem fails, then one can choose primes `p_n → ∞`,
forbidden sets `F_n`, dense vertex sets `U_n`, Fourier lower bias
`ε_n → 0`, and a vanishing count threshold `c_n → 0` such that the avoiding
tuple count is always below `c_n p_n^m`.
-/

import Erdos.P42.FourierPositive.FiniteAvoidance

namespace Erdos42.FourierPositive

open Filter Erdos42
open scoped Topology Classical

/-- Explicit-prime version of the Route A count theorem statement.  This
avoids typeclass binders in the counterexample extraction while preserving the
same mathematical content as `finite_fourier_avoidance_count`. -/
def FiniteFourierAvoidanceCountStatementExplicit (m : ℕ) (α ρ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
  ∃ c : ℝ, 0 < c ∧
  ∃ p₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      (letI : NeZero p := ⟨hp.ne_zero⟩; FourierLowerIndicator F ε) →
      (letI : NeZero p := ⟨hp.ne_zero⟩;
        c * (p : ℝ) ^ m ≤
          (((Finset.univ : Finset (Fin m → ZMod p)).filter
            (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ))

/-- The original typeclass-shaped Route A count theorem statement implies the
explicit-prime statement used for contradiction extraction. -/
theorem explicit_of_finite_fourier_avoidance_count_statement
    {m : ℕ} {α ρ : ℝ}
    (h : ∃ ε : ℝ, 0 < ε ∧
      ∃ c : ℝ, 0 < c ∧
      ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
      ∀ F U : Finset (ZMod p),
        SymmetricFinset F →
        (0 : ZMod p) ∈ F →
        (F.card : ℝ) ≤ (1 - ρ) * p →
        α * p ≤ (U.card : ℝ) →
        FourierLowerIndicator F ε →
        c * (p : ℝ) ^ m ≤
          (((Finset.univ : Finset (Fin m → ZMod p)).filter
            (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ)) :
    FiniteFourierAvoidanceCountStatementExplicit m α ρ := by
  rcases h with ⟨ε, hε, c, hc, p₀, hp₀⟩
  refine ⟨ε, hε, c, hc, p₀, ?_⟩
  intro p hp hpge F U hsym hzero hFdense hUdense hFourier
  haveI : Fact p.Prime := ⟨hp⟩
  exact hp₀ p hpge F U hsym hzero hFdense hUdense (by simpa using hFourier)

/-- Conversely, the explicit-prime statement implies the original
typeclass-shaped Route A count theorem statement. -/
theorem finite_fourier_avoidance_count_statement_from_explicit
    {m : ℕ} {α ρ : ℝ}
    (h : FiniteFourierAvoidanceCountStatementExplicit m α ρ) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      c * (p : ℝ) ^ m ≤
        (((Finset.univ : Finset (Fin m → ZMod p)).filter
          (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ) := by
  rcases h with ⟨ε, hε, c, hc, p₀, hp₀⟩
  refine ⟨ε, hε, c, hc, p₀, ?_⟩
  intro p hpFact hpge F U hsym hzero hFdense hUdense hFourier
  have hp : p.Prime := Fact.out
  exact hp₀ p hp hpge F U hsym hzero hFdense hUdense (by simpa using hFourier)

/-- A Route A counterexample sequence for a failed finite Fourier avoidance
count theorem. -/
structure FourierAvoidanceCounterSeq (m : ℕ) (α ρ : ℝ) where
  p : ℕ → ℕ
  prime : ∀ n, (p n).Prime
  p_ge : ∀ n, n ≤ p n
  F : ∀ n, Finset (ZMod (p n))
  U : ∀ n, Finset (ZMod (p n))
  F_sym : ∀ n, SymmetricFinset (F n)
  F_zero : ∀ n, (0 : ZMod (p n)) ∈ F n
  F_density : ∀ n, ((F n).card : ℝ) ≤ (1 - ρ) * (p n : ℝ)
  U_density : ∀ n, α * (p n : ℝ) ≤ ((U n).card : ℝ)
  eps : ℕ → ℝ
  c : ℕ → ℝ
  eps_pos : ∀ n, 0 < eps n
  c_pos : ∀ n, 0 < c n
  eps_tendsto_zero : Tendsto eps atTop (𝓝 0)
  c_tendsto_zero : Tendsto c atTop (𝓝 0)
  F_fourier_lower : ∀ n,
    letI : NeZero (p n) := ⟨(prime n).ne_zero⟩
    FourierLowerIndicator (F n) (eps n)
  count_small : ∀ n,
    letI : NeZero (p n) := ⟨(prime n).ne_zero⟩
    (((Finset.univ : Finset (Fin m → ZMod (p n))).filter
      (fun x => AvoidsForbiddenDiffs (F n) (U n) x)).card : ℝ) <
      c n * (p n : ℝ) ^ m

lemma FourierAvoidanceCounterSeq.tendsto_p_atTop {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ) :
    Tendsto S.p atTop atTop :=
  tendsto_atTop_mono S.p_ge tendsto_id

lemma FourierAvoidanceCounterSeq.tendsto_p_natCast_atTop {m : ℕ} {α ρ : ℝ}
    (S : FourierAvoidanceCounterSeq m α ρ) :
    Tendsto (fun n => (S.p n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp S.tendsto_p_atTop

/-- Failure of the explicit Route A count statement produces the standard
contradiction sequence with `ε_n = c_n = 1 / (n + 1)` and `p_n ≥ n`. -/
theorem exists_fourierAvoidanceCounterSeq_of_not_finiteFourierAvoidanceCountStatementExplicit
    {m : ℕ} {α ρ : ℝ}
    (hfail : ¬ FiniteFourierAvoidanceCountStatementExplicit m α ρ) :
    ∃ _S : FourierAvoidanceCounterSeq m α ρ, True := by
  classical
  have hbad : ∀ n : ℕ,
      ∃ p : ℕ, ∃ hp : p.Prime, n ≤ p ∧
      ∃ F U : Finset (ZMod p),
        SymmetricFinset F ∧
        (0 : ZMod p) ∈ F ∧
        (F.card : ℝ) ≤ (1 - ρ) * (p : ℝ) ∧
        α * (p : ℝ) ≤ (U.card : ℝ) ∧
        (letI : NeZero p := ⟨hp.ne_zero⟩;
          FourierLowerIndicator F (((n + 1 : ℕ) : ℝ)⁻¹)) ∧
        (letI : NeZero p := ⟨hp.ne_zero⟩;
          (((Finset.univ : Finset (Fin m → ZMod p)).filter
            (fun x => AvoidsForbiddenDiffs F U x)).card : ℝ) <
            (((n + 1 : ℕ) : ℝ)⁻¹) * (p : ℝ) ^ m) := by
    intro n
    by_contra hnone
    apply hfail
    refine ⟨(((n + 1 : ℕ) : ℝ)⁻¹), by positivity,
      (((n + 1 : ℕ) : ℝ)⁻¹), by positivity, n, ?_⟩
    intro p hp hpge F U hsym hzero hFdense hUdense hFourier
    by_contra hnot
    apply hnone
    exact ⟨p, hp, hpge, F, U, hsym, hzero, hFdense, hUdense, hFourier, not_le.mp hnot⟩
  choose p hp hpge F U hsym hzero hFdense hUdense hFourier hsmall using hbad
  refine ⟨{
    p := p
    prime := hp
    p_ge := hpge
    F := F
    U := U
    F_sym := hsym
    F_zero := hzero
    F_density := hFdense
    U_density := hUdense
    eps := fun n => (((n + 1 : ℕ) : ℝ)⁻¹)
    c := fun n => (((n + 1 : ℕ) : ℝ)⁻¹)
    eps_pos := by
      intro n
      positivity
    c_pos := by
      intro n
      positivity
    eps_tendsto_zero := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    c_tendsto_zero := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    F_fourier_lower := by
      intro n
      simpa using hFourier n
    count_small := by
      intro n
      simpa using hsmall n
  }, trivial⟩

end Erdos42.FourierPositive
