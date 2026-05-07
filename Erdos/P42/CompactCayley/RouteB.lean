/-
Erdős Problem 42 — Route B final assembly.

This is the only compact-Cayley downstream file that imports the
`compact_cayley_clique` trust-boundary axiom. The finite allowed-difference
Fourier estimates and greedy Sidon extraction stay in `Application.lean` so
Route A can reuse them without importing this axiom.
-/

import Erdos.P42.CompactCayley.Axiom
import Erdos.P42.CompactCayley.Application

namespace Erdos42.CompactCayley

open Finset Erdos42

/-! ## Final assembly: Theorem 1.1 from `compact_cayley_clique` -/

/-- **Theorem 1.1, Route B.** For every `M ≥ 1`, there is `N₀` such that for
all `N ≥ N₀` and every non-empty Sidon `A ⊆ [1, N] ⊂ ℤ`, there is a Sidon
`B ⊆ [1, N]` with `|B| = M` and no nonzero common difference. Proved
conditional on `compact_cayley_clique`. -/
theorem theorem_1_1_from_compact_cayley
    (M : ℕ) (_hM : 1 ≤ M) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) → IsSidonInt A → A.Nonempty →
        ∃ B : Finset ℤ,
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ (N : ℤ)) ∧
          IsSidonInt B ∧ B.card = M ∧
          AvoidsNonzeroDiff A B := by
  classical
  let R := greedySidonThreshold M
  have hRpos : 0 < R := by
    dsimp [R, greedySidonThreshold]
    omega
  have hCliqueSize : 2 ≤ 8 * R := by omega
  obtain ⟨ε, hεpos, p₀, hcompact⟩ :=
    compact_cayley_clique (8 * R) (1 / 2 : ℝ) hCliqueSize (by norm_num)
  obtain ⟨Nε, hNε⟩ := sidon_card_minus_one_div_prime_eventually_small ε hεpos
  refine ⟨max (p₀ + 1) Nε, ?_⟩
  intro N hN A hAint hSidon _hAnonempty
  have hNpos : 0 < N := by omega
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp₀lt : p₀ < p := by omega
  have hpN : N < p := by omega
  have hpupper : p < 8 * N := by
    have hple' : p ≤ 8 * N := by omega
    have hpne2 : p ≠ 2 := by omega
    have hpodd : Odd p := hpprime.odd_of_ne_two hpne2
    have hpne : p ≠ 8 * N := by
      intro hpeq
      have heven : Even p := by
        rw [hpeq, even_iff_two_dvd]
        exact ⟨4 * N, by ring⟩
      exact (Nat.not_even_iff_odd.mpr hpodd) heven
    omega
  let T : Finset (ZMod p) := allowedDiffSetMod p A
  have hT_sym : SymmetricFinset T := by
    simpa [T] using allowedDiffSetMod_symmetric p A
  have hT_zero : (0 : ZMod p) ∉ T := by
    simpa [T] using zero_notMem_allowedDiffSetMod p A
  have hT_density : (1 / 2 : ℝ) * p ≤ (T.card : ℝ) := by
    simpa [T] using allowedDiffSetMod_density (p := p) (N := N) hpgt A hAint hSidon
  have hsmall : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε :=
    hNε N p (by omega) hpgt A hAint hSidon
  have hT_fourier : FourierUpperIndicator T ε := by
    simpa [T] using
      allowedDiffs_fourier_upper (p := p) (N := N) hpgt A hAint hSidon ε hsmall
  obtain ⟨C, hCcard, hCclique⟩ :=
    hcompact p hp₀lt T hT_sym hT_zero hT_density hT_fourier
  obtain ⟨s, hs⟩ :=
    exists_large_intersection_cyclicInterval (p := p) (N := N) (R := R)
      hpN C (by simpa [R] using hCcard) hpupper
  let X : Finset ℤ := intervalLiftSet p N s C
  have hXcard : R ≤ X.card := by
    dsimp [X]
    rw [intervalLiftSet_card_eq hpN]
    exact hs
  obtain ⟨B, hBX, hBcard, hBsidon⟩ := exists_sidon_subset_of_card_ge M X hXcard
  refine ⟨B, ?_, hBsidon, hBcard, ?_⟩
  · intro b hb
    rcases mem_intervalLiftSet.mp (hBX hb) with ⟨i, hiN, _hiC, rfl⟩
    constructor <;> omega
  · intro d hdA hdB
    rw [mem_diffFinset] at hdA hdB
    rcases hdA with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    rcases hdB with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
    by_cases hzero : a₁ - a₂ = 0
    · exact hzero
    · exfalso
      rcases mem_intervalLiftSet.mp (hBX hb₁) with ⟨i₁, hi₁N, hi₁C, hb₁eq⟩
      rcases mem_intervalLiftSet.mp (hBX hb₂) with ⟨i₂, hi₂N, hi₂C, hb₂eq⟩
      have hbne : b₁ ≠ b₂ := by
        intro hb
        apply hzero
        rw [hb] at hbDiff
        linarith
      have hine : i₁ ≠ i₂ := by
        intro hi
        apply hbne
        rw [hb₁eq, hb₂eq, hi]
      let y₁ : ZMod p := s + (i₁ : ZMod p)
      let y₂ : ZMod p := s + (i₂ : ZMod p)
      have hyne : y₁ ≠ y₂ := by
        intro hy
        apply hine
        apply nat_eq_of_zmod_eq_of_lt
          (Nat.lt_trans hi₁N hpN) (Nat.lt_trans hi₂N hpN)
        apply add_left_cancel (a := s)
        simpa [y₁, y₂] using hy
      have hallowed : y₁ - y₂ ∈ T := hCclique y₁ hi₁C y₂ hi₂C hyne
      have hyDiff : y₁ - y₂ = ((a₁ - a₂ : ℤ) : ZMod p) := by
        calc
          y₁ - y₂ = (i₁ : ZMod p) - (i₂ : ZMod p) := by
            simp [y₁, y₂]
          _ = ((b₁ - b₂ : ℤ) : ZMod p) := by
            rw [hb₁eq, hb₂eq]
            norm_num
          _ = ((a₁ - a₂ : ℤ) : ZMod p) := by
            rw [hbDiff]
      have hcast : ((a₁ - a₂ : ℤ) : ZMod p) ∈ allowedDiffSetMod p A := by
        simpa [T, hyDiff] using hallowed
      rw [allowedDiffSetMod, Finset.mem_filter] at hcast
      exact hcast.2.2 a₁ ha₁ a₂ ha₂ rfl

end Erdos42.CompactCayley
