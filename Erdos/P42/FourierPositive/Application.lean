/-
Erdős Problem 42 — Route A application.

Derives Theorem 1.1 (Erdős statement, `Finset ℤ` form) from the single
trust-boundary axiom `finite_fourier_avoidance`. Pipeline (combined PDF /
Ulam note Section 3):

  1. Forbidden set: `F := (A − A) mod p` for `p` a prime in `(2N, 4N)`.
     Symmetric, `0 ∈ F`, `|F| ≤ 2N − 1 ≤ (1 − 1/2) p`.
  2. Sidon Fourier lower bound: `1̂_F(r) = |1̂_A(r)|² − (|A|−1)/p ≥ −(|A|−1)/p`,
     which is `≥ −ε` for `p` large enough (combined PDF §3).
  3. `U := [1, N] mod p` has density `≥ 1/4 · p` (since `p < 4N`).
  4. Apply `finite_fourier_avoidance` to get `≫ p^M` good ordered tuples whose
     pairwise differences avoid `F`.
  5. Bad-tuple bound: among ordered `M`-tuples in `[1, N]^M`, at most `O_M(N^{M-1})`
     are non-Sidon. Crude explicit bound `(M^4 + M^3 + 1) · N^{M-1}` suffices.
  6. For `N` large in `M`, good tuples outnumber bad ones; pick a good Sidon
     tuple. Its image is the desired `B`.
-/

import Erdos.P42.Basic
import Erdos.P42.Sidon
import Erdos.P42.FourierAPI
import Erdos.P42.FourierPositive.Axiom
import Erdos.P42.CompactCayley.Application

namespace Erdos42.FourierPositive

open Finset Erdos42
open scoped Classical

/-! ## Step 2 — Sidon Fourier lower bound -/

/-- The forbidden set: `F_A := (A − A) mod p` projected into `ZMod p`. -/
noncomputable def forbiddenDiffSetMod (p : ℕ) (A : Finset ℤ) : Finset (ZMod p) :=
  (DiffFinset A A).image (fun x : ℤ => (x : ZMod p))

/-- Forbidden set is symmetric. -/
lemma forbiddenDiffSetMod_symmetric (p : ℕ) (A : Finset ℤ) :
    SymmetricFinset (forbiddenDiffSetMod p A) := by
  classical
  intro x
  rw [forbiddenDiffSetMod, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨-d, ?_, by simp⟩
    exact (diffFinset_self_symmetric A d).mp hd
  · rintro ⟨d, hd, hdx⟩
    refine ⟨-d, ?_, ?_⟩
    · exact (diffFinset_self_symmetric A d).mp hd
    · simp [hdx]

/-- `0 ∈ F_A` (when `A` non-empty). -/
lemma zero_mem_forbiddenDiffSetMod (p : ℕ) (A : Finset ℤ) (hA : A.Nonempty) :
    (0 : ZMod p) ∈ forbiddenDiffSetMod p A := by
  classical
  rw [forbiddenDiffSetMod, Finset.mem_image]
  exact ⟨0, zero_mem_diffFinset_self hA, by simp⟩

/-- For `A ⊆ [1, N]` Sidon, `|F_A| ≤ 2N − 1`. -/
lemma forbiddenDiffSetMod_card_le
    {p N : ℕ} (_hp : 0 < p) (_hbig : 2 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) (hA : A.Nonempty) :
    ((forbiddenDiffSetMod p A).card : ℤ) ≤ ((2 * N - 1 : ℕ) : ℤ) := by
  classical
  have hNpos : 0 < N := by
    obtain ⟨a, ha⟩ := hA
    have hNint : (0 : ℤ) < (N : ℤ) := by
      linarith [(hAint a ha).1, (hAint a ha).2]
    exact_mod_cast hNint
  let nonzeroMod : Finset (ZMod p) :=
    ((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p))
  have hsubset : forbiddenDiffSetMod p A ⊆ insert 0 nonzeroMod := by
    intro x hx
    rw [forbiddenDiffSetMod, Finset.mem_image] at hx
    rcases hx with ⟨d, hd, rfl⟩
    by_cases hd0 : d = 0
    · simp [hd0]
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_image.mpr ⟨d, by simpa [hd0] using hd, rfl⟩))
  have hcard_nat : (forbiddenDiffSetMod p A).card ≤ 2 * N - 1 := by
    calc
      (forbiddenDiffSetMod p A).card ≤ (insert 0 nonzeroMod).card :=
        Finset.card_le_card hsubset
      _ ≤ nonzeroMod.card + 1 := Finset.card_insert_le _ _
      _ ≤ ((DiffFinset A A).erase 0).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ (2 * N - 2) + 1 :=
        Nat.add_le_add_right (sidon_nonzero_diff_card_le A N hAint hSidon) 1
      _ = 2 * N - 1 := by omega
  exact_mod_cast hcard_nat

lemma forbiddenDiffSetMod_eq_insert_offDiagDiffSetMod
    {p : ℕ} [NeZero p] (A : Finset ℤ) (hA : A.Nonempty) :
    forbiddenDiffSetMod p A =
      insert 0 (Erdos42.CompactCayley.offDiagDiffSetMod p A) := by
  classical
  ext t
  constructor
  · intro ht
    rw [forbiddenDiffSetMod, Finset.mem_image] at ht
    rcases ht with ⟨d, hd, rfl⟩
    rw [mem_diffFinset] at hd
    rcases hd with ⟨a, ha, b, hb, rfl⟩
    by_cases hzero : ((a - b : ℤ) : ZMod p) = 0
    · exact Finset.mem_insert.mpr (Or.inl hzero)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [Erdos42.CompactCayley.offDiagDiffSetMod, Finset.mem_image]
      have hab : a ≠ b := by
        intro hab
        subst b
        exact hzero (by simp)
      refine ⟨(a, b), ?_, rfl⟩
      rw [Finset.mem_offDiag]
      exact ⟨ha, hb, hab⟩
  · intro ht
    rw [Finset.mem_insert] at ht
    rcases ht with ht0 | ht
    · subst t
      exact zero_mem_forbiddenDiffSetMod p A hA
    · rw [Erdos42.CompactCayley.offDiagDiffSetMod, Finset.mem_image] at ht
      rcases ht with ⟨ab, hab, rfl⟩
      rw [Finset.mem_offDiag] at hab
      rcases hab with ⟨ha, hb, _hne⟩
      rw [forbiddenDiffSetMod, Finset.mem_image]
      exact ⟨ab.1 - ab.2, mem_diffFinset.mpr ⟨ab.1, ha, ab.2, hb, rfl⟩, rfl⟩

/-- Sidon Fourier lower bound (normalized): `Re 1̂_{F_A}(r) ≥ -(|A|−1)/p` for
every character `r` (combined PDF §3). For `p` large enough in `N`, this is
`≥ −ε`, hence `FourierLowerIndicator F_A ε`. -/
lemma sidon_forbidden_fourier_lower
    {p N : ℕ} [Fact p.Prime] [NeZero p] (_hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) (hA : A.Nonempty)
    (ε : ℝ)
    (hε : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε) :
    FourierLowerIndicator (forbiddenDiffSetMod p A) ε := by
  classical
  intro r
  have hε_nonneg : 0 ≤ ε := by
    have hleft : 0 ≤ ((A.card - 1 : ℕ) : ℝ) / (p : ℝ) := by positivity
    exact hleft.trans hε
  by_cases hr : r = 0
  · subst r
    have hcoeff_nonneg : 0 ≤ (normalizedDftCoeff (forbiddenDiffSetMod p A) 0).re := by
      have hp_pos : 0 < (p : ℝ) := by
        exact_mod_cast (Fact.out : p.Prime).pos
      rw [normalizedDftCoeff_zero_eq_card_div]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
      simp [div_nonneg (Nat.cast_nonneg _) hp_pos.le]
    linarith
  · have hF_eq :=
      forbiddenDiffSetMod_eq_insert_offDiagDiffSetMod (p := p) A hA
    have hsum_allowed :=
      Erdos42.CompactCayley.sum_allowedDiffSetMod_eq_neg_forbidden
        (p := p) A hr
    have hsum_forbidden :
        ∑ x ∈ insert 0 (Erdos42.CompactCayley.offDiagDiffSetMod p A),
            ZMod.stdAddChar (-(x * r)) =
          - ∑ x ∈ Erdos42.CompactCayley.allowedDiffSetMod p A,
              ZMod.stdAddChar (-(x * r)) := by
      calc
        ∑ x ∈ insert 0 (Erdos42.CompactCayley.offDiagDiffSetMod p A),
            ZMod.stdAddChar (-(x * r))
            = -(-∑ x ∈ insert 0 (Erdos42.CompactCayley.offDiagDiffSetMod p A),
                ZMod.stdAddChar (-(x * r))) := by simp
        _ = -∑ x ∈ Erdos42.CompactCayley.allowedDiffSetMod p A,
                ZMod.stdAddChar (-(x * r)) := by rw [← hsum_allowed]
    have hcoeff :
        normalizedDftCoeff (forbiddenDiffSetMod p A) r =
          - normalizedDftCoeff (Erdos42.CompactCayley.allowedDiffSetMod p A) r := by
      rw [hF_eq, normalizedDftCoeff_eq_sum, normalizedDftCoeff_eq_sum, hsum_forbidden]
      ring
    have hupper :
        (normalizedDftCoeff (Erdos42.CompactCayley.allowedDiffSetMod p A) r).re ≤ ε :=
      Erdos42.CompactCayley.allowedDiffs_fourier_upper
        (p := p) (N := N) _hbig A hAint hSidon ε hε r hr
    rw [hcoeff]
    simp
    linarith

/-! ## Step 5 — bad-tuple bound (non-Sidon ordered tuples in `[1, N]^M`) -/

/-- Crude bound: at most `(M^4 + M^3 + 1) · N^{M-1}` ordered `M`-tuples in
`[1, N]^M` are non-Sidon. The intended proof fixes the witness collision and
counts solutions one coordinate at a time. Kept as a theorem-shaped local
scaffold axiom until the tuple-counting bookkeeping is formalized. -/
axiom non_sidon_ordered_tuple_bound (M N : ℕ) :
    ((Finset.univ : Finset (Fin M → (Finset.Icc (1 : ℤ) N : Finset ℤ))).filter
        (fun x : Fin M → (Finset.Icc (1 : ℤ) N : Finset ℤ) =>
          ¬ IsSidonInt
            ((Finset.univ : Finset (Fin M)).image
              (fun i => ((x i).val : ℤ))))).card
      ≤ (M ^ 4 + M ^ 3 + 1) * N ^ (M - 1)

/-! ## Step 6 — final assembly: Theorem 1.1 from `finite_fourier_avoidance` -/

/-- **Theorem 1.1, Route A.** Same statement as Route B; intended to be proved
from `finite_fourier_avoidance`, the forbidden-set Fourier estimate above, and
`non_sidon_ordered_tuple_bound`. Kept as a theorem-shaped local scaffold axiom
until the final asymptotic/tuple-selection assembly is formalized. -/
axiom theorem_1_1_from_finite_fourier_avoidance
    (M : ℕ) (_hM : 1 ≤ M) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) → IsSidonInt A → A.Nonempty →
        ∃ B : Finset ℤ,
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ (N : ℤ)) ∧
          IsSidonInt B ∧ B.card = M ∧
          AvoidsNonzeroDiff A B

end Erdos42.FourierPositive
