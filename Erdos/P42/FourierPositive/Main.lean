/-
Erdős Problem 42 — Route A application.

Derives Theorem 1.1 (Erdős statement, `Finset ℤ` form) from the Route A
counting trust-boundary axiom `finite_fourier_avoidance_count`, through the
derived existence theorem `finite_fourier_avoidance_exists`. Pipeline
(combined PDF / Ulam note Section 3, with Tao's greedy-Sidon simplification):

  1. Forbidden set: `F := (A − A) mod p` for `p` a prime in `(4N, 8N)`.
     Symmetric, `0 ∈ F`, `|F| ≤ 2N − 1 ≤ (1 − 1/2) p`.
  2. Sidon Fourier lower bound: `1̂_F(r) = |1̂_A(r)|² − (|A|−1)/p ≥ −(|A|−1)/p`,
     which is `≥ −ε` for `p` large enough (combined PDF §3).
  3. `U := [1, N] mod p` has density `≥ 1/8 · p` (since `p < 8N`).
  4. Apply `finite_fourier_avoidance_exists` with
     `m = greedySidonThreshold M` to get a large distinct tuple avoiding `F`.
  5. Take its image `X ⊆ [1,N]`; because `0 ∈ F`, the tuple is injective.
  6. Greedily extract a Sidon subset `B ⊆ X` of size `M`.
-/

import Erdos.P42.Shared.Common
import Erdos.P42.Shared.Sidon
import Erdos.P42.Shared.FiniteFourier
import Erdos.P42.FourierPositive.FiniteAvoidance
import Erdos.P42.FourierPositive.Counterexample
import Erdos.P42.FourierPositive.Counting
import Erdos.P42.FourierPositive.CompactModel
import Erdos.P42.FourierPositive.LargeSpectrum
import Erdos.P42.FourierPositive.Limit
import Erdos.P42.FourierPositive.ExtractionGroup
import Erdos.P42.FourierPositive.CompactDual
import Erdos.P42.FourierPositive.TrigPolynomial
import Erdos.P42.FourierPositive.Fejer
import Erdos.P42.Shared.FiniteReduction

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
      insert 0 (Erdos42.offDiagDiffSetMod p A) := by
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
      rw [Erdos42.offDiagDiffSetMod, Finset.mem_image]
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
    · rw [Erdos42.offDiagDiffSetMod, Finset.mem_image] at ht
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
      Erdos42.sum_allowedDiffSetMod_eq_neg_forbidden
        (p := p) A hr
    have hsum_forbidden :
        ∑ x ∈ insert 0 (Erdos42.offDiagDiffSetMod p A),
            ZMod.stdAddChar (-(x * r)) =
          - ∑ x ∈ Erdos42.allowedDiffSetMod p A,
              ZMod.stdAddChar (-(x * r)) := by
      calc
        ∑ x ∈ insert 0 (Erdos42.offDiagDiffSetMod p A),
            ZMod.stdAddChar (-(x * r))
            = -(-∑ x ∈ insert 0 (Erdos42.offDiagDiffSetMod p A),
                ZMod.stdAddChar (-(x * r))) := by simp
        _ = -∑ x ∈ Erdos42.allowedDiffSetMod p A,
                ZMod.stdAddChar (-(x * r)) := by rw [← hsum_allowed]
    have hcoeff :
        normalizedDftCoeff (forbiddenDiffSetMod p A) r =
          - normalizedDftCoeff (Erdos42.allowedDiffSetMod p A) r := by
      rw [hF_eq, normalizedDftCoeff_eq_sum, normalizedDftCoeff_eq_sum, hsum_forbidden]
      ring
    have hupper :
        (normalizedDftCoeff (Erdos42.allowedDiffSetMod p A) r).re ≤ ε :=
      Erdos42.allowedDiffs_fourier_upper
        (p := p) (N := N) _hbig A hAint hSidon ε hε r hr
    rw [hcoeff]
    simp
    linarith

/-! ## Step 3 — final assembly from existence avoidance + greedy Sidon -/

/-- **Theorem 1.1, Route A.** Same statement as Route B; intended to be proved
from the existence form of finite Fourier avoidance, the forbidden-set Fourier
estimate above, and the shared greedy Sidon extraction. -/
theorem theorem_1_1_from_finite_fourier_avoidance
    (M : ℕ) (_hM : 1 ≤ M) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) → IsSidonInt A → A.Nonempty →
        ∃ B : Finset ℤ,
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ (N : ℤ)) ∧
          IsSidonInt B ∧ B.card = M ∧
          AvoidsNonzeroDiff A B := by
  classical
  let R := Erdos42.greedySidonThreshold M
  have hRpos : 0 < R := by
    dsimp [R, Erdos42.greedySidonThreshold]
    omega
  have hRge : 1 ≤ R := Nat.succ_le_of_lt hRpos
  obtain ⟨ε, hεpos, p₀, havoid⟩ :=
    finite_fourier_avoidance_exists R (1 / 8 : ℝ) (1 / 2 : ℝ)
      hRge (by norm_num) (by norm_num)
  obtain ⟨Nε, hNε⟩ :=
    Erdos42.sidon_card_minus_one_div_prime_eventually_small ε hεpos
  refine ⟨max (p₀ + 1) Nε, ?_⟩
  intro N hN A hAint hSidon hAnonempty
  have hNpos : 0 < N := by
    obtain ⟨a, ha⟩ := hAnonempty
    have hNint : (0 : ℤ) < (N : ℤ) := by
      linarith [(hAint a ha).1, (hAint a ha).2]
    exact_mod_cast hNint
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  haveI : Fact p.Prime := ⟨hpprime⟩
  haveI : NeZero p := ⟨hpprime.ne_zero⟩
  have hp₀le : p₀ ≤ p := by omega
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
  let F : Finset (ZMod p) := forbiddenDiffSetMod p A
  let U : Finset (ZMod p) :=
    (Finset.Icc 1 N).image (fun n : ℕ => (n : ZMod p))
  have hF_sym : SymmetricFinset F := by
    simpa [F] using forbiddenDiffSetMod_symmetric p A
  have hF_zero : (0 : ZMod p) ∈ F := by
    simpa [F] using zero_mem_forbiddenDiffSetMod p A hAnonempty
  have hF_density : (F.card : ℝ) ≤ (1 - 1 / 2 : ℝ) * p := by
    have hcard_int :=
      forbiddenDiffSetMod_card_le (p := p) (N := N) hpprime.pos (by omega) A
        hAint hSidon hAnonempty
    have hcard_real :
        (F.card : ℝ) ≤ (((2 * N - 1 : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast hcard_int
    have hbound :
        (((2 * N - 1 : ℕ) : ℤ) : ℝ) ≤ (1 / 2 : ℝ) * (p : ℝ) := by
      have hcast : (((2 * N - 1 : ℕ) : ℤ) : ℝ) = 2 * (N : ℝ) - 1 := by
        have hle : 1 ≤ 2 * N := by omega
        rw [Nat.cast_sub hle]
        norm_num
      have hpgtR : 4 * (N : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
      rw [hcast]
      nlinarith
    have hhalf : (1 - 1 / 2 : ℝ) * (p : ℝ) = (1 / 2 : ℝ) * p := by ring
    rw [hhalf]
    exact hcard_real.trans hbound
  have hUcard : U.card = N := by
    dsimp [U]
    have hinj :
        Set.InjOn (fun n : ℕ => (n : ZMod p)) ((Finset.Icc 1 N : Finset ℕ) : Set ℕ) := by
      intro i hi j hj hij
      change i ∈ (Finset.Icc 1 N : Finset ℕ) at hi
      change j ∈ (Finset.Icc 1 N : Finset ℕ) at hj
      rw [Finset.mem_Icc] at hi hj
      exact Erdos42.nat_eq_of_zmod_eq_of_lt
        (p := p) (i := i) (j := j) (by omega) (by omega) hij
    rw [Finset.card_image_of_injOn hinj]
    simp
  have hU_density : (1 / 8 : ℝ) * (p : ℝ) ≤ (U.card : ℝ) := by
    rw [hUcard]
    have hpupperR : (p : ℝ) < 8 * (N : ℝ) := by exact_mod_cast hpupper
    nlinarith
  have hsmall : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε :=
    hNε N p (by omega) hpgt A hAint hSidon
  have hF_fourier : FourierLowerIndicator F ε := by
    simpa [F] using
      sidon_forbidden_fourier_lower (p := p) (N := N) hpgt A hAint hSidon hAnonempty ε hsmall
  obtain ⟨x, hx⟩ :=
    havoid p hp₀le F U hF_sym hF_zero hF_density hU_density hF_fourier
  have hxU : ∀ i : Fin R, x i ∈ U := hx.1
  have hxAvoid : ∀ i j : Fin R, i ≠ j → x i - x j ∉ F := hx.2
  have hpre :
      ∀ i : Fin R, ∃ n : ℕ, n ∈ Finset.Icc 1 N ∧ (n : ZMod p) = x i := by
    intro i
    have hxi := hxU i
    change x i ∈ U at hxi
    change x i ∈ (Finset.Icc 1 N).image (fun n : ℕ => (n : ZMod p)) at hxi
    rw [Finset.mem_image] at hxi
    rcases hxi with ⟨n, hn, hncast⟩
    exact ⟨n, hn, hncast⟩
  let nOf : Fin R → ℕ := fun i => Classical.choose (hpre i)
  have hnMem : ∀ i : Fin R, nOf i ∈ Finset.Icc 1 N := by
    intro i
    exact (Classical.choose_spec (hpre i)).1
  have hnCast : ∀ i : Fin R, (nOf i : ZMod p) = x i := by
    intro i
    exact (Classical.choose_spec (hpre i)).2
  let X : Finset ℤ := (Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ))
  have hXcard : R ≤ X.card := by
    have hinj :
        Set.InjOn (fun i : Fin R => (nOf i : ℤ)) ((Finset.univ : Finset (Fin R)) : Set (Fin R)) := by
      intro i _hi j _hj hij
      by_contra hijFin
      have hnEq : nOf i = nOf j := Int.ofNat_injective hij
      have hxEq : x i = x j := by
        rw [← hnCast i, ← hnCast j, hnEq]
      exact (hxAvoid i j hijFin) (by simpa [F, hxEq] using hF_zero)
    change R ≤ ((Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ))).card
    rw [Finset.card_image_of_injOn hinj]
    simp
  have hXint : ∀ b ∈ X, 1 ≤ b ∧ b ≤ (N : ℤ) := by
    intro b hb
    change b ∈ (Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ)) at hb
    rw [Finset.mem_image] at hb
    rcases hb with ⟨i, _hi, rfl⟩
    have hi := hnMem i
    rw [Finset.mem_Icc] at hi
    exact_mod_cast hi
  have hAvoidAX : AvoidsNonzeroDiff A X := by
    intro d hdA hdX
    rw [mem_diffFinset] at hdA hdX
    rcases hdA with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    rcases hdX with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
    by_cases hzero : a₁ - a₂ = 0
    · exact hzero
    · exfalso
      change b₁ ∈ (Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ)) at hb₁
      change b₂ ∈ (Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ)) at hb₂
      rw [Finset.mem_image] at hb₁ hb₂
      rcases hb₁ with ⟨i, _hi, hb₁eq⟩
      rcases hb₂ with ⟨j, _hj, hb₂eq⟩
      have hij : i ≠ j := by
        intro hij
        subst j
        apply hzero
        rw [← hb₁eq, ← hb₂eq] at hbDiff
        linarith
      have hFmem : x i - x j ∈ F := by
        change x i - x j ∈ forbiddenDiffSetMod p A
        rw [forbiddenDiffSetMod, Finset.mem_image]
        refine ⟨a₁ - a₂, ?_, ?_⟩
        · rw [mem_diffFinset]
          exact ⟨a₁, ha₁, a₂, ha₂, rfl⟩
        · calc
            ((a₁ - a₂ : ℤ) : ZMod p) = ((b₁ - b₂ : ℤ) : ZMod p) := by rw [hbDiff]
            _ = ((nOf i : ℤ) - (nOf j : ℤ) : ℤ) := by rw [hb₁eq, hb₂eq]
            _ = x i - x j := by
              rw [← hnCast i, ← hnCast j]
              norm_num
      exact (hxAvoid i j hij) hFmem
  obtain ⟨B, hBX, hBcard, hBsidon⟩ :=
    Erdos42.exists_sidon_subset_of_card_ge M X (by simpa [R] using hXcard)
  refine ⟨B, ?_, hBsidon, hBcard, ?_⟩
  · intro b hb
    exact hXint b (hBX hb)
  · intro d hdA hdB
    apply hAvoidAX d hdA
    rw [mem_diffFinset] at hdB ⊢
    rcases hdB with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨b₁, hBX hb₁, b₂, hBX hb₂, rfl⟩

end Erdos42.FourierPositive
