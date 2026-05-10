/-
Erdős Problem 42 — contradiction from a compact-Cayley counterexample sequence.
-/

import Erdos.P42.CompactCayley.SmoothDensityConvergence
import Mathlib.Data.Real.Archimedean

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

theorem CayleyCounterSeq.false
    {ℓ : ℕ} {η : ℝ} (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (S : CayleyCounterSeq ℓ η) :
    False := by
  classical
  obtain ⟨E, _⟩ := exists_cayleyExtraction S
  let ρ : ℝ := continuousCliqueDensity E.haar ℓ E.fReal
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact E.compact_limit_cliqueDensity_pos hℓ hη
  let L : ℝ := ((ℓ * ℓ : ℕ) : ℝ)
  have hℓ_pos : 0 < ℓ := by omega
  have hL_pos : 0 < L := by
    dsimp [L]
    exact_mod_cast Nat.mul_pos hℓ_pos hℓ_pos
  have htarget_pos : 0 < ρ / (8 * L) := by
    exact div_pos hρ_pos (mul_pos (by norm_num) hL_pos)
  obtain ⟨qNat, hqNat_pos, hqNat_inv⟩ :=
    Real.exists_nat_pos_inv_lt htarget_pos
  let q : ℕ+ := ⟨qNat, hqNat_pos⟩
  let qinv : ℝ := ((q : ℝ)⁻¹ : ℝ)
  have hq_pos_real : 0 < (q : ℝ) := by
    exact_mod_cast q.pos
  have hqinv_pos : 0 < qinv := by
    dsimp [qinv]
    exact inv_pos.mpr hq_pos_real
  have hqinv_lt : qinv < ρ / (8 * L) := by
    simpa [q, qinv] using hqNat_inv
  have hq_margin : L * (2 * qinv) < ρ / 4 := by
    have hmul :
        (2 * L) * qinv < (2 * L) * (ρ / (8 * L)) :=
      mul_lt_mul_of_pos_left hqinv_lt (mul_pos (by norm_num) hL_pos)
    have hcalc : (2 * L) * (ρ / (8 * L)) = ρ / 4 := by
      field_simp [ne_of_gt hL_pos]
      ring
    nlinarith
  let Bextra : Finset E.Group :=
    (E.data.largeSpectrumGenerators q).image Neg.neg
  obtain ⟨Q, hQ, hlower, _hQdensity_pos, hQdensity_ge⟩ :=
    E.exists_compactSmoothReal_cliqueDensity_pos_and_fejerPairCoeffLowerBound
      hℓ hη Bextra hqinv_pos
  let Merr : ℝ := max (2 * qinv) qinv
  have hMerr_eq : Merr = 2 * qinv := by
    dsimp [Merr]
    exact max_eq_left (by nlinarith [le_of_lt hqinv_pos])
  have hMerr_nonneg : 0 ≤ Merr := by
    rw [hMerr_eq]
    positivity
  have hMerr_margin : L * Merr < ρ / 4 := by
    simpa [Merr, hMerr_eq] using hq_margin
  have hthreshold_lt_limit :
      L * Merr <
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    have hquarter_half : ρ / 4 < ρ / 2 := by nlinarith
    exact lt_of_lt_of_le (lt_trans hMerr_margin hquarter_half)
      (by simpa [ρ] using hQdensity_ge)
  have hdensity_eventually :
      ∀ᶠ n in atTop,
        L * Merr <
          (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
           letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
           finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := ℓ)
            (E.finiteSmooth Q n)).re := by
    have hconv :=
      E.finiteCliqueKernelDensity_finiteSmooth_re_tendsto_compactSmoothReal
        Q ℓ
    exact hconv.eventually (isOpen_Ioi.mem_nhds hthreshold_lt_limit)
  have hnorm_eventually := E.finiteSmooth_norm_le_one_eventually Q hQ
  have hspectral_eventually :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          SpectralBound
            (fun z : ZMod (S.p (E.φ n)) =>
              indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
            Merr) := by
    have hspec :=
      E.spectralBound_indicator_sub_finiteSmooth_eventually_of_lowerBound_neg
        q Q hQ hlower
    refine hspec.mono ?_
    intro n hn
    simpa [Merr, qinv] using hn
  have hall :
      ∀ᶠ n in atTop,
        (∀ z : ZMod (S.p (E.φ n)), ‖E.finiteSmooth Q n z‖ ≤ 1) ∧
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          SpectralBound
            (fun z : ZMod (S.p (E.φ n)) =>
              indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
            Merr) ∧
        L * Merr <
          (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
           letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
           finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := ℓ)
            (E.finiteSmooth Q n)).re :=
    hnorm_eventually.and (hspectral_eventually.and hdensity_eventually)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  rcases hN N le_rfl with ⟨hnorm, hspectral, hdensity⟩
  haveI : Fact (S.p (E.φ N)).Prime := ⟨S.prime (E.φ N)⟩
  haveI : NeZero (S.p (E.φ N)) := ⟨(S.prime (E.φ N)).ne_zero⟩
  have hdensity' :
      ((ℓ * ℓ : ℕ) : ℝ) * Merr <
        (finiteCliqueKernelDensity (p := S.p (E.φ N)) (ℓ := ℓ)
          (E.finiteSmooth Q N)).re := by
    simpa [L] using hdensity
  have hclique :
      ∃ C : Finset (ZMod (S.p (E.φ N))),
        C.card = ℓ ∧ CliqueInCayley (S.T (E.φ N)) C :=
    exists_clique_of_spectral_density_transfer_sq
      (T := S.T (E.φ N))
      (g := E.finiteSmooth Q N)
      (M := Merr)
      (S.T_sym (E.φ N))
      (S.T_zero (E.φ N))
      hMerr_nonneg
      hnorm
      hspectral
      hdensity'
  exact S.no_clique (E.φ N) hclique

end

end Erdos42.CompactCayley
