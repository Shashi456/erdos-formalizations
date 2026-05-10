/-
Erdős Problem 42 — compact-Cayley extraction specialized to counterexamples.

This file connects the generic Fourier extraction sequence to the concrete
counterexample sets `T_n`.  The resulting coefficient facts are the finite
hypotheses that later define the compact limit kernel.
-/

import Erdos.P42.CompactCayley.CoeffLimit

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Classical Topology

noncomputable section

/-- Stable Fourier extraction package attached to a compact-Cayley
counterexample sequence. -/
structure CayleyExtraction {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η) where
  data :
    (S.toFourierSeq).StableSubseqData
      (S.toFourierSeq.largeSpectrumLabelFreq)

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- The discrete extraction quotient. -/
abbrev Group (E : CayleyExtraction S) : Type :=
  E.data.Group

instance (E : CayleyExtraction S) : Countable E.Group :=
  inferInstance

instance (E : CayleyExtraction S) : IsAddTorsionFree E.Group :=
  inferInstance

/-- The selected index in the original counterexample sequence. -/
def φ (E : CayleyExtraction S) : ℕ → ℕ :=
  E.data.φ

lemma strictMono_φ (E : CayleyExtraction S) :
    StrictMono E.φ :=
  E.data.strictMono_φ

/-- Finite lift of an extraction quotient frequency to the selected cyclic
group. -/
noncomputable def lift (E : CayleyExtraction S)
    (n : ℕ) (γ : E.Group) :
    ZMod (S.p (E.φ n)) :=
  E.data.finiteLift n γ

/-- Coefficient limit attached to a quotient frequency. -/
noncomputable def coeff (E : CayleyExtraction S) (γ : E.Group) : ℂ :=
  E.data.coeff γ

lemma coeff_tendsto (E : CayleyExtraction S) (γ : E.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ))
      atTop (𝓝 (E.coeff γ)) := by
  simpa [coeff, lift, φ, CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
    normalizedDftCoeff] using E.data.coeff_tendsto γ

/-- Canonical labels cover all finite large spectra along the extracted
subsequence. -/
lemma eventually_largeSpectrum_covered
    (E : CayleyExtraction S) (q : ℕ+) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (S.p (E.φ n)),
        ((q : ℝ)⁻¹ : ℝ) <
            ‖(letI : NeZero (S.p (E.φ n)) :=
                ⟨(S.prime (E.φ n)).ne_zero⟩;
              normalizedDftCoeff (S.T (E.φ n)) r)‖ →
          ∃ γ ∈ E.data.largeSpectrumGenerators q,
            E.lift n γ = r := by
  have hcover :
      ∀ q n r,
        r ∈ (S.toFourierSeq).largeSpectrum q n →
          ∃ k : Fin ((q : ℕ) ^ 2 + 1),
            (S.toFourierSeq).largeSpectrumLabelFreq ⟨q, k⟩ n = r := by
    intro q n r hr
    exact (S.toFourierSeq).exists_largeSpectrumLabelFreq_eq_of_mem q n hr
  simpa [lift, φ, CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
    normalizedDftCoeff] using
      E.data.eventually_largeSpectrum_covered hcover q

lemma coeff_norm_le_inv_of_not_mem_largeSpectrumGenerators
    (E : CayleyExtraction S) (q : ℕ+) {γ : E.Group}
    (hγ : γ ∉ E.data.largeSpectrumGenerators q) :
    ‖E.coeff γ‖ ≤ ((q : ℝ)⁻¹ : ℝ) := by
  have hcover :
      ∀ q n r,
        r ∈ (S.toFourierSeq).largeSpectrum q n →
          ∃ k : Fin ((q : ℕ) ^ 2 + 1),
            (S.toFourierSeq).largeSpectrumLabelFreq ⟨q, k⟩ n = r := by
    intro q n r hr
    exact (S.toFourierSeq).exists_largeSpectrumLabelFreq_eq_of_mem q n hr
  simpa [coeff] using
    E.data.coeff_norm_le_inv_of_not_mem_largeSpectrumGenerators hcover q hγ

lemma coeff_im_eq_zero (E : CayleyExtraction S) (γ : E.Group) :
    (E.coeff γ).im = 0 := by
  have hlim :=
    Complex.continuous_im.tendsto (E.coeff γ) |>.comp (E.coeff_tendsto γ)
  have him :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          (normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)).im) = 0 :=
    Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      exact normalizedDftCoeff_im_eq_zero_of_symmetric
        (S.T_sym (E.φ n)) (E.lift n γ))
  have hzero :
      Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 (E.coeff γ).im) :=
    Filter.Tendsto.congr' him hlim
  exact tendsto_nhds_unique hzero tendsto_const_nhds

lemma coeff_neg_eq (E : CayleyExtraction S) (γ : E.Group) :
    E.coeff (-γ) = E.coeff γ := by
  have hneg_tendsto := E.coeff_tendsto (-γ)
  have hpos_tendsto := E.coeff_tendsto γ
  have heq :
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n (-γ))) =ᶠ[atTop]
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)) := by
    filter_upwards [E.data.finiteLift_neg_eventually_eq γ] with n hneg
    haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    rw [lift, lift, hneg]
    exact normalizedDftCoeff_neg_eq_of_symmetric (S.T_sym (E.φ n)) (E.lift n γ)
  exact tendsto_nhds_unique (hneg_tendsto.congr' heq) hpos_tendsto

lemma coeff_nonpos_of_ne_zero
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    (E.coeff γ).re ≤ 0 := by
  have hlim :=
    Complex.continuous_re.tendsto (E.coeff γ) |>.comp (E.coeff_tendsto γ)
  have heps :
      Tendsto (fun n => S.eps (E.φ n)) atTop (𝓝 0) :=
    S.eps_tendsto_zero.comp E.strictMono_φ.tendsto_atTop
  have hupper :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          (normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)).re) ≤
          S.eps (E.φ n) := by
    filter_upwards [E.data.finiteLift_eventually_ne_zero hγ] with n hn
    letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    exact S.T_fourier_upper (E.φ n) (E.lift n γ) hn
  exact le_of_tendsto_of_tendsto hlim heps hupper

lemma coeff_zero_ge_eta (E : CayleyExtraction S) :
    η ≤ (E.coeff 0).re := by
  have hlim :=
    Complex.continuous_re.tendsto (E.coeff (0 : E.Group)) |>.comp
      (E.coeff_tendsto (0 : E.Group))
  have hdens :
      ∀ᶠ n in atTop,
        η ≤
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            (normalizedDftCoeff (S.T (E.φ n)) (E.lift n 0)).re) := by
    filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hn
    letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    have hp_pos : 0 < (S.p (E.φ n) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (S.prime (E.φ n)).ne_zero
    have hη_div :
        η ≤ ((S.T (E.φ n)).card : ℝ) / (S.p (E.φ n) : ℝ) :=
      (le_div_iff₀ hp_pos).mpr (S.T_density (E.φ n))
    simpa [lift, hn, normalizedDftCoeff_zero_eq_card_div,
      Complex.ofReal_div] using hη_div
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hdens

end CayleyExtraction

/-- Existence of compact-Cayley stable extraction data for a counterexample
sequence. -/
theorem exists_cayleyExtraction
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) :
    ∃ _E : CayleyExtraction S, True := by
  classical
  rcases (S.toFourierSeq).exists_stableSubseqData
      (S.toFourierSeq.largeSpectrumLabelFreq) with
    ⟨data, _⟩
  exact ⟨⟨data⟩, trivial⟩

end

end Erdos42.CompactCayley
