/-
Erdős Problem 42 — quotient coefficient limits and large-spectrum cover.

This file pushes the formal-word coefficient limits from stable extraction data
to chosen representatives of quotient frequencies.  It also records the key
large-spectrum covering consequence of the non-nested labels.
-/

import Erdos.P42.CompactCayley.TorsionFree

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped BigOperators Classical Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

/-- Coefficient limit attached to a quotient frequency, using its chosen
representative. -/
noncomputable def coeff
    (data : F.StableSubseqData labelFreq) (γ : data.Group) : ℂ :=
  data.coeffLimit (Quotient.out γ)

lemma coeff_tendsto
    (data : F.StableSubseqData labelFreq) (γ : data.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (F.p (data.φ n)) := ⟨(F.prime (data.φ n)).ne_zero⟩;
        F.coeff (data.φ n) (data.finiteLift n γ))
      atTop (𝓝 (data.coeff γ)) := by
  simpa [coeff, finiteLift] using
    data.coeffLimit_tendsto (Quotient.out γ)

/-- Quotient generator associated to a large-spectrum label. -/
noncomputable def generator
    (data : F.StableSubseqData labelFreq) (label : LargeLabel) :
    data.Group :=
  QuotientAddGroup.mk (FreeAbelianGroup.of label)

/-- The finite set of quotient frequencies representing the `q`-large
spectrum, plus zero. -/
noncomputable def largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq) (q : ℕ+) :
    Finset data.Group :=
  ((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
      (fun k => data.generator (⟨q, k⟩ : LargeLabel))) ∪ {0}

lemma generator_mem_largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq) (q : ℕ+)
    (k : Fin ((q : ℕ) ^ 2 + 1)) :
    data.generator (⟨q, k⟩ : LargeLabel) ∈
      data.largeSpectrumGenerators q := by
  classical
  unfold largeSpectrumGenerators
  exact Finset.mem_union.mpr <|
    Or.inl (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

lemma zero_mem_largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq) (q : ℕ+) :
    (0 : data.Group) ∈ data.largeSpectrumGenerators q := by
  classical
  simp [largeSpectrumGenerators]

lemma largeSpectrumGenerators_card_le
    (data : F.StableSubseqData labelFreq) (q : ℕ+) :
    (data.largeSpectrumGenerators q).card ≤ (q : ℕ) ^ 2 + 2 := by
  classical
  unfold largeSpectrumGenerators
  calc
    (((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
          (fun k => data.generator (⟨q, k⟩ : LargeLabel))) ∪ {0}).card
        ≤ ((((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
          (fun k => data.generator (⟨q, k⟩ : LargeLabel))).card) +
            (({(0 : data.Group)} : Finset data.Group).card)) := by
          exact Finset.card_union_le _ _
    _ = (((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
          (fun k => data.generator (⟨q, k⟩ : LargeLabel))).card) + 1 := by
          simp
    _ ≤ (Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).card + 1 := by
          exact Nat.add_le_add_right Finset.card_image_le 1
    _ = (q : ℕ) ^ 2 + 2 := by simp

/-- Label generators have their labelled finite frequency as finite lift,
eventually. -/
lemma finiteLift_generator_eventually_eq
    (data : F.StableSubseqData labelFreq) (label : LargeLabel) :
    ∀ᶠ n in atTop,
      data.finiteLift n (data.generator label) =
        labelFreq label (data.φ n) := by
  filter_upwards
    [data.finiteLift_mk_eventually_eq (FreeAbelianGroup.of label)] with n hn
  simpa [generator, finiteLiftHom_apply, FourierSeq.wordLift,
    FourierSeq.wordLiftHom_apply_of] using hn

/-- If `labelFreq` covers every finite large spectrum before extraction, then
the quotient generators cover every finite large spectrum along the stable
subsequence. -/
lemma eventually_largeSpectrum_covered
    (data : F.StableSubseqData labelFreq)
    (hcover :
      ∀ q n r, r ∈ F.largeSpectrum q n →
        ∃ k : Fin ((q : ℕ) ^ 2 + 1),
          labelFreq ⟨q, k⟩ n = r)
    (q : ℕ+) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (F.p (data.φ n)),
        ((q : ℝ)⁻¹ : ℝ) < ‖F.coeff (data.φ n) r‖ →
          ∃ γ ∈ data.largeSpectrumGenerators q,
            data.finiteLift n γ = r := by
  classical
  have hlabels' :
      ∀ᶠ n in atTop,
        ∀ k ∈ (Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))),
          data.finiteLift n (data.generator (⟨q, k⟩ : LargeLabel)) =
            labelFreq ⟨q, k⟩ (data.φ n) := by
    rw [(Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).eventually_all]
    intro k _hk
    exact data.finiteLift_generator_eventually_eq (⟨q, k⟩ : LargeLabel)
  have hlabels :
      ∀ᶠ n in atTop,
        ∀ k : Fin ((q : ℕ) ^ 2 + 1),
          data.finiteLift n (data.generator (⟨q, k⟩ : LargeLabel)) =
            labelFreq ⟨q, k⟩ (data.φ n) := by
    filter_upwards [hlabels'] with n hn k
    exact hn k (Finset.mem_univ k)
  filter_upwards [hlabels] with n hn r hr
  have hrmem : r ∈ F.largeSpectrum q (data.φ n) :=
    FourierSeq.mem_largeSpectrum.mpr hr
  rcases hcover q (data.φ n) r hrmem with ⟨k, hk⟩
  refine ⟨data.generator (⟨q, k⟩ : LargeLabel),
    data.generator_mem_largeSpectrumGenerators q k, ?_⟩
  exact (hn k).trans hk

/-- Coefficient limits outside the `q`-large-spectrum generator set have norm
at most `q⁻¹`. -/
lemma coeff_norm_le_inv_of_not_mem_largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq)
    (hcover :
      ∀ q n r, r ∈ F.largeSpectrum q n →
        ∃ k : Fin ((q : ℕ) ^ 2 + 1),
          labelFreq ⟨q, k⟩ n = r)
    (q : ℕ+) {γ : data.Group}
    (hγ : γ ∉ data.largeSpectrumGenerators q) :
    ‖data.coeff γ‖ ≤ ((q : ℝ)⁻¹ : ℝ) := by
  classical
  by_contra hnot
  have hlt : ((q : ℝ)⁻¹ : ℝ) < ‖data.coeff γ‖ := lt_of_not_ge hnot
  have hnorm :
      Tendsto
        (fun n =>
          ‖(letI : NeZero (F.p (data.φ n)) :=
              ⟨(F.prime (data.φ n)).ne_zero⟩;
            F.coeff (data.φ n) (data.finiteLift n γ))‖)
        atTop (𝓝 ‖data.coeff γ‖) :=
    (continuous_norm.tendsto (data.coeff γ)).comp (data.coeff_tendsto γ)
  have hlarge :
      ∀ᶠ n in atTop,
        ((q : ℝ)⁻¹ : ℝ) <
          ‖(letI : NeZero (F.p (data.φ n)) :=
              ⟨(F.prime (data.φ n)).ne_zero⟩;
            F.coeff (data.φ n) (data.finiteLift n γ))‖ :=
    hnorm.eventually (eventually_gt_nhds hlt)
  have hcovered := data.eventually_largeSpectrum_covered hcover q
  have hinj :=
    data.finiteLift_eventually_injOn_finset
      (data.largeSpectrumGenerators q ∪ {γ})
  rcases (hlarge.and (hcovered.and hinj)).exists with
    ⟨n, hnlarge, hncovered, hninj⟩
  rcases hncovered (data.finiteLift n γ) (by simpa using hnlarge) with
    ⟨δ, hδmem, hδeq⟩
  have hδmem' : δ ∈ (data.largeSpectrumGenerators q ∪ {γ}) := by
    simp [hδmem]
  have hγmem' : γ ∈ (data.largeSpectrumGenerators q ∪ {γ}) := by
    simp
  have hδγ : δ = γ := hninj hδmem' hγmem' hδeq
  exact hγ (by simpa [hδγ] using hδmem)

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley
