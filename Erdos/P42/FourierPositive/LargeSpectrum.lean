/-
Erdos Problem 42 — Route A large-spectrum bounds.

The compact extraction begins by taking finite large spectra of the forbidden
indicators `1_{F_n}`.  Parseval bounds their cardinalities uniformly at each
fixed threshold.  This file records the finite, axiom-free part of that
argument.
-/

import Erdos.P42.FourierPositive.Counting

namespace Erdos42.FourierPositive

open Finset Erdos42
open scoped BigOperators Classical

/-- Large spectrum of a finite cyclic-group function at threshold `τ`. -/
noncomputable def largeSpectrum {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (τ : ℝ) : Finset (ZMod p) :=
  (Finset.univ : Finset (ZMod p)).filter
    (fun r => τ < ‖normalizedDftFunction f r‖)

lemma mem_largeSpectrum {p : ℕ} [NeZero p] {f : ZMod p → ℂ} {τ : ℝ}
    {r : ZMod p} :
    r ∈ largeSpectrum f τ ↔ τ < ‖normalizedDftFunction f r‖ := by
  simp [largeSpectrum]

lemma largeSpectrum_subset_univ {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (τ : ℝ) :
    largeSpectrum f τ ⊆ (Finset.univ : Finset (ZMod p)) := by
  intro r _hr
  simp

lemma largeSpectrum_mono {p : ℕ} [NeZero p] {f : ZMod p → ℂ}
    {τ₁ τ₂ : ℝ} (hτ : τ₂ ≤ τ₁) :
    largeSpectrum f τ₁ ⊆ largeSpectrum f τ₂ := by
  intro r hr
  exact mem_largeSpectrum.mpr (lt_of_le_of_lt hτ (mem_largeSpectrum.mp hr))

lemma norm_normalizedDftFunction_le_of_notMem_largeSpectrum
    {p : ℕ} [NeZero p] {f : ZMod p → ℂ} {τ : ℝ} {r : ZMod p}
    (hr : r ∉ largeSpectrum f τ) :
    ‖normalizedDftFunction f r‖ ≤ τ := by
  exact not_lt.mp (by simpa [mem_largeSpectrum] using hr)

lemma dyadicThreshold_antitone {k l : ℕ} (hkl : k ≤ l) :
    ((2 : ℝ) ^ l)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := by
  rw [inv_le_inv₀ (pow_pos (by norm_num : (0 : ℝ) < 2) l)
    (pow_pos (by norm_num : (0 : ℝ) < 2) k)]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hkl

lemma norm_normalizedDftFunction_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {f : ZMod p → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ 1) (r : ZMod p) :
    ‖normalizedDftFunction f r‖ ≤ 1 := by
  have hsum := sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hf
  have hterm :
      ‖normalizedDftFunction f r‖ ^ 2 ≤
        ∑ s : ZMod p, ‖normalizedDftFunction f s‖ ^ 2 :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (ZMod p)))
      (f := fun s : ZMod p => ‖normalizedDftFunction f s‖ ^ 2)
      (fun _s _hs => sq_nonneg _) (Finset.mem_univ r)
  have hsquare : ‖normalizedDftFunction f r‖ ^ 2 ≤ 1 := hterm.trans hsum
  have habs : |‖normalizedDftFunction f r‖| ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mp hsquare
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

lemma norm_normalizedDftCoeff_indicator_le_one
    {p : ℕ} [NeZero p] (F : Finset (ZMod p)) (r : ZMod p) :
    ‖normalizedDftCoeff F r‖ ≤ 1 := by
  simpa [normalizedDftCoeff] using
    (norm_normalizedDftFunction_le_one_of_norm_le_one
      (f := indicatorC F) (indicatorC_norm_le_one F) r)

/-- The large spectrum cardinality times `τ²` is bounded by the Fourier `L²`
mass. -/
lemma largeSpectrum_card_mul_sq_le_sum_sq
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((largeSpectrum f τ).card : ℝ) * τ ^ 2 ≤
      ∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2 := by
  classical
  calc
    ((largeSpectrum f τ).card : ℝ) * τ ^ 2 =
        ∑ r ∈ largeSpectrum f τ, τ ^ 2 := by
          simp [mul_comm]
    _ ≤ ∑ r ∈ largeSpectrum f τ, ‖normalizedDftFunction f r‖ ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hlt : τ < ‖normalizedDftFunction f r‖ :=
            (mem_largeSpectrum.mp hr)
          have hnorm_nonneg : 0 ≤ ‖normalizedDftFunction f r‖ := norm_nonneg _
          have hle_abs : |τ| ≤ |‖normalizedDftFunction f r‖| := by
            rw [abs_of_nonneg hτ, abs_of_nonneg hnorm_nonneg]
            exact le_of_lt hlt
          exact sq_le_sq.mpr hle_abs
    _ ≤ ∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (largeSpectrum_subset_univ f τ)
            (by intro r _hrUniv _hrNotLarge; exact sq_nonneg _)

/-- Large spectra of functions bounded by `1` have cardinality `≤ τ⁻²` in real
cardinality form. -/
lemma largeSpectrum_card_le_inv_sq_of_norm_le_one
    {p : ℕ} [NeZero p] {f : ZMod p → ℂ} {τ : ℝ}
    (hτ : 0 < τ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ((largeSpectrum f τ).card : ℝ) ≤ τ⁻¹ ^ 2 := by
  have hmass :=
    (largeSpectrum_card_mul_sq_le_sum_sq f (le_of_lt hτ)).trans
      (sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hf)
  have hτsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  calc
    ((largeSpectrum f τ).card : ℝ) ≤ 1 / τ ^ 2 := by
      exact (le_div_iff₀ hτsq).mpr (by simpa [mul_comm] using hmass)
    _ = τ⁻¹ ^ 2 := by
      field_simp [hτ.ne']

/-- Dyadic version used by the compact extraction: threshold `(2^k)⁻¹` has
large spectrum cardinality at most `(2^k)^2`. -/
lemma largeSpectrum_card_le_pow_two_sq_of_norm_le_one
    {p : ℕ} [NeZero p] {f : ZMod p → ℂ} (k : ℕ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ((largeSpectrum f (((2 : ℝ) ^ k)⁻¹)).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 := by
  have hτ : 0 < (((2 : ℝ) ^ k)⁻¹) :=
    inv_pos.mpr (pow_pos (by norm_num) k)
  simpa using
    (largeSpectrum_card_le_inv_sq_of_norm_le_one (p := p) (f := f)
      (τ := ((2 : ℝ) ^ k)⁻¹) hτ hf)

/-- Indicator-specialized dyadic large-spectrum bound. -/
lemma largeSpectrum_indicatorC_card_le_pow_two_sq
    {p : ℕ} [NeZero p] (F : Finset (ZMod p)) (k : ℕ) :
    ((largeSpectrum (indicatorC F) (((2 : ℝ) ^ k)⁻¹)).card : ℝ) ≤
      ((2 : ℝ) ^ k) ^ 2 :=
  largeSpectrum_card_le_pow_two_sq_of_norm_le_one k (indicatorC_norm_le_one F)

/-! ## Counterexample-sequence large spectra -/

/-- The dyadic large spectrum of the forbidden indicator in a Route A
counterexample sequence. -/
noncomputable def FourierAvoidanceCounterSeq.largeSpectrumAt
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n k : ℕ) : Finset (ZMod (S.p n)) :=
  letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
  largeSpectrum (indicatorC (S.F n)) (((2 : ℝ) ^ k)⁻¹)

lemma FourierAvoidanceCounterSeq.mem_largeSpectrumAt
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {n k : ℕ} {r : ZMod (S.p n)} :
    r ∈ S.largeSpectrumAt n k ↔
      (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        ((2 : ℝ) ^ k)⁻¹ < ‖normalizedDftFunction (indicatorC (S.F n)) r‖) := by
  simp [FourierAvoidanceCounterSeq.largeSpectrumAt, mem_largeSpectrum]

lemma FourierAvoidanceCounterSeq.largeSpectrumAt_card_le_pow_two_sq
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n k : ℕ) :
    ((S.largeSpectrumAt n k).card : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 := by
  letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
  change ((largeSpectrum (indicatorC (S.F n)) (((2 : ℝ) ^ k)⁻¹)).card : ℝ) ≤
    ((2 : ℝ) ^ k) ^ 2
  exact largeSpectrum_indicatorC_card_le_pow_two_sq (F := S.F n) k

lemma FourierAvoidanceCounterSeq.largeSpectrumAt_card_le_natCeil
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n k : ℕ) :
    (S.largeSpectrumAt n k).card ≤ Nat.ceil (((2 : ℝ) ^ k) ^ 2) := by
  have hreal := S.largeSpectrumAt_card_le_pow_two_sq n k
  have hceil : ((2 : ℝ) ^ k) ^ 2 ≤
      (Nat.ceil (((2 : ℝ) ^ k) ^ 2) : ℝ) :=
    Nat.le_ceil _
  exact Nat.cast_le.mp (hreal.trans hceil)

lemma FourierAvoidanceCounterSeq.largeSpectrumAt_mono
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    S.largeSpectrumAt n k ⊆ S.largeSpectrumAt n l := by
  letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
  unfold FourierAvoidanceCounterSeq.largeSpectrumAt
  exact largeSpectrum_mono (dyadicThreshold_antitone hkl)

lemma FourierAvoidanceCounterSeq.largeSpectrumAt_card_mono
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    (S.largeSpectrumAt n k).card ≤ (S.largeSpectrumAt n l).card :=
  Finset.card_le_card (S.largeSpectrumAt_mono n hkl)

lemma FourierAvoidanceCounterSeq.norm_normalizedDftFunction_le_of_notMem_largeSpectrumAt
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {n k : ℕ} {r : ZMod (S.p n)} (hr : r ∉ S.largeSpectrumAt n k) :
    (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
      ‖normalizedDftFunction (indicatorC (S.F n)) r‖ ≤ ((2 : ℝ) ^ k)⁻¹) := by
  letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
  unfold FourierAvoidanceCounterSeq.largeSpectrumAt at hr
  exact norm_normalizedDftFunction_le_of_notMem_largeSpectrum hr

/-- A fixed finite label bound for the `k`-th dyadic large spectrum. -/
noncomputable def largeSpectrumLabelBound (k : ℕ) : ℕ :=
  Nat.ceil (((2 : ℝ) ^ k) ^ 2)

lemma largeSpectrumLabelBound_pos (k : ℕ) : 0 < largeSpectrumLabelBound k := by
  unfold largeSpectrumLabelBound
  exact Nat.ceil_pos.mpr (sq_pos_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k))

/-- A fixed label type large enough to contain every `k`-th large spectrum in a
counterexample sequence.  Later diagonal extraction chooses subsequences of
these labels. -/
abbrev LargeSpectrumLabel (k : ℕ) : Type :=
  Fin (largeSpectrumLabelBound k)

/-- Any finite type whose cardinality is bounded by `B` embeds into `Fin B`.
This keeps the later large-spectrum labelling independent of the concrete
finite set. -/
noncomputable def boundedFintypeEmbedding
    (ι : Type*) [Fintype ι] (B : ℕ) (hcard : Fintype.card ι ≤ B) :
    ι ↪ Fin B where
  toFun x := Fin.castLE hcard ((Fintype.equivFin ι) x)
  inj' := by
    intro x y hxy
    have hfin : (Fintype.equivFin ι) x = (Fintype.equivFin ι) y :=
      (Fin.castLE_inj.mp hxy)
    exact (Fintype.equivFin ι).injective hfin

/-- Uniformly label the `k`-th large spectrum of the `n`-th finite group by the
fixed type `LargeSpectrumLabel k`. -/
noncomputable def FourierAvoidanceCounterSeq.largeSpectrumAtEmbedding
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n k : ℕ) :
    {r : ZMod (S.p n) // r ∈ S.largeSpectrumAt n k} ↪ LargeSpectrumLabel k :=
  by
    classical
    letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
    exact
      boundedFintypeEmbedding
        {r : ZMod (S.p n) // r ∈ S.largeSpectrumAt n k}
        (largeSpectrumLabelBound k)
        (by
          have hcard :
              Fintype.card {r : ZMod (S.p n) // r ∈ S.largeSpectrumAt n k} =
                (S.largeSpectrumAt n k).card := by
            simp
          rw [hcard]
          exact S.largeSpectrumAt_card_le_natCeil n k)

/-- Frequency represented by a fixed large-spectrum label.  Labels not hit by
the finite large spectrum at `(n,k)` are sent to `0`. -/
noncomputable def FourierAvoidanceCounterSeq.largeSpectrumLabelFreq
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n k : ℕ) (label : LargeSpectrumLabel k) : ZMod (S.p n) :=
  if h : ∃ r : {r : ZMod (S.p n) // r ∈ S.largeSpectrumAt n k},
      S.largeSpectrumAtEmbedding n k r = label
    then (Classical.choose h).1
    else 0

lemma FourierAvoidanceCounterSeq.largeSpectrumLabelFreq_mem_of_exists
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {n k : ℕ} {label : LargeSpectrumLabel k}
    (h : ∃ r : {r : ZMod (S.p n) // r ∈ S.largeSpectrumAt n k},
      S.largeSpectrumAtEmbedding n k r = label) :
    S.largeSpectrumLabelFreq n k label ∈ S.largeSpectrumAt n k := by
  classical
  simp [FourierAvoidanceCounterSeq.largeSpectrumLabelFreq, h]

lemma FourierAvoidanceCounterSeq.largeSpectrumLabelFreq_eq_zero_of_not_exists
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {n k : ℕ} {label : LargeSpectrumLabel k}
    (h : ¬ ∃ r : {r : ZMod (S.p n) // r ∈ S.largeSpectrumAt n k},
      S.largeSpectrumAtEmbedding n k r = label) :
    S.largeSpectrumLabelFreq n k label = 0 := by
  classical
  simp [FourierAvoidanceCounterSeq.largeSpectrumLabelFreq, h]

lemma FourierAvoidanceCounterSeq.largeSpectrumLabelFreq_embedding
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {n k : ℕ} (r : ZMod (S.p n)) (hr : r ∈ S.largeSpectrumAt n k) :
    S.largeSpectrumLabelFreq n k
        (S.largeSpectrumAtEmbedding n k ⟨r, hr⟩) = r := by
  classical
  let x : {r : ZMod (S.p n) // r ∈ S.largeSpectrumAt n k} := ⟨r, hr⟩
  have h : ∃ y : {r : ZMod (S.p n) // r ∈ S.largeSpectrumAt n k},
      S.largeSpectrumAtEmbedding n k y = S.largeSpectrumAtEmbedding n k x :=
    ⟨x, rfl⟩
  have hchoose :
      Classical.choose h = x := by
    apply (S.largeSpectrumAtEmbedding n k).injective
    exact Classical.choose_spec h
  simp [FourierAvoidanceCounterSeq.largeSpectrumLabelFreq]

end Erdos42.FourierPositive
