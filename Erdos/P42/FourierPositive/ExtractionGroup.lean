/-
Erdos Problem 42 — Route A extraction group skeleton.

After diagonal extraction of labelled large-spectrum Fourier coefficients, the
compactness proof builds a discrete abelian group from formal integer
combinations of labels, quotienting by the combinations whose finite lifts are
eventually zero.  The Pontryagin dual of this quotient is the compact group
used in the final model.

This file formalizes the algebraic quotient interface, without yet proving the
torsion-free/connected-dual facts.
-/

import Erdos.P42.FourierPositive.Limit
import Mathlib.Algebra.Group.Torsion

namespace Erdos42.FourierPositive

open Filter Erdos42
open scoped Topology Classical

/-- Formal integer combinations of the extended Route A large-spectrum labels. -/
abbrev ExtractionFreeGroup : Type :=
  FreeAbelianGroup ExtendedLargeSpectrumIndex

instance extractionFreeGroupCountable : Countable ExtractionFreeGroup := by
  dsimp [ExtractionFreeGroup, ExtendedLargeSpectrumIndex, LargeSpectrumIndex,
    LargeSpectrumLabel]
  infer_instance

/-- Pass coefficient-limit data to a further strictly monotone subsequence. -/
noncomputable def ExtendedLargeSpectrumCoeffLimitData.subseq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    ExtendedLargeSpectrumCoeffLimitData S where
  φ := data.φ ∘ ψ
  strictMono_φ := data.strictMono_φ.comp hψ
  fCoeff := data.fCoeff
  uCoeff := data.uCoeff
  fCoeff_tendsto := by
    intro idx
    simpa [Function.comp] using
      (data.fCoeff_tendsto idx).comp hψ.tendsto_atTop
  uCoeff_tendsto := by
    intro idx
    simpa [Function.comp] using
      (data.uCoeff_tendsto idx).comp hψ.tendsto_atTop
  fCoeff_nonneg := data.fCoeff_nonneg
  fCoeff_im_eq_zero := data.fCoeff_im_eq_zero
  zero_fCoeff_le := data.zero_fCoeff_le
  zero_uCoeff_ge := data.zero_uCoeff_ge
  zero_uCoeff_im_eq_zero := data.zero_uCoeff_im_eq_zero

/-- Finite lift of a formal label combination to the `n`-th cyclic group along
the subsequence selected by `data`. -/
noncomputable def extractionFiniteLiftHom
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) (n : ℕ) :
    ExtractionFreeGroup →+ ZMod (S.p (data.φ n)) :=
  FreeAbelianGroup.lift fun idx : ExtendedLargeSpectrumIndex =>
    S.extendedLargeSpectrumIndexFreq (data.φ n) idx

lemma extractionFiniteLiftHom_apply_of
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S)
    (n : ℕ) (idx : ExtendedLargeSpectrumIndex) :
    extractionFiniteLiftHom data n (FreeAbelianGroup.of idx) =
      S.extendedLargeSpectrumIndexFreq (data.φ n) idx := by
  simp [extractionFiniteLiftHom]

lemma extractionFiniteLiftHom_subseq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (n : ℕ) (g : ExtractionFreeGroup) :
    extractionFiniteLiftHom (data.subseq ψ hψ) n g =
      extractionFiniteLiftHom data (ψ n) g := by
  rfl

/-- Coefficient-limit data together with eventual stability of all formal
finite-lift zero relations.  This is the subsequence package needed before
finite trigonometric polynomial averages can be compared with compact
averages. -/
structure StableExtendedLargeSpectrumCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    extends ExtendedLargeSpectrumCoeffLimitData S where
  finiteLift_eventually_stable : ∀ g : ExtractionFreeGroup,
    (∀ᶠ n in atTop, extractionFiniteLiftHom toExtendedLargeSpectrumCoeffLimitData n g = 0) ∨
      (∀ᶠ n in atTop, extractionFiniteLiftHom toExtendedLargeSpectrumCoeffLimitData n g ≠ 0)

theorem FourierAvoidanceCounterSeq.exists_stableExtendedLargeSpectrumCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) :
    ∃ _data : StableExtendedLargeSpectrumCoeffLimitData S, True := by
  classical
  rcases S.exists_extendedLargeSpectrumCoeffLimitData with ⟨data, _⟩
  let P : ExtractionFreeGroup → ℕ → Prop :=
    fun g n => extractionFiniteLiftHom data n g = 0
  rcases exists_strictMono_subseq_eventually_const_countable_family P with
    ⟨ψ, hψ, hstable⟩
  let data' : ExtendedLargeSpectrumCoeffLimitData S := data.subseq ψ hψ
  refine ⟨{
    toExtendedLargeSpectrumCoeffLimitData := data'
    finiteLift_eventually_stable := ?_
  }, trivial⟩
  intro g
  rcases hstable g with hzero | hnonzero
  · exact Or.inl (by
      simpa [data', P, extractionFiniteLiftHom_subseq] using hzero)
  · exact Or.inr (by
      simpa [data', P, extractionFiniteLiftHom_subseq] using hnonzero)

/-- Pass stable extraction data to a further strictly monotone subsequence.

This is the bookkeeping step needed before the next diagonal extraction: the
large-spectrum coefficient limits can be refined to make additional formal
frequencies converge, and the eventual zero/nonzero relation stability used to
define the extraction quotient is preserved by that refinement. -/
noncomputable def StableExtendedLargeSpectrumCoeffLimitData.subseq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    StableExtendedLargeSpectrumCoeffLimitData S where
  toExtendedLargeSpectrumCoeffLimitData :=
    data.toExtendedLargeSpectrumCoeffLimitData.subseq ψ hψ
  finiteLift_eventually_stable := by
    intro g
    rcases data.finiteLift_eventually_stable g with hzero | hnonzero
    · exact Or.inl (by
        simpa [extractionFiniteLiftHom_subseq] using
          hψ.tendsto_atTop.eventually hzero)
    · exact Or.inr (by
        simpa [extractionFiniteLiftHom_subseq] using
          hψ.tendsto_atTop.eventually hnonzero)

/-- Stable extraction data plus coefficient limits for every formal frequency
in the free abelian group on the extended large-spectrum labels.

The labelled large-spectrum data gives limits only for the generators.  Fixed
Fejer kernels and trigonometric-polynomial counts use finite sums and
differences of those generators, so the compactness proof needs one more
diagonal subsequence making all such formal-frequency coefficients converge. -/
structure StableExtractionCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    extends StableExtendedLargeSpectrumCoeffLimitData S where
  fCoeffG : ExtractionFreeGroup → ℂ
  uCoeffG : ExtractionFreeGroup → ℂ
  fCoeffG_tendsto : ∀ g : ExtractionFreeGroup,
    Tendsto
      (fun n =>
        (letI : NeZero (S.p (toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
            ⟨(S.prime (toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.F (toExtendedLargeSpectrumCoeffLimitData.φ n))
            (extractionFiniteLiftHom toExtendedLargeSpectrumCoeffLimitData n g)))
      atTop (𝓝 (fCoeffG g))
  uCoeffG_tendsto : ∀ g : ExtractionFreeGroup,
    Tendsto
      (fun n =>
        (letI : NeZero (S.p (toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
            ⟨(S.prime (toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.U (toExtendedLargeSpectrumCoeffLimitData.φ n))
            (extractionFiniteLiftHom toExtendedLargeSpectrumCoeffLimitData n g)))
      atTop (𝓝 (uCoeffG g))
  fCoeffG_nonneg : ∀ g : ExtractionFreeGroup, 0 ≤ (fCoeffG g).re
  fCoeffG_im_eq_zero : ∀ g : ExtractionFreeGroup, (fCoeffG g).im = 0

theorem StableExtendedLargeSpectrumCoeffLimitData.exists_stableExtractionCoeffLimitData
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : StableExtendedLargeSpectrumCoeffLimitData S) :
    ∃ _data : StableExtractionCoeffLimitData S, True := by
  classical
  let base : ExtendedLargeSpectrumCoeffLimitData S :=
    data.toExtendedLargeSpectrumCoeffLimitData
  let a : Sum ExtractionFreeGroup ExtractionFreeGroup → ℕ → ℂ := fun tag n =>
    match tag with
    | Sum.inl g =>
        (letI : NeZero (S.p (base.φ n)) :=
            ⟨(S.prime (base.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.F (base.φ n))
            (extractionFiniteLiftHom base n g))
    | Sum.inr g =>
        (letI : NeZero (S.p (base.φ n)) :=
            ⟨(S.prime (base.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.U (base.φ n))
            (extractionFiniteLiftHom base n g))
  have ha : ∀ tag n, ‖a tag n‖ ≤ 1 := by
    intro tag n
    cases tag with
    | inl g =>
        dsimp [a]
        letI : NeZero (S.p (base.φ n)) :=
          ⟨(S.prime (base.φ n)).ne_zero⟩
        exact norm_normalizedDftCoeff_indicator_le_one
          (S.F (base.φ n)) (extractionFiniteLiftHom base n g)
    | inr g =>
        dsimp [a]
        letI : NeZero (S.p (base.φ n)) :=
          ⟨(S.prime (base.φ n)).ne_zero⟩
        exact norm_normalizedDftCoeff_indicator_le_one
          (S.U (base.φ n)) (extractionFiniteLiftHom base n g)
  rcases exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one a ha with
    ⟨ψ, hψ, hconv⟩
  let data' : StableExtendedLargeSpectrumCoeffLimitData S := data.subseq ψ hψ
  have hF : ∀ g : ExtractionFreeGroup, ∃ zF : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (S.p
              (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
              ⟨(S.prime
                (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
            normalizedDftCoeff
              (S.F (data'.toExtendedLargeSpectrumCoeffLimitData.φ n))
              (extractionFiniteLiftHom
                data'.toExtendedLargeSpectrumCoeffLimitData n g)))
        atTop (𝓝 zF) := by
    intro g
    rcases hconv (Sum.inl g) with ⟨zF, hzF⟩
    refine ⟨zF, ?_⟩
    simpa [a, base, data', StableExtendedLargeSpectrumCoeffLimitData.subseq,
      extractionFiniteLiftHom_subseq] using hzF
  have hU : ∀ g : ExtractionFreeGroup, ∃ zU : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (S.p
              (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
              ⟨(S.prime
                (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩;
            normalizedDftCoeff
              (S.U (data'.toExtendedLargeSpectrumCoeffLimitData.φ n))
              (extractionFiniteLiftHom
                data'.toExtendedLargeSpectrumCoeffLimitData n g)))
        atTop (𝓝 zU) := by
    intro g
    rcases hconv (Sum.inr g) with ⟨zU, hzU⟩
    refine ⟨zU, ?_⟩
    simpa [a, base, data', StableExtendedLargeSpectrumCoeffLimitData.subseq,
      extractionFiniteLiftHom_subseq] using hzU
  choose fCoeffG hfCoeffG using hF
  choose uCoeffG huCoeffG using hU
  refine ⟨{
    toStableExtendedLargeSpectrumCoeffLimitData := data'
    fCoeffG := fCoeffG
    uCoeffG := uCoeffG
    fCoeffG_tendsto := hfCoeffG
    uCoeffG_tendsto := huCoeffG
    fCoeffG_nonneg := ?_
    fCoeffG_im_eq_zero := ?_
  }, trivial⟩
  · intro g
    exact (complex_limit_re_nonneg_and_im_zero
      (S.eps_tendsto_zero.comp
        data'.toExtendedLargeSpectrumCoeffLimitData.strictMono_φ.tendsto_atTop)
      (hfCoeffG g)
      (Filter.Eventually.of_forall (fun n => by
        letI : NeZero (S.p
            (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime
            (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩
        exact S.F_fourier_lower
          (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)
          (extractionFiniteLiftHom
            data'.toExtendedLargeSpectrumCoeffLimitData n g)))
      (Filter.Eventually.of_forall (fun n => by
        letI : NeZero (S.p
            (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime
            (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩
        exact normalizedDftCoeff_im_eq_zero_of_symmetric
          (S.F_sym (data'.toExtendedLargeSpectrumCoeffLimitData.φ n))
          (extractionFiniteLiftHom
            data'.toExtendedLargeSpectrumCoeffLimitData n g)))).1
  · intro g
    exact (complex_limit_re_nonneg_and_im_zero
      (S.eps_tendsto_zero.comp
        data'.toExtendedLargeSpectrumCoeffLimitData.strictMono_φ.tendsto_atTop)
      (hfCoeffG g)
      (Filter.Eventually.of_forall (fun n => by
        letI : NeZero (S.p
            (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime
            (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩
        exact S.F_fourier_lower
          (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)
          (extractionFiniteLiftHom
            data'.toExtendedLargeSpectrumCoeffLimitData n g)))
      (Filter.Eventually.of_forall (fun n => by
        letI : NeZero (S.p
            (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)) :=
          ⟨(S.prime
            (data'.toExtendedLargeSpectrumCoeffLimitData.φ n)).ne_zero⟩
        exact normalizedDftCoeff_im_eq_zero_of_symmetric
          (S.F_sym (data'.toExtendedLargeSpectrumCoeffLimitData.φ n))
          (extractionFiniteLiftHom
            data'.toExtendedLargeSpectrumCoeffLimitData n g)))).2

theorem FourierAvoidanceCounterSeq.exists_stableExtractionCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) :
    ∃ _data : StableExtractionCoeffLimitData S, True := by
  rcases S.exists_stableExtendedLargeSpectrumCoeffLimitData with ⟨data, _⟩
  exact data.exists_stableExtractionCoeffLimitData

/-- Formal combinations whose finite lifts vanish eventually along the
selected subsequence. -/
def extractionEventualKernel
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    AddSubgroup ExtractionFreeGroup where
  carrier := {g | ∀ᶠ n in atTop, extractionFiniteLiftHom data n g = 0}
  zero_mem' := by
    simp
  add_mem' := by
    intro g h hg hh
    filter_upwards [hg, hh] with n hgn hhn
    simp [map_add, hgn, hhn]
  neg_mem' := by
    intro g hg
    filter_upwards [hg] with n hgn
    simp [hgn]

lemma mem_extractionEventualKernel_iff
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {g : ExtractionFreeGroup} :
    g ∈ extractionEventualKernel data ↔
      ∀ᶠ n in atTop, extractionFiniteLiftHom data n g = 0 :=
  Iff.rfl

/-- Discrete quotient group produced by the Route A extraction skeleton.  The
future compact group is its Pontryagin dual. -/
abbrev ExtractionDiscreteGroup
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) : Type :=
  ExtractionFreeGroup ⧸ extractionEventualKernel data

/-- Canonical map from labels to the extraction quotient. -/
noncomputable def extractionGenerator
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    ExtendedLargeSpectrumIndex → ExtractionDiscreteGroup data :=
  fun idx => QuotientAddGroup.mk (FreeAbelianGroup.of idx)

/-- Quotient equality for two formal combinations is exactly eventual equality
of their finite lifts. -/
lemma extractionQuotient_eq_iff_eventually_lift_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {g h : ExtractionFreeGroup} :
    (QuotientAddGroup.mk g : ExtractionDiscreteGroup data) =
        QuotientAddGroup.mk h ↔
      ∀ᶠ n in atTop, extractionFiniteLiftHom data n g =
        extractionFiniteLiftHom data n h := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp only [mem_extractionEventualKernel_iff, AddMonoidHom.map_sub, sub_eq_zero]

/-- Equality of two quotient generators is eventual equality of the
corresponding finite frequencies. -/
lemma extractionGenerator_eq_iff_eventually_freq_eq
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (idx jdx : ExtendedLargeSpectrumIndex) :
    extractionGenerator data idx = extractionGenerator data jdx ↔
      ∀ᶠ n in atTop,
        S.extendedLargeSpectrumIndexFreq (data.φ n) idx =
          S.extendedLargeSpectrumIndexFreq (data.φ n) jdx := by
  rw [extractionGenerator, extractionGenerator,
    extractionQuotient_eq_iff_eventually_lift_eq]
  simp [extractionFiniteLiftHom_apply_of]

/-- A quotient class is zero exactly when its finite lifts are eventually
zero. -/
lemma extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {g : ExtractionFreeGroup} :
    (QuotientAddGroup.mk g : ExtractionDiscreteGroup data) = 0 ↔
      ∀ᶠ n in atTop, extractionFiniteLiftHom data n g = 0 := by
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- The adjoined zero-frequency label is the zero element of the extraction
quotient. -/
lemma extractionGenerator_none_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S} :
    extractionGenerator data none = 0 := by
  rw [extractionGenerator]
  exact (extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
    (data := data)
    (g := FreeAbelianGroup.of (none : ExtendedLargeSpectrumIndex))).mpr (by
      simp [extractionFiniteLiftHom_apply_of,
        FourierAvoidanceCounterSeq.extendedLargeSpectrumIndexFreq])

/-- Multiplication by `q` in the extraction quotient is detected by eventual
multiplication by `q` on the finite lifts. -/
lemma extractionQuotient_nsmul_eq_zero_iff_eventually_lift_nsmul_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    (q : ℕ) {g : ExtractionFreeGroup} :
    q • (QuotientAddGroup.mk g : ExtractionDiscreteGroup data) = 0 ↔
      ∀ᶠ n in atTop, q • extractionFiniteLiftHom data n g = 0 := by
  rw [← QuotientAddGroup.mk_nsmul (extractionEventualKernel data) g q,
    extractionQuotient_eq_zero_iff_eventually_lift_eq_zero]
  simp [AddMonoidHom.map_nsmul]

lemma zmod_nsmul_eq_zero_iff_of_prime_not_dvd
    {p q : ℕ} [Fact p.Prime] (hnot : ¬ p ∣ q) (x : ZMod p) :
    q • x = 0 ↔ x = 0 := by
  have hunit : IsUnit (q : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnot).symm
  constructor
  · intro hx
    have hxmul : (q : ZMod p) * x = (q : ZMod p) * 0 := by
      simpa [nsmul_eq_mul] using hx
    exact hunit.mul_left_cancel hxmul
  · intro hx
    simp [hx]

lemma ExtendedLargeSpectrumCoeffLimitData.eventually_prime_gt
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) (q : ℕ) :
    ∀ᶠ n in atTop, q < S.p (data.φ n) := by
  rw [Filter.eventually_atTop]
  refine ⟨q + 1, ?_⟩
  intro n hn
  exact lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self q) hn)
    (S.p_ge (data.φ n) |>.trans' data.strictMono_φ.le_apply)

lemma extractionFiniteLift_eventually_eq_zero_of_eventually_nsmul_eq_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {data : ExtendedLargeSpectrumCoeffLimitData S}
    {q : ℕ} (hq : q ≠ 0) {g : ExtractionFreeGroup}
    (h : ∀ᶠ n in atTop, q • extractionFiniteLiftHom data n g = 0) :
    ∀ᶠ n in atTop, extractionFiniteLiftHom data n g = 0 := by
  filter_upwards [h, data.eventually_prime_gt q] with n hn hgt
  haveI : Fact (S.p (data.φ n)).Prime := ⟨S.prime (data.φ n)⟩
  have hnot : ¬ S.p (data.φ n) ∣ q :=
    Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hq) hgt
  exact (zmod_nsmul_eq_zero_iff_of_prime_not_dvd hnot
    (extractionFiniteLiftHom data n g)).mp hn

/-- The extraction quotient is torsion-free.  This is the algebraic core of
the compact-dual connectedness step: eventual finite lifts into groups of
larger and larger prime order rule out nonzero torsion in the quotient. -/
theorem extractionDiscreteGroup_isAddTorsionFree
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    (data : ExtendedLargeSpectrumCoeffLimitData S) :
    IsAddTorsionFree (ExtractionDiscreteGroup data) where
  nsmul_right_injective := by
    intro q hq x y hxy
    induction x using QuotientAddGroup.induction_on with
    | H g =>
      induction y using QuotientAddGroup.induction_on with
      | H h =>
        have hsub_q :
            q • (QuotientAddGroup.mk (g - h) :
                ExtractionDiscreteGroup data) = 0 := by
          rw [QuotientAddGroup.mk_sub]
          simp [nsmul_sub, hxy]
        have hlift_q :
            ∀ᶠ n in atTop,
              q • extractionFiniteLiftHom data n (g - h) = 0 :=
          (extractionQuotient_nsmul_eq_zero_iff_eventually_lift_nsmul_eq_zero
            (data := data) q).mp hsub_q
        have hlift :
            ∀ᶠ n in atTop, extractionFiniteLiftHom data n (g - h) = 0 :=
          extractionFiniteLift_eventually_eq_zero_of_eventually_nsmul_eq_zero
            (data := data) hq hlift_q
        have hsub :
            (QuotientAddGroup.mk (g - h) :
                ExtractionDiscreteGroup data) = 0 :=
          (extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
            (data := data)).mpr hlift
        rw [QuotientAddGroup.mk_sub] at hsub
        exact sub_eq_zero.mp hsub

end Erdos42.FourierPositive
