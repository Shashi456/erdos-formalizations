/-
Erdős Problem 42 — finite lifts from the compact-Cayley extraction quotient.

Stable extraction data selects a subsequence.  The quotient group used later is
the extraction quotient of that subsequenced `FourierSeq`; finite lifts of
quotient elements use arbitrary representatives, so all algebraic facts are
recorded as eventual statements.
-/

import Erdos.P42.CompactCayley.StableExtraction

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Classical Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

/-- The Fourier sequence after applying the stable extraction subsequence. -/
def seq (data : F.StableSubseqData labelFreq) : FourierSeq :=
  F.subseq data.φ data.strictMono_φ

/-- The label frequencies transported to the stable extraction subsequence. -/
def subseqLabelFreq (data : F.StableSubseqData labelFreq) :
    LargeLabel → ∀ n, ZMod ((data.seq).p n) :=
  F.subseqLabelFreq labelFreq data.φ data.strictMono_φ

/-- The discrete extraction quotient attached to stable compact-Cayley data. -/
abbrev Group (data : F.StableSubseqData labelFreq) : Type :=
  (data.seq).ExtractionGroup data.subseqLabelFreq

instance (data : F.StableSubseqData labelFreq) :
    Countable data.Group :=
  FourierSeq.extractionGroupCountable data.seq data.subseqLabelFreq

/-- Finite lift homomorphism for formal words along the stable subsequence. -/
noncomputable def finiteLiftHom
    (data : F.StableSubseqData labelFreq) (n : ℕ) :
    ExtractionFreeGroup →+ ZMod (F.p (data.φ n)) :=
  (data.seq).wordLiftHom data.subseqLabelFreq n

lemma finiteLiftHom_apply
    (data : F.StableSubseqData labelFreq) (n : ℕ)
    (w : ExtractionFreeGroup) :
    data.finiteLiftHom n w = F.wordLift labelFreq w (data.φ n) := by
  rfl

/-- Chosen finite lift of a quotient frequency. -/
noncomputable def finiteLift
    (data : F.StableSubseqData labelFreq) (n : ℕ)
    (γ : data.Group) :
    ZMod (F.p (data.φ n)) :=
  data.finiteLiftHom n (Quotient.out γ)

/-- Quotient equality is eventual equality of chosen finite lifts of formal
representatives, along the stable subsequence. -/
lemma quotient_eq_iff_eventually_lift_eq
    (data : F.StableSubseqData labelFreq)
    {w v : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : data.Group) = QuotientAddGroup.mk v ↔
      ∀ᶠ n in atTop, data.finiteLiftHom n w = data.finiteLiftHom n v := by
  rw [FourierSeq.extractionQuotient_eq_iff_eventually_lift_eq
    (F := data.seq) (labelFreq := data.subseqLabelFreq)]
  rfl

/-- A quotient class is zero exactly when its representative lift vanishes
eventually. -/
lemma quotient_eq_zero_iff_eventually_lift_eq_zero
    (data : F.StableSubseqData labelFreq)
    {w : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : data.Group) = 0 ↔
      ∀ᶠ n in atTop, data.finiteLiftHom n w = 0 := by
  rw [FourierSeq.extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
    (F := data.seq) (labelFreq := data.subseqLabelFreq)]
  rfl

/-- A chosen quotient representative has the same finite lift as any specified
representative of the same quotient class, eventually. -/
lemma finiteLift_mk_eventually_eq
    (data : F.StableSubseqData labelFreq) (w : ExtractionFreeGroup) :
    ∀ᶠ n in atTop,
      data.finiteLift n (QuotientAddGroup.mk w : data.Group) =
        data.finiteLiftHom n w := by
  exact (data.quotient_eq_iff_eventually_lift_eq
    (w := Quotient.out (QuotientAddGroup.mk w : data.Group)) (v := w)).mp
    (Quotient.out_eq _)

lemma finiteLift_zero_eventually_eq_zero
    (data : F.StableSubseqData labelFreq) :
    ∀ᶠ n in atTop, data.finiteLift n (0 : data.Group) = 0 := by
  simpa [finiteLift] using
    (data.quotient_eq_zero_iff_eventually_lift_eq_zero
      (w := Quotient.out (0 : data.Group))).mp
      (Quotient.out_eq (0 : data.Group))

lemma finiteLift_add_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ δ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (γ + δ) =
        data.finiteLift n γ + data.finiteLift n δ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (γ + δ)) : data.Group) =
        QuotientAddGroup.mk (Quotient.out γ + Quotient.out δ) := by
    simp [Quotient.out_eq γ, Quotient.out_eq δ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (γ + δ))
      (v := Quotient.out γ + Quotient.out δ)).mp hquot] with n hn
  rw [finiteLift, hn]
  simp [finiteLift, finiteLiftHom]

lemma finiteLift_neg_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (-γ) = -data.finiteLift n γ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (-γ)) : data.Group) =
        QuotientAddGroup.mk (-Quotient.out γ) := by
    simp [Quotient.out_eq γ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (-γ)) (v := -Quotient.out γ)).mp hquot] with n hn
  rw [finiteLift, hn]
  simp [finiteLift, finiteLiftHom]

lemma finiteLift_sub_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ δ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (γ - δ) =
        data.finiteLift n γ - data.finiteLift n δ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (γ - δ)) : data.Group) =
        QuotientAddGroup.mk (Quotient.out γ - Quotient.out δ) := by
    simp [Quotient.out_eq γ, Quotient.out_eq δ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (γ - δ))
      (v := Quotient.out γ - Quotient.out δ)).mp hquot] with n hn
  rw [finiteLift, hn]
  simp [finiteLift, finiteLiftHom]

lemma finiteLift_sum_eventually_eq
    (data : F.StableSubseqData labelFreq)
    {ι : Type*} (s : Finset ι) (f : ι → data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (∑ i ∈ s, f i) =
        ∑ i ∈ s, data.finiteLift n (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · filter_upwards [data.finiteLift_zero_eventually_eq_zero] with n hzero
    simpa using hzero
  · intro a s ha ih
    filter_upwards
      [ih, data.finiteLift_add_eventually_eq (f a) (∑ i ∈ s, f i)] with n hsum hadd
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsum]

lemma finiteLift_sum_univ_eventually_eq
    (data : F.StableSubseqData labelFreq)
    {ι : Type*} [Fintype ι] (f : ι → data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (∑ i, f i) =
        ∑ i, data.finiteLift n (f i) := by
  simpa using data.finiteLift_sum_eventually_eq (Finset.univ : Finset ι) f

lemma finiteLift_eq_of_eq_eventually
    (data : F.StableSubseqData labelFreq)
    {γ δ : data.Group} (h : γ = δ) :
    ∀ᶠ n in atTop, data.finiteLift n γ = data.finiteLift n δ := by
  subst h
  exact Eventually.of_forall fun _ => rfl

/-- Nonzero quotient elements have nonzero finite lifts eventually. -/
lemma finiteLift_eventually_ne_zero
    (data : F.StableSubseqData labelFreq)
    {γ : data.Group} (hγ : γ ≠ 0) :
    ∀ᶠ n in atTop, data.finiteLift n γ ≠ 0 := by
  rcases data.finiteLift_eventually_stable (Quotient.out γ) with hzero | hnonzero
  · have hγ0 : γ = 0 := by
      have hmk :
          (QuotientAddGroup.mk (Quotient.out γ) : data.Group) = 0 :=
        (data.quotient_eq_zero_iff_eventually_lift_eq_zero
          (w := Quotient.out γ)).mpr (by
            simpa [finiteLiftHom_apply] using hzero)
      simpa [Quotient.out_eq γ] using hmk
    exact (hγ hγ0).elim
  · simpa [finiteLift, finiteLiftHom_apply] using hnonzero

/-- Distinct quotient elements have distinct finite lifts eventually. -/
lemma finiteLift_eventually_ne_of_ne
    (data : F.StableSubseqData labelFreq)
    {γ δ : data.Group} (hγδ : γ ≠ δ) :
    ∀ᶠ n in atTop, data.finiteLift n γ ≠ data.finiteLift n δ := by
  have hsub : γ - δ ≠ 0 := sub_ne_zero.mpr hγδ
  filter_upwards
    [data.finiteLift_eventually_ne_zero hsub,
      data.finiteLift_sub_eventually_eq γ δ] with n hn hsubeq heq
  exact hn (by simpa [heq] using hsubeq)

/-- The finite lift is eventually injective on any fixed finite subset of the
extraction quotient. -/
lemma finiteLift_eventually_injOn_finset
    (data : F.StableSubseqData labelFreq) (Q : Finset data.Group) :
    ∀ᶠ n in atTop,
      Set.InjOn (fun γ => data.finiteLift n γ) (Q : Set data.Group) := by
  classical
  have hpairs :
      ∀ᶠ n in atTop, ∀ pair ∈ Q.product Q,
        pair.1 ≠ pair.2 →
          data.finiteLift n pair.1 ≠ data.finiteLift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hmem
    by_cases hp : pair.1 = pair.2
    · exact Eventually.of_forall fun _ hne => (hne hp).elim
    · exact (data.finiteLift_eventually_ne_of_ne hp).mono
        (fun _ hn _hne => hn)
  filter_upwards [hpairs] with n hn γ hγ δ hδ heq
  by_contra hne
  have hpair : (γ, δ) ∈ Q.product Q := Finset.mem_product.mpr ⟨hγ, hδ⟩
  exact (hn (γ, δ) hpair hne) heq

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley
