/-
Erdős Problem 42 — compact-Cayley diagonal extraction data.

The free-abelian extraction group from `ExtractionGroup` only becomes useful
after passing to a subsequence where every formal finite-lift zero relation is
eventually stable and every formal Fourier coefficient converges.  This file
packages that diagonal step for a generic `FourierSeq`.
-/

import Erdos.P42.CompactCayley.ExtractionGroup

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Classical Topology

noncomputable section

/-- Closed unit disk, used as a compact target for countable diagonal
subsequence extraction. -/
abbrev ClosedUnitDisk : Type :=
  {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) 1}

lemma compactSpace_closedUnitDisk : CompactSpace ClosedUnitDisk := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    ProperSpace.isCompact_closedBall (0 : ℂ) 1
  exact isCompact_iff_compactSpace.mp hK

lemma exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one
    {ι : Type*} [Countable ι] (a : ι → ℕ → ℂ)
    (ha : ∀ i n, ‖a i n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, ∃ z : ℂ,
        Tendsto (fun n => a i (φ n)) atTop (𝓝 z) := by
  let x : ℕ → (ι → ClosedUnitDisk) := fun n i =>
    ⟨a i n, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact ha i n⟩
  letI : CompactSpace ClosedUnitDisk := compactSpace_closedUnitDisk
  rcases CompactSpace.tendsto_subseq x with ⟨y, φ, hφ, hlim⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  refine ⟨(y i : ℂ), ?_⟩
  have hcont :
      Continuous (fun y : ι → ClosedUnitDisk => ((y i : ClosedUnitDisk) : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have hi := (hcont.tendsto y).comp hlim
  simpa [x] using hi

/-- Countable diagonal stabilization for decidable relations.  This is the
relation-theoretic companion to coefficient convergence: after passing to one
subsequence, every countably indexed yes/no relation is eventually constantly
true or eventually constantly false. -/
lemma exists_strictMono_subseq_eventually_const_countable_family
    {ι : Type*} [Countable ι] (P : ι → ℕ → Prop)
    [∀ i n, Decidable (P i n)] :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, (∀ᶠ n in atTop, P i (φ n)) ∨
        (∀ᶠ n in atTop, ¬ P i (φ n)) := by
  let x : ℕ → (ι → Bool) := fun n i => decide (P i n)
  rcases CompactSpace.tendsto_subseq x with ⟨y, φ, hφ, hlim⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  have hcont : Continuous (fun y : ι → Bool => y i) := continuous_apply i
  have hi : Tendsto (fun n => x (φ n) i) atTop (𝓝 (y i)) :=
    (hcont.tendsto y).comp hlim
  have hmem : ({y i} : Set Bool) ∈ 𝓝 (y i) := by
    exact (isOpen_discrete ({y i} : Set Bool)).mem_nhds rfl
  have heq : ∀ᶠ n in atTop, x (φ n) i = y i := by
    simpa using hi.eventually hmem
  cases hy : y i <;> simp [x, hy] at heq ⊢
  · exact Or.inr heq
  · exact Or.inl heq

/-- Relabel a label-frequency assignment after passing a `FourierSeq` to a
subsequence. -/
def FourierSeq.subseqLabelFreq
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    LargeLabel → ∀ n, ZMod ((F.subseq φ hφ).p n) :=
  fun label n => labelFreq label (φ n)

lemma FourierSeq.wordLift_subseq
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (w : ExtractionFreeGroup) (n : ℕ) :
    (F.subseq φ hφ).wordLift (F.subseqLabelFreq labelFreq φ hφ) w n =
      F.wordLift labelFreq w (φ n) := by
  rfl

/-- A fully diagonalized compact-Cayley Fourier extraction package for a fixed
label-frequency assignment.

The subsequence `φ` is still recorded explicitly because later Cayley
specialization will pass the whole counterexample sequence through the same
subsequence. -/
structure FourierSeq.StableSubseqData
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) where
  φ : ℕ → ℕ
  strictMono_φ : StrictMono φ
  finiteLift_eventually_stable : ∀ w : ExtractionFreeGroup,
    (∀ᶠ n in atTop, F.wordLift labelFreq w (φ n) = 0) ∨
      (∀ᶠ n in atTop, F.wordLift labelFreq w (φ n) ≠ 0)
  coeffLimit : ExtractionFreeGroup → ℂ
  coeffLimit_tendsto : ∀ w : ExtractionFreeGroup,
    Tendsto
      (fun n =>
        letI : NeZero (F.p (φ n)) := ⟨(F.prime (φ n)).ne_zero⟩;
        F.coeff (φ n) (F.wordLift labelFreq w (φ n)))
      atTop (𝓝 (coeffLimit w))

/-- Countable diagonal extraction for all formal finite-lift zero relations
and all formal Fourier coefficients. -/
theorem FourierSeq.exists_stableSubseqData
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    ∃ _data : F.StableSubseqData labelFreq, True := by
  classical
  let P : ExtractionFreeGroup → ℕ → Prop :=
    fun w n => F.wordLift labelFreq w n = 0
  rcases
      exists_strictMono_subseq_eventually_const_countable_family
        P with
    ⟨φ, hφ, hstable⟩
  let a : ExtractionFreeGroup → ℕ → ℂ := fun w n =>
    letI : NeZero (F.p (φ n)) := ⟨(F.prime (φ n)).ne_zero⟩
    F.coeff (φ n) (F.wordLift labelFreq w (φ n))
  have ha : ∀ w n, ‖a w n‖ ≤ 1 := by
    intro w n
    dsimp [a]
    exact F.norm_coeff_le_one (φ n) (F.wordLift labelFreq w (φ n))
  rcases
      exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one
        a ha with
    ⟨ψ, hψ, hconv⟩
  have hstrict : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hstable' : ∀ w : ExtractionFreeGroup,
      (∀ᶠ n in atTop, F.wordLift labelFreq w ((φ ∘ ψ) n) = 0) ∨
        (∀ᶠ n in atTop, F.wordLift labelFreq w ((φ ∘ ψ) n) ≠ 0) := by
    intro w
    rcases hstable w with hzero | hnonzero
    · exact Or.inl (by
        simpa [P, Function.comp_def] using hψ.tendsto_atTop.eventually hzero)
    · exact Or.inr (by
        simpa [P, Function.comp_def] using hψ.tendsto_atTop.eventually hnonzero)
  have hcoeff : ∀ w : ExtractionFreeGroup, ∃ z : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (F.p ((φ ∘ ψ) n)) :=
              ⟨(F.prime ((φ ∘ ψ) n)).ne_zero⟩;
            F.coeff ((φ ∘ ψ) n)
              (F.wordLift labelFreq w ((φ ∘ ψ) n))))
        atTop (𝓝 z) := by
    intro w
    rcases hconv w with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [a, Function.comp_def] using hz
  choose coeffLimit hcoeffLimit using hcoeff
  refine ⟨{
    φ := φ ∘ ψ
    strictMono_φ := hstrict
    finiteLift_eventually_stable := hstable'
    coeffLimit := coeffLimit
    coeffLimit_tendsto := hcoeffLimit
  }, trivial⟩

end

end Erdos42.CompactCayley
