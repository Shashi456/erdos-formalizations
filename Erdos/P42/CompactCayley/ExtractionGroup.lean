/-
Erdős Problem 42 — compact-Cayley extraction quotient skeleton.

This file implements the formal free-abelian word lifts and the eventual-kernel
quotient used by the compact dual construction.  It intentionally stops before
the diagonal stability layer: without eventual zero/nonzero stabilization one
can define the quotient and its basic equality API, but not yet prove the
finite-lift injectivity-on-finite-sets facts needed later.
-/

import Erdos.P42.CompactCayley.FourierExtraction

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Classical Topology

/-- Formal integer combinations of compact-Cayley large-spectrum labels. -/
abbrev ExtractionFreeGroup : Type :=
  FreeAbelianGroup LargeLabel

instance extractionFreeGroupCountable : Countable ExtractionFreeGroup := by
  dsimp [ExtractionFreeGroup, LargeLabel]
  infer_instance

/-- Finite lift homomorphism of a formal label combination to the `n`-th
cyclic group. -/
noncomputable def FourierSeq.wordLiftHom
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (n : ℕ) :
    ExtractionFreeGroup →+ ZMod (F.p n) :=
  FreeAbelianGroup.lift fun label : LargeLabel => labelFreq label n

/-- Finite lift of a formal label combination. -/
noncomputable def FourierSeq.wordLift
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w : ExtractionFreeGroup) (n : ℕ) :
    ZMod (F.p n) :=
  F.wordLiftHom labelFreq n w

lemma FourierSeq.wordLiftHom_apply_of
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (n : ℕ) (label : LargeLabel) :
    F.wordLiftHom labelFreq n (FreeAbelianGroup.of label) =
      labelFreq label n := by
  simp [FourierSeq.wordLiftHom]

lemma FourierSeq.wordLift_add
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w v : ExtractionFreeGroup) (n : ℕ) :
    F.wordLift labelFreq (w + v) n =
      F.wordLift labelFreq w n + F.wordLift labelFreq v n := by
  simp [FourierSeq.wordLift]

lemma FourierSeq.wordLift_neg
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w : ExtractionFreeGroup) (n : ℕ) :
    F.wordLift labelFreq (-w) n =
      -F.wordLift labelFreq w n := by
  simp [FourierSeq.wordLift]

/-- Formal combinations whose finite lifts vanish eventually. -/
def FourierSeq.eventualKernel
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    AddSubgroup ExtractionFreeGroup where
  carrier := {w | ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0}
  zero_mem' := by
    simp [FourierSeq.wordLift]
  add_mem' := by
    intro w v hw hv
    filter_upwards [hw, hv] with n hwn hvn
    simp [FourierSeq.wordLift_add, hwn, hvn]
  neg_mem' := by
    intro w hw
    filter_upwards [hw] with n hwn
    simp [FourierSeq.wordLift_neg, hwn]

lemma FourierSeq.mem_eventualKernel_iff
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w : ExtractionFreeGroup} :
    w ∈ F.eventualKernel labelFreq ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0 :=
  Iff.rfl

/-- Discrete quotient group produced by the compact-Cayley extraction
skeleton.  Its Pontryagin dual is the future compact limit group. -/
abbrev FourierSeq.ExtractionGroup
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) : Type :=
  ExtractionFreeGroup ⧸ F.eventualKernel labelFreq

instance FourierSeq.extractionGroupAddCommGroup
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    AddCommGroup (F.ExtractionGroup labelFreq) :=
  inferInstance

instance FourierSeq.extractionGroupCountable
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    Countable (F.ExtractionGroup labelFreq) :=
  (QuotientAddGroup.mk'_surjective (F.eventualKernel labelFreq)).countable

/-- Canonical quotient class of a large-spectrum label. -/
noncomputable def FourierSeq.extractionGenerator
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    LargeLabel → F.ExtractionGroup labelFreq :=
  fun label => QuotientAddGroup.mk (FreeAbelianGroup.of label)

/-- Quotient equality is exactly eventual equality of finite lifts. -/
lemma FourierSeq.extractionQuotient_eq_iff_eventually_lift_eq
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w v : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : F.ExtractionGroup labelFreq) =
        QuotientAddGroup.mk v ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n =
        F.wordLift labelFreq v n := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp only [FourierSeq.mem_eventualKernel_iff, AddMonoidHom.map_sub,
    FourierSeq.wordLift, sub_eq_zero]

/-- A quotient class is zero exactly when its finite lifts are eventually zero. -/
lemma FourierSeq.extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : F.ExtractionGroup labelFreq) = 0 ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0 := by
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- Equality of two quotient generators is eventual equality of their labelled
finite frequencies. -/
lemma FourierSeq.extractionGenerator_eq_iff_eventually_freq_eq
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (label label' : LargeLabel) :
    F.extractionGenerator labelFreq label =
        F.extractionGenerator labelFreq label' ↔
      ∀ᶠ n in atTop, labelFreq label n = labelFreq label' n := by
  rw [FourierSeq.extractionGenerator, FourierSeq.extractionGenerator,
    FourierSeq.extractionQuotient_eq_iff_eventually_lift_eq]
  simp [FourierSeq.wordLiftHom_apply_of, FourierSeq.wordLift]

end Erdos42.CompactCayley
