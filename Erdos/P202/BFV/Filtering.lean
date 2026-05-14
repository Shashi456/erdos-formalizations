/-
Erdos Problem 202 -- finite filtering helpers for BFV pruning.

These lemmas are deliberately elementary.  They isolate the finite-set
bookkeeping used by the pruning step from the analytic BFV estimates.
-/

import Mathlib

namespace Erdos202

open Finset
open scoped BigOperators

/-! ## Removing a small bad set -/

lemma filter_card_add_filter_not_card {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  classical
  exact Finset.card_filter_add_card_filter_not p

lemma filter_not_card_real_ge_of_filter_card_real_le {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] {δ : ℝ}
    (hbad : ((s.filter p).card : ℝ) ≤ δ * (s.card : ℝ)) :
    ((s.filter fun x => ¬ p x).card : ℝ) ≥ (1 - δ) * (s.card : ℝ) := by
  classical
  have hsum := filter_card_add_filter_not_card s p
  have hreal :
      ((s.filter fun x => ¬ p x).card : ℝ) =
        (s.card : ℝ) - ((s.filter p).card : ℝ) := by
    nlinarith [show ((s.filter p).card + (s.filter fun x => ¬ p x).card : ℝ) =
      (s.card : ℝ) by exact_mod_cast hsum]
  rw [hreal]
  nlinarith

lemma filter_not_card_real_ge_of_filter_card_le_floor {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] {δ X : ℝ}
    (hXnonneg : 0 ≤ X)
    (hfloor : (s.filter p).card ≤ Nat.floor X)
    (hX : X ≤ δ * (s.card : ℝ)) :
    ((s.filter fun x => ¬ p x).card : ℝ) ≥ (1 - δ) * (s.card : ℝ) := by
  refine filter_not_card_real_ge_of_filter_card_real_le s p ?_
  have hfloor_real : ((s.filter p).card : ℝ) ≤ (Nat.floor X : ℝ) := by
    exact_mod_cast hfloor
  have hfloor_le : (Nat.floor X : ℝ) ≤ X := Nat.floor_le hXnonneg
  exact hfloor_real.trans (hfloor_le.trans hX)

lemma filter_large_of_bad_small {α : Type*} [DecidableEq α]
    (Q Bad : Finset α) {δ : ℝ}
    (hBad : Bad ⊆ Q)
    (hsmall : (Bad.card : ℝ) ≤ δ * (Q.card : ℝ)) :
    (((Q \ Bad).card : ℝ) ≥ (1 - δ) * (Q.card : ℝ)) := by
  have hreal : ((Q \ Bad).card : ℝ) = (Q.card : ℝ) - (Bad.card : ℝ) := by
    simpa using (Finset.cast_card_sdiff (R := ℝ) hBad)
  rw [hreal]
  nlinarith

lemma filter_large_of_three_bad_small {α : Type*} [DecidableEq α]
    (Q Bad₁ Bad₂ Bad₃ : Finset α) {δ₁ δ₂ δ₃ : ℝ}
    (hBad₁ : Bad₁ ⊆ Q) (hBad₂ : Bad₂ ⊆ Q) (hBad₃ : Bad₃ ⊆ Q)
    (hsmall₁ : (Bad₁.card : ℝ) ≤ δ₁ * (Q.card : ℝ))
    (hsmall₂ : (Bad₂.card : ℝ) ≤ δ₂ * (Q.card : ℝ))
    (hsmall₃ : (Bad₃.card : ℝ) ≤ δ₃ * (Q.card : ℝ)) :
    (((Q \ (Bad₁ ∪ Bad₂ ∪ Bad₃)).card : ℝ) ≥
      (1 - (δ₁ + δ₂ + δ₃)) * (Q.card : ℝ)) := by
  have hBad : Bad₁ ∪ Bad₂ ∪ Bad₃ ⊆ Q := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx12 | hx3
    · rcases Finset.mem_union.1 hx12 with hx1 | hx2
      · exact hBad₁ hx1
      · exact hBad₂ hx2
    · exact hBad₃ hx3
  refine filter_large_of_bad_small Q (Bad₁ ∪ Bad₂ ∪ Bad₃) hBad ?_
  have hcard_nat :
      (Bad₁ ∪ Bad₂ ∪ Bad₃).card ≤ Bad₁.card + Bad₂.card + Bad₃.card := by
    calc
      (Bad₁ ∪ Bad₂ ∪ Bad₃).card
          ≤ (Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
      _ ≤ (Bad₁.card + Bad₂.card) + Bad₃.card := by
            exact Nat.add_le_add_right (Finset.card_union_le Bad₁ Bad₂) Bad₃.card
      _ = Bad₁.card + Bad₂.card + Bad₃.card := by omega
  have hcard_real :
      ((Bad₁ ∪ Bad₂ ∪ Bad₃).card : ℝ) ≤
        (Bad₁.card : ℝ) + (Bad₂.card : ℝ) + (Bad₃.card : ℝ) := by
    exact_mod_cast hcard_nat
  nlinarith

/-! ## Pigeonhole over a finite range -/

lemma exists_fiber_card_mul_range_card_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (B : Finset β) (g : α → β)
    (hBne : B.Nonempty) (hB : ∀ x ∈ s, g x ∈ B) :
    ∃ b ∈ B, s.card ≤ B.card * (s.filter fun x => g x = b).card := by
  classical
  rcases Finset.exists_max_image B (fun b => (s.filter fun x => g x = b).card) hBne with
    ⟨b, hb, hbmax⟩
  refine ⟨b, hb, ?_⟩
  have hsum :
      s.card = ∑ b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.card_eq_sum_card_fiberwise hB
  have hsum_le :
      (∑ b ∈ B, (s.filter fun x => g x = b).card) ≤
        ∑ _b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.sum_le_sum hbmax
  rw [hsum]
  exact hsum_le.trans (by simp)

/-! ## Choosing one representative per fiber -/

noncomputable def chooseOnePerImage {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) : Finset α :=
  ((s.image g).attach.image fun b =>
    Classical.choose (Finset.mem_image.1 b.2))

lemma chooseOnePerImage_subset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    chooseOnePerImage s g ⊆ s := by
  classical
  intro x hx
  unfold chooseOnePerImage at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨b, -, rfl⟩
  exact (Classical.choose_spec (Finset.mem_image.1 b.2)).1

lemma chooseOnePerImage_maps {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) {b : β} (hb : b ∈ s.image g) :
    g (Classical.choose (Finset.mem_image.1 hb)) = b := by
  exact (Classical.choose_spec (Finset.mem_image.1 hb)).2

lemma chooseOnePerImage_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    ∀ x ∈ chooseOnePerImage s g, ∀ y ∈ chooseOnePerImage s g, g x = g y → x = y := by
  classical
  intro x hx y hy hxy
  unfold chooseOnePerImage at hx hy
  rw [Finset.mem_image] at hx
  rw [Finset.mem_image] at hy
  rcases hx with ⟨bx, hbx, rfl⟩
  rcases hy with ⟨byy, hby, rfl⟩
  have hbxval : g (Classical.choose (Finset.mem_image.1 bx.2)) = bx.1 := by
    exact chooseOnePerImage_maps s g bx.2
  have hbyval : g (Classical.choose (Finset.mem_image.1 byy.2)) = byy.1 := by
    exact chooseOnePerImage_maps s g byy.2
  have hbxy : bx = byy := by
    ext
    simpa [hbxval, hbyval] using hxy
  subst hbxy
  rfl

lemma chooseOnePerImage_card_eq_image_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    (chooseOnePerImage s g).card = (s.image g).card := by
  classical
  unfold chooseOnePerImage
  calc
    (((s.image g).attach.image fun b =>
        Classical.choose (Finset.mem_image.1 b.2))).card =
        (s.image g).attach.card := by
          apply Finset.card_image_of_injective
          intro b₁ b₂ h
          have hb₁ : g (Classical.choose (Finset.mem_image.1 b₁.2)) = b₁.1 :=
            chooseOnePerImage_maps s g b₁.2
          have hb₂ : g (Classical.choose (Finset.mem_image.1 b₂.2)) = b₂.1 :=
            chooseOnePerImage_maps s g b₂.2
          ext
          simpa [hb₁, hb₂] using congrArg g h
    _ = (s.image g).card := by simp

lemma image_card_mul_fiber_bound_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (g : α → β) (C : ℕ)
    (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
    s.card ≤ C * (s.image g).card := by
  classical
  exact Finset.card_le_mul_card_image s C hC

lemma choose_one_per_fiber_card_lower {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) (C : ℕ)
    (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
    ∃ s' : Finset α,
      s' ⊆ s ∧
      (∀ x ∈ s', ∀ y ∈ s', g x = g y → x = y) ∧
      s.card ≤ C * s'.card := by
  classical
  refine ⟨chooseOnePerImage s g, chooseOnePerImage_subset s g,
    chooseOnePerImage_injOn s g, ?_⟩
  simpa [chooseOnePerImage_card_eq_image_card s g] using
    image_card_mul_fiber_bound_ge s g C hC

end Erdos202
