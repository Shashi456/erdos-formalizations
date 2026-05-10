/-
Erdős Problem 42 — finite Følner overlap infrastructure.

This file isolates the finite pair-count lower bound from the extraction
structure.  The later constructive box estimate can then be proved in a
standard free abelian model and transported back to finite generated
subgroups of the extraction group.
-/

import Erdos.P42.CompactCayley.Fejer
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Finiteness.Defs

namespace Erdos42.CompactCayley

open scoped BigOperators Classical

noncomputable section

namespace PairCoeffLowerBound

variable {G H : Type*} [AddGroup G] [AddGroup H]

def addEquivEmbedding (e : G ≃+ H) : G ↪ H :=
  e.toEquiv.toEmbedding

def addMonoidHomEmbedding (f : G →+ H) (hf : Function.Injective f) : G ↪ H where
  toFun := f
  inj' := hf

private def addEquivPairEmbedding (e : G ≃+ H) : G × G ↪ H × H where
  toFun pair := (e pair.1, e pair.2)
  inj' := by
    intro pair pair' hpair
    exact Prod.ext
      (e.injective (congrArg Prod.fst hpair))
      (e.injective (congrArg Prod.snd hpair))

lemma pairFiber_card_map_addEquiv
    (e : G ≃+ H) (Q : Finset G) (γ : G) :
    (pairFiber (Q.map (addEquivEmbedding e))
        ((addEquivEmbedding e) γ)).card =
      (pairFiber Q γ).card := by
  classical
  have hleft :
      pairFiber (Q.map (addEquivEmbedding e)) ((addEquivEmbedding e) γ) =
        ((Q.map (addEquivEmbedding e)).product
          (Q.map (addEquivEmbedding e))).filter
          (fun pair : H × H => pair.1 - pair.2 =
            (addEquivEmbedding e) γ) := by
    ext pair
    simp [pairFiber]
  have hright :
      pairFiber Q γ =
        (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
    ext pair
    simp [pairFiber]
  rw [hleft, hright]
  symm
  apply Finset.card_bij (fun pair _hpair => (e pair.1, e pair.2))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    rw [Finset.mem_filter]
    constructor
    · apply Finset.mem_product.mpr
      have hprod := Finset.mem_product.mp hpair.1
      exact
        ⟨Finset.mem_map.mpr ⟨pair.1, hprod.1, rfl⟩,
          Finset.mem_map.mpr ⟨pair.2, hprod.2, rfl⟩⟩
    · have hdiff : e (pair.1 - pair.2) = e γ := congrArg e hpair.2
      simpa [e.map_sub] using hdiff
  · intro pair _hpair pair' _hpair' h
    exact Prod.ext
      (e.injective (congrArg Prod.fst h))
      (e.injective (congrArg Prod.snd h))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    have hprod := Finset.mem_product.mp hpair.1
    rcases Finset.mem_map.mp hprod.1 with ⟨a, haQ, ha⟩
    rcases Finset.mem_map.mp hprod.2 with ⟨b, hbQ, hb⟩
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨haQ, hbQ⟩
      · have hdiff :
            (addEquivEmbedding e) (a - b) = (addEquivEmbedding e) γ := by
          have htarget :
              (addEquivEmbedding e) a - (addEquivEmbedding e) b =
                (addEquivEmbedding e) γ := by
            rw [ha, hb]
            exact hpair.2
          simpa [addEquivEmbedding, e.map_sub] using htarget
        exact e.injective (by simpa [addEquivEmbedding] using hdiff)
    · exact Prod.ext ha hb

lemma pairFiber_card_map_addMonoidHom_of_injective
    (f : G →+ H) (hf : Function.Injective f) (Q : Finset G) (γ : G) :
    (pairFiber (Q.map (addMonoidHomEmbedding f hf))
        ((addMonoidHomEmbedding f hf) γ)).card =
      (pairFiber Q γ).card := by
  classical
  have hleft :
      pairFiber (Q.map (addMonoidHomEmbedding f hf))
          ((addMonoidHomEmbedding f hf) γ) =
        ((Q.map (addMonoidHomEmbedding f hf)).product
          (Q.map (addMonoidHomEmbedding f hf))).filter
          (fun pair : H × H => pair.1 - pair.2 =
            (addMonoidHomEmbedding f hf) γ) := by
    ext pair
    simp [pairFiber]
  have hright :
      pairFiber Q γ =
        (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
    ext pair
    simp [pairFiber]
  rw [hleft, hright]
  symm
  apply Finset.card_bij (fun pair _hpair => (f pair.1, f pair.2))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    rw [Finset.mem_filter]
    constructor
    · apply Finset.mem_product.mpr
      have hprod := Finset.mem_product.mp hpair.1
      exact
        ⟨Finset.mem_map.mpr ⟨pair.1, hprod.1, rfl⟩,
          Finset.mem_map.mpr ⟨pair.2, hprod.2, rfl⟩⟩
    · have hdiff : f (pair.1 - pair.2) = f γ := congrArg f hpair.2
      simpa [addMonoidHomEmbedding] using hdiff
  · intro pair _hpair pair' _hpair' h
    exact Prod.ext
      (hf (congrArg Prod.fst h))
      (hf (congrArg Prod.snd h))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    have hprod := Finset.mem_product.mp hpair.1
    rcases Finset.mem_map.mp hprod.1 with ⟨a, haQ, ha⟩
    rcases Finset.mem_map.mp hprod.2 with ⟨b, hbQ, hb⟩
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨haQ, hbQ⟩
      · have hdiff : f (a - b) = f γ := by
          have htarget :
              (addMonoidHomEmbedding f hf) a - (addMonoidHomEmbedding f hf) b =
                (addMonoidHomEmbedding f hf) γ := by
            rw [ha, hb]
            exact hpair.2
          simpa [addMonoidHomEmbedding] using htarget
        exact hf hdiff
    · exact Prod.ext ha hb

lemma map_addEquiv
    (e : G ≃+ H) {Q B : Finset G} {M : ℝ}
    (h : PairCoeffLowerBound Q B M) :
    PairCoeffLowerBound
      (Q.map (addEquivEmbedding e)) (B.map (addEquivEmbedding e)) M := by
  classical
  intro γ hγ
  rcases Finset.mem_map.mp hγ with ⟨δ, hδ, rfl⟩
  rw [pairFiber_card_map_addEquiv, Finset.card_map]
  exact h δ hδ

lemma map_addMonoidHom_of_injective
    (f : G →+ H) (hf : Function.Injective f) {Q B : Finset G} {M : ℝ}
    (h : PairCoeffLowerBound Q B M) :
    PairCoeffLowerBound
      (Q.map (addMonoidHomEmbedding f hf)) (B.map (addMonoidHomEmbedding f hf)) M := by
  classical
  intro γ hγ
  rcases Finset.mem_map.mp hγ with ⟨δ, hδ, rfl⟩
  rw [pairFiber_card_map_addMonoidHom_of_injective, Finset.card_map]
  exact h δ hδ

lemma of_map_addEquiv
    (e : G ≃+ H) {Q B : Finset G} {M : ℝ}
    (h :
      PairCoeffLowerBound
        (Q.map (addEquivEmbedding e)) (B.map (addEquivEmbedding e)) M) :
    PairCoeffLowerBound Q B M := by
  classical
  intro γ hγ
  have hγ' : (addEquivEmbedding e) γ ∈ B.map (addEquivEmbedding e) :=
    Finset.mem_map.mpr ⟨γ, hγ, rfl⟩
  have hbound := h ((addEquivEmbedding e) γ) hγ'
  rwa [pairFiber_card_map_addEquiv, Finset.card_map] at hbound

lemma exists_of_addEquiv
    (e : G ≃+ H) {B : Finset G} {M : ℝ}
    (h :
      ∃ Q : Finset H, Q.Nonempty ∧
        PairCoeffLowerBound Q (B.map (addEquivEmbedding e)) M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  rcases h with ⟨Q, hQ, hbound⟩
  refine ⟨Q.map (addEquivEmbedding e.symm), ?_, ?_⟩
  · rcases hQ with ⟨q, hq⟩
    exact ⟨e.symm q, Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  have hmap := map_addEquiv e.symm hbound
  simpa [addEquivEmbedding, Finset.map_map] using hmap

end PairCoeffLowerBound

section PairFiberCounting

variable {G : Type*} [AddCommGroup G]

/-- Any set whose `γ`-backward translate stays inside `Q` injects into the
pair fiber `{(x,y) ∈ Q × Q | x - y = γ}`. -/
lemma card_le_pairFiber_card_of_sub_right_subset
    (Q R : Finset G) (γ : G)
    (hR : ∀ x ∈ R, x ∈ Q ∧ x - γ ∈ Q) :
    R.card ≤
      ((Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun x : G => (x, x - γ)) ?_ ?_
  · intro x hx
    change (x, x - γ) ∈
      ((Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ))
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr ⟨(hR x hx).1, (hR x hx).2⟩
    · simp [sub_eq_add_neg, add_left_comm]
  · intro x _hx y _hy hxy
    exact congrArg Prod.fst hxy

lemma pairCoeffLowerBound_of_inner_card
    {Q B : Finset G} {M : ℝ}
    (inner : G → Finset G)
    (hinner : ∀ γ ∈ B, ∀ x ∈ inner γ, x ∈ Q ∧ x - γ ∈ Q)
    (hcard :
      ∀ γ ∈ B,
        1 - M ≤ ((inner γ).card : ℝ) / (Q.card : ℝ)) :
    PairCoeffLowerBound Q B M := by
  classical
  intro γ hγ
  have hle :
      ((inner γ).card : ℝ) ≤
        (((Q.product Q).filter
          (fun pair : G × G => pair.1 - pair.2 = γ)).card : ℝ) := by
    exact_mod_cast
      card_le_pairFiber_card_of_sub_right_subset Q (inner γ) γ
        (hinner γ hγ)
  exact (hcard γ hγ).trans (div_le_div_of_nonneg_right hle (by positivity))

end PairFiberCounting

section IntIntervals

/-- Centered integer interval `[-N,N]`. -/
def intCenteredInterval (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- Inner interval that stays inside `[-N,N]` after subtracting any integer of
absolute value at most `K`. -/
def intInnerInterval (N K : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ) + (K : ℤ)) ((N : ℤ) - (K : ℤ))

lemma intCenteredInterval_nonempty (N : ℕ) :
    (intCenteredInterval N).Nonempty := by
  refine ⟨0, ?_⟩
  rw [intCenteredInterval, Finset.mem_Icc]
  constructor
  · exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le N)
  · exact_mod_cast Nat.zero_le N

lemma intCenteredInterval_card (N : ℕ) :
    (intCenteredInterval N).card = 2 * N + 1 := by
  rw [intCenteredInterval, Int.card_Icc]
  omega

lemma intInnerInterval_card {N K : ℕ} (hK : K ≤ N) :
    (intInnerInterval N K).card = 2 * (N - K) + 1 := by
  rw [intInnerInterval, Int.card_Icc]
  omega

lemma intInnerInterval_subset_centered
    {N K : ℕ} :
    intInnerInterval N K ⊆ intCenteredInterval N := by
  intro x hx
  rw [intInnerInterval, Finset.mem_Icc] at hx
  rw [intCenteredInterval, Finset.mem_Icc]
  constructor <;> nlinarith

lemma intInnerInterval_sub_mem_centered
    {N K : ℕ} {γ x : ℤ}
    (hγ : γ.natAbs ≤ K) (hx : x ∈ intInnerInterval N K) :
    x - γ ∈ intCenteredInterval N := by
  rw [intInnerInterval, Finset.mem_Icc] at hx
  rw [intCenteredInterval, Finset.mem_Icc]
  have hγ_le_K : γ ≤ (K : ℤ) := by
    exact le_trans Int.le_natAbs (by exact_mod_cast hγ)
  have hnegK_le_γ : -(K : ℤ) ≤ γ := by
    have hneg_abs : -((γ.natAbs : ℤ)) ≤ γ := by
      exact neg_le.mp (by simpa using (Int.le_natAbs (a := -γ)))
    have hγZ : (γ.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hγ
    exact le_trans (neg_le_neg hγZ) hneg_abs
  constructor <;> nlinarith [hx.1, hx.2, hγ_le_K, hnegK_le_γ]

lemma int_pairCoeffLowerBound_of_inner_ratio
    {B : Finset ℤ} {N K : ℕ} {M : ℝ}
    (hB : ∀ γ ∈ B, γ.natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((intInnerInterval N K).card : ℝ) /
          ((intCenteredInterval N).card : ℝ)) :
    PairCoeffLowerBound (intCenteredInterval N) B M := by
  classical
  refine pairCoeffLowerBound_of_inner_card
    (Q := intCenteredInterval N) (B := B) (M := M)
    (fun _γ => intInnerInterval N K) ?_ ?_
  · intro γ hγ x hx
    exact
      ⟨intInnerInterval_subset_centered hx,
        intInnerInterval_sub_mem_centered (hB γ hγ) hx⟩
  · intro γ _hγ
    exact hratio

lemma int_pairCoeffLowerBound_of_nat_ratio
    {B : Finset ℤ} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, γ.natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((2 * (N - K) + 1 : ℕ) : ℝ) /
          ((2 * N + 1 : ℕ) : ℝ)) :
    PairCoeffLowerBound (intCenteredInterval N) B M :=
  int_pairCoeffLowerBound_of_inner_ratio hB (by
    simpa [intInnerInterval_card hK, intCenteredInterval_card] using hratio)

lemma int_interval_ratio_bound
    {N K : ℕ} {M : ℝ} (hK : K ≤ N)
    (hloss : (2 * K : ℝ) ≤ M * ((2 * N + 1 : ℕ) : ℝ)) :
    1 - M ≤
      ((2 * (N - K) + 1 : ℕ) : ℝ) /
        ((2 * N + 1 : ℕ) : ℝ) := by
  have hden : 0 < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hden]
  norm_num [Nat.cast_sub hK] at hloss hden ⊢
  nlinarith

lemma int_pairCoeffLowerBound_of_loss
    {B : Finset ℤ} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, γ.natAbs ≤ K)
    (hloss : (2 * K : ℝ) ≤ M * ((2 * N + 1 : ℕ) : ℝ)) :
    PairCoeffLowerBound (intCenteredInterval N) B M :=
  int_pairCoeffLowerBound_of_nat_ratio hK hB
    (int_interval_ratio_bound hK hloss)

lemma exists_int_pairCoeffLowerBound_of_bound
    (B : Finset ℤ) (K : ℕ) {M : ℝ} (hM : 0 < M)
    (hB : ∀ γ ∈ B, γ.natAbs ≤ K) :
    ∃ Q : Finset ℤ, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (((2 * K : ℝ) / M) + (K : ℝ))
  have hN_gt_K : (K : ℝ) < (N : ℝ) := by
    have hterm_nonneg : 0 ≤ (2 * K : ℝ) / M := by
      positivity
    nlinarith [hN]
  have hKle : K ≤ N := by exact_mod_cast le_of_lt hN_gt_K
  have hloss : (2 * K : ℝ) ≤ M * ((2 * N + 1 : ℕ) : ℝ) := by
    have hNbig : (2 * K : ℝ) / M < (N : ℝ) := by
      nlinarith [hN]
    have htwoK_lt : (2 * K : ℝ) < M * (N : ℝ) := by
      have hraw : (2 * K : ℝ) < (N : ℝ) * M := by
        rwa [div_lt_iff₀ hM] at hNbig
      nlinarith
    have hN_le : (N : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N ≤ 2 * N + 1)
    exact (le_of_lt htwoK_lt).trans
      (mul_le_mul_of_nonneg_left hN_le (le_of_lt hM))
  exact
    ⟨intCenteredInterval N, intCenteredInterval_nonempty N,
      int_pairCoeffLowerBound_of_loss hKle hB hloss⟩

lemma exists_int_pairCoeffLowerBound
    (B : Finset ℤ) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset ℤ, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  by_cases hBne : B.Nonempty
  · let K : ℕ := (B.image Int.natAbs).max' (hBne.image Int.natAbs)
    exact exists_int_pairCoeffLowerBound_of_bound B K hM (by
      intro γ hγ
      exact (B.image Int.natAbs).le_max' γ.natAbs
        (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩))
  · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBne
    exact
      ⟨intCenteredInterval 0, intCenteredInterval_nonempty 0, by
        simp [PairCoeffLowerBound, hBempty]⟩

end IntIntervals

section IntPiBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product box `[-N,N]^ι` in the finite-rank free abelian group `ι → Z`. -/
def intPiCenteredBox (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ : ι => intCenteredInterval N

/-- Inner product box that stays inside `[-N,N]^ι` after subtracting any vector
whose coordinates have absolute value at most `K`. -/
def intPiInnerBox (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N K : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ : ι => intInnerInterval N K

lemma intPiCenteredBox_nonempty (N : ℕ) :
    (intPiCenteredBox ι N).Nonempty := by
  rw [intPiCenteredBox, Fintype.piFinset_nonempty]
  intro i
  exact intCenteredInterval_nonempty N

lemma intPiCenteredBox_card (N : ℕ) :
    (intPiCenteredBox ι N).card = ∏ _i : ι, (2 * N + 1 : ℕ) := by
  rw [intPiCenteredBox, Fintype.card_piFinset]
  simp [intCenteredInterval_card]

lemma intPiInnerBox_card {N K : ℕ} (hK : K ≤ N) :
    (intPiInnerBox ι N K).card =
      ∏ _i : ι, (2 * (N - K) + 1 : ℕ) := by
  rw [intPiInnerBox, Fintype.card_piFinset]
  simp [intInnerInterval_card hK]

lemma intPiInnerBox_subset_centered
    {N K : ℕ} {x : ι → ℤ}
    (hx : x ∈ intPiInnerBox ι N K) :
    x ∈ intPiCenteredBox ι N := by
  rw [intPiInnerBox, Fintype.mem_piFinset] at hx
  rw [intPiCenteredBox, Fintype.mem_piFinset]
  intro i
  exact intInnerInterval_subset_centered (hx i)

lemma intPiInnerBox_sub_mem_centered
    {N K : ℕ} {γ x : ι → ℤ}
    (hγ : ∀ i : ι, (γ i).natAbs ≤ K)
    (hx : x ∈ intPiInnerBox ι N K) :
    x - γ ∈ intPiCenteredBox ι N := by
  rw [intPiInnerBox, Fintype.mem_piFinset] at hx
  rw [intPiCenteredBox, Fintype.mem_piFinset]
  intro i
  simpa using intInnerInterval_sub_mem_centered (hγ i) (hx i)

lemma intPi_pairCoeffLowerBound_of_inner_ratio
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((intPiInnerBox ι N K).card : ℝ) /
          ((intPiCenteredBox ι N).card : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M := by
  classical
  refine pairCoeffLowerBound_of_inner_card
    (Q := intPiCenteredBox ι N) (B := B) (M := M)
    (fun _γ => intPiInnerBox ι N K) ?_ ?_
  · intro γ hγ x hx
    exact
      ⟨intPiInnerBox_subset_centered hx,
        intPiInnerBox_sub_mem_centered (hB γ hγ) hx⟩
  · intro γ _hγ
    exact hratio

lemma intPi_pairCoeffLowerBound_of_nat_ratio
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M :=
  intPi_pairCoeffLowerBound_of_inner_ratio hB (by
    simpa [intPiInnerBox_card (ι := ι) hK, intPiCenteredBox_card (ι := ι)]
      using hratio)

omit [DecidableEq ι] in
lemma intPi_product_ratio_bound
    {N K : ℕ} {M : ℝ} (hK : K ≤ N)
    (hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ)) :
    1 - M ≤
      ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
        ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) := by
  classical
  let d : ℕ := Fintype.card ι
  let inner : ℝ := ((2 * (N - K) + 1 : ℕ) : ℝ)
  let outer : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have houter_pos : 0 < outer := by
    dsimp [outer]
    positivity
  have hinner_nonneg : 0 ≤ inner := by
    dsimp [inner]
    positivity
  have hratio_eq :
      ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) =
        (inner / outer) ^ d := by
    simp [d, inner, outer, Finset.prod_const, Finset.card_univ, div_pow]
  have hratio_nonneg : 0 ≤ inner / outer :=
    div_nonneg hinner_nonneg houter_pos.le
  have hbernoulli :
      1 + (d : ℝ) * (inner / outer - 1) ≤ (inner / outer) ^ d :=
    one_add_mul_sub_le_pow (a := inner / outer) (n := d) (by linarith)
  have hinner_eq : inner = outer - (2 * K : ℝ) := by
    dsimp [inner, outer]
    norm_num [Nat.cast_sub hK]
    ring
  have hsub :
      inner / outer - 1 = -((2 * K : ℝ) / outer) := by
    rw [hinner_eq]
    field_simp [houter_pos.ne']
    ring
  have hdiv_loss' :
      (((d : ℝ) * (2 * K : ℝ)) / outer) ≤ M := by
    rw [div_le_iff₀ houter_pos]
    simpa [d, outer] using hloss
  have hdiv_loss :
      (d : ℝ) * ((2 * K : ℝ) / outer) ≤ M := by
    simpa [mul_div_assoc] using hdiv_loss'
  have hlower :
      1 - M ≤ 1 + (d : ℝ) * (inner / outer - 1) := by
    rw [hsub]
    nlinarith
  calc
    1 - M ≤ 1 + (d : ℝ) * (inner / outer - 1) := hlower
    _ ≤ (inner / outer) ^ d := hbernoulli
    _ = ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) := hratio_eq.symm

lemma intPi_pairCoeffLowerBound_of_loss
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M :=
  intPi_pairCoeffLowerBound_of_nat_ratio hK hB
    (intPi_product_ratio_bound (ι := ι) hK hloss)

lemma exists_intPi_pairCoeffLowerBound_of_bound
    (B : Finset (ι → ℤ)) (K : ℕ) {M : ℝ} (hM : 0 < M)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K) :
    ∃ Q : Finset (ι → ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  obtain ⟨N, hN⟩ :=
    exists_nat_gt ((((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) + (K : ℝ))
  have hN_gt_K : (K : ℝ) < (N : ℝ) := by
    have hterm_nonneg :
        0 ≤ (((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) := by
      positivity
    nlinarith [hN]
  have hKle : K ≤ N := by exact_mod_cast le_of_lt hN_gt_K
  have hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ) := by
    have hNbig :
        (((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) < (N : ℝ) := by
      nlinarith [hN]
    have hlt :
        ((Fintype.card ι : ℝ) * (2 * K : ℝ)) < M * (N : ℝ) := by
      have hraw :
          ((Fintype.card ι : ℝ) * (2 * K : ℝ)) < (N : ℝ) * M := by
        rwa [div_lt_iff₀ hM] at hNbig
      nlinarith
    have hN_le : (N : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N ≤ 2 * N + 1)
    exact (le_of_lt hlt).trans
      (mul_le_mul_of_nonneg_left hN_le (le_of_lt hM))
  exact
    ⟨intPiCenteredBox ι N, intPiCenteredBox_nonempty N,
      intPi_pairCoeffLowerBound_of_loss hKle hB hloss⟩

lemma exists_intPi_pairCoeffLowerBound
    (B : Finset (ι → ℤ)) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset (ι → ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let C : Finset ℕ :=
    B.biUnion fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs
  by_cases hC : C.Nonempty
  · let K : ℕ := C.max' hC
    exact exists_intPi_pairCoeffLowerBound_of_bound B K hM (by
      intro γ hγ i
      exact C.le_max' (γ i).natAbs (by
        change (γ i).natAbs ∈
          B.biUnion (fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs)
        rw [Finset.mem_biUnion]
        exact ⟨γ, hγ, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩))
  · exact exists_intPi_pairCoeffLowerBound_of_bound B 0 hM (by
      intro γ hγ i
      exfalso
      exact hC ⟨(γ i).natAbs, by
        change (γ i).natAbs ∈
          B.biUnion (fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs)
        rw [Finset.mem_biUnion]
        exact ⟨γ, hγ, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩⟩)

end IntPiBoxes

section FinsuppBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exists_finsupp_pairCoeffLowerBound
    (B : Finset (ι →₀ ℤ)) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset (ι →₀ ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let e : (ι →₀ ℤ) ≃+ (ι → ℤ) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).toAddEquiv
  exact PairCoeffLowerBound.exists_of_addEquiv e
    (exists_intPi_pairCoeffLowerBound
      (B.map (PairCoeffLowerBound.addEquivEmbedding e)) hM)

end FinsuppBoxes

section FreeFinite

variable {G : Type*} [AddCommGroup G]

lemma exists_free_finite_pairCoeffLowerBound
    [Module.Free ℤ G] [Module.Finite ℤ G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ G
  let b := Module.Free.chooseBasis ℤ G
  haveI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let e : G ≃+ (ι →₀ ℤ) := b.repr.toAddEquiv
  exact PairCoeffLowerBound.exists_of_addEquiv e
    (exists_finsupp_pairCoeffLowerBound
      (B.map (PairCoeffLowerBound.addEquivEmbedding e)) hM)

lemma exists_fg_torsionFree_pairCoeffLowerBound
    [IsAddTorsionFree G] [AddGroup.FG G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  haveI : Module.Finite ℤ G :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG G)
  haveI : Module.Free ℤ G := Module.free_of_finite_type_torsion_free'
  exact exists_free_finite_pairCoeffLowerBound B hM

lemma exists_torsionFree_pairCoeffLowerBound
    [IsAddTorsionFree G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let H : AddSubgroup G := AddSubgroup.closure (B : Set G)
  let BH : Finset H := B.subtype fun x => x ∈ H
  haveI : IsAddTorsionFree H := by
    constructor
    intro n hn x y hxy
    ext
    exact IsAddTorsionFree.nsmul_right_injective hn (by
      simpa using congrArg Subtype.val hxy)
  haveI : Finite (B : Set G) := Set.finite_coe_iff.mpr B.finite_toSet
  haveI : AddGroup.FG H := AddGroup.closure_finite_fg (B : Set G)
  obtain ⟨QH, hQH, hboundH⟩ :=
    exists_fg_torsionFree_pairCoeffLowerBound (G := H) BH hM
  let emb := PairCoeffLowerBound.addMonoidHomEmbedding
    H.subtype (AddSubgroup.subtype_injective H)
  have hBmap : BH.map emb = B := by
    ext γ
    simp [BH, H, emb, PairCoeffLowerBound.addMonoidHomEmbedding]
    intro hγ
    exact AddSubgroup.subset_closure hγ
  refine ⟨QH.map emb, ?_, ?_⟩
  · rcases hQH with ⟨q, hq⟩
    exact ⟨q, Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  · have hmap :=
      PairCoeffLowerBound.map_addMonoidHom_of_injective
        H.subtype (AddSubgroup.subtype_injective H) hboundH
    simpa [emb, hBmap] using hmap

end FreeFinite

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

lemma exists_pairCoeffLowerBound
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q.Nonempty ∧ PairCoeffLowerBound Q B M :=
  exists_torsionFree_pairCoeffLowerBound (G := E.Group) B hM

lemma exists_pairCoeffLowerBound_nonempty_ne
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧ PairCoeffLowerBound Q B M := by
  classical
  obtain ⟨Q, hQ, hbound⟩ :=
    E.exists_pairCoeffLowerBound B hM
  exact ⟨Q, Finset.nonempty_iff_ne_empty.mp hQ, hbound⟩

lemma exists_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M := by
  simpa [FejerPairCoeffLowerBound] using
    E.exists_pairCoeffLowerBound_nonempty_ne B hM

end CayleyExtraction

end

end Erdos42.CompactCayley
