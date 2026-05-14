/-
Erdos Problem 202 — Park–Pham layer, fragment infrastructure.

This file starts the source-aligned formalization of the Park--Pham /
Kahn--Kalai expectation-threshold proof.  The "simple proof" route of
Park--Vondrak works with fragments

  F(H, W) = {S \ W | S in H}

and their inclusion-minimal members, then splits those minimal fragments into
large and small parts at a cardinality cutoff.  The deep probabilistic cost
lemma is not proved here; this file only provides the finite set-system
bookkeeping needed to state it cleanly.
-/

import Mathlib
import Erdos.P202.ParkPham.BooleanFamilies
import Erdos.P202.ParkPham.Smallness

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Fragment family `F(H,W) = {S \ W | S in H}`. -/
def fragmentFamily (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  H.image fun S => S \ W

@[simp]
lemma mem_fragmentFamily {H : Finset (Finset α)} {W T : Finset α} :
    T ∈ fragmentFamily H W ↔ ∃ S ∈ H, S \ W = T := by
  simp [fragmentFamily]

/-- Minimal fragments `F*(H,W)`: inclusion-minimal members of
`fragmentFamily H W`.  The ground-set argument of `minimalMembersIn` is
irrelevant for minimality, so we use `∅`. -/
def minimalFragments (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  minimalMembersIn (∅ : Finset α) (fragmentFamily H W)

@[simp]
lemma mem_minimalFragments {H : Finset (Finset α)} {W T : Finset α} :
    T ∈ minimalFragments H W ↔
      T ∈ fragmentFamily H W ∧
        ∀ R ∈ fragmentFamily H W, ¬ R ⊂ T := by
  simp [minimalFragments]

lemma minimalFragments_subset_fragmentFamily
    (H : Finset (Finset α)) (W : Finset α) :
    minimalFragments H W ⊆ fragmentFamily H W :=
  minimalMembersIn_subset

lemma fragmentFamily_card_le_card
    (H : Finset (Finset α)) (W : Finset α) :
    (fragmentFamily H W).card ≤ H.card := by
  rw [fragmentFamily]
  exact Finset.card_image_le

lemma minimalFragments_card_le_card
    (H : Finset (Finset α)) (W : Finset α) :
    (minimalFragments H W).card ≤ H.card :=
  (Finset.card_le_card (minimalFragments_subset_fragmentFamily H W)).trans
    (fragmentFamily_card_le_card H W)

lemma fragment_disjoint_exposure
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ fragmentFamily H W) :
    Disjoint T W := by
  rcases mem_fragmentFamily.mp hT with ⟨S, _hS, rfl⟩
  rw [Finset.disjoint_left]
  intro x hx hW
  exact (Finset.mem_sdiff.mp hx).2 hW

lemma minimalFragment_disjoint_exposure
    {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ minimalFragments H W) :
    Disjoint T W :=
  fragment_disjoint_exposure (minimalFragments_subset_fragmentFamily H W hT)

/-- Large minimal fragments: those of cardinality at least `m`. -/
def largeMinimalFragments (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  (minimalFragments H W).filter fun T => m ≤ T.card

/-- Small minimal fragments: those of cardinality strictly below `m`. -/
def smallMinimalFragments (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    Finset (Finset α) :=
  (minimalFragments H W).filter fun T => T.card < m

lemma largeMinimalFragments_card_le_card
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    (largeMinimalFragments m H W).card ≤ H.card :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (minimalFragments_card_le_card H W)

lemma smallMinimalFragments_card_le_card
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    (smallMinimalFragments m H W).card ≤ H.card :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (minimalFragments_card_le_card H W)

@[simp]
lemma mem_largeMinimalFragments {m : ℕ} {H : Finset (Finset α)}
    {W T : Finset α} :
    T ∈ largeMinimalFragments m H W ↔
      T ∈ minimalFragments H W ∧ m ≤ T.card := by
  simp [largeMinimalFragments]

lemma largeMinimalFragment_disjoint_exposure
    {m : ℕ} {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ largeMinimalFragments m H W) :
    Disjoint T W :=
  minimalFragment_disjoint_exposure (mem_largeMinimalFragments.mp hT).1

lemma union_sdiff_right_eq_left_of_disjoint
    {W S : Finset α} (hdisj : Disjoint S W) :
    (W ∪ S) \ S = W := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxWS, hxSnot⟩
    rcases Finset.mem_union.mp hxWS with hxW | hxS
    · exact hxW
    · exact False.elim (hxSnot hxS)
  · intro hxW
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union.mpr (Or.inl hxW),
        fun hxS => (Finset.disjoint_left.mp hdisj) hxS hxW⟩

@[simp]
lemma mem_smallMinimalFragments {m : ℕ} {H : Finset (Finset α)}
    {W T : Finset α} :
    T ∈ smallMinimalFragments m H W ↔
      T ∈ minimalFragments H W ∧ T.card < m := by
  simp [smallMinimalFragments]

/-- The large/small split partitions the minimal fragments. -/
lemma small_union_large_minimalFragments
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    smallMinimalFragments m H W ∪ largeMinimalFragments m H W =
      minimalFragments H W := by
  ext T
  by_cases hT : T ∈ minimalFragments H W
  · by_cases hsmall : T.card < m
    · simp [hT, hsmall, largeMinimalFragments, smallMinimalFragments,
        not_le.mpr hsmall]
    · have hlarge : m ≤ T.card := le_of_not_gt hsmall
      simp [hT, hlarge, hsmall, largeMinimalFragments, smallMinimalFragments]
  · simp [hT, largeMinimalFragments, smallMinimalFragments]

/-- The large and small minimal-fragment parts are disjoint. -/
lemma disjoint_small_large_minimalFragments
    (m : ℕ) (H : Finset (Finset α)) (W : Finset α) :
    Disjoint (smallMinimalFragments m H W) (largeMinimalFragments m H W) := by
  rw [Finset.disjoint_left]
  intro T hsmall hlarge
  rcases mem_smallMinimalFragments.mp hsmall with ⟨_, hlt⟩
  rcases mem_largeMinimalFragments.mp hlarge with ⟨_, hle⟩
  exact not_lt_of_ge hle hlt

/-- Fragments inherit any cardinality upper bound on the source family. -/
lemma fragmentFamily_card_le_of_forall_card_le
    {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (hH : ∀ S ∈ H, S.card ≤ ℓ)
    (hT : T ∈ fragmentFamily H W) :
    T.card ≤ ℓ := by
  rcases mem_fragmentFamily.mp hT with ⟨S, hS, rfl⟩
  have hsub : S \ W ⊆ S := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  exact (Finset.card_le_card hsub).trans (hH S hS)

/-- Minimal fragments inherit any cardinality upper bound on the source
family. -/
lemma minimalFragments_card_le_of_forall_card_le
    {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (hH : ∀ S ∈ H, S.card ≤ ℓ)
    (hT : T ∈ minimalFragments H W) :
    T.card ≤ ℓ :=
  fragmentFamily_card_le_of_forall_card_le hH
    (minimalFragments_subset_fragmentFamily H W hT)

/-- Minimal fragments are a canonical cover of the fragment family. -/
lemma minimalFragments_cover
    (X : Finset α) (H : Finset (Finset α)) (W : Finset α) :
    CoversIn X (minimalFragments H W) (fragmentFamily H W) := by
  simpa [minimalFragments] using
    (minimalMembers_cover (X := (∅ : Finset α)) (U := fragmentFamily H W))

/-- If a family covers all minimal fragments, then it covers the original
family.  This is the finite covering step used in the Park--Vondrak proof when
passing from `F*(H,W)` back to `H`. -/
lemma CoversIn.of_minimalFragments
    {X : Finset α} {G H : Finset (Finset α)} {W : Finset α}
    (hCover : CoversIn X G (minimalFragments H W)) :
    CoversIn X G H := by
  intro S hS
  have hfrag : S \ W ∈ fragmentFamily H W :=
    mem_fragmentFamily.mpr ⟨S, hS, rfl⟩
  rcases minimalFragments_cover X H W (S \ W) hfrag with
    ⟨R, hRmin, hRsub⟩
  rcases hCover R hRmin with ⟨T, hTG, hTR⟩
  have hsdiff_sub : S \ W ⊆ S := by
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  exact ⟨T, hTG, hTR.trans (hRsub.trans hsdiff_sub)⟩

lemma sdiff_eq_empty_iff_subset {S W : Finset α} :
    S \ W = ∅ ↔ S ⊆ W := by
  constructor
  · intro h x hxS
    by_contra hxW
    have hx : x ∈ S \ W := Finset.mem_sdiff.mpr ⟨hxS, hxW⟩
    simp [h] at hx
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Finset.mem_sdiff.mp hx).2 (h (Finset.mem_sdiff.mp hx).1)

/-- The empty set is a fragment exactly when some source member is contained in
`W`. -/
lemma empty_mem_fragmentFamily_iff
    {H : Finset (Finset α)} {W : Finset α} :
    (∅ : Finset α) ∈ fragmentFamily H W ↔ ∃ S ∈ H, S ⊆ W := by
  constructor
  · intro h
    rcases mem_fragmentFamily.mp h with ⟨S, hS, hdiff⟩
    exact ⟨S, hS, sdiff_eq_empty_iff_subset.mp hdiff⟩
  · rintro ⟨S, hS, hSW⟩
    exact mem_fragmentFamily.mpr ⟨S, hS, sdiff_eq_empty_iff_subset.mpr hSW⟩

lemma subset_union_of_sdiff_subset
    {S W V : Finset α} (h : S \ W ⊆ V) :
    S ⊆ W ∪ V := by
  intro x hxS
  by_cases hxW : x ∈ W
  · exact Finset.mem_union.mpr (Or.inl hxW)
  · exact Finset.mem_union.mpr
      (Or.inr (h (Finset.mem_sdiff.mpr ⟨hxS, hxW⟩)))

lemma sdiff_subset_of_subset_union
    {S W V : Finset α} (h : S ⊆ W ∪ V) :
    S \ W ⊆ V := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxW_not⟩
  rcases Finset.mem_union.mp (h hxS) with hxW | hxV
  · exact False.elim (hxW_not hxW)
  · exact hxV

lemma exists_source_subset_union_of_minimalFragment_subset
    {H : Finset (Finset α)} {W V : Finset α}
    (h : ∃ R ∈ minimalFragments H W, R ⊆ V) :
    ∃ S ∈ H, S ⊆ W ∪ V := by
  rcases h with ⟨R, hR, hRV⟩
  have hRfrag : R ∈ fragmentFamily H W :=
    minimalFragments_subset_fragmentFamily H W hR
  rcases mem_fragmentFamily.mp hRfrag with ⟨S, hS, hSR⟩
  refine ⟨S, hS, subset_union_of_sdiff_subset ?_⟩
  intro x hx
  exact hRV (by simpa [hSR] using hx)

lemma exists_minimalFragment_subset_of_source_subset_union
    {H : Finset (Finset α)} {W V : Finset α}
    (h : ∃ S ∈ H, S ⊆ W ∪ V) :
    ∃ R ∈ minimalFragments H W, R ⊆ V := by
  rcases h with ⟨S, hS, hSWV⟩
  have hfrag : S \ W ∈ fragmentFamily H W :=
    mem_fragmentFamily.mpr ⟨S, hS, rfl⟩
  rcases minimalFragments_cover (∅ : Finset α) H W (S \ W) hfrag with
    ⟨R, hR, hRsub⟩
  exact ⟨R, hR, hRsub.trans (sdiff_subset_of_subset_union hSWV)⟩

lemma exists_minimalFragment_subset_iff_source_subset_union
    {H : Finset (Finset α)} {W V : Finset α} :
    (∃ R ∈ minimalFragments H W, R ⊆ V) ↔
      ∃ S ∈ H, S ⊆ W ∪ V := by
  constructor
  · exact exists_source_subset_union_of_minimalFragment_subset
  · exact exists_minimalFragment_subset_of_source_subset_union

/-- Park--Pham/Park--Vondrak containment trick.  If `T ∈ H` is contained in
`Z`, then every minimal fragment `S ∈ F*(H, Z \ S)` with `S ⊆ Z` is contained
in `T`.  Otherwise the smaller set `T \ (Z \ S)` would be a fragment properly
contained in `S`. -/
lemma minimalFragment_subset_of_source_subset
    {H : Finset (Finset α)} {Z S T : Finset α}
    (hT : T ∈ H) (hTZ : T ⊆ Z)
    (hSmin : S ∈ minimalFragments H (Z \ S)) :
    S ⊆ T := by
  by_contra hnot
  have hRfrag : T \ (Z \ S) ∈ fragmentFamily H (Z \ S) :=
    mem_fragmentFamily.mpr ⟨T, hT, rfl⟩
  have hRsub : T \ (Z \ S) ⊆ S := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxNot⟩
    by_contra hxS
    exact hxNot (Finset.mem_sdiff.mpr ⟨hTZ hxT, hxS⟩)
  have hproper : T \ (Z \ S) ⊂ S := by
    refine hRsub.ssubset_of_ne ?_
    intro hEq
    have hST : S ⊆ T := by
      intro x hxS
      have hxR : x ∈ T \ (Z \ S) := by
        simpa [hEq] using hxS
      exact (Finset.mem_sdiff.mp hxR).1
    exact hnot hST
  exact (mem_minimalFragments.mp hSmin).2 (T \ (Z \ S)) hRfrag hproper

lemma largeMinimalFragment_subset_of_source_subset
    {H : Finset (Finset α)} {Z S T : Finset α} {m : ℕ}
    (hT : T ∈ H) (hTZ : T ⊆ Z)
    (hS : S ∈ largeMinimalFragments m H (Z \ S)) :
    S ⊆ T :=
  minimalFragment_subset_of_source_subset hT hTZ
    (mem_largeMinimalFragments.mp hS).1

lemma largeMinimalFragment_subset_ground
    {X : Finset α} {H : Finset (Finset α)} {W S : Finset α} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    (hS : S ∈ largeMinimalFragments m H W) :
    S ⊆ X := by
  have hSfrag : S ∈ fragmentFamily H W :=
    minimalFragments_subset_fragmentFamily H W
      (mem_largeMinimalFragments.mp hS).1
  rcases mem_fragmentFamily.mp hSfrag with ⟨T, hT, rfl⟩
  exact (Finset.sdiff_subset : T \ W ⊆ T).trans (hHX T hT)

/-- Inner witness set in the Park--Pham/Park--Vondrak double-counting
argument: subsets `S ⊆ Z` that are large minimal fragments after exposing
`Z \ S`. -/
def largeFragmentWitnesses
    (H : Finset (Finset α)) (m : ℕ) (Z : Finset α) :
    Finset (Finset α) :=
  Z.powerset.filter fun S => S ∈ largeMinimalFragments m H (Z \ S)

@[simp]
lemma mem_largeFragmentWitnesses
    {H : Finset (Finset α)} {m : ℕ} {Z S : Finset α} :
    S ∈ largeFragmentWitnesses H m Z ↔
      S ⊆ Z ∧ S ∈ largeMinimalFragments m H (Z \ S) := by
  simp [largeFragmentWitnesses]

lemma largeMinimalFragment_mem_witnesses_union
    {m : ℕ} {H : Finset (Finset α)} {W S : Finset α}
    (hS : S ∈ largeMinimalFragments m H W) :
    S ∈ largeFragmentWitnesses H m (W ∪ S) := by
  have hdisj : Disjoint S W := largeMinimalFragment_disjoint_exposure hS
  have hsdiff : (W ∪ S) \ S = W :=
    union_sdiff_right_eq_left_of_disjoint hdisj
  rw [mem_largeFragmentWitnesses]
  constructor
  · exact Finset.subset_union_right
  · simpa [hsdiff] using hS

lemma largeFragmentWitnesses_subset_source_powerset_filter
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    largeFragmentWitnesses H m Z ⊆
      T.powerset.filter fun S => m ≤ S.card := by
  intro S hS
  rcases mem_largeFragmentWitnesses.mp hS with ⟨_hSZ, hSlarge⟩
  have hST : S ⊆ T :=
    largeMinimalFragment_subset_of_source_subset hT hTZ hSlarge
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hST, (mem_largeMinimalFragments.mp hSlarge).2⟩

lemma largeFragmentWitnesses_card_le_source
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    (largeFragmentWitnesses H m Z).card ≤
      (T.powerset.filter fun S => m ≤ S.card).card :=
  Finset.card_le_card
    (largeFragmentWitnesses_subset_source_powerset_filter hT hTZ)

lemma exists_source_subset_of_largeFragmentWitness
    {H : Finset (Finset α)} {m : ℕ} {Z S : Finset α}
    (hS : S ∈ largeFragmentWitnesses H m Z) :
    ∃ T ∈ H, T ⊆ Z := by
  rcases mem_largeFragmentWitnesses.mp hS with ⟨hSZ, hSlarge⟩
  have hSfrag : S ∈ fragmentFamily H (Z \ S) :=
    minimalFragments_subset_fragmentFamily H (Z \ S)
      (mem_largeMinimalFragments.mp hSlarge).1
  rcases mem_fragmentFamily.mp hSfrag with ⟨T, hT, hdiff⟩
  refine ⟨T, hT, ?_⟩
  intro x hxT
  by_contra hxZ
  have hxNot : x ∉ Z \ S := by
    intro hx
    exact hxZ (Finset.mem_sdiff.mp hx).1
  have hxS : x ∈ S := by
    have hx : x ∈ T \ (Z \ S) :=
      Finset.mem_sdiff.mpr ⟨hxT, hxNot⟩
    simpa [hdiff] using hx
  exact hxZ (hSZ hxS)

lemma largeFragmentWitnesses_eq_empty_of_no_source_subset
    {H : Finset (Finset α)} {m : ℕ} {Z : Finset α}
    (hno : ¬ ∃ T ∈ H, T ⊆ Z) :
    largeFragmentWitnesses H m Z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  exact hno (exists_source_subset_of_largeFragmentWitness hS)

lemma sum_largeFragmentWitnesses_le_source_sum
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α}
    (w : Finset α → ℝ) (hw : ∀ S, 0 ≤ w S)
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    (∑ S ∈ largeFragmentWitnesses H m Z, w S) ≤
      ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), w S :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (largeFragmentWitnesses_subset_source_powerset_filter hT hTZ)
    (by intro S _ _; exact hw S)

omit [DecidableEq α] in
lemma sum_powerset_filter_pow_card_le_card_mul_pow
    (T : Finset α) (m : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card) ≤
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) := by
  calc
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card)
        ≤ ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ m := by
          refine Finset.sum_le_sum ?_
          intro S hS
          exact pow_le_pow_of_le_one ha0 ha1 (Finset.mem_filter.mp hS).2
    _ = (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) := by
          rw [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq α] in
lemma sum_powerset_filter_pow_card_le_two_pow_mul_pow
    (T : Finset α) (m : ℕ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card) ≤
      (2 : ℝ) ^ T.card * a ^ m := by
  have hsum :=
    sum_powerset_filter_pow_card_le_card_mul_pow T m ha0 ha1
  have hcard_nat :
      (T.powerset.filter fun S => m ≤ S.card).card ≤ T.powerset.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcard_real :
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ)) ≤
        (2 : ℝ) ^ T.card := by
    have hcast : (((T.powerset.filter fun S => m ≤ S.card).card : ℝ)) ≤
        (T.powerset.card : ℝ) := by
      exact_mod_cast hcard_nat
    simpa using hcast
  have hmul :
      (((T.powerset.filter fun S => m ≤ S.card).card : ℝ) * a ^ m) ≤
        (2 : ℝ) ^ T.card * a ^ m :=
    mul_le_mul_of_nonneg_right hcard_real (pow_nonneg ha0 m)
  exact hsum.trans hmul

lemma sum_largeFragmentWitnesses_pow_le_two_pow_mul_pow
    {H : Finset (Finset α)} {m : ℕ} {Z T : Finset α} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : T ∈ H) (hTZ : T ⊆ Z) :
    (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
      (2 : ℝ) ^ T.card * a ^ m := by
  have hle_source :
      (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
        ∑ S ∈ T.powerset.filter (fun S => m ≤ S.card), a ^ S.card :=
    sum_largeFragmentWitnesses_le_source_sum
      (fun S => a ^ S.card) (fun S => pow_nonneg ha0 S.card) hT hTZ
  exact hle_source.trans
    (sum_powerset_filter_pow_card_le_two_pow_mul_pow T m ha0 ha1)

/-- Pairs `(W,S)` with `W ⊆ X` and `S` a large minimal fragment after
exposing `W`. -/
def largeFragmentPairs
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ) :
    Finset (Finset α × Finset α) :=
  X.powerset.biUnion fun W =>
    (largeMinimalFragments m H W).image fun S => (W, S)

lemma disjoint_largeFragmentPair_fibers
    {H : Finset (Finset α)} {m : ℕ} {W W' : Finset α}
    (hWW' : W ≠ W') :
    Disjoint
      ((largeMinimalFragments m H W).image fun S => (W, S))
      ((largeMinimalFragments m H W').image fun S => (W', S)) := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  rcases Finset.mem_image.mp hP with ⟨S, _hS, hEq⟩
  rcases Finset.mem_image.mp hP' with ⟨S', _hS', hEq'⟩
  have hfirst : W = W' := by
    calc
      W = (W, S).1 := rfl
      _ = P.1 := congrArg Prod.fst hEq
      _ = (W', S').1 := (congrArg Prod.fst hEq').symm
      _ = W' := rfl
  exact hWW' hfirst

lemma pairwiseDisjoint_largeFragmentPair_fibers
    (H : Finset (Finset α)) (m : ℕ) :
    (X : Finset (Finset α)) →
      ∀ W ∈ X, ∀ W' ∈ X, W ≠ W' →
        Disjoint
          ((largeMinimalFragments m H W).image fun S => (W, S))
          ((largeMinimalFragments m H W').image fun S => (W', S)) :=
  fun _ W _ W' _ hWW' =>
    disjoint_largeFragmentPair_fibers (H := H) (m := m) (W := W) (W' := W') hWW'

@[simp]
lemma mem_largeFragmentPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    {P : Finset α × Finset α} :
    P ∈ largeFragmentPairs X H m ↔
      P.1 ⊆ X ∧ P.2 ∈ largeMinimalFragments m H P.1 := by
  constructor
  · intro hP
    rcases Finset.mem_biUnion.mp hP with ⟨W, hWXpow, hPimg⟩
    rcases Finset.mem_image.mp hPimg with ⟨S, hS, hEq⟩
    have hP1 : P.1 = W := (congrArg Prod.fst hEq).symm
    have hP2 : P.2 = S := (congrArg Prod.snd hEq).symm
    exact ⟨by simpa [hP1] using Finset.mem_powerset.mp hWXpow,
      by simpa [hP1, hP2] using hS⟩
  · intro h
    rcases P with ⟨W, S⟩
    exact Finset.mem_biUnion.mpr
      ⟨W, Finset.mem_powerset.mpr h.1,
        Finset.mem_image.mpr ⟨S, h.2, rfl⟩⟩

/-- Pairs `(Z,S)` where `S` is a large-fragment witness inside `Z`. -/
def largeWitnessPairs
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ) :
    Finset (Finset α × Finset α) :=
  X.powerset.biUnion fun Z =>
    (largeFragmentWitnesses H m Z).image fun S => (Z, S)

lemma disjoint_largeWitnessPair_fibers
    {H : Finset (Finset α)} {m : ℕ} {Z Z' : Finset α}
    (hZZ' : Z ≠ Z') :
    Disjoint
      ((largeFragmentWitnesses H m Z).image fun S => (Z, S))
      ((largeFragmentWitnesses H m Z').image fun S => (Z', S)) := by
  rw [Finset.disjoint_left]
  intro P hP hP'
  rcases Finset.mem_image.mp hP with ⟨S, _hS, hEq⟩
  rcases Finset.mem_image.mp hP' with ⟨S', _hS', hEq'⟩
  have hfirst : Z = Z' := by
    calc
      Z = (Z, S).1 := rfl
      _ = P.1 := congrArg Prod.fst hEq
      _ = (Z', S').1 := (congrArg Prod.fst hEq').symm
      _ = Z' := rfl
  exact hZZ' hfirst

lemma pairwiseDisjoint_largeWitnessPair_fibers
    (H : Finset (Finset α)) (m : ℕ) :
    (X : Finset (Finset α)) →
      ∀ Z ∈ X, ∀ Z' ∈ X, Z ≠ Z' →
        Disjoint
          ((largeFragmentWitnesses H m Z).image fun S => (Z, S))
          ((largeFragmentWitnesses H m Z').image fun S => (Z', S)) :=
  fun _ Z _ Z' _ hZZ' =>
    disjoint_largeWitnessPair_fibers (H := H) (m := m) (Z := Z) (Z' := Z') hZZ'

@[simp]
lemma mem_largeWitnessPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    {P : Finset α × Finset α} :
    P ∈ largeWitnessPairs X H m ↔
      P.1 ⊆ X ∧ P.2 ∈ largeFragmentWitnesses H m P.1 := by
  constructor
  · intro hP
    rcases Finset.mem_biUnion.mp hP with ⟨Z, hZXpow, hPimg⟩
    rcases Finset.mem_image.mp hPimg with ⟨S, hS, hEq⟩
    have hP1 : P.1 = Z := (congrArg Prod.fst hEq).symm
    have hP2 : P.2 = S := (congrArg Prod.snd hEq).symm
    exact ⟨by simpa [hP1] using Finset.mem_powerset.mp hZXpow,
      by simpa [hP1, hP2] using hS⟩
  · intro h
    rcases P with ⟨Z, S⟩
    exact Finset.mem_biUnion.mpr
      ⟨Z, Finset.mem_powerset.mpr h.1,
        Finset.mem_image.mpr ⟨S, h.2, rfl⟩⟩

def largeFragmentPairToWitness
    (P : Finset α × Finset α) : Finset α × Finset α :=
  (P.1 ∪ P.2, P.2)

lemma largeFragmentPairToWitness_mem
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    {P : Finset α × Finset α}
    (hP : P ∈ largeFragmentPairs X H m) :
    largeFragmentPairToWitness P ∈ largeWitnessPairs X H m := by
  rcases P with ⟨W, S⟩
  rcases mem_largeFragmentPairs.mp hP with ⟨hWX, hS⟩
  rw [mem_largeWitnessPairs]
  constructor
  · exact Finset.union_subset hWX (largeMinimalFragment_subset_ground hHX hS)
  · exact largeMinimalFragment_mem_witnesses_union hS

lemma largeFragmentPairToWitness_injOn
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ} :
    Set.InjOn (largeFragmentPairToWitness : Finset α × Finset α → Finset α × Finset α)
      (↑(largeFragmentPairs X H m)) := by
  intro P hP Q hQ hEq
  rcases P with ⟨W, S⟩
  rcases Q with ⟨W', S'⟩
  have hS_eq : S = S' := by
    exact congrArg Prod.snd hEq
  have hUnion_eq : W ∪ S = W' ∪ S' := by
    exact congrArg Prod.fst hEq
  rcases mem_largeFragmentPairs.mp hP with ⟨_hWX, hSlarge⟩
  rcases mem_largeFragmentPairs.mp hQ with ⟨_hW'X, hS'large⟩
  have hW_eq : W = W' := by
    have hleft :
        (W ∪ S) \ S = W :=
      union_sdiff_right_eq_left_of_disjoint
        (largeMinimalFragment_disjoint_exposure hSlarge)
    have hright :
        (W' ∪ S') \ S' = W' :=
      union_sdiff_right_eq_left_of_disjoint
        (largeMinimalFragment_disjoint_exposure hS'large)
    calc
      W = (W ∪ S) \ S := hleft.symm
      _ = (W' ∪ S') \ S' := by rw [hUnion_eq, hS_eq]
      _ = W' := hright
  simp [hW_eq, hS_eq]

lemma image_largeFragmentPairToWitness_subset
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X) :
    (largeFragmentPairs X H m).image largeFragmentPairToWitness ⊆
      largeWitnessPairs X H m := by
  intro Q hQ
  rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
  exact largeFragmentPairToWitness_mem hHX hP

lemma sum_largeFragmentPairs_toWitness_le_sum_witnessPairs
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ}
    (hHX : ∀ T ∈ H, T ⊆ X)
    (w : Finset α × Finset α → ℝ)
    (hw : ∀ P, 0 ≤ w P) :
    (∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P)) ≤
      ∑ Q ∈ largeWitnessPairs X H m, w Q := by
  have himage_subset := image_largeFragmentPairToWitness_subset
    (X := X) (H := H) (m := m) hHX
  calc
    (∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P))
        = ∑ Q ∈ (largeFragmentPairs X H m).image largeFragmentPairToWitness, w Q := by
          rw [Finset.sum_image (largeFragmentPairToWitness_injOn
            (X := X) (H := H) (m := m))]
    _ ≤ ∑ Q ∈ largeWitnessPairs X H m, w Q :=
        Finset.sum_le_sum_of_subset_of_nonneg himage_subset
          (by intro Q _ _; exact hw Q)

/-- Union of a finite list of exposure sets. -/
def exposureUnion : List (Finset α) → Finset α
  | [] => ∅
  | W :: Ws => W ∪ exposureUnion Ws

lemma exposureUnion_subset
    {Ws : List (Finset α)} {X : Finset α}
    (hWs : ∀ W ∈ Ws, W ⊆ X) :
    exposureUnion Ws ⊆ X := by
  induction Ws with
  | nil =>
      simp [exposureUnion]
  | cons W Ws ih =>
      intro x hx
      rcases Finset.mem_union.mp (by simpa [exposureUnion] using hx) with hxW | hxRest
      · exact hWs W (by simp) hxW
      · exact ih (by
          intro V hV
          exact hWs V (by simp [hV])) hxRest

lemma exposureUnion_union_subset
    {Ws : List (Finset α)} {V X : Finset α}
    (hWs : ∀ W ∈ Ws, W ⊆ X) (hV : V ⊆ X) :
    exposureUnion Ws ∪ V ⊆ X :=
  Finset.union_subset (exposureUnion_subset hWs) hV

/-- Iterated minimal-fragment family after exposing a finite list of sets. -/
def iteratedMinimalFragments (H : Finset (Finset α)) :
    List (Finset α) → Finset (Finset α)
  | [] => H
  | W :: Ws => iteratedMinimalFragments (minimalFragments H W) Ws

lemma exists_iteratedMinimalFragment_subset_iff_source_subset_union
    (H : Finset (Finset α)) (Ws : List (Finset α)) (V : Finset α) :
    (∃ T ∈ iteratedMinimalFragments H Ws, T ⊆ V) ↔
      ∃ S ∈ H, S ⊆ exposureUnion Ws ∪ V := by
  induction Ws generalizing H V with
  | nil =>
      simp [iteratedMinimalFragments, exposureUnion]
  | cons W Ws ih =>
      rw [iteratedMinimalFragments]
      rw [ih (H := minimalFragments H W) (V := V)]
      rw [exists_minimalFragment_subset_iff_source_subset_union
        (H := H) (W := W) (V := exposureUnion Ws ∪ V)]
      simp [exposureUnion, Finset.union_assoc]

/-- Exposing `V` after passing to minimal fragments of `F(H,W)` finds an empty
fragment exactly when some original source member is contained in `W ∪ V`. -/
lemma empty_mem_fragmentFamily_minimalFragments_iff
    {H : Finset (Finset α)} {W V : Finset α} :
    (∅ : Finset α) ∈ fragmentFamily (minimalFragments H W) V ↔
      ∃ S ∈ H, S ⊆ W ∪ V := by
  rw [empty_mem_fragmentFamily_iff]
  exact exists_minimalFragment_subset_iff_source_subset_union

/-- For any family, `∅` is a minimal member exactly when it belongs to the
family. -/
lemma empty_mem_minimalMembersIn_iff
    (X : Finset α) (U : Finset (Finset α)) :
    (∅ : Finset α) ∈ minimalMembersIn X U ↔ (∅ : Finset α) ∈ U := by
  constructor
  · intro h
    exact minimalMembersIn_subset h
  · intro h
    refine mem_minimalMembersIn.mpr ⟨h, ?_⟩
    intro T _hT hTlt
    have hT_empty : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      simpa using hTlt.subset hx
    exact hTlt.ne hT_empty

/-- The empty set is a minimal fragment exactly when some source member is
already contained in `W`. -/
lemma empty_mem_minimalFragments_iff
    {H : Finset (Finset α)} {W : Finset α} :
    (∅ : Finset α) ∈ minimalFragments H W ↔ ∃ S ∈ H, S ⊆ W := by
  rw [minimalFragments, empty_mem_minimalMembersIn_iff,
    empty_mem_fragmentFamily_iff]

end

end ParkPham
end Erdos202
