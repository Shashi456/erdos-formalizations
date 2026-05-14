/-
Erdos Problem 202 — Park–Pham layer, fragment iteration bookkeeping.

This file packages the deterministic Park--Vondrak iteration skeleton.  It
does not prove the probabilistic large-fragment estimate; it only proves that
if the accumulated large-fragment cost losses are strictly smaller than the
initial cover cost, then the final cutoff-`1` small-fragment step forces an
original generator to be contained in the union of the exposed sets.
-/

import Erdos.P202.ParkPham.FragmentCost

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Union of the exposure sets in a finite list of `(cutoff, exposure)` steps. -/
def smallStepExposureUnion : List (ℕ × Finset α) → Finset α
  | [] => ∅
  | step :: steps => step.2 ∪ smallStepExposureUnion steps

/-- Iteration of `smallMinimalFragments` along a finite list of
`(cutoff, exposure)` steps. -/
def iteratedSmallFragments (H : Finset (Finset α)) :
    List (ℕ × Finset α) → Finset (Finset α)
  | [] => H
  | step :: steps =>
      iteratedSmallFragments
        (smallMinimalFragments step.1 H step.2) steps

/-- Accumulated large-fragment cover-cost loss along the same finite
small-fragment iteration. -/
noncomputable def iteratedLargeCostSum
    (X : Finset α) (p : ℝ) (H : Finset (Finset α)) :
    List (ℕ × Finset α) → ℝ
  | [] => 0
  | step :: steps =>
      coverCost X (largeMinimalFragments step.1 H step.2) p +
        iteratedLargeCostSum X p
          (smallMinimalFragments step.1 H step.2) steps

/-- Convert a tuple of exposure sets and cutoff values into the list format
used by the deterministic fragment iteration. -/
def exposureTupleSteps {n : ℕ} (cutoff : Fin n → ℕ)
    (Ws : Fin n → Finset α) : List (ℕ × Finset α) :=
  List.ofFn fun i => (cutoff i, Ws i)

/-- Snoc-ordered version of `exposureTupleSteps`, convenient when the final
cutoff-`1` exposure must be peeled off. -/
def exposureTupleStepsSnoc :
    {n : ℕ} → (Fin n → ℕ) → (Fin n → Finset α) → List (ℕ × Finset α)
  | 0, _cutoff, _Ws => []
  | n + 1, cutoff, Ws =>
      exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc)
        (fun i : Fin n => Ws i.castSucc) ++
        [(cutoff (Fin.last n), Ws (Fin.last n))]

omit [DecidableEq α] in
lemma exposureTupleStepsSnoc_snoc {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
    (W : Finset α) :
    exposureTupleStepsSnoc cutoff
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws ++
        [(cutoff (Fin.last n), W)] := by
  simp [exposureTupleStepsSnoc]

lemma smallStepExposureUnion_exposureTupleSteps
    {n : ℕ} (cutoff : Fin n → ℕ) (Ws : Fin n → Finset α) :
    smallStepExposureUnion (exposureTupleSteps cutoff Ws) =
      exposureTupleUnion Ws := by
  induction n with
  | zero =>
      ext x
      simp [exposureTupleSteps, smallStepExposureUnion, exposureTupleUnion]
  | succ n ih =>
      have htail :=
        ih (fun i : Fin n => cutoff i.succ) (fun i : Fin n => Ws i.succ)
      have htail' :
          smallStepExposureUnion
              (List.ofFn fun i : Fin n => (cutoff i.succ, Ws i.succ)) =
            exposureTupleUnion (fun i : Fin n => Ws i.succ) := by
        simpa [exposureTupleSteps] using htail
      ext x
      rw [exposureTupleSteps, List.ofFn_succ]
      simp only [smallStepExposureUnion, Finset.mem_union]
      rw [htail']
      constructor
      · intro hx
        rcases hx with hx0 | hxtail
        · simpa [exposureTupleUnion] using
            (Exists.intro (0 : Fin (n + 1)) hx0)
        · rcases (by
            simpa [exposureTupleUnion] using hxtail :
              ∃ i : Fin n, x ∈ Ws i.succ) with ⟨i, hi⟩
          simpa [exposureTupleUnion] using
            (Exists.intro (i.succ : Fin (n + 1)) hi)
      · intro hx
        rcases (by
          simpa [exposureTupleUnion] using hx :
            ∃ i : Fin (n + 1), x ∈ Ws i) with ⟨i, hi⟩
        cases i using Fin.cases with
        | zero =>
            exact Or.inl hi
        | succ i =>
            exact Or.inr (by
              have : x ∈ exposureTupleUnion (fun i : Fin n => Ws i.succ) := by
                simpa [exposureTupleUnion] using (Exists.intro i hi)
              simpa using this)

lemma exists_exposure_largeCost_lt_of_bernoulli_average_lt
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ p B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (havg :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments m H W) p) < B) :
    ∃ W ∈ X.powerset,
      coverCost X (largeMinimalFragments m H W) p < B :=
  exists_powerset_value_lt_of_bernoulli_average_lt X
    (fun W => coverCost X (largeMinimalFragments m H W) p) hρ0 hρ1 havg

lemma bernoulli_average_largeCost_le_source_card_mul_pow
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ p : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) p) ≤
      (H.card : ℝ) * p ^ m := by
  have hpoint :
      ∀ W ∈ X.powerset,
        coverCost X (largeMinimalFragments m H W) p ≤
          (H.card : ℝ) * p ^ m := by
    intro W _hW
    exact coverCost_largeMinimalFragments_le_source_card_mul_pow
      hp0 hp1 hHX
  calc
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) p)
        ≤ ∑ W ∈ X.powerset,
            bernoulliMass X W ρ * ((H.card : ℝ) * p ^ m) := by
          refine Finset.sum_le_sum ?_
          intro W hW
          exact mul_le_mul_of_nonneg_left (hpoint W hW)
            (bernoulliMass_nonneg hρ0 hρ1)
    _ = (∑ W ∈ X.powerset, bernoulliMass X W ρ) *
          ((H.card : ℝ) * p ^ m) := by
          rw [Finset.sum_mul]
    _ = (H.card : ℝ) * p ^ m := by
          rw [sum_bernoulliMass_eq_one (α := α) X (p := ρ) (by ring)]
          ring

lemma exists_exposure_largeCost_lt_of_source_card_mul_pow_lt
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ p B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hbound : (H.card : ℝ) * p ^ m < B) :
    ∃ W ∈ X.powerset,
      coverCost X (largeMinimalFragments m H W) p < B := by
  have havg :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments m H W) p) < B :=
    (bernoulli_average_largeCost_le_source_card_mul_pow
      X H m hρ0 hρ1 hp0 hp1 hHX).trans_lt hbound
  exact exists_exposure_largeCost_lt_of_bernoulli_average_lt
    X H m hρ0 hρ1 havg

lemma sum_largeFragmentPairs_eq_nested
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (w : Finset α × Finset α → ℝ) :
    (∑ P ∈ largeFragmentPairs X H m, w P) =
      ∑ W ∈ X.powerset,
        ∑ S ∈ largeMinimalFragments m H W, w (W, S) := by
  unfold largeFragmentPairs
  rw [Finset.sum_biUnion (pairwiseDisjoint_largeFragmentPair_fibers H m X.powerset)]
  refine Finset.sum_congr rfl ?_
  intro W _hW
  rw [Finset.sum_image]
  intro S _hS T _hT hEq
  exact congrArg Prod.snd hEq

lemma bernoulli_average_largeCoverWeight_eq_pair_sum
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (ρ q : ℝ) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ * coverWeight (largeMinimalFragments m H W) q) =
      ∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card := by
  rw [sum_largeFragmentPairs_eq_nested]
  unfold coverWeight
  refine Finset.sum_congr rfl ?_
  intro W _hW
  rw [Finset.mul_sum]

lemma sum_largeWitnessPairs_eq_nested
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    (w : Finset α × Finset α → ℝ) :
    (∑ P ∈ largeWitnessPairs X H m, w P) =
      ∑ Z ∈ X.powerset,
        ∑ S ∈ largeFragmentWitnesses H m Z, w (Z, S) := by
  unfold largeWitnessPairs
  rw [Finset.sum_biUnion (pairwiseDisjoint_largeWitnessPair_fibers H m X.powerset)]
  refine Finset.sum_congr rfl ?_
  intro Z _hZ
  rw [Finset.sum_image]
  intro S _hS T _hT hEq
  exact congrArg Prod.snd hEq

lemma bernoulli_average_largeCost_le_pair_sum
    (X : Finset α) (H : Finset (Finset α)) (m : ℕ)
    {ρ q : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q) ≤
      ∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card := by
  calc
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q)
        ≤ ∑ W ∈ X.powerset,
            bernoulliMass X W ρ *
              coverWeight (largeMinimalFragments m H W) q := by
          refine Finset.sum_le_sum ?_
          intro W _hW
          have hcost :
              coverCost X (largeMinimalFragments m H W) q ≤
                coverWeight (largeMinimalFragments m H W) q :=
            coverCost_le_coverWeight_self
              (fun T hT => largeMinimalFragment_subset_ground hHX hT)
          exact mul_le_mul_of_nonneg_left hcost
            (bernoulliMass_nonneg hρ0 hρ1)
    _ = ∑ P ∈ largeFragmentPairs X H m,
          bernoulliMass X P.1 ρ * q ^ P.2.card :=
        bernoulli_average_largeCoverWeight_eq_pair_sum X H m ρ q

lemma largeFragment_pair_sum_le_witness_sum
    (X : Finset α) (H : Finset (Finset α)) (m L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X) :
    (∑ P ∈ largeFragmentPairs X H m,
      bernoulliMass X P.1 ρ * q ^ P.2.card) ≤
      ∑ Q ∈ largeWitnessPairs X H m,
        bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  let w : Finset α × Finset α → ℝ :=
    fun Q => bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card
  have hterm :
      (∑ P ∈ largeFragmentPairs X H m,
        bernoulliMass X P.1 ρ * q ^ P.2.card) ≤
        ∑ P ∈ largeFragmentPairs X H m, w (largeFragmentPairToWitness P) := by
    refine Finset.sum_le_sum ?_
    intro P hP
    rcases P with ⟨W, S⟩
    rcases mem_largeFragmentPairs.mp hP with ⟨hWX, hSlarge⟩
    have hdisj : Disjoint S W :=
      largeMinimalFragment_disjoint_exposure hSlarge
    have hUnionX : W ∪ S ⊆ X :=
      Finset.union_subset hWX (largeMinimalFragment_subset_ground hHX hSlarge)
    exact bernoulliMass_mul_pow_le_union_mul_inv_nat_pow
      (X := X) (W := W) (S := S) (q := q) (ρ := ρ) (L := L)
      hL hq0 hq1 hρ hdisj hUnionX
  have hw_nonneg : ∀ Q, 0 ≤ w Q := by
    intro Q
    exact mul_nonneg (bernoulliMass_nonneg hρ0 hρ1)
      (pow_nonneg (by positivity : 0 ≤ (1 / (L : ℝ))) Q.2.card)
  exact hterm.trans
    (sum_largeFragmentPairs_toWitness_le_sum_witnessPairs hHX w hw_nonneg)

lemma largeWitness_sum_le_muP_mul_two_pow
    (X : Finset α) (H : Finset (Finset α)) (m ell : ℕ)
    {ρ a : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hHbound : ∀ T ∈ H, T.card ≤ ell) :
    (∑ Q ∈ largeWitnessPairs X H m,
      bernoulliMass X Q.1 ρ * a ^ Q.2.card) ≤
      muP X (upClosureIn X H) ρ * ((2 : ℝ) ^ ell * a ^ m) := by
  let B : ℝ := (2 : ℝ) ^ ell * a ^ m
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hinner_zero :
      ∀ Z ∈ X.powerset, Z ∉ upClosureIn X H →
        (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card) = 0 := by
    intro Z _hZ hZnot
    have hno : ¬ ∃ T ∈ H, T ⊆ Z := by
      intro h
      exact hZnot (mem_upClosureIn.mpr
        ⟨Finset.mem_powerset.mp _hZ, h⟩)
    rw [largeFragmentWitnesses_eq_empty_of_no_source_subset hno]
    simp
  have hinner_bound :
      ∀ Z ∈ X.powerset, Z ∈ upClosureIn X H →
        (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card) ≤
          bernoulliMass X Z ρ * B := by
    intro Z _hZ hZU
    rcases mem_upClosureIn.mp hZU with ⟨_hZX, T, hT, hTZ⟩
    have hsum_le :
        (∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card) ≤
          (2 : ℝ) ^ T.card * a ^ m :=
      sum_largeFragmentWitnesses_pow_le_two_pow_mul_pow ha0 ha1 hT hTZ
    have hT_le : T.card ≤ ell := hHbound T hT
    have hpow2_le : (2 : ℝ) ^ T.card ≤ (2 : ℝ) ^ ell :=
      pow_le_pow_right₀ (by norm_num) hT_le
    have hsource_le_B :
        (2 : ℝ) ^ T.card * a ^ m ≤ B := by
      exact mul_le_mul_of_nonneg_right hpow2_le (pow_nonneg ha0 m)
    calc
      (∑ S ∈ largeFragmentWitnesses H m Z,
          bernoulliMass X Z ρ * a ^ S.card)
          = bernoulliMass X Z ρ *
              ∑ S ∈ largeFragmentWitnesses H m Z, a ^ S.card := by
            rw [Finset.mul_sum]
      _ ≤ bernoulliMass X Z ρ * ((2 : ℝ) ^ T.card * a ^ m) :=
            mul_le_mul_of_nonneg_left hsum_le
              (bernoulliMass_nonneg hρ0 hρ1)
      _ ≤ bernoulliMass X Z ρ * B :=
            mul_le_mul_of_nonneg_left hsource_le_B
              (bernoulliMass_nonneg hρ0 hρ1)
  calc
    (∑ Q ∈ largeWitnessPairs X H m,
      bernoulliMass X Q.1 ρ * a ^ Q.2.card)
        = ∑ Z ∈ X.powerset,
            ∑ S ∈ largeFragmentWitnesses H m Z,
              bernoulliMass X Z ρ * a ^ S.card := by
          rw [sum_largeWitnessPairs_eq_nested]
    _ = ∑ Z ∈ X.powerset,
            if Z ∈ upClosureIn X H then
              ∑ S ∈ largeFragmentWitnesses H m Z,
                bernoulliMass X Z ρ * a ^ S.card
            else 0 := by
          refine Finset.sum_congr rfl ?_
          intro Z hZ
          by_cases hZU : Z ∈ upClosureIn X H
          · simp [hZU]
          · simp [hZU, hinner_zero Z hZ hZU]
    _ = ∑ Z ∈ X.powerset.filter (fun Z => Z ∈ upClosureIn X H),
            ∑ S ∈ largeFragmentWitnesses H m Z,
              bernoulliMass X Z ρ * a ^ S.card := by
          rw [Finset.sum_filter]
    _ ≤ ∑ Z ∈ X.powerset.filter (fun Z => Z ∈ upClosureIn X H),
            bernoulliMass X Z ρ * B := by
          refine Finset.sum_le_sum ?_
          intro Z hZ
          exact hinner_bound Z (Finset.mem_filter.mp hZ).1
            (Finset.mem_filter.mp hZ).2
    _ = muP X (upClosureIn X H) ρ * B := by
          unfold muP
          rw [← Finset.sum_mul]

/-- Loose uniform Park--Vondrak large-fragment cost lemma.  This is the
`2^ell / L^m` version mentioned in the paper, sufficient for a large absolute
constant in the expectation-threshold theorem. -/
lemma bernoulli_average_largeCost_le_muP_mul_two_pow_inv
    (X : Finset α) (H : Finset (Finset α)) (m ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q) ≤
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  have hinv0 : 0 ≤ (1 / (L : ℝ)) := by positivity
  have hinv1 : (1 / (L : ℝ)) ≤ 1 := by
    rw [div_le_one hLpos]
    exact_mod_cast hL
  calc
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρ *
        coverCost X (largeMinimalFragments m H W) q)
        ≤ ∑ P ∈ largeFragmentPairs X H m,
            bernoulliMass X P.1 ρ * q ^ P.2.card :=
          bernoulli_average_largeCost_le_pair_sum X H m hρ0 hρ1 hHX
    _ ≤ ∑ Q ∈ largeWitnessPairs X H m,
          bernoulliMass X Q.1 ρ * (1 / (L : ℝ)) ^ Q.2.card :=
          largeFragment_pair_sum_le_witness_sum
            X H m L hL hq0 hq1 hρ hHX
    _ ≤ muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) :=
          largeWitness_sum_le_muP_mul_two_pow
            X H m ell hρ0 hρ1 hinv0 hinv1 hHbound

/-- If the Park--Vondrak large-fragment expectation bound is below a budget,
then one exposure has large-fragment cost below that budget. -/
lemma exists_exposure_largeCost_lt_of_muP_mul_two_pow_inv_lt
    (X : Finset α) (H : Finset (Finset α)) (m ell L : ℕ)
    {q ρ B : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell)
    (hbound :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ m) < B) :
    ∃ W ∈ X.powerset,
      coverCost X (largeMinimalFragments m H W) q < B := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have havg_lt :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments m H W) q) < B :=
    (bernoulli_average_largeCost_le_muP_mul_two_pow_inv
      X H m ell L hL hq0 hq1 hρ hHX hHbound).trans_lt hbound
  exact exists_exposure_largeCost_lt_of_bernoulli_average_lt
    X H m hρ0 hρ1 havg_lt

lemma smallStepExposureUnion_subset
    {steps : List (ℕ × Finset α)} {X : Finset α}
    (hsteps : ∀ step ∈ steps, step.2 ⊆ X) :
    smallStepExposureUnion steps ⊆ X := by
  induction steps with
  | nil =>
      simp [smallStepExposureUnion]
  | cons step steps ih =>
      intro x hx
      rcases Finset.mem_union.mp (by
        simpa [smallStepExposureUnion] using hx) with hxStep | hxRest
      · exact hsteps step (by simp) hxStep
      · exact ih (by
          intro step' hstep'
          exact hsteps step' (by simp [hstep'])) hxRest

lemma smallStepExposureUnion_append_singleton
    (steps : List (ℕ × Finset α)) (step : ℕ × Finset α) :
    smallStepExposureUnion (steps ++ [step]) =
      smallStepExposureUnion steps ∪ step.2 := by
  induction steps with
  | nil =>
      simp [smallStepExposureUnion]
  | cons head steps ih =>
      simp [smallStepExposureUnion, ih, Finset.union_assoc]

lemma smallStepExposureUnion_exposureTupleStepsSnoc
    {n : ℕ} (cutoff : Fin n → ℕ) (Ws : Fin n → Finset α) :
    smallStepExposureUnion (exposureTupleStepsSnoc cutoff Ws) =
      exposureTupleUnion Ws := by
  induction n with
  | zero =>
      ext x
      simp [exposureTupleStepsSnoc, smallStepExposureUnion, exposureTupleUnion]
  | succ n ih =>
      rw [exposureTupleStepsSnoc]
      rw [smallStepExposureUnion_append_singleton]
      rw [ih]
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxtail | hxlast
        · rcases (by
            simpa [exposureTupleUnion] using hxtail :
              ∃ i : Fin n, x ∈ Ws i.castSucc) with ⟨i, hi⟩
          simpa [exposureTupleUnion] using
            (Exists.intro (i.castSucc : Fin (n + 1)) hi)
        · simpa [exposureTupleUnion] using
            (Exists.intro (Fin.last n) hxlast)
      · intro hx
        rcases (by
          simpa [exposureTupleUnion] using hx :
            ∃ i : Fin (n + 1), x ∈ Ws i) with ⟨i, hi⟩
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact Finset.mem_union.mpr (Or.inl (by
            simpa [exposureTupleUnion] using (Exists.intro j hi)))
        · exact Finset.mem_union.mpr (Or.inr hi)

lemma exposureTupleStepsSnoc_last_shape
    {X : Finset α} {n : ℕ} {cutoff : Fin (n + 1) → ℕ}
    {Ws : Fin (n + 1) → Finset α}
    (hWs : Ws ∈ exposureTupleSpace X (n + 1))
    (hlast : cutoff (Fin.last n) = 1) :
    ∃ steps V,
      exposureTupleStepsSnoc cutoff Ws = steps ++ [(1, V)] ∧
      smallStepExposureUnion steps ∪ V ⊆ X := by
  refine ⟨exposureTupleStepsSnoc
      (fun i : Fin n => cutoff i.castSucc)
      (fun i : Fin n => Ws i.castSucc),
    Ws (Fin.last n), ?_, ?_⟩
  · simp [exposureTupleStepsSnoc, hlast]
  · rw [smallStepExposureUnion_exposureTupleStepsSnoc]
    intro x hx
    rcases Finset.mem_union.mp hx with hxtail | hxlast
    · rcases (by
        simpa [exposureTupleUnion] using hxtail :
          ∃ i : Fin n, x ∈ Ws i.castSucc) with ⟨i, hi⟩
      exact Finset.mem_powerset.mp ((mem_exposureTupleSpace.mp hWs) i.castSucc) hi
    · exact Finset.mem_powerset.mp
        ((mem_exposureTupleSpace.mp hWs) (Fin.last n)) hxlast

lemma smallStepExposureUnion_exposureTupleSteps_append_singleton
    {n : ℕ} (cutoff : Fin n → ℕ) (Ws : Fin n → Finset α)
    (V : Finset α) :
    smallStepExposureUnion (exposureTupleSteps cutoff Ws ++ [(1, V)]) =
      exposureTupleUnion Ws ∪ V := by
  rw [smallStepExposureUnion_append_singleton,
    smallStepExposureUnion_exposureTupleSteps]

lemma exposureTupleSteps_append_singleton_shape
    {X : Finset α} {n : ℕ} {cutoff : Fin n → ℕ}
    {Ws : Fin n → Finset α} {V : Finset α}
    (hWs : Ws ∈ exposureTupleSpace X n) (hV : V ⊆ X) :
    ∃ steps V',
      exposureTupleSteps cutoff Ws ++ [(1, V)] = steps ++ [(1, V')] ∧
      smallStepExposureUnion steps ∪ V' ⊆ X := by
  refine ⟨exposureTupleSteps cutoff Ws, V, rfl, ?_⟩
  rw [smallStepExposureUnion_exposureTupleSteps]
  exact Finset.union_subset (exposureTupleUnion_subset hWs) hV

lemma iteratedSmallFragments_append_singleton
    (H : Finset (Finset α)) (steps : List (ℕ × Finset α))
    (step : ℕ × Finset α) :
    iteratedSmallFragments H (steps ++ [step]) =
      smallMinimalFragments step.1 (iteratedSmallFragments H steps) step.2 := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedSmallFragments]
  | cons head steps ih =>
      simp [iteratedSmallFragments, ih]

lemma smallMinimalFragments_subset_ground
    {X : Finset α} {H : Finset (Finset α)} {m : ℕ} {W : Finset α}
    (hHX : ∀ S ∈ H, S ⊆ X) :
    ∀ T ∈ smallMinimalFragments m H W, T ⊆ X := by
  intro T hT x hx
  rcases mem_smallMinimalFragments.mp hT with ⟨hTmin, _hsmall⟩
  rcases mem_fragmentFamily.mp
      (minimalFragments_subset_fragmentFamily H W hTmin) with
    ⟨S, hS, rfl⟩
  exact hHX S hS (Finset.mem_sdiff.mp hx).1

lemma smallMinimalFragments_card_le_of_forall_card_le
    {H : Finset (Finset α)} {m ℓ : ℕ} {W : Finset α}
    (hH : ∀ S ∈ H, S.card ≤ ℓ) :
    ∀ T ∈ smallMinimalFragments m H W, T.card ≤ ℓ := by
  intro T hT
  exact minimalFragments_card_le_of_forall_card_le hH
    (mem_smallMinimalFragments.mp hT).1

lemma iteratedSmallFragments_subset_ground
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α))
    (hHX : ∀ S ∈ H, S ⊆ X) :
    ∀ T ∈ iteratedSmallFragments H steps, T ⊆ X := by
  induction steps generalizing H with
  | nil =>
      simpa [iteratedSmallFragments] using hHX
  | cons step steps ih =>
      simpa [iteratedSmallFragments] using
        ih (H := smallMinimalFragments step.1 H step.2)
          (smallMinimalFragments_subset_ground (X := X) hHX)

lemma iteratedSmallFragments_card_le_of_forall_card_le
    (H : Finset (Finset α)) (steps : List (ℕ × Finset α)) {ℓ : ℕ}
    (hH : ∀ S ∈ H, S.card ≤ ℓ) :
    ∀ T ∈ iteratedSmallFragments H steps, T.card ≤ ℓ := by
  induction steps generalizing H with
  | nil =>
      simpa [iteratedSmallFragments] using hH
  | cons step steps ih =>
      simpa [iteratedSmallFragments] using
        ih (H := smallMinimalFragments step.1 H step.2)
          (smallMinimalFragments_card_le_of_forall_card_le hH)

lemma iteratedLargeCostSum_nonneg
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ iteratedLargeCostSum X p H steps := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedLargeCostSum]
  | cons step steps ih =>
      have hcost :
          0 ≤ coverCost X (largeMinimalFragments step.1 H step.2) p :=
        coverCost_nonneg hp0
      have hrest :
          0 ≤ iteratedLargeCostSum X p
            (smallMinimalFragments step.1 H step.2) steps :=
        ih (H := smallMinimalFragments step.1 H step.2)
      simpa [iteratedLargeCostSum] using add_nonneg hcost hrest

lemma iteratedLargeCostSum_append_singleton
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (step : ℕ × Finset α) {p : ℝ} :
    iteratedLargeCostSum X p H (steps ++ [step]) =
      iteratedLargeCostSum X p H steps +
        coverCost X
          (largeMinimalFragments step.1 (iteratedSmallFragments H steps) step.2) p := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedLargeCostSum, iteratedSmallFragments]
  | cons head steps ih =>
      simp [iteratedLargeCostSum, iteratedSmallFragments, ih, add_assoc]

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_snoc
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
    (W : Finset α) :
    iteratedLargeCostSum X p H
        (exposureTupleStepsSnoc cutoff
          (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W)) =
      iteratedLargeCostSum X p H
        (exposureTupleStepsSnoc
          (fun i : Fin n => cutoff i.castSucc) Ws) +
        coverCost X
          (largeMinimalFragments (cutoff (Fin.last n))
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) W) p := by
  rw [exposureTupleStepsSnoc_snoc]
  simpa using
    iteratedLargeCostSum_append_singleton
      (X := X) (H := H)
      (steps := exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws)
      (step := (cutoff (Fin.last n), W)) (p := p)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω)) =
      ∑ W ∈ X.powerset,
        ∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
              bernoulliMass X W (ρ (Fin.last n))) *
            (iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
              coverCost X
                (largeMinimalFragments (cutoff (Fin.last n))
                  (iteratedSmallFragments H
                    (exposureTupleStepsSnoc
                      (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) := by
  classical
  let e : Finset α × (Fin n → Finset α) ↪
      (Fin (n + 1) → Finset α) :=
    (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding
  calc
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω))
        = ∑ P ∈ (X.powerset ×ˢ exposureTupleSpace X n),
            exposureTupleWeight X ρ (e P) *
              iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc cutoff (e P)) := by
            rw [exposureTupleSpace_snoc X n, Finset.sum_map]
    _ = ∑ W ∈ X.powerset,
        ∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
              bernoulliMass X W (ρ (Fin.last n))) *
            (iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
              coverCost X
                (largeMinimalFragments (cutoff (Fin.last n))
                  (iteratedSmallFragments H
                    (exposureTupleStepsSnoc
                      (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl ?_
          intro W _hW
          refine Finset.sum_congr rfl ?_
          intro Ws _hWs
          change
            exposureTupleWeight X ρ
                (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) *
              iteratedLargeCostSum X p H
                (exposureTupleStepsSnoc cutoff
                  (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W)) =
            (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
                bernoulliMass X W (ρ (Fin.last n))) *
              (iteratedLargeCostSum X p H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws) +
                coverCost X
                  (largeMinimalFragments (cutoff (Fin.last n))
                    (iteratedSmallFragments H
                      (exposureTupleStepsSnoc
                        (fun i : Fin n => cutoff i.castSucc) Ws)) W) p)
          rw [exposureTupleWeight_snoc,
            iteratedLargeCostSum_exposureTupleStepsSnoc_snoc]

lemma bernoulli_average_iterated_final_largeCost_le_muP_mul_two_pow_inv
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q ρlast : ℝ} {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin n → Finset α)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρlast = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W ρlast *
        coverCost X
          (largeMinimalFragments (cutoff (Fin.last n))
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
      muP X
        (upClosureIn X
          (iteratedSmallFragments H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws))) ρlast *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)) := by
  exact bernoulli_average_largeCost_le_muP_mul_two_pow_inv
    X
    (iteratedSmallFragments H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws))
    (cutoff (Fin.last n)) ell L hL hq0 hq1 hρlast
    (iteratedSmallFragments_subset_ground X H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws) hHX)
    (iteratedSmallFragments_card_le_of_forall_card_le H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws) hHbound)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (B : (Fin n → Finset α) → ℝ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hfinal :
      ∀ Ws ∈ exposureTupleSpace X n,
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) p) ≤
          B Ws) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ω)) ≤
      ∑ Ws ∈ exposureTupleSpace X n,
        (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
            iteratedLargeCostSum X p H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws) +
          exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws * B Ws) := by
  classical
  rw [iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro Ws hWs
  let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
  let ρlast : ℝ := ρ (Fin.last n)
  let loss : ℝ :=
    iteratedLargeCostSum X p H
      (exposureTupleStepsSnoc
        (fun i : Fin n => cutoff i.castSucc) Ws)
  let finalCost : Finset α → ℝ := fun W =>
    coverCost X
      (largeMinimalFragments (cutoff (Fin.last n))
        (iteratedSmallFragments H
          (exposureTupleStepsSnoc
            (fun i : Fin n => cutoff i.castSucc) Ws)) W) p
  let wt : ℝ := exposureTupleWeight X ρtail Ws
  have hwt0 : 0 ≤ wt := by
    dsimp [wt, ρtail]
    exact exposureTupleWeight_nonneg X
      (fun i : Fin n => hρ0 i.castSucc)
      (fun i : Fin n => hρ1 i.castSucc) Ws
  have hinner_eq :
      (∑ W ∈ X.powerset,
        (wt * bernoulliMass X W ρlast) * (loss + finalCost W)) =
        wt * loss +
          wt * (∑ W ∈ X.powerset,
            bernoulliMass X W ρlast * finalCost W) := by
    calc
      (∑ W ∈ X.powerset,
        (wt * bernoulliMass X W ρlast) * (loss + finalCost W))
          = ∑ W ∈ X.powerset,
            (  bernoulliMass X W ρlast * (wt * loss) +
                wt * (bernoulliMass X W ρlast * finalCost W)) := by
              refine Finset.sum_congr rfl ?_
              intro W _hW
              ring
      _ = (∑ W ∈ X.powerset, bernoulliMass X W ρlast) * (wt * loss) +
            wt * (∑ W ∈ X.powerset,
              bernoulliMass X W ρlast * finalCost W) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = wt * loss +
            wt * (∑ W ∈ X.powerset,
              bernoulliMass X W ρlast * finalCost W) := by
              rw [sum_bernoulliMass_eq_one (α := α) X (p := ρlast) (by ring)]
              ring
  calc
    (∑ W ∈ X.powerset,
      (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          bernoulliMass X W (ρ (Fin.last n))) *
        (iteratedLargeCostSum X p H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) +
          coverCost X
            (largeMinimalFragments (cutoff (Fin.last n))
              (iteratedSmallFragments H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws)) W) p))
        = wt * loss +
          wt * (∑ W ∈ X.powerset,
            bernoulliMass X W ρlast * finalCost W) := by
            simpa [wt, loss, finalCost, ρtail, ρlast] using hinner_eq
    _ ≤ wt * loss + wt * B Ws := by
          have hmul_le :
              wt * (∑ W ∈ X.powerset,
                bernoulliMass X W ρlast * finalCost W) ≤ wt * B Ws :=
            mul_le_mul_of_nonneg_left (by
              simpa [finalCost, ρlast] using hfinal Ws hWs) hwt0
          linarith
    _ = exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          iteratedLargeCostSum X p H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) +
        exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws * B Ws := by
          simp [wt, loss, ρtail]

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_muP_final
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρ (Fin.last n) = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
      ∑ Ws ∈ exposureTupleSpace X n,
        (exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws) +
          exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
            (muP X
              (upClosureIn X
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)))
                (ρ (Fin.last n)) *
              ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)))) := by
  refine
    iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le
      X H ρ cutoff
      (fun Ws =>
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) *
          ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)))
      hρ0 hρ1 ?_
  intro Ws _hWs
  exact bernoulli_average_iterated_final_largeCost_le_muP_mul_two_pow_inv
    X H ell L cutoff Ws hL hq0 hq1 hρlast hHX hHbound

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρ (Fin.last n) = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
      (∑ Ws ∈ exposureTupleSpace X n,
        exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          iteratedLargeCostSum X q H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws)) +
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)) := by
  classical
  let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
  let C : ℝ := (2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbase :=
    iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_muP_final
      X H ell L ρ cutoff hρ0 hρ1 hL hq0 hq1 hρlast hHX hHbound
  have hsum_le :
      (∑ Ws ∈ exposureTupleSpace X n,
        (exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws) +
          exposureTupleWeight X ρtail Ws *
            (muP X
              (upClosureIn X
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)))
                (ρ (Fin.last n)) * C))) ≤
        ∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C) := by
    refine Finset.sum_le_sum ?_
    intro Ws _hWs
    have hwt0 : 0 ≤ exposureTupleWeight X ρtail Ws := by
      dsimp [ρtail]
      exact exposureTupleWeight_nonneg X
        (fun i : Fin n => hρ0 i.castSucc)
        (fun i : Fin n => hρ1 i.castSucc) Ws
    have hmu_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) ≤ 1 :=
      muP_le_one (hρ0 (Fin.last n)) (hρ1 (Fin.last n))
    have hmuC_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) * C ≤ C := by
      have := mul_le_mul_of_nonneg_right hmu_le hC0
      simpa using this
    have hterm :
        exposureTupleWeight X ρtail Ws *
            (muP X
              (upClosureIn X
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)))
              (ρ (Fin.last n)) * C) ≤
          exposureTupleWeight X ρtail Ws * C :=
      mul_le_mul_of_nonneg_left hmuC_le hwt0
    have h := add_le_add_right hterm
      (exposureTupleWeight X ρtail Ws *
        iteratedLargeCostSum X q H
          (exposureTupleStepsSnoc
            (fun i : Fin n => cutoff i.castSucc) Ws))
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hsum_eq :
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C)) =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
    calc
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C))
          =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          ∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws * C := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws) * C := by
            rw [Finset.sum_mul]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
            rw [sum_exposureTupleWeight_eq_one X ρtail]
            ring
  exact hbase.trans (hsum_le.trans_eq hsum_eq)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget_of_current_bound
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin (n + 1) → ℝ) (cutoff : Fin (n + 1) → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρlast : ρ (Fin.last n) = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hCurrentBound :
      ∀ Ws ∈ exposureTupleSpace X n,
        ∀ S ∈ iteratedSmallFragments H
          (exposureTupleStepsSnoc
            (fun i : Fin n => cutoff i.castSucc) Ws),
          S.card ≤ ell) :
    (∑ Ω ∈ exposureTupleSpace X (n + 1),
      exposureTupleWeight X ρ Ω *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
      (∑ Ws ∈ exposureTupleSpace X n,
        exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
          iteratedLargeCostSum X q H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws)) +
        ((2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)) := by
  classical
  let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
  let C : ℝ := (2 : ℝ) ^ ell * (1 / (L : ℝ)) ^ cutoff (Fin.last n)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfinal :
      ∀ Ws ∈ exposureTupleSpace X n,
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
          C := by
    intro Ws hWs
    have hlarge :
        (∑ W ∈ X.powerset,
          bernoulliMass X W (ρ (Fin.last n)) *
            coverCost X
              (largeMinimalFragments (cutoff (Fin.last n))
                (iteratedSmallFragments H
                  (exposureTupleStepsSnoc
                    (fun i : Fin n => cutoff i.castSucc) Ws)) W) q) ≤
          muP X
            (upClosureIn X
              (iteratedSmallFragments H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws)))
            (ρ (Fin.last n)) * C := by
      simpa [C] using
        bernoulli_average_largeCost_le_muP_mul_two_pow_inv
          X
          (iteratedSmallFragments H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws))
          (cutoff (Fin.last n)) ell L hL hq0 hq1 hρlast
          (iteratedSmallFragments_subset_ground X H
            (exposureTupleStepsSnoc
              (fun i : Fin n => cutoff i.castSucc) Ws) hHX)
          (hCurrentBound Ws hWs)
    have hmu_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) ≤ 1 :=
      muP_le_one (hρ0 (Fin.last n)) (hρ1 (Fin.last n))
    have hmuC_le :
        muP X
          (upClosureIn X
            (iteratedSmallFragments H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)))
          (ρ (Fin.last n)) * C ≤ C := by
      have := mul_le_mul_of_nonneg_right hmu_le hC0
      simpa using this
    exact hlarge.trans hmuC_le
  have hbase :=
    iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le
      X H ρ cutoff (fun _Ws => C) hρ0 hρ1 hfinal
  have hsum_eq :
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C)) =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
    calc
      (∑ Ws ∈ exposureTupleSpace X n,
          (exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc
                  (fun i : Fin n => cutoff i.castSucc) Ws) +
            exposureTupleWeight X ρtail Ws * C))
          =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          ∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws * C := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) +
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws) * C := by
            rw [Finset.sum_mul]
      _ =
        (∑ Ws ∈ exposureTupleSpace X n,
          exposureTupleWeight X ρtail Ws *
            iteratedLargeCostSum X q H
              (exposureTupleStepsSnoc
                (fun i : Fin n => cutoff i.castSucc) Ws)) + C := by
            rw [sum_exposureTupleWeight_eq_one X ρtail]
            ring
  exact hbase.trans_eq hsum_eq

lemma iteratedSmallFragments_exposureTupleStepsSnoc_card_lt_last
    (H : Finset (Finset α)) {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin (n + 1) → Finset α) :
    ∀ T ∈ iteratedSmallFragments H (exposureTupleStepsSnoc cutoff Ws),
      T.card < cutoff (Fin.last n) := by
  intro T hT
  rw [exposureTupleStepsSnoc, iteratedSmallFragments_append_singleton] at hT
  exact (mem_smallMinimalFragments.mp hT).2

lemma iteratedSmallFragments_exposureTupleStepsSnoc_card_le_last
    (H : Finset (Finset α)) {n : ℕ}
    (cutoff : Fin (n + 1) → ℕ) (Ws : Fin (n + 1) → Finset α) :
    ∀ T ∈ iteratedSmallFragments H (exposureTupleStepsSnoc cutoff Ws),
      T.card ≤ cutoff (Fin.last n) := by
  intro T hT
  exact Nat.le_of_lt
    (iteratedSmallFragments_exposureTupleStepsSnoc_card_lt_last H cutoff Ws T hT)

/-- Cardinality bound available just before the last snoc stage.  If there is
no previous stage, this is the original bound `ell`; otherwise it is the cutoff
from the previous small-fragment step. -/
def snocCurrentCardBound :
    {n : ℕ} → ℕ → (Fin n → ℕ) → ℕ
  | 0, ell, _cutoff => ell
  | n + 1, _ell, cutoff => cutoff (Fin.last n)

/-- Recursive large-fragment budget for a snoc-ordered exposure tuple, charging
each stage against the cardinality bound available immediately before that
stage. -/
noncomputable def snocLargeCostBudget :
    {n : ℕ} → ℕ → (Fin n → ℕ) → (Fin n → ℕ) → ℝ
  | 0, _ell, _cutoff, _L => 0
  | n + 1, ell, cutoff, L =>
      snocLargeCostBudget ell
        (fun i : Fin n => cutoff i.castSucc)
        (fun i : Fin n => L i.castSucc) +
        (2 : ℝ) ^
            snocCurrentCardBound ell
              (fun i : Fin n => cutoff i.castSucc) *
          (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_snocLargeCostBudget
    (X : Finset α) (H : Finset (Finset α)) (ell : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin n → ℝ) (cutoff L : Fin n → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : ∀ i, 1 ≤ L i) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ∀ i, ρ i = 1 - (1 - q) ^ L i)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ws ∈ exposureTupleSpace X n,
      exposureTupleWeight X ρ Ws *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) ≤
      snocLargeCostBudget ell cutoff L := by
  classical
  induction n with
  | zero =>
      simp [snocLargeCostBudget, exposureTupleSpace, exposureTupleWeight,
        exposureTupleStepsSnoc, iteratedLargeCostSum]
  | succ n ih =>
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      let cutoffTail : Fin n → ℕ := fun i => cutoff i.castSucc
      let Ltail : Fin n → ℕ := fun i => L i.castSucc
      have htail :
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc cutoffTail Ws)) ≤
            snocLargeCostBudget ell cutoffTail Ltail := by
        exact ih ρtail cutoffTail Ltail
          (fun i => hρ0 i.castSucc)
          (fun i => hρ1 i.castSucc)
          (fun i => hL i.castSucc)
          (fun i => hρ i.castSucc)
      have hCurrentBound :
          ∀ Ws ∈ exposureTupleSpace X n,
            ∀ S ∈ iteratedSmallFragments H
              (exposureTupleStepsSnoc cutoffTail Ws),
              S.card ≤ snocCurrentCardBound ell cutoffTail := by
        cases n with
        | zero =>
            intro Ws _hWs S hS
            simpa [snocCurrentCardBound, exposureTupleStepsSnoc,
              iteratedSmallFragments] using hHbound S hS
        | succ m =>
            intro Ws _hWs S hS
            exact
              iteratedSmallFragments_exposureTupleStepsSnoc_card_le_last
                H cutoffTail Ws S hS
      have hsnoc :
          (∑ Ω ∈ exposureTupleSpace X (n + 1),
            exposureTupleWeight X ρ Ω *
              iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
            (∑ Ws ∈ exposureTupleSpace X n,
              exposureTupleWeight X ρtail Ws *
                iteratedLargeCostSum X q H
                  (exposureTupleStepsSnoc cutoffTail Ws)) +
              ((2 : ℝ) ^ snocCurrentCardBound ell cutoffTail *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        exact
          iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget_of_current_bound
            X H (snocCurrentCardBound ell cutoffTail) (L (Fin.last n))
            ρ cutoff hρ0 hρ1 (hL (Fin.last n)) hq0 hq1
            (hρ (Fin.last n)) hHX hCurrentBound
      have hadd := add_le_add_right htail
        ((2 : ℝ) ^ snocCurrentCardBound ell cutoffTail *
          (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n))
      exact hsnoc.trans (by
        simpa [snocLargeCostBudget, cutoffTail, Ltail, add_comm,
          add_left_comm, add_assoc] using hadd)

lemma iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_budget_sum
    (X : Finset α) (H : Finset (Finset α)) (ell : ℕ)
    {q : ℝ} {n : ℕ}
    (ρ : Fin n → ℝ) (cutoff L : Fin n → ℕ)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hL : ∀ i, 1 ≤ L i) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ∀ i, ρ i = 1 - (1 - q) ^ L i)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell) :
    (∑ Ws ∈ exposureTupleSpace X n,
      exposureTupleWeight X ρ Ws *
        iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) ≤
      ∑ i : Fin n, (2 : ℝ) ^ ell * (1 / (L i : ℝ)) ^ cutoff i := by
  classical
  induction n with
  | zero =>
      simp [exposureTupleSpace, exposureTupleWeight, exposureTupleStepsSnoc,
        iteratedLargeCostSum]
  | succ n ih =>
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      let cutoffTail : Fin n → ℕ := fun i => cutoff i.castSucc
      let Ltail : Fin n → ℕ := fun i => L i.castSucc
      have htail :
          (∑ Ws ∈ exposureTupleSpace X n,
            exposureTupleWeight X ρtail Ws *
              iteratedLargeCostSum X q H
                (exposureTupleStepsSnoc cutoffTail Ws)) ≤
            ∑ i : Fin n,
              (2 : ℝ) ^ ell * (1 / (Ltail i : ℝ)) ^ cutoffTail i := by
        exact ih ρtail cutoffTail Ltail
          (fun i => hρ0 i.castSucc)
          (fun i => hρ1 i.castSucc)
          (fun i => hL i.castSucc)
          (fun i => hρ i.castSucc)
      have hsnoc :
          (∑ Ω ∈ exposureTupleSpace X (n + 1),
            exposureTupleWeight X ρ Ω *
              iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
            (∑ Ws ∈ exposureTupleSpace X n,
              exposureTupleWeight X ρtail Ws *
                iteratedLargeCostSum X q H
                  (exposureTupleStepsSnoc cutoffTail Ws)) +
              ((2 : ℝ) ^ ell *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        exact iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget
          X H ell (L (Fin.last n)) ρ cutoff hρ0 hρ1
          (hL (Fin.last n)) hq0 hq1 (hρ (Fin.last n)) hHX hHbound
      have hcombined :
          (∑ Ω ∈ exposureTupleSpace X (n + 1),
            exposureTupleWeight X ρ Ω *
              iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ω)) ≤
            (∑ i : Fin n,
              (2 : ℝ) ^ ell * (1 / (Ltail i : ℝ)) ^ cutoffTail i) +
              ((2 : ℝ) ^ ell *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        have hadd := add_le_add_right htail
          ((2 : ℝ) ^ ell *
            (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n))
        exact hsnoc.trans (by
          simpa [add_comm, add_left_comm, add_assoc] using hadd)
      have hsum :
          (∑ i : Fin (n + 1),
              (2 : ℝ) ^ ell * (1 / (L i : ℝ)) ^ cutoff i) =
            (∑ i : Fin n,
              (2 : ℝ) ^ ell * (1 / (Ltail i : ℝ)) ^ cutoffTail i) +
              ((2 : ℝ) ^ ell *
                (1 / (L (Fin.last n) : ℝ)) ^ cutoff (Fin.last n)) := by
        rw [Fin.sum_univ_castSucc]
      exact hcombined.trans_eq hsum.symm

lemma exists_source_subset_union_of_iteratedSmallFragment_subset
    {H : Finset (Finset α)} {steps : List (ℕ × Finset α)} {V : Finset α}
    (h : ∃ T ∈ iteratedSmallFragments H steps, T ⊆ V) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  induction steps generalizing H V with
  | nil =>
      simpa [iteratedSmallFragments, smallStepExposureUnion] using h
  | cons step steps ih =>
      rcases ih (H := smallMinimalFragments step.1 H step.2) h with
        ⟨R, hRsmall, hRsub⟩
      have hRmin : R ∈ minimalFragments H step.2 :=
        (mem_smallMinimalFragments.mp hRsmall).1
      rcases exists_source_subset_union_of_minimalFragment_subset
          (H := H) (W := step.2)
          (V := smallStepExposureUnion steps ∪ V)
          ⟨R, hRmin, hRsub⟩ with
        ⟨S, hS, hSsub⟩
      exact ⟨S, hS, by
        simpa [smallStepExposureUnion, Finset.union_assoc] using hSsub⟩

lemma coverCost_le_iteratedSmallFragments_add_largeCostSum
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p) :
    coverCost X H p ≤
      coverCost X (iteratedSmallFragments H steps) p +
        iteratedLargeCostSum X p H steps := by
  induction steps generalizing H with
  | nil =>
      simp [iteratedSmallFragments, iteratedLargeCostSum]
  | cons step steps ih =>
      let H' : Finset (Finset α) :=
        smallMinimalFragments step.1 H step.2
      let L : Finset (Finset α) :=
        largeMinimalFragments step.1 H step.2
      have hstep :
          coverCost X H p ≤ coverCost X H' p + coverCost X L p := by
        simpa [H', L] using
          coverCost_le_small_add_large_minimalFragments
            X step.1 H step.2 hp0
      have hih :
          coverCost X H' p ≤
            coverCost X (iteratedSmallFragments H' steps) p +
              iteratedLargeCostSum X p H' steps :=
        ih (H := H')
      have hcombine :
          coverCost X H' p + coverCost X L p ≤
            coverCost X (iteratedSmallFragments H' steps) p +
              (coverCost X L p + iteratedLargeCostSum X p H' steps) := by
        linarith
      exact hstep.trans (by
        simpa [iteratedSmallFragments, iteratedLargeCostSum, H', L,
          add_assoc, add_comm, add_left_comm] using hcombine)

lemma coverCost_iteratedSmallFragments_pos_of_largeCostSum_lt
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) {p : ℝ} (hp0 : 0 ≤ p)
    (hloss : iteratedLargeCostSum X p H steps < coverCost X H p) :
    0 < coverCost X (iteratedSmallFragments H steps) p := by
  have hle :=
    coverCost_le_iteratedSmallFragments_add_largeCostSum
      X H steps hp0
  linarith

lemma exists_source_subset_union_of_iteratedSmallCost_pos_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hpos :
      0 < coverCost X (iteratedSmallFragments H (steps ++ [(1, V)])) p) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  have hpos' :
      0 < coverCost X
        (smallMinimalFragments 1 (iteratedSmallFragments H steps) V) p := by
    simpa [iteratedSmallFragments_append_singleton] using hpos
  rcases
      (coverCost_smallMinimalFragments_one_pos_iff_exists_subset
        X (iteratedSmallFragments H steps) V hp0).mp hpos' with
    ⟨T, hT, hTV⟩
  exact exists_source_subset_union_of_iteratedSmallFragment_subset
    (H := H) (steps := steps) (V := V) ⟨T, hT, hTV⟩

lemma exists_source_subset_union_of_largeCostSum_lt_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hloss :
      iteratedLargeCostSum X p H (steps ++ [(1, V)]) < coverCost X H p) :
    ∃ S ∈ H, S ⊆ smallStepExposureUnion steps ∪ V := by
  have hpos :
      0 < coverCost X (iteratedSmallFragments H (steps ++ [(1, V)])) p :=
    coverCost_iteratedSmallFragments_pos_of_largeCostSum_lt
      X H (steps ++ [(1, V)]) hp0 hloss
  exact exists_source_subset_union_of_iteratedSmallCost_pos_append_one
    X H steps V hp0 hpos

lemma exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one
    (X : Finset α) (H : Finset (Finset α))
    (steps : List (ℕ × Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p)
    (hUnionX : smallStepExposureUnion steps ∪ V ⊆ X)
    (hloss :
      iteratedLargeCostSum X p H (steps ++ [(1, V)]) < coverCost X H p) :
    smallStepExposureUnion steps ∪ V ∈ upClosureIn X H := by
  rcases exists_source_subset_union_of_largeCostSum_lt_append_one
      X H steps V hp0 hloss with
    ⟨S, hS, hSsub⟩
  exact mem_upClosureIn.mpr ⟨hUnionX, S, hS, hSsub⟩

/-- One-step endpoint of the deterministic iteration: if the cutoff-`1`
large-fragment loss after exposing `V` is smaller than the original cover cost,
then `V` already lies in the upper closure generated by `H`. -/
lemma exposure_mem_upClosureIn_of_largeCost_lt
    (X : Finset α) (H : Finset (Finset α)) (V : Finset α)
    {p : ℝ} (hp0 : 0 ≤ p) (hVX : V ⊆ X)
    (hloss :
      coverCost X (largeMinimalFragments 1 H V) p < coverCost X H p) :
    V ∈ upClosureIn X H := by
  have hUnionX : smallStepExposureUnion ([] : List (ℕ × Finset α)) ∪ V ⊆ X := by
    simpa [smallStepExposureUnion] using hVX
  have hloss' :
      iteratedLargeCostSum X p H (([] : List (ℕ × Finset α)) ++ [(1, V)]) <
        coverCost X H p := by
    simpa [iteratedLargeCostSum] using hloss
  simpa [smallStepExposureUnion] using
    exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one
      X H ([] : List (ℕ × Finset α)) V hp0 hUnionX hloss'

/-- Probabilistic one-step endpoint: if the large-fragment expectation estimate
is below the original cover cost at cutoff `1`, then some exposure in the
ground cube lies in the upper closure. -/
lemma exists_exposure_mem_upClosureIn_of_muP_mul_two_pow_inv_lt
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell)
    (hbound :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ))) < coverCost X H q) :
    ∃ W ∈ X.powerset, W ∈ upClosureIn X H := by
  rcases exists_exposure_largeCost_lt_of_muP_mul_two_pow_inv_lt
      X H 1 ell L hL hq0 hq1 hρ hHX hHbound (by
        simpa using hbound) with
    ⟨W, hWX, hloss⟩
  exact ⟨W, hWX,
    exposure_mem_upClosureIn_of_largeCost_lt X H W hq0.le
      (Finset.mem_powerset.mp hWX) hloss⟩

/-- One-step Markov bridge: if the expected cutoff-`1` large-fragment loss is
less than half the original cover cost, then the upper closure already has
Bernoulli measure greater than `1/2`. -/
lemma half_lt_muP_of_average_largeCost_lt_half_coverCost
    (X : Finset α) (H : Finset (Finset α)) {q ρ : ℝ}
    (hq0 : 0 < q) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcost_pos : 0 < coverCost X H q)
    (havg :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments 1 H W) q) <
        coverCost X H q * (1 / 2)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) ρ := by
  refine half_lt_muP_of_average_lt_half_of_bad_le
    X (upClosureIn X H)
    (fun W => coverCost X (largeMinimalFragments 1 H W) q)
    hρ0 hρ1 hcost_pos ?_ ?_ havg
  · intro W _hWX
    exact coverCost_nonneg hq0.le
  · intro W hWX hWnot
    exact le_of_not_gt fun hloss =>
      hWnot (exposure_mem_upClosureIn_of_largeCost_lt
        X H W hq0.le (Finset.mem_powerset.mp hWX) hloss)

/-- One-step Park--Vondrak bridge using the proved large-fragment expectation
estimate.  This is intentionally a weak one-step corollary; the full
Kahn--Kalai proof needs the multi-step version with geometrically decreasing
cutoffs. -/
lemma half_lt_muP_of_muP_mul_two_pow_inv_lt_half_coverCost
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell)
    (hcost_pos : 0 < coverCost X H q)
    (hbound :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ))) <
          coverCost X H q * (1 / 2)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) ρ := by
  have hρ0 : 0 ≤ ρ := by
    have hρpos : 0 < ρ := by
      simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
    exact hρpos.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have havg_lt :
      (∑ W ∈ X.powerset,
        bernoulliMass X W ρ *
          coverCost X (largeMinimalFragments 1 H W) q) <
        coverCost X H q * (1 / 2) :=
    (bernoulli_average_largeCost_le_muP_mul_two_pow_inv
      X H 1 ell L hL hq0 hq1 hρ hHX hHbound).trans_lt (by
        simpa using hbound)
  exact half_lt_muP_of_average_largeCost_lt_half_coverCost
    X H hq0 hρ0 hρ1 hcost_pos havg_lt

lemma half_lt_coverCost_of_not_pSmall_upClosureIn
    {X : Finset α} {H : Finset (Finset α)} {q : ℝ}
    (hq0 : 0 ≤ q) (hHX : ∀ S ∈ H, S ⊆ X)
    (hNotSmall : ¬ pSmall X (upClosureIn X H) q) :
    (1 / 2 : ℝ) < coverCost X H q := by
  have hNotSmallH : ¬ pSmall X H q :=
    (not_pSmall_upClosureIn_iff hHX).mp hNotSmall
  exact (not_pSmall_iff_half_lt_coverCost hq0 hHX).mp hNotSmallH

/-- One-step Park--Vondrak threshold corollary from non-smallness.  Since
`¬ pSmall` gives cover cost larger than `1/2`, an expected large-fragment
loss below `1/4` is enough for Markov's inequality. -/
lemma half_lt_muP_of_not_pSmall_upClosureIn_muP_mul_two_pow_inv_lt_quarter
    (X : Finset α) (H : Finset (Finset α)) (ell L : ℕ)
    {q ρ : ℝ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hHbound : ∀ S ∈ H, S.card ≤ ell)
    (hNotSmall : ¬ pSmall X (upClosureIn X H) q)
    (hbound :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ))) < (1 / 4 : ℝ)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) ρ := by
  have hcost_half :
      (1 / 2 : ℝ) < coverCost X H q :=
    half_lt_coverCost_of_not_pSmall_upClosureIn hq0.le hHX hNotSmall
  have hcost_pos : 0 < coverCost X H q := by linarith
  have hbudget :
      muP X (upClosureIn X H) ρ *
        ((2 : ℝ) ^ ell * (1 / (L : ℝ))) <
          coverCost X H q * (1 / 2) := by
    nlinarith
  exact half_lt_muP_of_muP_mul_two_pow_inv_lt_half_coverCost
    X H ell L hL hq0 hq1 hρ hHX hHbound hcost_pos hbudget

/-- Abstract multi-outcome Park--Vondrak Markov bridge.  The outcome space is
kept arbitrary so the later proof can instantiate it with independent exposure
tuples.  Each outcome must end with a cutoff-`1` exposure; if the accumulated
loss has expectation below half the initial cover cost, then the endpoint
upper-closure event has weight greater than `1/2`. -/
lemma half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt
    {Ω : Type*} [DecidableEq Ω]
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    (s : Finset Ω) (weight : Ω → ℝ)
    (stepsOf : Ω → List (ℕ × Finset α))
    (hp0 : 0 ≤ p)
    (hcost_pos : 0 < coverCost X H p)
    (hweight_nonneg : ∀ ω ∈ s, 0 ≤ weight ω)
    (hsum_weight : (∑ ω ∈ s, weight ω) = 1)
    (hshape :
      ∀ ω ∈ s,
        ∃ steps V,
          stepsOf ω = steps ++ [(1, V)] ∧
          smallStepExposureUnion steps ∪ V ⊆ X)
    (havg :
      (∑ ω ∈ s,
        weight ω * iteratedLargeCostSum X p H (stepsOf ω)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ ω ∈ s.filter
        (fun ω => smallStepExposureUnion (stepsOf ω) ∈ upClosureIn X H),
        weight ω := by
  refine half_lt_weighted_good_of_average_lt_half_of_bad_le
    s weight
    (fun ω => smallStepExposureUnion (stepsOf ω) ∈ upClosureIn X H)
    (fun ω => iteratedLargeCostSum X p H (stepsOf ω))
    hweight_nonneg hsum_weight hcost_pos ?_ ?_ havg
  · intro ω _hωs
    exact iteratedLargeCostSum_nonneg X H (stepsOf ω) hp0
  · intro ω hωs hbad
    rcases hshape ω hωs with ⟨steps, V, hsteps, hUnionX⟩
    exact le_of_not_gt fun hloss =>
      hbad (by
        have hmem :=
          exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one
            X H steps V hp0 hUnionX (by
              simpa [hsteps] using hloss)
        simpa [hsteps, smallStepExposureUnion_append_singleton] using hmem)

/-- Exposure-tuple specialization of
`half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt`. -/
lemma half_lt_exposureTuple_endpoint_of_iteratedLargeCost_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin n → ℝ)
    (stepsOf : (Fin n → Finset α) → List (ℕ × Finset α))
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hshape :
      ∀ Ws ∈ exposureTupleSpace X n,
        ∃ steps V,
          stepsOf Ws = steps ++ [(1, V)] ∧
          smallStepExposureUnion steps ∪ V ⊆ X)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X n,
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (stepsOf Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ Ws ∈ (exposureTupleSpace X n).filter
        (fun Ws => smallStepExposureUnion (stepsOf Ws) ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws := by
  exact half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt
    X H (exposureTupleSpace X n) (exposureTupleWeight X ρ) stepsOf
    hp0 hcost_pos
    (fun Ws _hWs => exposureTupleWeight_nonneg X hρ0 hρ1 Ws)
    (sum_exposureTupleWeight_eq_one X ρ)
    hshape havg

/-- Snoc-step exposure-tuple endpoint bridge.  If the final cutoff is `1` and
the accumulated large-fragment loss has expectation below half the initial
cover cost, then the tuple union lands in the upper closure with probability
greater than `1/2`. -/
lemma half_lt_exposureTupleUnion_of_iteratedLargeCostSnoc_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      ∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
        (fun Ws => exposureTupleUnion Ws ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws := by
  have hhalf :=
    half_lt_exposureTuple_endpoint_of_iteratedLargeCost_average_lt
      X H ρ (fun Ws => exposureTupleStepsSnoc cutoff Ws)
      hp0 hρ0 hρ1 hcost_pos
      (fun Ws hWs => exposureTupleStepsSnoc_last_shape hWs hlast)
      havg
  simpa [smallStepExposureUnion_exposureTupleStepsSnoc] using hhalf

/-- Snoc-step endpoint bridge converted to a `muP` conclusion once the
tuple-union distribution identity is available.  This lemma deliberately keeps
that identity as an explicit hypothesis, isolating the remaining probability
bookkeeping from the deterministic fragment iteration. -/
lemma half_lt_muP_of_iteratedLargeCostSnoc_average_lt_of_union_measure_eq
    (X : Finset α) (H : Finset (Finset α)) {p θ : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (hmeasure :
      (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
        (fun Ws => exposureTupleUnion Ws ∈ upClosureIn X H),
        exposureTupleWeight X ρ Ws) =
          muP X (upClosureIn X H) θ)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) < muP X (upClosureIn X H) θ := by
  have hhalf :=
    half_lt_exposureTupleUnion_of_iteratedLargeCostSnoc_average_lt
      X H ρ cutoff hp0 hρ0 hρ1 hcost_pos hlast havg
  rw [← hmeasure]
  simpa [upClosureIn] using hhalf

/-- Snoc-step endpoint bridge with the tuple-union distribution identity
already discharged. -/
lemma half_lt_muP_of_iteratedLargeCostSnoc_average_lt
    (X : Finset α) (H : Finset (Finset α)) {p : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hp0 : 0 ≤ p)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hcost_pos : 0 < coverCost X H p)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X p H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H p * (1 / 2)) :
    (1 / 2 : ℝ) <
      muP X (upClosureIn X H) (tupleUnionDensity ρ) := by
  exact half_lt_muP_of_iteratedLargeCostSnoc_average_lt_of_union_measure_eq
    X H ρ cutoff hp0 hρ0 hρ1 hcost_pos hlast
    (exposureTupleUnion_measure_eq_muP X (upClosureIn X H) ρ)
    havg

/-- Non-smallness-budget version of the snoc-step endpoint bridge.  Since
`¬ pSmall` gives cover cost greater than `1/2`, it is enough to bound the
expected accumulated large-fragment loss by `1/4`. -/
lemma half_lt_muP_of_not_pSmall_iteratedLargeCostSnoc_average_lt_quarter
    (X : Finset α) (H : Finset (Finset α)) {q : ℝ}
    {n : ℕ} (ρ : Fin (n + 1) → ℝ)
    (cutoff : Fin (n + 1) → ℕ)
    (hq0 : 0 < q)
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hHX : ∀ S ∈ H, S ⊆ X)
    (hNotSmall : ¬ pSmall X (upClosureIn X H) q)
    (hlast : cutoff (Fin.last n) = 1)
    (havg :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) <
          (1 / 4 : ℝ)) :
    (1 / 2 : ℝ) <
      muP X (upClosureIn X H) (tupleUnionDensity ρ) := by
  have hcost_half :
      (1 / 2 : ℝ) < coverCost X H q :=
    half_lt_coverCost_of_not_pSmall_upClosureIn hq0.le hHX hNotSmall
  have hcost_pos : 0 < coverCost X H q := by linarith
  have hbudget :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q H (exposureTupleStepsSnoc cutoff Ws)) <
          coverCost X H q * (1 / 2) := by
    nlinarith
  exact half_lt_muP_of_iteratedLargeCostSnoc_average_lt
    X H ρ cutoff hq0.le hρ0 hρ1 hcost_pos hlast hbudget

end

end ParkPham
end Erdos202
