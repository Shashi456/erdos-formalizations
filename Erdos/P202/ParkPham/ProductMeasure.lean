/-
Erdős Problem 202 — Park–Pham layer, Stage 2.

Finite Bernoulli product measure on subsets of a finite universe `X`,
expressed as a finite sum (no `MeasureTheory`). Used by the expectation-
threshold theorem and the random-partition argument downstream.
-/

import Mathlib
import Erdos.P202.ParkPham.BooleanFamilies

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- Bernoulli mass of a subset `S ⊆ X` at density `p`. -/
noncomputable def bernoulliMass (X S : Finset α) (p : ℝ) : ℝ :=
  p ^ S.card * (1 - p) ^ (X.card - S.card)

/-- Bernoulli probability of a family `U` of subsets of `X` at density `p`. -/
noncomputable def muP (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ S ∈ X.powerset.filter (· ∈ U), bernoulliMass X S p

omit [DecidableEq α] in
lemma bernoulliMass_nonneg {X S : Finset α} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ bernoulliMass X S p := by
  unfold bernoulliMass
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- `muP` is nonnegative for `p ∈ [0, 1]`. -/
lemma muP_nonneg {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ muP X U p := by
  refine Finset.sum_nonneg fun S _ => bernoulliMass_nonneg h0 h1

/-- `muP` is monotone in the family. -/
lemma muP_mono_family {X : Finset α} {U V : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hUV : U ⊆ V) : muP X U p ≤ muP X V p := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSU⟩
    exact Finset.mem_filter.mpr ⟨hSX, hUV hSU⟩
  · intros
    exact bernoulliMass_nonneg h0 h1

/-- Replacing an already-increasing family by its upper closure does not change
its product measure. -/
lemma muP_upClosureIn_eq_self_of_increasing
    {X : Finset α} {U : Finset (Finset α)} (p : ℝ)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U) :
    muP X (upClosureIn X U) p = muP X U p := by
  rw [upClosureIn_eq_self_of_increasing hUX hIncr]

omit [DecidableEq α] in
/-- Bernoulli weights sum to 1 over the powerset of any finite set `X`,
for any `p ∈ ℝ`. This is the finite binomial identity. -/
lemma sum_bernoulliMass_eq_one (X : Finset α) {p : ℝ}
    (h : p + (1 - p) = 1) :
    (∑ S ∈ X.powerset, bernoulliMass X S p) = 1 := by
  classical
  -- Group by cardinality and use the binomial theorem.
  have hsum :
      (∑ S ∈ X.powerset, p ^ S.card * (1 - p) ^ (X.card - S.card)) =
        ∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k)) := by
    classical
    rw [Finset.sum_powerset_apply_card
      (f := fun k => p ^ k * (1 - p) ^ (X.card - k))]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [nsmul_eq_mul]
  unfold bernoulliMass
  rw [hsum]
  have hbinom : (p + (1 - p)) ^ X.card =
      ∑ k ∈ Finset.range (X.card + 1),
        p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ) :=
    add_pow p (1 - p) X.card
  have : (p + (1 - p)) ^ X.card = 1 := by rw [h]; exact one_pow _
  rw [this] at hbinom
  -- Reshape RHS to match.
  have hreshape :
      (∑ k ∈ Finset.range (X.card + 1),
          (X.card.choose k : ℝ) * (p ^ k * (1 - p) ^ (X.card - k))) =
        (∑ k ∈ Finset.range (X.card + 1),
          p ^ k * (1 - p) ^ (X.card - k) * (X.card.choose k : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [hreshape, ← hbinom]

/-- Upper bound: `muP X U p ≤ 1` for `p ∈ [0,1]` (in fact equals 1 minus the
mass on the complement). -/
lemma muP_le_one {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) : muP X U p ≤ 1 := by
  have hsum := sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)
  have hsub : muP X U p ≤ ∑ S ∈ X.powerset, bernoulliMass X S p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro S hS; exact (Finset.mem_filter.mp hS).1
    · intros; exact bernoulliMass_nonneg h0 h1
  linarith

omit [DecidableEq α] in
/-- Finite Bernoulli averaging choice principle.  If the Bernoulli-weighted
average of a function on subsets of `X` is strictly below `B`, then at least
one subset has value strictly below `B`. -/
lemma exists_powerset_value_lt_of_bernoulli_average_lt
    (X : Finset α) {p B : ℝ} (F : Finset α → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (havg :
      (∑ W ∈ X.powerset, bernoulliMass X W p * F W) < B) :
    ∃ W ∈ X.powerset, F W < B := by
  by_contra hnone
  have hB_le : ∀ W ∈ X.powerset, B ≤ F W := by
    intro W hW
    exact le_of_not_gt fun hlt => hnone ⟨W, hW, hlt⟩
  have hsum_le :
      (∑ W ∈ X.powerset, bernoulliMass X W p * B) ≤
        ∑ W ∈ X.powerset, bernoulliMass X W p * F W := by
    refine Finset.sum_le_sum ?_
    intro W hW
    exact mul_le_mul_of_nonneg_left (hB_le W hW)
      (bernoulliMass_nonneg hp0 hp1)
  have hsum_const :
      (∑ W ∈ X.powerset, bernoulliMass X W p * B) = B := by
    calc
      (∑ W ∈ X.powerset, bernoulliMass X W p * B)
          = (∑ W ∈ X.powerset, bernoulliMass X W p) * B := by
              rw [Finset.sum_mul]
      _ = 1 * B := by
          rw [sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)]
      _ = B := by ring
  linarith

omit [DecidableEq α] in
/-- Finite Markov/complement principle over an arbitrary finite probability
space.  This is the bookkeeping form needed for a multi-exposure process:
if all bad outcomes have loss at least `B > 0` and the expected loss is below
`B/2`, then the good event has weight greater than `1/2`. -/
lemma half_lt_weighted_good_of_average_lt_half_of_bad_le
    {Ω : Type*} [DecidableEq Ω] (s : Finset Ω)
    (weight : Ω → ℝ) (Good : Ω → Prop) [DecidablePred Good]
    (F : Ω → ℝ) {B : ℝ}
    (hweight_nonneg : ∀ ω ∈ s, 0 ≤ weight ω)
    (hsum_weight : (∑ ω ∈ s, weight ω) = 1)
    (hB : 0 < B)
    (hF_nonneg : ∀ ω ∈ s, 0 ≤ F ω)
    (hbad : ∀ ω ∈ s, ¬ Good ω → B ≤ F ω)
    (havg : (∑ ω ∈ s, weight ω * F ω) < B * (1 / 2)) :
    (1 / 2 : ℝ) < ∑ ω ∈ s.filter Good, weight ω := by
  let bad : Finset Ω := s.filter fun ω => ¬ Good ω
  have hbad_weight_le :
      (∑ ω ∈ bad, weight ω * B) ≤
        ∑ ω ∈ bad, weight ω * F ω := by
    refine Finset.sum_le_sum ?_
    intro ω hωbad
    have hωs : ω ∈ s := (Finset.mem_filter.mp hωbad).1
    have hωGood : ¬ Good ω := (Finset.mem_filter.mp hωbad).2
    exact mul_le_mul_of_nonneg_left (hbad ω hωs hωGood)
      (hweight_nonneg ω hωs)
  have hbad_avg_le :
      (∑ ω ∈ bad, weight ω * F ω) ≤
        ∑ ω ∈ s, weight ω * F ω := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro ω hωs _hωnot
    exact mul_nonneg (hweight_nonneg ω hωs) (hF_nonneg ω hωs)
  have hbad_mass_mul_lt :
      (∑ ω ∈ bad, weight ω) * B < B * (1 / 2) := by
    calc
      (∑ ω ∈ bad, weight ω) * B
          = ∑ ω ∈ bad, weight ω * B := by
              rw [Finset.sum_mul]
      _ ≤ ∑ ω ∈ bad, weight ω * F ω := hbad_weight_le
      _ ≤ ∑ ω ∈ s, weight ω * F ω := hbad_avg_le
      _ < B * (1 / 2) := havg
  have hbad_mass_lt_half :
      (∑ ω ∈ bad, weight ω) < (1 / 2 : ℝ) := by
    have hbad_mass_mul_lt' :
        (∑ ω ∈ bad, weight ω) * B < (1 / 2 : ℝ) * B := by
      linarith
    exact lt_of_mul_lt_mul_right hbad_mass_mul_lt' hB.le
  have hsplit :
      (∑ ω ∈ s.filter Good, weight ω) + (∑ ω ∈ bad, weight ω) = 1 := by
    have hsplit_raw :=
      Finset.sum_filter_add_sum_filter_not
        (s := s) (p := Good) (f := weight)
    unfold bad
    simpa using hsplit_raw.trans hsum_weight
  linarith

/-- Finite outcome space for `n` independent exposure sets, each chosen from
the powerset of `X`. -/
noncomputable def exposureTupleSpace (X : Finset α) (n : ℕ) :
    Finset (Fin n → Finset α) :=
  Fintype.piFinset fun _ : Fin n => X.powerset

omit [DecidableEq α] in
lemma mem_exposureTupleSpace
    {X : Finset α} {n : ℕ} {Ws : Fin n → Finset α} :
    Ws ∈ exposureTupleSpace X n ↔ ∀ i, Ws i ∈ X.powerset := by
  simp [exposureTupleSpace, Fintype.mem_piFinset]

/-- Product Bernoulli weight of an exposure tuple. -/
noncomputable def exposureTupleWeight
    (X : Finset α) {n : ℕ} (ρ : Fin n → ℝ)
    (Ws : Fin n → Finset α) : ℝ :=
  ∏ i, bernoulliMass X (Ws i) (ρ i)

omit [DecidableEq α] in
lemma exposureTupleWeight_nonneg
    (X : Finset α) {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (Ws : Fin n → Finset α) :
    0 ≤ exposureTupleWeight X ρ Ws := by
  unfold exposureTupleWeight
  exact Finset.prod_nonneg fun i _hi =>
    bernoulliMass_nonneg (hρ0 i) (hρ1 i)

omit [DecidableEq α] in
lemma sum_exposureTupleWeight_eq_one
    (X : Finset α) {n : ℕ} (ρ : Fin n → ℝ) :
    (∑ Ws ∈ exposureTupleSpace X n, exposureTupleWeight X ρ Ws) = 1 := by
  unfold exposureTupleSpace exposureTupleWeight
  rw [Finset.sum_prod_piFinset
    (s := X.powerset)
    (g := fun i W => bernoulliMass X W (ρ i))]
  simp [sum_bernoulliMass_eq_one]

/-- Union of all exposure sets in a finite exposure tuple. -/
def exposureTupleUnion {n : ℕ} (Ws : Fin n → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin n)).biUnion fun i => Ws i

/-- Density of the union of independent exposure sets with coordinate
densities `ρ`. -/
noncomputable def tupleUnionDensity {n : ℕ} (ρ : Fin n → ℝ) : ℝ :=
  1 - ∏ i, (1 - ρ i)

omit [DecidableEq α] in
@[simp] lemma tupleUnionDensity_zero (ρ : Fin 0 → ℝ) :
    tupleUnionDensity ρ = 0 := by
  simp [tupleUnionDensity]

omit [DecidableEq α] in
@[simp] lemma tupleUnionDensity_one (ρ : Fin 1 → ℝ) :
    tupleUnionDensity ρ = ρ 0 := by
  simp [tupleUnionDensity]

omit [DecidableEq α] in
@[simp] lemma one_sub_tupleUnionDensity {n : ℕ} (ρ : Fin n → ℝ) :
    1 - tupleUnionDensity ρ = ∏ i, (1 - ρ i) := by
  unfold tupleUnionDensity
  ring

omit [DecidableEq α] in
lemma tupleUnionDensity_snoc {n : ℕ} (ρ : Fin (n + 1) → ℝ) :
    tupleUnionDensity ρ =
      1 - (1 - tupleUnionDensity (fun i : Fin n => ρ i.castSucc)) *
        (1 - ρ (Fin.last n)) := by
  unfold tupleUnionDensity
  rw [Fin.prod_univ_castSucc]
  ring

omit [DecidableEq α] in
@[simp] lemma tupleUnionDensity_const (n : ℕ) (q : ℝ) :
    tupleUnionDensity (fun _ : Fin n => q) = 1 - (1 - q) ^ n := by
  simp [tupleUnionDensity, Finset.prod_const]

omit [DecidableEq α] in
lemma tupleUnionDensity_nonneg {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1) :
    0 ≤ tupleUnionDensity ρ := by
  have hprod_le_one : (∏ i, (1 - ρ i)) ≤ (1 : ℝ) := by
    refine Finset.prod_le_one ?_ ?_
    · intro i _hi
      exact sub_nonneg.mpr (hρ1 i)
    · intro i _hi
      linarith [hρ0 i]
  unfold tupleUnionDensity
  linarith

omit [DecidableEq α] in
lemma tupleUnionDensity_le_one {n : ℕ} {ρ : Fin n → ℝ}
    (hρ1 : ∀ i, ρ i ≤ 1) :
    tupleUnionDensity ρ ≤ 1 := by
  have hprod_nonneg : 0 ≤ (∏ i, (1 - ρ i)) := by
    refine Finset.prod_nonneg ?_
    intro i _hi
    exact sub_nonneg.mpr (hρ1 i)
  unfold tupleUnionDensity
  linarith

omit [DecidableEq α] in
lemma tupleUnionDensity_le_sum {n : ℕ} {ρ : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1) :
    tupleUnionDensity ρ ≤ ∑ i, ρ i := by
  induction n with
  | zero =>
      simp [tupleUnionDensity]
  | succ n ih =>
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      have htail0 : ∀ i : Fin n, 0 ≤ ρtail i := fun i => hρ0 i.castSucc
      have htail1 : ∀ i : Fin n, ρtail i ≤ 1 := fun i => hρ1 i.castSucc
      have htail_le : tupleUnionDensity ρtail ≤ ∑ i, ρtail i :=
        ih htail0 htail1
      have htail_nonneg : 0 ≤ tupleUnionDensity ρtail :=
        tupleUnionDensity_nonneg htail0 htail1
      have hlast_nonneg : 0 ≤ ρ (Fin.last n) := hρ0 (Fin.last n)
      have hsplit :
          tupleUnionDensity ρ ≤ tupleUnionDensity ρtail + ρ (Fin.last n) := by
        rw [tupleUnionDensity_snoc]
        have hmul_nonneg :
            0 ≤ tupleUnionDensity ρtail * ρ (Fin.last n) :=
          mul_nonneg htail_nonneg hlast_nonneg
        nlinarith
      have hsum :
          (∑ i : Fin (n + 1), ρ i) =
            (∑ i : Fin n, ρtail i) + ρ (Fin.last n) := by
        rw [Fin.sum_univ_castSucc]
      exact hsplit.trans (by
        rw [hsum]
        have h := add_le_add_right htail_le (ρ (Fin.last n))
        simpa [add_comm, add_left_comm, add_assoc] using h)

omit [DecidableEq α] in
lemma tupleUnionDensity_le_sum_of_le {n : ℕ} {ρ B : Fin n → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hρB : ∀ i, ρ i ≤ B i) :
    tupleUnionDensity ρ ≤ ∑ i, B i := by
  exact (tupleUnionDensity_le_sum hρ0 hρ1).trans
    (Finset.sum_le_sum fun i _hi => hρB i)

lemma exposureTupleUnion_subset
    {X : Finset α} {n : ℕ} {Ws : Fin n → Finset α}
    (hWs : Ws ∈ exposureTupleSpace X n) :
    exposureTupleUnion Ws ⊆ X := by
  intro x hx
  rcases (by simpa [exposureTupleUnion] using hx : ∃ i, x ∈ Ws i) with
    ⟨i, hxi⟩
  exact Finset.mem_powerset.mp ((mem_exposureTupleSpace.mp hWs) i) hxi

@[simp] lemma exposureTupleUnion_zero (Ws : Fin 0 → Finset α) :
    exposureTupleUnion Ws = ∅ := by
  ext x
  simp [exposureTupleUnion]

@[simp] lemma exposureTupleUnion_one (Ws : Fin 1 → Finset α) :
    exposureTupleUnion Ws = Ws 0 := by
  ext x
  simp [exposureTupleUnion]

@[simp] lemma exposureTupleUnion_snoc {n : ℕ}
    (Ws : Fin n → Finset α) (W : Finset α) :
    exposureTupleUnion
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleUnion Ws ∪ W := by
  ext x
  constructor
  · intro hx
    rcases (by
      simpa [exposureTupleUnion] using hx :
        ∃ i : Fin (n + 1),
          x ∈ (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) i) with
      ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Finset.mem_union.mpr (Or.inl (by
        simpa [exposureTupleUnion] using (Exists.intro j (by simpa using hi))))
    · exact Finset.mem_union.mpr (Or.inr (by simpa using hi))
  · intro hx
    rcases Finset.mem_union.mp hx with htail | hlast
    · rcases (by
        simpa [exposureTupleUnion] using htail :
          ∃ i : Fin n, x ∈ Ws i) with ⟨i, hi⟩
      simpa [exposureTupleUnion] using
        (Exists.intro (i.castSucc : Fin (n + 1)) (by simpa using hi))
    · simpa [exposureTupleUnion] using
        (Exists.intro (Fin.last n) (by simpa using hlast))

omit [DecidableEq α] in
lemma exposureTupleSpace_snoc (X : Finset α) (n : ℕ) :
    exposureTupleSpace X (n + 1) =
      (X.powerset ×ˢ exposureTupleSpace X n).map
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding := by
  ext Ws
  constructor
  · intro hWs
    refine Finset.mem_map.mpr ⟨⟨Ws (Fin.last n),
      fun i : Fin n => Ws i.castSucc⟩, ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨(mem_exposureTupleSpace.mp hWs) (Fin.last n),
          mem_exposureTupleSpace.mpr fun i =>
            (mem_exposureTupleSpace.mp hWs) i.castSucc⟩
    · exact (Fin.snocEquiv
        (fun _ : Fin (n + 1) => Finset α)).right_inv Ws
  · intro hWs
    rcases Finset.mem_map.mp hWs with ⟨⟨W, Ws₀⟩, hpair, hEq⟩
    rw [← hEq]
    rcases Finset.mem_product.mp hpair with ⟨hW, hWs₀⟩
    refine mem_exposureTupleSpace.mpr ?_
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa using (mem_exposureTupleSpace.mp hWs₀) j
    · simpa using hW

omit [DecidableEq α] in
@[simp] lemma exposureTupleWeight_snoc {n : ℕ}
    (X : Finset α) (ρ : Fin (n + 1) → ℝ)
    (Ws : Fin n → Finset α) (W : Finset α) :
    exposureTupleWeight X ρ
        (Fin.snoc (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
      exposureTupleWeight X (fun i : Fin n => ρ i.castSucc) Ws *
        bernoulliMass X W (ρ (Fin.last n)) := by
  unfold exposureTupleWeight
  rw [Fin.prod_univ_castSucc]
  simp

/-- For one exposure, the exposure-tuple model is exactly `muP`. -/
lemma exposureTupleUnion_measure_one
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 1 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 1).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (ρ 0) := by
  unfold exposureTupleSpace exposureTupleWeight muP
  have hmap :
      ((Fintype.piFinset fun _ : Fin 1 => X.powerset).filter
        (fun Ws : Fin 1 → Finset α => exposureTupleUnion Ws ∈ U)).image
          (fun Ws => Ws 0) =
        X.powerset.filter (fun W => W ∈ U) := by
    ext W
    constructor
    · intro hW
      rcases Finset.mem_image.mp hW with ⟨Ws, hWs, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨(Fintype.mem_piFinset.mp (Finset.mem_filter.mp hWs).1) 0,
          by simpa using (Finset.mem_filter.mp hWs).2⟩
    · intro hW
      refine Finset.mem_image.mpr ⟨(fun _ : Fin 1 => W), ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Fintype.mem_piFinset.mpr (by intro i; simpa using (Finset.mem_filter.mp hW).1),
          by simpa [exposureTupleUnion_one] using (Finset.mem_filter.mp hW).2⟩
  have hinj :
      Set.InjOn (fun Ws : Fin 1 → Finset α => Ws 0)
        (((Fintype.piFinset fun _ : Fin 1 => X.powerset).filter
          (fun Ws : Fin 1 → Finset α => exposureTupleUnion Ws ∈ U)) : Set (Fin 1 → Finset α)) := by
    intro Ws _hWs Vs _hVs h0
    funext i
    have hi : i = 0 := by fin_cases i; rfl
    simpa [hi] using h0
  rw [← hmap, Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro Ws hWs
    simp
  · exact hinj

/-- One-exposure case expressed using `tupleUnionDensity`. -/
lemma exposureTupleUnion_measure_one_density
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 1 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 1).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (tupleUnionDensity ρ) := by
  simpa using exposureTupleUnion_measure_one X U ρ

/-- Finite Markov/complement principle for Bernoulli sums.  If every outcome
outside `U` has loss at least `B > 0`, and the expected loss is below `B/2`,
then `U` has Bernoulli measure strictly bigger than `1/2`. -/
lemma half_lt_muP_of_average_lt_half_of_bad_le
    (X : Finset α) (U : Finset (Finset α)) {p B : ℝ}
    (F : Finset α → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hB : 0 < B)
    (hF_nonneg : ∀ W ∈ X.powerset, 0 ≤ F W)
    (hbad : ∀ W ∈ X.powerset, W ∉ U → B ≤ F W)
    (havg :
      (∑ W ∈ X.powerset, bernoulliMass X W p * F W) < B * (1 / 2)) :
    (1 / 2 : ℝ) < muP X U p := by
  let bad : Finset (Finset α) := X.powerset.filter fun W => W ∉ U
  have hbad_weight_le :
      (∑ W ∈ bad, bernoulliMass X W p * B) ≤
        ∑ W ∈ bad, bernoulliMass X W p * F W := by
    refine Finset.sum_le_sum ?_
    intro W hWbad
    have hWX : W ∈ X.powerset := (Finset.mem_filter.mp hWbad).1
    have hWU : W ∉ U := (Finset.mem_filter.mp hWbad).2
    exact mul_le_mul_of_nonneg_left (hbad W hWX hWU)
      (bernoulliMass_nonneg hp0 hp1)
  have hbad_avg_le :
      (∑ W ∈ bad, bernoulliMass X W p * F W) ≤
        ∑ W ∈ X.powerset, bernoulliMass X W p * F W := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro W hWX _hWnot
    exact mul_nonneg (bernoulliMass_nonneg hp0 hp1) (hF_nonneg W hWX)
  have hbad_mass_mul_lt :
      (∑ W ∈ bad, bernoulliMass X W p) * B < B * (1 / 2) := by
    calc
      (∑ W ∈ bad, bernoulliMass X W p) * B
          = ∑ W ∈ bad, bernoulliMass X W p * B := by
              rw [Finset.sum_mul]
      _ ≤ ∑ W ∈ bad, bernoulliMass X W p * F W := hbad_weight_le
      _ ≤ ∑ W ∈ X.powerset, bernoulliMass X W p * F W := hbad_avg_le
      _ < B * (1 / 2) := havg
  have hbad_mass_lt_half :
      (∑ W ∈ bad, bernoulliMass X W p) < (1 / 2 : ℝ) := by
    have hbad_mass_mul_lt' :
        (∑ W ∈ bad, bernoulliMass X W p) * B < (1 / 2 : ℝ) * B := by
      linarith
    exact lt_of_mul_lt_mul_right hbad_mass_mul_lt' hB.le
  have htotal :
      (∑ W ∈ X.powerset, bernoulliMass X W p) = 1 :=
    sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)
  have hsplit :
      muP X U p + (∑ W ∈ bad, bernoulliMass X W p) = 1 := by
    have hsplit_raw :=
      Finset.sum_filter_add_sum_filter_not
        (s := X.powerset) (p := fun W : Finset α => W ∈ U)
        (f := fun W => bernoulliMass X W p)
    unfold muP bad
    simpa using hsplit_raw.trans htotal
  linarith

omit [DecidableEq α] in
/-- Uniform geometric estimate used in the Park--Pham/Park--Vondrak cost
lemma.  If `p = 1 - (1 - q)^L`, then the numerator
`L * q * (1 - q)^L` is bounded by the denominator `p`. -/
lemma nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow
    {q : ℝ} {L : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (L : ℝ) * q * (1 - q) ^ L ≤ 1 - (1 - q) ^ L := by
  let r : ℝ := 1 - q
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hq_eq : q = 1 - r := by dsimp [r]; ring
  have hsum_ge :
      (L : ℝ) * r ^ L ≤ ∑ i ∈ Finset.range L, r ^ i := by
    calc
      (L : ℝ) * r ^ L = ∑ _i ∈ Finset.range L, r ^ L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range L, r ^ i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact pow_le_pow_of_le_one hr0 hr1
          (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hmul :=
    mul_le_mul_of_nonneg_right hsum_ge (by dsimp [r]; linarith : 0 ≤ 1 - r)
  calc
    (L : ℝ) * q * (1 - q) ^ L
        = ((L : ℝ) * r ^ L) * (1 - r) := by
          dsimp [r]
          ring
    _ ≤ (∑ i ∈ Finset.range L, r ^ i) * (1 - r) := hmul
    _ = 1 - r ^ L := geom_sum_mul_neg r L
    _ = 1 - (1 - q) ^ L := by rfl

omit [DecidableEq α] in
lemma one_sub_one_sub_q_pow_pos
    {q : ℝ} {L : ℕ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    0 < 1 - (1 - q) ^ L := by
  have hr0 : 0 ≤ 1 - q := by linarith
  have hr1 : 1 - q ≤ 1 := by linarith
  have hpow_le : (1 - q) ^ L ≤ (1 - q) ^ 1 :=
    pow_le_pow_of_le_one hr0 hr1 hL
  have hq_le : q ≤ 1 - (1 - q) ^ L := by
    simpa using sub_le_sub_left hpow_le 1
  exact lt_of_lt_of_le hq0 hq_le

omit [DecidableEq α] in
/-- Bernoulli union bound in scalar form:
`1 - (1 - q)^L <= L q` for `q ∈ [0,1]`. -/
lemma one_sub_one_sub_q_pow_le_nat_mul
    {q : ℝ} {L : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 - (1 - q) ^ L ≤ (L : ℝ) * q := by
  let r : ℝ := 1 - q
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hsum_le :
      (∑ i ∈ Finset.range L, r ^ i) ≤
        ∑ _i ∈ Finset.range L, (1 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact pow_le_one₀ hr0 hr1
  have hmul :=
    mul_le_mul_of_nonneg_right hsum_le (by dsimp [r]; linarith : 0 ≤ 1 - r)
  calc
    1 - (1 - q) ^ L = (∑ i ∈ Finset.range L, r ^ i) * (1 - r) := by
        dsimp [r]
        rw [geom_sum_mul_neg]
    _ ≤ (∑ _i ∈ Finset.range L, (1 : ℝ)) * (1 - r) := hmul
    _ = (L : ℝ) * q := by
        dsimp [r]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

omit [DecidableEq α] in
lemma tupleUnionDensity_one_sub_pow_le_q_sum
    {q : ℝ} {n : ℕ} (L : Fin n → ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    tupleUnionDensity (fun i : Fin n => 1 - (1 - q) ^ L i) ≤
      q * ∑ i : Fin n, (L i : ℝ) := by
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase1 : 1 - q ≤ 1 := by linarith
  have hρ0 :
      ∀ i : Fin n, 0 ≤ 1 - (1 - q) ^ L i := by
    intro i
    have hpow_le_one : (1 - q) ^ L i ≤ (1 : ℝ) :=
      pow_le_one₀ hbase0 hbase1
    linarith
  have hρ1 :
      ∀ i : Fin n, 1 - (1 - q) ^ L i ≤ 1 := by
    intro i
    have hpow_nonneg : 0 ≤ (1 - q) ^ L i :=
      pow_nonneg hbase0 _
    linarith
  have hbound :
      ∀ i : Fin n, 1 - (1 - q) ^ L i ≤ (L i : ℝ) * q := by
    intro i
    exact one_sub_one_sub_q_pow_le_nat_mul hq0 hq1
  calc
    tupleUnionDensity (fun i : Fin n => 1 - (1 - q) ^ L i)
        ≤ ∑ i : Fin n, (L i : ℝ) * q :=
          tupleUnionDensity_le_sum_of_le hρ0 hρ1 hbound
    _ = q * ∑ i : Fin n, (L i : ℝ) := by
          rw [← Finset.sum_mul]
          ring

omit [DecidableEq α] in
/-- Divided form of `nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow`. -/
lemma q_mul_one_sub_q_pow_div_one_sub_pow_le_inv_nat
    {q : ℝ} {L : ℕ} (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    q * (1 - q) ^ L / (1 - (1 - q) ^ L) ≤ 1 / (L : ℝ) := by
  have hmain :=
    nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow
      (q := q) (L := L) hq0.le hq1
  have hden : 0 < 1 - (1 - q) ^ L :=
    one_sub_one_sub_q_pow_pos hL hq0 hq1
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  have hnum :
      q * (1 - q) ^ L ≤ (1 - (1 - q) ^ L) / (L : ℝ) := by
    rw [le_div_iff₀ hLpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  calc
    q * (1 - q) ^ L / (1 - (1 - q) ^ L)
        ≤ ((1 - (1 - q) ^ L) / (L : ℝ)) /
            (1 - (1 - q) ^ L) :=
          div_le_div_of_nonneg_right hnum hden.le
    _ = 1 / (L : ℝ) := by
          field_simp [hden.ne', hLpos.ne']

/-- Termwise uniform Park--Vondrak reindexing bound.  If
`ρ = 1 - (1 - q)^L`, then for a disjoint pair `W,S`, the Bernoulli weight of
`W` times `q^|S|` is bounded by the Bernoulli weight of `W ∪ S` times
`(1/L)^|S|`. -/
lemma bernoulliMass_mul_pow_le_union_mul_inv_nat_pow
    {X W S : Finset α} {q ρ : ℝ} {L : ℕ}
    (hL : 1 ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hρ : ρ = 1 - (1 - q) ^ L)
    (hdisj : Disjoint S W) (hUnionX : W ∪ S ⊆ X) :
    bernoulliMass X W ρ * q ^ S.card ≤
      bernoulliMass X (W ∪ S) ρ * (1 / (L : ℝ)) ^ S.card := by
  have hρ_pos : 0 < ρ := by
    simpa [hρ] using one_sub_one_sub_q_pow_pos hL hq0 hq1
  have hρ_nonneg : 0 ≤ ρ := hρ_pos.le
  have hρ_le_one : ρ ≤ 1 := by
    rw [hρ]
    have hpow_nonneg : 0 ≤ (1 - q) ^ L := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - q) L
    linarith
  have hone_minus_ρ_nonneg : 0 ≤ 1 - ρ := by linarith
  have hLpos : 0 < (L : ℝ) := by
    have hL_nat_pos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
    exact_mod_cast hL_nat_pos
  have hsingle : q * (1 - ρ) ≤ ρ * (1 / (L : ℝ)) := by
    have hmain :
        (L : ℝ) * q * (1 - ρ) ≤ ρ := by
      have hraw :=
        nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow
          (q := q) (L := L) hq0.le hq1
      simpa [hρ, mul_assoc, mul_comm, mul_left_comm] using hraw
    rw [← div_eq_mul_one_div]
    rw [le_div_iff₀ hLpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  have hpow_single :
      (q * (1 - ρ)) ^ S.card ≤ (ρ * (1 / (L : ℝ))) ^ S.card :=
    pow_le_pow_left₀ (mul_nonneg hq0.le hone_minus_ρ_nonneg) hsingle S.card
  have hcard_union : (W ∪ S).card = W.card + S.card := by
    rw [Finset.card_union_of_disjoint]
    exact hdisj.symm
  have hWsub : W ⊆ W ∪ S := Finset.subset_union_left
  have hWcard_le : W.card ≤ X.card :=
    Finset.card_le_card (hWsub.trans hUnionX)
  have hUcard_le : (W ∪ S).card ≤ X.card :=
    Finset.card_le_card hUnionX
  have hdiff : X.card - W.card = (X.card - (W ∪ S).card) + S.card := by
    rw [hcard_union]
    omega
  have hcommon_nonneg :
      0 ≤ ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card) := by
    positivity
  calc
    bernoulliMass X W ρ * q ^ S.card
        = (ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card)) *
            (q * (1 - ρ)) ^ S.card := by
          unfold bernoulliMass
          rw [hdiff, pow_add, mul_pow]
          ring
    _ ≤ (ρ ^ W.card * (1 - ρ) ^ (X.card - (W ∪ S).card)) *
          (ρ * (1 / (L : ℝ))) ^ S.card :=
        mul_le_mul_of_nonneg_left hpow_single hcommon_nonneg
    _ = bernoulliMass X (W ∪ S) ρ * (1 / (L : ℝ)) ^ S.card := by
          unfold bernoulliMass
          rw [hcard_union, pow_add, mul_pow]
          ring

omit [DecidableEq α] in
/-- At density `1`, the top set `X` has Bernoulli mass `1`. -/
lemma bernoulliMass_self_one (X : Finset α) :
    bernoulliMass X X (1 : ℝ) = 1 := by
  simp [bernoulliMass]

omit [DecidableEq α] in
/-- At density `1`, any proper subset of `X` has Bernoulli mass `0`. -/
lemma bernoulliMass_one_of_ne_top {X S : Finset α}
    (hSX : S ⊆ X) (hS_ne : S ≠ X) :
    bernoulliMass X S (1 : ℝ) = 0 := by
  have hlt : S.card < X.card := Finset.card_lt_card (hSX.ssubset_of_ne hS_ne)
  have hpos : 0 < X.card - S.card := Nat.sub_pos_of_lt hlt
  simp [bernoulliMass, hpos.ne']

/-- If the family contains the top set `X`, then its product measure at
density `1` is `1`. -/
lemma muP_one_of_mem_top {X : Finset α} {U : Finset (Finset α)}
    (hXU : X ∈ U) :
    muP X U (1 : ℝ) = 1 := by
  classical
  unfold muP
  refine Finset.sum_eq_single_of_mem X ?_ ?_ |>.trans (bernoulliMass_self_one X)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl X), hXU⟩
  · intro S hS hS_ne
    have hSX : S ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    exact bernoulliMass_one_of_ne_top hSX hS_ne

/-- A nonempty increasing family on `X` has product measure `1` at density
`1`. -/
lemma muP_one_of_nonempty_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hU : U.Nonempty) :
    muP X U (1 : ℝ) = 1 :=
  muP_one_of_mem_top (top_mem_of_nonempty_increasing hUX hIncr hU)

omit [DecidableEq α] in
/-- At density `0`, the empty set has Bernoulli mass `1`. -/
lemma bernoulliMass_empty_zero (X : Finset α) :
    bernoulliMass X ∅ (0 : ℝ) = 1 := by
  simp [bernoulliMass]

omit [DecidableEq α] in
/-- At density `0`, every nonempty set has Bernoulli mass `0`. -/
lemma bernoulliMass_zero_of_nonempty {X S : Finset α}
    (hS : S.Nonempty) :
    bernoulliMass X S (0 : ℝ) = 0 := by
  simp [bernoulliMass, hS.card_pos.ne']

/-- If the family contains `∅`, then its product measure at density `0` is
`1`. -/
lemma muP_zero_of_mem_empty {X : Finset α} {U : Finset (Finset α)}
    (hEmpty : (∅ : Finset α) ∈ U) :
    muP X U (0 : ℝ) = 1 := by
  classical
  unfold muP
  refine (Finset.sum_eq_single_of_mem ∅ ?_ ?_).trans (bernoulliMass_empty_zero X)
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.empty_subset X), hEmpty⟩
  · intro S hS hS_ne
    have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_ne
    exact bernoulliMass_zero_of_nonempty hS_nonempty

/-- If the family does not contain `∅`, then its product measure at density
`0` is `0`. -/
lemma muP_zero_of_not_mem_empty {X : Finset α} {U : Finset (Finset α)}
    (hEmpty : (∅ : Finset α) ∉ U) :
    muP X U (0 : ℝ) = 0 := by
  classical
  unfold muP
  refine Finset.sum_eq_zero ?_
  intro S hS
  have hSU : S ∈ U := (Finset.mem_filter.mp hS).2
  have hS_ne : S ≠ ∅ := by
    intro hS_empty
    exact hEmpty (by simpa [hS_empty] using hSU)
  exact bernoulliMass_zero_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hS_ne)

/-- Base case for the tuple-union distribution identity. -/
lemma exposureTupleUnion_measure_zero
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 0 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 0).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (0 : ℝ) := by
  by_cases hEmpty : (∅ : Finset α) ∈ U
  · have hfilter :
        (exposureTupleSpace X 0).filter
          (fun Ws : Fin 0 → Finset α => exposureTupleUnion Ws ∈ U) =
            exposureTupleSpace X 0 := by
      apply Finset.filter_eq_self.mpr
      intro Ws _hWs
      simpa using hEmpty
    rw [hfilter, sum_exposureTupleWeight_eq_one X ρ,
      muP_zero_of_mem_empty hEmpty]
  · have hfilter :
        (exposureTupleSpace X 0).filter
          (fun Ws : Fin 0 → Finset α => exposureTupleUnion Ws ∈ U) =
            ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro Ws _hWs
      simpa using hEmpty
    rw [hfilter]
    simp [muP_zero_of_not_mem_empty hEmpty]

/-- Zero-exposure case expressed using `tupleUnionDensity`. -/
lemma exposureTupleUnion_measure_zero_density
    (X : Finset α) (U : Finset (Finset α)) (ρ : Fin 0 → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X 0).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (tupleUnionDensity ρ) := by
  simpa using exposureTupleUnion_measure_zero X U ρ

/-- If `U` is the whole powerset of `X`, then its product measure is `1`. -/
lemma muP_eq_one_of_eq_powerset {X : Finset α} {U : Finset (Finset α)}
    (hU : U = X.powerset) (p : ℝ) :
    muP X U p = 1 := by
  classical
  unfold muP
  have hfilter : X.powerset.filter (fun S => S ∈ U) = X.powerset := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    simpa [hU] using hS
  rw [hfilter]
  exact sum_bernoulliMass_eq_one (α := α) X (p := p) (by ring)

/-- An increasing family on `X` containing `∅` has product measure `1` at every
density. -/
lemma muP_eq_one_of_empty_mem_increasing {X : Finset α} {U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) (p : ℝ) :
    muP X U p = 1 :=
  muP_eq_one_of_eq_powerset
    (eq_powerset_of_empty_mem_increasing hUX hIncr hEmpty) p

/-! ## Marginal at a fixed subset

If `U = upClosureIn X {T₀}` (the upper closure of a single set), then
`muP X U p = p^|T₀|`. This is the "probability that random subset at
density `p` contains `T₀`" identity used by the random-partition argument.
-/

/-- The upper closure of a singleton family `{T₀}` inside `X` is
`{T ⊆ X : T₀ ⊆ T}`. -/
lemma upClosureIn_singleton (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) :
    upClosureIn X {T₀} =
      X.powerset.filter (fun T => T₀ ⊆ T) := by
  classical
  ext T
  constructor
  · intro hT
    rcases mem_upClosureIn.mp hT with ⟨hTX, S, hS, hST⟩
    rcases Finset.mem_singleton.mp hS with rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hST⟩
  · intro hT
    rcases Finset.mem_filter.mp hT with ⟨hTX, hT₀T⟩
    exact mem_upClosureIn.mpr ⟨Finset.mem_powerset.mp hTX, T₀,
      Finset.mem_singleton.mpr rfl, hT₀T⟩

/-- **Marginal identity.** For `T₀ ⊆ X` and `p ∈ [0,1]`,
`muP X (upClosureIn X {T₀}) p = p^|T₀|`. -/
theorem muP_upClosure_single (X T₀ : Finset α) (hT₀ : T₀ ⊆ X) {p : ℝ}
    (_h0 : 0 ≤ p) (_h1 : p ≤ 1) :
    muP X (upClosureIn X {T₀}) p = p ^ T₀.card := by
  classical
  -- Reparametrize: subsets `S ⊆ X` with `T₀ ⊆ S` correspond bijectively
  -- to subsets `S' ⊆ X \ T₀` via `S = T₀ ∪ S'`. The Bernoulli mass factors
  -- as `p^|T₀| · p^|S'| · (1-p)^(|X\T₀|-|S'|)`, and the inner sum is 1.
  set Y : Finset α := X \ T₀ with hY
  have hY_card : Y.card = X.card - T₀.card := by
    simp [hY, Finset.card_sdiff_of_subset hT₀]
  have hT₀_disj_Y : Disjoint T₀ Y := by
    simp [hY, Finset.disjoint_sdiff]
  -- Set up the bijection.
  let f : Finset α → Finset α := fun S' => T₀ ∪ S'
  have hf_inj : Set.InjOn f (↑Y.powerset) := by
    intro S' hS' R' hR' hfeq
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hR'Y : R' ⊆ Y := Finset.mem_powerset.mp hR'
    have hdisj_S' : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hdisj_R' : Disjoint T₀ R' := Finset.disjoint_of_subset_right hR'Y hT₀_disj_Y
    have heq : T₀ ∪ S' = T₀ ∪ R' := hfeq
    -- Use sdiff: S' = (T₀ ∪ S') \ T₀ when T₀ is disjoint from S'.
    have hS'_eq : S' = (T₀ ∪ S') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_S' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxS'
        · exact (hxnT₀ hxT₀).elim
        · exact hxS'
    have hR'_eq : R' = (T₀ ∪ R') \ T₀ := by
      ext x
      constructor
      · intro hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hx), ?_⟩
        exact fun hxT₀ => (Finset.disjoint_left.mp hdisj_R' hxT₀ hx).elim
      · intro hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxun, hxnT₀⟩
        rcases Finset.mem_union.mp hxun with hxT₀ | hxR'
        · exact (hxnT₀ hxT₀).elim
        · exact hxR'
    rw [hS'_eq, hR'_eq, heq]
  -- The image of Y.powerset under f is exactly the filter we sum over.
  have him :
      Y.powerset.image f =
        X.powerset.filter (fun T => T ∈ upClosureIn X {T₀}) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_filter,
      mem_upClosureIn, Finset.mem_singleton]
    constructor
    · rintro ⟨S', hS'Y, rfl⟩
      have hS'X : S' ⊆ X := hS'Y.trans Finset.sdiff_subset
      have hfX : T₀ ∪ S' ⊆ X := Finset.union_subset hT₀ hS'X
      refine ⟨hfX, hfX, T₀, rfl, ?_⟩
      exact Finset.subset_union_left
    · rintro ⟨hTX, _, S₀, hS₀eq, hS₀T⟩
      refine ⟨T \ T₀, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxT, hxnT₀⟩
        exact Finset.mem_sdiff.mpr ⟨hTX hxT, hxnT₀⟩
      · -- f (T \ T₀) = T₀ ∪ (T \ T₀) = T, since T₀ ⊆ T (via S₀ = T₀ ⊆ T).
        have hT₀T : T₀ ⊆ T := by
          have := hS₀T
          rw [hS₀eq] at this
          exact this
        show T₀ ∪ (T \ T₀) = T
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hxT₀ | hxd
          · exact hT₀T hxT₀
          · exact (Finset.mem_sdiff.mp hxd).1
        · intro hxT
          by_cases hxT₀ : x ∈ T₀
          · exact Finset.mem_union.mpr (Or.inl hxT₀)
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxT₀⟩))
  -- Now: muP = Σ_{T in filter} bernoulli T = Σ_{S' ⊆ Y} bernoulli (T₀ ∪ S').
  unfold muP
  rw [← him, Finset.sum_image hf_inj]
  -- bernoulliMass X (T₀ ∪ S') p = p^|T₀ ∪ S'| (1-p)^(|X| - |T₀ ∪ S'|)
  --                              = p^(|T₀| + |S'|) (1-p)^(|Y| - |S'|)
  --                              = p^|T₀| · [p^|S'| (1-p)^(|Y| - |S'|)]
  have hkey :
      ∀ S' ∈ Y.powerset,
        bernoulliMass X (f S') p = p ^ T₀.card * bernoulliMass Y S' p := by
    intro S' hS'
    have hS'Y : S' ⊆ Y := Finset.mem_powerset.mp hS'
    have hdisj : Disjoint T₀ S' := Finset.disjoint_of_subset_right hS'Y hT₀_disj_Y
    have hcard : (T₀ ∪ S').card = T₀.card + S'.card :=
      Finset.card_union_of_disjoint hdisj
    have hsum_eq : X.card - (T₀.card + S'.card) = Y.card - S'.card := by
      rw [hY_card]; omega
    show p ^ (f S').card * (1 - p) ^ (X.card - (f S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    show p ^ (T₀ ∪ S').card * (1 - p) ^ (X.card - (T₀ ∪ S').card)
        = p ^ T₀.card * (p ^ S'.card * (1 - p) ^ (Y.card - S'.card))
    rw [hcard, hsum_eq, pow_add, mul_assoc]
  -- Apply hkey, factor out p^|T₀|, and use sum_bernoulliMass_eq_one on Y.
  rw [Finset.sum_congr rfl hkey, ← Finset.mul_sum]
  have : (∑ S' ∈ Y.powerset, bernoulliMass Y S' p) = 1 :=
    sum_bernoulliMass_eq_one (α := α) Y (p := p) (by ring)
  rw [this, mul_one]

/-! ## Conditioning on one coordinate -/

/-- If `S ⊆ X` and `a ∉ X`, then the Bernoulli mass of `S` inside
`insert a X` is `(1-p)` times its mass inside `X`. -/
lemma bernoulliMass_insert_of_notMem {X S : Finset α} {a : α} {p : ℝ}
    (ha : a ∉ X) (hS : S ⊆ X) :
    bernoulliMass (insert a X) S p = (1 - p) * bernoulliMass X S p := by
  have hcardX : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem ha
  have hS_le : S.card ≤ X.card := Finset.card_le_card hS
  have hdiff : (insert a X).card - S.card = (X.card - S.card) + 1 := by
    rw [hcardX]
    omega
  unfold bernoulliMass
  rw [hdiff, pow_succ]
  ring

/-- If `S ⊆ X` and `a ∉ X`, then the Bernoulli mass of `insert a S` inside
`insert a X` is `p` times the mass of `S` inside `X`. -/
lemma bernoulliMass_insert_with_mem {X S : Finset α} {a : α} {p : ℝ}
    (ha : a ∉ X) (hS : S ⊆ X) :
    bernoulliMass (insert a X) (insert a S) p = p * bernoulliMass X S p := by
  have haS : a ∉ S := fun h => ha (hS h)
  have hcardX : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem ha
  have hcardS : (insert a S).card = S.card + 1 := Finset.card_insert_of_notMem haS
  have hS_le : S.card ≤ X.card := Finset.card_le_card hS
  have hdiff : (insert a X).card - (S.card + 1) = X.card - S.card := by
    rw [hcardX]
    omega
  unfold bernoulliMass
  rw [hcardS, hdiff, pow_succ]
  ring

/-- On subsets of `X`, adjoining a new element `a ∉ X` is injective. -/
lemma insert_injective_on_powerset_of_notMem {X : Finset α} {a : α}
    (ha : a ∉ X) :
    Set.InjOn (fun S : Finset α => insert a S) X.powerset := by
  intro S hS T hT hST
  have haS : a ∉ S := fun h => ha ((Finset.mem_powerset.mp hS) h)
  have haT : a ∉ T := fun h => ha ((Finset.mem_powerset.mp hT) h)
  calc
    S = (insert a S).erase a := (Finset.erase_insert haS).symm
    _ = (insert a T).erase a := congrArg (fun U : Finset α => U.erase a) hST
    _ = T := Finset.erase_insert haT

/-- The old subsets of `X` are disjoint from the subsets obtained by adjoining
a new element `a`. -/
lemma powerset_disjoint_image_insert_of_notMem {X : Finset α} {a : α}
    (ha : a ∉ X) :
    Disjoint X.powerset (X.powerset.image fun S : Finset α => insert a S) := by
  rw [Finset.disjoint_left]
  intro S hS hSimage
  rcases Finset.mem_image.mp hSimage with ⟨T, _hT, rfl⟩
  have ha_insert : a ∈ insert a T := Finset.mem_insert_self a T
  have ha_not_insert : a ∉ insert a T := fun h =>
    ha ((Finset.mem_powerset.mp hS) h)
  exact ha_not_insert ha_insert

/-- Slice of a family consisting of members not using the new coordinate. -/
noncomputable def withoutCoordFamily (X : Finset α) (U : Finset (Finset α)) :
    Finset (Finset α) :=
  X.powerset.filter fun S => S ∈ U

/-- Slice of a family consisting of members that use the new coordinate,
with that coordinate removed. -/
noncomputable def withCoordFamily (a : α) (X : Finset α)
    (U : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun S => insert a S ∈ U

/-- Slice of a family seen after unioning with a fixed exposure `W`. -/
noncomputable def unionShiftFamily (X : Finset α)
    (U : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
  X.powerset.filter fun S => S ∪ W ∈ U

lemma mem_unionShiftFamily {X : Finset α} {U : Finset (Finset α)}
    {W S : Finset α} :
    S ∈ unionShiftFamily X U W ↔ S ⊆ X ∧ S ∪ W ∈ U := by
  simp [unionShiftFamily]

lemma unionShiftFamily_subset_ground
    (X : Finset α) (U : Finset (Finset α)) (W : Finset α) :
    ∀ S ∈ unionShiftFamily X U W, S ⊆ X := by
  intro S hS
  exact (mem_unionShiftFamily.mp hS).1

lemma withoutCoordFamily_unionShiftFamily_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withoutCoordFamily X (unionShiftFamily (insert a X) U W) =
      unionShiftFamily X (withoutCoordFamily X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hS_insert, hSU⟩
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            hSU⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU0⟩
    rcases Finset.mem_filter.mp hSU0 with ⟨_hunionX, hSU⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨hSX.trans (Finset.subset_insert a X), hSU⟩⟩

lemma withCoordFamily_unionShiftFamily_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withCoordFamily a X (unionShiftFamily (insert a X) U W) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hinsertX, hSU⟩
    have hrewrite : insert a (S ∪ W) = insert a S ∪ W := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : insert a S ∪ W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨Finset.insert_subset (Finset.mem_insert_self a X)
            (hSX.trans (Finset.subset_insert a X)),
            by rwa [hrewrite]⟩⟩

lemma withoutCoordFamily_unionShiftFamily_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withoutCoordFamily X (unionShiftFamily (insert a X) U (insert a W)) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hS_insert, hSU⟩
    have hrewrite : S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [← hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨hSX.trans (Finset.subset_insert a X),
            by rwa [hrewrite]⟩⟩

lemma withCoordFamily_unionShiftFamily_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α}
    (hW : W ⊆ X) :
    withCoordFamily a X (unionShiftFamily (insert a X) U (insert a W)) =
      unionShiftFamily X (withCoordFamily a X U) W := by
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hSX, hSshift⟩
    rcases mem_unionShiftFamily.mp hSshift with ⟨_hinsertX, hSU⟩
    have hrewrite : insert a S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact mem_unionShiftFamily.mpr
      ⟨Finset.mem_powerset.mp hSX,
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.union_subset (Finset.mem_powerset.mp hSX) hW),
            by rwa [← hrewrite]⟩⟩
  · intro hS
    rcases mem_unionShiftFamily.mp hS with ⟨hSX, hSU1⟩
    rcases Finset.mem_filter.mp hSU1 with ⟨_hunionX, hSU⟩
    have hrewrite : insert a S ∪ insert a W = insert a (S ∪ W) := by
      ext x
      simp [or_comm]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSX,
        mem_unionShiftFamily.mpr
          ⟨Finset.insert_subset (Finset.mem_insert_self a X)
              (hSX.trans (Finset.subset_insert a X)),
            by rwa [hrewrite]⟩⟩

/-- Product measure conditioned on whether a new coordinate is absent or
present. -/
lemma muP_insert_split {X : Finset α} {U : Finset (Finset α)} {a : α} {p : ℝ}
    (ha : a ∉ X) :
    muP (insert a X) U p =
      (1 - p) * muP X (withoutCoordFamily X U) p +
        p * muP X (withCoordFamily a X U) p := by
  classical
  let ins : Finset α → Finset α := fun S => insert a S
  let A : Finset (Finset α) := X.powerset.filter fun S => S ∈ U
  let B : Finset (Finset α) := (X.powerset.image ins).filter fun S => S ∈ U
  have hdisj_raw :
      Disjoint X.powerset (X.powerset.image ins) := by
    simpa [ins] using powerset_disjoint_image_insert_of_notMem (X := X) (a := a) ha
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro S hSA hSB
    exact (Finset.disjoint_left.mp hdisj_raw)
      (Finset.mem_filter.mp hSA).1 (Finset.mem_filter.mp hSB).1
  have hfilter_union :
      (insert a X).powerset.filter (fun S => S ∈ U) = A ∪ B := by
    calc
      (insert a X).powerset.filter (fun S => S ∈ U)
          = (X.powerset ∪ X.powerset.image ins).filter (fun S => S ∈ U) := by
            rw [Finset.powerset_insert]
      _ = A ∪ B := by
            rw [Finset.filter_union]
  have hU0_filter :
      X.powerset.filter (fun S => S ∈ withoutCoordFamily X U) = A := by
    ext S
    simp [withoutCoordFamily, A]
  have hterm0 :
      (∑ S ∈ A, bernoulliMass (insert a X) S p) =
        (1 - p) * muP X (withoutCoordFamily X U) p := by
    calc
      (∑ S ∈ A, bernoulliMass (insert a X) S p)
          = ∑ S ∈ A, (1 - p) * bernoulliMass X S p := by
            refine Finset.sum_congr rfl ?_
            intro S hSA
            have hSX : S ⊆ X :=
              Finset.mem_powerset.mp (Finset.mem_filter.mp hSA).1
            exact bernoulliMass_insert_of_notMem ha hSX
      _ = (1 - p) * ∑ S ∈ A, bernoulliMass X S p := by
            rw [Finset.mul_sum]
      _ = (1 - p) * muP X (withoutCoordFamily X U) p := by
            unfold muP
            rw [hU0_filter]
  have hB_image :
      (X.powerset.filter fun S => ins S ∈ U).image ins = B := by
    ext R
    constructor
    · intro hR
      rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨S, (Finset.mem_filter.mp hS).1, rfl⟩,
          (Finset.mem_filter.mp hS).2⟩
    · intro hR
      rcases Finset.mem_filter.mp hR with ⟨hRimg, hRU⟩
      rcases Finset.mem_image.mp hRimg with ⟨S, hS, rfl⟩
      exact Finset.mem_image.mpr
        ⟨S, Finset.mem_filter.mpr ⟨hS, hRU⟩, rfl⟩
  have hinj :
      Set.InjOn ins (↑(X.powerset.filter fun S => ins S ∈ U)) := by
    exact (insert_injective_on_powerset_of_notMem (X := X) (a := a) ha).mono
      (by intro S hS; exact (Finset.mem_filter.mp hS).1)
  have hU1_filter :
      X.powerset.filter (fun S => S ∈ withCoordFamily a X U) =
        X.powerset.filter fun S => ins S ∈ U := by
    ext S
    simp [withCoordFamily, ins]
  have hterm1 :
      (∑ S ∈ B, bernoulliMass (insert a X) S p) =
        p * muP X (withCoordFamily a X U) p := by
    calc
      (∑ S ∈ B, bernoulliMass (insert a X) S p)
          = ∑ S ∈ (X.powerset.filter fun S => ins S ∈ U).image ins,
              bernoulliMass (insert a X) S p := by rw [hB_image]
      _ = ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              bernoulliMass (insert a X) (ins S) p := by
            rw [Finset.sum_image hinj]
      _ = ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              p * bernoulliMass X S p := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hSX : S ⊆ X := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
            simpa [ins] using bernoulliMass_insert_with_mem (X := X) (S := S)
              (a := a) (p := p) ha hSX
      _ = p * ∑ S ∈ X.powerset.filter (fun S => ins S ∈ U),
              bernoulliMass X S p := by
            rw [Finset.mul_sum]
      _ = p * muP X (withCoordFamily a X U) p := by
            unfold muP
            rw [hU1_filter]
  calc
    muP (insert a X) U p
        = ∑ S ∈ A ∪ B, bernoulliMass (insert a X) S p := by
          unfold muP
          rw [hfilter_union]
    _ = (∑ S ∈ A, bernoulliMass (insert a X) S p) +
        ∑ S ∈ B, bernoulliMass (insert a X) S p := by
          rw [Finset.sum_union hdisj]
    _ = (1 - p) * muP X (withoutCoordFamily X U) p +
        p * muP X (withCoordFamily a X U) p := by
          rw [hterm0, hterm1]

/-- Splitting a fixed-union slice when the fixed exposure does not contain the
new coordinate. -/
lemma muP_insert_unionShift_absent
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α} {p : ℝ}
    (ha : a ∉ X) (hW : W ⊆ X) :
    muP (insert a X) (unionShiftFamily (insert a X) U W) p =
      (1 - p) *
          muP X (unionShiftFamily X (withoutCoordFamily X U) W) p +
        p * muP X (unionShiftFamily X (withCoordFamily a X U) W) p := by
  rw [muP_insert_split (X := X)
    (U := unionShiftFamily (insert a X) U W) (a := a) (p := p) ha]
  rw [withoutCoordFamily_unionShiftFamily_absent (a := a) hW,
    withCoordFamily_unionShiftFamily_absent (a := a) hW]

/-- Splitting a fixed-union slice when the fixed exposure already contains the
new coordinate. -/
lemma muP_insert_unionShift_present
    {X : Finset α} {U : Finset (Finset α)} {a : α} {W : Finset α} {p : ℝ}
    (ha : a ∉ X) (hW : W ⊆ X) :
    muP (insert a X) (unionShiftFamily (insert a X) U (insert a W)) p =
      muP X (unionShiftFamily X (withCoordFamily a X U) W) p := by
  rw [muP_insert_split (X := X)
    (U := unionShiftFamily (insert a X) U (insert a W)) (a := a) (p := p) ha]
  rw [withoutCoordFamily_unionShiftFamily_present (a := a) hW,
    withCoordFamily_unionShiftFamily_present (a := a) hW]
  ring

/-- The union of two independent Bernoulli subsets has Bernoulli density
`1 - (1 - θ) * (1 - r)`.  This is stated as a finite convolution over the
second exposure `W`, with `unionShiftFamily` encoding the first exposure's
target event. -/
lemma muP_unionShift_average_eq_muP_union_density
    (X : Finset α) (U : Finset (Finset α)) (θ r : ℝ) :
    (∑ W ∈ X.powerset,
      bernoulliMass X W r * muP X (unionShiftFamily X U W) θ) =
      muP X U (1 - (1 - θ) * (1 - r)) := by
  classical
  induction X using Finset.induction generalizing U with
  | empty =>
      by_cases hEmpty : (∅ : Finset α) ∈ U
      · have hleft_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S = ∅ ∧ S ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro S hS
          have hSempty : S = ∅ := by simpa using hS
          exact ⟨hSempty, by simpa [hSempty] using hEmpty⟩
        have hright_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro S hS
          have hSempty : S = ∅ := by simpa using hS
          simpa [hSempty] using hEmpty
        simp [muP, bernoulliMass, unionShiftFamily, hleft_filter, hright_filter]
      · have hleft_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S = ∅ ∧ S ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro S hS hbad
          exact hEmpty (by simpa [hbad.1] using hbad.2)
        have hright_filter :
            ({∅} : Finset (Finset α)).filter
              (fun S => S ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro S hS hSU
          have hSempty : S = ∅ := by simpa using hS
          exact hEmpty (by simpa [hSempty] using hSU)
        simp [muP, bernoulliMass, unionShiftFamily, hleft_filter, hright_filter]
  | insert a X ha ih =>
      let η : ℝ := 1 - (1 - θ) * (1 - r)
      let ins : Finset α → Finset α := fun S => insert a S
      have hdisj :
          Disjoint X.powerset (X.powerset.image ins) := by
        simpa [ins] using powerset_disjoint_image_insert_of_notMem
          (X := X) (a := a) ha
      have hinj : Set.InjOn ins (↑X.powerset) := by
        simpa [ins] using insert_injective_on_powerset_of_notMem
          (X := X) (a := a) ha
      have hpowerset_split :
          (∑ W ∈ (insert a X).powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ) =
            (∑ W ∈ X.powerset,
              bernoulliMass (insert a X) W r *
                muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
              ∑ W ∈ X.powerset,
                bernoulliMass (insert a X) (insert a W) r *
                  muP (insert a X)
                    (unionShiftFamily (insert a X) U (insert a W)) θ := by
        calc
          (∑ W ∈ (insert a X).powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ)
              = ∑ W ∈ X.powerset ∪ X.powerset.image ins,
                  bernoulliMass (insert a X) W r *
                    muP (insert a X) (unionShiftFamily (insert a X) U W) θ := by
                    rw [Finset.powerset_insert]
          _ = (∑ W ∈ X.powerset,
                bernoulliMass (insert a X) W r *
                  muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
                ∑ W ∈ X.powerset.image ins,
                  bernoulliMass (insert a X) W r *
                    muP (insert a X) (unionShiftFamily (insert a X) U W) θ := by
                    rw [Finset.sum_union hdisj]
          _ = (∑ W ∈ X.powerset,
                bernoulliMass (insert a X) W r *
                  muP (insert a X) (unionShiftFamily (insert a X) U W) θ) +
                ∑ W ∈ X.powerset,
                  bernoulliMass (insert a X) (insert a W) r *
                    muP (insert a X)
                      (unionShiftFamily (insert a X) U (insert a W)) θ := by
                    rw [Finset.sum_image hinj]
      have habsent :
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ) =
            ((1 - r) * (1 - θ)) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
              ((1 - r) * θ) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
        calc
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) W r *
              muP (insert a X) (unionShiftFamily (insert a X) U W) θ)
              = ∑ W ∈ X.powerset,
                  (((1 - r) * (1 - θ)) *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
                  ((1 - r) * θ) *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withCoordFamily a X U) W) θ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro W hW
                    have hWX : W ⊆ X := Finset.mem_powerset.mp hW
                    rw [bernoulliMass_insert_of_notMem ha hWX,
                      muP_insert_unionShift_absent (X := X) (U := U)
                        (a := a) (W := W) (p := θ) ha hWX]
                    ring
          _ = ((1 - r) * (1 - θ)) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withoutCoordFamily X U) W) θ) +
              ((1 - r) * θ) *
                (∑ W ∈ X.powerset,
                  bernoulliMass X W r *
                    muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      have hpresent :
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) (insert a W) r *
              muP (insert a X)
                (unionShiftFamily (insert a X) U (insert a W)) θ) =
            r *
              (∑ W ∈ X.powerset,
                bernoulliMass X W r *
                  muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
        calc
          (∑ W ∈ X.powerset,
            bernoulliMass (insert a X) (insert a W) r *
              muP (insert a X)
                (unionShiftFamily (insert a X) U (insert a W)) θ)
              = ∑ W ∈ X.powerset,
                  r *
                    (bernoulliMass X W r *
                      muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    refine Finset.sum_congr rfl ?_
                    intro W hW
                    have hWX : W ⊆ X := Finset.mem_powerset.mp hW
                    rw [bernoulliMass_insert_with_mem ha hWX,
                      muP_insert_unionShift_present (X := X) (U := U)
                        (a := a) (W := W) (p := θ) ha hWX]
                    ring
          _ = r *
              (∑ W ∈ X.powerset,
                bernoulliMass X W r *
                  muP X (unionShiftFamily X (withCoordFamily a X U) W) θ) := by
                    rw [Finset.mul_sum]
      have hwithout :=
        ih (withoutCoordFamily X U)
      have hwith :=
        ih (withCoordFamily a X U)
      rw [hpowerset_split, habsent, hpresent, hwithout, hwith]
      have hsplit :=
        muP_insert_split (X := X) (U := U) (a := a) (p := η) ha
      change
        ((1 - r) * (1 - θ)) * muP X (withoutCoordFamily X U) η +
            ((1 - r) * θ) * muP X (withCoordFamily a X U) η +
          r * muP X (withCoordFamily a X U) η =
        muP (insert a X) U η
      rw [hsplit]
      ring

/-- Distribution identity for the union of an independent tuple of Bernoulli
exposures.  The union has the same law as one Bernoulli subset with density
`tupleUnionDensity ρ = 1 - ∏ i, (1 - ρ i)`. -/
lemma exposureTupleUnion_measure_eq_muP
    (X : Finset α) (U : Finset (Finset α)) {n : ℕ}
    (ρ : Fin n → ℝ) :
    (∑ Ws ∈ (exposureTupleSpace X n).filter
      (fun Ws => exposureTupleUnion Ws ∈ U),
      exposureTupleWeight X ρ Ws) =
      muP X U (tupleUnionDensity ρ) := by
  classical
  induction n generalizing U with
  | zero =>
      simpa using exposureTupleUnion_measure_zero_density X U ρ
  | succ n ih =>
      let e : Finset α × (Fin n → Finset α) ↪
          (Fin (n + 1) → Finset α) :=
        (Fin.snocEquiv (fun _ : Fin (n + 1) => Finset α)).toEmbedding
      let ρtail : Fin n → ℝ := fun i => ρ i.castSucc
      let ρlast : ℝ := ρ (Fin.last n)
      have hmap :
          (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
            (fun Ws => exposureTupleUnion Ws ∈ U),
            exposureTupleWeight X ρ Ws) =
          ∑ P ∈ ((X.powerset ×ˢ exposureTupleSpace X n).filter
              (fun P => exposureTupleUnion (e P) ∈ U)),
            exposureTupleWeight X ρ (e P) := by
        rw [exposureTupleSpace_snoc X n, Finset.filter_map]
        rw [Finset.sum_map]
        rfl
      have hproduct :
          (∑ P ∈ ((X.powerset ×ˢ exposureTupleSpace X n).filter
              (fun P => exposureTupleUnion (e P) ∈ U)),
            exposureTupleWeight X ρ (e P)) =
          ∑ W ∈ X.powerset,
            ∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws)) := by
        rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl ?_
        intro W hW
        rw [← Finset.sum_filter]
        have hfilter :
            (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion (e (W, Ws)) ∈ U) =
              (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W) := by
          ext Ws
          by_cases hWs : Ws ∈ exposureTupleSpace X n
          · have hWsX : exposureTupleUnion Ws ⊆ X :=
              exposureTupleUnion_subset hWs
            have hevent :
                exposureTupleUnion (e (W, Ws)) ∈ U ↔
                  exposureTupleUnion Ws ∈ unionShiftFamily X U W := by
              change
                exposureTupleUnion
                    (Fin.snoc
                      (α := fun _ : Fin (n + 1) => Finset α) Ws W) ∈ U ↔
                  exposureTupleUnion Ws ∈ unionShiftFamily X U W
              rw [exposureTupleUnion_snoc]
              simp [mem_unionShiftFamily, hWsX]
            simp [hWs, hevent]
          · simp [hWs]
        rw [hfilter]
      have hfactor :
          (∑ W ∈ X.powerset,
            ∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws))) =
          ∑ W ∈ X.powerset,
            bernoulliMass X W ρlast *
              (∑ Ws ∈ (exposureTupleSpace X n).filter
                (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                exposureTupleWeight X ρtail Ws) := by
        refine Finset.sum_congr rfl ?_
        intro W hW
        calc
          (∑ Ws ∈ (exposureTupleSpace X n).filter
              (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
              exposureTupleWeight X ρ (e (W, Ws)))
              = ∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws * bernoulliMass X W ρlast := by
                    refine Finset.sum_congr rfl ?_
                    intro Ws hWs
                    change
                      exposureTupleWeight X ρ
                          (Fin.snoc
                            (α := fun _ : Fin (n + 1) => Finset α) Ws W) =
                        exposureTupleWeight X ρtail Ws *
                          bernoulliMass X W ρlast
                    simp [ρtail, ρlast]
          _ = (∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws) * bernoulliMass X W ρlast := by
                    rw [Finset.sum_mul]
          _ = bernoulliMass X W ρlast *
                (∑ Ws ∈ (exposureTupleSpace X n).filter
                  (fun Ws => exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                  exposureTupleWeight X ρtail Ws) := by
                    ring
      calc
        (∑ Ws ∈ (exposureTupleSpace X (n + 1)).filter
          (fun Ws => exposureTupleUnion Ws ∈ U),
          exposureTupleWeight X ρ Ws)
            = ∑ W ∈ X.powerset,
                bernoulliMass X W ρlast *
                  (∑ Ws ∈ (exposureTupleSpace X n).filter
                    (fun Ws =>
                      exposureTupleUnion Ws ∈ unionShiftFamily X U W),
                    exposureTupleWeight X ρtail Ws) := by
                  rw [hmap, hproduct, hfactor]
        _ = ∑ W ∈ X.powerset,
              bernoulliMass X W ρlast *
                muP X (unionShiftFamily X U W) (tupleUnionDensity ρtail) := by
                  refine Finset.sum_congr rfl ?_
                  intro W hW
                  rw [ih (unionShiftFamily X U W) ρtail]
        _ = muP X U
              (1 - (1 - tupleUnionDensity ρtail) * (1 - ρlast)) :=
            muP_unionShift_average_eq_muP_union_density
              X U (tupleUnionDensity ρtail) ρlast
        _ = muP X U (tupleUnionDensity ρ) := by
            rw [tupleUnionDensity_snoc]

/-- Bernoulli product measure is monotone in the density for increasing
families. -/
theorem muP_mono_density {X : Finset α} {U : Finset (Finset α)} {p q : ℝ}
    (hIncr : IncreasingIn X U) (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    muP X U p ≤ muP X U q := by
  classical
  induction X using Finset.induction generalizing U with
  | empty =>
      by_cases hU : (∅ : Finset α) ∈ U
      · have hfilter :
            ({∅} : Finset (Finset α)).filter (fun x => x ∈ U) = {∅} := by
          apply Finset.filter_eq_self.mpr
          intro x hx
          have hxempty : x = ∅ := by simpa using hx
          simpa [hxempty] using hU
        simp [muP, bernoulliMass, hfilter]
      · have hfilter :
            ({∅} : Finset (Finset α)).filter (fun x => x ∈ U) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx
          have hxempty : x = ∅ := by simpa using hx
          simpa [hxempty] using hU
        simp [muP, bernoulliMass, hfilter]
  | insert a X ha ih =>
      let U0 : Finset (Finset α) := withoutCoordFamily X U
      let U1 : Finset (Finset α) := withCoordFamily a X U
      have hp1 : p ≤ 1 := hpq.trans hq1
      have hq0 : 0 ≤ q := hp0.trans hpq
      have hIncr0 : IncreasingIn X U0 := by
        intro S hSU0 T hTX hST
        rcases Finset.mem_filter.mp hSU0 with ⟨_hSX, hSU⟩
        have hT_insert : T ⊆ insert a X := hTX.trans (Finset.subset_insert a X)
        have hTU : T ∈ U := hIncr S hSU T hT_insert hST
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hTU⟩
      have hIncr1 : IncreasingIn X U1 := by
        intro S hSU1 T hTX hST
        rcases Finset.mem_filter.mp hSU1 with ⟨_hSX, hInsSU⟩
        have hInsT_insert : insert a T ⊆ insert a X := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxT
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hTX hxT))
        have hInsSInsT : insert a S ⊆ insert a T := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hST hxS))
        have hInsTU : insert a T ∈ U :=
          hIncr (insert a S) hInsSU (insert a T) hInsT_insert hInsSInsT
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTX, hInsTU⟩
      have hU0U1 : U0 ⊆ U1 := by
        intro S hSU0
        rcases Finset.mem_filter.mp hSU0 with ⟨hSXpow, hSU⟩
        have hSX : S ⊆ X := Finset.mem_powerset.mp hSXpow
        have hInsSX : insert a S ⊆ insert a X := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · simp
          · exact Finset.mem_insert.mpr (Or.inr (hSX hxS))
        have hSInsS : S ⊆ insert a S := Finset.subset_insert a S
        have hInsSU : insert a S ∈ U := hIncr S hSU (insert a S) hInsSX hSInsS
        exact Finset.mem_filter.mpr ⟨hSXpow, hInsSU⟩
      have hF0 : muP X U0 p ≤ muP X U0 q := ih hIncr0
      have hF1 : muP X U1 p ≤ muP X U1 q := ih hIncr1
      have hF01q : muP X U0 q ≤ muP X U1 q :=
        muP_mono_family hq0 hq1 hU0U1
      rw [muP_insert_split (X := X) (U := U) (a := a) (p := p) ha,
        muP_insert_split (X := X) (U := U) (a := a) (p := q) ha]
      have hfirst :
          (1 - p) * muP X U0 p + p * muP X U1 p ≤
            (1 - p) * muP X U0 q + p * muP X U1 q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hF0 (by linarith))
          (mul_le_mul_of_nonneg_left hF1 hp0)
      have hsecond :
          (1 - p) * muP X U0 q + p * muP X U1 q ≤
            (1 - q) * muP X U0 q + q * muP X U1 q := by
        have hqp_nonneg : 0 ≤ q - p := by linarith
        have hmul := mul_le_mul_of_nonneg_left hF01q hqp_nonneg
        nlinarith
      exact hfirst.trans hsecond

/-- A single member of an increasing family gives a product-measure lower bound:
the event contains all random subsets that include that member. -/
lemma pow_card_le_muP_of_mem_increasing
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hS : S ∈ U) :
    p ^ S.card ≤ muP X U p := by
  have hSX : S ⊆ X := hUX S hS
  have hsub : upClosureIn X {S} ⊆ U :=
    upClosureIn_singleton_subset_of_mem_increasing hIncr hS
  have hmono :
      muP X (upClosureIn X {S}) p ≤ muP X U p :=
    muP_mono_family hp0 hp1 hsub
  have hsingle : muP X (upClosureIn X {S}) p = p ^ S.card :=
    muP_upClosure_single X S hSX hp0 hp1
  simpa [hsingle] using hmono

/-- If an increasing family contains a singleton, its product measure is at
least the density. -/
lemma density_le_muP_of_singleton_mem_increasing
    {X : Finset α} {U : Finset (Finset α)} {a : α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U)
    (hS : ({a} : Finset α) ∈ U) :
    p ≤ muP X U p := by
  have hpow :
      p ^ ({a} : Finset α).card ≤ muP X U p :=
    pow_card_le_muP_of_mem_increasing hp0 hp1 hUX hIncr hS
  simpa using hpow

/-- A nonempty increasing family has product measure at least `p^ell`: choose a
minimal member, whose cardinality is bounded by `ell`. -/
lemma pow_ell_le_muP_of_nonempty_increasing
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hU : U.Nonempty) :
    p ^ ell X U ≤ muP X U p := by
  rcases minimalMembersIn_nonempty_of_nonempty (X := X) hU with ⟨S, hSmin⟩
  have hSU : S ∈ U := minimalMembersIn_subset hSmin
  have hcard : S.card ≤ ell X U := card_le_ell_of_mem_minimalMembersIn hSmin
  have hpow : p ^ ell X U ≤ p ^ S.card :=
    pow_le_pow_of_le_one hp0 hp1 hcard
  exact hpow.trans (pow_card_le_muP_of_mem_increasing hp0 hp1 hUX hIncr hSU)

end

end ParkPham
end Erdos202
