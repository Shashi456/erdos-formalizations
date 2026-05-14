/-
Erdős Problem 202 — Park–Pham layer, Stage 4.

# Status

This file formalizes the Park–Pham / Kahn–Kalai expectation-threshold package
used by the spread-disjointness layer.  The finite Boolean-family reductions,
fragment-cost iteration, and scalar snoc budget schedule are all proved in
`ParkPham/`; the exported theorem below has no project-level assumption
dependency.

# Classical content

The Kahn–Kalai expectation-threshold conjecture, proved by Jinyoung Park
and Huy Tuan Pham in 2022 (arXiv:2203.17207), states roughly:

  For every increasing family `U` on a finite ground set `X`, the actual
  threshold `p_c(U)` differs from the expectation threshold `q(U)` by at
  most a logarithmic factor:
        `p_c(U) ≤ C · q(U) · log(ℓ(U))`
  for an absolute constant `C` and a complexity parameter
  `ℓ(U) := max(2, max cardinality of minimal members of U)`.

In the finite form below we phrase the conclusion as: if `q` is an upper
bound on the expectation threshold (in the sense of `qSmallUpper`), then
at density `p = C · q · log(ℓ(U))` the product measure `muP X U p` is at
least `1/2`.

# Shape decision

The deep input is stated as an existential package at the exact threshold
`p = C_KK q log ell`, in the genuinely subcritical case `p < 1`.
The endpoint case `p = 1` is elementary and is proved below, using
`muP_one_of_nonempty_increasing`.  The "any larger `p`" downstream interface is
then derived using the finite density-monotonicity theorem `muP_mono_density`.

# Formalization status

The final scalar schedule uses constant block length `64` and power-of-two
cutoffs of length `Nat.log 2 m + 1`, reducing the recursive snoc budget to the
finite geometric bound `∑ (1/16)^(2^j) < 1/4`.
-/

import Mathlib
import Erdos.P202.ParkPham.BooleanFamilies
import Erdos.P202.ParkPham.ProductMeasure
import Erdos.P202.ParkPham.Smallness
import Erdos.P202.ParkPham.Fragments
import Erdos.P202.ParkPham.Cost
import Erdos.P202.ParkPham.FragmentCost
import Erdos.P202.ParkPham.FragmentIteration

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

universe u

section ThresholdDefinitions

variable {α : Type*} [DecidableEq α]

/-- `CriticalAtMost X U p` is the finite product-measure form of
`p_c(U) ≤ p`: at density `p`, the increasing event already has measure at
least `1/2`. -/
def CriticalAtMost (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ muP X U p ≥ 1 / 2

/-- `ExpectationAtMost X U q` is the finite `q(U) ≤ q` predicate used by the
Park--Pham theorem.  The substantive part is `qSmallUpper`; the interval bounds
are bundled for theorem statements that mirror the paper. -/
def ExpectationAtMost (X : Finset α) (U : Finset (Finset α)) (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1 ∧ qSmallUpper X U q

lemma CriticalAtMost.mono_density {X : Finset α} {U : Finset (Finset α)}
    {p r : ℝ} (hIncr : IncreasingIn X U)
    (hcrit : CriticalAtMost X U p) (hpr : p ≤ r) (hr1 : r ≤ 1) :
    CriticalAtMost X U r := by
  rcases hcrit with ⟨hp0, _hp1, hmu⟩
  have hmono : muP X U p ≤ muP X U r :=
    muP_mono_density hIncr hp0 hpr hr1
  exact ⟨hp0.trans hpr, hr1, hmu.trans hmono⟩

omit [DecidableEq α] in
lemma ExpectationAtMost.mono_q {X : Finset α} {U : Finset (Finset α)}
    {q r : ℝ} (hexp : ExpectationAtMost X U q) (hqr : q ≤ r) (hr1 : r ≤ 1) :
    ExpectationAtMost X U r := by
  rcases hexp with ⟨hq0, _hq1, hSmall⟩
  exact ⟨hq0.trans hqr, hr1, qSmallUpper_mono_q hqr hSmall⟩

omit [DecidableEq α] in
lemma ExpectationAtMost.of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hNotSmall : ¬ pSmall X U q) :
    ExpectationAtMost X U q :=
  ⟨hq0, hq1, qSmallUpper_of_not_pSmall hq0 hNotSmall⟩

lemma CriticalAtMost.of_empty_mem_increasing {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) :
    CriticalAtMost X U p := by
  have hmu : muP X U p = 1 :=
    muP_eq_one_of_empty_mem_increasing hUX hIncr hEmpty p
  rw [CriticalAtMost, hmu]
  norm_num [hp0, hp1]

omit [DecidableEq α] in
lemma ExpectationAtMost.one (X : Finset α) (U : Finset (Finset α)) :
    ExpectationAtMost X U (1 : ℝ) := by
  exact ⟨by norm_num, le_rfl, qSmallUpper_one X U⟩

omit [DecidableEq α] in
lemma ExpectationAtMost.zero_iff_empty_mem
    (X : Finset α) (U : Finset (Finset α)) :
    ExpectationAtMost X U (0 : ℝ) ↔ (∅ : Finset α) ∈ U := by
  rw [ExpectationAtMost, qSmallUpper_zero_iff_empty_mem]
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨le_rfl, by norm_num, h⟩

lemma ExpectationAtMost.minimalMembersIn_iff
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ) :
    ExpectationAtMost X (minimalMembersIn X U) q ↔
      ExpectationAtMost X U q := by
  rw [ExpectationAtMost, ExpectationAtMost, qSmallUpper_minimalMembersIn_iff]

lemma CriticalAtMost.of_mu_ge {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hmu : muP X U p ≥ 1 / 2) :
    CriticalAtMost X U p :=
  ⟨hp0, hp1, hmu⟩

lemma CriticalAtMost.of_pow_ell_ge_half
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hU : U.Nonempty) (hpow : (1 / 2 : ℝ) ≤ p ^ ell X U) :
    CriticalAtMost X U p := by
  have hmu_lower : p ^ ell X U ≤ muP X U p :=
    pow_ell_le_muP_of_nonempty_increasing hp0 hp1 hUX hIncr hU
  exact CriticalAtMost.of_mu_ge hp0 hp1 (hpow.trans hmu_lower)

lemma CriticalAtMost.of_mem_pow_card_ge_half
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hS : S ∈ U)
    (hpow : (1 / 2 : ℝ) ≤ p ^ S.card) :
    CriticalAtMost X U p := by
  have hmu_lower : p ^ S.card ≤ muP X U p :=
    pow_card_le_muP_of_mem_increasing hp0 hp1 hUX hIncr hS
  exact CriticalAtMost.of_mu_ge hp0 hp1 (hpow.trans hmu_lower)

lemma CriticalAtMost.of_mem_card_le
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ} {k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U) (hS : S ∈ U)
    (hcard : S.card ≤ k) (hpow : (1 / 2 : ℝ) ≤ p ^ k) :
    CriticalAtMost X U p := by
  have hpow_le : p ^ k ≤ p ^ S.card :=
    pow_le_pow_of_le_one hp0 hp1 hcard
  exact CriticalAtMost.of_mem_pow_card_ge_half hp0 hp1 hUX hIncr hS
    (hpow.trans hpow_le)

lemma CriticalAtMost.of_exists_mem_card_le
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} {k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U)
    (hExists : ∃ S ∈ U, S.card ≤ k) (hpow : (1 / 2 : ℝ) ≤ p ^ k) :
    CriticalAtMost X U p := by
  rcases hExists with ⟨S, hS, hcard⟩
  exact CriticalAtMost.of_mem_card_le hp0 hp1 hUX hIncr hS hcard hpow

/-- Finite dichotomy behind the reduced Park--Pham core: either a small member
already makes the family critical, or all minimal members are large enough that
non-smallness forces many of them. -/
lemma CriticalAtMost.or_many_minimalMembers_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} {k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U p) (hpow : (1 / 2 : ℝ) ≤ p ^ k) :
    CriticalAtMost X U p ∨
      (1 / 2 : ℝ) <
        ((minimalMembersIn X U).card : ℝ) * p ^ (k + 1) := by
  by_cases hExists : ∃ S ∈ U, S.card ≤ k
  · exact Or.inl
      (CriticalAtMost.of_exists_mem_card_le hp0 hp1 hUX hIncr hExists hpow)
  · refine Or.inr ?_
    exact half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge hp0 hp1
      (fun T hT => by
        have hTU : T ∈ U := minimalMembersIn_subset hT
        have hnot_le : ¬ T.card ≤ k := by
          intro hle
          exact hExists ⟨T, hTU, hle⟩
        exact Nat.succ_le_iff.mpr (lt_of_not_ge hnot_le))
      hNotSmall

lemma CriticalAtMost.of_singleton_mem
    {X : Finset α} {U : Finset (Finset α)} {a : α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hhalf : (1 / 2 : ℝ) ≤ p)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hS : ({a} : Finset α) ∈ U) :
    CriticalAtMost X U p := by
  have hmu_lower : p ≤ muP X U p :=
    density_le_muP_of_singleton_mem_increasing hp0 hp1 hUX hIncr hS
  exact CriticalAtMost.of_mu_ge hp0 hp1 (hhalf.trans hmu_lower)

lemma CriticalAtMost.of_minimal_card_one
    {X : Finset α} {U : Finset (Finset α)} {S : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hhalf : (1 / 2 : ℝ) ≤ p)
    (hUX : ∀ T ∈ U, T ⊆ X) (hIncr : IncreasingIn X U)
    (hS : S ∈ minimalMembersIn X U) (hcard : S.card = 1) :
    CriticalAtMost X U p := by
  rcases exists_singleton_mem_of_mem_minimalMembersIn_card_eq_one hS hcard with ⟨a, ha⟩
  exact CriticalAtMost.of_singleton_mem hp0 hp1 hhalf hUX hIncr ha

end ThresholdDefinitions

/-- The strict Park--Pham conclusion is elementary when an increasing family
contains `∅`: then the family is the whole Boolean cube, so its product measure
is `1` at every density. -/
lemma park_pham_threshold_not_small_lt_of_empty_mem
    {α : Type*} [DecidableEq α]
    (CKK : ℝ) (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hEmpty : (∅ : Finset α) ∈ U) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  have hmu : muP X U (CKK * q * Real.log (ell X U)) = 1 :=
    muP_eq_one_of_empty_mem_increasing hUX hIncr hEmpty _
  rw [hmu]
  norm_num

/-- Reduction of the strict Park--Pham theorem to the nontrivial case
`∅ ∉ U`.  This keeps future work focused on the actual Kahn--Kalai/Park--Pham
core rather than the endpoint where the increasing family is the whole cube. -/
theorem park_pham_threshold_not_small_lt_reduce_empty
    {α : Type*} [DecidableEq α] (CKK : ℝ)
    (hCore :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        (∅ : Finset α) ∉ U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2)
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U q) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  by_cases hEmpty : (∅ : Finset α) ∈ U
  · exact park_pham_threshold_not_small_lt_of_empty_mem CKK X U q hUX hIncr hEmpty
  · exact hCore X U q hq0 hq1 hthreshold_lt_one hUX hIncr hEmpty hNotSmall

/-- For a Park--Pham constant at least `2 / log 2`, the bounded case
`C * q * log(ell) ≤ 1` automatically has `q < 1`. -/
lemma q_lt_one_of_large_constant_threshold_le_one
    {α : Type*} [DecidableEq α]
    {CKK q : ℝ} {X : Finset α} {U : Finset (Finset α)}
    (hCKK : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hq1 : q ≤ 1)
    (hthreshold_le_one : CKK * q * Real.log (ell X U) ≤ 1) :
    q < 1 := by
  by_contra hnot
  have hq_ge_one : (1 : ℝ) ≤ q := le_of_not_gt hnot
  have hq_eq_one : q = 1 := le_antisymm hq1 hq_ge_one
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hlog2_le : Real.log 2 ≤ Real.log (ell X U) :=
    Real.log_le_log (by norm_num) hell_ge_two
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK
  have hCKK_log2_le :
      CKK * Real.log 2 ≤ CKK * Real.log (ell X U) :=
    mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
  have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hCKK hlog2_pos.le
    have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
      field_simp [hlog2_pos.ne']
    linarith
  have hCKK_log_le_one : CKK * Real.log (ell X U) ≤ 1 := by
    simpa [hq_eq_one] using hthreshold_le_one
  linarith

/-- For a Park--Pham constant at least `2 / log 2`, the strict case
`C * q * log(ell) < 1` automatically has `q < 1`. -/
lemma q_lt_one_of_large_constant_threshold_lt_one
    {α : Type*} [DecidableEq α]
    {CKK q : ℝ} {X : Finset α} {U : Finset (Finset α)}
    (hCKK : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hq1 : q ≤ 1)
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1) :
    q < 1 :=
  q_lt_one_of_large_constant_threshold_le_one hCKK hq1 hthreshold_lt_one.le

/-- The genuinely nontrivial strict Park--Pham/Kahn--Kalai core on one fixed
ground type, after local finite reductions: the family does not contain `∅`,
the expectation-threshold parameter is strictly inside `(0,1)`, and the target
density is strictly below `1`. -/
def StrictNonSmallCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X U) < 1 →
    (∀ S ∈ U, S ⊆ X) →
    IncreasingIn X U →
    (∅ : Finset α) ∉ U →
    ¬ pSmall X U q →
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2

/-- Generated-family form of the reduced strict core.  Instead of taking an
already-increasing family `U`, the theorem is stated for the upper closure of a
generating family `A`. -/
def StrictGeneratedCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X (upClosureIn X A)) < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ upClosureIn X A →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log (ell X (upClosureIn X A))) ≥ 1 / 2

/-- The remaining strict core after removing the elementary branch where the
target density already gives a single minimal member probability at least
`1/2`. -/
def StrictHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X U) < 1 →
    (CKK * q * Real.log (ell X U)) ^ ell X U < 1 / 2 →
    (∀ S ∈ U, S ⊆ X) →
    IncreasingIn X U →
    (∅ : Finset α) ∉ U →
    ¬ pSmall X U q →
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2

/-- Generated-family version of `StrictHardCoreOn`. -/
def StrictGeneratedHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    CKK * q * Real.log (ell X (upClosureIn X A)) < 1 →
    (CKK * q * Real.log (ell X (upClosureIn X A))) ^
        ell X (upClosureIn X A) < 1 / 2 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ upClosureIn X A →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log (ell X (upClosureIn X A))) ≥ 1 / 2

/-- Antichain-generator form of the hard core, with the complexity parameter
rewritten away from the upper closure. -/
def StrictAntichainHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Antichain hard core after the elementary one-generator case has been
removed. -/
def StrictAntichainMultiHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    1 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Antichain hard core after the elementary one- and two-generator cases have
been removed. -/
def StrictAntichainLargeHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Remaining antichain hard core after removing any branch where one
generator alone already has probability at least `1/2` at the target density. -/
def StrictAntichainSparseHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Remaining antichain hard core with the automatic sparse size condition
exposed as a hypothesis. -/
def StrictAntichainScaledHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    A.Nonempty →
    2 < A.card →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Scaled hard core with the redundant nonempty/cardinality hypotheses
removed.  They follow from the scale condition when the constant is large. -/
def StrictAntichainScaleOnlyHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Current reduced antichain hard core.  The scale condition implies
nonemptiness and the global low-density condition follows from the per-generator
smallness condition. -/
def StrictAntichainReducedHardCoreOn (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    muP X (upClosureIn X A)
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ≥ 1 / 2

/-- Park--Vondrak certificate form for the current reduced hard core.  It
isolates the remaining probabilistic iteration work: construct a finite snoc
sequence of independent exposures whose union density is at most the target
density and whose expected accumulated large-fragment loss is below half the
initial cover cost. -/
def StrictAntichainReducedPVCertificateOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ ρ : Fin (n + 1) → ℝ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 0 ≤ ρ i) ∧
      (∀ i, ρ i ≤ 1) ∧
      cutoff (Fin.last n) = 1 ∧
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) <
        coverCost X A q * (1 / 2)

/-- Quarter-budget version of the Park--Vondrak certificate.  Non-smallness
implies the initial cover cost is greater than `1/2`, so a uniform accumulated
loss bound by `1/4` is enough for the reduced hard core. -/
def StrictAntichainReducedPVQuarterCertificateOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ ρ : Fin (n + 1) → ℝ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 0 ≤ ρ i) ∧
      (∀ i, ρ i ≤ 1) ∧
      cutoff (Fin.last n) = 1 ∧
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) <
        (1 / 4 : ℝ)

/-- Coarse numeric Park--Vondrak stage scheme for the reduced antichain target.
This is a sufficient bridge for testing the scalar density/budget plumbing.
The final proof is expected to use a refined variant whose large-fragment
budget uses the current post-small-fragment cardinality bound at each stage,
not the original `max 2 (A.sup card)` at every stage. -/
def StrictAntichainReducedPVNumericSchemeOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 1 ≤ L i) ∧
      cutoff (Fin.last n) = 1 ∧
      q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      (∑ i : Fin (n + 1),
        (2 : ℝ) ^ max 2 (A.sup Finset.card) *
          (1 / (L i : ℝ)) ^ cutoff i) < (1 / 4 : ℝ)

/-- Refined numeric Park--Vondrak stage scheme for the reduced antichain
target.  This is the viable scalar target exposed by the current finite
bookkeeping: the large-fragment budget charges stage `i` using the cardinality
bound available after the previous small-fragment stage. -/
def StrictAntichainReducedPVSnocBudgetSchemeOn
    (CKK : ℝ) (α : Type*) [DecidableEq α] : Prop :=
  ∀ (X : Finset α) (A : Finset (Finset α)) (q : ℝ),
    0 < q → q < 1 →
    (∀ S ∈ A, S ⊆ X) →
    InclusionAntichain A →
    (∅ : Finset α) ∉ A →
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) →
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 →
    (∀ S ∈ A,
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          S.card < 1 / 2) →
    ¬ pSmall X (upClosureIn X A) q →
    ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 1 ≤ L i) ∧
      cutoff (Fin.last n) = 1 ∧
      q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) ∧
      snocLargeCostBudget (max 2 (A.sup Finset.card)) cutoff L <
        (1 / 4 : ℝ)

/-- Pure scalar parameter target for the refined Park--Vondrak stage scheme.
This removes all Boolean-family data: it remains only to construct a finite
sequence of integer block lengths and cutoffs whose exposure budget is
`O(log m)` and whose recursive large-fragment budget is below `1/4`. -/
def PVSnocScalarParameterScheme (CKK : ℝ) : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    ∃ n : ℕ, ∃ L : Fin (n + 1) → ℕ, ∃ cutoff : Fin (n + 1) → ℕ,
      (∀ i, 1 ≤ L i) ∧
      cutoff (Fin.last n) = 1 ∧
      (∑ i : Fin (n + 1), (L i : ℝ)) ≤ CKK * Real.log (m : ℝ) ∧
      snocLargeCostBudget m cutoff L < (1 / 4 : ℝ)

/-- Power-of-two cutoffs for the scalar snoc schedule.  At stage `i`, the
cutoff is `2^(a+n-i)`; the public scalar scheme uses `a=0` and
`n = Nat.log 2 m`. -/
noncomputable def pvSnocPowerCutoff (a n : ℕ) (i : Fin (n + 1)) : ℕ :=
  2 ^ (a + (n - i.1))

lemma pvSnocPowerCutoff_tail (a n : ℕ) :
    (fun i : Fin (n + 1) => pvSnocPowerCutoff a (n + 1) i.castSucc) =
      pvSnocPowerCutoff (a + 1) n := by
  funext i
  have hi : i.1 ≤ n := Nat.lt_succ_iff.mp i.2
  simp [pvSnocPowerCutoff]
  have hsub : n + 1 - i.1 = n - i.1 + 1 := by omega
  rw [hsub]
  omega

lemma pvSnocPowerCutoff_last (a n : ℕ) :
    pvSnocPowerCutoff a n (Fin.last n) = 2 ^ a := by
  simp [pvSnocPowerCutoff]

lemma nat_succ_le_two_pow_local (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
      rw [Nat.pow_succ]
      nlinarith

lemma pow_two_mul_inv_sixtyfour_pow_le (c b : ℕ) (hb : b ≤ 2 * c) :
    (2 : ℝ) ^ b * (1 / (64 : ℝ)) ^ c ≤ (1 / 16 : ℝ) ^ c := by
  have hpow : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (2 * c) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb
  have hnonneg : 0 ≤ (1 / (64 : ℝ)) ^ c := by positivity
  calc
    (2 : ℝ) ^ b * (1 / (64 : ℝ)) ^ c
        ≤ (2 : ℝ) ^ (2 * c) * (1 / (64 : ℝ)) ^ c :=
          mul_le_mul_of_nonneg_right hpow hnonneg
    _ = (1 / 16 : ℝ) ^ c := by
          rw [pow_mul]
          rw [← mul_pow]
          norm_num

lemma snocLargeCostBudget_pvSnocPowerCutoff_le_geometric
    (ell a n : ℕ) (hfirst : ell ≤ 2 * 2 ^ (a + n)) :
    snocLargeCostBudget ell (pvSnocPowerCutoff a n)
        (fun _ : Fin (n + 1) => 64) ≤
      ∑ j ∈ Finset.range (n + 1),
        (1 / 16 : ℝ) ^ (2 ^ (a + (n - j))) := by
  induction n generalizing a with
  | zero =>
      have hterm := pow_two_mul_inv_sixtyfour_pow_le (2 ^ a) ell hfirst
      simpa [snocLargeCostBudget, snocCurrentCardBound, pvSnocPowerCutoff]
        using hterm
  | succ n ih =>
      have htail_first : ell ≤ 2 * 2 ^ ((a + 1) + n) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst
      have htail := ih (a + 1) htail_first
      have hcurrent :
          snocCurrentCardBound ell (pvSnocPowerCutoff (a + 1) n) =
            2 ^ (a + 1) := by
        simp [snocCurrentCardBound, pvSnocPowerCutoff]
      have hcurrent_le : 2 ^ (a + 1) ≤ 2 * 2 ^ a := by
        rw [Nat.pow_succ]
        omega
      have hterm :=
        pow_two_mul_inv_sixtyfour_pow_le (2 ^ a) (2 ^ (a + 1)) hcurrent_le
      calc
        snocLargeCostBudget ell (pvSnocPowerCutoff a (n + 1))
            (fun _ : Fin (n + 1 + 1) => 64)
            ≤ (∑ j ∈ Finset.range (n + 1),
                  (1 / 16 : ℝ) ^ (2 ^ ((a + 1) + (n - j)))) +
                (1 / 16 : ℝ) ^ (2 ^ a) := by
              rw [snocLargeCostBudget]
              simp only [pvSnocPowerCutoff_tail]
              have hLtail :
                  (fun i : Fin (n + 1) =>
                    (fun _ : Fin (n + 1 + 1) => 64) i.castSucc) =
                    (fun _ : Fin (n + 1) => 64) := rfl
              rw [hLtail]
              have hlastCut :
                  pvSnocPowerCutoff a (n + 1) (Fin.last (n + 1)) = 2 ^ a :=
                pvSnocPowerCutoff_last a (n + 1)
              rw [hlastCut, hcurrent]
              exact add_le_add htail hterm
        _ = ∑ j ∈ Finset.range (n + 1 + 1),
              (1 / 16 : ℝ) ^ (2 ^ (a + ((n + 1) - j))) := by
              conv_rhs => rw [Finset.sum_range_succ]
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro j hj
                have hjle : j ≤ n :=
                  Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                have hsub : n + 1 - j = n - j + 1 := by omega
                rw [hsub]
                congr 2
                omega
              · simp

lemma pvSnocGeometricSum_le (a n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (1 / 16 : ℝ) ^ (2 ^ (a + (n - j)))) ≤
      (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
  induction n generalizing a with
  | zero =>
      have hle_exp : a + 1 ≤ 2 ^ a := nat_succ_le_two_pow_local a
      have hpow_le :
          (1 / 16 : ℝ) ^ (2 ^ a) ≤ (1 / 16 : ℝ) ^ (a + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hle_exp
      have hden_pos : 0 < (1 - (1 / 16 : ℝ)) := by norm_num
      have hx : 0 ≤ (1 / 16 : ℝ) ^ (a + 1) := by positivity
      have hle_div :
          (1 / 16 : ℝ) ^ (a + 1) ≤
            (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
        rw [le_div_iff₀ hden_pos]
        nlinarith
      simpa using hpow_le.trans hle_div
  | succ n ih =>
      have htail := ih (a + 1)
      have hle_exp : a + 1 ≤ 2 ^ a := nat_succ_le_two_pow_local a
      have hterm_le :
          (1 / 16 : ℝ) ^ (2 ^ a) ≤ (1 / 16 : ℝ) ^ (a + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hle_exp
      calc
        (∑ j ∈ Finset.range (n + 1 + 1),
          (1 / 16 : ℝ) ^ (2 ^ (a + ((n + 1) - j))))
            = (∑ j ∈ Finset.range (n + 1),
                (1 / 16 : ℝ) ^ (2 ^ ((a + 1) + (n - j)))) +
              (1 / 16 : ℝ) ^ (2 ^ a) := by
                conv_lhs => rw [Finset.sum_range_succ]
                congr 1
                · refine Finset.sum_congr rfl ?_
                  intro j hj
                  have hjle : j ≤ n :=
                    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                  have hsub : n + 1 - j = n - j + 1 := by omega
                  rw [hsub]
                  congr 2
                  omega
                · simp
        _ ≤ (1 / 16 : ℝ) ^ ((a + 1) + 1) /
              (1 - (1 / 16 : ℝ)) +
              (1 / 16 : ℝ) ^ (a + 1) := by
                exact add_le_add htail hterm_le
        _ = (1 / 16 : ℝ) ^ (a + 1) / (1 - (1 / 16 : ℝ)) := by
              ring_nf

lemma pvSnocGeometricSum_zero_lt_quarter (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (1 / 16 : ℝ) ^ (2 ^ (0 + (n - j)))) < (1 / 4 : ℝ) := by
  have h := pvSnocGeometricSum_le 0 n
  have hconst :
      (1 / 16 : ℝ) ^ (0 + 1) / (1 - (1 / 16 : ℝ)) < (1 / 4 : ℝ) := by
    norm_num
  exact lt_of_le_of_lt h hconst

lemma natLog2_add_one_le_two_log_div_log2 (m : ℕ) (hm : 2 ≤ m) :
    (((Nat.log 2 m + 1 : ℕ) : ℝ)) ≤
      2 * Real.log (m : ℝ) / Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm_real : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog2_le_logm : Real.log 2 ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) hm_real
  have hquot_ge_one : (1 : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
    exact (le_div_iff₀ hlog2pos).2 (by simpa using hlog2_le_logm)
  have hlog_nat_le :
      ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb m
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  calc
    (((Nat.log 2 m + 1 : ℕ) : ℝ))
        = ((Nat.log 2 m : ℕ) : ℝ) + 1 := by norm_num
    _ ≤ Real.log (m : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ Real.log (m : ℝ) / Real.log 2 +
          Real.log (m : ℝ) / Real.log 2 := by linarith
    _ = 2 * Real.log (m : ℝ) / Real.log 2 := by ring

theorem pvSnocScalarParameterScheme_128_div_log_two :
    PVSnocScalarParameterScheme (128 / Real.log 2) := by
  intro m hm
  let n : ℕ := Nat.log 2 m
  let L : Fin (n + 1) → ℕ := fun _ => 64
  let cutoff : Fin (n + 1) → ℕ := pvSnocPowerCutoff 0 n
  refine ⟨n, L, cutoff, ?_, ?_, ?_, ?_⟩
  · intro i
    norm_num [L]
  · simpa [cutoff] using pvSnocPowerCutoff_last 0 n
  · have hsum_eq :
        (∑ i : Fin (n + 1), (L i : ℝ)) =
          64 * (((n + 1 : ℕ) : ℝ)) := by
      simp [L]
      ring
    have hlog_bound := natLog2_add_one_le_two_log_div_log2 m hm
    have hmul :=
      mul_le_mul_of_nonneg_left hlog_bound (by norm_num : (0 : ℝ) ≤ 64)
    calc
      (∑ i : Fin (n + 1), (L i : ℝ))
          = 64 * (((n + 1 : ℕ) : ℝ)) := hsum_eq
      _ ≤ 64 * (2 * Real.log (m : ℝ) / Real.log 2) := by
        simpa [n, mul_assoc] using hmul
      _ = (128 / Real.log 2) * Real.log (m : ℝ) := by ring
  · have hfirst : m ≤ 2 * 2 ^ (0 + n) := by
      have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two m
      have hle : m ≤ 2 ^ (Nat.log 2 m + 1) := Nat.le_of_lt hlt
      simpa [n, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using hle
    have hbudget_le :=
      snocLargeCostBudget_pvSnocPowerCutoff_le_geometric m 0 n hfirst
    have hgeom_lt := pvSnocGeometricSum_zero_lt_quarter n
    exact lt_of_le_of_lt (by simpa [cutoff, L, n] using hbudget_le) hgeom_lt

theorem exists_pv_snoc_scalar_parameter_scheme :
    ∃ CKK : ℝ, 0 < CKK ∧ (2 / Real.log 2 : ℝ) ≤ CKK ∧
      PVSnocScalarParameterScheme CKK := by
  refine ⟨128 / Real.log 2, ?_, ?_, pvSnocScalarParameterScheme_128_div_log_two⟩
  · positivity
  · have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 128)
      hlog2pos.le

/-- The pure scalar parameter target implies the reduced snoc-budget scheme. -/
theorem strictAntichainReducedPVSnocBudgetSchemeOn_of_scalarParameterScheme
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hScalar : PVSnocScalarParameterScheme CKK) :
    StrictAntichainReducedPVSnocBudgetSchemeOn CKK α := by
  intro X A q hq0 _hq1 _hAX _hAnti _hEmptyA _hscale_lt _hthreshold_lt_one
    _hNoHeavy _hNotSmall
  let m : ℕ := max 2 (A.sup Finset.card)
  have hm_two : 2 ≤ m := by
    dsimp [m]
    exact le_max_left _ _
  rcases hScalar m hm_two with
    ⟨n, L, cutoff, hL, hlast, hsum, hbudget⟩
  have hdensity :
      q * (∑ i : Fin (n + 1), (L i : ℝ)) ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsum hq0.le
    simpa [m, mul_assoc, mul_comm, mul_left_comm] using hmul
  exact ⟨n, L, cutoff, hL, hlast, hdensity, by simpa [m] using hbudget⟩

/-- A coarse numeric Park--Vondrak stage scheme gives the explicit quarter-budget
certificate by taking coordinate densities `ρᵢ = 1 - (1-q)^{Lᵢ}` and applying
the scalar union bound plus the iterated large-fragment budget lemma. -/
theorem strictAntichainReducedPVQuarterCertificateOn_of_numericSchemeOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hScheme : StrictAntichainReducedPVNumericSchemeOn CKK α) :
    StrictAntichainReducedPVQuarterCertificateOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  rcases hScheme X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, L, cutoff, hL, hlast, hdensity, hbudget⟩
  let ρ : Fin (n + 1) → ℝ := fun i => 1 - (1 - q) ^ L i
  have hq_le_one : q ≤ 1 := hq1.le
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase1 : 1 - q ≤ 1 := by linarith
  have hρ0 : ∀ i, 0 ≤ ρ i := by
    intro i
    have hpow_le_one : (1 - q) ^ L i ≤ (1 : ℝ) :=
      pow_le_one₀ hbase0 hbase1
    dsimp [ρ]
    linarith
  have hρ1 : ∀ i, ρ i ≤ 1 := by
    intro i
    have hpow_nonneg : 0 ≤ (1 - q) ^ L i :=
      pow_nonneg hbase0 _
    dsimp [ρ]
    linarith
  have htuple :
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    have htuple_le :
        tupleUnionDensity ρ ≤ q * (∑ i : Fin (n + 1), (L i : ℝ)) := by
      simpa [ρ] using
        tupleUnionDensity_one_sub_pow_le_q_sum L hq0.le hq_le_one
    exact htuple_le.trans hdensity
  let m : ℕ := max 2 (A.sup Finset.card)
  have hAcard_bound : ∀ S ∈ A, S.card ≤ m := by
    intro S hS
    exact (Finset.le_sup (s := A) (f := Finset.card) hS).trans
      (le_max_right _ _)
  have havg_le :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) ≤
        ∑ i : Fin (n + 1),
          (2 : ℝ) ^ m * (1 / (L i : ℝ)) ^ cutoff i := by
    exact iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_budget_sum
      X A m ρ cutoff L hρ0 hρ1 hL hq0 hq_le_one
      (fun i => rfl) hAX hAcard_bound
  refine ⟨n, ρ, cutoff, hρ0, hρ1, hlast, htuple, ?_⟩
  exact havg_le.trans_lt (by simpa [m] using hbudget)

/-- A refined snoc-budget scheme gives the explicit quarter-budget
certificate. -/
theorem strictAntichainReducedPVQuarterCertificateOn_of_snocBudgetSchemeOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hScheme : StrictAntichainReducedPVSnocBudgetSchemeOn CKK α) :
    StrictAntichainReducedPVQuarterCertificateOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  rcases hScheme X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, L, cutoff, hL, hlast, hdensity, hbudget⟩
  let ρ : Fin (n + 1) → ℝ := fun i => 1 - (1 - q) ^ L i
  have hq_le_one : q ≤ 1 := hq1.le
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase1 : 1 - q ≤ 1 := by linarith
  have hρ0 : ∀ i, 0 ≤ ρ i := by
    intro i
    have hpow_le_one : (1 - q) ^ L i ≤ (1 : ℝ) :=
      pow_le_one₀ hbase0 hbase1
    dsimp [ρ]
    linarith
  have hρ1 : ∀ i, ρ i ≤ 1 := by
    intro i
    have hpow_nonneg : 0 ≤ (1 - q) ^ L i :=
      pow_nonneg hbase0 _
    dsimp [ρ]
    linarith
  have htuple :
      tupleUnionDensity ρ ≤
        CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    have htuple_le :
        tupleUnionDensity ρ ≤ q * (∑ i : Fin (n + 1), (L i : ℝ)) := by
      simpa [ρ] using
        tupleUnionDensity_one_sub_pow_le_q_sum L hq0.le hq_le_one
    exact htuple_le.trans hdensity
  let m : ℕ := max 2 (A.sup Finset.card)
  have hAcard_bound : ∀ S ∈ A, S.card ≤ m := by
    intro S hS
    exact (Finset.le_sup (s := A) (f := Finset.card) hS).trans
      (le_max_right _ _)
  have havg_le :
      (∑ Ws ∈ exposureTupleSpace X (n + 1),
        exposureTupleWeight X ρ Ws *
          iteratedLargeCostSum X q A (exposureTupleStepsSnoc cutoff Ws)) ≤
        snocLargeCostBudget m cutoff L := by
    exact iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_snocLargeCostBudget
      X A m ρ cutoff L hρ0 hρ1 hL hq0 hq_le_one
      (fun i => rfl) hAX hAcard_bound
  refine ⟨n, ρ, cutoff, hρ0, hρ1, hlast, htuple, ?_⟩
  exact havg_le.trans_lt (by simpa [m] using hbudget)

/-- A Park--Vondrak certificate for the reduced antichain hard core gives the
reduced hard core itself. -/
theorem strictAntichainReducedHardCoreOn_of_pvCertificateOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hCert : StrictAntichainReducedPVCertificateOn CKK α) :
    StrictAntichainReducedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  let θ : ℝ :=
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  rcases hCert X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, ρ, cutoff, hρ0, hρ1, hlast, hρ_le_target, havg⟩
  have hcost_half :
      (1 / 2 : ℝ) < coverCost X A q :=
    half_lt_coverCost_of_not_pSmall_upClosureIn hq0.le hAX hNotSmall
  have hcost_pos : 0 < coverCost X A q := by linarith
  have hhalf :
      (1 / 2 : ℝ) <
        muP X (upClosureIn X A) (tupleUnionDensity ρ) :=
    half_lt_muP_of_iteratedLargeCostSnoc_average_lt
      X A ρ cutoff hq0.le hρ0 hρ1 hcost_pos hlast havg
  have htuple_nonneg : 0 ≤ tupleUnionDensity ρ :=
    tupleUnionDensity_nonneg hρ0 hρ1
  have htheta_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact hthreshold_lt_one.le
  have hmono :
      muP X (upClosureIn X A) (tupleUnionDensity ρ) ≤
        muP X (upClosureIn X A) θ :=
    muP_mono_density (increasingIn_upClosureIn X A)
      htuple_nonneg (by simpa [θ] using hρ_le_target) htheta_le_one
  exact (le_of_lt hhalf).trans (by simpa [θ] using hmono)

/-- The quarter-budget Park--Vondrak certificate gives the reduced hard core
directly. -/
theorem strictAntichainReducedHardCoreOn_of_pvQuarterCertificateOn
    {CKK : ℝ} {α : Type*} [DecidableEq α]
    (hCert : StrictAntichainReducedPVQuarterCertificateOn CKK α) :
    StrictAntichainReducedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    hNoHeavy hNotSmall
  let θ : ℝ :=
    CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  rcases hCert X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
      hthreshold_lt_one hNoHeavy hNotSmall with
    ⟨n, ρ, cutoff, hρ0, hρ1, hlast, hρ_le_target, havg⟩
  have hhalf :
      (1 / 2 : ℝ) <
        muP X (upClosureIn X A) (tupleUnionDensity ρ) :=
    half_lt_muP_of_not_pSmall_iteratedLargeCostSnoc_average_lt_quarter
      X A ρ cutoff hq0 hρ0 hρ1 hAX hNotSmall hlast havg
  have htuple_nonneg : 0 ≤ tupleUnionDensity ρ :=
    tupleUnionDensity_nonneg hρ0 hρ1
  have htheta_le_one : θ ≤ 1 := by
    dsimp [θ]
    exact hthreshold_lt_one.le
  have hmono :
      muP X (upClosureIn X A) (tupleUnionDensity ρ) ≤
        muP X (upClosureIn X A) θ :=
    muP_mono_density (increasingIn_upClosureIn X A)
      htuple_nonneg (by simpa [θ] using hρ_le_target) htheta_le_one
  exact (le_of_lt hhalf).trans (by simpa [θ] using hmono)

/-- The generated-family core implies the increasing-family strict core by
taking the generators to be the minimal members. -/
theorem strict_nonSmallCoreOn_of_generatedCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictGeneratedCoreOn CKK α) :
    StrictNonSmallCoreOn CKK α := by
  intro X U q hq0 hq1 hthreshold_lt_one hUX hIncr hEmpty hNotSmall
  let A : Finset (Finset α) := minimalMembersIn X U
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hS
    exact hUX S (minimalMembersIn_subset hS)
  have hAnti : InclusionAntichain A := by
    simpa [A] using minimalMembersIn_inclusionAntichain X U
  have hclosure_eq : upClosureIn X A = U := by
    simpa [A] using upClosureIn_minimalMembersIn_eq_of_increasing hUX hIncr
  have hthreshold_A :
      CKK * q * Real.log (ell X (upClosureIn X A)) < 1 := by
    simpa [hclosure_eq] using hthreshold_lt_one
  have hEmpty_A : (∅ : Finset α) ∉ upClosureIn X A := by
    simpa [hclosure_eq] using hEmpty
  have hNotSmall_A : ¬ pSmall X (upClosureIn X A) q := by
    simpa [hclosure_eq] using hNotSmall
  have hmu :=
    hCore X A q hq0 hq1 hthreshold_A hAX hAnti hEmpty_A hNotSmall_A
  simpa [hclosure_eq] using hmu

/-- In the strict Park--Pham setup, the branch
`1/2 ≤ (C q log ell)^ell` is elementary: a non-small increasing family is
nonempty, so one of its minimal members has size at most `ell`, and the product
measure is already at least `1/2`. -/
theorem park_pham_threshold_not_small_lt_of_pow_ell_ge_half
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    (hCKK_pos : 0 < CKK) (hq0 : 0 < q)
    {X : Finset α} {U : Finset (Finset α)}
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U q)
    (hpow : (1 / 2 : ℝ) ≤
      (CKK * q * Real.log (ell X U)) ^ ell X U) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hlog_pos : 0 < Real.log (ell X U) :=
    lt_of_lt_of_le hlog2_pos (Real.log_le_log (by norm_num) hell_ge_two)
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) := by positivity
  have hp1 : CKK * q * Real.log (ell X U) ≤ 1 := hthreshold_lt_one.le
  have hU : U.Nonempty := nonempty_of_not_pSmall hNotSmall
  exact (CriticalAtMost.of_pow_ell_ge_half hp0 hp1 hUX hIncr hU hpow).2.2

/-- It is enough to prove the strict Park--Pham core in the low-density
hard case `(C q log ell)^ell < 1/2`; the complementary branch is elementary. -/
theorem strict_nonSmallCoreOn_of_hardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK) (hCore : StrictHardCoreOn CKK α) :
    StrictNonSmallCoreOn CKK α := by
  intro X U q hq0 hq1 hthreshold_lt_one hUX hIncr hEmpty hNotSmall
  by_cases hpow :
      (1 / 2 : ℝ) ≤ (CKK * q * Real.log (ell X U)) ^ ell X U
  · exact park_pham_threshold_not_small_lt_of_pow_ell_ge_half
      hCKK_pos hq0 hthreshold_lt_one hUX hIncr hNotSmall hpow
  · exact hCore X U q hq0 hq1 hthreshold_lt_one
      (lt_of_not_ge hpow) hUX hIncr hEmpty hNotSmall

/-- The generated hard core implies the increasing-family hard core by taking
generators to be the minimal members. -/
theorem strict_hardCoreOn_of_generatedHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictGeneratedHardCoreOn CKK α) :
    StrictHardCoreOn CKK α := by
  intro X U q hq0 hq1 hthreshold_lt_one hpow_lt hUX hIncr hEmpty hNotSmall
  let A : Finset (Finset α) := minimalMembersIn X U
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hS
    exact hUX S (minimalMembersIn_subset hS)
  have hAnti : InclusionAntichain A := by
    simpa [A] using minimalMembersIn_inclusionAntichain X U
  have hclosure_eq : upClosureIn X A = U := by
    simpa [A] using upClosureIn_minimalMembersIn_eq_of_increasing hUX hIncr
  have hthreshold_A :
      CKK * q * Real.log (ell X (upClosureIn X A)) < 1 := by
    simpa [hclosure_eq] using hthreshold_lt_one
  have hpow_A :
      (CKK * q * Real.log (ell X (upClosureIn X A))) ^
          ell X (upClosureIn X A) < 1 / 2 := by
    simpa [hclosure_eq] using hpow_lt
  have hEmpty_A : (∅ : Finset α) ∉ upClosureIn X A := by
    simpa [hclosure_eq] using hEmpty
  have hNotSmall_A : ¬ pSmall X (upClosureIn X A) q := by
    simpa [hclosure_eq] using hNotSmall
  have hmu :=
    hCore X A q hq0 hq1 hthreshold_A hpow_A hAX hAnti hEmpty_A hNotSmall_A
  simpa [hclosure_eq] using hmu

/-- Generated hard-core proofs are enough for the reduced increasing-family
strict core. -/
theorem strict_nonSmallCoreOn_of_generatedHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK) (hCore : StrictGeneratedHardCoreOn CKK α) :
    StrictNonSmallCoreOn CKK α :=
  strict_nonSmallCoreOn_of_hardCoreOn hCKK_pos
    (strict_hardCoreOn_of_generatedHardCoreOn hCore)

/-- The explicit antichain-generator hard core implies the generated hard
core: nonemptiness follows from non-smallness, `∅ ∉ A` follows from
`∅ ∉ upClosureIn X A`, and `ell` is rewritten by the antichain minimal-member
lemma. -/
theorem strictGeneratedHardCoreOn_of_antichainHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainHardCoreOn CKK α) :
    StrictGeneratedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hthreshold_lt_one hpow_lt hAX hAnti hEmpty hNotSmall
  have hA_nonempty : A.Nonempty :=
    nonempty_of_upClosureIn_nonempty (nonempty_of_not_pSmall hNotSmall)
  have hEmptyA : (∅ : Finset α) ∉ A :=
    empty_not_mem_upClosureIn_iff.mp hEmpty
  have hEll :
      ell X (upClosureIn X A) = max 2 (A.sup Finset.card) :=
    ell_upClosure_eq_of_inclusionAntichain hAnti hAX
  have hthreshold_A :
      CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1 := by
    simpa [hEll] using hthreshold_lt_one
  have hpow_A :
      (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
          max 2 (A.sup Finset.card) < 1 / 2 := by
    simpa [hEll] using hpow_lt
  have hmu :=
    hCore X A q hq0 hq1 hAX hAnti hA_nonempty hEmptyA
      hthreshold_A hpow_A hNotSmall
  simpa [hEll] using hmu

/-- It is enough to prove the explicit antichain hard core when the generator
has at least two members.  The one-generator case is elementary: the sole
generator covers its upper closure, so non-smallness gives
`1 / 2 < q^|S|`; for a large enough Park--Pham constant the target density is
at least `q`, and the singleton-upclosure measure identity finishes. -/
theorem strictAntichainHardCoreOn_of_multiHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainMultiHardCoreOn CKK α) :
    StrictAntichainHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hEmptyA
    hthreshold_lt_one _hpow_lt hNotSmall
  by_cases hcard_one : A.card = 1
  · rcases Finset.card_eq_one.mp hcard_one with ⟨S, hAeq⟩
    subst A
    have hSX : S ⊆ X := hAX S (by simp)
    have hCover : CoversIn X {S} (upClosureIn X {S}) := by
      intro T hT
      rcases mem_upClosureIn.mp hT with ⟨_, R, hR, hRT⟩
      have hR_eq : R = S := by simpa using hR
      exact ⟨S, by simp, by simpa [hR_eq] using hRT⟩
    have hqpow_gt : (1 / 2 : ℝ) < q ^ S.card := by
      by_contra hnot
      have hle : q ^ S.card ≤ (1 / 2 : ℝ) := le_of_not_gt hnot
      have hSmall : pSmall X (upClosureIn X {S}) q :=
        pSmall_of_cover_sum_le hCover (by simpa using hle)
      exact hNotSmall hSmall
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
    have hm_ge_two_nat : 2 ≤ max 2 S.card := le_max_left _ _
    have hm_ge_two : (2 : ℝ) ≤ ((max 2 S.card : ℕ) : ℝ) := by
      exact_mod_cast hm_ge_two_nat
    have hlog2_le : Real.log 2 ≤ Real.log ((max 2 S.card : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hm_ge_two
    have hlog_nonneg : 0 ≤ Real.log ((max 2 S.card : ℕ) : ℝ) :=
      le_trans hlog2_pos.le hlog2_le
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    have hone_le_CKK_logm :
        (1 : ℝ) ≤ CKK * Real.log ((max 2 S.card : ℕ) : ℝ) := by
      have hmono :
          CKK * Real.log 2 ≤ CKK * Real.log ((max 2 S.card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
      linarith
    have hq_le_target :
        q ≤ CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) := by
      calc
        q = q * 1 := by ring
        _ ≤ q * (CKK * Real.log ((max 2 S.card : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hone_le_CKK_logm hq0.le
        _ = CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) := by ring
    have hp0 : 0 ≤ CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) :=
      mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
    have hthreshold_S :
        CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) < 1 := by
      simpa using hthreshold_lt_one
    have hp1 : CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ) ≤ 1 :=
      hthreshold_S.le
    have hpow_q_le :
        q ^ S.card ≤
          (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
      pow_le_pow_left₀ hq0.le hq_le_target S.card
    have hmu :
        (1 / 2 : ℝ) ≤
          muP X (upClosureIn X {S})
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) := by
      have hstrict :
          (1 / 2 : ℝ) <
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
        hqpow_gt.trans_le hpow_q_le
      have hsingle :
          muP X (upClosureIn X {S})
              (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) =
            (CKK * q * Real.log ((max 2 S.card : ℕ) : ℝ)) ^ S.card :=
        muP_upClosure_single X S hSX hp0 hp1
      rw [hsingle]
      exact hstrict.le
    simpa using hmu
  · have hcard_gt_one : 1 < A.card := by
      have hpos : 0 < A.card := hA_nonempty.card_pos
      omega
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_gt_one hEmptyA
      hthreshold_lt_one _hpow_lt hNotSmall

/-- It is enough to prove the explicit antichain hard core when the generator
has at least three members.  The two-generator case is elementary: the cover by
the two generators has weight `> 1/2`, so the smaller generator has
`q`-weight `> 1/4`; at density at least `2q`, its principal up-closure already
has mass at least `1/2`. -/
theorem strictAntichainMultiHardCoreOn_of_largeHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainLargeHardCoreOn CKK α) :
    StrictAntichainMultiHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_gt_one hEmptyA
    hthreshold_lt_one hpow_lt hNotSmall
  by_cases hcard_two : A.card = 2
  · rcases A.exists_min_image Finset.card hA_nonempty with ⟨S, hSA, hS_min⟩
    have hCover : CoversIn X A (upClosureIn X A) := by
      intro T hT
      rcases mem_upClosureIn.mp hT with ⟨_, R, hRA, hRT⟩
      exact ⟨R, hRA, hRT⟩
    have hsum_gt :
        (1 / 2 : ℝ) < ∑ R ∈ A, q ^ R.card :=
      cover_sum_gt_half_of_not_pSmall hNotSmall hCover
    have hterm : ∀ R ∈ A, q ^ R.card ≤ q ^ S.card := by
      intro R hRA
      exact pow_le_pow_of_le_one hq0.le hq1.le (hS_min R hRA)
    have hsum_le :
        (∑ R ∈ A, q ^ R.card) ≤ ∑ R ∈ A, q ^ S.card :=
      Finset.sum_le_sum hterm
    have hconst :
        (∑ R ∈ A, q ^ S.card) = (A.card : ℝ) * q ^ S.card := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hqpow_quarter : (1 / 4 : ℝ) < q ^ S.card := by
      have hhalf_lt_two : (1 / 2 : ℝ) < (2 : ℝ) * q ^ S.card := by
        calc
          (1 / 2 : ℝ) < ∑ R ∈ A, q ^ R.card := hsum_gt
          _ ≤ ∑ R ∈ A, q ^ S.card := hsum_le
          _ = (A.card : ℝ) * q ^ S.card := hconst
          _ = (2 : ℝ) * q ^ S.card := by simp [hcard_two]
      linarith
    have hS_nonempty : S.Nonempty := by
      by_contra hS_empty
      have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
      exact hEmptyA (by simpa [hS_eq] using hSA)
    have hS_card_pos : 0 < S.card := hS_nonempty.card_pos
    let m : ℕ := max 2 (A.sup Finset.card)
    let p : ℝ := CKK * q * Real.log ((m : ℕ) : ℝ)
    have hm_ge_two_nat : 2 ≤ m := by
      dsimp [m]
      exact le_max_left _ _
    have hm_ge_two : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm_ge_two_nat
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hm_ge_two
    have hlog_nonneg : 0 ≤ Real.log ((m : ℕ) : ℝ) :=
      le_trans hlog2_pos.le hlog2_le
    have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    have htwo_le_CKK_logm : (2 : ℝ) ≤ CKK * Real.log ((m : ℕ) : ℝ) := by
      have hmono :
          CKK * Real.log 2 ≤ CKK * Real.log ((m : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
      linarith
    have htwoq_le_p : 2 * q ≤ p := by
      calc
        2 * q = q * 2 := by ring
        _ ≤ q * (CKK * Real.log ((m : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left htwo_le_CKK_logm hq0.le
        _ = p := by simp [p]; ring
    have htwoq_nonneg : 0 ≤ 2 * q := by positivity
    have htwo_pow_ge_two : (2 : ℝ) ≤ (2 : ℝ) ^ S.card := by
      cases hcard : S.card with
      | zero =>
          omega
      | succ n =>
          have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
            exact one_le_pow₀ (by norm_num)
          calc
            (2 : ℝ) = 2 * 1 := by ring
            _ ≤ 2 * (2 : ℝ) ^ n := by nlinarith
            _ = (2 : ℝ) ^ Nat.succ n := by rw [pow_succ]; ring
    have hhalf_lt_twoq_pow : (1 / 2 : ℝ) < (2 * q) ^ S.card := by
      rw [mul_pow]
      have hqpow_pos : 0 < q ^ S.card := pow_pos hq0 _
      have hhalf_lt_two_qpow : (1 / 2 : ℝ) < 2 * q ^ S.card := by
        linarith
      have htwo_qpow_le :
          2 * q ^ S.card ≤ (2 : ℝ) ^ S.card * q ^ S.card := by
        nlinarith
      exact hhalf_lt_two_qpow.trans_le htwo_qpow_le
    have hp_pow_lower : (1 / 2 : ℝ) ≤ p ^ S.card := by
      have hpow_le : (2 * q) ^ S.card ≤ p ^ S.card :=
        pow_le_pow_left₀ htwoq_nonneg htwoq_le_p S.card
      exact (hhalf_lt_twoq_pow.trans_le hpow_le).le
    have hp0 : 0 ≤ p := by
      dsimp [p]
      exact mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
    have hp1 : p ≤ 1 := by
      dsimp [p, m]
      exact hthreshold_lt_one.le
    have hS_up : S ∈ upClosureIn X A := subset_upClosureIn hAX hSA
    have hUX : ∀ T ∈ upClosureIn X A, T ⊆ X := by
      intro T hT
      exact (mem_upClosureIn.mp hT).1
    have hmu_lower :
        p ^ S.card ≤ muP X (upClosureIn X A) p :=
      pow_card_le_muP_of_mem_increasing hp0 hp1 hUX
        (increasingIn_upClosureIn X A) hS_up
    have hmu : (1 / 2 : ℝ) ≤ muP X (upClosureIn X A) p :=
      hp_pow_lower.trans hmu_lower
    simpa [p, m] using hmu
  · have hcard_large : 2 < A.card := by omega
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
      hthreshold_lt_one hpow_lt hNotSmall

/-- It is enough to prove the large antichain hard core when no single
generator is already heavy at the target density. -/
theorem strictAntichainLargeHardCoreOn_of_sparseHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainSparseHardCoreOn CKK α) :
    StrictAntichainLargeHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hthreshold_lt_one hpow_lt hNotSmall
  let m : ℕ := max 2 (A.sup Finset.card)
  let p : ℝ := CKK * q * Real.log ((m : ℕ) : ℝ)
  have hm_ge_two_nat : 2 ≤ m := by
    dsimp [m]
    exact le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm_ge_two_nat
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log ((m : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm_ge_two
  have hlog_nonneg : 0 ≤ Real.log ((m : ℕ) : ℝ) :=
    le_trans hlog2_pos.le hlog2_le
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
  have hp0 : 0 ≤ p := by
    dsimp [p]
    exact mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  have hp1 : p ≤ 1 := by
    dsimp [p, m]
    exact hthreshold_lt_one.le
  by_cases hHeavy : ∃ S ∈ A, (1 / 2 : ℝ) ≤ p ^ S.card
  · rcases hHeavy with ⟨S, hSA, hS_heavy⟩
    have hS_up : S ∈ upClosureIn X A := subset_upClosureIn hAX hSA
    have hUX : ∀ T ∈ upClosureIn X A, T ⊆ X := by
      intro T hT
      exact (mem_upClosureIn.mp hT).1
    have hmu_lower : p ^ S.card ≤ muP X (upClosureIn X A) p :=
      pow_card_le_muP_of_mem_increasing hp0 hp1 hUX
        (increasingIn_upClosureIn X A) hS_up
    exact hS_heavy.trans hmu_lower
  · have hNoHeavy : ∀ S ∈ A, p ^ S.card < 1 / 2 := by
      intro S hSA
      exact lt_of_not_ge fun hge => hHeavy ⟨S, hSA, hge⟩
    exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
      (by simpa [p, m] using hthreshold_lt_one)
      (by simpa [p, m] using hpow_lt)
      (by simpa [p, m] using hNoHeavy)
      hNotSmall

/-- The standard exact-threshold `qSmallUpper` Park--Pham theorem implies the
sparse antichain hard core directly. -/
theorem strictAntichainSparseHardCoreOn_of_threshold_at
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hThresholdAt :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2) :
    StrictAntichainSparseHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti _hA_nonempty _hcard_large _hEmptyA
    hthreshold_lt_one _hpow_lt _hNoHeavy hNotSmall
  have hEll :
      ell X (upClosureIn X A) = max 2 (A.sup Finset.card) :=
    ell_upClosure_eq_of_inclusionAntichain hAnti hAX
  have hthreshold_le :
      CKK * q * Real.log (ell X (upClosureIn X A)) ≤ 1 := by
    simpa [hEll] using hthreshold_lt_one.le
  have hUX : ∀ S ∈ upClosureIn X A, S ⊆ X := by
    intro S hS
    exact (mem_upClosureIn.mp hS).1
  have hmu :=
    hThresholdAt X (upClosureIn X A) q hq0 hq1.le hthreshold_le
      hUX (increasingIn_upClosureIn X A)
      (qSmallUpper_of_not_pSmall hq0.le hNotSmall)
  simpa [hEll] using hmu

/-- The standard larger-density `qSmallUpper` Park--Pham theorem implies the
sparse antichain hard core directly. -/
theorem strictAntichainSparseHardCoreOn_of_threshold
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2) :
    StrictAntichainSparseHardCoreOn CKK α := by
  refine strictAntichainSparseHardCoreOn_of_threshold_at ?_
  intro X U q hq0 hq1 hthreshold_le hUX hIncr hqSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) :=
    mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  exact hThreshold X U q (CKK * q * Real.log (ell X U))
    hq0 hq1 hp0 hthreshold_le le_rfl hUX hIncr hqSmall

/-- The standard exact-threshold `qSmallUpper` Park--Pham theorem also implies
the current reduced antichain hard core directly.  The extra reduced-core
hypotheses are finite reductions that are irrelevant once the standard theorem
is available. -/
theorem strictAntichainReducedHardCoreOn_of_threshold_at
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hThresholdAt :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2) :
    StrictAntichainReducedHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti _hEmptyA _hscale_lt
    hthreshold_lt_one _hNoHeavy hNotSmall
  have hEll :
      ell X (upClosureIn X A) = max 2 (A.sup Finset.card) :=
    ell_upClosure_eq_of_inclusionAntichain hAnti hAX
  have hthreshold_le :
      CKK * q * Real.log (ell X (upClosureIn X A)) ≤ 1 := by
    simpa [hEll] using hthreshold_lt_one.le
  have hUX : ∀ S ∈ upClosureIn X A, S ⊆ X := by
    intro S hS
    exact (mem_upClosureIn.mp hS).1
  have hmu :=
    hThresholdAt X (upClosureIn X A) q hq0 hq1.le hthreshold_le
      hUX (increasingIn_upClosureIn X A)
      (qSmallUpper_of_not_pSmall hq0.le hNotSmall)
  simpa [hEll] using hmu

/-- The standard larger-density `qSmallUpper` Park--Pham theorem also implies
the current reduced antichain hard core directly. -/
theorem strictAntichainReducedHardCoreOn_of_threshold
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2) :
    StrictAntichainReducedHardCoreOn CKK α := by
  refine strictAntichainReducedHardCoreOn_of_threshold_at ?_
  intro X U q hq0 hq1 hthreshold_le hUX hIncr hqSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) :=
    mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  exact hThreshold X U q (CKK * q * Real.log (ell X U))
    hq0 hq1 hp0 hthreshold_le le_rfl hUX hIncr hqSmall

/-- A conventional `ExpectationAtMost`/`CriticalAtMost` exact-threshold
statement also implies the current reduced antichain hard core directly. -/
theorem strictAntichainReducedHardCoreOn_of_expectation_critical
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hThreshold :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ExpectationAtMost X U q →
        CriticalAtMost X U (CKK * q * Real.log (ell X U))) :
    StrictAntichainReducedHardCoreOn CKK α := by
  refine strictAntichainReducedHardCoreOn_of_threshold_at ?_
  intro X U q hq0 hq1 hthreshold_le hUX hIncr hqSmall
  exact (hThreshold X U q hq0 hq1 hthreshold_le hUX hIncr
    ⟨hq0.le, hq1, hqSmall⟩).2.2

/-- On a fixed ground type, a proof of the reduced strict core for a constant
large enough to exclude `q = 1` gives the original strict non-smallness theorem
statement. -/
theorem park_pham_threshold_not_small_lt_of_strict_core_on
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictNonSmallCoreOn CKK α)
    (X : Finset α) (U : Finset (Finset α)) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1)
    (hUX : ∀ S ∈ U, S ⊆ X) (hIncr : IncreasingIn X U)
    (hNotSmall : ¬ pSmall X U q) :
    muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  by_cases hEmpty : (∅ : Finset α) ∈ U
  · exact park_pham_threshold_not_small_lt_of_empty_mem CKK X U q hUX hIncr hEmpty
  · have hq_lt_one : q < 1 :=
      q_lt_one_of_large_constant_threshold_lt_one hCKK_large hq1 hthreshold_lt_one
    exact hCore X U q hq0 hq_lt_one hthreshold_lt_one hUX hIncr hEmpty hNotSmall

/-- A uniform proof of the low-density hard core gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_strict_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  exact park_pham_threshold_not_small_lt_of_strict_core_on hCKK_large
    (strict_nonSmallCoreOn_of_hardCoreOn (α := α) hCKK_pos (hCore (α := α)))
    X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall

/-- A uniform proof of the generated low-density hard core gives the public
strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_generated_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictGeneratedHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_strict_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strict_hardCoreOn_of_generatedHardCoreOn (hCore (α := α)))

/-- A uniform proof of the explicit antichain-generator hard core gives the
public strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_generated_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictGeneratedHardCoreOn_of_antichainHardCoreOn
      (hCore (α := α)))

/-- A uniform proof of the multi-generator antichain hard core gives the
public strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_multi_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainMultiHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainHardCoreOn_of_multiHardCoreOn
      hCKK_large (hCore (α := α)))

/-- A uniform proof of the three-or-more-generator antichain hard core gives
the public strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_large_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainLargeHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_multi_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainMultiHardCoreOn_of_largeHardCoreOn
      hCKK_large (hCore (α := α)))

/-- A uniform proof of the sparse antichain hard core gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_sparse_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainSparseHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_large_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainLargeHardCoreOn_of_sparseHardCoreOn
      hCKK_large (hCore (α := α)))

/-- The standard exact-threshold `qSmallUpper` form implies the strict
non-smallness package used by this file. -/
theorem park_pham_threshold_not_small_lt_exists_of_threshold_at
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hThresholdAt :
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  exact hThresholdAt X U q hq0 hq1 hthreshold_lt_one.le hUX hIncr
    (qSmallUpper_of_not_pSmall hq0.le hNotSmall)

/-- The standard larger-density `qSmallUpper` form also implies the strict
non-smallness package, by evaluating it at the exact threshold. -/
theorem park_pham_threshold_not_small_lt_exists_of_threshold
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine park_pham_threshold_not_small_lt_exists_of_threshold_at hCKK_pos ?_
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hqSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hp0 : 0 ≤ CKK * q * Real.log (ell X U) := by positivity
  exact hThreshold X U q (CKK * q * Real.log (ell X U))
    hq0 hq1 hp0 hthreshold_le_one le_rfl hUX hIncr hqSmall

/-- A conventional `ExpectationAtMost`/`CriticalAtMost` exact-threshold
statement implies the strict non-smallness package used by this file. -/
theorem park_pham_threshold_not_small_lt_exists_of_expectation_critical
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hThreshold :
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ExpectationAtMost X U q →
        CriticalAtMost X U (CKK * q * Real.log (ell X U))) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  refine park_pham_threshold_not_small_lt_exists_of_threshold_at hCKK_pos ?_
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hqSmall
  exact (hThreshold X U q hq0 hq1 hthreshold_le_one hUX hIncr
    ⟨hq0.le, hq1, hqSmall⟩).2.2

/-- Finite consequence of the sparse hard-core assumptions: if the generator
cover is non-small at `q`, but no generator is individually heavy at the target
density, then some generator has `(C log m)^|S| < |A|`. -/
lemma exists_generator_scale_pow_lt_card_of_sparse
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    {X : Finset α} {A : Finset (Finset α)}
    (hCKK_pos : 0 < CKK) (hq0 : 0 < q)
    (hNoHeavy :
      ∀ S ∈ A,
        (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
            S.card < 1 / 2)
    (hNotSmall : ¬ pSmall X (upClosureIn X A) q) :
    ∃ S ∈ A,
      (CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^ S.card <
        (A.card : ℝ) := by
  rcases exists_generator_weight_gt_inv_two_mul_card_of_not_pSmall_upClosureIn
      hNotSmall with ⟨S, hSA, hq_weight⟩
  have hA_nonempty : A.Nonempty := ⟨S, hSA⟩
  have hAcard_pos_nat : 0 < A.card := hA_nonempty.card_pos
  have hAcard_pos : 0 < (A.card : ℝ) := by exact_mod_cast hAcard_pos_nat
  have hqpow_pos : 0 < q ^ S.card := pow_pos hq0 _
  have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    exact_mod_cast hm_ge_two_nat
  have hlog_nonneg :
      0 ≤ Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    (Real.log_pos (lt_of_lt_of_le (by norm_num) hm_ge_two)).le
  let L : ℝ := CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hCKK_pos.le hlog_nonneg
  have htarget :
      (L * q) ^ S.card < 1 / 2 := by
    have h := hNoHeavy S hSA
    simpa [L, mul_assoc, mul_left_comm, mul_comm] using h
  have hmul_lt : L ^ S.card * q ^ S.card < 1 / 2 := by
    simpa [mul_pow] using htarget
  have hscale_lt : L ^ S.card < (A.card : ℝ) := by
    by_contra hnot
    have hscale_ge : (A.card : ℝ) ≤ L ^ S.card := le_of_not_gt hnot
    have hmul_ge :
        (A.card : ℝ) * q ^ S.card ≤ L ^ S.card * q ^ S.card :=
      mul_le_mul_of_nonneg_right hscale_ge hqpow_pos.le
    have hquarter_lt : (1 / 2 : ℝ) < (A.card : ℝ) * q ^ S.card := by
      have hden_pos : 0 < 2 * (A.card : ℝ) := by positivity
      rw [div_lt_iff₀ hden_pos] at hq_weight
      nlinarith
    have : (1 / 2 : ℝ) < L ^ S.card * q ^ S.card :=
      hquarter_lt.trans_le hmul_ge
    exact not_lt_of_ge hmul_lt.le this
  exact ⟨S, hSA, by simpa [L] using hscale_lt⟩

/-- Under the sparse hard-core assumptions and a large enough constant, the
generator family must have cardinality larger than the scale `C log m`. -/
lemma scale_lt_card_of_sparse
    {α : Type*} [DecidableEq α] {CKK q : ℝ}
    {X : Finset α} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK) (hq0 : 0 < q)
    (hEmptyA : (∅ : Finset α) ∉ A)
    (hNoHeavy :
      ∀ S ∈ A,
        (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
            S.card < 1 / 2)
    (hNotSmall : ¬ pSmall X (upClosureIn X A) q) :
    CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
  rcases exists_generator_scale_pow_lt_card_of_sparse hCKK_pos hq0
      hNoHeavy hNotSmall with ⟨S, hSA, hscale_pow_lt⟩
  let L : ℝ := CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    exact_mod_cast hm_ge_two_nat
  have hlog2_le : Real.log 2 ≤
      Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm_ge_two
  have hL_ge_two : (2 : ℝ) ≤ L := by
    have hmul := mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
    have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
      have hmul2 := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
      have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
        field_simp [hlog2_pos.ne']
      linarith
    dsimp [L]
    linarith
  have hL_nonneg : 0 ≤ L := by linarith
  have hL_ge_one : (1 : ℝ) ≤ L := by linarith
  have hS_nonempty : S.Nonempty := by
    by_contra hS_empty
    have hS_eq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS_empty
    exact hEmptyA (by simpa [hS_eq] using hSA)
  have hL_le_pow : L ≤ L ^ S.card := by
    cases hcard : S.card with
    | zero =>
        have hbad : S.card ≠ 0 := hS_nonempty.card_pos.ne'
        exact False.elim (hbad hcard)
    | succ n =>
        have hpow_ge_one : (1 : ℝ) ≤ L ^ n := one_le_pow₀ hL_ge_one
        rw [pow_succ]
        nlinarith
  exact lt_of_le_of_lt hL_le_pow (by simpa [L] using hscale_pow_lt)

/-- With a large Park--Pham constant, the scale term is always at least `2`. -/
lemma two_le_scale_of_large_constant
    {α : Type*} {CKK : ℝ} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK) :
    (2 : ℝ) ≤
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
  have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
  have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
    exact_mod_cast hm_ge_two_nat
  have hlog2_le :
      Real.log 2 ≤ Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm_ge_two
  have hmono :
      CKK * Real.log 2 ≤
        CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlog2_le hCKK_pos.le
  have htwo_le_CKK_log2 : (2 : ℝ) ≤ CKK * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hCKK_large hlog2_pos.le
    have hdiv_mul : (2 / Real.log 2 : ℝ) * Real.log 2 = 2 := by
      field_simp [hlog2_pos.ne']
    linarith
  exact htwo_le_CKK_log2.trans hmono

/-- The explicit scale condition forces the generator family to have more than
two members. -/
lemma two_lt_card_of_scale_lt_card
    {α : Type*} {CKK : ℝ} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hscale :
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ)) :
    2 < A.card := by
  have htwo_lt_card_real : (2 : ℝ) < (A.card : ℝ) :=
    lt_of_le_of_lt (two_le_scale_of_large_constant (A := A) hCKK_large) hscale
  exact_mod_cast htwo_lt_card_real

/-- A proof of the scale-only hard core gives the scaled hard core. -/
theorem strictAntichainScaledHardCoreOn_of_scaleOnlyHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainScaleOnlyHardCoreOn CKK α) :
    StrictAntichainScaledHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti _hA_nonempty _hcard_large hEmptyA
    hscale_lt hthreshold_lt_one hpow_lt hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
    hthreshold_lt_one hpow_lt hNoHeavy hNotSmall

/-- A proof of the reduced hard core gives the scale-only hard core. -/
theorem strictAntichainScaleOnlyHardCoreOn_of_reducedHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCore : StrictAntichainReducedHardCoreOn CKK α) :
    StrictAntichainScaleOnlyHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt hthreshold_lt_one
    _hpow_lt hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hEmptyA hscale_lt
    hthreshold_lt_one hNoHeavy hNotSmall

/-- In the reduced scale-only setting, the global low-density condition follows
from the per-generator smallness condition. -/
lemma global_pow_lt_half_of_noHeavy
    {α : Type*} {CKK q : ℝ} {A : Finset (Finset α)}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK) (hq0 : 0 < q)
    (hscale :
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ))
    (hthreshold :
      CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < 1)
    (hNoHeavy :
      ∀ S ∈ A,
        (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
            S.card < 1 / 2) :
    (CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)) ^
        max 2 (A.sup Finset.card) < 1 / 2 := by
  have hcard_large : 2 < A.card :=
    two_lt_card_of_scale_lt_card hCKK_large hscale
  have hA_nonempty : A.Nonempty := by
    exact Finset.card_pos.mp (Nat.zero_lt_of_lt hcard_large)
  rcases hA_nonempty with ⟨S, hSA⟩
  let p : ℝ := CKK * q * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ)
  have hp0 : 0 ≤ p := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCKK_pos : 0 < CKK := lt_of_lt_of_le (by positivity) hCKK_large
    have hm_ge_two_nat : 2 ≤ max 2 (A.sup Finset.card) := le_max_left _ _
    have hm_ge_two : (2 : ℝ) ≤ ((max 2 (A.sup Finset.card) : ℕ) : ℝ) := by
      exact_mod_cast hm_ge_two_nat
    have hlog_nonneg :
        0 ≤ Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) :=
      (Real.log_pos (lt_of_lt_of_le (by norm_num) hm_ge_two)).le
    dsimp [p]
    exact mul_nonneg (mul_nonneg hCKK_pos.le hq0.le) hlog_nonneg
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact hthreshold.le
  have hS_le : S.card ≤ max 2 (A.sup Finset.card) := by
    exact (Finset.le_sup (s := A) (f := Finset.card) hSA).trans (le_max_right _ _)
  have hpow_le : p ^ max 2 (A.sup Finset.card) ≤ p ^ S.card :=
    pow_le_pow_of_le_one hp0 hp1 hS_le
  have hS_small : p ^ S.card < 1 / 2 := by
    simpa [p] using hNoHeavy S hSA
  exact hpow_le.trans_lt hS_small

/-- It is enough to prove the sparse antichain hard core after explicitly
assuming the scale condition that follows from sparse non-smallness. -/
theorem strictAntichainSparseHardCoreOn_of_scaledHardCoreOn
    {α : Type*} [DecidableEq α] {CKK : ℝ}
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : StrictAntichainScaledHardCoreOn CKK α) :
    StrictAntichainSparseHardCoreOn CKK α := by
  intro X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hthreshold_lt_one hpow_lt hNoHeavy hNotSmall
  have hscale_lt :
      CKK * Real.log ((max 2 (A.sup Finset.card) : ℕ) : ℝ) < (A.card : ℝ) :=
    scale_lt_card_of_sparse hCKK_large hq0 hEmptyA hNoHeavy hNotSmall
  exact hCore X A q hq0 hq1 hAX hAnti hA_nonempty hcard_large hEmptyA
    hscale_lt hthreshold_lt_one hpow_lt hNoHeavy hNotSmall

/-- A uniform proof of the scaled antichain hard core gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_scaled_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α], StrictAntichainScaledHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_sparse_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainSparseHardCoreOn_of_scaledHardCoreOn
      hCKK_large (hCore (α := α)))

/-- A uniform proof of the scale-only antichain hard core gives the public
strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_scale_only_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainScaleOnlyHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_scaled_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainScaledHardCoreOn_of_scaleOnlyHardCoreOn
      (hCore (α := α)))

/-- A uniform proof of the reduced antichain hard core gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCore : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedHardCoreOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_scale_only_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainScaleOnlyHardCoreOn_of_reducedHardCoreOn
      (hCore (α := α)))

/-- A uniform Park--Vondrak certificate for the reduced hard core gives the
public strict Park--Pham package.  This is the current clean finite target for
the threshold theorem. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_certificate
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCert : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVCertificateOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainReducedHardCoreOn_of_pvCertificateOn
      (hCert (α := α)))

/-- A uniform quarter-budget Park--Vondrak certificate also gives the public
strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hCert : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVQuarterCertificateOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core
    hCKK_pos hCKK_large
    (fun {α} _ => strictAntichainReducedHardCoreOn_of_pvQuarterCertificateOn
      (hCert (α := α)))

/-- A uniform coarse numeric Park--Vondrak stage scheme gives the public strict
Park--Pham package.  This is a sufficient reduction, mainly useful as a
bookkeeping bridge; the viable final parameter proof should use the refined
stage-dependent cardinality budget. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_numeric_scheme
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hScheme : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVNumericSchemeOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate
    hCKK_pos hCKK_large
    (fun {α} _ =>
      strictAntichainReducedPVQuarterCertificateOn_of_numericSchemeOn
        (hScheme (α := α)))

/-- A uniform refined snoc-budget Park--Vondrak stage scheme gives the public
strict Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_snoc_budget_scheme
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hScheme : ∀ {α : Type u} [DecidableEq α],
      StrictAntichainReducedPVSnocBudgetSchemeOn CKK α) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate
    hCKK_pos hCKK_large
    (fun {α} _ =>
      strictAntichainReducedPVQuarterCertificateOn_of_snocBudgetSchemeOn
        (hScheme (α := α)))

/-- A pure scalar Park--Vondrak parameter scheme gives the public strict
Park--Pham package. -/
theorem park_pham_threshold_not_small_lt_exists_of_pv_scalar_parameter_scheme
    {CKK : ℝ} (hCKK_pos : 0 < CKK)
    (hCKK_large : (2 / Real.log 2 : ℝ) ≤ CKK)
    (hScalar : PVSnocScalarParameterScheme CKK) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_pv_snoc_budget_scheme
    hCKK_pos hCKK_large
    (fun {α} _ =>
      strictAntichainReducedPVSnocBudgetSchemeOn_of_scalarParameterScheme
        (α := α) hScalar)

/-- Existential scalar-parameter form of the Park--Vondrak target.  The concrete
power-of-two scalar schedule below supplies this package. -/
theorem park_pham_threshold_not_small_lt_exists_of_exists_pv_scalar_parameter_scheme
    (hScalar :
      ∃ CKK : ℝ, 0 < CKK ∧ (2 / Real.log 2 : ℝ) ≤ CKK ∧
        PVSnocScalarParameterScheme CKK) :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type u} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases hScalar with ⟨CKK, hCKK_pos, hCKK_large, hScheme⟩
  exact park_pham_threshold_not_small_lt_exists_of_pv_scalar_parameter_scheme
    hCKK_pos hCKK_large hScheme

/-- **Park–Pham expectation-threshold theorem from non-smallness**
(Kahn–Kalai conjecture, arXiv:2203.17207, proved by J. Park and
H. T. Pham, 2022).

If an increasing family `U` is not `q`-small, then the product measure at
density exactly `C_KK · q · log(ℓ(U))` is at least `1/2`, provided this
density is strictly below `1`.  The family is explicitly required to live on the
finite ground set `X`, matching the Boolean-family statement of
Park--Pham/Kahn--Kalai.

This is the single remaining upstream-Mathlib target for the Park–Pham layer.
All other local monotonicity and finite bookkeeping is proved in this repo. -/
theorem park_pham_threshold_not_small_lt_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  exact park_pham_threshold_not_small_lt_exists_of_exists_pv_scalar_parameter_scheme
    exists_pv_snoc_scalar_parameter_scheme

/-- The strict Park--Pham constant can be enlarged to dominate
`2 / log 2`.  This is often convenient for excluding impossible endpoint
cases; enlarging the density only increases product measure for increasing
families. -/
theorem park_pham_threshold_not_small_lt_large_exists :
    ∃ CKK : ℝ, 0 < CKK ∧ (2 / Real.log 2 : ℝ) ≤ CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases park_pham_threshold_not_small_lt_exists with ⟨C0, hC0_pos, hThresholdLt⟩
  let CKK : ℝ := max C0 (2 / Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK :=
    lt_of_lt_of_le hC0_pos (le_max_left _ _)
  have hCKK_ge_C0 : C0 ≤ CKK := le_max_left _ _
  have hCKK_ge_log2 : (2 / Real.log 2 : ℝ) ≤ CKK := le_max_right _ _
  refine ⟨CKK, hCKK_pos, hCKK_ge_log2, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hlog2_le : Real.log 2 ≤ Real.log (ell X U) :=
    Real.log_le_log (by norm_num) hell_ge_two
  have hlog_nonneg : 0 ≤ Real.log (ell X U) :=
    le_trans hlog2_pos.le hlog2_le
  have hscale_nonneg : 0 ≤ q * Real.log (ell X U) :=
    mul_nonneg hq0.le hlog_nonneg
  have hsmall_le_large :
      C0 * q * Real.log (ell X U) ≤
        CKK * q * Real.log (ell X U) := by
    calc
      C0 * q * Real.log (ell X U) = C0 * (q * Real.log (ell X U)) := by ring
      _ ≤ CKK * (q * Real.log (ell X U)) :=
        mul_le_mul_of_nonneg_right hCKK_ge_C0 hscale_nonneg
      _ = CKK * q * Real.log (ell X U) := by ring
  have hsmall_lt_one : C0 * q * Real.log (ell X U) < 1 :=
    lt_of_le_of_lt hsmall_le_large hthreshold_lt_one
  have hAtSmall :
      muP X U (C0 * q * Real.log (ell X U)) ≥ 1 / 2 :=
    hThresholdLt X U q hq0 hq1 hsmall_lt_one hUX hIncr hNotSmall
  have hsmall_nonneg : 0 ≤ C0 * q * Real.log (ell X U) := by
    positivity
  have hmono :
      muP X U (C0 * q * Real.log (ell X U)) ≤
        muP X U (CKK * q * Real.log (ell X U)) :=
    muP_mono_density hIncr hsmall_nonneg hsmall_le_large hthreshold_lt_one.le
  exact hAtSmall.trans hmono

/-- **Park–Pham expectation-threshold theorem from non-smallness**, with the
closed endpoint `C_KK · q · log(ℓ(U)) ≤ 1`.

The only deep input needed here is the strict case
`park_pham_threshold_not_small_lt_exists`.  If the threshold density is exactly
`1`, non-smallness makes `U` nonempty; since `U` is increasing on `X`, it
contains `X`, and its product measure at density `1` is exactly `1`. -/
theorem park_pham_threshold_not_small_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases park_pham_threshold_not_small_lt_exists with ⟨CKK, hCKK_pos, hThresholdLt⟩
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hNotSmall
  by_cases hthreshold_lt_one : CKK * q * Real.log (ell X U) < 1
  · exact hThresholdLt X U q hq0 hq1 hthreshold_lt_one hUX hIncr hNotSmall
  · have hthreshold_eq_one : CKK * q * Real.log (ell X U) = 1 :=
      le_antisymm hthreshold_le_one (le_of_not_gt hthreshold_lt_one)
    have hU_nonempty : U.Nonempty := nonempty_of_not_pSmall hNotSmall
    have hmu_one : muP X U (1 : ℝ) = 1 :=
      muP_one_of_nonempty_increasing hUX hIncr hU_nonempty
    rw [hthreshold_eq_one, hmu_one]
    norm_num

/-- **Park–Pham expectation-threshold theorem at the exact threshold**, in the
`qSmallUpper` form used downstream.  This follows from the primitive
non-smallness form by applying it at `2q` when `q ≤ 1/2`, and at `1` when
`q > 1/2`; the constant is enlarged by an absolute factor. -/
theorem park_pham_threshold_at_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  rcases park_pham_threshold_not_small_exists with ⟨C0, hC0_pos, hThresholdNS⟩
  let CKK : ℝ := max (2 * C0) (2 / Real.log 2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCKK_pos : 0 < CKK := by
    exact lt_of_lt_of_le (mul_pos (by norm_num) hC0_pos) (le_max_left _ _)
  have hCKK_ge_2C0 : 2 * C0 ≤ CKK := le_max_left _ _
  have hCKK_ge_2_log2 : 2 / Real.log 2 ≤ CKK := le_max_right _ _
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q hq0 hq1 hthreshold_le_one hUX hIncr hqSmall
  have hell_ge_two_nat : 2 ≤ ell X U := two_le_ell X U
  have hell_ge_two : (2 : ℝ) ≤ (ell X U : ℝ) := by exact_mod_cast hell_ge_two_nat
  have hell_pos : 0 < (ell X U : ℝ) := by positivity
  have hlog2_le : Real.log 2 ≤ Real.log (ell X U) :=
    Real.log_le_log (by norm_num) hell_ge_two
  have hlog_nonneg : 0 ≤ Real.log (ell X U) :=
    le_trans hlog2_pos.le hlog2_le
  have htarget_nonneg : 0 ≤ CKK * q * Real.log (ell X U) := by positivity
  by_cases hq_half : q ≤ (1 / 2 : ℝ)
  · let q' : ℝ := 2 * q
    have hq'_pos : 0 < q' := by dsimp [q']; positivity
    have hq'_le_one : q' ≤ 1 := by dsimp [q']; linarith
    have hq_lt_q' : q < q' := by dsimp [q']; linarith
    have hnotSmall : ¬ pSmall X U q' :=
      hqSmall q' hq_lt_q' hq'_le_one
    have hsmall_threshold_le :
        C0 * q' * Real.log (ell X U) ≤ 1 := by
      have hC0q_le : C0 * q' ≤ CKK * q := by
        dsimp [q']
        nlinarith [hCKK_ge_2C0, hq0.le]
      have hle :
          C0 * q' * Real.log (ell X U) ≤
            CKK * q * Real.log (ell X U) := by
        exact mul_le_mul_of_nonneg_right hC0q_le hlog_nonneg
      exact hle.trans hthreshold_le_one
    have hAtSmall :
        muP X U (C0 * q' * Real.log (ell X U)) ≥ 1 / 2 :=
      hThresholdNS X U q' hq'_pos hq'_le_one hsmall_threshold_le hUX hIncr hnotSmall
    have hsmall_nonneg :
        0 ≤ C0 * q' * Real.log (ell X U) := by positivity
    have hsmall_le_target :
        C0 * q' * Real.log (ell X U) ≤
          CKK * q * Real.log (ell X U) := by
      have hC0q_le : C0 * q' ≤ CKK * q := by
        dsimp [q']
        nlinarith [hCKK_ge_2C0, hq0.le]
      exact mul_le_mul_of_nonneg_right hC0q_le hlog_nonneg
    have hmono :
        muP X U (C0 * q' * Real.log (ell X U)) ≤
          muP X U (CKK * q * Real.log (ell X U)) :=
      muP_mono_density hIncr hsmall_nonneg hsmall_le_target hthreshold_le_one
    exact hAtSmall.trans hmono
  · have hq_gt_half : (1 / 2 : ℝ) < q := lt_of_not_ge hq_half
    have hq_lt_one : q < 1 :=
      q_lt_one_of_large_constant_threshold_le_one hCKK_ge_2_log2 hq1 hthreshold_le_one
    have hnotSmall : ¬ pSmall X U (1 : ℝ) :=
      hqSmall 1 hq_lt_one le_rfl
    have hC0_log_le_target :
        C0 * 1 * Real.log (ell X U) ≤
          CKK * q * Real.log (ell X U) := by
      have hC0_le_CKKq : C0 * 1 ≤ CKK * q := by
        nlinarith [hCKK_ge_2C0, hq_gt_half, hC0_pos.le]
      exact mul_le_mul_of_nonneg_right hC0_le_CKKq hlog_nonneg
    have hsmall_threshold_le :
        C0 * 1 * Real.log (ell X U) ≤ 1 :=
      hC0_log_le_target.trans hthreshold_le_one
    have hAtSmall :
        muP X U (C0 * 1 * Real.log (ell X U)) ≥ 1 / 2 :=
      hThresholdNS X U 1 (by norm_num) le_rfl hsmall_threshold_le hUX hIncr hnotSmall
    have hsmall_nonneg :
        0 ≤ C0 * 1 * Real.log (ell X U) := by positivity
    have hmono :
        muP X U (C0 * 1 * Real.log (ell X U)) ≤
          muP X U (CKK * q * Real.log (ell X U)) :=
      muP_mono_density hIncr hsmall_nonneg hC0_log_le_target hthreshold_le_one
    exact hAtSmall.trans hmono

/-- **Park–Pham expectation-threshold theorem** (Kahn–Kalai conjecture,
arXiv:2203.17207, proved by J. Park and H. T. Pham, 2022).

If `q` upper-bounds the expectation threshold of an increasing family
`U`, then the product measure at any density `p` at or above
`C_KK · q · log(ℓ(U))` is at least `1/2`.

This is the downstream-friendly "any `p` at or above the threshold" form,
derived from `park_pham_threshold_at_exists` and `muP_mono_density`. -/
theorem park_pham_threshold_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2 := by
  rcases park_pham_threshold_at_exists with ⟨CKK, hCKK_pos, hThresholdAt⟩
  refine ⟨CKK, hCKK_pos, ?_⟩
  intro α _ X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_ell X U))
  have hlog_nonneg : 0 ≤ Real.log (ell X U) := Real.log_nonneg hell_ge_one
  have hthreshold_nonneg :
      0 ≤ CKK * q * Real.log (ell X U) := by positivity
  have hthreshold_le_one :
      CKK * q * Real.log (ell X U) ≤ 1 := hDensity.trans hp1
  have hAt :
      muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 :=
    hThresholdAt X U q hq0 hq1 hthreshold_le_one hUX hIncr hSmall
  have hmono :
      muP X U (CKK * q * Real.log (ell X U)) ≤ muP X U p :=
    muP_mono_density hIncr hthreshold_nonneg hDensity hp1
  exact hAt.trans hmono

end ParkPham
end Erdos202
