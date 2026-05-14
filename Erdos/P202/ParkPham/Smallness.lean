/-
Erdős Problem 202 — Park–Pham layer, Stage 3.

The `p`-small predicate underlying the Kahn–Kalai expectation threshold:
a family `U` is `p`-small if some "cover" `G` (a finite family whose
upper closure contains `U`) has total `p`-weight at most `1/2`.

`qSmallUpper X U q` asserts that `U` is NOT `p`-small for any `p > q`,
i.e. the threshold lies in `[0, q]`. This is the form consumed by the
Park–Pham theorem in `Threshold.lean`.
-/

import Mathlib
import Erdos.P202.ParkPham.BooleanFamilies
import Erdos.P202.ParkPham.ProductMeasure

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- `G` covers `U` inside `X`: every member of `U` contains some member of
`G`. -/
def CoversIn (_X : Finset α) (G U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∃ T ∈ G, T ⊆ S

/-- The `p`-weight of a cover family.  This is the finite quantity minimized
in the expectation-threshold cost. -/
def coverWeight (G : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ T ∈ G, p ^ T.card

/-- A family `U` is `p`-small inside `X` if there is a cover `G` with
total weight `∑ p^|T|` at most `1/2`. -/
def pSmall (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  ∃ G : Finset (Finset α),
    CoversIn X G U ∧ (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)

/-- `qSmallUpper X U q`: `U` is not `p`-small for any strictly larger `p`. -/
def qSmallUpper (X : Finset α) (U : Finset (Finset α)) (q : ℝ) : Prop :=
  ∀ p : ℝ, q < p → p ≤ 1 → ¬ pSmall X U p

omit [DecidableEq α] in
/-- Direct eliminator for `qSmallUpper`. -/
lemma not_pSmall_of_qSmallUpper {X : Finset α} {U : Finset (Finset α)}
    {q p : ℝ} (hSmall : qSmallUpper X U q) (hqp : q < p) (hp1 : p ≤ 1) :
    ¬ pSmall X U p :=
  hSmall p hqp hp1

omit [DecidableEq α] in
/-- If one finds a `p`-small witness above `q`, then `q` is not an upper bound
for the expectation threshold. -/
lemma not_qSmallUpper_of_pSmall {X : Finset α} {U : Finset (Finset α)}
    {q p : ℝ} (hqp : q < p) (hp1 : p ≤ 1) (hSmall : pSmall X U p) :
    ¬ qSmallUpper X U q := by
  intro hq
  exact hq p hqp hp1 hSmall

omit [DecidableEq α] in
/-- `qSmallUpper` is monotone in the threshold parameter. -/
lemma qSmallUpper_mono_q {X : Finset α} {U : Finset (Finset α)}
    {q₀ q₁ : ℝ} (hqq : q₀ ≤ q₁)
    (hSmall : qSmallUpper X U q₀) :
    qSmallUpper X U q₁ := by
  intro p hq₁p hp1
  exact hSmall p (lt_of_le_of_lt hqq hq₁p) hp1

omit [DecidableEq α] in
/-- The value `q = 1` is always an upper bound in the `qSmallUpper` sense. -/
lemma qSmallUpper_one (X : Finset α) (U : Finset (Finset α)) :
    qSmallUpper X U (1 : ℝ) := by
  intro p hp hp1 _
  linarith

omit [DecidableEq α] in
/-- The empty family is `p`-small for every density. -/
lemma pSmall_empty (X : Finset α) (p : ℝ) :
    pSmall X (∅ : Finset (Finset α)) p := by
  refine ⟨∅, ?_, ?_⟩
  · intro S hS
    simp at hS
  · simp

omit [DecidableEq α] in
/-- A non-small family must be nonempty. -/
lemma nonempty_of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ} (h : ¬ pSmall X U p) :
    U.Nonempty := by
  by_contra hU
  have hUeq : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
  exact h (by simpa [hUeq] using pSmall_empty X p)

omit [DecidableEq α] in
/-- At density `1`, the only `p`-small family is the empty family. -/
lemma pSmall_one_iff_empty (X : Finset α) (U : Finset (Finset α)) :
    pSmall X U (1 : ℝ) ↔ U = ∅ := by
  constructor
  · rintro ⟨G, hCover, hsum⟩
    have hGsum : ((G.card : ℕ) : ℝ) ≤ 1 / 2 := by
      simpa using hsum
    have hG_empty : G = ∅ := by
      by_contra hGne
      have hG_nonempty : G.Nonempty := Finset.nonempty_iff_ne_empty.mpr hGne
      have hge : (1 : ℝ) ≤ (G.card : ℝ) := by
        exact_mod_cast (Finset.one_le_card.mpr hG_nonempty)
      linarith
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    rcases hCover S hS with ⟨T, hTG, _⟩
    simp [hG_empty] at hTG
  · intro hU
    subst hU
    exact pSmall_empty X 1

omit [DecidableEq α] in
/-- Non-smallness at density `1` is exactly nonemptiness. -/
lemma not_pSmall_one_iff_nonempty (X : Finset α) (U : Finset (Finset α)) :
    ¬ pSmall X U (1 : ℝ) ↔ U.Nonempty := by
  constructor
  · intro h
    exact nonempty_of_not_pSmall h
  · intro hU hSmall
    exact hU.ne_empty (pSmall_one_iff_empty X U |>.mp hSmall)

omit [DecidableEq α] in
/-- At density `0`, a family is `p`-small exactly when it does not contain
the empty set. -/
lemma pSmall_zero_iff_empty_not_mem (X : Finset α) (U : Finset (Finset α)) :
    pSmall X U (0 : ℝ) ↔ (∅ : Finset α) ∉ U := by
  constructor
  · rintro ⟨G, hCover, hsum⟩ hEmptyU
    rcases hCover ∅ hEmptyU with ⟨T, hTG, hTsub⟩
    have hT_empty : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hxT
      simpa using hTsub hxT
    have hsingle :
        (0 : ℝ) ^ T.card ≤ ∑ S ∈ G, (0 : ℝ) ^ S.card :=
      Finset.single_le_sum
        (s := G) (f := fun S : Finset α => (0 : ℝ) ^ S.card)
        (fun S _ => by positivity) hTG
    have hterm : (0 : ℝ) ^ T.card = 1 := by
      subst hT_empty
      simp
    linarith
  · intro hEmpty
    refine ⟨U, ?_, ?_⟩
    · intro S hS
      exact ⟨S, hS, subset_refl S⟩
    · have hsum_zero : (∑ T ∈ U, (0 : ℝ) ^ T.card) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro T hTU
        have hT_ne : T ≠ ∅ := by
          intro hT_empty
          exact hEmpty (by simpa [hT_empty] using hTU)
        exact by
          have hT_nonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT_ne
          simp [hT_nonempty.card_pos.ne']
      rw [hsum_zero]
      norm_num

omit [DecidableEq α] in
/-- Non-smallness at density `0` is exactly membership of the empty set. -/
lemma not_pSmall_zero_iff_empty_mem (X : Finset α) (U : Finset (Finset α)) :
    ¬ pSmall X U (0 : ℝ) ↔ (∅ : Finset α) ∈ U := by
  rw [pSmall_zero_iff_empty_not_mem]
  exact not_not

omit [DecidableEq α] in
/-- If the family contains `∅`, it is not `p`-small at any nonnegative
density. -/
lemma not_pSmall_of_empty_mem {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ} (hp0 : 0 ≤ p) (hEmpty : (∅ : Finset α) ∈ U) :
    ¬ pSmall X U p := by
  rintro ⟨G, hCover, hsum⟩
  rcases hCover ∅ hEmpty with ⟨T, hTG, hTsub⟩
  have hT_empty : T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hxT
    simpa using hTsub hxT
  have hsingle :
      p ^ T.card ≤ ∑ S ∈ G, p ^ S.card :=
    Finset.single_le_sum
      (s := G) (f := fun S : Finset α => p ^ S.card)
      (fun S _ => pow_nonneg hp0 S.card) hTG
  have hterm : p ^ T.card = 1 := by
    subst hT_empty
    simp
  linarith

omit [DecidableEq α] in
/-- If the family contains `∅`, then every nonnegative `q ≤ 1` is an upper
bound in the `qSmallUpper` sense. -/
lemma qSmallUpper_of_empty_mem {X : Finset α} {U : Finset (Finset α)}
    {q : ℝ} (hq0 : 0 ≤ q) (hEmpty : (∅ : Finset α) ∈ U) :
    qSmallUpper X U q := by
  intro p hqp _hp1
  exact not_pSmall_of_empty_mem (hq0.trans hqp.le) hEmpty

omit [DecidableEq α] in
/-- If `∅ ∉ U`, then `U` is `p`-small at some positive density.  The cover is
`U` itself, and the density is chosen small enough that
`∑_{T∈U} p^|T| ≤ |U|p ≤ 1/2`. -/
lemma exists_pos_pSmall_of_empty_not_mem
    (X : Finset α) (U : Finset (Finset α))
    (hEmpty : (∅ : Finset α) ∉ U) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ pSmall X U p := by
  classical
  let p : ℝ := 1 / (2 * ((U.card : ℝ) + 1))
  have hden_pos : 0 < 2 * ((U.card : ℝ) + 1) := by positivity
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hp_nonneg : 0 ≤ p := hp_pos.le
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    rw [div_le_one hden_pos]
    have hcard_nonneg : 0 ≤ (U.card : ℝ) := by positivity
    nlinarith
  refine ⟨p, hp_pos, hp_le_one, ?_⟩
  refine ⟨U, ?_, ?_⟩
  · intro S hS
    exact ⟨S, hS, subset_refl S⟩
  · have hterm : ∀ T ∈ U, p ^ T.card ≤ p := by
      intro T hT
      have hT_nonempty : T.Nonempty := by
        by_contra hT_empty
        exact hEmpty (by
          have hT_eq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT_empty
          simpa [hT_eq] using hT)
      have hcard : 1 ≤ T.card := Finset.one_le_card.mpr hT_nonempty
      calc
        p ^ T.card ≤ p ^ 1 := pow_le_pow_of_le_one hp_nonneg hp_le_one hcard
        _ = p := by simp
    calc
      (∑ T ∈ U, p ^ T.card) ≤ ∑ T ∈ U, p :=
        Finset.sum_le_sum hterm
      _ = (U.card : ℝ) * p := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 / 2 := by
        have hcard_nonneg : 0 ≤ (U.card : ℝ) := by positivity
        dsimp [p]
        field_simp [hden_pos.ne']
        nlinarith

omit [DecidableEq α] in
/-- At the endpoint `q = 0`, `qSmallUpper` is exactly membership of the empty
set. -/
lemma qSmallUpper_zero_iff_empty_mem (X : Finset α) (U : Finset (Finset α)) :
    qSmallUpper X U (0 : ℝ) ↔ (∅ : Finset α) ∈ U := by
  constructor
  · intro hq
    by_contra hEmpty
    rcases exists_pos_pSmall_of_empty_not_mem X U hEmpty with ⟨p, hp0, hp1, hpSmall⟩
    exact hq p hp0 hp1 hpSmall
  · intro hEmpty
    exact qSmallUpper_of_empty_mem le_rfl hEmpty

omit [DecidableEq α] in
/-- Enlarging the cover preserves the covering property. -/
lemma CoversIn.mono_cover {X : Finset α} {G H U : Finset (Finset α)}
    (hGH : G ⊆ H) (hCover : CoversIn X G U) :
    CoversIn X H U := by
  intro S hS
  rcases hCover S hS with ⟨T, hTG, hTS⟩
  exact ⟨T, hGH hTG, hTS⟩

omit [DecidableEq α] in
/-- A cover of a larger family covers every subfamily. -/
lemma CoversIn.mono_family {X : Finset α} {G U V : Finset (Finset α)}
    (hVU : V ⊆ U) (hCover : CoversIn X G U) :
    CoversIn X G V := by
  intro S hS
  exact hCover S (hVU hS)

/-- The union of two covers covers the union of the target families. -/
lemma CoversIn.union {X : Finset α} {G H U V : Finset (Finset α)}
    (hG : CoversIn X G U) (hH : CoversIn X H V) :
    CoversIn X (G ∪ H) (U ∪ V) := by
  intro S hS
  rcases Finset.mem_union.mp hS with hSU | hSV
  · rcases hG S hSU with ⟨T, hTG, hTS⟩
    exact ⟨T, Finset.mem_union.mpr (Or.inl hTG), hTS⟩
  · rcases hH S hSV with ⟨T, hTH, hTS⟩
    exact ⟨T, Finset.mem_union.mpr (Or.inr hTH), hTS⟩

/-- Covering is the same as containment in the upper closure, once the target
family is known to live inside the ground universe. -/
lemma CoversIn_iff_subset_upClosureIn {X : Finset α} {G U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    CoversIn X G U ↔ U ⊆ upClosureIn X G := by
  constructor
  · intro hCover S hS
    rcases hCover S hS with ⟨T, hTG, hTS⟩
    exact mem_upClosureIn.mpr ⟨hUX S hS, T, hTG, hTS⟩
  · intro hsub S hS
    rcases mem_upClosureIn.mp (hsub hS) with ⟨_, T, hTG, hTS⟩
    exact ⟨T, hTG, hTS⟩

/-- Covering a family is equivalent to covering its upper closure, provided the
original family lives in the ground universe. -/
lemma CoversIn_upClosureIn_iff {X : Finset α} {G U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    CoversIn X G (upClosureIn X U) ↔ CoversIn X G U := by
  constructor
  · intro hCover S hS
    exact hCover S (subset_upClosureIn hUX hS)
  · intro hCover S hS
    rcases mem_upClosureIn.mp hS with ⟨_, T, hTU, hTS⟩
    rcases hCover T hTU with ⟨R, hRG, hRT⟩
    exact ⟨R, hRG, hRT.trans hTS⟩

/-- If the target family lives inside `X`, a cover can be restricted to sets
inside `X` without losing the covering property. -/
lemma CoversIn.filter_subset_ground {X : Finset α} {G U : Finset (Finset α)}
    (hUX : ∀ S ∈ U, S ⊆ X) (hCover : CoversIn X G U) :
    CoversIn X (G.filter fun T => T ⊆ X) U := by
  intro S hS
  rcases hCover S hS with ⟨T, hTG, hTS⟩
  have hTX : T ⊆ X := hTS.trans (hUX S hS)
  exact ⟨T, Finset.mem_filter.mpr ⟨hTG, hTX⟩, hTS⟩

lemma pSmall_upClosureIn_iff {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    pSmall X (upClosureIn X U) p ↔ pSmall X U p := by
  constructor
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, (CoversIn_upClosureIn_iff hUX).mp hCover, hsum⟩
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, (CoversIn_upClosureIn_iff hUX).mpr hCover, hsum⟩

lemma not_pSmall_upClosureIn_iff {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    ¬ pSmall X (upClosureIn X U) p ↔ ¬ pSmall X U p := by
  rw [pSmall_upClosureIn_iff hUX]

lemma qSmallUpper_upClosureIn_iff {X : Finset α} {U : Finset (Finset α)} {q : ℝ}
    (hUX : ∀ S ∈ U, S ⊆ X) :
    qSmallUpper X (upClosureIn X U) q ↔ qSmallUpper X U q := by
  constructor
  · intro hSmall p hqp hp1 hSmallU
    exact hSmall p hqp hp1 ((pSmall_upClosureIn_iff hUX).mpr hSmallU)
  · intro hSmall p hqp hp1 hSmallClosure
    exact hSmall p hqp hp1 ((pSmall_upClosureIn_iff hUX).mp hSmallClosure)

omit [DecidableEq α] in
/-- A single cover with total weight at most `1/2` proves `p`-smallness. -/
lemma pSmall_of_cover_sum_le {X : Finset α} {U G : Finset (Finset α)}
    {p : ℝ} (hCover : CoversIn X G U)
    (hsum : (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)) :
    pSmall X U p :=
  ⟨G, hCover, hsum⟩

/-- Cover weight is subadditive under union, with nonnegative density. -/
lemma coverWeight_union_le {G H : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) :
    coverWeight (G ∪ H) p ≤ coverWeight G p + coverWeight H p := by
  classical
  unfold coverWeight
  let H' : Finset (Finset α) := H \ G
  have hdisj : Disjoint G H' := by
    exact disjoint_sdiff
  have hunion : G ∪ H = G ∪ H' := by
    ext T
    by_cases hTG : T ∈ G <;> simp [H', hTG]
  calc
    (∑ T ∈ G ∪ H, p ^ T.card)
        = ∑ T ∈ G ∪ H', p ^ T.card := by rw [hunion]
    _ = (∑ T ∈ G, p ^ T.card) + ∑ T ∈ H', p ^ T.card := by
      rw [Finset.sum_union hdisj]
    _ ≤ (∑ T ∈ G, p ^ T.card) + ∑ T ∈ H, p ^ T.card := by
      exact add_le_add_right
        (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.sdiff_subset : H' ⊆ H)
        (by intro T _ _; exact pow_nonneg hp0 T.card))
        (∑ T ∈ G, p ^ T.card)

/-- A `pSmall` witness may be chosen with every cover set inside the ground
universe. -/
lemma pSmall.exists_ground_cover
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hUX : ∀ S ∈ U, S ⊆ X) (hSmall : pSmall X U p) :
    ∃ G : Finset (Finset α),
      (∀ T ∈ G, T ⊆ X) ∧
      CoversIn X G U ∧
      (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ) := by
  rcases hSmall with ⟨G, hCover, hsum⟩
  refine ⟨G.filter fun T => T ⊆ X, ?_, ?_, ?_⟩
  · intro T hT
    exact (Finset.mem_filter.mp hT).2
  · exact hCover.filter_subset_ground hUX
  · have hfilter_le :
        (∑ T ∈ G.filter (fun T => T ⊆ X), p ^ T.card) ≤
          ∑ T ∈ G, p ^ T.card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro T _ _; exact pow_nonneg hp0 T.card)
    exact hfilter_le.trans hsum

omit [DecidableEq α] in
/-- Contrapositive form of `pSmall`: if `U` is not `p`-small, every cover has
weight strictly larger than `1/2`. -/
lemma cover_sum_gt_half_of_not_pSmall
    {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) (hCover : CoversIn X G U) :
    (1 / 2 : ℝ) < ∑ T ∈ G, p ^ T.card := by
  exact lt_of_not_ge fun hsum => h (pSmall_of_cover_sum_le hCover hsum)

omit [DecidableEq α] in
/-- Logical normal form for non-smallness. -/
lemma not_pSmall_iff_forall_cover_sum_gt_half
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} :
    ¬ pSmall X U p ↔
      ∀ G : Finset (Finset α), CoversIn X G U →
        (1 / 2 : ℝ) < ∑ T ∈ G, p ^ T.card := by
  constructor
  · intro h G hCover
    exact cover_sum_gt_half_of_not_pSmall h hCover
  · intro h hSmall
    rcases hSmall with ⟨G, hCover, hsum⟩
    exact not_le_of_gt (h G hCover) hsum

/-- Minimal members are a canonical cover of a family. -/
lemma minimalMembers_cover (X : Finset α) (U : Finset (Finset α)) :
    CoversIn X (minimalMembersIn X U) U := by
  intro S hS
  exact exists_minimal_subset hS

/-- A generating family covers its own upper closure. -/
lemma generators_cover_upClosureIn (X : Finset α) (A : Finset (Finset α)) :
    CoversIn X A (upClosureIn X A) := by
  intro S hS
  rcases mem_upClosureIn.mp hS with ⟨_, T, hTA, hTS⟩
  exact ⟨T, hTA, hTS⟩

/-- Covering the minimal members is equivalent to covering the whole family. -/
lemma CoversIn_minimalMembersIn_iff
    {X : Finset α} {G U : Finset (Finset α)} :
    CoversIn X G (minimalMembersIn X U) ↔ CoversIn X G U := by
  constructor
  · intro hCover S hS
    rcases exists_minimal_subset (X := X) hS with ⟨T, hTmin, hTS⟩
    rcases hCover T hTmin with ⟨R, hRG, hRT⟩
    exact ⟨R, hRG, hRT.trans hTS⟩
  · intro hCover
    exact hCover.mono_family minimalMembersIn_subset

/-- `pSmall` can be tested on the minimal members. -/
lemma pSmall_minimalMembersIn_iff
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} :
    pSmall X (minimalMembersIn X U) p ↔ pSmall X U p := by
  constructor
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, CoversIn_minimalMembersIn_iff.mp hCover, hsum⟩
  · rintro ⟨G, hCover, hsum⟩
    exact ⟨G, CoversIn_minimalMembersIn_iff.mpr hCover, hsum⟩

/-- Non-smallness can be tested on minimal members. -/
lemma not_pSmall_minimalMembersIn_iff
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} :
    ¬ pSmall X (minimalMembersIn X U) p ↔ ¬ pSmall X U p := by
  rw [pSmall_minimalMembersIn_iff]

/-- The expectation-threshold upper-bound predicate can be tested on minimal
members. -/
lemma qSmallUpper_minimalMembersIn_iff
    {X : Finset α} {U : Finset (Finset α)} {q : ℝ} :
    qSmallUpper X (minimalMembersIn X U) q ↔ qSmallUpper X U q := by
  constructor
  · intro hSmall p hqp hp1 hSmallU
    exact hSmall p hqp hp1 (pSmall_minimalMembersIn_iff.mpr hSmallU)
  · intro hSmall p hqp hp1 hSmallMin
    exact hSmall p hqp hp1 (pSmall_minimalMembersIn_iff.mp hSmallMin)

/-- If the minimal-member cover has small enough total weight, then the family
is `p`-small. -/
lemma pSmall_of_minimalMembers_sum_le {X : Finset α} {U : Finset (Finset α)}
    {p : ℝ}
    (hsum : (∑ T ∈ minimalMembersIn X U, p ^ T.card) ≤ (1 / 2 : ℝ)) :
    pSmall X U p :=
  pSmall_of_cover_sum_le (minimalMembers_cover X U) hsum

/-- If a family is not `p`-small, then even its canonical minimal-member cover
has weight strictly larger than `1/2`. -/
lemma half_lt_minimalMembers_sum_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) :
    (1 / 2 : ℝ) < ∑ T ∈ minimalMembersIn X U, p ^ T.card := by
  exact lt_of_not_ge fun hle => h (pSmall_of_minimalMembers_sum_le hle)

/-- If an upper closure is not `p`-small, then the generator cover has weight
strictly larger than `1/2`. -/
lemma half_lt_generators_sum_of_not_pSmall_upClosureIn
    {X : Finset α} {A : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X (upClosureIn X A) p) :
    (1 / 2 : ℝ) < ∑ T ∈ A, p ^ T.card := by
  exact cover_sum_gt_half_of_not_pSmall h (generators_cover_upClosureIn X A)

omit [DecidableEq α] in
/-- If a finite weighted sum is larger than `1/2`, then some term is larger
than the average threshold `1 / (2 * card)`. -/
lemma exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum
    {β : Type*} (s : Finset β) (w : β → ℝ)
    (hsum : (1 / 2 : ℝ) < ∑ x ∈ s, w x) :
    ∃ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ)) < w x := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra hs_empty
    have hs_eq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs_empty
    have hbad : (1 / 2 : ℝ) < 0 := by simpa [hs_eq] using hsum
    norm_num at hbad
  by_contra hnone
  have hbound : ∀ x ∈ s, w x ≤ (1 : ℝ) / (2 * (s.card : ℝ)) := by
    intro x hx
    exact le_of_not_gt fun hxgt => hnone ⟨x, hx, hxgt⟩
  have hsum_le :
      (∑ x ∈ s, w x) ≤
        ∑ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ)) :=
    Finset.sum_le_sum hbound
  have hcard_pos_nat : 0 < s.card := hs_nonempty.card_pos
  have hcard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hcard_pos_nat
  have hconst :
      (∑ x ∈ s, (1 : ℝ) / (2 * (s.card : ℝ))) = 1 / 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard_pos.ne']
  linarith

/-- If `U` is not `p`-small, then one minimal member has larger-than-average
`p`-weight in the canonical minimal cover. -/
lemma exists_minimalMember_weight_gt_inv_two_mul_card_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) :
    ∃ T ∈ minimalMembersIn X U,
      (1 : ℝ) / (2 * ((minimalMembersIn X U).card : ℝ)) < p ^ T.card :=
  exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum
    (minimalMembersIn X U) (fun T => p ^ T.card)
    (half_lt_minimalMembers_sum_of_not_pSmall h)

/-- If an upper closure is not `p`-small, then one generator has
larger-than-average `p`-weight in the generator cover. -/
lemma exists_generator_weight_gt_inv_two_mul_card_of_not_pSmall_upClosureIn
    {X : Finset α} {A : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X (upClosureIn X A) p) :
    ∃ T ∈ A, (1 : ℝ) / (2 * (A.card : ℝ)) < p ^ T.card :=
  exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum
    A (fun T => p ^ T.card)
    (half_lt_generators_sum_of_not_pSmall_upClosureIn h)

/-- If every minimal member has size at least `k`, then non-smallness forces
many minimal members at scale `p^k`. -/
lemma half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} {k : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcard_ge : ∀ T ∈ minimalMembersIn X U, k ≤ T.card)
    (h : ¬ pSmall X U p) :
    (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p ^ k := by
  have hsum_gt := half_lt_minimalMembers_sum_of_not_pSmall h
  have hterm : ∀ T ∈ minimalMembersIn X U, p ^ T.card ≤ p ^ k := by
    intro T hT
    exact pow_le_pow_of_le_one hp0 hp1 (hcard_ge T hT)
  have hsum_le :
      (∑ T ∈ minimalMembersIn X U, p ^ T.card) ≤
        ∑ T ∈ minimalMembersIn X U, p ^ k :=
    Finset.sum_le_sum hterm
  have hconst :
      (∑ T ∈ minimalMembersIn X U, p ^ k) =
        ((minimalMembersIn X U).card : ℝ) * p ^ k := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Rearranged form of
`half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge`. -/
lemma inv_two_mul_inv_pow_lt_minimalMembers_card_of_not_pSmall_card_ge
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ} {k : ℕ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hcard_ge : ∀ T ∈ minimalMembersIn X U, k ≤ T.card)
    (h : ¬ pSmall X U p) :
    (1 : ℝ) / (2 * p ^ k) < ((minimalMembersIn X U).card : ℝ) := by
  have hhalf :
      (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p ^ k :=
    half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge
      hp0.le hp1 hcard_ge h
  have hden : 0 < 2 * p ^ k := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

/-- If `U` has neither `∅` nor singleton members, non-smallness forces many
minimal members at scale `p^2`. -/
lemma half_lt_minimalMembers_card_mul_sq_of_not_pSmall_no_singleton
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hEmpty : (∅ : Finset α) ∉ U)
    (hNoSingleton : ∀ a : α, ({a} : Finset α) ∉ U)
    (h : ¬ pSmall X U p) :
    (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p ^ 2 :=
  half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge hp0 hp1
    (fun _T hT =>
      two_le_card_of_mem_minimalMembersIn_of_empty_not_mem_of_no_singleton
        hEmpty hNoSingleton hT)
    h

/-- Rearranged no-singleton minimal-cover lower bound. -/
lemma inv_two_mul_inv_sq_lt_minimalMembers_card_of_not_pSmall_no_singleton
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hEmpty : (∅ : Finset α) ∉ U)
    (hNoSingleton : ∀ a : α, ({a} : Finset α) ∉ U)
    (h : ¬ pSmall X U p) :
    (1 : ℝ) / (2 * p ^ 2) < ((minimalMembersIn X U).card : ℝ) :=
  inv_two_mul_inv_pow_lt_minimalMembers_card_of_not_pSmall_card_ge hp0 hp1
    (fun _T hT =>
      two_le_card_of_mem_minimalMembersIn_of_empty_not_mem_of_no_singleton
        hEmpty hNoSingleton hT)
    h

/-- In the nontrivial case `∅ ∉ U`, non-smallness implies that the number of
minimal members is large at scale `1 / p`. -/
lemma half_lt_minimalMembers_card_mul_of_not_pSmall_empty_not_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hEmpty : (∅ : Finset α) ∉ U) (h : ¬ pSmall X U p) :
    (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p := by
  have hsum_gt := half_lt_minimalMembers_sum_of_not_pSmall h
  have hterm : ∀ T ∈ minimalMembersIn X U, p ^ T.card ≤ p := by
    intro T hT
    have hT_nonempty : T.Nonempty :=
      nonempty_of_mem_minimalMembersIn_of_empty_not_mem hEmpty hT
    have hcard : 1 ≤ T.card := Finset.one_le_card.mpr hT_nonempty
    calc
      p ^ T.card ≤ p ^ 1 := pow_le_pow_of_le_one hp0 hp1 hcard
      _ = p := by simp
  have hsum_le :
      (∑ T ∈ minimalMembersIn X U, p ^ T.card) ≤
        ∑ T ∈ minimalMembersIn X U, p :=
    Finset.sum_le_sum hterm
  have hconst :
      (∑ T ∈ minimalMembersIn X U, p) =
        ((minimalMembersIn X U).card : ℝ) * p := by
    rw [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Rearranged cardinality lower bound from
`half_lt_minimalMembers_card_mul_of_not_pSmall_empty_not_mem`. -/
lemma inv_two_mul_inv_lt_minimalMembers_card_of_not_pSmall_empty_not_mem
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hEmpty : (∅ : Finset α) ∉ U) (h : ¬ pSmall X U p) :
    (1 : ℝ) / (2 * p) < ((minimalMembersIn X U).card : ℝ) := by
  have hhalf :
      (1 / 2 : ℝ) < ((minimalMembersIn X U).card : ℝ) * p :=
    half_lt_minimalMembers_card_mul_of_not_pSmall_empty_not_mem hp0.le hp1 hEmpty h
  have hden : 0 < 2 * p := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

/-- A non-small family has at least one minimal member. -/
lemma minimalMembersIn_nonempty_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) :
    (minimalMembersIn X U).Nonempty :=
  minimalMembersIn_nonempty_of_nonempty (nonempty_of_not_pSmall h)

/-- Existential form of `minimalMembersIn_nonempty_of_not_pSmall`. -/
lemma exists_mem_minimalMembersIn_of_not_pSmall
    {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h : ¬ pSmall X U p) :
    ∃ S, S ∈ minimalMembersIn X U := by
  exact minimalMembersIn_nonempty_of_not_pSmall h

omit [DecidableEq α] in
/-- `pSmall` is monotone in `p`: if `U` is `p`-small and `0 ≤ p₀ ≤ p`,
then `U` is `p₀`-small (the same cover works). -/
lemma pSmall_mono_density {X : Finset α} {U : Finset (Finset α)}
    {p₀ p : ℝ} (h0 : 0 ≤ p₀) (hle : p₀ ≤ p)
    (hSmall : pSmall X U p) : pSmall X U p₀ := by
  classical
  rcases hSmall with ⟨G, hCover, hsum⟩
  refine ⟨G, hCover, le_trans ?_ hsum⟩
  refine Finset.sum_le_sum ?_
  intro T _
  exact pow_le_pow_left₀ h0 hle T.card

omit [DecidableEq α] in
/-- A subfamily of a `p`-small family is `p`-small. -/
lemma pSmall_mono_family {X : Finset α} {U V : Finset (Finset α)}
    {p : ℝ} (hUV : U ⊆ V) (hSmall : pSmall X V p) :
    pSmall X U p := by
  rcases hSmall with ⟨G, hCover, hsum⟩
  exact ⟨G, hCover.mono_family hUV, hsum⟩

omit [DecidableEq α] in
/-- Non-smallness is monotone upward in the family. -/
lemma not_pSmall_mono_family {X : Finset α} {U V : Finset (Finset α)}
    {p : ℝ} (hUV : U ⊆ V) (hNotSmall : ¬ pSmall X U p) :
    ¬ pSmall X V p := by
  intro hSmallV
  exact hNotSmall (pSmall_mono_family hUV hSmallV)

omit [DecidableEq α] in
/-- The `qSmallUpper` predicate is monotone upward in the family. -/
lemma qSmallUpper_mono_family {X : Finset α} {U V : Finset (Finset α)}
    {q : ℝ} (hUV : U ⊆ V) (hSmall : qSmallUpper X U q) :
    qSmallUpper X V q := by
  intro p hqp hp1 hSmallV
  exact hSmall p hqp hp1 (pSmall_mono_family hUV hSmallV)

omit [DecidableEq α] in
/-- If `U` is not `p`-small at `p = p₀`, then it is not `p`-small for any
`p > p₀` with `p ≤ 1`. This is the `qSmallUpper` form. -/
lemma qSmallUpper_of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {p₀ : ℝ} (hp₀_nonneg : 0 ≤ p₀)
    (h : ¬ pSmall X U p₀) :
    qSmallUpper X U p₀ := by
  intro p hgt _ hSmall
  exact h (pSmall_mono_density hp₀_nonneg hgt.le hSmall)

/-- Finite union bound for sums over a `biUnion`, with nonnegative weights. -/
lemma sum_biUnion_le_sum_of_nonneg {ι β : Type*} [DecidableEq β]
    (s : Finset ι) (t : ι → Finset β) (w : β → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ s.biUnion t, w x) ≤ ∑ i ∈ s, ∑ x ∈ t i, w x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    have hunion_le :
        (∑ x ∈ t a ∪ s.biUnion t, w x) ≤
          (∑ x ∈ t a, w x) + ∑ x ∈ s.biUnion t, w x := by
      let A : Finset β := t a
      let B : Finset β := s.biUnion t
      have hdisj : Disjoint A (B \ A) := by
        exact disjoint_sdiff
      have hAB : A ∪ B = A ∪ (B \ A) := by
        ext x
        by_cases hxA : x ∈ A <;> simp [A, B, hxA]
      calc
        (∑ x ∈ A ∪ B, w x)
            = ∑ x ∈ A ∪ (B \ A), w x := by rw [hAB]
        _ = (∑ x ∈ A, w x) + ∑ x ∈ B \ A, w x := by
          rw [Finset.sum_union hdisj]
        _ ≤ (∑ x ∈ A, w x) + ∑ x ∈ B, w x := by
          have hsdiff_le : (∑ x ∈ B \ A, w x) ≤ ∑ x ∈ B, w x :=
            Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.sdiff_subset : B \ A ⊆ B)
            (by intro x _ _; exact hw x)
          exact add_le_add_right hsdiff_le _
    calc
      (∑ x ∈ (insert a s).biUnion t, w x)
          = ∑ x ∈ t a ∪ s.biUnion t, w x := by simp
      _ ≤ (∑ x ∈ t a, w x) + ∑ x ∈ s.biUnion t, w x := hunion_le
      _ ≤ (∑ x ∈ t a, w x) + ∑ i ∈ s, ∑ x ∈ t i, w x := by
        gcongr
      _ = ∑ i ∈ insert a s, ∑ x ∈ t i, w x := by simp [has]

/-- If `G` covers `U`, then the Bernoulli mass of `U` is bounded by the
sum of the singleton-upclosure masses of the cover. -/
lemma muP_le_cover_sum {X : Finset α} {U G : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hCover : CoversIn X G U) :
    muP X U p ≤ ∑ T ∈ G.filter (fun T => T ⊆ X), p ^ T.card := by
  classical
  let Gx : Finset (Finset α) := G.filter fun T => T ⊆ X
  let B : Finset α → Finset (Finset α) := fun T =>
    X.powerset.filter fun S => T ⊆ S
  have hsubset :
      X.powerset.filter (fun S => S ∈ U) ⊆ Gx.biUnion B := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSXpow, hSU⟩
    have hSX : S ⊆ X := Finset.mem_powerset.mp hSXpow
    rcases hCover S hSU with ⟨T, hTG, hTS⟩
    have hTX : T ⊆ X := hTS.trans hSX
    exact Finset.mem_biUnion.mpr
      ⟨T, Finset.mem_filter.mpr ⟨hTG, hTX⟩,
        Finset.mem_filter.mpr ⟨hSXpow, hTS⟩⟩
  have hnonneg : ∀ S, 0 ≤ bernoulliMass X S p := fun _ =>
    bernoulliMass_nonneg h0 h1
  calc
    muP X U p
        = ∑ S ∈ X.powerset.filter (fun S => S ∈ U), bernoulliMass X S p := rfl
    _ ≤ ∑ S ∈ Gx.biUnion B, bernoulliMass X S p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro S _ _; exact hnonneg S)
    _ ≤ ∑ T ∈ Gx, ∑ S ∈ B T, bernoulliMass X S p :=
      sum_biUnion_le_sum_of_nonneg Gx B (fun S => bernoulliMass X S p) hnonneg
    _ = ∑ T ∈ Gx, p ^ T.card := by
      refine Finset.sum_congr rfl ?_
      intro T hTGx
      have hTX : T ⊆ X := (Finset.mem_filter.mp hTGx).2
      have hB_eq : B T = upClosureIn X {T} := by
        rw [upClosureIn_singleton X T hTX]
      have hmuB :
          muP X (B T) p = ∑ S ∈ B T, bernoulliMass X S p := by
        unfold muP
        have hfilter : X.powerset.filter (fun S => S ∈ B T) = B T := by
          ext S
          simp [B]
        rw [hfilter]
      have hsingleB : muP X (B T) p = p ^ T.card := by
        rw [hB_eq]
        exact muP_upClosure_single X T hTX h0 h1
      exact hmuB.symm.trans hsingleB

/-- Union-bound direction of the expectation-threshold setup: a `p`-small
family has Bernoulli measure at most `1/2` at density `p`. -/
theorem muP_le_half_of_pSmall {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hSmall : pSmall X U p) :
    muP X U p ≤ 1 / 2 := by
  classical
  rcases hSmall with ⟨G, hCover, hsum⟩
  have hcover := muP_le_cover_sum h0 h1 hCover
  have hfilter :
      (∑ T ∈ G.filter (fun T => T ⊆ X), p ^ T.card) ≤
        ∑ T ∈ G, p ^ T.card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro T _ _; exact pow_nonneg h0 T.card)
  exact hcover.trans (hfilter.trans hsum)

/-- Contrapositive of `muP_le_half_of_pSmall`: if the Bernoulli measure is
strictly larger than `1/2`, the family is not `p`-small. -/
lemma not_pSmall_of_muP_gt_half {X : Finset α} {U : Finset (Finset α)} {p : ℝ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hmu : 1 / 2 < muP X U p) :
    ¬ pSmall X U p := by
  intro hSmall
  exact not_le_of_gt hmu (muP_le_half_of_pSmall h0 h1 hSmall)

/-- A measure-lower-bound way to establish `qSmallUpper`: if every density
above `q` has Bernoulli measure strictly larger than `1/2`, then no such
density can be `p`-small. -/
lemma qSmallUpper_of_forall_muP_gt_half
    {X : Finset α} {U : Finset (Finset α)} {q : ℝ}
    (hq0 : 0 ≤ q)
    (hmu : ∀ p : ℝ, q < p → p ≤ 1 → 1 / 2 < muP X U p) :
    qSmallUpper X U q := by
  intro p hqp hp1
  have hp0 : 0 ≤ p := hq0.trans hqp.le
  exact not_pSmall_of_muP_gt_half hp0 hp1 (hmu p hqp hp1)

end

end ParkPham
end Erdos202
