/-
Erdős Problem 202 — Park–Pham layer, Stage 6.

Final spread-disjointness theorem via the random-partition argument.

# Strategy

Given a κ-spread, k-uniform, nonempty family A with
`κ ≥ Csp · r · log(ek)`:

1. By `mu_at_partition_density_ge_half`, the Bernoulli measure of
   `upClosureIn X A` at density `1/(2r)` is at least `1/2`.
2. Equivalently (via the random-partition / coloring identification): for
   a uniformly random coloring `c : X → Fin (2r)`, the expected number
   of color classes `c⁻¹(i)` that contain a member of A is at least `r`.
3. Hence there exists a coloring with at least `r` "successful" parts.
4. Pick one member of A inside each successful part. The parts are
   pairwise disjoint, so the chosen members are pairwise disjoint.

The translation from "muP ≥ 1/2" to "∃ r pairwise-disjoint members"
(steps 2-4) is purely finite/discrete bookkeeping with no analytic
content.  This file proves that bookkeeping directly, then combines it
with the named Park--Pham threshold package.
-/

import Mathlib
import Erdos.P202.SpreadDefs
import Erdos.P202.ParkPham.BooleanFamilies
import Erdos.P202.ParkPham.ProductMeasure
import Erdos.P202.ParkPham.Smallness
import Erdos.P202.ParkPham.Threshold
import Erdos.P202.ParkPham.ParkPhamTheorem

namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

section

variable {α : Type*} [DecidableEq α]

/-- **Coloring of a finite universe.** A `Fin m`-valued labeling of the
elements of `X` (encoded as a function on the subtype `{x // x ∈ X}`).

The set of colorings is finite (a finite product of `Fin m`). A
uniformly random coloring corresponds to the discrete uniform measure
on this finite set, and color classes have the same marginal as a
random subset at density `1/m`. -/
abbrev Coloring (X : Finset α) (m : ℕ) :=
  {x // x ∈ X} → Fin m

/-- The `i`th part of a coloring as a `Finset α`. -/
noncomputable def colorPart {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) : Finset α :=
  Finset.image Subtype.val (X.attach.filter (fun x => c x = i))

/-- Membership in a color class, unpacked to an element of `X` with the
specified color. -/
lemma mem_colorPart {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) {x : α} :
    x ∈ colorPart c i ↔ ∃ hx : x ∈ X, c ⟨x, hx⟩ = i := by
  simp [colorPart]

lemma colorPart_subset {X : Finset α} {m : ℕ} (c : Coloring X m)
    (i : Fin m) :
    colorPart c i ⊆ X := by
  intro x hx
  rcases (mem_colorPart c i).1 hx with ⟨hxX, _⟩
  exact hxX

lemma colorPart_disjoint {X : Finset α} {m : ℕ} (c : Coloring X m)
    {i j : Fin m} (hij : i ≠ j) :
    Disjoint (colorPart c i) (colorPart c j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases (mem_colorPart c i).1 hxi with ⟨hxX, hxi'⟩
  rcases (mem_colorPart c j).1 hxj with ⟨_, hxj'⟩
  exact hij (hxi'.symm.trans hxj')

lemma colorPart_eq_iff {X T : Finset α} (hTX : T ⊆ X) {m : ℕ}
    (c : Coloring X m) (i : Fin m) :
    colorPart c i = T ↔ ∀ x : {x // x ∈ X}, (x.1 ∈ T ↔ c x = i) := by
  constructor
  · intro h x
    constructor
    · intro hxT
      have hxpart : x.1 ∈ colorPart c i := by simpa [h] using hxT
      rcases (mem_colorPart c i).1 hxpart with ⟨hxX, hxci⟩
      have hx_eq : (⟨x.1, hxX⟩ : {x // x ∈ X}) = x := by ext; rfl
      simpa [hx_eq] using hxci
    · intro hci
      have hxpart : x.1 ∈ colorPart c i :=
        (mem_colorPart c i).2 ⟨x.2, hci⟩
      simpa [h] using hxpart
  · intro h
    ext a
    constructor
    · intro ha
      rcases (mem_colorPart c i).1 ha with ⟨haX, hci⟩
      exact (h ⟨a, haX⟩).2 hci
    · intro haT
      have haX : a ∈ X := hTX haT
      exact (mem_colorPart c i).2 ⟨haX, (h ⟨a, haX⟩).1 haT⟩

/-- A fixed color class `T` leaves arbitrary choices of colors different from
`i` on `X \ T`. -/
noncomputable def colorPartFiberEquiv {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (i : Fin m) :
    {c : Coloring X m // colorPart c i = T} ≃
      ({x // x ∈ X \ T} → {j : Fin m // j ≠ i}) where
  toFun c x := by
    refine ⟨c.1 ⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩, ?_⟩
    intro hc
    have hxT : x.1 ∈ T :=
      ((colorPart_eq_iff hTX c.1 i).1 c.2
        ⟨x.1, (Finset.mem_sdiff.1 x.2).1⟩).2 hc
    exact (Finset.mem_sdiff.1 x.2).2 hxT
  invFun g := by
    refine ⟨(fun x =>
      if hxT : x.1 ∈ T then i
      else (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).1), ?_⟩
    rw [colorPart_eq_iff hTX]
    intro x
    constructor
    · intro hxT
      simp [hxT]
    · intro hxcolor
      by_contra hxT
      have hg_ne : (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).1 ≠ i :=
        (g ⟨x.1, Finset.mem_sdiff.2 ⟨x.2, hxT⟩⟩).2
      simp [hxT] at hxcolor
      exact hg_ne hxcolor
  left_inv c := by
    ext x
    by_cases hxT : x.1 ∈ T
    · have hxcolor : c.1 x = i :=
        ((colorPart_eq_iff hTX c.1 i).1 c.2 x).1 hxT
      simp [hxT, hxcolor]
    · simp [hxT]
  right_inv g := by
    funext x
    apply Subtype.ext
    have hxT : x.1 ∉ T := (Finset.mem_sdiff.1 x.2).2
    simp [hxT]

lemma colorPart_fiber_card {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (i : Fin m) :
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => colorPart c i = T)).card =
      (m - 1) ^ (X.card - T.card) := by
  classical
  have hleft :
      Fintype.card {c : Coloring X m // colorPart c i = T} =
        ((Finset.univ : Finset (Coloring X m)).filter
          (fun c => colorPart c i = T)).card := by
    exact Fintype.card_ofFinset _ (by
      intro c
      change c ∈ ((Finset.univ : Finset (Coloring X m)).filter
          (fun c => colorPart c i = T)) ↔ colorPart c i = T
      simp)
  have hcongr :
      Fintype.card {c : Coloring X m // colorPart c i = T} =
        Fintype.card ({x // x ∈ X \ T} → {j : Fin m // j ≠ i}) :=
    Fintype.card_congr (colorPartFiberEquiv hTX i)
  have hcod : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
    have hcompl := Fintype.card_subtype_compl (fun j : Fin m => j = i)
    simp [Fintype.card_fin] at hcompl ⊢
  have hdom : Fintype.card {x // x ∈ X \ T} = X.card - T.card := by
    calc
      Fintype.card {x // x ∈ X \ T} = (X \ T).card := by
          exact Fintype.card_ofFinset _ (by
            intro x
            change x ∈ X \ T ↔ x ∈ X \ T
            rfl)
      _ = X.card - T.card := Finset.card_sdiff_of_subset hTX
  rw [← hleft, hcongr, Fintype.card_fun, hcod, hdom]

lemma coloring_card (X : Finset α) (m : ℕ) :
    Fintype.card (Coloring X m) = m ^ X.card := by
  rw [Fintype.card_fun, Fintype.card_fin]
  congr
  exact Fintype.card_coe X

omit [DecidableEq α] in
lemma bernoulliMass_inv_nat_mul_card {X T : Finset α} (hTX : T ⊆ X)
    {m : ℕ} (hm : 0 < m) :
    ((m : ℝ) ^ X.card) *
        bernoulliMass X T ((1 : ℝ) / m) =
      ((m - 1 : ℕ) : ℝ) ^ (X.card - T.card) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcard_le : T.card ≤ X.card := Finset.card_le_card hTX
  have hsplit : X.card = T.card + (X.card - T.card) :=
    (Nat.add_sub_of_le hcard_le).symm
  have hone :
      (1 : ℝ) - (1 : ℝ) / m = ((m - 1 : ℕ) : ℝ) / m := by
    have hm1 : 1 ≤ m := hm
    rw [Nat.cast_sub hm1]
    field_simp [hmR]
    ring
  unfold bernoulliMass
  rw [hone, hsplit, Nat.add_sub_cancel_left, pow_add]
  rw [div_pow, div_pow]
  field_simp [hmR]
  ring

/-- Colors whose class contains at least one member of `A`. -/
noncomputable def successfulColors {X : Finset α} {m : ℕ}
    (A : Finset (Finset α)) (c : Coloring X m) : Finset (Fin m) :=
  Finset.univ.filter fun i => ∃ S ∈ A, S ⊆ colorPart c i

lemma mem_successfulColors {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m} :
    i ∈ successfulColors A c ↔ ∃ S ∈ A, S ⊆ colorPart c i := by
  simp [successfulColors]

lemma mem_successfulColors_iff_colorPart_mem_upClosureIn {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m} :
    i ∈ successfulColors A c ↔ colorPart c i ∈ upClosureIn X A := by
  rw [mem_successfulColors, mem_upClosureIn]
  exact ⟨fun h => ⟨colorPart_subset c i, h⟩, fun h => h.2⟩

lemma successful_colorings_card (X : Finset α) (A : Finset (Finset α))
    {m : ℕ} (i : Fin m) :
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card =
      ∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
        (m - 1) ^ (X.card - T.card) := by
  classical
  let s : Finset (Coloring X m) :=
    (Finset.univ : Finset (Coloring X m)).filter
      (fun c => i ∈ successfulColors A c)
  let t : Finset (Finset α) :=
    X.powerset.filter (fun T => T ∈ upClosureIn X A)
  have hmaps : Set.MapsTo (fun c : Coloring X m => colorPart c i) (↑s) (↑t) := by
    intro c hc
    have hsucc : i ∈ successfulColors A c := by
      simpa [s] using hc
    exact Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 (colorPart_subset c i),
        (mem_successfulColors_iff_colorPart_mem_upClosureIn).1 hsucc⟩
  calc
    ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card
        = s.card := rfl
    _ = ∑ T ∈ t, {c ∈ s | colorPart c i = T}.card :=
        Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ T ∈ t, (m - 1) ^ (X.card - T.card) := by
        apply Finset.sum_congr rfl
        intro T hT
        have hTX : T ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
        have hTU : T ∈ upClosureIn X A := (Finset.mem_filter.1 hT).2
        have hfiber :
            {c ∈ s | colorPart c i = T} =
              (Finset.univ : Finset (Coloring X m)).filter
                (fun c => colorPart c i = T) := by
          ext c
          constructor
          · intro hc
            exact Finset.mem_filter.2 ⟨Finset.mem_univ c, (Finset.mem_filter.1 hc).2⟩
          · intro hc
            have hct : colorPart c i = T := (Finset.mem_filter.1 hc).2
            have hsucc : i ∈ successfulColors A c := by
              rw [mem_successfulColors_iff_colorPart_mem_upClosureIn, hct]
              exact hTU
            exact Finset.mem_filter.2
              ⟨by simpa [s] using hsucc, hct⟩
        rw [hfiber, colorPart_fiber_card hTX i]

lemma successful_colorings_card_real (X : Finset α) (A : Finset (Finset α))
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card : ℝ) =
      (Fintype.card (Coloring X m) : ℝ) *
        muP X (upClosureIn X A) ((1 : ℝ) / m) := by
  classical
  rw [successful_colorings_card X A i, coloring_card]
  unfold muP
  rw [Nat.cast_sum]
  calc
    (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
        (((m - 1) ^ (X.card - T.card) : ℕ) : ℝ))
        = ∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            ((m : ℝ) ^ X.card) *
              bernoulliMass X T ((1 : ℝ) / m) := by
            apply Finset.sum_congr rfl
            intro T hT
            have hTX : T ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
            simpa [Nat.cast_pow] using (bernoulliMass_inv_nat_mul_card hTX hm).symm
    _ = (m : ℝ) ^ X.card *
          (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            bernoulliMass X T ((1 : ℝ) / m)) := by
            rw [Finset.mul_sum]
    _ = ↑(m ^ X.card) *
          (∑ T ∈ X.powerset.filter (fun T => T ∈ upClosureIn X A),
            bernoulliMass X T ((1 : ℝ) / m)) := by
            norm_num
    _ = ↑(m ^ X.card) * muP X (upClosureIn X A) ((1 : ℝ) / m) := rfl

lemma sum_successfulColors_card (X : Finset α) (A : Finset (Finset α)) (m : ℕ) :
    (∑ c : Coloring X m, (successfulColors A c).card) =
      ∑ i : Fin m, ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card := by
  calc
    (∑ c : Coloring X m, (successfulColors A c).card)
        = ∑ c : Coloring X m, ∑ i : Fin m,
            if i ∈ successfulColors A c then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [← Finset.card_filter]
            simp [successfulColors]
    _ = ∑ i : Fin m, ∑ c : Coloring X m,
            if i ∈ successfulColors A c then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin m, ((Finset.univ : Finset (Coloring X m)).filter
        (fun c => i ∈ successfulColors A c)).card := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.card_filter]

theorem exists_coloring_many_successful_of_mu_ge
    (X : Finset α) (A : Finset (Finset α)) (r : ℕ) (hr : 2 ≤ r)
    (hmu : muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2) :
    ∃ c : Coloring X (2 * r), r ≤ (successfulColors A c).card := by
  classical
  let m := 2 * r
  have hm : 0 < m := by dsimp [m]; omega
  let C : ℕ := Fintype.card (Coloring X m)
  have hCpos_nat : 0 < C := by
    dsimp [C]
    rw [coloring_card]
    exact Nat.pow_pos (a := m) (n := X.card) hm
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos_nat
  have hsum_eq :
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) =
        (m : ℝ) * (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
    rw [sum_successfulColors_card X A m]
    rw [Nat.cast_sum]
    calc
      (∑ i : Fin m,
          (((Finset.univ : Finset (Coloring X m)).filter
            (fun c => i ∈ successfulColors A c)).card : ℝ))
          = ∑ _i : Fin m,
              (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [C]
              exact successful_colorings_card_real X A hm i
      _ = (m : ℝ) * (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) := by
              simp [Fintype.card_fin, mul_assoc]
  have hsum_lower :
      (r : ℝ) * (C : ℝ) ≤
        ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) := by
    rw [hsum_eq]
    have hm_eq : (m : ℝ) = 2 * (r : ℝ) := by simp [m]
    have hmu' :
        (1 / 2 : ℝ) ≤ muP X (upClosureIn X A) ((1 : ℝ) / m) := by
      simpa [m] using hmu
    have hmul :
        (C : ℝ) * (1 / 2 : ℝ) ≤
          (C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m) :=
      mul_le_mul_of_nonneg_left hmu' hCpos.le
    calc
      (r : ℝ) * (C : ℝ) =
          (m : ℝ) * ((C : ℝ) * (1 / 2 : ℝ)) := by
            rw [hm_eq]
            ring
      _ ≤ (m : ℝ) *
          ((C : ℝ) * muP X (upClosureIn X A) ((1 : ℝ) / m)) := by
            exact mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (m : ℝ) * (C : ℝ) *
          muP X (upClosureIn X A) ((1 : ℝ) / m) := by
            ring
  by_contra hnone
  have hle_each : ∀ c : Coloring X m, (successfulColors A c).card ≤ r - 1 := by
    intro c
    have hnot : ¬ r ≤ (successfulColors A c).card := by
      intro hc
      exact hnone ⟨c, hc⟩
    omega
  have hsum_le_nat :
      (∑ c : Coloring X m, (successfulColors A c).card : ℕ) ≤
        ∑ _c : Coloring X m, (r - 1) := by
    exact Finset.sum_le_sum (fun c _ => hle_each c)
  have hsum_le :
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ) ≤
        (C : ℝ) * (r - 1 : ℕ) := by
    calc
      ((∑ c : Coloring X m, (successfulColors A c).card : ℕ) : ℝ)
          ≤ ((∑ _c : Coloring X m, (r - 1) : ℕ) : ℝ) := by
            exact_mod_cast hsum_le_nat
      _ = (C : ℝ) * (r - 1 : ℕ) := by
            simp [C]
  have hlt : (C : ℝ) * (r - 1 : ℕ) < (r : ℝ) * (C : ℝ) := by
    have hsub : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num
    rw [hsub]
    nlinarith
  nlinarith

/-- A chosen member of `A` witnessing that a color is successful. The value is
irrelevant on unsuccessful colors. -/
noncomputable def successfulMember {X : Finset α} {m : ℕ}
    (A : Finset (Finset α)) (c : Coloring X m) (i : Fin m) : Finset α :=
  if h : i ∈ successfulColors A c then
    Classical.choose ((mem_successfulColors).1 h)
  else
    ∅

lemma successfulMember_mem {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m}
    (hi : i ∈ successfulColors A c) :
    successfulMember A c i ∈ A := by
  unfold successfulMember
  rw [dif_pos hi]
  exact (Classical.choose_spec ((mem_successfulColors).1 hi)).1

lemma successfulMember_subset_colorPart {X : Finset α} {m : ℕ}
    {A : Finset (Finset α)} {c : Coloring X m} {i : Fin m}
    (hi : i ∈ successfulColors A c) :
    successfulMember A c i ⊆ colorPart c i := by
  unfold successfulMember
  rw [dif_pos hi]
  exact (Classical.choose_spec ((mem_successfulColors).1 hi)).2

lemma member_nonempty_of_uniform
    {A : Finset (Finset α)} {S : Finset α} {k : ℕ}
    (hk : 1 ≤ k) (hUniform : Erdos202.UniformFamily A k) (hS : S ∈ A) :
    S.Nonempty := by
  have hcard : S.card = k := hUniform S hS
  exact Finset.card_pos.1 (by omega)

/-- Deterministic part of the random-partition argument: once one coloring has
at least `r` successful colors, choose one nonempty `A`-member inside each of
`r` successful color classes. Distinct color classes are disjoint. -/
theorem disjoint_members_of_many_successful_colors {X : Finset α} {m r k : ℕ}
    {A : Finset (Finset α)} (c : Coloring X m)
    (hk : 1 ≤ k) (hUniform : Erdos202.UniformFamily A k)
    (hSuccess : r ≤ (successfulColors A c).card) :
    ∃ B : Finset (Finset α),
      B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  classical
  rcases Finset.exists_subset_card_eq hSuccess with ⟨I, hI_success, hI_card⟩
  let pick : Fin m → Finset α := successfulMember A c
  let B : Finset (Finset α) := I.image pick
  have hpick_mem : ∀ i ∈ I, pick i ∈ A := by
    intro i hi
    exact successfulMember_mem (hI_success hi)
  have hpick_subset : ∀ i ∈ I, pick i ⊆ colorPart c i := by
    intro i hi
    exact successfulMember_subset_colorPart (hI_success hi)
  have hpick_inj : Set.InjOn pick I := by
    intro i hi j hj hpick_eq
    by_contra hij
    have hnonempty : (pick i).Nonempty :=
      member_nonempty_of_uniform hk hUniform (hpick_mem i hi)
    rcases hnonempty with ⟨x, hx⟩
    have hxi : x ∈ colorPart c i := hpick_subset i hi hx
    have hxj : x ∈ colorPart c j := by
      have hx' : x ∈ pick j := by simpa [hpick_eq] using hx
      exact hpick_subset j hj hx'
    exact (Finset.disjoint_left.1 (colorPart_disjoint c hij) hxi) hxj
  refine ⟨B, ?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_image.1 hS with ⟨i, hi, rfl⟩
    exact hpick_mem i hi
  · calc
      B.card = I.card := Finset.card_image_of_injOn hpick_inj
      _ = r := hI_card
  · intro S hS T hT hST
    rcases Finset.mem_image.1 hS with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.1 hT with ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      exact hST (by simp [hij])
    exact (Disjoint.mono (hpick_subset i hi) (hpick_subset j hj)
      (colorPart_disjoint c hij))

end

/-- **Random-partition bookkeeping** (Park–Pham PDF Proposition 2.1 / Cor 2.3
final step). Once `muP X (upClosureIn X A) (1/(2r)) ≥ 1/2` is in hand
(via `mu_at_partition_density_ge_half`), the random-partition argument —
viewing the Bernoulli measure as the marginal of a uniform random `2r`-
coloring of `X`, then a double-counting argument over colorings — produces
`r` pairwise-disjoint members of `A`.

This is **purely finite combinatorics** with no analytic content; it
isolates the discrete random-partition translation from the Park–Pham
expectation-threshold core (`park_pham_threshold_not_small_lt_exists`, exposed
through the derived closed-endpoint theorem
`park_pham_threshold_not_small_exists`, the exact-threshold theorem
`park_pham_threshold_at_exists`, and the larger-density theorem
`park_pham_threshold_exists`).

The proof strategy is:
1. Re-express `muP` as the average over uniform colorings of the
   indicator "some color class contains a member of A".
2. By the `muP ≥ 1/2` hypothesis combined with a union bound over the
   `2r` colors, the expected number of "successful" color classes is at
   least `r`.
3. Pick a coloring witnessing this; pick a member of A inside each
   successful color class; color classes are pairwise disjoint, so the
   picked members are pairwise disjoint. -/
theorem partition_density_to_disjoint_members :
    ∀ {α : Type*} [DecidableEq α]
      (X : Finset α) (A : Finset (Finset α)) (r k : ℕ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      Erdos202.UniformFamily A k →
      (∀ S ∈ A, S ⊆ X) →
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  intro α _ X A r k _hA hr hk hUniform _hAX hmu
  rcases exists_coloring_many_successful_of_mu_ge X A r hr hmu with ⟨c, hc⟩
  exact disjoint_members_of_many_successful_colors c hk hUniform hc

section

variable {α : Type*} [DecidableEq α]

/-- **Spread-disjointness theorem** (PDF Proposition 2.1 / Corollary 2.3).

Matches the historical `Erdos202.spread_disjointness_input` interface in
`SpreadCore.lean`.

Proved from the strict Park--Pham non-smallness theorem
`park_pham_threshold_not_small_lt_exists`; the closed-endpoint theorem,
`qSmallUpper` wrapper, density-monotonicity, and finite random-partition
bookkeeping below are fully formalized in `ParkPham/`. -/
theorem spread_disjointness_theorem :
    ∃ Csp : ℝ, 0 < Csp ∧
      ∀ {α : Type*} [DecidableEq α]
        (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
        A.Nonempty →
        2 ≤ r →
        1 ≤ k →
        Erdos202.UniformFamily A k →
        Erdos202.SpreadFamily A κ →
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
        ∃ B : Finset (Finset α),
          B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  rcases park_pham_threshold_exists with ⟨CKK, hCKK_pos, hThreshold⟩
  refine ⟨CspOf CKK, CspOf_pos CKK, ?_⟩
  intro α _ A r k κ hA hr hk hUniform hSpread hκ
  -- Ground universe: X = ⋃_{S ∈ A} S
  let X : Finset α := A.biUnion id
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hSA x hxS
    exact Finset.mem_biUnion.mpr ⟨S, hSA, hxS⟩
  have hThresholdα :
      ∀ (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
        0 < q → q ≤ 1 →
        0 ≤ p → p ≤ 1 →
        CKK * q * Real.log (ell X U) ≤ p →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        qSmallUpper X U q →
        muP X U p ≥ 1 / 2 := by
    intro X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
    exact hThreshold X U q p hq0 hq1 hp0 hp1 hDensity hUX hIncr hSmall
  -- Step 1: muP ≥ 1/2 from the Park–Pham layer.
  have hmu :
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 :=
    mu_at_partition_density_ge_half_of_threshold
      CKK hCKK_pos hThresholdα hA hr hk hUniform hSpread hAX hκ
  -- Step 2: random-partition translation.
  exact partition_density_to_disjoint_members X A r k hA hr hk hUniform hAX hmu

end

end ParkPham
end Erdos202
