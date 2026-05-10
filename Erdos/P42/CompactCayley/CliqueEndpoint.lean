/-
Erdős Problem 42 — internal finite lemmas for the compact-Cayley theorem.

This file starts opening the remaining Route B trust boundary
`compact_cayley_clique`.  The lemmas here are finite bookkeeping around the
endpoint of the compactness argument: once counting convergence gives an
ordered tuple whose pairwise differences lie in the allowed set, `0 ∉ T`
turns that tuple into an actual finite clique.
-/

import Erdos.P42.Shared.FiniteFourier

namespace Erdos42.CompactCayley

open Finset Erdos42

/-- An ordered `ℓ`-tuple whose distinct pairwise differences all lie in the
allowed Cayley set `T`. -/
def CliqueTuple {p ℓ : ℕ} (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : Prop :=
  ∀ i j : Fin ℓ, i ≠ j → x i - x j ∈ T

lemma cliqueTuple_injective_of_zero_notMem
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hT0 : (0 : ZMod p) ∉ T) (hx : CliqueTuple T x) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  have hdiff : x i - x j ∈ T := hx i j hne
  apply hT0
  simpa [hij] using hdiff

/-- A zero-free ordered clique tuple yields the `Finset` clique required by
`compact_cayley_clique`. This is the finite endpoint used after the compact
counting argument proves that at least one ordered clique tuple exists. -/
theorem exists_clique_of_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    {x : Fin ℓ → ZMod p} (hx : CliqueTuple T x) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  classical
  let C : Finset (ZMod p) := (Finset.univ : Finset (Fin ℓ)).image x
  have hinj : Function.Injective x :=
    cliqueTuple_injective_of_zero_notMem hT0 hx
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro y hy z hz hyz
    change y ∈ (Finset.univ : Finset (Fin ℓ)).image x at hy
    change z ∈ (Finset.univ : Finset (Fin ℓ)).image x at hz
    rw [Finset.mem_image] at hy hz
    rcases hy with ⟨i, _hi, rfl⟩
    rcases hz with ⟨j, _hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      exact hyz (by simp [hij])
    exact hx i j hij

/-- Contrapositive form: a zero-free Cayley graph with no `ℓ`-clique has no
ordered clique tuple of length `ℓ`. -/
lemma not_cliqueTuple_of_no_clique
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C)
    (x : Fin ℓ → ZMod p) :
    ¬ CliqueTuple T x := by
  intro hx
  exact hNoClique (exists_clique_of_cliqueTuple hT0 hx)

/-- Boolean-valued indicator for ordered clique tuples, useful when connecting
finite homomorphism densities to actual cliques. -/
noncomputable def cliqueTupleIndicator {p ℓ : ℕ}
    (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : ℂ :=
  by
    classical
    exact if CliqueTuple T x then 1 else 0

lemma cliqueTupleIndicator_eq_zero_of_no_clique
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C)
    (x : Fin ℓ → ZMod p) :
    cliqueTupleIndicator T x = 0 := by
  classical
  unfold cliqueTupleIndicator
  simp [not_cliqueTuple_of_no_clique hT0 hNoClique x]

/-- The finite set of ordered `ℓ`-tuples forming a clique in the Cayley graph. -/
noncomputable def cliqueTupleFinset {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : Finset (Fin ℓ → ZMod p) :=
  by
    classical
    exact (Finset.univ : Finset (Fin ℓ → ZMod p)).filter (fun x => CliqueTuple T x)

lemma mem_cliqueTupleFinset {p ℓ : ℕ} [NeZero p]
    {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p} :
    x ∈ cliqueTupleFinset (ℓ := ℓ) T ↔ CliqueTuple T x := by
  classical
  simp [cliqueTupleFinset]

lemma cliqueTupleFinset_nonempty_of_cliqueTuple
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    {x : Fin ℓ → ZMod p} (hx : CliqueTuple T x) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty :=
  ⟨x, mem_cliqueTupleFinset.mpr hx⟩

lemma exists_clique_of_cliqueTupleFinset_nonempty
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (h : (cliqueTupleFinset (ℓ := ℓ) T).Nonempty) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rcases h with ⟨x, hx⟩
  exact exists_clique_of_cliqueTuple hT0 (mem_cliqueTupleFinset.mp hx)

lemma cliqueTupleFinset_nonempty_of_clique
    {p ℓ : ℕ} [NeZero p] {T C : Finset (ZMod p)}
    (hCcard : C.card = ℓ) (hClique : CliqueInCayley T C) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty := by
  classical
  let e : C ≃ Fin ℓ := C.equivFinOfCardEq hCcard
  let x : Fin ℓ → ZMod p := fun i => (e.symm i).1
  refine cliqueTupleFinset_nonempty_of_cliqueTuple (T := T) (x := x) ?_
  intro i j hij
  have hxi : x i ∈ C := (e.symm i).2
  have hxj : x j ∈ C := (e.symm j).2
  have hne : x i ≠ x j := by
    intro h
    have hsub : e.symm i = e.symm j := Subtype.ext h
    exact hij (by simpa using congrArg e hsub)
  exact hClique (x i) hxi (x j) hxj hne

lemma cliqueTupleFinset_nonempty_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  refine ⟨exists_clique_of_cliqueTupleFinset_nonempty hT0, ?_⟩
  rintro ⟨C, hCcard, hClique⟩
  exact cliqueTupleFinset_nonempty_of_clique hCcard hClique

/-- The edge set of the complete graph on `Fin ℓ`, oriented by the natural
order to avoid double-counting. -/
def cliqueEdgePairs (ℓ : ℕ) : Finset (Fin ℓ × Fin ℓ) :=
  (Finset.univ : Finset (Fin ℓ × Fin ℓ)).filter (fun e => e.1 < e.2)

lemma cliqueEdgePairs_left_lt_right {ℓ : ℕ} {e : Fin ℓ × Fin ℓ}
    (he : e ∈ cliqueEdgePairs ℓ) : e.1 < e.2 := by
  exact (Finset.mem_filter.mp he).2

lemma cliqueEdgePairs_left_ne_right {ℓ : ℕ} {e : Fin ℓ × Fin ℓ}
    (he : e ∈ cliqueEdgePairs ℓ) : e.1 ≠ e.2 :=
  ne_of_lt (cliqueEdgePairs_left_lt_right he)

lemma cliqueEdgePairs_card_le_sq (ℓ : ℕ) :
    (cliqueEdgePairs ℓ).card ≤ ℓ * ℓ := by
  classical
  unfold cliqueEdgePairs
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (Fin ℓ × Fin ℓ)))
    (p := fun e : Fin ℓ × Fin ℓ => e.1 < e.2)
  simpa [Fintype.card_prod, Fintype.card_fin] using h

/-- Product weight for the finite Cayley `K_ℓ` homomorphism density. For
indicator functions this is `1` exactly on ordered clique tuples and `0`
otherwise, once `T` is symmetric. -/
noncomputable def cliqueKernelWeight {p ℓ : ℕ}
    (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, indicatorC T (x e.1 - x e.2)

lemma cliqueKernelWeight_eq_one_of_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hx : CliqueTuple T x) :
    cliqueKernelWeight T x = 1 := by
  classical
  unfold cliqueKernelWeight
  apply Finset.prod_eq_one
  intro e he
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  have hmem : x e.1 - x e.2 ∈ T := hx e.1 e.2 (ne_of_lt hlt)
  simp [indicatorC, hmem]

lemma cliqueKernelWeight_eq_zero_of_not_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hTsym : SymmetricFinset T) (hx : ¬ CliqueTuple T x) :
    cliqueKernelWeight T x = 0 := by
  classical
  rw [CliqueTuple, not_forall] at hx
  rcases hx with ⟨i, hx⟩
  rw [not_forall] at hx
  rcases hx with ⟨j, hx⟩
  rw [Classical.not_imp] at hx
  rcases hx with ⟨hij, hnot⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · unfold cliqueKernelWeight
    apply Finset.prod_eq_zero (i := (i, j))
    · simp [cliqueEdgePairs, hlt]
    · simp [indicatorC, hnot]
  · have hnot' : x j - x i ∉ T := by
      intro hji
      have hneg : -(x j - x i) ∈ T := (hTsym (x j - x i)).mp hji
      exact hnot (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg)
    unfold cliqueKernelWeight
    apply Finset.prod_eq_zero (i := (j, i))
    · simp [cliqueEdgePairs, hgt]
    · simp [indicatorC, hnot']

lemma cliqueKernelWeight_eq_cliqueTupleIndicator_of_symmetric
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hTsym : SymmetricFinset T)
    (x : Fin ℓ → ZMod p) :
    cliqueKernelWeight T x = cliqueTupleIndicator T x := by
  classical
  unfold cliqueTupleIndicator
  by_cases hx : CliqueTuple T x
  · simp [hx, cliqueKernelWeight_eq_one_of_cliqueTuple hx]
  · simp [hx, cliqueKernelWeight_eq_zero_of_not_cliqueTuple hTsym hx]

/-- Ordered clique-tuple count. This is the finite, unnormalized version of the
`K_ℓ` Cayley homomorphism density for indicator functions. -/
noncomputable def cliqueTupleCount {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ∑ x : Fin ℓ → ZMod p, cliqueTupleIndicator T x

lemma cliqueTupleCount_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueTupleCount (ℓ := ℓ) T = 0 := by
  classical
  unfold cliqueTupleCount
  simp [cliqueTupleIndicator_eq_zero_of_no_clique hT0 hNoClique]

lemma cliqueTupleCount_eq_card_cliqueTupleFinset
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    cliqueTupleCount (ℓ := ℓ) T =
      ((cliqueTupleFinset (ℓ := ℓ) T).card : ℂ) := by
  classical
  rw [cliqueTupleCount]
  change
    (∑ x ∈ (Finset.univ : Finset (Fin ℓ → ZMod p)),
        if CliqueTuple T x then (1 : ℂ) else 0) =
      (((Finset.univ : Finset (Fin ℓ → ZMod p)).filter
        (fun x => CliqueTuple T x)).card : ℂ)
  rw [Finset.sum_boole]

/-- Normalized ordered clique-tuple density. -/
noncomputable def cliqueTupleDensity {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) * cliqueTupleCount (ℓ := ℓ) T

lemma cliqueTupleDensity_eq_card_cliqueTupleFinset
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    cliqueTupleDensity (ℓ := ℓ) T =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ((cliqueTupleFinset (ℓ := ℓ) T).card : ℂ) := by
  simp [cliqueTupleDensity, cliqueTupleCount_eq_card_cliqueTupleFinset]

lemma card_fun_fin_zmod (p ℓ : ℕ) [NeZero p] :
    Fintype.card (Fin ℓ → ZMod p) = p ^ ℓ := by
  simp [ZMod.card]

lemma cliqueTupleDensity_re_eq_card_div
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    (cliqueTupleDensity (ℓ := ℓ) T).re =
      ((cliqueTupleFinset (ℓ := ℓ) T).card : ℝ) /
        (Fintype.card (Fin ℓ → ZMod p) : ℝ) := by
  rw [cliqueTupleDensity_eq_card_cliqueTupleFinset]
  have hden :
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) =
        (((Fintype.card (Fin ℓ → ZMod p) : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [hden, Complex.re_ofReal_mul]
  simp [div_eq_inv_mul]

lemma cliqueTupleDensity_re_pos_iff_cliqueTupleFinset_nonempty
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    0 < (cliqueTupleDensity (ℓ := ℓ) T).re ↔
      (cliqueTupleFinset (ℓ := ℓ) T).Nonempty := by
  rw [cliqueTupleDensity_re_eq_card_div]
  have hden_pos : 0 < (Fintype.card (Fin ℓ → ZMod p) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin ℓ → ZMod p))
  rw [div_eq_inv_mul, mul_pos_iff_of_pos_left (inv_pos.mpr hden_pos)]
  constructor
  · intro hcard
    exact Finset.card_pos.mp (by exact_mod_cast hcard)
  · intro hnonempty
    exact_mod_cast (Finset.card_pos.mpr hnonempty)

lemma cliqueTupleDensity_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T) :
    0 < (cliqueTupleDensity (ℓ := ℓ) T).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [cliqueTupleDensity_re_pos_iff_cliqueTupleFinset_nonempty]
  exact cliqueTupleFinset_nonempty_iff_exists_clique hT0

/-- Product-form `K_ℓ` density, matching the notation in the compact-Cayley
PDF before it is specialized to indicators of Cayley sets. -/
noncomputable def cliqueKernelDensity {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, cliqueKernelWeight T x

lemma cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) :
    cliqueKernelDensity (ℓ := ℓ) T = cliqueTupleDensity (ℓ := ℓ) T := by
  classical
  simp [cliqueKernelDensity, cliqueTupleDensity, cliqueTupleCount,
    cliqueKernelWeight_eq_cliqueTupleIndicator_of_symmetric hTsym]

lemma cliqueTupleDensity_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueTupleDensity (ℓ := ℓ) T = 0 := by
  simp [cliqueTupleDensity, cliqueTupleCount_eq_zero_of_no_clique hT0 hNoClique]

/-- Nonzero ordered clique-tuple count yields an actual finite clique. -/
theorem exists_clique_of_cliqueTupleCount_ne_zero
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hcount : cliqueTupleCount (ℓ := ℓ) T ≠ 0) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  by_contra hNoClique
  exact hcount (cliqueTupleCount_eq_zero_of_no_clique hT0 hNoClique)

/-- Nonzero normalized ordered `K_ℓ` density yields an actual finite clique. -/
theorem exists_clique_of_cliqueTupleDensity_ne_zero
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : cliqueTupleDensity (ℓ := ℓ) T ≠ 0) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  by_contra hNoClique
  exact hdensity (cliqueTupleDensity_eq_zero_of_no_clique hT0 hNoClique)

/-- The form used at the end of the compactness proof: once counting
convergence gives a strictly positive real part for the finite `K_ℓ` density,
the finite Cayley graph contains an `ℓ`-clique. -/
theorem exists_clique_of_cliqueTupleDensity_re_pos
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : 0 < (cliqueTupleDensity (ℓ := ℓ) T).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  refine exists_clique_of_cliqueTupleDensity_ne_zero hT0 ?_
  intro hzero
  exact (ne_of_gt hdensity) (by simp [hzero])

lemma cliqueKernelDensity_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueKernelDensity (ℓ := ℓ) T = 0 := by
  rw [cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric hTsym]
  exact cliqueTupleDensity_eq_zero_of_no_clique hT0 hNoClique

lemma cliqueKernelDensity_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T) :
    0 < (cliqueKernelDensity (ℓ := ℓ) T).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric hTsym]
  exact cliqueTupleDensity_re_pos_iff_exists_clique hT0

end Erdos42.CompactCayley
