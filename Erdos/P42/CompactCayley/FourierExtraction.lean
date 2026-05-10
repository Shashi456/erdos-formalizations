/-
Erdős Problem 42 — generic finite Fourier extraction primitives.

This is the first compact-Cayley axiom-removal layer.  It deliberately avoids
clique-specific definitions: a `FourierSeq` is only a bounded sequence of
complex-valued functions on prime cyclic groups.  Later compact-Cayley
extraction specializes it to the indicators of the counterexample sets.
-/

import Erdos.P42.CompactCayley.Subseq
import Erdos.P42.CompactCayley.SpectralCutNorm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.PNat.Basic

namespace Erdos42.CompactCayley

open Finset Erdos42
open scoped BigOperators Classical Topology

/-- A bounded sequence of functions on prime cyclic groups. -/
structure FourierSeq where
  p : ℕ → ℕ
  prime : ∀ n, (p n).Prime
  p_gt : ∀ n, n < p n
  h : ∀ n, ZMod (p n) → ℂ
  h_bound : ∀ n x, ‖h n x‖ ≤ 1

/-- Pass a generic Fourier sequence to a strictly monotone subsequence. -/
def FourierSeq.subseq
    (F : FourierSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    FourierSeq where
  p n := F.p (φ n)
  prime n := F.prime (φ n)
  p_gt n := by
    have hn_le_φn : n ≤ φ n := by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
          exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))
    exact lt_of_le_of_lt hn_le_φn (F.p_gt (φ n))
  h n := F.h (φ n)
  h_bound n x := F.h_bound (φ n) x

/-- The Fourier sequence attached to a compact-Cayley counterexample sequence:
the functions are indicators of the allowed Cayley difference sets. -/
noncomputable def CayleyCounterSeq.toFourierSeq
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) :
    FourierSeq where
  p := S.p
  prime := S.prime
  p_gt := S.p_gt
  h n := indicatorC (S.T n)
  h_bound n x := by
    classical
    by_cases hx : x ∈ S.T n <;> simp [indicatorC, hx]

/-- Normalized Fourier coefficient of the `n`-th function in a `FourierSeq`. -/
noncomputable def FourierSeq.coeff
    (F : FourierSeq) (n : ℕ) (r : ZMod (F.p n)) : ℂ :=
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  normalizedDftFunction (F.h n) r

lemma FourierSeq.coeff_eq_normalizedDftFunction
    (F : FourierSeq) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    F.coeff n = normalizedDftFunction (F.h n) := by
  funext r
  rfl

/-- Parseval bound for a bounded `FourierSeq` term. -/
lemma FourierSeq.sum_sq_norm_coeff_le_one
    (F : FourierSeq) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    (∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2) ≤ 1 := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  simpa [FourierSeq.coeff] using
    (sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one
      (p := F.p n) (f := F.h n) (F.h_bound n))

/-- Pointwise normalized Fourier coefficients of a bounded `FourierSeq` are
bounded by `1`. -/
lemma FourierSeq.norm_coeff_le_one
    (F : FourierSeq) (n : ℕ) (r : ZMod (F.p n)) :
    ‖F.coeff n r‖ ≤ 1 := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  have hsum := F.sum_sq_norm_coeff_le_one n
  have hterm :
      ‖F.coeff n r‖ ^ 2 ≤
        ∑ s : ZMod (F.p n), ‖F.coeff n s‖ ^ 2 :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (ZMod (F.p n))))
      (f := fun s : ZMod (F.p n) => ‖F.coeff n s‖ ^ 2)
      (fun _s _hs => sq_nonneg _) (Finset.mem_univ r)
  have hsquare : ‖F.coeff n r‖ ^ 2 ≤ 1 := hterm.trans hsum
  have habs : |‖F.coeff n r‖| ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mp hsquare
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

/-- Large spectrum at threshold `q⁻¹`. -/
noncomputable def FourierSeq.largeSpectrum
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    Finset (ZMod (F.p n)) :=
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  (Finset.univ : Finset (ZMod (F.p n))).filter
    (fun r => ((q : ℝ)⁻¹) < ‖F.coeff n r‖)

lemma FourierSeq.mem_largeSpectrum
    {F : FourierSeq} {q : ℕ+} {n : ℕ} {r : ZMod (F.p n)} :
    r ∈ F.largeSpectrum q n ↔ ((q : ℝ)⁻¹) < ‖F.coeff n r‖ := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  simp [FourierSeq.largeSpectrum]

lemma FourierSeq.largeSpectrum_subset_univ
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    F.largeSpectrum q n ⊆ (Finset.univ : Finset (ZMod (F.p n))) := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  intro r _hr
  simp

lemma FourierSeq.largeSpectrum_card_mul_sq_le_sum_sq
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    ((F.largeSpectrum q n).card : ℝ) * ((q : ℝ)⁻¹) ^ 2 ≤
      ∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2 := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  calc
    ((F.largeSpectrum q n).card : ℝ) * ((q : ℝ)⁻¹) ^ 2 =
        ∑ r ∈ F.largeSpectrum q n, ((q : ℝ)⁻¹) ^ 2 := by
          simp [mul_comm]
    _ ≤ ∑ r ∈ F.largeSpectrum q n, ‖F.coeff n r‖ ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hlt : ((q : ℝ)⁻¹) < ‖F.coeff n r‖ :=
            FourierSeq.mem_largeSpectrum.mp hr
          have hq_nonneg : 0 ≤ ((q : ℝ)⁻¹) := by positivity
          have hnorm_nonneg : 0 ≤ ‖F.coeff n r‖ := norm_nonneg _
          have hle_abs : |((q : ℝ)⁻¹)| ≤ |‖F.coeff n r‖| := by
            rw [abs_of_nonneg hq_nonneg, abs_of_nonneg hnorm_nonneg]
            exact le_of_lt hlt
          exact sq_le_sq.mpr hle_abs
    _ ≤ ∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (F.largeSpectrum_subset_univ q n)
            (by intro r _hrUniv _hrNotLarge; exact sq_nonneg _)

/-- Parseval cardinality bound for the large spectrum at threshold `q⁻¹`. -/
lemma FourierSeq.largeSpectrum_card_le
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    (F.largeSpectrum q n).card ≤ (q : ℕ) ^ 2 := by
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  have hmass :=
    (F.largeSpectrum_card_mul_sq_le_sum_sq q n).trans
      (F.sum_sq_norm_coeff_le_one n)
  have hq_pos : 0 < (q : ℝ) := by positivity
  have hτsq_pos : 0 < ((q : ℝ)⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr hq_pos)
  have hreal :
      ((F.largeSpectrum q n).card : ℝ) ≤ ((q : ℝ) ^ 2) := by
    calc
      ((F.largeSpectrum q n).card : ℝ) ≤
          1 / (((q : ℝ)⁻¹) ^ 2) := by
            exact (le_div_iff₀ hτsq_pos).mpr (by simpa [mul_comm] using hmass)
      _ = (q : ℝ) ^ 2 := by
            field_simp [hq_pos.ne']
  have hreal_nat :
      ((F.largeSpectrum q n).card : ℝ) ≤ (((q : ℕ) ^ 2 : ℕ) : ℝ) := by
    simpa using hreal
  exact_mod_cast hreal_nat

/-! ## Finite large-spectrum labelling -/

/-- A fixed countable label type large enough to label every threshold-large
frequency, for every `n`, without needing cardinalities to stabilize. -/
abbrev LargeLabel : Type :=
  Sigma fun q : ℕ+ => Fin ((q : ℕ) ^ 2 + 1)

/-- A finite set of cardinality at most `m` can be covered by a map from
`Fin m`.  Extra indices may repeat an arbitrary default value. -/
lemma exists_cover_map_of_card_le
    {α : Type*} [Inhabited α] (s : Finset α) (m : ℕ)
    (hcard : s.card ≤ m) :
    ∃ f : Fin m → α, ∀ x ∈ s, ∃ i : Fin m, f i = x := by
  classical
  let f : Fin m → α := fun i =>
    if h : (i : ℕ) < s.card then
      ((Finset.equivFin s).symm ⟨i, h⟩).1
    else default
  refine ⟨f, ?_⟩
  intro x hx
  let xs : s := ⟨x, hx⟩
  let j : Fin s.card := Finset.equivFin s xs
  let i : Fin m := ⟨j, lt_of_lt_of_le j.2 hcard⟩
  refine ⟨i, ?_⟩
  have hi : (i : ℕ) < s.card := j.2
  have hfin : (⟨(i : ℕ), hi⟩ : Fin s.card) = j := by
    ext
    rfl
  have hpre :
      (Finset.equivFin s).symm ⟨(i : ℕ), hi⟩ = xs := by
    rw [hfin]
    dsimp [j]
    simp
  simp [f, i, hi, hpre, xs]

/-- A canonical, choice-based frequency assignment for all large-spectrum
labels of a fixed `FourierSeq`. -/
noncomputable def FourierSeq.largeSpectrumLabelFreq
    (F : FourierSeq) (label : LargeLabel) (n : ℕ) :
    ZMod (F.p n) :=
  let q := label.1
  let m := (q : ℕ) ^ 2 + 1
  let cover :=
    Classical.choose
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  cover label.2

/-- Every threshold-large frequency is represented by one of the fixed labels
at that threshold. -/
lemma FourierSeq.exists_largeSpectrumLabelFreq_eq_of_mem
    (F : FourierSeq) (q : ℕ+) (n : ℕ) {r : ZMod (F.p n)}
    (hr : r ∈ F.largeSpectrum q n) :
    ∃ k : Fin ((q : ℕ) ^ 2 + 1),
      F.largeSpectrumLabelFreq ⟨q, k⟩ n = r := by
  classical
  unfold FourierSeq.largeSpectrumLabelFreq
  let m := (q : ℕ) ^ 2 + 1
  let cover :=
    Classical.choose
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  have hcover :
      ∀ x ∈ F.largeSpectrum q n, ∃ i : Fin m, cover i = x :=
    Classical.choose_spec
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  rcases hcover r hr with ⟨k, hk⟩
  exact ⟨k, hk⟩

/-- Existential packaging of the label-frequency assignment, useful for later
extraction structures that should not expose the chosen implementation. -/
theorem FourierSeq.exists_labelFreq_for_largeSpectrum
    (F : FourierSeq) :
    ∃ labelFreq : LargeLabel → ∀ n, ZMod (F.p n),
      ∀ q n r,
        r ∈ F.largeSpectrum q n →
        ∃ k : Fin ((q : ℕ) ^ 2 + 1),
          labelFreq ⟨q, k⟩ n = r := by
  refine ⟨fun label n => F.largeSpectrumLabelFreq label n, ?_⟩
  intro q n r hr
  exact F.exists_largeSpectrumLabelFreq_eq_of_mem q n hr

end Erdos42.CompactCayley
