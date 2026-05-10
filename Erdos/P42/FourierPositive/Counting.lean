/-
Erdos Problem 42 — Route A finite weighted pattern counts.

This is the finite algebra layer used when opening the Route A
`finite_fourier_avoidance_count` axiom.  It is independent of Route B: it has
the dense vertex weight `U`, the forbidden kernel `F`, and the
inclusion-exclusion expansion of the avoidance density into weighted
complexity-one pattern counts.
-/

import Erdos.P42.FourierPositive.Counterexample
import Mathlib.Data.Real.Sqrt

namespace Erdos42.FourierPositive

open Finset Filter Erdos42
open scoped BigOperators Classical Topology

/-- The oriented edge set of the complete graph on `Fin m`.  Route A uses this
for pairwise forbidden differences in ordered `m`-tuples. -/
def pairEdgePairs (m : ℕ) : Finset (Fin m × Fin m) :=
  (Finset.univ : Finset (Fin m × Fin m)).filter (fun e => e.1 < e.2)

lemma pairEdgePairs_left_lt_right {m : ℕ} {e : Fin m × Fin m}
    (he : e ∈ pairEdgePairs m) : e.1 < e.2 := by
  exact (Finset.mem_filter.mp he).2

lemma pairEdgePairs_left_ne_right {m : ℕ} {e : Fin m × Fin m}
    (he : e ∈ pairEdgePairs m) : e.1 ≠ e.2 :=
  ne_of_lt (pairEdgePairs_left_lt_right he)

/-- Weighted finite pattern count:

`E_x (∏_i v(x_i)) (∏_{ij ∈ E} h(x_i - x_j))`.

In Route A, `v` will be `1_U` and `h` will be `1_F`. -/
noncomputable def finiteWeightedPattern {p m : ℕ} [NeZero p]
    (E : Finset (Fin m × Fin m)) (h v : ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin m → ZMod p,
      (∏ i : Fin m, v (x i)) *
        ∏ e ∈ E, h (x e.1 - x e.2)

/-- Edge-indexed version of `finiteWeightedPattern`.  This is the convenient
form for the one-edge replacement/telescoping argument: different edges may
temporarily use different kernels. -/
noncomputable def finiteWeightedPatternEdge {p m : ℕ} [NeZero p]
    (E : Finset (Fin m × Fin m))
    (H : (Fin m × Fin m) → ZMod p → ℂ) (v : ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin m → ZMod p,
      (∏ i : Fin m, v (x i)) *
        ∏ e ∈ E, H e (x e.1 - x e.2)

lemma finiteWeightedPatternEdge_const {p m : ℕ} [NeZero p]
    (E : Finset (Fin m × Fin m)) (h v : ZMod p → ℂ) :
    finiteWeightedPatternEdge E (fun _ => h) v =
      finiteWeightedPattern E h v := by
  rfl

/-- Replace one edge kernel by a new kernel. -/
noncomputable def replacePairEdgeKernel {p m : ℕ}
    (H : (Fin m × Fin m) → ZMod p → ℂ) (e₀ : Fin m × Fin m)
    (g : ZMod p → ℂ) : (Fin m × Fin m) → ZMod p → ℂ :=
  fun e z => if e = e₀ then g z else H e z

lemma finiteWeightedPatternEdge_replace_sub
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {H : (Fin m × Fin m) → ZMod p → ℂ} {e₀ : Fin m × Fin m}
    (he₀ : e₀ ∈ E) (g v : ZMod p → ℂ) :
    finiteWeightedPatternEdge E (replacePairEdgeKernel H e₀ g) v -
        finiteWeightedPatternEdge E H v =
      ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin m → ZMod p,
          (∏ i : Fin m, v (x i)) *
            ((g (x e₀.1 - x e₀.2) - H e₀ (x e₀.1 - x e₀.2)) *
              ∏ e ∈ E \ {e₀}, H e (x e.1 - x e.2)) := by
  classical
  unfold finiteWeightedPatternEdge
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [Finset.prod_eq_mul_prod_diff_singleton he₀
      (fun e => replacePairEdgeKernel H e₀ g e (x e.1 - x e.2)),
    Finset.prod_eq_mul_prod_diff_singleton he₀
      (fun e => H e (x e.1 - x e.2))]
  have hprod :
      (∏ e ∈ E \ {e₀}, replacePairEdgeKernel H e₀ g e (x e.1 - x e.2)) =
        ∏ e ∈ E \ {e₀}, H e (x e.1 - x e.2) := by
    refine Finset.prod_congr rfl ?_
    intro e he
    have hne : e ≠ e₀ := by
      intro h
      exact (Finset.mem_sdiff.mp he).2 (by simp [h])
    simp [replacePairEdgeKernel, hne]
  rw [hprod]
  simp [replacePairEdgeKernel]
  ring

/-- Patch a set of edges from a base kernel family `H` to a target family `G`. -/
noncomputable def patchPairEdgeKernel {p m : ℕ}
    (H G : (Fin m × Fin m) → ZMod p → ℂ) (S : Finset (Fin m × Fin m)) :
    (Fin m × Fin m) → ZMod p → ℂ :=
  fun e z => if e ∈ S then G e z else H e z

lemma patchPairEdgeKernel_insert_eq_replace {p m : ℕ}
    (H G : (Fin m × Fin m) → ZMod p → ℂ) (S : Finset (Fin m × Fin m))
    (e₀ : Fin m × Fin m) :
    patchPairEdgeKernel H G (insert e₀ S) =
      replacePairEdgeKernel (patchPairEdgeKernel H G S) e₀ (G e₀) := by
  funext e z
  by_cases h : e = e₀
  · subst h
    simp [patchPairEdgeKernel, replacePairEdgeKernel]
  · simp [patchPairEdgeKernel, replacePairEdgeKernel, h]

lemma finiteWeightedPatternEdge_patch_empty {p m : ℕ} [NeZero p]
    (E : Finset (Fin m × Fin m))
    (H G : (Fin m × Fin m) → ZMod p → ℂ) (v : ZMod p → ℂ) :
    finiteWeightedPatternEdge E (patchPairEdgeKernel H G ∅) v =
      finiteWeightedPatternEdge E H v := by
  unfold finiteWeightedPatternEdge
  simp [patchPairEdgeKernel]

lemma finiteWeightedPatternEdge_patch_all {p m : ℕ} [NeZero p]
    (E : Finset (Fin m × Fin m))
    (H G : (Fin m × Fin m) → ZMod p → ℂ) (v : ZMod p → ℂ) :
    finiteWeightedPatternEdge E (patchPairEdgeKernel H G E) v =
      finiteWeightedPatternEdge E G v := by
  classical
  unfold finiteWeightedPatternEdge
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  congr 1
  refine Finset.prod_congr rfl ?_
  intro e he
  simp [patchPairEdgeKernel, he]

/-- Abstract finite telescoping lemma for Route A weighted pattern counts.

Once each one-edge replacement is bounded by `M`, replacing all edge kernels
on a finite edge set costs at most `|E| * M`.  Later counting-convergence work
will supply the one-edge bound from the Cayley cut norm after Fejer smoothing. -/
lemma norm_finiteWeightedPatternEdge_patch_sub_le_card_mul {p m : ℕ} [NeZero p]
    {E S : Finset (Fin m × Fin m)}
    {H G : (Fin m × Fin m) → ZMod p → ℂ} {v : ZMod p → ℂ} {M : ℝ}
    (hstep : ∀ e ∈ E, ∀ S' : Finset (Fin m × Fin m), S' ⊆ E → e ∉ S' →
      ‖finiteWeightedPatternEdge E (patchPairEdgeKernel H G (insert e S')) v -
        finiteWeightedPatternEdge E (patchPairEdgeKernel H G S') v‖ ≤ M)
    (hS : S ⊆ E) :
    ‖finiteWeightedPatternEdge E (patchPairEdgeKernel H G S) v -
        finiteWeightedPatternEdge E H v‖ ≤ (S.card : ℝ) * M := by
  classical
  refine Finset.induction_on S ?base ?step hS
  · intro _hS
    rw [finiteWeightedPatternEdge_patch_empty]
    simp
  · intro e S heS ih hInsert
    have heE : e ∈ E := hInsert (by simp)
    have hSsub : S ⊆ E := by
      intro x hx
      exact hInsert (by simp [hx])
    have hstep' := hstep e heE S hSsub heS
    have hih := ih hSsub
    have hdecomp :
        finiteWeightedPatternEdge E (patchPairEdgeKernel H G (insert e S)) v -
            finiteWeightedPatternEdge E H v =
          (finiteWeightedPatternEdge E (patchPairEdgeKernel H G (insert e S)) v -
            finiteWeightedPatternEdge E (patchPairEdgeKernel H G S) v) +
          (finiteWeightedPatternEdge E (patchPairEdgeKernel H G S) v -
            finiteWeightedPatternEdge E H v) := by
      ring
    rw [hdecomp]
    calc
      ‖(finiteWeightedPatternEdge E (patchPairEdgeKernel H G (insert e S)) v -
            finiteWeightedPatternEdge E (patchPairEdgeKernel H G S) v) +
          (finiteWeightedPatternEdge E (patchPairEdgeKernel H G S) v -
            finiteWeightedPatternEdge E H v)‖
          ≤ ‖finiteWeightedPatternEdge E (patchPairEdgeKernel H G (insert e S)) v -
            finiteWeightedPatternEdge E (patchPairEdgeKernel H G S) v‖ +
            ‖finiteWeightedPatternEdge E (patchPairEdgeKernel H G S) v -
              finiteWeightedPatternEdge E H v‖ := norm_add_le _ _
      _ ≤ M + (S.card : ℝ) * M := add_le_add hstep' hih
      _ = ((insert e S).card : ℝ) * M := by
        rw [Finset.card_insert_of_notMem heS]
        norm_num
        ring

lemma norm_finiteWeightedPatternEdge_sub_le_card_mul {p m : ℕ} [NeZero p]
    {E : Finset (Fin m × Fin m)}
    {H G : (Fin m × Fin m) → ZMod p → ℂ} {v : ZMod p → ℂ} {M : ℝ}
    (hstep : ∀ e ∈ E, ∀ S' : Finset (Fin m × Fin m), S' ⊆ E → e ∉ S' →
      ‖finiteWeightedPatternEdge E (patchPairEdgeKernel H G (insert e S')) v -
        finiteWeightedPatternEdge E (patchPairEdgeKernel H G S') v‖ ≤ M) :
    ‖finiteWeightedPatternEdge E G v - finiteWeightedPatternEdge E H v‖ ≤
      (E.card : ℝ) * M := by
  have h := norm_finiteWeightedPatternEdge_patch_sub_le_card_mul
    (E := E) (S := E) (H := H) (G := G) (v := v) (M := M)
    hstep (by intro x hx; exact hx)
  rwa [finiteWeightedPatternEdge_patch_all] at h

/-- Normalized average over a finite nonempty type. -/
noncomputable def avgFinite (ι : Type*) [Fintype ι] (f : ι → ℂ) : ℂ :=
  ((Fintype.card ι : ℂ)⁻¹) * ∑ x : ι, f x

lemma norm_avgFinite_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ι → ℂ} {M : ℝ} (hf : ∀ x, ‖f x‖ ≤ M) :
    ‖avgFinite ι f‖ ≤ M := by
  classical
  have hcard_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcard_pos_nat
  have hsum :
      ‖∑ x : ι, f x‖ ≤ (Fintype.card ι : ℝ) * M := by
    calc
      ‖∑ x : ι, f x‖ ≤ ∑ x : ι, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ι, M := by
        exact Finset.sum_le_sum (fun x _hx => hf x)
      _ = (Fintype.card ι : ℝ) * M := by simp
  unfold avgFinite
  calc
    ‖((Fintype.card ι : ℂ)⁻¹) * ∑ x : ι, f x‖
        = ‖((Fintype.card ι : ℂ)⁻¹)‖ * ‖∑ x : ι, f x‖ := norm_mul _ _
    _ ≤ ‖((Fintype.card ι : ℂ)⁻¹)‖ * ((Fintype.card ι : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = M := by
      rw [norm_inv, Complex.norm_natCast]
      field_simp [ne_of_gt hcard_pos]

/-- Normalized average over `ZMod p`.  Kept in the Route A namespace to avoid
depending on the compact-Cayley route internals. -/
noncomputable def avgZMod {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℂ :=
  ((p : ℂ)⁻¹) * ∑ x : ZMod p, f x

lemma avgZMod_sum {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (F : ι → ZMod p → ℂ) :
    avgZMod (fun x => ∑ i : ι, F i x) = ∑ i : ι, avgZMod (F i) := by
  classical
  unfold avgZMod
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

lemma avgZMod_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) :
    avgZMod (fun x => c * f x) = c * avgZMod f := by
  unfold avgZMod
  rw [← Finset.mul_sum]
  ring

lemma avgZMod_mul_const {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (c : ℂ) :
    avgZMod (fun x => f x * c) = avgZMod f * c := by
  unfold avgZMod
  rw [← Finset.sum_mul]
  ring

lemma avgZMod_comm {p : ℕ} [NeZero p] (F : ZMod p → ZMod p → ℂ) :
    avgZMod (fun x => avgZMod fun y => F x y) =
      avgZMod (fun y => avgZMod fun x => F x y) := by
  unfold avgZMod
  calc
    ((p : ℂ)⁻¹) * ∑ x : ZMod p, ((p : ℂ)⁻¹) * ∑ y : ZMod p, F x y
        = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) * ∑ x : ZMod p, ∑ y : ZMod p, F x y := by
          rw [← Finset.mul_sum]
          ring
    _ = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) * ∑ y : ZMod p, ∑ x : ZMod p, F x y := by
          rw [Finset.sum_comm]
    _ = ((p : ℂ)⁻¹) * ∑ y : ZMod p, ((p : ℂ)⁻¹) * ∑ x : ZMod p, F x y := by
          rw [← Finset.mul_sum]
          ring

lemma avgZMod_sub_right {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (y : ZMod p) :
    avgZMod (fun x => f (x - y)) = avgZMod f := by
  unfold avgZMod
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Fintype.sum_equiv (Equiv.addRight (-y)) _ _ ?_
  intro x
  simp [sub_eq_add_neg]

lemma normalizedDftFunction_eq_avgZMod {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      avgZMod fun x => ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction_eq_sum]
  rfl

lemma norm_normalizedDftFunction_le_norm_average
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (r : ZMod p) :
    ‖normalizedDftFunction f r‖ ≤
      ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ := by
  rw [normalizedDftFunction_eq_avgZMod]
  unfold avgZMod
  calc
    ‖((p : ℂ)⁻¹) *
        ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x‖
        = ‖((p : ℂ)⁻¹)‖ *
            ‖∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x‖ := by
          rw [norm_mul]
    _ ≤ ‖((p : ℂ)⁻¹)‖ *
        ∑ x : ZMod p, ‖ZMod.stdAddChar (-(x * r)) * f x‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖((p : ℂ)⁻¹)‖ * ∑ x : ZMod p, ‖f x‖ := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [norm_mul, AddChar.norm_apply, one_mul]
    _ = ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ := by
          rw [norm_inv, Complex.norm_natCast]

/-- Normalized convolution on `ZMod p`, using the same averaging convention as
`normalizedDftFunction`. -/
noncomputable def avgConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun x => avgZMod fun y => f (x - y) * g y

lemma norm_avgConvolution_indicator_le_of_kernel_norm_average_le_one
    {p : ℕ} [NeZero p] (F : Finset (ZMod p)) (K : ZMod p → ℂ)
    (hK_norm_avg : ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ ≤ 1) :
    ∀ x : ZMod p, ‖avgConvolution (indicatorC F) K x‖ ≤ 1 := by
  intro x
  unfold avgConvolution avgZMod
  have hsum :
      ‖∑ y : ZMod p, indicatorC F (x - y) * K y‖ ≤
        ∑ y : ZMod p, ‖K y‖ := by
    calc
      ‖∑ y : ZMod p, indicatorC F (x - y) * K y‖
          ≤ ∑ y : ZMod p, ‖indicatorC F (x - y) * K y‖ := norm_sum_le _ _
      _ ≤ ∑ y : ZMod p, ‖K y‖ := by
          refine Finset.sum_le_sum ?_
          intro y _hy
          rw [norm_mul]
          have hind : ‖indicatorC F (x - y)‖ ≤ 1 := by
            classical
            by_cases h : x - y ∈ F
            · simp [indicatorC, h]
            · simp [indicatorC, h]
          exact mul_le_of_le_one_left (norm_nonneg _) hind
  calc
    ‖(↑p)⁻¹ * ∑ y : ZMod p, indicatorC F (x - y) * K y‖
        = ‖((p : ℂ)⁻¹)‖ *
            ‖∑ y : ZMod p, indicatorC F (x - y) * K y‖ := by
          rw [norm_mul]
    _ ≤ ‖((p : ℂ)⁻¹)‖ * ∑ y : ZMod p, ‖K y‖ :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ := by
          rw [norm_inv, Complex.norm_natCast]
    _ ≤ 1 := hK_norm_avg

lemma kernel_norm_average_eq_one_of_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1) :
    ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ = 1 := by
  have hsum_eq :
      (∑ y : ZMod p, K y) =
        ((∑ y : ZMod p, (K y).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.re_sum]
    · simp [Complex.im_sum, hK_im]
  have havg_re :
      ((p : ℝ)⁻¹) * ∑ y : ZMod p, (K y).re = 1 := by
    have h := congrArg Complex.re hK_avg
    unfold avgZMod at h
    rw [hsum_eq] at h
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv] at h
    simpa [Complex.ofReal_mul] using h
  calc
    ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖
        = ((p : ℝ)⁻¹) * ∑ y : ZMod p, (K y).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro y _hy
          have hnorm := (Complex.abs_re_eq_norm).mpr (hK_im y)
          rw [← hnorm, abs_of_nonneg (hK_nonneg y)]
    _ = 1 := havg_re

lemma norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1)
    (r : ZMod p) :
    ‖normalizedDftFunction K r‖ ≤ 1 := by
  exact (norm_normalizedDftFunction_le_norm_average K r).trans_eq
    (kernel_norm_average_eq_one_of_real_nonneg_avg_one K hK_nonneg hK_im hK_avg)

lemma norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (F : Finset (ZMod p)) (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1) :
    ∀ x : ZMod p, ‖avgConvolution (indicatorC F) K x‖ ≤ 1 :=
  norm_avgConvolution_indicator_le_of_kernel_norm_average_le_one F K
    ((kernel_norm_average_eq_one_of_real_nonneg_avg_one K hK_nonneg hK_im hK_avg).le)

lemma stdAddChar_neg_mul_split_sub
    {p : ℕ} [NeZero p] (x y r : ZMod p) :
    ZMod.stdAddChar (-(x * r)) =
      ZMod.stdAddChar (-((x - y) * r)) *
        ZMod.stdAddChar (-(y * r)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

/-- The normalized DFT sends normalized convolution to pointwise
multiplication. This is the finite Fourier identity used by Fejer smoothing. -/
lemma normalizedDftFunction_avgConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (avgConvolution f g) r =
      normalizedDftFunction f r * normalizedDftFunction g r := by
  classical
  rw [normalizedDftFunction_eq_avgZMod]
  unfold avgConvolution
  calc
    avgZMod
        (fun x : ZMod p =>
          ZMod.stdAddChar (-(x * r)) *
            avgZMod (fun y : ZMod p => f (x - y) * g y))
        =
      avgZMod
        (fun x : ZMod p =>
          avgZMod
            (fun y : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))) := by
          congr 1
          funext x
          rw [avgZMod_const_mul]
    _ =
      avgZMod
        (fun y : ZMod p =>
          avgZMod
            (fun x : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))) := by
          exact avgZMod_comm
            (fun x y : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))
    _ =
      avgZMod
        (fun y : ZMod p =>
          normalizedDftFunction f r *
            (ZMod.stdAddChar (-(y * r)) * g y)) := by
          congr 1
          funext y
          calc
            avgZMod
                (fun x : ZMod p =>
                  ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))
                =
              avgZMod
                (fun x : ZMod p =>
                  (ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) *
                    (ZMod.stdAddChar (-(y * r)) * g y)) := by
                congr 1
                funext x
                rw [stdAddChar_neg_mul_split_sub x y r]
                ring
            _ =
              avgZMod
                (fun x : ZMod p =>
                  ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) *
                (ZMod.stdAddChar (-(y * r)) * g y) := by
                rw [avgZMod_mul_const]
            _ =
              normalizedDftFunction f r *
                (ZMod.stdAddChar (-(y * r)) * g y) := by
                have hshift :
                    avgZMod
                        (fun x : ZMod p =>
                          ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) =
                      normalizedDftFunction f r := by
                  rw [avgZMod_sub_right
                    (fun z : ZMod p => ZMod.stdAddChar (-(z * r)) * f z) y]
                  rw [← normalizedDftFunction_eq_avgZMod]
                rw [hshift]
    _ = normalizedDftFunction f r * normalizedDftFunction g r := by
          rw [avgZMod_const_mul]
          rw [← normalizedDftFunction_eq_avgZMod]

/-- Route A Cayley cut functional for the single replaced edge. -/
noncomputable def weightedCayleyCutFunctional {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) : ℂ :=
  avgZMod fun x => avgZMod fun y => a (x - y) * φ x * ψ y

/-- Abstract cut-bound interface used by the weighted one-edge replacement
lemma. -/
def WeightedCayleyCutBound {p : ℕ} [NeZero p]
    (a : ZMod p → ℂ) (M : ℝ) : Prop :=
  ∀ φ ψ : ZMod p → ℂ,
    (∀ x, ‖φ x‖ ≤ 1) →
    (∀ y, ‖ψ y‖ ≤ 1) →
    ‖weightedCayleyCutFunctional a φ ψ‖ ≤ M

/-- Spectral coefficient bound for a Route A weighted Cayley kernel. -/
def WeightedSpectralBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) : Prop :=
  ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M

/-- The left test Fourier factor appearing after expanding the weighted Cayley
kernel. -/
noncomputable def weightedLeftFourierTest {p : ℕ} [NeZero p]
    (φ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  avgZMod fun x => ZMod.stdAddChar (r * x) * φ x

/-- The right test Fourier factor appearing after expanding the weighted Cayley
kernel. -/
noncomputable def weightedRightFourierTest {p : ℕ} [NeZero p]
    (ψ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  avgZMod fun y => ZMod.stdAddChar (-(r * y)) * ψ y

lemma weightedRightFourierTest_eq_normalizedDftFunction {p : ℕ} [NeZero p]
    (ψ : ZMod p → ℂ) (r : ZMod p) :
    weightedRightFourierTest ψ r = normalizedDftFunction ψ r := by
  dsimp [weightedRightFourierTest, avgZMod]
  rw [normalizedDftFunction_eq_sum (p := p) ψ r]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [mul_comm r y]

lemma weightedLeftFourierTest_eq_normalizedDftFunction_neg {p : ℕ} [NeZero p]
    (φ : ZMod p → ℂ) (r : ZMod p) :
    weightedLeftFourierTest φ r = normalizedDftFunction φ (-r) := by
  dsimp [weightedLeftFourierTest, avgZMod]
  rw [normalizedDftFunction_eq_sum (p := p) φ (-r)]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro x _
  congr 1
  simp [mul_comm]

lemma sum_sq_norm_weightedRightFourierTest_eq_normalizedDftFunction
    {p : ℕ} [NeZero p] (ψ : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖weightedRightFourierTest ψ r‖ ^ 2) =
      ∑ r : ZMod p, ‖normalizedDftFunction ψ r‖ ^ 2 := by
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [weightedRightFourierTest_eq_normalizedDftFunction]

lemma sum_sq_norm_weightedLeftFourierTest_eq_normalizedDftFunction
    {p : ℕ} [NeZero p] (φ : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖weightedLeftFourierTest φ r‖ ^ 2) =
      ∑ r : ZMod p, ‖normalizedDftFunction φ r‖ ^ 2 := by
  classical
  calc
    (∑ r : ZMod p, ‖weightedLeftFourierTest φ r‖ ^ 2) =
        ∑ r : ZMod p, ‖normalizedDftFunction φ (-r)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [weightedLeftFourierTest_eq_normalizedDftFunction_neg]
    _ = ∑ r : ZMod p, ‖normalizedDftFunction φ r‖ ^ 2 := by
          refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
          intro r
          simp

lemma star_stdAddChar_neg_mul {p : ℕ} [NeZero p] (x r : ZMod p) :
    (starRingEnd ℂ) (ZMod.stdAddChar (-(x * r))) =
      ZMod.stdAddChar (x * r) := by
  have h := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (x * r)
  simp [h]

lemma star_normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    (starRingEnd ℂ) (normalizedDftFunction f r) =
      ((p : ℂ)⁻¹) *
        ∑ x : ZMod p, ZMod.stdAddChar (x * r) * (starRingEnd ℂ) (f x) := by
  rw [normalizedDftFunction_eq_sum]
  simp [map_sum, star_stdAddChar_neg_mul, mul_comm]

lemma avg_stdAddChar_mul_star_eq_star_normalizedDftFunction
    {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (r : ZMod p) :
    avgZMod (fun x => ZMod.stdAddChar (r * x) * (starRingEnd ℂ) (g x)) =
      (starRingEnd ℂ) (normalizedDftFunction g r) := by
  rw [star_normalizedDftFunction, avgZMod]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [mul_comm r x]

/-- Parseval cross identity in normalized-average form. -/
lemma avg_mul_star_eq_sum_normalizedDftFunction {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    avgZMod (fun x => f x * (starRingEnd ℂ) (g x)) =
      ∑ r : ZMod p,
        normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction g r) := by
  classical
  calc
    avgZMod (fun x => f x * (starRingEnd ℂ) (g x)) =
        avgZMod
          (fun x =>
            (∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r) *
              (starRingEnd ℂ) (g x)) := by
          congr 1
          funext x
          rw [← function_eq_sum_normalizedDftFunction (p := p) f x]
    _ = avgZMod
          (fun x =>
            ∑ r : ZMod p,
              normalizedDftFunction f r *
                (ZMod.stdAddChar (r * x) * (starRingEnd ℂ) (g x))) := by
          congr 1
          funext x
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro r _
          ring
    _ = ∑ r : ZMod p,
        normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction g r) := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul, avg_stdAddChar_mul_star_eq_star_normalizedDftFunction]

/-- Parseval in the normalized convention used here. -/
lemma sum_sq_norm_normalizedDftFunction_eq_avg
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2) =
      ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  have hcomplex :
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, (‖f x‖ : ℂ) ^ 2 =
        ∑ r : ZMod p, (‖normalizedDftFunction f r‖ : ℂ) ^ 2 := by
    calc
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, (‖f x‖ : ℂ) ^ 2 =
          avgZMod (fun x => f x * (starRingEnd ℂ) (f x)) := by
            unfold avgZMod
            apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [← Complex.mul_conj']
      _ = ∑ r : ZMod p,
          normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction f r) :=
            avg_mul_star_eq_sum_normalizedDftFunction f f
      _ = ∑ r : ZMod p, (‖normalizedDftFunction f r‖ : ℂ) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [Complex.mul_conj']
  simpa [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_natCast] using hcomplex.symm

lemma sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {f : ZMod p → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    (∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2) ≤ 1 := by
  classical
  rw [sum_sq_norm_normalizedDftFunction_eq_avg]
  have hsum : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ) := by
    calc
      (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ ∑ _x : ZMod p, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro x _
        have hx_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have hx_le : ‖f x‖ ^ 2 ≤ (1 : ℝ) := by
          nlinarith [hf x]
        exact hx_le
      _ = (p : ℝ) := by simp [ZMod.card]
  have hp_nonneg : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  calc
    ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ ^ 2
        ≤ ((p : ℝ)⁻¹) * (p : ℝ) := mul_le_mul_of_nonneg_left hsum hp_nonneg
    _ = 1 := inv_mul_cancel₀ hp_ne

lemma sum_sq_norm_weightedRightFourierTest_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {ψ : ZMod p → ℂ}
    (hψ : ∀ y, ‖ψ y‖ ≤ 1) :
    (∑ r : ZMod p, ‖weightedRightFourierTest ψ r‖ ^ 2) ≤ 1 := by
  rw [sum_sq_norm_weightedRightFourierTest_eq_normalizedDftFunction]
  exact sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hψ

lemma sum_sq_norm_weightedLeftFourierTest_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {φ : ZMod p → ℂ}
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    (∑ r : ZMod p, ‖weightedLeftFourierTest φ r‖ ^ 2) ≤ 1 := by
  rw [sum_sq_norm_weightedLeftFourierTest_eq_normalizedDftFunction]
  exact sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hφ

lemma stdAddChar_mul_sub {p : ℕ} [NeZero p] (r x y : ZMod p) :
    ZMod.stdAddChar (r * (x - y)) =
      ZMod.stdAddChar (r * x) * ZMod.stdAddChar (-(r * y)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

/-- Fourier inversion applied to the weighted Cayley kernel `a(x-y)`, in the
exact factorized form used by the spectral-cut argument. -/
lemma weightedCayleyKernel_eq_fourier_sum {p : ℕ} [NeZero p]
    (a : ZMod p → ℂ) (x y : ZMod p) :
    a (x - y) =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) *
          ZMod.stdAddChar (-(r * y)) := by
  calc
    a (x - y) =
        ∑ r : ZMod p, ZMod.stdAddChar (r * (x - y)) *
          normalizedDftFunction a r := by
          exact function_eq_sum_normalizedDftFunction (p := p) a (x - y)
    _ = ∑ r : ZMod p,
        normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) *
          ZMod.stdAddChar (-(r * y)) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [stdAddChar_mul_sub]
          ring

lemma weightedCayleyKernel_mul_tests_eq_fourier_sum {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) (x y : ZMod p) :
    a (x - y) * φ x * ψ y =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          (ZMod.stdAddChar (r * x) * φ x) *
          (ZMod.stdAddChar (-(r * y)) * ψ y) := by
  rw [weightedCayleyKernel_eq_fourier_sum (p := p) a x y]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

/-- The weighted double-average Cayley cut functional factors through the
normalized Fourier coefficients of the kernel and the two test Fourier factors. -/
lemma weightedCayleyCutFunctional_eq_fourier_sum {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    weightedCayleyCutFunctional a φ ψ =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          weightedLeftFourierTest φ r * weightedRightFourierTest ψ r := by
  classical
  unfold weightedCayleyCutFunctional
  simp_rw [weightedCayleyKernel_mul_tests_eq_fourier_sum (p := p) a φ ψ]
  calc
    avgZMod
        (fun x : ZMod p =>
          avgZMod
            (fun y : ZMod p =>
              ∑ r : ZMod p,
                normalizedDftFunction a r *
                  (ZMod.stdAddChar (r * x) * φ x) *
                  (ZMod.stdAddChar (-(r * y)) * ψ y))) =
        avgZMod
          (fun x : ZMod p =>
            ∑ r : ZMod p,
              normalizedDftFunction a r *
                (ZMod.stdAddChar (r * x) * φ x) *
                weightedRightFourierTest ψ r) := by
          congr 1
          funext x
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul]
          simp [weightedRightFourierTest, mul_assoc]
    _ = ∑ r : ZMod p,
        normalizedDftFunction a r *
          weightedLeftFourierTest φ r * weightedRightFourierTest ψ r := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_mul_const, avgZMod_const_mul]
          simp [weightedLeftFourierTest, mul_assoc]

lemma norm_weightedCayleyCutFunctional_le_fourier_l1 {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    ‖weightedCayleyCutFunctional a φ ψ‖ ≤
      ∑ r : ZMod p,
        ‖normalizedDftFunction a r‖ * ‖weightedLeftFourierTest φ r‖ *
          ‖weightedRightFourierTest ψ r‖ := by
  rw [weightedCayleyCutFunctional_eq_fourier_sum]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro r _
  rw [norm_mul, norm_mul]

lemma norm_weightedCayleyCutFunctional_le_spectral_of_fourier_l2
    {p : ℕ} [NeZero p] (a φ ψ : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M)
    (hMnonneg : 0 ≤ M)
    (hφ2 : (∑ r : ZMod p, ‖weightedLeftFourierTest φ r‖ ^ 2) ≤ 1)
    (hψ2 : (∑ r : ZMod p, ‖weightedRightFourierTest ψ r‖ ^ 2) ≤ 1) :
    ‖weightedCayleyCutFunctional a φ ψ‖ ≤ M := by
  classical
  let L : ZMod p → ℝ := fun r => ‖weightedLeftFourierTest φ r‖
  let R : ZMod p → ℝ := fun r => ‖weightedRightFourierTest ψ r‖
  have h_l1 :
      ‖weightedCayleyCutFunctional a φ ψ‖ ≤ ∑ r : ZMod p,
        ‖normalizedDftFunction a r‖ * L r * R r := by
    simpa [L, R, mul_assoc] using norm_weightedCayleyCutFunctional_le_fourier_l1 a φ ψ
  have h_by_M :
      ∑ r : ZMod p, ‖normalizedDftFunction a r‖ * L r * R r ≤
        ∑ r : ZMod p, M * (L r * R r) := by
    refine Finset.sum_le_sum ?_
    intro r _
    have hLR : 0 ≤ L r * R r := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖normalizedDftFunction a r‖ * L r * R r =
          ‖normalizedDftFunction a r‖ * (L r * R r) := by ring
      _ ≤ M * (L r * R r) := mul_le_mul_of_nonneg_right (hM r) hLR
  have hcs :
      ∑ r : ZMod p, L r * R r ≤
        Real.sqrt (∑ r : ZMod p, L r ^ 2) *
          Real.sqrt (∑ r : ZMod p, R r ^ 2) := by
    simpa [L, R] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ZMod p)) L R)
  have hsqrtL : Real.sqrt (∑ r : ZMod p, L r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa [L] using hφ2
  have hsqrtR : Real.sqrt (∑ r : ZMod p, R r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa [R] using hψ2
  have hsqrt_nonneg_L : 0 ≤ Real.sqrt (∑ r : ZMod p, L r ^ 2) := Real.sqrt_nonneg _
  have hsqrt_nonneg_R : 0 ≤ Real.sqrt (∑ r : ZMod p, R r ^ 2) := Real.sqrt_nonneg _
  have hprod :
      Real.sqrt (∑ r : ZMod p, L r ^ 2) *
          Real.sqrt (∑ r : ZMod p, R r ^ 2) ≤ 1 := by
    nlinarith
  have hsumLR : ∑ r : ZMod p, L r * R r ≤ 1 := hcs.trans hprod
  calc
    ‖weightedCayleyCutFunctional a φ ψ‖
        ≤ ∑ r : ZMod p, ‖normalizedDftFunction a r‖ * L r * R r := h_l1
    _ ≤ ∑ r : ZMod p, M * (L r * R r) := h_by_M
    _ = M * ∑ r : ZMod p, L r * R r := by rw [Finset.mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hsumLR hMnonneg
    _ = M := by ring

lemma norm_weightedCayleyCutFunctional_le_spectral
    {p : ℕ} [NeZero p] (a φ ψ : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M)
    (hMnonneg : 0 ≤ M)
    (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hψ : ∀ y, ‖ψ y‖ ≤ 1) :
    ‖weightedCayleyCutFunctional a φ ψ‖ ≤ M := by
  exact norm_weightedCayleyCutFunctional_le_spectral_of_fourier_l2 a φ ψ hM hMnonneg
    (sum_sq_norm_weightedLeftFourierTest_le_one_of_norm_le_one hφ)
    (sum_sq_norm_weightedRightFourierTest_le_one_of_norm_le_one hψ)

/-- Route A finite spectral cut-norm control in predicate form. -/
theorem weightedCayleyCutBound_of_spectralBound
    {p : ℕ} [NeZero p] (a : ZMod p → ℂ) {M : ℝ}
    (hMnonneg : 0 ≤ M) (hM : WeightedSpectralBound a M) :
    WeightedCayleyCutBound a M := by
  intro φ ψ hφ hψ
  exact norm_weightedCayleyCutFunctional_le_spectral a φ ψ hM hMnonneg hφ hψ

lemma norm_avgFinite_weightedCayleyCutFunctional_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} [NeZero p] {a : ZMod p → ℂ} {M : ℝ}
    (hcut : WeightedCayleyCutBound a M)
    (φ ψ : ι → ZMod p → ℂ)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖avgFinite ι (fun t => weightedCayleyCutFunctional a (φ t) (ψ t))‖ ≤ M := by
  exact norm_avgFinite_le (fun t => hcut (φ t) (ψ t) (hφ t) (hψ t))

/-- One-edge replacement bound once the replacement difference has been
reindexed/factored as an average of bounded Cayley cut functionals. -/
lemma norm_finiteWeightedPatternEdge_replace_sub_le_of_cut_representation
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {H : (Fin m × Fin m) → ZMod p → ℂ} {e₀ : Fin m × Fin m}
    {g v : ZMod p → ℂ} {M : ℝ}
    (φ ψ : ι → ZMod p → ℂ)
    (hrep :
      finiteWeightedPatternEdge E (replacePairEdgeKernel H e₀ g) v -
          finiteWeightedPatternEdge E H v =
        avgFinite ι
          (fun t => weightedCayleyCutFunctional
            (fun z => g z - H e₀ z) (φ t) (ψ t)))
    (hcut : WeightedCayleyCutBound (fun z => g z - H e₀ z) M)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖finiteWeightedPatternEdge E (replacePairEdgeKernel H e₀ g) v -
        finiteWeightedPatternEdge E H v‖ ≤ M := by
  rw [hrep]
  exact norm_avgFinite_weightedCayleyCutFunctional_le hcut φ ψ hφ hψ

/-! ## Frozen-coordinate factorization for one-edge replacement -/

/-- Indices other than the two endpoints of a chosen edge. -/
def PairEdgeRest {m : ℕ} (e₀ : Fin m × Fin m) : Type :=
  {k : Fin m // k ≠ e₀.1 ∧ k ≠ e₀.2}

instance instFintypePairEdgeRest {m : ℕ} (e₀ : Fin m × Fin m) :
    Fintype (PairEdgeRest e₀) := by
  classical
  unfold PairEdgeRest
  infer_instance

noncomputable instance instDecidableEqPairEdgeRest {m : ℕ} (e₀ : Fin m × Fin m) :
    DecidableEq (PairEdgeRest e₀) := by
  classical
  infer_instance

/-- Assignments to all non-endpoint coordinates of a chosen edge. -/
abbrev PairEdgeRestAssignment (p m : ℕ) (e₀ : Fin m × Fin m) : Type :=
  PairEdgeRest e₀ → ZMod p

noncomputable instance instFintypePairEdgeRestAssignment {p m : ℕ} [NeZero p]
    (e₀ : Fin m × Fin m) : Fintype (PairEdgeRestAssignment p m e₀) := by
  unfold PairEdgeRestAssignment
  infer_instance

/-- Extend a frozen assignment on the remaining vertices by assigning `u` and
`w` to the two endpoints of the chosen edge. -/
noncomputable def extendPairEdgeTuple {p m : ℕ} (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) : Fin m → ZMod p :=
  fun k =>
    if h1 : k = e₀.1 then u
    else if h2 : k = e₀.2 then w
    else r ⟨k, h1, h2⟩

@[simp] lemma extendPairEdgeTuple_left {p m : ℕ} (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    extendPairEdgeTuple e₀ r u w e₀.1 = u := by
  simp [extendPairEdgeTuple]

@[simp] lemma extendPairEdgeTuple_right {p m : ℕ} {e₀ : Fin m × Fin m}
    (hne : e₀.2 ≠ e₀.1) (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    extendPairEdgeTuple e₀ r u w e₀.2 = w := by
  simp [extendPairEdgeTuple, hne]

lemma extendPairEdgeTuple_rest {p m : ℕ} (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p)
    {k : Fin m} (h1 : k ≠ e₀.1) (h2 : k ≠ e₀.2) :
    extendPairEdgeTuple e₀ r u w k = r ⟨k, h1, h2⟩ := by
  simp [extendPairEdgeTuple, h1, h2]

lemma extendPairEdgeTuple_edge_diff {p m : ℕ} {e₀ : Fin m × Fin m}
    (hne : e₀.1 ≠ e₀.2) (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    extendPairEdgeTuple e₀ r u w e₀.1 - extendPairEdgeTuple e₀ r u w e₀.2 = u - w := by
  simp [extendPairEdgeTuple_right (e₀ := e₀) (show e₀.2 ≠ e₀.1 from hne.symm)]

/-- Reindex all tuples by a chosen edge's two endpoint values and the
assignment on the remaining vertices. -/
noncomputable def pairEdgeTupleEquiv {p m : ℕ} (e₀ : Fin m × Fin m)
    (hne : e₀.1 ≠ e₀.2) :
    (Fin m → ZMod p) ≃ (PairEdgeRestAssignment p m e₀ × ZMod p × ZMod p) where
  toFun x := (fun k => x k.1, x e₀.1, x e₀.2)
  invFun q := extendPairEdgeTuple e₀ q.1 q.2.1 q.2.2
  left_inv x := by
    funext k
    by_cases h1 : k = e₀.1
    · subst h1
      simp [extendPairEdgeTuple]
    · by_cases h2 : k = e₀.2
      · subst h2
        simp [extendPairEdgeTuple, hne.symm]
      · simp [extendPairEdgeTuple, h1, h2]
  right_inv q := by
    rcases q with ⟨r, u, w⟩
    ext k
    · exact extendPairEdgeTuple_rest e₀ r u w k.property.1 k.property.2
    · simp [extendPairEdgeTuple]
    · simp [extendPairEdgeTuple, hne.symm]

lemma sum_pairEdgeTupleEquiv {p m : ℕ} [NeZero p] {e₀ : Fin m × Fin m}
    (hne : e₀.1 ≠ e₀.2) (f : (Fin m → ZMod p) → ℂ) :
    (∑ x : Fin m → ZMod p, f x) =
      ∑ q : PairEdgeRestAssignment p m e₀ × ZMod p × ZMod p,
        f (extendPairEdgeTuple e₀ q.1 q.2.1 q.2.2) := by
  simpa [pairEdgeTupleEquiv] using ((pairEdgeTupleEquiv (p := p) e₀ hne).symm.sum_comp f).symm

lemma pairEdgeTuple_normalized_sum_eq_avgFinite_avgZMod
    {p m : ℕ} [NeZero p] {e₀ : Fin m × Fin m} (hne : e₀.1 ≠ e₀.2)
    (K : PairEdgeRestAssignment p m e₀ → ZMod p → ZMod p → ℂ) :
    ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
      ∑ q : PairEdgeRestAssignment p m e₀ × ZMod p × ZMod p,
        K q.1 q.2.1 q.2.2 =
    avgFinite (PairEdgeRestAssignment p m e₀)
      (fun r => avgZMod fun u => avgZMod fun w => K r u w) := by
  classical
  have hcard_nat :
      Fintype.card (Fin m → ZMod p) =
        Fintype.card (PairEdgeRestAssignment p m e₀) * p * p := by
    calc
      Fintype.card (Fin m → ZMod p) =
          Fintype.card (PairEdgeRestAssignment p m e₀ × ZMod p × ZMod p) :=
            Fintype.card_congr (pairEdgeTupleEquiv (p := p) e₀ hne)
      _ = Fintype.card (PairEdgeRestAssignment p m e₀) * p * p := by
            simp [Fintype.card_prod, ZMod.card, mul_assoc]
  have hcard_complex :
      (Fintype.card (Fin m → ZMod p) : ℂ) =
        (Fintype.card (PairEdgeRestAssignment p m e₀) : ℂ) * (p : ℂ) * (p : ℂ) := by
    exact_mod_cast hcard_nat
  unfold avgFinite avgZMod
  rw [hcard_complex]
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  ring

lemma finiteWeightedPatternEdge_replace_sub_reindex
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {H : (Fin m × Fin m) → ZMod p → ℂ} {e₀ : Fin m × Fin m}
    (he₀ : e₀ ∈ E) (hne : e₀.1 ≠ e₀.2) (g v : ZMod p → ℂ) :
    finiteWeightedPatternEdge E (replacePairEdgeKernel H e₀ g) v -
        finiteWeightedPatternEdge E H v =
      ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
        ∑ q : PairEdgeRestAssignment p m e₀ × ZMod p × ZMod p,
          (∏ i : Fin m, v (extendPairEdgeTuple e₀ q.1 q.2.1 q.2.2 i)) *
            ((g (q.2.1 - q.2.2) - H e₀ (q.2.1 - q.2.2)) *
              ∏ e ∈ E \ {e₀},
                H e (extendPairEdgeTuple e₀ q.1 q.2.1 q.2.2 e.1 -
                  extendPairEdgeTuple e₀ q.1 q.2.1 q.2.2 e.2)) := by
  rw [finiteWeightedPatternEdge_replace_sub he₀]
  congr 1
  rw [sum_pairEdgeTupleEquiv hne]
  refine Finset.sum_congr rfl ?_
  intro q _hq
  rw [extendPairEdgeTuple_edge_diff hne]

lemma finiteWeightedPatternEdge_replace_sub_eq_avgFinite_weightedCayleyCutFunctional_of_factorization
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {H : (Fin m × Fin m) → ZMod p → ℂ} {e₀ : Fin m × Fin m}
    (he₀ : e₀ ∈ E) (hne : e₀.1 ≠ e₀.2) (g v : ZMod p → ℂ)
    (φ ψ : PairEdgeRestAssignment p m e₀ → ZMod p → ℂ)
    (hprod : ∀ r u w,
      (∏ i : Fin m, v (extendPairEdgeTuple e₀ r u w i)) *
        (∏ e ∈ E \ {e₀},
          H e (extendPairEdgeTuple e₀ r u w e.1 -
            extendPairEdgeTuple e₀ r u w e.2)) =
          φ r u * ψ r w) :
    finiteWeightedPatternEdge E (replacePairEdgeKernel H e₀ g) v -
        finiteWeightedPatternEdge E H v =
      avgFinite (PairEdgeRestAssignment p m e₀)
        (fun r => weightedCayleyCutFunctional
          (fun z => g z - H e₀ z) (φ r) (ψ r)) := by
  rw [finiteWeightedPatternEdge_replace_sub_reindex he₀ hne]
  rw [pairEdgeTuple_normalized_sum_eq_avgFinite_avgZMod
    (p := p) (m := m) (e₀ := e₀) hne
    (fun r u w =>
      (∏ i : Fin m, v (extendPairEdgeTuple e₀ r u w i)) *
        ((g (u - w) - H e₀ (u - w)) *
          ∏ e ∈ E \ {e₀},
            H e (extendPairEdgeTuple e₀ r u w e.1 -
              extendPairEdgeTuple e₀ r u w e.2)))]
  unfold weightedCayleyCutFunctional
  congr 1
  funext r
  congr 1
  funext u
  congr 1
  funext w
  calc
    (∏ i : Fin m, v (extendPairEdgeTuple e₀ r u w i)) *
        ((g (u - w) - H e₀ (u - w)) *
          ∏ e ∈ E \ {e₀},
            H e (extendPairEdgeTuple e₀ r u w e.1 -
              extendPairEdgeTuple e₀ r u w e.2))
        = (g (u - w) - H e₀ (u - w)) *
            ((∏ i : Fin m, v (extendPairEdgeTuple e₀ r u w i)) *
              ∏ e ∈ E \ {e₀},
                H e (extendPairEdgeTuple e₀ r u w e.1 -
                  extendPairEdgeTuple e₀ r u w e.2)) := by
          ring
    _ = (g (u - w) - H e₀ (u - w)) * (φ r u * ψ r w) := by
          rw [hprod]
    _ = (fun z => g z - H e₀ z) (u - w) * φ r u * ψ r w := by
          ring

/-- An edge is incident to a vertex. -/
def pairEdgeUsesVertex {m : ℕ} (e : Fin m × Fin m) (i : Fin m) : Prop :=
  e.1 = i ∨ e.2 = i

instance instDecidablePairEdgeUsesVertex {m : ℕ} (e : Fin m × Fin m) (i : Fin m) :
    Decidable (pairEdgeUsesVertex e i) := by
  unfold pairEdgeUsesVertex
  infer_instance

/-- The remaining edges after removing the edge currently being replaced. -/
def remainingPairEdges {m : ℕ} (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m) :
    Finset (Fin m × Fin m) :=
  E \ {e₀}

def leftPairEdges {m : ℕ} (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m) :
    Finset (Fin m × Fin m) :=
  (remainingPairEdges E e₀).filter (fun e => pairEdgeUsesVertex e e₀.1)

def rightPairEdges {m : ℕ} (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m) :
    Finset (Fin m × Fin m) :=
  (remainingPairEdges E e₀).filter
    (fun e => ¬ pairEdgeUsesVertex e e₀.1 ∧ pairEdgeUsesVertex e e₀.2)

def constantPairEdges {m : ℕ} (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m) :
    Finset (Fin m × Fin m) :=
  (remainingPairEdges E e₀).filter
    (fun e => ¬ pairEdgeUsesVertex e e₀.1 ∧ ¬ pairEdgeUsesVertex e e₀.2)

lemma pairEdge_not_uses_both_endpoints_of_mem_remaining {m : ℕ}
    {E : Finset (Fin m × Fin m)} {e₀ e : Fin m × Fin m}
    (hE : E ⊆ pairEdgePairs m) (he₀ : e₀ ∈ pairEdgePairs m)
    (he : e ∈ remainingPairEdges E e₀)
    (hleft : pairEdgeUsesVertex e e₀.1) (hright : pairEdgeUsesVertex e e₀.2) :
    False := by
  have he_pair : e ∈ pairEdgePairs m := hE (Finset.mem_sdiff.mp he).1
  have hne_single : e ∉ ({e₀} : Finset (Fin m × Fin m)) := (Finset.mem_sdiff.mp he).2
  have hlt_e : e.1 < e.2 := pairEdgePairs_left_lt_right he_pair
  have hlt_e₀ : e₀.1 < e₀.2 := pairEdgePairs_left_lt_right he₀
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · have h_eq : e₀.1 = e₀.2 := hleft.symm.trans hright
    exact (ne_of_lt hlt_e₀) h_eq
  · have h_eq : e = e₀ := Prod.ext hleft hright
    exact hne_single (by simp [h_eq])
  · have hbad : e₀.2 < e₀.1 := by simpa [hleft, hright] using hlt_e
    exact (not_lt_of_ge (le_of_lt hlt_e₀)) hbad
  · have h_eq : e₀.1 = e₀.2 := hleft.symm.trans hright
    exact (ne_of_lt hlt_e₀) h_eq

lemma extendPairEdgeTuple_eq_of_same_left {p m : ℕ} {e₀ : Fin m × Fin m}
    (r : PairEdgeRestAssignment p m e₀) (u w w' : ZMod p) {k : Fin m}
    (h2 : k ≠ e₀.2) :
    extendPairEdgeTuple e₀ r u w k = extendPairEdgeTuple e₀ r u w' k := by
  by_cases h1 : k = e₀.1
  · subst h1
    simp [extendPairEdgeTuple]
  · rw [extendPairEdgeTuple_rest e₀ r u w h1 h2,
      extendPairEdgeTuple_rest e₀ r u w' h1 h2]

lemma extendPairEdgeTuple_eq_of_same_right {p m : ℕ} {e₀ : Fin m × Fin m}
    (r : PairEdgeRestAssignment p m e₀) (u u' w : ZMod p) {k : Fin m}
    (h1 : k ≠ e₀.1) :
    extendPairEdgeTuple e₀ r u w k = extendPairEdgeTuple e₀ r u' w k := by
  by_cases h2 : k = e₀.2
  · subst h2
    simp [extendPairEdgeTuple, h1]
  · rw [extendPairEdgeTuple_rest e₀ r u w h1 h2,
      extendPairEdgeTuple_rest e₀ r u' w h1 h2]

lemma extendPairEdgeTuple_eq_of_not_endpoints {p m : ℕ} {e₀ : Fin m × Fin m}
    (r : PairEdgeRestAssignment p m e₀) (u w u' w' : ZMod p) {k : Fin m}
    (h1 : k ≠ e₀.1) (h2 : k ≠ e₀.2) :
    extendPairEdgeTuple e₀ r u w k = extendPairEdgeTuple e₀ r u' w' k := by
  rw [extendPairEdgeTuple_rest e₀ r u w h1 h2,
    extendPairEdgeTuple_rest e₀ r u' w' h1 h2]

noncomputable def remainingLeftPairTest {p m : ℕ} [NeZero p]
    (H : (Fin m × Fin m) → ZMod p → ℂ) (E : Finset (Fin m × Fin m))
    (e₀ : Fin m × Fin m) (r : PairEdgeRestAssignment p m e₀) (u : ZMod p) : ℂ :=
  ∏ e ∈ leftPairEdges E e₀,
    H e (extendPairEdgeTuple e₀ r u 0 e.1 - extendPairEdgeTuple e₀ r u 0 e.2)

noncomputable def remainingRightPairTest {p m : ℕ} [NeZero p]
    (H : (Fin m × Fin m) → ZMod p → ℂ) (E : Finset (Fin m × Fin m))
    (e₀ : Fin m × Fin m) (r : PairEdgeRestAssignment p m e₀) (w : ZMod p) : ℂ :=
  ∏ e ∈ rightPairEdges E e₀,
    H e (extendPairEdgeTuple e₀ r 0 w e.1 - extendPairEdgeTuple e₀ r 0 w e.2)

noncomputable def remainingConstPairFactor {p m : ℕ} [NeZero p]
    (H : (Fin m × Fin m) → ZMod p → ℂ) (E : Finset (Fin m × Fin m))
    (e₀ : Fin m × Fin m) (r : PairEdgeRestAssignment p m e₀) : ℂ :=
  ∏ e ∈ constantPairEdges E e₀,
    H e (extendPairEdgeTuple e₀ r 0 0 e.1 - extendPairEdgeTuple e₀ r 0 0 e.2)

lemma prod_remainingPairEdges_split {m : ℕ}
    (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m)
    (K : Fin m × Fin m → ℂ) :
    (∏ e ∈ remainingPairEdges E e₀, K e) =
      (∏ e ∈ leftPairEdges E e₀, K e) *
        (∏ e ∈ rightPairEdges E e₀, K e) *
          (∏ e ∈ constantPairEdges E e₀, K e) := by
  classical
  unfold leftPairEdges rightPairEdges constantPairEdges
  let s := remainingPairEdges E e₀
  let P : Fin m × Fin m → Prop := fun e => pairEdgeUsesVertex e e₀.1
  let Q : Fin m × Fin m → Prop := fun e => pairEdgeUsesVertex e e₀.2
  have h1 := Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := K)
  have h2 := Finset.prod_filter_mul_prod_filter_not
    (s := s.filter (fun e => ¬ P e)) (p := Q) (f := K)
  dsimp [P, Q, s] at h1 h2 ⊢
  rw [← h1]
  rw [← h2]
  simp [Finset.filter_filter, mul_assoc]

lemma prod_leftPairEdges_actual_eq {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} {E : Finset (Fin m × Fin m)}
    {e₀ : Fin m × Fin m}
    (hE : E ⊆ pairEdgePairs m) (he₀ : e₀ ∈ pairEdgePairs m)
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    (∏ e ∈ leftPairEdges E e₀,
      H e (extendPairEdgeTuple e₀ r u w e.1 - extendPairEdgeTuple e₀ r u w e.2)) =
    remainingLeftPairTest H E e₀ r u := by
  classical
  unfold remainingLeftPairTest
  refine Finset.prod_congr rfl ?_
  intro e he
  have he_rem : e ∈ remainingPairEdges E e₀ := (Finset.mem_filter.mp he).1
  have hleft : pairEdgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2
  have hnot_right : ¬ pairEdgeUsesVertex e e₀.2 := by
    intro hright
    exact pairEdge_not_uses_both_endpoints_of_mem_remaining hE he₀ he_rem hleft hright
  have hnr := not_or.mp hnot_right
  rw [extendPairEdgeTuple_eq_of_same_left r u w 0 hnr.1,
    extendPairEdgeTuple_eq_of_same_left r u w 0 hnr.2]

lemma prod_rightPairEdges_actual_eq {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} {E : Finset (Fin m × Fin m)}
    {e₀ : Fin m × Fin m}
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    (∏ e ∈ rightPairEdges E e₀,
      H e (extendPairEdgeTuple e₀ r u w e.1 - extendPairEdgeTuple e₀ r u w e.2)) =
    remainingRightPairTest H E e₀ r w := by
  classical
  unfold remainingRightPairTest
  refine Finset.prod_congr rfl ?_
  intro e he
  have hnot_left : ¬ pairEdgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2.1
  have hnl := not_or.mp hnot_left
  rw [extendPairEdgeTuple_eq_of_same_right r u 0 w hnl.1,
    extendPairEdgeTuple_eq_of_same_right r u 0 w hnl.2]

lemma prod_constantPairEdges_actual_eq {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} {E : Finset (Fin m × Fin m)}
    {e₀ : Fin m × Fin m}
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    (∏ e ∈ constantPairEdges E e₀,
      H e (extendPairEdgeTuple e₀ r u w e.1 - extendPairEdgeTuple e₀ r u w e.2)) =
    remainingConstPairFactor H E e₀ r := by
  classical
  unfold remainingConstPairFactor
  refine Finset.prod_congr rfl ?_
  intro e he
  have hnot_left : ¬ pairEdgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2.1
  have hnot_right : ¬ pairEdgeUsesVertex e e₀.2 := (Finset.mem_filter.mp he).2.2
  have hnl := not_or.mp hnot_left
  have hnr := not_or.mp hnot_right
  rw [extendPairEdgeTuple_eq_of_not_endpoints r u w 0 0 hnl.1 hnr.1,
    extendPairEdgeTuple_eq_of_not_endpoints r u w 0 0 hnl.2 hnr.2]

lemma remainingPairEdgeProduct_factorization {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} {E : Finset (Fin m × Fin m)}
    {e₀ : Fin m × Fin m}
    (hE : E ⊆ pairEdgePairs m) (he₀ : e₀ ∈ pairEdgePairs m)
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    (∏ e ∈ E \ {e₀},
      H e (extendPairEdgeTuple e₀ r u w e.1 - extendPairEdgeTuple e₀ r u w e.2)) =
        (remainingConstPairFactor H E e₀ r * remainingLeftPairTest H E e₀ r u) *
          remainingRightPairTest H E e₀ r w := by
  classical
  change (∏ e ∈ remainingPairEdges E e₀,
      H e (extendPairEdgeTuple e₀ r u w e.1 - extendPairEdgeTuple e₀ r u w e.2)) = _
  rw [prod_remainingPairEdges_split]
  rw [prod_leftPairEdges_actual_eq hE he₀ r u w,
    prod_rightPairEdges_actual_eq r u w,
    prod_constantPairEdges_actual_eq r u w]
  ring

noncomputable def pairVertexRestFinset {m : ℕ} (e₀ : Fin m × Fin m) : Finset (Fin m) :=
  ((Finset.univ : Finset (Fin m)) \ {e₀.1}) \ {e₀.2}

noncomputable def remainingVertexFactor {p m : ℕ}
    (v : ZMod p → ℂ) (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) : ℂ :=
  ∏ i ∈ pairVertexRestFinset e₀, v (extendPairEdgeTuple e₀ r 0 0 i)

lemma vertexProduct_factorization {p m : ℕ} {e₀ : Fin m × Fin m}
    (hne : e₀.1 ≠ e₀.2) (v : ZMod p → ℂ)
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    (∏ i : Fin m, v (extendPairEdgeTuple e₀ r u w i)) =
      (remainingVertexFactor v e₀ r * v u) * v w := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ e₀.1)
      (fun i => v (extendPairEdgeTuple e₀ r u w i))]
  have hmem2 : e₀.2 ∈ (Finset.univ : Finset (Fin m)) \ {e₀.1} := by
    simp [hne.symm]
  rw [Finset.prod_eq_mul_prod_diff_singleton hmem2]
  have hrest :
      (∏ i ∈ (((Finset.univ : Finset (Fin m)) \ {e₀.1}) \ {e₀.2}),
        v (extendPairEdgeTuple e₀ r u w i)) =
      remainingVertexFactor v e₀ r := by
    unfold remainingVertexFactor pairVertexRestFinset
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hi2 : i ∈ ((Finset.univ : Finset (Fin m)) \ {e₀.1}) ∧
        i ∉ ({e₀.2} : Finset (Fin m)) :=
      Finset.mem_sdiff.mp hi
    have hi1 : i ∉ ({e₀.1} : Finset (Fin m)) := (Finset.mem_sdiff.mp hi2.1).2
    have h1 : i ≠ e₀.1 := by simpa using hi1
    have h2 : i ≠ e₀.2 := by simpa using hi2.2
    rw [extendPairEdgeTuple_eq_of_not_endpoints r u w 0 0 h1 h2]
  rw [hrest]
  simp [extendPairEdgeTuple_right (e₀ := e₀) (show e₀.2 ≠ e₀.1 from hne.symm)]
  ring

noncomputable def weightedLeftPairTest {p m : ℕ} [NeZero p]
    (H : (Fin m × Fin m) → ZMod p → ℂ) (E : Finset (Fin m × Fin m))
    (v : ZMod p → ℂ) (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (u : ZMod p) : ℂ :=
  (remainingVertexFactor v e₀ r * v u) *
    (remainingConstPairFactor H E e₀ r * remainingLeftPairTest H E e₀ r u)

noncomputable def weightedRightPairTest {p m : ℕ} [NeZero p]
    (H : (Fin m × Fin m) → ZMod p → ℂ) (E : Finset (Fin m × Fin m))
    (v : ZMod p → ℂ) (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (w : ZMod p) : ℂ :=
  v w * remainingRightPairTest H E e₀ r w

lemma weightedPairRemainingProduct_factorization {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} {E : Finset (Fin m × Fin m)}
    {e₀ : Fin m × Fin m}
    (hE : E ⊆ pairEdgePairs m) (he₀ : e₀ ∈ pairEdgePairs m)
    (v : ZMod p → ℂ)
    (r : PairEdgeRestAssignment p m e₀) (u w : ZMod p) :
    (∏ i : Fin m, v (extendPairEdgeTuple e₀ r u w i)) *
      (∏ e ∈ E \ {e₀},
        H e (extendPairEdgeTuple e₀ r u w e.1 -
          extendPairEdgeTuple e₀ r u w e.2)) =
        weightedLeftPairTest H E v e₀ r u *
          weightedRightPairTest H E v e₀ r w := by
  rw [vertexProduct_factorization (pairEdgePairs_left_ne_right he₀) v r u w,
    remainingPairEdgeProduct_factorization hE he₀ r u w]
  unfold weightedLeftPairTest weightedRightPairTest
  ring

lemma finiteWeightedPatternEdge_replace_sub_eq_avgFinite_weightedCayleyCutFunctional
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {H : (Fin m × Fin m) → ZMod p → ℂ} {e₀ : Fin m × Fin m}
    (hE : E ⊆ pairEdgePairs m) (he₀E : e₀ ∈ E) (he₀ : e₀ ∈ pairEdgePairs m)
    (g v : ZMod p → ℂ) :
    finiteWeightedPatternEdge E (replacePairEdgeKernel H e₀ g) v -
        finiteWeightedPatternEdge E H v =
      avgFinite (PairEdgeRestAssignment p m e₀)
        (fun r => weightedCayleyCutFunctional
          (fun z => g z - H e₀ z)
          (weightedLeftPairTest H E v e₀ r)
          (weightedRightPairTest H E v e₀ r)) := by
  exact finiteWeightedPatternEdge_replace_sub_eq_avgFinite_weightedCayleyCutFunctional_of_factorization
    he₀E (pairEdgePairs_left_ne_right he₀) g v
    (weightedLeftPairTest H E v e₀)
    (weightedRightPairTest H E v e₀)
    (weightedPairRemainingProduct_factorization hE he₀ v)

/-- Every edge kernel in a weighted pattern is uniformly bounded by `1`. -/
def PairKernelBoundedByOne {p m : ℕ}
    (H : (Fin m × Fin m) → ZMod p → ℂ) : Prop :=
  ∀ e z, ‖H e z‖ ≤ 1

/-- The vertex weight in a weighted pattern is uniformly bounded by `1`. -/
def VertexWeightBoundedByOne {p : ℕ} (v : ZMod p → ℂ) : Prop :=
  ∀ z, ‖v z‖ ≤ 1

lemma indicatorC_norm_le_one {p : ℕ} (T : Finset (ZMod p)) (z : ZMod p) :
    ‖indicatorC T z‖ ≤ 1 := by
  classical
  by_cases h : z ∈ T
  · simp [indicatorC, h]
  · simp [indicatorC, h]

lemma vertexWeightBoundedByOne_indicatorC {p : ℕ} (U : Finset (ZMod p)) :
    VertexWeightBoundedByOne (indicatorC U) :=
  indicatorC_norm_le_one U

lemma pairKernelBoundedByOne_const_indicatorC {p m : ℕ} (F : Finset (ZMod p)) :
    PairKernelBoundedByOne (m := m) (fun _ : Fin m × Fin m => indicatorC F) := by
  intro _e z
  exact indicatorC_norm_le_one F z

lemma norm_remainingLeftPairTest_le_one {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} (hH : PairKernelBoundedByOne H)
    (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (u : ZMod p) :
    ‖remainingLeftPairTest H E e₀ r u‖ ≤ 1 := by
  classical
  unfold remainingLeftPairTest
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (H e (extendPairEdgeTuple e₀ r u 0 e.1 - extendPairEdgeTuple e₀ r u 0 e.2)))
    (fun e _he =>
      hH e (extendPairEdgeTuple e₀ r u 0 e.1 - extendPairEdgeTuple e₀ r u 0 e.2))

lemma norm_remainingRightPairTest_le_one {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} (hH : PairKernelBoundedByOne H)
    (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (w : ZMod p) :
    ‖remainingRightPairTest H E e₀ r w‖ ≤ 1 := by
  classical
  unfold remainingRightPairTest
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (H e (extendPairEdgeTuple e₀ r 0 w e.1 - extendPairEdgeTuple e₀ r 0 w e.2)))
    (fun e _he =>
      hH e (extendPairEdgeTuple e₀ r 0 w e.1 - extendPairEdgeTuple e₀ r 0 w e.2))

lemma norm_remainingConstPairFactor_le_one {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} (hH : PairKernelBoundedByOne H)
    (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) :
    ‖remainingConstPairFactor H E e₀ r‖ ≤ 1 := by
  classical
  unfold remainingConstPairFactor
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (H e (extendPairEdgeTuple e₀ r 0 0 e.1 - extendPairEdgeTuple e₀ r 0 0 e.2)))
    (fun e _he =>
      hH e (extendPairEdgeTuple e₀ r 0 0 e.1 - extendPairEdgeTuple e₀ r 0 0 e.2))

lemma norm_remainingVertexFactor_le_one {p m : ℕ}
    {v : ZMod p → ℂ} (hv : VertexWeightBoundedByOne v)
    (e₀ : Fin m × Fin m) (r : PairEdgeRestAssignment p m e₀) :
    ‖remainingVertexFactor v e₀ r‖ ≤ 1 := by
  classical
  unfold remainingVertexFactor
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun i _hi => norm_nonneg (v (extendPairEdgeTuple e₀ r 0 0 i)))
    (fun i _hi => hv (extendPairEdgeTuple e₀ r 0 0 i))

lemma norm_weightedLeftPairTest_le_one {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} {v : ZMod p → ℂ}
    (hH : PairKernelBoundedByOne H) (hv : VertexWeightBoundedByOne v)
    (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (u : ZMod p) :
    ‖weightedLeftPairTest H E v e₀ r u‖ ≤ 1 := by
  unfold weightedLeftPairTest
  rw [norm_mul]
  have hvertex : ‖remainingVertexFactor v e₀ r * v u‖ ≤ 1 := by
    rw [norm_mul]
    have hrv := norm_remainingVertexFactor_le_one hv e₀ r
    have hvu := hv u
    have hrv_nonneg : 0 ≤ ‖remainingVertexFactor v e₀ r‖ := norm_nonneg _
    have hvu_nonneg : 0 ≤ ‖v u‖ := norm_nonneg _
    nlinarith
  have hedge : ‖remainingConstPairFactor H E e₀ r * remainingLeftPairTest H E e₀ r u‖ ≤ 1 := by
    rw [norm_mul]
    have hc := norm_remainingConstPairFactor_le_one hH E e₀ r
    have hl := norm_remainingLeftPairTest_le_one hH E e₀ r u
    have hc_nonneg : 0 ≤ ‖remainingConstPairFactor H E e₀ r‖ := norm_nonneg _
    have hl_nonneg : 0 ≤ ‖remainingLeftPairTest H E e₀ r u‖ := norm_nonneg _
    nlinarith
  have hvertex_nonneg : 0 ≤ ‖remainingVertexFactor v e₀ r * v u‖ := norm_nonneg _
  have hedge_nonneg :
      0 ≤ ‖remainingConstPairFactor H E e₀ r * remainingLeftPairTest H E e₀ r u‖ :=
    norm_nonneg _
  nlinarith

lemma norm_weightedRightPairTest_le_one {p m : ℕ} [NeZero p]
    {H : (Fin m × Fin m) → ZMod p → ℂ} {v : ZMod p → ℂ}
    (hH : PairKernelBoundedByOne H) (hv : VertexWeightBoundedByOne v)
    (E : Finset (Fin m × Fin m)) (e₀ : Fin m × Fin m)
    (r : PairEdgeRestAssignment p m e₀) (w : ZMod p) :
    ‖weightedRightPairTest H E v e₀ r w‖ ≤ 1 := by
  unfold weightedRightPairTest
  rw [norm_mul]
  have hvw := hv w
  have hr := norm_remainingRightPairTest_le_one hH E e₀ r w
  have hvw_nonneg : 0 ≤ ‖v w‖ := norm_nonneg _
  have hr_nonneg : 0 ≤ ‖remainingRightPairTest H E e₀ r w‖ := norm_nonneg _
  nlinarith

/-- Concrete Route A one-edge replacement estimate.  Once all unreplaced edge
kernels and the vertex weight are bounded by `1`, replacing the chosen edge is
controlled by the weighted Cayley cut bound of the replacement difference. -/
lemma norm_finiteWeightedPatternEdge_replace_sub_le_of_cutBound
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {H : (Fin m × Fin m) → ZMod p → ℂ} {e₀ : Fin m × Fin m}
    {g v : ZMod p → ℂ} {M : ℝ}
    (hE : E ⊆ pairEdgePairs m) (he₀E : e₀ ∈ E) (he₀ : e₀ ∈ pairEdgePairs m)
    (hH : PairKernelBoundedByOne H) (hv : VertexWeightBoundedByOne v)
    (hcut : WeightedCayleyCutBound (fun z => g z - H e₀ z) M) :
    ‖finiteWeightedPatternEdge E (replacePairEdgeKernel H e₀ g) v -
        finiteWeightedPatternEdge E H v‖ ≤ M := by
  exact norm_finiteWeightedPatternEdge_replace_sub_le_of_cut_representation
    (ι := PairEdgeRestAssignment p m e₀)
    (weightedLeftPairTest H E v e₀)
    (weightedRightPairTest H E v e₀)
    (finiteWeightedPatternEdge_replace_sub_eq_avgFinite_weightedCayleyCutFunctional
      hE he₀E he₀ g v)
    hcut
    (by intro r u; exact norm_weightedLeftPairTest_le_one hH hv E e₀ r u)
    (by intro r w; exact norm_weightedRightPairTest_le_one hH hv E e₀ r w)

lemma PairKernelBoundedByOne.patch {p m : ℕ}
    {H G : (Fin m × Fin m) → ZMod p → ℂ}
    (hH : PairKernelBoundedByOne H) (hG : PairKernelBoundedByOne G)
    (S : Finset (Fin m × Fin m)) :
    PairKernelBoundedByOne (patchPairEdgeKernel H G S) := by
  intro e z
  by_cases he : e ∈ S
  · simpa [patchPairEdgeKernel, he] using hG e z
  · simpa [patchPairEdgeKernel, he] using hH e z

/-- Concrete one-edge patch estimate for the telescoping proof. -/
lemma norm_finiteWeightedPatternEdge_patch_insert_sub_le_of_cutBound
    {p m : ℕ} [NeZero p] {E S : Finset (Fin m × Fin m)}
    {H G : (Fin m × Fin m) → ZMod p → ℂ} {e₀ : Fin m × Fin m}
    {v : ZMod p → ℂ} {M : ℝ}
    (hE : E ⊆ pairEdgePairs m) (he₀E : e₀ ∈ E) (he₀S : e₀ ∉ S)
    (hH : PairKernelBoundedByOne H) (hG : PairKernelBoundedByOne G)
    (hv : VertexWeightBoundedByOne v)
    (hcut : WeightedCayleyCutBound (fun z => G e₀ z - H e₀ z) M) :
    ‖finiteWeightedPatternEdge E (patchPairEdgeKernel H G (insert e₀ S)) v -
        finiteWeightedPatternEdge E (patchPairEdgeKernel H G S) v‖ ≤ M := by
  rw [patchPairEdgeKernel_insert_eq_replace]
  exact norm_finiteWeightedPatternEdge_replace_sub_le_of_cutBound
    hE he₀E (hE he₀E)
    ((PairKernelBoundedByOne.patch hH hG S))
    hv
    (by simpa [patchPairEdgeKernel, he₀S] using hcut)

/-- Finite telescoping estimate for Route A weighted patterns from concrete
edgewise weighted Cayley cut bounds. -/
lemma norm_finiteWeightedPatternEdge_sub_le_card_mul_cutBound
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {H G : (Fin m × Fin m) → ZMod p → ℂ} {v : ZMod p → ℂ} {M : ℝ}
    (hE : E ⊆ pairEdgePairs m)
    (hH : PairKernelBoundedByOne H) (hG : PairKernelBoundedByOne G)
    (hv : VertexWeightBoundedByOne v)
    (hcut : ∀ e ∈ E, WeightedCayleyCutBound (fun z => G e z - H e z) M) :
    ‖finiteWeightedPatternEdge E G v - finiteWeightedPatternEdge E H v‖ ≤
      (E.card : ℝ) * M := by
  exact norm_finiteWeightedPatternEdge_sub_le_card_mul
    (E := E) (H := H) (G := G) (v := v) (M := M)
    (fun e heE S hS _heS =>
      norm_finiteWeightedPatternEdge_patch_insert_sub_le_of_cutBound
        hE heE _heS hH hG hv (hcut e heE))

/-- Route A finite weighted counting estimate from edgewise normalized Fourier
coefficient bounds. -/
lemma norm_finiteWeightedPatternEdge_sub_le_card_mul_spectralBound
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {H G : (Fin m × Fin m) → ZMod p → ℂ} {v : ZMod p → ℂ} {M : ℝ}
    (hE : E ⊆ pairEdgePairs m) (hMnonneg : 0 ≤ M)
    (hH : PairKernelBoundedByOne H) (hG : PairKernelBoundedByOne G)
    (hv : VertexWeightBoundedByOne v)
    (hspec : ∀ e ∈ E, WeightedSpectralBound (fun z => G e z - H e z) M) :
    ‖finiteWeightedPatternEdge E G v - finiteWeightedPatternEdge E H v‖ ≤
      (E.card : ℝ) * M := by
  exact norm_finiteWeightedPatternEdge_sub_le_card_mul_cutBound
    hE hH hG hv
    (fun e he => weightedCayleyCutBound_of_spectralBound
      (fun z => G e z - H e z) hMnonneg (hspec e he))

/-- Common-kernel specialization of the Route A finite weighted counting
estimate. -/
lemma norm_finiteWeightedPattern_sub_le_card_mul_spectralBound
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {h g v : ZMod p → ℂ} {M : ℝ}
    (hE : E ⊆ pairEdgePairs m) (hMnonneg : 0 ≤ M)
    (hh : ∀ z, ‖h z‖ ≤ 1) (hg : ∀ z, ‖g z‖ ≤ 1)
    (hv : VertexWeightBoundedByOne v)
    (hspec : WeightedSpectralBound (fun z => g z - h z) M) :
    ‖finiteWeightedPattern E g v - finiteWeightedPattern E h v‖ ≤
      (E.card : ℝ) * M := by
  simpa [finiteWeightedPatternEdge_const] using
    norm_finiteWeightedPatternEdge_sub_le_card_mul_spectralBound
      (E := E) (H := fun _ : Fin m × Fin m => h) (G := fun _ : Fin m × Fin m => g)
      (v := v) hE hMnonneg
      (by intro _e z; exact hh z)
      (by intro _e z; exact hg z)
      hv
      (by intro _e _he; exact hspec)

/-- Indicator-kernel specialization used in the Route A counting-convergence
setup. -/
lemma norm_finiteWeightedPattern_sub_indicator_le_card_mul_spectralBound
    {p m : ℕ} [NeZero p] {E : Finset (Fin m × Fin m)}
    {F U : Finset (ZMod p)} {g : ZMod p → ℂ} {M : ℝ}
    (hE : E ⊆ pairEdgePairs m) (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : WeightedSpectralBound (fun z => g z - indicatorC F z) M) :
    ‖finiteWeightedPattern E g (indicatorC U) -
        finiteWeightedPattern E (indicatorC F) (indicatorC U)‖ ≤
      (E.card : ℝ) * M := by
  exact norm_finiteWeightedPattern_sub_le_card_mul_spectralBound
    hE hMnonneg
    (indicatorC_norm_le_one F) hg
    (vertexWeightBoundedByOne_indicatorC U)
    hspec

/-- Oriented finite-avoidance predicate using only the edges `i < j`.  For
symmetric forbidden sets this is equivalent to `AvoidsForbiddenDiffs`, which is
stated over all ordered pairs. -/
def AvoidsForbiddenDiffsOriented {p m : ℕ}
    (F U : Finset (ZMod p)) (x : Fin m → ZMod p) : Prop :=
  (∀ i, x i ∈ U) ∧
    ∀ e ∈ pairEdgePairs m, x e.1 - x e.2 ∉ F

lemma avoidsForbiddenDiffs_iff_oriented_of_symmetric {p m : ℕ} [NeZero p]
    {F U : Finset (ZMod p)} (hFsym : SymmetricFinset F) (x : Fin m → ZMod p) :
    AvoidsForbiddenDiffs F U x ↔ AvoidsForbiddenDiffsOriented F U x := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro e he
    exact h.2 e.1 e.2 (pairEdgePairs_left_ne_right he)
  · intro h
    refine ⟨h.1, ?_⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h.2 (i, j) (by simp [pairEdgePairs, hlt])
    · intro hmem
      have hneg : -(x i - x j) ∈ F := (hFsym (x i - x j)).mp hmem
      have hji : x j - x i ∈ F := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
      exact h.2 (j, i) (by simp [pairEdgePairs, hgt]) hji

/-- Pointwise integrand for the finite avoidance density. -/
noncomputable def finiteAvoidanceWeight {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) (x : Fin m → ZMod p) : ℂ :=
  (∏ i : Fin m, indicatorC U (x i)) *
    ∏ e ∈ pairEdgePairs m, (1 - indicatorC F (x e.1 - x e.2))

/-- Finite avoidance density:

`E_x (∏_i 1_U(x_i)) ∏_{i<j} (1 - 1_F(x_i - x_j))`.

This is the normalized ordered density counted in the Route A contradiction
argument. -/
noncomputable def finiteAvoidanceDensity {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin m → ZMod p, finiteAvoidanceWeight F U x

lemma finiteAvoidanceWeight_eq_indicator_oriented {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) (x : Fin m → ZMod p) :
    finiteAvoidanceWeight F U x =
      if AvoidsForbiddenDiffsOriented F U x then 1 else 0 := by
  classical
  by_cases hx : AvoidsForbiddenDiffsOriented F U x
  · rw [if_pos hx]
    have hU : ∀ i : Fin m, x i ∈ U := hx.1
    have hF : ∀ e ∈ pairEdgePairs m, x e.1 - x e.2 ∉ F := hx.2
    have hvertex : (∏ i : Fin m, indicatorC U (x i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _hi
      simp [indicatorC, hU i]
    have hedge :
        (∏ e ∈ pairEdgePairs m, (1 - indicatorC F (x e.1 - x e.2))) = 1 := by
      apply Finset.prod_eq_one
      intro e he
      simp [indicatorC, hF e he]
    simp [finiteAvoidanceWeight, hvertex, hedge]
  · rw [if_neg hx]
    unfold finiteAvoidanceWeight
    by_cases hU : ∀ i : Fin m, x i ∈ U
    · have hFbad : ¬ ∀ e ∈ pairEdgePairs m, x e.1 - x e.2 ∉ F := by
        intro hF
        exact hx ⟨hU, hF⟩
      rw [not_forall] at hFbad
      rcases hFbad with ⟨e, hebad⟩
      have he : e ∈ pairEdgePairs m := by
        by_contra hne
        exact hebad (fun he => False.elim (hne he))
      have hmem : x e.1 - x e.2 ∈ F := by
        by_contra hnot
        exact hebad (fun _he => hnot)
      have hprod :
          (∏ e ∈ pairEdgePairs m, (1 - indicatorC F (x e.1 - x e.2))) = 0 := by
        refine Finset.prod_eq_zero (i := e) he ?_
        simp [indicatorC, hmem]
      simp [hprod]
    · rw [not_forall] at hU
      rcases hU with ⟨i, hi⟩
      have hprod : (∏ i : Fin m, indicatorC U (x i)) = 0 := by
        refine Finset.prod_eq_zero (i := i) (by simp) ?_
        simp [indicatorC, hi]
      simp [hprod]

/-- The oriented avoiding tuples counted by `finiteAvoidanceDensity`. -/
noncomputable def finiteAvoidingTupleFinsetOriented {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) : Finset (Fin m → ZMod p) :=
  (Finset.univ : Finset (Fin m → ZMod p)).filter
    (fun x => AvoidsForbiddenDiffsOriented F U x)

/-- The all-ordered-pair avoiding tuples from the Route A finite avoidance
axiom. -/
noncomputable def finiteAvoidingTupleFinset {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) : Finset (Fin m → ZMod p) :=
  (Finset.univ : Finset (Fin m → ZMod p)).filter
    (fun x => AvoidsForbiddenDiffs F U x)

/-- Real normalized count of all-ordered-pair avoiding tuples.  This is the
`Λ_n` density before inclusion-exclusion rewrites it as a weighted pattern
count. -/
noncomputable def normalizedAvoidanceDensity {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) : ℝ :=
  ((finiteAvoidingTupleFinset (m := m) F U).card : ℝ) / (p : ℝ) ^ m

lemma normalizedAvoidanceDensity_nonneg {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) :
    0 ≤ normalizedAvoidanceDensity (m := m) F U := by
  unfold normalizedAvoidanceDensity
  positivity

lemma FourierAvoidanceCounterSeq.normalizedAvoidanceDensity_le_c
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) (n : ℕ) :
    (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
      normalizedAvoidanceDensity (m := m) (S.F n) (S.U n)) ≤ S.c n := by
  letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
  have hp_pos : 0 < (S.p n : ℝ) := by
    exact_mod_cast (S.prime n).pos
  have hpow_pos : 0 < (S.p n : ℝ) ^ m := pow_pos hp_pos m
  unfold normalizedAvoidanceDensity finiteAvoidingTupleFinset
  rw [div_le_iff₀ hpow_pos]
  exact le_of_lt (by simpa using S.count_small n)

lemma FourierAvoidanceCounterSeq.normalizedAvoidanceDensity_tendsto_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        normalizedAvoidanceDensity (m := m) (S.F n) (S.U n))
      atTop (𝓝 0) := by
  refine squeeze_zero ?_ ?_ S.c_tendsto_zero
  · intro n
    letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
    exact normalizedAvoidanceDensity_nonneg (m := m) (S.F n) (S.U n)
  · intro n
    exact S.normalizedAvoidanceDensity_le_c n

lemma finiteAvoidingTupleFinset_eq_oriented_of_symmetric {p m : ℕ} [NeZero p]
    {F U : Finset (ZMod p)} (hFsym : SymmetricFinset F) :
    finiteAvoidingTupleFinset (m := m) F U =
      finiteAvoidingTupleFinsetOriented (m := m) F U := by
  classical
  ext x
  simp [finiteAvoidingTupleFinset, finiteAvoidingTupleFinsetOriented,
    avoidsForbiddenDiffs_iff_oriented_of_symmetric hFsym x]

theorem finiteAvoidanceDensity_eq_oriented_count {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) :
    finiteAvoidanceDensity (m := m) F U =
      ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
        ((finiteAvoidingTupleFinsetOriented (m := m) F U).card : ℂ) := by
  classical
  simp [finiteAvoidanceDensity, finiteAvoidanceWeight_eq_indicator_oriented,
    finiteAvoidingTupleFinsetOriented]

theorem finiteAvoidanceDensity_eq_count_of_symmetric {p m : ℕ} [NeZero p]
    {F U : Finset (ZMod p)} (hFsym : SymmetricFinset F) :
    finiteAvoidanceDensity (m := m) F U =
      ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
        ((finiteAvoidingTupleFinset (m := m) F U).card : ℂ) := by
  rw [finiteAvoidanceDensity_eq_oriented_count,
    ← finiteAvoidingTupleFinset_eq_oriented_of_symmetric hFsym]

lemma card_fun_fin_zmod (p m : ℕ) [NeZero p] :
    Fintype.card (Fin m → ZMod p) = p ^ m := by
  simp [ZMod.card]

lemma finiteAvoidanceDensity_eq_normalizedAvoidanceDensity_of_symmetric
    {p m : ℕ} [NeZero p] {F U : Finset (ZMod p)}
    (hFsym : SymmetricFinset F) :
    finiteAvoidanceDensity (m := m) F U =
      (normalizedAvoidanceDensity (m := m) F U : ℂ) := by
  rw [finiteAvoidanceDensity_eq_count_of_symmetric hFsym]
  unfold normalizedAvoidanceDensity
  rw [card_fun_fin_zmod]
  norm_num [div_eq_inv_mul]

lemma finiteAvoidanceDensity_re_eq_normalizedAvoidanceDensity_of_symmetric
    {p m : ℕ} [NeZero p] {F U : Finset (ZMod p)}
    (hFsym : SymmetricFinset F) :
    (finiteAvoidanceDensity (m := m) F U).re =
      normalizedAvoidanceDensity (m := m) F U := by
  rw [finiteAvoidanceDensity_eq_normalizedAvoidanceDensity_of_symmetric hFsym]
  simp

lemma FourierAvoidanceCounterSeq.finiteAvoidanceDensity_tendsto_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        finiteAvoidanceDensity (m := m) (S.F n) (S.U n))
      atTop (𝓝 0) := by
  have hreal := S.normalizedAvoidanceDensity_tendsto_zero
  have hcomplex :
      Tendsto
        (fun n =>
          ((letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            normalizedAvoidanceDensity (m := m) (S.F n) (S.U n)) : ℂ))
        atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.tendsto 0 |>.comp hreal
  have heq :
      (fun n =>
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        finiteAvoidanceDensity (m := m) (S.F n) (S.U n)) =
      (fun n =>
        ((letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          normalizedAvoidanceDensity (m := m) (S.F n) (S.U n)) : ℂ)) := by
    funext n
    letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
    exact finiteAvoidanceDensity_eq_normalizedAvoidanceDensity_of_symmetric (S.F_sym n)
  rw [heq]
  simpa using hcomplex

lemma FourierAvoidanceCounterSeq.finiteAvoidanceDensity_re_tendsto_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) :
    Tendsto
      (fun n =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          finiteAvoidanceDensity (m := m) (S.F n) (S.U n)).re)
      atTop (𝓝 0) := by
  simpa using (Complex.continuous_re.tendsto (0 : ℂ)).comp
    S.finiteAvoidanceDensity_tendsto_zero

lemma avoidanceProduct_inclusion_exclusion {p m : ℕ} [NeZero p]
    (F : Finset (ZMod p)) (x : Fin m → ZMod p) :
    (∏ e ∈ pairEdgePairs m, (1 - indicatorC F (x e.1 - x e.2))) =
      ∑ E ∈ (pairEdgePairs m).powerset,
        (-1 : ℂ) ^ E.card *
          ∏ e ∈ E, indicatorC F (x e.1 - x e.2) := by
  classical
  rw [Finset.prod_sub]
  refine Finset.sum_congr rfl ?_
  intro E hE
  simp

/-- Inclusion-exclusion expansion of the finite avoidance density into Route A
weighted pattern counts. -/
theorem finiteAvoidanceDensity_inclusion_exclusion {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) :
    finiteAvoidanceDensity (m := m) F U =
      ∑ E ∈ (pairEdgePairs m).powerset,
        (-1 : ℂ) ^ E.card *
          finiteWeightedPattern E (indicatorC F) (indicatorC U) := by
  classical
  unfold finiteAvoidanceDensity finiteWeightedPattern
  unfold finiteAvoidanceWeight
  simp_rw [avoidanceProduct_inclusion_exclusion F]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_left_comm]

/-! ## Generic kernel avoidance density -/

/-- Route A avoidance density with an arbitrary edge kernel `h` and vertex
weight `v`.  This is the finite object that Fejer-smoothed kernels converge
through before taking the compact limit. -/
noncomputable def finiteKernelAvoidanceDensity {p m : ℕ} [NeZero p]
    (h v : ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin m → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin m → ZMod p,
      (∏ i : Fin m, v (x i)) *
        ∏ e ∈ pairEdgePairs m, (1 - h (x e.1 - x e.2))

lemma kernelAvoidanceProduct_inclusion_exclusion {p m : ℕ} [NeZero p]
    (h : ZMod p → ℂ) (x : Fin m → ZMod p) :
    (∏ e ∈ pairEdgePairs m, (1 - h (x e.1 - x e.2))) =
      ∑ E ∈ (pairEdgePairs m).powerset,
        (-1 : ℂ) ^ E.card *
          ∏ e ∈ E, h (x e.1 - x e.2) := by
  classical
  rw [Finset.prod_sub]
  refine Finset.sum_congr rfl ?_
  intro E hE
  simp

/-- Inclusion-exclusion expansion of the generic kernel avoidance density. -/
theorem finiteKernelAvoidanceDensity_inclusion_exclusion {p m : ℕ} [NeZero p]
    (h v : ZMod p → ℂ) :
    finiteKernelAvoidanceDensity (m := m) h v =
      ∑ E ∈ (pairEdgePairs m).powerset,
        (-1 : ℂ) ^ E.card * finiteWeightedPattern E h v := by
  classical
  unfold finiteKernelAvoidanceDensity finiteWeightedPattern
  simp_rw [kernelAvoidanceProduct_inclusion_exclusion h]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_left_comm]

lemma finiteKernelAvoidanceDensity_indicatorC_eq {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) :
    finiteKernelAvoidanceDensity (m := m) (indicatorC F) (indicatorC U) =
      finiteAvoidanceDensity (m := m) F U := by
  unfold finiteKernelAvoidanceDensity finiteAvoidanceDensity finiteAvoidanceWeight
  rfl

/-- The full finite Route A avoidance density is stable under replacing `1_F`
by a bounded kernel whose normalized Fourier coefficients are uniformly close
to those of `1_F`. -/
lemma norm_finiteKernelAvoidanceDensity_sub_finiteAvoidanceDensity_le_spectral
    {p m : ℕ} [NeZero p] {F U : Finset (ZMod p)} {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : WeightedSpectralBound (fun z => g z - indicatorC F z) M) :
    ‖finiteKernelAvoidanceDensity (m := m) g (indicatorC U) -
        finiteAvoidanceDensity (m := m) F U‖ ≤
      ∑ E ∈ (pairEdgePairs m).powerset, (E.card : ℝ) * M := by
  classical
  rw [← finiteKernelAvoidanceDensity_indicatorC_eq (m := m) F U]
  rw [finiteKernelAvoidanceDensity_inclusion_exclusion,
    finiteKernelAvoidanceDensity_inclusion_exclusion]
  have hdiff :
      (∑ E ∈ (pairEdgePairs m).powerset,
          (-1 : ℂ) ^ E.card * finiteWeightedPattern E g (indicatorC U)) -
        (∑ E ∈ (pairEdgePairs m).powerset,
          (-1 : ℂ) ^ E.card * finiteWeightedPattern E (indicatorC F) (indicatorC U)) =
        ∑ E ∈ (pairEdgePairs m).powerset,
          (-1 : ℂ) ^ E.card *
            (finiteWeightedPattern E g (indicatorC U) -
              finiteWeightedPattern E (indicatorC F) (indicatorC U)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro E hE
    ring
  rw [hdiff]
  calc
    ‖∑ E ∈ (pairEdgePairs m).powerset,
        (-1 : ℂ) ^ E.card *
          (finiteWeightedPattern E g (indicatorC U) -
            finiteWeightedPattern E (indicatorC F) (indicatorC U))‖
        ≤ ∑ E ∈ (pairEdgePairs m).powerset,
            ‖(-1 : ℂ) ^ E.card *
              (finiteWeightedPattern E g (indicatorC U) -
                finiteWeightedPattern E (indicatorC F) (indicatorC U))‖ := by
          exact norm_sum_le _ _
    _ = ∑ E ∈ (pairEdgePairs m).powerset,
          ‖finiteWeightedPattern E g (indicatorC U) -
            finiteWeightedPattern E (indicatorC F) (indicatorC U)‖ := by
          refine Finset.sum_congr rfl ?_
          intro E hE
          simp
    _ ≤ ∑ E ∈ (pairEdgePairs m).powerset, (E.card : ℝ) * M := by
          refine Finset.sum_le_sum ?_
          intro E hE
          have hEsub : E ⊆ pairEdgePairs m := Finset.mem_powerset.mp hE
          exact norm_finiteWeightedPattern_sub_indicator_le_card_mul_spectralBound
            hEsub hMnonneg hg hspec

lemma sum_powerset_card_mul_le_card_mul_two_pow
    {α : Type*} (s : Finset α) {M : ℝ} (hMnonneg : 0 ≤ M) :
    (∑ E ∈ s.powerset, (E.card : ℝ) * M) ≤
      (s.card : ℝ) * ((2 ^ s.card : ℕ) : ℝ) * M := by
  classical
  calc
    (∑ E ∈ s.powerset, (E.card : ℝ) * M)
        ≤ ∑ _E ∈ s.powerset, (s.card : ℝ) * M := by
          refine Finset.sum_le_sum ?_
          intro E hE
          have hsub : E ⊆ s := Finset.mem_powerset.mp hE
          have hcard : E.card ≤ s.card := Finset.card_le_card hsub
          have hcardR : (E.card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hcardR hMnonneg
    _ = (s.powerset.card : ℝ) * ((s.card : ℝ) * M) := by
          simp [mul_comm, mul_assoc]
    _ = (s.card : ℝ) * ((2 ^ s.card : ℕ) : ℝ) * M := by
          rw [Finset.card_powerset]
          ring

/-- Coarse closed-form version of
`norm_finiteKernelAvoidanceDensity_sub_finiteAvoidanceDensity_le_spectral`. -/
lemma norm_finiteKernelAvoidanceDensity_sub_finiteAvoidanceDensity_le_spectral_closed
    {p m : ℕ} [NeZero p] {F U : Finset (ZMod p)} {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : WeightedSpectralBound (fun z => g z - indicatorC F z) M) :
    ‖finiteKernelAvoidanceDensity (m := m) g (indicatorC U) -
        finiteAvoidanceDensity (m := m) F U‖ ≤
      ((pairEdgePairs m).card : ℝ) * ((2 ^ (pairEdgePairs m).card : ℕ) : ℝ) * M := by
  exact (norm_finiteKernelAvoidanceDensity_sub_finiteAvoidanceDensity_le_spectral
    (m := m) hMnonneg hg hspec).trans
      (sum_powerset_card_mul_le_card_mul_two_pow (pairEdgePairs m) hMnonneg)

end Erdos42.FourierPositive
