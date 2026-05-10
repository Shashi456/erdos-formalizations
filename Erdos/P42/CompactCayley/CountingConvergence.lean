/-
Erdős Problem 42 — finite density target for compact-Cayley counting convergence.

This file does not prove the compactness/counting-convergence lemma yet.  It
sets up the exact finite `K_ℓ` density that Lemma 2.6 should converge to, and
connects its indicator-specialized form to the existing finite clique endpoint.
-/

import Erdos.P42.CompactCayley.CliqueEndpoint
import Erdos.P42.CompactCayley.Counterexample
import Erdos.P42.CompactCayley.SpectralCutNorm

namespace Erdos42.CompactCayley

open Finset Erdos42 Filter
open scoped Topology

/-- Normalized average over a nonempty finite type.  This is used for the
remaining coordinates after a single clique edge has been isolated. -/
noncomputable def avgFinite (α : Type*) [Fintype α] (f : α → ℂ) : ℂ :=
  ((Fintype.card α : ℂ)⁻¹) * ∑ x : α, f x

lemma norm_avgFinite_le {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℂ} {M : ℝ} (hf : ∀ x, ‖f x‖ ≤ M) :
    ‖avgFinite α f‖ ≤ M := by
  classical
  have hcard_pos_nat : 0 < Fintype.card α := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hcard_pos_nat
  have hsum :
      ‖∑ x : α, f x‖ ≤ (Fintype.card α : ℝ) * M := by
    calc
      ‖∑ x : α, f x‖ ≤ ∑ x : α, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : α, M := by
        exact Finset.sum_le_sum (fun x _hx => hf x)
      _ = (Fintype.card α : ℝ) * M := by simp
  unfold avgFinite
  calc
    ‖((Fintype.card α : ℂ)⁻¹) * ∑ x : α, f x‖
        = ‖((Fintype.card α : ℂ)⁻¹)‖ * ‖∑ x : α, f x‖ := norm_mul _ _
    _ ≤ ‖((Fintype.card α : ℂ)⁻¹)‖ * ((Fintype.card α : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = M := by
      rw [norm_inv, Complex.norm_natCast]
      field_simp [ne_of_gt hcard_pos]

lemma norm_avgZMod_le {p : ℕ} [NeZero p] {f : ZMod p → ℂ} {M : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ M) :
    ‖avgZMod f‖ ≤ M := by
  simpa [avgFinite, avgZMod, ZMod.card] using
    norm_avgFinite_le (α := ZMod p) (f := f) hf

/-- Averaging Cayley cut functionals over a nonempty finite parameter set does
not increase a uniform Cayley cut bound.  This is the reusable analytic estimate
for one-edge replacement after the remaining vertices are frozen. -/
lemma norm_avgFinite_cayleyCutFunctional_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} [NeZero p] {a : ZMod p → ℂ} {M : ℝ}
    (hcut : CayleyCutBound a M)
    (φ ψ : ι → ZMod p → ℂ)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖avgFinite ι (fun t => cayleyCutFunctional a (φ t) (ψ t))‖ ≤ M := by
  exact norm_avgFinite_le (fun t => hcut (φ t) (ψ t) (hφ t) (hψ t))

/-- Indices other than the two endpoints of a chosen clique edge. -/
def EdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Type :=
  {k : Fin ℓ // k ≠ e₀.1 ∧ k ≠ e₀.2}

instance instFintypeEdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) :
    Fintype (EdgeRest e₀) := by
  classical
  unfold EdgeRest
  infer_instance

noncomputable instance instDecidableEqEdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) :
    DecidableEq (EdgeRest e₀) := by
  classical
  infer_instance

/-- Assignments to all non-endpoint coordinates of a chosen clique edge. -/
abbrev EdgeRestAssignment (p ℓ : ℕ) (e₀ : Fin ℓ × Fin ℓ) : Type :=
  EdgeRest e₀ → ZMod p

noncomputable instance instFintypeEdgeRestAssignment {p ℓ : ℕ} [NeZero p]
    (e₀ : Fin ℓ × Fin ℓ) : Fintype (EdgeRestAssignment p ℓ e₀) := by
  unfold EdgeRestAssignment
  infer_instance

/-- Extend a frozen assignment on the remaining vertices by assigning `u` and
`v` to the two endpoints of the chosen edge. -/
noncomputable def extendEdgeTuple {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) : Fin ℓ → ZMod p :=
  fun k =>
    if h1 : k = e₀.1 then u
    else if h2 : k = e₀.2 then v
    else r ⟨k, h1, h2⟩

@[simp] lemma extendEdgeTuple_left {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 = u := by
  simp [extendEdgeTuple]

@[simp] lemma extendEdgeTuple_right {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.2 ≠ e₀.1) (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.2 = v := by
  simp [extendEdgeTuple, hne]

lemma extendEdgeTuple_rest {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p)
    {k : Fin ℓ} (h1 : k ≠ e₀.1) (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = r ⟨k, h1, h2⟩ := by
  simp [extendEdgeTuple, h1, h2]

lemma extendEdgeTuple_edge_diff {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.1 ≠ e₀.2) (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 - extendEdgeTuple e₀ r u v e₀.2 = u - v := by
  simp [extendEdgeTuple_right (e₀ := e₀) (show e₀.2 ≠ e₀.1 from hne.symm)]

lemma extendEdgeTuple_edge_diff_of_mem_cliqueEdgePairs {p ℓ : ℕ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 - extendEdgeTuple e₀ r u v e₀.2 = u - v :=
  extendEdgeTuple_edge_diff (cliqueEdgePairs_left_ne_right he₀) r u v

/-- An edge is incident to a vertex. -/
def edgeUsesVertex {ℓ : ℕ} (e : Fin ℓ × Fin ℓ) (i : Fin ℓ) : Prop :=
  e.1 = i ∨ e.2 = i

instance instDecidableEdgeUsesVertex {ℓ : ℕ} (e : Fin ℓ × Fin ℓ) (i : Fin ℓ) :
    Decidable (edgeUsesVertex e i) := by
  unfold edgeUsesVertex
  infer_instance

/-- All clique edges except the edge currently being replaced. -/
def remainingCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  cliqueEdgePairs ℓ \ {e₀}

/-- Remaining clique edges incident to the left endpoint of the replaced edge. -/
def leftCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter (fun e => edgeUsesVertex e e₀.1)

/-- Remaining clique edges incident to the right endpoint but not the left
endpoint of the replaced edge. -/
def rightCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter
    (fun e => ¬ edgeUsesVertex e e₀.1 ∧ edgeUsesVertex e e₀.2)

/-- Remaining clique edges incident to neither endpoint of the replaced edge. -/
def constantCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter
    (fun e => ¬ edgeUsesVertex e e₀.1 ∧ ¬ edgeUsesVertex e e₀.2)

lemma edge_not_uses_both_endpoints_of_mem_remaining {ℓ : ℕ}
    {e₀ e : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (he : e ∈ remainingCliqueEdges e₀)
    (hleft : edgeUsesVertex e e₀.1) (hright : edgeUsesVertex e e₀.2) : False := by
  have he_pair : e ∈ cliqueEdgePairs ℓ := (Finset.mem_sdiff.mp he).1
  have hne_single : e ∉ ({e₀} : Finset (Fin ℓ × Fin ℓ)) := (Finset.mem_sdiff.mp he).2
  have hlt_e : e.1 < e.2 := cliqueEdgePairs_left_lt_right he_pair
  have hlt_e₀ : e₀.1 < e₀.2 := cliqueEdgePairs_left_lt_right he₀
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · have h_eq : e₀.1 = e₀.2 := hleft.symm.trans hright
    exact (ne_of_lt hlt_e₀) h_eq
  · have h_eq : e = e₀ := Prod.ext hleft hright
    exact hne_single (by simp [h_eq])
  · have hbad : e₀.2 < e₀.1 := by simpa [hleft, hright] using hlt_e
    exact (not_lt_of_ge (le_of_lt hlt_e₀)) hbad
  · have h_eq : e₀.1 = e₀.2 := hleft.symm.trans hright
    exact (ne_of_lt hlt_e₀) h_eq

lemma extendEdgeTuple_eq_of_same_left {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v v' : ZMod p) {k : Fin ℓ}
    (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u v' k := by
  by_cases h1 : k = e₀.1
  · subst h1
    simp [extendEdgeTuple]
  · rw [extendEdgeTuple_rest e₀ r u v h1 h2,
      extendEdgeTuple_rest e₀ r u v' h1 h2]

lemma extendEdgeTuple_eq_of_same_right {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u u' v : ZMod p) {k : Fin ℓ}
    (h1 : k ≠ e₀.1) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u' v k := by
  by_cases h2 : k = e₀.2
  · subst h2
    simp [extendEdgeTuple, h1]
  · rw [extendEdgeTuple_rest e₀ r u v h1 h2,
      extendEdgeTuple_rest e₀ r u' v h1 h2]

lemma extendEdgeTuple_eq_of_not_endpoints {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v u' v' : ZMod p) {k : Fin ℓ}
    (h1 : k ≠ e₀.1) (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u' v' k := by
  rw [extendEdgeTuple_rest e₀ r u v h1 h2,
    extendEdgeTuple_rest e₀ r u' v' h1 h2]

/-- Product over remaining edges incident to the left endpoint.  It only
depends on the left endpoint variable. -/
noncomputable def remainingLeftTest {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) : ℂ :=
  ∏ e ∈ leftCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2)

/-- Product over remaining edges incident to the right endpoint but not the
left endpoint.  It only depends on the right endpoint variable. -/
noncomputable def remainingRightTest {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (v : ZMod p) : ℂ :=
  ∏ e ∈ rightCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2)

/-- Product over remaining edges incident to neither endpoint.  It is constant
in the two active endpoint variables once the rest assignment is fixed. -/
noncomputable def remainingConstFactor {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) : ℂ :=
  ∏ e ∈ constantCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2)

lemma prod_remainingCliqueEdges_split {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (H : Fin ℓ × Fin ℓ → ℂ) :
    (∏ e ∈ remainingCliqueEdges e₀, H e) =
      (∏ e ∈ leftCliqueEdges e₀, H e) *
        (∏ e ∈ rightCliqueEdges e₀, H e) *
          (∏ e ∈ constantCliqueEdges e₀, H e) := by
  classical
  unfold leftCliqueEdges rightCliqueEdges constantCliqueEdges
  let s := remainingCliqueEdges e₀
  let P : Fin ℓ × Fin ℓ → Prop := fun e => edgeUsesVertex e e₀.1
  let Q : Fin ℓ × Fin ℓ → Prop := fun e => edgeUsesVertex e e₀.2
  have h1 := Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := H)
  have h2 := Finset.prod_filter_mul_prod_filter_not
    (s := s.filter (fun e => ¬ P e)) (p := Q) (f := H)
  dsimp [P, Q, s] at h1 h2 ⊢
  rw [← h1]
  rw [← h2]
  simp [Finset.filter_filter, mul_assoc]

lemma prod_leftCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (r : EdgeRestAssignment p ℓ e₀)
    (u v : ZMod p) :
    (∏ e ∈ leftCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingLeftTest F e₀ r u := by
  classical
  unfold remainingLeftTest
  refine Finset.prod_congr rfl ?_
  intro e he
  have he_rem : e ∈ remainingCliqueEdges e₀ := (Finset.mem_filter.mp he).1
  have hleft : edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2
  have hnot_right : ¬ edgeUsesVertex e e₀.2 := by
    intro hright
    exact edge_not_uses_both_endpoints_of_mem_remaining he₀ he_rem hleft hright
  have hnr := not_or.mp hnot_right
  rw [extendEdgeTuple_eq_of_same_left r u v 0 hnr.1,
    extendEdgeTuple_eq_of_same_left r u v 0 hnr.2]

lemma prod_rightCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    (∏ e ∈ rightCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingRightTest F e₀ r v := by
  classical
  unfold remainingRightTest
  refine Finset.prod_congr rfl ?_
  intro e he
  have hnot_left : ¬ edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2.1
  have hnl := not_or.mp hnot_left
  rw [extendEdgeTuple_eq_of_same_right r u 0 v hnl.1,
    extendEdgeTuple_eq_of_same_right r u 0 v hnl.2]

lemma prod_constantCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    (∏ e ∈ constantCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingConstFactor F e₀ r := by
  classical
  unfold remainingConstFactor
  refine Finset.prod_congr rfl ?_
  intro e he
  have hnot_left : ¬ edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2.1
  have hnot_right : ¬ edgeUsesVertex e e₀.2 := (Finset.mem_filter.mp he).2.2
  have hnl := not_or.mp hnot_left
  have hnr := not_or.mp hnot_right
  rw [extendEdgeTuple_eq_of_not_endpoints r u v 0 0 hnl.1 hnr.1,
    extendEdgeTuple_eq_of_not_endpoints r u v 0 0 hnl.2 hnr.2]

lemma remainingCliqueEdgeProduct_factorization {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (r : EdgeRestAssignment p ℓ e₀)
    (u v : ZMod p) :
    (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
        (remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u) *
          remainingRightTest F e₀ r v := by
  classical
  change (∏ e ∈ remainingCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) = _
  rw [prod_remainingCliqueEdges_split]
  rw [prod_leftCliqueEdges_actual_eq he₀ r u v,
    prod_rightCliqueEdges_actual_eq r u v,
    prod_constantCliqueEdges_actual_eq r u v]
  ring

/-- Reindex all clique tuples by a chosen edge's two endpoint values and the
assignment on the remaining vertices. -/
noncomputable def edgeTupleEquiv {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (hne : e₀.1 ≠ e₀.2) :
    (Fin ℓ → ZMod p) ≃ (EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p) where
  toFun x := (fun k => x k.1, x e₀.1, x e₀.2)
  invFun q := extendEdgeTuple e₀ q.1 q.2.1 q.2.2
  left_inv x := by
    funext k
    by_cases h1 : k = e₀.1
    · subst h1
      simp [extendEdgeTuple]
    · by_cases h2 : k = e₀.2
      · subst h2
        simp [extendEdgeTuple, hne.symm]
      · simp [extendEdgeTuple, h1, h2]
  right_inv q := by
    rcases q with ⟨r, u, v⟩
    ext k
    · exact extendEdgeTuple_rest e₀ r u v k.property.1 k.property.2
    · simp [extendEdgeTuple]
    · simp [extendEdgeTuple, hne.symm]

lemma sum_edgeTupleEquiv {p ℓ : ℕ} [NeZero p] {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.1 ≠ e₀.2) (f : (Fin ℓ → ZMod p) → ℂ) :
    (∑ x : Fin ℓ → ZMod p, f x) =
      ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
        f (extendEdgeTuple e₀ q.1 q.2.1 q.2.2) := by
  simpa [edgeTupleEquiv] using ((edgeTupleEquiv (p := p) e₀ hne).symm.sum_comp f).symm

/-- The normalized tuple average, after reindexing at one chosen edge, is the
average over frozen remaining coordinates of a two-variable normalized
average. -/
lemma edgeTuple_normalized_sum_eq_avgFinite_avgZMod
    {p ℓ : ℕ} [NeZero p] {e₀ : Fin ℓ × Fin ℓ} (hne : e₀.1 ≠ e₀.2)
    (H : EdgeRestAssignment p ℓ e₀ → ZMod p → ZMod p → ℂ) :
    ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
      ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
        H q.1 q.2.1 q.2.2 =
    avgFinite (EdgeRestAssignment p ℓ e₀)
      (fun r => avgZMod fun u => avgZMod fun v => H r u v) := by
  classical
  have hcard_nat :
      Fintype.card (Fin ℓ → ZMod p) =
        Fintype.card (EdgeRestAssignment p ℓ e₀) * p * p := by
    calc
      Fintype.card (Fin ℓ → ZMod p) =
          Fintype.card (EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p) :=
            Fintype.card_congr (edgeTupleEquiv (p := p) e₀ hne)
      _ = Fintype.card (EdgeRestAssignment p ℓ e₀) * p * p := by
            simp [Fintype.card_prod, ZMod.card, mul_assoc]
  have hcard_complex :
      (Fintype.card (Fin ℓ → ZMod p) : ℂ) =
        (Fintype.card (EdgeRestAssignment p ℓ e₀) : ℂ) * (p : ℂ) * (p : ℂ) := by
    exact_mod_cast hcard_nat
  unfold avgFinite avgZMod
  rw [hcard_complex]
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  ring

/-- Product weight for the finite Cayley `K_ℓ` density with an arbitrary complex
kernel `f`.  The compact-Cayley counting convergence lemma should produce
positivity of the density built from this generic kernel, before specializing
`f` to an indicator. -/
noncomputable def finiteCliqueKernelWeight {p ℓ : ℕ}
    (f : ZMod p → ℂ) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, f (x e.1 - x e.2)

/-- Normalized finite `K_ℓ` Cayley density for an arbitrary kernel on `ZMod p`. -/
noncomputable def finiteCliqueKernelDensity {p ℓ : ℕ} [NeZero p]
    (f : ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, finiteCliqueKernelWeight f x

/-- Edge-indexed version of the finite Cayley `K_ℓ` product weight.  This is
the natural bookkeeping object for the telescoping proof of counting
convergence, where one edge kernel is replaced at a time. -/
noncomputable def finiteCliqueKernelWeightEdge {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, F e (x e.1 - x e.2)

/-- Edge-indexed normalized finite `K_ℓ` Cayley density. -/
noncomputable def finiteCliqueKernelDensityEdge {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, finiteCliqueKernelWeightEdge F x

lemma finiteCliqueKernelWeightEdge_const
    {p ℓ : ℕ} (f : ZMod p → ℂ) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge (fun _ => f) x =
      finiteCliqueKernelWeight f x := by
  rfl

lemma finiteCliqueKernelDensityEdge_const
    {p ℓ : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (ℓ := ℓ) (fun _ => f) =
      finiteCliqueKernelDensity (ℓ := ℓ) f := by
  rfl

/-- Every edge kernel is uniformly bounded by `1`. -/
def EdgeKernelBoundedByOne {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) : Prop :=
  ∀ e z, ‖F e z‖ ≤ 1

/-- Replace one edge kernel in an edge-indexed kernel family. -/
noncomputable def replaceEdgeKernel {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (g : ZMod p → ℂ) : (Fin ℓ × Fin ℓ) → ZMod p → ℂ :=
  fun e z => if e = e₀ then g z else F e z

lemma EdgeKernelBoundedByOne.const {p ℓ : ℕ} {f : ZMod p → ℂ}
    (hf : ∀ z, ‖f z‖ ≤ 1) :
    EdgeKernelBoundedByOne (ℓ := ℓ) (fun _ => f) := by
  intro _ z
  exact hf z

lemma EdgeKernelBoundedByOne.replace {p ℓ : ℕ}
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (hg : ∀ z, ‖g z‖ ≤ 1) :
    EdgeKernelBoundedByOne (replaceEdgeKernel F e₀ g) := by
  intro e z
  by_cases h : e = e₀
  · simp [replaceEdgeKernel, h, hg z]
  · simp [replaceEdgeKernel, h, hF e z]

lemma norm_remainingLeftTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) :
    ‖remainingLeftTest F e₀ r u‖ ≤ 1 := by
  classical
  unfold remainingLeftTest
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2))

lemma norm_remainingRightTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (v : ZMod p) :
    ‖remainingRightTest F e₀ r v‖ ≤ 1 := by
  classical
  unfold remainingRightTest
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2))

lemma norm_remainingConstFactor_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) :
    ‖remainingConstFactor F e₀ r‖ ≤ 1 := by
  classical
  unfold remainingConstFactor
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2))

lemma norm_remainingConstFactor_mul_leftTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) :
    ‖remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u‖ ≤ 1 := by
  rw [norm_mul]
  have hc := norm_remainingConstFactor_le_one hF e₀ r
  have hl := norm_remainingLeftTest_le_one hF e₀ r u
  have hcn : 0 ≤ ‖remainingConstFactor F e₀ r‖ := norm_nonneg _
  have hln : 0 ≤ ‖remainingLeftTest F e₀ r u‖ := norm_nonneg _
  nlinarith

lemma norm_finiteCliqueKernelWeightEdge_le_one
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    (hF : EdgeKernelBoundedByOne F) (x : Fin ℓ → ZMod p) :
    ‖finiteCliqueKernelWeightEdge F x‖ ≤ 1 := by
  classical
  rw [finiteCliqueKernelWeightEdge, norm_prod]
  exact Finset.prod_le_one
    (fun e _he => norm_nonneg (F e (x e.1 - x e.2)))
    (fun e _he => hF e (x e.1 - x e.2))

lemma norm_finiteCliqueKernelWeight_le_one
    {p ℓ : ℕ} {f : ZMod p → ℂ} (hf : ∀ z, ‖f z‖ ≤ 1)
    (x : Fin ℓ → ZMod p) :
    ‖finiteCliqueKernelWeight f x‖ ≤ 1 := by
  simpa [finiteCliqueKernelWeightEdge_const] using
    norm_finiteCliqueKernelWeightEdge_le_one
      (F := fun _ : Fin ℓ × Fin ℓ => f)
      (EdgeKernelBoundedByOne.const (ℓ := ℓ) hf) x

lemma finiteCliqueKernelWeightEdge_eq_single_mul
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge F x =
      F e₀ (x e₀.1 - x e₀.2) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  classical
  unfold finiteCliqueKernelWeightEdge
  exact Finset.prod_eq_mul_prod_diff_singleton he₀
    (fun e => F e (x e.1 - x e.2))

lemma finiteCliqueKernelWeightEdge_replace_eq_single_mul
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge (replaceEdgeKernel F e₀ g) x =
      g (x e₀.1 - x e₀.2) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  classical
  rw [finiteCliqueKernelWeightEdge_eq_single_mul he₀]
  congr 1
  · simp [replaceEdgeKernel]
  · refine Finset.prod_congr rfl ?_
    intro e he
    have hne : e ≠ e₀ := by
      intro h
      exact (Finset.mem_sdiff.mp he).2 (by simp [h])
    simp [replaceEdgeKernel, hne]

lemma norm_remainingCliqueEdgeProduct_le_one
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    (hF : EdgeKernelBoundedByOne F) (e₀ : Fin ℓ × Fin ℓ)
    (x : Fin ℓ → ZMod p) :
    ‖∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2)‖ ≤ 1 := by
  classical
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he => norm_nonneg (F e (x e.1 - x e.2)))
    (fun e _he => hF e (x e.1 - x e.2))

/-- Pointwise single-edge replacement identity, used by the telescoping proof of
finite counting convergence. -/
lemma finiteCliqueKernelWeightEdge_replace_sub
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge (replaceEdgeKernel F e₀ g) x -
        finiteCliqueKernelWeightEdge F x =
      (g (x e₀.1 - x e₀.2) - F e₀ (x e₀.1 - x e₀.2)) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  rw [finiteCliqueKernelWeightEdge_replace_eq_single_mul he₀,
    finiteCliqueKernelWeightEdge_eq_single_mul he₀]
  ring

/-- Density-level form of the single-edge replacement identity. -/
lemma finiteCliqueKernelDensityEdge_replace_sub
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin ℓ → ZMod p,
          (g (x e₀.1 - x e₀.2) - F e₀ (x e₀.1 - x e₀.2)) *
            ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  unfold finiteCliqueKernelDensityEdge
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  exact finiteCliqueKernelWeightEdge_replace_sub he₀ g x

/-- Reindexed density-level single-edge replacement identity.  The full tuple
sum is rewritten as a sum over frozen non-endpoint coordinates and the two
endpoint variables. -/
lemma finiteCliqueKernelDensityEdge_replace_sub_reindex
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
          (g (q.2.1 - q.2.2) - F e₀ (q.2.1 - q.2.2)) *
            ∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
              F e (extendEdgeTuple e₀ q.1 q.2.1 q.2.2 e.1 -
                extendEdgeTuple e₀ q.1 q.2.1 q.2.2 e.2) := by
  rw [finiteCliqueKernelDensityEdge_replace_sub he₀]
  congr 1
  rw [sum_edgeTupleEquiv (cliqueEdgePairs_left_ne_right he₀)]
  refine Finset.sum_congr rfl ?_
  intro q _hq
  rw [extendEdgeTuple_edge_diff_of_mem_cliqueEdgePairs he₀]

/-- If the remaining-edge product factors into a left test and a right test
after the chosen edge has been isolated, then the single-edge replacement
difference is exactly an average of Cayley cut functionals. -/
lemma finiteCliqueKernelDensityEdge_replace_sub_eq_avgFinite_cayleyCutFunctional_of_factorization
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ)
    (φ ψ : EdgeRestAssignment p ℓ e₀ → ZMod p → ℂ)
    (hprod : ∀ r u v,
      (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
        F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
          φ r u * ψ r v) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      avgFinite (EdgeRestAssignment p ℓ e₀)
        (fun r => cayleyCutFunctional
          (fun z => g z - F e₀ z) (φ r) (ψ r)) := by
  rw [finiteCliqueKernelDensityEdge_replace_sub_reindex he₀]
  rw [edgeTuple_normalized_sum_eq_avgFinite_avgZMod
    (p := p) (ℓ := ℓ) (e₀ := e₀) (cliqueEdgePairs_left_ne_right he₀)
    (fun r u v =>
      (g (u - v) - F e₀ (u - v)) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
          F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2))]
  unfold cayleyCutFunctional
  congr 1
  funext r
  congr 1
  funext u
  congr 1
  funext v
  rw [hprod]
  ring

/-- One-edge replacement estimate, assuming the tuple-sum difference has already
been rewritten as an average of Cayley cut functionals over the frozen remaining
coordinates.  The remaining work for Lemma 2.6 is to supply this representation
for the concrete edge being replaced. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cut_representation
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (φ ψ : ι → ZMod p → ℂ)
    (hrepr :
      finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
          finiteCliqueKernelDensityEdge F =
        avgFinite ι
          (fun t => cayleyCutFunctional
            (fun z => g z - F e₀ z) (φ t) (ψ t)))
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  rw [hrepr]
  exact norm_avgFinite_cayleyCutFunctional_le hcut φ ψ hφ hψ

/-- One-edge replacement estimate from a concrete factorization of the
remaining-edge product into two bounded test functions. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_factorization
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (φ ψ : EdgeRestAssignment p ℓ e₀ → ZMod p → ℂ)
    (hprod : ∀ r u v,
      (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
        F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
          φ r u * ψ r v)
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cut_representation φ ψ
    (finiteCliqueKernelDensityEdge_replace_sub_eq_avgFinite_cayleyCutFunctional_of_factorization
      he₀ g φ ψ hprod)
    hcut hφ hψ

/-- Concrete one-edge replacement estimate: if all unreplaced edge kernels are
bounded by `1`, then replacing one edge is controlled by the Cayley cut bound of
the replacement difference. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cutBound
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (hF : EdgeKernelBoundedByOne F)
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_factorization he₀
    (fun r u => remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u)
    (fun r v => remainingRightTest F e₀ r v)
    (by intro r u v; exact remainingCliqueEdgeProduct_factorization he₀ r u v)
    hcut
    (by intro r u; exact norm_remainingConstFactor_mul_leftTest_le_one hF e₀ r u)
    (by intro r v; exact norm_remainingRightTest_le_one hF e₀ r v)

/-- Patch an edge-indexed kernel family by replacing the kernels on `S` with
those from another family. -/
noncomputable def patchEdgeKernel {p ℓ : ℕ}
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (S : Finset (Fin ℓ × Fin ℓ)) :
    (Fin ℓ × Fin ℓ) → ZMod p → ℂ :=
  fun e z => if e ∈ S then G e z else F e z

lemma patchEdgeKernel_insert_eq_replace {p ℓ : ℕ}
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (S : Finset (Fin ℓ × Fin ℓ))
    (e₀ : Fin ℓ × Fin ℓ) :
    patchEdgeKernel F G (insert e₀ S) =
      replaceEdgeKernel (patchEdgeKernel F G S) e₀ (G e₀) := by
  funext e z
  by_cases h : e = e₀
  · subst h
    simp [patchEdgeKernel, replaceEdgeKernel]
  · simp [patchEdgeKernel, replaceEdgeKernel, h]

lemma EdgeKernelBoundedByOne.patch {p ℓ : ℕ}
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {S : Finset (Fin ℓ × Fin ℓ)}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G) :
    EdgeKernelBoundedByOne (patchEdgeKernel F G S) := by
  intro e z
  by_cases h : e ∈ S
  · simp [patchEdgeKernel, h, hG e z]
  · simp [patchEdgeKernel, h, hF e z]

lemma finiteCliqueKernelDensityEdge_patch_empty {p ℓ : ℕ} [NeZero p]
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (patchEdgeKernel F G (∅ : Finset (Fin ℓ × Fin ℓ))) =
      finiteCliqueKernelDensityEdge F := by
  unfold finiteCliqueKernelDensityEdge finiteCliqueKernelWeightEdge
  simp [patchEdgeKernel]

lemma finiteCliqueKernelDensityEdge_patch_all {p ℓ : ℕ} [NeZero p]
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (patchEdgeKernel F G (cliqueEdgePairs ℓ)) =
      finiteCliqueKernelDensityEdge G := by
  classical
  unfold finiteCliqueKernelDensityEdge finiteCliqueKernelWeightEdge
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  refine Finset.prod_congr rfl ?_
  intro e he
  simp [patchEdgeKernel, he]

lemma norm_finiteCliqueKernelDensityEdge_patch_insert_sub_le {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {S : Finset (Fin ℓ × Fin ℓ)}
    {e₀ : Fin ℓ × Fin ℓ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (heS : e₀ ∉ S)
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : CayleyCutBound (fun z => G e₀ z - F e₀ z) M) :
    ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e₀ S)) -
        finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)‖ ≤ M := by
  rw [patchEdgeKernel_insert_eq_replace]
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cutBound he₀
    (EdgeKernelBoundedByOne.patch hF hG)
    (by simpa [patchEdgeKernel, heS] using hcut)

/-- Finite telescoping estimate for compact-Cayley Lemma 2.6.  Replacing all
edge kernels changes the finite `K_ℓ` density by at most the number of clique
edges times a uniform Cayley cut bound. -/
lemma norm_finiteCliqueKernelDensityEdge_patch_sub_le_card_mul {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {M : ℝ}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : ∀ e ∈ cliqueEdgePairs ℓ, CayleyCutBound (fun z => G e z - F e z) M)
    (S : Finset (Fin ℓ × Fin ℓ)) (hS : S ⊆ cliqueEdgePairs ℓ) :
    ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
        finiteCliqueKernelDensityEdge F‖ ≤ (S.card : ℝ) * M := by
  classical
  refine Finset.induction_on S ?base ?step hS
  · intro _hS
    rw [finiteCliqueKernelDensityEdge_patch_empty]
    simp
  · intro e S heS ih hInsert
    have heClique : e ∈ cliqueEdgePairs ℓ := hInsert (by simp)
    have hSsub : S ⊆ cliqueEdgePairs ℓ := by
      intro x hx
      exact hInsert (by simp [hx])
    have hstep := norm_finiteCliqueKernelDensityEdge_patch_insert_sub_le
      (F := F) (G := G) (S := S) (e₀ := e) heClique heS hF hG (hcut e heClique)
    have hih := ih hSsub
    have hdecomp :
        finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge F =
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)) +
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
            finiteCliqueKernelDensityEdge F) := by
      ring
    rw [hdecomp]
    calc
      ‖(finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)) +
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
            finiteCliqueKernelDensityEdge F)‖
          ≤ ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)‖ +
            ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
              finiteCliqueKernelDensityEdge F‖ := norm_add_le _ _
      _ ≤ M + (S.card : ℝ) * M := add_le_add hstep hih
      _ = ((insert e S).card : ℝ) * M := by
        rw [Finset.card_insert_of_notMem heS]
        norm_num
        ring

lemma norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {M : ℝ}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : ∀ e ∈ cliqueEdgePairs ℓ, CayleyCutBound (fun z => G e z - F e z) M) :
    ‖finiteCliqueKernelDensityEdge G - finiteCliqueKernelDensityEdge F‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  have h := norm_finiteCliqueKernelDensityEdge_patch_sub_le_card_mul
    (F := F) (G := G) (M := M) hF hG hcut (cliqueEdgePairs ℓ) (by intro x hx; exact hx)
  rwa [finiteCliqueKernelDensityEdge_patch_all] at h

lemma norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_spectralBound
    {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hspec : ∀ e ∈ cliqueEdgePairs ℓ,
      SpectralBound (fun z => G e z - F e z) M) :
    ‖finiteCliqueKernelDensityEdge G - finiteCliqueKernelDensityEdge F‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  exact norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound hF hG
    (fun e he => cayleyCutBound_of_spectralBound
      (a := fun z => G e z - F e z) hMnonneg (hspec e he))

lemma norm_finiteCliqueKernelDensity_sub_le_card_mul_cutBound
    {p ℓ : ℕ} [NeZero p] {f g : ZMod p → ℂ} {M : ℝ}
    (hf : ∀ z, ‖f z‖ ≤ 1) (hg : ∀ z, ‖g z‖ ≤ 1)
    (hcut : CayleyCutBound (fun z => g z - f z) M) :
    ‖finiteCliqueKernelDensity (ℓ := ℓ) g - finiteCliqueKernelDensity (ℓ := ℓ) f‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  simpa [finiteCliqueKernelDensityEdge_const] using
    norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound
      (F := fun _ : Fin ℓ × Fin ℓ => f) (G := fun _ : Fin ℓ × Fin ℓ => g)
      (M := M)
      (EdgeKernelBoundedByOne.const (ℓ := ℓ) hf)
      (EdgeKernelBoundedByOne.const (ℓ := ℓ) hg)
      (fun _e _he => hcut)

lemma norm_finiteCliqueKernelDensity_sub_le_card_mul_spectralBound
    {p ℓ : ℕ} [NeZero p] {f g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hf : ∀ z, ‖f z‖ ≤ 1) (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => g z - f z) M) :
    ‖finiteCliqueKernelDensity (ℓ := ℓ) g - finiteCliqueKernelDensity (ℓ := ℓ) f‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  exact norm_finiteCliqueKernelDensity_sub_le_card_mul_cutBound
    (ℓ := ℓ) hf hg
    (cayleyCutBound_of_spectralBound (a := fun z => g z - f z) hMnonneg hspec)

lemma indicatorC_norm_le_one {p : ℕ} (T : Finset (ZMod p)) (z : ZMod p) :
    ‖indicatorC T z‖ ≤ 1 := by
  classical
  by_cases h : z ∈ T
  · simp [indicatorC, h]
  · simp [indicatorC, h]

lemma finiteCliqueKernelWeight_indicatorC
    {p ℓ : ℕ} (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeight (indicatorC T) x = cliqueKernelWeight T x := by
  rfl

lemma finiteCliqueKernelDensity_indicatorC
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) =
      cliqueKernelDensity (ℓ := ℓ) T := by
  rfl

lemma finiteCliqueKernelDensity_indicatorC_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) = 0 := by
  rw [finiteCliqueKernelDensity_indicatorC]
  exact cliqueKernelDensity_eq_zero_of_no_clique hTsym hT0 hNoClique

lemma CayleyCounterSeq.finiteCliqueKernelDensity_indicatorC_eq_zero
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) (n : ℕ) :
    (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
      finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC (S.T n))) = 0 := by
  letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
  exact finiteCliqueKernelDensity_indicatorC_eq_zero_of_no_clique
    (S.T_sym n) (S.T_zero n) (S.no_clique n)

lemma CayleyCounterSeq.finiteCliqueKernelDensity_indicatorC_tendsto_zero
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC (S.T n)))
      atTop (𝓝 0) := by
  have hzero : ∀ n,
      (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC (S.T n))) = 0 :=
    S.finiteCliqueKernelDensity_indicatorC_eq_zero
  have heq :
      (fun n =>
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
        finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC (S.T n))) = fun _ => (0 : ℂ) := by
    funext n
    exact hzero n
  rw [heq]
  exact tendsto_const_nhds

/-- Indicator-specialized finite generic density is positive exactly when the
finite Cayley graph contains a clique. -/
lemma finiteCliqueKernelDensity_indicatorC_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T) :
    0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [finiteCliqueKernelDensity_indicatorC]
  exact cliqueKernelDensity_re_pos_iff_exists_clique hTsym hT0

/-- Positive finite generic density for the indicator kernel gives the finite
clique needed by the compact-Cayley theorem.  This is the endpoint that the
future counting-convergence proof should feed into. -/
theorem exists_clique_of_finiteCliqueKernelDensity_indicator_re_pos
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : 0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  exact (finiteCliqueKernelDensity_indicatorC_re_pos_iff_exists_clique hTsym hT0).mp hdensity

/-- Finite endpoint for the compact counting transfer: if a bounded model
kernel has positive finite `K_ℓ` density by more than the spectral-transfer
error, and it is spectrally close to `1_T`, then `T` contains a clique. -/
theorem exists_clique_of_spectral_density_transfer
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => indicatorC T z - g z) M)
    (hdensity : ((cliqueEdgePairs ℓ).card : ℝ) * M <
      (finiteCliqueKernelDensity (ℓ := ℓ) g).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  have hclose := norm_finiteCliqueKernelDensity_sub_le_card_mul_spectralBound
    (ℓ := ℓ) hMnonneg hg (indicatorC_norm_le_one T) hspec
  have hre_abs :
      |(finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
          finiteCliqueKernelDensity (ℓ := ℓ) g).re| ≤
        ((cliqueEdgePairs ℓ).card : ℝ) * M := by
    exact le_trans (Complex.abs_re_le_norm _) hclose
  have hre_low :
      -(((cliqueEdgePairs ℓ).card : ℝ) * M) ≤
        (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
          finiteCliqueKernelDensity (ℓ := ℓ) g).re :=
    (abs_le.mp hre_abs).1
  have hpos : 0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re := by
    have hcalc :
        (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re =
          (finiteCliqueKernelDensity (ℓ := ℓ) g).re +
            (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
              finiteCliqueKernelDensity (ℓ := ℓ) g).re := by
      simp
    rw [hcalc]
    linarith
  exact exists_clique_of_finiteCliqueKernelDensity_indicator_re_pos hTsym hT0 hpos

/-- Same finite endpoint with the rough bound `#E(K_ℓ) ≤ ℓ²`, avoiding exact
edge-count bookkeeping at higher compactness layers. -/
theorem exists_clique_of_spectral_density_transfer_sq
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => indicatorC T z - g z) M)
    (hdensity : ((ℓ * ℓ : ℕ) : ℝ) * M <
      (finiteCliqueKernelDensity (ℓ := ℓ) g).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  have hcard : ((cliqueEdgePairs ℓ).card : ℝ) ≤ ((ℓ * ℓ : ℕ) : ℝ) := by
    exact_mod_cast cliqueEdgePairs_card_le_sq ℓ
  exact exists_clique_of_spectral_density_transfer hTsym hT0 hMnonneg hg hspec
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hMnonneg) hdensity)

end Erdos42.CompactCayley
