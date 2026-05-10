/-
Erdős Problem 42 — finite-to-compact density convergence for smoothed kernels.

This file contains the finite edge-frequency bookkeeping needed to turn the
fixed-`Q` finite Fejér-smoothed clique density into a compact Haar integral.
-/

import Erdos.P42.CompactCayley.CountingConvergence
import Erdos.P42.CompactCayley.LimitKernel

namespace Erdos42.CompactCayley

open Filter MeasureTheory
open scoped BigOperators Classical Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- The finite type of oriented clique edges. -/
abbrev CliqueEdgeIndex (M : ℕ) : Type :=
  {e : Fin M × Fin M // e ∈ cliqueEdgePairs M}

/-- Extend an assignment on clique edges by zero off the clique-edge set. -/
noncomputable def extendCliqueEdgeAssignment
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) :
    Fin M × Fin M → E.Group :=
  fun e => if h : e ∈ cliqueEdgePairs M then ω ⟨e, h⟩ else 0

@[simp]
lemma extendCliqueEdgeAssignment_apply_mem
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) (e : Fin M × Fin M)
    (he : e ∈ cliqueEdgePairs M) :
    E.extendCliqueEdgeAssignment ω e = ω ⟨e, he⟩ := by
  simp [extendCliqueEdgeAssignment, he]

/-- Coefficient product attached to an assignment of frequencies to the clique
edges. -/
noncomputable def cliqueEdgeAssignmentCoeff
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (ω : CliqueEdgeIndex M → E.Group) : ℂ :=
  ∏ e : CliqueEdgeIndex M, P (ω e)

lemma TrigPoly.evalFinite_eq_sum_support
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    TrigPoly.evalFinite P n x =
      ∑ γ ∈ P.support,
        P γ * ZMod.stdAddChar (-(E.lift n γ * x)) := by
  classical
  unfold TrigPoly.evalFinite
  rw [Finsupp.sum_of_support_subset
    (f := P) (s := P.support) (by intro γ hγ; exact hγ)]
  intro γ _hγ
  simp

lemma TrigPoly.evalFinite_eq_sum_of_support_subset
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    (A : Finset E.Group) (hP : P.support ⊆ A)
    (x : ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    TrigPoly.evalFinite P n x =
      ∑ γ ∈ A, P γ * ZMod.stdAddChar (-(E.lift n γ * x)) := by
  classical
  unfold TrigPoly.evalFinite
  rw [Finsupp.sum_of_support_subset (f := P) (s := A) hP]
  intro γ _hγ
  simp

lemma TrigPoly.evalAdd_eq_sum_support
    (E : CayleyExtraction S) (P : E.TrigPoly)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd P z =
      ∑ γ ∈ P.support, P γ * E.addCharacterValue z γ := by
  classical
  unfold TrigPoly.evalAdd
  rw [Finsupp.sum_of_support_subset
    (f := P) (s := P.support) (by intro γ hγ; exact hγ)]
  intro γ _hγ
  simp

lemma TrigPoly.evalAdd_eq_sum_of_support_subset
    (E : CayleyExtraction S) (P : E.TrigPoly)
    (A : Finset E.Group) (hP : P.support ⊆ A)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd P z =
      ∑ γ ∈ A, P γ * E.addCharacterValue z γ := by
  classical
  unfold TrigPoly.evalAdd
  rw [Finsupp.sum_of_support_subset (f := P) (s := A) hP]
  intro γ _hγ
  simp

lemma addCharacterValue_sum
    (E : CayleyExtraction S) {ι : Type*} (s : Finset ι)
    (z : E.CompactAddDual) (f : ι → E.Group) :
    E.addCharacterValue z (∑ i ∈ s, f i) =
      ∏ i ∈ s, E.addCharacterValue z (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [E.addCharacterValue_add, ih]

lemma addCharacterValue_sum_univ
    (E : CayleyExtraction S) {ι : Type*} [Fintype ι]
    (z : E.CompactAddDual) (f : ι → E.Group) :
    E.addCharacterValue z (∑ i, f i) =
      ∏ i, E.addCharacterValue z (f i) := by
  simpa using E.addCharacterValue_sum (Finset.univ : Finset ι) z f

lemma stdAddChar_neg_sum_mul
    {p : ℕ} [NeZero p] {ι : Type*} (s : Finset ι)
    (f : ι → ZMod p) (x : ZMod p) :
    ZMod.stdAddChar (-((∑ i ∈ s, f i) * x)) =
      ∏ i ∈ s, ZMod.stdAddChar (-(f i * x)) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [← ih]
    rw [← ZMod.stdAddChar.map_add_eq_mul]
    congr 1
    ring

lemma stdAddChar_sum
    {p : ℕ} [NeZero p] {ι : Type*} (s : Finset ι)
    (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, f i) =
      ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [ZMod.stdAddChar.map_add_eq_mul, ih]

lemma stdAddChar_sum_univ
    {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i, f i) =
      ∏ i, ZMod.stdAddChar (f i) := by
  simpa using stdAddChar_sum (Finset.univ : Finset ι) f

lemma stdAddChar_neg_sum_univ_mul
    {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (f : ι → ZMod p) (x : ZMod p) :
    ZMod.stdAddChar (-((∑ i, f i) * x)) =
      ∏ i, ZMod.stdAddChar (-(f i * x)) := by
  simpa using stdAddChar_neg_sum_mul (Finset.univ : Finset ι) f x

lemma finitePiAverage_prod_zmod {p M : ℕ} [NeZero p]
    (φ : Fin M → ZMod p → ℂ) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p, ∏ i : Fin M, φ i (x i) =
      ∏ i : Fin M, avgZMod (φ i) := by
  classical
  have hcard_nat : Fintype.card (Fin M → ZMod p) = p ^ M := by
    simp [ZMod.card]
  have hcard_complex : (Fintype.card (Fin M → ZMod p) : ℂ) = (p : ℂ) ^ M := by
    rw [hcard_nat]
    norm_cast
  unfold avgZMod
  rw [hcard_complex]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  simp

lemma finitePiAverage_prod_stdAddChar_neg_mul
    {p M : ℕ} [Fact p.Prime] [NeZero p]
    (β : Fin M → ZMod p) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p,
          ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
      ∏ i : Fin M, if β i = 0 then (1 : ℂ) else 0 := by
  rw [show
      ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod p,
            ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
        ∏ i : Fin M,
          avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(β i * x))) by
        simpa using
          finitePiAverage_prod_zmod
            (p := p) (M := M)
            (fun i x => ZMod.stdAddChar (-(β i * x)))]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact avgZMod_stdAddChar_neg_mul_eq_ite (β i)

lemma finitePiAverage_prod_stdAddChar_neg_mul_eq_if
    {p M : ℕ} [Fact p.Prime] [NeZero p]
    (β : Fin M → ZMod p) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p,
          ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
      if (∀ i : Fin M, β i = 0) then 1 else 0 := by
  rw [finitePiAverage_prod_stdAddChar_neg_mul β]
  by_cases hβ : ∀ i : Fin M, β i = 0
  · simp [hβ]
  · rw [if_neg hβ]
    push_neg at hβ
    rcases hβ with ⟨i, hi⟩
    exact Finset.prod_eq_zero (by simp : i ∈ (Finset.univ : Finset (Fin M)))
      (by simp [hi])

/-- Net finite frequency at a vertex for an arbitrary finite set of oriented
edges. The compact-Cayley clique balance is this construction specialized to
`cliqueEdgePairs`. -/
noncomputable def finiteEdgeFrequencyBalanceOn
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (i : Fin M) : ZMod p :=
  (∑ e ∈ s.filter (fun e => e.1 = i), r e) -
  (∑ e ∈ s.filter (fun e => e.2 = i), r e)

lemma sum_vertex_outgoing_eq_edge_sum
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i) =
      ∑ e ∈ s, r e * x e.1 := by
  classical
  calc
    (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i)
        = ∑ i : Fin M, ∑ e ∈ s, (if e.1 = i then r e else 0) * x i := by
          simp [Finset.sum_mul]
    _ = ∑ e ∈ s, ∑ i : Fin M, (if e.1 = i then r e else 0) * x i := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ s, r e * x e.1 := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          rw [Finset.sum_eq_single e.1]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma sum_vertex_incoming_eq_edge_sum
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i) =
      ∑ e ∈ s, r e * x e.2 := by
  classical
  calc
    (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i)
        = ∑ i : Fin M, ∑ e ∈ s, (if e.2 = i then r e else 0) * x i := by
          simp [Finset.sum_mul]
    _ = ∑ e ∈ s, ∑ i : Fin M, (if e.2 = i then r e else 0) * x i := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ s, r e * x e.2 := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          rw [Finset.sum_eq_single e.2]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma finiteEdgeFrequencyBalanceOn_exponent_identity
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ e ∈ s, -(r e * (x e.1 - x e.2))) =
      ∑ i : Fin M, -(finiteEdgeFrequencyBalanceOn s r i * x i) := by
  classical
  simp [finiteEdgeFrequencyBalanceOn, Finset.sum_filter]
  rw [show
      (∑ i : Fin M,
        ((∑ e ∈ s, if e.1 = i then r e else 0) -
          (∑ e ∈ s, if e.2 = i then r e else 0)) * x i) =
        (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i) -
          (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i) by
        simp [sub_mul, Finset.sum_sub_distrib]]
  rw [sum_vertex_outgoing_eq_edge_sum s r x,
    sum_vertex_incoming_eq_edge_sum s r x]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro e _he
  ring

lemma prod_stdAddChar_edge_eq_prod_balance
    {p M : ℕ} [NeZero p] (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∏ e ∈ s, ZMod.stdAddChar (-(r e * (x e.1 - x e.2)))) =
      ∏ i : Fin M,
        ZMod.stdAddChar (-(finiteEdgeFrequencyBalanceOn s r i * x i)) := by
  rw [← stdAddChar_sum s (fun e => -(r e * (x e.1 - x e.2)))]
  rw [← stdAddChar_sum_univ
    (fun i : Fin M => -(finiteEdgeFrequencyBalanceOn s r i * x i))]
  rw [finiteEdgeFrequencyBalanceOn_exponent_identity]

lemma prod_vertex_outgoing_eq_edge_prod
    {M : ℕ} {A : Type*} [CommMonoid A]
    (s : Finset (Fin M × Fin M)) (F : (Fin M × Fin M) → Fin M → A) :
    (∏ i : Fin M, ∏ e ∈ s, if e.1 = i then F e i else 1) =
      ∏ e ∈ s, F e e.1 := by
  classical
  calc
    (∏ i : Fin M, ∏ e ∈ s, if e.1 = i then F e i else 1)
        = ∏ e ∈ s, ∏ i : Fin M, if e.1 = i then F e i else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ e ∈ s, F e e.1 := by
          refine Finset.prod_congr rfl ?_
          intro e _he
          rw [Finset.prod_eq_single e.1]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma prod_vertex_incoming_eq_edge_prod
    {M : ℕ} {A : Type*} [CommMonoid A]
    (s : Finset (Fin M × Fin M)) (F : (Fin M × Fin M) → Fin M → A) :
    (∏ i : Fin M, ∏ e ∈ s, if e.2 = i then F e i else 1) =
      ∏ e ∈ s, F e e.2 := by
  classical
  calc
    (∏ i : Fin M, ∏ e ∈ s, if e.2 = i then F e i else 1)
        = ∏ e ∈ s, ∏ i : Fin M, if e.2 = i then F e i else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ e ∈ s, F e e.2 := by
          refine Finset.prod_congr rfl ?_
          intro e _he
          rw [Finset.prod_eq_single e.2]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma compactPiIntegral_prod_addCharacterValue
    (E : CayleyExtraction S) {M : ℕ}
    (β : Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        ∏ i : Fin M, E.addCharacterValue (x i) (β i)
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∏ i : Fin M, if β i = 0 then (1 : ℂ) else 0 := by
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun _ : Fin M => E.haar)
    (f := fun i z => E.addCharacterValue z (β i))]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact E.integral_addCharacterValue (β i)

lemma compactPiIntegral_prod_addCharacterValue_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (β : Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        ∏ i : Fin M, E.addCharacterValue (x i) (β i)
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      if (∀ i : Fin M, β i = 0) then 1 else 0 := by
  rw [E.compactPiIntegral_prod_addCharacterValue β]
  by_cases hβ : ∀ i : Fin M, β i = 0
  · simp [hβ]
  · rw [if_neg hβ]
    push_neg at hβ
    rcases hβ with ⟨i, hi⟩
    exact Finset.prod_eq_zero (by simp : i ∈ (Finset.univ : Finset (Fin M)))
      (by simp [hi])

/-- Sum of edge frequencies leaving a vertex in the oriented clique edge set. -/
noncomputable def cliqueOutgoingFreq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i), ω e

/-- Sum of edge frequencies entering a vertex in the oriented clique edge set. -/
noncomputable def cliqueIncomingFreq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e

/-- Net compact frequency at a vertex after multiplying edge characters
`χ_γ(x_i - x_j)` over all oriented clique edges `i < j`. -/
noncomputable def cliqueFrequencyBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  E.cliqueOutgoingFreq ω i - E.cliqueIncomingFreq ω i

/-- Finite cyclic lift of the vertex frequency balance attached to an
edge-frequency assignment. -/
noncomputable def finiteCliqueFrequencyBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ) (i : Fin M) :
    ZMod (S.p (E.φ n)) :=
  (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i),
    E.lift n (ω e)) -
  (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i),
    E.lift n (ω e))

lemma finiteLift_cliqueOutgoingFreq_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueOutgoingFreq ω i) =
        ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i),
          E.lift n (ω e) := by
  simpa [cliqueOutgoingFreq, lift] using
    E.data.finiteLift_sum_eventually_eq
      ((cliqueEdgePairs M).filter (fun e => e.1 = i)) ω

lemma finiteLift_cliqueIncomingFreq_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueIncomingFreq ω i) =
        ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i),
          E.lift n (ω e) := by
  simpa [cliqueIncomingFreq, lift] using
    E.data.finiteLift_sum_eventually_eq
      ((cliqueEdgePairs M).filter (fun e => e.2 = i)) ω

lemma finiteLift_cliqueFrequencyBalance_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueFrequencyBalance ω i) =
        E.finiteCliqueFrequencyBalance ω n i := by
  filter_upwards
    [E.data.finiteLift_sub_eventually_eq
      (E.cliqueOutgoingFreq ω i) (E.cliqueIncomingFreq ω i),
      E.finiteLift_cliqueOutgoingFreq_eventually_eq ω i,
      E.finiteLift_cliqueIncomingFreq_eventually_eq ω i] with n hsub hout hin
  rw [cliqueFrequencyBalance]
  change
    E.data.finiteLift n (E.cliqueOutgoingFreq ω i - E.cliqueIncomingFreq ω i) =
      (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i),
        E.data.finiteLift n (ω e)) -
      (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i),
        E.data.finiteLift n (ω e))
  rw [hsub]
  rw [show
      E.data.finiteLift n (E.cliqueOutgoingFreq ω i) =
        ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i),
          E.data.finiteLift n (ω e) by
        simpa [lift] using hout]
  rw [show
      E.data.finiteLift n (E.cliqueIncomingFreq ω i) =
        ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i),
          E.data.finiteLift n (ω e) by
        simpa [lift] using hin]

lemma finiteLift_cliqueFrequencyBalance_all_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop, ∀ i : Fin M,
      E.lift n (E.cliqueFrequencyBalance ω i) =
        E.finiteCliqueFrequencyBalance ω n i := by
  have h :
      ∀ᶠ n in atTop, ∀ i ∈ (Finset.univ : Finset (Fin M)),
        E.lift n (E.cliqueFrequencyBalance ω i) =
          E.finiteCliqueFrequencyBalance ω n i := by
    rw [(Finset.univ : Finset (Fin M)).eventually_all]
    intro i _hi
    exact E.finiteLift_cliqueFrequencyBalance_eventually_eq ω i
  filter_upwards [h] with n hn i
  exact hn i (by simp)

lemma finiteLift_cliqueFrequencyBalance_zero_iff_eventually
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop, ∀ i : Fin M,
      E.lift n (E.cliqueFrequencyBalance ω i) = 0 ↔
        E.cliqueFrequencyBalance ω i = 0 := by
  have h :
      ∀ᶠ n in atTop, ∀ i ∈ (Finset.univ : Finset (Fin M)),
        E.lift n (E.cliqueFrequencyBalance ω i) = 0 ↔
          E.cliqueFrequencyBalance ω i = 0 := by
    rw [(Finset.univ : Finset (Fin M)).eventually_all]
    intro i _hi
    by_cases hbal : E.cliqueFrequencyBalance ω i = 0
    · filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hzero
      constructor
      · intro _h
        exact hbal
      · intro _h
        simpa [hbal, lift] using hzero
    · filter_upwards [E.finiteLift_eventually_ne_zero hbal] with n hn
      constructor
      · intro hzero
        exact (hn hzero).elim
      · intro h
        exact (hbal h).elim
  filter_upwards [h] with n hn i
  exact hn i (by simp)

lemma finiteCliqueFrequencyBalance_all_zero_iff_eventually
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop,
      ((∀ i : Fin M, E.finiteCliqueFrequencyBalance ω n i = 0) ↔
        ∀ i : Fin M, E.cliqueFrequencyBalance ω i = 0) := by
  filter_upwards
    [E.finiteLift_cliqueFrequencyBalance_all_eventually_eq ω,
      E.finiteLift_cliqueFrequencyBalance_zero_iff_eventually ω] with n heq hzero
  constructor
  · intro hfin i
    exact (hzero i).mp (by rw [heq i, hfin i])
  · intro hcompact i
    have hlift_zero : E.lift n (E.cliqueFrequencyBalance ω i) = 0 :=
      (hzero i).mpr (hcompact i)
    rwa [heq i] at hlift_zero

lemma finiteCliqueFrequencyBalance_eq_finiteEdgeFrequencyBalanceOn
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ) (i : Fin M) :
    E.finiteCliqueFrequencyBalance ω n i =
      finiteEdgeFrequencyBalanceOn (cliqueEdgePairs M)
        (fun e => E.lift n (ω e)) i := by
  rfl

lemma prod_stdAddChar_cliqueEdge_eq_prod_finiteCliqueBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    (∏ e ∈ cliqueEdgePairs M,
        ZMod.stdAddChar
          (-(E.lift n (ω e) * (x e.1 - x e.2)))) =
      ∏ i : Fin M,
        ZMod.stdAddChar (-(E.finiteCliqueFrequencyBalance ω n i * x i)) := by
  simpa [E.finiteCliqueFrequencyBalance_eq_finiteEdgeFrequencyBalanceOn ω n] using
    prod_stdAddChar_edge_eq_prod_balance (cliqueEdgePairs M)
      (fun e => E.lift n (ω e)) x

lemma finiteCliqueAssignmentAverage_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))] :
    ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod (S.p (E.φ n)),
          ∏ e ∈ cliqueEdgePairs M,
            ZMod.stdAddChar
              (-(E.lift n (ω e) * (x e.1 - x e.2))) =
      if (∀ i : Fin M, E.finiteCliqueFrequencyBalance ω n i = 0)
      then 1 else 0 := by
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e ∈ cliqueEdgePairs M,
              ZMod.stdAddChar
                (-(E.lift n (ω e) * (x e.1 - x e.2))) =
        ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ i : Fin M,
              ZMod.stdAddChar
                (-(E.finiteCliqueFrequencyBalance ω n i * x i)) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.prod_stdAddChar_cliqueEdge_eq_prod_finiteCliqueBalance ω n x]
  exact finitePiAverage_prod_stdAddChar_neg_mul_eq_if
    (fun i : Fin M => E.finiteCliqueFrequencyBalance ω n i)

lemma finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelWeight (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) x =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            ZMod.stdAddChar
              (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) := by
  classical
  unfold finiteCliqueKernelWeight
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalFinite P n (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalFinite P n (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ P.support,
            P γ * ZMod.stdAddChar
              (-(E.lift n γ * (x e.1.1 - x e.1.2))) by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalFinite_eq_sum_support E P n
          (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A)
    (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelWeight (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) x =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            ZMod.stdAddChar
              (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) := by
  classical
  unfold finiteCliqueKernelWeight
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalFinite P n (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalFinite P n (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ A,
            P γ * ZMod.stdAddChar
              (-(E.lift n γ * (x e.1.1 - x e.1.2))) by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalFinite_eq_sum_of_support_subset E P n A hP
          (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma prod_stdAddChar_cliqueEdgeIndex_eq_extend
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    (∏ e : CliqueEdgeIndex M,
        ZMod.stdAddChar
          (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) =
      ∏ e ∈ cliqueEdgePairs M,
        ZMod.stdAddChar
          (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
              (x e.1 - x e.2))) := by
  simpa [CliqueEdgeIndex] using
    (Finset.prod_attach (s := cliqueEdgePairs M)
      (f := fun e : Fin M × Fin M =>
        ZMod.stdAddChar
          (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
              (x e.1 - x e.2)))))

lemma finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.finiteCliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) n i = 0)
            then 1 else 0) := by
  classical
  unfold finiteCliqueKernelDensity
  rw [show
      (∑ x : Fin M → ZMod (S.p (E.φ n)),
          finiteCliqueKernelWeight
            (fun z : ZMod (S.p (E.φ n)) =>
              TrigPoly.evalFinite P n z) x) =
        ∑ x : Fin M → ZMod (S.p (E.φ n)),
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments P n x]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ω hω
  rw [← Finset.mul_sum]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          (E.cliqueEdgeAssignmentCoeff P ω *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) =
        E.cliqueEdgeAssignmentCoeff P ω *
          (((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) by
        ring]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e : CliqueEdgeIndex M,
              ZMod.stdAddChar
                (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) =
        ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e ∈ cliqueEdgePairs M,
              ZMod.stdAddChar
                (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
                    (x e.1 - x e.2))) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.prod_stdAddChar_cliqueEdgeIndex_eq_extend ω n x]
  rw [E.finiteCliqueAssignmentAverage_eq_if (E.extendCliqueEdgeAssignment ω) n]

lemma finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.finiteCliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) n i = 0)
            then 1 else 0) := by
  classical
  unfold finiteCliqueKernelDensity
  rw [show
      (∑ x : Fin M → ZMod (S.p (E.φ n)),
          finiteCliqueKernelWeight
            (fun z : ZMod (S.p (E.φ n)) =>
              TrigPoly.evalFinite P n z) x) =
        ∑ x : Fin M → ZMod (S.p (E.φ n)),
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments_of_support_subset
          P A hP n x]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ω hω
  rw [← Finset.mul_sum]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          (E.cliqueEdgeAssignmentCoeff P ω *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) =
        E.cliqueEdgeAssignmentCoeff P ω *
          (((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) by
        ring]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e : CliqueEdgeIndex M,
              ZMod.stdAddChar
                (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) =
        ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e ∈ cliqueEdgePairs M,
              ZMod.stdAddChar
                (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
                    (x e.1 - x e.2))) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.prod_stdAddChar_cliqueEdgeIndex_eq_extend ω n x]
  rw [E.finiteCliqueAssignmentAverage_eq_if (E.extendCliqueEdgeAssignment ω) n]

/-- Compact character product for one edge-frequency assignment, regrouped by
vertex balances. -/
lemma prod_addCharacterValue_cliqueEdge_eq_prod_balance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (x : Fin M → E.CompactAddDual) :
    (∏ e ∈ cliqueEdgePairs M,
        E.addCharacterValue (x e.1 - x e.2) (ω e)) =
      ∏ i : Fin M, E.addCharacterValue (x i) (E.cliqueFrequencyBalance ω i) := by
  classical
  unfold cliqueFrequencyBalance cliqueOutgoingFreq cliqueIncomingFreq
  rw [show
      (∏ i : Fin M,
          E.addCharacterValue (x i)
            ((∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i), ω e) -
              ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e)) =
        (∏ i : Fin M,
          (∏ e ∈ cliqueEdgePairs M,
            if e.1 = i then E.addCharacterValue (x i) (ω e) else 1) *
          (∏ e ∈ cliqueEdgePairs M,
            if e.2 = i then E.addCharacterValue (x i) (-ω e) else 1)) by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        rw [sub_eq_add_neg, E.addCharacterValue_add]
        rw [E.addCharacterValue_sum]
        rw [show
            E.addCharacterValue (x i)
                (-(∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e)) =
              E.addCharacterValue (x i)
                (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), -ω e) by
              simp]
        rw [E.addCharacterValue_sum]
        rw [Finset.prod_filter, Finset.prod_filter]]
  rw [Finset.prod_mul_distrib]
  rw [prod_vertex_outgoing_eq_edge_prod (cliqueEdgePairs M)
    (fun e i => E.addCharacterValue (x i) (ω e))]
  rw [prod_vertex_incoming_eq_edge_prod (cliqueEdgePairs M)
    (fun e i => E.addCharacterValue (x i) (-ω e))]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro e _he
  simp [sub_eq_add_neg, E.addCharacterValue_add_point]

lemma compactCliqueAssignmentIntegral_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.addCharacterValue (x e.1 - x e.2) (ω e))
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      if (∀ i : Fin M, E.cliqueFrequencyBalance ω i = 0)
      then 1 else 0 := by
  rw [show
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.addCharacterValue (x e.1 - x e.2) (ω e))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∫ x : Fin M → E.CompactAddDual,
          ∏ i : Fin M, E.addCharacterValue (x i)
            (E.cliqueFrequencyBalance ω i)
          ∂Measure.pi (fun _ : Fin M => E.haar) by
        congr 1
        funext x
        exact E.prod_addCharacterValue_cliqueEdge_eq_prod_balance ω x]
  exact E.compactPiIntegral_prod_addCharacterValue_eq_if
    (fun i : Fin M => E.cliqueFrequencyBalance ω i)

lemma continuous_cliqueEdgeAssignmentCharacterProduct
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) :
    Continuous (fun x : Fin M → E.CompactAddDual =>
      ∏ e : CliqueEdgeIndex M,
        E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)) := by
  simpa using
    (continuous_finset_prod (Finset.univ : Finset (CliqueEdgeIndex M))
      (fun e _he =>
        (E.addCharacterValue_continuous (ω e)).comp
          ((continuous_apply e.1.1).sub (continuous_apply e.1.2))))

lemma integrable_cliqueEdgeAssignmentTerm
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (ω : CliqueEdgeIndex M → E.Group) :
    Integrable
      (fun x : Fin M → E.CompactAddDual =>
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            E.addCharacterValue (x e.1.1 - x e.1.2) (ω e))
      (Measure.pi (fun _ : Fin M => E.haar)) :=
  (continuous_const.mul
      (E.continuous_cliqueEdgeAssignmentCharacterProduct ω)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma compactCliqueKernel_evalAdd_eq_sum_edgeAssignments
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (x : Fin M → E.CompactAddDual) :
    (∏ e ∈ cliqueEdgePairs M,
        TrigPoly.evalAdd P (x e.1 - x e.2)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            E.addCharacterValue (x e.1.1 - x e.1.2) (ω e) := by
  classical
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalAdd P (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ P.support,
            P γ * E.addCharacterValue (x e.1.1 - x e.1.2) γ by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalAdd_eq_sum_support E P (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma compactCliqueKernel_evalAdd_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A)
    (x : Fin M → E.CompactAddDual) :
    (∏ e ∈ cliqueEdgePairs M,
        TrigPoly.evalAdd P (x e.1 - x e.2)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            E.addCharacterValue (x e.1.1 - x e.1.2) (ω e) := by
  classical
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalAdd P (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ A,
            P γ * E.addCharacterValue (x e.1.1 - x e.1.2) γ by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalAdd_eq_sum_of_support_subset E P A hP
          (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma prod_addCharacterValue_cliqueEdgeIndex_eq_extend
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group)
    (x : Fin M → E.CompactAddDual) :
    (∏ e : CliqueEdgeIndex M,
        E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)) =
      ∏ e ∈ cliqueEdgePairs M,
        E.addCharacterValue (x e.1 - x e.2)
          (E.extendCliqueEdgeAssignment ω e) := by
  simpa [CliqueEdgeIndex] using
    (Finset.prod_attach (s := cliqueEdgePairs M)
      (f := fun e : Fin M × Fin M =>
        E.addCharacterValue (x e.1 - x e.2)
          (E.extendCliqueEdgeAssignment ω e)))

lemma compactCliqueDensity_evalAdd_eq_sum_edgeAssignments
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0)
            then 1 else 0) := by
  classical
  rw [show
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∫ x : Fin M → E.CompactAddDual,
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
          ∂Measure.pi (fun _ : Fin M => E.haar) by
        congr 1
        funext x
        exact E.compactCliqueKernel_evalAdd_eq_sum_edgeAssignments P x]
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro ω _hω
    rw [MeasureTheory.integral_const_mul]
    rw [show
        (∫ x : Fin M → E.CompactAddDual,
            (∏ e : CliqueEdgeIndex M,
              E.addCharacterValue (x e.1.1 - x e.1.2) (ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar)) =
          ∫ x : Fin M → E.CompactAddDual,
            (∏ e ∈ cliqueEdgePairs M,
              E.addCharacterValue (x e.1 - x e.2)
                (E.extendCliqueEdgeAssignment ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar) by
          congr 1
          funext x
          exact E.prod_addCharacterValue_cliqueEdgeIndex_eq_extend ω x]
    rw [E.compactCliqueAssignmentIntegral_eq_if (E.extendCliqueEdgeAssignment ω)]
  · intro ω _hω
    exact E.integrable_cliqueEdgeAssignmentTerm P ω

lemma compactCliqueDensity_evalAdd_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0)
            then 1 else 0) := by
  classical
  rw [show
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∫ x : Fin M → E.CompactAddDual,
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
          ∂Measure.pi (fun _ : Fin M => E.haar) by
        congr 1
        funext x
        exact E.compactCliqueKernel_evalAdd_eq_sum_edgeAssignments_of_support_subset
          P A hP x]
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro ω _hω
    rw [MeasureTheory.integral_const_mul]
    rw [show
        (∫ x : Fin M → E.CompactAddDual,
            (∏ e : CliqueEdgeIndex M,
              E.addCharacterValue (x e.1.1 - x e.1.2) (ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar)) =
          ∫ x : Fin M → E.CompactAddDual,
            (∏ e ∈ cliqueEdgePairs M,
              E.addCharacterValue (x e.1 - x e.2)
                (E.extendCliqueEdgeAssignment ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar) by
          congr 1
          funext x
          exact E.prod_addCharacterValue_cliqueEdgeIndex_eq_extend ω x]
    rw [E.compactCliqueAssignmentIntegral_eq_if (E.extendCliqueEdgeAssignment ω)]
  · intro ω _hω
    exact E.integrable_cliqueEdgeAssignmentTerm P ω

lemma finiteCliqueKernelDensity_evalFinite_eventually_eq_compact
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) :
    ∀ᶠ n in atTop,
      (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
       letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
       finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z)) =
      (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)) := by
  classical
  let A : Finset (CliqueEdgeIndex M → E.Group) :=
    Fintype.piFinset (fun _ : CliqueEdgeIndex M => P.support)
  have hbalance :
      ∀ᶠ n in atTop, ∀ ω ∈ A,
        ((∀ i : Fin M,
            E.finiteCliqueFrequencyBalance
              (E.extendCliqueEdgeAssignment ω) n i = 0) ↔
          ∀ i : Fin M,
            E.cliqueFrequencyBalance
              (E.extendCliqueEdgeAssignment ω) i = 0) := by
    rw [A.eventually_all]
    intro ω _hω
    exact E.finiteCliqueFrequencyBalance_all_zero_iff_eventually
      (E.extendCliqueEdgeAssignment ω)
  filter_upwards [hbalance] with n hbalance_n
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [E.finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments P n]
  rw [E.compactCliqueDensity_evalAdd_eq_sum_edgeAssignments P]
  dsimp [A] at hbalance_n
  refine Finset.sum_congr rfl ?_
  intro ω hω
  by_cases hfin :
      ∀ i : Fin M,
        E.finiteCliqueFrequencyBalance
          (E.extendCliqueEdgeAssignment ω) n i = 0
  · have hcompact :
        ∀ i : Fin M,
          E.cliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) i = 0 :=
      (hbalance_n ω hω).mp hfin
    simp [hfin, hcompact]
  · have hcompact :
        ¬ ∀ i : Fin M,
          E.cliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) i = 0 := by
      intro hc
      exact hfin ((hbalance_n ω hω).mpr hc)
    simp [hfin, hcompact]

lemma finiteCliqueKernelDensity_evalFinite_tendsto_compact_of_coeff_tendsto
    (E : CayleyExtraction S) {M : ℕ}
    (Pseq : ℕ → E.TrigPoly) (P : E.TrigPoly) (A : Finset E.Group)
    (hPseq_support : ∀ᶠ n in atTop, (Pseq n).support ⊆ A)
    (hP_support : P.support ⊆ A)
    (hcoeff :
      ∀ γ ∈ A, Tendsto (fun n => Pseq n γ) atTop (𝓝 (P γ))) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (Pseq n) n z))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  classical
  let W : Finset (CliqueEdgeIndex M → E.Group) :=
    Fintype.piFinset (fun _ : CliqueEdgeIndex M => A)
  let compactTerm : (CliqueEdgeIndex M → E.Group) → ℂ := fun ω =>
    E.cliqueEdgeAssignmentCoeff P ω *
      (if (∀ i : Fin M,
          E.cliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) i = 0)
        then 1 else 0)
  let finiteTerm : ℕ → (CliqueEdgeIndex M → E.Group) → ℂ := fun n ω =>
    E.cliqueEdgeAssignmentCoeff (Pseq n) ω *
      (if (∀ i : Fin M,
          E.finiteCliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) n i = 0)
        then 1 else 0)
  have hfinite_exp :
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (Pseq n) n z)) =ᶠ[atTop]
      (fun n => ∑ ω ∈ W, finiteTerm n ω) := by
    filter_upwards [hPseq_support] with n hn_support
    haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
    haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    rw [E.finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments_of_support_subset
      (Pseq n) A hn_support n]
  have hcompact_exp :
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∑ ω ∈ W, compactTerm ω := by
    rw [E.compactCliqueDensity_evalAdd_eq_sum_edgeAssignments_of_support_subset
      P A hP_support]
  have hterm :
      ∀ ω ∈ W, Tendsto (fun n => finiteTerm n ω) atTop (𝓝 (compactTerm ω)) := by
    intro ω hω
    have hω_mem : ∀ e : CliqueEdgeIndex M, ω e ∈ A :=
      Fintype.mem_piFinset.mp hω
    have hcoeff_prod :
        Tendsto (fun n => E.cliqueEdgeAssignmentCoeff (Pseq n) ω)
          atTop (𝓝 (E.cliqueEdgeAssignmentCoeff P ω)) := by
      unfold cliqueEdgeAssignmentCoeff
      exact tendsto_finset_prod (Finset.univ : Finset (CliqueEdgeIndex M))
        (fun e _he => hcoeff (ω e) (hω_mem e))
    have hif :
        (fun n =>
          if (∀ i : Fin M,
              E.finiteCliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) n i = 0)
          then (1 : ℂ) else 0) =ᶠ[atTop]
        (fun _n =>
          if (∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0)
          then (1 : ℂ) else 0) := by
      filter_upwards
        [E.finiteCliqueFrequencyBalance_all_zero_iff_eventually
          (E.extendCliqueEdgeAssignment ω)] with n hn
      by_cases hfin :
          ∀ i : Fin M,
            E.finiteCliqueFrequencyBalance
              (E.extendCliqueEdgeAssignment ω) n i = 0
      · have hcompact :
            ∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0 :=
          hn.mp hfin
        simp [hfin, hcompact]
      · have hcompact :
            ¬ ∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0 := by
          intro hc
          exact hfin (hn.mpr hc)
        simp [hfin, hcompact]
    have hif_tendsto :
        Tendsto
          (fun n =>
            if (∀ i : Fin M,
                E.finiteCliqueFrequencyBalance
                  (E.extendCliqueEdgeAssignment ω) n i = 0)
            then (1 : ℂ) else 0)
          atTop
          (𝓝
            (if (∀ i : Fin M,
                E.cliqueFrequencyBalance
                  (E.extendCliqueEdgeAssignment ω) i = 0)
              then (1 : ℂ) else 0)) :=
      tendsto_const_nhds.congr' hif.symm
    exact (hcoeff_prod.mul hif_tendsto).congr' (Filter.Eventually.of_forall fun n => rfl)
  have hsum :
      Tendsto (fun n => ∑ ω ∈ W, finiteTerm n ω)
        atTop (𝓝 (∑ ω ∈ W, compactTerm ω)) :=
    tendsto_finset_sum W hterm
  rw [hcompact_exp]
  exact hsum.congr' hfinite_exp.symm

lemma finiteSmoothModelTrigPoly_support_subset_fejer
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    (E.finiteSmoothModelTrigPoly Q n).support ⊆
      (E.fejerTrigPoly Q).support := by
  intro γ hγ
  rw [Finsupp.mem_support_iff] at hγ ⊢
  intro hfejer
  have hzero : E.finiteSmoothModelTrigPoly Q n γ = 0 := by
    rw [E.finiteSmoothModelTrigPoly_apply Q n γ, hfejer]
    simp
  exact hγ hzero

lemma compactSmoothTrigPoly_support_subset_fejer
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    (E.compactSmoothTrigPoly Q).support ⊆
      (E.fejerTrigPoly Q).support := by
  intro γ hγ
  rw [Finsupp.mem_support_iff] at hγ ⊢
  intro hfejer
  have hzero : E.compactSmoothTrigPoly Q γ = 0 := by
    rw [E.compactSmoothTrigPoly_apply Q γ, hfejer]
    simp
  exact hγ hzero

lemma finiteCliqueKernelDensity_finiteSmoothModelTrigPoly_tendsto_compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n z))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  simpa [compactSmooth] using
    E.finiteCliqueKernelDensity_evalFinite_tendsto_compact_of_coeff_tendsto
      (fun n => E.finiteSmoothModelTrigPoly Q n)
      (E.compactSmoothTrigPoly Q)
      (E.fejerTrigPoly Q).support
      (Filter.Eventually.of_forall
        (fun n => E.finiteSmoothModelTrigPoly_support_subset_fejer Q n))
      (E.compactSmoothTrigPoly_support_subset_fejer Q)
      (fun γ _hγ =>
        E.finiteSmoothModelTrigPoly_apply_tendsto_compactSmoothTrigPoly Q γ)

lemma finiteCliqueKernelDensity_finiteSmooth_tendsto_compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (E.finiteSmooth Q n))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  refine
    (E.finiteCliqueKernelDensity_finiteSmoothModelTrigPoly_tendsto_compactSmooth
      Q M).congr' ?_
  filter_upwards
    [E.finiteSmooth_eq_evalFinite_finiteSmoothModelTrigPoly_eventually Q]
    with n hn
  haveI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  haveI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  congr 1
  funext z
  exact (hn z).symm

lemma compactSmooth_cliqueDensity_integral_re_eq_continuousCliqueDensity
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)).re =
      continuousCliqueDensity E.haar M (E.compactSmoothReal Q) := by
  classical
  let μ : Measure (Fin M → E.CompactAddDual) :=
    Measure.pi (fun _ : Fin M => E.haar)
  have hprod :
      (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2)) =
      (fun x : Fin M → E.CompactAddDual =>
        ((∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) := by
    funext x
    calc
      (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
          =
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) := by
            refine Finset.prod_congr rfl ?_
            intro e _he
            exact E.compactSmooth_eq_ofReal_compactSmoothReal Q
              (x e.1 - x e.2)
      _ =
        ((∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) := by
            simp
  have hintegral :
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂μ) =
        ∫ x : Fin M → E.CompactAddDual,
          ((∏ e ∈ cliqueEdgePairs M,
            E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) ∂μ := by
    rw [hprod]
  have hcont :
      Continuous (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) := by
    refine continuous_finset_prod (cliqueEdgePairs M) ?_
    intro e _he
    exact Complex.continuous_ofReal.comp
      ((E.compactSmoothReal_continuous Q).comp
        ((continuous_apply e.1).sub (continuous_apply e.2)))
  have hint :
      Integrable
        (fun x : Fin M → E.CompactAddDual =>
          ∏ e ∈ cliqueEdgePairs M,
            ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hintegral]
  change RCLike.re
      (∫ x : Fin M → E.CompactAddDual,
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) ∂μ) =
    continuousCliqueDensity E.haar M (E.compactSmoothReal Q)
  rw [← integral_re (μ := μ) (f := fun x : Fin M → E.CompactAddDual =>
    ∏ e ∈ cliqueEdgePairs M,
      ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) hint]
  have hre_fun :
      (fun x : Fin M → E.CompactAddDual =>
        RCLike.re
          (∏ e ∈ cliqueEdgePairs M,
            ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ))) =
      (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) := by
    funext x
    have hprod_cast :=
      (Complex.ofReal_prod (cliqueEdgePairs M)
        (fun e : Fin M × Fin M =>
          E.compactSmoothReal Q (x e.1 - x e.2))).symm
    rw [hprod_cast]
    exact Complex.ofReal_re _
  rw [hre_fun]
  simp [continuousCliqueDensity, continuousCliqueKernel,
    continuousCliqueEdgePairs, cliqueEdgePairs, μ]

lemma finiteCliqueKernelDensity_finiteSmooth_re_tendsto_compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
         letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
         finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (E.finiteSmooth Q n)).re)
      atTop
      (𝓝 (continuousCliqueDensity E.haar M (E.compactSmoothReal Q))) := by
  have hcomplex :=
    E.finiteCliqueKernelDensity_finiteSmooth_tendsto_compactSmooth Q M
  have hre :=
    (Complex.continuous_re.tendsto
      (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar))).comp hcomplex
  simpa [E.compactSmooth_cliqueDensity_integral_re_eq_continuousCliqueDensity Q M]
    using hre

end CayleyExtraction

end

end Erdos42.CompactCayley
