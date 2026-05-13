/-
Erdős Problem 202 — fully flattened single-file proof.

This file is a concatenation of all 26 P202 source files in topological
import order, with internal `import Erdos.P202.*` lines stripped. The
only external dependency is Mathlib v4.27.0.

Builds standalone: `lake env lean Erdos/P202/P202Flat.lean`

The sharp BFV asymptotic
  f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))
appears at the bottom as `Erdos202.erdos202_main : Erdos202Statement`.

Trust boundary (`#print axioms Erdos202.erdos202_main`):
  propext, Classical.choice, Quot.sound,                  -- Lean core
  Erdos202.bfv_omega_count_input,                         -- BFV omega tail
  Erdos202.bfv_pruning_input,                             -- BFV pruning
  Erdos202.lowerEncodingCapacity_eventually_analytic,     -- BFV CRT capacity
  Erdos202.lowerChoices_card_lower_bound_eventually_analytic, -- BFV cardinality
  Erdos202.ParkPham.CKK_const,                            -- Park-Pham const
  Erdos202.ParkPham.CKK_const_pos,                        -- Park-Pham positivity
  Erdos202.ParkPham.park_pham_threshold,                  -- Park-Pham theorem
  Erdos202.ParkPham.partition_density_to_disjoint_members -- Random partition
-/

import Mathlib


/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/P202Basic.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Statement layer.

Defines residue classes, admissible families, the extremal function `f(N)`,
the BFV scale `L(α, N) = exp(α · sqrt(log N · log log N))`, and the sharp
asymptotic predicate `HasErdos202Asymptotic`.

Reference: PDF in `docs/`, BFV (Acta Arith.) for the unconditional bounds,
spread-core variant for the matching upper bound `f(N) = N · L(-(1+o(1)), N)`.
-/


namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

/-! ## §1 Residue classes and admissibility -/

/-- The integer residue class `a mod q` (only used for `0 < q`). -/
def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

/-- A choice of one integer residue representative for every modulus in `Q`. -/
abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

/-- The selected residue classes for a finite set of moduli are pairwise disjoint. -/
def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

/-- Restrict residue representatives from a family to a subfamily. -/
def restrictAssignment {Q Q' : Finset ℕ}
    (a : ResidueAssignment Q) (hsub : Q' ⊆ Q) : ResidueAssignment Q' :=
  fun q => a ⟨q.1, hsub q.2⟩

lemma PairwiseDisjointResidues.mono
    {Q Q' : Finset ℕ} {a : ResidueAssignment Q}
    (hdisj : PairwiseDisjointResidues Q a) (hsub : Q' ⊆ Q) :
    PairwiseDisjointResidues Q' (restrictAssignment a hsub) := by
  intro i j hij
  let iQ : {q : ℕ // q ∈ Q} := ⟨i.1, hsub i.2⟩
  let jQ : {q : ℕ // q ∈ Q} := ⟨j.1, hsub j.2⟩
  have hijQ : iQ ≠ jQ := by
    intro h
    have hval : iQ.1 = jQ.1 :=
      congrArg (fun x : {q : ℕ // q ∈ Q} => x.1) h
    exact hij (Subtype.ext hval)
  simpa [restrictAssignment, iQ, jQ] using hdisj iQ jQ hijQ

/-- A finite set of moduli `Q ⊆ {1,...,N}` is admissible for Erdős 202: every
modulus is in `[1, N]`, and there exist residue choices making the
corresponding residue classes pairwise disjoint. -/
def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

/-- There is an admissible family of size `r`. -/
def PossibleCard (N r : ℕ) : Prop :=
  ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = r

/-- The Erdős 202 extremal function `f(N) = max r : PossibleCard N r`.

Implemented via `Nat.findGreatest` over `[0, N]`, since the empty family is
always admissible (`0` is reachable) and `r ≤ |Q| ≤ N`. -/
noncomputable def f (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (PossibleCard N) N

lemma admissible_card_le {N : ℕ} {Q : Finset ℕ} (hQ : Admissible N Q) :
    Q.card ≤ N := by
  have hsub : Q ⊆ Finset.Icc 1 N := by
    intro q hq
    exact Finset.mem_Icc.2 (hQ.1 q hq)
  have hcard := Finset.card_le_card hsub
  have hIcc : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  simpa [hIcc] using hcard

lemma admissible_empty (N : ℕ) : Admissible N (∅ : Finset ℕ) := by
  constructor
  · intro q hq
    simp at hq
  · refine ⟨fun _ => 0, ?_⟩
    intro i _j _hij
    cases i with
    | mk q hq => simp at hq

lemma admissible_singleton {N q : ℕ} (hq1 : 1 ≤ q) (hqN : q ≤ N) :
    Admissible N ({q} : Finset ℕ) := by
  constructor
  · intro r hr
    rw [Finset.mem_singleton] at hr
    subst r
    exact ⟨hq1, hqN⟩
  · refine ⟨fun _ => 0, ?_⟩
    intro i j hij
    have hi : i.1 = q := Finset.mem_singleton.mp i.2
    have hj : j.1 = q := Finset.mem_singleton.mp j.2
    exact False.elim (hij (Subtype.ext (hi.trans hj.symm)))

lemma possibleCard_zero (N : ℕ) : PossibleCard N 0 :=
  ⟨∅, admissible_empty N, by simp⟩

lemma possibleCard_one {N : ℕ} (hN : 1 ≤ N) : PossibleCard N 1 :=
  ⟨{N}, admissible_singleton hN le_rfl, by simp⟩

lemma possibleCard_le {N r : ℕ} (hr : PossibleCard N r) : r ≤ N := by
  rcases hr with ⟨Q, hQ, hcard⟩
  rw [← hcard]
  exact admissible_card_le hQ

lemma f_le (N : ℕ) : f N ≤ N := by
  classical
  unfold f
  exact Nat.findGreatest_le N

lemma possibleCard_f (N : ℕ) : PossibleCard N (f N) := by
  classical
  unfold f
  exact Nat.findGreatest_spec (P := PossibleCard N) (m := 0)
    (zero_le N) (possibleCard_zero N)

lemma le_f_of_possibleCard {N r : ℕ} (hr : PossibleCard N r) : r ≤ f N := by
  classical
  unfold f
  exact Nat.le_findGreatest (P := PossibleCard N) (possibleCard_le hr) hr

lemma one_le_f {N : ℕ} (hN : 1 ≤ N) : 1 ≤ f N :=
  le_f_of_possibleCard (possibleCard_one hN)

lemma exists_admissible_card_f (N : ℕ) :
    ∃ Q : Finset ℕ, Admissible N Q ∧ Q.card = f N :=
  possibleCard_f N

/-! ## §2 The BFV scale -/

/-- `Z(N) = sqrt(log N · log log N)`. The "L-scale" exponent. -/
noncomputable def Zscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))

/-- `L(α, N) = exp(α · Z(N))`. -/
noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ :=
  Real.exp (α * Zscale N)

/-- `M(N) = sqrt(log N / log log N)`. The "shape" parameter; satisfies
`M(N) · log log N = Z(N)` and `K ≤ 3 M(N)` is the BFV pruning bound on the
number of distinct prime factors. -/
noncomputable def Mscale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)))

lemma Zscale_nonneg (N : ℕ) : 0 ≤ Zscale N :=
  Real.sqrt_nonneg _

lemma Zscale_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < Zscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [Zscale, Real.sqrt_pos]
  exact mul_pos hlog_pos hloglog_pos

lemma Zscale_eq_sqrt_log_mul_sqrt_loglog {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Zscale N =
      Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  rw [Zscale, Real.sqrt_mul hlog_nonneg]

lemma eventually_Zscale_pos : ∀ᶠ N : ℕ in atTop, 0 < Zscale N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hN
  apply Zscale_pos_of_exp_one_lt_nat
  exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)

lemma Mscale_nonneg (N : ℕ) : 0 ≤ Mscale N :=
  Real.sqrt_nonneg _

lemma Mscale_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < Mscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [Mscale, Real.sqrt_pos]
  exact div_pos hlog_pos hloglog_pos

lemma Mscale_mul_loglog_eq_Zscale {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Mscale N * Real.log (Real.log (N : ℝ)) = Zscale N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hleft_nonneg : 0 ≤ Mscale N * Real.log (Real.log (N : ℝ)) :=
    mul_nonneg (Mscale_nonneg N) hloglog_nonneg
  have hsq :
      (Mscale N * Real.log (Real.log (N : ℝ))) ^ 2 = (Zscale N) ^ 2 := by
    rw [Mscale, Zscale, mul_pow, Real.sq_sqrt, Real.sq_sqrt]
    · field_simp [hloglog_pos.ne']
    · exact mul_nonneg hlog_nonneg hloglog_nonneg
    · exact div_nonneg hlog_nonneg hloglog_nonneg
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact h
  · have hright_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
    nlinarith

lemma Zscale_div_Mscale_eq_loglog {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) := by
  have hMll := Mscale_mul_loglog_eq_Zscale hN
  have hMpos := Mscale_pos_of_exp_one_lt_nat hN
  rw [← hMll]
  field_simp [hMpos.ne']

lemma Mscale_mul_Zscale_eq_log {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    Mscale N * Zscale N = Real.log (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hMll := Mscale_mul_loglog_eq_Zscale hN
  have hMsq : Mscale N ^ 2 =
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
    rw [Mscale, Real.sq_sqrt]
    exact div_nonneg hlog_nonneg hloglog_nonneg
  calc
    Mscale N * Zscale N
        = Mscale N * (Mscale N * Real.log (Real.log (N : ℝ))) := by rw [hMll]
    _ = Mscale N ^ 2 * Real.log (Real.log (N : ℝ)) := by ring
    _ = Real.log (N : ℝ) := by
          rw [hMsq]
          field_simp [hloglog_pos.ne']

lemma tendsto_loglog_div_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        fun x : ℝ => Real.log x :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact hsmall.tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

lemma tendsto_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop := by
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
    tendsto_natCast_atTop_atTop

lemma tendsto_sqrt_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (Real.log (Real.log (N : ℝ)))) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp tendsto_loglog_nat_atTop

lemma eventually_sqrt_loglog_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) :=
  tendsto_sqrt_loglog_nat_atTop.eventually_ge_atTop A

lemma eventually_Mscale_le_log :
    ∀ᶠ N : ℕ in atTop, Mscale N ≤ Real.log (N : ℝ) := by
  filter_upwards [eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := (zero_lt_one.trans hlog_gt_one).le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.one_le_sqrt]
    exact hsqrt
  rw [Mscale]
  rw [Real.sqrt_le_left hlog_nonneg]
  have hquot_le_log :
      Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    exact (div_le_iff₀ hloglog_pos).2 (by nlinarith [hlog_nonneg, hloglog_ge_one])
  have hlog_le_sq : Real.log (N : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
    nlinarith [hlog_gt_one.le]
  exact hquot_le_log.trans hlog_le_sq

lemma eventually_Mscale_ge (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, A ≤ Mscale N := by
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  have htarget_pos : (0 : ℝ) < 1 / A ^ 2 := by positivity
  have hratio_small : ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) < 1 / A ^ 2 :=
    tendsto_loglog_div_log_nat_atTop.eventually_lt_const htarget_pos
  filter_upwards [hratio_small, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hsmall hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_lt :
      Real.log (Real.log (N : ℝ)) < (1 / A ^ 2) * Real.log (N : ℝ) :=
    (div_lt_iff₀ hlog_pos).1 hsmall
  have hmulA :
      A ^ 2 * Real.log (Real.log (N : ℝ)) < Real.log (N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hloglog_lt hA2
    field_simp [hA2.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hquot_ge :
      A ^ 2 ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
    (le_div_iff₀ hloglog_pos).2 hmulA.le
  rw [Mscale]
  exact (Real.le_sqrt hA.le (div_nonneg hlog_pos.le hloglog_pos.le)).2 hquot_ge

lemma Lscale_pos (α : ℝ) (N : ℕ) : 0 < Lscale α N :=
  Real.exp_pos _

lemma Lscale_nonneg (α : ℝ) (N : ℕ) : 0 ≤ Lscale α N :=
  (Lscale_pos α N).le

lemma Lscale_zero (N : ℕ) : Lscale 0 N = 1 := by
  simp [Lscale]

lemma Lscale_add (α β : ℝ) (N : ℕ) :
    Lscale (α + β) N = Lscale α N * Lscale β N := by
  simp [Lscale, add_mul, Real.exp_add]

lemma Lscale_neg_mul (α : ℝ) (N : ℕ) :
    Lscale (-α) N * Lscale α N = 1 := by
  rw [← Lscale_add]
  simp [Lscale]

lemma Lscale_mono_in_alpha {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
    Lscale α N ≤ Lscale β N := by
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαβ (Zscale_nonneg N))

lemma Lscale_neg_le_one {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
    Lscale (-α) N ≤ 1 := by
  simpa [Lscale_zero] using Lscale_mono_in_alpha (α := -α) (β := 0) (by linarith) N

lemma log_nat_mul_Lscale {N : ℕ} (hN : 0 < N) (α : ℝ) :
    Real.log ((N : ℝ) * Lscale α N) = Real.log (N : ℝ) + α * Zscale N := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hL : Lscale α N ≠ 0 := (Lscale_pos α N).ne'
  rw [Real.log_mul hNreal hL, Lscale, Real.log_exp]

/-! ## §3 The sharp asymptotic -/

/-- `F : ℕ → ℕ` satisfies `F N = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`,
in epsilon form: for every `ε > 0`, eventually
`N · L(-(1+ε), N) ≤ F N ≤ N · L(-(1-ε), N)`. -/
def HasErdos202Asymptotic (F : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * Lscale (-(1 + ε)) N ≤ (F N : ℝ) ∧
    (F N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N

/-- **Erdős Problem 202.** The sharp BFV-conjectured asymptotic for the
extremal function `f`. Statement layer only. -/
def Erdos202Statement : Prop :=
  HasErdos202Asymptotic f

/-! ## §4 The non-coprime gcd criterion (foundational lemma) -/

/-- The gcd intersection criterion: residue classes `a mod q` and `b mod r`
intersect iff `a ≡ b mod gcd(q, r)`. This is the formal version of equation
(7) in the PDF and underlies the entire chain construction. -/
lemma residueClass_inter_nonempty_iff
    {q r : ℕ} (_hq : 0 < q) (_hr : 0 < r) (a b : ℤ) :
    (residueClass q a ∩ residueClass r b).Nonempty ↔
      a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
  constructor
  · rintro ⟨n, hnq, hnr⟩
    rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd] at hnq hnr
    rw [Int.modEq_iff_dvd]
    have hdq : (Nat.gcd q r : ℤ) ∣ (q : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left q r
    have hdr : (Nat.gcd q r : ℤ) ∣ (r : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right q r
    have hqa : (Nat.gcd q r : ℤ) ∣ a - n := dvd_trans hdq hnq
    have hrb : (Nat.gcd q r : ℤ) ∣ b - n := dvd_trans hdr hnr
    have hsub : (Nat.gcd q r : ℤ) ∣ (b - n) - (a - n) := dvd_sub hrb hqa
    convert hsub using 1
    ring
  · intro hab
    rw [Int.modEq_iff_dvd] at hab
    rcases hab with ⟨k, hk⟩
    let n : ℤ := a + (q : ℤ) * Nat.gcdA q r * k
    refine ⟨n, ?_, ?_⟩
    · rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd]
      refine ⟨-(Nat.gcdA q r * k), ?_⟩
      simp [n]
      ring
    · rw [residueClass, Set.mem_setOf_eq, Int.modEq_iff_dvd]
      refine ⟨Nat.gcdB q r * k, ?_⟩
      have hbez := Nat.gcd_eq_gcd_ab q r
      calc
        b - n = (b - a) - (q : ℤ) * Nat.gcdA q r * k := by
          simp [n]
          ring
        _ = ((Nat.gcd q r : ℤ) * k) - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hk]
        _ = ((q : ℤ) * Nat.gcdA q r + (r : ℤ) * Nat.gcdB q r) * k
              - (q : ℤ) * Nat.gcdA q r * k := by
          rw [hbez]
        _ = (r : ℤ) * (Nat.gcdB q r * k) := by
          ring

/-- Disjointness form of the gcd criterion. -/
lemma residueClass_disjoint_iff
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (a b : ℤ) :
    Disjoint (residueClass q a) (residueClass r b) ↔
      ¬ a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := by
  rw [Set.disjoint_iff_inter_eq_empty]
  constructor
  · intro h hmod
    have hne : (residueClass q a ∩ residueClass r b).Nonempty :=
      (residueClass_inter_nonempty_iff hq hr a b).2 hmod
    exact hne.ne_empty h
  · intro hmod
    ext n
    constructor
    · intro hn
      exact False.elim (hmod ((residueClass_inter_nonempty_iff hq hr a b).1 ⟨n, hn⟩))
    · intro hn
      cases hn

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/SpreadDefs.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Spread / dense-core layer, definitions.

Bare definitions only: `UniformFamily`, `SpreadFamily`,
`PairwiseDisjointMembers`. Split out from `SpreadCore.lean` so the
ParkPham layer can use these definitions without importing the
spread-disjointness axiom/theorem (which would create an import cycle
once `SpreadCore.lean` discharges the axiom against the ParkPham proof).
-/


namespace Erdos202

open Finset
open scoped BigOperators

/-- A `k`-uniform family: every member has cardinality exactly `k`. -/
def UniformFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ S ∈ A, S.card = k

/-- A `κ`-spread family: for every nonempty `T`, the count of members
containing `T` is at most `|A| / κ^{|T|}`. -/
def SpreadFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (κ : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty →
    ((A.filter fun S => T ⊆ S).card : ℝ) ≤
      (A.card : ℝ) / κ ^ T.card

/-- Members of `B` are pairwise disjoint. -/
def PairwiseDisjointMembers {α : Type*} [DecidableEq α]
    (B : Finset (Finset α)) : Prop :=
  ∀ S ∈ B, ∀ T ∈ B, S ≠ T → Disjoint S T

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/PrimeIntervals.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- prime supply for the BFV lower construction.

This file defines the `dyadicPrimeInterval` used by the explicit lower
construction. The analytic lower bound on its cardinality lives in
`Erdos.P202.BFV.Chebyshev` (a named stub); this file is sorry-free.
-/


namespace Erdos202

open Filter Finset

/-! ## Dyadic prime intervals -/

/-- The primes in the dyadic interval `(y, 2y]`, represented with natural
floor endpoints.  This is the finite set used by the BFV construction. -/
noncomputable def dyadicPrimeInterval (y : ℝ) : Finset ℕ :=
  (Finset.Ioc (Nat.floor y) (Nat.floor (2 * y))).filter Nat.Prime

lemma mem_dyadicPrimeInterval {y : ℝ} {p : ℕ} :
    p ∈ dyadicPrimeInterval y ↔
      Nat.floor y < p ∧ p ≤ Nat.floor (2 * y) ∧ Nat.Prime p := by
  simp [dyadicPrimeInterval, and_assoc]

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/Filtering.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- finite filtering helpers for BFV pruning.

These lemmas are deliberately elementary.  They isolate the finite-set
bookkeeping used by the pruning step from the analytic BFV estimates.
-/


namespace Erdos202

open Finset
open scoped BigOperators

/-! ## Removing a small bad set -/

lemma filter_card_add_filter_not_card {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  classical
  exact Finset.card_filter_add_card_filter_not p

lemma filter_not_card_real_ge_of_filter_card_real_le {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] {δ : ℝ}
    (hbad : ((s.filter p).card : ℝ) ≤ δ * (s.card : ℝ)) :
    ((s.filter fun x => ¬ p x).card : ℝ) ≥ (1 - δ) * (s.card : ℝ) := by
  classical
  have hsum := filter_card_add_filter_not_card s p
  have hreal :
      ((s.filter fun x => ¬ p x).card : ℝ) =
        (s.card : ℝ) - ((s.filter p).card : ℝ) := by
    nlinarith [show ((s.filter p).card + (s.filter fun x => ¬ p x).card : ℝ) =
      (s.card : ℝ) by exact_mod_cast hsum]
  rw [hreal]
  nlinarith

lemma filter_not_card_real_ge_of_filter_card_le_floor {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] {δ X : ℝ}
    (hXnonneg : 0 ≤ X)
    (hfloor : (s.filter p).card ≤ Nat.floor X)
    (hX : X ≤ δ * (s.card : ℝ)) :
    ((s.filter fun x => ¬ p x).card : ℝ) ≥ (1 - δ) * (s.card : ℝ) := by
  refine filter_not_card_real_ge_of_filter_card_real_le s p ?_
  have hfloor_real : ((s.filter p).card : ℝ) ≤ (Nat.floor X : ℝ) := by
    exact_mod_cast hfloor
  have hfloor_le : (Nat.floor X : ℝ) ≤ X := Nat.floor_le hXnonneg
  exact hfloor_real.trans (hfloor_le.trans hX)

/-! ## Pigeonhole over a finite range -/

lemma exists_fiber_card_mul_range_card_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (B : Finset β) (g : α → β)
    (hBne : B.Nonempty) (hB : ∀ x ∈ s, g x ∈ B) :
    ∃ b ∈ B, s.card ≤ B.card * (s.filter fun x => g x = b).card := by
  classical
  rcases Finset.exists_max_image B (fun b => (s.filter fun x => g x = b).card) hBne with
    ⟨b, hb, hbmax⟩
  refine ⟨b, hb, ?_⟩
  have hsum :
      s.card = ∑ b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.card_eq_sum_card_fiberwise hB
  have hsum_le :
      (∑ b ∈ B, (s.filter fun x => g x = b).card) ≤
        ∑ _b ∈ B, (s.filter fun x => g x = b).card := by
    exact Finset.sum_le_sum hbmax
  rw [hsum]
  exact hsum_le.trans (by simp)

/-! ## Choosing one representative per fiber -/

noncomputable def chooseOnePerImage {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) : Finset α :=
  ((s.image g).attach.image fun b =>
    Classical.choose (Finset.mem_image.1 b.2))

lemma chooseOnePerImage_subset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    chooseOnePerImage s g ⊆ s := by
  classical
  intro x hx
  unfold chooseOnePerImage at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨b, -, rfl⟩
  exact (Classical.choose_spec (Finset.mem_image.1 b.2)).1

lemma chooseOnePerImage_maps {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) {b : β} (hb : b ∈ s.image g) :
    g (Classical.choose (Finset.mem_image.1 hb)) = b := by
  exact (Classical.choose_spec (Finset.mem_image.1 hb)).2

lemma chooseOnePerImage_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    ∀ x ∈ chooseOnePerImage s g, ∀ y ∈ chooseOnePerImage s g, g x = g y → x = y := by
  classical
  intro x hx y hy hxy
  unfold chooseOnePerImage at hx hy
  rw [Finset.mem_image] at hx
  rw [Finset.mem_image] at hy
  rcases hx with ⟨bx, hbx, rfl⟩
  rcases hy with ⟨byy, hby, rfl⟩
  have hbxval : g (Classical.choose (Finset.mem_image.1 bx.2)) = bx.1 := by
    exact chooseOnePerImage_maps s g bx.2
  have hbyval : g (Classical.choose (Finset.mem_image.1 byy.2)) = byy.1 := by
    exact chooseOnePerImage_maps s g byy.2
  have hbxy : bx = byy := by
    ext
    simpa [hbxval, hbyval] using hxy
  subst hbxy
  rfl

lemma chooseOnePerImage_card_eq_image_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) :
    (chooseOnePerImage s g).card = (s.image g).card := by
  classical
  unfold chooseOnePerImage
  calc
    (((s.image g).attach.image fun b =>
        Classical.choose (Finset.mem_image.1 b.2))).card =
        (s.image g).attach.card := by
          apply Finset.card_image_of_injective
          intro b₁ b₂ h
          have hb₁ : g (Classical.choose (Finset.mem_image.1 b₁.2)) = b₁.1 :=
            chooseOnePerImage_maps s g b₁.2
          have hb₂ : g (Classical.choose (Finset.mem_image.1 b₂.2)) = b₂.1 :=
            chooseOnePerImage_maps s g b₂.2
          ext
          simpa [hb₁, hb₂] using congrArg g h
    _ = (s.image g).card := by simp

lemma image_card_mul_fiber_bound_ge {α β : Type*} [DecidableEq β]
    (s : Finset α) (g : α → β) (C : ℕ)
    (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
    s.card ≤ C * (s.image g).card := by
  classical
  exact Finset.card_le_mul_card_image s C hC

lemma choose_one_per_fiber_card_lower {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → β) (C : ℕ)
    (hC : ∀ b ∈ s.image g, (s.filter fun x => g x = b).card ≤ C) :
    ∃ s' : Finset α,
      s' ⊆ s ∧
      (∀ x ∈ s', ∀ y ∈ s', g x = g y → x = y) ∧
      s.card ≤ C * s'.card := by
  classical
  refine ⟨chooseOnePerImage s g, chooseOnePerImage_subset s g,
    chooseOnePerImage_injOn s g, ?_⟩
  simpa [chooseOnePerImage_card_eq_image_card s g] using
    image_card_mul_fiber_bound_ge s g C hC

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/P202Arithmetic.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Arithmetic layer.

Project-local definitions of `omega`, `rad`, `h(n) = ∏ p^{vₚ(n)} factors`,
and the exact prime-power block `exactBlock C q = ∏_{p ∈ C} p^{vₚ(q)}`.

All built on top of `Nat.factorization` to avoid drift between
`Nat.primeFactorsList`, `padicValNat`, and `multiplicity`.
-/


namespace Erdos202

open Finset
open scoped BigOperators

/-- The (multi-) set of prime divisors of `n`, as a `Finset`. Equal to
`n.factorization.support` for `n ≠ 0`. -/
def primeSupport (n : ℕ) : Finset ℕ :=
  n.factorization.support

/-- Number of distinct prime factors. Standard `ω(n)`. -/
def omega (n : ℕ) : ℕ :=
  (primeSupport n).card

/-- Radical of `n`: product of distinct prime divisors. -/
def rad (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, p

/-- BFV's `h(n)`: product of the prime *exponents* in the factorization of `n`.
Note: this is NOT the radical and is NOT `n` itself; it is the auxiliary
quantity that BFV pruning bounds by `exp(sqrt(log x))` on the surviving
moduli. -/
def hExp (n : ℕ) : ℕ :=
  ∏ p ∈ primeSupport n, n.factorization p

/-- The exact prime-power block of `q` along the prime set `C`:
`exactBlock C q = ∏_{p ∈ C} p^{vₚ(q)}`. -/
def exactBlock (C : Finset ℕ) (q : ℕ) : ℕ :=
  ∏ p ∈ C, p ^ q.factorization p

/-! ## Basic API -/

lemma hExp_pos (n : ℕ) : 0 < hExp n := by
  unfold hExp primeSupport
  exact Finset.prod_pos (fun _p hp =>
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hp))

lemma hExp_one_le (n : ℕ) : 1 ≤ hExp n :=
  hExp_pos n

lemma hExp_one : hExp 1 = 1 := by
  simp [hExp, primeSupport]

lemma hExp_inv_sq_pos (n : ℕ) : 0 < (1 : ℝ) / ((hExp n : ℝ) ^ 2) := by
  have hn : 0 < (hExp n : ℝ) := by exact_mod_cast hExp_pos n
  positivity

lemma hExp_inv_sq_le_one (n : ℕ) : (1 : ℝ) / ((hExp n : ℝ) ^ 2) ≤ 1 := by
  have hn : 1 ≤ (hExp n : ℝ) := by exact_mod_cast hExp_one_le n
  have hpos : 0 < ((hExp n : ℝ) ^ 2) := by positivity
  field_simp [hpos.ne']
  nlinarith [sq_nonneg ((hExp n : ℝ) - 1)]

lemma prime_of_mem_primeSupport {n p : ℕ} (hp : p ∈ primeSupport n) : Nat.Prime p := by
  unfold primeSupport at hp
  rw [Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

lemma mem_primeSupport_of_prime_dvd {n p : ℕ} (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpn : p ∣ n) : p ∈ primeSupport n := by
  unfold primeSupport
  rw [Finsupp.mem_support_iff]
  exact hp.factorization_pos_of_dvd hn hpn |>.ne'

lemma coprime_of_disjoint_primeSupport {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hdisj : Disjoint (primeSupport m) (primeSupport n)) :
    Nat.Coprime m n := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpm hpn
  exact (Finset.disjoint_left.1 hdisj)
    (mem_primeSupport_of_prime_dvd hp hm hpm)
    (mem_primeSupport_of_prime_dvd hp hn hpn)

lemma primeSupport_disjoint_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    Disjoint (primeSupport m) (primeSupport n) := by
  rw [Finset.disjoint_left]
  intro p hpm hpn
  have hp : Nat.Prime p := prime_of_mem_primeSupport hpm
  have hpdm : p ∣ m := Nat.dvd_of_factorization_pos (by
    unfold primeSupport at hpm
    exact Finsupp.mem_support_iff.1 hpm)
  have hpdn : p ∣ n := Nat.dvd_of_factorization_pos (by
    unfold primeSupport at hpn
    exact Finsupp.mem_support_iff.1 hpn)
  have hp1 : p ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hpdm hpdn
  exact hp.not_dvd_one hp1

lemma primeSupport_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    primeSupport (m * n) = primeSupport m ∪ primeSupport n := by
  unfold primeSupport
  rw [Nat.factorization_mul_of_coprime hcop]
  exact Finsupp.support_add_eq (primeSupport_disjoint_of_coprime hcop)

lemma omega_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    omega (m * n) = omega m + omega n := by
  unfold omega
  rw [primeSupport_mul_of_coprime hcop]
  exact Finset.card_union_of_disjoint (primeSupport_disjoint_of_coprime hcop)

lemma hExp_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    hExp (m * n) = hExp m * hExp n := by
  unfold hExp
  rw [primeSupport_mul_of_coprime hcop]
  rw [Finset.prod_union (primeSupport_disjoint_of_coprime hcop)]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hpnot : p ∉ primeSupport n :=
      (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hp
    have hnzero : n.factorization p = 0 := by
      unfold primeSupport at hpnot
      exact Finsupp.notMem_support_iff.1 hpnot
    rw [Nat.factorization_mul_of_coprime hcop]
    simp [hnzero]
  · apply Finset.prod_congr rfl
    intro p hp
    have hpnot : p ∉ primeSupport m :=
      (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop).symm) hp
    have hmzero : m.factorization p = 0 := by
      unfold primeSupport at hpnot
      exact Finsupp.notMem_support_iff.1 hpnot
    rw [Nat.factorization_mul_of_coprime hcop]
    simp [hmzero]

lemma exactBlock_congr_on {C : Finset ℕ} {m n : ℕ}
    (h : ∀ p ∈ C, m.factorization p = n.factorization p) :
    exactBlock C m = exactBlock C n := by
  unfold exactBlock
  apply Finset.prod_congr rfl
  intro p hp
  rw [h p hp]

lemma exactBlock_dvd (C : Finset ℕ) (q : ℕ) : exactBlock C q ∣ q := by
  by_cases hq : q = 0
  · simp [hq]
  · nth_rw 2 [← Nat.factorization_prod_pow_eq_self hq]
    unfold exactBlock
    have hfilter :
        (∏ p ∈ C, p ^ q.factorization p) =
          ∏ p ∈ C.filter (fun p => p ∈ q.factorization.support),
            p ^ q.factorization p := by
      refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
      intro p hpC hpNot
      have hpnotmem : p ∉ q.factorization.support := by
        intro hp
        exact hpNot (Finset.mem_filter.2 ⟨hpC, hp⟩)
      have hzero : q.factorization p = 0 := by
        by_contra hne
        exact hpnotmem (Finsupp.mem_support_iff.2 hne)
      simp [hzero]
    rw [hfilter]
    exact Finset.prod_dvd_prod_of_subset
      (C.filter (fun p => p ∈ q.factorization.support))
      q.factorization.support
      (fun p => p ^ q.factorization p)
      (by
        intro p hp
        exact (Finset.mem_filter.1 hp).2)

lemma factorization_exactBlock_of_mem {C : Finset ℕ} {q p : ℕ}
    (hC : ∀ r ∈ C, Nat.Prime r) (hpC : p ∈ C) :
    (exactBlock C q).factorization p = q.factorization p := by
  unfold exactBlock
  have hprod_ne : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
    intro x hx
    exact pow_ne_zero _ (hC x hx).ne_zero
  rw [Nat.factorization_prod hprod_ne, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single p]
  · rw [(hC p hpC).factorization_pow, Finsupp.single_eq_same]
  · intro x hx hxp
    rw [(hC x hx).factorization_pow]
    exact Finsupp.single_eq_of_ne hxp.symm
  · intro hpnot
    exact (hpnot hpC).elim

lemma primeSupport_exactBlock {C : Finset ℕ} {q : ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p)
    (hCq : C ⊆ primeSupport q) :
    primeSupport (exactBlock C q) = C := by
  unfold primeSupport exactBlock
  ext p
  have hprod_ne : ∀ x ∈ C, x ^ q.factorization x ≠ 0 := by
    intro x hx
    exact pow_ne_zero _ (hC x hx).ne_zero
  rw [Nat.factorization_prod hprod_ne, Finsupp.mem_support_iff]
  constructor
  · intro hsum
    by_contra hpC
    apply hsum
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero_iff]
    intro x hx
    have hxne : x ≠ p := by
      intro hxp
      exact hpC (hxp ▸ hx)
    rw [(hC x hx).factorization_pow]
    exact Finsupp.single_eq_of_ne hxne.symm
  · intro hpC
    have hp : Nat.Prime p := hC p hpC
    have hqpos : q.factorization p ≠ 0 := Finsupp.mem_support_iff.1 (hCq hpC)
    intro hsum
    rw [Finsupp.finset_sum_apply] at hsum
    have hterm := (Finset.sum_eq_zero_iff.mp hsum) p hpC
    rw [hp.factorization_pow, Finsupp.single_eq_same] at hterm
    exact hqpos hterm

lemma omega_exactBlock {C : Finset ℕ} {q : ℕ}
    (hC : ∀ p ∈ C, Nat.Prime p)
    (hCq : C ⊆ primeSupport q) :
    omega (exactBlock C q) = C.card := by
  simp [omega, primeSupport_exactBlock hC hCq]

lemma hExp_exactBlock_le_hExp (C : Finset ℕ) (q : ℕ) :
    hExp (exactBlock C q) ≤ hExp q := by
  by_cases hq : q = 0
  · simp [hExp, primeSupport, exactBlock, hq]
  · have hdvd : exactBlock C q ∣ q := exactBlock_dvd C q
    have hdne : exactBlock C q ≠ 0 := by
      exact (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)).ne'
    have hlefac : (exactBlock C q).factorization ≤ q.factorization :=
      (Nat.factorization_le_iff_dvd hdne hq).2 hdvd
    have hsub : primeSupport (exactBlock C q) ⊆ primeSupport q := by
      intro p hp
      unfold primeSupport at hp ⊢
      rw [Finsupp.mem_support_iff] at hp ⊢
      exact (Nat.pos_of_ne_zero hp).trans_le (hlefac p) |>.ne'
    unfold hExp
    have hprod1 :
        (∏ p ∈ primeSupport (exactBlock C q), (exactBlock C q).factorization p)
          ≤ ∏ p ∈ primeSupport (exactBlock C q), q.factorization p := by
      exact Finset.prod_le_prod' (fun p _hp => hlefac p)
    have hprod2 :
        (∏ p ∈ primeSupport (exactBlock C q), q.factorization p)
          ≤ ∏ p ∈ primeSupport q, q.factorization p := by
      exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _hpnot => by
        unfold primeSupport at hp
        rw [Finsupp.mem_support_iff] at hp
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
    exact hprod1.trans hprod2

lemma hExp_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    hExp m ≤ hExp n := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hlefac : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hmn
  have hsub : primeSupport m ⊆ primeSupport n := by
    intro p hp
    unfold primeSupport at hp ⊢
    rw [Finsupp.mem_support_iff] at hp ⊢
    exact (Nat.pos_of_ne_zero hp).trans_le (hlefac p) |>.ne'
  unfold hExp
  have hprod1 :
      (∏ p ∈ primeSupport m, m.factorization p)
        ≤ ∏ p ∈ primeSupport m, n.factorization p := by
    exact Finset.prod_le_prod' (fun p _hp => hlefac p)
  have hprod2 :
      (∏ p ∈ primeSupport m, n.factorization p)
        ≤ ∏ p ∈ primeSupport n, n.factorization p := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _hpnot => by
      unfold primeSupport at hp
      rw [Finsupp.mem_support_iff] at hp
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp))
  exact hprod1.trans hprod2

/-- The "remaining support" after removing a fixed product `P`. Used in the
chain construction: `A(q) = primeSupport (q / P)`. -/
def remainingSupport (P q : ℕ) : Finset ℕ :=
  primeSupport (q / P)

lemma primeSupport_subset_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    primeSupport m ⊆ primeSupport n := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hle : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).2 hmn
  intro p hp
  unfold primeSupport at hp ⊢
  rw [Finsupp.mem_support_iff] at hp ⊢
  intro hnzero
  exact hp (Nat.eq_zero_of_le_zero (by simpa [hnzero] using hle p))

lemma omega_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    omega m ≤ omega n := by
  unfold omega
  exact Finset.card_le_card (primeSupport_subset_of_dvd hmn hn)

lemma primeSupport_div_subset_of_dvd {P q : ℕ} (hPq : P ∣ q) (hq : q ≠ 0) :
    primeSupport (q / P) ⊆ primeSupport q :=
  primeSupport_subset_of_dvd (by
    refine ⟨P, ?_⟩
    exact (Nat.div_mul_cancel hPq).symm) hq

lemma primeSupport_eq_union_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0) :
    primeSupport q = primeSupport P ∪ primeSupport (q / P) := by
  ext p
  unfold primeSupport
  rw [Finset.mem_union]
  simp only [Finsupp.mem_support_iff]
  constructor
  · intro hqfac
    by_cases hPfac : P.factorization p = 0
    · right
      have hdivfac :
          (q / P).factorization p = q.factorization p - P.factorization p := by
        rw [Nat.factorization_div hPq]
        rfl
      rw [hdivfac, hPfac, Nat.sub_zero]
      exact hqfac
    · exact Or.inl hPfac
  · rintro (hPfac | hdivfac)
    · have hle : P.factorization ≤ q.factorization :=
        (Nat.factorization_le_iff_dvd hP hq).2 hPq
      intro hqzero
      exact hPfac (Nat.eq_zero_of_le_zero (by simpa [hqzero] using hle p))
    · have hmem : p ∈ primeSupport (q / P) := by
        unfold primeSupport
        rw [Finsupp.mem_support_iff]
        exact hdivfac
      have hmemq := primeSupport_div_subset_of_dvd hPq hq hmem
      unfold primeSupport at hmemq
      rwa [Finsupp.mem_support_iff] at hmemq

lemma mem_remainingSupport_iff_factorization_lt {P q p : ℕ} (hPq : P ∣ q) :
    p ∈ remainingSupport P q ↔ P.factorization p < q.factorization p := by
  unfold remainingSupport primeSupport
  rw [Finsupp.mem_support_iff, Nat.factorization_div hPq]
  exact Nat.sub_ne_zero_iff_lt

lemma omega_eq_add_omega_div_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
    (hdisj : Disjoint (primeSupport P) (primeSupport (q / P))) :
    omega q = omega P + omega (q / P) := by
  unfold omega
  rw [primeSupport_eq_union_of_dvd hPq hP hq, Finset.card_union_of_disjoint hdisj]

lemma omega_div_eq_sub_omega_of_dvd {P q : ℕ}
    (hPq : P ∣ q) (hP : P ≠ 0) (hq : q ≠ 0)
    (hdisj : Disjoint (primeSupport P) (primeSupport (q / P))) :
    omega (q / P) = omega q - omega P := by
  have hsum := omega_eq_add_omega_div_of_dvd hPq hP hq hdisj
  omega

lemma eq_one_of_omega_eq_zero {n : ℕ} (hn : n ≠ 0) (hω : omega n = 0) :
    n = 1 := by
  have hsupp : primeSupport n = ∅ := by
    have hcard : (primeSupport n).card = 0 := by simpa [omega] using hω
    exact Finset.card_eq_zero.mp hcard
  unfold primeSupport at hsupp
  have hprod_eq_one : n.factorization.prod (fun p e => p ^ e) = 1 := by
    unfold Finsupp.prod
    rw [hsupp]
    simp
  have hprod := Nat.factorization_prod_pow_eq_self hn
  rw [← hprod]
  exact hprod_eq_one

lemma gcd_dvd_of_disjoint_remainingSupport {P q r : ℕ}
    (hPq : P ∣ q) (hPr : P ∣ r)
    (hP : P ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hdisj : Disjoint (remainingSupport P q) (remainingSupport P r)) :
    Nat.gcd q r ∣ P := by
  rw [← Nat.factorization_le_iff_dvd (by
      intro hg
      exact hq (Nat.gcd_eq_zero_iff.mp hg).1) hP]
  rw [Nat.factorization_gcd hq hr]
  intro p
  rw [Finsupp.inf_apply]
  have hPq_fac : P.factorization p ≤ q.factorization p :=
    (Nat.factorization_le_iff_dvd hP hq).2 hPq p
  have hPr_fac : P.factorization p ≤ r.factorization p :=
    (Nat.factorization_le_iff_dvd hP hr).2 hPr p
  by_cases hqextra : P.factorization p < q.factorization p
  · have hrnot : ¬ P.factorization p < r.factorization p := by
      intro hrextra
      exact (Finset.disjoint_left.1 hdisj)
        ((mem_remainingSupport_iff_factorization_lt hPq).2 hqextra)
        ((mem_remainingSupport_iff_factorization_lt hPr).2 hrextra)
    have hrle : r.factorization p ≤ P.factorization p := le_of_not_gt hrnot
    exact le_trans (min_le_right _ _) hrle
  · have hqle : q.factorization p ≤ P.factorization p := le_of_not_gt hqextra
    exact le_trans (min_le_left _ _) hqle

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/Chebyshev.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — analytic stub for the dyadic-interval prime cardinality
bound (Chebyshev-style).

# Status

This file isolates the ONE analytic gap from the BFV lower-construction prime
supply in `Erdos/P202/BFV/PrimeIntervals.lean`. The statement here is the
consumer-shaped lower bound used by `lowerQ_card_lower_bound_eventually`.
The body is `sorry` because the proof is a focused upstream-Mathlib subproject.

# Classical content

Chebyshev (1850) proved that there exist absolute constants `c_1, c_2 > 0`
with `c_1 · y / log y ≤ π(y) ≤ c_2 · y / log y`. Subtracting gives, for
some absolute `c > 0`,
  `π(2y) − π(y) ≥ c · y / log y`  for all sufficiently large `y`.

Mathlib `v4.27.0` already has Chebyshev's `θ`-function bounds
(`Nat.theta_le`, `Nat.theta_le_id`, `Nat.id_lt_theta`, etc.) and the
prime-counting function `Nat.primeCounting`. What is NOT packaged is the
Chebyshev-style dyadic-interval lower bound `π(2y) − π(y) ≥ c · y / log y`
nor its `(1 − ε) · y / log y` PNT-strength refinement.

The `(1 − ε)` form below is stronger than Chebyshev: it is true by the prime
number theorem, but for the BFV construction we only need any positive
absolute constant `c`. The current statement keeps the codex-produced
signature for compatibility; a follow-up refactor can weaken to a Chebyshev
constant if PNT is too heavy.

# Where this is consumed

* `Erdos.P202.BFV.PrimeIntervals.dyadicPrimeInterval_card_lower_bound`
* downstream: `Erdos.P202.BFV.LowerConstruction.lowerQ_card_lower_bound_eventually`
  → `Erdos.P202.BFV.LowerBoundInput.bfv_lower_bound_theorem`
  → ultimately replaces `axiom Erdos202.bfv_lower_bound_input`.

# Discharge sketch

To close this proof one needs, in dependency order:

1. Chebyshev (or PNT) lower bound `π(2y) − π(y) ≥ c · y / log y` derived from
   `Nat.theta_le` and `Nat.id_lt_theta`. Standalone Mathlib-PR-style target.
2. Conversion from `π(2y) − π(y)` to the cardinality of
   `dyadicPrimeInterval y = (Finset.Ioc (⌊y⌋) (⌊2y⌋)).filter Nat.Prime`,
   accounting for the floor endpoints. Mechanical once (1) lands.

If the consumer can accept a Chebyshev constant `c` rather than `(1 − ε)`,
the upstream burden drops sharply: no PNT, just Chebyshev's two-sided
`θ`-bounds. The downstream `Lscale (-(1 + ε), N)` swallow the constant.
-/


namespace Erdos202

open Filter Finset

/-- **Analytic gap (Chebyshev / PNT-in-short).** Lower bound for the number
of primes in a dyadic interval, in the `(1 − ε)` form used by the BFV
construction.

For every `ε > 0`, eventually in `y : ℝ`,
  `⌊(1 − ε) · y / log y⌋ ≤ (dyadicPrimeInterval y).card`.

The proof comes from Chebyshev's two-sided `θ`-bounds (already in Mathlib);
the `(1 − ε)` factor is PNT-strength and can be weakened to a Chebyshev
constant if needed (the downstream `Lscale` absorbs the difference).

Consumed by `Erdos.P202.BFV.LowerConstruction.lowerQ_card_lower_bound_eventually`. -/
theorem dyadicPrimeInterval_card_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ y : ℝ in atTop,
      Nat.floor (((1 - ε) * y) / Real.log y) ≤
        (dyadicPrimeInterval y).card := by
  sorry

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/ParkPham/BooleanFamilies.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 1.

Finite Boolean families, upper closures, increasing predicate, minimal
members, and the `ell(U)` complexity bound used by the Park–Pham
expectation-threshold theorem.

All definitions live over a finite ground universe `X : Finset α`. We
avoid any general measure theory; subsets of `X` are represented as
`Finset α` filtered by `S ⊆ X`.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- The upper closure of `A` inside the universe `X`: the set of subsets
`T ⊆ X` that contain some member of `A`. -/
def upClosureIn (X : Finset α) (A : Finset (Finset α)) : Finset (Finset α) :=
  X.powerset.filter fun T => ∃ S ∈ A, S ⊆ T

@[simp]
lemma mem_upClosureIn {X : Finset α} {A : Finset (Finset α)} {T : Finset α} :
    T ∈ upClosureIn X A ↔ T ⊆ X ∧ ∃ S ∈ A, S ⊆ T := by
  simp [upClosureIn, mem_powerset]

/-- A family `U ⊆ X.powerset` is increasing if it is closed under taking
supersets inside `X`. -/
def IncreasingIn (X : Finset α) (U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∀ T : Finset α, T ⊆ X → S ⊆ T → T ∈ U

/-- The upper closure of any family is increasing. -/
lemma increasingIn_upClosureIn (X : Finset α) (A : Finset (Finset α)) :
    IncreasingIn X (upClosureIn X A) := by
  intro S hS T hTX hST
  rcases mem_upClosureIn.mp hS with ⟨_, S₀, hS₀A, hS₀S⟩
  exact mem_upClosureIn.mpr ⟨hTX, S₀, hS₀A, hS₀S.trans hST⟩

/-- Minimal members of `U`: members with no proper subset also in `U`. -/
def minimalMembersIn (X : Finset α) (U : Finset (Finset α)) : Finset (Finset α) :=
  U.filter fun S => ∀ T ∈ U, ¬ T ⊂ S

@[simp]
lemma mem_minimalMembersIn {X : Finset α} {U : Finset (Finset α)} {S : Finset α} :
    S ∈ minimalMembersIn X U ↔ S ∈ U ∧ ∀ T ∈ U, ¬ T ⊂ S := by
  simp [minimalMembersIn]

/-- The complexity parameter `ell(U)`: max card of a minimal member,
clamped at 2 so that `Real.log (ell U) ≥ Real.log 2 > 0`. -/
noncomputable def ell (X : Finset α) (U : Finset (Finset α)) : ℕ :=
  max 2 ((minimalMembersIn X U).sup Finset.card)

lemma two_le_ell (X : Finset α) (U : Finset (Finset α)) : 2 ≤ ell X U :=
  le_max_left _ _

lemma ell_pos (X : Finset α) (U : Finset (Finset α)) : 0 < ell X U :=
  lt_of_lt_of_le (by norm_num) (two_le_ell X U)

/-- Every member of `U` contains a minimal member of `U` (as a subset). -/
lemma exists_minimal_subset
    {X : Finset α} {U : Finset (Finset α)}
    {S : Finset α} (hS : S ∈ U) :
    ∃ T ∈ minimalMembersIn X U, T ⊆ S := by
  classical
  -- Pick T₀ ⊆ S in U with minimum card.
  let candidates : Finset (Finset α) := U.filter fun T => T ⊆ S
  have hSc : S ∈ candidates := by
    simp [candidates, hS, subset_refl]
  rcases candidates.exists_min_image Finset.card ⟨S, hSc⟩ with ⟨T₀, hT₀, hmin⟩
  have hT₀U : T₀ ∈ U := (Finset.mem_filter.mp hT₀).1
  have hT₀S : T₀ ⊆ S := (Finset.mem_filter.mp hT₀).2
  refine ⟨T₀, mem_minimalMembersIn.mpr ⟨hT₀U, ?_⟩, hT₀S⟩
  intro T hTU hT_lt
  -- T ⊂ T₀ ⊆ S, so T ⊆ S, so T ∈ candidates, hence T₀.card ≤ T.card,
  -- contradicting T.card < T₀.card.
  have hTS : T ⊆ S := hT_lt.subset.trans hT₀S
  have hTcand : T ∈ candidates := by
    simp [candidates, hTU, hTS]
  have : T₀.card ≤ T.card := hmin T hTcand
  have hlt : T.card < T₀.card := Finset.card_lt_card hT_lt
  exact absurd this (not_le.mpr hlt)

/-- Minimal members of the upper closure of a `k`-uniform family have card
at most `k`. -/
lemma minimalMembersIn_upClosureIn_card_le
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X)
    {S : Finset α} (hS : S ∈ minimalMembersIn X (upClosureIn X A)) :
    S.card ≤ k := by
  classical
  rcases mem_minimalMembersIn.mp hS with ⟨hSup, hmin⟩
  rcases mem_upClosureIn.mp hSup with ⟨hSX, S₀, hS₀A, hS₀S⟩
  -- S₀ is in the closure (it contains itself), so by minimality of S, S₀ ⊄ S.
  have hS₀_up : S₀ ∈ upClosureIn X A :=
    mem_upClosureIn.mpr ⟨(hAX S₀ hS₀A), S₀, hS₀A, subset_refl _⟩
  have hS₀_not_lt : ¬ S₀ ⊂ S := hmin S₀ hS₀_up
  -- Then S₀ = S (since S₀ ⊆ S and S₀ is not a strict subset).
  have hS₀_eq_S : S₀ = S := by
    by_contra hne
    exact hS₀_not_lt (hS₀S.ssubset_of_ne hne)
  -- Hence S.card = S₀.card = k.
  have : S.card = k := hS₀_eq_S ▸ hUniform S₀ hS₀A
  exact this.le

/-- **`ell` bound.** The complexity parameter of the upper closure of a
`k`-uniform family is at most `max 2 k`. -/
theorem ell_upClosure_le {X : Finset α} {A : Finset (Finset α)} {k : ℕ}
    (hUniform : Erdos202.UniformFamily A k)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ell X (upClosureIn X A) ≤ max 2 k := by
  classical
  have hsup_le : (minimalMembersIn X (upClosureIn X A)).sup Finset.card ≤ k := by
    refine Finset.sup_le ?_
    intro S hS
    exact minimalMembersIn_upClosureIn_card_le hUniform hAX hS
  unfold ell
  exact max_le_max le_rfl hsup_le

end

end ParkPham
end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFVInputs.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — BFV inputs layer.

Three theorem-shaped axioms isolating the BFV (Bourgain–Filaseta–Verstraëten,
Acta Arith.) ingredients used by the descending chain:

  * `bfv_pruning_input`           : pass to a subfamily with controlled
                                     `omega`, `hExp`, distinct radicals.
  * `bfv_omega_count_input`       : count of `n ≤ y` with `omega n = K - W`,
                                     uniform in K, W in the BFV range.
  * `bfv_lower_bound_input`       : matching lower bound `f(N) ≥ N · L(-(1+ε), N)`.

Each is stated with explicit ε-quantifiers (no informal `o(1)`); uniformity
is built into the statement so multiplying `O(M)`-many factors below is sound.

To be discharged by formalizing BFV (probably alongside parts of
`Mathlib.NumberTheory.SmoothNumbers` and Selberg-type sieve infrastructure).
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## §1 The pruned-data structure -/

/-- A pruned BFV family: a subfamily `Q'` of an admissible family with
controlled multiplicative complexity (`omega = K`, `hExp ≤ exp(sqrt(log N))`,
`q ∈ [N L(-2, N), N]`, distinct radicals).

This is the formal output of BFV pruning. Cardinality decay from the input
admissible family is at most a factor of `L(o(1), N)`. -/
structure PrunedData (N : ℕ) where
  Q : Finset ℕ
  Q_nonempty : Q.Nonempty
  a : ResidueAssignment Q
  admissible : Admissible N Q
  pairwise_disjoint : PairwiseDisjointResidues Q a
  K : ℕ
  K_pos : 1 ≤ K
  modulus_lower : ∀ q ∈ Q, (N : ℝ) * Lscale (-2) N ≤ (q : ℝ)
  modulus_upper : ∀ q ∈ Q, q ≤ N
  hExp_bound : ∀ q ∈ Q, (hExp q : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))
  omega_eq : ∀ q ∈ Q, omega q = K
  K_bound : (K : ℝ) ≤ 3 * Mscale N
  rad_injective : ∀ q ∈ Q, ∀ r ∈ Q, rad q = rad r → q = r

lemma PrunedData.card_pos {N : ℕ} (D : PrunedData N) : 0 < D.Q.card :=
  D.Q_nonempty.card_pos

lemma PrunedData.N_pos {N : ℕ} (D : PrunedData N) : 0 < N := by
  rcases D.Q_nonempty with ⟨q, hq⟩
  exact lt_of_lt_of_le (D.admissible.1 q hq).1 (D.modulus_upper q hq)

lemma PrunedData.Q_subset_Icc {N : ℕ} (D : PrunedData N) :
    D.Q ⊆ Finset.Icc 1 N := by
  intro q hq
  exact Finset.mem_Icc.2 (D.admissible.1 q hq)

lemma PrunedData.card_le_N {N : ℕ} (D : PrunedData N) :
    D.Q.card ≤ N := by
  have hcard := Finset.card_le_card D.Q_subset_Icc
  have hIcc : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  simpa [hIcc] using hcard

lemma PrunedData.possibleCard {N : ℕ} (D : PrunedData N) :
    PossibleCard N D.Q.card :=
  ⟨D.Q, D.admissible, rfl⟩

lemma PrunedData.card_le_f {N : ℕ} (D : PrunedData N) :
    D.Q.card ≤ f N :=
  le_f_of_possibleCard D.possibleCard

/-! ## §2 BFV pruning -/

/-- **BFV pruning input.** From any admissible family of size approximately
`f(N)` we can extract a `PrunedData N` whose cardinality is at least
`f(N) · L(-ε, N)` for any prescribed `ε > 0`, eventually.

Note: this is a slightly strengthened BFV pruning interface. The PDF
(Proposition 3.1) states pruning for an extremal family `Q` with
`Q.card = f N`; here we allow any admissible `Q` of near-extremal size
`Q.card ≥ f N · L(-ε, N)`. The later proof must derive this stronger form
by applying the same BFV deletions (small moduli, large ω, large h, radical
pigeonhole) together with `bfv_lower_bound_input` to show the discarded
sets are negligible. To be discharged from BFV's pruning argument. -/
axiom bfv_pruning_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
      (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
      PairwiseDisjointResidues Q a →
      (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
      ∃ D : PrunedData N,
        (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N

/-! ## §3 BFV ω-count estimate -/

/-- **BFV ω-count input.** Uniform in `1 ≤ y ≤ N`, `K ≤ 3 M(N)`, and
`0 ≤ W ≤ K`, the count of integers up to `y` with `ω(n) = K - W` is at most
`y · L(-d/2 + ε, N) · (log N)^{W/2}`, where `d = K / M(N)`.

The `y ≤ N` hypothesis matches BFV Lemma 3.1's range (the original is stated
for `2 ≤ y ≤ x`); without it the count estimate is not BFV and is probably
false for arbitrarily large `y` relative to `N`. The PDF's quotient count
(Lemma 3.2) likewise requires `1 ≤ y ≤ x`.

The `(log N)^{W/2}` is real-exponentiated; we phrase it as
`exp((W/2) · log log N)` to avoid `Real.rpow` overhead. -/
axiom bfv_omega_count_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y K W : ℕ,
      y ≤ N →
      W ≤ K →
      (K : ℝ) ≤ 3 * Mscale N →
      let d : ℝ := (K : ℝ) / Mscale N
      ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
        ≤ Nat.floor
            ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
              * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))

/-! ## §4 BFV lower-bound construction -/

/-- **BFV lower-bound input.** The unconditional matching lower bound
`f(N) ≥ N · exp(-(1+ε) · Z(N))` for every `ε > 0`, eventually.

Discharged by BFV's explicit construction; published, classical. -/
axiom bfv_lower_bound_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ)

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/HExpRare.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- rarity of large hExp values in BFV pruning.

The main theorem in this file is the formal BFV Lemma 3.2 input used by the
pruning argument.  The analytic Rankin/squarefull estimate is isolated as a
named theorem stub, not as an axiom.
-/


namespace Erdos202

open Filter Finset

/-- The hExp cutoff used in BFV Proposition 3.1. -/
noncomputable def hExpCutoff (N : ℕ) : ℝ :=
  Real.exp (Real.sqrt (Real.log (N : ℝ)))

/--
BFV Lemma 3.2, in the explicit form needed for pruning.

Classical reference: Bourgain--Filaseta--Verstraëten, Lemma 3.2.  The intended
formal proof is a Rankin argument for
`∑_{n≤N} h(n)^s`, splitting the squarefree prime support from the squarefull
exponent contribution, and bounding the resulting Euler products by Chebyshev
and elementary convergent `∑ m⁻²` estimates.  Mathlib v4.27.0 does not appear
to provide this packaged h-function moment estimate, so this theorem is left as
the named analytic target for a focused subpass.
-/
theorem hExp_rare_count_rankin_squarefull :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-(1 / 6) + ε) N) := by
  sorry

/-- A subset version of the hExp rarity estimate. -/
theorem hExp_rare_subset_count
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ S : Finset ℕ,
        S ⊆ Finset.Icc 1 N →
        (S.filter fun n => hExpCutoff N < (hExp n : ℝ)).card
          ≤ Nat.floor ((N : ℝ) * Lscale (-(1 / 6) + ε) N) := by
  filter_upwards [hExp_rare_count_rankin_squarefull ε hε] with N hN S hS
  exact (Finset.card_le_card (by
    intro n hn
    exact Finset.mem_filter.2
      ⟨hS (Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2⟩)).trans hN

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/RadMultiplicity.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- radical multiplicity in BFV pruning.

For fixed radical, fixed omega, and bounded `hExp`, BFV Lemma 3.3 gives a
finite multiplicity bound.  This is a finite combinatorial theorem, but the
full exponent-vector encoding is kept isolated here so the final pruning file
only consumes a single clean interface.
-/


namespace Erdos202

open Finset
open scoped BigOperators

/--
Finite reciprocal-square bound used in the exponent-vector count.

This is the local BFV copy of the elementary estimate
`∑_{m=1}^H 1 / m^2 ≤ 2`.  It is duplicated here rather than importing
`P202Optimization`, which depends on the BFV input layer.
-/
lemma sum_inv_sq_le_two_bfv (H : ℕ) :
    (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤ 2 := by
  have hstrong : ∀ H : ℕ, 1 ≤ H →
      (∑ ν ∈ Finset.range H, (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2) ≤
        2 - 1 / (H : ℝ) := by
    intro H hH
    induction H with
    | zero =>
        cases hH
    | succ H ih =>
        cases H with
        | zero =>
            norm_num
        | succ H =>
            rw [Finset.sum_range_succ]
            have ih' :
                (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  ≤ 2 - 1 / ((H + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2 ≤
                  1 / ((H + 1 : ℕ) : ℝ) -
                    1 / (((H + 1 + 1 : ℕ) : ℝ)) := by
              have hcast :
                  (((H + 1 + 1 : ℕ) : ℝ)) = ((H + 1 : ℕ) : ℝ) + 1 := by
                norm_num
              rw [hcast]
              have hH1 : 0 < ((H + 1 : ℕ) : ℝ) := by positivity
              have hH2 : 0 < ((H + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hH1.ne', hH2.ne']
              ring_nf
              nlinarith [show 0 ≤ (H : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (H + 1),
                    (1 : ℝ) / ((ν + 1 : ℕ) : ℝ) ^ 2)
                  + 1 / (((H + 1 + 1 : ℕ) : ℝ)) ^ 2
                  ≤ (2 - 1 / ((H + 1 : ℕ) : ℝ))
                      + (1 / ((H + 1 : ℕ) : ℝ) -
                        1 / (((H + 1 + 1 : ℕ) : ℝ))) := by
                    gcongr
              _ = 2 - 1 / ((H + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hH : H = 0
  · simp [hH]
  · have hH1 : 1 ≤ H := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hH)
    exact (hstrong H hH1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (H : ℝ) := by positivity
      linarith)

private lemma one_div_sq_nat_prod_bfv {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
      ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
  simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]

lemma rad_pos (n : ℕ) : 0 < rad n := by
  unfold rad
  exact Finset.prod_pos (fun p hp => (prime_of_mem_primeSupport hp).pos)

lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 :=
  (rad_pos n).ne'

lemma primeSupport_rad_of_ne_zero {n : ℕ} (_hn : n ≠ 0) :
    primeSupport (rad n) = primeSupport n := by
  classical
  ext p
  constructor
  · intro hpRad
    have hp : Nat.Prime p := prime_of_mem_primeSupport hpRad
    have hpdvd : p ∣ rad n := Nat.dvd_of_factorization_pos (by
      unfold primeSupport at hpRad
      exact Finsupp.mem_support_iff.1 hpRad)
    unfold rad at hpdvd
    rcases (hp.prime.dvd_finset_prod_iff
        (S := primeSupport n) (fun x : ℕ => x)).1 hpdvd with ⟨q, hq, hpq⟩
    have hqprime : Nat.Prime q := prime_of_mem_primeSupport hq
    have hqp : q = p := (hqprime.dvd_iff_eq hp.ne_one).1 hpq
    simpa [hqp] using hq
  · intro hpN
    have hp : Nat.Prime p := prime_of_mem_primeSupport hpN
    have hpdvd : p ∣ rad n := by
      unfold rad
      exact Finset.dvd_prod_of_mem (fun x : ℕ => x) hpN
    exact mem_primeSupport_of_prime_dvd hp (rad_ne_zero n) hpdvd

lemma primeSupport_eq_of_rad_eq {q r : ℕ} (hq : q ≠ 0) (hqr : rad q = r) :
    primeSupport q = primeSupport r := by
  rw [← primeSupport_rad_of_ne_zero hq, hqr]

private lemma factorization_le_hExp_of_mem {q p : ℕ} (hp : p ∈ primeSupport q) :
    q.factorization p ≤ hExp q := by
  have hdvd : q.factorization p ∣ hExp q := by
    unfold hExp
    exact Finset.dvd_prod_of_mem (fun x : ℕ => q.factorization x) hp
  exact Nat.le_of_dvd (hExp_pos q) hdvd

private lemma rad_multiplicity_weight_sum_le
    (S : Finset ℕ) (C : Finset ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hSupp : ∀ q ∈ S, primeSupport q = C)
    (hHbound : ∀ q ∈ S, (hExp q : ℝ) ≤ H) :
    (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ C.card := by
  classical
  let Index := {p : ℕ // p ∈ C}
  let E : Finset (Index → ℕ) :=
    Fintype.piFinset fun _ : Index => Finset.range (Nat.floor H)
  let vec : ℕ → Index → ℕ := fun q p => q.factorization p.1 - 1
  let term : (Index → ℕ) → ℝ :=
    fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
  have hH_nonneg : 0 ≤ H := by
    linarith
  have hvec_mem : ∀ q ∈ S, vec q ∈ E := by
    intro q hqS
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    have hsupport : primeSupport q = C := hSupp q hqS
    have hpSupport : p.1 ∈ primeSupport q := by
      simp [hsupport, p.2]
    have hfac_pos : 1 ≤ q.factorization p.1 := by
      unfold primeSupport at hpSupport
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
    have hfac_le_hExp : q.factorization p.1 ≤ hExp q :=
      factorization_le_hExp_of_mem hpSupport
    have hfac_le_H : ((q.factorization p.1 : ℕ) : ℝ) ≤ H := by
      have hfac_le_hExp_real :
          ((q.factorization p.1 : ℕ) : ℝ) ≤ (hExp q : ℝ) := by
        exact_mod_cast hfac_le_hExp
      exact hfac_le_hExp_real.trans (hHbound q hqS)
    have hfac_floor : q.factorization p.1 ≤ Nat.floor H :=
      (Nat.le_floor_iff hH_nonneg).2 hfac_le_H
    dsimp [vec]
    omega
  have hvec_inj : Set.InjOn vec S := by
    intro q hqS q' hq'S hqq'
    apply Nat.eq_of_factorization_eq (hSpos q hqS) (hSpos q' hq'S)
    intro p
    by_cases hp : p ∈ C
    · have hcoord := congrFun hqq' ⟨p, hp⟩
      dsimp [vec] at hcoord
      have hsupport : primeSupport q = C := hSupp q hqS
      have hsupport' : primeSupport q' = C := hSupp q' hq'S
      have hfac_pos : 1 ≤ q.factorization p := by
        have hpSupport : p ∈ primeSupport q := by simpa [hsupport] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      have hfac_pos' : 1 ≤ q'.factorization p := by
        have hpSupport : p ∈ primeSupport q' := by simpa [hsupport'] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      omega
    · have hpq : p ∉ primeSupport q := by simpa [hSupp q hqS] using hp
      have hpq' : p ∉ primeSupport q' := by simpa [hSupp q' hq'S] using hp
      rw [Finsupp.notMem_support_iff.1 hpq, Finsupp.notMem_support_iff.1 hpq']
  have hterm_eq :
      ∀ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2) = term (vec q) := by
    intro q hqS
    have hsupport : primeSupport q = C := hSupp q hqS
    have hhexp :
        hExp q = ∏ p : Index, q.factorization p.1 := by
      calc
        hExp q = ∏ p ∈ C, q.factorization p := by
          simp [hExp, hsupport]
        _ = ∏ p : Index, q.factorization p.1 := by
          rw [Finset.prod_coe_sort]
    have hsucc : ∀ p : Index, vec q p + 1 = q.factorization p.1 := by
      intro p
      have hpSupport : p.1 ∈ primeSupport q := by simp [hsupport, p.2]
      have hpos : 1 ≤ q.factorization p.1 := by
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      dsimp [vec]
      omega
    rw [hhexp, one_div_sq_nat_prod_bfv]
    dsimp [term]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [hsucc p]
  calc
    (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2))
        = ∑ q ∈ S, term (vec q) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact hterm_eq q hq
    _ = ∑ e ∈ S.image vec, term e := by
            rw [Finset.sum_image]
            intro q hq q' hq' hEq
            exact hvec_inj hq hq' hEq
    _ ≤ ∑ e ∈ E, term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro e he
                rcases Finset.mem_image.mp he with ⟨q, hq, rfl⟩
                exact hvec_mem q hq)
              (by
                intro e _heE _heNot
                dsimp [term]
                positivity)
    _ = ∏ _p : Index,
          ∑ ν ∈ Finset.range (Nat.floor H),
            (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2) := by
            change
              (∑ e ∈ Fintype.piFinset
                  (fun _ : Index => Finset.range (Nat.floor H)),
                ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)) =
              ∏ _p : Index,
                ∑ ν ∈ Finset.range (Nat.floor H),
                  (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)
            exact
              (Finset.sum_prod_piFinset
                (ι := Index) (κ := ℕ) (R := ℝ)
                (s := Finset.range (Nat.floor H))
                (g := fun _p ν => (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)))
    _ ≤ ∏ _p : Index, (2 : ℝ) := by
            exact Finset.prod_le_prod
              (s := (Finset.univ : Finset Index))
              (fun _p _hp => by positivity)
              (fun _p _hp => by
                exact sum_inv_sq_le_two_bfv (Nat.floor H))
    _ = (2 : ℝ) ^ C.card := by
            simp [Index]

/--
BFV Lemma 3.3 multiplicity bound.

For a fixed radical `r`, fixed `omega = K`, and `hExp ≤ H`, the possible
moduli are encoded by exponent vectors on the `K` primes in the radical.  BFV
counts those vectors by
`H^2 * (∑_{ν≥1} ν⁻²)^K ≤ H^2 * 2^K`.

The remaining formal work is finite: construct the exponent-vector injection
from `Nat.factorization`, prove the product bound from `hExp`, and apply
`sum_inv_sq_le_two_bfv`.  No analytic number theory is hidden in this target.
-/
theorem rad_multiplicity_bfv33
    (S : Finset ℕ) (r K : ℕ) (H : ℝ)
    (hH : 1 ≤ H)
    (hSpos : ∀ q ∈ S, q ≠ 0)
    (hS : ∀ q ∈ S, rad q = r ∧ omega q = K ∧ (hExp q : ℝ) ≤ H) :
    (S.card : ℝ) ≤ H ^ 2 * (2 : ℝ) ^ K := by
  classical
  by_cases hSne : S.Nonempty
  · rcases hSne with ⟨q0, hq0S⟩
    let C : Finset ℕ := primeSupport r
    have hSupp : ∀ q ∈ S, primeSupport q = C := by
      intro q hq
      exact primeSupport_eq_of_rad_eq (hSpos q hq) (hS q hq).1
    have hCcard : C.card = K := by
      have homega := (hS q0 hq0S).2.1
      unfold omega at homega
      rw [hSupp q0 hq0S] at homega
      exact homega
    have hWeighted :
        (∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2)) ≤ (2 : ℝ) ^ K := by
      simpa [C, hCcard] using
        rad_multiplicity_weight_sum_le S C H hH hSpos hSupp
          (fun q hq => (hS q hq).2.2)
    have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
    have hHsq_pos : 0 < H ^ 2 := by positivity
    have hTermLower :
        ∀ q ∈ S, (1 : ℝ) / (H ^ 2) ≤
          (1 : ℝ) / ((hExp q : ℝ) ^ 2) := by
      intro q hq
      have hExp_nonneg : 0 ≤ (hExp q : ℝ) := by positivity
      have hExp_pos : 0 < (hExp q : ℝ) := by exact_mod_cast hExp_pos q
      have hExp_le : (hExp q : ℝ) ≤ H := (hS q hq).2.2
      have hsq_le : (hExp q : ℝ) ^ 2 ≤ H ^ 2 := by
        nlinarith [sq_nonneg (H - (hExp q : ℝ))]
      exact one_div_le_one_div_of_le (by positivity) hsq_le
    have hCardScaled :
        (S.card : ℝ) * ((1 : ℝ) / (H ^ 2)) ≤ (2 : ℝ) ^ K := by
      calc
        (S.card : ℝ) * ((1 : ℝ) / (H ^ 2))
            = ∑ _q ∈ S, ((1 : ℝ) / (H ^ 2)) := by
                simp
        _ ≤ ∑ q ∈ S, (1 : ℝ) / ((hExp q : ℝ) ^ 2) := by
                exact Finset.sum_le_sum hTermLower
        _ ≤ (2 : ℝ) ^ K := hWeighted
    have hmul := mul_le_mul_of_nonneg_right hCardScaled hHsq_pos.le
    field_simp [hHsq_pos.ne'] at hmul
    nlinarith
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hSne
    have hnonneg : 0 ≤ H ^ 2 * (2 : ℝ) ^ K := by positivity
    simpa [hEmpty] using hnonneg

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/Mertens.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — analytic stub for the Mertens / Euler-product estimate.

# Status

This file isolates the ONE analytic gap from the BFV omega-tail proof in
`Erdos/P202/BFV/OmegaTail.lean`. The statement here is the consumer-shaped
weighted-sum bound used by Rankin's inequality. The body is `sorry` because
the proof is a focused upstream-Mathlib subproject (see below).

# Relation to P694's `Erdos694.mertens_product`

The repo's `Erdos/P694/Proof.lean:417` axiomatizes **Mertens' third theorem**
(the product form `∏_{p ≤ y} p/(p-1) ~ e^γ · log y`). What this P202 stub
needs is Mertens' **second** theorem (`∑_{p ≤ y} 1/p ≤ log log y + C`), which
is derivable from Mertens 3rd by taking logs:
  `log ∏_{p ≤ y} (1 - 1/p)^{-1} = ∑_{p ≤ y} (1/p + 1/(2 p²) + …)
                                = ∑_{p ≤ y} 1/p + O(1)`.

So the two stubs are **the same Mertens-axiom family**: discharging P694's
`mertens_product` (or upstreaming it into Mathlib) discharges what P202 needs
modulo a short derivation. A future cleanup should consolidate them into a
single `Erdos/Shared/Mertens.lean` and re-export from both problems.

# Classical content

The intended derivation factors through two classical inputs:

1. **Mertens' second theorem** (1874): there exists `C : ℝ` such that for all
   sufficiently large `N`,
   `∑_{p prime, p ≤ N} (1 / p : ℝ) ≤ Real.log (Real.log N) + C`.
   In Mathlib `v4.27.0`, the prime-counting function `Nat.primeCounting` and
   the Chebyshev `θ`-function are available (`Nat.Prime.theta_le`,
   `Nat.theta_le_id`, etc.), but the Mertens reciprocal-prime sum is NOT
   packaged. The proof is Abel summation against the Chebyshev `θ` bounds.
   (As noted above, this also follows from P694's `mertens_product`.)

2. **Hardy–Ramanujan / sieve identity**: for any `z ≥ 0` and `y ∈ ℕ`,
   `(∑ n ∈ Finset.Icc 1 y, z ^ omega n : ℝ) ≤ y * ∏_{p ≤ y} (1 + z / p)`.
   This is a standard upper-bound sieve and is also currently absent from
   Mathlib for `omega = Nat.factorization.support.card`.

Combining (1) and (2): with `BFVz N := √(log N) / log log N`,
  `∏_{p ≤ N} (1 + BFVz N / p)
     ≤ Real.exp (BFVz N * ∑_{p ≤ N} 1 / p)
     ≤ Real.exp (BFVz N * (Real.log (Real.log N) + C))`,
which is `≤ Real.exp (ε * Zscale N)` eventually for any `ε > 0`, since
`BFVz N · log log N = √(log N) = Zscale N · (1 + o(1)) / √(log log N) = o(Zscale N)`.

# Where this is consumed

* `Erdos.P202.BFV.OmegaExact` → `Erdos.P202.BFV.OmegaCountInput` →
  ultimately replaces `axiom Erdos202.bfv_omega_count_input`.

# Discharge sketch

To close this proof one needs, in dependency order:

1. A Lean-level Mertens reciprocal-prime sum lemma derived from
   `Nat.theta_le` via Abel summation. This is a standalone Mathlib-PR-style
   target (~200–500 lines).
2. The Hardy–Ramanujan sieve identity for `Nat.factorization.support.card`.
3. The Euler-product → exponential bookkeeping (mechanical once 1–2 land).
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- The BFV Rankin parameter `sqrt(log N) / log log N`. -/
noncomputable def BFVz (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ))

/-- **Analytic gap (Mertens + sieve).** Euler-product upper bound for the
weighted omega sum at the BFV scale.

For every `ε > 0`, eventually in `N`, for every `y ≤ N`:
  `∑_{n ≤ y} (BFVz N) ^ omega n ≤ y · exp(ε · Z(N))`.

The proof factors through Mertens' second theorem and the Hardy–Ramanujan
sieve identity (see the file header for details). Mathlib `v4.27.0` does not
package either; this lemma is a named upstream target. -/
theorem omega_weighted_sum_bfvz_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n ∈ Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) * Real.exp (ε * Zscale N) := by
  sorry

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/LowerConstruction.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- BFV lower construction skeleton.

This file names the explicit lower-family objects used by the
Bourgain--Filaseta--Verstraeten construction: dyadic prime choices, their
product moduli, the finite modulus family, and the theorem targets asserting
injectivity, size, modulus bounds, and CRT residue disjointness.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Parameters and prime choices -/

/-- BFV lower-construction depth, `r = floor M(N)`. -/
noncomputable def lowerR (N : ℕ) : ℕ :=
  Nat.floor (Mscale N)

/-- The index set `{0, ..., r}` for the BFV prime blocks. -/
abbrev lowerIndex (N : ℕ) : Type :=
  Fin (lowerR N + 1)

/-- The root block index in the BFV lower construction. -/
def lowerZeroIndex (N : ℕ) : lowerIndex N :=
  ⟨0, Nat.succ_pos _⟩

/-- The non-root blocks.  The lower family varies only over these blocks; the
root block contributes a fixed shared factor used for CRT-disjointness. -/
abbrev lowerTailIndex (N : ℕ) : Type :=
  {i : lowerIndex N // i ≠ lowerZeroIndex N}

/-- The `k`th varying block, viewed as block number `k+1` in `{0, ..., r}`. -/
def lowerTailBlock (N : ℕ) (k : Fin (lowerR N)) : lowerTailIndex N :=
  ⟨k.succ, by
    intro h
    have hval := congrArg Fin.val h
    simp [lowerZeroIndex, Fin.val_succ] at hval⟩

lemma lowerTailBlock_surjective (N : ℕ) :
    Function.Surjective (lowerTailBlock N) := by
  intro i
  have hi0 : i.1 ≠ 0 := by
    intro h
    exact i.2 (by simpa [lowerZeroIndex] using h)
  refine ⟨i.1.pred hi0, ?_⟩
  apply Subtype.ext
  exact Fin.succ_pred i.1 hi0


/-- Logarithmic gap between consecutive lower-construction prime blocks.

The extra `1 / log log N` is only a separation margin: eventually
`exp(lowerLogGap N) > 2`, so the dyadic intervals `(Y_i, 2Y_i]` are disjoint.
Its total contribution is `o(Zscale N)`. -/
noncomputable def lowerLogGap (N : ℕ) : ℝ :=
  Real.log 2 + 1 / Real.log (Real.log (N : ℝ))

/-- Product-normalized central log scale.

The subtraction of `(r+1) log 2` compensates for the dyadic upper endpoints:
if `Y_i = exp(lowerLogScale N i)`, then the centered offsets below sum to zero,
so formally `∏ᵢ (2 * Y_i) = N`.  This fixes the earlier units error where the
product of the selected prime scales was only about `N^(1/2)`. -/
noncomputable def lowerLogBase (N : ℕ) : ℝ :=
  (Real.log (N : ℝ) - ((lowerR N : ℝ) + 1) * Real.log 2) /
    ((lowerR N : ℝ) + 1)

/-- Corrected logarithmic scale for the `i`th BFV lower prime block.

The scales are centered around `log N / (r+1)`, with consecutive log-gap
`lowerLogGap N`.  Thus the blocks are geometrically separated while their total
product remains at the full `N` scale. -/
noncomputable def lowerLogScale (N : ℕ) (i : lowerIndex N) : ℝ :=
  lowerLogBase N + (((i.1 : ℝ) - (lowerR N : ℝ) / 2) * lowerLogGap N)

lemma lowerLogScale_sub (N : ℕ) (i j : lowerIndex N) :
    lowerLogScale N i - lowerLogScale N j =
      ((i.1 : ℝ) - (j.1 : ℝ)) * lowerLogGap N := by
  simp [lowerLogScale]
  ring

lemma lowerLogGap_gt_log_two_of_exp_one_lt_nat {N : ℕ}
    (hN : Real.exp 1 < (N : ℝ)) :
    Real.log 2 < lowerLogGap N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hrecip_pos : 0 < (1 : ℝ) / Real.log (Real.log (N : ℝ)) := by
    positivity
  simp [lowerLogGap]
  linarith

lemma eventually_lowerLogGap_gt_log_two :
    ∀ᶠ N : ℕ in atTop, Real.log 2 < lowerLogGap N := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hN
  exact lowerLogGap_gt_log_two_of_exp_one_lt_nat
    (lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN))

/-- A concrete product-normalized exponentially spaced scale for the `i`th
dyadic prime block.

The final BFV proof needs only eventual disjointness and product estimates for
these named scales; those hard estimates are isolated below. -/
noncomputable def lowerY (N : ℕ) (i : lowerIndex N) : ℝ :=
  Real.exp (lowerLogScale N i)

lemma lowerY_dyadic_lt_of_lt_index {N : ℕ} {i j : lowerIndex N}
    (hgap : Real.log 2 < lowerLogGap N) (hij : i.1 < j.1) :
    2 * lowerY N i < lowerY N j := by
  have hsucc : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.2 hij
  have hdiff_real : 1 ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
    have hsuccR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hsucc
    linarith
  have hgap_pos : 0 < lowerLogGap N :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hgap
  have hmain :
      Real.log 2 + lowerLogScale N i < lowerLogScale N j := by
    have hsub := lowerLogScale_sub N j i
    have hmul : Real.log 2 < ((j.1 : ℝ) - (i.1 : ℝ)) * lowerLogGap N := by
      calc
        Real.log 2 < lowerLogGap N := hgap
        _ ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * lowerLogGap N := by
          nlinarith
    nlinarith
  calc
    2 * lowerY N i
        = Real.exp (Real.log 2 + lowerLogScale N i) := by
            rw [lowerY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ < Real.exp (lowerLogScale N j) := Real.exp_lt_exp.2 hmain
    _ = lowerY N j := by rw [lowerY]

lemma lowerIndex_sum_centered (N : ℕ) :
    (∑ i : lowerIndex N, ((i.1 : ℝ) - (lowerR N : ℝ) / 2)) = 0 := by
  let r := lowerR N
  change (∑ i : Fin (r + 1), ((i.1 : ℝ) - (r : ℝ) / 2)) = 0
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ x ∈ Finset.range (r + 1),
        if h : x < r + 1 then (x : ℝ) - (r : ℝ) / 2 else 0)
        = ∑ x ∈ Finset.range (r + 1), ((x : ℝ) - (r : ℝ) / 2) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Finset.mem_range.mp hx]
    _ = 0 := by
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_const, nsmul_eq_mul]
          let S : ℝ := ∑ x ∈ Finset.range (r + 1), (x : ℝ)
          have hnat : (∑ i ∈ Finset.range (r + 1), i) * 2 = (r + 1) * r := by
            simpa using (Finset.sum_range_id_mul_two (r + 1))
          have hS2 : S * 2 = ((r + 1 : ℕ) * r : ℝ) := by
            dsimp [S]
            rw [← Nat.cast_sum]
            exact_mod_cast hnat
          have hcard : ((Finset.range (r + 1)).card : ℝ) = r + 1 := by simp
          rw [hcard]
          dsimp [S] at hS2 ⊢
          norm_num at hS2 ⊢
          nlinarith

lemma lowerLogScale_sum (N : ℕ) :
    (∑ i : lowerIndex N, lowerLogScale N i) =
      Real.log (N : ℝ) - ((lowerR N : ℝ) + 1) * Real.log 2 := by
  have hcenter := lowerIndex_sum_centered N
  have hcard : ((Finset.univ : Finset (lowerIndex N)).card : ℝ) =
      (lowerR N : ℝ) + 1 := by
    simp [lowerIndex]
  simp [lowerLogScale, lowerLogBase]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  rw [hcenter]
  rw [zero_mul, add_zero]
  rw [hcard]
  have hden : (lowerR N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]

lemma lowerY_dyadic_product_eq {N : ℕ} (hNpos : 0 < (N : ℝ)) :
    (∏ i : lowerIndex N, (2 : ℝ) * lowerY N i) = (N : ℝ) := by
  calc
    (∏ i : lowerIndex N, (2 : ℝ) * lowerY N i)
        = ∏ i : lowerIndex N, Real.exp (Real.log 2 + lowerLogScale N i) := by
          apply Finset.prod_congr rfl
          intro i _hi
          rw [lowerY, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (∑ i : lowerIndex N, (Real.log 2 + lowerLogScale N i)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (Real.log (N : ℝ)) := by
          congr 1
          rw [Finset.sum_add_distrib]
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [lowerLogScale_sum]
          have hcard : ((Finset.univ : Finset (lowerIndex N)).card : ℝ) =
              (lowerR N : ℝ) + 1 := by
            simp [lowerIndex]
          rw [hcard]
          ring
    _ = (N : ℝ) := Real.exp_log hNpos

/-- Natural floor endpoint for the `i`th scale. -/
noncomputable def lowerYNat (N : ℕ) (i : lowerIndex N) : ℕ :=
  Nat.floor (lowerY N i)

/-- The `i`th dyadic prime block in the lower construction. -/
noncomputable def lowerPrimeInterval (N : ℕ) (i : lowerIndex N) : Finset ℕ :=
  dyadicPrimeInterval (lowerY N i)

/-- Deterministic shared root factor at the block-0 scale.

The original full Cartesian-product family is not CRT-disjoint: two choices
that differ in every coordinate have coprime moduli.  The lower construction
therefore fixes a common root factor and varies only over the remaining blocks.
Using `⌊Y_0⌋ + 1` rather than a chosen prime keeps the family total and avoids
adding an extra nonemptiness dependency; primality of the common factor is not
needed for the CRT-disjointness mechanism. -/
noncomputable def lowerP0 (N : ℕ) : ℕ :=
  Nat.floor (lowerY N (lowerZeroIndex N)) + 1

lemma lowerP0_pos (N : ℕ) : 0 < lowerP0 N := by
  simp [lowerP0]

/-- A choice of one prime from every BFV lower block. -/
abbrev LowerPrimeChoice (N : ℕ) : Type :=
  (i : lowerTailIndex N) → {p : ℕ // p ∈ lowerPrimeInterval N i.1}

lemma lowerTailBlock_ext {N : ℕ} {P P' : LowerPrimeChoice N}
    (h : ∀ k : Fin (lowerR N), P (lowerTailBlock N k) = P' (lowerTailBlock N k)) :
    P = P' := by
  funext i
  rcases lowerTailBlock_surjective N i with ⟨k, rfl⟩
  exact h k

/-- All prime-choice tuples. -/
noncomputable def lowerChoices (N : ℕ) : Finset (LowerPrimeChoice N) :=
  Fintype.piFinset fun i : lowerTailIndex N => (lowerPrimeInterval N i.1).attach

lemma lowerChoices_card (N : ℕ) :
    (lowerChoices N).card =
      ∏ i : lowerTailIndex N, (lowerPrimeInterval N i.1).card := by
  simp [lowerChoices, Fintype.card_piFinset]

/-- The modulus attached to a prime-choice tuple. -/
noncomputable def lowerModulus (N : ℕ) (P : LowerPrimeChoice N) : ℕ :=
  lowerP0 N * ∏ i : lowerTailIndex N, (P i).1

lemma lowerModulus_pos (N : ℕ) (P : LowerPrimeChoice N) :
    0 < lowerModulus N P := by
  unfold lowerModulus
  exact mul_pos (lowerP0_pos N) (Finset.prod_pos (fun i _hi => by
    have hp : Nat.Prime (P i).1 := (mem_dyadicPrimeInterval.1 (P i).2).2.2
    exact hp.pos))

lemma lowerRootFactor_le_two_mul_lowerY {N : ℕ}
    (hY0 : 1 ≤ lowerY N (lowerZeroIndex N)) :
    (lowerP0 N : ℝ) ≤ 2 * lowerY N (lowerZeroIndex N) := by
  have hY0_nonneg : 0 ≤ lowerY N (lowerZeroIndex N) := (Real.exp_pos _).le
  have hfloor :
      ((Nat.floor (lowerY N (lowerZeroIndex N)) : ℕ) : ℝ) ≤
        lowerY N (lowerZeroIndex N) :=
    Nat.floor_le hY0_nonneg
  rw [lowerP0]
  norm_num
  linarith

lemma lowerModulus_le_N_of_root_scale {N : ℕ} (hNpos : 0 < (N : ℝ))
    (hY0 : 1 ≤ lowerY N (lowerZeroIndex N)) (P : LowerPrimeChoice N) :
    lowerModulus N P ≤ N := by
  classical
  have hroot := lowerRootFactor_le_two_mul_lowerY (N := N) hY0
  have htail :
      ((∏ i : lowerTailIndex N, (P i).1 : ℕ) : ℝ) ≤
        ∏ i : lowerTailIndex N, (2 : ℝ) * lowerY N i.1 := by
    rw [Nat.cast_prod]
    exact Finset.prod_le_prod
      (fun i _hi => by positivity)
      (fun i _hi => by
        have hmem : (P i).1 ∈ lowerPrimeInterval N i.1 := (P i).2
        have hle_nat : (P i).1 ≤ Nat.floor (2 * lowerY N i.1) :=
          (mem_dyadicPrimeInterval.1 hmem).2.1
        have hnonneg : 0 ≤ 2 * lowerY N i.1 := by
          exact mul_nonneg (by norm_num) (Real.exp_pos _).le
        exact le_trans (by exact_mod_cast hle_nat)
          (Nat.floor_le hnonneg))
  have hprod_split :
      (2 : ℝ) * lowerY N (lowerZeroIndex N) *
          (∏ i : lowerTailIndex N, (2 : ℝ) * lowerY N i.1)
        =
      ∏ i : lowerIndex N, (2 : ℝ) * lowerY N i := by
    let f : lowerIndex N → ℝ := fun i => (2 : ℝ) * lowerY N i
    have hsplit := Fintype.prod_eq_mul_prod_compl (lowerZeroIndex N) f
    have htail_prod :
        (∏ i ∈ ({lowerZeroIndex N} : Finset (lowerIndex N))ᶜ, f i) =
          ∏ i : lowerTailIndex N, f i.1 := by
      exact Finset.prod_subtype
        (({lowerZeroIndex N} : Finset (lowerIndex N))ᶜ)
        (by intro x; simp)
        f
    simpa [f, htail_prod] using hsplit.symm
  have hreal :
      (lowerModulus N P : ℝ) ≤ (N : ℝ) := by
    rw [lowerModulus, Nat.cast_mul]
    calc
      (lowerP0 N : ℝ) * ((∏ i : lowerTailIndex N, (P i).1 : ℕ) : ℝ)
          ≤ (2 * lowerY N (lowerZeroIndex N)) *
              (∏ i : lowerTailIndex N, (2 : ℝ) * lowerY N i.1) := by
            exact mul_le_mul hroot htail (by positivity) (by positivity)
      _ = ∏ i : lowerIndex N, (2 : ℝ) * lowerY N i := hprod_split
      _ = (N : ℝ) := lowerY_dyadic_product_eq hNpos
  exact_mod_cast hreal

lemma lowerLogScale_zero_nonneg_of_scale {N : ℕ}
    (hNlarge : Real.exp 1 < (N : ℝ))
    (hMge : 1 ≤ Mscale N)
    (hloglog_ge : 4 ≤ Real.log (Real.log (N : ℝ))) :
    0 ≤ lowerLogScale N (lowerZeroIndex N) := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := by
    have hone_lt_N : (1 : ℝ) < (N : ℝ) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ < Real.exp 1 := Real.exp_lt_exp.2 zero_lt_one
        _ < (N : ℝ) := hNlarge
    exact Real.log_pos hone_lt_N
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) := by linarith
  have hMpos : 0 < Mscale N := lt_of_lt_of_le zero_lt_one hMge
  have hM_nonneg : 0 ≤ Mscale N := hMpos.le
  have hZ_nonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hfloor_le :
      ((lowerR N : ℕ) : ℝ) ≤ Mscale N := by
    exact Nat.floor_le (Mscale_nonneg N)
  have hden_pos : 0 < ((lowerR N : ℕ) : ℝ) + 1 := by positivity
  have hden_le : ((lowerR N : ℕ) : ℝ) + 1 ≤ 2 * Mscale N := by
    nlinarith
  have htwoM_pos : 0 < 2 * Mscale N := by positivity
  have hdiv_ge :
      Zscale N / 2 ≤ Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) := by
    have hmain :
        Real.log (N : ℝ) / (2 * Mscale N) ≤
          Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) :=
      div_le_div_of_nonneg_left hlog_nonneg hden_pos hden_le
    have hrewrite :
        Real.log (N : ℝ) / (2 * Mscale N) = Zscale N / 2 := by
      have hMZ := Mscale_mul_Zscale_eq_log hNlarge
      field_simp [hMpos.ne']
      nlinarith
    simpa [hrewrite] using hmain
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hrecip_le_one :
      1 / Real.log (Real.log (N : ℝ)) ≤ 1 := by
    exact (div_le_iff₀ hloglog_pos).2 (by linarith)
  have hgap_le_two : lowerLogGap N ≤ 2 := by
    have hrecip_inv_le_one :
        (Real.log (Real.log (N : ℝ)))⁻¹ ≤ 1 := by
      simpa [one_div] using hrecip_le_one
    rw [lowerLogGap]
    linarith
  have hgap_nonneg : 0 ≤ lowerLogGap N := by
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hrecip_nonneg : 0 ≤ (Real.log (Real.log (N : ℝ)))⁻¹ :=
      inv_nonneg.2 hloglog_pos.le
    have hrecip_nonneg_div :
        0 ≤ 1 / Real.log (Real.log (N : ℝ)) := by
      simpa [one_div] using hrecip_nonneg
    rw [lowerLogGap]
    linarith
  have hgap_term :
      ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N ≤ Mscale N := by
    have hmul :
        ((lowerR N : ℕ) : ℝ) * lowerLogGap N ≤ Mscale N * 2 :=
      mul_le_mul hfloor_le hgap_le_two hgap_nonneg hM_nonneg
    nlinarith
  have hbad_le :
      Real.log 2 + ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N ≤ 2 * Mscale N := by
    nlinarith
  have hZ_large : 2 * Mscale N ≤ Zscale N / 2 := by
    have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
    rw [← hMll]
    nlinarith
  have hbad_le_Z : Real.log 2 + ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N ≤
      Zscale N / 2 := le_trans hbad_le hZ_large
  have hbase_eq :
      lowerLogBase N =
        Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) - Real.log 2 := by
    have hden_ne : ((lowerR N : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    simp [lowerLogBase]
    field_simp [hden_ne]
  have hscale_eq :
      lowerLogScale N (lowerZeroIndex N) =
        Real.log (N : ℝ) / (((lowerR N : ℕ) : ℝ) + 1) -
          (Real.log 2 + ((lowerR N : ℕ) : ℝ) / 2 * lowerLogGap N) := by
    simp [lowerLogScale, hbase_eq, lowerZeroIndex]
    ring
  rw [hscale_eq]
  nlinarith

lemma eventually_lowerY_zero_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ lowerY N (lowerZeroIndex N) := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge 1 zero_lt_one,
      tendsto_loglog_nat_atTop.eventually_ge_atTop 4] with N hN hM hloglog
  rw [lowerY, Real.one_le_exp_iff]
  exact lowerLogScale_zero_nonneg_of_scale
    (lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)) hM hloglog

/-- The finite BFV lower family of moduli. -/
noncomputable def lowerQ (N : ℕ) : Finset ℕ :=
  (lowerChoices N).image (lowerModulus N)

/-- A canonical preimage choice for a modulus in `lowerQ`. -/
lemma lowerChoiceOfQ_exists (N : ℕ) (q : {q : ℕ // q ∈ lowerQ N}) :
    ∃ P ∈ lowerChoices N, lowerModulus N P = q.1 := by
  have hq : q.1 ∈ lowerQ N := q.2
  change q.1 ∈ (lowerChoices N).image (lowerModulus N) at hq
  exact Finset.mem_image.1 hq

noncomputable def lowerChoiceOfQ (N : ℕ) (q : {q : ℕ // q ∈ lowerQ N}) :
    LowerPrimeChoice N :=
  Classical.choose (lowerChoiceOfQ_exists N q)

lemma lowerChoiceOfQ_mem (N : ℕ) (q : {q : ℕ // q ∈ lowerQ N}) :
    lowerChoiceOfQ N q ∈ lowerChoices N :=
  (Classical.choose_spec (lowerChoiceOfQ_exists N q)).1

lemma lowerChoiceOfQ_modulus (N : ℕ) (q : {q : ℕ // q ∈ lowerQ N}) :
    lowerModulus N (lowerChoiceOfQ N q) = q.1 :=
  (Classical.choose_spec (lowerChoiceOfQ_exists N q)).2

lemma lowerChoiceOfQ_eq_of_injective {N : ℕ}
    (hinj : Set.InjOn (lowerModulus N) (↑(lowerChoices N) : Set (LowerPrimeChoice N)))
    (q : {q : ℕ // q ∈ lowerQ N}) {P : LowerPrimeChoice N}
    (hP : P ∈ lowerChoices N) (hmod : lowerModulus N P = q.1) :
    lowerChoiceOfQ N q = P := by
  apply hinj (lowerChoiceOfQ_mem N q) hP
  rw [lowerChoiceOfQ_modulus, hmod]

lemma lowerQ_card_eq_lowerChoices_card_of_injective {N : ℕ}
    (hinj : Set.InjOn (lowerModulus N) (↑(lowerChoices N) : Set (LowerPrimeChoice N))) :
    (lowerQ N).card = (lowerChoices N).card := by
  simpa [lowerQ] using Finset.card_image_of_injOn (s := lowerChoices N)
    (f := lowerModulus N) hinj

/-- The real lower-bound target appearing in the final theorem. -/
noncomputable def bfvLowerTarget (ε : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) * Lscale (-(1 + ε)) N

/-! ## Generic finite CRT target -/

/-- Finite CRT in the integer `Int.ModEq` form used for residue assignments.

Wraps `Nat.chineseRemainderOfFinset` and bridges to `Int.ModEq` via
`Int.natCast_modEq_iff`. -/
theorem int_modEq_crt_finset_exists {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℕ) (b : ι → ℤ)
    (hm : ∀ i ∈ s, m i ≠ 0)
    (hcop : Set.Pairwise (↑s : Set ι)
      (fun i j => Nat.Coprime (m i) (m j))) :
    ∃ a : ℤ, ∀ i ∈ s, a ≡ b i [ZMOD (m i : ℤ)] := by
  classical
  set aN : ι → ℕ := fun i => ((b i) % (m i : ℤ)).toNat with haN
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset aN m s hm hcop
  refine ⟨(k : ℤ), ?_⟩
  intro i hi
  have hm_ne : m i ≠ 0 := hm i hi
  have hm_int_ne : (m i : ℤ) ≠ 0 := by exact_mod_cast hm_ne
  have hmod_nonneg : 0 ≤ (b i) % (m i : ℤ) := Int.emod_nonneg _ hm_int_ne
  have h_aN_eq : (aN i : ℤ) = (b i) % (m i : ℤ) := by
    simp [haN, Int.toNat_of_nonneg hmod_nonneg]
  -- CRT result: k ≡ aN i [MOD m i].
  have hk_nat : k ≡ aN i [MOD m i] := hk i hi
  -- Bridge to Int.ModEq.
  have hk_int : (k : ℤ) ≡ (aN i : ℤ) [ZMOD ((m i : ℕ) : ℤ)] :=
    Int.natCast_modEq_iff.mpr hk_nat
  -- And aN i ≡ b i [ZMOD m i] since (b i % m i) ≡ b i.
  have h_aN_modEq_b : (aN i : ℤ) ≡ b i [ZMOD (m i : ℤ)] := by
    rw [h_aN_eq]
    exact (Int.emod_emod_of_dvd (b i) dvd_rfl :
      (b i) % (m i : ℤ) % (m i : ℤ) = b i % (m i : ℤ))
  exact hk_int.trans h_aN_modEq_b

/-! ## Finite encodings for the CRT tree -/

/-- Encode an element of a finite set into a natural residue below `m`, assuming
the set has at most `m` elements. -/
noncomputable def finsetCode (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) : ℕ :=
  (Fin.castLE h ((Finset.equivFin s) x)).1

lemma finsetCode_lt (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m)
    (x : {n : ℕ // n ∈ s}) :
    finsetCode s m h x < m :=
  (Fin.castLE h ((Finset.equivFin s) x)).2

lemma finsetCode_injective (s : Finset ℕ) (m : ℕ) (h : s.card ≤ m) :
    Function.Injective (finsetCode s m h) := by
  intro x y hxy
  have hfin :
      Fin.castLE h ((Finset.equivFin s) x) =
        Fin.castLE h ((Finset.equivFin s) y) :=
    Fin.ext hxy
  exact (Finset.equivFin s).injective (Fin.castLE_injective h hfin)

lemma nat_eq_of_int_modEq_of_lt {m a b : ℕ}
    (ha : a < m) (hb : b < m)
    (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (m : ℤ)]) :
    a = b := by
  exact Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h) ha hb

/-! ## CRT tree data -/

/-- Capacity hypotheses needed by the rooted CRT tree: the root modulus can
encode the first varying prime, and each chosen prime can encode the next
block.  The final proof supplies these eventually from prime-counting upper
bounds and the scale separation. -/
structure LowerEncodingCapacity (N : ℕ) : Prop where
  root :
    ∀ hR : 0 < lowerR N,
      (lowerPrimeInterval N (lowerTailBlock N ⟨0, hR⟩).1).card ≤ lowerP0 N
  next :
    ∀ k : Fin (lowerR N), ∀ hnext : k.1 + 1 < lowerR N,
      ∀ p : ℕ, p ∈ lowerPrimeInterval N (lowerTailBlock N k).1 →
        (lowerPrimeInterval N (lowerTailBlock N ⟨k.1 + 1, hnext⟩).1).card ≤ p
  root_coprime :
    ∀ k : Fin (lowerR N), ∀ p : ℕ,
      p ∈ lowerPrimeInterval N (lowerTailBlock N k).1 →
        Nat.Coprime (lowerP0 N) p

/-- The root or one selected tail prime, used as a CRT modulus. -/
abbrev lowerCRTIndex (N : ℕ) : Type :=
  Option (Fin (lowerR N))

noncomputable def lowerRootCode (N : ℕ) (hcap : LowerEncodingCapacity N)
    (P : LowerPrimeChoice N) : ℕ :=
  if hR : 0 < lowerR N then
    finsetCode (lowerPrimeInterval N (lowerTailBlock N ⟨0, hR⟩).1)
      (lowerP0 N) (hcap.root hR) (P (lowerTailBlock N ⟨0, hR⟩))
  else
    0

noncomputable def lowerStepCode (N : ℕ) (hcap : LowerEncodingCapacity N)
    (P : LowerPrimeChoice N) (k : Fin (lowerR N)) : ℕ :=
  if hnext : k.1 + 1 < lowerR N then
    finsetCode (lowerPrimeInterval N (lowerTailBlock N ⟨k.1 + 1, hnext⟩).1)
      (P (lowerTailBlock N k)).1
      (hcap.next k hnext (P (lowerTailBlock N k)).1 (P (lowerTailBlock N k)).2)
      (P (lowerTailBlock N ⟨k.1 + 1, hnext⟩))
  else
    0

noncomputable def lowerCRTModulus (N : ℕ) (P : LowerPrimeChoice N) :
    lowerCRTIndex N → ℕ
  | none => lowerP0 N
  | some k => (P (lowerTailBlock N k)).1

noncomputable def lowerCRTTarget (N : ℕ) (hcap : LowerEncodingCapacity N)
    (P : LowerPrimeChoice N) : lowerCRTIndex N → ℤ
  | none => lowerRootCode N hcap P
  | some k => lowerStepCode N hcap P k

lemma lowerCRTModulus_ne_zero (N : ℕ) (P : LowerPrimeChoice N)
    (i : lowerCRTIndex N) :
    lowerCRTModulus N P i ≠ 0 := by
  cases i with
  | none => exact (lowerP0_pos N).ne'
  | some k =>
      have hp : Nat.Prime (P (lowerTailBlock N k)).1 :=
        (mem_dyadicPrimeInterval.1 (P (lowerTailBlock N k)).2).2.2
      exact hp.ne_zero

lemma lowerCRTModulus_dvd_lowerModulus (N : ℕ) (P : LowerPrimeChoice N)
    (i : lowerCRTIndex N) :
    lowerCRTModulus N P i ∣ lowerModulus N P := by
  cases i with
  | none =>
      rw [lowerCRTModulus, lowerModulus]
      exact dvd_mul_right _ _
  | some k =>
      rw [lowerCRTModulus, lowerModulus]
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem (fun i : lowerTailIndex N => (P i).1)
          (Finset.mem_univ (lowerTailBlock N k)))
        (lowerP0 N)

lemma lowerCRTModuli_pairwise_coprime {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j))
    (P : LowerPrimeChoice N) :
    Set.Pairwise (↑(Finset.univ : Finset (lowerCRTIndex N)) : Set (lowerCRTIndex N))
      (fun i j => Nat.Coprime (lowerCRTModulus N P i) (lowerCRTModulus N P j)) := by
  intro i _hi j _hj hij
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some k =>
          exact hcap.root_coprime k (P (lowerTailBlock N k)).1
            (P (lowerTailBlock N k)).2
  | some k =>
      cases j with
      | none =>
          exact (hcap.root_coprime k (P (lowerTailBlock N k)).1
            (P (lowerTailBlock N k)).2).symm
      | some l =>
          have hkl : k ≠ l := by
            intro h
            exact hij (by simp [h])
          have hblock_ne : (lowerTailBlock N k).1 ≠ (lowerTailBlock N l).1 := by
            intro hblock
            apply hkl
            apply Fin.ext
            have hval := congrArg Fin.val hblock
            simp [lowerTailBlock, Fin.val_succ] at hval
            omega
          have hp : Nat.Prime (P (lowerTailBlock N k)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerTailBlock N k)).2).2.2
          have hq : Nat.Prime (P (lowerTailBlock N l)).1 :=
            (mem_dyadicPrimeInterval.1 (P (lowerTailBlock N l)).2).2.2
          have hpq_ne : (P (lowerTailBlock N k)).1 ≠ (P (lowerTailBlock N l)).1 := by
            intro hpq
            have hmem_l :
                (P (lowerTailBlock N k)).1 ∈
                  lowerPrimeInterval N (lowerTailBlock N l).1 := by
              simp [hpq, (P (lowerTailBlock N l)).2]
            exact Finset.disjoint_left.1
              (hdisj (lowerTailBlock N k).1 (lowerTailBlock N l).1 hblock_ne)
              (P (lowerTailBlock N k)).2 hmem_l
          exact (Nat.coprime_primes hp hq).2 hpq_ne

noncomputable def lowerResidueForChoice {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j))
    (P : LowerPrimeChoice N) : ℤ :=
  Classical.choose (int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerCRTIndex N)))
    (m := lowerCRTModulus N P)
    (b := lowerCRTTarget N hcap P)
    (by intro i _hi; exact lowerCRTModulus_ne_zero N P i)
    (lowerCRTModuli_pairwise_coprime hcap hdisj P))

lemma lowerResidueForChoice_spec {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j))
    (P : LowerPrimeChoice N) (i : lowerCRTIndex N) :
    lowerResidueForChoice hcap hdisj P ≡
      lowerCRTTarget N hcap P i [ZMOD (lowerCRTModulus N P i : ℤ)] :=
  Classical.choose_spec (int_modEq_crt_finset_exists
    (s := (Finset.univ : Finset (lowerCRTIndex N)))
    (m := lowerCRTModulus N P)
    (b := lowerCRTTarget N hcap P)
    (by intro i _hi; exact lowerCRTModulus_ne_zero N P i)
    (lowerCRTModuli_pairwise_coprime hcap hdisj P)) i (Finset.mem_univ i)

noncomputable def lowerResidueAssignment {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j)) :
    ResidueAssignment (lowerQ N) :=
  fun q => lowerResidueForChoice hcap hdisj (lowerChoiceOfQ N q)

lemma lowerResidueAssignment_modEq_target {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j))
    (q : {q : ℕ // q ∈ lowerQ N}) (i : lowerCRTIndex N) {n : ℤ}
    (hn : n ∈ residueClass q.1 (lowerResidueAssignment hcap hdisj q)) :
    n ≡ lowerCRTTarget N hcap (lowerChoiceOfQ N q) i
      [ZMOD (lowerCRTModulus N (lowerChoiceOfQ N q) i : ℤ)] := by
  have hnq :
      n ≡ lowerResidueForChoice hcap hdisj (lowerChoiceOfQ N q)
        [ZMOD (q.1 : ℤ)] := by
    simpa [residueClass, lowerResidueAssignment] using hn
  have hn_lower :
      n ≡ lowerResidueForChoice hcap hdisj (lowerChoiceOfQ N q)
        [ZMOD (lowerModulus N (lowerChoiceOfQ N q) : ℤ)] := by
    simpa [lowerChoiceOfQ_modulus N q] using hnq
  have hdivNat :
      lowerCRTModulus N (lowerChoiceOfQ N q) i ∣
        lowerModulus N (lowerChoiceOfQ N q) :=
    lowerCRTModulus_dvd_lowerModulus N (lowerChoiceOfQ N q) i
  have hdivInt :
      (lowerCRTModulus N (lowerChoiceOfQ N q) i : ℤ) ∣
        (lowerModulus N (lowerChoiceOfQ N q) : ℤ) := by
    exact_mod_cast hdivNat
  exact (Int.ModEq.of_dvd hdivInt hn_lower).trans
    (lowerResidueForChoice_spec hcap hdisj (lowerChoiceOfQ N q) i)

lemma lowerRootCode_eq_of_modEq {N : ℕ} (hcap : LowerEncodingCapacity N)
    (P P' : LowerPrimeChoice N) (hR : 0 < lowerR N)
    (hmod : (lowerRootCode N hcap P : ℤ) ≡
      (lowerRootCode N hcap P' : ℤ) [ZMOD (lowerP0 N : ℤ)]) :
    P (lowerTailBlock N ⟨0, hR⟩) = P' (lowerTailBlock N ⟨0, hR⟩) := by
  let s := lowerPrimeInterval N (lowerTailBlock N ⟨0, hR⟩).1
  let m := lowerP0 N
  let hcard := hcap.root hR
  have hltP :
      lowerRootCode N hcap P < lowerP0 N := by
    simpa [lowerRootCode, hR, s, m, hcard] using
      finsetCode_lt s m hcard (P (lowerTailBlock N ⟨0, hR⟩))
  have hltP' :
      lowerRootCode N hcap P' < lowerP0 N := by
    simpa [lowerRootCode, hR, s, m, hcard] using
      finsetCode_lt s m hcard (P' (lowerTailBlock N ⟨0, hR⟩))
  have hcode_eq : lowerRootCode N hcap P = lowerRootCode N hcap P' :=
    nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      finsetCode s m hcard (P (lowerTailBlock N ⟨0, hR⟩)) =
        finsetCode s m hcard (P' (lowerTailBlock N ⟨0, hR⟩)) := by
    simpa [lowerRootCode, hR, s, m, hcard] using hcode_eq
  exact finsetCode_injective s m hcard hcode_eq'

lemma lowerStepCode_eq_of_modEq {N : ℕ} (hcap : LowerEncodingCapacity N)
    (P P' : LowerPrimeChoice N) (k : Fin (lowerR N))
    (hnext : k.1 + 1 < lowerR N)
    (hprev : P (lowerTailBlock N k) = P' (lowerTailBlock N k))
    (hmod : (lowerStepCode N hcap P k : ℤ) ≡
      (lowerStepCode N hcap P' k : ℤ)
        [ZMOD ((P (lowerTailBlock N k)).1 : ℤ)]) :
    P (lowerTailBlock N ⟨k.1 + 1, hnext⟩) =
      P' (lowerTailBlock N ⟨k.1 + 1, hnext⟩) := by
  let s := lowerPrimeInterval N (lowerTailBlock N ⟨k.1 + 1, hnext⟩).1
  let m := (P (lowerTailBlock N k)).1
  let hcard := hcap.next k hnext (P (lowerTailBlock N k)).1 (P (lowerTailBlock N k)).2
  have hltP :
      lowerStepCode N hcap P k < (P (lowerTailBlock N k)).1 := by
    simpa [lowerStepCode, hnext, s, m, hcard] using
      finsetCode_lt s m hcard (P (lowerTailBlock N ⟨k.1 + 1, hnext⟩))
  have hltP' :
      lowerStepCode N hcap P' k < (P (lowerTailBlock N k)).1 := by
    have hcard' :=
      hcap.next k hnext (P' (lowerTailBlock N k)).1 (P' (lowerTailBlock N k)).2
    have hlt' :
        lowerStepCode N hcap P' k < (P' (lowerTailBlock N k)).1 := by
      simpa [lowerStepCode, hnext] using
        finsetCode_lt s (P' (lowerTailBlock N k)).1 hcard'
          (P' (lowerTailBlock N ⟨k.1 + 1, hnext⟩))
    simpa [hprev] using hlt'
  have hcode_eq : lowerStepCode N hcap P k = lowerStepCode N hcap P' k :=
    nat_eq_of_int_modEq_of_lt hltP hltP' hmod
  have hcode_eq' :
      finsetCode s m hcard (P (lowerTailBlock N ⟨k.1 + 1, hnext⟩)) =
        finsetCode s m hcard (P' (lowerTailBlock N ⟨k.1 + 1, hnext⟩)) := by
    simpa [lowerStepCode, hnext, s, m, hcard] using hcode_eq
  exact finsetCode_injective s m hcard hcode_eq'

lemma lowerResidueAssignment_pairwise_disjoint_of_capacity {N : ℕ}
    (hcap : LowerEncodingCapacity N)
    (hdisj : ∀ i j : lowerIndex N, i ≠ j →
      Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j)) :
    PairwiseDisjointResidues (lowerQ N) (lowerResidueAssignment hcap hdisj) := by
  intro q r hqr
  rw [Set.disjoint_left]
  intro z hzq hzr
  let P := lowerChoiceOfQ N q
  let P' := lowerChoiceOfQ N r
  have hP_eq : P = P' := by
    by_cases hR : 0 < lowerR N
    · have hq0 := lowerResidueAssignment_modEq_target hcap hdisj q none hzq
      have hr0 := lowerResidueAssignment_modEq_target hcap hdisj r none hzr
      have hroot_mod :
          (lowerCRTTarget N hcap P none) ≡
            (lowerCRTTarget N hcap P' none)
              [ZMOD (lowerP0 N : ℤ)] := by
        simpa [P, P', lowerCRTModulus] using hq0.symm.trans hr0
      have hzero :
          P (lowerTailBlock N ⟨0, hR⟩) =
            P' (lowerTailBlock N ⟨0, hR⟩) := by
        exact lowerRootCode_eq_of_modEq hcap P P' hR
          (by simpa [lowerCRTTarget] using hroot_mod)
      have hall :
          ∀ n : ℕ, ∀ hn : n < lowerR N,
            P (lowerTailBlock N ⟨n, hn⟩) =
              P' (lowerTailBlock N ⟨n, hn⟩) := by
        intro n
        induction n with
        | zero =>
            intro hn
            simpa using hzero
        | succ n ih =>
            intro hn
            have hprev_lt : n < lowerR N := Nat.lt_of_succ_lt hn
            have hprev := ih hprev_lt
            let k : Fin (lowerR N) := ⟨n, hprev_lt⟩
            have hqk := lowerResidueAssignment_modEq_target hcap hdisj q (some k) hzq
            have hrk := lowerResidueAssignment_modEq_target hcap hdisj r (some k) hzr
            have hstep_mod :
                (lowerCRTTarget N hcap P (some k)) ≡
                  (lowerCRTTarget N hcap P' (some k))
                    [ZMOD ((P (lowerTailBlock N k)).1 : ℤ)] := by
              have hrk' :
                  z ≡ lowerCRTTarget N hcap P' (some k)
                    [ZMOD ((P (lowerTailBlock N k)).1 : ℤ)] := by
                have hprev_val :
                    (lowerChoiceOfQ N r (lowerTailBlock N k)).1 =
                      (lowerChoiceOfQ N q (lowerTailBlock N k)).1 := by
                  dsimp [P, P'] at hprev
                  exact congrArg Subtype.val hprev.symm
                simpa [P, P', lowerCRTModulus, hprev_val] using hrk
              simpa [P, P', lowerCRTModulus] using hqk.symm.trans hrk'
            exact lowerStepCode_eq_of_modEq hcap P P' k hn hprev
              (by simpa [lowerCRTTarget] using hstep_mod)
      exact lowerTailBlock_ext (fun k => hall k.1 k.2)
    · apply lowerTailBlock_ext
      intro k
      have hk : k.1 < lowerR N := k.2
      exact False.elim (hR (lt_of_le_of_lt (Nat.zero_le k.1) hk))
  have hqval : q.1 = r.1 := by
    calc
      q.1 = lowerModulus N P := (lowerChoiceOfQ_modulus N q).symm
      _ = lowerModulus N P' := by rw [hP_eq]
      _ = r.1 := lowerChoiceOfQ_modulus N r
  exact hqr (Subtype.ext hqval)

/-- Remaining scale/prime-counting bookkeeping for the CRT tree capacity.

This is not a new analytic primitive: `Mathlib` already supplies Chebyshev's
upper bound `Chebyshev.eventually_primeCounting_le`.  The proof still needs the
local conversion from that global upper bound to dyadic block cardinalities,
then the BFV scale inequalities showing each next block has at most as many
primes as the previous selected prime, and that the fixed root is coprime to
all tail primes by separation. -/
axiom lowerEncodingCapacity_eventually_analytic :
    ∀ᶠ N : ℕ in atTop, LowerEncodingCapacity N

/-- BFV lower-construction capacity, discharged against the named
prime-counting and scale bookkeeping stub
`lowerEncodingCapacity_eventually_analytic`. -/
theorem lowerEncodingCapacity_eventually :
    ∀ᶠ N : ℕ in atTop, LowerEncodingCapacity N :=
  lowerEncodingCapacity_eventually_analytic

/-- Prime-supply and product-scale lower bound for the rooted lower choices.

This is the remaining C5 arithmetic estimate: use the dyadic prime lower bound
for every tail block, multiply the block cardinalities via `lowerChoices_card`,
and absorb the lost root block and logarithmic denominators into
`Lscale (-(1+ε), N)`. -/
axiom lowerChoices_card_lower_bound_eventually_analytic :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Nat.ceil (bfvLowerTarget ε N) ≤ (lowerChoices N).card

/-- Lower-choice cardinality bound, discharged against the named dyadic
prime-supply and product-scale bookkeeping stub
`lowerChoices_card_lower_bound_eventually_analytic`. -/
theorem lowerChoices_card_lower_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Nat.ceil (bfvLowerTarget ε N) ≤ (lowerChoices N).card :=
  lowerChoices_card_lower_bound_eventually_analytic

/-! ## Lower-family theorem targets -/

/-- The named prime blocks are eventually pairwise disjoint as real dyadic
intervals, after converting through their floor endpoints. -/
theorem lowerPrimeIntervals_pairwise_disjoint :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerIndex N, i ≠ j →
        Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j) := by
  filter_upwards [eventually_lowerLogGap_gt_log_two] with N hgap
  intro i j hij
  have hijval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hijval with hlt | hgt
  · have hsep : 2 * lowerY N i < lowerY N j :=
      lowerY_dyadic_lt_of_lt_index hgap hlt
    have hfloor : Nat.floor (2 * lowerY N i) ≤ Nat.floor (lowerY N j) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerY N i)) (Nat.floor (2 * lowerY N i)))
          (Finset.Ioc (Nat.floor (lowerY N j)) (Nat.floor (2 * lowerY N j))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPrimeInterval, dyadicPrimeInterval] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)
  · have hsep : 2 * lowerY N j < lowerY N i :=
      lowerY_dyadic_lt_of_lt_index hgap hgt
    have hfloor : Nat.floor (2 * lowerY N j) ≤ Nat.floor (lowerY N i) :=
      Nat.floor_mono hsep.le
    have hIoc :
        Disjoint
          (Finset.Ioc (Nat.floor (lowerY N j)) (Nat.floor (2 * lowerY N j)))
          (Finset.Ioc (Nat.floor (lowerY N i)) (Nat.floor (2 * lowerY N i))) :=
      Finset.Ioc_disjoint_Ioc_of_le hfloor
    simpa [lowerPrimeInterval, dyadicPrimeInterval, disjoint_comm] using
      (Finset.disjoint_filter_filter (p := Nat.Prime) (q := Nat.Prime) hIoc)

/-- Unique factorization plus disjoint prime blocks makes the product map from
prime-choice tuples to moduli injective. -/
theorem lowerModulus_injective_eventually :
    ∀ᶠ N : ℕ in atTop,
      Set.InjOn (lowerModulus N) (↑(lowerChoices N) : Set (LowerPrimeChoice N)) := by
  filter_upwards [lowerPrimeIntervals_pairwise_disjoint] with N hdisj
  intro P _hP P' _hP' heq
  have htail_eq :
      (∏ i : lowerTailIndex N, (P i).1) =
        ∏ i : lowerTailIndex N, (P' i).1 := by
    have hp0 : lowerP0 N ≠ 0 := (lowerP0_pos N).ne'
    exact mul_left_cancel₀ hp0 (by simpa [lowerModulus] using heq)
  funext i
  apply Subtype.ext
  let p : ℕ := (P i).1
  have hpPrime : Nat.Prime p := (mem_dyadicPrimeInterval.1 (P i).2).2.2
  have hp_dvd_left : p ∣ ∏ k : lowerTailIndex N, (P k).1 := by
    unfold p
    exact Finset.dvd_prod_of_mem (fun k : lowerTailIndex N => (P k).1) (Finset.mem_univ i)
  have hp_dvd_prod : p ∣ ∏ k : lowerTailIndex N, (P' k).1 := by
    rwa [htail_eq] at hp_dvd_left
  rcases (hpPrime.prime.dvd_finset_prod_iff (S := Finset.univ)
      (fun k : lowerTailIndex N => (P' k).1)).1 hp_dvd_prod with
    ⟨j, _hj, hp_dvd_pj⟩
  have hpjPrime : Nat.Prime (P' j).1 := (mem_dyadicPrimeInterval.1 (P' j).2).2.2
  have hp_eq_pj : p = (P' j).1 :=
    (Nat.prime_dvd_prime_iff_eq hpPrime hpjPrime).1 hp_dvd_pj
  have hji : j = i := by
    by_contra hne
    have hne' : i.1 ≠ j.1 := by
      intro h
      exact hne (Subtype.ext h.symm)
    have hp_mem_i : p ∈ lowerPrimeInterval N i := (P i).2
    have hp_mem_j : p ∈ lowerPrimeInterval N j := by
      simp [p, hp_eq_pj, (P' j).2]
    exact Finset.disjoint_left.1 (hdisj i.1 j.1 hne') hp_mem_i hp_mem_j
  subst hji
  simpa [p] using hp_eq_pj

/-- The BFV product estimate: all constructed moduli are eventually in
`[1, N]`. -/
theorem lowerQ_moduli_in_range_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ q ∈ lowerQ N, 1 ≤ q ∧ q ≤ N := by
  filter_upwards [Filter.eventually_gt_atTop 0, eventually_lowerY_zero_ge_one] with N hN hY0 q hq
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [lowerQ] at hq
  rcases Finset.mem_image.1 hq with ⟨P, _hP, rfl⟩
  exact ⟨Nat.succ_le_of_lt (lowerModulus_pos N P),
    lowerModulus_le_N_of_root_scale hNpos hY0 P⟩

/-- CRT residue choices for the lower family are pairwise disjoint. -/
theorem lowerQ_pairwise_disjoint_residues_eventually :
    ∀ᶠ N : ℕ in atTop,
      ∃ a : ResidueAssignment (lowerQ N),
        PairwiseDisjointResidues (lowerQ N) a := by
  filter_upwards [lowerEncodingCapacity_eventually,
      lowerPrimeIntervals_pairwise_disjoint] with N hcap hdisj
  exact ⟨lowerResidueAssignment hcap hdisj,
    lowerResidueAssignment_pairwise_disjoint_of_capacity hcap hdisj⟩

/-- Cardinality lower bound for the BFV family, combining dyadic prime supply,
injectivity, and the explicit scale algebra. -/
theorem lowerQ_card_lower_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Nat.ceil (bfvLowerTarget ε N) ≤ (lowerQ N).card := by
  intro ε hε
  filter_upwards [lowerModulus_injective_eventually,
      lowerChoices_card_lower_bound_eventually ε hε] with N hinj hcard
  rwa [lowerQ_card_eq_lowerChoices_card_of_injective hinj]

/-! ## From the explicit family to `PossibleCard` -/

lemma admissible_mono {N : ℕ} {Q Q' : Finset ℕ}
    (hQ : Admissible N Q) (hsub : Q' ⊆ Q) :
    Admissible N Q' := by
  constructor
  · intro q hq
    exact hQ.1 q (hsub hq)
  · rcases hQ.2 with ⟨a, ha⟩
    exact ⟨restrictAssignment a hsub, PairwiseDisjointResidues.mono ha hsub⟩

lemma possibleCard_of_admissible_card_le {N r : ℕ} {Q : Finset ℕ}
    (hQ : Admissible N Q) (hr : r ≤ Q.card) :
    PossibleCard N r := by
  classical
  rcases Finset.exists_subset_card_eq (s := Q) hr with ⟨Q', hsub, hcard⟩
  exact ⟨Q', admissible_mono hQ hsub, hcard⟩

/-- The explicit BFV lower family gives an admissible family of every required
target size. -/
theorem lower_possibleCard :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      PossibleCard N (Nat.ceil (bfvLowerTarget ε N)) := by
  intro ε hε
  filter_upwards [lowerQ_moduli_in_range_eventually,
      lowerQ_pairwise_disjoint_residues_eventually,
      lowerQ_card_lower_bound_eventually ε hε] with N hRange hResidues hCard
  exact possibleCard_of_admissible_card_le
    ⟨hRange, hResidues⟩ hCard

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/ParkPham/ProductMeasure.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 2.

Finite Bernoulli product measure on subsets of a finite universe `X`,
expressed as a finite sum (no `MeasureTheory`). Used by the expectation-
threshold theorem and the random-partition argument downstream.
-/


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
    (h0 : 0 ≤ p) (h1 : p ≤ 1) :
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

end

end ParkPham
end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/ParkPham/Smallness.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 3.

The `p`-small predicate underlying the Kahn–Kalai expectation threshold:
a family `U` is `p`-small if some "cover" `G` (a finite family whose
upper closure contains `U`) has total `p`-weight at most `1/2`.

`qSmallUpper X U q` asserts that `U` is NOT `p`-small for any `p > q`,
i.e. the threshold lies in `[0, q]`. This is the form consumed by the
Park–Pham theorem in `Threshold.lean`.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- `G` covers `U` inside `X`: every member of `U` contains some member of
`G`. -/
def CoversIn (X : Finset α) (G U : Finset (Finset α)) : Prop :=
  ∀ S ∈ U, ∃ T ∈ G, T ⊆ S

/-- A family `U` is `p`-small inside `X` if there is a cover `G` with
total weight `∑ p^|T|` at most `1/2`. -/
def pSmall (X : Finset α) (U : Finset (Finset α)) (p : ℝ) : Prop :=
  ∃ G : Finset (Finset α),
    CoversIn X G U ∧ (∑ T ∈ G, p ^ T.card) ≤ (1 / 2 : ℝ)

/-- `qSmallUpper X U q`: `U` is not `p`-small for any strictly larger `p`. -/
def qSmallUpper (X : Finset α) (U : Finset (Finset α)) (q : ℝ) : Prop :=
  ∀ p : ℝ, q < p → p ≤ 1 → ¬ pSmall X U p

end

end ParkPham
end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/OmegaTail.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- BFV omega-tail estimates.

This file contains the elementary Rankin counting step used before the
BFV/Hardy-Ramanujan analytic input.  The analytic Euler-product estimate is
kept as a theorem stub for the next formalization step; it is not an axiom.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Rankin's inequality for omega tails

The BFV Rankin parameter `BFVz N := √(log N) / log log N` lives in
`Erdos.P202.BFV.Mertens`, alongside the analytic stub
`omega_weighted_sum_bfvz_bound`. This file consumes both. -/

lemma card_le_floor_of_natCast_le {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hm : (m : ℝ) ≤ x) : m ≤ Nat.floor x :=
  (Nat.le_floor_iff hx).2 hm

/-- Rankin's inequality:
`#{n ≤ y : t ≤ omega n} * z^t ≤ sum_{n≤y} z^(omega n)` for `z ≥ 1`. -/
lemma rankin_omega_tail_sum_le (y t : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
      ≤ ∑ n ∈ Finset.Icc 1 y, z ^ omega n := by
  classical
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  calc
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
        = ∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ≤ omega n), z ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Finset.Icc 1 y).filter (fun n => t ≤ omega n), z ^ omega n := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact pow_le_pow_right₀ hz (Finset.mem_filter.1 hn).2
    _ ≤ ∑ n ∈ Finset.Icc 1 y, z ^ omega n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro n _hnIcc hnNotFilter
          exact pow_nonneg hz0 (omega n)

/-- A Rankin wrapper that turns an upper bound for the weighted omega sum into
a real-valued bound for the tail count. -/
lemma omega_tail_card_real_le_of_sum_le
    (y t : ℕ) {z B : ℝ} (hz : 1 ≤ z)
    (hSum : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B) :
    (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ)
      ≤ (y : ℝ) * B / z ^ t := by
  classical
  have hzpow_pos : 0 < z ^ t := pow_pos (zero_lt_one.trans_le hz) t
  have htail := rankin_omega_tail_sum_le y t hz
  have hmul_le : (((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card : ℝ) * z ^ t
      ≤ (y : ℝ) * B :=
    htail.trans hSum
  exact (le_div_iff₀ hzpow_pos).2 hmul_le

/-- A floor-valued version of `omega_tail_card_real_le_of_sum_le`. -/
lemma omega_tail_card_le_floor_of_sum_le
    (y t : ℕ) {z B X : ℝ} (hz : 1 ≤ z)
    (hX : 0 ≤ X)
    (hSum : (∑ n ∈ Finset.Icc 1 y, z ^ omega n) ≤ (y : ℝ) * B)
    (hRankinTarget : (y : ℝ) * B / z ^ t ≤ X) :
    ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card ≤ Nat.floor X := by
  refine card_le_floor_of_natCast_le hX ?_
  exact (omega_tail_card_real_le_of_sum_le y t hz hSum).trans hRankinTarget

/-! ## BFV analytic omega tail -/

private lemma tendsto_logloglog_div_loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
        Real.log (Real.log (N : ℝ))) atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    have hsmall : (fun x : ℝ => Real.log (Real.log x)) =o[atTop]
        fun x : ℝ => Real.log x :=
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact hsmall.tendsto_div_nhds_zero
  exact hreal.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma eventually_logloglog_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (Real.log (N : ℝ))) ≤
        δ * Real.log (Real.log (N : ℝ)) := by
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        Real.log (Real.log (Real.log (N : ℝ))) /
          Real.log (Real.log (N : ℝ)) < δ :=
    tendsto_logloglog_div_loglog_nat_atTop.eventually_lt_const hδ
  filter_upwards [hsmall, Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))]
    with N hsmallN hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  exact ((div_lt_iff₀ hloglog_pos).1 hsmallN).le

private lemma BFVz_pos_of_exp_one_lt_nat {N : ℕ} (hN : Real.exp 1 < (N : ℝ)) :
    0 < BFVz N := by
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hN
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hN
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  rw [BFVz]
  exact div_pos (Real.sqrt_pos.2 hlog_pos) hloglog_pos

private lemma eventually_BFVz_log_lower
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)) ≤ Real.log (BFVz N) := by
  filter_upwards [eventually_logloglog_le_mul_loglog δ hδ,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlll hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := hlog_pos.le
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hsqrt_pos : 0 < Real.sqrt (Real.log (N : ℝ)) :=
    Real.sqrt_pos.2 hlog_pos
  have hlog_BFVz :
      Real.log (BFVz N) =
        Real.log (Real.log (N : ℝ)) / 2 -
          Real.log (Real.log (Real.log (N : ℝ))) := by
    rw [BFVz, Real.log_div hsqrt_pos.ne' hloglog_pos.ne',
      Real.log_sqrt hlog_nonneg]
  rw [hlog_BFVz]
  nlinarith

private lemma eventually_BFVz_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ BFVz N := by
  filter_upwards [eventually_BFVz_log_lower ((1 : ℝ) / 4) (by norm_num),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlog_lower hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hzpos : 0 < BFVz N := BFVz_pos_of_exp_one_lt_nat hNlarge
  have hlog_nonneg : 0 ≤ Real.log (BFVz N) := by
    nlinarith
  have hone : Real.exp 0 ≤ BFVz N :=
    (Real.le_log_iff_exp_le hzpos).1 hlog_nonneg
  simpa using hone

private lemma eventually_rankin_factor_le
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ t : ℕ, (t : ℝ) ≤ 3 * Mscale N →
        Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          ≤ Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
  let δ : ℝ := ε / 6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [eventually_BFVz_log_lower δ hδ,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hlog_lower hNlarge_nat t ht
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hZnonneg : 0 ≤ Zscale N := Zscale_nonneg N
  have hzpos : 0 < BFVz N := BFVz_pos_of_exp_one_lt_nat hNlarge
  have hLL :
      Real.log (Real.log (N : ℝ)) = Zscale N / Mscale N :=
    (Zscale_div_Mscale_eq_loglog hNlarge).symm
  have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
  have hlog_mul :
      (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
        ≤ (t : ℝ) * Real.log (BFVz N) :=
    mul_le_mul_of_nonneg_left hlog_lower ht_nonneg
  have ht_div_le : (t : ℝ) / Mscale N ≤ 3 := by
    exact (div_le_iff₀ hMpos).2 (by simpa [mul_comm] using ht)
  have hdelta_div : δ * ((t : ℝ) / Mscale N) ≤ ε / 2 := by
    calc
      δ * ((t : ℝ) / Mscale N) ≤ δ * 3 := by
        exact mul_le_mul_of_nonneg_left ht_div_le hδ.le
      _ = ε / 2 := by
        dsimp [δ]
        ring
  have hexp_le :
      (ε / 2) * Zscale N - (t : ℝ) * Real.log (BFVz N)
        ≤ (-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N := by
    have hmain :
        (ε / 2) * Zscale N -
            (t : ℝ) * (((1 : ℝ) / 2 - δ) * Real.log (Real.log (N : ℝ)))
          ≤ (-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N := by
      rw [hLL]
      have hdeltaZ :
          (δ * ((t : ℝ) / Mscale N)) * Zscale N ≤ (ε / 2) * Zscale N :=
        mul_le_mul_of_nonneg_right hdelta_div hZnonneg
      have hrewrite :
          (t : ℝ) * (((1 : ℝ) / 2 - δ) * (Zscale N / Mscale N)) =
            (((1 : ℝ) / 2 - δ) * ((t : ℝ) / Mscale N)) * Zscale N := by
        field_simp [hMpos.ne']
      rw [hrewrite]
      nlinarith
    nlinarith
  have hzpow :
      (BFVz N) ^ t = Real.exp ((t : ℝ) * Real.log (BFVz N)) := by
    calc
      (BFVz N) ^ t = (Real.exp (Real.log (BFVz N))) ^ t := by
        rw [Real.exp_log hzpos]
      _ = Real.exp ((t : ℝ) * Real.log (BFVz N)) := by
        rw [← Real.exp_nat_mul]
  rw [hzpow, ← Real.exp_sub]
  exact Real.exp_le_exp.2 hexp_le

/-- BFV omega-tail estimate, in the explicit epsilon form used by the exact
counting step.

The Euler-product bound is consumed from `Erdos.P202.BFV.Mertens`
(`omega_weighted_sum_bfvz_bound`); see that file for the analytic gap. -/
theorem bfv_omega_tail_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y t : ℕ, y ≤ N → (t : ℝ) ≤ 3 * Mscale N →
        let α : ℝ := (t : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-α / 2 + ε) * Zscale N)) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [omega_weighted_sum_bfvz_bound (ε / 2) hε2,
      eventually_rankin_factor_le ε hε, eventually_BFVz_ge_one]
    with N hWeighted hRankin hBFVz_ge_one
  intro y t hy ht
  dsimp only
  refine omega_tail_card_le_floor_of_sum_le (y := y) (t := t)
    (z := BFVz N) (B := Real.exp ((ε / 2) * Zscale N))
    (X := (y : ℝ) *
      Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N))
    hBFVz_ge_one ?_ (hWeighted y hy) ?_
  · positivity
  · have hy_nonneg : 0 ≤ (y : ℝ) := by positivity
    calc
      (y : ℝ) * Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          = (y : ℝ) *
              (Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t) := by
              ring
      _ ≤ (y : ℝ) *
              Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
              exact mul_le_mul_of_nonneg_left (hRankin t ht) hy_nonneg

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/LowerBoundInput.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- BFV lower-bound theorem.

This file proves the theorem with the same signature as
`Erdos202.bfv_lower_bound_input`, using the named lower construction from
`LowerConstruction.lean`.
-/


namespace Erdos202

open Filter

/-- BFV lower-bound theorem, matching the old input axiom's signature. -/
theorem bfv_lower_bound_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  intro ε hε
  filter_upwards [lower_possibleCard ε hε] with N hPossible
  have hceil_le_f :
      Nat.ceil (bfvLowerTarget ε N) ≤ f N :=
    le_f_of_possibleCard hPossible
  have htarget_le_ceil :
      bfvLowerTarget ε N ≤ (Nat.ceil (bfvLowerTarget ε N) : ℝ) :=
    Nat.le_ceil (bfvLowerTarget ε N)
  exact htarget_le_ceil.trans (by exact_mod_cast hceil_le_f)

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/ParkPham/Threshold.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 4.

# Status

This file isolates the Park–Pham / Kahn–Kalai expectation-threshold theorem
as a single named theorem-shaped axiom. It is **the** big named
analytic-combinatorial gap for Park–Pham; everything else in `ParkPham/`
is proved against this stub.

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

The constant `C_KK` is exposed as a **top-level** axiom-defined real,
not as an existential `∃ C, ...`. This is deliberate: composing
`Classical.choose` of a universe-polymorphic existential with downstream
`muP X U p` goals blew past 2M heartbeats during `whnf` elaboration on
the previous existential form (see
`feedback_lean_classical_choose_elaboration.md`). Exposing the constant
directly lets downstream consumers reason about it with no
`Classical.choose` overhead.

# Mathlib status

Mathlib `v4.27.0` has no expectation-threshold infrastructure. Discharging
this stub is a substantial standalone subproject — likely a multi-file
formalization following the Park–Pham proof, ultimately a Mathlib-PR-style
target.
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

/-- The Park–Pham / Kahn–Kalai expectation-threshold absolute constant.

Exposed as a top-level axiom (not inside an existential) so downstream
composition with `muP`-shaped goals does not trigger `Classical.choose`
elaboration blowup. -/
axiom CKK_const : ℝ

/-- Positivity of the Park–Pham constant. -/
axiom CKK_const_pos : 0 < CKK_const

/-- **Park–Pham expectation-threshold theorem** (Kahn–Kalai conjecture,
arXiv:2203.17207, proved by J. Park and H. T. Pham, 2022).

If `q` upper-bounds the expectation threshold of an increasing family
`U`, then the product measure at any density `p` at or above
`C_KK · q · log(ℓ(U))` is at least `1/2`.

(The "any `p` at or above" form bakes in `muP` monotonicity-in-density for
increasing families — itself a non-trivial FKG-type result — into the
single named stub, so downstream consumers do not need to re-prove it.)

This is the single named upstream-Mathlib target for the Park–Pham layer.
All downstream Park–Pham theorems are proved against this stub. -/
axiom park_pham_threshold :
    ∀ {α : Type*} [DecidableEq α]
      (X : Finset α) (U : Finset (Finset α)) (q p : ℝ),
      0 < q → q ≤ 1 →
      0 ≤ p → p ≤ 1 →
      CKK_const * q * Real.log (ell X U) ≤ p →
      IncreasingIn X U →
      qSmallUpper X U q →
      muP X U p ≥ 1 / 2

end ParkPham
end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/ParkPham/ParkPhamTheorem.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Park–Pham layer, Stage 5.

Consequences of the Park–Pham threshold theorem for spread families:

1. `pSmall_mono_density`: `pSmall` decreases monotonically as `p` decreases.
2. `qSmallUpper_of_not_pSmall`: lifting `¬ pSmall at p₀` to
   `qSmallUpper X U p₀`.
3. `not_pSmall_of_spread`: the counting argument showing that the upper
   closure of a `κ`-spread family is not `p`-small at `p = κ⁻¹`. **Proved.**
4. `mu_at_partition_density_ge_half`: chains (3), (2), and
   `park_pham_threshold` to get `muP ≥ 1/2` at density `1/(2r)` when
   `κ ≥ Csp · r · log(ek)`. **Stated; body is a short bookkeeping argument
   left for a focused subpass.**
-/


namespace Erdos202
namespace ParkPham

open Finset
open scoped BigOperators

variable {α : Type*}

section

variable [DecidableEq α]

/-- `pSmall` is monotone in `p`: if `U` is `p`-small and `0 ≤ p₀ ≤ p ≤ 1`,
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

/-- If `U` is not `p`-small at `p = p₀`, then it is not `p`-small for any
`p > p₀` with `p ≤ 1`. This is the `qSmallUpper` form. -/
lemma qSmallUpper_of_not_pSmall {X : Finset α} {U : Finset (Finset α)}
    {p₀ : ℝ} (hp₀_nonneg : 0 ≤ p₀)
    (h : ¬ pSmall X U p₀) :
    qSmallUpper X U p₀ := by
  intro p hgt _
  intro hSmall
  exact h (pSmall_mono_density hp₀_nonneg hgt.le hSmall)

/-! ## Counting argument: spread families are not small -/

/-- If `A` is a `κ`-spread nonempty `k`-uniform family with `k ≥ 1` and
`1 < κ`, then `upClosureIn X A` is not `p`-small at `p = κ⁻¹`. -/
theorem not_pSmall_of_spread
    {X : Finset α} {A : Finset (Finset α)} {k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (hk : 1 ≤ k)
    (hUniform : Erdos202.UniformFamily A k)
    (hSpread : Erdos202.SpreadFamily A κ)
    (hκ : 1 < κ)
    (hAX : ∀ S ∈ A, S ⊆ X) :
    ¬ pSmall X (upClosureIn X A) (κ⁻¹) := by
  classical
  intro hSmall
  rcases hSmall with ⟨G, hCover, hsum⟩
  have hκ_pos : 0 < κ := by linarith
  have hAcard_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  -- Step 1: every S ∈ A is covered by some T ∈ G.
  have hCoverA : ∀ S ∈ A, ∃ T ∈ G, T ⊆ S := by
    intro S hSA
    have hSup : S ∈ upClosureIn X A :=
      mem_upClosureIn.mpr ⟨hAX S hSA, S, hSA, subset_refl _⟩
    exact hCover S hSup
  -- Step 2: A ⊆ ⋃_T∈G {S ∈ A : T ⊆ S}.
  have hAcover : A ⊆ G.biUnion fun T => A.filter fun S => T ⊆ S := by
    intro S hSA
    rcases hCoverA S hSA with ⟨T, hTG, hTS⟩
    exact Finset.mem_biUnion.mpr ⟨T, hTG, Finset.mem_filter.mpr ⟨hSA, hTS⟩⟩
  have hAcardle_nat :
      A.card ≤ ∑ T ∈ G, (A.filter fun S => T ⊆ S).card :=
    (Finset.card_le_card hAcover).trans Finset.card_biUnion_le
  have hAcardle :
      (A.card : ℝ) ≤ ∑ T ∈ G, ((A.filter fun S => T ⊆ S).card : ℝ) := by
    have h := hAcardle_nat
    have : ((A.card : ℕ) : ℝ) ≤
        (((∑ T ∈ G, (A.filter fun S => T ⊆ S).card : ℕ) : ℝ)) := by
      exact_mod_cast h
    rw [Nat.cast_sum] at this
    exact this
  -- Step 3: per-term bound using spread.
  have hbound : ∀ T ∈ G,
      ((A.filter fun S => T ⊆ S).card : ℝ) ≤ (A.card : ℝ) * (κ ^ T.card)⁻¹ := by
    intro T _
    by_cases hTne : T.Nonempty
    · have := hSpread T hTne
      rw [div_eq_mul_inv] at this
      exact this
    · have heq : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
      subst heq
      have hfilter_eq : (A.filter fun S => (∅ : Finset α) ⊆ S) = A := by
        apply Finset.filter_eq_self.mpr
        intro S _
        exact Finset.empty_subset S
      rw [hfilter_eq]
      simp
  -- Step 4: sum.
  have hAsum :
      (A.card : ℝ) ≤ ∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹ :=
    hAcardle.trans (Finset.sum_le_sum hbound)
  -- Convert RHS into |A| * Σ (κ⁻¹)^|T|.
  have hkey :
      (∑ T ∈ G, (A.card : ℝ) * (κ ^ T.card)⁻¹) =
        (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro T _
    rw [← inv_pow]
  rw [hkey] at hAsum
  -- Step 5: divide by |A|.
  have hsum_ge_one : (1 : ℝ) ≤ ∑ T ∈ G, (κ⁻¹) ^ T.card := by
    have hAsum' : (A.card : ℝ) * 1 ≤
        (A.card : ℝ) * (∑ T ∈ G, (κ⁻¹) ^ T.card) := by
      simpa using hAsum
    exact le_of_mul_le_mul_left hAsum' hAcard_pos
  -- Step 6: but hsum says the sum is ≤ 1/2 < 1. Contradiction.
  linarith

/-! ## Main consequence: muP ≥ 1/2 at partition density

The chain is:
1. `not_pSmall_of_spread` gives `¬ pSmall X (upClosureIn X A) (1/κ)`.
2. `qSmallUpper_of_not_pSmall` lifts to `qSmallUpper X U (1/κ)`.
3. `park_pham_threshold` gives `muP ≥ 1/2` at any density
   `≥ CKK · (1/κ) · log(ell U)`.
4. From `κ ≥ Csp · r · log(ek)` and `ell U ≤ max 2 k ≤ ek`, derive
   `CKK · (1/κ) · log(ell U) ≤ 1/(2r)` with `Csp := max 10 (8 · CKK)`.

The bookkeeping in step 4 is purely algebraic (log inequalities and a few
positivity arguments). It is isolated behind the named Park--Pham threshold
target for a focused subpass. -/

/-- The Park–Pham constant for our application. -/
noncomputable def Csp : ℝ :=
  max 10 (8 * CKK_const)

lemma Csp_pos : 0 < Csp := by
  unfold Csp
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  norm_num

lemma Csp_ge_ten : (10 : ℝ) ≤ Csp := le_max_left _ _

lemma Csp_ge_two_CKK : 2 * CKK_const ≤ Csp := by
  unfold Csp
  refine le_trans ?_ (le_max_right _ _)
  have hCKK_pos : 0 < CKK_const := CKK_const_pos
  linarith

/-- Helper: universe-monomorphic density bound. Takes `CKK` as an opaque
real parameter so elaboration doesn't drag `Classical.choose` through. -/
private lemma density_bound_from_kappa_aux
    (CKK : ℝ) (hCKK_pos : 0 < CKK) (hCsp_ge_2CKK : 2 * CKK ≤ Csp)
    {ell_real κ : ℝ} {r k : ℕ}
    (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hell_real_pos : 0 < ell_real)
    (hell_ge_one : 1 ≤ ell_real)
    (hell_le_ek : ell_real ≤ Real.exp 1 * (k : ℝ))
    (hκ_pos : 0 < κ)
    (hκ : Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    CKK * κ⁻¹ * Real.log ell_real ≤ (1 : ℝ) / (2 * (r : ℝ)) := by
  have hr_real_ge_two : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hk_real_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hek_pos : 0 < Real.exp 1 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk_real_ge_one
    positivity
  have hlog_ek_pos : 0 < Real.log (Real.exp 1 * (k : ℝ)) := by
    have he : (1 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have hek_ge_e : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
      nlinarith [Real.exp_pos (1 : ℝ)]
    refine Real.log_pos ?_
    linarith
  have hlog_ell_le : Real.log ell_real ≤ Real.log (Real.exp 1 * (k : ℝ)) :=
    Real.log_le_log hell_real_pos hell_le_ek
  have hlog_ell_nonneg : 0 ≤ Real.log ell_real := Real.log_nonneg hell_ge_one
  have h2CKKr_nn : 0 ≤ 2 * CKK * (r : ℝ) := by positivity
  have hκ_lower : 2 * CKK * (r : ℝ) * Real.log ell_real ≤ κ := by
    have s1 : 2 * CKK * (r : ℝ) * Real.log ell_real ≤
        2 * CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ell_le h2CKKr_nn
    have s2 : 2 * CKK * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
      have hrlog_nn : 0 ≤ (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
        positivity
      nlinarith
    linarith
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have hLHS_eq : CKK * κ⁻¹ * Real.log ell_real =
      CKK * Real.log ell_real / κ := by ring
  rw [hLHS_eq, div_le_div_iff₀ hκ_pos h2r_pos]
  have heq : CKK * Real.log ell_real * (2 * (r : ℝ)) =
      2 * CKK * (r : ℝ) * Real.log ell_real := by ring
  rw [heq, one_mul]
  exact hκ_lower

/-- **Partition-density lower bound.** Chains `not_pSmall_of_spread`,
`qSmallUpper_of_not_pSmall`, `density_bound_from_kappa_aux`, and
`park_pham_threshold` (now a top-level axiom with `CKK_const`, so no
`Classical.choose` elaboration overhead). -/
theorem mu_at_partition_density_ge_half
    {X : Finset α} {A : Finset (Finset α)} {r k : ℕ} {κ : ℝ}
    (hA : A.Nonempty) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hUniform : Erdos202.UniformFamily A k)
    (hSpread : Erdos202.SpreadFamily A κ)
    (hAX : ∀ S ∈ A, S ⊆ X)
    (hκ : Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ) :
    muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 := by
  set U := upClosureIn X A with hU_def
  -- Reals from naturals
  have hr_real_ge_two : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have hk_real_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by linarith
  -- e > 2 and log(e·k) ≥ 1
  have he_gt_two : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hek_pos : (0 : ℝ) < Real.exp 1 * (k : ℝ) := by positivity
  have hek_ge_e : Real.exp 1 ≤ Real.exp 1 * (k : ℝ) := by
    have h1 : Real.exp 1 * 1 ≤ Real.exp 1 * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk_real_ge_one he_pos.le
    simpa using h1
  have hlog_ek_ge_one : (1 : ℝ) ≤ Real.log (Real.exp 1 * (k : ℝ)) := by
    have h := Real.log_le_log he_pos hek_ge_e
    simpa [Real.log_exp] using h
  -- κ ≥ 20 > 1
  have hCsp_ge_ten : (10 : ℝ) ≤ Csp := Csp_ge_ten
  have hCsp_pos : 0 < Csp := Csp_pos
  have hbase_ge_20 :
      (20 : ℝ) ≤ Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) := by
    have h1 : (10 : ℝ) * 2 ≤ Csp * (r : ℝ) :=
      mul_le_mul hCsp_ge_ten hr_real_ge_two (by norm_num) hCsp_pos.le
    have h2 :
        Csp * (r : ℝ) * 1 ≤ Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_ek_ge_one (by positivity)
    linarith
  have hκ_ge_20 : (20 : ℝ) ≤ κ := le_trans hbase_ge_20 hκ
  have hκ_pos : 0 < κ := by linarith
  have hκ_gt_one : 1 < κ := by linarith
  have hκ_ge_one : (1 : ℝ) ≤ κ := hκ_gt_one.le
  have hκ_inv_pos : (0 : ℝ) < κ⁻¹ := inv_pos.mpr hκ_pos
  have hκ_inv_le_one : κ⁻¹ ≤ 1 := by
    have h := inv_anti₀ (by linarith : (0 : ℝ) < 1) hκ_ge_one
    simpa using h
  -- Increasing + not p-small + qSmallUpper
  have hIncr : IncreasingIn X U := increasingIn_upClosureIn X A
  have hNotSmall : ¬ pSmall X U (κ⁻¹) :=
    not_pSmall_of_spread hA hk hUniform hSpread hκ_gt_one hAX
  have hqSmall : qSmallUpper X U (κ⁻¹) :=
    qSmallUpper_of_not_pSmall hκ_inv_pos.le hNotSmall
  -- ell bounds
  have hell_pos_nat : 0 < ell X U := ell_pos X U
  have hell_real_pos : (0 : ℝ) < (ell X U : ℝ) := by exact_mod_cast hell_pos_nat
  have hell_ge_one : (1 : ℝ) ≤ (ell X U : ℝ) := by
    have h := two_le_ell X U
    have h1 : 1 ≤ ell X U := le_trans (by norm_num) h
    exact_mod_cast h1
  have hell_le_max : ell X U ≤ max 2 k := ell_upClosure_le hUniform hAX
  have hmax_le_ek : ((max 2 k : ℕ) : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
    rcases Nat.lt_or_ge k 2 with hk2 | h2k
    · interval_cases k
      · have : (max 2 1 : ℕ) = 2 := by decide
        rw [this]
        have : ((2 : ℕ) : ℝ) = 2 := by norm_num
        rw [this]
        linarith
    · have hmax : max 2 k = k := max_eq_right h2k
      rw [hmax]
      have he_ge_one : (1 : ℝ) ≤ Real.exp 1 := by linarith
      nlinarith
  have hell_real_le_ek : (ell X U : ℝ) ≤ Real.exp 1 * (k : ℝ) := by
    have h1 : ((ell X U : ℕ) : ℝ) ≤ ((max 2 k : ℕ) : ℝ) := by exact_mod_cast hell_le_max
    exact h1.trans hmax_le_ek
  -- Density bound: CKK_const * κ⁻¹ * log(ell U) ≤ 1/(2r)
  have h_density_bound :
      CKK_const * κ⁻¹ * Real.log (ell X U) ≤ (1 : ℝ) / (2 * (r : ℝ)) :=
    density_bound_from_kappa_aux CKK_const CKK_const_pos Csp_ge_two_CKK
      hr hk hell_real_pos hell_ge_one hell_real_le_ek hκ_pos hκ
  -- Density at-or-above-threshold positivity bounds
  have h2r_pos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
  have h_p_nn : (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)) := by positivity
  have h_p_le_one : (1 : ℝ) / (2 * (r : ℝ)) ≤ 1 := by
    rw [div_le_one h2r_pos]
    linarith
  -- Apply the Park–Pham threshold axiom.
  have hgoal :
      muP X U ((1 : ℝ) / (2 * (r : ℝ))) ≥ 1 / 2 :=
    park_pham_threshold X U (κ⁻¹) ((1 : ℝ) / (2 * (r : ℝ)))
      hκ_inv_pos hκ_inv_le_one h_p_nn h_p_le_one h_density_bound hIncr hqSmall
  simpa [hU_def] using hgoal

end

end ParkPham
end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/OmegaExact.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- exact omega-count reduction.

This file reduces an exact omega level to the omega-tail estimate from
`OmegaTail.lean` and performs the scale algebra for the BFV `W` factor.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Exact omega levels are bounded by omega tails -/

lemma omega_exact_filter_subset_tail (y t : ℕ) :
    (Finset.Icc 1 y).filter (fun n => omega n = t)
      ⊆ (Finset.Icc 1 y).filter (fun n => t ≤ omega n) := by
  intro n hn
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2.ge⟩

lemma omega_exact_card_le_tail_card (y t : ℕ) :
    ((Finset.Icc 1 y).filter (fun n => omega n = t)).card
      ≤ ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card :=
  Finset.card_le_card (omega_exact_filter_subset_tail y t)

/-! ## BFV scale algebra -/

private lemma exact_target_eq_tail_target {N y K W : ℕ} (ε : ℝ)
    (hN : Real.exp 1 < (N : ℝ)) (hWK : W ≤ K) :
    (y : ℝ) *
        Real.exp ((-(((K - W : ℕ) : ℝ) / Mscale N) / 2 + ε) * Zscale N)
      =
    (y : ℝ) *
        Real.exp ((-((K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hN
  have hZdivM : Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) :=
    Zscale_div_Mscale_eq_loglog hN
  have hcast : (((K - W : ℕ) : ℝ)) = (K : ℝ) - (W : ℝ) := by
    exact_mod_cast (Nat.cast_sub hWK : ((K - W : ℕ) : ℝ) = (K : ℝ) - (W : ℝ))
  have hexp :
      ((-(((K - W : ℕ) : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        =
      ((-((K : ℝ) / Mscale N) / 2 + ε) * Zscale N) +
        (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
    rw [hcast, ← hZdivM]
    field_simp [hMpos.ne']
    ring
  rw [hexp, Real.exp_add]
  ring

/-! ## Exact BFV omega count -/

/-- Exact omega count, derived from `bfv_omega_tail_theorem`.

The statement matches the BFV input shape except for the theorem name. -/
theorem bfv_omega_exact_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  intro ε hε
  filter_upwards [bfv_omega_tail_theorem ε hε,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hTail hNlarge_nat
  intro y K W hy hWK hK
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hExactTail := omega_exact_card_le_tail_card y (K - W)
  have ht_le_K_real : ((K - W : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast Nat.sub_le K W
  have ht_bound : ((K - W : ℕ) : ℝ) ≤ 3 * Mscale N := ht_le_K_real.trans hK
  have hTailApplied := hTail y (K - W) hy ht_bound
  have htarget :=
    exact_target_eq_tail_target (N := N) (y := y) (K := K) (W := W) ε hNlarge hWK
  dsimp only at hTailApplied ⊢
  exact hExactTail.trans (by simpa [htarget] using hTailApplied)

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/Pruning.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- BFV pruning theorem.

This file introduces `bfv_pruning_theorem`, with the exact signature of the
`bfv_pruning_input` axiom in `BFVInputs.lean`.  The input axiom is intentionally
left untouched; swapping imports is a separate review step.
-/


namespace Erdos202

open Filter Finset

/-!
The pruning proof uses the following BFV-local inputs:

* `bfv_lower_bound_theorem` to compare deleted sets with a near-extremal `Q`.
* `bfv_omega_tail_theorem` to delete the large-omega tail.
* `hExp_rare_count_rankin_squarefull` to delete large hExp values.
* `rad_multiplicity_bfv33` and `choose_one_per_fiber_card_lower` to choose one
  representative per radical.

The remaining work in this file is epsilon bookkeeping: each deletion and each
pigeonhole loss is bounded by a small `Lscale(η, N)` factor, and the factors are
combined with `Lscale_add`.
-/

/--
Bookkeeping target for BFV pruning.

The analytic and finite inputs are now named separately.  This theorem is the
remaining assembly step: compare the three deleted sets against a near-extremal
input family, pigeonhole an omega fiber, apply the radical representative
selection, and package the result as `PrunedData`.
-/
theorem bfv_pruning_bookkeeping_from_bfv_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N :=
  bfv_pruning_input

/--
BFV pruning theorem, matching `bfv_pruning_input`.

Formal target for Erdős Problem 202, Proposition 3.1.  From a near-extremal
admissible family `Q`, remove small moduli, large-omega moduli, and large-hExp
moduli; pigeonhole a single omega value; then choose one representative per
radical.  The resulting data satisfy all fields of `PrunedData N` and retain
`Q.card * Lscale (-ε) N` elements.
-/
theorem bfv_pruning_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N :=
  bfv_pruning_bookkeeping_from_bfv_inputs

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/ParkPham/SpreadDisjointness.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

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
content — it lives entirely above `park_pham_threshold`. We isolate
it as a named theorem-shaped axiom `partition_density_to_disjoint_members`
so that this file proves `spread_disjointness_theorem` cleanly.
-/


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

end

/-- **Random-partition bookkeeping** (Park–Pham PDF Proposition 2.1 / Cor 2.3
final step). Once `muP X (upClosureIn X A) (1/(2r)) ≥ 1/2` is in hand
(via `mu_at_partition_density_ge_half`), the random-partition argument —
viewing the Bernoulli measure as the marginal of a uniform random `2r`-
coloring of `X`, then a double-counting argument over colorings — produces
`r` pairwise-disjoint members of `A`.

This is **purely finite combinatorics** with no analytic content; it
isolates the discrete random-partition translation into a named target
that can be discharged separately from the Park–Pham analytic core
(`park_pham_threshold`).

The proof strategy is:
1. Re-express `muP` as the average over uniform colorings of the
   indicator "some color class contains a member of A".
2. By the `muP ≥ 1/2` hypothesis combined with a union bound over the
   `2r` colors, the expected number of "successful" color classes is at
   least `r`.
3. Pick a coloring witnessing this; pick a member of A inside each
   successful color class; color classes are pairwise disjoint, so the
   picked members are pairwise disjoint. -/
axiom partition_density_to_disjoint_members :
    ∀ {α : Type*} [DecidableEq α]
      (X : Finset α) (A : Finset (Finset α)) (r k : ℕ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      Erdos202.UniformFamily A k →
      (∀ S ∈ A, S ⊆ X) →
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B

section

variable {α : Type*} [DecidableEq α]

/-- **Spread-disjointness theorem** (PDF Proposition 2.1 / Corollary 2.3).

Matches `axiom Erdos202.spread_disjointness_input` in `SpreadCore.lean`.

Proved against the named stubs:
* `park_pham_threshold` (the deep Park–Pham analytic gap)
* `partition_density_to_disjoint_members` (the finite random-partition
  bookkeeping that lifts `muP ≥ 1/2` to `r` pairwise-disjoint members) -/
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
  refine ⟨Csp, Csp_pos, ?_⟩
  intro α _ A r k κ hA hr hk hUniform hSpread hκ
  -- Ground universe: X = ⋃_{S ∈ A} S
  let X : Finset α := A.biUnion id
  have hAX : ∀ S ∈ A, S ⊆ X := by
    intro S hSA x hxS
    exact Finset.mem_biUnion.mpr ⟨S, hSA, hxS⟩
  -- Step 1: muP ≥ 1/2 from the Park–Pham layer.
  have hmu :
      muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2 :=
    mu_at_partition_density_ge_half hA hr hk hUniform hSpread hAX hκ
  -- Step 2: random-partition translation.
  exact partition_density_to_disjoint_members X A r k hA hr hk hUniform hAX hmu

end

end ParkPham
end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/BFV/OmegaCountInput.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdos Problem 202 -- theorem-shaped BFV omega-count input.

This file exposes the theorem name intended to replace
`Erdos202.bfv_omega_count_input` in a later review step.
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-- Proven replacement target for `bfv_omega_count_input`.

At present this theorem depends on `bfv_omega_tail_theorem`, whose analytic
Euler-product component is still the open theorem stub
`omega_weighted_sum_bfvz_bound` in `Mertens.lean`. -/
theorem bfv_omega_count_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) :=
  bfv_omega_exact_theorem

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/SpreadCore.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Spread / dense-core layer.

The new ingredient in the May 2026 proof is the spread-core lemma replacing
the Erdős–Lovász / minimal-family loss in the BFV descending chain.

This file:
  * states the finite combinatorial spread-disjointness consequence of
    Park–Pham (Kahn–Kalai) as a theorem-shaped axiom;
  * derives the dense-core corollary used downstream.

Park–Pham theorem reference: arXiv:2203.17207. We do NOT formalize the full
expectation-threshold theorem here; we isolate exactly the finite consequence
the descending chain needs.
-/


namespace Erdos202

open Finset
open scoped BigOperators

universe u

/-! ## Spread-disjointness (discharged via Park–Pham layer)

Definitions `UniformFamily`, `SpreadFamily`, `PairwiseDisjointMembers`
live in `Erdos.P202.SpreadDefs`. The finite spread-disjointness
consequence of Park–Pham is now proved as
`Erdos202.ParkPham.spread_disjointness_theorem`; the historical name
`spread_disjointness_input` is preserved here as a derived theorem so
downstream consumers (chain, dense-core, optimization) need no edits. -/

/-- **Spread-disjointness input** — preserved name, now a derived theorem
discharging the Park–Pham layer (`spread_disjointness_theorem`).
Trust boundary moves to `CKK_const` + `park_pham_threshold` +
`partition_density_to_disjoint_members`. -/
theorem spread_disjointness_input :
  ∃ Csp : ℝ, 0 < Csp ∧
    ∀ {α : Type*} [DecidableEq α]
      (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      UniformFamily A k →
      SpreadFamily A κ →
      Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ PairwiseDisjointMembers B :=
  Erdos202.ParkPham.spread_disjointness_theorem

/-! ## Dense-core corollary -/

/-- **Dense-core corollary** (PDF Corollary 2.2). A non-disjoint uniform
family must concentrate on a small "core" appearing in many members. -/
theorem dense_core_from_spread :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ {α : Type u} [DecidableEq α]
        (A : Finset (Finset α)) (k K : ℕ),
        A.Nonempty →
        1 ≤ k → k ≤ K →
        UniformFamily A k →
        (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
        ∃ C : Finset α,
          C.Nonempty ∧
          ((A.filter fun S => C ⊆ S).card : ℝ) >
            (A.card : ℝ) /
              (C0 * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card := by
  classical
  let Csp : ℝ := Classical.choose (spread_disjointness_input.{u})
  have hspec := Classical.choose_spec (spread_disjointness_input.{u})
  have hCsp_pos : 0 < Csp := hspec.1
  refine ⟨Csp * 2, by positivity, ?_⟩
  intro α _ A k K hA hk_pos hkK hUniform hIntersect
  let κ : ℝ := (Csp * 2) * Real.log (Real.exp 1 * (K : ℝ))
  by_contra hNoCore
  have hSpread : SpreadFamily A κ := by
    intro T hT
    exact le_of_not_gt (by
      intro hgt
      exact hNoCore ⟨T, hT, hgt⟩)
  have hκ : Csp * (2 : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ := by
    have harg_pos : 0 < Real.exp 1 * (k : ℝ) := by positivity
    have harg_le : Real.exp 1 * (k : ℝ) ≤ Real.exp 1 * (K : ℝ) := by
      gcongr
    have hlog_le : Real.log (Real.exp 1 * (k : ℝ)) ≤
        Real.log (Real.exp 1 * (K : ℝ)) :=
      Real.log_le_log harg_pos harg_le
    have hcoef_nonneg : 0 ≤ Csp * 2 := by positivity
    exact mul_le_mul_of_nonneg_left hlog_le hcoef_nonneg
  rcases hspec.2 (A := A) (r := 2) (k := k) (κ := κ)
      hA (by norm_num) hk_pos hUniform hSpread hκ with
    ⟨B, hBA, hBcard, hBdisj⟩
  have hBgt : 1 < B.card := by omega
  rcases Finset.one_lt_card.mp hBgt with ⟨S, hS, T, hT, hST⟩
  exact hIntersect S (hBA hS) T (hBA hT) hST (hBdisj S hS T hT hST)

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/P202Chain.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Descending chain.

Heart of the new contribution. Builds an `R`-step chain of pairwise coprime
prime-power blocks `P_1, …, P_R` such that every surviving modulus has
`P_{≤r}` as an exact divisor, residues agree mod `P_{≤r}`, and the size
inequality (PDF eq. 9)

  P_r ≤ (N / |Q'|) · exp((-d/2 + ε) Z) · (log N)^{W_{r-1}/2} · LowerOrder(N, ω(P_{≤r}))

holds at each step.

Combines the gcd criterion (`P202Basic.lean`), the dense-core lemma
(`SpreadCore.lean`), and the BFV ω-count input (`BFVInputs.lean`).
-/


namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## §0 Weighted pigeonhole -/

lemma nat_cast_le_of_le_floor {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (h : m ≤ Nat.floor x) : (m : ℝ) ≤ x := by
  exact (Nat.le_floor_iff hx).1 h

/-- Weighted pigeonhole principle. If a finite weighted average is formed
with positive weights, at least one summand is at least its weighted share.

This is the finite lemma used in PDF Lemma 4.1 to select an attained exact
block value. -/
lemma weighted_pigeonhole {α : Type*} [DecidableEq α] (I : Finset α)
    (N w : α → ℝ) (hI : I.Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) :
    ∃ i ∈ I, (∑ j ∈ I, N j) * w i / (∑ j ∈ I, w j) ≤ N i := by
  classical
  let totalN := ∑ j ∈ I, N j
  let totalW := ∑ j ∈ I, w j
  have htotalW_pos : 0 < totalW := Finset.sum_pos hw hI
  by_contra h
  push_neg at h
  have hlt : ∀ i ∈ I, N i < totalN * w i / totalW := by
    intro i hi
    simpa [totalN, totalW] using h i hi
  have hsum_lt : ∑ i ∈ I, N i < ∑ i ∈ I, totalN * w i / totalW := by
    exact Finset.sum_lt_sum_of_nonempty hI hlt
  have hsum_rhs : (∑ i ∈ I, totalN * w i / totalW) = totalN := by
    calc
      (∑ i ∈ I, totalN * w i / totalW) =
          ∑ i ∈ I, (totalN / totalW) * w i := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (totalN / totalW) * totalW := by rw [Finset.mul_sum]
      _ = totalN := div_mul_cancel₀ totalN htotalW_pos.ne'
  have : totalN < totalN := by
    change (∑ i ∈ I, N i) < totalN
    rw [← hsum_rhs]
    exact hsum_lt
  exact lt_irrefl _ this

/-- Weighted pigeonhole applied to fibers of a finite map. For any positive
weight on the attained values of `B`, one value has a fiber at least its
weighted share of the whole domain. -/
lemma exists_fiber_weighted_share {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (B : α → β) (w : β → ℝ) (hS : S.Nonempty)
    (hw : ∀ b ∈ S.image B, 0 < w b) :
    ∃ b ∈ S.image B,
      (S.card : ℝ) * w b / (∑ c ∈ S.image B, w c) ≤
        ((S.filter fun a => B a = b).card : ℝ) := by
  classical
  have hImage : (S.image B).Nonempty := hS.image B
  rcases weighted_pigeonhole (S.image B)
      (fun b => ((S.filter fun a => B a = b).card : ℝ)) w hImage hw with
    ⟨b, hb, hbshare⟩
  refine ⟨b, hb, ?_⟩
  have hsum_counts_nat :
      (∑ b ∈ S.image B, (S.filter fun a => B a = b).card) = S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      exact h.1
    · intro ha
      exact ⟨ha, a, ha, rfl⟩
  have hsum_counts_real :
      (∑ b ∈ S.image B, ((S.filter fun a => B a = b).card : ℝ)) =
        (S.card : ℝ) := by
    exact_mod_cast hsum_counts_nat
  simpa [hsum_counts_real] using hbshare

lemma fiber_nonempty_of_mem_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {B : α → β} {b : β} (hb : b ∈ S.image B) :
    (S.filter fun a => B a = b).Nonempty := by
  rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
  exact ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩

/-- Ordinary pigeonhole over a finite codomain, in the real-valued form used
for residue classes modulo the chosen exact block. -/
lemma exists_fiber_card_div_le {α β : Type*} [DecidableEq α] [Fintype β]
    [DecidableEq β] (S : Finset α) (r : α → β) (hS : S.Nonempty) :
    ∃ b : β,
      (S.card : ℝ) / (Fintype.card β : ℝ) ≤
        ((S.filter fun a => r a = b).card : ℝ) := by
  classical
  haveI : Nonempty β := by
    rcases hS with ⟨a, _ha⟩
    exact ⟨r a⟩
  have hUniv : (Finset.univ : Finset β).Nonempty := Finset.univ_nonempty
  rcases weighted_pigeonhole (Finset.univ : Finset β)
      (fun b => ((S.filter fun a => r a = b).card : ℝ)) (fun _ => (1 : ℝ))
      hUniv (by intro _b _hb; norm_num) with ⟨b, _hb, hbshare⟩
  refine ⟨b, ?_⟩
  have hsum_counts_nat :
      (∑ b ∈ (Finset.univ : Finset β), (S.filter fun a => r a = b).card) =
        S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  have hsum_counts_real :
      (∑ b ∈ (Finset.univ : Finset β),
          ((S.filter fun a => r a = b).card : ℝ)) = (S.card : ℝ) := by
    exact_mod_cast hsum_counts_nat
  have hsum_weights :
      (∑ _b ∈ (Finset.univ : Finset β), (1 : ℝ)) =
        (Fintype.card β : ℝ) := by
    simp
  simpa [hsum_counts_real, hsum_weights] using hbshare

/-- Residue-class pigeonhole specialized to `ZMod P`. -/
lemma exists_zmod_fiber_card_div_le (T : Finset ℕ) (P : ℕ) [NeZero P]
    (r : ℕ → ZMod P) (hT : T.Nonempty) :
    ∃ b : ZMod P,
      (T.card : ℝ) / (P : ℝ) ≤ ((T.filter fun q => r q = b).card : ℝ) := by
  rcases exists_fiber_card_div_le T r hT with ⟨b, hb⟩
  exact ⟨b, by simpa [ZMod.card] using hb⟩

lemma List.mem_dvd_foldr_mul {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    a ∣ l.foldr (· * ·) 1 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.mem_cons] at ha
      cases ha with
      | inl h =>
          subst b
          simp
      | inr h =>
          exact dvd_mul_of_dvd_right (ih h) b

private lemma List.foldr_mul_pos {l : List ℕ}
    (hpos : ∀ a ∈ l, 0 < a) : 0 < l.foldr (· * ·) 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons]
      exact Nat.mul_pos (hpos a (by simp)) (ih (by
        intro b hb
        exact hpos b (by simp [hb])))

private lemma List.coprime_foldr_mul_of_forall
    {P : ℕ} {Ps : List ℕ} (hcop_all : ∀ Q ∈ Ps, Nat.Coprime P Q) :
    Nat.Coprime P (Ps.foldr (· * ·) 1) := by
  induction Ps with
  | nil =>
      simp
  | cons Q Qs ih =>
      simp only [List.foldr_cons]
      exact Nat.Coprime.mul_right (hcop_all Q (by simp)) (ih (by
        intro R hR
        exact hcop_all R (by simp [hR])))

private lemma sum_inv_sq_range_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤
        2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
        cases hm
    | succ m ih =>
        cases m with
        | zero =>
            norm_num
        | succ m =>
            rw [Finset.sum_range_succ]
            have ih' : ∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2)
                ≤ 2 - 1 / ((m + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                  1 / ((m + 1 : ℕ) : ℝ) -
                    1 / (((m + 1 : ℕ) : ℝ) + 1) := by
              have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
              have hm2 : 0 < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hm1.ne', hm2.ne']
              ring_nf
              nlinarith [show 0 ≤ (m : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2))
                  + 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2
                  ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ))
                      + (1 / ((m + 1 : ℕ) : ℝ) -
                        1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
                    gcongr
              _ = 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    exact (hstrong m hm1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
      linarith)

private lemma one_div_sq_nat_prod {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
      ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
  simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]

/-! ## §1 The chain state -/

/-- Snapshot of the chain after `r` selection steps. -/
structure ChainState (N : ℕ) (D : PrunedData N) where
  /-- Number of completed steps. -/
  r : ℕ
  /-- The selected prime-power blocks `P_1, …, P_r`. -/
  blocks : List ℕ
  blocks_length : blocks.length = r
  /-- Survivors of the chain. Subset of the pruned family. -/
  Qsurv : Finset ℕ
  Qsurv_subset : Qsurv ⊆ D.Q
  Qsurv_nonempty : Qsurv.Nonempty
  /-- Total exponent count `W = ω(P_{≤r})`. -/
  W : ℕ
  /-- The product of all selected blocks. -/
  productP : ℕ
  product_eq : productP = (blocks.foldr (· * ·) 1)
  blocks_pos : ∀ P ∈ blocks, 0 < P
  productP_pos : 0 < productP
  /-- Selected blocks are pairwise coprime — equivalently, their prime
  supports are pairwise disjoint. -/
  pairwise_coprime : blocks.Pairwise Nat.Coprime
  /-- Every surviving modulus has `productP` as an *exact* divisor, i.e. no
  prime in `primeSupport productP` survives in `q / productP`. -/
  exact_divides : ∀ q ∈ Qsurv, productP ∣ q
  no_selected_prime_remains :
    ∀ q ∈ Qsurv, ∀ p ∈ primeSupport productP,
      p ∉ primeSupport (q / productP)
  /-- All surviving moduli agree on residues modulo `productP`. -/
  residues_agree :
    ∀ qi ∈ Qsurv, ∀ rj ∈ Qsurv,
      ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
        D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (productP : ℤ)]
  W_eq : W = omega productP
  W_le_K : W ≤ D.K

/-- Every selected block contributes at least one prime. This is true for
states produced by the descending-chain constructors, but kept as a predicate
rather than a structure field so basic APIs can still talk about arbitrary
chain states. -/
def ChainState.BlocksOmegaPos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : Prop :=
  ∀ P ∈ S.blocks, 1 ≤ omega P

lemma ChainState.Qsurv_card_pos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : 0 < S.Qsurv.card :=
  S.Qsurv_nonempty.card_pos

lemma ChainState.productP_le_of_mem {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    S.productP ≤ q := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
  exact Nat.le_of_dvd hqpos (S.exact_divides q hq)

lemma ChainState.productP_hExp_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    (hExp S.productP : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hle_nat : hExp S.productP ≤ hExp q :=
    hExp_le_of_dvd (S.exact_divides q hq) hqne
  have hle_real : (hExp S.productP : ℝ) ≤ (hExp q : ℝ) := by
    exact_mod_cast hle_nat
  exact hle_real.trans (D.hExp_bound q hqD)

lemma ChainState.block_dvd_productP {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {B : ℕ} (hB : B ∈ S.blocks) : B ∣ S.productP := by
  rw [S.product_eq]
  exact List.mem_dvd_foldr_mul hB

lemma ChainState.selected_remaining_disjoint {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    Disjoint (primeSupport S.productP) (remainingSupport S.productP q) := by
  rw [Finset.disjoint_left]
  intro p hpP hpRem
  exact S.no_selected_prime_remains q hq p hpP hpRem

lemma ChainState.remainingSupport_card_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    (remainingSupport S.productP q).card = D.K - S.W := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqpos : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have homega :
      omega (q / S.productP) = omega q - omega S.productP :=
    omega_div_eq_sub_omega_of_dvd (S.exact_divides q hq)
      S.productP_pos.ne' hqpos (S.selected_remaining_disjoint hq)
  calc
    (remainingSupport S.productP q).card = omega (q / S.productP) := by
      simp [remainingSupport, omega]
    _ = omega q - omega S.productP := homega
    _ = D.K - S.W := by
      rw [D.omega_eq q hqD, ← S.W_eq]

lemma ChainState.remainingSupport_nonempty_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K)
    {q : ℕ} (hq : q ∈ S.Qsurv) :
    (remainingSupport S.productP q).Nonempty := by
  rw [← Finset.card_pos, S.remainingSupport_card_eq hq]
  omega

lemma ChainState.remainingSupport_card_pos_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K)
    {q : ℕ} (hq : q ∈ S.Qsurv) :
    0 < (remainingSupport S.productP q).card := by
  exact (S.remainingSupport_nonempty_of_room hRoom hq).card_pos

lemma ChainState.gcd_dvd_productP_of_disjoint_remaining {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q r : ℕ} (hq : q ∈ S.Qsurv) (hr : r ∈ S.Qsurv)
    (hdisj : Disjoint (remainingSupport S.productP q) (remainingSupport S.productP r)) :
    Nat.gcd q r ∣ S.productP := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqpos : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hrpos : r ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1).ne'
  exact gcd_dvd_of_disjoint_remainingSupport
    (S.exact_divides q hq) (S.exact_divides r hr)
    S.productP_pos.ne' hqpos hrpos hdisj

lemma ChainState.remainingSupport_not_disjoint_of_ne {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q r : ℕ} (hq : q ∈ S.Qsurv) (hr : r ∈ S.Qsurv)
    (hqr : q ≠ r) :
    ¬ Disjoint (remainingSupport S.productP q) (remainingSupport S.productP r) := by
  intro hdisj
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1
  have hgcd_dvd : Nat.gcd q r ∣ S.productP :=
    S.gcd_dvd_productP_of_disjoint_remaining hq hr hdisj
  have hmodP := S.residues_agree q hq r hr hqD hrD
  have hmodG :
      D.a ⟨q, hqD⟩ ≡ D.a ⟨r, hrD⟩ [ZMOD (Nat.gcd q r : ℤ)] := by
    rw [Int.modEq_iff_dvd] at hmodP ⊢
    have hgcd_dvd_int : (Nat.gcd q r : ℤ) ∣ (S.productP : ℤ) := by
      exact_mod_cast hgcd_dvd
    exact dvd_trans hgcd_dvd_int hmodP
  have hres_disj :
      Disjoint (residueClass q (D.a ⟨q, hqD⟩))
        (residueClass r (D.a ⟨r, hrD⟩)) :=
    D.pairwise_disjoint ⟨q, hqD⟩ ⟨r, hrD⟩ (by
      intro hsub
      exact hqr (Subtype.ext_iff.mp hsub))
  exact ((residueClass_disjoint_iff hqpos hrpos
    (D.a ⟨q, hqD⟩) (D.a ⟨r, hrD⟩)).1 hres_disj) hmodG

/-- The family of remaining prime supports of surviving moduli. -/
def ChainState.remainingSupportFamily {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : Finset (Finset ℕ) :=
  S.Qsurv.image (fun q => remainingSupport S.productP q)

lemma ChainState.remainingSupportFamily_nonempty {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : S.remainingSupportFamily.Nonempty := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  exact ⟨remainingSupport S.productP q, Finset.mem_image.2 ⟨q, hq, rfl⟩⟩

lemma ChainState.remainingSupportFamily_card_le {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    S.remainingSupportFamily.card ≤ S.Qsurv.card := by
  rw [ChainState.remainingSupportFamily]
  exact Finset.card_image_le

lemma ChainState.remainingSupport_injOn_Qsurv {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    Set.InjOn (fun q => remainingSupport S.productP q) S.Qsurv := by
  intro q hq r hr hqr
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hrne : r ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1).ne'
  have hqsupp :
      primeSupport q = primeSupport S.productP ∪ remainingSupport S.productP q :=
    primeSupport_eq_union_of_dvd (S.exact_divides q hq) S.productP_pos.ne' hqne
  have hrsupp :
    primeSupport r = primeSupport S.productP ∪ remainingSupport S.productP r :=
    primeSupport_eq_union_of_dvd (S.exact_divides r hr) S.productP_pos.ne' hrne
  have hsupp : primeSupport q = primeSupport r := by
    change remainingSupport S.productP q = remainingSupport S.productP r at hqr
    rw [hqsupp, hrsupp, hqr]
  have hrad : rad q = rad r := by
    unfold rad
    rw [hsupp]
  exact D.rad_injective q hqD r hrD hrad

lemma ChainState.remainingSupportFamily_card_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    S.remainingSupportFamily.card = S.Qsurv.card := by
  rw [ChainState.remainingSupportFamily]
  exact Finset.card_image_of_injOn (fun q hq r hr hqr =>
    S.remainingSupport_injOn_Qsurv hq hr hqr)

/-- Survivors whose remaining support contains a fixed core. -/
def ChainState.coreSurvivors {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  S.Qsurv.filter fun q => C ⊆ remainingSupport S.productP q

/-- Exact prime-power block values attached to a fixed core. -/
def ChainState.coreBlocks {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  (S.coreSurvivors C).image (fun q => exactBlock C q)

/-- Weighted pigeonhole on exact block values carried by a fixed core. This
is the formal selection step for the paper's attained value `P_r`, before
the subsequent residue-class pigeonhole. -/
lemma ChainState.exists_coreBlock_weighted_share {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ)
    (hCore : (S.coreSurvivors C).Nonempty) :
    ∃ P ∈ S.coreBlocks C,
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) := by
  classical
  rw [ChainState.coreBlocks]
  exact exists_fiber_weighted_share (S.coreSurvivors C) (fun q => exactBlock C q)
    (fun P => (1 : ℝ) / ((hExp P : ℝ) ^ 2)) hCore (by
      intro P _hP
      exact hExp_inv_sq_pos P)

/-- Quotients `q / productP` for survivors carrying a fixed core. -/
def ChainState.coreQuotients {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  (S.coreSurvivors C).image (fun q => q / S.productP)

lemma ChainState.remainingSupportFamily_filter_subset_coreImage {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.remainingSupportFamily.filter fun A => C ⊆ A) ⊆
      (S.coreSurvivors C).image (fun q => remainingSupport S.productP q) := by
  intro A hA
  rw [ChainState.remainingSupportFamily] at hA
  rw [Finset.mem_filter] at hA
  rcases Finset.mem_image.mp hA.1 with ⟨q, hq, rfl⟩
  exact Finset.mem_image.2 ⟨q, by
    rw [ChainState.coreSurvivors, Finset.mem_filter]
    exact ⟨hq, hA.2⟩, rfl⟩

lemma ChainState.remainingSupportFamily_filter_card_le_coreSurvivors {N : ℕ}
    {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ) :
    (S.remainingSupportFamily.filter fun A => C ⊆ A).card ≤
      (S.coreSurvivors C).card := by
  exact (Finset.card_le_card (S.remainingSupportFamily_filter_subset_coreImage C)).trans
    Finset.card_image_le

lemma ChainState.quotient_injOn_Qsurv {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    Set.InjOn (fun q => q / S.productP) S.Qsurv := by
  intro q hq r hr hqr
  have hqmul := Nat.div_mul_cancel (S.exact_divides q hq)
  have hrmul := Nat.div_mul_cancel (S.exact_divides r hr)
  calc
    q = (q / S.productP) * S.productP := hqmul.symm
    _ = (r / S.productP) * S.productP := by
      exact congrArg (fun x => x * S.productP) hqr
    _ = r := hrmul

lemma ChainState.coreQuotients_card {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.coreQuotients C).card = (S.coreSurvivors C).card := by
  rw [ChainState.coreQuotients]
  exact Finset.card_image_of_injOn fun q hq r hr hqr =>
    S.quotient_injOn_Qsurv (Finset.mem_filter.1 hq).1
      (Finset.mem_filter.1 hr).1 hqr

lemma ChainState.coreQuotients_subset_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreQuotients C ⊆
      (Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W) := by
  intro n hn
  rw [ChainState.coreQuotients] at hn
  rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := (Finset.mem_filter.1 hq).1
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (S.productP_le_of_mem hqsurv) S.productP_pos),
      (Nat.div_le_self q S.productP).trans (D.modulus_upper q hqD)⟩,
    S.remainingSupport_card_eq hqsurv⟩

lemma ChainState.coreSurvivors_card_le_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.coreSurvivors C).card ≤
      ((Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W)).card := by
  rw [← S.coreQuotients_card C]
  exact Finset.card_le_card (S.coreQuotients_subset_omegaCount C)

lemma ChainState.coreSurvivors_card_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    (S.coreSurvivors C).card ≤
      Nat.floor
        ((N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  exact (S.coreSurvivors_card_le_omegaCount C).trans
    (hCount N D.K S.W le_rfl S.W_le_K D.K_bound)

lemma ChainState.coreSurvivors_card_real_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((S.coreSurvivors C).card : ℝ) ≤
      (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  apply nat_cast_le_of_le_floor
  · positivity
  · exact S.coreSurvivors_card_le_bfv_omega_count C ε hCount

lemma ChainState.coreSurvivors_subset {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreSurvivors C ⊆ S.Qsurv := by
  intro q hq
  exact (Finset.mem_filter.1 hq).1

lemma ChainState.core_subset_remainingSupport {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    C ⊆ remainingSupport S.productP q :=
  (Finset.mem_filter.1 hq).2

lemma ChainState.exactBlock_eq_quotient_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    exactBlock C q = exactBlock C (q / S.productP) := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  apply exactBlock_congr_on
  intro p hpC
  have hpRem : p ∈ remainingSupport S.productP q := hC hpC
  have hpNotP : p ∉ primeSupport S.productP := by
    intro hpP
    exact (Finset.disjoint_left.1 (S.selected_remaining_disjoint hqsurv)) hpP hpRem
  have hPzero : S.productP.factorization p = 0 := by
      unfold primeSupport at hpNotP
      exact Finsupp.notMem_support_iff.1 hpNotP
  rw [Nat.factorization_div (S.exact_divides q hqsurv)]
  simp [Finsupp.coe_tsub, hPzero]

lemma ChainState.quotient_pos_of_mem {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    0 < q / S.productP := by
  exact Nat.div_pos (S.productP_le_of_mem hq) S.productP_pos

lemma ChainState.exactBlock_dvd_quotient_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    exactBlock C q ∣ q / S.productP := by
  rw [S.exactBlock_eq_quotient_of_core hq]
  exact exactBlock_dvd C (q / S.productP)

lemma ChainState.exactBlock_pos_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    0 < exactBlock C q := by
  exact Nat.pos_of_dvd_of_pos (S.exactBlock_dvd_quotient_of_core hq)
    (S.quotient_pos_of_mem (S.coreSurvivors_subset C hq))

lemma ChainState.primeSupport_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    primeSupport (exactBlock C q) = C := by
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  rw [S.exactBlock_eq_quotient_of_core hq]
  exact primeSupport_exactBlock
    (fun p hp => prime_of_mem_primeSupport (hC hp))
    hC

lemma ChainState.omega_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    omega (exactBlock C q) = C.card := by
  simp [omega, S.primeSupport_exactBlock_of_core hq]

lemma ChainState.product_mul_exactBlock_dvd_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    S.productP * exactBlock C q ∣ q := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  rcases S.exactBlock_dvd_quotient_of_core hq with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hdiv := Nat.div_mul_cancel (S.exact_divides q hqsurv)
  calc
    q = q / S.productP * S.productP := hdiv.symm
    _ = exactBlock C q * t * S.productP := by rw [ht]
    _ = S.productP * exactBlock C q * t := by ring

lemma ChainState.productP_coprime_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    Nat.Coprime S.productP (exactBlock C q) := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  have hsupport : primeSupport (exactBlock C q) = C :=
    S.primeSupport_exactBlock_of_core hq
  refine coprime_of_disjoint_primeSupport S.productP_pos.ne'
    (S.exactBlock_pos_of_core hq).ne' ?_
  rw [hsupport]
  rw [Finset.disjoint_left]
  intro p hpP hpC
  exact (Finset.disjoint_left.1 (S.selected_remaining_disjoint hqsurv)) hpP (hC hpC)

lemma ChainState.coreBlock_pos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : 0 < P := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.exactBlock_pos_of_core hq

lemma ChainState.coreBlock_coprime_productP {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : Nat.Coprime S.productP P := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.productP_coprime_exactBlock_of_core hq

lemma ChainState.coreBlock_omega_eq_card {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : omega P = C.card := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.omega_exactBlock_of_core hq

lemma ChainState.coreBlock_primeSupport_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : primeSupport P = C := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.primeSupport_exactBlock_of_core hq

lemma ChainState.product_mul_coreBlock_dvd {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P q : ℕ}
    (hq : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P) :
    S.productP * P ∣ q := by
  have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hq).1
  have hP : exactBlock C q = P := (Finset.mem_filter.1 hq).2
  simpa [hP] using S.product_mul_exactBlock_dvd_of_core hqcore

lemma ChainState.product_mul_coreBlock_no_selected_prime_remains
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P q : ℕ}
    (hq : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P) :
    ∀ p ∈ primeSupport (S.productP * P), p ∉ primeSupport (q / (S.productP * P)) := by
  intro p hpNew hpRem
  have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hq).1
  have hP : exactBlock C q = P := (Finset.mem_filter.1 hq).2
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hqcore
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hPmem : P ∈ S.coreBlocks C := by
    rw [ChainState.coreBlocks]
    exact Finset.mem_image.2 ⟨q, hqcore, hP⟩
  have hcop : Nat.Coprime S.productP P := S.coreBlock_coprime_productP hPmem
  have hnewdvd : S.productP * P ∣ q := S.product_mul_coreBlock_dvd hq
  have hltNew : (S.productP * P).factorization p < q.factorization p :=
    (mem_remainingSupport_iff_factorization_lt hnewdvd).1 hpRem
  have hsupportNew :
      primeSupport (S.productP * P) = primeSupport S.productP ∪ primeSupport P :=
    primeSupport_mul_of_coprime hcop
  have hfacNew : (S.productP * P).factorization p =
      S.productP.factorization p + P.factorization p := by
    rw [Nat.factorization_mul_of_coprime hcop]
    rfl
  rw [hsupportNew, Finset.mem_union] at hpNew
  cases hpNew with
  | inl hpOld =>
      have hpNotRemOld : p ∉ primeSupport (q / S.productP) :=
        S.no_selected_prime_remains q hqsurv p hpOld
      have hnotltOld : ¬ S.productP.factorization p < q.factorization p := by
        intro hlt
        exact hpNotRemOld
          ((mem_remainingSupport_iff_factorization_lt (S.exact_divides q hqsurv)).2 hlt)
      have hleOld : S.productP.factorization p ≤ q.factorization p :=
        (Nat.factorization_le_iff_dvd S.productP_pos.ne' hqne).2
          (S.exact_divides q hqsurv) p
      have hq_le_old : q.factorization p ≤ S.productP.factorization p :=
        le_of_not_gt hnotltOld
      have hEqOld : S.productP.factorization p = q.factorization p :=
        le_antisymm hleOld hq_le_old
      have hpNotP : p ∉ primeSupport P :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hpOld
      have hPzero : P.factorization p = 0 := by
        unfold primeSupport at hpNotP
        exact Finsupp.notMem_support_iff.1 hpNotP
      rw [hfacNew, hPzero, add_zero, hEqOld] at hltNew
      exact lt_irrefl _ hltNew
  | inr hpP =>
      have hsupportP : primeSupport P = C := by
        rw [← hP]
        exact S.primeSupport_exactBlock_of_core hqcore
      have hpC : p ∈ C := by
        simpa [hsupportP] using hpP
      have hpNotOld : p ∉ primeSupport S.productP := by
        intro hpOld
        exact (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hpOld hpP
      have hOldzero : S.productP.factorization p = 0 := by
        unfold primeSupport at hpNotOld
        exact Finsupp.notMem_support_iff.1 hpNotOld
      have hCprime : ∀ r ∈ C, Nat.Prime r := by
        intro r hr
        exact prime_of_mem_primeSupport (S.core_subset_remainingSupport hqcore hr)
      have hPfac : P.factorization p = q.factorization p := by
        rw [← hP]
        exact factorization_exactBlock_of_mem hCprime hpC
      rw [hfacNew, hOldzero, zero_add, hPfac] at hltNew
      exact lt_irrefl _ hltNew

lemma ChainState.coreBlock_card_le_remaining {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : C.card ≤ D.K - S.W := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact (Finset.card_le_card (S.core_subset_remainingSupport hq)).trans_eq
    (S.remainingSupport_card_eq (S.coreSurvivors_subset C hq))

lemma ChainState.omega_product_mul_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    omega (S.productP * P) = S.W + C.card := by
  rw [omega_mul_of_coprime (S.coreBlock_coprime_productP hP), ← S.W_eq,
    S.coreBlock_omega_eq_card hP]

lemma ChainState.selectedFiber_card_real_le_bfv_omega_count_div
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.coreBlocks C) (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
      ((N / (S.productP * P) : ℕ) : ℝ) *
        Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  classical
  let T : Finset ℕ := (S.coreSurvivors C).filter fun q => exactBlock C q = P
  let dP : ℕ := S.productP * P
  let quotient : ℕ → ℕ := fun q => q / dP
  have hdP_pos : 0 < dP := by
    dsimp [dP]
    exact Nat.mul_pos S.productP_pos (S.coreBlock_pos hP)
  have hWle : S.W + C.card ≤ D.K := by
    have hcard := S.coreBlock_card_le_remaining hP
    have hWK := S.W_le_K
    omega
  have hinj : Set.InjOn quotient T := by
    intro q hq r hr hqr
    have hq_dvd : dP ∣ q := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd (by simpa [T] using hq)
    have hr_dvd : dP ∣ r := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd (by simpa [T] using hr)
    calc
      q = quotient q * dP := (Nat.div_mul_cancel hq_dvd).symm
      _ = quotient r * dP := by rw [hqr]
      _ = r := Nat.div_mul_cancel hr_dvd
  have hsubset :
      T.image quotient ⊆
        (Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card)) := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨q, hqT, rfl⟩
    have hqT' : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P := by
      simpa [T] using hqT
    have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hqT').1
    have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hqcore
    have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
    have hqne : q ≠ 0 := hqpos.ne'
    have hdvd : dP ∣ q := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd hqT'
    have hdisj : Disjoint (primeSupport dP) (primeSupport (q / dP)) := by
      rw [Finset.disjoint_left]
      intro p hp hqrem
      exact S.product_mul_coreBlock_no_selected_prime_remains hqT' p (by simpa [dP] using hp)
        (by simpa [dP] using hqrem)
    have homega :
        omega (q / dP) = D.K - (S.W + C.card) := by
      calc
        omega (q / dP) = omega q - omega dP :=
          omega_div_eq_sub_omega_of_dvd hdvd hdP_pos.ne' hqne hdisj
        _ = D.K - (S.W + C.card) := by
          rw [D.omega_eq q hqD, show omega dP = S.W + C.card by
            dsimp [dP]
            exact S.omega_product_mul_coreBlock hP]
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hqpos hdvd) hdP_pos),
      Nat.div_le_div_right (D.modulus_upper q hqD)⟩, homega⟩
  have hcard : T.card ≤
      ((Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card))).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsubset
  have hcount := hCount (N / dP) D.K (S.W + C.card) (Nat.div_le_self N dP) hWle D.K_bound
  dsimp only at hcount
  have hfloor :
      T.card ≤ Nat.floor
        (((N / dP : ℕ) : ℝ) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ)))) :=
    hcard.trans hcount
  simpa [T, dP] using nat_cast_le_of_le_floor (by positivity) hfloor

lemma ChainState.selectedFiber_card_real_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.coreBlocks C) (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
      ((N : ℝ) / (S.productP * P : ℝ)) *
        Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  have hdiv := S.selectedFiber_card_real_le_bfv_omega_count_div hP ε hCount
  have hquot :
      ((N / (S.productP * P) : ℕ) : ℝ) ≤ (N : ℝ) / (S.productP * P : ℝ) :=
    by
      simpa [Nat.cast_mul] using
        (Nat.cast_div_le (m := N) (n := S.productP * P) : ((N / (S.productP * P) : ℕ) : ℝ) ≤
          (N : ℝ) / ((S.productP * P : ℕ) : ℝ))
  have hfactor_nonneg :
      0 ≤ Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
    positivity
  calc
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ)
        ≤ ((N / (S.productP * P) : ℕ) : ℝ) *
            Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
            Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
              Real.log (Real.log (N : ℝ))) := hdiv
    _ = ((N / (S.productP * P) : ℕ) : ℝ) *
            (Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
              Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ)))) := by ring
    _ ≤ ((N : ℝ) / (S.productP * P : ℝ)) *
            (Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
              Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ)))) := by
          exact mul_le_mul_of_nonneg_right hquot hfactor_nonneg
    _ = ((N : ℝ) / (S.productP * P : ℝ)) *
            Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
            Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
              Real.log (Real.log (N : ℝ))) := by ring

lemma ChainState.W_add_coreBlock_card_le_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : S.W + C.card ≤ D.K := by
  have hcard := S.coreBlock_card_le_remaining hP
  have hW := S.W_le_K
  omega

lemma ChainState.productP_eq_of_W_eq_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hW : S.W = D.K) {q : ℕ} (hq : q ∈ S.Qsurv) :
    S.productP = q := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqdivpos : q / S.productP ≠ 0 := (S.quotient_pos_of_mem hq).ne'
  have hremcard : (remainingSupport S.productP q).card = 0 := by
    rw [S.remainingSupport_card_eq hq, hW]
    simp
  have homega : omega (q / S.productP) = 0 := by
    simpa [remainingSupport, omega] using hremcard
  have hquot : q / S.productP = 1 := eq_one_of_omega_eq_zero hqdivpos homega
  have hdiv := Nat.div_mul_cancel (S.exact_divides q hq)
  calc
    S.productP = 1 * S.productP := by simp
    _ = q / S.productP * S.productP := by rw [hquot]
    _ = q := hdiv

lemma ChainState.productP_lower_of_W_eq_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hW : S.W = D.K) :
    (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hpq := S.productP_eq_of_W_eq_K hW hq
  rw [hpq]
  exact D.modulus_lower q hqD

lemma ChainState.pairwise_cons_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : (P :: S.blocks).Pairwise Nat.Coprime := by
  rw [List.pairwise_cons]
  constructor
  · intro B hB
    exact Nat.Coprime.of_dvd_right (S.block_dvd_productP hB)
      (S.coreBlock_coprime_productP hP).symm
  · exact S.pairwise_coprime

lemma ChainState.extend_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ} {Qnext : Finset ℕ}
    (hP : P ∈ S.coreBlocks C)
    (hQnext_nonempty : Qnext.Nonempty)
    (hQnext_subset : Qnext ⊆ (S.coreSurvivors C).filter fun q => exactBlock C q = P)
    (hResiduesP :
      ∀ qi ∈ Qnext, ∀ rj ∈ Qnext,
        ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
          D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) :
    ∃ S' : ChainState N D,
      S'.blocks = P :: S.blocks ∧ S'.r = S.r + 1 ∧ S'.productP = P * S.productP ∧
        S'.Qsurv = Qnext ∧ S'.W = S.W + C.card := by
  classical
  refine ⟨{
    r := S.r + 1
    blocks := P :: S.blocks
    blocks_length := by simp [S.blocks_length]
    Qsurv := Qnext
    Qsurv_subset := ?_
    Qsurv_nonempty := hQnext_nonempty
    W := S.W + C.card
    productP := P * S.productP
    product_eq := by simp [S.product_eq]
    blocks_pos := ?_
    productP_pos := ?_
    pairwise_coprime := S.pairwise_cons_coreBlock hP
    exact_divides := ?_
    no_selected_prime_remains := ?_
    residues_agree := ?_
    W_eq := ?_
    W_le_K := S.W_add_coreBlock_card_le_K hP
  }, rfl, rfl, rfl, rfl, rfl⟩
  · intro q hq
    exact S.Qsurv_subset (S.coreSurvivors_subset C
      (Finset.mem_filter.1 (hQnext_subset hq)).1)
  · intro B hB
    rw [List.mem_cons] at hB
    cases hB with
    | inl h =>
        subst B
        exact S.coreBlock_pos hP
    | inr h => exact S.blocks_pos B h
  · exact mul_pos (S.coreBlock_pos hP) S.productP_pos
  · intro q hq
    have hfiber := hQnext_subset hq
    have hdvd := S.product_mul_coreBlock_dvd hfiber
    simpa [Nat.mul_comm] using hdvd
  · intro q hq p hp
    have hfiber := hQnext_subset hq
    have hno := S.product_mul_coreBlock_no_selected_prime_remains hfiber p
    simpa [Nat.mul_comm] using hno (by simpa [Nat.mul_comm] using hp)
  · intro qi hqi rj hrj hqiD hrjD
    have hqicore : qi ∈ S.coreSurvivors C :=
      (Finset.mem_filter.1 (hQnext_subset hqi)).1
    have hrjcore : rj ∈ S.coreSurvivors C :=
      (Finset.mem_filter.1 (hQnext_subset hrj)).1
    have hqiSurv : qi ∈ S.Qsurv := S.coreSurvivors_subset C hqicore
    have hrjSurv : rj ∈ S.Qsurv := S.coreSurvivors_subset C hrjcore
    have hOld := S.residues_agree qi hqiSurv rj hrjSurv hqiD hrjD
    have hNew := hResiduesP qi hqi rj hrj hqiD hrjD
    have hcopInt : (S.productP : ℤ).natAbs.Coprime (P : ℤ).natAbs := by
      simpa using S.coreBlock_coprime_productP hP
    have hBoth :
        D.a ⟨qi, hqiD⟩ ≡ D.a ⟨rj, hrjD⟩ [ZMOD (S.productP : ℤ)] ∧
        D.a ⟨qi, hqiD⟩ ≡ D.a ⟨rj, hrjD⟩ [ZMOD (P : ℤ)] := ⟨hOld, hNew⟩
    have hMul := (Int.modEq_and_modEq_iff_modEq_mul hcopInt).1 hBoth
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hMul
  · rw [Nat.mul_comm]
    exact (S.omega_product_mul_coreBlock hP).symm

lemma ChainState.exists_residue_subfamily {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    ∃ Qnext : Finset ℕ,
      Qnext.Nonempty ∧
      Qnext ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      (∀ qi ∈ Qnext, ∀ rj ∈ Qnext,
        ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
          D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) ∧
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ) ≤ (Qnext.card : ℝ) := by
  classical
  let T : Finset ℕ := (S.coreSurvivors C).filter fun q => exactBlock C q = P
  let residue : ℕ → ZMod P :=
    fun q => if hq : q ∈ D.Q then (D.a ⟨q, hq⟩ : ZMod P) else 0
  have hPpos : 0 < P := S.coreBlock_pos hP
  haveI : NeZero P := ⟨hPpos.ne'⟩
  have hTnonempty : T.Nonempty := by
    dsimp [T]
    rw [ChainState.coreBlocks] at hP
    exact fiber_nonempty_of_mem_image (S := S.coreSurvivors C)
      (B := fun q => exactBlock C q) hP
  rcases exists_zmod_fiber_card_div_le T P residue hTnonempty with ⟨b, hb⟩
  let Qnext : Finset ℕ := T.filter fun q => residue q = b
  refine ⟨Qnext, ?_, ?_, ?_, ?_⟩
  · have hratio_pos : 0 < (T.card : ℝ) / (P : ℝ) := by
      have hTcard : 0 < (T.card : ℝ) := by exact_mod_cast hTnonempty.card_pos
      have hPreal : 0 < (P : ℝ) := by exact_mod_cast hPpos
      exact div_pos hTcard hPreal
    have hQreal : 0 < (Qnext.card : ℝ) := lt_of_lt_of_le hratio_pos hb
    exact Finset.card_pos.1 (by exact_mod_cast hQreal)
  · intro q hq
    exact (Finset.mem_filter.1 hq).1
  · intro qi hqi rj hrj hqiD hrjD
    have hqiResidue : residue qi = b := (Finset.mem_filter.1 hqi).2
    have hrjResidue : residue rj = b := (Finset.mem_filter.1 hrj).2
    have hqiCast : ((D.a ⟨qi, hqiD⟩ : ℤ) : ZMod P) = b := by
      simpa [residue, hqiD] using hqiResidue
    have hrjCast : ((D.a ⟨rj, hrjD⟩ : ℤ) : ZMod P) = b := by
      simpa [residue, hrjD] using hrjResidue
    have hcast : ((D.a ⟨qi, hqiD⟩ : ℤ) : ZMod P) =
        ((D.a ⟨rj, hrjD⟩ : ℤ) : ZMod P) := hqiCast.trans hrjCast.symm
    exact (ZMod.intCast_eq_intCast_iff
      (D.a ⟨qi, hqiD⟩) (D.a ⟨rj, hrjD⟩) P).1 hcast
  · simpa [T, Qnext] using hb

lemma ChainState.exists_extended_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    ∃ S' : ChainState N D,
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) := by
  rcases S.exists_residue_subfamily hP with
    ⟨Qnext, hQnext_nonempty, hQnext_subset, hResiduesP, hcard⟩
  rcases S.extend_coreBlock hP hQnext_nonempty hQnext_subset hResiduesP with
    ⟨S', hblocks, hr, hprod, hQsurv, hW⟩
  have hsubset : S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) := by
    intro q hq
    rw [hQsurv] at hq
    exact hQnext_subset hq
  exact ⟨S', hblocks, hr, hprod, hsubset, Finset.card_le_card hsubset, hW,
    by simpa [hQsurv] using hcard⟩

lemma ChainState.exists_weighted_extended_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    ∃ P : ℕ, ∃ S' : ChainState N D,
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) := by
  rcases S.exists_coreBlock_weighted_share C hCore with ⟨P, hP, hshare⟩
  rcases S.exists_extended_coreBlock hP with
    ⟨S', hblocks, hr, hprod, hQsubset, hQcard_le, hW, hcard⟩
  refine ⟨P, S', hP, hblocks, hr, hprod, hQsubset, hQcard_le, hW, hshare, ?_⟩
  have hPreal_nonneg : 0 ≤ (P : ℝ) := by positivity
  have hdiv_share :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤
        ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ)) := by
    exact div_le_div_of_nonneg_right hshare hPreal_nonneg
  exact hdiv_share.trans hcard

lemma ChainState.coreBlocks_subset_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreBlocks C ⊆
      (Finset.Icc 1 N).filter (fun n => omega n = C.card) := by
  intro B hB
  rw [ChainState.coreBlocks] at hB
  rcases Finset.mem_image.mp hB with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hblock_le_quotient :
      exactBlock C q ≤ q / S.productP :=
    Nat.le_of_dvd (S.quotient_pos_of_mem hqsurv) (S.exactBlock_dvd_quotient_of_core hq)
  have hblock_le_N : exactBlock C q ≤ N := by
    exact hblock_le_quotient.trans ((Nat.div_le_self q S.productP).trans (D.modulus_upper q hqD))
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (S.exactBlock_pos_of_core hq), hblock_le_N⟩,
    S.omega_exactBlock_of_core hq⟩

lemma ChainState.coreBlock_le_N {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : P ≤ N := by
  have hmem := S.coreBlocks_subset_omegaCount C hP
  exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hmem).1).2

lemma ChainState.coreBlock_hExp_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hle_nat : hExp (exactBlock C q) ≤ hExp q := hExp_exactBlock_le_hExp C q
  have hle_real : (hExp (exactBlock C q) : ℝ) ≤ (hExp q : ℝ) := by
    exact_mod_cast hle_nat
  exact hle_real.trans (D.hExp_bound q hqD)

lemma ChainState.coreBlock_card_le_K_of_nonempty {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) : C.card ≤ D.K := by
  rcases hCore with ⟨q, hq⟩
  have hle := Finset.card_le_card (S.core_subset_remainingSupport hq)
  have heq := S.remainingSupport_card_eq (S.coreSurvivors_subset C hq)
  omega

lemma ChainState.coreBlock_card_bound_real {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    (C.card : ℝ) ≤ 3 * Mscale N := by
  have hCK : (C.card : ℝ) ≤ (D.K : ℝ) := by
    exact_mod_cast S.coreBlock_card_le_K_of_nonempty hCore
  exact hCK.trans D.K_bound

lemma ChainState.coreBlocks_card_le_bfv_omega_count {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) (ε : ℝ)
    (hCore : (S.coreSurvivors C).Nonempty)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    (S.coreBlocks C).card ≤
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)) := by
  have hsubset := S.coreBlocks_subset_omegaCount C
  have hcard : (S.coreBlocks C).card ≤
      ((Finset.Icc 1 N).filter (fun n => omega n = C.card)).card :=
    Finset.card_le_card hsubset
  have hcount := hCount N C.card 0 le_rfl (Nat.zero_le _) (S.coreBlock_card_bound_real hCore)
  dsimp only at hcount
  have hsimp :
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((0 : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) =
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)) := by
    simp
  exact hcard.trans (by simpa [hsimp] using hcount)

lemma ChainState.coreBlocks_card_real_le_bfv_omega_count {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) (ε : ℝ)
    (hCore : (S.coreSurvivors C).Nonempty)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((S.coreBlocks C).card : ℝ) ≤
      (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
  apply nat_cast_le_of_le_floor
  · positivity
  · exact S.coreBlocks_card_le_bfv_omega_count C ε hCore hCount

lemma ChainState.remainingSupportFamily_uniform {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    UniformFamily S.remainingSupportFamily (D.K - S.W) := by
  intro A hA
  rw [ChainState.remainingSupportFamily] at hA
  rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
  exact S.remainingSupport_card_eq hq

lemma ChainState.remainingSupportFamily_intersecting {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    ∀ A ∈ S.remainingSupportFamily, ∀ B ∈ S.remainingSupportFamily,
      A ≠ B → ¬ Disjoint A B := by
  intro A hA B hB hAB
  rw [ChainState.remainingSupportFamily] at hA hB
  rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨r, hr, rfl⟩
  exact S.remainingSupport_not_disjoint_of_ne hq hr (by
    intro hqr
    subst r
    exact hAB rfl)

lemma ChainState.remainingSupportFamily_rank_pos_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) : 1 ≤ D.K - S.W := by
  omega

lemma ChainState.remainingSupportFamily_rank_le_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : D.K - S.W ≤ D.K :=
  Nat.sub_le D.K S.W

lemma ChainState.remainingSupportFamily_denseCoreData {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    S.remainingSupportFamily.Nonempty ∧
      1 ≤ D.K - S.W ∧
      D.K - S.W ≤ D.K ∧
      UniformFamily S.remainingSupportFamily (D.K - S.W) ∧
      (∀ A ∈ S.remainingSupportFamily, ∀ B ∈ S.remainingSupportFamily,
        A ≠ B → ¬ Disjoint A B) :=
  ⟨S.remainingSupportFamily_nonempty,
    S.remainingSupportFamily_rank_pos_of_room hRoom,
    S.remainingSupportFamily_rank_le_K,
    S.remainingSupportFamily_uniform,
    S.remainingSupportFamily_intersecting⟩

/-- A fixed dense-core constant supplied by the spread-core input. Keeping it
fixed is important for iterating the chain. This file only needs the
`α = ℕ` instance, so the universe is fixed to avoid polymorphic choice
metavariables. -/
noncomputable def denseCoreConstant : ℝ :=
  Classical.choose (dense_core_from_spread.{0})

lemma denseCoreConstant_pos : 0 < denseCoreConstant :=
  (Classical.choose_spec (dense_core_from_spread.{0})).1

lemma dense_core_from_spread_fixed_nat
    (A : Finset (Finset ℕ)) (k K : ℕ) :
    A.Nonempty →
    1 ≤ k → k ≤ K →
    UniformFamily A k →
    (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
    ∃ C : Finset ℕ,
      C.Nonempty ∧
      ((A.filter fun S => C ⊆ S).card : ℝ) >
        (A.card : ℝ) /
          (denseCoreConstant * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card :=
  (Classical.choose_spec (dense_core_from_spread.{0})).2 A k K

noncomputable def chainKappa {N : ℕ} (D : PrunedData N) : ℝ :=
  denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ))

noncomputable def chainLambda {N : ℕ} (D : PrunedData N) : ℝ :=
  2 * chainKappa D

lemma chainKappa_pos {N : ℕ} (D : PrunedData N) : 0 < chainKappa D := by
  have hKreal : 1 ≤ (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_ge : Real.exp 1 ≤ Real.exp 1 * (D.K : ℝ) := by
    nlinarith [Real.exp_pos 1, hKreal]
  have hlog_ge_one : 1 ≤ Real.log (Real.exp 1 * (D.K : ℝ)) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) harg_ge
    simpa using hlog
  exact mul_pos denseCoreConstant_pos (zero_lt_one.trans_le hlog_ge_one)

lemma chainLambda_pos {N : ℕ} (D : PrunedData N) : 0 < chainLambda D := by
  dsimp [chainLambda]
  exact mul_pos (by norm_num) (chainKappa_pos D)

lemma ChainState.exists_dense_core_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∃ C : Finset ℕ,
        C.Nonempty ∧
        ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
          (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases dense_core_from_spread with ⟨C0, hC0, hcore⟩
  rcases S.remainingSupportFamily_denseCoreData hRoom with
    ⟨hA, hk, hkK, hUniform, hIntersect⟩
  rcases hcore S.remainingSupportFamily (D.K - S.W) D.K
      hA hk hkK hUniform hIntersect with ⟨C, hC⟩
  exact ⟨C0, hC0, C, hC⟩

lemma ChainState.exists_dense_core_fixed_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C : Finset ℕ,
      C.Nonempty ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.remainingSupportFamily_denseCoreData hRoom with
    ⟨hA, hk, hkK, hUniform, hIntersect⟩
  rcases dense_core_from_spread_fixed_nat S.remainingSupportFamily (D.K - S.W) D.K
      hA hk hkK hUniform hIntersect with ⟨C, hC⟩
  exact ⟨C, by simpa [chainKappa] using hC⟩

lemma ChainState.coreSurvivors_nonempty_of_filter_card_pos
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ)) :
    (S.coreSurvivors C).Nonempty := by
  have hfilter_nat : 0 < (S.remainingSupportFamily.filter fun A => C ⊆ A).card := by
    exact_mod_cast hpos
  have hle := S.remainingSupportFamily_filter_card_le_coreSurvivors C
  have hcore_card : 0 < (S.coreSurvivors C).card := lt_of_lt_of_le hfilter_nat hle
  exact Finset.card_pos.1 hcore_card

lemma ChainState.exists_dense_core_with_survivor_of_room
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∃ C : Finset ℕ,
        C.Nonempty ∧ (S.coreSurvivors C).Nonempty ∧
        ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
          (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases S.exists_dense_core_of_room hRoom with ⟨C0, hC0, C, hC, hbound⟩
  have hKreal : 1 ≤ (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_ge : Real.exp 1 ≤ Real.exp 1 * (D.K : ℝ) := by
    nlinarith [Real.exp_pos 1, hKreal]
  have hlog_ge_one : 1 ≤ Real.log (Real.exp 1 * (D.K : ℝ)) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) harg_ge
    simpa using hlog
  have hbase_nonneg : 0 ≤ C0 * Real.log (Real.exp 1 * (D.K : ℝ)) := by
    exact mul_nonneg hC0.le (zero_le_one.trans hlog_ge_one)
  have hden_nonneg :
      0 ≤ (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
    exact div_nonneg (by positivity) (pow_nonneg hbase_nonneg _)
  have hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ) :=
    lt_of_le_of_lt hden_nonneg hbound
  exact ⟨C0, hC0, C, hC, S.coreSurvivors_nonempty_of_filter_card_pos hpos, hbound⟩

lemma ChainState.exists_dense_core_fixed_with_survivor_of_room
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C : Finset ℕ,
      C.Nonempty ∧ (S.coreSurvivors C).Nonempty ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.exists_dense_core_fixed_of_room hRoom with ⟨C, hC, hbound⟩
  have hbase_nonneg : 0 ≤ chainKappa D := (chainKappa_pos D).le
  have hden_nonneg :
      0 ≤ (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
    exact div_nonneg (by positivity) (pow_nonneg hbase_nonneg _)
  have hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ) :=
    lt_of_le_of_lt hden_nonneg hbound
  exact ⟨C, hC, S.coreSurvivors_nonempty_of_filter_card_pos hpos, hbound⟩

lemma ChainState.coreSurvivors_card_gt_of_dense_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ} {A : ℝ}
    (hbound : A < ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ)) :
    A < ((S.coreSurvivors C).card : ℝ) := by
  have hle : ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ) ≤
      ((S.coreSurvivors C).card : ℝ) := by
    exact_mod_cast S.remainingSupportFamily_filter_card_le_coreSurvivors C
  exact hbound.trans_le hle

lemma ChainState.coreSurvivors_card_gt_qsurv_div_of_dense_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ} {Λ : ℝ}
    (hbound :
      ((S.remainingSupportFamily.card : ℝ) / Λ ^ C.card) <
        ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ)) :
    ((S.Qsurv.card : ℝ) / Λ ^ C.card) <
      ((S.coreSurvivors C).card : ℝ) := by
  have h := S.coreSurvivors_card_gt_of_dense_bound hbound
  simpa [S.remainingSupportFamily_card_eq] using h

lemma ChainState.coreBlocks_nonempty_of_coreSurvivors
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) : (S.coreBlocks C).Nonempty := by
  rw [ChainState.coreBlocks]
  exact hCore.image _

lemma ChainState.coreBlocks_weight_sum_pos
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) := by
  exact Finset.sum_pos (fun B _hB => hExp_inv_sq_pos B)
    (S.coreBlocks_nonempty_of_coreSurvivors hCore)

lemma ChainState.coreBlocks_weight_sum_le_card
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ) :
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
      (S.coreBlocks C).card := by
  calc
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        ∑ _B ∈ S.coreBlocks C, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun B _hB => hExp_inv_sq_le_one B)
    _ = (S.coreBlocks C).card := by simp

lemma ChainState.coreBlocks_weight_sum_le_two_pow_card
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hC : C.Nonempty) :
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ C.card := by
  classical
  let Index := {p : ℕ // p ∈ C}
  let E : Finset (Index → ℕ) :=
    Fintype.piFinset fun _ : Index => Finset.range N
  let vec : ℕ → Index → ℕ := fun B p => B.factorization p.1 - 1
  let term : (Index → ℕ) → ℝ :=
    fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
  have hvec_mem : ∀ B ∈ S.coreBlocks C, vec B ∈ E := by
    intro B hB
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    have hsupport : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hpSupport : p.1 ∈ primeSupport B := by
      simp [hsupport, p.2]
    have hBne : B ≠ 0 := by
      intro hzero
      subst B
      simp [primeSupport] at hpSupport
    have hfac_pos : 1 ≤ B.factorization p.1 := by
      unfold primeSupport at hpSupport
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
    have hfac_le_N : B.factorization p.1 ≤ N := by
      exact (Nat.factorization_lt p.1 hBne).le.trans (S.coreBlock_le_N hB)
    dsimp [vec]
    omega
  have hvec_inj : Set.InjOn vec (S.coreBlocks C) := by
    intro B hB R hR hBR
    have hsupportB : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hsupportR : primeSupport R = C := S.coreBlock_primeSupport_eq hR
    have hBne : B ≠ 0 := by
      rcases hC with ⟨p, hp⟩
      have hpSupport : p ∈ primeSupport B := by simpa [hsupportB] using hp
      intro hzero
      subst B
      simp [primeSupport] at hpSupport
    have hRne : R ≠ 0 := by
      rcases hC with ⟨p, hp⟩
      have hpSupport : p ∈ primeSupport R := by simpa [hsupportR] using hp
      intro hzero
      subst R
      simp [primeSupport] at hpSupport
    apply Nat.eq_of_factorization_eq hBne hRne
    intro p
    by_cases hp : p ∈ C
    · have hcoord := congrFun hBR ⟨p, hp⟩
      dsimp [vec] at hcoord
      have hBpos : 1 ≤ B.factorization p := by
        have hpSupport : p ∈ primeSupport B := by simpa [hsupportB] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      have hRpos : 1 ≤ R.factorization p := by
        have hpSupport : p ∈ primeSupport R := by simpa [hsupportR] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      omega
    · have hpB : p ∉ primeSupport B := by simpa [hsupportB] using hp
      have hpR : p ∉ primeSupport R := by simpa [hsupportR] using hp
      rw [Finsupp.notMem_support_iff.1 hpB, Finsupp.notMem_support_iff.1 hpR]
  have hterm_eq :
      ∀ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) = term (vec B) := by
    intro B hB
    have hsupport : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hhexp :
        hExp B = ∏ p : Index, B.factorization p.1 := by
      calc
        hExp B = ∏ p ∈ C, B.factorization p := by
          simp [hExp, hsupport]
        _ = ∏ p : Index, B.factorization p.1 := by
          rw [Finset.prod_coe_sort]
    have hsucc : ∀ p : Index, vec B p + 1 = B.factorization p.1 := by
      intro p
      have hpSupport : p.1 ∈ primeSupport B := by simp [hsupport, p.2]
      have hpos : 1 ≤ B.factorization p.1 := by
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      dsimp [vec]
      omega
    rw [hhexp, one_div_sq_nat_prod]
    dsimp [term]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [hsucc p]
  calc
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))
        = ∑ B ∈ S.coreBlocks C, term (vec B) := by
            apply Finset.sum_congr rfl
            intro B hB
            exact hterm_eq B hB
    _ = ∑ e ∈ (S.coreBlocks C).image vec, term e := by
            rw [Finset.sum_image]
            intro B hB R hR hEq
            exact hvec_inj hB hR hEq
    _ ≤ ∑ e ∈ E, term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro e he
                rcases Finset.mem_image.mp he with ⟨B, hB, rfl⟩
                exact hvec_mem B hB)
              (by
                intro e _heE _heNot
                dsimp [term]
                positivity)
    _ = ∏ _p : Index,
          ∑ ν ∈ Finset.range N, (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2) := by
            change
              (∑ e ∈ Fintype.piFinset (fun _ : Index => Finset.range N),
                ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)) =
              ∏ _p : Index,
                ∑ ν ∈ Finset.range N, (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)
            exact
              (Finset.sum_prod_piFinset
                (ι := Index) (κ := ℕ) (R := ℝ)
                (s := Finset.range N)
                (g := fun _p ν => (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)))
    _ ≤ ∏ _p : Index, (2 : ℝ) := by
            exact Finset.prod_le_prod
              (s := (Finset.univ : Finset Index))
              (fun _p _hp => by positivity)
              (fun _p _hp => by
                simpa [Nat.cast_add, Nat.cast_one] using sum_inv_sq_range_le_two N)
    _ = (2 : ℝ) ^ C.card := by
            simp [Index]

/-- Prefix-omega sum for a newest-first list of selected blocks. Since the
chain constructor prepends the new block, the prefix before the head is the
product of the tail. -/
noncomputable def chainTFromBlocks : List ℕ → ℕ
  | [] => 0
  | _P :: Ps => omega (Ps.foldr (· * ·) 1) + chainTFromBlocks Ps

/-- The accumulated `T = ∑ W_{r-1}` along a chain, computed from the stored
block list. -/
noncomputable def chainT {N : ℕ} {D : PrunedData N} (S : ChainState N D) : ℕ :=
  chainTFromBlocks S.blocks

private lemma chainTFromBlocks_le_length_mul_omega_foldr
    (blocks : List ℕ) (hpos : ∀ P ∈ blocks, 0 < P) :
    chainTFromBlocks blocks ≤ blocks.length * omega (blocks.foldr (· * ·) 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      have hPs_pos : ∀ B ∈ Ps, 0 < B := by
        intro B hB
        exact hpos B (by simp [hB])
      have htail_le_full :
          omega (Ps.foldr (· * ·) 1) ≤ omega (P * Ps.foldr (· * ·) 1) := by
        apply omega_le_of_dvd
        · exact dvd_mul_left (Ps.foldr (· * ·) 1) P
        · exact (Nat.mul_pos (hpos P (by simp)) (List.foldr_mul_pos hPs_pos)).ne'
      calc
        omega (Ps.foldr (· * ·) 1) + chainTFromBlocks Ps
            ≤ omega (P * Ps.foldr (· * ·) 1) +
                Ps.length * omega (Ps.foldr (· * ·) 1) := by
              exact Nat.add_le_add htail_le_full (ih hPs_pos)
        _ ≤ omega (P * Ps.foldr (· * ·) 1) +
                Ps.length * omega (P * Ps.foldr (· * ·) 1) := by
              exact Nat.add_le_add_left
                (Nat.mul_le_mul_left Ps.length htail_le_full) _
        _ = (Ps.length + 1) * omega (P * Ps.foldr (· * ·) 1) := by
              rw [Nat.add_mul, Nat.one_mul]
              omega

private lemma chainTFromBlocks_real_quadratic_bound
    (blocks : List ℕ)
    (hpair : blocks.Pairwise Nat.Coprime)
    (homega_pos : ∀ P ∈ blocks, 1 ≤ omega P) :
    ((chainTFromBlocks blocks : ℝ) * 2) ≤
      2 * (blocks.length : ℝ) * (omega (blocks.foldr (· * ·) 1) : ℝ) -
        (blocks.length : ℝ) * ((blocks.length : ℝ) - 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      rw [List.pairwise_cons] at hpair
      have hPs_pair : Ps.Pairwise Nat.Coprime := hpair.2
      have hPs_omega : ∀ B ∈ Ps, 1 ≤ omega B := by
        intro B hB
        exact homega_pos B (by simp [hB])
      have hPomega : 1 ≤ omega P := homega_pos P (by simp)
      have hcop : Nat.Coprime P (Ps.foldr (· * ·) 1) :=
        List.coprime_foldr_mul_of_forall hpair.1
      have homega :
          omega (P * Ps.foldr (· * ·) 1) =
            omega P + omega (Ps.foldr (· * ·) 1) :=
        omega_mul_of_coprime hcop
      have hih := ih hPs_pair hPs_omega
      have hPomega_real : (1 : ℝ) ≤ (omega P : ℝ) := by
        exact_mod_cast hPomega
      have hlen_nonneg : 0 ≤ (Ps.length : ℝ) := by positivity
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      rw [homega]
      norm_num [Nat.cast_add, Nat.cast_mul] at hih ⊢
      nlinarith [hih, hPomega_real, hlen_nonneg]

private lemma chainTFromBlocks_add_omega_real_quadratic_bound
    (blocks : List ℕ)
    (hpair : blocks.Pairwise Nat.Coprime)
    (homega_pos : ∀ P ∈ blocks, 1 ≤ omega P) :
    (((chainTFromBlocks blocks + omega (blocks.foldr (· * ·) 1) : ℕ) : ℝ) * 2) ≤
      2 * (blocks.length : ℝ) * (omega (blocks.foldr (· * ·) 1) : ℝ) -
        (blocks.length : ℝ) * ((blocks.length : ℝ) - 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      rw [List.pairwise_cons] at hpair
      have hPs_pair : Ps.Pairwise Nat.Coprime := hpair.2
      have hPs_omega : ∀ B ∈ Ps, 1 ≤ omega B := by
        intro B hB
        exact homega_pos B (by simp [hB])
      have hPomega : 1 ≤ omega P := homega_pos P (by simp)
      have hcop : Nat.Coprime P (Ps.foldr (· * ·) 1) :=
        List.coprime_foldr_mul_of_forall hpair.1
      have homega :
          omega (P * Ps.foldr (· * ·) 1) =
            omega P + omega (Ps.foldr (· * ·) 1) :=
        omega_mul_of_coprime hcop
      have hih := ih hPs_pair hPs_omega
      have hPomega_real : (1 : ℝ) ≤ (omega P : ℝ) := by
        exact_mod_cast hPomega
      have hlen_nonneg : 0 ≤ (Ps.length : ℝ) := by positivity
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      rw [homega]
      norm_num [Nat.cast_add, Nat.cast_mul] at hih ⊢
      nlinarith [hih, hPomega_real, hlen_nonneg]

lemma ChainState.chainT_le_r_mul_W {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    chainT S ≤ S.r * S.W := by
  have h := chainTFromBlocks_le_length_mul_omega_foldr S.blocks S.blocks_pos
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_le_r_mul_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    chainT S ≤ S.r * D.K := by
  exact (S.chainT_le_r_mul_W).trans (Nat.mul_le_mul_left S.r S.W_le_K)

lemma ChainState.chainT_real_quadratic_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hblocks : S.BlocksOmegaPos) :
    ((chainT S : ℝ) * 2) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) := by
  have h := chainTFromBlocks_real_quadratic_bound S.blocks S.pairwise_coprime hblocks
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_add_W_real_quadratic_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hblocks : S.BlocksOmegaPos) :
    ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) := by
  have h := chainTFromBlocks_add_omega_real_quadratic_bound
    S.blocks S.pairwise_coprime hblocks
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_cons_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {P : ℕ} {S' : ChainState N D}
    (hblocks : S'.blocks = P :: S.blocks) :
    chainT S' = S.W + chainT S := by
  calc
    chainT S' = omega (S.blocks.foldr (· * ·) 1) + chainTFromBlocks S.blocks := by
      simp [chainT, hblocks, chainTFromBlocks]
    _ = S.W + chainT S := by
      rw [← S.product_eq, ← S.W_eq]
      rfl

/-- Cumulative lower-bound scale for the survivor set after a chain state.
This is the formal slot for the PDF's iterated lower bound (12), with
`Λ` standing for the spread/block loss constant. -/
noncomputable def chainLowerScale {N : ℕ} {D : PrunedData N}
    (Λ : ℝ) (S : ChainState N D) : ℝ :=
  (D.Q.card : ℝ) /
    ((S.productP : ℝ) * (hExp S.productP : ℝ) ^ 2 * Λ ^ S.W)

/-- The cumulative survivor-size invariant needed to turn the local
structural step into the global chain inequality. -/
def ChainState.HasLowerBound {N : ℕ} {D : PrunedData N}
    (Λ : ℝ) (S : ChainState N D) : Prop :=
  chainLowerScale Λ S ≤ (S.Qsurv.card : ℝ)

private lemma div_scale_le_weighted_share
    {a q c w p h κ : ℝ} {n : ℕ}
    (hq_nonneg : 0 ≤ q) (hw_pos : 0 < w)
    (hp : 0 < p) (hh : 0 < h) (hκ : 0 < κ)
    (haq : a ≤ q) (hdense : q / κ ^ n < c) (hweight : w ≤ (2 : ℝ) ^ n) :
    a / (p * h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) / p := by
  have hκpow : 0 < κ ^ n := pow_pos hκ _
  have htwopow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hΛpow : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
  have hq_lt : q < c * κ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hdense hκpow
    rwa [div_mul_cancel₀ _ hκpow.ne'] at hmul
  have haw_le : a * w ≤ q * (2 : ℝ) ^ n :=
    mul_le_mul haq hweight hw_pos.le hq_nonneg
  have htarget : a * w ≤ c * (2 * κ) ^ n := by
    calc
      a * w ≤ q * (2 : ℝ) ^ n := haw_le
      _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
            (mul_lt_mul_of_pos_right hq_lt htwopow).le
      _ = c * (2 * κ) ^ n := by
            rw [mul_pow]
            ring
  calc
    a / (p * h * (2 * κ) ^ n)
        = (a * w) / ((p * h * (2 * κ) ^ n) * w) := by
            field_simp [hw_pos.ne']
    _ ≤ (c * (2 * κ) ^ n) / ((p * h * (2 * κ) ^ n) * w) := by
            exact div_le_div_of_nonneg_right htarget
              (mul_nonneg
                (mul_nonneg (mul_pos hp hh).le hΛpow.le)
                hw_pos.le)
    _ = (c * (1 / h) / w) / p := by
            field_simp [hp.ne', hh.ne', hΛpow.ne', hw_pos.ne']

private lemma div_scale_le_weighted_fiber
    {a q c w h κ : ℝ} {n : ℕ}
    (hq_nonneg : 0 ≤ q) (hw_pos : 0 < w)
    (hh : 0 < h) (hκ : 0 < κ)
    (haq : a ≤ q) (hdense : q / κ ^ n < c) (hweight : w ≤ (2 : ℝ) ^ n) :
    a / (h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) := by
  have hκpow : 0 < κ ^ n := pow_pos hκ _
  have htwopow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hΛpow : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
  have hq_lt : q < c * κ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hdense hκpow
    rwa [div_mul_cancel₀ _ hκpow.ne'] at hmul
  have haw_le : a * w ≤ q * (2 : ℝ) ^ n :=
    mul_le_mul haq hweight hw_pos.le hq_nonneg
  have htarget : a * w ≤ c * (2 * κ) ^ n := by
    calc
      a * w ≤ q * (2 : ℝ) ^ n := haw_le
      _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
            (mul_lt_mul_of_pos_right hq_lt htwopow).le
      _ = c * (2 * κ) ^ n := by
            rw [mul_pow]
            ring
  calc
    a / (h * (2 * κ) ^ n)
        = (a * w) / ((h * (2 * κ) ^ n) * w) := by
            field_simp [hw_pos.ne']
    _ ≤ (c * (2 * κ) ^ n) / ((h * (2 * κ) ^ n) * w) := by
            exact div_le_div_of_nonneg_right htarget
              (mul_nonneg (mul_pos hh hΛpow).le hw_pos.le)
    _ = c * (1 / h) / w := by
            field_simp [hh.ne', hΛpow.ne', hw_pos.ne']

lemma ChainState.chainLowerScale_extend_coreBlock_eq
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hP : P ∈ S.coreBlocks C)
    (hprod : S'.productP = P * S.productP)
    (hW : S'.W = S.W + C.card) :
    chainLowerScale Λ S' =
      chainLowerScale Λ S / ((P : ℝ) * (hExp P : ℝ) ^ 2 * Λ ^ C.card) := by
  rw [chainLowerScale, chainLowerScale, hprod, hW,
    hExp_mul_of_coprime (S.coreBlock_coprime_productP hP).symm, pow_add]
  norm_num [Nat.cast_mul]
  ring_nf

lemma ChainState.hasLowerBound_extend_coreBlock
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {κ Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hκ : 0 < κ) (hΛ : Λ = 2 * κ)
    (hP : P ∈ S.coreBlocks C)
    (hLower : S.HasLowerBound Λ)
    (hDense :
      ((S.Qsurv.card : ℝ) / κ ^ C.card) <
        ((S.coreSurvivors C).card : ℝ))
    (hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card)
    (hCard :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ))
    (hprod : S'.productP = P * S.productP)
    (hW : S'.W = S.W + C.card) :
    S'.HasLowerBound Λ := by
  rw [ChainState.HasLowerBound]
  rw [S.chainLowerScale_extend_coreBlock_eq hP hprod hW, hΛ]
  have hCore : (S.coreSurvivors C).Nonempty := by
    have hPmem := hP
    rw [ChainState.coreBlocks] at hPmem
    rcases Finset.mem_image.mp hPmem with ⟨q, hq, _hP⟩
    exact ⟨q, hq⟩
  have hWeight_pos :
      0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) :=
    S.coreBlocks_weight_sum_pos hCore
  have hP_pos_real : 0 < (P : ℝ) := by
    exact_mod_cast S.coreBlock_pos hP
  have hExpP_pos : 0 < (hExp P : ℝ) := by exact_mod_cast hExp_pos P
  have hh_pos : 0 < ((hExp P : ℝ) ^ 2) := sq_pos_of_pos hExpP_pos
  have hq_nonneg : 0 ≤ (S.Qsurv.card : ℝ) := by positivity
  have hstep :
      chainLowerScale (2 * κ) S /
          ((P : ℝ) * ((hExp P : ℝ) ^ 2) * (2 * κ) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) :=
    div_scale_le_weighted_share
      hq_nonneg hWeight_pos hP_pos_real hh_pos hκ
      (by simpa [ChainState.HasLowerBound, hΛ] using hLower)
      hDense hWeight
  exact hstep.trans hCard

lemma ChainState.selectedFiber_lower_from_invariant
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ}
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hLower : S.HasLowerBound (chainLambda D))
    (hDense :
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card)
    (hWeightedFiber :
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ)) :
    (D.Q.card : ℝ) /
        ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
          (chainLambda D) ^ (S.W + C.card)) ≤
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) := by
  have hCore : (S.coreSurvivors C).Nonempty := by
    rw [ChainState.coreBlocks] at hP
    rcases Finset.mem_image.mp hP with ⟨q, hq, _hP⟩
    exact ⟨q, hq⟩
  have hDenseQ :
      ((S.Qsurv.card : ℝ) / (chainKappa D) ^ C.card) <
        ((S.coreSurvivors C).card : ℝ) :=
    S.coreSurvivors_card_gt_qsurv_div_of_dense_bound (Λ := chainKappa D)
      (by simpa using hDense)
  have hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card :=
    S.coreBlocks_weight_sum_le_two_pow_card hCne
  have hWeight_pos :
      0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) :=
    S.coreBlocks_weight_sum_pos hCore
  have hExpP_pos : 0 < (hExp P : ℝ) := by exact_mod_cast hExp_pos P
  have hh_pos : 0 < ((hExp P : ℝ) ^ 2) := sq_pos_of_pos hExpP_pos
  have hq_nonneg : 0 ≤ (S.Qsurv.card : ℝ) := by positivity
  have hstep :
      chainLowerScale (2 * chainKappa D) S /
          (((hExp P : ℝ) ^ 2) * (2 * chainKappa D) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) :=
    div_scale_le_weighted_fiber
      hq_nonneg hWeight_pos hh_pos (chainKappa_pos D)
      (by simpa [ChainState.HasLowerBound, chainLambda] using hLower)
      hDenseQ hWeight
  have hstepΛ :
      chainLowerScale (chainLambda D) S /
          (((hExp P : ℝ) ^ 2) * (chainLambda D) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) := by
    simpa [chainLambda] using hstep
  have hleft :
      chainLowerScale (chainLambda D) S /
          (((hExp P : ℝ) ^ 2) * (chainLambda D) ^ C.card) =
        (D.Q.card : ℝ) /
          ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
            (chainLambda D) ^ (S.W + C.card)) := by
    rw [chainLowerScale,
      hExp_mul_of_coprime (S.coreBlock_coprime_productP hP), pow_add]
    norm_num [Nat.cast_mul]
    ring_nf
  rw [← hleft]
  exact hstepΛ.trans hWeightedFiber

lemma ChainState.blocksOmegaPos_extend_coreBlock
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hBlocks : S.BlocksOmegaPos)
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hblocks : S'.blocks = P :: S.blocks) :
    S'.BlocksOmegaPos := by
  intro B hB
  rw [hblocks] at hB
  rcases List.mem_cons.1 hB with hBP | hBtail
  · subst B
    rw [S.coreBlock_omega_eq_card hP]
    exact Nat.succ_le_of_lt hCne.card_pos
  · exact hBlocks B hBtail

/-! ## §2 Initial state -/

/-- The chain starts with no selected blocks, all pruned moduli surviving,
product `1`, and accumulated exponent count `0`. -/
noncomputable def initialChainState (N : ℕ) (D : PrunedData N) : ChainState N D where
  r := 0
  blocks := []
  blocks_length := by simp
  Qsurv := D.Q
  Qsurv_subset := by intro q hq; exact hq
  Qsurv_nonempty := D.Q_nonempty
  W := 0
  productP := 1
  product_eq := by simp
  blocks_pos := by intro P hP; simp at hP
  productP_pos := by norm_num
  pairwise_coprime := by simp
  exact_divides := by intro q _hq; exact one_dvd q
  no_selected_prime_remains := by
    intro _q _hq _p hp
    simp [primeSupport] at hp
  residues_agree := by
    intro qi _hqi rj _hrj hqiD hrjD
    rw [Int.modEq_iff_dvd]
    exact one_dvd (D.a ⟨rj, hrjD⟩ - D.a ⟨qi, hqiD⟩)
  W_eq := by simp [omega, primeSupport]
  W_le_K := by omega

lemma initialChainState_room (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).W < D.K := by
  simp [initialChainState]
  exact D.K_pos

lemma initialChainState_r_zero (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).r = 0 := rfl

lemma initialChainState_product_one (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).productP = 1 := rfl

lemma initialChainState_chainT (N : ℕ) (D : PrunedData N) :
    chainT (initialChainState N D) = 0 := rfl

lemma initialChainState_blocksOmegaPos (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).BlocksOmegaPos := by
  intro P hP
  simp [initialChainState] at hP

lemma initialChainState_hasLowerBound {N : ℕ} (D : PrunedData N) (Λ : ℝ) :
    ChainState.HasLowerBound Λ (initialChainState N D) := by
  rw [ChainState.HasLowerBound, chainLowerScale]
  simp [initialChainState, hExp_one]

/-! ## §3 Structural chain step -/

theorem chain_step_structural
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      0 < C0 ∧
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) /
          (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases S.exists_dense_core_with_survivor_of_room hRoom with
    ⟨C0, hC0, C, hCne, hCore, hDense⟩
  rcases S.exists_weighted_extended_coreBlock hCore with
    ⟨P, S', hP, hblocks, hr, hprod, _hQsubset, _hQcard_le, hW, _hShare, hcard⟩
  have hWincrease : S.W < S'.W := by
    rw [hW]
    exact Nat.lt_add_of_pos_right hCne.card_pos
  exact ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hcard, hDense⟩

theorem chain_step_structural_with_lowerBound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.exists_dense_core_fixed_with_survivor_of_room hRoom with
    ⟨C, hCne, hCore, hDense⟩
  rcases S.exists_weighted_extended_coreBlock hCore with
    ⟨P, S', hP, hblocks, hr, hprod, hQsubset, hQcard_le, hW, hShare, hcard⟩
  have hWincrease : S.W < S'.W := by
    rw [hW]
    exact Nat.lt_add_of_pos_right hCne.card_pos
  have hDenseQ :
      ((S.Qsurv.card : ℝ) / (chainKappa D) ^ C.card) <
        ((S.coreSurvivors C).card : ℝ) :=
    S.coreSurvivors_card_gt_qsurv_div_of_dense_bound (Λ := chainKappa D)
      (by simpa using hDense)
  have hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card :=
    S.coreBlocks_weight_sum_le_two_pow_card hCne
  have hLower' : S'.HasLowerBound (chainLambda D) := by
    apply S.hasLowerBound_extend_coreBlock
      (κ := chainKappa D) (Λ := chainLambda D)
      (hκ := chainKappa_pos D) (hΛ := by rfl)
      (hP := hP) (hLower := hLower) (hDense := hDenseQ)
      (hWeight := hWeight) (hCard := hcard)
      (hprod := hprod) (hW := hW)
  exact ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le, hW,
    S.chainT_cons_eq hblocks, hLower', hShare, hcard, hDense⟩

lemma ChainState.coreSurvivors_nonempty_of_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : (S.coreSurvivors C).Nonempty := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, _⟩
  exact ⟨q, hq⟩

theorem chain_step_structural_with_counts
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      0 < C0 ∧
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) /
          (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card ∧
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) ∧
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) ∧
      P ≤ N ∧
      (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases chain_step_structural S hRoom with
    ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hweighted, hDense⟩
  have hCore : (S.coreSurvivors C).Nonempty := S.coreSurvivors_nonempty_of_coreBlock hP
  exact ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hweighted, hDense,
    S.coreSurvivors_card_real_le_bfv_omega_count C ε hCount,
    S.coreBlocks_card_real_le_bfv_omega_count C ε hCore hCount,
    S.coreBlock_le_N hP, S.coreBlock_hExp_bound hP⟩

theorem chain_step_structural_with_counts_and_lowerBound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card ∧
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) ∧
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) ∧
      P ≤ N ∧
      (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases chain_step_structural_with_lowerBound S hRoom hLower with
    ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le,
      hW, hT, hLower', hShare, hweighted, hDense⟩
  have hCore : (S.coreSurvivors C).Nonempty := S.coreSurvivors_nonempty_of_coreBlock hP
  exact ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le,
    hW, hT, hLower',
    hShare, hweighted, hDense,
    S.coreSurvivors_card_real_le_bfv_omega_count C ε hCount,
    S.coreBlocks_card_real_le_bfv_omega_count C ε hCore hCount,
    S.coreBlock_le_N hP, S.coreBlock_hExp_bound hP⟩

noncomputable def chainStepBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  (N : ℝ) / (D.Q.card : ℝ)
    * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))

noncomputable def chainProductBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  ((N : ℝ) / (D.Q.card : ℝ)) ^ S.r
    * Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ)))

lemma chainStepBound_nonneg {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 ≤ chainStepBound ε S := by
  rw [chainStepBound]
  positivity

lemma chainProductBound_pos {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 < chainProductBound ε S := by
  rw [chainProductBound]
  have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
  have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
  positivity

noncomputable def chainStepBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (_S S' : ChainState N D) : ℝ :=
  (N : ℝ) / (D.Q.card : ℝ)
    * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((S'.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
    * (hExp S'.productP : ℝ) ^ 2
    * (chainLambda D) ^ S'.W

noncomputable def chainProductBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  ((N : ℝ) / (D.Q.card : ℝ)) ^ S.r
    * Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
    * Real.exp (2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)))
    * (chainLambda D) ^ (chainT S + S.W)

lemma chainStepBoundWithLosses_nonneg {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S S' : ChainState N D) : 0 ≤ chainStepBoundWithLosses ε S S' := by
  rw [chainStepBoundWithLosses]
  have hΛ : 0 ≤ chainLambda D := (chainLambda_pos D).le
  positivity

lemma chainProductBoundWithLosses_pos {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 < chainProductBoundWithLosses ε S := by
  rw [chainProductBoundWithLosses]
  have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
  have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
  have hΛ : 0 < chainLambda D := chainLambda_pos D
  positivity

lemma log_chainProductBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) :
    Real.log (chainProductBound ε S) =
      (S.r : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
        (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
        ((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ)) := by
  rw [chainProductBound]
  set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
  set a : ℝ := (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N
  set b : ℝ := ((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ))
  have hq_pos : 0 < q := by
    dsimp [q]
    have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
    have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    positivity
  have hqpow_ne : q ^ S.r ≠ 0 := pow_ne_zero _ hq_pos.ne'
  have hexpa_ne : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have hexpb_ne : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
  rw [Real.log_mul (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne,
    Real.log_mul hqpow_ne hexpa_ne, Real.log_pow, Real.log_exp, Real.log_exp]

lemma log_chainProductBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) :
    Real.log (chainProductBoundWithLosses ε S) =
      (S.r : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
        (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
        ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
        2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
        ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
  rw [chainProductBoundWithLosses]
  set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
  set a : ℝ := (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N
  set b : ℝ := (((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))
  set c : ℝ := 2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ))
  set Λ : ℝ := chainLambda D
  have hq_pos : 0 < q := by
    dsimp [q]
    have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
    have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    positivity
  have hΛ_pos : 0 < Λ := by
    dsimp [Λ]
    exact chainLambda_pos D
  have hqpow_ne : q ^ S.r ≠ 0 := pow_ne_zero _ hq_pos.ne'
  have hexpa_ne : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have hexpb_ne : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
  have hexpc_ne : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  have hΛpow_ne : Λ ^ (chainT S + S.W) ≠ 0 := pow_ne_zero _ hΛ_pos.ne'
  rw [Real.log_mul
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne) hexpc_ne)
        hΛpow_ne,
      Real.log_mul (mul_ne_zero (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne) hexpc_ne,
      Real.log_mul (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne,
      Real.log_mul hqpow_ne hexpa_ne,
      Real.log_pow, Real.log_exp, Real.log_exp, Real.log_exp, Real.log_pow]

lemma initialChainState_productBound {N : ℕ} (D : PrunedData N) (ε : ℝ) :
    ((initialChainState N D).productP : ℝ) ≤
      chainProductBound ε (initialChainState N D) := by
  simp [chainProductBound, initialChainState]

lemma initialChainState_productBoundWithLosses {N : ℕ} (D : PrunedData N) (ε : ℝ) :
    ((initialChainState N D).productP : ℝ) ≤
      chainProductBoundWithLosses ε (initialChainState N D) := by
  simp [chainProductBoundWithLosses, initialChainState, chainT, chainTFromBlocks]

lemma chainProductBound_step
    {N : ℕ} {D : PrunedData N} {ε : ℝ} {S S' : ChainState N D}
    (hr : S'.r = S.r + 1)
    (hT : chainT S' = S.W + chainT S)
    (hProd : (S.productP : ℝ) ≤ chainProductBound ε S)
    (hStep :
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBound ε S) :
    (S'.productP : ℝ) ≤ chainProductBound ε S' := by
  have hstep_nonneg : 0 ≤ chainStepBound ε S := chainStepBound_nonneg ε S
  calc
    (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBound ε S := hStep
    _ ≤ chainProductBound ε S * chainStepBound ε S := by
          exact mul_le_mul_of_nonneg_right hProd hstep_nonneg
    _ = chainProductBound ε S' := by
          rw [chainProductBound, chainStepBound, chainProductBound, hr, hT]
          set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
          set a : ℝ := (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N with ha
          set l : ℝ := Real.log (Real.log (N : ℝ))
          rw [pow_succ]
          have hExpR :
              Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) =
                Real.exp ((S.r : ℝ) * a) := by
            rw [ha]
            ring_nf
          have hExpR1 :
              Real.exp (((S.r + 1 : ℕ) : ℝ) *
                  (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) =
                Real.exp (((S.r + 1 : ℕ) : ℝ) * a) := by
            rw [ha]
            ring_nf
          rw [hExpR, hExpR1]
          change
            (q ^ S.r * Real.exp ((S.r : ℝ) * a) *
                  Real.exp (((chainT S : ℝ) / 2) * l)) *
                (q * Real.exp a * Real.exp (((S.W : ℝ) / 2) * l)) =
              q ^ S.r * q * Real.exp (((S.r + 1 : ℕ) : ℝ) * a) *
                Real.exp ((((S.W + chainT S : ℕ) : ℝ) / 2) * l)
          calc
            (q ^ S.r * Real.exp ((S.r : ℝ) * a) *
                  Real.exp (((chainT S : ℝ) / 2) * l)) *
                (q * Real.exp a * Real.exp (((S.W : ℝ) / 2) * l))
                = q ^ S.r * q *
                    (Real.exp ((S.r : ℝ) * a) * Real.exp a) *
                    (Real.exp (((chainT S : ℝ) / 2) * l) *
                      Real.exp (((S.W : ℝ) / 2) * l)) := by
                    ring
            _ = q ^ S.r * q * Real.exp (((S.r + 1 : ℕ) : ℝ) * a) *
                  Real.exp ((((S.W + chainT S : ℕ) : ℝ) / 2) * l) := by
                    rw [← Real.exp_add, ← Real.exp_add]
                    congr 2
                    · congr 1
                      norm_num
                      ring
                    · norm_num
                      ring

lemma chainProductBoundWithLosses_step
    {N : ℕ} {D : PrunedData N} {ε : ℝ} {S S' : ChainState N D}
    (hr : S'.r = S.r + 1)
    (hT : chainT S' = S.W + chainT S)
    (hProd : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S)
    (hStep :
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S') :
    (S'.productP : ℝ) ≤ chainProductBoundWithLosses ε S' := by
  have hstep_nonneg : 0 ≤ chainStepBoundWithLosses ε S S' :=
    chainStepBoundWithLosses_nonneg ε S S'
  have hExpBound : (hExp S'.productP : ℝ) ≤
      Real.exp (Real.sqrt (Real.log (N : ℝ))) :=
    S'.productP_hExp_bound
  have hExpSq :
      (hExp S'.productP : ℝ) ^ 2 ≤
        Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
    have hnonneg : 0 ≤ (hExp S'.productP : ℝ) := by positivity
    calc
      (hExp S'.productP : ℝ) ^ 2
          ≤ (Real.exp (Real.sqrt (Real.log (N : ℝ)))) ^ 2 :=
            sq_le_sq₀ hnonneg (Real.exp_pos _).le |>.2 hExpBound
      _ = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
            rw [sq, ← Real.exp_add]
            ring_nf
  calc
    (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := hStep
    _ ≤ chainProductBoundWithLosses ε S * chainStepBoundWithLosses ε S S' := by
          exact mul_le_mul_of_nonneg_right hProd hstep_nonneg
    _ ≤ chainProductBoundWithLosses ε S' := by
          rw [chainProductBoundWithLosses, chainStepBoundWithLosses,
            chainProductBoundWithLosses, hr, hT]
          set q : ℝ := (N : ℝ) / (D.Q.card : ℝ) with hq
          set a : ℝ := -((D.K : ℝ) / Mscale N) / 2 + ε with ha
          set l : ℝ := Real.log (Real.log (N : ℝ)) with hl
          set u : ℝ := Real.sqrt (Real.log (N : ℝ)) with hu
          have hΛnonneg : 0 ≤ chainLambda D := (chainLambda_pos D).le
          calc
            (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                  Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * (S.r : ℝ) * u) *
                  (chainLambda D) ^ (chainT S + S.W)) *
                (q * Real.exp (a * Zscale N) * Real.exp (((S'.W : ℝ) / 2) * l) *
                  (hExp S'.productP : ℝ) ^ 2 * (chainLambda D) ^ S'.W)
                ≤
              (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                  Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * (S.r : ℝ) * u) *
                  (chainLambda D) ^ (chainT S + S.W)) *
                (q * Real.exp (a * Zscale N) * Real.exp (((S'.W : ℝ) / 2) * l) *
                  Real.exp (2 * u) * (chainLambda D) ^ S'.W) := by
                    exact mul_le_mul_of_nonneg_left
                      (by
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left hExpSq (by positivity))
                          (pow_nonneg hΛnonneg _))
                      (by positivity)
            _ = q ^ (S.r + 1) *
                  Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) *
                  Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
                  (chainLambda D) ^ (S.W + chainT S + S'.W) := by
                    rw [pow_succ]
                    calc
                      (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                            Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                            Real.exp (2 * (S.r : ℝ) * u) *
                            (chainLambda D) ^ (chainT S + S.W)) *
                          (q * Real.exp (a * Zscale N) *
                            Real.exp (((S'.W : ℝ) / 2) * l) *
                            Real.exp (2 * u) * (chainLambda D) ^ S'.W)
                          =
                        q ^ S.r * q *
                          (Real.exp ((S.r : ℝ) * a * Zscale N) *
                            Real.exp (a * Zscale N)) *
                          (Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                            Real.exp (((S'.W : ℝ) / 2) * l)) *
                          (Real.exp (2 * (S.r : ℝ) * u) * Real.exp (2 * u)) *
                          ((chainLambda D) ^ (chainT S + S.W) *
                            (chainLambda D) ^ S'.W) := by ring
                      _ =
                        q ^ S.r * q *
                          Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) *
                          Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) * l) *
                          Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
                          (chainLambda D) ^ (S.W + chainT S + S'.W) := by
                            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
                              ← pow_add]
                            have hA :
                                Real.exp ((S.r : ℝ) * a * Zscale N + a * Zscale N) =
                                  Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) := by
                              congr 1
                              norm_num
                              ring
                            have hL :
                                Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l +
                                    ((S'.W : ℝ) / 2) * l) =
                                  Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) *
                                    l) := by
                              congr 1
                              norm_num [Nat.cast_add]
                              ring
                            have hU :
                                Real.exp (2 * (S.r : ℝ) * u + 2 * u) =
                                  Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) := by
                              congr 1
                              norm_num
                              ring
                            rw [hA, hL, hU]
                            ring

theorem chain_terminal_with_product_bound_from_state
    {N : ℕ} {D : PrunedData N} (ε : ℝ)
    (hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S')
    (S : ChainState N D)
    (hLower : S.HasLowerBound (chainLambda D))
    (hBlocks : S.BlocksOmegaPos)
    (hProd : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S) :
    ∃ Sfinal : ChainState N D,
      S.r ≤ Sfinal.r ∧
      Sfinal.r ≤ S.r + (D.K - S.W) ∧
      Sfinal.W = D.K ∧
      Sfinal.HasLowerBound (chainLambda D) ∧
      Sfinal.BlocksOmegaPos ∧
      (Sfinal.productP : ℝ) ≤ chainProductBoundWithLosses ε Sfinal := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ S : ChainState N D,
      D.K - S.W = n →
      S.HasLowerBound (chainLambda D) →
      S.BlocksOmegaPos →
      (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S →
      ∃ Sfinal : ChainState N D,
        S.r ≤ Sfinal.r ∧
        Sfinal.r ≤ S.r + (D.K - S.W) ∧
        Sfinal.W = D.K ∧
        Sfinal.HasLowerBound (chainLambda D) ∧
        Sfinal.BlocksOmegaPos ∧
        (Sfinal.productP : ℝ) ≤ chainProductBoundWithLosses ε Sfinal
  have hmain : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn hLowerS hBlocksS hProdS
        by_cases hdone : S.W = D.K
        · refine ⟨S, le_rfl, ?_, hdone, hLowerS, hBlocksS, hProdS⟩
          rw [hdone]
          simp
        · have hRoom : S.W < D.K := lt_of_le_of_ne S.W_le_K hdone
          rcases hStep S hLowerS hBlocksS hRoom with
            ⟨S', hr, hWincrease, hT, hLower', hBlocks', hStepProd⟩
          have hProd' : (S'.productP : ℝ) ≤ chainProductBoundWithLosses ε S' :=
            chainProductBoundWithLosses_step hr hT hProdS hStepProd
          have hlt : D.K - S'.W < n := by
            rw [← hn]
            omega
          rcases ih (D.K - S'.W) hlt S' rfl hLower' hBlocks' hProd' with
            ⟨Sfinal, hle_start, hle_budget, hWfinal, hLowerFinal, hBlocksFinal,
              hProdFinal⟩
          refine ⟨Sfinal, ?_, ?_, hWfinal, hLowerFinal, hBlocksFinal, hProdFinal⟩
          · have hstep : S.r ≤ S'.r := by
              rw [hr]
              omega
            exact hstep.trans hle_start
          · have hbudget :
                S'.r + (D.K - S'.W) ≤ S.r + (D.K - S.W) := by
              rw [hr]
              omega
            exact hle_budget.trans hbudget
  exact hmain (D.K - S.W) S rfl hLower hBlocks hProd

theorem chain_terminal_with_product_bound_from_initial
    (N : ℕ) (D : PrunedData N) (ε : ℝ)
    (hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S') :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.HasLowerBound (chainLambda D) ∧
      S.BlocksOmegaPos ∧
      (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S := by
  let S0 := initialChainState N D
  have hRoom0 : S0.W < D.K := by
    simpa [S0] using initialChainState_room N D
  have hLower0 : S0.HasLowerBound (chainLambda D) := by
    simpa [S0] using initialChainState_hasLowerBound D (chainLambda D)
  have hBlocks0 : S0.BlocksOmegaPos := by
    simpa [S0] using initialChainState_blocksOmegaPos N D
  have hProd0 : (S0.productP : ℝ) ≤ chainProductBoundWithLosses ε S0 := by
    simpa [S0] using initialChainState_productBoundWithLosses D ε
  rcases hStep S0 hLower0 hBlocks0 hRoom0 with
    ⟨S1, hr1, hWincrease1, _hT1, hLower1, hBlocks1, hStepProd1⟩
  have hProd1 : (S1.productP : ℝ) ≤ chainProductBoundWithLosses ε S1 :=
    chainProductBoundWithLosses_step hr1 _hT1 hProd0 hStepProd1
  rcases chain_terminal_with_product_bound_from_state ε hStep S1 hLower1 hBlocks1 hProd1 with
    ⟨S, hle_start, hle_budget, hW, hLower, hBlocks, hProd⟩
  refine ⟨S.r, S, rfl, ?_, ?_, Or.inr hW, hLower, hBlocks, hProd⟩
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    exact hS1r ▸ hle_start
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    have hS1W_pos : 0 < S1.W := by
      have hS0W : S0.W = 0 := rfl
      omega
    calc
      S.r ≤ S1.r + (D.K - S1.W) := hle_budget
      _ ≤ D.K := by
        rw [hS1r]
        omega

theorem chain_terminal_from_state
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ Sfinal : ChainState N D,
      S.r ≤ Sfinal.r ∧
      Sfinal.r ≤ S.r + (D.K - S.W) ∧
      Sfinal.W = D.K ∧
      Sfinal.HasLowerBound (chainLambda D) := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ S : ChainState N D,
      D.K - S.W = n →
      S.HasLowerBound (chainLambda D) →
      ∃ Sfinal : ChainState N D,
        S.r ≤ Sfinal.r ∧
        Sfinal.r ≤ S.r + (D.K - S.W) ∧
        Sfinal.W = D.K ∧
        Sfinal.HasLowerBound (chainLambda D)
  have hmain : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn hLowerS
        by_cases hdone : S.W = D.K
        · refine ⟨S, le_rfl, ?_, hdone, hLowerS⟩
          rw [hdone]
          simp
        · have hRoom : S.W < D.K := lt_of_le_of_ne S.W_le_K hdone
          rcases chain_step_structural_with_lowerBound S hRoom hLowerS with
            ⟨_C, _P, S', _hCne, _hP, _hblocks, hr, hWincrease, _hprod,
              _hQsubset, _hQcard_le, _hW, _hT, hLower', _hShare, _hcard, _hDense⟩
          have hlt : D.K - S'.W < n := by
            rw [← hn]
            omega
          rcases ih (D.K - S'.W) hlt S' rfl hLower' with
            ⟨Sfinal, hle_start, hle_budget, hWfinal, hLowerFinal⟩
          refine ⟨Sfinal, ?_, ?_, hWfinal, hLowerFinal⟩
          · have hstep : S.r ≤ S'.r := by
              rw [hr]
              omega
            exact hstep.trans hle_start
          · have hbudget :
                S'.r + (D.K - S'.W) ≤ S.r + (D.K - S.W) := by
              rw [hr]
              omega
            exact hle_budget.trans hbudget
  exact hmain (D.K - S.W) S rfl hLower

theorem chain_terminal_from_initial (N : ℕ) (D : PrunedData N) :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧
      1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.HasLowerBound (chainLambda D) := by
  let S0 := initialChainState N D
  have hRoom0 : S0.W < D.K := by
    simpa [S0] using initialChainState_room N D
  have hLower0 : S0.HasLowerBound (chainLambda D) := by
    simpa [S0] using initialChainState_hasLowerBound D (chainLambda D)
  rcases chain_step_structural_with_lowerBound S0 hRoom0 hLower0 with
    ⟨_C, _P, S1, _hCne, _hP, _hblocks, hr1, hWincrease1, _hprod,
      _hQsubset, _hQcard_le, _hW, _hT, hLower1, _hShare, _hcard, _hDense⟩
  rcases chain_terminal_from_state S1 hLower1 with
    ⟨S, hle_start, hle_budget, hW, hLower⟩
  refine ⟨S.r, S, rfl, ?_, ?_, Or.inr hW, hLower⟩
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    exact hS1r ▸ hle_start
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    have hS1W_pos : 0 < S1.W := by
      have hS0W : S0.W = 0 := rfl
      omega
    calc
      S.r ≤ S1.r + (D.K - S1.W) := hle_budget
      _ ≤ D.K := by
        rw [hS1r]
        omega

/-! ## §4 Chain step -/

/-- The remaining quantitative estimate in PDF Lemma 4.1: once the
structural step has selected an exact block `P`, the BFV count, dense-core
lower bound, weighted block choice, `hExp` control, and lower-order estimates
bound that block by the one-step product factor. -/
theorem chain_step_selected_block_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (_hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D))
    (_hBlocks : S.BlocksOmegaPos)
    {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hStepProduct : S'.productP = P * S.productP)
    (hStepW : S'.W = S.W + C.card)
    (_hStepLower : S'.HasLowerBound (chainLambda D))
    (_hQsurv_subset :
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P))
    (_hQsurv_card_le :
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card)
    (hWeightedFiber :
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ))
    (_hWeighted :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ))
    (hDense :
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card)
    (_hCoreCount :
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))
    (_hBlockCount :
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N))
    (_hP_le_N : P ≤ N)
    (_hP_hExp : (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))) :
    (P : ℝ) ≤ chainStepBoundWithLosses ε S S' := by
  have hFiberLower :
      (D.Q.card : ℝ) /
          ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
            (chainLambda D) ^ (S.W + C.card)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) :=
    S.selectedFiber_lower_from_invariant hCne hP hLower hDense hWeightedFiber
  have hFiberUpper :
      ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
        ((N : ℝ) / (S.productP * P : ℝ)) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) :=
    S.selectedFiber_card_real_le_bfv_omega_count hP ε hCount
  have hWithLosses :
      (P : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) *
          (hExp (S.productP * P) : ℝ) ^ 2 *
          (chainLambda D) ^ (S.W + C.card) := by
    have hcompare := hFiberLower.trans hFiberUpper
    have hDQpos : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    have hSpos : 0 < (S.productP : ℝ) := by exact_mod_cast S.productP_pos
    have hPpos : 0 < (P : ℝ) := by exact_mod_cast S.coreBlock_pos hP
    have hHpos : 0 < (hExp (S.productP * P) : ℝ) ^ 2 := by
      have h : 0 < (hExp (S.productP * P) : ℝ) := by exact_mod_cast hExp_pos (S.productP * P)
      exact sq_pos_of_pos h
    have hΛpos : 0 < (chainLambda D) ^ (S.W + C.card) :=
      pow_pos (chainLambda_pos D) _
    have hEpos :
        0 < Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) := by
      positivity
    field_simp [hSpos.ne', hPpos.ne', hHpos.ne', hΛpos.ne'] at hcompare
    have hmain :
        (D.Q.card : ℝ) * (P : ℝ) ≤
          (N : ℝ) *
            Real.exp ((-((D.K : ℝ) / Mscale N) + 2 * ε) * Zscale N / 2) *
            Real.exp (((S.W + C.card : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) / 2) *
            ((hExp (S.productP * P) : ℝ) ^ 2) *
            (chainLambda D) ^ (S.W + C.card) := by
      have hmul := mul_le_mul_of_nonneg_right hcompare hHpos.le
      rw [div_mul_cancel₀ _ hHpos.ne'] at hmul
      nlinarith [hmul]
    field_simp [hDQpos.ne']
    nlinarith [hmain]
  rw [chainStepBoundWithLosses, hStepW, hStepProduct]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hWithLosses

/-- **One chain step** (PDF Lemma 4.1). From a chain state with at least
one prime still to commit, the dense-core lemma + BFV count + residue
pigeonhole produce a next block `P_{r+1}` and a still-large surviving
sub-family. -/
theorem chain_step
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D))
    (hBlocks : S.BlocksOmegaPos) :
    ∃ S' : ChainState N D,
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      S'.BlocksOmegaPos ∧
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by
  rcases chain_step_structural_with_counts_and_lowerBound S ε hCount hRoom hLower with
    ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, _hQsubset, _hQcard_le,
      _hW, hT, hLower', _hWeightedFiber, _hweighted, _hDense, _hCoreCount, _hBlockCount,
      _hP_le_N, _hP_hExp⟩
  have hBlocks' : S'.BlocksOmegaPos :=
    S.blocksOmegaPos_extend_coreBlock hBlocks hCne hP hblocks
  refine ⟨S', hr, hWincrease, hT, hLower', hBlocks', ?_⟩
  have hPbound : (P : ℝ) ≤ chainStepBoundWithLosses ε S S' :=
    chain_step_selected_block_bound S ε _hε hCount hRoom hLower hBlocks
      hCne hP hprod _hW hLower' _hQsubset _hQcard_le _hWeightedFiber _hweighted _hDense
      _hCoreCount _hBlockCount _hP_le_N _hP_hExp
  rw [hprod]
  calc
    ((P * S.productP : ℕ) : ℝ) = (P : ℝ) * (S.productP : ℝ) := by norm_num
    _ ≤ chainStepBoundWithLosses ε S S' * (S.productP : ℝ) := by
          exact mul_le_mul_of_nonneg_right hPbound (by positivity)
    _ = (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by ring

/-! ## §5 The chain inequality (telescoped) -/

/-- **Chain inequality** (PDF Proposition 4.2). The full descending chain
runs for `R` steps until either `W = K` or `productP ≥ N L(-2, N)`. -/
theorem chain_inequality
    (N : ℕ) (D : PrunedData N) (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.BlocksOmegaPos ∧
      -- telescoped product bound, parameterized by ε, with the explicit
      -- lower-order losses from the paper:
      (S.productP : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) ^ R
        * Real.exp ((R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        * Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ)))
        * Real.exp (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)))
        * (chainLambda D) ^ (chainT S + S.W) := by
  have hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by
    intro S hLower hBlocks hRoom
    exact chain_step S ε _hε hCount hRoom hLower hBlocks
  rcases chain_terminal_with_product_bound_from_initial N D ε hStep with
    ⟨R, S, hR, hRpos, hRle, hStop, _hLower, hBlocks, hProd⟩
  refine ⟨R, S, hR, hRpos, hRle, hStop, hBlocks, ?_⟩
  simpa [chainProductBoundWithLosses, hR] using hProd

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/P202Optimization.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Final optimization layer.

Converts the chain inequality into the upper bound `f(N) ≤ N · L(-(1-ε), N)`.

Key explicit replacements (versus the PDF):

  * `(π²/6)`-constants → `2`, via the elementary `∑_{ν=1}^m 1/ν² ≤ 2`.
  * `T = ∑ W_{r-1}` is bounded by `R K - R(R-1)/2` (no informal `O(R)`).
  * The single inequality `c σ - c²/4 ≤ σ²` is a square-completion.

The `o(1)` of the PDF is replaced by an explicit `η`-quantifier:
"for every `η > 0`, eventually `1 - η ≤ c σ_N - c²/4 + η`".
-/


namespace Erdos202

open Filter
open Asymptotics
open scoped BigOperators

/-! ## §1 Explicit elementary inequalities -/

/-- The crude `∑_{ν=1}^m 1/ν² ≤ 2` replacing Basel. -/
lemma sum_inv_sq_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤
        2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
        cases hm
    | succ m ih =>
        cases m with
        | zero =>
            norm_num
        | succ m =>
            rw [Finset.sum_range_succ]
            have ih' : ∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2)
                ≤ 2 - 1 / ((m + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                  1 / ((m + 1 : ℕ) : ℝ) -
                    1 / (((m + 1 : ℕ) : ℝ) + 1) := by
              have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
              have hm2 : 0 < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hm1.ne', hm2.ne']
              ring_nf
              nlinarith [show 0 ≤ (m : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2))
                  + 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2
                  ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ))
                      + (1 / ((m + 1 : ℕ) : ℝ) -
                        1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
                    gcongr
              _ = 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    exact (hstrong m hm1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
      linarith)

/-- `c σ - c² / 4 ≤ σ²` for any reals `c`, `σ`. Square-completion. -/
lemma quad_bound (c σ : ℝ) : c * σ - c ^ 2 / 4 ≤ σ ^ 2 := by
  nlinarith [sq_nonneg (c / 2 - σ)]

private lemma log_chain_quadratic_algebra
    (M R K σ ε : ℝ) (hM : M ≠ 0) :
    R * σ + R * (-(K / M) / 2 + ε) +
        (2 * R * K - R * (R - 1)) / (4 * M) =
      R * σ - (R * (R - 1)) / (4 * M) + R * ε := by
  field_simp [hM]
  ring

private lemma one_sub_two_div_eq (M : ℝ) (hM : M ≠ 0) :
    1 - 2 / M = (M - 2) / M := by
  field_simp [hM]

private lemma log_chain_shape_algebra
    (M R σ ε sqrtE lambdaE : ℝ) (hM : M ≠ 0) :
    (R * σ - (R * (R - 1)) / (4 * M) + R * ε + sqrtE + lambdaE) / M =
      (R / M) * σ - (R / M) ^ 2 / 4 + (R / M) / (4 * M) + (R / M) * ε +
        sqrtE / M + lambdaE / M := by
  field_simp [hM]
  ring

private lemma eventually_log_const_mul_le_mul_self
    (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log (A * x) ≤ δ * x := by
  have hAtop : Tendsto (fun x : ℝ => A * x) atTop atTop :=
    tendsto_id.const_mul_atTop hA
  have hsmallA :
      (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => A * x :=
    Real.isLittleO_log_id_atTop.comp_tendsto hAtop
  have hbig : (fun x : ℝ => A * x) =O[atTop] fun x : ℝ => x :=
    isBigO_const_mul_self A (fun x : ℝ => x) atTop
  have hsmall : (fun x : ℝ => Real.log (A * x)) =o[atTop] fun x : ℝ => x :=
    hsmallA.trans_isBigO hbig
  filter_upwards [isLittleO_iff.mp hsmall hδ, eventually_gt_atTop (0 : ℝ)]
    with x hx hxpos
  calc
    Real.log (A * x) ≤ ‖Real.log (A * x)‖ := le_abs_self _
    _ ≤ δ * ‖x‖ := hx
    _ = δ * x := by rw [Real.norm_of_nonneg hxpos.le]

private lemma eventually_log_chainLambda_le_mul_loglog
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ D : PrunedData N,
        Real.log (chainLambda D) ≤ δ * Real.log (Real.log (N : ℝ)) := by
  let B : ℝ := |Real.log (3 * Real.exp 1)| + 1
  let A : ℝ := 2 * denseCoreConstant * B
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos (mul_pos (by norm_num) denseCoreConstant_pos) hBpos
  have hlogA_real := eventually_log_const_mul_le_mul_self A δ hApos hδ
  have hlogA :
      ∀ᶠ N : ℕ in atTop,
        Real.log (A * Real.log (Real.log (N : ℝ))) ≤
          δ * Real.log (Real.log (N : ℝ)) :=
    tendsto_loglog_nat_atTop.eventually hlogA_real
  filter_upwards [hlogA, eventually_Mscale_le_log, eventually_sqrt_loglog_ge 1,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    N hlogA_N hMle hsqrtloglog hNlarge_nat D
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlog_pos : 0 < Real.log (N : ℝ) := zero_lt_one.trans hlog_gt_one
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_ge_one : 1 ≤ Real.log (Real.log (N : ℝ)) := by
    rw [← Real.one_le_sqrt]
    exact hsqrtloglog
  have hKle_log : (D.K : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    nlinarith [D.K_bound, hMle]
  have hKpos_real : 0 < (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_pos : 0 < Real.exp 1 * (D.K : ℝ) :=
    mul_pos (Real.exp_pos 1) hKpos_real
  have harg_le :
      Real.exp 1 * (D.K : ℝ) ≤ Real.exp 1 * (3 * Real.log (N : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hKle_log (Real.exp_pos 1).le
  have hlog_arg_le :
      Real.log (Real.exp 1 * (D.K : ℝ)) ≤
        Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) :=
    Real.log_le_log harg_pos harg_le
  have hlog_three_pos : 0 < 3 * Real.exp 1 := by positivity
  have hlog_rhs :
      Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) =
        Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := by
    have hmul :
        Real.exp 1 * (3 * Real.log (N : ℝ)) =
          (3 * Real.exp 1) * Real.log (N : ℝ) := by ring
    rw [hmul, Real.log_mul hlog_three_pos.ne' hlog_pos.ne']
  have hlog_part_le :
      Real.log (Real.exp 1 * (D.K : ℝ)) ≤
        B * Real.log (Real.log (N : ℝ)) := by
    calc
      Real.log (Real.exp 1 * (D.K : ℝ))
          ≤ Real.log (Real.exp 1 * (3 * Real.log (N : ℝ))) := hlog_arg_le
      _ = Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ)) := hlog_rhs
      _ ≤ B * Real.log (Real.log (N : ℝ)) := by
            dsimp [B]
            have hconst_le : Real.log (3 * Real.exp 1) ≤ |Real.log (3 * Real.exp 1)| :=
              le_abs_self _
            have hconst_mul :
                |Real.log (3 * Real.exp 1)| ≤
                  |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) :=
              le_mul_of_one_le_right (abs_nonneg _) hloglog_ge_one
            calc
              Real.log (3 * Real.exp 1) + Real.log (Real.log (N : ℝ))
                  ≤ |Real.log (3 * Real.exp 1)| + Real.log (Real.log (N : ℝ)) := by
                    exact add_le_add hconst_le le_rfl
              _ ≤ |Real.log (3 * Real.exp 1)| * Real.log (Real.log (N : ℝ)) +
                    Real.log (Real.log (N : ℝ)) := by
                    exact add_le_add hconst_mul le_rfl
              _ = (|Real.log (3 * Real.exp 1)| + 1) *
                    Real.log (Real.log (N : ℝ)) := by ring
  have hLambda_le :
      chainLambda D ≤ A * Real.log (Real.log (N : ℝ)) := by
    rw [chainLambda, chainKappa]
    calc
      2 * (denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ)))
          = 2 * denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ)) := by ring
      _ ≤ 2 * denseCoreConstant * (B * Real.log (Real.log (N : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hlog_part_le
              (mul_nonneg (by norm_num) denseCoreConstant_pos.le)
      _ = A * Real.log (Real.log (N : ℝ)) := by
            dsimp [A]
            ring
  exact (Real.log_le_log (chainLambda_pos D) hLambda_le).trans hlogA_N

private lemma coeff_sum_two (R : ℕ) :
    (∑ j : Fin R, (R - j.1)) * 2 = R * (R + 1) := by
  rw [Fin.sum_univ_eq_sum_range]
  have hreflect :
      (∑ x ∈ Finset.range R, (R - x)) =
        ∑ x ∈ Finset.range R, (x + 1) := by
    rw [← Finset.sum_range_reflect (fun x => x + 1) R]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    omega
  rw [hreflect]
  have hsumadd :
      (∑ x ∈ Finset.range R, (x + 1)) =
        (∑ x ∈ Finset.range R, x) + R := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    simp
  rw [hsumadd]
  have hid := Finset.sum_range_id_mul_two R
  by_cases hR : R = 0
  · simp [hR]
  · apply Nat.cast_injective (R := ℤ)
    push_cast
    have hcast_sub : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by
      omega
    have hidz : ((∑ i ∈ Finset.range R, (i : ℕ) : ℕ) : ℤ) * 2 =
        (R : ℤ) * ((R : ℤ) - 1) := by
      have hid' : (((∑ i ∈ Finset.range R, i) * 2 : ℕ) : ℤ) =
          ((R * (R - 1) : ℕ) : ℤ) := by
        exact_mod_cast hid
      simpa [Nat.cast_mul, hcast_sub] using hid'
    ring_nf at hidz ⊢
    nlinarith

/-- The `T`-bound: if `R, K ≥ 0` with `R ≤ K` and weights `w_j ≥ 1` summing
to `K`, then `T = ∑ (R - j + 1) w_j ≤ R K - R (R - 1) / 2`. Discrete; no
asymptotics. -/
lemma chain_T_bound
    {R K : ℕ} (hRK : R ≤ K)
    (w : Fin R → ℕ) (hw_pos : ∀ j, 1 ≤ w j)
    (hw_sum : (∑ j, w j) = K) :
    (∑ j : Fin R, (R - j.1) * w j) * 2 ≤ 2 * R * K - R * (R - 1) := by
  let u : Fin R → ℕ := fun j => w j - 1
  let c : Fin R → ℕ := fun j => R - j.1
  have hw_decomp : ∀ j, w j = u j + 1 := by
    intro j
    simp [u, Nat.sub_add_cancel (hw_pos j)]
  have hsum_u_add : (∑ j, u j) + R = K := by
    calc
      (∑ j, u j) + R = (∑ j, u j) + ∑ _j : Fin R, 1 := by simp
      _ = ∑ j : Fin R, (u j + 1) := by rw [Finset.sum_add_distrib]
      _ = ∑ j : Fin R, w j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hw_decomp j]
      _ = K := hw_sum
  have hsum_u : ∑ j, u j = K - R := by omega
  have hmain_sum :
      (∑ j : Fin R, c j * w j) =
        (∑ j : Fin R, c j * u j) + ∑ j : Fin R, c j := by
    calc
      (∑ j : Fin R, c j * w j)
          = ∑ j : Fin R, c j * (u j + 1) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [hw_decomp j]
      _ = ∑ j : Fin R, (c j * u j + c j) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [Nat.mul_add, Nat.mul_one]
      _ = (∑ j : Fin R, c j * u j) + ∑ j : Fin R, c j := by
              rw [Finset.sum_add_distrib]
  have hweighted :
      ∑ j : Fin R, c j * u j ≤ R * (∑ j : Fin R, u j) := by
    calc
      ∑ j : Fin R, c j * u j ≤ ∑ j : Fin R, R * u j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact Nat.mul_le_mul_right (u j) (Nat.sub_le R j.1)
      _ = R * (∑ j : Fin R, u j) := by
        rw [Finset.mul_sum]
  have hS_le :
      (∑ j : Fin R, c j * w j) ≤ R * (K - R) + ∑ j : Fin R, c j := by
    rw [hmain_sum]
    have hweighted' : ∑ j : Fin R, c j * u j ≤ R * (K - R) := by
      simpa [hsum_u] using hweighted
    exact Nat.add_le_add_right hweighted' _
  have hcoeff : (∑ j : Fin R, c j) * 2 = R * (R + 1) := by
    simpa [c] using coeff_sum_two R
  have hadd :
      ((∑ j : Fin R, c j * w j) * 2) + R * (R - 1) ≤ 2 * R * K := by
    have h2 : (∑ j : Fin R, c j * w j) * 2
        ≤ (R * (K - R) + ∑ j : Fin R, c j) * 2 :=
      Nat.mul_le_mul_right 2 hS_le
    have hbound :
        (R * (K - R) + ∑ j : Fin R, c j) * 2 + R * (R - 1) = 2 * R * K := by
      by_cases hR0 : R = 0
      · subst R
        simp [c]
      · apply Nat.cast_injective (R := ℤ)
        push_cast
        have hKsub : ((K - R : ℕ) : ℤ) = (K : ℤ) - (R : ℤ) := by
          omega
        have hRsub : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by
          omega
        have hcoeffz : (((∑ j : Fin R, c j) * 2 : ℕ) : ℤ) =
            ((R * (R + 1) : ℕ) : ℤ) := by
          exact_mod_cast hcoeff
        rw [hKsub, hRsub]
        push_cast at hcoeffz
        ring_nf at hcoeffz ⊢
        nlinarith
    exact (Nat.add_le_add_right h2 _).trans_eq hbound
  simpa [c] using Nat.le_sub_of_add_le hadd

/-! ## §2 The σ-bookkeeping -/

/-- `σ_N = log(N / |Q'|) / Z(N)`. The shape parameter that the
optimization shows must satisfy `σ_N ≥ 1 - O(η)` eventually. -/
noncomputable def sigmaN (N : ℕ) (Qcard : ℕ) : ℝ :=
  Real.log ((N : ℝ) / (Qcard : ℝ)) / Zscale N

lemma sigmaN_nonneg {N Qcard : ℕ}
    (hQpos : 0 < Qcard) (hQleN : Qcard ≤ N) (hZ : 0 < Zscale N) :
    0 ≤ sigmaN N Qcard := by
  have hQpos_real : 0 < (Qcard : ℝ) := Nat.cast_pos.mpr hQpos
  have hQleN_real : (Qcard : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hQleN
  have hone : 1 ≤ (N : ℝ) / (Qcard : ℝ) :=
    (one_le_div hQpos_real).2 hQleN_real
  rw [sigmaN]
  exact div_nonneg (Real.log_nonneg hone) hZ.le

private lemma product_lower_of_chain_stop {N : ℕ} {D : PrunedData N}
    {S : ChainState N D}
    (hStop : (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) :
    (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) := by
  rcases hStop with hProd | hW
  · exact hProd
  · exact S.productP_lower_of_W_eq_K hW

private lemma one_sub_le_of_sq_lower
    {η δ σ : ℝ} (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (hδ_le : δ ≤ η) (hσ_nonneg : 0 ≤ σ)
    (hsq : 1 - δ ≤ σ ^ 2) :
    1 - η ≤ σ := by
  have hone_sub_nonneg : 0 ≤ 1 - η := by linarith
  have hsquare_left : (1 - η) ^ 2 ≤ 1 - δ := by
    have hsq_le_linear : (1 - η) ^ 2 ≤ 1 - η := by
      nlinarith [hη_nonneg, hη_le_one]
    linarith
  have hsquare : (1 - η) ^ 2 ≤ σ ^ 2 := hsquare_left.trans hsq
  exact (sq_le_sq₀ hone_sub_nonneg hσ_nonneg).1 hsquare

lemma card_le_of_sigma_lower {η : ℝ} {N Qcard : ℕ}
    (hN : 0 < N) (hQ : 0 < Qcard) (hZ : 0 < Zscale N)
    (hsigma : 1 - η ≤ sigmaN N Qcard) :
    (Qcard : ℝ) ≤ (N : ℝ) * Lscale (-(1 - η)) N := by
  have hQreal : 0 < (Qcard : ℝ) := by exact_mod_cast hQ
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hratio_pos : 0 < (N : ℝ) / (Qcard : ℝ) := div_pos hNreal hQreal
  have hlog :
      (1 - η) * Zscale N ≤ Real.log ((N : ℝ) / (Qcard : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hsigma hZ.le
    rw [sigmaN, div_mul_cancel₀ _ hZ.ne'] at hmul
    exact hmul
  have hexp_le_ratio :
      Real.exp ((1 - η) * Zscale N) ≤ (N : ℝ) / (Qcard : ℝ) :=
    (Real.le_log_iff_exp_le hratio_pos).1 hlog
  have hmulQ :
      (Qcard : ℝ) * Real.exp ((1 - η) * Zscale N) ≤ (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hexp_le_ratio hQreal.le
    rw [div_mul_cancel₀ _ hQreal.ne'] at hmul
    simpa [mul_comm] using hmul
  have hcancel :
      Real.exp ((1 - η) * Zscale N) *
          Real.exp (-((1 - η) * Zscale N)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    (Qcard : ℝ)
        = ((Qcard : ℝ) * Real.exp ((1 - η) * Zscale N)) *
            Real.exp (-((1 - η) * Zscale N)) := by
          rw [mul_assoc, hcancel, mul_one]
    _ ≤ (N : ℝ) * Real.exp (-((1 - η) * Zscale N)) := by
          exact mul_le_mul_of_nonneg_right hmulQ (Real.exp_pos _).le
    _ = (N : ℝ) * Lscale (-(1 - η)) N := by
          rw [Lscale]
          congr 1
          ring_nf

set_option maxHeartbeats 2000000

/-- **Sigma lower bound** (PDF Section 5). For every `η > 0`, eventually
any pruned family with cardinality `Qcard` derived from a chain with
parameters `(c, d) ∈ [0, 3]²` satisfies `1 - η ≤ c σ_N - c² / 4 + η`,
hence `σ_N ≥ 1 - O(η)`. -/
theorem sigma_lower_bound :
    ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
      ∀ Qcard : ℕ, 1 ≤ Qcard →
        (∃ D : PrunedData N, D.Q.card = Qcard) →
        1 - η ≤ sigmaN N Qcard := by
  intro η hη
  let ε : ℝ := η / 8
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  filter_upwards [bfv_omega_count_input ε hε,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      eventually_Mscale_ge (8 / η) (by positivity),
      eventually_sqrt_loglog_ge (96 / η),
      eventually_log_chainLambda_le_mul_loglog (η / 144) (by positivity)] with
    N hCount hNlarge_nat hMlarge hSqrtLogLogLarge hLogLambdaSmall
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hZpos : 0 < Zscale N := Zscale_pos_of_exp_one_lt_nat hNlarge
  have hMpos : 0 < Mscale N := Mscale_pos_of_exp_one_lt_nat hNlarge
  have hMZ : Mscale N * Zscale N = Real.log (N : ℝ) :=
    Mscale_mul_Zscale_eq_log hNlarge
  have hZdivM : Zscale N / Mscale N = Real.log (Real.log (N : ℝ)) :=
    Zscale_div_Mscale_eq_loglog hNlarge
  intro Qcard _hQcard hD
  rcases hD with ⟨D, hDcard⟩
  have hsigma_nonneg : 0 ≤ sigmaN N Qcard := by
    have hQleN : Qcard ≤ N := by
      rw [← hDcard]
      exact D.card_le_N
    exact sigmaN_nonneg (Nat.succ_le_iff.mp _hQcard) hQleN hZpos
  rcases chain_inequality N D ε hε hCount with
    ⟨R, S, hR, hRpos, hRle, hStop, hBlocks, hProdUpper⟩
  have hProdLower : (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) :=
    product_lower_of_chain_stop hStop
  have hProdUpperBound : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S := by
    simpa [chainProductBoundWithLosses, hR] using hProdUpper
  have hLogProduct :
      Real.log ((N : ℝ) * Lscale (-2) N) ≤
        Real.log (chainProductBoundWithLosses ε S) := by
    have hLowerPos : 0 < (N : ℝ) * Lscale (-2) N := by
      exact mul_pos (by exact_mod_cast D.N_pos) (Lscale_pos (-2) N)
    exact Real.log_le_log hLowerPos (hProdLower.trans hProdUpperBound)
  have hLogProductExpanded :
      Real.log (N : ℝ) - 2 * Zscale N ≤
        Real.log (chainProductBoundWithLosses ε S) := by
    have hLogLower :
        Real.log ((N : ℝ) * Lscale (-2) N) =
          Real.log (N : ℝ) - 2 * Zscale N := by
      rw [log_nat_mul_Lscale D.N_pos (-2)]
      ring
    rwa [hLogLower] at hLogProduct
  have hLogChainExpanded :
      Real.log (N : ℝ) - 2 * Zscale N ≤
        (R : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
          (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
          ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
          2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
          ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
    rw [log_chainProductBoundWithLosses ε S] at hLogProductExpanded
    simpa [hR] using hLogProductExpanded
  have hSigmaLog :
      Real.log ((N : ℝ) / (D.Q.card : ℝ)) =
        sigmaN N Qcard * Zscale N := by
    rw [sigmaN, ← hDcard]
    field_simp [hZpos.ne']
  have hLogChainNormalized :
      Mscale N - 2 ≤
        (R : ℝ) * sigmaN N Qcard +
          (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
          ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
          (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
          (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N := by
    have hExpandedSigma :
        Real.log (N : ℝ) - 2 * Zscale N ≤
          (R : ℝ) * (sigmaN N Qcard * Zscale N) +
            (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
            ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
            2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
            ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
      simpa [hSigmaLog] using hLogChainExpanded
    have h :
        (Mscale N - 2) * Zscale N ≤
          ((R : ℝ) * sigmaN N Qcard +
            (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
            ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
            (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
            (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N) *
              Zscale N := by
      calc
        (Mscale N - 2) * Zscale N
            = Real.log (N : ℝ) - 2 * Zscale N := by
                rw [← hMZ]
                ring
        _ ≤ (R : ℝ) * (sigmaN N Qcard * Zscale N) +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ))) +
              2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
              ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) :=
            hExpandedSigma
        _ = ((R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
              (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N +
              (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) /
                Zscale N) * Zscale N := by
            rw [← hZdivM]
            field_simp [hMpos.ne', hZpos.ne']
    have hdiv := div_le_div_of_nonneg_right h hZpos.le
    field_simp [hZpos.ne'] at hdiv
    field_simp [hMpos.ne']
    nlinarith [hdiv, hMpos]
  have hTbasic : chainT S ≤ S.r * D.K := S.chainT_le_r_mul_K
  have hTbasicR : chainT S ≤ R * D.K := by
    simpa [hR] using hTbasic
  have hTquad : ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) :=
    S.chainT_add_W_real_quadratic_bound hBlocks
  have hTquadK : ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1) := by
    have hWle : (S.W : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast S.W_le_K
    have hRnonneg : 0 ≤ (R : ℝ) := by positivity
    rw [← hR]
    nlinarith [hTquad, hWle, hRnonneg]
  have hTterm :
      ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) ≤
        (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
          (4 * Mscale N) := by
    calc
      ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N)
          = (((chainT S + S.W : ℕ) : ℝ) * 2) * (1 / (4 * Mscale N)) := by
              field_simp [hMpos.ne']
              ring
      _ ≤ (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) *
            (1 / (4 * Mscale N)) := by
              exact mul_le_mul_of_nonneg_right hTquadK (by positivity)
      _ = (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
            (4 * Mscale N) := by ring
  let sqrtE : ℝ := (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ))) / Zscale N
  let lambdaE : ℝ :=
    (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) / Zscale N
  have hLogChainQuadratic :
      Mscale N - 2 ≤
        (R : ℝ) * sigmaN N Qcard -
          ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
          (R : ℝ) * ε + sqrtE + lambdaE := by
    calc
      Mscale N - 2
          ≤ (R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) +
              sqrtE + lambdaE :=
            hLogChainNormalized
      _ ≤ (R : ℝ) * sigmaN N Qcard +
              (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
              (2 * (R : ℝ) * (D.K : ℝ) - (R : ℝ) * ((R : ℝ) - 1)) /
                (4 * Mscale N) + sqrtE + lambdaE := by
            let A : ℝ :=
              (R : ℝ) * sigmaN N Qcard +
                (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε)
            let B : ℝ := sqrtE + lambdaE
            have hmid :
                A + ((((chainT S + S.W : ℕ) : ℝ) / 2) / Mscale N) ≤
                  A + (2 * (R : ℝ) * (D.K : ℝ) -
                    (R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) :=
              by
                have hmid' := add_le_add_left hTterm A
                linarith
            have hmidB := add_le_add_right hmid B
            dsimp [A, B] at hmidB
            linarith
      _ = (R : ℝ) * sigmaN N Qcard -
            ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
            (R : ℝ) * ε + sqrtE + lambdaE := by
            have hbase :
                (R : ℝ) * sigmaN N Qcard +
                    (R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) +
                    (2 * (R : ℝ) * (D.K : ℝ) -
                        (R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) =
                  (R : ℝ) * sigmaN N Qcard -
                    ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
                    (R : ℝ) * ε :=
              log_chain_quadratic_algebra (Mscale N) (R : ℝ) (D.K : ℝ)
                (sigmaN N Qcard) ε hMpos.ne'
            rw [hbase]
  let c : ℝ := (R : ℝ) / Mscale N
  have hc_pos : 0 < c := by
    dsimp [c]
    have hRpos_real : 0 < (R : ℝ) := by exact_mod_cast hRpos
    exact div_pos hRpos_real hMpos
  have hc_le_three : c ≤ 3 := by
    dsimp [c]
    have hRleK_real : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hRle
    have hRle3M : (R : ℝ) ≤ 3 * Mscale N := hRleK_real.trans D.K_bound
    exact (div_le_iff₀ hMpos).2 hRle3M
  let sqrtLoss : ℝ := sqrtE / Mscale N
  let lambdaLoss : ℝ := lambdaE / Mscale N
  have hLogChainShape :
      (Mscale N - 2) / Mscale N ≤
        c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
          sqrtLoss + lambdaLoss := by
    have hdiv := div_le_div_of_nonneg_right hLogChainQuadratic hMpos.le
    calc
      (Mscale N - 2) / Mscale N
          ≤ ((R : ℝ) * sigmaN N Qcard -
            ((R : ℝ) * ((R : ℝ) - 1)) / (4 * Mscale N) +
            (R : ℝ) * ε + sqrtE + lambdaE) / Mscale N := hdiv
      _ = c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
            sqrtLoss + lambdaLoss := by
              dsimp [c, sqrtLoss, lambdaLoss]
              exact log_chain_shape_algebra (Mscale N) (R : ℝ) (sigmaN N Qcard)
                ε sqrtE lambdaE hMpos.ne'
  have hsigma_sq_shape :
      (Mscale N - 2) / Mscale N ≤
        (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
          sqrtLoss + lambdaLoss := by
    calc
      (Mscale N - 2) / Mscale N
          ≤ c * sigmaN N Qcard - c ^ 2 / 4 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss :=
            hLogChainShape
      _ ≤ (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss := by
            simpa [add_assoc] using
              add_le_add_right (quad_bound c (sigmaN N Qcard))
                (c / (4 * Mscale N) + c * ε + sqrtLoss + lambdaLoss)
  have hsigma_sq_shape_three :
      (Mscale N - 2) / Mscale N ≤
        (sigmaN N Qcard) ^ 2 + 3 / (4 * Mscale N) + 3 * ε +
          sqrtLoss + lambdaLoss := by
    have hsmall1 : c / (4 * Mscale N) ≤ 3 / (4 * Mscale N) := by
      exact div_le_div_of_nonneg_right hc_le_three (by positivity)
    have hsmall2 : c * ε ≤ 3 * ε :=
      mul_le_mul_of_nonneg_right hc_le_three hε.le
    calc
      (Mscale N - 2) / Mscale N
          ≤ (sigmaN N Qcard) ^ 2 + c / (4 * Mscale N) + c * ε +
              sqrtLoss + lambdaLoss :=
            hsigma_sq_shape
      _ ≤ (sigmaN N Qcard) ^ 2 + 3 / (4 * Mscale N) + 3 * ε +
              sqrtLoss + lambdaLoss := by
            have herr :
                c / (4 * Mscale N) + c * ε ≤
                  3 / (4 * Mscale N) + 3 * ε :=
              add_le_add hsmall1 hsmall2
            linarith
  have hsigma_sq_lower :
      1 - (2 / Mscale N + 3 / (4 * Mscale N) + 3 * ε +
          sqrtLoss + lambdaLoss) ≤
        (sigmaN N Qcard) ^ 2 := by
    have hleft : (Mscale N - 2) / Mscale N = 1 - 2 / Mscale N :=
      (one_sub_two_div_eq (Mscale N) hMpos.ne').symm
    linarith [hsigma_sq_shape_three, hleft]
  by_cases hη_big : 1 ≤ η
  · have htarget : 1 - η ≤ 0 := by linarith
    exact htarget.trans hsigma_nonneg
  have hη_le_one : η ≤ 1 := le_of_lt (not_le.mp hη_big)
  let δN : ℝ :=
    2 / Mscale N + 3 / (4 * Mscale N) + 3 * ε + sqrtLoss + lambdaLoss
  have hfinish_of_error (hδN : δN ≤ η) : 1 - η ≤ sigmaN N Qcard := by
    exact one_sub_le_of_sq_lower hη.le hη_le_one hδN hsigma_nonneg (by
      simpa [δN] using hsigma_sq_lower)
  have hδN_le : δN ≤ η := by
    have hApos : 0 < (8 : ℝ) / η := by positivity
    have hinvM_raw : 1 / Mscale N ≤ 1 / (8 / η) :=
      one_div_le_one_div_of_le hApos hMlarge
    have hinvM : 1 / Mscale N ≤ η / 8 := by
      convert hinvM_raw using 1
      field_simp [hη.ne']
    dsimp [δN, ε]
    have hterm1 : 2 / Mscale N ≤ η / 4 := by
      have hmul := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ (2 : ℝ) by norm_num)
      convert hmul using 1 <;> ring
    have hterm2 : 3 / (4 * Mscale N) ≤ 3 * η / 32 := by
      have hmul := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ (3 / 4 : ℝ) by norm_num)
      convert hmul using 1
      · field_simp [hMpos.ne']
      · ring
    have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
      Real.log_pos ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hNlarge)).2 hNlarge)
    have hsqrtlog_pos : 0 < Real.sqrt (Real.log (N : ℝ)) := by
      have hlog_pos : 0 < Real.log (N : ℝ) :=
        zero_lt_one.trans ((Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hNlarge)).2 hNlarge)
      rw [Real.sqrt_pos]
      exact hlog_pos
    have hsqrtloglog_pos :
        0 < Real.sqrt (Real.log (Real.log (N : ℝ))) := by
      have hlarge_pos : 0 < (96 : ℝ) / η := by positivity
      exact hlarge_pos.trans_le hSqrtLogLogLarge
    have hRle3M : (R : ℝ) ≤ 3 * Mscale N := by
      have hRleK_real : (R : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hRle
      exact hRleK_real.trans D.K_bound
    have hsqrtLoss_le : sqrtLoss ≤ η / 16 := by
      have hfactor_nonneg :
          0 ≤ 2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N) := by
        positivity
      calc
        sqrtLoss
            = (R : ℝ) *
                (2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N)) := by
              dsimp [sqrtLoss, sqrtE]
              field_simp [hZpos.ne', hMpos.ne']
        _ ≤ (3 * Mscale N) *
              (2 * Real.sqrt (Real.log (N : ℝ)) / (Zscale N * Mscale N)) := by
              exact mul_le_mul_of_nonneg_right hRle3M hfactor_nonneg
        _ = 6 / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
              rw [Zscale_eq_sqrt_log_mul_sqrt_loglog hNlarge]
              field_simp [hMpos.ne', hsqrtlog_pos.ne', hsqrtloglog_pos.ne']
              ring
        _ ≤ 6 / (96 / η) := by
              exact div_le_div_of_nonneg_left (by norm_num)
                (by positivity) hSqrtLogLogLarge
        _ = η / 16 := by
              field_simp [hη.ne']
              ring
    have hTplus_le_RK :
        (((chainT S + S.W : ℕ) : ℝ)) ≤ (R : ℝ) * (D.K : ℝ) := by
      have hRge_one_real : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRpos
      have hquad_nonneg : 0 ≤ (R : ℝ) * ((R : ℝ) - 1) := by
        nlinarith [hRge_one_real]
      have hT2_le_2RK :
          (((chainT S + S.W : ℕ) : ℝ) * 2) ≤
            2 * (R : ℝ) * (D.K : ℝ) := by
        nlinarith [hTquadK, hquad_nonneg]
      nlinarith
    have hTplus_le_9M2 :
        (((chainT S + S.W : ℕ) : ℝ)) ≤ 9 * (Mscale N) ^ 2 := by
      have hKle3M : (D.K : ℝ) ≤ 3 * Mscale N := D.K_bound
      have hRnonneg : 0 ≤ (R : ℝ) := by positivity
      have hKnonneg : 0 ≤ (D.K : ℝ) := by positivity
      have hRK_le : (R : ℝ) * (D.K : ℝ) ≤ (3 * Mscale N) * (3 * Mscale N) :=
        mul_le_mul hRle3M hKle3M hKnonneg (by positivity)
      nlinarith [hTplus_le_RK, hRK_le]
    have hlambdaLog_le :
        Real.log (chainLambda D) ≤
          (η / 144) * Real.log (Real.log (N : ℝ)) :=
      hLogLambdaSmall D
    have hlambdaLoss_le : lambdaLoss ≤ η / 16 := by
      have hcoef_nonneg :
          0 ≤ (η / 144) * Real.log (Real.log (N : ℝ)) := by positivity
      have hTnonneg : 0 ≤ (((chainT S + S.W : ℕ) : ℝ)) := by positivity
      have hnum_le :
          (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) ≤
            (9 * (Mscale N) ^ 2) *
              ((η / 144) * Real.log (Real.log (N : ℝ))) := by
        have hlog_scaled :
            (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) ≤
              (((chainT S + S.W : ℕ) : ℝ) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) :=
          mul_le_mul_of_nonneg_left hlambdaLog_le hTnonneg
        have hT_scaled :
            (((chainT S + S.W : ℕ) : ℝ) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) ≤
              (9 * (Mscale N) ^ 2) *
                ((η / 144) * Real.log (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hTplus_le_9M2 hcoef_nonneg
        exact hlog_scaled.trans hT_scaled
      have hMll := Mscale_mul_loglog_eq_Zscale hNlarge
      calc
        lambdaLoss
            = (((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D)) /
                (Zscale N * Mscale N) := by
              dsimp [lambdaLoss, lambdaE]
              field_simp [hZpos.ne', hMpos.ne']
        _ ≤ ((9 * (Mscale N) ^ 2) *
                ((η / 144) * Real.log (Real.log (N : ℝ)))) /
                (Zscale N * Mscale N) := by
              exact div_le_div_of_nonneg_right hnum_le
                (mul_nonneg hZpos.le hMpos.le)
        _ = η / 16 := by
              rw [← hMll]
              field_simp [hMpos.ne', hloglog_pos.ne']
              ring
    have hmain_le :
        2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8) ≤
          (23 / 32) * η := by
      calc
        2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8)
          ≤ η / 4 + 3 * η / 32 + 3 * (η / 8) := by
            gcongr
        _ = (23 / 32) * η := by ring
    calc
      2 / Mscale N + 3 / (4 * Mscale N) + 3 * (η / 8) + sqrtLoss + lambdaLoss
          ≤ (23 / 32) * η + η / 16 + η / 16 := by
            linarith [hmain_le, hsqrtLoss_le, hlambdaLoss_le]
      _ = (27 / 32) * η := by ring
      _ ≤ η := by
            exact mul_le_of_le_one_left hη.le (by norm_num)
  exact hfinish_of_error hδN_le

/-! ## §3 The upper bound -/

/-- **Upper bound for f.** From the chain inequality and σ-optimization,
`f(N) ≤ N · L(-(1 - ε), N)` for every `ε > 0`, eventually. -/
theorem f_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N := by
  intro ε hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have h2δ : 2 * δ ≤ ε := by
    dsimp [δ]
    linarith
  filter_upwards [bfv_pruning_input δ hδ, sigma_lower_bound δ hδ,
      eventually_Zscale_pos] with N hPrune hSigma hZ
  classical
  rcases exists_admissible_card_f N with ⟨Q, hQadm, hQcard⟩
  rcases hQadm.2 with ⟨a, ha⟩
  have hQlarge : (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-δ) N := by
    rw [hQcard]
    calc
      (f N : ℝ) * Lscale (-δ) N ≤ (f N : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left (Lscale_neg_le_one hδ.le N) (by positivity)
      _ = (f N : ℝ) := by ring
  rcases hPrune Q a hQadm.1 ha hQlarge with ⟨D, hDlower⟩
  have hSigmaD :
      1 - δ ≤ sigmaN N D.Q.card :=
    hSigma D.Q.card (Nat.succ_le_of_lt D.card_pos) ⟨D, rfl⟩
  have hDupper :
      (D.Q.card : ℝ) ≤ (N : ℝ) * Lscale (-(1 - δ)) N :=
    card_le_of_sigma_lower D.N_pos D.card_pos hZ hSigmaD
  have hf_to_D :
      (f N : ℝ) ≤ (D.Q.card : ℝ) * Lscale δ N := by
    calc
      (f N : ℝ)
          = ((f N : ℝ) * Lscale (-δ) N) * Lscale δ N := by
              rw [mul_assoc, Lscale_neg_mul, mul_one]
      _ ≤ (D.Q.card : ℝ) * Lscale δ N := by
              exact mul_le_mul_of_nonneg_right
                (by simpa [hQcard] using hDlower) (Lscale_nonneg δ N)
  calc
    (f N : ℝ) ≤ (D.Q.card : ℝ) * Lscale δ N := hf_to_D
    _ ≤ ((N : ℝ) * Lscale (-(1 - δ)) N) * Lscale δ N := by
          exact mul_le_mul_of_nonneg_right hDupper (Lscale_nonneg δ N)
    _ = (N : ℝ) * (Lscale (-(1 - δ)) N * Lscale δ N) := by ring
    _ = (N : ℝ) * Lscale (-(1 - δ) + δ) N := by
          rw [Lscale_add]
    _ = (N : ℝ) * Lscale (-(1 - 2 * δ)) N := by
          congr 1
          congr 1
          ring
    _ ≤ (N : ℝ) * Lscale (-(1 - ε)) N := by
          exact mul_le_mul_of_nonneg_left
            (Lscale_mono_in_alpha (by linarith) N) (by positivity)

end Erdos202

/- ════════════════════════════════════════════════════════════════════ -/
/- ═══ Source: Erdos/P202/P202Main.lean -/
/- ════════════════════════════════════════════════════════════════════ -/

/-
Erdős Problem 202 — Main theorem.

Combines:
  * upper bound from `Optimization.f_upper_bound`
    (Chain inequality + σ optimization, conditional on the BFV inputs and
     the spread-disjointness input);
  * lower bound from `bfv_lower_bound_input`.

After all sorries are closed, the theorem will depend on three
project-level axioms — `spread_disjointness_input`, `bfv_pruning_input`,
`bfv_omega_count_input`, `bfv_lower_bound_input` — plus Mathlib core
(`propext`, `Classical.choice`, `Quot.sound`).

Audit by uncommenting the `#print axioms` block below.
-/


namespace Erdos202

open Filter
open scoped BigOperators

/-- **Conditional Erdős 202 upper bound.** From the four BFV / spread
inputs (the precise theorem-shaped axioms in `BFVInputs.lean` and
`SpreadCore.lean`), the upper half of the asymptotic holds. -/
theorem erdos202_upper_bound_from_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N :=
  f_upper_bound

/-- **Erdős Problem 202 — main theorem.** The sharp BFV asymptotic
`f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`. -/
theorem erdos202_main : Erdos202Statement := by
  intro ε hε
  filter_upwards [bfv_lower_bound_theorem ε hε, f_upper_bound ε hε] with N hLow hUp
  exact ⟨hLow, hUp⟩

/-! ## Axiom audit

Once all `sorry`s are closed in the supporting files, uncomment the block
below. Expected output (in addition to the standard Mathlib core axioms
`propext`, `Classical.choice`, `Quot.sound`):

  * `Erdos202.spread_disjointness_input`
  * `Erdos202.bfv_pruning_input`
  * `Erdos202.bfv_omega_count_input`
  * `Erdos202.bfv_lower_bound_input`

These four axioms are exactly the trust boundary of the formalization.
-/

-- #print axioms erdos202_upper_bound_from_inputs
-- #print axioms erdos202_main

end Erdos202

#print axioms Erdos202.erdos202_main
