/-
Erdős Problem 202 — Statement layer.

Defines residue classes, admissible families, the extremal function `f(N)`,
the BFV scale `L(α, N) = exp(α · sqrt(log N · log log N))`, and the sharp
asymptotic predicate `HasErdos202Asymptotic`.

Reference: PDF in `docs/`, BFV (Acta Arith.) for the unconditional bounds,
spread-core variant for the matching upper bound `f(N) = N · L(-(1+o(1)), N)`.
-/

import Mathlib

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
