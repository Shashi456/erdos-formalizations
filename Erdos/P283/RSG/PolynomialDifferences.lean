/-
Copyright (c) 2026

Finite-difference operators used in Graham's proof of complete polynomial
sequences.
-/

import Erdos.P283.RSG.CompleteSequences

namespace Erdos.P283.RSG

open Polynomial
open Filter
open fwdDiff

/-! ## Graham's fourth-step difference operator -/

/-- The affine polynomial `a * X + b`. -/
noncomputable def affinePoly (a b : ℚ) : ℚ[X] :=
  Polynomial.C a * Polynomial.X + Polynomial.C b

/-- Graham's difference operator `Δ f(x) = f(4x + 2) - f(4x)`. -/
noncomputable def Delta1 (f : ℚ[X]) : ℚ[X] :=
  f.comp (affinePoly 4 2) - f.comp (affinePoly 4 0)

/-- The `k`-fold iterate of Graham's difference operator. -/
noncomputable def Delta (k : ℕ) (f : ℚ[X]) : ℚ[X] :=
  (Delta1^[k]) f

/-- Signed offsets appearing in the expansion of `Delta k`.

An entry `(sgn, off)` represents the term
`sgn * f(4^k * x + off)`. Graham's base-4 construction keeps all coefficients
equal to `±1`, which is what later allows conversion to signed subset sums. -/
def deltaTerms : ℕ → List (ℤ × ℕ)
  | 0 => [(1, 0)]
  | k + 1 =>
      (deltaTerms k).map (fun p => (p.1, 2 * 4 ^ k + p.2)) ++
      (deltaTerms k).map (fun p => (-p.1, p.2))

noncomputable def deltaTermValue (k : ℕ) (f : ℚ[X]) (x : ℚ) (p : ℤ × ℕ) : ℚ :=
  (p.1 : ℚ) * f.eval ((4 ^ k : ℚ) * x + (p.2 : ℚ))

/-! ## Elementary structure of the `Delta` expansion -/

@[simp] lemma deltaTerms_length (k : ℕ) :
    (deltaTerms k).length = 2 ^ k := by
  induction k with
  | zero =>
      simp [deltaTerms]
  | succ k ih =>
      simp [deltaTerms, ih, pow_succ]
      ring

lemma deltaTerms_sign_eq_one_or_neg_one {k : ℕ} {p : ℤ × ℕ}
    (hp : p ∈ deltaTerms k) :
    p.1 = 1 ∨ p.1 = -1 := by
  induction k generalizing p with
  | zero =>
      simp [deltaTerms] at hp
      exact Or.inl (by simp [hp])
  | succ k ih =>
      simp only [deltaTerms, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact ih (p := q) hq
      · rcases ih (p := q) hq with hsgn | hsgn
        · right
          simp [hsgn]
        · left
          simp [hsgn]

lemma deltaTerms_offset_lt_pow_four {k : ℕ} {p : ℤ × ℕ}
    (hp : p ∈ deltaTerms k) :
    p.2 < 4 ^ k := by
  induction k generalizing p with
  | zero =>
      simp [deltaTerms] at hp
      simp [hp]
  | succ k ih =>
      simp only [deltaTerms, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · have hq_lt : q.2 < 4 ^ k := ih hq
        have hpow : 0 < 4 ^ k := pow_pos (by norm_num) k
        rw [pow_succ]
        nlinarith
      · have hq_lt : q.2 < 4 ^ k := ih hq
        have hpow : 0 < 4 ^ k := pow_pos (by norm_num) k
        rw [pow_succ]
        nlinarith

lemma deltaTerms_offset_even {k : ℕ} {p : ℤ × ℕ}
    (hp : p ∈ deltaTerms k) :
    ∃ a : ℕ, p.2 = 2 * a := by
  induction k generalizing p with
  | zero =>
      simp [deltaTerms] at hp
      refine ⟨0, ?_⟩
      simp [hp]
  | succ k ih =>
      simp only [deltaTerms, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · rcases ih (p := q) hq with ⟨a, ha⟩
        refine ⟨4 ^ k + a, ?_⟩
        rw [ha]
        ring
      · exact ih (p := q) hq

lemma deltaTerms_first_branch_offset_ge (k : ℕ) (p : ℤ × ℕ) :
    2 * 4 ^ k ≤ (2 * 4 ^ k + p.2 : ℕ) := by
  omega

lemma deltaTerms_second_branch_offset_lt_half {k : ℕ} {p : ℤ × ℕ}
    (hp : p ∈ deltaTerms k) :
    p.2 < 2 * 4 ^ k := by
  have h := deltaTerms_offset_lt_pow_four hp
  have hpow : 0 < 4 ^ k := pow_pos (by norm_num) k
  nlinarith

lemma deltaTerms_branch_disjoint (k : ℕ) :
    List.Disjoint
      ((deltaTerms k).map (fun p : ℤ × ℕ => (p.1, 2 * 4 ^ k + p.2)))
      ((deltaTerms k).map (fun p : ℤ × ℕ => (-p.1, p.2))) := by
  rw [List.disjoint_left]
  intro a ha hb
  simp only [List.mem_map] at ha hb
  rcases ha with ⟨p, hp, rfl⟩
  rcases hb with ⟨q, hq, hqeq⟩
  have hcoord : q.2 = 2 * 4 ^ k + p.2 := by
    exact congrArg Prod.snd hqeq
  have hq_lt : q.2 < 2 * 4 ^ k := deltaTerms_second_branch_offset_lt_half hq
  omega

lemma deltaTerms_nodup (k : ℕ) : (deltaTerms k).Nodup := by
  induction k with
  | zero =>
      simp [deltaTerms]
  | succ k ih =>
      simp only [deltaTerms]
      apply List.Nodup.append
      · refine ih.map ?_
        intro p q hpq
        rcases p with ⟨ps, po⟩
        rcases q with ⟨qs, qo⟩
        simp only at hpq
        simp only [Prod.mk.injEq] at hpq ⊢
        omega
      · refine ih.map ?_
        intro p q hpq
        rcases p with ⟨ps, po⟩
        rcases q with ⟨qs, qo⟩
        simp only [Prod.mk.injEq, neg_inj] at hpq ⊢
        exact hpq
      · exact deltaTerms_branch_disjoint k

lemma deltaTerms_offset_injective_on {k : ℕ} :
    ∀ {p q : ℤ × ℕ}, p ∈ deltaTerms k → q ∈ deltaTerms k → p.2 = q.2 → p = q := by
  induction k with
  | zero =>
      intro p q hp hq hpq
      simp [deltaTerms] at hp hq
      simp [hp, hq]
  | succ k ih =>
      intro p q hp hq hpq
      simp only [deltaTerms, List.mem_append, List.mem_map] at hp hq
      rcases hp with ⟨p₀, hp₀, rfl⟩ | ⟨p₀, hp₀, rfl⟩
      · rcases hq with ⟨q₀, hq₀, rfl⟩ | ⟨q₀, hq₀, rfl⟩
        · have hoff : p₀.2 = q₀.2 := by omega
          have hpq₀ : p₀ = q₀ := ih hp₀ hq₀ hoff
          simp [hpq₀]
        · have hq_lt : q₀.2 < 2 * 4 ^ k :=
            deltaTerms_second_branch_offset_lt_half hq₀
          omega
      · rcases hq with ⟨q₀, hq₀, rfl⟩ | ⟨q₀, hq₀, rfl⟩
        · have hp_lt : p₀.2 < 2 * 4 ^ k :=
            deltaTerms_second_branch_offset_lt_half hp₀
          omega
        · have hpq₀ : p₀ = q₀ := ih hp₀ hq₀ hpq
          simp [hpq₀]

lemma deltaTerms_offsets_nodup (k : ℕ) :
    ((deltaTerms k).map fun p : ℤ × ℕ => p.2).Nodup := by
  refine (deltaTerms_nodup k).map_on ?_
  intro p hp q hq hpq
  exact deltaTerms_offset_injective_on hp hq hpq

lemma deltaTerms_signed_sum_mem_signedFS (k : ℕ) (s : ℕ → ℤ) :
    ((deltaTerms k).map fun p : ℤ × ℕ => p.1 * s p.2).sum ∈ SignedFS s := by
  exact signedFSOf_subset_signedFS s _
    (signedFSOf_list_sum
      (s := s)
      (l := deltaTerms k)
      (fun p hp => deltaTerms_sign_eq_one_or_neg_one hp)
      (deltaTerms_offsets_nodup k))

@[simp] lemma Delta_zero (f : ℚ[X]) : Delta 0 f = f := by
  rfl

@[simp] lemma Delta_succ (k : ℕ) (f : ℚ[X]) :
    Delta (k + 1) f = Delta1 (Delta k f) := by
  simp [Delta, Function.iterate_succ_apply']

@[simp] lemma affinePoly_eval (a b x : ℚ) :
    (affinePoly a b).eval x = a * x + b := by
  simp [affinePoly]

lemma affinePoly_natDegree {a b : ℚ} (ha : a ≠ 0) :
    (affinePoly a b).natDegree = 1 := by
  unfold affinePoly
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_C_mul_X a ha
  · rw [Polynomial.natDegree_C_mul_X a ha, Polynomial.natDegree_C]
    norm_num

lemma affinePoly_leadingCoeff {a b : ℚ} (ha : a ≠ 0) :
    (affinePoly a b).leadingCoeff = a := by
  rw [Polynomial.leadingCoeff, affinePoly_natDegree ha]
  simp [affinePoly]

lemma natDegree_comp_affine (f : ℚ[X]) {a b : ℚ} (ha : a ≠ 0) :
    (f.comp (affinePoly a b)).natDegree = f.natDegree := by
  rw [Polynomial.natDegree_comp, affinePoly_natDegree ha, mul_one]

lemma leadingCoeff_comp_affine (f : ℚ[X]) {a b : ℚ} (ha : a ≠ 0) :
    (f.comp (affinePoly a b)).leadingCoeff =
      f.leadingCoeff * a ^ f.natDegree := by
  rw [Polynomial.leadingCoeff_comp]
  · rw [affinePoly_leadingCoeff ha]
  · rw [affinePoly_natDegree ha]
    norm_num

lemma affinePoly_ne_C_coeff_zero {a b : ℚ} (ha : a ≠ 0) :
    affinePoly a b ≠ Polynomial.C ((affinePoly a b).coeff 0) := by
  intro h
  have hc := congr_arg (fun p : ℚ[X] => p.coeff 1) h
  simp [affinePoly, ha] at hc

lemma comp_affine_ne_zero (f : ℚ[X]) (hf : f ≠ 0) {a b : ℚ} (ha : a ≠ 0) :
    f.comp (affinePoly a b) ≠ 0 := by
  intro h
  rcases Polynomial.comp_eq_zero_iff.mp h with hf0 | ⟨_, hconst⟩
  · exact hf hf0
  · exact affinePoly_ne_C_coeff_zero ha hconst

lemma degree_comp_affine (f : ℚ[X]) (hf : f ≠ 0) {a b : ℚ} (ha : a ≠ 0) :
    (f.comp (affinePoly a b)).degree = f.degree := by
  rw [Polynomial.degree_eq_natDegree (comp_affine_ne_zero f hf ha),
    Polynomial.degree_eq_natDegree hf, natDegree_comp_affine f ha]

lemma Delta1_degree_lt (f : ℚ[X]) (hf : f ≠ 0) :
    (Delta1 f).degree < f.degree := by
  unfold Delta1
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hdeg :
      (f.comp (affinePoly 4 2)).degree = (f.comp (affinePoly 4 0)).degree := by
    rw [degree_comp_affine f hf h4, degree_comp_affine f hf h4]
  have hp0 : f.comp (affinePoly 4 2) ≠ 0 :=
    comp_affine_ne_zero f hf h4
  have hlead :
      (f.comp (affinePoly 4 2)).leadingCoeff =
        (f.comp (affinePoly 4 0)).leadingCoeff := by
    rw [leadingCoeff_comp_affine f h4, leadingCoeff_comp_affine f h4]
  simpa [degree_comp_affine f hf h4] using Polynomial.degree_sub_lt hdeg hp0 hlead

lemma Delta1_natDegree_lt (f : ℚ[X]) (hfdeg : 0 < f.natDegree) :
    (Delta1 f).natDegree < f.natDegree := by
  have hf : f ≠ 0 := by
    intro hf0
    rw [hf0, Polynomial.natDegree_zero] at hfdeg
    omega
  by_cases hD : Delta1 f = 0
  · rw [hD, Polynomial.natDegree_zero]
    exact hfdeg
  · have hdeg := Delta1_degree_lt f hf
    rw [Polynomial.degree_eq_natDegree hD, Polynomial.degree_eq_natDegree hf] at hdeg
    exact_mod_cast hdeg

lemma Delta1_eq_zero_of_natDegree_eq_zero (f : ℚ[X]) (hfdeg : f.natDegree = 0) :
    Delta1 f = 0 := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero hfdeg]
  simp [Delta1]

lemma Delta1_natDegree_le_pred (f : ℚ[X]) :
    (Delta1 f).natDegree ≤ f.natDegree - 1 := by
  by_cases hfdeg : f.natDegree = 0
  · rw [hfdeg, Delta1_eq_zero_of_natDegree_eq_zero f hfdeg, Polynomial.natDegree_zero]
  · have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hfdeg
    exact Nat.le_pred_of_lt (Delta1_natDegree_lt f hpos)

lemma Delta_natDegree_le_sub (f : ℚ[X]) :
    ∀ k : ℕ, (Delta k f).natDegree ≤ f.natDegree - k
  | 0 => by simp
  | k + 1 => by
      rw [Delta_succ]
      have hstep := Delta1_natDegree_le_pred (Delta k f)
      have ih := Delta_natDegree_le_sub f k
      omega

lemma Delta_top_natDegree_eq_zero (f : ℚ[X]) :
    (Delta f.natDegree f).natDegree = 0 := by
  have h := Delta_natDegree_le_sub f f.natDegree
  exact Nat.eq_zero_of_le_zero (by simpa using h)

lemma Delta_top_eq_C (f : ℚ[X]) :
    Delta f.natDegree f = Polynomial.C ((Delta f.natDegree f).coeff 0) :=
  Polynomial.eq_C_of_natDegree_eq_zero (Delta_top_natDegree_eq_zero f)

/-! ## Standard forward-difference helpers from Mathlib -/

/-- Mathlib's top forward-difference theorem specialized to rational polynomial
evaluation. -/
lemma fwdDiff_top_eval (f : ℚ[X]) (x : ℚ) :
    (fwdDiff (1 : ℚ))^[f.natDegree] f.eval x =
      f.leadingCoeff * (Nat.factorial f.natDegree : ℚ) := by
  have h := congr_fun (Polynomial.fwdDiff_iter_degree_eq_factorial f) x
  simpa [Pi.smul_apply, smul_eq_mul] using h

lemma fwdDiff_top_eval_pos (f : ℚ[X]) (x : ℚ)
    (hlead : 0 < f.leadingCoeff) :
    0 < (fwdDiff (1 : ℚ))^[f.natDegree] f.eval x := by
  rw [fwdDiff_top_eval]
  exact mul_pos hlead (by exact_mod_cast Nat.factorial_pos f.natDegree)

/-- Explicit signed expansion of the top standard forward difference. This is
often the easiest way to connect finite differences to signed finite subset
sums. -/
lemma fwdDiff_top_eval_eq_sum_shift (f : ℚ[X]) (x : ℚ) :
    (fwdDiff (1 : ℚ))^[f.natDegree] f.eval x =
      ∑ k ∈ Finset.range (f.natDegree + 1),
        (((-1 : ℤ) ^ (f.natDegree - k) * f.natDegree.choose k : ℤ) : ℚ) *
          f.eval (x + k) := by
  have h :=
    fwdDiff_iter_eq_sum_shift (h := (1 : ℚ)) (f := f.eval) (n := f.natDegree) (y := x)
  simpa [zsmul_eq_mul, nsmul_eq_mul, one_nsmul] using h

@[simp] lemma Delta1_eval (f : ℚ[X]) (x : ℚ) :
    (Delta1 f).eval x = f.eval (4 * x + 2) - f.eval (4 * x) := by
  simp [Delta1, affinePoly]

lemma affinePoly_four_eq_C_mul_X_add_C (b : ℚ) :
    affinePoly 4 b = Polynomial.C (4 : ℚ) * (Polynomial.X + Polynomial.C (b / 4)) := by
  rw [affinePoly, mul_add, ← Polynomial.C_mul]
  congr 1
  congr 1
  ring

lemma coeff_affinePoly_four_pow_pred (n : ℕ) (_hn : 0 < n) (b : ℚ) :
    ((affinePoly 4 b) ^ n).coeff (n - 1) =
      4 ^ n * ((b / 4) ^ (n - (n - 1)) * (n.choose (n - 1) : ℚ)) := by
  rw [affinePoly_four_eq_C_mul_X_add_C b, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]

lemma coeff_affinePoly_four_pow_pred_simplified (n : ℕ) (hn : 0 < n) (b : ℚ) :
    ((affinePoly 4 b) ^ n).coeff (n - 1) =
      4 ^ (n - 1) * b * (n : ℚ) := by
  rw [coeff_affinePoly_four_pow_pred n hn b]
  have hsub : n - (n - 1) = 1 := by omega
  have hchoose : n.choose (n - 1) = n := by
    calc
      n.choose (n - 1) = ((n - 1) + 1).choose (n - 1) := by
        rw [Nat.sub_add_cancel hn]
      _ = (n - 1) + 1 := Nat.choose_succ_self_right (n - 1)
      _ = n := Nat.sub_add_cancel hn
  rw [hsub, hchoose]
  have hpow : 4 ^ n = 4 ^ (n - 1) * (4 : ℚ) := by
    have hsucc : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    nth_rewrite 1 [hsucc]
    rw [pow_succ]
  rw [hpow]
  field_simp

@[simp] lemma Delta1_add (f g : ℚ[X]) :
    Delta1 (f + g) = Delta1 f + Delta1 g := by
  ext n
  simp [Delta1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma Delta1_C_mul_X_pow_coeff_pred (n : ℕ) (hn : 0 < n) (c : ℚ) :
    (Delta1 (Polynomial.C c * Polynomial.X ^ n)).coeff (n - 1) =
      2 * 4 ^ (n - 1) * (n : ℚ) * c := by
  simp [Delta1, coeff_affinePoly_four_pow_pred_simplified n hn]
  ring

lemma Delta1_coeff_pred (f : ℚ[X]) (hfdeg : 0 < f.natDegree) :
    (Delta1 f).coeff (f.natDegree - 1) =
      2 * 4 ^ (f.natDegree - 1) * (f.natDegree : ℚ) * f.leadingCoeff := by
  have herase_coeff :
      (Delta1 f.eraseLead).coeff (f.natDegree - 1) = 0 := by
    by_cases hEdeg : f.eraseLead.natDegree = 0
    · rw [Delta1_eq_zero_of_natDegree_eq_zero _ hEdeg]
      simp
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le
          (Delta1_natDegree_lt f.eraseLead (Nat.pos_of_ne_zero hEdeg))
          (Polynomial.eraseLead_natDegree_le f))
  calc
    (Delta1 f).coeff (f.natDegree - 1)
        = (Delta1
            (f.eraseLead + Polynomial.C f.leadingCoeff * Polynomial.X ^ f.natDegree)).coeff
              (f.natDegree - 1) := by
          rw [Polynomial.eraseLead_add_C_mul_X_pow]
    _ = (Delta1 f.eraseLead).coeff (f.natDegree - 1) +
          (Delta1 (Polynomial.C f.leadingCoeff * Polynomial.X ^ f.natDegree)).coeff
            (f.natDegree - 1) := by
          rw [Delta1_add, Polynomial.coeff_add]
    _ = 2 * 4 ^ (f.natDegree - 1) * (f.natDegree : ℚ) * f.leadingCoeff := by
          rw [herase_coeff, Delta1_C_mul_X_pow_coeff_pred f.natDegree hfdeg f.leadingCoeff]
          ring

lemma Delta1_natDegree_eq_pred (f : ℚ[X])
    (hfdeg : 0 < f.natDegree) (hlead : 0 < f.leadingCoeff) :
    (Delta1 f).natDegree = f.natDegree - 1 := by
  refine le_antisymm (Delta1_natDegree_le_pred f) ?_
  apply Polynomial.le_natDegree_of_ne_zero
  rw [Delta1_coeff_pred f hfdeg]
  positivity

lemma Delta1_leadingCoeff_pos (f : ℚ[X])
    (hfdeg : 0 < f.natDegree) (hlead : 0 < f.leadingCoeff) :
    0 < (Delta1 f).leadingCoeff := by
  rw [Polynomial.leadingCoeff, Delta1_natDegree_eq_pred f hfdeg hlead,
    Delta1_coeff_pred f hfdeg]
  positivity

lemma Delta_natDegree_eq_sub_and_leadingCoeff_pos (f : ℚ[X])
    (hlead : 0 < f.leadingCoeff) :
    ∀ k : ℕ, k ≤ f.natDegree →
      (Delta k f).natDegree = f.natDegree - k ∧
        0 < (Delta k f).leadingCoeff
  | 0, _ => by
      simp [hlead]
  | k + 1, hk_succ => by
      have hk : k ≤ f.natDegree := Nat.le_trans (Nat.le_succ k) hk_succ
      rcases Delta_natDegree_eq_sub_and_leadingCoeff_pos f hlead k hk with
        ⟨hdeg, hlead_k⟩
      have hpos_deg : 0 < (Delta k f).natDegree := by
        rw [hdeg]
        omega
      constructor
      · rw [Delta_succ, Delta1_natDegree_eq_pred (Delta k f) hpos_deg hlead_k, hdeg]
        omega
      · rw [Delta_succ]
        exact Delta1_leadingCoeff_pos (Delta k f) hpos_deg hlead_k

lemma Delta_natDegree_eq_sub (f : ℚ[X]) (hlead : 0 < f.leadingCoeff)
    {k : ℕ} (hk : k ≤ f.natDegree) :
    (Delta k f).natDegree = f.natDegree - k :=
  (Delta_natDegree_eq_sub_and_leadingCoeff_pos f hlead k hk).1

lemma Delta_leadingCoeff_pos (f : ℚ[X]) (hlead : 0 < f.leadingCoeff)
    {k : ℕ} (hk : k ≤ f.natDegree) :
    0 < (Delta k f).leadingCoeff :=
  (Delta_natDegree_eq_sub_and_leadingCoeff_pos f hlead k hk).2

lemma Delta_top_coeff_zero_pos (f : ℚ[X]) (hlead : 0 < f.leadingCoeff) :
    0 < (Delta f.natDegree f).coeff 0 := by
  have hlead_top := Delta_leadingCoeff_pos f hlead (k := f.natDegree) le_rfl
  have hdeg_top := Delta_natDegree_eq_sub f hlead (k := f.natDegree) le_rfl
  simpa [Polynomial.leadingCoeff, hdeg_top] using hlead_top

lemma Delta_succ_eval (k : ℕ) (f : ℚ[X]) (x : ℚ) :
    (Delta (k + 1) f).eval x =
      (Delta k f).eval (4 * x + 2) - (Delta k f).eval (4 * x) := by
  simp

lemma Delta_eval_eq_deltaTerms (k : ℕ) (f : ℚ[X]) (x : ℚ) :
    (Delta k f).eval x =
      ((deltaTerms k).map (deltaTermValue k f x)).sum := by
  induction k generalizing x with
  | zero =>
      simp [deltaTerms, deltaTermValue]
  | succ k ih =>
      rw [Delta_succ_eval, ih (4 * x + 2), ih (4 * x)]
      simp only [deltaTerms, List.map_append, List.sum_append, List.map_map]
      have hpos_map :
          List.map (deltaTermValue (k + 1) f x ∘
              fun p : ℤ × ℕ => (p.1, 2 * 4 ^ k + p.2)) (deltaTerms k) =
            List.map (deltaTermValue k f (4 * x + 2)) (deltaTerms k) := by
        apply List.map_congr_left
        intro p hp
        dsimp [Function.comp, deltaTermValue]
        have harg :
            (4 ^ (k + 1) : ℚ) * x + ((2 * 4 ^ k + p.2 : ℕ) : ℚ) =
              (4 ^ k : ℚ) * (4 * x + 2) + (p.2 : ℚ) := by
          norm_num [pow_succ]
          ring
        rw [harg]
      have hneg_map :
          List.map (deltaTermValue (k + 1) f x ∘
              fun p : ℤ × ℕ => (-p.1, p.2)) (deltaTerms k) =
            List.map (fun q => -q) (List.map (deltaTermValue k f (4 * x)) (deltaTerms k)) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro p hp
        dsimp [Function.comp, deltaTermValue]
        have harg :
            (4 ^ (k + 1) : ℚ) * x + (p.2 : ℚ) =
              (4 ^ k : ℚ) * (4 * x) + (p.2 : ℚ) := by
          norm_num [pow_succ]
          ring
        rw [harg]
        ring
      rw [hpos_map, hneg_map, ← List.sum_neg]
      ring

/-- If all polynomial values in the explicit `Delta` expansion are represented
by an integer sequence `s`, then any integer representative of the difference is
a signed finite subset sum of `s`. -/
lemma Delta_eval_integer_mem_signedFS
    (k : ℕ) (f : ℚ[X]) (x : ℚ) (s : ℕ → ℤ) (z : ℤ)
    (hvals :
      ∀ p ∈ deltaTerms k,
        (s p.2 : ℚ) = f.eval ((4 ^ k : ℚ) * x + (p.2 : ℚ)))
    (hz : (z : ℚ) = (Delta k f).eval x) :
    z ∈ SignedFS s := by
  let y : ℤ := ((deltaTerms k).map fun p : ℤ × ℕ => p.1 * s p.2).sum
  have hy_mem : y ∈ SignedFS s := by
    exact deltaTerms_signed_sum_mem_signedFS k s
  have hmap :
      (deltaTerms k).map (fun p : ℤ × ℕ => ((p.1 * s p.2 : ℤ) : ℚ)) =
        (deltaTerms k).map (deltaTermValue k f x) := by
    apply List.map_congr_left
    intro p hp
    simp [deltaTermValue, hvals p hp]
  have hy_eval : (y : ℚ) = (Delta k f).eval x := by
    rw [Delta_eval_eq_deltaTerms]
    dsimp [y]
    norm_cast
    rw [List.map_map]
    change
      ((deltaTerms k).map (fun p : ℤ × ℕ => ((p.1 * s p.2 : ℤ) : ℚ))).sum =
        ((deltaTerms k).map (deltaTermValue k f x)).sum
    rw [hmap]
  have hcast : (z : ℚ) = (y : ℚ) := by
    rw [hz, hy_eval]
  have hzy : z = y := by
    exact_mod_cast hcast
  rw [hzy]
  exact hy_mem

/-! ## Polynomial ratio limits -/

/-- Equal-degree rational polynomials with the same nonzero leading coefficient
have evaluation ratio tending to `1` at `+∞`.

This is a small wrapper around Mathlib's
`Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq`, recorded here because it
is the analytic input needed to turn Graham's odd tail into a Sigma-sequence. -/
lemma polynomial_eval_ratio_tendsto_one_of_degree_eq_of_leadingCoeff_eq
    (P Q : ℚ[X])
    (hdeg : P.degree = Q.degree)
    (hlead : P.leadingCoeff = Q.leadingCoeff)
    (hQ : Q.leadingCoeff ≠ 0) :
    Tendsto (fun x : ℚ => P.eval x / Q.eval x) atTop (nhds (1 : ℚ)) := by
  have h := Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq P Q hdeg
  simpa [hlead, div_self hQ] using h

/-- Ratio limit for one polynomial evaluated along two affine-linear arguments
with the same nonzero slope. -/
lemma polynomial_eval_same_slope_ratio_tendsto_one
    (f : ℚ[X]) {a b c : ℚ}
    (ha : a ≠ 0)
    (hflead : f.leadingCoeff ≠ 0) :
    Tendsto
      (fun x : ℚ => f.eval (a * x + b) / f.eval (a * x + c))
      atTop (nhds (1 : ℚ)) := by
  let P : ℚ[X] := f.comp (affinePoly a b)
  let Q : ℚ[X] := f.comp (affinePoly a c)
  have hf : f ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hflead
  have hdeg : P.degree = Q.degree := by
    simp [P, Q, degree_comp_affine f hf ha]
  have hlead : P.leadingCoeff = Q.leadingCoeff := by
    simp [P, Q, leadingCoeff_comp_affine f ha]
  have hQ : Q.leadingCoeff ≠ 0 := by
    simp [Q, leadingCoeff_comp_affine f ha, hflead, ha]
  have h :=
    polynomial_eval_ratio_tendsto_one_of_degree_eq_of_leadingCoeff_eq P Q hdeg hlead hQ
  simpa [P, Q, affinePoly_eval] using h

end Erdos.P283.RSG
