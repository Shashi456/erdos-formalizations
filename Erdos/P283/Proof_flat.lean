/-
**STANDALONE FLAT BUNDLE** of Erdős Problems #283 + #351 — POLYNOMIAL EGYPTIAN SUMS.

This file is the concatenation of the 10-module modular development under
`Erdos/P283/`, in dependency order:

  Basic, Egyptian, PolynomialPeriod, Switching, MainSlots, Collision,
  Corrections, Theorem1, Corollary351, FC.

It is suitable for loading into `live.lean-lang.org` (which only resolves
`import Mathlib`, not project-local imports like `Erdos.P283.Theorem1`).
For local Lake builds, prefer the modular `Proof.lean` in the same directory
— this flat file is auto-generated for live-load convenience.

Trust boundary (verify with `#print axioms` at the bottom):
  Mathlib core (propext, Classical.choice, Quot.sound)
  + PolynomialEgyptianSums.roth_szekeres_graham
        (Graham 1964 / Roth-Szekeres 1954, the asymptotic input)

The May 3 2026 proof (GPT-5.5 Pro, cleaned up by Liam Price; Kevin Barreto
noticed #351 follows) — see proof.pdf.
-/

import Mathlib


/-! =============================================================
    Section from: Erdos/P283/Basic.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — Foundational definitions.

Predicates and helpers used throughout the formalization:

  * `IsEgyptianPattern E` — `E ⊆ {2, 3, …}` with `∑_{e ∈ E} 1/e = 1`.
  * `IntValued p`         — `p : ℚ[X]` takes integer values on ℤ.
  * `intEval p hp z`      — extract the integer value (via `Classical.choose`).
  * `NoFixedDivisor p hp` — no `d ≥ 2` divides every `p(n)` for `n ≥ 1`.
  * `HasIntegralMultiple B p` — `B p(x) ∈ ℤ[x]` (denominator-cleared form).
  * `FS s`                — finite subset sums of a sequence (used by RSG).
  * `roth_szekeres_graham` — the trust-boundary axiom (with integer-divisibility
                              gcd hypothesis, fixed from earlier scaffold).

This file is imported by every other P283 file.
-/


namespace PolynomialEgyptianSums

open Polynomial Filter

/-! ## Egyptian patterns -/

/-- `E ⊆ {2, 3, …}` is an **Egyptian pattern** if `∑_{e ∈ E} 1/e = 1`. Used
throughout the proof for the switch identity and the residue-correction trick. -/
def IsEgyptianPattern (E : Finset ℕ) : Prop :=
  (∀ e ∈ E, 2 ≤ e) ∧ (∑ e ∈ E, (1 : ℚ) / (e : ℚ)) = 1

/-! ## Integer-valued polynomials -/

/-- `p : ℚ[X]` takes integer values on every `z ∈ ℤ`. -/
def IntValued (p : ℚ[X]) : Prop :=
  ∀ z : ℤ, ∃ k : ℤ, (k : ℚ) = p.eval (z : ℚ)

/-- The integer value of an integer-valued polynomial at `z ∈ ℤ`. -/
noncomputable def intEval (p : ℚ[X]) (hp : IntValued p) (z : ℤ) : ℤ :=
  (hp z).choose

/-- The defining specification of `intEval`. -/
lemma intEval_spec (p : ℚ[X]) (hp : IntValued p) (z : ℤ) :
    ((intEval p hp z : ℤ) : ℚ) = p.eval (z : ℚ) :=
  (hp z).choose_spec

/-! ### Closure of `IntValued` -/

lemma IntValued.add {p q : ℚ[X]} (hp : IntValued p) (hq : IntValued q) :
    IntValued (p + q) := by
  intro z
  obtain ⟨a, ha⟩ := hp z
  obtain ⟨b, hb⟩ := hq z
  refine ⟨a + b, ?_⟩
  rw [Polynomial.eval_add, ← ha, ← hb]
  push_cast; ring

lemma IntValued.sub {p q : ℚ[X]} (hp : IntValued p) (hq : IntValued q) :
    IntValued (p - q) := by
  intro z
  obtain ⟨a, ha⟩ := hp z
  obtain ⟨b, hb⟩ := hq z
  refine ⟨a - b, ?_⟩
  rw [Polynomial.eval_sub, ← ha, ← hb]
  push_cast; ring

lemma IntValued.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X])
    (hf : ∀ i ∈ s, IntValued (f i)) :
    IntValued (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z
    refine ⟨0, ?_⟩
    simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine IntValued.add (hf a (Finset.mem_insert_self a s)) ?_
    apply ih
    intro i hi
    exact hf i (Finset.mem_insert_of_mem hi)

/-! ## Fixed-divisor predicate -/

/-- The polynomial `p` has **no fixed divisor** on the positive integers if no
`d ≥ 2` divides every `p(n)` for `n ≥ 1`. -/
def NoFixedDivisor (p : ℚ[X]) (hp : IntValued p) : Prop :=
  ∀ d : ℕ, 2 ≤ d → ¬ (∀ n : ℕ, 1 ≤ n → (d : ℤ) ∣ intEval p hp (n : ℤ))

/-! ## Integral multiples (denominator clearing) -/

/-- `B p(x) ∈ ℤ[x]`: there is an integer-coefficient polynomial whose ℚ-cast equals
`B p`. (Used in Lemma 5 to upgrade integer-valuedness to actual integer
coefficients after scaling.) -/
def HasIntegralMultiple (B : ℕ) (p : ℚ[X]) : Prop :=
  ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) = Polynomial.C (B : ℚ) * p

/-- Every rational polynomial has an integral multiple. (Routine denominator
clearing: take `B` = product of the denominators of the coefficients.) -/
theorem exists_integral_multiple (p : ℚ[X]) :
    ∃ B : ℕ, 1 ≤ B ∧ HasIntegralMultiple B p := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨B₁, hB₁, P₁, hP₁⟩ := hp
    obtain ⟨B₂, hB₂, P₂, hP₂⟩ := hq
    refine ⟨B₁ * B₂, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (Nat.one_le_iff_ne_zero.mp hB₁) (Nat.one_le_iff_ne_zero.mp hB₂))
    · refine ⟨Polynomial.C (B₂ : ℤ) * P₁ + Polynomial.C (B₁ : ℤ) * P₂, ?_⟩
      simp [Polynomial.map_add, Polynomial.map_mul, hP₁, hP₂]
      ring
  | monomial n c =>
    refine ⟨c.den, c.den_pos, Polynomial.monomial n c.num, ?_⟩
    rw [Polynomial.map_monomial, Polynomial.C_mul_monomial]
    congr 1
    show (c.num : ℚ) = (c.den : ℚ) * c
    have h : (c.num : ℚ) / (c.den : ℚ) = c := c.num_div_den
    field_simp at h
    linarith

/-! ## Roth–Szekeres–Graham (axiom) -/

/-- The set of finite subset sums of a sequence `s : ℕ → ℤ`. -/
def FS (s : ℕ → ℤ) : Set ℤ := { x | ∃ I : Finset ℕ, x = ∑ i ∈ I, s i }

/-- **Roth–Szekeres–Graham theorem.** For a non-constant polynomial `f ∈ ℚ[x]`
with positive leading coefficient that takes positive integer values on
`ℕ_{>0}`, with `gcd{f(n) : n ≥ 1} = 1` (encoded as: no prime `ℓ` divides every
integer value), all sufficiently large integers `X` admit an expression
`X = ∑_{i ∈ I} f(i + 1)` for some finite `I ⊆ ℕ`.

Classical (Graham 1964 / Roth-Szekeres 1954); Mathlib has surrounding analytic
NT infrastructure but not this named result. We postulate it as the single
trust-boundary axiom for the polynomial-Egyptian-sums proof. -/
axiom roth_szekeres_graham (f : ℚ[X])
    (h_nonconst : 0 < f.natDegree)
    (h_lead_pos : 0 < f.leadingCoeff)
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = f.eval (n : ℚ))
    (h_gcd_one :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ n : ℕ, 1 ≤ n ∧ ∃ z : ℤ,
          (z : ℚ) = f.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z)) :
    ∃ X_f : ℤ, ∀ X : ℤ, X_f ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, f.eval ((i + 1 : ℕ) : ℚ)

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/Egyptian.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — §1 Egyptian switches, Lemmas 3 & 4.

  * `Lemma 3 (egyptian_expansion)` — every `R ∈ ℚ_{>0}` has Egyptian expansions
    (sums of distinct unit fractions with denominators `> L`) of all sufficiently
    large lengths.
  * `Lemma 4 (egyptian_pattern_with_period)` — for any `T, M ≥ 1` and residue
    `ρ ∈ ZMod M`, an Egyptian pattern `E` exists with `T ∣ e` for every `e ∈ E`
    and `|E| ≡ ρ (mod M)`.

Both are axiom-free. Lemma 4 is a direct corollary of Lemma 3.

Internal helper lemmas (broken out for clarity):
  * `egyptian_split_*`        — properties of the `1/y → 1/(y+1) + 1/(y(y+1))`
                                 step that extends an expansion by one term.
  * `egyptian_expansion_exists` — a single expansion exists (greedy).
  * `egyptian_expansion_all_large_cardinalities` — all sufficiently large
                                                    lengths.
-/


namespace PolynomialEgyptianSums

open Finset

/-! ## Splitting step (extends an expansion by one term) -/

/-- The split identity `1/y = 1/(y+1) + 1/(y(y+1))` for `y ≥ 1`. -/
lemma egyptian_split_identity (y : ℕ) (hy : 1 ≤ y) :
    (1 : ℚ) / y = 1 / (y + 1 : ℕ) + 1 / (y * (y + 1) : ℕ) := by
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hy
  have hy1 : ((y : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- After a split at the largest denominator `y`, the new denominators
`y + 1` and `y(y+1)` are both larger than `y`. -/
lemma egyptian_split_lower_bound (y : ℕ) (hy : 1 ≤ y) :
    y < y + 1 ∧ y < y * (y + 1) := by
  refine ⟨Nat.lt_succ_self y, ?_⟩
  have h_le : y * 1 ≤ y * (y + 1) := Nat.mul_le_mul_left y (by omega)
  have h_pos : y * 1 < y * (y + 1) ∨ y * 1 = y * (y + 1) := lt_or_eq_of_le h_le
  rcases h_pos with h | h
  · simpa using h
  · exfalso; have := (Nat.mul_left_cancel hy h); omega

/-! ## Lemma 3 — Egyptian expansion existence and arbitrary length -/

/-! ### Helpers for the existence proof -/

/-- The harmonic series partial sums grow without bound. -/
private lemma harmonic_mono_aux (m n : ℕ) (h : m ≤ n) : harmonic m ≤ harmonic n := by
  induction n, h using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih =>
    rw [harmonic_succ]
    have h_pos : (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ)⁻¹ := by positivity
    linarith

/-- For any rational `R`, there exists a natural `N` with `harmonic N > R`. -/
private lemma exists_harmonic_gt_aux (R : ℚ) : ∃ N : ℕ, harmonic N > R := by
  have h : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (1 : ℝ) / (↑i + 1))
      Filter.atTop Filter.atTop := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h ((R : ℝ) + 1)
  use N
  have h_eq : (∑ i ∈ Finset.range N, (1 : ℝ) / (↑i + 1)) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [show (Finset.Icc 1 N) = (Finset.range N).image (· + 1) from ?_]
    · rw [Finset.sum_image (fun a _ b _ h => by simp at h; omega)]
      simp
    · ext x
      simp [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩; refine ⟨x - 1, ?_, ?_⟩ <;> omega
      · rintro ⟨a, ha, rfl⟩; omega
  have h_test : ((R : ℝ) + 1) ≤ (harmonic N : ℝ) := h_eq ▸ hN N le_rfl
  have h_cast : (R : ℝ) < (harmonic N : ℝ) := by linarith
  exact_mod_cast h_cast

/-- The harmonic tail `∑_{j=L+1}^N 1/j` equals `harmonic N - harmonic L`. -/
private lemma harmonicTail_eq_aux (L N : ℕ) (h : L ≤ N) :
    ∑ j ∈ Finset.Ioc L N, (1 : ℚ) / j = harmonic N - harmonic L := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  rw [show Finset.Ioc L N = Finset.Icc (L+1) N from by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]]
  have h_split : Finset.Icc 1 N = Finset.Icc 1 L ∪ Finset.Icc (L+1) N := by
    ext x; simp [Finset.mem_Icc, Finset.mem_union]; omega
  rw [h_split, Finset.sum_union ?_]
  · simp [one_div]
  · simp [Finset.disjoint_left, Finset.mem_Icc]; intros; omega

/-- For any positive rational `R` and natural `L`, there exists `N ≥ L` such that
the harmonic tail from `L+1` to `N` is at least `R`. -/
private lemma exists_harmonicTail_ge_aux (R : ℚ) (L : ℕ) :
    ∃ N : ℕ, L ≤ N ∧ R ≤ ∑ j ∈ Finset.Ioc L N, (1 : ℚ) / j := by
  obtain ⟨N₀, hN₀⟩ := exists_harmonic_gt_aux (R + harmonic L)
  refine ⟨max N₀ L, le_max_right _ _, ?_⟩
  have hLN : L ≤ max N₀ L := le_max_right _ _
  rw [harmonicTail_eq_aux _ _ hLN]
  have h_mono : harmonic N₀ ≤ harmonic (max N₀ L) :=
    harmonic_mono_aux _ _ (le_max_left _ _)
  linarith

/-- Algebraic identity: rewrite `R - 1/q` as a `Rat.divInt`. -/
private lemma sub_one_div_eq_divInt_aux (R : ℚ) (q : ℕ) (hq_pos : 0 < q) :
    R - 1/(q : ℚ) = ((R.num * q - R.den : ℤ) : ℚ) / ((R.den * q : ℕ) : ℤ) := by
  have hRd : (R.den : ℚ) ≠ 0 := by exact_mod_cast R.den_pos.ne'
  have hq_q : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hR_eq : (R.num : ℚ) = R * R.den := by
    have h := Rat.num_div_den R
    field_simp at h
    linarith
  push_cast
  rw [eq_div_iff (by positivity : (R.den : ℚ) * q ≠ 0)]
  rw [sub_mul]
  rw [show R * ((R.den : ℚ) * q) = (R * R.den) * q from by ring]
  rw [← hR_eq]
  rw [show (1 / (q : ℚ)) * ((R.den : ℚ) * q) = ((q : ℚ) * (q : ℚ)⁻¹) * R.den from by
    rw [one_div]; ring]
  rw [mul_inv_cancel₀ hq_q, one_mul]

/-- The greedy step decreases the numerator (in `natAbs`). -/
private lemma greedy_num_decrease_aux (R : ℚ) (hR : 0 < R)
    (h_neq : R ≠ 1/(⌈(R⁻¹ : ℚ)⌉₊ : ℚ)) :
    (R - 1/(⌈(R⁻¹ : ℚ)⌉₊ : ℚ)).num.natAbs < R.num.natAbs := by
  set q : ℕ := ⌈(R⁻¹ : ℚ)⌉₊ with hq_def
  have hq_pos : 0 < q := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hq
    have h : (R⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
    have h_pos : (0 : ℚ) < R⁻¹ := inv_pos.mpr hR
    linarith
  have ha_pos : 0 < R.num := Rat.num_pos.mpr hR
  have hb_pos : (0 : ℕ) < R.den := R.den_pos
  have hR_inv : (R⁻¹ : ℚ) = (R.den : ℚ) / R.num := by
    rw [show R = (R.num : ℚ) / R.den from (Rat.num_div_den R).symm]
    rw [inv_div, Rat.num_div_den]
  have ha_pos_q : (0 : ℚ) < R.num := by exact_mod_cast ha_pos
  have hb_pos_q : (0 : ℚ) < R.den := by exact_mod_cast hb_pos
  have h_qa_ge_b : (R.den : ℤ) ≤ R.num * q := by
    have h1 : (R⁻¹ : ℚ) ≤ q := Nat.le_ceil _
    rw [hR_inv] at h1
    rw [div_le_iff₀ ha_pos_q] at h1
    have h_int : (R.den : ℤ) ≤ (q : ℤ) * R.num := by exact_mod_cast h1
    linarith
  have h_qa_lt : (R.num : ℤ) * q < R.den + R.num := by
    have h2 : ((q : ℚ) : ℚ) < R⁻¹ + 1 :=
      Nat.ceil_lt_add_one (le_of_lt (inv_pos.mpr hR))
    rw [hR_inv] at h2
    have h3 : (q : ℚ) * R.num < R.den + R.num := by
      have := mul_lt_mul_of_pos_right h2 ha_pos_q
      rw [add_mul, div_mul_cancel₀ _ ha_pos_q.ne', one_mul] at this
      exact this
    have h_int : (q : ℤ) * R.num < R.den + R.num := by exact_mod_cast h3
    linarith
  have h_div : (R - 1/(q : ℚ)).num ∣ (R.num * q - R.den : ℤ) := by
    rw [sub_one_div_eq_divInt_aux R q hq_pos]
    have h_cast : ((R.den * q : ℕ) : ℤ) = (R.den : ℤ) * q := by push_cast; ring
    rw [h_cast]
    rw [show ((R.num * q - R.den : ℤ) : ℚ) / ((R.den : ℤ) * q : ℤ) =
            Rat.divInt (R.num * q - R.den) ((R.den : ℤ) * q) from
      (Rat.divInt_eq_div _ _).symm]
    apply Rat.num_dvd
    have h1 : 0 < (q : ℤ) := by exact_mod_cast hq_pos
    have h2 : 0 < (R.den : ℤ) := by exact_mod_cast hb_pos
    positivity
  have h_nonneg : 0 ≤ R.num * q - R.den := by linarith
  have h_lt' : R.num * q - R.den < R.num := by linarith
  have h_diff_pos : 0 < R.num * q - R.den := by
    by_contra h_neg
    push_neg at h_neg
    have h_eq : R.num * q - R.den = 0 := by omega
    have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
    have h_R_eq : R = 1/(q : ℚ) := by
      rw [show R = (R.num : ℚ) / R.den from (Rat.num_div_den R).symm]
      rw [div_eq_div_iff hb_pos_q.ne' hq_pos_q.ne']
      have : (R.num * q : ℤ) = R.den := by linarith
      have hh : (R.num : ℚ) * q = R.den := by exact_mod_cast this
      linarith
    exact h_neq h_R_eq
  have ha_eq : (R.num.natAbs : ℤ) = R.num := Int.natAbs_of_nonneg ha_pos.le
  have hd_eq : ((R.num * q - R.den).natAbs : ℤ) = R.num * q - R.den :=
    Int.natAbs_of_nonneg h_nonneg
  have h_lt_natabs : (R.num * q - R.den).natAbs < R.num.natAbs := by
    have : ((R.num * q - R.den).natAbs : ℤ) < R.num.natAbs := by
      rw [hd_eq, ha_eq]; exact h_lt'
    exact_mod_cast this
  have h_pos_natabs : 0 < (R.num * q - R.den).natAbs := by
    have : 0 < ((R.num * q - R.den).natAbs : ℤ) := by rw [hd_eq]; exact h_diff_pos
    exact_mod_cast this
  have h_le_natabs : (R - 1/(q : ℚ)).num.natAbs ≤ (R.num * q - R.den).natAbs :=
    Nat.le_of_dvd h_pos_natabs (Int.natAbs_dvd_natAbs.mpr h_div)
  omega

/-- For positive rational `R`, `0 ≤ R - 1/⌈R⁻¹⌉₊`. -/
private lemma greedy_step_nonneg_aux (R : ℚ) (hR : 0 < R) :
    0 ≤ R - 1/((⌈(R⁻¹ : ℚ)⌉₊ : ℕ) : ℚ) := by
  set q := ⌈(R⁻¹ : ℚ)⌉₊
  have hq_pos : 0 < q := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hq
    have h : (R⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
    have h_pos : (0 : ℚ) < R⁻¹ := inv_pos.mpr hR
    linarith
  have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
  have h1 : (R⁻¹ : ℚ) ≤ q := Nat.le_ceil _
  rw [sub_nonneg, div_le_iff₀ hq_pos_q, mul_comm, ← div_le_iff₀ hR, one_div]
  exact h1

/-- Greedy expansion for a residual `S` with the precondition that
`minDen ≥ 2` and either `S = 0` or `⌈S⁻¹⌉₊ ≥ minDen`.
This produces a finite set of distinct integers `≥ minDen` whose reciprocals
sum to `S`.

Proven by strong induction on `S.num.natAbs`. -/
private lemma greedy_residual_aux (n : ℕ) :
    ∀ (S : ℚ), 0 ≤ S → S.num.natAbs ≤ n → ∀ (minDen : ℕ), 2 ≤ minDen →
      (S = 0 ∨ minDen ≤ ⌈(S⁻¹ : ℚ)⌉₊) →
      ∃ E : Finset ℕ, (∀ e ∈ E, minDen ≤ e) ∧ S = ∑ e ∈ E, (1 : ℚ) / e := by
  induction n with
  | zero =>
    intros S hS_nonneg hS_num minDen _ _
    have hS_num_zero : S.num.natAbs = 0 := Nat.le_zero.mp hS_num
    have hS_zero_num : S.num = 0 := Int.natAbs_eq_zero.mp hS_num_zero
    have hS : S = 0 := Rat.num_eq_zero.mp hS_zero_num
    refine ⟨∅, by simp, ?_⟩
    rw [hS]; simp
  | succ n ih =>
    intros S hS_nonneg hS_num minDen hminDen_two hS_inv
    by_cases hS_zero : S = 0
    · refine ⟨∅, by simp, ?_⟩
      rw [hS_zero]; simp
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_zero)
    have hq_ge : minDen ≤ ⌈(S⁻¹ : ℚ)⌉₊ := by
      rcases hS_inv with hS_eq | hq_le
      · exact (hS_zero hS_eq).elim
      · exact hq_le
    set q : ℕ := ⌈(S⁻¹ : ℚ)⌉₊ with hq_def
    have hq_pos : 0 < q := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hq
      have h : (S⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
      have h_pos : (0 : ℚ) < S⁻¹ := inv_pos.mpr hS_pos
      linarith
    have hq_ge_two : 2 ≤ q := by omega
    have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
    -- Case: S = 1/q
    by_cases h_eq : S = 1/(q : ℚ)
    · refine ⟨{q}, ?_, ?_⟩
      · intro e he; simp at he; rw [he]; exact hq_ge
      · rw [Finset.sum_singleton]; exact h_eq
    -- S ≠ 1/q: greedy step
    have h_nonneg' : 0 ≤ S - 1/(q : ℚ) := greedy_step_nonneg_aux S hS_pos
    have h_num_lt : (S - 1/(q : ℚ)).num.natAbs < S.num.natAbs :=
      greedy_num_decrease_aux S hS_pos h_eq
    have h_num_le : (S - 1/(q : ℚ)).num.natAbs ≤ n := by omega
    -- Need: (S - 1/q) = 0 OR ⌈(S-1/q)⁻¹⌉₊ ≥ q + 1.
    have h_new_inv : (S - 1/(q : ℚ)) = 0 ∨ q + 1 ≤ ⌈((S - 1/(q : ℚ))⁻¹ : ℚ)⌉₊ := by
      by_cases h_zero : S - 1/(q : ℚ) = 0
      · left; exact h_zero
      right
      have h_pos' : 0 < S - 1/(q : ℚ) := lt_of_le_of_ne h_nonneg' (Ne.symm h_zero)
      have hq_minus_one_pos : (0 : ℚ) < (q : ℚ) - 1 := by
        have : (2 : ℚ) ≤ q := by exact_mod_cast hq_ge_two
        linarith
      -- Step 1: S⁻¹ > q - 1 (since q = ⌈S⁻¹⌉₊).
      have hSinv_gt : (q : ℚ) - 1 < S⁻¹ := by
        by_contra h_neg
        push_neg at h_neg
        -- S⁻¹ ≤ q - 1, so ⌈S⁻¹⌉₊ ≤ ⌈q - 1⌉₊ = q - 1, contradicting q = ⌈S⁻¹⌉₊.
        have h_ceil_le : ⌈(S⁻¹ : ℚ)⌉₊ ≤ ⌈((q : ℚ) - 1)⌉₊ := Nat.ceil_le_ceil h_neg
        have h_eq_cast : ((q : ℚ) - 1) = ((q - 1 : ℕ) : ℚ) := by
          have hq_ge : 1 ≤ q := by omega
          rw [Nat.cast_sub hq_ge]; push_cast; ring
        rw [h_eq_cast, Nat.ceil_natCast] at h_ceil_le
        omega
      -- Step 2: 1/(q-1) ≤ 2/q (since q ≥ 2).
      have h_two_q_ineq : 1/((q : ℚ) - 1) ≤ 2/(q : ℚ) := by
        rw [div_le_div_iff₀ hq_minus_one_pos hq_pos_q]
        have : (2 : ℚ) ≤ q := by exact_mod_cast hq_ge_two
        nlinarith
      -- Step 3: S < 1/(q-1)
      have hS_lt_inv : S < 1/((q : ℚ) - 1) := by
        have h1 : (q : ℚ) - 1 < S⁻¹ := hSinv_gt
        rw [lt_div_iff₀ hq_minus_one_pos]
        have h2 : ((q : ℚ) - 1) * S < S⁻¹ * S := by
          have := mul_lt_mul_of_pos_right h1 hS_pos
          linarith
        rw [inv_mul_cancel₀ hS_pos.ne'] at h2
        linarith
      -- Step 4: S - 1/q < 1/q
      have hS_lt_two_q : S < 2/(q : ℚ) := lt_of_lt_of_le hS_lt_inv h_two_q_ineq
      have h_diff_lt : S - 1/(q : ℚ) < 1/(q : ℚ) := by
        have : (2 : ℚ) / q = 1/(q : ℚ) + 1/(q : ℚ) := by ring
        linarith
      -- Step 5: (S - 1/q)⁻¹ > q.
      have h_inv_gt : (q : ℚ) < (S - 1/(q : ℚ))⁻¹ := by
        rw [lt_inv_comm₀ hq_pos_q h_pos']
        have : (1 : ℚ) / q = (q : ℚ)⁻¹ := one_div _
        linarith
      -- Step 6: ⌈(S-1/q)⁻¹⌉₊ ≥ q + 1.
      rw [Nat.add_one_le_iff, Nat.lt_ceil]
      exact h_inv_gt
    obtain ⟨E', hE'_lb, hE'_sum⟩ := ih (S - 1/(q : ℚ)) h_nonneg' h_num_le (q + 1)
      (by omega) h_new_inv
    have hq_notin : q ∉ E' := by
      intro h
      have := hE'_lb q h
      omega
    refine ⟨insert q E', ?_, ?_⟩
    · intro e he
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · exact hq_ge
      · have := hE'_lb e he
        omega
    · rw [Finset.sum_insert hq_notin, ← hE'_sum]
      ring

/-- Auxiliary: a single Egyptian expansion exists (greedy).

The proof uses a harmonic-tail prelude to reduce to a small residual `S ≤ 1/N`,
then applies the greedy step recursion `greedy_residual_aux`. -/
lemma egyptian_expansion_exists (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ E : Finset ℕ, (∀ e ∈ E, L < e) ∧ R = ∑ e ∈ E, (1 : ℚ) / e := by
  classical
  -- Lift to L' = max L 1 so that minDen ≥ 2.
  set L' := max L 1 with hL'_def
  have hL'_ge : 1 ≤ L' := le_max_right _ _
  have hL_le_L' : L ≤ L' := le_max_left _ _
  -- Find smallest N ≥ L' with R ≤ harmonicTail L' N. Such N exists by harmonic divergence.
  set P : ℕ → Prop := fun N => L' ≤ N ∧ R ≤ ∑ j ∈ Finset.Ioc L' N, (1 : ℚ) / j with hP_def
  have hP_ex : ∃ N, P N := exists_harmonicTail_ge_aux R L'
  set N := Nat.find hP_ex with hN_def
  have hN_spec : P N := Nat.find_spec hP_ex
  obtain ⟨hLN, hRle⟩ := hN_spec
  have hN_min : ∀ M, M < N → ¬ P M := fun M hM => Nat.find_min hP_ex hM
  -- Note R > 0, harmonicTail L' L' = 0, so N ≠ L'. Hence N > L'.
  have hN_gt : L' < N := by
    rcases lt_or_eq_of_le hLN with h | h
    · exact h
    · -- N = L', so harmonicTail L' L' = 0 ≥ R, contradicting R > 0.
      exfalso
      rw [← h, Finset.Ioc_self, Finset.sum_empty] at hRle
      linarith
  -- The harmonicTail to N-1 is < R (otherwise N is not minimal).
  have hN_minus_one_lt : ∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j < R := by
    by_contra h_neg
    push_neg at h_neg
    have hN_minus_pos : N - 1 < N := by omega
    have hLeN : L' ≤ N - 1 := by omega
    apply hN_min (N - 1) hN_minus_pos
    exact ⟨hLeN, h_neg⟩
  -- Residual S = R - harmonicTail L' (N-1).
  set S := R - ∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j with hS_def
  have hS_pos : 0 < S := by simp only [hS_def]; linarith
  -- The harmonic sum to N is harmonic to N-1 plus 1/N (since N > L').
  have hSplit : (∑ j ∈ Finset.Ioc L' N, (1 : ℚ) / j) =
                (∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j) + 1/(N : ℚ) := by
    have h_succ : N = (N - 1) + 1 := by omega
    have hLeN_minus : L' ≤ N - 1 := by omega
    have hN_minus_le_N : N - 1 ≤ N := by omega
    rw [show Finset.Ioc L' N = Finset.Ioc L' (N - 1) ∪ Finset.Ioc (N - 1) N from ?_]
    · rw [Finset.sum_union ?_]
      · congr 1
        rw [show Finset.Ioc (N - 1) N = {N} from by
          ext x; simp [Finset.mem_Ioc]; omega]
        rw [Finset.sum_singleton]
      · rw [Finset.disjoint_left]
        intros a ha hb
        simp [Finset.mem_Ioc] at ha hb
        omega
    · ext x
      simp [Finset.mem_Ioc, Finset.mem_union]
      omega
  -- S ≤ 1/N
  have hS_le : S ≤ 1/(N : ℚ) := by
    simp only [hS_def]
    have := hRle
    rw [hSplit] at this
    linarith
  -- N ≥ 2 (since L' ≥ 1 and N > L')
  have hN_ge_two : 2 ≤ N := by omega
  -- Apply greedy on S with minDen = N.
  have hN_pos : 0 < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
  -- Need to show N ≤ ⌈S⁻¹⌉₊.
  have hSinv_ge : (N : ℚ) ≤ S⁻¹ := by
    rw [le_inv_comm₀ hN_pos hS_pos]
    rwa [one_div] at hS_le
  have h_minDen_le_ceil : N ≤ ⌈(S⁻¹ : ℚ)⌉₊ := by
    have : (N : ℚ) ≤ ⌈(S⁻¹ : ℚ)⌉₊ := le_trans hSinv_ge (Nat.le_ceil _)
    exact_mod_cast this
  obtain ⟨E', hE'_lb, hE'_sum⟩ :=
    greedy_residual_aux S.num.natAbs S hS_pos.le le_rfl N hN_ge_two
      (Or.inr h_minDen_le_ceil)
  -- Combine harmonic-tail with E'.
  refine ⟨Finset.Ioc L' (N - 1) ∪ E', ?_, ?_⟩
  · -- All elements > L
    intros e he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · -- e ∈ Ioc L' (N-1), so e > L' ≥ L
      simp [Finset.mem_Ioc] at he
      omega
    · -- e ∈ E', so e ≥ N > L' ≥ L
      have := hE'_lb e he
      omega
  · -- Sum
    have h_disj : Disjoint (Finset.Ioc L' (N - 1)) E' := by
      rw [Finset.disjoint_left]
      intros a ha hb
      simp [Finset.mem_Ioc] at ha
      have := hE'_lb a hb
      omega
    rw [Finset.sum_union h_disj]
    have : R = (∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j) + S := by
      simp only [hS_def]; ring
    rw [this]
    rw [← hE'_sum]

/-- Replace the largest element `y` of `E` with `{y+1, y(y+1)}`. -/
private noncomputable def splitAtMax (E : Finset ℕ) : Finset ℕ := by
  classical
  exact if h : E.Nonempty then
    let y := E.max' h
    insert (y + 1) (insert (y * (y + 1)) (E.erase y))
  else E

private lemma splitAtMax_card (E : Finset ℕ) (hne : E.Nonempty)
    (h2 : ∀ e ∈ E, 2 ≤ e) : (splitAtMax E).card = E.card + 1 := by
  classical
  unfold splitAtMax
  simp only [hne, dif_pos]
  set y := E.max' hne with hy_def
  have hy_mem : y ∈ E := E.max'_mem hne
  have hy_ge2 : 2 ≤ y := h2 y hy_mem
  -- Elements of E.erase y are < y.
  have h_erase_lt : ∀ e ∈ E.erase y, e < y := by
    intro e he
    rcases Finset.mem_erase.mp he with ⟨hne_e, he_in⟩
    have : e ≤ y := E.le_max' e he_in
    omega
  -- y+1 ∉ E.erase y because elements of E.erase y are < y < y+1.
  have h_yp1_notin : (y + 1) ∉ E.erase y := by
    intro h
    have := h_erase_lt _ h
    omega
  -- y*(y+1) ∉ E.erase y because elements of E.erase y are < y ≤ y*(y+1).
  have h_yyp1_notin : y * (y + 1) ∉ E.erase y := by
    intro h
    have h_lt := h_erase_lt _ h
    have h_le : y ≤ y * (y + 1) := by
      have := Nat.le_mul_of_pos_right y (by omega : 0 < y + 1)
      simpa using this
    omega
  -- y+1 ≠ y*(y+1) when y ≥ 2.
  have h_yp1_ne_yyp1 : (y + 1) ≠ y * (y + 1) := by
    intro h
    -- y*(y+1) = (y+1) means (y-1)*(y+1) = 0, contradicting y ≥ 2.
    have : y * (y + 1) = 1 * (y + 1) := by linarith
    have h_cancel : y = 1 := by
      have hpos : 0 < y + 1 := by omega
      exact Nat.eq_of_mul_eq_mul_right hpos this
    omega
  -- y+1 ∉ insert (y*(y+1)) (E.erase y).
  have h_yp1_notin_full : (y + 1) ∉ insert (y * (y + 1)) (E.erase y) := by
    rw [Finset.mem_insert]
    push_neg
    exact ⟨h_yp1_ne_yyp1, h_yp1_notin⟩
  -- Compute card.
  rw [Finset.card_insert_of_notMem h_yp1_notin_full,
      Finset.card_insert_of_notMem h_yyp1_notin,
      Finset.card_erase_of_mem hy_mem]
  have h_card_pos : 1 ≤ E.card := Finset.card_pos.mpr hne
  omega

private lemma splitAtMax_sum (E : Finset ℕ) (hne : E.Nonempty)
    (h2 : ∀ e ∈ E, 2 ≤ e) :
    (∑ e ∈ splitAtMax E, (1 : ℚ) / e) = ∑ e ∈ E, (1 : ℚ) / e := by
  classical
  unfold splitAtMax
  simp only [hne, dif_pos]
  set y := E.max' hne with hy_def
  have hy_mem : y ∈ E := E.max'_mem hne
  have hy_ge2 : 2 ≤ y := h2 y hy_mem
  have hy_ge1 : 1 ≤ y := by omega
  -- Set up notation.
  have h_erase_lt : ∀ e ∈ E.erase y, e < y := by
    intro e he
    rcases Finset.mem_erase.mp he with ⟨hne_e, he_in⟩
    have : e ≤ y := E.le_max' e he_in
    omega
  have h_yp1_notin : (y + 1) ∉ E.erase y := by
    intro h; have := h_erase_lt _ h; omega
  have h_yyp1_notin : y * (y + 1) ∉ E.erase y := by
    intro h
    have h_lt := h_erase_lt _ h
    have h_le : y ≤ y * (y + 1) := by
      have := Nat.le_mul_of_pos_right y (by omega : 0 < y + 1)
      simpa using this
    omega
  have h_yp1_ne_yyp1 : (y + 1) ≠ y * (y + 1) := by
    intro h
    have : y * (y + 1) = 1 * (y + 1) := by linarith
    have h_cancel : y = 1 :=
      Nat.eq_of_mul_eq_mul_right (by omega : 0 < y + 1) this
    omega
  have h_yp1_notin_full : (y + 1) ∉ insert (y * (y + 1)) (E.erase y) := by
    rw [Finset.mem_insert]
    push_neg
    exact ⟨h_yp1_ne_yyp1, h_yp1_notin⟩
  -- Sum on the LHS.
  rw [Finset.sum_insert h_yp1_notin_full,
      Finset.sum_insert h_yyp1_notin]
  -- Sum on the RHS: split off y.
  rw [← Finset.sum_erase_add _ _ hy_mem]
  -- Use the split identity: 1/y = 1/(y+1) + 1/(y(y+1)).
  have h_id := egyptian_split_identity y hy_ge1
  linarith [h_id]

private lemma splitAtMax_lower_bound (E : Finset ℕ) (hne : E.Nonempty)
    (L : ℕ) (h2 : ∀ e ∈ E, 2 ≤ e) (hL : ∀ e ∈ E, L < e) :
    ∀ e ∈ splitAtMax E, L < e := by
  classical
  unfold splitAtMax
  simp only [hne, dif_pos]
  set y := E.max' hne with hy_def
  have hy_mem : y ∈ E := E.max'_mem hne
  have hy_ge2 : 2 ≤ y := h2 y hy_mem
  have hy_gt_L : L < y := hL y hy_mem
  intro e he
  rw [Finset.mem_insert] at he
  rcases he with h_eq | he
  · -- e = y + 1 > y > L
    omega
  · rw [Finset.mem_insert] at he
    rcases he with h_eq | he
    · -- e = y * (y + 1) ≥ y > L
      have h_le : y ≤ y * (y + 1) := by
        have := Nat.le_mul_of_pos_right y (by omega : 0 < y + 1)
        simpa using this
      omega
    · -- e ∈ E.erase y, so e ∈ E.
      have he_in : e ∈ E := (Finset.mem_erase.mp he).2
      exact hL e he_in

private lemma splitAtMax_nonempty (E : Finset ℕ) (hne : E.Nonempty) :
    (splitAtMax E).Nonempty := by
  classical
  unfold splitAtMax
  simp only [hne, dif_pos]
  exact Finset.insert_nonempty _ _

private lemma splitAtMax_two (E : Finset ℕ) (hne : E.Nonempty)
    (h2 : ∀ e ∈ E, 2 ≤ e) :
    ∀ e ∈ splitAtMax E, 2 ≤ e := by
  classical
  unfold splitAtMax
  simp only [hne, dif_pos]
  set y := E.max' hne with hy_def
  have hy_mem : y ∈ E := E.max'_mem hne
  have hy_ge2 : 2 ≤ y := h2 y hy_mem
  intro e he
  rw [Finset.mem_insert] at he
  rcases he with h_eq | he
  · omega
  · rw [Finset.mem_insert] at he
    rcases he with h_eq | he
    · have h_le : y ≤ y * (y + 1) := by
        have := Nat.le_mul_of_pos_right y (by omega : 0 < y + 1)
        simpa using this
      omega
    · have he_in : e ∈ E := (Finset.mem_erase.mp he).2
      exact h2 e he_in

/-- **Lemma 3 (PDF §1).** Any positive rational `R` admits Egyptian expansions
(distinct denominators all `> L`) with all sufficiently large numbers of terms. -/
theorem egyptian_expansion (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ E : Finset ℕ,
      E.card = k ∧ (∀ e ∈ E, L < e) ∧ R = ∑ e ∈ E, (1 : ℚ) / e := by
  -- Step 1: get the base expansion at L' := max L 1 so all denominators are ≥ 2.
  obtain ⟨E0, hE0_lb, hE0_sum⟩ := egyptian_expansion_exists R hR (max L 1)
  -- Step 2: E0 is nonempty (R > 0).
  have hne0 : E0.Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    rw [h_empty, Finset.sum_empty] at hE0_sum
    linarith
  -- Step 3: every element of E0 is ≥ 2.
  have h2_0 : ∀ e ∈ E0, 2 ≤ e := by
    intro e he
    have h_lt : max L 1 < e := hE0_lb e he
    have hL1 : 1 ≤ max L 1 := le_max_right _ _
    omega
  -- Step 4: every element of E0 is > L.
  have hL_0 : ∀ e ∈ E0, L < e := by
    intro e he
    have h_lt : max L 1 < e := hE0_lb e he
    have h_le : L ≤ max L 1 := le_max_left _ _
    omega
  -- Step 5: iterate splitAtMax. Define the iterate `iter n := splitAtMax^[n] E0`.
  set iter : ℕ → Finset ℕ := fun n => (splitAtMax^[n]) E0 with hiter_def
  -- Invariants by induction on n.
  have h_inv : ∀ n : ℕ,
      (iter n).Nonempty ∧
      (∀ e ∈ iter n, 2 ≤ e) ∧
      (∀ e ∈ iter n, L < e) ∧
      (iter n).card = E0.card + n ∧
      (∑ e ∈ iter n, (1 : ℚ) / e) = R := by
    intro n
    induction n with
    | zero =>
      refine ⟨hne0, h2_0, hL_0, ?_, ?_⟩
      · show (splitAtMax^[0] E0).card = E0.card + 0
        rw [Function.iterate_zero_apply]; ring
      · show (∑ e ∈ splitAtMax^[0] E0, (1 : ℚ) / e) = R
        rw [Function.iterate_zero_apply]; linarith
    | succ n ih =>
      obtain ⟨hne_n, h2_n, hL_n, hcard_n, hsum_n⟩ := ih
      have h_iter_succ : iter (n + 1) = splitAtMax (iter n) := by
        show splitAtMax^[n + 1] E0 = splitAtMax (splitAtMax^[n] E0)
        exact Function.iterate_succ_apply' splitAtMax n E0
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [h_iter_succ]; exact splitAtMax_nonempty _ hne_n
      · rw [h_iter_succ]; exact splitAtMax_two _ hne_n h2_n
      · rw [h_iter_succ]; exact splitAtMax_lower_bound _ hne_n L h2_n hL_n
      · rw [h_iter_succ, splitAtMax_card _ hne_n h2_n, hcard_n]; ring
      · rw [h_iter_succ, splitAtMax_sum _ hne_n h2_n, hsum_n]
  -- Step 6: choose K = E0.card and use n := k - E0.card.
  refine ⟨E0.card, fun k hk => ⟨iter (k - E0.card), ?_, ?_, ?_⟩⟩
  · obtain ⟨_, _, _, hcard, _⟩ := h_inv (k - E0.card)
    rw [hcard]; omega
  · obtain ⟨_, _, hL', _, _⟩ := h_inv (k - E0.card)
    exact hL'
  · obtain ⟨_, _, _, _, hsum⟩ := h_inv (k - E0.card)
    linarith

/-! ## Lemma 4 — Egyptian patterns with prescribed period and cardinality -/

/-- **Lemma 4 (PDF §1).** For integers `T, M ≥ 1` and a residue `ρ ∈ ZMod M`,
there is an Egyptian pattern `E` such that `T ∣ e` for every `e ∈ E` and
`|E| ≡ ρ (mod M)`. -/
theorem egyptian_pattern_with_period (T M : ℕ) (hT : 1 ≤ T) (hM : 1 ≤ M)
    (ρ : ZMod M) :
    ∃ E : Finset ℕ, IsEgyptianPattern E ∧ (∀ e ∈ E, T ∣ e) ∧
      (E.card : ZMod M) = ρ := by
  classical
  -- Step 1: Apply egyptian_expansion to R = T at L = 1.
  have hT_pos : (0 : ℚ) < T := by exact_mod_cast hT
  obtain ⟨K, hK⟩ := egyptian_expansion (T : ℚ) hT_pos 1
  -- Step 2: Choose k ≥ K with (k : ZMod M) = ρ.
  have hM_ne : NeZero M := ⟨Nat.one_le_iff_ne_zero.mp hM⟩
  let r : ℕ := (ρ - (K : ZMod M)).val
  let k : ℕ := K + r
  have hk_ge : k ≥ K := Nat.le_add_right _ _
  have hk_cast : (k : ZMod M) = ρ := by
    show ((K + r : ℕ) : ZMod M) = ρ
    push_cast
    show (K : ZMod M) + ((ρ - (K : ZMod M)).val : ZMod M) = ρ
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring
  -- Step 3: Get F : Finset ℕ from egyptian_expansion at this k.
  obtain ⟨F, hF_card, hF_lb, hF_sum⟩ := hK k hk_ge
  -- Each f ∈ F satisfies 2 ≤ f.
  have hF_two : ∀ f ∈ F, 2 ≤ f := fun f hf => hF_lb f hf
  -- Step 4: Build E = F.image (fun f => T * f).
  refine ⟨F.image (fun f => T * f), ?_, ?_, ?_⟩
  · -- IsEgyptianPattern E
    refine ⟨?_, ?_⟩
    · -- ∀ e ∈ E, 2 ≤ e
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨f, hf, rfl⟩ := he
      have : 2 ≤ f := hF_two f hf
      have : T * 2 ≤ T * f := Nat.mul_le_mul_left T this
      have hT2 : 2 ≤ T * 2 := by omega
      omega
    · -- ∑ e ∈ E, 1/e = 1
      have h_inj : Set.InjOn (fun f => T * f) F := by
        intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < T) hab
      rw [Finset.sum_image h_inj]
      have hT_ne : (T : ℚ) ≠ 0 := by
        have : (0 : ℚ) < T := hT_pos
        linarith
      have h_eq : ∀ f ∈ F, (1 : ℚ) / (T * f : ℕ) = (1 / T) * (1 / f) := by
        intro f hf
        have hf2 : 2 ≤ f := hF_two f hf
        have hf_ne : (f : ℚ) ≠ 0 := by
          have : (0 : ℚ) < f := by exact_mod_cast (by omega : 0 < f)
          linarith
        push_cast
        field_simp
      rw [Finset.sum_congr rfl h_eq, ← Finset.mul_sum, ← hF_sum]
      field_simp
  · -- ∀ e ∈ E, T ∣ e
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨f, _, rfl⟩ := he
    exact Dvd.intro f rfl
  · -- (E.card : ZMod M) = ρ
    have h_inj : Function.Injective (fun f => T * f) := by
      intro a b hab
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < T) hab
    rw [Finset.card_image_of_injective F h_inj, hF_card]
    exact hk_cast

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/PolynomialPeriod.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — §1 Egyptian switches, Lemma 5 (polynomial periodicity).

  * `int_poly_eval_congr` — `x ≡ y (mod M) → P.eval x ≡ P.eval y (mod M)` for
                            `P : ℤ[X]`.
  * `polynomial_periodicity` — Lemma 5 for ℚ-polynomials with integral multiple.

The proof goes via denominator clearing: pick `B` with `B p ∈ ℤ[X]`, get the
ℤ-version periodicity, and divide back by `B` using integer-valuedness.

All axiom-free.
-/


namespace PolynomialEgyptianSums

open Polynomial

/-- For an integer-coefficient polynomial `P : ℤ[X]` and integers `x ≡ y (mod M)`,
`P.eval x ≡ P.eval y (mod M)`. Standard polynomial congruence. -/
lemma int_poly_eval_congr (P : ℤ[X]) {M x y : ℤ}
    (hxy : x ≡ y [ZMOD M]) :
    (P.eval x : ℤ) ≡ P.eval y [ZMOD M] := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]
    exact hp.add hq
  | monomial n c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact (Int.ModEq.refl c).mul (hxy.pow n)

set_option linter.unusedVariables false in
/-- **Lemma 5 (PDF §1).** If `B p(x) ∈ ℤ[x]` and `x ≡ y (mod m B)`, then
`p(x) ≡ p(y) (mod m)`. So `m B` is a period of the integer values of `p` modulo
`m`. -/
theorem polynomial_periodicity
    (p : ℚ[X]) (hp_int : IntValued p)
    (B : ℕ) (hBpos : 1 ≤ B) (hB : HasIntegralMultiple B p)
    (m : ℕ) (hm : 1 ≤ m) (x y : ℤ)
    (hxy : x ≡ y [ZMOD ((m * B : ℕ) : ℤ)]) :
    intEval p hp_int x ≡ intEval p hp_int y [ZMOD ((m : ℕ) : ℤ)] := by
  obtain ⟨R, hR⟩ := hB
  -- R.eval x ≡ R.eval y (mod m * B).
  have h_R_congr : R.eval x ≡ R.eval y [ZMOD ((m * B : ℕ) : ℤ)] :=
    int_poly_eval_congr R hxy
  -- (R.eval z : ℚ) = B * p.eval z for all z.
  have h_R_eval : ∀ z : ℤ, ((R.eval z : ℤ) : ℚ) = (B : ℚ) * p.eval (z : ℚ) := by
    intro z
    have h1 : ((R.map (Int.castRingHom ℚ)).eval ((z : ℤ) : ℚ)) =
        (Polynomial.C (B : ℚ) * p).eval ((z : ℚ)) := by
      rw [hR]
    rw [Polynomial.eval_map, Polynomial.eval_mul, Polynomial.eval_C] at h1
    -- h1 : eval₂ (Int.castRingHom ℚ) (↑z) R = ↑B * eval ↑z p
    -- Polynomial.eval₂_at_apply : eval₂ f (f r) p = f (eval r p), so with f = Int.castRingHom ℚ,
    -- eval₂ (Int.castRingHom ℚ) ((z : ℤ) : ℚ) R = ((R.eval z : ℤ) : ℚ).
    have h2 : Polynomial.eval₂ (Int.castRingHom ℚ) ((z : ℤ) : ℚ) R = ((R.eval z : ℤ) : ℚ) :=
      Polynomial.eval₂_at_apply (Int.castRingHom ℚ) z
    rw [h2] at h1
    exact h1
  -- Hence R.eval z = B * intEval p hp_int z (in ℤ) via Int.cast injectivity into ℚ.
  have h_R_int_eval : ∀ z : ℤ, R.eval z = (B : ℤ) * intEval p hp_int z := by
    intro z
    have h1 := h_R_eval z
    have h2 := intEval_spec p hp_int z
    have : ((R.eval z : ℤ) : ℚ) = (((B : ℤ) * intEval p hp_int z : ℤ) : ℚ) := by
      push_cast
      rw [h1, ← h2]
    exact_mod_cast this
  rw [h_R_int_eval x, h_R_int_eval y] at h_R_congr
  -- h_R_congr : (B : ℤ) * intEval p hp_int x ≡ (B : ℤ) * intEval p hp_int y [ZMOD (m * B : ℤ)]
  -- Goal: intEval p hp_int x ≡ intEval p hp_int y [ZMOD m]
  -- Use: m * B ∣ B * (a - b) ↔ m ∣ (a - b), with B > 0.
  have hBpos_int : (0 : ℤ) < (B : ℤ) := by exact_mod_cast hBpos
  have hBne : (B : ℤ) ≠ 0 := ne_of_gt hBpos_int
  -- Convert h_R_congr to divisibility form.
  have h_dvd : ((m * B : ℕ) : ℤ) ∣
      ((B : ℤ) * intEval p hp_int y - (B : ℤ) * intEval p hp_int x) :=
    Int.modEq_iff_dvd.mp h_R_congr
  -- Rewrite as ((m * B : ℕ) : ℤ) ∣ (B : ℤ) * (intEval p hp_int y - intEval p hp_int x).
  have h_dvd' : ((m * B : ℕ) : ℤ) ∣
      (B : ℤ) * (intEval p hp_int y - intEval p hp_int x) := by
    have heq : (B : ℤ) * intEval p hp_int y - (B : ℤ) * intEval p hp_int x =
        (B : ℤ) * (intEval p hp_int y - intEval p hp_int x) := by ring
    rwa [heq] at h_dvd
  -- ((m * B : ℕ) : ℤ) = (B : ℤ) * (m : ℤ).
  have hmB : ((m * B : ℕ) : ℤ) = (B : ℤ) * (m : ℤ) := by push_cast; ring
  rw [hmB] at h_dvd'
  -- (B : ℤ) * (m : ℤ) ∣ (B : ℤ) * (a - b) ↔ (m : ℤ) ∣ (a - b) (using B ≠ 0).
  have h_m_dvd : (m : ℤ) ∣ (intEval p hp_int y - intEval p hp_int x) :=
    (mul_dvd_mul_iff_left hBne).mp h_dvd'
  exact Int.modEq_iff_dvd.mpr h_m_dvd

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/Switching.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — §1 Egyptian switches, switching polynomials & Lemma 6.

  * `switchingPoly p E := ∑_{e ∈ E} p(e·) - p`  — the switching polynomial.
  * `switchingPoly_leadingCoeff` — `lc(Q_E) = lc(p) · (∑_{e ∈ E} e^r - 1) > 0`.
  * `switchValueSet`             — the set of all integer values `Q_E(n)` over
                                    all Egyptian patterns `E` and `n ≥ 1`.
  * `switching_values_span_top`  — Lemma 6 (corrected): `Ideal.span (switchValueSet) = ⊤`,
                                    i.e. the gcd of all switching values is 1.
  * `finite_switch_values_generate_zmod` — finite version usable for the
                                            correction-slot construction.

Lemma 6 is axiom-free; uses Lemmas 4, 5 and `IntValued p`.
-/


namespace PolynomialEgyptianSums

open Polynomial Finset

/-- The **switching polynomial** `Q_E(x) := ∑_{e ∈ E} p(e·x) - p(x)` for an
Egyptian pattern `E`. -/
noncomputable def switchingPoly (p : ℚ[X]) (E : Finset ℕ) : ℚ[X] :=
  (E.sum fun e => p.comp ((Polynomial.C (e : ℚ)) * Polynomial.X)) - p

/-- Direct evaluation: `Q_E(c) = ∑_{e ∈ E} p(e · c) - p(c)`. The p-increment
when swapping a denominator `c` for `{e c : e ∈ E}`. -/
lemma switchingPoly_eval_nat (p : ℚ[X]) (E : Finset ℕ) (c : ℕ) :
    (switchingPoly p E).eval ((c : ℕ) : ℚ) =
      (∑ e ∈ E, p.eval (((e * c : ℕ) : ℕ) : ℚ)) - p.eval ((c : ℕ) : ℚ) := by
  unfold switchingPoly
  rw [Polynomial.eval_sub, Polynomial.eval_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  push_cast
  ring_nf

/-- Reciprocal-preservation property: `∑_{e ∈ E} 1/(e c) = 1/c` whenever `E` is
an Egyptian pattern (`∑ 1/e = 1`) and `c > 0`. The arithmetic core of the
"switch" operation that preserves the reciprocal sum. -/
lemma IsEgyptianPattern.sum_scaled_recip
    {E : Finset ℕ} (hE : IsEgyptianPattern E) (c : ℕ) (hc : 0 < c) :
    (∑ e ∈ E, (1 : ℚ) / ((e * c : ℕ) : ℚ)) = (1 : ℚ) / (c : ℚ) := by
  have hc_q : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc
  have hc_ne : (c : ℚ) ≠ 0 := ne_of_gt hc_q
  -- ∑ 1/(e*c) = (1/c) * ∑ 1/e = (1/c) * 1.
  have h_factor : (∑ e ∈ E, (1 : ℚ) / ((e * c : ℕ) : ℚ)) =
      (1 / (c : ℚ)) * ∑ e ∈ E, (1 : ℚ) / (e : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have he_pos : 1 ≤ e := le_of_lt (lt_of_lt_of_le (by norm_num) (hE.1 e he))
    have he_q : (0 : ℚ) < (e : ℚ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one he_pos)
    have he_ne : (e : ℚ) ≠ 0 := ne_of_gt he_q
    push_cast
    field_simp
  rw [h_factor, hE.2, mul_one]

def scaledPatternDenoms (E : Finset ℕ) (c : ℕ) : Finset ℕ :=
  E.image (fun e => e * c)

lemma scaledPatternDenoms_sum_recip
    {E : Finset ℕ} (hE : IsEgyptianPattern E) {c : ℕ} (hc : 0 < c) :
    (∑ n ∈ scaledPatternDenoms E c, (1 : ℚ) / (n : ℚ)) =
      (1 : ℚ) / (c : ℚ) := by
  unfold scaledPatternDenoms
  rw [Finset.sum_image]
  · exact IsEgyptianPattern.sum_scaled_recip hE c hc
  · intro e _ e' _ heq
    exact Nat.eq_of_mul_eq_mul_right hc heq

lemma scaledPatternDenoms_eval_sum
    (p : ℚ[X]) (E : Finset ℕ) {c : ℕ} (hc : 0 < c) :
    (∑ n ∈ scaledPatternDenoms E c, p.eval ((n : ℕ) : ℚ)) =
      ∑ e ∈ E, p.eval (((e * c : ℕ) : ℕ) : ℚ) := by
  unfold scaledPatternDenoms
  rw [Finset.sum_image]
  intro e _ e' _ heq
  exact Nat.eq_of_mul_eq_mul_right hc heq

lemma scaledPatternDenoms_intEval_sum
    (p : ℚ[X]) (hp : IntValued p) (E : Finset ℕ) {c : ℕ} (hc : 0 < c) :
    (∑ n ∈ scaledPatternDenoms E c, intEval p hp ((n : ℕ) : ℤ)) =
      ∑ e ∈ E, intEval p hp (((e * c : ℕ) : ℕ) : ℤ) := by
  unfold scaledPatternDenoms
  rw [Finset.sum_image]
  intro e _ e' _ heq
  exact Nat.eq_of_mul_eq_mul_right hc heq

/-- The leading coefficient of `Q_E` is `lc(p) · (∑_{e ∈ E} e^r - 1)`, where
`r := deg p`. Positive whenever `lc(p) > 0` and `E` is non-trivial (since
`∑ e^r ≥ ∑ e ≥ 2|E| ≥ 2 > 1`). -/
lemma switchingPoly_leadingCoeff (p : ℚ[X]) (E : Finset ℕ)
    (hE : IsEgyptianPattern E) (h_lead_pos : 0 < p.leadingCoeff)
    (h_nonconst : 1 ≤ p.natDegree) :
    0 < (switchingPoly p E).leadingCoeff := by
  classical
  obtain ⟨h2, hsum⟩ := hE
  -- E is nonempty since otherwise ∑ 1/e = 0 ≠ 1.
  have hne : E.Nonempty := by
    rcases Finset.eq_empty_or_nonempty E with h | h
    · rw [h, Finset.sum_empty] at hsum
      norm_num at hsum
    · exact h
  -- p ≠ 0 since natDegree ≥ 1.
  have hp_ne : p ≠ 0 := by
    intro h
    rw [h] at h_nonconst
    simp at h_nonconst
  set r := p.natDegree with hr_def
  -- Each q_e := p.comp (C e * X) has natDegree r and leadingCoeff = lc(p) * e^r.
  have h_nat_deg : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = r := by
    intro e he
    have he_ne : (e : ℚ) ≠ 0 := by
      have := h2 e he
      exact_mod_cast (by omega : e ≠ 0)
    rw [Polynomial.natDegree_comp]
    rw [Polynomial.natDegree_C_mul_X (e : ℚ) he_ne]
    ring
  have h_lc : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff =
        p.leadingCoeff * ((e : ℚ) ^ r) := by
    intro e he
    have he_ne : (e : ℚ) ≠ 0 := by
      have := h2 e he
      exact_mod_cast (by omega : e ≠ 0)
    have h_deg : (Polynomial.C (e : ℚ) * Polynomial.X).natDegree = 1 :=
      Polynomial.natDegree_C_mul_X (e : ℚ) he_ne
    rw [Polynomial.leadingCoeff_comp (by rw [h_deg]; norm_num)]
    rw [Polynomial.leadingCoeff_C_mul_X]
  -- Each q_e ≠ 0 since natDegree = r ≥ 1.
  have h_q_e_ne : ∀ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X) ≠ 0 := by
    intro e he h_eq
    have : (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = 0 := by
      rw [h_eq]; simp
    rw [h_nat_deg e he] at this
    omega
  -- Each q_e has degree exactly r in WithBot ℕ.
  have h_q_e_deg : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = (r : WithBot ℕ) := by
    intro e he
    rw [Polynomial.degree_eq_natDegree (h_q_e_ne e he)]
    rw [h_nat_deg e he]
  -- ∑ e^r ≥ 2 (since each e^r ≥ 2 and E.card ≥ 1).
  have h_sum_pow_ge : (2 : ℚ) ≤ (∑ e ∈ E, ((e : ℚ) ^ r)) := by
    have h_card_pos : 1 ≤ E.card := Finset.card_pos.mpr hne
    have step : ∀ e ∈ E, (2 : ℚ) ≤ ((e : ℚ) ^ r) := by
      intro e he
      have he2 : (2 : ℚ) ≤ e := by exact_mod_cast h2 e he
      have hr_le : 1 ≤ r := h_nonconst
      calc (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
      _ ≤ (2 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr_le
      _ ≤ (e : ℚ) ^ r := pow_le_pow_left₀ (by norm_num) he2 _
    have hsum2 : (∑ _ ∈ E, (2 : ℚ)) ≤ (∑ e ∈ E, ((e : ℚ) ^ r)) :=
      Finset.sum_le_sum step
    have hsum2_eq : (∑ _ ∈ E, (2 : ℚ)) = 2 * E.card := by
      rw [Finset.sum_const]; ring
    rw [hsum2_eq] at hsum2
    have h_card_q : (1 : ℚ) ≤ E.card := by exact_mod_cast h_card_pos
    linarith
  -- Sum of leading coefficients is positive (so nonzero).
  have h_sum_lc_pos : 0 <
      ∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
    have h_eq :
        (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) =
        ∑ e ∈ E, p.leadingCoeff * ((e : ℚ) ^ r) :=
      Finset.sum_congr rfl h_lc
    rw [h_eq, ← Finset.mul_sum]
    apply mul_pos h_lead_pos
    linarith
  have h_sum_lc_ne :
      (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) ≠ 0 :=
    ne_of_gt h_sum_lc_pos
  -- Sum's leadingCoeff = ∑ leadingCoeff(q_e) = lc(p) · ∑ e^r.
  have h_sum_lc_eq :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        = ∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff :=
    Polynomial.leadingCoeff_sum_of_degree_eq h_q_e_deg h_sum_lc_ne
  -- Sum has natDegree exactly r.
  have h_sum_natDegree :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = r := by
    have h_le :
        (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree ≤ r := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      rw [h_nat_deg i hi]
    apply le_antisymm h_le
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.finset_sum_coeff]
    have h_coeff_eq : ∀ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).coeff r =
        (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
      intro e he
      rw [show (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff = _ from rfl,
          Polynomial.leadingCoeff, h_nat_deg e he]
    rw [Finset.sum_congr rfl h_coeff_eq]
    exact h_sum_lc_ne
  -- Sum's leadingCoeff = lc(p) · ∑ e^r.
  have h_sum_lc_val :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        = p.leadingCoeff * ∑ e ∈ E, ((e : ℚ) ^ r) := by
    rw [h_sum_lc_eq]
    have h_eq :
        (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) =
        ∑ e ∈ E, p.leadingCoeff * ((e : ℚ) ^ r) :=
      Finset.sum_congr rfl h_lc
    rw [h_eq, ← Finset.mul_sum]
  -- Sum and p have the same degree r in WithBot ℕ.
  have h_sum_deg :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = (r : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree, h_sum_natDegree]
    intro h
    rw [h] at h_sum_natDegree
    simp at h_sum_natDegree
    omega
  have h_p_deg : p.degree = (r : WithBot ℕ) :=
    Polynomial.degree_eq_natDegree hp_ne
  -- Leading coefficients differ since ∑ e^r ≥ 2 > 1.
  have h_p_lc_ne : p.leadingCoeff ≠ 0 := ne_of_gt h_lead_pos
  have h_lc_diff :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        ≠ p.leadingCoeff := by
    rw [h_sum_lc_val]
    intro h_eq
    have : p.leadingCoeff * (∑ e ∈ E, ((e : ℚ) ^ r) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h2
    · exact h_p_lc_ne h1
    · linarith
  unfold switchingPoly
  have h_deg_eq :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = p.degree := by
    rw [h_sum_deg, h_p_deg]
  rw [Polynomial.leadingCoeff_sub_of_degree_eq h_deg_eq h_lc_diff]
  rw [h_sum_lc_val]
  have h_rewrite :
      p.leadingCoeff * ∑ e ∈ E, ((e : ℚ) ^ r) - p.leadingCoeff
        = p.leadingCoeff * ((∑ e ∈ E, ((e : ℚ) ^ r)) - 1) := by ring
  rw [h_rewrite]
  apply mul_pos h_lead_pos
  linarith

/-! ### Exact `natDegree` and `leadingCoeff` formulas for `switchingPoly`

These are needed in Theorem 1 for the asymptotic comparison `λ < μ < a Θ P^{2r}`,
where `Θ = ∑_{e ∈ E} e^r - 1` for `E = E0`. -/

/-- The natDegree of `switchingPoly p E` equals `natDegree p` whenever `E` is an
Egyptian pattern, `lc(p) > 0`, and `1 ≤ natDegree p`. -/
lemma switchingPoly_natDegree_eq (p : ℚ[X]) (E : Finset ℕ)
    (hE : IsEgyptianPattern E) (h_lead_pos : 0 < p.leadingCoeff)
    (h_nonconst : 1 ≤ p.natDegree) :
    (switchingPoly p E).natDegree = p.natDegree := by
  classical
  obtain ⟨h2, hsum⟩ := hE
  have hne : E.Nonempty := by
    rcases Finset.eq_empty_or_nonempty E with h | h
    · rw [h, Finset.sum_empty] at hsum; norm_num at hsum
    · exact h
  have hp_ne : p ≠ 0 := by
    intro h; rw [h] at h_nonconst; simp at h_nonconst
  set r := p.natDegree with hr_def
  have h_nat_deg : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = r := by
    intro e he
    have he_ne : (e : ℚ) ≠ 0 := by
      have := h2 e he; exact_mod_cast (by omega : e ≠ 0)
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X (e : ℚ) he_ne]; ring
  have h_q_e_ne : ∀ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X) ≠ 0 := by
    intro e he h_eq
    have : (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = 0 := by
      rw [h_eq]; simp
    rw [h_nat_deg e he] at this; omega
  have h_q_e_deg : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = (r : WithBot ℕ) := by
    intro e he
    rw [Polynomial.degree_eq_natDegree (h_q_e_ne e he), h_nat_deg e he]
  have h_lc : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff =
        p.leadingCoeff * ((e : ℚ) ^ r) := by
    intro e he
    have he_ne : (e : ℚ) ≠ 0 := by
      have := h2 e he; exact_mod_cast (by omega : e ≠ 0)
    have h_deg : (Polynomial.C (e : ℚ) * Polynomial.X).natDegree = 1 :=
      Polynomial.natDegree_C_mul_X (e : ℚ) he_ne
    rw [Polynomial.leadingCoeff_comp (by rw [h_deg]; norm_num),
        Polynomial.leadingCoeff_C_mul_X]
  have h_sum_pow_ge : (2 : ℚ) ≤ (∑ e ∈ E, ((e : ℚ) ^ r)) := by
    have h_card_pos : 1 ≤ E.card := Finset.card_pos.mpr hne
    have step : ∀ e ∈ E, (2 : ℚ) ≤ ((e : ℚ) ^ r) := by
      intro e he
      have he2 : (2 : ℚ) ≤ e := by exact_mod_cast h2 e he
      have hr_le : 1 ≤ r := h_nonconst
      calc (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
      _ ≤ (2 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr_le
      _ ≤ (e : ℚ) ^ r := pow_le_pow_left₀ (by norm_num) he2 _
    have hsum2 : (∑ _ ∈ E, (2 : ℚ)) ≤ (∑ e ∈ E, ((e : ℚ) ^ r)) :=
      Finset.sum_le_sum step
    have hsum2_eq : (∑ _ ∈ E, (2 : ℚ)) = 2 * E.card := by
      rw [Finset.sum_const]; ring
    rw [hsum2_eq] at hsum2
    have h_card_q : (1 : ℚ) ≤ E.card := by exact_mod_cast h_card_pos
    linarith
  have h_sum_lc_pos : 0 <
      ∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
    have h_eq :
        (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) =
        ∑ e ∈ E, p.leadingCoeff * ((e : ℚ) ^ r) :=
      Finset.sum_congr rfl h_lc
    rw [h_eq, ← Finset.mul_sum]; apply mul_pos h_lead_pos; linarith
  have h_sum_lc_ne :
      (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) ≠ 0 :=
    ne_of_gt h_sum_lc_pos
  have h_sum_natDegree :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = r := by
    have h_le :
        (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree ≤ r := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi; rw [h_nat_deg i hi]
    apply le_antisymm h_le
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.finset_sum_coeff]
    have h_coeff_eq : ∀ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).coeff r =
        (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
      intro e he
      rw [show (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff = _ from rfl,
          Polynomial.leadingCoeff, h_nat_deg e he]
    rw [Finset.sum_congr rfl h_coeff_eq]; exact h_sum_lc_ne
  have h_sum_lc_eq :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        = ∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff :=
    Polynomial.leadingCoeff_sum_of_degree_eq h_q_e_deg h_sum_lc_ne
  have h_sum_lc_val :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        = p.leadingCoeff * ∑ e ∈ E, ((e : ℚ) ^ r) := by
    rw [h_sum_lc_eq]
    have h_eq :
        (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) =
        ∑ e ∈ E, p.leadingCoeff * ((e : ℚ) ^ r) :=
      Finset.sum_congr rfl h_lc
    rw [h_eq, ← Finset.mul_sum]
  have h_sum_deg :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = (r : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree, h_sum_natDegree]
    intro h; rw [h] at h_sum_natDegree; simp at h_sum_natDegree; omega
  have h_p_deg : p.degree = (r : WithBot ℕ) := Polynomial.degree_eq_natDegree hp_ne
  have h_p_lc_ne : p.leadingCoeff ≠ 0 := ne_of_gt h_lead_pos
  have h_lc_diff :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        ≠ p.leadingCoeff := by
    rw [h_sum_lc_val]
    intro h_eq
    have : p.leadingCoeff * (∑ e ∈ E, ((e : ℚ) ^ r) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h2
    · exact h_p_lc_ne h1
    · linarith
  unfold switchingPoly
  -- (sum - p).natDegree ≤ max sum.natDegree p.natDegree = r.
  have h_le : (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X) - p).natDegree ≤ r := by
    have := Polynomial.natDegree_sub_le
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)) p
    rw [h_sum_natDegree, ← hr_def] at this
    omega
  -- coeff at r is sum.lc - p.lc, which is nonzero by h_lc_diff.
  have h_coeff_ne : (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X) - p).coeff r ≠ 0 := by
    rw [Polynomial.coeff_sub]
    have h1 : (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).coeff r =
        (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
      rw [Polynomial.leadingCoeff, h_sum_natDegree]
    have h2 : p.coeff r = p.leadingCoeff := by rw [Polynomial.leadingCoeff, ← hr_def]
    rw [h1, h2]
    intro h_eq
    apply h_lc_diff
    linarith
  have h_ge : r ≤ (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X) - p).natDegree :=
    Polynomial.le_natDegree_of_ne_zero h_coeff_ne
  omega

/-- Exact leading-coefficient formula:
`lc(switchingPoly p E) = lc(p) · (∑_{e∈E} e^r − 1)` where `r = natDegree p`. -/
lemma switchingPoly_leadingCoeff_eq (p : ℚ[X]) (E : Finset ℕ)
    (hE : IsEgyptianPattern E) (h_lead_pos : 0 < p.leadingCoeff)
    (h_nonconst : 1 ≤ p.natDegree) :
    (switchingPoly p E).leadingCoeff =
      p.leadingCoeff * ((∑ e ∈ E, ((e : ℚ) ^ p.natDegree)) - 1) := by
  classical
  obtain ⟨h2, hsum⟩ := hE
  have hne : E.Nonempty := by
    rcases Finset.eq_empty_or_nonempty E with h | h
    · rw [h, Finset.sum_empty] at hsum; norm_num at hsum
    · exact h
  have hp_ne : p ≠ 0 := by
    intro h; rw [h] at h_nonconst; simp at h_nonconst
  set r := p.natDegree with hr_def
  have h_nat_deg : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = r := by
    intro e he
    have he_ne : (e : ℚ) ≠ 0 := by
      have := h2 e he; exact_mod_cast (by omega : e ≠ 0)
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X (e : ℚ) he_ne]; ring
  have h_q_e_ne : ∀ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X) ≠ 0 := by
    intro e he h_eq
    have : (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = 0 := by
      rw [h_eq]; simp
    rw [h_nat_deg e he] at this; omega
  have h_q_e_deg : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = (r : WithBot ℕ) := by
    intro e he
    rw [Polynomial.degree_eq_natDegree (h_q_e_ne e he), h_nat_deg e he]
  have h_lc : ∀ e ∈ E,
      (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff =
        p.leadingCoeff * ((e : ℚ) ^ r) := by
    intro e he
    have he_ne : (e : ℚ) ≠ 0 := by
      have := h2 e he; exact_mod_cast (by omega : e ≠ 0)
    have h_deg : (Polynomial.C (e : ℚ) * Polynomial.X).natDegree = 1 :=
      Polynomial.natDegree_C_mul_X (e : ℚ) he_ne
    rw [Polynomial.leadingCoeff_comp (by rw [h_deg]; norm_num),
        Polynomial.leadingCoeff_C_mul_X]
  have h_sum_pow_ge : (2 : ℚ) ≤ (∑ e ∈ E, ((e : ℚ) ^ r)) := by
    have h_card_pos : 1 ≤ E.card := Finset.card_pos.mpr hne
    have step : ∀ e ∈ E, (2 : ℚ) ≤ ((e : ℚ) ^ r) := by
      intro e he
      have he2 : (2 : ℚ) ≤ e := by exact_mod_cast h2 e he
      have hr_le : 1 ≤ r := h_nonconst
      calc (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
      _ ≤ (2 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr_le
      _ ≤ (e : ℚ) ^ r := pow_le_pow_left₀ (by norm_num) he2 _
    have hsum2 : (∑ _ ∈ E, (2 : ℚ)) ≤ (∑ e ∈ E, ((e : ℚ) ^ r)) :=
      Finset.sum_le_sum step
    have hsum2_eq : (∑ _ ∈ E, (2 : ℚ)) = 2 * E.card := by
      rw [Finset.sum_const]; ring
    rw [hsum2_eq] at hsum2
    have h_card_q : (1 : ℚ) ≤ E.card := by exact_mod_cast h_card_pos
    linarith
  have h_sum_lc_pos : 0 <
      ∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
    have h_eq :
        (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) =
        ∑ e ∈ E, p.leadingCoeff * ((e : ℚ) ^ r) :=
      Finset.sum_congr rfl h_lc
    rw [h_eq, ← Finset.mul_sum]; apply mul_pos h_lead_pos; linarith
  have h_sum_lc_ne :
      (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) ≠ 0 :=
    ne_of_gt h_sum_lc_pos
  have h_sum_lc_eq :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        = ∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff :=
    Polynomial.leadingCoeff_sum_of_degree_eq h_q_e_deg h_sum_lc_ne
  have h_sum_lc_val :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        = p.leadingCoeff * ∑ e ∈ E, ((e : ℚ) ^ r) := by
    rw [h_sum_lc_eq]
    have h_eq :
        (∑ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff) =
        ∑ e ∈ E, p.leadingCoeff * ((e : ℚ) ^ r) :=
      Finset.sum_congr rfl h_lc
    rw [h_eq, ← Finset.mul_sum]
  have h_sum_natDegree :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree = r := by
    have h_le :
        (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).natDegree ≤ r := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi; rw [h_nat_deg i hi]
    apply le_antisymm h_le
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.finset_sum_coeff]
    have h_coeff_eq : ∀ e ∈ E, (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).coeff r =
        (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff := by
      intro e he
      rw [show (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff = _ from rfl,
          Polynomial.leadingCoeff, h_nat_deg e he]
    rw [Finset.sum_congr rfl h_coeff_eq]; exact h_sum_lc_ne
  have h_sum_deg :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = (r : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree, h_sum_natDegree]
    intro h; rw [h] at h_sum_natDegree; simp at h_sum_natDegree; omega
  have h_p_deg : p.degree = (r : WithBot ℕ) := Polynomial.degree_eq_natDegree hp_ne
  have h_deg_eq :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).degree = p.degree := by
    rw [h_sum_deg, h_p_deg]
  have h_p_lc_ne : p.leadingCoeff ≠ 0 := ne_of_gt h_lead_pos
  have h_lc_diff :
      (∑ e ∈ E, p.comp (Polynomial.C (e : ℚ) * Polynomial.X)).leadingCoeff
        ≠ p.leadingCoeff := by
    rw [h_sum_lc_val]
    intro h_eq
    have : p.leadingCoeff * (∑ e ∈ E, ((e : ℚ) ^ r) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h2
    · exact h_p_lc_ne h1
    · linarith
  unfold switchingPoly
  rw [Polynomial.leadingCoeff_sub_of_degree_eq h_deg_eq h_lc_diff,
      h_sum_lc_val]
  ring

/-! ### Closure of `IntValued` under `switchingPoly` -/

/-- Composition `p(e · x)` of an integer-valued polynomial with `e ∈ ℕ` is
integer-valued. -/
lemma IntValued.comp_nat_mul_X (p : ℚ[X]) (hp : IntValued p) (e : ℕ) :
    IntValued (p.comp (Polynomial.C (e : ℚ) * Polynomial.X)) := by
  intro z
  obtain ⟨k, hk⟩ := hp ((e : ℤ) * z)
  refine ⟨k, ?_⟩
  rw [hk, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
  push_cast
  ring

/-- `switchingPoly p E` is integer-valued whenever `p` is. -/
lemma switchingPoly_intValued (p : ℚ[X]) (hp : IntValued p) (E : Finset ℕ) :
    IntValued (switchingPoly p E) := by
  unfold switchingPoly
  exact IntValued.sub
    (IntValued.sum E _ (fun e _ => IntValued.comp_nat_mul_X p hp e))
    hp

lemma intEval_switchingPoly_nat (p : ℚ[X]) (hp : IntValued p)
    (E : Finset ℕ) (c : ℕ) :
    intEval (switchingPoly p E) (switchingPoly_intValued p hp E) ((c : ℕ) : ℤ) =
      (∑ e ∈ E, intEval p hp (((e * c : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((c : ℕ) : ℤ) := by
  have hq :
      ((intEval (switchingPoly p E) (switchingPoly_intValued p hp E)
        ((c : ℕ) : ℤ) : ℤ) : ℚ) =
      (((∑ e ∈ E, intEval p hp (((e * c : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((c : ℕ) : ℤ) : ℤ) : ℚ) := by
    rw [intEval_spec]
    change (switchingPoly p E).eval ((c : ℕ) : ℚ) =
      (((∑ e ∈ E, intEval p hp (((e * c : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((c : ℕ) : ℤ) : ℤ) : ℚ)
    rw [switchingPoly_eval_nat]
    push_cast
    congr 1
    · apply Finset.sum_congr rfl
      intro e _
      rw [intEval_spec]
      congr 1
      push_cast
      ring
    · rw [intEval_spec]
      rfl
  exact_mod_cast hq

lemma scaledPatternDenoms_intEval_sum_sub
    (p : ℚ[X]) (hp : IntValued p) (E : Finset ℕ) {c : ℕ} (hc : 0 < c) :
    (∑ n ∈ scaledPatternDenoms E c, intEval p hp ((n : ℕ) : ℤ)) -
        intEval p hp ((c : ℕ) : ℤ) =
      intEval (switchingPoly p E) (switchingPoly_intValued p hp E)
        ((c : ℕ) : ℤ) := by
  rw [scaledPatternDenoms_intEval_sum p hp E hc,
    intEval_switchingPoly_nat p hp E c]

/-- The set of **integer values** of switching polynomials over all Egyptian
patterns and positive integers. -/
noncomputable def switchValueSet (p : ℚ[X]) (hp : IntValued p) : Set ℤ :=
  { z | ∃ E : Finset ℕ, ∃ n : ℕ,
      IsEgyptianPattern E ∧ 1 ≤ n ∧
      z = (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ))
            - intEval p hp ((n : ℕ) : ℤ) }

set_option linter.unusedVariables false in
/-- **Lemma 6 (PDF §1, corrected).** If `p` has degree `≥ 1`, positive leading
coefficient, and no fixed divisor on positive integers, then the integer values
of all switching polynomials `Q_E(n)` (over Egyptian patterns `E` and positive
integers `n`) generate the unit ideal of `ℤ`.

Proof (PDF §1): Suppose a prime `ℓ` divides every value. Choose `B` with
`B p ∈ ℤ[X]` (`exists_integral_multiple`); set `T_ℓ = ℓ B`. By Lemma 4 choose `E`
with `T_ℓ ∣ e` for all `e ∈ E` and `|E| ≡ 0 (mod ℓ)`. By Lemma 5, `p(e n) ≡ p(0)
(mod ℓ)` for `e ∈ E, n ≥ 1`, so `Q_E(n) ≡ |E| p(0) - p(n) ≡ -p(n) (mod ℓ)`.
Hence `ℓ ∣ p(n)` for all `n`, contradicting no-fixed-divisor. -/
theorem switching_values_span_top (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed : NoFixedDivisor p hp) :
    Ideal.span (switchValueSet p hp) = ⊤ := by
  classical
  by_contra h_top
  -- Step 1: Extract a prime ℓ : ℕ such that ℓ ∣ z for every z ∈ switchValueSet.
  obtain ⟨M, hM_max, hM_le⟩ := Ideal.exists_le_maximal _ h_top
  haveI hM_prime : M.IsPrime := hM_max.isPrime
  haveI hM_principal : Submodule.IsPrincipal M := IsPrincipalIdealRing.principal M
  -- ℤ is not a field, so the maximal ideal M ≠ ⊥.
  have h_field : ¬ IsField ℤ := by
    intro h
    haveI := h.toField
    have h2 : (2 : ℤ) ≠ 0 := by norm_num
    obtain ⟨a, ha⟩ := h.mul_inv_cancel h2
    have : (2 : ℤ) ∣ 1 := ⟨a, ha.symm⟩
    omega
  have hM_ne_bot : M ≠ ⊥ := by
    intro h_bot
    rw [h_bot] at hM_max
    exact h_field (Ring.isField_iff_maximal_bot.mpr hM_max)
  -- The generator a is prime, and a.natAbs = ℓ is a prime natural.
  set a := Submodule.IsPrincipal.generator M with ha_def
  have ha : Prime a := Submodule.IsPrincipal.prime_generator_of_isPrime M hM_ne_bot
  have ha_nat : a.natAbs.Prime := Int.prime_iff_natAbs_prime.mp ha
  set ℓ := a.natAbs with hℓ_def
  have hℓ_prime : ℓ.Prime := ha_nat
  -- ℓ divides every z in the switching-value set.
  have hℓ_dvd : ∀ z ∈ switchValueSet p hp, (ℓ : ℤ) ∣ z := by
    intro z hz
    have hz_M : z ∈ M := hM_le (Ideal.subset_span hz)
    have ha_eq : Ideal.span ({a} : Set ℤ) = M :=
      Submodule.IsPrincipal.span_singleton_generator M
    rw [← ha_eq] at hz_M
    rw [Ideal.mem_span_singleton] at hz_M
    rcases Int.natAbs_eq a with heq | heq
    · rw [← heq]; exact hz_M
    · rw [heq] at hz_M; exact (Int.neg_dvd.mp hz_M)
  -- Step 2: Get B with B p ∈ ℤ[X].
  obtain ⟨B, hB_pos, hB_int⟩ := exists_integral_multiple p
  -- Step 3: Apply egyptian_pattern_with_period with T = ℓ * B, M = ℓ, ρ = 0.
  have hℓ_pos : 1 ≤ ℓ := hℓ_prime.one_lt.le
  have hℓ_ge_two : 2 ≤ ℓ := hℓ_prime.two_le
  have hT_pos : 1 ≤ ℓ * B :=
    Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  obtain ⟨E, hE_pat, hE_dvd, hE_card⟩ :=
    egyptian_pattern_with_period (ℓ * B) ℓ hT_pos hℓ_pos (0 : ZMod ℓ)
  -- E.card ≡ 0 (mod ℓ).
  have h_card_dvd : (ℓ : ℤ) ∣ (E.card : ℤ) := by
    have hcard : (E.card : ZMod ℓ) = 0 := hE_card
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact_mod_cast hcard
  -- Step 4: For every n ≥ 1, derive ℓ ∣ intEval p n.
  have h_div : ∀ n : ℕ, 1 ≤ n → (ℓ : ℤ) ∣ intEval p hp (n : ℤ) := by
    intro n hn
    set Qn : ℤ :=
      (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) - intEval p hp ((n : ℕ) : ℤ) with hQn_def
    have hQ_in : Qn ∈ switchValueSet p hp := ⟨E, n, hE_pat, hn, rfl⟩
    have hℓ_dvd_Qn : (ℓ : ℤ) ∣ Qn := hℓ_dvd Qn hQ_in
    -- For each e ∈ E, intEval p (e * n) ≡ intEval p 0 (mod ℓ) by polynomial_periodicity.
    have h_each : ∀ e ∈ E,
        intEval p hp ((e * n : ℕ) : ℤ) ≡ intEval p hp 0 [ZMOD (ℓ : ℤ)] := by
      intro e he
      have hdvd : (ℓ * B) ∣ e := hE_dvd e he
      have h_eq_zmod : ((e * n : ℕ) : ℤ) ≡ (0 : ℤ) [ZMOD ((ℓ * B : ℕ) : ℤ)] := by
        rw [Int.modEq_zero_iff_dvd]
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨(k * n : ℕ), ?_⟩
        have h_e_int : (e : ℤ) = ((ℓ * B * k : ℕ) : ℤ) := by exact_mod_cast hk
        push_cast
        push_cast at h_e_int
        rw [h_e_int]
        ring
      have h_per := polynomial_periodicity p hp B hB_pos hB_int ℓ hℓ_pos
        ((e * n : ℕ) : ℤ) (0 : ℤ) h_eq_zmod
      exact_mod_cast h_per
    -- Sum congruence: ∑_e intEval p (e * n) ≡ ∑_e intEval p 0 = E.card * intEval p 0 (mod ℓ).
    have h_sum_congr :
        (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) ≡
        (∑ _ ∈ E, intEval p hp 0) [ZMOD (ℓ : ℤ)] :=
      Int.ModEq.sum h_each
    have h_const_sum :
        (∑ _ ∈ E, intEval p hp 0) = (E.card : ℤ) * intEval p hp 0 := by
      rw [Finset.sum_const]
      ring
    rw [h_const_sum] at h_sum_congr
    -- E.card * intEval p 0 ≡ 0 (mod ℓ).
    have h_const_zero :
        (E.card : ℤ) * intEval p hp 0 ≡ 0 [ZMOD (ℓ : ℤ)] := by
      rw [Int.modEq_zero_iff_dvd]
      exact Dvd.dvd.mul_right h_card_dvd _
    have h_sum_zero :
        (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) ≡ 0 [ZMOD (ℓ : ℤ)] :=
      h_sum_congr.trans h_const_zero
    have h_dvd_sum :
        (ℓ : ℤ) ∣ (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) := by
      rw [Int.modEq_zero_iff_dvd] at h_sum_zero
      exact h_sum_zero
    -- ℓ ∣ Qn = sum - intEval p n, and ℓ ∣ sum, so ℓ ∣ intEval p n.
    have h_diff : intEval p hp ((n : ℕ) : ℤ) =
        (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) - Qn := by
      change intEval p hp ((n : ℕ) : ℤ) =
        (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) -
          ((∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ)) - intEval p hp ((n : ℕ) : ℤ))
      ring
    show (ℓ : ℤ) ∣ intEval p hp ((n : ℕ) : ℤ)
    rw [h_diff]
    exact dvd_sub h_dvd_sum hℓ_dvd_Qn
  -- Apply NoFixedDivisor at d = ℓ.
  exact h_no_fixed ℓ hℓ_ge_two h_div

/-- **Finite extracted form of Lemma 6.** Used in the correction-slot
construction: there are finitely many Egyptian patterns and positive integers
whose switching-polynomial residues mod `g` generate `ZMod g`. -/
theorem finite_switch_values_generate_zmod (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed : NoFixedDivisor p hp) (g : ℕ) (hg : 1 ≤ g) :
    ∃ (t : ℕ) (E : Fin t → Finset ℕ) (a : Fin t → ℕ) (b : Fin t → ℤ),
      (∀ i, IsEgyptianPattern (E i)) ∧
      (∀ i, 1 ≤ a i) ∧
      (∀ i, b i = (∑ e ∈ E i, intEval p hp ((e * a i : ℕ) : ℤ))
                  - intEval p hp ((a i : ℕ) : ℤ)) ∧
      AddSubgroup.closure (Set.range fun i : Fin t => ((b i : ℤ) : ZMod g)) = ⊤ := by
  classical
  haveI hg_neZero : NeZero g := ⟨Nat.one_le_iff_ne_zero.mp hg⟩
  -- Step 1: span = ⊤ ⟹ 1 ∈ span ⟹ a finite ℤ-combination summing to 1.
  have h_top := switching_values_span_top p hp h_nonconst h_lead_pos h_no_fixed
  have h1 : (1 : ℤ) ∈ Ideal.span (switchValueSet p hp) := by rw [h_top]; trivial
  obtain ⟨c, t_set, h_t_sub, _h_supp, h_sum⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp h1
  -- Each z ∈ t_set lies in switchValueSet, so (E_z, n_z) data exists.
  have h_each : ∀ z ∈ t_set, ∃ E : Finset ℕ, ∃ n : ℕ,
      IsEgyptianPattern E ∧ 1 ≤ n ∧
      z = (∑ e ∈ E, intEval p hp ((e * n : ℕ) : ℤ))
            - intEval p hp ((n : ℕ) : ℤ) := fun z hz => h_t_sub hz
  -- Convert the Finset t_set to an indexed Fin t form via `t_set.equivFin`.
  set t : ℕ := t_set.card with ht_def
  let φ : Fin t → ℤ := fun i => t_set.equivFin.symm i
  have h_φ_mem : ∀ i, φ i ∈ t_set := fun i => (t_set.equivFin.symm i).property
  let data : Fin t → (Finset ℕ × ℕ) := fun i =>
    let h := h_each (φ i) (h_φ_mem i)
    let E := h.choose
    let rest := h.choose_spec
    let n := rest.choose
    ⟨E, n⟩
  let E : Fin t → Finset ℕ := fun i => (data i).1
  let aᵢ : Fin t → ℕ := fun i => (data i).2
  let b : Fin t → ℤ := fun i => φ i
  -- Extract the three properties via `Classical.choose_spec`.
  have hpat : ∀ i, IsEgyptianPattern (E i) := by
    intro i
    have h := h_each (φ i) (h_φ_mem i)
    obtain ⟨pat, _, _⟩ := h.choose_spec.choose_spec
    exact pat
  have han : ∀ i, 1 ≤ aᵢ i := by
    intro i
    have h := h_each (φ i) (h_φ_mem i)
    obtain ⟨_, han, _⟩ := h.choose_spec.choose_spec
    exact han
  have hb_eq : ∀ i, b i = (∑ e ∈ E i, intEval p hp ((e * aᵢ i : ℕ) : ℤ)) -
      intEval p hp ((aᵢ i : ℕ) : ℤ) := by
    intro i
    have h := h_each (φ i) (h_φ_mem i)
    obtain ⟨_, _, hb⟩ := h.choose_spec.choose_spec
    exact hb
  refine ⟨t, E, aᵢ, b, hpat, han, hb_eq, ?_⟩
  -- Closure equals ⊤ iff every element of `ZMod g` lies in it.
  rw [AddSubgroup.eq_top_iff']
  intro x
  -- Step: 1 ∈ closure {(b i : ZMod g)}: cast h_sum down to ZMod g and assemble.
  have h_one_in : (1 : ZMod g) ∈
      AddSubgroup.closure (Set.range fun i : Fin t => ((b i : ℤ) : ZMod g)) := by
    have h_sum_zmod : (1 : ZMod g) = ∑ a ∈ t_set, c a • ((a : ZMod g)) := by
      have h := congr_arg (Int.cast : ℤ → ZMod g) h_sum
      push_cast at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro a _
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [h_sum_zmod]
    apply AddSubgroup.sum_mem
    intro a ha
    apply zsmul_mem
    apply AddSubgroup.subset_closure
    refine ⟨t_set.equivFin ⟨a, ha⟩, ?_⟩
    show ((b (t_set.equivFin ⟨a, ha⟩) : ℤ) : ZMod g) = ((a : ℤ) : ZMod g)
    have h_b_eq : b (t_set.equivFin ⟨a, ha⟩) = (a : ℤ) := by
      show (t_set.equivFin.symm (t_set.equivFin ⟨a, ha⟩) : ℤ) = (a : ℤ)
      simp
    rw [h_b_eq]
  -- Every x = (ZMod.val x) • 1 ∈ closure.
  have h_x_eq : x = (ZMod.val x : ℤ) • (1 : ZMod g) := by
    rw [zsmul_one]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [h_x_eq]
  exact zsmul_mem h_one_in _

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/MainSlots.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — §2 main-slot construction.

The explicit family of denominators that powers Theorem 1:

  P := 36
  u j := P j + 1
  D j := u j · u (j+1)
  τ N := P · u (N+1)
  E0 := {2, 3, 6}
  A p := switchingPoly p E0  (= p(2x) + p(3x) + p(6x) - p(x))

Telescoping identity:

  ∑_{j=J}^N 1/D j = 1/(P u_J) - 1/τ_N

The fixed divisor `g := gcd { A(D j) : j ≥ J }` is then extracted as the
nonnegative generator of an `Ideal.span` over ℤ, and we form

  Dpoly p J x  := (P (J + x - 1) + 1)(P (J + x) + 1)
  q p J        := (A p) ∘ Dpoly p J / g

with the goal of applying `roth_szekeres_graham` to `q`.

This file declares the construction objects and proves the supporting
lemmas; the `theorem_1` assembly lives in `Theorem1.lean`.
-/


namespace PolynomialEgyptianSums

open Polynomial Finset

/-- The constant `P = 36 = 2² · 3²`, chosen so that `u j = P j + 1` is coprime to
`6`, giving the v₂/v₃ valuation profiles needed for collision avoidance. -/
def P : ℕ := 36

/-- `u j := P j + 1`. -/
def u (j : ℕ) : ℕ := P * j + 1

/-- `D j := u j · u (j+1)`, the main-slot denominators. Telescopes via
`1/D j = (1/P) · (1/u_j - 1/u_{j+1})`. -/
def D (j : ℕ) : ℕ := u j * u (j + 1)

/-- `τ N := P · u (N+1)`. The "endpoint" denominator that closes the telescoping
sum and provides a (v₂, v₃) = (2, 2) signature distinct from main slots. -/
def tau (N : ℕ) : ℕ := P * u (N + 1)

/-- `u j = 36j + 1` is strictly increasing. -/
lemma u_strictMono : StrictMono u := by
  intro a b h
  unfold u P
  omega

/-- Main denominators are positive. -/
lemma D_pos (j : ℕ) : 0 < D j := by
  unfold D u P
  positivity

/-- Endpoint denominators are positive. -/
lemma tau_pos (N : ℕ) : 0 < tau N := by
  unfold tau u P
  positivity

/-- `D j = u_j u_{j+1}` is strictly increasing. -/
lemma D_strictMono : StrictMono D := by
  intro a b h
  unfold D u P
  nlinarith [h]

/-- `D` is injective. -/
lemma D_injective : Function.Injective D :=
  D_strictMono.injective

/-- `τ N = 36 u_{N+1}` is strictly increasing. -/
lemma tau_strictMono : StrictMono tau := by
  intro a b h
  unfold tau u P
  omega

/-- `τ` is injective. -/
lemma tau_injective : Function.Injective tau :=
  tau_strictMono.injective

/-- The base Egyptian pattern `{2, 3, 6}` underlying the `1/x = 1/(2x) + 1/(3x)
+ 1/(6x)` switch identity. -/
def E0 : Finset ℕ := {2, 3, 6}

/-- The switching polynomial of the base pattern: `A p (x) = p(2x) + p(3x) +
p(6x) - p(x)`. -/
noncomputable def A (p : ℚ[X]) : ℚ[X] := switchingPoly p E0

/-! ## Reciprocal identity (the heart of telescoping) -/

/-- `1/D j = (1/P) · (1/u j - 1/u (j+1))`. -/
lemma D_recip (j : ℕ) :
    (1 : ℚ) / (D j : ℚ) =
      (1 / (P : ℚ)) * ((1 / (u j : ℚ)) - (1 / (u (j + 1) : ℚ))) := by
  unfold D u P
  push_cast
  have hu1 : (36 * (j : ℚ) + 1) ≠ 0 := ne_of_gt (by positivity)
  have hu2 : (36 * ((j : ℚ) + 1) + 1) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The telescoping sum `∑_{j=J}^N 1/D j = 1/(P u_J) - 1/τ_N`. -/
lemma main_telescoping (J N : ℕ) (hJN : J ≤ N) :
    (∑ j ∈ Finset.Icc J N, (1 : ℚ) / (D j : ℚ)) =
      1 / ((P : ℚ) * (u J : ℚ)) - 1 / (tau N : ℚ) := by
  have hP_ne : (P : ℚ) ≠ 0 := by unfold P; norm_num
  have hu_pos : ∀ k : ℕ, (0 : ℚ) < (u k : ℚ) := by
    intro k; unfold u; push_cast; positivity
  have hu_ne : ∀ k : ℕ, (u k : ℚ) ≠ 0 := fun k => ne_of_gt (hu_pos k)
  let f : ℕ → ℚ := fun i => -1 / ((P : ℚ) * (u i : ℚ))
  have hD_eq : ∀ j, (1 : ℚ) / (D j : ℚ) = f (j + 1) - f j := by
    intro j
    rw [D_recip]
    show (1 / (P : ℚ)) * (1 / (u j : ℚ) - 1 / (u (j + 1) : ℚ)) =
        -1 / ((P : ℚ) * (u (j + 1) : ℚ)) - -1 / ((P : ℚ) * (u j : ℚ))
    field_simp
    ring
  calc (∑ j ∈ Finset.Icc J N, (1 : ℚ) / (D j : ℚ))
      = ∑ j ∈ Finset.Icc J N, (f (j + 1) - f j) :=
        Finset.sum_congr rfl (fun j _ => hD_eq j)
    _ = ∑ j ∈ Finset.Ico J (N + 1), (f (j + 1) - f j) := by
        rw [show (Finset.Icc J N) = Finset.Ico J (N + 1) from
              (Finset.Ico_add_one_right_eq_Icc J N).symm]
    _ = f (N + 1) - f J := Finset.sum_Ico_sub f (by omega : J ≤ N + 1)
    _ = 1 / ((P : ℚ) * (u J : ℚ)) - 1 / (tau N : ℚ) := by
        show -1 / ((P : ℚ) * (u (N + 1) : ℚ)) - -1 / ((P : ℚ) * (u J : ℚ)) =
            1 / ((P : ℚ) * (u J : ℚ)) - 1 / (tau N : ℚ)
        unfold tau
        push_cast
        field_simp
        ring

/-! ## E0 is an Egyptian pattern -/

/-- `E0 = {2, 3, 6}` is an Egyptian pattern (`1/2 + 1/3 + 1/6 = 1`). -/
lemma isEgyptianPattern_E0 : IsEgyptianPattern E0 := by
  refine ⟨?_, ?_⟩
  · intro e he
    fin_cases he <;> norm_num
  · show ∑ e ∈ E0, (1 : ℚ) / (e : ℚ) = 1
    rw [show (E0 : Finset ℕ) = insert 2 (insert 3 ({6} : Finset ℕ)) from rfl]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    norm_num

/-! ## Leading coefficient of A and the constant Θ

The asymptotic comparison in Theorem 1 needs the *exact* leading coefficient of
`A p`, not just positivity. Specifically, `lc(A p) = lc(p) · (Θ_r) > 0` where
`Θ_r := 2^r + 3^r + 6^r − 1`. -/

/-- `Θ r := 2^r + 3^r + 6^r - 1`. Used in the main-theorem asymptotics:
`λ = a P^{2r}` and `a Θ_r P^{2r}` bracket the rescaled-polynomial leading term. -/
def theta (r : ℕ) : ℚ := (2 : ℚ)^r + (3 : ℚ)^r + (6 : ℚ)^r - 1

/-- `1 < Θ r` for `r ≥ 1`. (At `r = 1`: `Θ = 2 + 3 + 6 - 1 = 10`.) -/
lemma theta_gt_one (r : ℕ) (hr : 1 ≤ r) : 1 < theta r := by
  unfold theta
  have h2 : (2 : ℚ) ≤ (2 : ℚ) ^ r := by
    calc (2 : ℚ) = (2 : ℚ) ^ 1 := by norm_num
    _ ≤ (2 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have h3 : (3 : ℚ) ≤ (3 : ℚ) ^ r := by
    calc (3 : ℚ) = (3 : ℚ) ^ 1 := by norm_num
    _ ≤ (3 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have h6 : (6 : ℚ) ≤ (6 : ℚ) ^ r := by
    calc (6 : ℚ) = (6 : ℚ) ^ 1 := by norm_num
    _ ≤ (6 : ℚ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  linarith

/-- `theta r = ∑ e ∈ E0, e^r - 1`. -/
lemma theta_eq_sum (r : ℕ) :
    theta r = (∑ e ∈ E0, ((e : ℚ) ^ r)) - 1 := by
  unfold theta E0
  rw [show ({2, 3, 6} : Finset ℕ) = insert 2 (insert 3 ({6} : Finset ℕ)) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  push_cast; ring

/-- The natDegree of `A p` equals `natDegree p` whenever `lc(p) > 0` and
`1 ≤ natDegree p`. -/
lemma A_natDegree_eq (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (A p).natDegree = p.natDegree := by
  unfold A
  exact switchingPoly_natDegree_eq p E0 isEgyptianPattern_E0 h_lead_pos h_nonconst

/-- Exact leading-coefficient formula:
`lc(A p) = lc(p) · Θ_r` where `r = natDegree p`. -/
lemma A_leadingCoeff_eq (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (A p).leadingCoeff = p.leadingCoeff * theta p.natDegree := by
  unfold A
  rw [switchingPoly_leadingCoeff_eq p E0 isEgyptianPattern_E0 h_lead_pos h_nonconst,
      theta_eq_sum]

/-- The leading coefficient of `A p = switchingPoly p {2, 3, 6}` is
`lc(p) · (2^r + 3^r + 6^r - 1) > 0` when `lc(p) > 0` and `r := deg p ≥ 1`. -/
lemma A_leadingCoeff (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < (A p).leadingCoeff := by
  unfold A
  exact switchingPoly_leadingCoeff p E0 isEgyptianPattern_E0 h_lead_pos h_nonconst

/-- `A p` is integer-valued whenever `p` is. -/
lemma A_intValued (p : ℚ[X]) (hp : IntValued p) : IntValued (A p) :=
  switchingPoly_intValued p hp E0

/-! ## Asymptotic constants for Theorem 1

`λ`, `μ`, `aΘP^{2r}` bracket the rescaled-polynomial leading term. Theorem 1's
attainable-interval / overlap argument needs `λ < μ < a Θ_r P^{2r}`; the
midpoint choice `μ := a P^{2r} (1 + Θ_r) / 2` works in ℚ. -/

/-- `λ p := lc(p) · P^{2r}` where `r = natDegree p`. The interval-step
constant: `B_{N+1} − B_N = λ N^{2r} + O(N^{2r-1})`. -/
def lambdaConst (p : ℚ[X]) : ℚ :=
  p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree))

/-- `μ p := lc(p) · P^{2r} · (1 + Θ_r) / 2`. The strict mid-constant
between `λ p` and `lc(p) · Θ_r · P^{2r}`. Used as the upper-edge slope of
attainable intervals so consecutive intervals overlap. -/
def muConst (p : ℚ[X]) : ℚ :=
  p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) *
    ((1 + theta p.natDegree) / 2)

/-- `λ p < μ p` whenever `lc(p) > 0` and `1 ≤ natDegree p`. -/
lemma lambdaConst_lt_muConst (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    lambdaConst p < muConst p := by
  unfold lambdaConst muConst
  have hθ : 1 < theta p.natDegree := theta_gt_one _ h_nonconst
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  have hap : 0 < p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) :=
    mul_pos h_lead_pos hP
  have h_factor : 1 < (1 + theta p.natDegree) / 2 := by linarith
  -- aP^{2r} < aP^{2r} * ((1+Θ)/2)
  calc p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree))
      = p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) * 1 := by ring
    _ < p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) *
          ((1 + theta p.natDegree) / 2) :=
        mul_lt_mul_of_pos_left h_factor hap

/-- `μ p < lc(p) · Θ_r · P^{2r}` whenever `lc(p) > 0` and `1 ≤ natDegree p`. -/
lemma muConst_lt_a_theta_P (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    muConst p < p.leadingCoeff * theta p.natDegree *
      ((P : ℚ) ^ (2 * p.natDegree)) := by
  unfold muConst
  have hθ : 1 < theta p.natDegree := theta_gt_one _ h_nonconst
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  have hap : 0 < p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) :=
    mul_pos h_lead_pos hP
  -- (1+Θ)/2 < Θ ↔ 1+Θ < 2Θ ↔ 1 < Θ
  have h_factor : (1 + theta p.natDegree) / 2 < theta p.natDegree := by linarith
  calc p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) *
        ((1 + theta p.natDegree) / 2)
      < p.leadingCoeff * ((P : ℚ) ^ (2 * p.natDegree)) * theta p.natDegree :=
        mul_lt_mul_of_pos_left h_factor hap
    _ = p.leadingCoeff * theta p.natDegree *
          ((P : ℚ) ^ (2 * p.natDegree)) := by ring

/-- `0 < λ p` whenever `lc(p) > 0`. -/
lemma lambdaConst_pos (p : ℚ[X]) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < lambdaConst p := by
  unfold lambdaConst
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  exact mul_pos h_lead_pos hP

/-- `0 < μ p` whenever `lc(p) > 0` and `1 ≤ natDegree p`. -/
lemma muConst_pos (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < muConst p :=
  lt_trans (lambdaConst_pos p h_lead_pos)
    (lambdaConst_lt_muConst p h_nonconst h_lead_pos)

/-! ## The set of main-slot increments -/

/-- The set of integer values `A(D j)` for `j ≥ J`. Used to define `g`. The
`IntValued (A p)` witness is derived automatically via `A_intValued` so
callers only need `hp : IntValued p`. -/
noncomputable def mainValueSet (p : ℚ[X]) (hp : IntValued p) (J : ℕ) : Set ℤ :=
  { z | ∃ j : ℕ, J ≤ j ∧ z = intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) }

/-! ## The polynomial `Dpoly` and rescaled `q` -/

/-- `Dpoly p J x := (P(J + x - 1) + 1)(P(J + x) + 1)`, a polynomial of degree 2
with leading coefficient `P²`. Substituting `t ≥ 1` gives `D (J + t - 1)`.

Defined with explicit ℚ-subtraction inside `ℚ[X]` (not Nat subtraction) so the
formula matches the paper for every `J`, including `J = 0`. -/
noncomputable def Dpoly (J : ℕ) : ℚ[X] :=
  (Polynomial.C (P : ℚ) *
      (Polynomial.C (J : ℚ) + Polynomial.X - Polynomial.C (1 : ℚ)) + 1) *
  (Polynomial.C (P : ℚ) *
      (Polynomial.C (J : ℚ) + Polynomial.X) + 1)

/-- `Dpoly J` applied at `t : ℕ` (with `1 ≤ t`) gives `D (J + t - 1)`. -/
lemma Dpoly_eval_at_succ (J t : ℕ) (ht : 1 ≤ t) :
    (Dpoly J).eval (t : ℚ) = (D (J + t - 1) : ℚ) := by
  have h_pos : 1 ≤ J + t := by omega
  have h_succ : J + t - 1 + 1 = J + t := by omega
  have h_cast : ((J + t - 1 : ℕ) : ℚ) = (J : ℚ) + (t : ℚ) - 1 := by
    rw [Nat.cast_sub h_pos]; push_cast; ring
  unfold Dpoly D u
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
             Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  rw [h_succ]
  push_cast
  rw [h_cast]

/-! ### `Dpoly` natDegree and leadingCoeff -/

/-- `Dpoly J` factors as `(C P · X + C ((P : ℚ)·(J-1) + 1)) · (C P · X + C ((P : ℚ)·J + 1))`. -/
lemma Dpoly_eq_linear_mul (J : ℕ) :
    Dpoly J =
      (Polynomial.C (P : ℚ) * Polynomial.X + Polynomial.C ((P : ℚ) * ((J : ℚ) - 1) + 1)) *
      (Polynomial.C (P : ℚ) * Polynomial.X + Polynomial.C ((P : ℚ) * (J : ℚ) + 1)) := by
  unfold Dpoly
  simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_1]
  ring

/-- `Dpoly J` has natDegree exactly 2. -/
lemma Dpoly_natDegree (J : ℕ) : (Dpoly J).natDegree = 2 := by
  have hP_ne : (P : ℚ) ≠ 0 := by unfold P; norm_num
  rw [Dpoly_eq_linear_mul]
  rw [Polynomial.natDegree_mul]
  · rw [Polynomial.natDegree_linear hP_ne, Polynomial.natDegree_linear hP_ne]
  · -- first factor ≠ 0
    intro h
    have := Polynomial.natDegree_linear (a := (P : ℚ))
        (b := (P : ℚ) * ((J : ℚ) - 1) + 1) hP_ne
    rw [h] at this; simp at this
  · -- second factor ≠ 0
    intro h
    have := Polynomial.natDegree_linear (a := (P : ℚ))
        (b := (P : ℚ) * (J : ℚ) + 1) hP_ne
    rw [h] at this; simp at this

/-- `Dpoly J` has leading coefficient `P²`. -/
lemma Dpoly_leadingCoeff (J : ℕ) : (Dpoly J).leadingCoeff = (P : ℚ) ^ 2 := by
  have hP_ne : (P : ℚ) ≠ 0 := by unfold P; norm_num
  rw [Dpoly_eq_linear_mul, Polynomial.leadingCoeff_mul]
  rw [Polynomial.leadingCoeff_linear hP_ne, Polynomial.leadingCoeff_linear hP_ne]
  ring

/-! ### Composition `(A p) ∘ (Dpoly J)`

The rescaled polynomial in Theorem 1 is `q := (A p).comp (Dpoly J) / g` where
`g` is the gcd of the main-slot values. Before dividing by `g`, we have:

  * natDegree `(A p).comp (Dpoly J) = 2 r` where `r = natDegree p`
  * leadingCoeff `(A p).comp (Dpoly J) = lc(p) · Θ_r · P^{2r}`

These follow from `Polynomial.natDegree_comp` and `Polynomial.leadingCoeff_comp`,
combined with `A_natDegree_eq`, `A_leadingCoeff_eq`, `Dpoly_natDegree`,
`Dpoly_leadingCoeff`. -/

/-- natDegree of the composition. -/
lemma A_comp_Dpoly_natDegree (p : ℚ[X]) (J : ℕ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    ((A p).comp (Dpoly J)).natDegree = 2 * p.natDegree := by
  rw [Polynomial.natDegree_comp, A_natDegree_eq p h_nonconst h_lead_pos,
      Dpoly_natDegree]
  ring

/-- `Dpoly J` is integer-valued (its coefficients are rationals but evaluate to ℤ
on ℤ inputs since each linear factor is `P·X + integer`). -/
lemma Dpoly_intValued (J : ℕ) : IntValued (Dpoly J) := by
  intro z
  refine ⟨((P : ℤ) * (z + (J : ℤ) - 1) + 1) * ((P : ℤ) * (z + (J : ℤ)) + 1), ?_⟩
  unfold Dpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
             Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  push_cast
  ring

/-- The composition `(A p).comp (Dpoly J)` is integer-valued whenever `p` is. -/
lemma A_comp_Dpoly_intValued (p : ℚ[X]) (hp : IntValued p) (J : ℕ) :
    IntValued ((A p).comp (Dpoly J)) := by
  intro z
  obtain ⟨k_D, hk_D⟩ := Dpoly_intValued J z
  obtain ⟨k_A, hk_A⟩ := A_intValued p hp k_D
  refine ⟨k_A, ?_⟩
  rw [Polynomial.eval_comp, ← hk_D, hk_A]

/-- Leading coefficient of the composition: `lc(p) · Θ_r · P^{2r}`. -/
lemma A_comp_Dpoly_leadingCoeff (p : ℚ[X]) (J : ℕ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    ((A p).comp (Dpoly J)).leadingCoeff =
      p.leadingCoeff * theta p.natDegree * ((P : ℚ) ^ (2 * p.natDegree)) := by
  have hP_ne : (P : ℚ) ≠ 0 := by unfold P; norm_num
  rw [Polynomial.leadingCoeff_comp ?_, A_leadingCoeff_eq p h_nonconst h_lead_pos,
      Dpoly_leadingCoeff, A_natDegree_eq p h_nonconst h_lead_pos]
  · -- Goal: lc(p) * Θ * (P²)^r = lc(p) * Θ * P^{2r}
    rw [← pow_mul]
  · -- Goal: (Dpoly J).natDegree ≠ 0
    rw [Dpoly_natDegree]; norm_num

/-- `0 < ((A p).comp (Dpoly J)).natDegree` whenever `1 ≤ p.natDegree`,
`lc(p) > 0`. (RSG's `0 < f.natDegree` hypothesis after `g`-division.) -/
lemma A_comp_Dpoly_natDegree_pos (p : ℚ[X]) (J : ℕ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < ((A p).comp (Dpoly J)).natDegree := by
  rw [A_comp_Dpoly_natDegree p J h_nonconst h_lead_pos]
  omega

/-- `0 < ((A p).comp (Dpoly J)).leadingCoeff` whenever `1 ≤ p.natDegree`,
`lc(p) > 0`. (RSG's `0 < f.leadingCoeff` hypothesis after `g`-division.) -/
lemma A_comp_Dpoly_leadingCoeff_pos (p : ℚ[X]) (J : ℕ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < ((A p).comp (Dpoly J)).leadingCoeff := by
  rw [A_comp_Dpoly_leadingCoeff p J h_nonconst h_lead_pos]
  have hθ : 0 < theta p.natDegree := by
    have := theta_gt_one _ h_nonconst; linarith
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  positivity

/-- `(A p).comp (Dpoly J)` evaluated at a positive integer `t` equals the
integer value `intEval (A p) (D (J + t - 1))`. This is the bridge between the
rescaled polynomial (used by RSG) and the main-slot value set used to define
the gcd `g`. -/
lemma A_comp_Dpoly_eval_at_succ (p : ℚ[X]) (hp : IntValued p) (J t : ℕ)
    (ht : 1 ≤ t) :
    ((A p).comp (Dpoly J)).eval (t : ℚ) =
      ((intEval (A p) (A_intValued p hp) ((D (J + t - 1) : ℕ) : ℤ) : ℤ) : ℚ) := by
  rw [Polynomial.eval_comp, Dpoly_eval_at_succ J t ht]
  rw [intEval_spec (A p) (A_intValued p hp) ((D (J + t - 1) : ℕ) : ℤ)]
  push_cast
  rfl

/-! ## The rescaled polynomial `qPoly`

`qPoly p J g := (A p) ∘ (Dpoly J) / g`, where `g` will be the gcd of
`(A p).intEval (D j)` for `j ≥ J` (constructed inside `Theorem1.lean`'s
case-neg). The structural facts below cover the post-division layer:
natDegree, leadingCoeff (with explicit `1/g`), and positivity. The RSG-input
predicates (positivity at positive integers + no-prime-fixed-divisor for the
quotient values) live in `Theorem1.lean` since they require `J` and the
ideal/gcd construction. -/

/-- The divided rescaled polynomial `qPoly p J g := (1/g) · (A p ∘ Dpoly J)`. -/
noncomputable def qPoly (p : ℚ[X]) (J g : ℕ) : ℚ[X] :=
  Polynomial.C ((g : ℚ)⁻¹) * ((A p).comp (Dpoly J))

/-- natDegree of `qPoly` is `2 r` (scalar `1/g ≠ 0` doesn't change degree). -/
lemma qPoly_natDegree (p : ℚ[X]) (J g : ℕ) (hg : 1 ≤ g)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (qPoly p J g).natDegree = 2 * p.natDegree := by
  unfold qPoly
  rw [Polynomial.natDegree_C_mul, A_comp_Dpoly_natDegree p J h_nonconst h_lead_pos]
  exact inv_ne_zero (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hg))

/-- Leading coefficient of `qPoly`: `lc(p) · Θ_r · P^{2r} / g`. -/
lemma qPoly_leadingCoeff (p : ℚ[X]) (J g : ℕ) (hg : 1 ≤ g)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (qPoly p J g).leadingCoeff =
      p.leadingCoeff * theta p.natDegree *
        ((P : ℚ) ^ (2 * p.natDegree)) / (g : ℚ) := by
  unfold qPoly
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      A_comp_Dpoly_leadingCoeff p J h_nonconst h_lead_pos]
  have hg_ne : (g : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hg)
  field_simp

/-- `0 < (qPoly p J g).leadingCoeff` whenever `1 ≤ g`, `1 ≤ p.natDegree`,
`lc(p) > 0`. RSG's `0 < f.leadingCoeff` hypothesis. -/
lemma qPoly_leadingCoeff_pos (p : ℚ[X]) (J g : ℕ) (hg : 1 ≤ g)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < (qPoly p J g).leadingCoeff := by
  rw [qPoly_leadingCoeff p J g hg h_nonconst h_lead_pos]
  have hθ : 0 < theta p.natDegree := by
    have := theta_gt_one _ h_nonconst; linarith
  have hP : (0 : ℚ) < (P : ℚ) ^ (2 * p.natDegree) := by
    have : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
    exact pow_pos this _
  have hg_pos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  positivity

/-- `0 < (qPoly p J g).natDegree`. RSG's `0 < f.natDegree` hypothesis. -/
lemma qPoly_natDegree_pos (p : ℚ[X]) (J g : ℕ) (hg : 1 ≤ g)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    0 < (qPoly p J g).natDegree := by
  rw [qPoly_natDegree p J g hg h_nonconst h_lead_pos]; omega

/-- `qPoly p J g` evaluated at `t : ℕ` (with `1 ≤ t`) equals `intEval (A p) at
D (J + t - 1)` divided by `g`. Direct corollary of `A_comp_Dpoly_eval_at_succ`. -/
lemma qPoly_eval_at_succ (p : ℚ[X]) (hp : IntValued p) (J g t : ℕ)
    (ht : 1 ≤ t) :
    (qPoly p J g).eval (t : ℚ) =
      ((intEval (A p) (A_intValued p hp)
        ((D (J + t - 1) : ℕ) : ℤ) : ℤ) : ℚ) / (g : ℚ) := by
  unfold qPoly
  rw [Polynomial.eval_mul, Polynomial.eval_C,
      A_comp_Dpoly_eval_at_succ p hp J t ht]
  ring

/-! ### RSG-indexing note

`roth_szekeres_graham` returns subset sums of `f.eval ((i + 1 : ℕ) : ℚ)` indexed
by `i : ℕ`. Substituting `t := i + 1` into `qPoly_eval_at_succ` gives:

  `(qPoly p J g).eval ((i + 1 : ℕ) : ℚ) = (intEval (A p) (D (J + i))) / g`

so the natural index correspondence in the window-representation is `i ↦ J + i`,
*not* `t ↦ J + t - 1`. The latter is internal to `Dpoly_eval_at_succ`'s proof. -/

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/Collision.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — §2 collision avoidance via 2-adic / 3-adic valuations.

For all sufficiently large `N`, all denominators that may appear after any
collection of switches are pairwise distinct. The argument uses
`(v₂(d), v₃(d))` valuation profiles:

  D j        : (0, 0)        u_j is coprime to 6
  2 D j      : (1, 0)
  3 D j      : (0, 1)
  6 D j      : (1, 1)
  τ_N        : (2, 2)        τ_N = 36 u_{N+1}
  Λ f        : v₂ ≥ 3        (we choose 8 ∣ Λ)
  c_ν, e c_ν : avoided by construction during correction-slot setup

The pairwise-distinctness theorem `all_denominators_distinct_after_switches`
is the goal; sub-lemmas formalize the per-pair valuation argument.
-/


namespace PolynomialEgyptianSums

open Nat

/-- `u j = 36 j + 1` is coprime to `6`. -/
lemma u_coprime_six (j : ℕ) : Nat.Coprime (u j) 6 := by
  unfold u P
  rw [show 36 * j + 1 = 1 + 6 * (6 * j) from by ring]
  rw [Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left 6

/-- `D j = u j · u (j+1)` is coprime to `6`. -/
lemma D_coprime_six (j : ℕ) : Nat.Coprime (D j) 6 := by
  unfold D
  exact (u_coprime_six j).mul_left (u_coprime_six (j + 1))

/-- For `h ∈ {1, 2, 3, 6}`, `(v₂(h · D j), v₃(h · D j))` is `(0,0), (1,0), (0,1),
(1,1)` respectively. -/
lemma main_valuation_profile (j : ℕ) :
    (padicValNat 2 (1 * D j), padicValNat 3 (1 * D j)) = (0, 0) ∧
    (padicValNat 2 (2 * D j), padicValNat 3 (2 * D j)) = (1, 0) ∧
    (padicValNat 2 (3 * D j), padicValNat 3 (3 * D j)) = (0, 1) ∧
    (padicValNat 2 (6 * D j), padicValNat 3 (6 * D j)) = (1, 1) := by
  have hD_ne : D j ≠ 0 := by unfold D u P; positivity
  have hcop := D_coprime_six j
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2_ndvd : ¬ (2 : ℕ) ∣ D j := by
    have h2cop : Nat.Coprime (D j) 2 := by
      have h6 : (2 : ℕ) ∣ 6 := by norm_num
      exact hcop.coprime_dvd_right h6
    have h2cop' : Nat.Coprime 2 (D j) := h2cop.symm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h2cop'
  have h3_ndvd : ¬ (3 : ℕ) ∣ D j := by
    have h3cop : Nat.Coprime (D j) 3 := by
      have h6 : (3 : ℕ) ∣ 6 := by norm_num
      exact hcop.coprime_dvd_right h6
    have h3cop' : Nat.Coprime 3 (D j) := h3cop.symm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3cop'
  have h2D : padicValNat 2 (D j) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h2_ndvd))
  have h3D : padicValNat 3 (D j) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h3_ndvd))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- h = 1
    rw [one_mul]
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨h2D, h3D⟩
  · -- h = 2
    have e2 : padicValNat 2 (2 * D j) = 1 := by
      rw [padicValNat.mul (by norm_num) hD_ne, h2D, add_zero, padicValNat_self]
    have e3 : padicValNat 3 (2 * D j) = 0 := by
      apply padicValNat.eq_zero_iff.mpr
      refine Or.inr (Or.inr ?_)
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h2 | h2
      · norm_num at h2
      · exact h3_ndvd h2
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨e2, e3⟩
  · -- h = 3
    have e2 : padicValNat 2 (3 * D j) = 0 := by
      apply padicValNat.eq_zero_iff.mpr
      refine Or.inr (Or.inr ?_)
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h2 | h2
      · norm_num at h2
      · exact h2_ndvd h2
    have e3 : padicValNat 3 (3 * D j) = 1 := by
      rw [padicValNat.mul (by norm_num) hD_ne, h3D, add_zero, padicValNat_self]
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨e2, e3⟩
  · -- h = 6
    have h6_eq : (6 : ℕ) = 2 * 3 := by norm_num
    have e2 : padicValNat 2 (6 * D j) = 1 := by
      rw [show (6 : ℕ) * D j = 2 * (3 * D j) from by ring]
      rw [padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hD_ne)]
      rw [padicValNat_self]
      have : padicValNat 2 (3 * D j) = 0 := by
        apply padicValNat.eq_zero_iff.mpr
        refine Or.inr (Or.inr ?_)
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h2 | h2
        · norm_num at h2
        · exact h2_ndvd h2
      omega
    have e3 : padicValNat 3 (6 * D j) = 1 := by
      rw [show (6 : ℕ) * D j = 3 * (2 * D j) from by ring]
      rw [padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hD_ne)]
      rw [padicValNat_self]
      have : padicValNat 3 (2 * D j) = 0 := by
        apply padicValNat.eq_zero_iff.mpr
        refine Or.inr (Or.inr ?_)
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h2 | h2
        · norm_num at h2
        · exact h3_ndvd h2
      omega
    exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨e2, e3⟩

/-- `τ_N = 36 · u_{N+1}` has valuation profile `(2, 2)`. -/
lemma tau_valuation_profile (N : ℕ) :
    padicValNat 2 (tau N) = 2 ∧ padicValNat 3 (tau N) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu_ne : u (N + 1) ≠ 0 := by unfold u P; positivity
  have hcop := u_coprime_six (N + 1)
  have h2_ndvd : ¬ (2 : ℕ) ∣ u (N + 1) := by
    have h2cop : Nat.Coprime (u (N + 1)) 2 := by
      have h6 : (2 : ℕ) ∣ 6 := by norm_num
      exact hcop.coprime_dvd_right h6
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h2cop.symm
  have h3_ndvd : ¬ (3 : ℕ) ∣ u (N + 1) := by
    have h3cop : Nat.Coprime (u (N + 1)) 3 := by
      have h6 : (3 : ℕ) ∣ 6 := by norm_num
      exact hcop.coprime_dvd_right h6
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3cop.symm
  have h2u : padicValNat 2 (u (N + 1)) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h2_ndvd))
  have h3u : padicValNat 3 (u (N + 1)) = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h3_ndvd))
  -- tau N = P * u (N+1) = 36 * u (N+1)
  have htau_eq : tau N = 2^2 * (3^2 * u (N + 1)) := by
    unfold tau P; ring
  refine ⟨?_, ?_⟩
  · rw [htau_eq]
    rw [padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hu_ne)]
    rw [padicValNat.prime_pow]
    have h32u : padicValNat 2 (3^2 * u (N + 1)) = 0 := by
      apply padicValNat.eq_zero_iff.mpr
      refine Or.inr (Or.inr ?_)
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h2 | h2
      · have : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        norm_num at this
      · exact h2_ndvd h2
    omega
  · have htau_eq3 : tau N = 3^2 * (2^2 * u (N + 1)) := by
      unfold tau P; ring
    rw [htau_eq3]
    rw [padicValNat.mul (by norm_num) (mul_ne_zero (by norm_num) hu_ne)]
    rw [padicValNat.prime_pow]
    have h22u : padicValNat 3 (2^2 * u (N + 1)) = 0 := by
      apply padicValNat.eq_zero_iff.mpr
      refine Or.inr (Or.inr ?_)
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h2 | h2
      · have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
        norm_num at this
      · exact h3_ndvd h2
    omega

/-- For `8 ∣ Λ`, `Λ ≥ 1`, and `f ≥ 1`, `v₂(Λ f) ≥ 3`. -/
lemma filler_v2_at_least_three (Λ f : ℕ) (hΛ : 8 ∣ Λ) (hΛpos : 1 ≤ Λ) (hf : 1 ≤ f) :
    3 ≤ padicValNat 2 (Λ * f) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : (2 : ℕ) ^ 3 ∣ Λ * f := by
    have h8eq : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [h8eq]
    exact dvd_mul_of_dvd_left hΛ f
  have hne : Λ * f ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  exact (padicValNat_dvd_iff_le hne).mp h8

lemma main_multiplier_cases {h : ℕ}
    (hh : h ∈ ({1, 2, 3, 6} : Finset ℕ)) :
    h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 6 := by
  fin_cases hh <;> simp

lemma main_copy_eq_of_eq {h h' j k : ℕ}
    (hh : h ∈ ({1, 2, 3, 6} : Finset ℕ))
    (hh' : h' ∈ ({1, 2, 3, 6} : Finset ℕ))
    (heq : h * D j = h' * D k) : h = h' ∧ j = k := by
  have hv : (padicValNat 2 (h * D j), padicValNat 3 (h * D j)) =
      (padicValNat 2 (h' * D k), padicValNat 3 (h' * D k)) := by
    rw [heq]
  rcases main_multiplier_cases hh with rfl | rfl | rfl | rfl <;>
  rcases main_multiplier_cases hh' with rfl | rfl | rfl | rfl
  · have hD : D j = D k := Nat.mul_left_cancel (by norm_num) heq
    exact ⟨rfl, D_injective hD⟩
  · obtain ⟨hv1, _hv2, _hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, hw2, _hw3, _hw6⟩ := main_valuation_profile k
    rw [hv1, hw2] at hv
    norm_num at hv
  · obtain ⟨hv1, _hv2, _hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, _hw2, hw3, _hw6⟩ := main_valuation_profile k
    rw [hv1, hw3] at hv
    norm_num at hv
  · obtain ⟨hv1, _hv2, _hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, _hw2, _hw3, hw6⟩ := main_valuation_profile k
    rw [hv1, hw6] at hv
    norm_num at hv
  · obtain ⟨_hv1, hv2, _hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨hw1, _hw2, _hw3, _hw6⟩ := main_valuation_profile k
    rw [hv2, hw1] at hv
    norm_num at hv
  · have hD : D j = D k := Nat.mul_left_cancel (by norm_num) heq
    exact ⟨rfl, D_injective hD⟩
  · obtain ⟨_hv1, hv2, _hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, _hw2, hw3, _hw6⟩ := main_valuation_profile k
    rw [hv2, hw3] at hv
    norm_num at hv
  · obtain ⟨_hv1, hv2, _hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, _hw2, _hw3, hw6⟩ := main_valuation_profile k
    rw [hv2, hw6] at hv
    norm_num at hv
  · obtain ⟨_hv1, _hv2, hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨hw1, _hw2, _hw3, _hw6⟩ := main_valuation_profile k
    rw [hv3, hw1] at hv
    norm_num at hv
  · obtain ⟨_hv1, _hv2, hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, hw2, _hw3, _hw6⟩ := main_valuation_profile k
    rw [hv3, hw2] at hv
    norm_num at hv
  · have hD : D j = D k := Nat.mul_left_cancel (by norm_num) heq
    exact ⟨rfl, D_injective hD⟩
  · obtain ⟨_hv1, _hv2, hv3, _hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, _hw2, _hw3, hw6⟩ := main_valuation_profile k
    rw [hv3, hw6] at hv
    norm_num at hv
  · obtain ⟨_hv1, _hv2, _hv3, hv6⟩ := main_valuation_profile j
    obtain ⟨hw1, _hw2, _hw3, _hw6⟩ := main_valuation_profile k
    rw [hv6, hw1] at hv
    norm_num at hv
  · obtain ⟨_hv1, _hv2, _hv3, hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, hw2, _hw3, _hw6⟩ := main_valuation_profile k
    rw [hv6, hw2] at hv
    norm_num at hv
  · obtain ⟨_hv1, _hv2, _hv3, hv6⟩ := main_valuation_profile j
    obtain ⟨_hw1, _hw2, hw3, _hw6⟩ := main_valuation_profile k
    rw [hv6, hw3] at hv
    norm_num at hv
  · have hD : D j = D k := Nat.mul_left_cancel (by norm_num) heq
    exact ⟨rfl, D_injective hD⟩

lemma main_copy_ne_tau {h j N : ℕ}
    (hh : h ∈ ({1, 2, 3, 6} : Finset ℕ)) :
    h * D j ≠ tau N := by
  intro heq
  have hv : (padicValNat 2 (h * D j), padicValNat 3 (h * D j)) =
      (padicValNat 2 (tau N), padicValNat 3 (tau N)) := by
    rw [heq]
  obtain ⟨ht2, ht3⟩ := tau_valuation_profile N
  rcases main_multiplier_cases hh with rfl | rfl | rfl | rfl
  · obtain ⟨hv1, _hv2, _hv3, _hv6⟩ := main_valuation_profile j
    rw [hv1, ht2, ht3] at hv
    norm_num at hv
  · obtain ⟨_hv1, hv2, _hv3, _hv6⟩ := main_valuation_profile j
    rw [hv2, ht2, ht3] at hv
    norm_num at hv
  · obtain ⟨_hv1, _hv2, hv3, _hv6⟩ := main_valuation_profile j
    rw [hv3, ht2, ht3] at hv
    norm_num at hv
  · obtain ⟨_hv1, _hv2, _hv3, hv6⟩ := main_valuation_profile j
    rw [hv6, ht2, ht3] at hv
    norm_num at hv

lemma filler_ne_tau {Λ f N : ℕ} (hΛ : 8 ∣ Λ) (hΛpos : 1 ≤ Λ)
    (hf : 1 ≤ f) : Λ * f ≠ tau N := by
  intro heq
  have hfill : 3 ≤ padicValNat 2 (Λ * f) :=
    filler_v2_at_least_three Λ f hΛ hΛpos hf
  obtain ⟨ht2, _ht3⟩ := tau_valuation_profile N
  have : padicValNat 2 (Λ * f) = 2 := by
    rw [heq, ht2]
  omega

/-! ## Collision avoidance master lemma

For all sufficiently large `N`, given the collection of all main-slot copies
(`h · D j` for `h ∈ {1,2,3,6}`, `J ≤ j ≤ N`), the endpoint `τ_N`, the
correction denominators (and their `e ∈ G_ν` multiples), and the filler
denominators `Λ f`, all values are pairwise distinct.

Full statement deferred — assembled inside `Theorem1.lean`. -/

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/Corrections.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — §2 correction-slot construction.

If `g := gcd { A(D j) : j ≥ J } = 1`, no correction is needed.
Otherwise, we build correction slots (denominators `c_ν`, patterns `G_ν`)
whose switch increments `b_ν = Q_{G_ν}(c_ν)` represent every residue class
mod `g` as a subset sum.

Two main supporting results:

  * `duplicated_generators_subset_sum_all_residues` — given residues
    generating `ZMod g`, duplicating each `g − 1` times allows representing
    every residue as a subset sum.
  * `exists_large_correction_denominator` — given a forbidden finite set and
    forbidden multiples-of-D-multiplied set, an arithmetic-progression element
    avoiding all forbidden values exists arbitrarily far out.

Plus the bookkeeping for `B_*`, `R_c`, `C_0`.
-/


namespace PolynomialEgyptianSums

open Finset Polynomial

/-! ## Subset-sum representability -/

/-- If finitely many residues `ρ : Fin w → ZMod g` generate `ZMod g` as an
additive group, then duplicating each residue `g - 1` times allows every
residue to be represented as a subset sum (with repetitions encoded as choices
of how many duplicates to take). -/
theorem duplicated_generators_subset_sum_all_residues
    {w g : ℕ} (hg : 1 ≤ g) (ρ : Fin w → ZMod g)
    (hgen : AddSubgroup.closure (Set.range ρ) = ⊤) :
    ∀ r : ZMod g,
      ∃ T : Finset (Fin w × Fin (g - 1)),
        r = ∑ t ∈ T, ρ t.1 := by
  intro r
  haveI : NeZero g := ⟨by omega⟩
  have hr : r ∈ AddSubgroup.closure (Set.range ρ) := by rw [hgen]; trivial
  obtain ⟨a, ha⟩ := AddSubgroup.exists_of_mem_closure_range ρ r hr
  have hgZ : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hg
  -- Reduce each integer coefficient `a i` to its residue `k i ∈ {0, …, g - 1}`.
  set k : Fin w → ℕ := fun i => ((a i) % (g : ℤ)).toNat with hk_def
  have hk_lt : ∀ i, k i < g := fun i => by
    have hnn : (0 : ℤ) ≤ (a i) % (g : ℤ) := Int.emod_nonneg _ hgZ.ne'
    have hub : (a i) % (g : ℤ) < (g : ℤ) := Int.emod_lt_of_pos _ hgZ
    rw [hk_def]
    exact (Int.toNat_lt hnn).mpr hub
  have hk_le : ∀ i, k i ≤ g - 1 := fun i => by have := hk_lt i; omega
  -- In `ZMod g`, the natural-number scalar `k i` matches the integer scalar `a i`.
  have key : ∀ i, (k i : ℕ) • ρ i = a i • ρ i := fun i => by
    have hnn : (0 : ℤ) ≤ (a i) % (g : ℤ) := Int.emod_nonneg _ hgZ.ne'
    rw [hk_def]
    rw [show ((((a i) % (g : ℤ)).toNat : ℕ) • ρ i) = ((((a i) % (g : ℤ)).toNat : ℤ) • ρ i) from
      (natCast_zsmul (ρ i) _).symm]
    rw [Int.toNat_of_nonneg hnn]
    rw [show ((g : ℤ) : ℤ) = (Fintype.card (ZMod g) : ℤ) by simp [ZMod.card]]
    exact mod_card_zsmul (ρ i) (a i)
  -- For each `i`, choose the first `k i` elements of `Fin (g - 1)`.
  let T : Finset (Fin w × Fin (g - 1)) :=
    ((Finset.univ : Finset (Fin w)) ×ˢ (Finset.univ : Finset (Fin (g - 1)))).filter
      (fun p => p.2.1 < k p.1)
  refine ⟨T, ?_⟩
  show r = ∑ t ∈ T, ρ t.1
  have hsum : (∑ t ∈ T, ρ t.1) = ∑ i, k i • ρ i := by
    show (∑ t ∈ ((Finset.univ : Finset (Fin w)) ×ˢ
            (Finset.univ : Finset (Fin (g - 1)))).filter
            (fun p => p.2.1 < k p.1), ρ t.1) = ∑ i, k i • ρ i
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show (∑ y : Fin (g - 1), if y.val < k i then ρ i else 0) = k i • ρ i
    rw [← Finset.sum_filter, Finset.sum_const]
    congr 1
    have heq : ((Finset.univ : Finset (Fin (g - 1))).filter
                  (fun j : Fin (g - 1) => j.val < k i)) =
               (Finset.range (k i)).attachFin (fun j hj =>
                 lt_of_lt_of_le (Finset.mem_range.mp hj) (hk_le i)) := by
      ext ⟨b, hb⟩
      simp [Finset.mem_attachFin, Finset.mem_range]
    rw [heq, Finset.card_attachFin]
    simp
  rw [hsum, ha]
  exact Finset.sum_congr rfl (fun i _ => (key i).symm)

/-! ## Correction-denominator existence (density argument) -/

section ExistsLargeCorrectionDenominator
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

/-- A density argument: an arithmetic progression `{a + k T_g : k ∈ ℕ}` has
positive density `1/T_g`, while the union of finitely many specific values
plus the curves `{(h/e) D j : j ≥ J}` (parametrized by `j`, contributing
`O(√X)` elements up to `X`) has density zero. So the AP eventually contains
elements avoiding all forbidden values.

The hypothesis `hQpos : 0 < (switchingPoly p Gν).leadingCoeff` makes
`Q_{Gν}(c) > 0` for `c` past the largest real root. This is supplied at the
call site from `switchingPoly_leadingCoeff`.

The forbidden-finite avoidance is stated in the same shape as the
main-denominator avoidance (`∀ e ∈ insert 1 Gν, e * c ∉ forbiddenFinite`)
so the caller can stuff "all previous correction-denominator candidates"
directly into `forbiddenFinite` without extra division-by-`e` bookkeeping.

`hQGν : IntValued (switchingPoly p Gν)` is derived from `hp` via
`switchingPoly_intValued`; the caller doesn't need to plumb it manually.

This is the second-hardest sub-lemma of the whole proof (after Lemma 3). -/
theorem exists_large_correction_denominator
    (p : ℚ[X]) (hp : IntValued p)
    (Tg aσ J L lower : ℕ) (Gν : Finset ℕ) (hGν : IsEgyptianPattern Gν)
    (hQpos : 0 < (switchingPoly p Gν).leadingCoeff)
    (forbiddenFinite : Finset ℕ) (hTg : 1 ≤ Tg) :
    ∃ c : ℕ,
      c ≡ aσ [MOD Tg] ∧
      lower < c ∧ L < c ∧
      0 < intEval (switchingPoly p Gν)
            (switchingPoly_intValued p hp Gν) ((c : ℕ) : ℤ) ∧
      (∀ e ∈ insert 1 Gν, e * c ∉ forbiddenFinite) ∧
      (∀ j, J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ insert 1 Gν, e * c ≠ h * D j) := by
  classical
  -- Notation.
  set Q : ℚ[X] := switchingPoly p Gν with hQ_def
  set hQint : IntValued Q := switchingPoly_intValued p hp Gν with hQint_def
  set EE : Finset ℕ := insert 1 Gν with hEE_def
  -- All elements of EE are positive (1 or ≥ 2 from Egyptian pattern).
  have hEE_pos : ∀ e ∈ EE, 1 ≤ e := by
    intro e he
    rw [hEE_def] at he
    rcases Finset.mem_insert.mp he with h1 | h2
    · omega
    · exact le_trans (by norm_num) (hGν.1 e h2)
  -- Pick a uniform upper bound on EE for sqrt-style counting.
  set maxE : ℕ := (EE.sup id) + 1 with hmaxE_def
  have hmaxE_ge : ∀ e ∈ EE, e ≤ maxE := by
    intro e he
    have := Finset.le_sup (f := id) he
    simp at this; omega
  have hmaxE_pos : 1 ≤ maxE := by rw [hmaxE_def]; omega
  -- Step 1: positivity threshold for Q on naturals.
  -- Cast Q to ℝ[X], use leading coefficient positivity to find threshold.
  obtain ⟨Npos, hNpos⟩ : ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      0 < intEval Q hQint ((x : ℕ) : ℤ) := by
    set Qr : ℝ[X] := Q.map (algebraMap ℚ ℝ) with hQr_def
    have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
      (algebraMap ℚ ℝ).injective
    have hQr_lc : (0 : ℝ) < Qr.leadingCoeff := by
      rw [hQr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
      have : (0 : ℝ) < (Q.leadingCoeff : ℝ) := by exact_mod_cast hQpos
      simpa [algebraMap] using this
    by_cases hd : 0 < Qr.degree
    · have h_tendsto :
          Filter.Tendsto (fun x : ℝ => Qr.eval x) Filter.atTop Filter.atTop :=
        Polynomial.tendsto_atTop_of_leadingCoeff_nonneg Qr hd hQr_lc.le
      obtain ⟨N0, hN0⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto 1
      refine ⟨Nat.ceil (max N0 0) + 1, ?_⟩
      intro x hx
      have hx_real : ((Nat.ceil (max N0 0) : ℕ) : ℝ) + 1 ≤ (x : ℝ) := by
        exact_mod_cast hx
      have h_max_le : N0 ≤ ((Nat.ceil (max N0 0) : ℕ) : ℝ) := by
        have h1 : N0 ≤ max N0 0 := le_max_left _ _
        have h2 : (max N0 0) ≤ ((Nat.ceil (max N0 0) : ℕ) : ℝ) := Nat.le_ceil _
        linarith
      have h_x_ge : N0 ≤ (x : ℝ) := by linarith
      have h_eval : 1 ≤ Qr.eval ((x : ℕ) : ℝ) := hN0 _ h_x_ge
      -- Convert to ℚ.
      have h_eval_cast :
          Qr.eval ((x : ℕ) : ℝ) = ((Q.eval ((x : ℕ) : ℚ) : ℚ) : ℝ) := by
        rw [hQr_def]
        have h1 : ((x : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((x : ℕ) : ℚ) := by
          simp [algebraMap]
        rw [h1, Polynomial.eval_map_apply]
        simp [algebraMap]
      have h_eval_q : 1 ≤ Q.eval ((x : ℕ) : ℚ) := by
        have : ((1 : ℚ) : ℝ) ≤ ((Q.eval ((x : ℕ) : ℚ) : ℚ) : ℝ) := by
          rw [show ((1 : ℚ) : ℝ) = (1 : ℝ) by norm_num]
          rw [← h_eval_cast]; exact h_eval
        exact_mod_cast this
      have h_intEval_eq :
          ((intEval Q hQint ((x : ℕ) : ℤ) : ℤ) : ℚ) = Q.eval ((x : ℕ) : ℚ) := by
        rw [intEval_spec]; push_cast; rfl
      have h_pos_q : 0 < Q.eval ((x : ℕ) : ℚ) := by linarith
      have h_pos_int : (0 : ℚ) < ((intEval Q hQint ((x : ℕ) : ℤ) : ℤ) : ℚ) := by
        rw [h_intEval_eq]; exact h_pos_q
      exact_mod_cast h_pos_int
    · -- Q has degree ≤ 0. Then Q is constant, equal to its leading coefficient.
      push_neg at hd
      have hQr_ne : Qr ≠ 0 := by
        intro h0; rw [h0] at hQr_lc; simp at hQr_lc
      have hQr_natDeg : Qr.natDegree = 0 := by
        have h_deg_eq : Qr.degree = (Qr.natDegree : WithBot ℕ) :=
          Polynomial.degree_eq_natDegree hQr_ne
        rw [h_deg_eq] at hd
        have hle : (Qr.natDegree : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by
          exact_mod_cast hd
        exact Nat.le_antisymm (by exact_mod_cast hle) (Nat.zero_le _)
      have hQ_ne : Q ≠ 0 := by
        intro h0
        rw [h0] at hQr_def
        have : Qr = 0 := by rw [hQr_def]; simp
        exact hQr_ne this
      have hQ_natDeg : Q.natDegree = 0 := by
        rw [hQr_def] at hQr_natDeg
        rw [Polynomial.natDegree_map_eq_of_injective h_inj] at hQr_natDeg
        exact hQr_natDeg
      have hQ_eq : Q = Polynomial.C (Q.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hQ_natDeg
      have hQ_coeff_eq : Q.coeff 0 = Q.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hQ_natDeg]
      refine ⟨0, fun x _ => ?_⟩
      have h_eval : Q.eval ((x : ℕ) : ℚ) = Q.leadingCoeff := by
        conv_lhs => rw [hQ_eq]
        rw [Polynomial.eval_C, hQ_coeff_eq]
      have h_intEval_eq :
          ((intEval Q hQint ((x : ℕ) : ℤ) : ℤ) : ℚ) = Q.eval ((x : ℕ) : ℚ) := by
        rw [intEval_spec]; push_cast; rfl
      rw [h_eval] at h_intEval_eq
      have : (0 : ℚ) < ((intEval Q hQint ((x : ℕ) : ℤ) : ℤ) : ℚ) := by
        rw [h_intEval_eq]; exact hQpos
      exact_mod_cast this
  -- Step 2: combine all "large enough" thresholds.
  set X₀ : ℕ := max (max Npos (lower + 1)) (L + 1) with hX₀_def
  have hX₀_Npos : Npos ≤ X₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hX₀_lower : lower < X₀ := by
    have h1 : lower + 1 ≤ X₀ := le_trans (le_max_right _ _) (le_max_left _ _)
    omega
  have hX₀_L : L < X₀ := by
    have h1 : L + 1 ≤ X₀ := le_max_right _ _
    omega
  -- Step 3: collect forbidden values from forbiddenFinite, expressed as constraints on c.
  -- For each e ∈ EE and f ∈ forbiddenFinite, if e ∣ f then c = f / e is forbidden.
  set badFinSet : Finset ℕ :=
    EE.biUnion (fun e =>
      forbiddenFinite.image (fun f => f / e)) with hbadFinSet_def
  have hbadFin_forbid : ∀ c : ℕ, (∀ e ∈ EE, e * c ∉ forbiddenFinite) ∨ c ∈ badFinSet := by
    intro c
    by_cases h : ∀ e ∈ EE, e * c ∉ forbiddenFinite
    · exact Or.inl h
    · right
      push_neg at h
      obtain ⟨e, heE, hfE⟩ := h
      rw [hbadFinSet_def]
      refine Finset.mem_biUnion.mpr ⟨e, heE, ?_⟩
      refine Finset.mem_image.mpr ⟨e * c, hfE, ?_⟩
      have he_pos : 0 < e := hEE_pos e heE
      exact Nat.mul_div_cancel_left c he_pos
  -- Step 4: Bound the maximum value in badFinSet ∪ {X₀ - 1} so the AP starts past it.
  set XbadMax : ℕ :=
    (badFinSet ∪ {X₀ - 1}).sup id + 1 with hXbadMax_def
  have hXbadMax_ge_X₀ : X₀ ≤ XbadMax := by
    have h1 : X₀ - 1 ∈ (badFinSet ∪ {X₀ - 1}) := by
      apply Finset.mem_union_right; exact Finset.mem_singleton.mpr rfl
    have h2 : X₀ - 1 ≤ (badFinSet ∪ {X₀ - 1}).sup id := by
      exact Finset.le_sup (f := id) h1
    rw [hXbadMax_def]
    -- X₀ - 1 + 1 ≤ ... + 1, and X₀ ≤ X₀ - 1 + 1 (since X₀ ≥ 1 from hX₀_lower)
    have hX₀_ge_1 : 1 ≤ X₀ := by omega
    omega
  have hXbadMax_avoid : ∀ c : ℕ, XbadMax ≤ c → c ∉ badFinSet := by
    intro c hc hmem
    have h1 : c ∈ (badFinSet ∪ {X₀ - 1}) := Finset.mem_union_left _ hmem
    have h2 : c ≤ (badFinSet ∪ {X₀ - 1}).sup id := by
      exact Finset.le_sup (f := id) h1
    rw [hXbadMax_def] at hc; omega
  -- Step 5: The remaining counting/density step.
  --
  -- We seek `k : ℕ` such that, setting `c := aσ + k*Tg`, we have:
  --   (a) `c ≥ XbadMax` (covers lower, L, Npos, badFinSet via the threshold reductions),
  --   (b) `∀ j ≥ J, ∀ h ∈ {1,2,3,6}, ∀ e ∈ EE, e*c ≠ h*D j` (no main-slot collisions).
  --
  -- Mathematical content: the AP `{aσ + k*Tg : k ∈ ℕ}` has positive density `1/Tg`,
  -- while the main-collision forbidden set `{h*D j/e : j ≥ J, h ∈ {1,2,3,6}, e ∈ EE}`
  -- has density 0 — for c ≤ X, we need D j ≤ maxE * X, hence j ≤ √(maxE*X)/36
  -- (since D j ≥ 1296 j² for j ≥ 1), giving O(√X) forbidden values up to X.
  -- So for K large, the AP segment `{aσ + k*Tg : 0 ≤ k ≤ K}` of size K+1 in [X₀, X₀+K*Tg]
  -- exceeds the O(√(X₀+K*Tg)) forbidden values, hence contains a good `c`.
  --
  -- The focused claim below packages the final pigeonhole step after the
  -- bookkeeping reductions: positivity threshold, finite-forbidden reduction,
  -- and AP setup.
  obtain ⟨k, hk_AP, hk_main⟩ : ∃ k : ℕ,
      XbadMax ≤ aσ + k * Tg ∧
      (∀ j, J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ EE, e * (aσ + k * Tg) ≠ h * D j) := by
    -- Pigeonhole. The AP segment {aσ + k*Tg : kStart ≤ k ≤ kStart + N} (size N+1)
    -- must exceed the count of "bad" k's: those with e*(aσ + k*Tg) = h*D j for
    -- some h ∈ {1,2,3,6}, e ∈ EE, j ≥ J.
    --
    -- Bound on bad k's: any j contributing such a k must satisfy
    --   D j = e*(aσ+k*Tg)/h ≤ maxE * UpperC, where UpperC = aσ + (kStart+N)*Tg.
    -- Since D j ≥ (j+1)² (as D j = (36j+1)(36j+37) ≥ (j+1)·1 = j+1 ≥ ... wait
    -- D j ≥ (j+1)²? Actually D j ≥ 36j+1 ≥ j+1 always; for the sqrt bound, we
    -- use D j ≥ j+1 only.
    --
    -- Crude (linear) bound: count of j ≥ J with D j ≤ M is at most M
    -- (since D j ≥ j+1 means j ≤ M-1 ≤ M). With this, the bound is:
    --   |bad k's| ≤ 4 * card(EE) * M
    -- which grows linearly. We can't beat AP linear growth this way.
    --
    -- Hence we use the sqrt bound: D j ≥ (j+1)² for j ≥ 0 (since D j =
    -- (36j+1)(36(j+1)+1) ≥ (j+1)(j+1) when 36j+1 ≥ j+1 [iff 35j ≥ 0] and
    -- 36(j+1)+1 ≥ j+1 [iff 35(j+1) ≥ 0], both trivially true).
    -- Hence j+1 ≤ Nat.sqrt(M) (where M = max value of D j).
    classical
    set HE_set : Finset (ℕ × ℕ) := (({1,2,3,6} : Finset ℕ) ×ˢ EE) with hHE_def
    -- Choose kStart so that the AP starts past XbadMax.
    set kStart : ℕ := XbadMax + 1 with hkStart_def
    have hkStart_AP : ∀ k : ℕ, kStart ≤ k → XbadMax ≤ aσ + k * Tg := by
      intro k hk
      have : kStart ≤ k * 1 := by simpa using hk
      have h1 : kStart ≤ k * Tg := by
        calc kStart ≤ k * 1 := this
          _ ≤ k * Tg := Nat.mul_le_mul_left k hTg
      omega
    -- Constant for pigeonhole: each j contributes ≤ |HE_set| bad k's.
    set HEcard : ℕ := HE_set.card with hHEcard_def
    -- Crude size choice.
    -- We need N + 1 > HEcard * (Nat.sqrt(maxE * (aσ + (kStart+N)*Tg)) + 1).
    -- Trick: ensure Nat.sqrt(maxE * (aσ + (kStart+N)*Tg)) ≤ N/(HEcard+1) - 1 (roughly).
    -- Concretely, pick N = (HEcard+1)² * maxE * Tg * 4 + (HEcard+1) * (aσ + kStart*Tg) * 4 + 100.
    set Cbig : ℕ := HEcard + 1 with hCbig_def
    have hCbig_ge : 1 ≤ Cbig := by rw [hCbig_def]; omega
    set baseShift : ℕ := aσ + kStart * Tg with hbaseShift_def
    -- Choose N huge enough that the pigeonhole works.
    -- N = 100 * Cbig² * T + 100, where T = maxE * baseShift + maxE * Tg + 1.
    set N : ℕ := 100 * Cbig * Cbig * (maxE * baseShift + maxE * Tg + 1) + 100 with hN_def
    -- Upper bound on c we'll consider.
    set UpperC : ℕ := aσ + (kStart + N) * Tg with hUpperC_def
    have hUpperC_eq : UpperC = baseShift + N * Tg := by
      rw [hUpperC_def, hbaseShift_def]; ring
    -- The relevant j-range: j ∈ [J, Jbound) where Jbound = Nat.sqrt(maxE * UpperC) + 2.
    set Jbound : ℕ := Nat.sqrt (maxE * UpperC) + 2 with hJbound_def
    -- All j ≥ Jbound have D j > maxE * UpperC, hence e*(aσ + k*Tg) ≠ h*D j for k ≤ kStart+N.
    have hD_lower : ∀ j : ℕ, (j + 1) * (j + 1) ≤ D j := by
      intro j
      unfold D u P
      -- D j = (36j+1) * (36(j+1)+1) ≥ (j+1)*(j+1)
      have h1 : j + 1 ≤ 36 * j + 1 := by omega
      have h2 : j + 1 ≤ 36 * (j + 1) + 1 := by omega
      exact Nat.mul_le_mul h1 h2
    -- For j ≥ Jbound, D j > maxE * UpperC.
    have hD_big : ∀ j : ℕ, Jbound ≤ j → maxE * UpperC < D j := by
      intro j hj
      have h1 : (j + 1) * (j + 1) ≤ D j := hD_lower j
      have hj_lower : Nat.sqrt (maxE * UpperC) + 2 ≤ j := by rw [hJbound_def] at hj; exact hj
      -- (Nat.sqrt(maxE*UpperC) + 1)² > maxE * UpperC
      have h2 : maxE * UpperC < (Nat.sqrt (maxE * UpperC) + 1) * (Nat.sqrt (maxE * UpperC) + 1) := by
        have h := Nat.lt_succ_sqrt (maxE * UpperC)
        -- h : maxE * UpperC < (maxE*UpperC).sqrt.succ * (maxE*UpperC).sqrt.succ
        show maxE * UpperC < (Nat.sqrt (maxE * UpperC) + 1) * (Nat.sqrt (maxE * UpperC) + 1)
        convert h using 2
      have h3 : (Nat.sqrt (maxE * UpperC) + 1) * (Nat.sqrt (maxE * UpperC) + 1) ≤ (j + 1) * (j + 1) := by
        have hjp : Nat.sqrt (maxE * UpperC) + 1 ≤ j + 1 := by omega
        exact Nat.mul_le_mul hjp hjp
      omega
    -- Define the "bad k" finset within our range.
    set badK_finset : Finset ℕ :=
      (Finset.Ico J Jbound).biUnion (fun j =>
        HE_set.filter (fun he => he.1 * D j ≥ he.2 * aσ ∧ he.2 ∣ (he.1 * D j - he.2 * aσ) ∧ he.2 * Tg ∣ (he.1 * D j - he.2 * aσ))
          |>.image (fun he => (he.1 * D j - he.2 * aσ) / (he.2 * Tg))) with hbadK_def
    -- Key: any k that is "bad" with some j in the relevant range is in badK_finset.
    -- More precisely: if e*(aσ + k*Tg) = h*D j for j ≥ J, h ∈ HE, e ∈ EE, and k ≤ kStart+N,
    -- then j < Jbound, and k ∈ badK_finset.
    have hbadK_contains : ∀ k : ℕ, k ≤ kStart + N →
        (∃ j h e, J ≤ j ∧ h ∈ ({1,2,3,6} : Finset ℕ) ∧ e ∈ EE ∧
          e * (aσ + k * Tg) = h * D j) →
        k ∈ badK_finset := by
      intro k hk_le ⟨j, h, e, hjJ, hh, he, heq⟩
      -- Step 1: j < Jbound.
      have hcle : aσ + k * Tg ≤ UpperC := by
        rw [hUpperC_def]
        have : k * Tg ≤ (kStart + N) * Tg := Nat.mul_le_mul_right Tg hk_le
        omega
      have he_pos : 1 ≤ e := hEE_pos e he
      have he_le : e ≤ maxE := hmaxE_ge e he
      -- e*(aσ + k*Tg) = h * D j ⇒ D j = h⁻¹ * e * (...) ≤ maxE * UpperC (since h ≥ 1)
      have hh_pos : 1 ≤ h := by
        rcases Finset.mem_insert.mp hh with rfl | h2
        · omega
        · rcases Finset.mem_insert.mp h2 with rfl | h3
          · omega
          · rcases Finset.mem_insert.mp h3 with rfl | h4
            · omega
            · simp at h4; omega
      have hD_bound : D j ≤ maxE * UpperC := by
        have h1 : h * D j = e * (aσ + k * Tg) := heq.symm
        have h2 : e * (aσ + k * Tg) ≤ maxE * UpperC :=
          le_trans (Nat.mul_le_mul he_le hcle) (le_refl _)
        have h3 : 1 * D j ≤ h * D j := Nat.mul_le_mul_right _ hh_pos
        have h4 : D j ≤ h * D j := by simpa using h3
        omega
      have hj_lt : j < Jbound := by
        by_contra hj_ge
        push_neg at hj_ge
        exact absurd (hD_big j hj_ge) (not_lt.mpr hD_bound)
      -- Step 2: k ∈ badK_finset.
      rw [hbadK_def]
      refine Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩
      · exact Finset.mem_Ico.mpr ⟨hjJ, hj_lt⟩
      -- Now k ∈ HE_set.filter(...).image(...).
      refine Finset.mem_image.mpr ⟨(h, e), ?_, ?_⟩
      · rw [Finset.mem_filter]
        show (h, e) ∈ HE_set ∧ h * D j ≥ e * aσ ∧
             e ∣ h * D j - e * aσ ∧ e * Tg ∣ h * D j - e * aσ
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hHE_def]; exact Finset.mem_product.mpr ⟨hh, he⟩
        · -- h * D j ≥ e * aσ since h * D j = e * (aσ + k * Tg) ≥ e * aσ.
          have h0 : e * (aσ + k * Tg) ≥ e * aσ := Nat.mul_le_mul_left e (Nat.le_add_right aσ (k * Tg))
          omega
        · -- e ∣ (h * D j - e * aσ) = e * k * Tg.
          have : h * D j - e * aσ = e * (k * Tg) := by
            have h2 : e * aσ + e * (k * Tg) = h * D j := by
              have := heq
              linarith [Nat.mul_add e aσ (k*Tg)]
            omega
          rw [this]; exact ⟨k * Tg, rfl⟩
        · -- e * Tg ∣ (h * D j - e * aσ).
          have : h * D j - e * aσ = e * (k * Tg) := by
            have h2 : e * aσ + e * (k * Tg) = h * D j := by
              have := heq
              linarith [Nat.mul_add e aσ (k*Tg)]
            omega
          rw [this]
          -- e * Tg ∣ e * (k * Tg) = e * Tg * k
          refine ⟨k, ?_⟩; ring
      · -- the image element equals k
        show (h * D j - e * aσ) / (e * Tg) = k
        have : h * D j - e * aσ = e * (k * Tg) := by
          have h2 : e * aσ + e * (k * Tg) = h * D j := by
            have := heq
            linarith [Nat.mul_add e aσ (k * Tg)]
          omega
        rw [this]
        -- (e * (k * Tg)) / (e * Tg) = k.
        have he_pos' : 0 < e := he_pos
        have hTg_pos : 0 < Tg := hTg
        have heTg_pos : 0 < e * Tg := Nat.mul_pos he_pos' hTg_pos
        have h_eq : e * (k * Tg) = (e * Tg) * k := by ring
        rw [h_eq, Nat.mul_div_cancel_left _ heTg_pos]
    -- Bound on cardinality: badK_finset has card ≤ (Jbound - J) * HEcard.
    have hbadK_card : badK_finset.card ≤ (Jbound - J) * HEcard := by
      rw [hbadK_def]
      calc ((Finset.Ico J Jbound).biUnion (fun j =>
              HE_set.filter (fun he => he.1 * D j ≥ he.2 * aσ ∧ he.2 ∣ (he.1 * D j - he.2 * aσ) ∧ he.2 * Tg ∣ (he.1 * D j - he.2 * aσ))
                |>.image (fun he => (he.1 * D j - he.2 * aσ) / (he.2 * Tg)))).card
          ≤ ∑ j ∈ Finset.Ico J Jbound, (HE_set.filter _ |>.image _).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ j ∈ Finset.Ico J Jbound, HEcard := by
            apply Finset.sum_le_sum
            intro j _
            exact le_trans (Finset.card_image_le) (Finset.card_filter_le _ _)
        _ = (Finset.Ico J Jbound).card * HEcard := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (Jbound - J) * HEcard := by
            have : (Finset.Ico J Jbound).card ≤ Jbound - J := by
              rw [Nat.card_Ico]
            exact Nat.mul_le_mul_right _ this
    -- AP segment finset.
    set APseg : Finset ℕ := Finset.Icc kStart (kStart + N) with hAPseg_def
    have hAPseg_card : APseg.card = N + 1 := by
      rw [hAPseg_def, Nat.card_Icc]; omega
    -- Pigeonhole: APseg.card > badK_finset.card means ∃ k ∈ APseg, k ∉ badK_finset.
    have hcard_lt : badK_finset.card < APseg.card := by
      rw [hAPseg_card]
      -- Need: badK_finset.card < N + 1.
      have hbk_le : badK_finset.card ≤ Jbound * HEcard :=
        le_trans hbadK_card (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      -- Goal: badK_finset.card < N + 1. Since HEcard < Cbig, suffices Jbound * Cbig ≤ N,
      -- i.e., Nat.sqrt(maxE * UpperC) + 2 ≤ N / Cbig, i.e., Nat.sqrt(maxE * UpperC) * Cbig + 2 * Cbig ≤ N.
      -- Squaring: (Nat.sqrt(maxE * UpperC) * Cbig)² ≤ maxE * UpperC * Cbig² ≤ ?
      -- maxE * UpperC = maxE * baseShift + maxE * Tg * N.
      -- maxE * UpperC * Cbig² ≤ N²/16 if maxE * baseShift * Cbig² ≤ N²/32 and maxE * Tg * N * Cbig² ≤ N²/32.
      -- Second: maxE * Tg * Cbig² ≤ N/32, which holds since N ≥ 16 * Cbig² * maxE * Tg.
      -- First: maxE * baseShift * Cbig² ≤ N²/32. Since N ≥ 16 * Cbig² * maxE * baseShift, N² ≥ 256 * Cbig⁴ * (maxE*baseShift)².
      -- Need 256 * Cbig⁴ * (maxE*baseShift)² ≥ 32 * maxE * baseShift * Cbig², i.e., 8 * Cbig² * maxE * baseShift ≥ 1, ✓.
      -- So Nat.sqrt(maxE * UpperC) * Cbig ≤ N/4 (approximately).
      -- Then Jbound * Cbig = (Nat.sqrt + 2) * Cbig ≤ N/4 + 2 * Cbig ≤ N/4 + N/8 < N (for N large enough).
      have hsqUC : Nat.sqrt (maxE * UpperC) * Nat.sqrt (maxE * UpperC) ≤ maxE * UpperC := Nat.sqrt_le _
      have hUpperC_eq2 : maxE * UpperC = maxE * baseShift + maxE * Tg * N := by
        rw [hUpperC_eq]; ring
      -- Strategy: prove (Nat.sqrt(maxE * UpperC) + 2) * Cbig ≤ N by squaring.
      -- We use: a ≤ b ↔ a * a ≤ b * b for naturals (when b ≥ 0, which is always).
      -- Actually use: (a ≤ b) follows from (a * a ≤ b * b) when b ≥ a.
      -- Cleanest: prove via Nat.le_sqrt. We have ((Nat.sqrt(M) + 2) * Cbig)² ≤ ((sqrt(M))*Cbig + 2*Cbig)²
      -- ≤ ((sqrt(M))*Cbig)² + 2*((sqrt(M))*Cbig)*(2*Cbig) + (2*Cbig)²
      -- = SS²*Cbig² + 4*SS*Cbig² + 4*Cbig²
      -- ≤ M*Cbig² + 4*M*Cbig² + 4*Cbig² (using SS ≤ M when M ≥ 1, else SS = 0)
      -- ... hmm.
      -- OK let me take a direct path using polynomial inequalities.
      set T : ℕ := maxE * baseShift + maxE * Tg + 1 with hT_def
      have hT_ge : 1 ≤ T := by rw [hT_def]; omega
      have hN_def2 : N = 100 * Cbig * Cbig * T + 100 := by
        rw [hN_def, hT_def]
      -- maxE * UpperC ≤ T * (N + 1). Detailed: maxE * baseShift ≤ T * 1, maxE * Tg ≤ T, so maxE * Tg * N ≤ T * N.
      have hUpperC_T : maxE * UpperC ≤ T * (N + 1) := by
        rw [hUpperC_eq2, hT_def]
        have h1 : maxE * baseShift ≤ (maxE * baseShift + maxE * Tg + 1) := by omega
        have h2 : maxE * Tg ≤ (maxE * baseShift + maxE * Tg + 1) := by omega
        have h3 : maxE * Tg * N ≤ (maxE * baseShift + maxE * Tg + 1) * N :=
          Nat.mul_le_mul_right N h2
        calc maxE * baseShift + maxE * Tg * N
            ≤ (maxE * baseShift + maxE * Tg + 1) + (maxE * baseShift + maxE * Tg + 1) * N := by omega
          _ = (maxE * baseShift + maxE * Tg + 1) * (N + 1) := by ring
      -- Substantial bound: SS² ≤ M ≤ T * (N + 1).
      set SS : ℕ := Nat.sqrt (maxE * UpperC) with hSS_def
      have hSSsq : SS * SS ≤ T * (N + 1) := le_trans hsqUC hUpperC_T
      -- We want (SS + 2) * Cbig ≤ N. Since both sides are naturals, suffices ((SS+2)*Cbig)² ≤ N².
      -- ((SS+2)*Cbig)² = (SS+2)² * Cbig² = (SS² + 4*SS + 4) * Cbig².
      -- We have SS² ≤ T*(N+1) and SS ≤ T*(N+1) (as shown below).
      -- So ((SS+2)*Cbig)² ≤ (5*T*(N+1) + 4) * Cbig².
      -- Need (5*T*(N+1) + 4) * Cbig² ≤ N².
      -- Expand: 5 * T * Cbig² * (N+1) + 4 * Cbig² ≤ N².
      -- We have: T * Cbig² ≤ N/100 (since 100 * T * Cbig² ≤ N).
      -- So 5 * T * Cbig² * (N+1) ≤ N/100 * 5 * (N+1) ≤ N² * 5/100 + 5N/100 ≤ N²/20 + N/20.
      -- And 4 * Cbig² ≤ 4 * Cbig² * T * 100 ≤ N (since 100*Cbig²*T ≤ N), so 4 * Cbig² ≤ N ≤ N²/20 (for N ≥ 20).
      -- Total: ≤ N²/20 + N/20 + N²/20 = 2*N²/20 + N/20 ≤ N²/10 + N/20 ≤ N²/2 ≤ N². ✓
      have hSS_le_TN : SS ≤ T * (N + 1) := by
        rcases Nat.eq_zero_or_pos SS with h0 | hpos
        · rw [h0]; exact Nat.zero_le _
        · -- SS² ≤ T*(N+1), and SS ≤ SS² when SS ≥ 1.
          have : SS * 1 ≤ SS * SS := Nat.mul_le_mul_left SS hpos
          rw [Nat.mul_one] at this
          exact le_trans this hSSsq
      have hT_Cbig_le_N : 100 * (Cbig * Cbig * T) ≤ N := by
        have : 100 * (Cbig * Cbig * T) = 100 * Cbig * Cbig * T := by ring
        rw [this, hN_def2]; omega
      -- Auxiliary: T * Cbig² * (N+1) ≤ T * Cbig² * N + T * Cbig².
      -- 100 * T * Cbig² ≤ N, so T * Cbig² ≤ N / 100, so 100 * T * Cbig² ≤ N.
      have hT_Cbig_N : T * Cbig * Cbig ≤ N := by
        have : T * Cbig * Cbig ≤ 100 * T * Cbig * Cbig := by
          have : 1 ≤ 100 := by norm_num
          calc T * Cbig * Cbig = 1 * (T * Cbig * Cbig) := (one_mul _).symm
            _ ≤ 100 * (T * Cbig * Cbig) := Nat.mul_le_mul_right _ this
            _ = 100 * T * Cbig * Cbig := by ring
        have h2 : 100 * T * Cbig * Cbig = 100 * (Cbig * Cbig * T) := by ring
        omega
      -- The big inequality, proved by nlinarith.
      have hkey : (SS + 2) * Cbig ≤ N := by
        -- We use: a ≤ b ↔ a*a ≤ b*b (for a, b nat, equivalent direction).
        -- Suffices: ((SS+2)*Cbig)² ≤ N².
        -- ((SS+2)*Cbig)² = (SS² + 4 SS + 4) * Cbig²
        -- Use SS² ≤ T(N+1), SS ≤ T(N+1).
        -- ≤ (5T(N+1) + 4) * Cbig²
        -- = 5 * T * Cbig² * N + 5 * T * Cbig² + 4 * Cbig².
        -- Each term controlled.
        have hsq_le : ((SS + 2) * Cbig) * ((SS + 2) * Cbig) ≤ N * N := by
          -- LHS = (SS + 2)^2 * Cbig^2 = (SS² + 4 SS + 4) * Cbig²
          have hLHS : ((SS + 2) * Cbig) * ((SS + 2) * Cbig) =
              SS * SS * (Cbig * Cbig) + 4 * SS * (Cbig * Cbig) + 4 * (Cbig * Cbig) := by ring
          rw [hLHS]
          -- Bound each term.
          have hb1 : SS * SS * (Cbig * Cbig) ≤ T * (N + 1) * (Cbig * Cbig) :=
            Nat.mul_le_mul_right _ hSSsq
          have hb2 : 4 * SS * (Cbig * Cbig) ≤ 4 * (T * (N + 1)) * (Cbig * Cbig) := by
            have : 4 * SS ≤ 4 * (T * (N + 1)) := Nat.mul_le_mul_left 4 hSS_le_TN
            exact Nat.mul_le_mul_right _ this
          -- Sum: ≤ 5 * T * (N + 1) * Cbig² + 4 * Cbig².
          have hsum_le : SS * SS * (Cbig * Cbig) + 4 * SS * (Cbig * Cbig) + 4 * (Cbig * Cbig) ≤
              5 * (T * (N + 1)) * (Cbig * Cbig) + 4 * (Cbig * Cbig) := by
            have : SS * SS * (Cbig * Cbig) + 4 * SS * (Cbig * Cbig) ≤
                T * (N + 1) * (Cbig * Cbig) + 4 * (T * (N + 1)) * (Cbig * Cbig) := by
              omega
            have h2 : T * (N + 1) * (Cbig * Cbig) + 4 * (T * (N + 1)) * (Cbig * Cbig) =
                5 * (T * (N + 1)) * (Cbig * Cbig) := by ring
            omega
          -- Final: 5 * T * (N+1) * Cbig² + 4 * Cbig² ≤ N².
          -- Expand: 5 * T * Cbig² * N + 5 * T * Cbig² + 4 * Cbig² ≤ N².
          -- T * Cbig² ≤ N (from hT_Cbig_N), so 5 * T * Cbig² * N ≤ 5 * N² and 5 * T * Cbig² ≤ 5 * N.
          -- 4 * Cbig² ≤ 4 * (T * Cbig²) ≤ 4 * N (using T ≥ 1). Wait, 4 * Cbig² ≤ 4 * Cbig² * T = 4 * (T * Cbig²) ≤ 4 * N.
          -- Sum: 5N² + 5N + 4N = 5N² + 9N. We need ≤ N². NOPE. So 100 not big enough.
          -- WAIT: I need to use that 100 * T * Cbig² ≤ N, NOT just T * Cbig² ≤ N.
          -- So T * Cbig² ≤ N/100. So 5 * T * Cbig² * N ≤ 5N²/100 = N²/20.
          -- Hmm but I wrote hT_Cbig_N : T * Cbig² ≤ N. Looser.
          -- Let me get a tighter bound.
          have hT_Cbig_N_tight : 100 * (T * (Cbig * Cbig)) ≤ N := by
            have h1 : 100 * (T * (Cbig * Cbig)) = 100 * (Cbig * Cbig * T) := by ring
            rw [h1]; exact hT_Cbig_le_N
          -- Now: 5 * T * (N+1) * Cbig² + 4 * Cbig²
          --    = 5 * T * Cbig² * N + 5 * T * Cbig² + 4 * Cbig².
          -- Bound 5 * T * Cbig² * N ≤ 5 * N * N / 100 = N²/20 ≤ N².
          -- Bound 5 * T * Cbig² ≤ 5 * N / 100 ≤ N.
          -- Bound 4 * Cbig² ≤ 4 * (T * Cbig²) ≤ 4 * N / 100 ≤ N.
          -- Sum: N²/20 + N + N ≤ N² (for N large).
          -- Concrete: N²/20 + 2N ≤ N² requires N²/20 - N² + 2N ≤ 0, i.e., -19N²/20 + 2N ≤ 0,
          -- i.e., 2N ≤ 19N²/20, i.e., 40 ≤ 19N, i.e., N ≥ 40/19 ≈ 2.1. Easy since N ≥ 100.
          -- Use nlinarith.
          have hN_100 : 100 ≤ N := by rw [hN_def2]; omega
          -- Let Y := T * (Cbig * Cbig). Have: 100 * Y ≤ N.
          -- Cbig * Cbig ≤ Y (since T ≥ 1).
          have hCsq_le_Y : Cbig * Cbig ≤ T * (Cbig * Cbig) := by
            calc Cbig * Cbig = 1 * (Cbig * Cbig) := (one_mul _).symm
              _ ≤ T * (Cbig * Cbig) := Nat.mul_le_mul_right _ hT_ge
          -- Rewrite LHS in terms of Y.
          -- 5 * (T * (N + 1)) * (Cbig * Cbig) = 5 * (T * (Cbig * Cbig)) * (N + 1)
          --                                  = 5 * Y * N + 5 * Y.
          -- 4 * (Cbig * Cbig) ≤ 4 * Y.
          -- So total ≤ 5*Y*N + 5*Y + 4*Y = 5*Y*N + 9*Y.
          have hLHS_le : 5 * (T * (N + 1)) * (Cbig * Cbig) + 4 * (Cbig * Cbig) ≤
              5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig)) := by
            have h1 : 5 * (T * (N + 1)) * (Cbig * Cbig) =
                5 * (T * (Cbig * Cbig)) * N + 5 * (T * (Cbig * Cbig)) := by ring
            have h2 : 4 * (Cbig * Cbig) ≤ 4 * (T * (Cbig * Cbig)) := by
              apply Nat.mul_le_mul_left; exact hCsq_le_Y
            omega
          -- Now: 5*Y*N + 9*Y ≤ N².
          -- Multiply 100*Y ≤ N by N: 100*Y*N ≤ N*N. So 5*Y*N ≤ N*N/20 ≤ N*N.
          -- Multiply 100*Y ≤ N by 1: 100*Y ≤ N. So 9*Y ≤ 9*N/100 ≤ N (for N ≥ 9*N/100 iff N ≥ 0).
          -- 5*Y*N + 9*Y ≤ ?
          -- Concrete: 100 * (5*Y*N + 9*Y) = 500*Y*N + 900*Y. And 500*Y*N ≤ 5*N*N (mult both sides by 5N), 900*Y ≤ 9*N.
          -- So 100 * (5*Y*N + 9*Y) ≤ 5*N*N + 9*N.
          -- And we want 5*Y*N + 9*Y ≤ N*N. Equivalent to 100*(5*Y*N+9*Y) ≤ 100*N*N.
          -- Have 100*(5*Y*N+9*Y) ≤ 5*N²+9*N. And 5*N²+9*N ≤ 100*N² iff 95N² ≥ 9N iff N(95N-9) ≥ 0 ✓.
          have hY_bound : 5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig)) ≤ N * N := by
            -- 100 * (5*Y*N + 9*Y) ≤ 5*N² + 9*N ≤ 100*N² (for N ≥ 1).
            -- Step 1: 100 * Y * N ≤ N * N (from 100 * Y ≤ N).
            have step1 : 100 * (T * (Cbig * Cbig)) * N ≤ N * N := by
              have := Nat.mul_le_mul_right N hT_Cbig_N_tight
              linarith
            -- Step 2: 5 * Y * N ≤ N * N (since 5 ≤ 100).
            have step2 : 5 * (T * (Cbig * Cbig)) * N ≤ N * N := by
              have h : 5 * (T * (Cbig * Cbig)) * N ≤ 100 * (T * (Cbig * Cbig)) * N := by
                have : (5 : ℕ) ≤ 100 := by norm_num
                nlinarith
              linarith
            -- Step 3: 9 * Y ≤ N (from 100 * Y ≤ N and 9 ≤ 100).
            have step3 : 9 * (T * (Cbig * Cbig)) ≤ N := by
              have : 9 * (T * (Cbig * Cbig)) ≤ 100 * (T * (Cbig * Cbig)) := by
                have : (9 : ℕ) ≤ 100 := by norm_num
                nlinarith
              linarith
            -- Step 4: combine. Need 5*Y*N + 9*Y ≤ N². Use step2 + step3, but they're separate bounds.
            -- 5*Y*N + 9*Y ≤ N*N + N. We need ≤ N*N. Hmm, off by N.
            -- BUT step2 actually gives 5*Y*N ≤ N²/20, which gives lots of room. Let me use a tighter form.
            -- Tighter: from 100 * Y ≤ N, we get 5 * Y ≤ N/20. So 5*Y*N + 9*Y = Y * (5N + 9) ≤ ?
            -- Y * (5N + 9). 100 * Y * (5N + 9) ≤ N * (5N + 9) = 5*N² + 9*N.
            -- We want Y*(5N+9) ≤ N². Equivalent: 100 * Y * (5N+9) ≤ 100 * N². Have ≤ 5N²+9N. Need ≤ 100 N². ✓.
            have step4 : 100 * (5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig))) ≤ 5 * (N * N) + 9 * N := by
              -- = 500 * Y * N + 900 * Y. Bound each.
              -- 500 * Y * N = 5 * (100 * Y * N) ≤ 5 * (N * N) = 5*N².
              -- 900 * Y = 9 * (100 * Y) ≤ 9 * N.
              have ha : 500 * (T * (Cbig * Cbig)) * N ≤ 5 * (N * N) := by
                have : 5 * (100 * (T * (Cbig * Cbig)) * N) = 500 * (T * (Cbig * Cbig)) * N := by ring
                have h2 := Nat.mul_le_mul_left 5 step1
                linarith
              have hb : 900 * (T * (Cbig * Cbig)) ≤ 9 * N := by
                have : 9 * (100 * (T * (Cbig * Cbig))) = 900 * (T * (Cbig * Cbig)) := by ring
                have h2 := Nat.mul_le_mul_left 9 hT_Cbig_N_tight
                linarith
              -- 100 * (5*Y*N + 9*Y) = 500 * Y * N + 900 * Y ≤ 5*N² + 9*N.
              have hexpand : 100 * (5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig))) =
                  500 * (T * (Cbig * Cbig)) * N + 900 * (T * (Cbig * Cbig)) := by ring
              linarith
            -- Now 5 * N² + 9 * N ≤ 100 * N² for N ≥ 1.
            have step5 : 5 * (N * N) + 9 * N ≤ 100 * (N * N) := by
              have h1 : 9 * N ≤ 95 * (N * N) := by
                -- 9 N ≤ 95 N² iff 9 ≤ 95 N iff N ≥ 9/95 ≈ 0.1. Since N ≥ 100, easy.
                have hN_le_NN : N ≤ N * N := by
                  rcases Nat.eq_zero_or_pos N with hn | hp
                  · rw [hn]
                  · calc N = N * 1 := (Nat.mul_one _).symm
                      _ ≤ N * N := Nat.mul_le_mul_left _ hp
                have h2 : 9 * N ≤ 9 * (N * N) := Nat.mul_le_mul_left 9 hN_le_NN
                have h3 : 9 * (N * N) ≤ 95 * (N * N) :=
                  Nat.mul_le_mul_right _ (by norm_num : (9 : ℕ) ≤ 95)
                linarith
              linarith
            -- Combine: 100 * (5 Y N + 9 Y) ≤ 5N² + 9N ≤ 100 N², so 5YN + 9Y ≤ N².
            have h6 : 100 * (5 * (T * (Cbig * Cbig)) * N + 9 * (T * (Cbig * Cbig))) ≤ 100 * (N * N) :=
              le_trans step4 step5
            exact Nat.le_of_mul_le_mul_left h6 (by norm_num : 0 < 100)
          linarith
        -- Convert ((SS+2)*Cbig)² ≤ N² to (SS+2)*Cbig ≤ N.
        have hh : (SS + 2) * Cbig ≤ N := by
          rw [show N * N = N ^ 2 from by ring,
              show ((SS + 2) * Cbig) * ((SS + 2) * Cbig) = ((SS + 2) * Cbig) ^ 2 from by ring] at hsq_le
          have := (Nat.pow_le_pow_iff_left (n := 2) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq_le
          exact this
        exact hh
      have hbk_lt : badK_finset.card < N + 1 := by
        have h1 : Jbound = Nat.sqrt (maxE * UpperC) + 2 := hJbound_def
        have h2 : Jbound * HEcard ≤ Jbound * Cbig := by
          apply Nat.mul_le_mul_left
          rw [hCbig_def]; omega
        have h3 : Jbound * Cbig ≤ N := by rw [h1]; exact hkey
        omega
      exact hbk_lt
    obtain ⟨k, hk_mem, hk_notin⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
    rw [hAPseg_def] at hk_mem
    have hk_ge : kStart ≤ k := (Finset.mem_Icc.mp hk_mem).1
    have hk_le : k ≤ kStart + N := (Finset.mem_Icc.mp hk_mem).2
    refine ⟨k, hkStart_AP k hk_ge, ?_⟩
    intro j hjJ h hh e he heq
    apply hk_notin
    exact hbadK_contains k hk_le ⟨j, h, e, hjJ, hh, he, heq⟩
  -- Step 6: assemble the final witness from k.
  refine ⟨aσ + k * Tg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- AP membership.
    exact (Nat.add_mul_modulus_modEq_iff).mpr (Nat.ModEq.refl aσ)
  · -- lower < c.
    have : XbadMax ≤ aσ + k * Tg := hk_AP
    have : X₀ ≤ aσ + k * Tg := le_trans hXbadMax_ge_X₀ this
    omega
  · -- L < c.
    have : XbadMax ≤ aσ + k * Tg := hk_AP
    have : X₀ ≤ aσ + k * Tg := le_trans hXbadMax_ge_X₀ this
    omega
  · -- Q positivity.
    have hX₀_le : X₀ ≤ aσ + k * Tg := le_trans hXbadMax_ge_X₀ hk_AP
    have hNpos_le : Npos ≤ aσ + k * Tg := le_trans hX₀_Npos hX₀_le
    exact hNpos (aσ + k * Tg) hNpos_le
  · -- Avoid forbiddenFinite.
    rcases hbadFin_forbid (aσ + k * Tg) with h | h
    · -- Goal: ∀ e ∈ insert 1 Gν, e * (aσ + k*Tg) ∉ forbiddenFinite. Note EE = insert 1 Gν.
      intro e he
      have heE : e ∈ EE := by rw [hEE_def]; exact he
      exact h e heE
    · exfalso; exact hXbadMax_avoid (aσ + k * Tg) hk_AP h
  · -- Avoid main collisions.
    intro j hj h hh e he
    have heE : e ∈ EE := by rw [hEE_def]; exact he
    exact hk_main j hj h hh e heE
end ExistsLargeCorrectionDenominator

/-! ## Correction slots (assembled)

The full correction-slot setup. Given `g ≥ 1` and the data needed for
`finite_switch_values_generate_zmod`, produce the list of correction
denominators `c_ν`, patterns `G_ν`, and increments `b_ν` such that:

  * `b_ν > 0` (positivity of `Q_{G_ν}`)
  * `b_ν ≡ ρ_σ (mod g)` for the assigned residue
  * Reciprocal sum `C_0 := ∑_ν 1/c_ν < δ` (made small by choosing `c_ν` large)
  * Subset sums of `{b_ν}` represent every residue mod `g`
  * No collisions with main slots, between correction slots, etc.

Statement deferred — assembled inside `Theorem1.lean`. -/

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/Theorem1.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — §2 main theorem assembly.

`theorem_1`: For `α ∈ ℚ_{>0}`, `L ≥ 1`, and `p ∈ ℚ[x]` integer-valued, with
positive leading coefficient and no fixed divisor on positive integers, all
sufficiently large integers `m` admit an expression `m = ∑ p(n_i)` with
distinct `L < n_1 < ⋯ < n_k` and `∑ 1/n_i = α`.

Sub-results:
  * `main_window_representation` — multiples of `g` in `[M_0, μ N^{2r}]` are
    subset sums of `A(D j)`, by RSG applied to `q := A ∘ Dpoly / g`.
  * `attainable_interval` — every integer in `[B_N + B_* + M_0, B_N + μ N^{2r}]`
    is an attainable p-sum.
  * `B_diff_tendsto` — `(B_{N+1} - B_N) / N^{2r} → λ` (for explicit `λ`).
  * `intervals_overlap_eventually` — consecutive intervals overlap for large `N`.

Trust boundary: `roth_szekeres_graham` (Basic.lean) only.
-/


namespace PolynomialEgyptianSums

open Filter Polynomial Finset

/-! ## Construction-data records

The non-constant branch of `theorem_1` constructs auxiliary data in two
phases. Splitting them into records keeps the proof modular and makes the
RSG inputs explicit. -/

/-- **First phase**: choose `J` so that the asymptotic threshold conditions
hold. The key facts are:
  * `1 ≤ J`,
  * `A(D j) > 0` for all `j ≥ J` (positivity past the leading-coefficient
    threshold of `A p`),
  * `1/(P u_J) < α` (the telescoping head leaves room for filler),
  * `L < D J` and `L < τ J` (denominator threshold respected). -/
structure MainChoice (α : ℚ) (L : ℕ) (p : ℚ[X]) (hp : IntValued p) : Type where
  J : ℕ
  hJ_pos : 1 ≤ J
  hA_pos :
    ∀ j : ℕ, J ≤ j →
      0 < intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)
  hleft_small :
    (1 : ℚ) / ((P : ℚ) * (u J : ℚ)) < α
  hD_gt_L : L < D J
  htau_base_gt_L : L < tau J

/-- **Second phase**: extract the gcd `g` of `A(D j)` values for `j ≥ J`,
along with the no-prime-fixed-divisor RSG hypothesis for the quotient
polynomial `qPoly p md.J g`. The `hg_no_prime_fixed_quot` field is the key
RSG bridge: it says that for every prime `ℓ`, some quotient value
`(qPoly p md.J g).eval (t : ℚ) ≠ 0 (mod ℓ)` for `t ≥ 1`. -/
structure MainGCDData
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (md : MainChoice α L p hp) : Type where
  g : ℕ
  hg_pos : 1 ≤ g
  hg_dvd :
    ∀ j : ℕ, md.J ≤ j →
      (g : ℤ) ∣
        intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)
  hg_no_prime_fixed_quot :
    ∀ ℓ : ℕ, ℓ.Prime →
      ∃ t : ℕ, 1 ≤ t ∧ ∃ z : ℤ,
        (z : ℚ) = (qPoly p md.J g).eval (t : ℚ) ∧
        ¬ ((ℓ : ℤ) ∣ z)

/-- Constructor for `MainChoice`: under the standard hypotheses (positive
leading coefficient + nonconstant), there exists `J ≥ 1` satisfying all the
threshold conditions of `MainChoice`. -/
lemma chooseMainChoice (α : ℚ) (hα : 0 < α) (L : ℕ) (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    Nonempty (MainChoice α L p hp) := by
  -- Cast `A p : ℚ[X]` to a real polynomial to apply the asymptotic lemma.
  set Ar : ℝ[X] := (A p).map (algebraMap ℚ ℝ) with hAr_def
  have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
    (algebraMap ℚ ℝ).injective
  have hAr_natDegree : Ar.natDegree = p.natDegree := by
    rw [hAr_def, Polynomial.natDegree_map_eq_of_injective h_inj,
        A_natDegree_eq p h_nonconst h_lead_pos]
  have hAr_lead : (0 : ℝ) < Ar.leadingCoeff := by
    rw [hAr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
    have hpos : (0 : ℚ) < (A p).leadingCoeff := A_leadingCoeff p h_nonconst h_lead_pos
    have : (0 : ℝ) < ((A p).leadingCoeff : ℝ) := by exact_mod_cast hpos
    simpa [algebraMap] using this
  have hAr_deg_pos : 0 < Ar.degree := by
    have hnat : 0 < Ar.natDegree := by
      rw [hAr_natDegree]; exact h_nonconst
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
  -- `Ar.eval` tends to `+∞` at `+∞`.
  have h_tendsto : Filter.Tendsto (fun x : ℝ => Ar.eval x) Filter.atTop Filter.atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg Ar hAr_deg_pos hAr_lead.le
  -- Get a real threshold N₀ : ℝ such that x ≥ N₀ ⇒ Ar.eval x ≥ 1.
  have hN0 : ∃ N0 : ℝ, ∀ x : ℝ, N0 ≤ x → 1 ≤ Ar.eval x :=
    Filter.tendsto_atTop_atTop.mp h_tendsto 1
  obtain ⟨N0, hN0_le⟩ := hN0
  -- We need a natural-number threshold M such that for j ≥ M, (D j : ℝ) ≥ N0.
  -- `D j = (36j+1)(36(j+1)+1) ≥ j`, so M := ⌈N0⌉₊ + 1 works.
  set M_real : ℕ := Nat.ceil (max N0 0) with hM_real_def
  have hM_real_ge : (M_real : ℝ) ≥ N0 := by
    have hN0_le_max : N0 ≤ max N0 0 := le_max_left _ _
    have h_le_ceil : (max N0 0) ≤ (Nat.ceil (max N0 0) : ℝ) := Nat.le_ceil _
    linarith
  -- We also want a lower bound for `1 / (P · u_J) < α`.
  -- u_J = 36J + 1, P = 36, so P · u_J = 36(36J+1) ≥ 36J ≥ J.
  -- We need 1 / (P · u_J) < α, i.e., (P · u_J) · α > 1.
  -- Since P · u_J ≥ J, sufficient that J · α > 1, i.e., J > 1/α.
  set M_alpha : ℕ := Nat.ceil ((1 : ℚ) / α) + 1 with hM_alpha_def
  -- Final J: max of all thresholds, plus extra to ensure all conditions.
  set J : ℕ := max (max M_real M_alpha) (max (L + 1) 1) with hJ_def
  refine ⟨{ J := J, hJ_pos := ?_, hA_pos := ?_, hleft_small := ?_,
            hD_gt_L := ?_, htau_base_gt_L := ?_ }⟩
  · -- 1 ≤ J
    have : 1 ≤ max (L + 1) 1 := le_max_right _ _
    exact le_trans this (le_max_right _ _)
  · -- ∀ j ≥ J, 0 < intEval (A p) (D j : ℤ)
    intro j hj
    -- D j ≥ j ≥ J ≥ M_real, so (D j : ℝ) ≥ N0, so Ar.eval (D j) ≥ 1.
    have hj_ge_M_real : M_real ≤ j := by
      have h1 : M_real ≤ max M_real M_alpha := le_max_left _ _
      have h2 : max M_real M_alpha ≤ J := by
        rw [hJ_def]; exact le_max_left _ _
      omega
    -- D j ≥ j: in fact much bigger, but j is enough.
    have hDj_ge_j : j ≤ D j := by
      unfold D u P
      have h2 : 1 ≤ 36 * (j + 1) + 1 := by omega
      have h3 : j ≤ (36 * j + 1) := by omega
      calc j ≤ 36 * j + 1 := h3
        _ ≤ (36 * j + 1) * (36 * (j + 1) + 1) := Nat.le_mul_of_pos_right _ h2
    have hDj_ge_M_real : M_real ≤ D j := le_trans hj_ge_M_real hDj_ge_j
    have hDj_real_ge_N0 : N0 ≤ ((D j : ℕ) : ℝ) := by
      have : ((M_real : ℕ) : ℝ) ≤ ((D j : ℕ) : ℝ) := by exact_mod_cast hDj_ge_M_real
      linarith
    -- Ar.eval ((D j : ℕ) : ℝ) ≥ 1.
    have h_eval_real : 1 ≤ Ar.eval ((D j : ℕ) : ℝ) := hN0_le _ hDj_real_ge_N0
    -- Convert: Ar.eval ((D j : ℕ) : ℝ) = ((A p).eval ((D j : ℕ) : ℚ) : ℝ).
    have h_eval_cast :
        Ar.eval ((D j : ℕ) : ℝ) = (((A p).eval ((D j : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [hAr_def]
      have h1 : ((D j : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((D j : ℕ) : ℚ) := by
        simp [algebraMap]
      rw [h1, Polynomial.eval_map_apply]
      simp [algebraMap]
    -- So 1 ≤ (A p).eval ((D j : ℕ) : ℚ) (in ℝ, hence ℚ).
    have h_eval_q : 1 ≤ (A p).eval ((D j : ℕ) : ℚ) := by
      have : ((1 : ℚ) : ℝ) ≤ ((((A p).eval ((D j : ℕ) : ℚ)) : ℚ) : ℝ) := by
        rw [show ((1 : ℚ) : ℝ) = (1 : ℝ) by norm_num]
        rw [← h_eval_cast]; exact h_eval_real
      exact_mod_cast this
    -- intEval is positive iff its rational version is.
    have h_intEval_eq :
        ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ) =
          (A p).eval ((D j : ℕ) : ℚ) := by
      rw [intEval_spec]
      push_cast
      rfl
    have h_pos_q : 0 < (A p).eval ((D j : ℕ) : ℚ) := by linarith
    have h_pos_int : (0 : ℚ) < ((intEval (A p) (A_intValued p hp)
        ((D j : ℕ) : ℤ) : ℤ) : ℚ) := by rw [h_intEval_eq]; exact h_pos_q
    exact_mod_cast h_pos_int
  · -- 1 / (P · u_J) < α
    -- Since J ≥ M_alpha = ⌈1/α⌉ + 1 > 1/α, we have α · J > 1, and
    -- P · u_J ≥ u_J ≥ J + 1 > J, so α · P · u_J > 1.
    have hJ_ge_M_alpha : M_alpha ≤ J := by
      have h1 : M_alpha ≤ max M_real M_alpha := le_max_right _ _
      have h2 : max M_real M_alpha ≤ J := by
        rw [hJ_def]; exact le_max_left _ _
      omega
    have hP_ge_one : (1 : ℚ) ≤ (P : ℚ) := by unfold P; norm_num
    have huJ_ge : (J + 1 : ℚ) ≤ (u J : ℚ) := by
      unfold u P; push_cast; linarith
    have huJ_pos : (0 : ℚ) < (u J : ℚ) := by unfold u P; push_cast; positivity
    have hPuJ_pos : (0 : ℚ) < ((P : ℚ) * (u J : ℚ)) := by
      have hP_pos : (0 : ℚ) < (P : ℚ) := by unfold P; norm_num
      exact mul_pos hP_pos huJ_pos
    rw [div_lt_iff₀ hPuJ_pos]
    -- J > 1/α (strictly).
    have hJ_alpha_strict : (1 : ℚ) / α < (J : ℚ) := by
      have h_ceil_ge : ((1 : ℚ) / α) ≤ (Nat.ceil ((1 : ℚ) / α) : ℚ) := Nat.le_ceil _
      have hM_alpha_le_J : ((M_alpha : ℕ) : ℚ) ≤ (J : ℚ) := by exact_mod_cast hJ_ge_M_alpha
      rw [hM_alpha_def] at hM_alpha_le_J
      push_cast at hM_alpha_le_J
      linarith
    -- Hence α · J > 1.
    have h_alpha_J : (1 : ℚ) < α * (J : ℚ) := by
      have hα_ne : α ≠ 0 := ne_of_gt hα
      have h_eq : α * (1 / α) = 1 := by field_simp
      nlinarith [hα, hJ_alpha_strict]
    -- P · u_J ≥ J: u_J ≥ J + 1 > J, and P ≥ 1.
    have hJ_le_PuJ : (J : ℚ) ≤ (P : ℚ) * (u J : ℚ) := by
      have hJ_le_uJ : (J : ℚ) ≤ (u J : ℚ) := by linarith
      calc (J : ℚ) ≤ (u J : ℚ) := hJ_le_uJ
        _ = 1 * (u J : ℚ) := by ring
        _ ≤ (P : ℚ) * (u J : ℚ) := mul_le_mul_of_nonneg_right hP_ge_one huJ_pos.le
    have h_step : α * (J : ℚ) ≤ α * ((P : ℚ) * (u J : ℚ)) :=
      mul_le_mul_of_nonneg_left hJ_le_PuJ hα.le
    linarith [h_alpha_J, h_step]
  · -- L < D J
    have hJ_ge_L1 : L + 1 ≤ J := by
      have h1 : L + 1 ≤ max (L + 1) 1 := le_max_left _ _
      have h2 : max (L + 1) 1 ≤ J := by rw [hJ_def]; exact le_max_right _ _
      omega
    -- D J ≥ J ≥ L + 1 > L.
    have hJ_le_DJ : J ≤ D J := by
      unfold D u P
      have h2 : 1 ≤ 36 * (J + 1) + 1 := by omega
      have h3 : J ≤ (36 * J + 1) := by omega
      calc J ≤ 36 * J + 1 := h3
        _ ≤ (36 * J + 1) * (36 * (J + 1) + 1) := Nat.le_mul_of_pos_right _ h2
    omega
  · -- L < tau J
    have hJ_ge_L1 : L + 1 ≤ J := by
      have h1 : L + 1 ≤ max (L + 1) 1 := le_max_left _ _
      have h2 : max (L + 1) 1 ≤ J := by rw [hJ_def]; exact le_max_right _ _
      omega
    -- tau J = P · u (J+1) = 36 · (36(J+1)+1) ≥ J+1 ≥ L+1 > L.
    have hJ_le_tau : J ≤ tau J := by
      unfold tau u P
      -- tau J = 36 · (36(J+1)+1) ≥ 36 · (J+1) ≥ J+1 > J
      have hJ1 : J + 1 ≤ 36 * (J + 1) + 1 := by omega
      calc J ≤ J + 1 := by omega
        _ ≤ 36 * (J + 1) + 1 := hJ1
        _ = 1 * (36 * (J + 1) + 1) := by ring
        _ ≤ 36 * (36 * (J + 1) + 1) := by
            apply Nat.mul_le_mul_right; omega
    omega

set_option linter.unusedVariables false in
/-- Constructor for `MainGCDData`: given a fixed `MainChoice md` (so `J` is
chosen and `A(D j) > 0` for `j ≥ J`), extract the gcd `g` of the integer
values `A(D j) : j ≥ J` (as the natAbs of the generator of
`Ideal.span (mainValueSet p hp md.J)`), prove `1 ≤ g` and divisibility,
and prove the no-prime-fixed-divisor RSG hypothesis for the quotient
values. -/
lemma chooseMainGCDData {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (md : MainChoice α L p hp) :
    Nonempty (MainGCDData p hp md) := by
  classical
  -- The ideal we extract a generator from.
  set I : Ideal ℤ := Ideal.span (mainValueSet p hp md.J) with hI_def
  -- ℤ is a PID, so I is principal.
  haveI hI_principal : Submodule.IsPrincipal I := IsPrincipalIdealRing.principal I
  set z : ℤ := Submodule.IsPrincipal.generator I with hz_def
  set g : ℕ := z.natAbs with hg_def
  -- Span = ⟨z⟩.
  have hI_span : Ideal.span ({z} : Set ℤ) = I :=
    Submodule.IsPrincipal.span_singleton_generator I
  -- The value at j = md.J is in mainValueSet, hence in I, and is positive.
  have hA_J_pos : 0 < intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ) :=
    md.hA_pos md.J (le_refl _)
  have hA_J_in_set :
      intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ)
        ∈ mainValueSet p hp md.J := ⟨md.J, le_refl _, rfl⟩
  have hA_J_in_I :
      intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ) ∈ I :=
    Ideal.subset_span hA_J_in_set
  -- I ≠ ⊥ since it contains a positive integer.
  have hI_ne_bot : I ≠ ⊥ := by
    intro h_bot
    have : intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ) = 0 := by
      have hmem : intEval (A p) (A_intValued p hp) ((D md.J : ℕ) : ℤ) ∈ (⊥ : Ideal ℤ) := by
        rw [← h_bot]; exact hA_J_in_I
      simpa [Ideal.mem_bot] using hmem
    omega
  -- Hence z ≠ 0, so g ≥ 1.
  have hz_ne_zero : z ≠ 0 := by
    intro hz0
    apply hI_ne_bot
    rw [Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero, ← hz_def]
    exact hz0
  have hg_pos : 1 ≤ g := by
    have : 0 < g := Int.natAbs_pos.mpr hz_ne_zero
    omega
  -- Divisibility: for j ≥ md.J, intEval (A p) (D j) ∈ I, hence z ∣ it, hence g ∣ it.
  have hg_dvd :
      ∀ j : ℕ, md.J ≤ j →
        (g : ℤ) ∣ intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) := by
    intro j hj
    have hmem : intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) ∈ I :=
      Ideal.subset_span ⟨j, hj, rfl⟩
    rw [← hI_span, Ideal.mem_span_singleton] at hmem
    -- z ∣ value, hence (z.natAbs : ℤ) ∣ value.
    rw [hg_def, Int.natAbs_dvd]
    exact hmem
  -- Step 4: no-prime-fixed-quot. Use that g ∈ I (the generator) is a finite ℤ-combo
  -- of values from mainValueSet. Dividing by g yields 1 = ∑ cᵢ (sᵢ/g), so any prime
  -- dividing every quotient would divide 1 — contradiction.
  have hg_no_prime_fixed_quot :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ t : ℕ, 1 ≤ t ∧ ∃ z' : ℤ,
          (z' : ℚ) = (qPoly p md.J g).eval (t : ℚ) ∧
          ¬ ((ℓ : ℤ) ∣ z') := by
    intro ℓ hℓ
    -- We argue by contradiction: assume ℓ divides every quotient (qPoly).eval(t).
    by_contra h_no
    push_neg at h_no
    -- After negating ∃ t, ∃ z', ..., we get ∀ t ≥ 1, ∀ z', if (z' = ...) then ℓ ∣ z'.
    have hℓ_dvd_quot : ∀ t : ℕ, 1 ≤ t → ∀ z' : ℤ,
        (z' : ℚ) = (qPoly p md.J g).eval (t : ℚ) → (ℓ : ℤ) ∣ z' := h_no
    -- The key idea: derive (ℓ * g : ℤ) ∣ a for every a ∈ mainValueSet,
    -- hence (ℓ * g : ℤ) ∣ z (the principal generator). But z.natAbs = g, so |z| = g,
    -- so ℓ * g ∣ ±g, forcing ℓ ∣ 1, contradiction.
    -- For each j ≥ md.J, ℓ * g ∣ intEval (A p) (D j).
    have hℓg_dvd : ∀ j : ℕ, md.J ≤ j →
        ((ℓ : ℤ) * (g : ℤ)) ∣ intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) := by
      intro j hj
      -- t := j - md.J + 1
      set t : ℕ := j - md.J + 1 with ht_def
      have ht_pos : 1 ≤ t := by omega
      have ht_eq : md.J + t - 1 = j := by omega
      -- Quotient value as integer:
      have hg_dvd_j := hg_dvd j hj
      obtain ⟨q, hq⟩ := hg_dvd_j
      -- (q : ℚ) = (qPoly).eval (t : ℚ)
      have hq_eq_eval : (q : ℚ) = (qPoly p md.J g).eval (t : ℚ) := by
        rw [qPoly_eval_at_succ p hp md.J g t ht_pos, ht_eq]
        rw [hq]
        push_cast
        have hg_ne : (g : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mp hg_pos)
        field_simp
      -- ℓ ∣ q.
      have hℓ_dvd_q : (ℓ : ℤ) ∣ q := hℓ_dvd_quot t ht_pos q hq_eq_eval
      -- So ℓ * g ∣ g * q = intEval (A p) (D j).
      obtain ⟨q', hq'⟩ := hℓ_dvd_q
      refine ⟨q', ?_⟩
      rw [hq, hq']
      ring
    -- Hence I ⊆ ⟨ℓ * g⟩.
    have hI_le : I ≤ Ideal.span ({(ℓ : ℤ) * (g : ℤ)} : Set ℤ) := by
      rw [hI_def]
      apply Ideal.span_le.mpr
      intro x hx
      obtain ⟨j, hj, hx_eq⟩ := hx
      have : x ∈ Ideal.span ({(ℓ : ℤ) * (g : ℤ)} : Set ℤ) := by
        rw [Ideal.mem_span_singleton, hx_eq]
        exact hℓg_dvd j hj
      exact this
    -- z ∈ I ⊆ ⟨ℓ * g⟩, so ℓ * g ∣ z.
    have hz_mem_I : z ∈ I := Submodule.IsPrincipal.generator_mem I
    have hℓg_dvd_z : ((ℓ : ℤ) * (g : ℤ)) ∣ z := by
      have hz_in : z ∈ Ideal.span ({(ℓ : ℤ) * (g : ℤ)} : Set ℤ) := hI_le hz_mem_I
      rwa [Ideal.mem_span_singleton] at hz_in
    -- (g : ℤ) = z.natAbs, so |z| = g, so z = ±g. Hence ℓ * g ∣ ±g, so ℓ ∣ 1.
    have hg_eq_natAbs : (g : ℤ) = z.natAbs := by rw [hg_def]
    -- z = g or z = -g.
    rcases Int.natAbs_eq z with hpos | hneg
    · -- z = z.natAbs = g
      have hz_eq_g : z = (g : ℤ) := by rw [hpos, hg_eq_natAbs]
      rw [hz_eq_g] at hℓg_dvd_z
      -- (ℓ * g : ℤ) ∣ (g : ℤ).
      have hg_pos_int : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hg_pos
      have : (ℓ : ℤ) ∣ 1 := by
        rcases hℓg_dvd_z with ⟨k, hk⟩
        -- (g : ℤ) = ℓ * g * k = g * (ℓ * k), cancel g.
        have hg_ne : (g : ℤ) ≠ 0 := ne_of_gt hg_pos_int
        have hk' : (1 : ℤ) = ℓ * k := by
          have : (g : ℤ) * 1 = (g : ℤ) * (ℓ * k) := by linarith
          exact (mul_left_cancel₀ hg_ne this)
        exact ⟨k, hk'⟩
      -- ℓ prime, so ℓ ≥ 2, so ℓ ∤ 1.
      have hℓ_ge_two : 2 ≤ ℓ := hℓ.two_le
      have h_le : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) this
      have h_ℓ_ge2_int : (2 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ_ge_two
      omega
    · -- z = -z.natAbs = -g
      have hz_eq_neg_g : z = -(g : ℤ) := by rw [hneg, hg_eq_natAbs]
      rw [hz_eq_neg_g] at hℓg_dvd_z
      have hg_pos_int : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hg_pos
      have hℓg_dvd_g : ((ℓ : ℤ) * (g : ℤ)) ∣ (g : ℤ) := by
        rcases hℓg_dvd_z with ⟨k, hk⟩
        refine ⟨-k, ?_⟩
        linarith
      have hℓ_dvd_one : (ℓ : ℤ) ∣ 1 := by
        rcases hℓg_dvd_g with ⟨k, hk⟩
        have hg_ne : (g : ℤ) ≠ 0 := ne_of_gt hg_pos_int
        have hk' : (1 : ℤ) = ℓ * k := by
          have : (g : ℤ) * 1 = (g : ℤ) * (ℓ * k) := by linarith
          exact (mul_left_cancel₀ hg_ne this)
        exact ⟨k, hk'⟩
      have hℓ_ge_two : 2 ≤ ℓ := hℓ.two_le
      have h_le : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hℓ_dvd_one
      have h_ℓ_ge2_int : (2 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ_ge_two
      omega
  exact ⟨{ g := g, hg_pos := hg_pos, hg_dvd := hg_dvd,
           hg_no_prime_fixed_quot := hg_no_prime_fixed_quot }⟩

/-- Helper: `qPoly` takes positive integer values on `n ≥ 1` whenever
`MainChoice` and `MainGCDData` are constructed. Combines `md.hA_pos` (positivity
of `A(D j)`) with `gcd.hg_dvd` (divisibility by `g`) and `qPoly_eval_at_succ`. -/
lemma qPoly_int_pos_on_pos {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (md : MainChoice α L p hp) (gcd : MainGCDData p hp md) :
    ∀ n : ℕ, 1 ≤ n →
      ∃ z : ℤ, 0 < z ∧ (z : ℚ) = (qPoly p md.J gcd.g).eval (n : ℚ) := by
  intro n hn
  -- Set j := md.J + n - 1 so that md.J ≤ j.
  set j : ℕ := md.J + n - 1 with hj_def
  have hjJ : md.J ≤ j := by omega
  -- val := intEval (A p) (D j) is positive.
  set val : ℤ := intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) with hval_def
  have hval_pos : 0 < val := md.hA_pos j hjJ
  -- (gcd.g : ℤ) divides val.
  have hg_dvd_val : (gcd.g : ℤ) ∣ val := gcd.hg_dvd j hjJ
  -- gcd.g is positive (as ℤ).
  have hg_pos_int : (0 : ℤ) < (gcd.g : ℤ) := by exact_mod_cast gcd.hg_pos
  have hg_ne_int : (gcd.g : ℤ) ≠ 0 := ne_of_gt hg_pos_int
  have hg_ne_q : (gcd.g : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp gcd.hg_pos)
  -- Extract z such that val = gcd.g * z.
  obtain ⟨z, hz⟩ := hg_dvd_val
  refine ⟨z, ?_, ?_⟩
  · -- 0 < z. From 0 < val = gcd.g * z and 0 < gcd.g.
    have h1 : 0 < (gcd.g : ℤ) * z := by rw [← hz]; exact hval_pos
    exact Int.pos_of_mul_pos_right h1 hg_pos_int
  · -- (z : ℚ) = (qPoly).eval (n : ℚ).
    -- qPoly_eval_at_succ p hp md.J gcd.g n hn :
    --   (qPoly p md.J gcd.g).eval (n : ℚ) =
    --     ((intEval (A p) (D (md.J + n - 1)) : ℤ) : ℚ) / (gcd.g : ℚ).
    rw [qPoly_eval_at_succ p hp md.J gcd.g n hn]
    -- Now goal: (z : ℚ) = (val : ℚ) / (gcd.g : ℚ), where val = gcd.g * z.
    show (z : ℚ) = ((intEval (A p) (A_intValued p hp)
        ((D (md.J + n - 1) : ℕ) : ℤ) : ℤ) : ℚ) / (gcd.g : ℚ)
    -- Rewrite via val = gcd.g * z.
    have hval_eq : (val : ℚ) = (gcd.g : ℚ) * (z : ℚ) := by
      have : ((val : ℤ) : ℚ) = (((gcd.g : ℤ) * z : ℤ) : ℚ) := by
        rw [hz]
      push_cast at this
      exact this
    -- val on the goal is exactly the intEval expression with j = md.J + n - 1.
    show (z : ℚ) = (val : ℚ) / (gcd.g : ℚ)
    rw [hval_eq]
    field_simp

/-- **Window representation (PDF §2).** Apply Roth–Szekeres–Graham to
`qPoly p md.J gcd.g`. Every sufficiently large integer `X` is a finite subset
sum of `qPoly`-values evaluated at `(i + 1 : ℕ)` for `i : ℕ`. -/
lemma main_window_representation {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (md : MainChoice α L p hp) (gcd : MainGCDData p hp md) :
    ∃ X_q : ℤ, ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ) := by
  exact roth_szekeres_graham (qPoly p md.J gcd.g)
    (qPoly_natDegree_pos p md.J gcd.g gcd.hg_pos h_nonconst h_lead_pos)
    (qPoly_leadingCoeff_pos p md.J gcd.g gcd.hg_pos h_nonconst h_lead_pos)
    (qPoly_int_pos_on_pos p hp md gcd)
    gcd.hg_no_prime_fixed_quot

/-- **Finite-window consequence of RSG.** If the RSG quotient sum for `X` cannot
use any index beyond `N - J` because every such term is already larger than
`X`, then `g · X` is a subset sum of the finite main-window values
`A(D j)`, `J ≤ j ≤ N`.

The eventual asymptotic proof supplies the `h_tail` hypothesis. Keeping it as
an explicit hypothesis isolates the purely algebraic/indexing part of the
main theorem assembly. -/
lemma main_window_finite {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (md : MainChoice α L p hp) (gcd : MainGCDData p hp md)
    (X_q X : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (hX_ge : X_q ≤ X) (N : ℕ) (hJN : md.J ≤ N)
    (h_tail : ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ)) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc md.J N ∧
      ((gcd.g : ℚ) * (X : ℚ)) =
        ∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ) := by
  classical
  obtain ⟨I, hI⟩ := hX_q X hX_ge
  let qv : ℕ → ℚ := fun i => (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ)
  have hqv_nonneg : ∀ i : ℕ, 0 ≤ qv i := by
    intro i
    obtain ⟨z, hz_pos, hz_eq⟩ :=
      qPoly_int_pos_on_pos p hp md gcd (i + 1) (by omega : 1 ≤ i + 1)
    have : (0 : ℚ) < qv i := by
      dsimp [qv]
      rw [← hz_eq]
      exact_mod_cast hz_pos
    exact this.le
  have hI_bound : ∀ i ∈ I, i ≤ N - md.J := by
    intro i hi
    by_contra hle
    have hlt : N - md.J < i := Nat.lt_of_not_ge hle
    have htail_i := h_tail i hlt
    have hqi_le_sum : qv i ≤ ∑ k ∈ I, qv k :=
      Finset.single_le_sum (fun k _ => hqv_nonneg k) hi
    have hsum_eq : ∑ k ∈ I, qv k = (X : ℚ) := by
      dsimp [qv]
      exact hI.symm
    change (X : ℚ) < qv i at htail_i
    linarith
  let S : Finset ℕ := I.image (fun i => md.J + i)
  refine ⟨S, ?_, ?_⟩
  · intro j hj
    simp only [S, Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact Finset.mem_Icc.mpr ⟨by omega, by
      have hi_bound := hI_bound i hi
      omega⟩
  · have hg_ne_q : (gcd.g : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp gcd.hg_pos)
    have hterm : ∀ i ∈ I,
        (gcd.g : ℚ) * qv i =
          ((intEval (A p) (A_intValued p hp) ((D (md.J + i) : ℕ) : ℤ) : ℤ) : ℚ) := by
      intro i _
      dsimp [qv]
      rw [qPoly_eval_at_succ p hp md.J gcd.g (i + 1) (by omega : 1 ≤ i + 1)]
      have hidx : md.J + (i + 1) - 1 = md.J + i := by omega
      rw [hidx]
      field_simp
    calc
      ((gcd.g : ℚ) * (X : ℚ))
          = (gcd.g : ℚ) * ∑ i ∈ I, qv i := by
              rw [hI]
      _ = ∑ i ∈ I,
            ((intEval (A p) (A_intValued p hp) ((D (md.J + i) : ℕ) : ℤ) : ℚ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm i hi
      _ = ∑ j ∈ I.image (fun i => md.J + i),
            ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℚ)) := by
              rw [Finset.sum_image]
              intro a _ b _ hab
              exact Nat.add_left_cancel hab
      _ = ∑ j ∈ S,
            ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℚ)) := rfl

/-! ### Construction-data records: corrections and fillers

These records package the correction-slot and filler-denominator data for
the non-constant branch of `theorem_1`. Together with `MainChoice` and
`MainGCDData` (above), they form the four structural pieces needed for the
final assembly. -/

/-- Correction-slot data: for each `gcd : MainGCDData md`, choose finite
correction denominators `c_ν` with patterns `G_ν` and switch increments
`b_ν := Q_{G_ν}(c_ν)` such that:
  * Each `c_ν > L`, distinct, collision-free with main slots.
  * The integer values `b_ν` cover all residues mod `gcd.g` as subset sums.
  * The reciprocal sum ∑_ν 1/c_ν is small (less than α/2).
  * Each `b_ν > 0`. -/
structure CorrectionData {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) : Type where
  t : ℕ
  G : Fin t → Finset ℕ
  c : Fin t → ℕ
  hG : ∀ ν, IsEgyptianPattern (G ν)
  b : Fin t → ℤ
  hb_def : ∀ ν, b ν =
    intEval (switchingPoly p (G ν))
      (switchingPoly_intValued p hp (G ν)) ((c ν : ℕ) : ℤ)
  hb_pos : ∀ ν, 0 < b ν
  c_gt_L : ∀ ν, L < c ν
  C0_lt :
    (∑ ν : Fin t, (1 : ℚ) / (c ν : ℚ)) <
      α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ))
  residue_cover :
    ∀ r : ZMod gcd.g,
      ∃ T : Finset (Fin t), r = ∑ ν ∈ T, ((b ν : ℤ) : ZMod gcd.g)
  no_corr_collision :
    ∀ ν μ, ν ≠ μ →
      ∀ e ∈ insert 1 (G ν), ∀ e' ∈ insert 1 (G μ),
        e * c ν ≠ e' * c μ
  no_main_collision :
    ∀ ν j, md.J ≤ j →
      ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ), ∀ e ∈ insert 1 (G ν),
        e * c ν ≠ h * D j

/-- Finite residue-generator data extracted from Lemma 6 before choosing the
actual large correction denominators. Duplicating each generator `g - 1` times
already gives subset sums for every residue modulo `g`. -/
structure CorrectionResidueData {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) : Type where
  w : ℕ
  G : Fin w → Finset ℕ
  a : Fin w → ℕ
  b : Fin w → ℤ
  hG : ∀ i, IsEgyptianPattern (G i)
  ha_pos : ∀ i, 1 ≤ a i
  hb_def : ∀ i, b i =
    (∑ e ∈ G i, intEval p hp (((e * a i : ℕ) : ℕ) : ℤ)) -
      intEval p hp ((a i : ℕ) : ℤ)
  residue_cover :
    ∀ r : ZMod gcd.g,
      ∃ T : Finset (Fin w × Fin (gcd.g - 1)),
        r = ∑ σ ∈ T, ((b σ.1 : ℤ) : ZMod gcd.g)

/-- Extract finite switching-value generators and duplicate them enough times
to cover every residue class modulo `g`. This is the residue-combinatorial
front half of the `g ≥ 2` correction-slot constructor. -/
lemma chooseCorrectionResidueData
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : NoFixedDivisor p hp) :
    Nonempty (CorrectionResidueData p hp gcd) := by
  classical
  obtain ⟨w, G, a, b, hG, ha, hb, hgen⟩ :=
    finite_switch_values_generate_zmod p hp h_nonconst h_lead_pos
      h_no_fixed_div gcd.g gcd.hg_pos
  refine ⟨{
    w := w
    G := G
    a := a
    b := b
    hG := hG
    ha_pos := ha
    hb_def := hb
    residue_cover := ?_
  }⟩
  exact duplicated_generators_subset_sum_all_residues gcd.hg_pos
    (fun i : Fin w => ((b i : ℤ) : ZMod gcd.g)) hgen

/-- Trivial CorrectionData when `gcd.g = 1`: take `t := 0` (no correction slots).
All `Fin 0` quantifiers are vacuously true; the residue cover is automatic
because `ZMod 1` is a subsingleton. -/
lemma chooseCorrectionData_g_eq_one
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (hg1 : gcd.g = 1) :
    Nonempty (CorrectionData p hp gcd) := by
  refine ⟨{
    t := 0
    G := Fin.elim0
    c := Fin.elim0
    hG := fun ν => ν.elim0
    b := Fin.elim0
    hb_def := fun ν => ν.elim0
    hb_pos := fun ν => ν.elim0
    c_gt_L := fun ν => ν.elim0
    C0_lt := ?_
    residue_cover := ?_
    no_corr_collision := ?_
    no_main_collision := ?_
  }⟩
  · -- Sum over Fin 0 is 0; positive residual gap from `md.hleft_small`.
    simp
    have h := md.hleft_small
    rw [one_div, mul_inv] at h
    linarith
  · -- ZMod 1: every element is 0; pick T := ∅.
    intro r
    refine ⟨∅, ?_⟩
    have hsub : Subsingleton (ZMod gcd.g) := by
      rw [hg1]; infer_instance
    have hzero : (∑ ν ∈ (∅ : Finset (Fin 0)), ((Fin.elim0 ν : ℤ) : ZMod gcd.g)) = 0 := by
      simp
    rw [hzero]
    exact Subsingleton.elim r 0
  · intro ν _ _ _ _ _ _; exact ν.elim0
  · intro ν _ _ _ _ _ _; exact ν.elim0

lemma exists_correction_slot_congruent
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (Gν : Finset ℕ) (hGν : IsEgyptianPattern Gν)
    (aσ lower : ℕ) (forbiddenFinite : Finset ℕ) :
    ∃ c : ℕ,
      lower < c ∧ L < c ∧
      0 < intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((c : ℕ) : ℤ) ∧
      ((intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((c : ℕ) : ℤ) : ℤ) : ZMod gcd.g) =
        ((intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((aσ : ℕ) : ℤ) : ℤ) : ZMod gcd.g) ∧
      (∀ e ∈ insert 1 Gν, e * c ∉ forbiddenFinite) ∧
      (∀ j, md.J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ insert 1 Gν, e * c ≠ h * D j) := by
  classical
  set Q : ℚ[X] := switchingPoly p Gν with hQ_def
  set hQint : IntValued Q := switchingPoly_intValued p hp Gν with hQint_def
  obtain ⟨B, hBpos, hBint⟩ := exists_integral_multiple Q
  set Tg : ℕ := gcd.g * B with hTg_def
  have hTg : 1 ≤ Tg := by
    rw [hTg_def]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Nat.one_le_iff_ne_zero.mp gcd.hg_pos)
        (Nat.one_le_iff_ne_zero.mp hBpos))
  have hQpos : 0 < (switchingPoly p Gν).leadingCoeff :=
    switchingPoly_leadingCoeff p Gν hGν h_lead_pos h_nonconst
  obtain ⟨c, hc_mod, hc_lower, hc_L, hc_pos, hc_fin, hc_main⟩ :=
    exists_large_correction_denominator p hp Tg aσ md.J L lower Gν hGν hQpos
      forbiddenFinite hTg
  have hxy : ((c : ℕ) : ℤ) ≡ ((aσ : ℕ) : ℤ)
      [ZMOD (((gcd.g * B : ℕ) : ℕ) : ℤ)] := by
    have hnat : c ≡ aσ [MOD gcd.g * B] := by
      simpa [hTg_def] using hc_mod
    exact Int.natCast_modEq_iff.mpr hnat
  have hper := polynomial_periodicity Q hQint B hBpos hBint gcd.g gcd.hg_pos
    ((c : ℕ) : ℤ) ((aσ : ℕ) : ℤ) hxy
  have hres :
      ((intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((c : ℕ) : ℤ) : ℤ) : ZMod gcd.g) =
        ((intEval (switchingPoly p Gν) (switchingPoly_intValued p hp Gν)
            ((aσ : ℕ) : ℤ) : ℤ) : ZMod gcd.g) := by
    exact (ZMod.intCast_eq_intCast_iff _ _ gcd.g).mpr (by
      simpa [Q, hQint, hQ_def, hQint_def] using hper)
  exact ⟨c, hc_lower, hc_L, hc_pos, hres, hc_fin, hc_main⟩

lemma exists_correction_slot_for_generator
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (Gσ : Finset ℕ) (hGσ : IsEgyptianPattern Gσ) (aσ : ℕ) (bσ : ℤ)
    (hbσ : bσ =
      (∑ e ∈ Gσ, intEval p hp (((e * aσ : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((aσ : ℕ) : ℤ))
    (lower : ℕ) (forbiddenFinite : Finset ℕ) :
    ∃ c : ℕ, ∃ b : ℤ,
      b = intEval (switchingPoly p Gσ) (switchingPoly_intValued p hp Gσ)
            ((c : ℕ) : ℤ) ∧
      0 < b ∧ lower < c ∧ L < c ∧
      ((b : ℤ) : ZMod gcd.g) = ((bσ : ℤ) : ZMod gcd.g) ∧
      (∀ e ∈ insert 1 Gσ, e * c ∉ forbiddenFinite) ∧
      (∀ j, md.J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
        ∀ e ∈ insert 1 Gσ, e * c ≠ h * D j) := by
  obtain ⟨c, hc_lower, hc_L, hc_pos, hc_res, hc_fin, hc_main⟩ :=
    exists_correction_slot_congruent p hp gcd h_nonconst h_lead_pos Gσ hGσ
      aσ lower forbiddenFinite
  let b : ℤ := intEval (switchingPoly p Gσ) (switchingPoly_intValued p hp Gσ)
    ((c : ℕ) : ℤ)
  refine ⟨c, b, rfl, hc_pos, hc_lower, hc_L, ?_, hc_fin, hc_main⟩
  have ha_eq :
      intEval (switchingPoly p Gσ) (switchingPoly_intValued p hp Gσ)
        ((aσ : ℕ) : ℤ) = bσ := by
    rw [hbσ]
    exact intEval_switchingPoly_nat p hp Gσ aσ
  simpa [b, ha_eq] using hc_res

/-- Sequentially choose a finite family of correction slots, each avoiding all
previous correction multiples and every main-slot multiple. This is the
collision-avoidance core of the `g ≥ 2` `CorrectionData` constructor. -/
lemma exists_ordered_correction_slots
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (t : ℕ) (G : Fin t → Finset ℕ) (hG : ∀ ν, IsEgyptianPattern (G ν))
    (a : Fin t → ℕ) (b₀ : Fin t → ℤ)
    (hb₀ : ∀ ν, b₀ ν =
      (∑ e ∈ G ν, intEval p hp (((e * a ν : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((a ν : ℕ) : ℤ))
    (lower : ℕ) :
    ∃ c : Fin t → ℕ, ∃ b : Fin t → ℤ,
      (∀ ν, b ν =
        intEval (switchingPoly p (G ν)) (switchingPoly_intValued p hp (G ν))
          ((c ν : ℕ) : ℤ)) ∧
      (∀ ν, 0 < b ν) ∧
      (∀ ν, lower < c ν) ∧
      (∀ ν, L < c ν) ∧
      (∀ ν, ((b ν : ℤ) : ZMod gcd.g) = ((b₀ ν : ℤ) : ZMod gcd.g)) ∧
      (∀ ν μ, ν ≠ μ →
        ∀ e ∈ insert 1 (G ν), ∀ e' ∈ insert 1 (G μ),
          e * c ν ≠ e' * c μ) ∧
      (∀ ν j, md.J ≤ j →
        ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ), ∀ e ∈ insert 1 (G ν),
          e * c ν ≠ h * D j) := by
  classical
  induction t with
  | zero =>
      refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
      · intro ν; exact ν.elim0
  | succ n ih =>
      let G_old : Fin n → Finset ℕ := fun ν => G ν.castSucc
      let a_old : Fin n → ℕ := fun ν => a ν.castSucc
      let b_old_target : Fin n → ℤ := fun ν => b₀ ν.castSucc
      have hG_old : ∀ ν, IsEgyptianPattern (G_old ν) := fun ν => hG ν.castSucc
      have hb_old_target : ∀ ν, b_old_target ν =
          (∑ e ∈ G_old ν, intEval p hp (((e * a_old ν : ℕ) : ℕ) : ℤ)) -
            intEval p hp ((a_old ν : ℕ) : ℤ) := by
        intro ν
        exact hb₀ ν.castSucc
      obtain ⟨c_old, b_old, hb_def_old, hb_pos_old, hc_lower_old, hc_L_old,
        hb_res_old, hcorr_old, hmain_old⟩ :=
        ih G_old hG_old a_old b_old_target hb_old_target
      let forbiddenFinite : Finset ℕ :=
        (Finset.univ : Finset (Fin n)).biUnion fun ν =>
          (insert 1 (G ν.castSucc)).image fun e => e * c_old ν
      obtain ⟨c_last, b_last, hb_last_def, hb_last_pos, hc_last_lower, hc_last_L,
        hb_last_res, hlast_finite, hlast_main⟩ :=
        exists_correction_slot_for_generator p hp gcd h_nonconst h_lead_pos
          (G (Fin.last n)) (hG (Fin.last n)) (a (Fin.last n)) (b₀ (Fin.last n))
          (hb₀ (Fin.last n)) lower forbiddenFinite
      let c : Fin (n + 1) → ℕ := Fin.snoc c_old c_last
      let b : Fin (n + 1) → ℤ := Fin.snoc b_old b_last
      refine ⟨c, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simp [c, b, hb_last_def]
        · simp [c, b, G_old, hb_def_old ν]
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simpa [b] using hb_last_pos
        · simpa [b] using hb_pos_old ν
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simpa [c] using hc_last_lower
        · simpa [c] using hc_lower_old ν
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simpa [c] using hc_last_L
        · simpa [c] using hc_L_old ν
      · intro ν
        refine Fin.lastCases ?_ (fun ν => ?_) ν
        · simpa [b] using hb_last_res
        · simpa [b, b_old_target] using hb_res_old ν
      · intro ν μ
        refine Fin.lastCases ?_ (fun ν' => ?_) ν
        · refine Fin.lastCases ?_ (fun μ' => ?_) μ
          · intro hne e he e' he' h_eq
            exact (hne rfl).elim
          · intro hne e he e' he' h_eq
            simp [c] at h_eq
            have hmem : e' * c_old μ' ∈ forbiddenFinite := by
              dsimp [forbiddenFinite]
              refine Finset.mem_biUnion.mpr ⟨μ', Finset.mem_univ μ', ?_⟩
              exact Finset.mem_image.mpr ⟨e', he', rfl⟩
            exact hlast_finite e he (by rwa [h_eq])
        · refine Fin.lastCases ?_ (fun μ' => ?_) μ
          · intro hne e he e' he' h_eq
            simp [c] at h_eq
            have hmem : e * c_old ν' ∈ forbiddenFinite := by
              dsimp [forbiddenFinite]
              refine Finset.mem_biUnion.mpr ⟨ν', Finset.mem_univ ν', ?_⟩
              exact Finset.mem_image.mpr ⟨e, he, rfl⟩
            exact hlast_finite e' he' (by rwa [← h_eq])
          · intro hne e he e' he' h_eq
            simp [c] at h_eq
            have hne_old : ν' ≠ μ' := by
              intro h
              apply hne
              simp [h]
            exact hcorr_old ν' μ' hne_old e he e' he' h_eq
      · intro ν j hj h hh
        refine Fin.lastCases ?_ (fun ν' => ?_) ν
        · intro e he
          simpa [c] using hlast_main j hj h hh e he
        · intro e he
          simpa [c, G_old] using hmain_old ν' j hj h hh e he

lemma exists_recip_sum_lt_of_large (t : ℕ) {η : ℚ} (hη : 0 < η) :
    ∃ lower : ℕ, ∀ c : Fin t → ℕ,
      (∀ ν, lower < c ν) →
      (∑ ν : Fin t, (1 : ℚ) / (c ν : ℚ)) < η := by
  classical
  let K : ℕ := Nat.ceil ((t : ℚ) / η) + 1
  refine ⟨K, ?_⟩
  intro c hc
  have hK_pos_nat : 0 < K := by
    dsimp [K]
    omega
  have hK_pos : (0 : ℚ) < (K : ℚ) := by exact_mod_cast hK_pos_nat
  have hK_gt : (t : ℚ) / η < (K : ℚ) := by
    have hle : (t : ℚ) / η ≤ (Nat.ceil ((t : ℚ) / η) : ℚ) :=
      Nat.le_ceil _
    have hlt : (Nat.ceil ((t : ℚ) / η) : ℚ) < (K : ℚ) := by
      dsimp [K]
      exact_mod_cast Nat.lt_succ_self (Nat.ceil ((t : ℚ) / η))
    exact lt_of_le_of_lt hle hlt
  have ht_div_K_lt : (t : ℚ) / (K : ℚ) < η := by
    have ht_lt : (t : ℚ) < (K : ℚ) * η := (div_lt_iff₀ hη).mp hK_gt
    rw [div_lt_iff₀ hK_pos]
    nlinarith [ht_lt]
  have hsum_le :
      (∑ ν : Fin t, (1 : ℚ) / (c ν : ℚ)) ≤
        ∑ _ν : Fin t, (1 : ℚ) / (K : ℚ) := by
    apply Finset.sum_le_sum
    intro ν _
    have hK_le_c_nat : K ≤ c ν := le_of_lt (hc ν)
    have hK_le_c : (K : ℚ) ≤ (c ν : ℚ) := by exact_mod_cast hK_le_c_nat
    exact one_div_le_one_div_of_le hK_pos hK_le_c
  have hconst :
      (∑ _ν : Fin t, (1 : ℚ) / (K : ℚ)) = (t : ℚ) / (K : ℚ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  exact lt_of_le_of_lt (by simpa [hconst] using hsum_le) ht_div_K_lt

lemma chooseCorrectionData_g_ge_two
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : NoFixedDivisor p hp) (_hg2 : 2 ≤ gcd.g) :
    Nonempty (CorrectionData p hp gcd) := by
  classical
  obtain ⟨rd⟩ :=
    chooseCorrectionResidueData p hp gcd h_nonconst h_lead_pos h_no_fixed_div
  let ι : Type := Fin rd.w × Fin (gcd.g - 1)
  let t : ℕ := Fintype.card ι
  let enc : ι ≃ Fin t := Fintype.equivFin ι
  let dec : Fin t → ι := enc.symm
  let G : Fin t → Finset ℕ := fun ν => rd.G ((dec ν).1)
  let a : Fin t → ℕ := fun ν => rd.a ((dec ν).1)
  let b₀ : Fin t → ℤ := fun ν => rd.b ((dec ν).1)
  have hG : ∀ ν, IsEgyptianPattern (G ν) := by
    intro ν
    exact rd.hG ((dec ν).1)
  have hb₀ : ∀ ν, b₀ ν =
      (∑ e ∈ G ν, intEval p hp (((e * a ν : ℕ) : ℕ) : ℤ)) -
        intEval p hp ((a ν : ℕ) : ℤ) := by
    intro ν
    exact rd.hb_def ((dec ν).1)
  set η : ℚ := α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    linarith [md.hleft_small]
  obtain ⟨lower, hlower⟩ := exists_recip_sum_lt_of_large t hη_pos
  obtain ⟨c, b, hb_def, hb_pos, hc_lower, hc_L, hb_res, hcorr, hmain⟩ :=
    exists_ordered_correction_slots p hp gcd h_nonconst h_lead_pos
      t G hG a b₀ hb₀ lower
  refine ⟨{
    t := t
    G := G
    c := c
    hG := hG
    b := b
    hb_def := hb_def
    hb_pos := hb_pos
    c_gt_L := hc_L
    C0_lt := ?_
    residue_cover := ?_
    no_corr_collision := hcorr
    no_main_collision := hmain
  }⟩
  · rw [hη_def] at hlower
    exact hlower c hc_lower
  · intro r
    obtain ⟨T, hT⟩ := rd.residue_cover r
    refine ⟨T.image enc, ?_⟩
    rw [Finset.sum_image]
    · rw [hT]
      apply Finset.sum_congr rfl
      intro σ _
      have hres := hb_res (enc σ)
      simpa [b₀, dec, enc] using hres.symm
    · intro σ _ τ _ hστ
      exact enc.injective hστ

/-- Filler-denominator data: a finite set `F` of natural numbers and a scaling
factor `Λ` (with `8 ∣ Λ`, `Λ > L`, `Λ` larger than all correction denominators)
such that `∑_{f ∈ F} 1/(Λ f) = R₀` for the residual reciprocal mass
`R₀ := α - 1/(P u_J) - C₀`. -/
structure FillerData {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) : Type where
  Λ : ℕ
  hΛ_div_8 : 8 ∣ Λ
  hΛ_gt_L : L < Λ
  hΛ_gt_corr : ∀ ν : Fin corr.t, corr.c ν < Λ
  F : Finset ℕ
  hF_pos : ∀ f ∈ F, 1 ≤ f
  hF_distinct_from_main_corr :
    -- Each Λ * f differs from any main slot multiple or correction-slot multiple
    (∀ f ∈ F, ∀ j, md.J ≤ j → ∀ h ∈ ({1, 2, 3, 6} : Finset ℕ),
      Λ * f ≠ h * D j) ∧
    (∀ f ∈ F, ∀ ν : Fin corr.t, ∀ e ∈ insert 1 (corr.G ν),
      Λ * f ≠ e * corr.c ν)
  hF_recip :
    (∑ f ∈ F, (1 : ℚ) / ((Λ * f : ℕ) : ℚ)) =
      α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) -
      (∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ))

/-- Constructor for FillerData via `egyptian_expansion`. The construction:
choose `Λ` large enough (multiple of 8, exceeding `L` and all `c_ν`, plus
collision-avoidance margins). Then apply `egyptian_expansion` to the residual
mass `Λ * R₀` to get an Egyptian set of denominators of the form `Λ * f`. -/
lemma chooseFillerData
    {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) :
    Nonempty (FillerData p hp corr) := by
  -- Step 1: Compute residual mass R₀ in ℚ.
  set R0 : ℚ := α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) -
    (∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ)) with hR0_def
  -- R₀ > 0 from corr.C0_lt.
  have hR0_pos : 0 < R0 := by rw [hR0_def]; linarith [corr.C0_lt]
  -- Step 2: Pick Λ as a multiple of 8 large enough.
  -- We need: 8 ∣ Λ, Λ > L, and Λ larger than every correction denominator
  -- after every possible pattern multiplier.
  set corrMax : ℕ := (Finset.univ : Finset (Fin corr.t)).sup
    (fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν)) with hcorrMax_def
  set Λ : ℕ := 8 * (L + corrMax + 2) with hΛ_def
  have hΛ_div_8 : 8 ∣ Λ := by rw [hΛ_def]; exact ⟨_, rfl⟩
  have hΛ_pos : 1 ≤ Λ := by rw [hΛ_def]; omega
  have hΛ_gt_L : L < Λ := by rw [hΛ_def]; omega
  have hΛ_gt_corr : ∀ ν : Fin corr.t, corr.c ν < Λ := by
    intro ν
    have h_inner : corr.c ν ≤ (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) := by
      have h := Finset.le_sup (f := fun e => e * corr.c ν)
        (Finset.mem_insert_self 1 (corr.G ν))
      simp only [one_mul] at h; exact h
    have h_outer : (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) ≤ corrMax := by
      rw [hcorrMax_def]
      exact Finset.le_sup (f := fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν))
        (Finset.mem_univ ν)
    have h_le : corr.c ν ≤ corrMax := le_trans h_inner h_outer
    rw [hΛ_def]; omega
  -- Step 3: Apply egyptian_expansion to R₀ at threshold 0.
  -- We get K : ℕ such that for all k ≥ K, ∃ E with |E| = k, ∀ e ∈ E, 0 < e,
  -- and R₀ = ∑ 1/e.
  obtain ⟨K, hK⟩ := egyptian_expansion R0 hR0_pos 0
  obtain ⟨E_full, _hE_card, hE_lb, hE_sum⟩ := hK K (le_refl K)
  -- Each e ∈ E_full satisfies 0 < e ⇒ e ≥ 1.
  have hE_pos : ∀ e ∈ E_full, 1 ≤ e := fun e he => Nat.one_le_iff_ne_zero.mpr
    (fun h0 => by have := hE_lb e he; omega)
  -- Step 4: Define F such that for each e ∈ E_full, the denominator is Λ * f
  -- where f := e (just rename). But we need 1/(Λ*f) = R₀, which would require
  -- Λ * f = e for ∑ 1/e. We don't have that directly. Instead:
  -- ∑ 1/e = R₀ ⇒ Λ * ∑ 1/e = Λ * R₀, but we need ∑ 1/(Λ*f) = R₀.
  -- This requires f := e/Λ, i.e., Λ ∣ e.
  -- So we instead apply egyptian_expansion to R₀ with denominators ≥ Λ,
  -- then set f := e/Λ. But the reciprocal sum identity wants
  -- ∑ 1/(Λ*f) = R₀ ⇒ (1/Λ) ∑ 1/f = R₀, so ∑ 1/f = Λ R₀.
  -- Apply egyptian_expansion to (Λ R₀) instead, with threshold 0:
  obtain ⟨K', hK'⟩ := egyptian_expansion ((Λ : ℚ) * R0)
    (by have hΛ_q : (0 : ℚ) < (Λ : ℚ) := by exact_mod_cast hΛ_pos
        exact mul_pos hΛ_q hR0_pos) 0
  obtain ⟨F0, _hF0_card, hF0_lb, hF0_sum⟩ := hK' K' (le_refl K')
  have hF0_pos : ∀ f ∈ F0, 1 ≤ f := fun f hf => Nat.one_le_iff_ne_zero.mpr
    (fun h0 => by have := hF0_lb f hf; omega)
  -- Now F := F0; verify ∑_{f ∈ F0} 1/(Λ*f) = R₀.
  have hΛ_q_ne : (Λ : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (Λ : ℚ) := by exact_mod_cast hΛ_pos
    exact ne_of_gt this
  have h_recip : (∑ f ∈ F0, (1 : ℚ) / ((Λ * f : ℕ) : ℚ)) = R0 := by
    have h1 : (∑ f ∈ F0, (1 : ℚ) / ((Λ * f : ℕ) : ℚ)) =
        (1 / (Λ : ℚ)) * ∑ f ∈ F0, (1 : ℚ) / (f : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      have hf_pos := hF0_pos f hf
      have hf_q_ne : (f : ℚ) ≠ 0 := by
        have : (0 : ℚ) < (f : ℚ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hf_pos)
        exact ne_of_gt this
      push_cast
      field_simp
    rw [h1, ← hF0_sum]
    field_simp
  refine ⟨{
    Λ := Λ
    hΛ_div_8 := hΛ_div_8
    hΛ_gt_L := hΛ_gt_L
    hΛ_gt_corr := hΛ_gt_corr
    F := F0
    hF_pos := hF0_pos
    hF_distinct_from_main_corr := ?_
    hF_recip := h_recip
  }⟩
  refine ⟨?_, ?_⟩
  · -- Filler denominators have `v₂ ≥ 3`, while main-slot denominators have
    -- `v₂ ∈ {0, 1}`.
    intro f hf j _ h hh h_eq
    have hf_pos := hF0_pos f hf
    have hfill_v2 : 3 ≤ padicValNat 2 (Λ * f) :=
      filler_v2_at_least_three Λ f hΛ_div_8 hΛ_pos hf_pos
    obtain ⟨hv1, hv2, hv3, hv6⟩ := main_valuation_profile j
    have hmain_v2 : padicValNat 2 (h * D j) ≤ 1 := by
      rw [show ({1, 2, 3, 6} : Finset ℕ) =
        insert 1 (insert 2 (insert 3 ({6} : Finset ℕ))) from rfl] at hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · rw [one_mul]
        have hv : padicValNat 2 (D j) = 0 := by
          have := congrArg Prod.fst hv1
          simpa using this
        rw [hv]
        norm_num
      · rcases Finset.mem_insert.mp hh with rfl | hh
        · have hv : padicValNat 2 (2 * D j) = 1 := by
            have := congrArg Prod.fst hv2
            simpa using this
          rw [hv]
        · rcases Finset.mem_insert.mp hh with rfl | hh
          · have hv : padicValNat 2 (3 * D j) = 0 := by
              have := congrArg Prod.fst hv3
              simpa using this
            rw [hv]
            norm_num
          · have h6 : h = 6 := by simpa using hh
            subst h
            have hv : padicValNat 2 (6 * D j) = 1 := by
              have := congrArg Prod.fst hv6
              simpa using this
            rw [hv]
    have hmain_v2_eq : padicValNat 2 (Λ * f) = padicValNat 2 (h * D j) := by
      rw [h_eq]
    omega
  · -- `Λ` is larger than every correction multiple `e * cν`, while
    -- `Λ * f ≥ Λ` because all filler factors are positive.
    intro f hf ν e he h_eq
    have hf_pos := hF0_pos f hf
    have hΛ_le : Λ ≤ Λ * f := by
      calc Λ = Λ * 1 := by ring
        _ ≤ Λ * f := Nat.mul_le_mul_left Λ hf_pos
    have h_inner : e * corr.c ν ≤
        (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) :=
      Finset.le_sup (f := fun e => e * corr.c ν) he
    have h_outer :
        (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) ≤ corrMax := by
      rw [hcorrMax_def]
      exact Finset.le_sup (f := fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν))
        (Finset.mem_univ ν)
    have hec_le : e * corr.c ν ≤ corrMax := le_trans h_inner h_outer
    have hcorr_lt : corrMax < Λ := by rw [hΛ_def]; omega
    have : Λ * f < Λ := by
      rw [h_eq]
      exact lt_of_le_of_lt hec_le hcorr_lt
    exact (not_lt_of_ge hΛ_le) this

/-! ### Bookkeeping for the final interval assembly -/

/-- `B_*`: the total correction increment obtained by switching every
correction slot. This is the harmless finite offset in the lower edge of the
attainable interval. -/
noncomputable def Bstar {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) : ℤ :=
  ∑ ν : Fin corr.t, corr.b ν

lemma Bstar_nonneg {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) :
    0 ≤ Bstar p hp corr := by
  unfold Bstar
  exact Finset.sum_nonneg (fun ν _ => (corr.hb_pos ν).le)

/-- Use the correction-slot subset-sum cover to choose a subset whose increment
puts an arbitrary integer `z` into the `g`-divisible residue class. -/
lemma correction_subset_dvd {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (z : ℤ) :
    ∃ T : Finset (Fin corr.t),
      (gcd.g : ℤ) ∣ z - ∑ ν ∈ T, corr.b ν := by
  classical
  obtain ⟨T, hT⟩ := corr.residue_cover (z : ZMod gcd.g)
  refine ⟨T, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hT]
  simp

lemma correction_subset_sum_nonneg {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t)) :
    0 ≤ ∑ ν ∈ T, corr.b ν := by
  exact Finset.sum_nonneg (fun ν _ => (corr.hb_pos ν).le)

lemma correction_subset_sum_le_Bstar {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t)) :
    (∑ ν ∈ T, corr.b ν) ≤ Bstar p hp corr := by
  unfold Bstar
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun ν _ _ => (corr.hb_pos ν).le)

lemma correction_subset_dvd_with_bounds {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd) (z : ℤ) :
    ∃ T : Finset (Fin corr.t),
      (gcd.g : ℤ) ∣ z - ∑ ν ∈ T, corr.b ν ∧
      0 ≤ ∑ ν ∈ T, corr.b ν ∧
      (∑ ν ∈ T, corr.b ν) ≤ Bstar p hp corr := by
  obtain ⟨T, hT⟩ := correction_subset_dvd p hp corr z
  exact ⟨T, hT, correction_subset_sum_nonneg p hp corr T,
    correction_subset_sum_le_Bstar p hp corr T⟩

/-- `M₀ := max 0 (g · X_q)`, the nonnegative RSG lower offset measured in the
undivided main-slot scale. -/
def M0 {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) (X_q : ℤ) : ℤ :=
  max 0 ((gcd.g : ℤ) * X_q)

lemma M0_nonneg {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) (X_q : ℤ) :
    0 ≤ M0 p hp gcd X_q := by
  unfold M0
  exact le_max_left _ _

lemma M0_ge_g_mul_Xq {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md) (X_q : ℤ) :
    ((gcd.g : ℤ) * X_q) ≤ M0 p hp gcd X_q := by
  unfold M0
  exact le_max_right _ _

/-- The base integer p-sum `B_N`, before any main or correction switch:
main denominators `D j`, endpoint `τ_N`, all correction denominators, and all
filler denominators. -/
noncomputable def baseInt {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr) (N : ℕ) : ℤ :=
  (∑ j ∈ Finset.Icc md.J N, intEval p hp ((D j : ℕ) : ℤ)) +
  intEval p hp ((tau N : ℕ) : ℤ) +
  (∑ ν : Fin corr.t, intEval p hp ((corr.c ν : ℕ) : ℤ)) +
  (∑ f ∈ fill.F, intEval p hp (((fill.Λ * f : ℕ) : ℤ)))

lemma baseInt_succ_eq {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} (hJN : md.J ≤ N + 1) :
    baseInt p hp corr fill (N + 1) =
      baseInt p hp corr fill N +
        intEval p hp ((D (N + 1) : ℕ) : ℤ) +
        intEval p hp ((tau (N + 1) : ℕ) : ℤ) -
        intEval p hp ((tau N : ℕ) : ℤ) := by
  unfold baseInt
  rw [Finset.sum_Icc_succ_top hJN]
  ring

noncomputable def upperInt (p : ℚ[X]) (N : ℕ) : ℤ :=
  ⌊(muConst p) * (N : ℚ) ^ (2 * p.natDegree)⌋

noncomputable def lowerInt {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (X_q : ℤ) (N : ℕ) : ℤ :=
  baseInt p hp corr fill N + Bstar p hp corr + M0 p hp gcd X_q

noncomputable def upperEdge {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N : ℕ) : ℤ :=
  baseInt p hp corr fill N + upperInt p N

noncomputable def tauPoly : ℚ[X] :=
  Polynomial.C ((P : ℚ) ^ 2) * Polynomial.X +
    Polynomial.C ((P : ℚ) * ((P : ℚ) + 1))

noncomputable def tauNextPoly : ℚ[X] :=
  Polynomial.C ((P : ℚ) ^ 2) * Polynomial.X +
    Polynomial.C ((P : ℚ) * (2 * (P : ℚ) + 1))

noncomputable def baseStepPoly (p : ℚ[X]) : ℚ[X] :=
  p.comp (Dpoly 2) + (p.comp tauNextPoly - p.comp tauPoly)

lemma tauPoly_eval_nat (N : ℕ) :
    tauPoly.eval (N : ℚ) = (tau N : ℚ) := by
  norm_num [tauPoly, tau, u, P]
  ring

lemma tauNextPoly_eval_nat (N : ℕ) :
    tauNextPoly.eval (N : ℚ) = (tau (N + 1) : ℚ) := by
  norm_num [tauNextPoly, tau, u, P]
  ring

lemma tauPoly_natDegree : tauPoly.natDegree = 1 := by
  unfold tauPoly
  exact Polynomial.natDegree_linear (by unfold P; norm_num : ((P : ℚ) ^ 2) ≠ 0)

lemma tauNextPoly_natDegree : tauNextPoly.natDegree = 1 := by
  unfold tauNextPoly
  exact Polynomial.natDegree_linear (by unfold P; norm_num : ((P : ℚ) ^ 2) ≠ 0)

lemma Dpoly_two_eval_nat {N : ℕ} (hN : 1 ≤ N) :
    (Dpoly 2).eval (N : ℚ) = (D (N + 1) : ℚ) := by
  rw [Dpoly_eval_at_succ 2 N hN]
  have hidx : 2 + N - 1 = N + 1 := by omega
  rw [hidx]

lemma baseStepPoly_eval_nat (p : ℚ[X]) (hp : IntValued p)
    {N : ℕ} (hN : 1 ≤ N) :
    (baseStepPoly p).eval (N : ℚ) =
      ((intEval p hp ((D (N + 1) : ℕ) : ℤ) : ℤ) : ℚ) +
      ((intEval p hp ((tau (N + 1) : ℕ) : ℤ) : ℤ) : ℚ) -
      ((intEval p hp ((tau N : ℕ) : ℤ) : ℤ) : ℚ) := by
  unfold baseStepPoly
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_comp]
  rw [Dpoly_two_eval_nat hN, tauNextPoly_eval_nat, tauPoly_eval_nat]
  rw [intEval_spec p hp ((D (N + 1) : ℕ) : ℤ)]
  rw [intEval_spec p hp ((tau (N + 1) : ℕ) : ℤ)]
  rw [intEval_spec p hp ((tau N : ℕ) : ℤ)]
  push_cast
  ring

lemma p_comp_Dpoly_two_natDegree (p : ℚ[X]) :
    (p.comp (Dpoly 2)).natDegree = 2 * p.natDegree := by
  rw [Polynomial.natDegree_comp, Dpoly_natDegree]
  ring

lemma p_comp_Dpoly_two_leadingCoeff (p : ℚ[X])
    (_h_lead_pos : 0 < p.leadingCoeff) :
    (p.comp (Dpoly 2)).leadingCoeff = lambdaConst p := by
  unfold lambdaConst
  rw [Polynomial.leadingCoeff_comp ?_, Dpoly_leadingCoeff]
  · rw [← pow_mul]
  · rw [Dpoly_natDegree]
    norm_num

lemma p_comp_tauPoly_natDegree_le (p : ℚ[X]) :
    (p.comp tauPoly).natDegree ≤ p.natDegree := by
  have h := Polynomial.natDegree_comp_le (p := p) (q := tauPoly)
  rw [tauPoly_natDegree] at h
  simpa using h

lemma p_comp_tauNextPoly_natDegree_le (p : ℚ[X]) :
    (p.comp tauNextPoly).natDegree ≤ p.natDegree := by
  have h := Polynomial.natDegree_comp_le (p := p) (q := tauNextPoly)
  rw [tauNextPoly_natDegree] at h
  simpa using h

lemma baseStepPoly_natDegree_eq (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) :
    (baseStepPoly p).natDegree = 2 * p.natDegree := by
  unfold baseStepPoly
  have hD : (p.comp (Dpoly 2)).natDegree = 2 * p.natDegree :=
    p_comp_Dpoly_two_natDegree p
  have hQle :
      (p.comp tauNextPoly - p.comp tauPoly).natDegree ≤ p.natDegree := by
    exact le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le (p_comp_tauNextPoly_natDegree_le p) (p_comp_tauPoly_natDegree_le p))
  have hQlt :
      (p.comp tauNextPoly - p.comp tauPoly).natDegree <
        (p.comp (Dpoly 2)).natDegree := by
    rw [hD]
    omega
  exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hQlt).trans hD

lemma baseStepPoly_leadingCoeff_eq (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (baseStepPoly p).leadingCoeff = lambdaConst p := by
  unfold baseStepPoly
  have hD : (p.comp (Dpoly 2)).natDegree = 2 * p.natDegree :=
    p_comp_Dpoly_two_natDegree p
  have hQle :
      (p.comp tauNextPoly - p.comp tauPoly).natDegree ≤ p.natDegree := by
    exact le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le (p_comp_tauNextPoly_natDegree_le p) (p_comp_tauPoly_natDegree_le p))
  have hQlt_nat :
      (p.comp tauNextPoly - p.comp tauPoly).natDegree <
        (p.comp (Dpoly 2)).natDegree := by
    rw [hD]
    omega
  have hQlt_deg :
      (p.comp tauNextPoly - p.comp tauPoly).degree <
        (p.comp (Dpoly 2)).degree :=
    Polynomial.degree_lt_degree hQlt_nat
  rw [Polynomial.leadingCoeff_add_of_degree_lt' hQlt_deg]
  exact p_comp_Dpoly_two_leadingCoeff p h_lead_pos

/-- If the leading coefficient of a rational polynomial is strictly below `c`,
then eventually its values are below `c N^d`, provided its natural degree is
exactly `d > 0`. -/
lemma polynomial_eventually_le_const_mul_pow (R : ℚ[X]) {d : ℕ} {c : ℚ}
    (hd_pos : 0 < d) (hdeg : R.natDegree = d)
    (hlead : R.leadingCoeff < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      R.eval (N : ℚ) ≤ c * (N : ℚ) ^ d := by
  classical
  let Xd : ℚ[X] := Polynomial.X ^ d
  have hR_ne : R ≠ 0 := by
    intro hR
    rw [hR, Polynomial.natDegree_zero] at hdeg
    omega
  have hdeg_degree : R.degree = Xd.degree := by
    rw [Polynomial.degree_eq_natDegree hR_ne, hdeg]
    dsimp [Xd]
    rw [Polynomial.degree_X_pow]
  have ht :
      Tendsto (fun x : ℚ => R.eval x / Xd.eval x) atTop
        (nhds (R.leadingCoeff / Xd.leadingCoeff)) :=
    Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq R Xd hdeg_degree
  have hlead_ratio : R.leadingCoeff / Xd.leadingCoeff = R.leadingCoeff := by
    dsimp [Xd]
    rw [Polynomial.leadingCoeff_X_pow]
    simp
  rw [hlead_ratio] at ht
  have ht_nat :
      Tendsto (fun N : ℕ => R.eval (N : ℚ) / Xd.eval (N : ℚ)) atTop
        (nhds R.leadingCoeff) :=
    ht.comp tendsto_natCast_atTop_atTop
  have hevent :
      ∀ᶠ N : ℕ in atTop,
        R.eval (N : ℚ) / Xd.eval (N : ℚ) < c :=
    ht_nat.eventually (eventually_lt_nhds hlead)
  rw [eventually_atTop] at hevent
  obtain ⟨N₁, hN₁⟩ := hevent
  refine ⟨max N₁ 1, ?_⟩
  intro N hN
  have hN₁N : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have h1N : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hratio := hN₁ N hN₁N
  have hXd_eval : Xd.eval (N : ℚ) = (N : ℚ) ^ d := by
    simp [Xd]
  have hNq_pos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast h1N
  have hden_pos : 0 < Xd.eval (N : ℚ) := by
    rw [hXd_eval]
    exact pow_pos hNq_pos d
  have hlt : R.eval (N : ℚ) < c * Xd.eval (N : ℚ) :=
    (div_lt_iff₀ hden_pos).mp hratio
  rw [hXd_eval] at hlt
  exact le_of_lt hlt

/-- Lower-bound companion to `polynomial_eventually_le_const_mul_pow`. -/
lemma const_mul_pow_eventually_le_polynomial (R : ℚ[X]) {d : ℕ} {c : ℚ}
    (hd_pos : 0 < d) (hdeg : R.natDegree = d)
    (hc_lt_lead : c < R.leadingCoeff) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℚ) ^ d ≤ R.eval (N : ℚ) := by
  have hneg_deg : (-R).natDegree = d := by
    rw [Polynomial.natDegree_neg, hdeg]
  have hneg_lead : (-R).leadingCoeff < -c := by
    rw [Polynomial.leadingCoeff_neg]
    linarith
  obtain ⟨N₀, hN₀⟩ :=
    polynomial_eventually_le_const_mul_pow (-R) hd_pos hneg_deg hneg_lead
  refine ⟨N₀, ?_⟩
  intro N hN
  have h := hN₀ N hN
  rw [Polynomial.eval_neg] at h
  linarith

/-- Since `(N - J + 1) / N → 1`, any strict coefficient gap `β < c`
eventually gives `β N^d < c (N - J + 1)^d`. -/
lemma shifted_power_eventually_mul_lt (J d : ℕ) {β c : ℚ}
    (_hd_pos : 0 < d) (hβ_pos : 0 < β) (hβc : β < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      β * (N : ℚ) ^ d < c * ((N - J + 1 : ℕ) : ℚ) ^ d := by
  classical
  let A : ℚ[X] := (Polynomial.X - Polynomial.C ((J : ℚ) - 1)) ^ d
  let Xd : ℚ[X] := Polynomial.X ^ d
  have hc_pos : 0 < c := lt_trans hβ_pos hβc
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hA_monic : A.Monic := by
    dsimp [A]
    exact (Polynomial.monic_X_sub_C ((J : ℚ) - 1)).pow d
  have hA_natDegree : A.natDegree = d := by
    dsimp [A]
    rw [(Polynomial.monic_X_sub_C ((J : ℚ) - 1)).natDegree_pow,
      Polynomial.natDegree_X_sub_C]
    ring
  have hdeg_degree : A.degree = Xd.degree := by
    rw [Polynomial.degree_eq_natDegree hA_monic.ne_zero, hA_natDegree]
    dsimp [Xd]
    rw [Polynomial.degree_X_pow]
  have ht :
      Tendsto (fun x : ℚ => A.eval x / Xd.eval x) atTop
        (nhds (A.leadingCoeff / Xd.leadingCoeff)) :=
    Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq A Xd hdeg_degree
  have hlead_ratio : A.leadingCoeff / Xd.leadingCoeff = 1 := by
    have hA_lc : A.leadingCoeff = 1 := hA_monic.leadingCoeff
    dsimp [Xd]
    rw [hA_lc, Polynomial.leadingCoeff_X_pow]
    simp
  rw [hlead_ratio] at ht
  have ht_nat :
      Tendsto (fun N : ℕ => A.eval (N : ℚ) / Xd.eval (N : ℚ)) atTop
        (nhds (1 : ℚ)) :=
    ht.comp tendsto_natCast_atTop_atTop
  have hβ_div_c_lt_one : β / c < 1 := by
    rw [div_lt_one₀ hc_pos]
    exact hβc
  have hevent :
      ∀ᶠ N : ℕ in atTop,
        β / c < A.eval (N : ℚ) / Xd.eval (N : ℚ) :=
    ht_nat.eventually (eventually_gt_nhds hβ_div_c_lt_one)
  rw [eventually_atTop] at hevent
  obtain ⟨N₁, hN₁⟩ := hevent
  refine ⟨max (max N₁ 1) J, ?_⟩
  intro N hN
  have hN₁N : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have h1N : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hJN : J ≤ N := le_trans (le_max_right _ _) hN
  have hratio := hN₁ N hN₁N
  have hXd_eval : Xd.eval (N : ℚ) = (N : ℚ) ^ d := by
    simp [Xd]
  have hA_eval : A.eval (N : ℚ) = ((N - J + 1 : ℕ) : ℚ) ^ d := by
    dsimp [A]
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have harg : (N : ℚ) - ((J : ℚ) - 1) = ((N - J + 1 : ℕ) : ℚ) := by
      have harg_int :
          (N : ℤ) - ((J : ℤ) - 1) = ((N - J + 1 : ℕ) : ℤ) := by
        omega
      exact_mod_cast harg_int
    rw [harg]
  have hNq_pos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast h1N
  have hden_pos : 0 < Xd.eval (N : ℚ) := by
    rw [hXd_eval]
    exact pow_pos hNq_pos d
  rw [lt_div_iff₀ hden_pos] at hratio
  have hmul := mul_lt_mul_of_pos_left hratio hc_pos
  have hleft :
      c * ((β / c) * Xd.eval (N : ℚ)) =
        β * Xd.eval (N : ℚ) := by
    field_simp [hc_ne]
  rw [hleft, hXd_eval, hA_eval] at hmul
  exact hmul

lemma baseStepPoly_add_const_natDegree_eq (p : ℚ[X]) (C : ℤ)
    (h_nonconst : 1 ≤ p.natDegree) :
    (baseStepPoly p + Polynomial.C (C : ℚ)).natDegree =
      2 * p.natDegree := by
  have hbase : (baseStepPoly p).natDegree = 2 * p.natDegree :=
    baseStepPoly_natDegree_eq p h_nonconst
  have hconst_lt :
      (Polynomial.C (C : ℚ)).natDegree < (baseStepPoly p).natDegree := by
    rw [hbase]
    simp
    omega
  exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hconst_lt).trans hbase

lemma baseStepPoly_add_const_leadingCoeff_eq (p : ℚ[X]) (C : ℤ)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    (baseStepPoly p + Polynomial.C (C : ℚ)).leadingCoeff =
      lambdaConst p := by
  have hbase : (baseStepPoly p).natDegree = 2 * p.natDegree :=
    baseStepPoly_natDegree_eq p h_nonconst
  have hconst_lt_nat :
      (Polynomial.C (C : ℚ)).natDegree < (baseStepPoly p).natDegree := by
    rw [hbase]
    simp
    omega
  have hconst_lt_deg :
      (Polynomial.C (C : ℚ)).degree < (baseStepPoly p).degree :=
    Polynomial.degree_lt_degree hconst_lt_nat
  rw [Polynomial.leadingCoeff_add_of_degree_lt' hconst_lt_deg]
  exact baseStepPoly_leadingCoeff_eq p h_nonconst h_lead_pos

lemma baseStep_eventually_le_upperInt {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (X_q : ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      intEval p hp ((D (N + 1) : ℕ) : ℤ) +
          intEval p hp ((tau (N + 1) : ℕ) : ℤ) -
          intEval p hp ((tau N : ℕ) : ℤ) +
          (Bstar p hp corr + M0 p hp gcd X_q) ≤ upperInt p N := by
  let C : ℤ := Bstar p hp corr + M0 p hp gcd X_q
  let R : ℚ[X] := baseStepPoly p + Polynomial.C (C : ℚ)
  have hd_pos : 0 < 2 * p.natDegree := by omega
  have hRdeg : R.natDegree = 2 * p.natDegree := by
    dsimp [R]
    exact baseStepPoly_add_const_natDegree_eq p C h_nonconst
  have hRlead : R.leadingCoeff < muConst p := by
    dsimp [R]
    rw [baseStepPoly_add_const_leadingCoeff_eq p C h_nonconst h_lead_pos]
    exact lambdaConst_lt_muConst p h_nonconst h_lead_pos
  obtain ⟨N₀, hN₀⟩ :=
    polynomial_eventually_le_const_mul_pow R hd_pos hRdeg hRlead
  refine ⟨max N₀ 1, ?_⟩
  intro N hN
  have hN₀N : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN_pos : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hpoly := hN₀ N hN₀N
  have hR_eval :
      R.eval (N : ℚ) =
        ((intEval p hp ((D (N + 1) : ℕ) : ℤ) +
          intEval p hp ((tau (N + 1) : ℕ) : ℤ) -
          intEval p hp ((tau N : ℕ) : ℤ) + C : ℤ) : ℚ) := by
    dsimp [R, C]
    rw [Polynomial.eval_add, Polynomial.eval_C, baseStepPoly_eval_nat p hp hN_pos]
    push_cast
    ring
  unfold upperInt
  exact Int.le_floor.mpr (by
    rw [← hR_eval]
    exact hpoly)

lemma intervals_overlap_eventually {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (X_q : ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      lowerInt p hp corr fill X_q (N + 1) ≤
        upperEdge p hp corr fill N + 1 := by
  obtain ⟨Ns, hNs⟩ :=
    baseStep_eventually_le_upperInt p hp h_nonconst h_lead_pos corr X_q
  refine ⟨max Ns md.J, ?_⟩
  intro N hN
  have hNsN : Ns ≤ N := le_trans (le_max_left _ _) hN
  have hJN : md.J ≤ N + 1 := by
    have : md.J ≤ N := le_trans (le_max_right _ _) hN
    omega
  have hstep := hNs N hNsN
  rw [lowerInt, upperEdge, baseInt_succ_eq p hp corr fill hJN]
  linarith

lemma qPoly_tail_eventually {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (X_q : ℤ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ upperInt p N →
        ∀ i : ℕ, N - md.J < i →
          (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ) := by
  classical
  let q : ℚ[X] := qPoly p md.J gcd.g
  let d : ℕ := 2 * p.natDegree
  let beta : ℚ := muConst p / (gcd.g : ℚ)
  have hd_pos : 0 < d := by
    dsimp [d]
    omega
  have hgq_pos : (0 : ℚ) < (gcd.g : ℚ) := by exact_mod_cast gcd.hg_pos
  have hbeta_pos : 0 < beta := by
    dsimp [beta]
    exact div_pos (muConst_pos p h_nonconst h_lead_pos) hgq_pos
  have hqdeg : q.natDegree = d := by
    dsimp [q, d]
    exact qPoly_natDegree p md.J gcd.g gcd.hg_pos h_nonconst h_lead_pos
  have hbeta_lt_qlead : beta < q.leadingCoeff := by
    dsimp [beta, q]
    rw [qPoly_leadingCoeff p md.J gcd.g gcd.hg_pos h_nonconst h_lead_pos]
    exact div_lt_div_of_pos_right
      (muConst_lt_a_theta_P p h_nonconst h_lead_pos) hgq_pos
  let c : ℚ := (beta + q.leadingCoeff) / 2
  have hbeta_lt_c : beta < c := by
    dsimp [c]
    linarith
  have hc_lt_qlead : c < q.leadingCoeff := by
    dsimp [c]
    linarith
  have hc_pos : 0 < c := lt_trans hbeta_pos hbeta_lt_c
  obtain ⟨Nq, hNq⟩ :=
    const_mul_pow_eventually_le_polynomial q hd_pos hqdeg hc_lt_qlead
  obtain ⟨Ns, hNs⟩ :=
    shifted_power_eventually_mul_lt md.J d hd_pos hbeta_pos hbeta_lt_c
  refine ⟨max Ns (Nq + md.J), ?_⟩
  intro N hN X _hX_ge hXU i hi
  have hNsN : Ns ≤ N := le_trans (le_max_left _ _) hN
  have hNqJ : Nq + md.J ≤ N := le_trans (le_max_right _ _) hN
  have hNq_base : Nq ≤ N - md.J + 1 := by omega
  have hbase_i1 : N - md.J + 1 ≤ i + 1 := by omega
  have hNq_i1 : Nq ≤ i + 1 := le_trans hNq_base hbase_i1
  have hq_lower := hNq (i + 1) hNq_i1
  have hshift := hNs N hNsN
  have hupper_le :
      (upperInt p N : ℚ) ≤ muConst p * (N : ℚ) ^ d := by
    dsimp [d]
    unfold upperInt
    exact Int.floor_le _
  have hgX_le_upper :
      (gcd.g : ℚ) * (X : ℚ) ≤ (upperInt p N : ℚ) := by
    exact_mod_cast hXU
  have hgX_le_mu :
      (gcd.g : ℚ) * (X : ℚ) ≤ muConst p * (N : ℚ) ^ d :=
    le_trans hgX_le_upper hupper_le
  have hbeta_mul_eq :
      beta * (N : ℚ) ^ d =
        (muConst p * (N : ℚ) ^ d) / (gcd.g : ℚ) := by
    dsimp [beta]
    ring
  have hX_le_beta : (X : ℚ) ≤ beta * (N : ℚ) ^ d := by
    rw [hbeta_mul_eq, le_div_iff₀ hgq_pos]
    calc
      (X : ℚ) * (gcd.g : ℚ) = (gcd.g : ℚ) * (X : ℚ) := by ring
      _ ≤ muConst p * (N : ℚ) ^ d := hgX_le_mu
  have hbase_i1_q :
      ((N - md.J + 1 : ℕ) : ℚ) ≤ ((i + 1 : ℕ) : ℚ) := by
    exact_mod_cast hbase_i1
  have hpow_le :
      ((N - md.J + 1 : ℕ) : ℚ) ^ d ≤
        ((i + 1 : ℕ) : ℚ) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase_i1_q d
  have hc_mul_le :
      c * ((N - md.J + 1 : ℕ) : ℚ) ^ d ≤
        c * ((i + 1 : ℕ) : ℚ) ^ d :=
    mul_le_mul_of_nonneg_left hpow_le hc_pos.le
  calc
    (X : ℚ) ≤ beta * (N : ℚ) ^ d := hX_le_beta
    _ < c * ((N - md.J + 1 : ℕ) : ℚ) ^ d := hshift
    _ ≤ c * ((i + 1 : ℕ) : ℚ) ^ d := hc_mul_le
    _ ≤ q.eval ((i + 1 : ℕ) : ℚ) := hq_lower

lemma upperInt_unbounded (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (N₀ : ℕ) :
    ∀ M : ℤ, ∃ N, N₀ ≤ N ∧ M ≤ upperInt p N := by
  intro M
  have hpow_ne : 2 * p.natDegree ≠ 0 := by omega
  have hμ_pos : 0 < muConst p := muConst_pos p h_nonconst h_lead_pos
  have ht_q :
      Tendsto (fun x : ℚ => muConst p * x ^ (2 * p.natDegree))
        atTop atTop :=
    tendsto_const_mul_pow_atTop hpow_ne hμ_pos
  have ht_nat :
      Tendsto (fun N : ℕ => muConst p * (N : ℚ) ^ (2 * p.natDegree))
        atTop atTop :=
    ht_q.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.tendsto_atTop_atTop.mp ht_nat ((M : ℚ) + 1)
  refine ⟨max N₀ N₁, le_max_left _ _, ?_⟩
  have hlarge :
      (M : ℚ) + 1 ≤
        muConst p * ((max N₀ N₁ : ℕ) : ℚ) ^ (2 * p.natDegree) :=
    hN₁ (max N₀ N₁) (le_max_right _ _)
  unfold upperInt
  exact Int.le_floor.mpr (by linarith)

lemma intEval_nonneg_eventually (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → 0 ≤ intEval p hp ((n : ℕ) : ℤ) := by
  set pr : ℝ[X] := p.map (algebraMap ℚ ℝ) with hpr_def
  have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
    (algebraMap ℚ ℝ).injective
  have hpr_natDegree : pr.natDegree = p.natDegree := by
    rw [hpr_def, Polynomial.natDegree_map_eq_of_injective h_inj]
  have hpr_deg_pos : 0 < pr.degree := by
    have hnat : 0 < pr.natDegree := by
      rw [hpr_natDegree]
      exact h_nonconst
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
  have hpr_lead_pos : 0 < pr.leadingCoeff := by
    rw [hpr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
    have : (0 : ℝ) < (p.leadingCoeff : ℝ) := by
      exact_mod_cast h_lead_pos
    simpa [algebraMap] using this
  have h_tendsto : Tendsto (fun x : ℝ => pr.eval x) atTop atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg pr hpr_deg_pos hpr_lead_pos.le
  obtain ⟨R, hR⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto 0
  refine ⟨Nat.ceil (max R 0), ?_⟩
  intro n hn
  have hR_le_n : R ≤ (n : ℝ) := by
    have hR_le_ceil : R ≤ (Nat.ceil (max R 0) : ℝ) := by
      exact le_trans (le_max_left _ _) (Nat.le_ceil _)
    have hceil_le_n : (Nat.ceil (max R 0) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact le_trans hR_le_ceil hceil_le_n
  have h_eval_real : 0 ≤ pr.eval ((n : ℕ) : ℝ) := hR _ hR_le_n
  have h_eval_cast :
      pr.eval ((n : ℕ) : ℝ) = ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [hpr_def]
    have hn_cast : ((n : ℕ) : ℝ) =
        (algebraMap ℚ ℝ) ((n : ℕ) : ℚ) := by
      simp [algebraMap]
    rw [hn_cast, Polynomial.eval_map_apply]
    simp [algebraMap]
  have h_eval_q : 0 ≤ p.eval ((n : ℕ) : ℚ) := by
    have : (0 : ℝ) ≤ ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [← h_eval_cast]
      exact h_eval_real
    exact_mod_cast this
  have h_intEval_eq :
      ((intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) =
        p.eval ((n : ℕ) : ℚ) := by
    rw [intEval_spec]
    push_cast
    rfl
  have : (0 : ℚ) ≤ ((intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) := by
    rw [h_intEval_eq]
    exact h_eval_q
  exact_mod_cast this

lemma intEval_eventually_ge (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    (M : ℤ) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → M ≤ intEval p hp ((n : ℕ) : ℤ) := by
  set pr : ℝ[X] := p.map (algebraMap ℚ ℝ) with hpr_def
  have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
    (algebraMap ℚ ℝ).injective
  have hpr_natDegree : pr.natDegree = p.natDegree := by
    rw [hpr_def, Polynomial.natDegree_map_eq_of_injective h_inj]
  have hpr_deg_pos : 0 < pr.degree := by
    have hnat : 0 < pr.natDegree := by
      rw [hpr_natDegree]
      exact h_nonconst
    exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
  have hpr_lead_pos : 0 < pr.leadingCoeff := by
    rw [hpr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
    have : (0 : ℝ) < (p.leadingCoeff : ℝ) := by
      exact_mod_cast h_lead_pos
    simpa [algebraMap] using this
  have h_tendsto : Tendsto (fun x : ℝ => pr.eval x) atTop atTop :=
    Polynomial.tendsto_atTop_of_leadingCoeff_nonneg pr hpr_deg_pos hpr_lead_pos.le
  obtain ⟨R, hR⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto (M : ℝ)
  refine ⟨Nat.ceil (max R 0), ?_⟩
  intro n hn
  have hR_le_n : R ≤ (n : ℝ) := by
    have hR_le_ceil : R ≤ (Nat.ceil (max R 0) : ℝ) := by
      exact le_trans (le_max_left _ _) (Nat.le_ceil _)
    have hceil_le_n : (Nat.ceil (max R 0) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact le_trans hR_le_ceil hceil_le_n
  have h_eval_real : (M : ℝ) ≤ pr.eval ((n : ℕ) : ℝ) := hR _ hR_le_n
  have h_eval_cast :
      pr.eval ((n : ℕ) : ℝ) = ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [hpr_def]
    have hn_cast : ((n : ℕ) : ℝ) =
        (algebraMap ℚ ℝ) ((n : ℕ) : ℚ) := by
      simp [algebraMap]
    rw [hn_cast, Polynomial.eval_map_apply]
    simp [algebraMap]
  have h_eval_q : (M : ℚ) ≤ p.eval ((n : ℕ) : ℚ) := by
    have : ((M : ℚ) : ℝ) ≤ ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [← h_eval_cast]
      exact_mod_cast h_eval_real
    exact_mod_cast this
  have h_intEval_eq :
      ((intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) =
        p.eval ((n : ℕ) : ℚ) := by
    rw [intEval_spec]
    push_cast
    rfl
  have : (M : ℚ) ≤ ((intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) := by
    rw [h_intEval_eq]
    exact h_eval_q
  exact_mod_cast this

lemma self_le_D (j : ℕ) : j ≤ D j := by
  unfold D u P
  nlinarith [Nat.zero_le j]

lemma self_le_tau (N : ℕ) : N ≤ tau N := by
  unfold tau u P
  nlinarith [Nat.zero_le N]

lemma baseInt_nonneg_eventually {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 ≤ baseInt p hp corr fill N := by
  classical
  obtain ⟨Kp, hKp⟩ := intEval_nonneg_eventually p hp h_nonconst h_lead_pos
  let f : ℕ → ℤ := fun j => intEval p hp ((D j : ℕ) : ℤ)
  let mainK : ℤ := ∑ j ∈ Finset.Icc md.J Kp, f j
  let corrBase : ℤ := ∑ ν : Fin corr.t, intEval p hp ((corr.c ν : ℕ) : ℤ)
  let fillBase : ℤ := ∑ x ∈ fill.F, intEval p hp (((fill.Λ * x : ℕ) : ℤ))
  let C : ℤ := mainK + corrBase + fillBase
  obtain ⟨Kτ, hKτ⟩ := intEval_eventually_ge p hp h_nonconst h_lead_pos (-C)
  refine ⟨max Kp Kτ, ?_⟩
  intro N hN
  have hKpN : Kp ≤ N := le_trans (le_max_left _ _) hN
  have hKτN : Kτ ≤ N := le_trans (le_max_right _ _) hN
  have hmain_ge :
      mainK ≤ ∑ j ∈ Finset.Icc md.J N, f j := by
    dsimp [mainK]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, le_trans (Finset.mem_Icc.mp hj).2 hKpN⟩
    · intro j hjN hjnot
      have hj_bounds := Finset.mem_Icc.mp hjN
      have hKp_lt_j : Kp < j := by
        by_contra hnotlt
        have hj_le_Kp : j ≤ Kp := le_of_not_gt hnotlt
        exact hjnot (Finset.mem_Icc.mpr ⟨hj_bounds.1, hj_le_Kp⟩)
      dsimp [f]
      exact hKp (D j) (le_trans (le_of_lt hKp_lt_j) (self_le_D j))
  have hKτ_tau : Kτ ≤ tau N := le_trans hKτN (self_le_tau N)
  have htau_ge :
      -C ≤ intEval p hp ((tau N : ℕ) : ℤ) :=
    hKτ (tau N) hKτ_tau
  unfold baseInt
  dsimp [C, mainK, corrBase, fillBase, f] at hmain_ge htau_ge ⊢
  linarith

lemma upperEdge_unbounded {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    (h_nonconst : 1 ≤ p.natDegree) (h_lead_pos : 0 < p.leadingCoeff)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N₀ : ℕ) :
    ∀ M : ℤ, ∃ N, N₀ ≤ N ∧ M ≤ upperEdge p hp corr fill N := by
  obtain ⟨Nb, hNb⟩ :=
    baseInt_nonneg_eventually p hp h_nonconst h_lead_pos corr fill
  intro M
  obtain ⟨N, hN, hupper⟩ :=
    upperInt_unbounded p h_nonconst h_lead_pos (max N₀ Nb) M
  refine ⟨N, le_trans (le_max_left _ _) hN, ?_⟩
  have hb : 0 ≤ baseInt p hp corr fill N :=
    hNb N (le_trans (le_max_right _ _) hN)
  unfold upperEdge
  linarith

lemma main_slot_switch_intEval_sum (p : ℚ[X]) (hp : IntValued p) (j : ℕ) :
    (∑ n ∈ scaledPatternDenoms E0 (D j), intEval p hp ((n : ℕ) : ℤ)) -
        intEval p hp ((D j : ℕ) : ℤ) =
      intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) := by
  have hD_pos : 0 < D j := by
    unfold D u P
    positivity
  change
    (∑ n ∈ scaledPatternDenoms E0 (D j), intEval p hp ((n : ℕ) : ℤ)) -
        intEval p hp ((D j : ℕ) : ℤ) =
      intEval (switchingPoly p E0) (switchingPoly_intValued p hp E0)
        ((D j : ℕ) : ℤ)
  exact scaledPatternDenoms_intEval_sum_sub p hp E0 hD_pos

lemma correction_slot_switch_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (ν : Fin corr.t) (hc : 0 < corr.c ν) :
    (∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
        intEval p hp ((n : ℕ) : ℤ)) -
        intEval p hp ((corr.c ν : ℕ) : ℤ) =
      corr.b ν := by
  rw [corr.hb_def ν]
  exact scaledPatternDenoms_intEval_sum_sub p hp (corr.G ν) hc

/-! ### Explicit final denominator blocks

The final construction starts with one denominator for each main slot and
correction slot, then replaces selected slots by their Egyptian-pattern
multiples. These definitions keep the concrete final `Finset ℕ` separate from
the indexed sum identities below. -/

def mainUnswitchedDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc md.J N \ S).image D

def mainSwitchedDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (_md : MainChoice α L p hp) (_N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.biUnion fun j => scaledPatternDenoms E0 (D j)

def mainDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  mainUnswitchedDenoms md N S ∪ mainSwitchedDenoms md N S ∪ {tau N}

def correctionUnswitchedDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) : Finset ℕ :=
  ((Finset.univ : Finset (Fin corr.t)) \ T).image corr.c

def correctionSwitchedDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) : Finset ℕ :=
  T.biUnion fun ν => scaledPatternDenoms (corr.G ν) (corr.c ν)

def correctionDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) : Finset ℕ :=
  correctionUnswitchedDenoms corr T ∪ correctionSwitchedDenoms corr T

def fillerDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} (fill : FillerData p hp corr) :
    Finset ℕ :=
  fill.F.image fun f => fill.Λ * f

def finalDenoms {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N : ℕ) (S : Finset ℕ) (T : Finset (Fin corr.t)) : Finset ℕ :=
  mainDenoms md N S ∪ correctionDenoms corr T ∪ fillerDenoms fill

abbrev MainUnswitchedIndex {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ) :=
  {j : ℕ // j ∈ Finset.Icc md.J N \ S}

noncomputable instance mainUnswitchedIndexFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ) :
    Fintype (MainUnswitchedIndex md N S) :=
  Fintype.ofFinset (Finset.Icc md.J N \ S) (by intro x; rfl)

abbrev MainSwitchSlotIndex (S : Finset ℕ) :=
  {j : ℕ // j ∈ S}

noncomputable instance mainSwitchSlotIndexFintype (S : Finset ℕ) :
    Fintype (MainSwitchSlotIndex S) :=
  Fintype.ofFinset S (by intro x; rfl)

abbrev MainSwitchedIndex (S : Finset ℕ) :=
  Sigma fun j : MainSwitchSlotIndex S =>
    {n : ℕ // n ∈ scaledPatternDenoms E0 (D j.1)}

noncomputable instance mainSwitchedIndexFiberFintype (S : Finset ℕ)
    (j : MainSwitchSlotIndex S) :
    Fintype {n : ℕ // n ∈ scaledPatternDenoms E0 (D j.1)} :=
  Fintype.ofFinset (scaledPatternDenoms E0 (D j.1)) (by intro x; rfl)

abbrev CorrectionUnswitchedIndex {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :=
  {ν : Fin corr.t // ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T}

noncomputable instance correctionUnswitchedIndexFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t)) :
    Fintype (CorrectionUnswitchedIndex corr T) :=
  Fintype.ofFinset ((Finset.univ : Finset (Fin corr.t)) \ T)
    (by intro x; rfl)

abbrev CorrectionSwitchSlotIndex {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :=
  {ν : Fin corr.t // ν ∈ T}

noncomputable instance correctionSwitchSlotIndexFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t)) :
    Fintype (CorrectionSwitchSlotIndex corr T) :=
  Fintype.ofFinset T (by intro x; rfl)

abbrev CorrectionSwitchedIndex {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :=
  Sigma fun ν : CorrectionSwitchSlotIndex corr T =>
    {n : ℕ // n ∈ scaledPatternDenoms (corr.G ν.1) (corr.c ν.1)}

noncomputable instance correctionSwitchedIndexFiberFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (T : Finset (Fin corr.t))
    (ν : CorrectionSwitchSlotIndex corr T) :
    Fintype {n : ℕ // n ∈ scaledPatternDenoms (corr.G ν.1) (corr.c ν.1)} :=
  Fintype.ofFinset (scaledPatternDenoms (corr.G ν.1) (corr.c ν.1))
    (by intro x; rfl)

abbrev FillerIndex {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} (fill : FillerData p hp corr) :=
  {f : ℕ // f ∈ fill.F}

noncomputable instance fillerIndexFintype
    {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} (fill : FillerData p hp corr) :
    Fintype (FillerIndex fill) :=
  Fintype.ofFinset fill.F (by intro x; rfl)

abbrev FinalIndex {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N : ℕ) (S : Finset ℕ) (T : Finset (Fin corr.t)) :=
  ((MainUnswitchedIndex md N S ⊕ MainSwitchedIndex S) ⊕ PUnit.{1}) ⊕
    ((CorrectionUnswitchedIndex corr T ⊕ CorrectionSwitchedIndex corr T) ⊕
      FillerIndex fill)

def finalIndexDenom {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} {fill : FillerData p hp corr}
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)} :
    FinalIndex corr fill N S T → ℕ
  | Sum.inl (Sum.inl (Sum.inl j)) => D j.1
  | Sum.inl (Sum.inl (Sum.inr sw)) => sw.2.1
  | Sum.inl (Sum.inr _) => tau N
  | Sum.inr (Sum.inl (Sum.inl ν)) => corr.c ν.1
  | Sum.inr (Sum.inl (Sum.inr sw)) => sw.2.1
  | Sum.inr (Sum.inr f) => fill.Λ * f.1

def correctionMultiplierMax {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd) : ℕ :=
  (Finset.univ : Finset (Fin corr.t)).sup fun ν =>
    (insert 1 (corr.G ν)).sup fun e => e * corr.c ν

lemma correctionMultiplierMax_lt_tau_eventually {α : ℚ} {L : ℕ}
    {p : ℚ[X]} {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      correctionMultiplierMax corr < tau N := by
  refine ⟨correctionMultiplierMax corr + 1, ?_⟩
  intro N hN
  unfold tau u P
  nlinarith [Nat.zero_le N, hN]

lemma correction_multiple_le_max {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (ν : Fin corr.t) {e : ℕ} (he : e ∈ insert 1 (corr.G ν)) :
    e * corr.c ν ≤ correctionMultiplierMax corr := by
  unfold correctionMultiplierMax
  have h_inner :
      e * corr.c ν ≤ (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) :=
    Finset.le_sup (f := fun e => e * corr.c ν) he
  have h_outer :
      (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν) ≤
        (Finset.univ : Finset (Fin corr.t)).sup
          (fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν)) :=
    Finset.le_sup
      (f := fun ν => (insert 1 (corr.G ν)).sup (fun e => e * corr.c ν))
      (Finset.mem_univ ν)
  exact le_trans h_inner h_outer

lemma correction_multiple_ne_tau_of_max_lt {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    {N : ℕ} (hτ : correctionMultiplierMax corr < tau N)
    (ν : Fin corr.t) {e : ℕ} (he : e ∈ insert 1 (corr.G ν)) :
    e * corr.c ν ≠ tau N := by
  intro h
  have hle := correction_multiple_le_max corr ν he
  omega

lemma main_copy_ne_correction {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (ν : Fin corr.t) {j h e : ℕ} (hj : md.J ≤ j)
    (hh : h ∈ ({1, 2, 3, 6} : Finset ℕ))
    (he : e ∈ insert 1 (corr.G ν)) :
    h * D j ≠ e * corr.c ν := by
  intro h_eq
  exact corr.no_main_collision ν j hj h hh e he h_eq.symm

lemma filler_ne_main_copy {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} {corr : CorrectionData p hp gcd}
    (fill : FillerData p hp corr) {f j h : ℕ}
    (hf : f ∈ fill.F) (hj : md.J ≤ j)
    (hh : h ∈ ({1, 2, 3, 6} : Finset ℕ)) :
    fill.Λ * f ≠ h * D j :=
  fill.hF_distinct_from_main_corr.1 f hf j hj h hh

lemma filler_ne_correction {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} {corr : CorrectionData p hp gcd}
    (fill : FillerData p hp corr) {f : ℕ}
    (hf : f ∈ fill.F) (ν : Fin corr.t) {e : ℕ}
    (he : e ∈ insert 1 (corr.G ν)) :
    fill.Λ * f ≠ e * corr.c ν :=
  fill.hF_distinct_from_main_corr.2 f hf ν e he

lemma mainSwitchedIndex_denom_injective (S : Finset ℕ) :
    Function.Injective (fun sw : MainSwitchedIndex S => sw.2.1) := by
  intro a b hab
  rcases a with ⟨⟨ja, hjaS⟩, ⟨na, hna⟩⟩
  rcases b with ⟨⟨jb, hjbS⟩, ⟨nb, hnb⟩⟩
  dsimp at hab ⊢
  simp only [scaledPatternDenoms, Finset.mem_image] at hna hnb
  obtain ⟨ea, hea, hea_eq⟩ := hna
  obtain ⟨eb, heb, heb_eq⟩ := hnb
  have hea_main : ea ∈ ({1, 2, 3, 6} : Finset ℕ) := by
    fin_cases hea <;> simp
  have heb_main : eb ∈ ({1, 2, 3, 6} : Finset ℕ) := by
    fin_cases heb <;> simp
  have hmul : ea * D ja = eb * D jb := by
    rw [hea_eq, heb_eq]
    exact hab
  have hcopy := main_copy_eq_of_eq hea_main heb_main hmul
  have hjab : ja = jb := hcopy.2
  subst jb
  subst nb
  rfl

lemma mainUnswitchedIndex_denom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} (md : MainChoice α L p hp) (N : ℕ)
    (S : Finset ℕ) :
    Function.Injective (fun j : MainUnswitchedIndex md N S => D j.1) := by
  intro a b hab
  apply Subtype.ext
  exact D_injective hab

lemma fillerIndex_denom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} {corr : CorrectionData p hp gcd}
    (fill : FillerData p hp corr) :
    Function.Injective (fun f : FillerIndex fill => fill.Λ * f.1) := by
  intro a b hab
  apply Subtype.ext
  have hΛ_pos : 0 < fill.Λ := lt_of_le_of_lt (Nat.zero_le L) fill.hΛ_gt_L
  exact Nat.mul_left_cancel hΛ_pos hab

lemma correctionUnswitchedIndex_denom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :
    Function.Injective (fun ν : CorrectionUnswitchedIndex corr T => corr.c ν.1) := by
  intro a b hab
  by_cases hν : a.1 = b.1
  · exact Subtype.ext hν
  · exfalso
    have hne := corr.no_corr_collision a.1 b.1 hν
      1 (Finset.mem_insert_self 1 (corr.G a.1))
      1 (Finset.mem_insert_self 1 (corr.G b.1))
    apply hne
    simpa using hab

lemma correctionSwitchedIndex_denom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) :
    Function.Injective (fun sw : CorrectionSwitchedIndex corr T => sw.2.1) := by
  intro a b hab
  rcases a with ⟨⟨νa, hνaT⟩, ⟨na, hna⟩⟩
  rcases b with ⟨⟨νb, hνbT⟩, ⟨nb, hnb⟩⟩
  dsimp at hab ⊢
  simp only [scaledPatternDenoms, Finset.mem_image] at hna hnb
  obtain ⟨ea, hea, hea_eq⟩ := hna
  obtain ⟨eb, heb, heb_eq⟩ := hnb
  by_cases hν : νa = νb
  · subst νb
    subst nb
    rfl
  · exfalso
    have hmul : ea * corr.c νa = eb * corr.c νb := by
      rw [hea_eq, heb_eq]
      exact hab
    exact corr.no_corr_collision νa νb hν ea (Finset.mem_insert_of_mem hea)
      eb (Finset.mem_insert_of_mem heb) hmul

lemma mainSwitchedIndex_copy (S : Finset ℕ) (sw : MainSwitchedIndex S) :
    ∃ h : ℕ, h ∈ E0 ∧ h ∈ ({1, 2, 3, 6} : Finset ℕ) ∧
      sw.2.1 = h * D sw.1.1 := by
  have hn := sw.2.2
  simp only [scaledPatternDenoms, Finset.mem_image] at hn
  obtain ⟨h, hhE, hhn⟩ := hn
  refine ⟨h, hhE, ?_, hhn.symm⟩
  fin_cases hhE <;> simp

lemma correctionSwitchedIndex_copy {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) (sw : CorrectionSwitchedIndex corr T) :
    ∃ e : ℕ, e ∈ corr.G sw.1.1 ∧ e ∈ insert 1 (corr.G sw.1.1) ∧
      sw.2.1 = e * corr.c sw.1.1 := by
  have hn := sw.2.2
  simp only [scaledPatternDenoms, Finset.mem_image] at hn
  obtain ⟨e, heG, hen⟩ := hn
  exact ⟨e, heG, Finset.mem_insert_of_mem heG, hen.symm⟩

lemma finalIndexDenom_injective {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (fill : FillerData p hp corr) {N : ℕ} {S : Finset ℕ}
    {T : Finset (Fin corr.t)}
    (hS : S ⊆ Finset.Icc md.J N)
    (hτ : correctionMultiplierMax corr < tau N) :
    Function.Injective
      (finalIndexDenom :
        FinalIndex corr fill N S T → ℕ) := by
  classical
  intro a b hab
  rcases a with (((aj | asw) | atau) | ((acu | acsw) | af))
  <;> rcases b with (((bj | bsw) | btau) | ((bcu | bcsw) | bf))
  <;> dsimp [finalIndexDenom] at hab ⊢
  · congr
    apply Subtype.ext
    exact D_injective hab
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S bsw
    have hcopy := main_copy_eq_of_eq (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      hh (by simpa [hval] using hab : 1 * D aj.1 = h * D bsw.1.1)
    have haj_notS : aj.1 ∉ S := (Finset.mem_sdiff.mp aj.2).2
    exact haj_notS (by simpa [← hcopy.2] using bsw.1.2)
  · exfalso
    exact main_copy_ne_tau (h := 1) (j := aj.1) (N := N)
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa using hab)
  · exfalso
    have hajJ : md.J ≤ aj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp aj.2).1).1
    exact main_copy_ne_correction corr bcu.1 (j := aj.1) (h := 1) (e := 1)
      hajJ (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (Finset.mem_insert_self 1 (corr.G bcu.1)) (by simpa using hab)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T bcsw
    have hajJ : md.J ≤ aj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp aj.2).1).1
    exact main_copy_ne_correction corr bcsw.1.1 (j := aj.1) (h := 1) (e := e)
      hajJ (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ)) he
      (by simpa [hval] using hab)
  · exfalso
    have hajJ : md.J ≤ aj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp aj.2).1).1
    exact filler_ne_main_copy fill bf.2 hajJ
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa using hab.symm)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S asw
    have hcopy := main_copy_eq_of_eq hh
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa [hval] using hab : h * D asw.1.1 = 1 * D bj.1)
    have hbj_notS : bj.1 ∉ S := (Finset.mem_sdiff.mp bj.2).2
    exact hbj_notS (by simpa [hcopy.2] using asw.1.2)
  · congr
    exact mainSwitchedIndex_denom_injective S hab
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S asw
    exact main_copy_ne_tau (h := h) (j := asw.1.1) (N := N) hh
      (by simpa [hval] using hab)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S asw
    have haswJ : md.J ≤ asw.1.1 := (Finset.mem_Icc.mp (hS asw.1.2)).1
    exact main_copy_ne_correction corr bcu.1 (j := asw.1.1) (h := h) (e := 1)
      haswJ hh (Finset.mem_insert_self 1 (corr.G bcu.1))
      (by simpa [hval] using hab)
  · exfalso
    obtain ⟨h, _hhE, hh, hval_main⟩ := mainSwitchedIndex_copy S asw
    obtain ⟨e, _heG, he, hval_corr⟩ := correctionSwitchedIndex_copy corr T bcsw
    have haswJ : md.J ≤ asw.1.1 := (Finset.mem_Icc.mp (hS asw.1.2)).1
    exact main_copy_ne_correction corr bcsw.1.1 (j := asw.1.1) (h := h) (e := e)
      haswJ hh he (by simpa [hval_main, hval_corr] using hab)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S asw
    have haswJ : md.J ≤ asw.1.1 := (Finset.mem_Icc.mp (hS asw.1.2)).1
    exact filler_ne_main_copy fill bf.2 haswJ hh
      (by simpa [hval] using hab.symm)
  · exfalso
    exact main_copy_ne_tau (h := 1) (j := bj.1) (N := N)
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa using hab.symm)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S bsw
    exact main_copy_ne_tau (h := h) (j := bsw.1.1) (N := N) hh
      (by simpa [hval] using hab.symm)
  · exfalso
    exact correction_multiple_ne_tau_of_max_lt corr hτ bcu.1
      (Finset.mem_insert_self 1 (corr.G bcu.1)) (by simpa using hab.symm)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T bcsw
    exact correction_multiple_ne_tau_of_max_lt corr hτ bcsw.1.1 he
      (by simpa [hval] using hab.symm)
  · exfalso
    have hΛ_pos : 1 ≤ fill.Λ :=
      Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le L) fill.hΛ_gt_L)
    exact filler_ne_tau fill.hΛ_div_8 hΛ_pos (fill.hF_pos bf.1 bf.2)
      (by simpa using hab.symm)
  · exfalso
    have hbjJ : md.J ≤ bj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp bj.2).1).1
    exact main_copy_ne_correction corr acu.1 (j := bj.1) (h := 1) (e := 1)
      hbjJ (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (Finset.mem_insert_self 1 (corr.G acu.1)) (by simpa using hab.symm)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S bsw
    have hbswJ : md.J ≤ bsw.1.1 := (Finset.mem_Icc.mp (hS bsw.1.2)).1
    exact main_copy_ne_correction corr acu.1 (j := bsw.1.1) (h := h) (e := 1)
      hbswJ hh (Finset.mem_insert_self 1 (corr.G acu.1))
      (by simpa [hval] using hab.symm)
  · exfalso
    exact correction_multiple_ne_tau_of_max_lt corr hτ acu.1
      (Finset.mem_insert_self 1 (corr.G acu.1)) (by simpa using hab)
  · congr
    exact correctionUnswitchedIndex_denom_injective corr T hab
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T bcsw
    by_cases hν : acu.1 = bcsw.1.1
    · have hacu_notT : acu.1 ∉ T := (Finset.mem_sdiff.mp acu.2).2
      exact hacu_notT (by simpa [← hν] using bcsw.1.2)
    · exact corr.no_corr_collision acu.1 bcsw.1.1 hν 1
        (Finset.mem_insert_self 1 (corr.G acu.1)) e he
        (by simpa [hval] using hab)
  · exfalso
    exact filler_ne_correction fill bf.2 acu.1
      (Finset.mem_insert_self 1 (corr.G acu.1)) (by simpa using hab.symm)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T acsw
    have hbjJ : md.J ≤ bj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp bj.2).1).1
    exact main_copy_ne_correction corr acsw.1.1 (j := bj.1) (h := 1) (e := e)
      hbjJ (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ)) he
      (by simpa [hval] using hab.symm)
  · exfalso
    obtain ⟨e, _heG, he, hval_corr⟩ := correctionSwitchedIndex_copy corr T acsw
    obtain ⟨h, _hhE, hh, hval_main⟩ := mainSwitchedIndex_copy S bsw
    have hbswJ : md.J ≤ bsw.1.1 := (Finset.mem_Icc.mp (hS bsw.1.2)).1
    exact main_copy_ne_correction corr acsw.1.1 (j := bsw.1.1) (h := h) (e := e)
      hbswJ hh he (by simpa [hval_corr, hval_main] using hab.symm)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T acsw
    exact correction_multiple_ne_tau_of_max_lt corr hτ acsw.1.1 he
      (by simpa [hval] using hab)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T acsw
    by_cases hν : acsw.1.1 = bcu.1
    · have hbcu_notT : bcu.1 ∉ T := (Finset.mem_sdiff.mp bcu.2).2
      exact hbcu_notT (by simpa [hν] using acsw.1.2)
    · exact corr.no_corr_collision acsw.1.1 bcu.1 hν e he 1
        (Finset.mem_insert_self 1 (corr.G bcu.1))
        (by simpa [hval] using hab)
  · congr
    exact correctionSwitchedIndex_denom_injective corr T hab
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T acsw
    exact filler_ne_correction fill bf.2 acsw.1.1 he
      (by simpa [hval] using hab.symm)
  · exfalso
    have hbjJ : md.J ≤ bj.1 := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp bj.2).1).1
    exact filler_ne_main_copy fill af.2 hbjJ
      (by simp : (1 : ℕ) ∈ ({1, 2, 3, 6} : Finset ℕ))
      (by simpa using hab)
  · exfalso
    obtain ⟨h, _hhE, hh, hval⟩ := mainSwitchedIndex_copy S bsw
    have hbswJ : md.J ≤ bsw.1.1 := (Finset.mem_Icc.mp (hS bsw.1.2)).1
    exact filler_ne_main_copy fill af.2 hbswJ hh
      (by simpa [hval] using hab)
  · exfalso
    have hΛ_pos : 1 ≤ fill.Λ :=
      Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le L) fill.hΛ_gt_L)
    exact filler_ne_tau fill.hΛ_div_8 hΛ_pos (fill.hF_pos af.1 af.2)
      (by simpa using hab)
  · exfalso
    exact filler_ne_correction fill af.2 bcu.1
      (Finset.mem_insert_self 1 (corr.G bcu.1)) (by simpa using hab)
  · exfalso
    obtain ⟨e, _heG, he, hval⟩ := correctionSwitchedIndex_copy corr T bcsw
    exact filler_ne_correction fill af.2 bcsw.1.1 he
      (by simpa [hval] using hab)
  · congr
    exact fillerIndex_denom_injective fill hab

lemma mainUnswitchedIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) (N : ℕ) (S : Finset ℕ)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ j : MainUnswitchedIndex md N S, f j.1) =
      ∑ j ∈ Finset.Icc md.J N \ S, f j := by
  rw [← Finset.sum_attach (Finset.Icc md.J N \ S) f]
  rfl

lemma mainSwitchedIndex_sum (S : Finset ℕ)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ sw : MainSwitchedIndex S, f sw.2.1) =
      ∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), f n := by
  rw [← Finset.univ_sigma_univ]
  rw [Finset.sum_sigma]
  rw [← Finset.sum_attach S
    (fun j => ∑ n ∈ scaledPatternDenoms E0 (D j), f n)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_attach (scaledPatternDenoms E0 (D j.1)) f]
  rfl

lemma correctionUnswitchedIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) {M : Type*} [AddCommMonoid M]
    (f : Fin corr.t → M) :
    (∑ ν : CorrectionUnswitchedIndex corr T, f ν.1) =
      ∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T, f ν := by
  rw [← Finset.sum_attach ((Finset.univ : Finset (Fin corr.t)) \ T) f]
  rfl

lemma correctionSwitchedIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (T : Finset (Fin corr.t)) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) :
    (∑ sw : CorrectionSwitchedIndex corr T, f sw.2.1) =
      ∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν), f n := by
  rw [← Finset.univ_sigma_univ]
  rw [Finset.sum_sigma]
  rw [← Finset.sum_attach T
    (fun ν => ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν), f n)]
  apply Finset.sum_congr rfl
  intro ν _
  rw [← Finset.sum_attach (scaledPatternDenoms (corr.G ν.1) (corr.c ν.1)) f]
  rfl

lemma fillerIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    {corr : CorrectionData p hp gcd} (fill : FillerData p hp corr)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ x : FillerIndex fill, f x.1) =
      ∑ x ∈ fill.F, f x := by
  rw [← Finset.sum_attach fill.F f]
  rfl

lemma finalIndex_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (N : ℕ) (S : Finset ℕ) (T : Finset (Fin corr.t))
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ i : FinalIndex corr fill N S T, f (finalIndexDenom i)) =
      ((∑ j ∈ Finset.Icc md.J N \ S, f (D j)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), f n) +
        f (tau N)) +
      ((∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T, f (corr.c ν)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν), f n)) +
      (∑ x ∈ fill.F, f (fill.Λ * x)) := by
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp only [finalIndexDenom]
  rw [mainUnswitchedIndex_sum md N S (fun x => f (D x))]
  rw [mainSwitchedIndex_sum S f]
  rw [show (∑ _x : PUnit, f (tau N)) = f (tau N) by simp]
  rw [correctionUnswitchedIndex_sum corr T (fun ν => f (corr.c ν))]
  rw [correctionSwitchedIndex_sum corr T f]
  rw [fillerIndex_sum fill (fun x => f (fill.Λ * x))]
  ac_rfl

lemma main_indexed_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    (md : MainChoice α L p hp) {N : ℕ} {S : Finset ℕ}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N) :
    (∑ j ∈ Finset.Icc md.J N \ S, (1 : ℚ) / (D j : ℚ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), (1 : ℚ) / (n : ℚ)) +
        (1 : ℚ) / (tau N : ℚ) =
      (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) := by
  have hD_pos : ∀ j : ℕ, 0 < D j := by
    intro j
    unfold D u P
    positivity
  calc
    (∑ j ∈ Finset.Icc md.J N \ S, (1 : ℚ) / (D j : ℚ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), (1 : ℚ) / (n : ℚ)) +
        (1 : ℚ) / (tau N : ℚ)
        = (∑ j ∈ Finset.Icc md.J N \ S, (1 : ℚ) / (D j : ℚ)) +
            (∑ j ∈ S, (1 : ℚ) / (D j : ℚ)) +
            (1 : ℚ) / (tau N : ℚ) := by
              congr 2
              apply Finset.sum_congr rfl
              intro j _
              exact scaledPatternDenoms_sum_recip isEgyptianPattern_E0 (hD_pos j)
    _ = (∑ j ∈ Finset.Icc md.J N, (1 : ℚ) / (D j : ℚ)) +
            (1 : ℚ) / (tau N : ℚ) := by
              rw [Finset.sum_sdiff hS]
    _ = (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) := by
              rw [main_telescoping md.J N hJN]
              ring

lemma main_indexed_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) (md : MainChoice α L p hp) {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc md.J N) :
    (∑ j ∈ Finset.Icc md.J N \ S, intEval p hp ((D j : ℕ) : ℤ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j),
          intEval p hp ((n : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ) =
      (∑ j ∈ Finset.Icc md.J N, intEval p hp ((D j : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ) +
        (∑ j ∈ S,
          intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)) := by
  let base : ℕ → ℤ := fun j => intEval p hp ((D j : ℕ) : ℤ)
  let inc : ℕ → ℤ := fun j =>
    intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)
  have hswitch : ∀ j ∈ S,
      (∑ n ∈ scaledPatternDenoms E0 (D j), intEval p hp ((n : ℕ) : ℤ)) =
        base j + inc j := by
    intro j _
    have h := main_slot_switch_intEval_sum p hp j
    dsimp [base, inc]
    omega
  calc
    (∑ j ∈ Finset.Icc md.J N \ S, intEval p hp ((D j : ℕ) : ℤ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j),
          intEval p hp ((n : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ)
        = (∑ j ∈ Finset.Icc md.J N \ S, base j) +
            (∑ j ∈ S, (base j + inc j)) +
            intEval p hp ((tau N : ℕ) : ℤ) := by
              congr 2
              apply Finset.sum_congr rfl
              intro j hj
              exact hswitch j hj
    _ = (∑ j ∈ Finset.Icc md.J N, base j) +
          intEval p hp ((tau N : ℕ) : ℤ) +
          (∑ j ∈ S, inc j) := by
            rw [Finset.sum_add_distrib]
            have hbase :
                (∑ j ∈ Finset.Icc md.J N \ S, base j) +
                  (∑ j ∈ S, base j) =
                    ∑ j ∈ Finset.Icc md.J N, base j :=
              Finset.sum_sdiff hS
            linarith
    _ = (∑ j ∈ Finset.Icc md.J N, intEval p hp ((D j : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ) +
        (∑ j ∈ S,
          intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)) := rfl

lemma correction_indexed_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    {T : Finset (Fin corr.t)} (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
        (1 : ℚ) / (corr.c ν : ℚ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          (1 : ℚ) / (n : ℚ)) =
      ∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ) := by
  calc
    (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
        (1 : ℚ) / (corr.c ν : ℚ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          (1 : ℚ) / (n : ℚ))
        = (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
            (1 : ℚ) / (corr.c ν : ℚ)) +
            (∑ ν ∈ T, (1 : ℚ) / (corr.c ν : ℚ)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro ν _
              exact scaledPatternDenoms_sum_recip (corr.hG ν) (hcorr_pos ν)
    _ = ∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ) := by
              rw [Finset.sum_sdiff (Finset.subset_univ T)]

lemma correction_indexed_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    {T : Finset (Fin corr.t)} (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
        intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          intEval p hp ((n : ℕ) : ℤ)) =
      (∑ ν : Fin corr.t, intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, corr.b ν) := by
  let base : Fin corr.t → ℤ := fun ν => intEval p hp ((corr.c ν : ℕ) : ℤ)
  let inc : Fin corr.t → ℤ := fun ν => corr.b ν
  have hswitch : ∀ ν ∈ T,
      (∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          intEval p hp ((n : ℕ) : ℤ)) =
        base ν + inc ν := by
    intro ν _
    have h := correction_slot_switch_intEval_sum p hp corr ν (hcorr_pos ν)
    dsimp [base, inc]
    omega
  calc
    (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
        intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          intEval p hp ((n : ℕ) : ℤ))
        = (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T, base ν) +
            (∑ ν ∈ T, (base ν + inc ν)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro ν hν
              exact hswitch ν hν
    _ = (∑ ν : Fin corr.t, base ν) + (∑ ν ∈ T, inc ν) := by
            rw [Finset.sum_add_distrib]
            have hbase :
                (∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T, base ν) +
                  (∑ ν ∈ T, base ν) =
                    ∑ ν : Fin corr.t, base ν :=
              Finset.sum_sdiff (Finset.subset_univ T)
            linarith
    _ = (∑ ν : Fin corr.t, intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, corr.b ν) := rfl

lemma filler_indexed_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]}
    {hp : IntValued p} {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} {corr : CorrectionData p hp gcd}
    (fill : FillerData p hp corr) :
    (∑ f ∈ fill.F, (1 : ℚ) / ((fill.Λ * f : ℕ) : ℚ)) =
      α - (1 : ℚ) / ((P : ℚ) * (u md.J : ℚ)) -
      (∑ ν : Fin corr.t, (1 : ℚ) / (corr.c ν : ℚ)) :=
  fill.hF_recip

lemma indexed_total_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N)
    (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    ((∑ j ∈ Finset.Icc md.J N \ S, (1 : ℚ) / (D j : ℚ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j), (1 : ℚ) / (n : ℚ)) +
        (1 : ℚ) / (tau N : ℚ)) +
      ((∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
          (1 : ℚ) / (corr.c ν : ℚ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          (1 : ℚ) / (n : ℚ))) +
      (∑ f ∈ fill.F, (1 : ℚ) / ((fill.Λ * f : ℕ) : ℚ)) =
      α := by
  rw [main_indexed_recip_sum md hJN hS]
  rw [correction_indexed_recip_sum corr hcorr_pos]
  rw [filler_indexed_recip_sum fill]
  ring

lemma indexed_total_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hS : S ⊆ Finset.Icc md.J N) (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    ((∑ j ∈ Finset.Icc md.J N \ S, intEval p hp ((D j : ℕ) : ℤ)) +
        (∑ j ∈ S, ∑ n ∈ scaledPatternDenoms E0 (D j),
          intEval p hp ((n : ℕ) : ℤ)) +
        intEval p hp ((tau N : ℕ) : ℤ)) +
      ((∑ ν ∈ (Finset.univ : Finset (Fin corr.t)) \ T,
          intEval p hp ((corr.c ν : ℕ) : ℤ)) +
        (∑ ν ∈ T, ∑ n ∈ scaledPatternDenoms (corr.G ν) (corr.c ν),
          intEval p hp ((n : ℕ) : ℤ))) +
      (∑ f ∈ fill.F, intEval p hp (((fill.Λ * f : ℕ) : ℤ))) =
      baseInt p hp corr fill N +
        (∑ j ∈ S, intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)) +
        (∑ ν ∈ T, corr.b ν) := by
  rw [main_indexed_intEval_sum p hp md hS]
  rw [correction_indexed_intEval_sum p hp corr hcorr_pos]
  unfold baseInt
  ring

lemma finalIndex_recip_sum {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N)
    (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    (∑ i : FinalIndex corr fill N S T,
      (1 : ℚ) / (finalIndexDenom i : ℚ)) = α := by
  rw [finalIndex_sum corr fill N S T (fun n => (1 : ℚ) / (n : ℚ))]
  exact indexed_total_recip_sum corr fill hJN hS hcorr_pos

lemma finalIndex_intEval_sum {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hS : S ⊆ Finset.Icc md.J N) (hcorr_pos : ∀ ν, 0 < corr.c ν) :
    (∑ i : FinalIndex corr fill N S T,
      intEval p hp ((finalIndexDenom i : ℕ) : ℤ)) =
      baseInt p hp corr fill N +
        (∑ j ∈ S, intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ)) +
        (∑ ν ∈ T, corr.b ν) := by
  rw [finalIndex_sum corr fill N S T
    (fun n => intEval p hp ((n : ℕ) : ℤ))]
  exact indexed_total_intEval_sum p hp corr fill hS hcorr_pos

lemma intEval_fintype_sum_cast (p : ℚ[X]) (hp : IntValued p)
    {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    ((∑ i : ι, intEval p hp ((d i : ℕ) : ℤ) : ℤ) : ℚ) =
      ∑ i : ι, p.eval ((d i : ℕ) : ℚ) := by
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [intEval_spec]
  rfl

lemma select_correction_and_main_subsets {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (fill : FillerData p hp corr) (X_q : ℤ) (N : ℕ) (U m : ℤ)
    (hlo :
      baseInt p hp corr fill N + Bstar p hp corr +
        M0 p hp gcd X_q ≤ m)
    (hhi : m ≤ baseInt p hp corr fill N + U)
    (hwindow : ∀ M : ℤ,
      M0 p hp gcd X_q ≤ M →
      M ≤ U →
      (gcd.g : ℤ) ∣ M →
      ∃ S : Finset ℕ, S ⊆ Finset.Icc md.J N ∧
        (M : ℚ) =
          ∑ j ∈ S,
            ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) :
    ∃ T : Finset (Fin corr.t), ∃ S : Finset ℕ,
      S ⊆ Finset.Icc md.J N ∧
      (m : ℚ) =
        (baseInt p hp corr fill N : ℚ) +
        (∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) +
        (∑ ν ∈ T, ((corr.b ν : ℤ) : ℚ)) := by
  classical
  obtain ⟨T, hT_dvd, hT_nonneg, hT_le⟩ :=
    correction_subset_dvd_with_bounds p hp corr (m - baseInt p hp corr fill N)
  set Δ : ℤ := ∑ ν ∈ T, corr.b ν with hΔ_def
  set M : ℤ := m - baseInt p hp corr fill N - Δ with hM_def
  have hM_dvd : (gcd.g : ℤ) ∣ M := by
    simpa [M, hM_def, Δ, hΔ_def, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hT_dvd
  have hM_lo : M0 p hp gcd X_q ≤ M := by
    rw [hM_def, hΔ_def]
    linarith [hlo, hT_le]
  have hM_hi : M ≤ U := by
    rw [hM_def, hΔ_def]
    linarith [hhi, hT_nonneg]
  obtain ⟨S, hS, hSsum⟩ := hwindow M hM_lo hM_hi hM_dvd
  refine ⟨T, S, hS, ?_⟩
  rw [← hSsum]
  rw [hM_def, hΔ_def]
  push_cast
  ring

lemma main_window_integer_subset {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} (gcd : MainGCDData p hp md)
    (X_q : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (N : ℕ) (hJN : md.J ≤ N)
    (U : ℤ)
    (h_tail : ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ U →
      ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (M : ℤ) (hM0 : M0 p hp gcd X_q ≤ M) (hMle : M ≤ U)
    (hdiv : (gcd.g : ℤ) ∣ M) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc md.J N ∧
      (M : ℚ) =
        ∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ) := by
  obtain ⟨X, hX⟩ := hdiv
  have hg_pos_int : (0 : ℤ) < (gcd.g : ℤ) := by
    exact_mod_cast gcd.hg_pos
  have hX_ge : X_q ≤ X := by
    have hle_gXq : ((gcd.g : ℤ) * X_q) ≤ M :=
      le_trans (M0_ge_g_mul_Xq p hp gcd X_q) hM0
    rw [hX] at hle_gXq
    nlinarith
  have hX_le_U : ((gcd.g : ℤ) * X) ≤ U := by
    rw [← hX]
    exact hMle
  obtain ⟨S, hS, hSsum⟩ :=
    main_window_finite p hp md gcd X_q X hX_q hX_ge N hJN
      (h_tail X hX_ge hX_le_U)
  refine ⟨S, hS, ?_⟩
  rw [← hSsum]
  rw [hX]
  push_cast
  ring

lemma select_subsets_from_rsg_interval {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (fill : FillerData p hp corr) (X_q : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (N : ℕ) (U m : ℤ) (hJN : md.J ≤ N)
    (h_tail : ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ U →
      ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (hlo :
      baseInt p hp corr fill N + Bstar p hp corr +
        M0 p hp gcd X_q ≤ m)
    (hhi : m ≤ baseInt p hp corr fill N + U) :
    ∃ T : Finset (Fin corr.t), ∃ S : Finset ℕ,
      S ⊆ Finset.Icc md.J N ∧
      (m : ℚ) =
        (baseInt p hp corr fill N : ℚ) +
        (∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) +
        (∑ ν ∈ T, ((corr.b ν : ℤ) : ℚ)) := by
  apply select_correction_and_main_subsets p hp corr fill X_q N U m hlo hhi
  intro M hM0 hMle hdiv
  exact main_window_integer_subset p hp gcd X_q hX_q N hJN U h_tail M hM0 hMle hdiv

lemma intEval_finset_sum_cast (p : ℚ[X]) (hp : IntValued p) (E : Finset ℕ) :
    ((∑ n ∈ E, intEval p hp ((n : ℕ) : ℤ) : ℤ) : ℚ) =
      ∑ n ∈ E, p.eval ((n : ℕ) : ℚ) := by
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [intEval_spec]
  rfl

lemma witness_of_denominator_finset (α : ℚ) (L m : ℕ) (p : ℚ[X])
    (E : Finset ℕ) (hE_nonempty : E.Nonempty)
    (hE_gt_L : ∀ n ∈ E, L < n)
    (hrecip : α = ∑ n ∈ E, (1 : ℚ) / (n : ℚ))
    (hsum : (m : ℚ) = ∑ n ∈ E, p.eval ((n : ℕ) : ℚ)) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  classical
  let c : ℕ := E.card
  have hc_pos : 1 ≤ c := by
    dsimp [c]
    exact Finset.card_pos.mpr hE_nonempty
  let g : Fin c ↪o ℕ := E.orderEmbOfFin (by rfl : E.card = c)
  have hc_succ : c - 1 + 1 = c := Nat.sub_add_cancel hc_pos
  refine ⟨c - 1, fun i => g (Fin.cast hc_succ i), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply g.strictMono
    exact Fin.cast_lt_cast hc_succ |>.mpr hij
  · have h0_mem : g (Fin.cast hc_succ 0) ∈ E :=
      E.orderEmbOfFin_mem (by rfl : E.card = c) _
    exact hE_gt_L _ h0_mem
  · rw [hrecip]
    have h_image : Finset.image (⇑g) Finset.univ = E :=
      E.image_orderEmbOfFin_univ (by rfl : E.card = c)
    rw [← h_image]
    rw [Finset.sum_image (fun a _ b _ hab => g.injective hab)]
    symm
    apply Finset.sum_equiv (Fin.castOrderIso hc_succ).toEquiv
    · intro i
      simp
    · intro i _
      rfl
  · rw [hsum]
    have h_image : Finset.image (⇑g) Finset.univ = E :=
      E.image_orderEmbOfFin_univ (by rfl : E.card = c)
    rw [← h_image]
    rw [Finset.sum_image (fun a _ b _ hab => g.injective hab)]
    symm
    apply Finset.sum_equiv (Fin.castOrderIso hc_succ).toEquiv
    · intro i
      simp
    · intro i _
      rfl

lemma witness_of_fintype_denominators (α : ℚ) (L m : ℕ) (p : ℚ[X])
    {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℕ)
    (hd_inj : Function.Injective d) (hd_gt_L : ∀ i, L < d i)
    (hrecip : α = ∑ i : ι, (1 : ℚ) / (d i : ℚ))
    (hsum : (m : ℚ) = ∑ i : ι, p.eval ((d i : ℕ) : ℚ)) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  classical
  let E : Finset ℕ := Finset.univ.image d
  have hE_nonempty : E.Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨d i, by simp [E]⟩
  have hE_gt_L : ∀ n ∈ E, L < n := by
    intro n hn
    simp [E] at hn
    obtain ⟨i, _, rfl⟩ := hn
    exact hd_gt_L i
  have hE_recip : α = ∑ n ∈ E, (1 : ℚ) / (n : ℚ) := by
    rw [hrecip]
    dsimp [E]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hd_inj hab
  have hE_sum : (m : ℚ) = ∑ n ∈ E, p.eval ((n : ℕ) : ℚ) := by
    rw [hsum]
    dsimp [E]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hd_inj hab
  exact witness_of_denominator_finset α L m p E hE_nonempty hE_gt_L hE_recip hE_sum

lemma witness_from_selected_subsets {α : ℚ} {L : ℕ} (p : ℚ[X])
    (hp : IntValued p) {md : MainChoice α L p hp}
    {gcd : MainGCDData p hp md} (corr : CorrectionData p hp gcd)
    (fill : FillerData p hp corr) {N m : ℕ}
    {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N)
    (hcorr_pos : ∀ ν, 0 < corr.c ν)
    (hden_inj :
      Function.Injective
        (finalIndexDenom :
          FinalIndex corr fill N S T → ℕ))
    (hden_gt_L :
      ∀ i : FinalIndex corr fill N S T, L < finalIndexDenom i)
    (hpsum :
      (m : ℚ) =
        (baseInt p hp corr fill N : ℚ) +
        (∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) +
        (∑ ν ∈ T, ((corr.b ν : ℤ) : ℚ))) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  classical
  haveI : Nonempty (FinalIndex corr fill N S T) :=
    ⟨Sum.inl (Sum.inr PUnit.unit)⟩
  have hrecip : α = ∑ i : FinalIndex corr fill N S T,
      (1 : ℚ) / (finalIndexDenom i : ℚ) := by
    exact (finalIndex_recip_sum corr fill hJN hS hcorr_pos).symm
  have hp_eval_sum :
      (m : ℚ) = ∑ i : FinalIndex corr fill N S T,
        p.eval ((finalIndexDenom i : ℕ) : ℚ) := by
    rw [← intEval_fintype_sum_cast p hp
      (finalIndexDenom : FinalIndex corr fill N S T → ℕ)]
    rw [finalIndex_intEval_sum p hp corr fill hS hcorr_pos]
    push_cast
    exact hpsum
  exact witness_of_fintype_denominators α L m p
    (finalIndexDenom : FinalIndex corr fill N S T → ℕ)
    hden_inj hden_gt_L hrecip hp_eval_sum

lemma finalIndex_denoms_gt_L {α : ℚ} {L : ℕ} {p : ℚ[X]} {hp : IntValued p}
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    {N : ℕ} {S : Finset ℕ} {T : Finset (Fin corr.t)}
    (hJN : md.J ≤ N) (hS : S ⊆ Finset.Icc md.J N) :
    ∀ i : FinalIndex corr fill N S T, L < finalIndexDenom i := by
  intro i
  rcases i with (((j | sw) | tauIdx) | ((ν | csw) | f))
  · -- Unswitched main denominator `D j`.
    have hj_mem : j.1 ∈ Finset.Icc md.J N := by
      exact (Finset.mem_sdiff.mp j.2).1
    have hjJ : md.J ≤ j.1 := (Finset.mem_Icc.mp hj_mem).1
    have hDj_ge : D md.J ≤ D j.1 := D_strictMono.monotone hjJ
    exact lt_of_lt_of_le md.hD_gt_L hDj_ge
  · -- Switched main denominator `n ∈ {2D j,3D j,6D j}`.
    have hj_mem : sw.1.1 ∈ Finset.Icc md.J N := hS sw.1.2
    have hjJ : md.J ≤ sw.1.1 := (Finset.mem_Icc.mp hj_mem).1
    have hDj_ge : D md.J ≤ D sw.1.1 := D_strictMono.monotone hjJ
    have hDj_gt : L < D sw.1.1 := lt_of_lt_of_le md.hD_gt_L hDj_ge
    have hn_mem := sw.2.2
    simp only [scaledPatternDenoms, Finset.mem_image] at hn_mem
    obtain ⟨e, he, heq⟩ := hn_mem
    have he_one : 1 ≤ e := by
      have he_two := (isEgyptianPattern_E0.1 e he)
      omega
    change L < sw.2.1
    rw [← heq]
    calc
      L < D sw.1.1 := hDj_gt
      _ = 1 * D sw.1.1 := by ring
      _ ≤ e * D sw.1.1 := Nat.mul_le_mul_right _ he_one
  · -- Endpoint `τ N`.
    have htau_ge : tau md.J ≤ tau N := tau_strictMono.monotone hJN
    exact lt_of_lt_of_le md.htau_base_gt_L htau_ge
  · -- Unswitched correction denominator `cν`.
    exact corr.c_gt_L ν.1
  · -- Switched correction denominator `n ∈ scaledPatternDenoms Gν cν`.
    have hc_gt : L < corr.c csw.1.1 := corr.c_gt_L csw.1.1
    have hn_mem := csw.2.2
    simp only [scaledPatternDenoms, Finset.mem_image] at hn_mem
    obtain ⟨e, he, heq⟩ := hn_mem
    have he_one : 1 ≤ e := by
      have he_two := (corr.hG csw.1.1).1 e he
      omega
    change L < csw.2.1
    rw [← heq]
    calc
      L < corr.c csw.1.1 := hc_gt
      _ = 1 * corr.c csw.1.1 := by ring
      _ ≤ e * corr.c csw.1.1 := Nat.mul_le_mul_right _ he_one
  · -- Filler denominator `Λ f`.
    have hf_one : 1 ≤ f.1 := fill.hF_pos f.1 f.2
    calc
      L < fill.Λ := fill.hΛ_gt_L
      _ = fill.Λ * 1 := by ring
      _ ≤ fill.Λ * f.1 := Nat.mul_le_mul_left _ hf_one

lemma attainable_interval_core {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (X_q : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (N m : ℕ) (U : ℤ) (hJN : md.J ≤ N)
    (h_tail : ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ U →
      ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (hlo :
      baseInt p hp corr fill N + Bstar p hp corr +
        M0 p hp gcd X_q ≤ (m : ℤ))
    (hhi : (m : ℤ) ≤ baseInt p hp corr fill N + U)
    (hcollision : ∀ (T : Finset (Fin corr.t)) (S : Finset ℕ),
      S ⊆ Finset.Icc md.J N →
      Function.Injective
        (finalIndexDenom :
          FinalIndex corr fill N S T → ℕ)) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  classical
  obtain ⟨T, S, hS, hpsum⟩ :=
    select_subsets_from_rsg_interval p hp corr fill X_q hX_q N U (m : ℤ)
      hJN h_tail hlo hhi
  have hcorr_pos : ∀ ν, 0 < corr.c ν := by
    intro ν
    exact lt_of_le_of_lt (Nat.zero_le L) (corr.c_gt_L ν)
  have hpsum_nat :
      (m : ℚ) =
        (baseInt p hp corr fill N : ℚ) +
        (∑ j ∈ S,
          ((intEval (A p) (A_intValued p hp) ((D j : ℕ) : ℤ) : ℤ) : ℚ)) +
        (∑ ν ∈ T, ((corr.b ν : ℤ) : ℚ)) := by
    exact_mod_cast hpsum
  exact witness_from_selected_subsets p hp corr fill hJN hS hcorr_pos
    (hcollision T S hS) (finalIndex_denoms_gt_L corr fill hJN hS) hpsum_nat

lemma attainable_interval {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)
    {md : MainChoice α L p hp} {gcd : MainGCDData p hp md}
    (corr : CorrectionData p hp gcd) (fill : FillerData p hp corr)
    (X_q : ℤ)
    (hX_q : ∀ X : ℤ, X_q ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (N m : ℕ) (U : ℤ) (hJN : md.J ≤ N)
    (hτ : correctionMultiplierMax corr < tau N)
    (h_tail : ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ U →
      ∀ i : ℕ, N - md.J < i →
      (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ))
    (hlo :
      baseInt p hp corr fill N + Bstar p hp corr +
        M0 p hp gcd X_q ≤ (m : ℤ))
    (hhi : (m : ℤ) ≤ baseInt p hp corr fill N + U) :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
      StrictMono n ∧ (L < n 0) ∧
      (α = ∑ i, (1 : ℚ) / (n i)) ∧
      ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  exact attainable_interval_core p hp corr fill X_q hX_q N m U hJN h_tail hlo hhi
    (fun T S hS => finalIndexDenom_injective corr fill hS hτ)

lemma integer_intervals_cover_tail (lo hi : ℕ → ℤ) (N₀ : ℕ)
    (hoverlap : ∀ N, N₀ ≤ N → lo (N + 1) ≤ hi N + 1)
    (hhi_unbounded : ∀ m : ℤ, ∃ N, N₀ ≤ N ∧ m ≤ hi N) :
    ∀ m : ℤ, lo N₀ ≤ m →
      ∃ N, N₀ ≤ N ∧ lo N ≤ m ∧ m ≤ hi N := by
  classical
  intro m hmlo
  let P : ℕ → Prop := fun N => N₀ ≤ N ∧ m ≤ hi N
  have hP : ∃ N, P N := hhi_unbounded m
  let N : ℕ := Nat.find hP
  have hN : P N := Nat.find_spec hP
  by_cases hbase : N = N₀
  · refine ⟨N, hN.1, ?_, hN.2⟩
    simpa [hbase] using hmlo
  · have hN₀_lt : N₀ < N := lt_of_le_of_ne hN.1 (Ne.symm hbase)
    let K : ℕ := N - 1
    have hK_succ : K + 1 = N := by
      dsimp [K]
      have hN_pos : 0 < N := lt_of_le_of_lt (Nat.zero_le N₀) hN₀_lt
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hN_pos)
    have hK_lt : K < N := by
      rw [← hK_succ]
      exact Nat.lt_succ_self K
    have hK_ge : N₀ ≤ K := by
      rw [← hK_succ] at hN₀_lt
      omega
    have hnotK : ¬ P K := Nat.find_min hP hK_lt
    have hhiK_lt : hi K < m := by
      by_contra hle
      push_neg at hle
      exact hnotK ⟨hK_ge, hle⟩
    have hloN : lo N ≤ hi K + 1 := by
      rw [← hK_succ]
      exact hoverlap K hK_ge
    have hle_m : hi K + 1 ≤ m := by omega
    refine ⟨N, hN.1, ?_, hN.2⟩
    exact le_trans hloN hle_m

/-! ### Quotient-gcd bridge reference statement

If `g` is the positive generator of `Ideal.span (mainValueSet p hp md.J)`,
then the quotient values `(qPoly p md.J g).eval (t : ℚ)` (for `t ≥ 1`)
generate the unit ideal in `ℤ`. Equivalently, no prime `ℓ` divides every
quotient value.

Mathematically: `g = gcd { A(D j) : j ≥ J }` by construction. Dividing the
spanning set by `g` gives values whose gcd is 1, so no prime divides them
all. RSG's `h_gcd_one` hypothesis is exactly this.

The full proof is implemented in `chooseMainGCDData`; the definition below
keeps the target statement shape available by name. -/
section MainQuotBridge

variable {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)

/-- Statement-shape for the quotient-gcd bridge proved inside
`chooseMainGCDData`. -/
def mainQuot_no_prime_fixed_stmt (md : MainChoice α L p hp) (g : ℕ)
    (_ : 1 ≤ g) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime →
    ∃ t : ℕ, 1 ≤ t ∧ ∃ z : ℤ,
      (z : ℚ) = (qPoly p md.J g).eval (t : ℚ) ∧
      ¬ ((ℓ : ℤ) ∣ z)

end MainQuotBridge

set_option linter.unusedVariables false in
/-- **Main theorem (PDF Theorem 1).** For `α ∈ ℚ_{>0}`, `L ≥ 1`, and a polynomial
`p ∈ ℚ[x]` integer-valued with positive leading coefficient and no fixed
divisor on positive integers, all sufficiently large integers `m` admit an
expression as `∑ p(n_i)` with distinct `L < n_1 < ⋯ < n_k` and `∑ 1/n_i = α`.

The proof combines:
  * `egyptian_expansion` (Lemma 3) for filler denominators
  * `egyptian_pattern_with_period` (Lemma 4) used by Lemma 6
  * `polynomial_periodicity` (Lemma 5) used by Lemma 6 and the correction slots
  * `switching_values_span_top` (Lemma 6) for the residue-correction trick
  * `roth_szekeres_graham` (axiom) applied to `q := A ∘ Dpoly / g`
  * Telescoping `D j` reciprocals via `main_telescoping`
  * Collision avoidance via `padicValNat` profiles

with the explicit constants `P := 36`, `D j := u j · u (j+1)`, `u j := P j + 1`,
`τ N := P u_{N+1}`, `E0 := {2, 3, 6}`, `A := switchingPoly p E0`. -/
theorem theorem_1 (α : ℚ) (hα : 0 < α) (L : ℕ) (hL : 1 ≤ L) (p : ℚ[X])
    (hp : IntValued p)
    (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : NoFixedDivisor p hp) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
        StrictMono n ∧ (L < n 0) ∧
        (α = ∑ i, (1 : ℚ) / (n i)) ∧
        ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  by_cases hd : p.natDegree = 0
  case pos =>
    -- CONSTANT CASE: p = C c with c = 1 (forced by NoFixedDivisor).
    -- Reduce to egyptian_expansion.
    -- Step 1: p = C (p.coeff 0).
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
    -- Step 2: leading coefficient is p.coeff 0.
    have h_lead_eq : p.leadingCoeff = p.coeff 0 := by
      rw [Polynomial.leadingCoeff, hd]
    have h_c_pos : 0 < p.coeff 0 := h_lead_eq ▸ h_lead_pos
    set c : ℚ := p.coeff 0 with hc_def
    -- Step 3: p.eval z = c for all z.
    have h_eval_const : ∀ z : ℚ, p.eval z = c := by
      intro z; rw [hpC]; simp
    -- Step 4: extract integer value c_int with (c_int : ℚ) = c.
    obtain ⟨c_int, hc_int⟩ := hp 0
    have h_eval_zero : p.eval ((0 : ℤ) : ℚ) = c := h_eval_const _
    have hc_int_eq : (c_int : ℚ) = c := by rw [hc_int, h_eval_zero]
    have h_intEval_const : ∀ z : ℤ, intEval p hp z = c_int := by
      intro z
      have h1 : ((intEval p hp z : ℤ) : ℚ) = p.eval (z : ℚ) := intEval_spec p hp z
      have h2 : p.eval ((z : ℤ) : ℚ) = c := h_eval_const _
      have h3 : ((intEval p hp z : ℤ) : ℚ) = (c_int : ℚ) := by rw [h1, h2, hc_int_eq]
      exact_mod_cast h3
    have h_c_int_pos : 0 < c_int := by
      have : (0 : ℚ) < (c_int : ℚ) := by rw [hc_int_eq]; exact h_c_pos
      exact_mod_cast this
    -- Step 5: c_int = 1, forced by NoFixedDivisor.
    have h_c_int_one : c_int = 1 := by
      by_contra h_ne
      have h_ge_two : 2 ≤ c_int := by
        rcases lt_or_ge c_int 2 with hlt | hge
        · interval_cases c_int
          · exact absurd rfl h_ne
        · exact hge
      set d : ℕ := c_int.toNat with hd_def
      have hd_eq : (d : ℤ) = c_int := Int.toNat_of_nonneg (le_of_lt h_c_int_pos)
      have hd_ge : 2 ≤ d := by
        have : (2 : ℤ) ≤ (d : ℤ) := by rw [hd_eq]; exact h_ge_two
        exact_mod_cast this
      apply h_no_fixed_div d hd_ge
      intro n _
      rw [h_intEval_const n, hd_eq]
    -- Step 6: p.eval z = 1 for all z (rational).
    have h_eval_one : ∀ z : ℚ, p.eval z = 1 := by
      intro z
      rw [h_eval_const z, ← hc_int_eq, h_c_int_one]
      simp
    -- Step 7: get K from egyptian_expansion.
    obtain ⟨K, hK⟩ := egyptian_expansion α hα L
    refine ⟨max K 1, ?_⟩
    intro m hm
    have hmK : K ≤ m := le_of_max_le_left hm
    have hm1 : 1 ≤ m := le_of_max_le_right hm
    obtain ⟨E, hE_card, hE_lb, hE_sum⟩ := hK m hmK
    -- Step 8: enumerate E as a strictly monotone function Fin m → ℕ.
    let g : Fin m ↪o ℕ := E.orderEmbOfFin hE_card
    -- We need a function Fin (k + 1) → ℕ with k = m - 1 such that k + 1 = m.
    have hm_succ : m - 1 + 1 = m := Nat.sub_add_cancel hm1
    refine ⟨m - 1, fun i => g (Fin.cast hm_succ i), ?_, ?_, ?_, ?_⟩
    · -- StrictMono
      intro i j hij
      apply g.strictMono
      exact Fin.cast_lt_cast hm_succ |>.mpr hij
    · -- L < n 0
      have h0_in : g (Fin.cast hm_succ 0) ∈ E := E.orderEmbOfFin_mem hE_card _
      exact hE_lb _ h0_in
    · -- α = ∑ i, 1 / n i
      rw [hE_sum]
      -- Sum over Fin (m - 1 + 1) of 1 / g (Fin.cast hm_succ i) equals sum over E of 1 / e.
      have h_image : Finset.image (⇑g) Finset.univ = E :=
        E.image_orderEmbOfFin_univ hE_card
      rw [← h_image]
      rw [Finset.sum_image (fun a _ b _ hab => g.injective hab)]
      -- Reindex from Fin m to Fin (m - 1 + 1) using the equivalence Fin.cast hm_succ.symm.
      symm
      apply Finset.sum_equiv (Fin.castOrderIso hm_succ).toEquiv
      · intro i; simp
      · intro i _; rfl
    · -- m = ∑ i, p.eval (n i)
      simp only [h_eval_one]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [hm_succ]
      simp
  case neg =>
    -- POLYNOMIAL CASE: 1 ≤ p.natDegree (since hd : p.natDegree ≠ 0).
    have h_nonconst : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hd
    -- Step 1: choose J via chooseMainChoice (asymptotic threshold).
    obtain ⟨md⟩ := chooseMainChoice α hα L p hp h_nonconst h_lead_pos
    -- Step 2: extract g via chooseMainGCDData (gcd of A(D j) values + bridge).
    obtain ⟨gcd⟩ := chooseMainGCDData p hp h_nonconst h_lead_pos md
    -- Step 3: apply RSG to qPoly to get the window representation.
    obtain ⟨X_q, hX_q⟩ := main_window_representation p hp h_nonconst h_lead_pos md gcd
    -- Step 4: choose correction data. The `g = 1` branch is empty; for
    -- `g ≥ 2` use finite switching generators, duplicated subset sums, and
    -- large collision-free denominators.
    have hcorr_nonempty : Nonempty (CorrectionData p hp gcd) := by
      by_cases hg1 : gcd.g = 1
      · exact chooseCorrectionData_g_eq_one p hp gcd hg1
      · have hg2 : 2 ≤ gcd.g := by
          have hgpos := gcd.hg_pos
          omega
        exact chooseCorrectionData_g_ge_two p hp gcd h_nonconst h_lead_pos
          h_no_fixed_div hg2
    obtain ⟨corr⟩ := hcorr_nonempty
    -- Step 5: choose the fixed filler denominators after the correction mass.
    obtain ⟨fill⟩ := chooseFillerData p hp corr
    obtain ⟨Nτ, hNτ⟩ := correctionMultiplierMax_lt_tau_eventually corr
    obtain ⟨Nt, hNt⟩ := qPoly_tail_eventually p hp h_nonconst h_lead_pos gcd X_q
    obtain ⟨No, hNo⟩ :=
      intervals_overlap_eventually p hp h_nonconst h_lead_pos corr fill X_q
    let Nbase : ℕ := max (max (max md.J Nτ) Nt) No
    have hJ_base : md.J ≤ Nbase := by
      dsimp [Nbase]
      omega
    have hτ_base : Nτ ≤ Nbase := by
      dsimp [Nbase]
      omega
    have ht_base : Nt ≤ Nbase := by
      dsimp [Nbase]
      omega
    have ho_base : No ≤ Nbase := by
      dsimp [Nbase]
      omega
    have hoverlap :
        ∀ N : ℕ, Nbase ≤ N →
          lowerInt p hp corr fill X_q (N + 1) ≤
            upperEdge p hp corr fill N + 1 := by
      intro N hN
      exact hNo N (le_trans ho_base hN)
    have hunbounded :
        ∀ M : ℤ, ∃ N, Nbase ≤ N ∧ M ≤ upperEdge p hp corr fill N :=
      upperEdge_unbounded p hp h_nonconst h_lead_pos corr fill Nbase
    let m₀ : ℕ := (lowerInt p hp corr fill X_q Nbase).toNat
    refine ⟨m₀, ?_⟩
    intro m hm
    have hmlo_base :
        lowerInt p hp corr fill X_q Nbase ≤ (m : ℤ) := by
      have hlo_toNat :
          lowerInt p hp corr fill X_q Nbase ≤ (m₀ : ℤ) := by
        dsimp [m₀]
        exact Int.self_le_toNat _
      exact le_trans hlo_toNat (by exact_mod_cast hm)
    obtain ⟨N, hNbase, hlo, hhi⟩ :=
      integer_intervals_cover_tail
        (fun N => lowerInt p hp corr fill X_q N)
        (fun N => upperEdge p hp corr fill N)
        Nbase hoverlap hunbounded (m : ℤ) hmlo_base
    have hJN : md.J ≤ N := le_trans hJ_base hNbase
    have hτN : correctionMultiplierMax corr < tau N :=
      hNτ N (le_trans hτ_base hNbase)
    have htailN :
        ∀ X : ℤ, X_q ≤ X → ((gcd.g : ℤ) * X) ≤ upperInt p N →
          ∀ i : ℕ, N - md.J < i →
            (X : ℚ) < (qPoly p md.J gcd.g).eval ((i + 1 : ℕ) : ℚ) :=
      hNt N (le_trans ht_base hNbase)
    exact attainable_interval p hp corr fill X_q hX_q N m (upperInt p N)
      hJN hτN htailN
      (by simpa [lowerInt] using hlo)
      (by simpa [upperEdge] using hhi)

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/Corollary351.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — §3 Corollary 7 (strong completeness, #351).

Three cases:

  * `corollary_7_zero`             — `p = 0`: every positive integer is a sum
                                      of distinct unit reciprocals (Lemma 3).
  * `corollary_7_pos_leading`      — `p ≠ 0` with positive leading coefficient:
                                      reduce to integer polynomial `q := Dp/h`,
                                      apply `theorem_1` for each residue
                                      `r ∈ {1, …, h}`.
  * `not_strongly_complete_of_neg_leadingCoeff` — `p` has negative leading
                                                   coefficient: bounded above,
                                                   so not strongly complete
                                                   (optional; FC #351 doesn't
                                                   need it).
-/


namespace PolynomialEgyptianSums

open Polynomial Filter

/-- The set `A_p = { p(n) + 1/n : n ∈ ℕ }` for `p ∈ ℚ[x]`. (Note: `1/0 = 0` in
`ℚ`, so `A_p` includes `p(0)` — harmless per the FC convention.) -/
def imageSet (p : ℚ[X]) : Set ℚ :=
  Set.range (fun (n : ℕ) ↦ p.eval (n : ℚ) + 1 / (n : ℚ))

/-- `A ⊆ ℚ` is **strongly complete** if every sufficiently large natural number
is a finite subset-sum of `A \ B` for any finite `B`. -/
def IsStronglyComplete (A : Set ℚ) : Prop :=
  ∀ B : Finset ℚ,
    ∀ᶠ (m : ℕ) in Filter.atTop,
      ((m : ℕ) : ℚ) ∈ { ∑ x ∈ X, x | (X : Finset ℚ) (_ : (↑X : Set ℚ) ⊆ A \ ↑B) }

/-! ## Case `p = 0` -/

/-- **Corollary 7, case `p = 0`.** `A_0 = {1/n : n ∈ ℕ}` is strongly complete:
every positive integer is a sum of distinct unit reciprocals (Lemma 3). -/
theorem corollary_7_zero : IsStronglyComplete (imageSet 0) := by
  classical
  intro B
  rw [Filter.eventually_atTop]
  -- Pick `L` large enough that `1/e ∉ B` for all `e > L`.
  set L := (insert 0 (B.image (fun b => b.den))).max'
    (Finset.insert_nonempty 0 _) with hL_def
  have hL_avoid : ∀ e : ℕ, L < e → (1 : ℚ) / e ∉ B := by
    intro e he hb
    have he_pos : 1 ≤ e := by omega
    have h_den : ((1 : ℚ) / e).den = e := by
      rw [one_div, Rat.inv_natCast_den_of_pos he_pos]
    have h_mem_image : e ∈ B.image (fun b => b.den) := by
      rw [Finset.mem_image]
      exact ⟨(1 : ℚ) / e, hb, h_den⟩
    have h_mem_insert : e ∈ (insert 0 (B.image (fun b => b.den))) := by
      rw [Finset.mem_insert]; exact Or.inr h_mem_image
    have h_le : e ≤ L := Finset.le_max' _ e h_mem_insert
    omega
  -- For `m ≥ 1`, apply Lemma 3 with `R = m` and our `L`.
  refine ⟨1, ?_⟩
  intro m hm
  have hm_pos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  obtain ⟨K, hK⟩ := egyptian_expansion (m : ℚ) hm_pos L
  obtain ⟨E, _hE_card, hE_lb, hE_sum⟩ := hK K (le_refl K)
  -- Build `X = E.image (fun e => 1/e)`.
  refine ⟨E.image (fun e : ℕ => (1 : ℚ) / (e : ℚ)), ?_, ?_⟩
  · -- ↑X ⊆ imageSet 0 \ ↑B
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have he_lb := hE_lb e he
    refine ⟨?_, ?_⟩
    · -- 1/e ∈ imageSet 0 since (0 : ℚ[X]).eval e + 1/e = 1/e
      refine ⟨e, ?_⟩
      simp [Polynomial.eval_zero]
    · exact hL_avoid e he_lb
  · -- ∑ x ∈ X, x = ↑m
    have h_inj : Set.InjOn (fun e : ℕ => (1 : ℚ) / (e : ℚ)) (E : Set ℕ) := by
      intro a ha b hb hab
      have ha_pos : 1 ≤ a := by have := hE_lb a ha; omega
      have hb_pos : 1 ≤ b := by have := hE_lb b hb; omega
      simp only [one_div] at hab
      have h1 : (a : ℚ) = (b : ℚ) := inv_inj.mp hab
      exact_mod_cast h1
    rw [Finset.sum_image h_inj]
    exact hE_sum.symm

/-! ## Case positive leading coefficient -/

set_option maxHeartbeats 800000

/-! ### Helper lemmas for `corollary_7_pos_leading` -/

/-- `IntValued (C D * p)` whenever `D · p` has integer coefficients. The
witness at `z : ℤ` is `R.eval z` where `R : ℤ[X]` is the integer multiple. -/
private lemma intValued_C_mul_of_HasIntegralMultiple (D : ℕ) (p : ℚ[X])
    (hDp : HasIntegralMultiple D p) :
    IntValued (Polynomial.C (D : ℚ) * p) := by
  obtain ⟨R, hR⟩ := hDp
  intro z
  refine ⟨R.eval z, ?_⟩
  have h1 : ((R.map (Int.castRingHom ℚ)).eval ((z : ℤ) : ℚ)) =
      (Polynomial.C (D : ℚ) * p).eval ((z : ℚ)) := by
    rw [hR]
  rw [Polynomial.eval_map] at h1
  have h2 : Polynomial.eval₂ (Int.castRingHom ℚ) ((z : ℤ) : ℚ) R =
      ((R.eval z : ℤ) : ℚ) := Polynomial.eval₂_at_apply (Int.castRingHom ℚ) z
  rw [h2] at h1
  exact h1

/-- `IntValued (C ((h : ℚ)⁻¹) * (C D * p))` whenever `D · p` is integer-valued
and `h ∣ (D · p).eval z` (as ℤ) for every `z : ℤ`. -/
private lemma intValued_C_inv_mul (h : ℕ) (hh_pos : 1 ≤ h) (Dp : ℚ[X])
    (hDp_int : IntValued Dp)
    (h_dvd : ∀ z : ℤ, (h : ℤ) ∣ intEval Dp hDp_int z) :
    IntValued (Polynomial.C ((h : ℚ)⁻¹) * Dp) := by
  intro z
  obtain ⟨k, hk⟩ := h_dvd z
  refine ⟨k, ?_⟩
  -- (k : ℚ) = (Dp.eval z) / h, since Dp.eval z = h · k.
  have hDpk : (intEval Dp hDp_int z : ℚ) = (h : ℚ) * (k : ℚ) := by
    have : ((intEval Dp hDp_int z : ℤ) : ℚ) = (((h : ℤ) * k : ℤ) : ℚ) := by
      rw [hk]
    push_cast at this; exact this
  have h_eval := intEval_spec Dp hDp_int z
  have hh_ne : (h : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh_pos
    exact ne_of_gt this
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  -- Goal: (k : ℚ) = (h : ℚ)⁻¹ * Dp.eval (z : ℚ).
  rw [← h_eval, hDpk]
  field_simp

/-- **Mahler / finite-differences extension of fixed divisor.** If `q : ℚ[X]` is
integer-valued and `d ∣ q(n)` for every positive integer `n`, then `d ∣ q(w)` for
every integer `w`. The proof uses that the `(N+1)`-th forward difference of a
degree-`N` polynomial vanishes, giving a recurrence that lets us extend
divisibility from `ℕ_{≥1}` to all of `ℤ`. -/
private lemma intValued_dvd_extends_to_int (q : ℚ[X]) (hq_int : IntValued q)
    (d : ℕ)
    (hdvd_pos : ∀ n : ℕ, 1 ≤ n → (d : ℤ) ∣ intEval q hq_int (n : ℤ)) :
    ∀ w : ℤ, (d : ℤ) ∣ intEval q hq_int w := by
  set N : ℕ := q.natDegree
  -- Step 1: (N+1)-th forward difference recurrence in ℤ at integer points.
  have h_recur : ∀ y : ℤ,
      ∑ k ∈ Finset.range (N + 2),
        ((-1 : ℤ) ^ (N + 1 - k) * ((N + 1).choose k)) •
          intEval q hq_int (y + (k : ℤ)) = 0 := by
    intro y
    -- Apply Polynomial.fwdDiff_iter_eq_zero_of_degree_lt to q.eval at (y : ℚ).
    have hq_zero : (fwdDiff (1 : ℚ))^[N + 1] (fun x => q.eval x) ((y : ℤ) : ℚ) = 0 := by
      have hP := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := q) (n := N + 1)
        (Nat.lt_succ_self _)
      exact congr_fun hP ((y : ℤ) : ℚ)
    rw [fwdDiff_iter_eq_sum_shift] at hq_zero
    -- Each term in ℚ is the cast of an integer term.
    have hsum_eq :
        ∑ k ∈ Finset.range (N + 2),
            ((-1 : ℤ) ^ (N + 1 - k) * ((N + 1).choose k)) •
              q.eval (((y : ℤ) : ℚ) + k • (1 : ℚ)) =
        (((∑ k ∈ Finset.range (N + 2),
            ((-1 : ℤ) ^ (N + 1 - k) * ((N + 1).choose k)) •
              intEval q hq_int (y + (k : ℤ))) : ℤ) : ℚ) := by
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro k _
      have h1 : ((y : ℤ) : ℚ) + k • (1 : ℚ) = ((y + (k : ℤ) : ℤ) : ℚ) := by
        push_cast; ring
      rw [h1, ← intEval_spec q hq_int (y + (k : ℤ))]
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one, Int.cast_natCast]
    rw [hsum_eq] at hq_zero
    exact_mod_cast hq_zero
  -- Step 2: Isolate `intEval q hq_int y` from the recurrence.
  have h_dvd_smul : ∀ y : ℤ,
      (∀ k : ℕ, k ∈ Finset.range (N + 1) →
        (d : ℤ) ∣ intEval q hq_int (y + ((k : ℤ) + 1))) →
      (d : ℤ) ∣ intEval q hq_int y := by
    intro y hk_dvd
    have h_recur_y := h_recur y
    -- Split sum: k = 0 term and k ≥ 1 terms.
    rw [Finset.sum_range_succ' _ (N + 1)] at h_recur_y
    -- Now h_recur_y has form: (sum over k ∈ range (N+1)) + (k=0 term) = 0.
    -- The (k=0) term: ((-1)^(N+1-0) * (N+1).choose 0) • intEval q hq_int (y + 0).
    have h_y_simp : intEval q hq_int (y + ((0 : ℕ) : ℤ)) = intEval q hq_int y := by
      norm_num
    have h_k_simp : ∀ k : ℕ,
        intEval q hq_int (y + ((k + 1 : ℕ) : ℤ)) =
          intEval q hq_int (y + ((k : ℤ) + 1)) := by
      intro k
      push_cast
      rfl
    -- Rewrite into a uniform form.
    have h_recur_y' :
        ∑ k ∈ Finset.range (N + 1),
            ((-1 : ℤ) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1))) •
              intEval q hq_int (y + ((k : ℤ) + 1)) +
        ((-1 : ℤ) ^ (N + 1)) * intEval q hq_int y = 0 := by
      have := h_recur_y
      simp only [smul_eq_mul, h_y_simp, Nat.choose_zero_right, Nat.cast_one,
        mul_one, Nat.sub_zero] at this
      have hsum_congr :
          ∑ x ∈ Finset.range (N + 1),
              (-1 : ℤ) ^ (N + 1 - (x + 1)) * ((N + 1).choose (x + 1)) *
                intEval q hq_int (y + ((x + 1 : ℕ) : ℤ)) =
          ∑ k ∈ Finset.range (N + 1),
              ((-1 : ℤ) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1))) •
                intEval q hq_int (y + ((k : ℤ) + 1)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [smul_eq_mul, h_k_simp k]
      linarith [hsum_congr ▸ this]
    have h_dvd_sum : (d : ℤ) ∣
        ∑ k ∈ Finset.range (N + 1),
          ((-1 : ℤ) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1))) •
            intEval q hq_int (y + ((k : ℤ) + 1)) := by
      apply Finset.dvd_sum
      intro k hk
      rw [smul_eq_mul]
      exact dvd_mul_of_dvd_right (hk_dvd k hk) _
    -- From h_recur_y', (-1)^(N+1) * intEval q hq_int y = -(sum).
    have h_main : ((-1 : ℤ) ^ (N + 1)) * intEval q hq_int y =
        - ∑ k ∈ Finset.range (N + 1),
          ((-1 : ℤ) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1))) •
            intEval q hq_int (y + ((k : ℤ) + 1)) := by linarith
    have h_dvd_pow : (d : ℤ) ∣ ((-1 : ℤ) ^ (N + 1)) * intEval q hq_int y := by
      rw [h_main]
      exact h_dvd_sum.neg_right
    -- Multiply by (-1)^(N+1) to extract intEval q hq_int y. ((-1)^(N+1))^2 = 1.
    have h_sq : ((-1 : ℤ) ^ (N + 1)) * ((-1 : ℤ) ^ (N + 1)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have h_recover :
        ((-1 : ℤ) ^ (N + 1)) * (((-1 : ℤ) ^ (N + 1)) * intEval q hq_int y) =
          intEval q hq_int y := by
      rw [← mul_assoc, h_sq, one_mul]
    rw [← h_recover]
    exact Dvd.dvd.mul_left h_dvd_pow _
  -- Step 3: Prove `(d : ℤ) ∣ intEval q hq_int (- (m : ℤ))` by strong induction on m.
  have h_neg : ∀ m : ℕ, (d : ℤ) ∣ intEval q hq_int (- (m : ℤ)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      apply h_dvd_smul
      intro k hk
      have hk_lt : k < N + 1 := Finset.mem_range.mp hk
      -- Argument: -m + (k + 1).
      by_cases h_pos : 1 ≤ -(m : ℤ) + ((k : ℤ) + 1)
      · -- Argument positive: use hdvd_pos.
        let n : ℕ := (-(m : ℤ) + ((k : ℤ) + 1)).toNat
        have hn : (n : ℤ) = -(m : ℤ) + ((k : ℤ) + 1) :=
          Int.toNat_of_nonneg (by linarith)
        have hn_pos : 1 ≤ n := by
          have h_one_le : (1 : ℤ) ≤ (n : ℤ) := by rw [hn]; exact h_pos
          exact_mod_cast h_one_le
        rw [show (-(m : ℤ) + ((k : ℤ) + 1) : ℤ) = (n : ℤ) from hn.symm]
        exact hdvd_pos n hn_pos
      · -- Argument ≤ 0: write as -(j : ℤ) for some j < m.
        push_neg at h_pos
        let j : ℕ := ((m : ℤ) - ((k : ℤ) + 1)).toNat
        have h_nonneg : 0 ≤ ((m : ℤ) - ((k : ℤ) + 1)) := by linarith
        have hj_cast : (j : ℤ) = (m : ℤ) - ((k : ℤ) + 1) :=
          Int.toNat_of_nonneg h_nonneg
        have hj_eq : -(m : ℤ) + ((k : ℤ) + 1) = -(j : ℤ) := by
          rw [hj_cast]; ring
        have hj_lt : j < m := by
          have hjm : (j : ℤ) < (m : ℤ) := by rw [hj_cast]; linarith
          exact_mod_cast hjm
        rw [hj_eq]
        exact ih j hj_lt
  -- Step 4: Conclude for arbitrary w : ℤ.
  intro w
  by_cases hw_pos : 1 ≤ w
  · -- w ≥ 1: directly from hdvd_pos.
    let n : ℕ := w.toNat
    have hn : (n : ℤ) = w := Int.toNat_of_nonneg (by linarith)
    have hn_pos : 1 ≤ n := by
      have h_one_le : (1 : ℤ) ≤ (n : ℤ) := by rw [hn]; exact hw_pos
      exact_mod_cast h_one_le
    rw [show w = (n : ℤ) from hn.symm]
    exact hdvd_pos n hn_pos
  · -- w ≤ 0: use h_neg.
    push_neg at hw_pos
    let m : ℕ := (-w).toNat
    have hm : (m : ℤ) = -w := Int.toNat_of_nonneg (by linarith)
    have hw_eq : w = -(m : ℤ) := by linarith
    rw [hw_eq]
    exact h_neg m

/-- **Corollary 7, positive-leading case.** For `p` with positive leading
coefficient, `A_p` is strongly complete.

Reduction (uniform in `natDegree p`): scale to `q := D·p/h` where `D` is the
common denominator of `p`'s coefficients and `h := gcd { (D·p)(n) : n ∈ ℤ }`,
making `q` integer-valued, fixed-divisor-free, and positive-leading. For each
`m`, take `M := (D·m - 1) / h, r := D·m - h·M ∈ {1, …, h}` (Euclidean
division), then apply `theorem_1` to `q` with `α := (r : ℚ) / D`. The
identity `∑ (p(n_i) + 1/n_i) = (h/D) ∑ q(n_i) + ∑ 1/n_i = hM/D + r/D = m`
recovers the imageSet form. -/
theorem corollary_7_pos_leading (p : ℚ[X])
    (h_lead_pos : 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := by
  classical
  intro B
  rw [Filter.eventually_atTop]
  -- Step 1: Choose D from `exists_integral_multiple`. Get IntValued (C D * p).
  obtain ⟨D, hD_pos, hDp_mult⟩ := exists_integral_multiple p
  set Dp : ℚ[X] := Polynomial.C (D : ℚ) * p with hDp_def
  have hD_ne_q : (D : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    exact ne_of_gt this
  have hDp_int : IntValued Dp :=
    intValued_C_mul_of_HasIntegralMultiple D p hDp_mult
  -- Dp.leadingCoeff = D * p.leadingCoeff > 0.
  have hDp_lead_pos : 0 < Dp.leadingCoeff := by
    rw [hDp_def, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    exact mul_pos hD_pos_q h_lead_pos
  -- Dp.natDegree = p.natDegree.
  have hDp_natDegree : Dp.natDegree = p.natDegree := by
    rw [hDp_def]
    exact Polynomial.natDegree_C_mul hD_ne_q
  -- Step 2: Extract h := gcd of (Dp.eval z : ℤ) for z ∈ ℤ via Ideal.span.
  set valSet : Set ℤ := { z : ℤ | ∃ w : ℤ, z = intEval Dp hDp_int w } with hvalSet_def
  set I : Ideal ℤ := Ideal.span valSet with hI_def
  haveI hI_principal : Submodule.IsPrincipal I := IsPrincipalIdealRing.principal I
  set z₀ : ℤ := Submodule.IsPrincipal.generator I with hz₀_def
  set h : ℕ := z₀.natAbs with hh_def
  have hI_span : Ideal.span ({z₀} : Set ℤ) = I :=
    Submodule.IsPrincipal.span_singleton_generator I
  -- Each value Dp.eval(w) is in valSet, hence in I.
  have h_val_in_I : ∀ w : ℤ, intEval Dp hDp_int w ∈ I := fun w =>
    Ideal.subset_span ⟨w, rfl⟩
  -- Eventually positive: since Dp has positive leading coeff and integer values,
  -- some value is positive (giving a positive ideal element, hence h ≥ 1).
  have h_some_pos : ∃ w : ℤ, 0 < intEval Dp hDp_int w := by
    set Dpr : ℝ[X] := Dp.map (algebraMap ℚ ℝ) with hDpr_def
    have h_inj : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
      (algebraMap ℚ ℝ).injective
    have hDpr_lead : (0 : ℝ) < Dpr.leadingCoeff := by
      rw [hDpr_def, Polynomial.leadingCoeff_map_of_injective h_inj]
      have : (0 : ℝ) < (Dp.leadingCoeff : ℝ) := by exact_mod_cast hDp_lead_pos
      simpa [algebraMap] using this
    by_cases hDp_const : Dp.natDegree = 0
    · -- Dp = C c for some c. Since lc > 0, c > 0.
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hDp_const
      have hlc : Dp.leadingCoeff = Dp.coeff 0 := by
        rw [Polynomial.leadingCoeff, hDp_const]
      have hc_pos : 0 < Dp.coeff 0 := hlc ▸ hDp_lead_pos
      refine ⟨0, ?_⟩
      have h_eval : Dp.eval ((0 : ℤ) : ℚ) = Dp.coeff 0 := by
        rw [hpC]; simp
      have h_intEval := intEval_spec Dp hDp_int 0
      rw [h_eval] at h_intEval
      have h_pos_q : (0 : ℚ) < ((intEval Dp hDp_int 0 : ℤ) : ℚ) := by
        rw [h_intEval]; exact hc_pos
      exact_mod_cast h_pos_q
    · -- Dp.natDegree ≥ 1. Take w large.
      have hd_pos : 0 < Dp.natDegree := Nat.pos_of_ne_zero hDp_const
      have hDpr_deg_pos : 0 < Dpr.degree := by
        have hnat : 0 < Dpr.natDegree := by
          rw [hDpr_def, Polynomial.natDegree_map_eq_of_injective h_inj]
          exact hd_pos
        exact Polynomial.natDegree_pos_iff_degree_pos.mp hnat
      have h_tendsto : Filter.Tendsto (fun x : ℝ => Dpr.eval x) Filter.atTop Filter.atTop :=
        Polynomial.tendsto_atTop_of_leadingCoeff_nonneg Dpr hDpr_deg_pos hDpr_lead.le
      obtain ⟨N0, hN0⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto 1
      set w : ℕ := Nat.ceil (max N0 0) + 1 with hw_def
      have hw_real_ge_N0 : N0 ≤ (w : ℝ) := by
        have h1 : N0 ≤ max N0 0 := le_max_left _ _
        have h2 : (max N0 0) ≤ (Nat.ceil (max N0 0) : ℝ) := Nat.le_ceil _
        have h3 : ((Nat.ceil (max N0 0) : ℕ) : ℝ) ≤ (w : ℝ) := by
          rw [hw_def]; push_cast; linarith
        linarith
      have h_eval_real : 1 ≤ Dpr.eval (w : ℝ) := hN0 _ hw_real_ge_N0
      have h_eval_cast : Dpr.eval (w : ℝ) = ((Dp.eval (w : ℚ) : ℚ) : ℝ) := by
        rw [hDpr_def]
        have h1 : ((w : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((w : ℕ) : ℚ) := by
          simp [algebraMap]
        rw [h1, Polynomial.eval_map_apply]; simp [algebraMap]
      have h_eval_q : 1 ≤ Dp.eval ((w : ℕ) : ℚ) := by
        have : ((1 : ℚ) : ℝ) ≤ ((Dp.eval ((w : ℕ) : ℚ) : ℚ) : ℝ) := by
          rw [show ((1 : ℚ) : ℝ) = (1 : ℝ) by norm_num, ← h_eval_cast]; exact h_eval_real
        exact_mod_cast this
      refine ⟨(w : ℤ), ?_⟩
      have h_intEval := intEval_spec Dp hDp_int (w : ℤ)
      have h_cast_eq : ((w : ℤ) : ℚ) = ((w : ℕ) : ℚ) := by push_cast; rfl
      rw [h_cast_eq] at h_intEval
      have h_pos_q : (0 : ℚ) < ((intEval Dp hDp_int (w : ℤ) : ℤ) : ℚ) := by
        rw [h_intEval]; linarith
      exact_mod_cast h_pos_q
  obtain ⟨w_pos, hw_pos⟩ := h_some_pos
  have hI_ne_bot : I ≠ ⊥ := by
    intro h_bot
    have hmem : intEval Dp hDp_int w_pos ∈ (⊥ : Ideal ℤ) := by
      rw [← h_bot]; exact h_val_in_I w_pos
    rw [Ideal.mem_bot] at hmem
    omega
  have hz₀_ne : z₀ ≠ 0 := by
    intro hz0
    apply hI_ne_bot
    rw [Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero, ← hz₀_def]
    exact hz0
  have hh_pos : 1 ≤ h := by
    have : 0 < h := Int.natAbs_pos.mpr hz₀_ne
    omega
  have hh_pos_q : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh_pos
  have hh_ne_q : (h : ℚ) ≠ 0 := ne_of_gt hh_pos_q
  -- h ∣ Dp.eval w (as ℤ) for every w.
  have hh_dvd : ∀ w : ℤ, (h : ℤ) ∣ intEval Dp hDp_int w := by
    intro w
    have hmem : intEval Dp hDp_int w ∈ I := h_val_in_I w
    rw [← hI_span, Ideal.mem_span_singleton] at hmem
    rw [hh_def, Int.natAbs_dvd]
    exact hmem
  -- Step 3: Define q := C ((h : ℚ)⁻¹) * Dp.
  set q : ℚ[X] := Polynomial.C ((h : ℚ)⁻¹) * Dp with hq_def
  have hq_int : IntValued q := intValued_C_inv_mul h hh_pos Dp hDp_int hh_dvd
  -- q.natDegree = p.natDegree.
  have hh_inv_ne : ((h : ℚ)⁻¹) ≠ 0 := by
    rw [ne_eq, inv_eq_zero]; exact hh_ne_q
  have hq_natDegree : q.natDegree = p.natDegree := by
    rw [hq_def, Polynomial.natDegree_C_mul hh_inv_ne, hDp_natDegree]
  -- q.leadingCoeff = (D / h) * p.leadingCoeff > 0.
  have hq_lead_pos : 0 < q.leadingCoeff := by
    rw [hq_def, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    have h_inv_pos : (0 : ℚ) < (h : ℚ)⁻¹ := inv_pos.mpr hh_pos_q
    exact mul_pos h_inv_pos hDp_lead_pos
  -- q.eval = Dp.eval / h.
  have hq_eval : ∀ z : ℚ, q.eval z = Dp.eval z / (h : ℚ) := by
    intro z
    rw [hq_def, Polynomial.eval_mul, Polynomial.eval_C]
    field_simp
  -- For w ∈ ℤ, intEval q hq_int w * h = intEval Dp hDp_int w (as ℤ).
  have hq_intEval : ∀ w : ℤ,
      (h : ℤ) * intEval q hq_int w = intEval Dp hDp_int w := by
    intro w
    have h1 := intEval_spec q hq_int w
    have h2 := intEval_spec Dp hDp_int w
    have h3 : (((h : ℤ) * intEval q hq_int w : ℤ) : ℚ) =
        ((intEval Dp hDp_int w : ℤ) : ℚ) := by
      push_cast
      rw [h1, hq_eval, h2]
      field_simp
    exact_mod_cast h3
  -- Step 4: NoFixedDivisor q.
  have hq_no_fixed : NoFixedDivisor q hq_int := by
    intro d hd hdvd
    -- If d ∣ q.eval n for all n ≥ 1, then by Mahler/finite-differences, d ∣ q.eval z
    -- for all z ∈ ℤ. Then (d * h) ∣ Dp.eval z for all z, so I ⊆ ⟨d*h⟩, hence d*h ∣ z₀,
    -- but |z₀| = h, forcing d ∣ 1, contradicting d ≥ 2.
    -- Mahler / finite-differences extension of fixed divisor from ℕ_{≥1} to ℤ.
    have hdvd_all : ∀ w : ℤ, (d : ℤ) ∣ intEval q hq_int w :=
      intValued_dvd_extends_to_int q hq_int d hdvd
    -- Now (d * h : ℤ) ∣ Dp.eval w for all w.
    have hdh_dvd_all : ∀ w : ℤ, ((d : ℤ) * (h : ℤ)) ∣ intEval Dp hDp_int w := by
      intro w
      rw [← hq_intEval w]
      obtain ⟨k, hk⟩ := hdvd_all w
      refine ⟨k, ?_⟩
      rw [hk]; ring
    have hI_le : I ≤ Ideal.span ({(d : ℤ) * (h : ℤ)} : Set ℤ) := by
      rw [hI_def]
      apply Ideal.span_le.mpr
      intro x hx
      obtain ⟨w, hx_eq⟩ := hx
      show x ∈ Ideal.span ({(d : ℤ) * (h : ℤ)} : Set ℤ)
      rw [Ideal.mem_span_singleton, hx_eq]
      exact hdh_dvd_all w
    have hz₀_mem_I : z₀ ∈ I := Submodule.IsPrincipal.generator_mem I
    have hdh_dvd_z₀ : ((d : ℤ) * (h : ℤ)) ∣ z₀ := by
      have hz_in : z₀ ∈ Ideal.span ({(d : ℤ) * (h : ℤ)} : Set ℤ) := hI_le hz₀_mem_I
      rwa [Ideal.mem_span_singleton] at hz_in
    have hh_pos_int : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh_pos
    have hd_ge_two_int : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    rcases Int.natAbs_eq z₀ with hpos | hneg
    · have hz_eq : z₀ = (h : ℤ) := by rw [hpos, hh_def]
      rw [hz_eq] at hdh_dvd_z₀
      rcases hdh_dvd_z₀ with ⟨k, hk⟩
      have hh_ne_int : (h : ℤ) ≠ 0 := ne_of_gt hh_pos_int
      have hk' : (1 : ℤ) = d * k := by
        have : (h : ℤ) * 1 = (h : ℤ) * (d * k) := by linarith
        exact mul_left_cancel₀ hh_ne_int this
      have hd_dvd_one : (d : ℤ) ∣ 1 := ⟨k, hk'⟩
      have h_le : (d : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hd_dvd_one
      omega
    · have hz_eq : z₀ = -(h : ℤ) := by rw [hneg, hh_def]
      rw [hz_eq] at hdh_dvd_z₀
      have hdh_dvd_h : ((d : ℤ) * (h : ℤ)) ∣ (h : ℤ) := by
        rcases hdh_dvd_z₀ with ⟨k, hk⟩
        refine ⟨-k, ?_⟩; linarith
      rcases hdh_dvd_h with ⟨k, hk⟩
      have hh_ne_int : (h : ℤ) ≠ 0 := ne_of_gt hh_pos_int
      have hk' : (1 : ℤ) = d * k := by
        have : (h : ℤ) * 1 = (h : ℤ) * (d * k) := by linarith
        exact mul_left_cancel₀ hh_ne_int this
      have hd_dvd_one : (d : ℤ) ∣ 1 := ⟨k, hk'⟩
      have h_le : (d : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hd_dvd_one
      omega
  -- Step 5: Choose L with two properties:
  --   (a) for n > L, p.eval n + 1/n ∉ B;
  --   (b) for n₁, n₂ > L, p.eval n₁ + 1/n₁ = p.eval n₂ + 1/n₂ → n₁ = n₂.
  have hL_exists : ∃ L : ℕ, 1 ≤ L ∧
      (∀ n : ℕ, L < n → p.eval (n : ℚ) + 1 / (n : ℚ) ∉ B) ∧
      (∀ n₁ n₂ : ℕ, L < n₁ → L < n₂ →
        p.eval (n₁ : ℚ) + 1 / (n₁ : ℚ) = p.eval (n₂ : ℚ) + 1 / (n₂ : ℚ) → n₁ = n₂) := by
    by_cases hd : p.natDegree = 0
    case pos =>
      -- p = C c, value c + 1/n. Take L > all bad denominators.
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hd
      have hlc : p.leadingCoeff = p.coeff 0 := by
        rw [Polynomial.leadingCoeff, hd]
      set c : ℚ := p.coeff 0 with hc_def
      have hc_pos : 0 < c := hlc ▸ h_lead_pos
      have h_eval_const : ∀ z : ℚ, p.eval z = c := by
        intro z; rw [hpC]; simp
      let bad_n : ℚ → ℕ := fun b => (b - c).den
      let bad_set : Finset ℕ := B.image bad_n
      let L : ℕ := max 1 (bad_set.sup id + 1)
      refine ⟨L, le_max_left _ _, ?_, ?_⟩
      · intro n hn hb
        rw [h_eval_const] at hb
        have hn_pos : 0 < n := by
          have : 1 ≤ n := by
            have h_le_max : 1 ≤ L := le_max_left _ _
            omega
          omega
        have hn_pos_q : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn_pos
        set b' : ℚ := c + 1 / (n : ℚ) with hb'_def
        have hb'_mem : b' ∈ B := hb
        have h_b'_minus_c : b' - c = 1 / (n : ℚ) := by rw [hb'_def]; ring
        have h_den : (b' - c).den = n := by
          rw [h_b'_minus_c, one_div]
          exact Rat.inv_natCast_den_of_pos hn_pos
        have h_b'_in_bad : bad_n b' ∈ bad_set := Finset.mem_image.mpr ⟨b', hb'_mem, rfl⟩
        have h_bad_eq : bad_n b' = n := h_den
        have h_n_le_sup : n ≤ bad_set.sup id := by
          rw [← h_bad_eq]
          exact Finset.le_sup (f := id) h_b'_in_bad
        have h_L_lb : bad_set.sup id + 1 ≤ L := le_max_right _ _
        omega
      · intro n₁ n₂ hn₁ hn₂ h_eq
        rw [h_eval_const, h_eval_const] at h_eq
        have h1 : (1 : ℚ) / (n₁ : ℚ) = 1 / (n₂ : ℚ) := by linarith
        have hn₁_pos : 0 < n₁ := by
          have : 1 ≤ n₁ := by
            have : 1 ≤ L := le_max_left _ _
            omega
          omega
        have hn₂_pos : 0 < n₂ := by
          have : 1 ≤ n₂ := by
            have : 1 ≤ L := le_max_left _ _
            omega
          omega
        have hn₁_pos_q : (0 : ℚ) < (n₁ : ℚ) := by exact_mod_cast hn₁_pos
        have hn₂_pos_q : (0 : ℚ) < (n₂ : ℚ) := by exact_mod_cast hn₂_pos
        rw [one_div, one_div, inv_inj] at h1
        exact_mod_cast h1
    case neg =>
      -- natDegree p ≥ 1. p.eval n + 1/n → ∞.
      have hd_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hd
      have hp_ne : p ≠ 0 := by
        intro hpz; rw [hpz, Polynomial.leadingCoeff_zero] at h_lead_pos
        exact lt_irrefl _ h_lead_pos
      set pr : ℝ[X] := p.map (algebraMap ℚ ℝ) with hpr_def
      have h_inj_qr : Function.Injective ((algebraMap ℚ ℝ) : ℚ →+* ℝ) :=
        (algebraMap ℚ ℝ).injective
      have hpr_lead : (0 : ℝ) < pr.leadingCoeff := by
        rw [hpr_def, Polynomial.leadingCoeff_map_of_injective h_inj_qr]
        have : (0 : ℝ) < (p.leadingCoeff : ℝ) := by exact_mod_cast h_lead_pos
        simpa [algebraMap] using this
      have hpr_natDeg_pos : 0 < pr.natDegree := by
        rw [hpr_def, Polynomial.natDegree_map_eq_of_injective h_inj_qr]
        exact hd_pos
      have hpr_deg_pos : 0 < pr.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp hpr_natDeg_pos
      have h_tendsto : Filter.Tendsto (fun x : ℝ => pr.eval x) Filter.atTop Filter.atTop :=
        Polynomial.tendsto_atTop_of_leadingCoeff_nonneg pr hpr_deg_pos hpr_lead.le
      set Bmax : ℝ := if hB : B.Nonempty then ((B.image fun b : ℚ => (b : ℝ)).max' (Finset.Nonempty.image hB _)) else 0
      obtain ⟨N₀, hN₀⟩ := Filter.tendsto_atTop_atTop.mp h_tendsto (Bmax + 2)
      -- Strict monotonicity threshold via derivative bound.
      -- We seek N₁ such that pr.derivative.eval x ≥ pr.leadingCoeff/2 for x ≥ N₁.
      set c_half : ℝ := pr.leadingCoeff / 2 with hc_half_def
      have hc_half_pos : 0 < c_half := by rw [hc_half_def]; linarith
      have h_deriv_natDeg : pr.derivative.natDegree = pr.natDegree - 1 := by
        rw [show pr.derivative = (Polynomial.hasseDeriv 1) pr from
              (Polynomial.hasseDeriv_one' pr).symm]
        exact Polynomial.natDegree_hasseDeriv pr 1
      have h_deriv_lb : ∃ N₁ : ℝ, ∀ x ≥ N₁, c_half ≤ pr.derivative.eval x := by
        by_cases h_nd1 : pr.natDegree = 1
        · -- pr.derivative is the constant pr.leadingCoeff.
          refine ⟨0, fun x _ => ?_⟩
          have hd_natDeg : pr.derivative.natDegree = 0 := by
            rw [h_deriv_natDeg, h_nd1]
          have h_pr_deriv_C : pr.derivative = Polynomial.C pr.derivative.leadingCoeff := by
            have := Polynomial.eq_C_of_natDegree_eq_zero hd_natDeg
            convert this using 1
            rw [Polynomial.leadingCoeff, hd_natDeg]
          have h_lead_eq : pr.derivative.leadingCoeff = pr.leadingCoeff := by
            rw [Polynomial.leadingCoeff, hd_natDeg, Polynomial.coeff_derivative,
                Polynomial.leadingCoeff, h_nd1]
            ring
          rw [h_pr_deriv_C, Polynomial.eval_C, h_lead_eq, hc_half_def]
          linarith
        · -- pr.natDegree ≥ 2; use tendsto.
          have h_nd_ge_two : 2 ≤ pr.natDegree := by omega
          have h_deriv_natDeg_pos : 0 < pr.derivative.natDegree := by
            rw [h_deriv_natDeg]; omega
          have h_deriv_deg_pos : 0 < pr.derivative.degree :=
            Polynomial.natDegree_pos_iff_degree_pos.mp h_deriv_natDeg_pos
          have h_deriv_lead_pos : 0 < pr.derivative.leadingCoeff := by
            rw [Polynomial.leadingCoeff, h_deriv_natDeg, Polynomial.coeff_derivative]
            have h1 : pr.natDegree - 1 + 1 = pr.natDegree := by omega
            rw [h1, Polynomial.coeff_natDegree]
            have h2 : (0 : ℝ) < ((pr.natDegree - 1 : ℕ) : ℝ) + 1 := by
              have : (0 : ℝ) ≤ ((pr.natDegree - 1 : ℕ) : ℝ) := by
                exact_mod_cast Nat.zero_le _
              linarith
            exact mul_pos hpr_lead h2
          have h_deriv_t : Filter.Tendsto (fun x : ℝ => pr.derivative.eval x)
              Filter.atTop Filter.atTop :=
            Polynomial.tendsto_atTop_of_leadingCoeff_nonneg pr.derivative
              h_deriv_deg_pos h_deriv_lead_pos.le
          obtain ⟨N₁, hN₁⟩ := Filter.tendsto_atTop_atTop.mp h_deriv_t c_half
          exact ⟨N₁, hN₁⟩
      obtain ⟨N₁, hN₁⟩ := h_deriv_lb
      -- For n₁, n₂ > L (with L large enough), the strict comparison holds.
      -- We need L ≥ ⌈max N₀ 0⌉ + 1 (for the avoid part)
      --        L ≥ ⌈max N₁ 0⌉ + 1 (so [L, ∞) ⊂ [N₁, ∞), where deriv ≥ c_half)
      --        L ≥ ⌈1/c_half⌉ + 1 (so for n₁, n₂ > L, n₁ * n₂ > 1/c_half, hence
      --           c_half * (n₂ - n₁) > (n₂ - n₁)/(n₁ n₂) = 1/n₁ - 1/n₂).
      let L : ℕ := max (max 1 (Nat.ceil (max N₀ 0) + 1))
                       (max (Nat.ceil (max N₁ 0) + 1) (Nat.ceil (1/c_half) + 1))
      refine ⟨L, ?_, ?_, ?_⟩
      · -- 1 ≤ L
        have h1 : 1 ≤ max 1 (Nat.ceil (max N₀ 0) + 1) := le_max_left _ _
        have h2 : max 1 (Nat.ceil (max N₀ 0) + 1) ≤ L := le_max_left _ _
        omega
      · intro n hn hb
        have h_part1 : max 1 (Nat.ceil (max N₀ 0) + 1) ≤ L := le_max_left _ _
        have hn_ge : (Nat.ceil (max N₀ 0) + 1) ≤ n := by
          have h_max_right : Nat.ceil (max N₀ 0) + 1 ≤ max 1 (Nat.ceil (max N₀ 0) + 1) :=
            le_max_right _ _
          omega
        have hn_pos : 0 < n := by
          have h1L : 1 ≤ max 1 (Nat.ceil (max N₀ 0) + 1) := le_max_left _ _
          omega
        have h1 : (Nat.ceil (max N₀ 0) : ℝ) ≥ N₀ := by
          have hN0_le_max : N₀ ≤ max N₀ 0 := le_max_left _ _
          have h_le_ceil : (max N₀ 0) ≤ (Nat.ceil (max N₀ 0) : ℝ) := Nat.le_ceil _
          linarith
        have h2 : N₀ ≤ (n : ℝ) := by
          have : (Nat.ceil (max N₀ 0) + 1 : ℕ) ≤ n := hn_ge
          have h3 : ((Nat.ceil (max N₀ 0) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
          push_cast at h3
          linarith
        have h_eval_real : Bmax + 2 ≤ pr.eval (n : ℝ) := hN₀ _ h2
        have h_eval_cast : pr.eval ((n : ℕ) : ℝ) = ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
          rw [hpr_def]
          have h1 : ((n : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((n : ℕ) : ℚ) := by simp [algebraMap]
          rw [h1, Polynomial.eval_map_apply]; simp [algebraMap]
        have h_p_eval_real : Bmax + 2 ≤ ((p.eval ((n : ℕ) : ℚ) : ℚ) : ℝ) := by
          rw [← h_eval_cast]; exact h_eval_real
        set v_p : ℚ := Polynomial.eval ((n : ℕ) : ℚ) p with hv_p_def
        set v_inv : ℚ := 1 / ((n : ℕ) : ℚ) with hv_inv_def
        have h_p_eval_real' : Bmax + 2 ≤ (v_p : ℝ) := h_p_eval_real
        have hb_le_Bmax : ((v_p + v_inv : ℚ) : ℝ) ≤ Bmax := by
          have hB_ne : B.Nonempty := ⟨_, hb⟩
          simp only [Bmax]
          rw [dif_pos hB_ne]
          apply Finset.le_max'
          simp only [Finset.mem_image]
          exact ⟨_, hb, rfl⟩
        have h1_le : (v_inv : ℝ) ≤ 1 := by
          have hn_pos_q : (0 : ℚ) < ((n : ℕ) : ℚ) := by exact_mod_cast hn_pos
          have h_q_le : v_inv ≤ 1 := by
            rw [hv_inv_def, div_le_one hn_pos_q]
            have : 1 ≤ (n : ℕ) := hn_pos
            exact_mod_cast this
          exact_mod_cast h_q_le
        have h_inv_pos : 0 ≤ (v_inv : ℝ) := by
          have hn_pos_q : (0 : ℚ) < ((n : ℕ) : ℚ) := by exact_mod_cast hn_pos
          have : (0 : ℚ) ≤ v_inv := by rw [hv_inv_def]; positivity
          exact_mod_cast this
        have h_split : ((v_p + v_inv : ℚ) : ℝ) = (v_p : ℝ) + (v_inv : ℝ) := by push_cast; ring
        rw [h_split] at hb_le_Bmax
        linarith
      · -- Injectivity for n > L, nonconstant case.
        -- For a < b, both > L, we show p.eval a + 1/a ≠ p.eval b + 1/b.
        -- Mean-value gives pr.eval b - pr.eval a ≥ c_half * (b - a).
        -- Meanwhile 1/a - 1/b = (b - a)/(a * b), and a * b > 1/c_half so
        -- 1/(a * b) < c_half, hence (b - a)/(a * b) < c_half * (b - a).
        -- Therefore pr.eval a + 1/a < pr.eval b + 1/b, contradicting equality.
        have hL_lb_N₁ : (Nat.ceil (max N₁ 0) + 1) ≤ L := by
          have h1 : Nat.ceil (max N₁ 0) + 1 ≤
              max (Nat.ceil (max N₁ 0) + 1) (Nat.ceil (1/c_half) + 1) := le_max_left _ _
          have h2 : max (Nat.ceil (max N₁ 0) + 1) (Nat.ceil (1/c_half) + 1) ≤ L := le_max_right _ _
          omega
        have hL_lb_inv : (Nat.ceil (1/c_half) + 1) ≤ L := by
          have h1 : Nat.ceil (1/c_half) + 1 ≤
              max (Nat.ceil (max N₁ 0) + 1) (Nat.ceil (1/c_half) + 1) := le_max_right _ _
          have h2 : max (Nat.ceil (max N₁ 0) + 1) (Nat.ceil (1/c_half) + 1) ≤ L := le_max_right _ _
          omega
        have hL_lb_one : 1 ≤ L := by
          have h1 : 1 ≤ max 1 (Nat.ceil (max N₀ 0) + 1) := le_max_left _ _
          have h2 : max 1 (Nat.ceil (max N₀ 0) + 1) ≤ L := le_max_left _ _
          omega
        -- Helper: for a < b, both > L, evaluation values differ.
        have helper : ∀ a b : ℕ, L < a → L < b → a < b →
            p.eval ((a : ℕ) : ℚ) + 1 / ((a : ℕ) : ℚ) ≠
              p.eval ((b : ℕ) : ℚ) + 1 / ((b : ℕ) : ℚ) := by
          intro a b ha hb hab heq
          have ha_pos : 1 ≤ a := by omega
          have hb_pos : 1 ≤ b := by omega
          have ha_real_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pos
          have hb_real_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
          have ha_le_b_real : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
          have h_ceil_ge_N₁ : (Nat.ceil (max N₁ 0) : ℝ) ≥ N₁ := by
            have h1 : N₁ ≤ max N₁ 0 := le_max_left _ _
            have h2 : (max N₁ 0) ≤ (Nat.ceil (max N₁ 0) : ℝ) := Nat.le_ceil _
            linarith
          have h_a_ge_N₁ : N₁ ≤ (a : ℝ) := by
            have h1 : (Nat.ceil (max N₁ 0) + 1 : ℕ) ≤ a := by omega
            have h2 : ((Nat.ceil (max N₁ 0) + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
            push_cast at h2
            linarith
          have h_b_ge_N₁ : N₁ ≤ (b : ℝ) := by
            have h1 : (Nat.ceil (max N₁ 0) + 1 : ℕ) ≤ b := by omega
            have h2 : ((Nat.ceil (max N₁ 0) + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast h1
            push_cast at h2
            linarith
          have h_deriv_lb_real : ∀ x ∈ interior (Set.Ici N₁),
              c_half ≤ Polynomial.eval x pr.derivative := by
            intro x hx
            simp only [interior_Ici, Set.mem_Ioi] at hx
            exact hN₁ x hx.le
          have h_pr_diffOn_int : DifferentiableOn ℝ (fun x : ℝ => pr.eval x)
              (interior (Set.Ici N₁)) := pr.differentiable.differentiableOn
          have h_pr_contOn : ContinuousOn (fun x : ℝ => pr.eval x) (Set.Ici N₁) :=
            pr.continuous.continuousOn
          have h_deriv_eq : ∀ x : ℝ, deriv (fun x : ℝ => pr.eval x) x = pr.derivative.eval x :=
            fun x => pr.deriv
          -- Mean-value: c_half * (b - a) ≤ pr.eval b - pr.eval a.
          have h_mvt : c_half * ((b : ℝ) - (a : ℝ)) ≤
              pr.eval (b : ℝ) - pr.eval (a : ℝ) := by
            apply (convex_Ici N₁).mul_sub_le_image_sub_of_le_deriv
                h_pr_contOn h_pr_diffOn_int
            · intro x hx
              rw [h_deriv_eq]
              exact h_deriv_lb_real x hx
            · exact h_a_ge_N₁
            · exact h_b_ge_N₁
            · exact ha_le_b_real
          -- Cast heq to ℝ.
          have h_eq_real : pr.eval (a : ℝ) + 1/(a : ℝ) = pr.eval (b : ℝ) + 1/(b : ℝ) := by
            have h_eval_cast_a : pr.eval ((a : ℕ) : ℝ) = ((p.eval ((a : ℕ) : ℚ) : ℚ) : ℝ) := by
              rw [hpr_def]
              have h1 : ((a : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((a : ℕ) : ℚ) := by simp [algebraMap]
              rw [h1, Polynomial.eval_map_apply]; simp [algebraMap]
            have h_eval_cast_b : pr.eval ((b : ℕ) : ℝ) = ((p.eval ((b : ℕ) : ℚ) : ℚ) : ℝ) := by
              rw [hpr_def]
              have h1 : ((b : ℕ) : ℝ) = (algebraMap ℚ ℝ) ((b : ℕ) : ℚ) := by simp [algebraMap]
              rw [h1, Polynomial.eval_map_apply]; simp [algebraMap]
            have h_lhs : pr.eval ((a : ℕ) : ℝ) + 1/((a : ℕ) : ℝ) =
                ((p.eval ((a : ℕ) : ℚ) + 1/((a : ℕ) : ℚ) : ℚ) : ℝ) := by
              rw [h_eval_cast_a]; push_cast; ring
            have h_rhs : pr.eval ((b : ℕ) : ℝ) + 1/((b : ℕ) : ℝ) =
                ((p.eval ((b : ℕ) : ℚ) + 1/((b : ℕ) : ℚ) : ℚ) : ℝ) := by
              rw [h_eval_cast_b]; push_cast; ring
            rw [h_lhs, h_rhs]
            exact_mod_cast heq
          -- pr.eval b - pr.eval a = 1/a - 1/b.
          have h_diff_eq : pr.eval (b : ℝ) - pr.eval (a : ℝ) = 1/(a : ℝ) - 1/(b : ℝ) := by
            linarith
          -- 1/a - 1/b = (b - a) / (a * b).
          have h_inv_diff : 1/(a : ℝ) - 1/(b : ℝ) =
              ((b : ℝ) - (a : ℝ)) / ((a : ℝ) * (b : ℝ)) := by field_simp
          -- a * b > 1/c_half (since a > Nat.ceil (1/c_half) ≥ 1/c_half and b ≥ 1).
          have h_a_ge_inv_c : 1 / c_half < (a : ℝ) := by
            have h1 : (Nat.ceil (1/c_half) : ℝ) ≥ 1/c_half := Nat.le_ceil _
            have h2 : (Nat.ceil (1/c_half) + 1 : ℕ) ≤ a := by omega
            have h3 : ((Nat.ceil (1/c_half) + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h2
            push_cast at h3
            linarith
          have h_a_b_pos : 0 < (a : ℝ) * (b : ℝ) := mul_pos ha_real_pos hb_real_pos
          have h_a_b_gt : 1 / c_half < (a : ℝ) * (b : ℝ) := by
            have hb_ge_one : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb_pos
            have h1 : (a : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
              calc (a : ℝ) = (a : ℝ) * 1 := by ring
                _ ≤ (a : ℝ) * (b : ℝ) :=
                  mul_le_mul_of_nonneg_left hb_ge_one ha_real_pos.le
            linarith
          have h_inv_lt_c : 1 / ((a : ℝ) * (b : ℝ)) < c_half := by
            rw [div_lt_iff₀ h_a_b_pos]
            rw [div_lt_iff₀ hc_half_pos] at h_a_b_gt
            linarith
          -- Strict: (b - a) / (a * b) < c_half * (b - a).
          have h_diff_pos : 0 < (b : ℝ) - (a : ℝ) := by
            have : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
            linarith
          have h_strict : ((b : ℝ) - (a : ℝ)) / ((a : ℝ) * (b : ℝ)) <
              c_half * ((b : ℝ) - (a : ℝ)) := by
            have h1 := mul_lt_mul_of_pos_right h_inv_lt_c h_diff_pos
            have h2 : 1 / ((a : ℝ) * (b : ℝ)) * ((b : ℝ) - (a : ℝ)) =
                ((b : ℝ) - (a : ℝ)) / ((a : ℝ) * (b : ℝ)) := by ring
            linarith
          -- Combine: c_half * (b - a) ≤ (b - a)/(a*b) < c_half * (b - a) — contradiction.
          have h_contra : c_half * ((b : ℝ) - (a : ℝ)) ≤
              ((b : ℝ) - (a : ℝ)) / ((a : ℝ) * (b : ℝ)) := by
            rw [← h_inv_diff]
            linarith
          linarith
        -- Now apply trichotomy.
        intro n₁ n₂ hn₁ hn₂ h_eq
        rcases lt_trichotomy n₁ n₂ with h_lt | h_neq | h_gt
        · exact absurd h_eq (helper n₁ n₂ hn₁ hn₂ h_lt)
        · exact h_neq
        · exact absurd h_eq.symm (helper n₂ n₁ hn₂ hn₁ h_gt)
  obtain ⟨L, hL_pos, hL_avoid, hL_inj⟩ := hL_exists
  -- Step 6: For each residue r ∈ {1, …, h}, get m₀_r from theorem_1 with α := (r : ℚ)/D.
  have hα_pos : ∀ r : ℕ, 1 ≤ r → r ≤ h → (0 : ℚ) < (r : ℚ) / (D : ℚ) := by
    intro r hr1 _
    have hr_pos : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr1
    have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    exact div_pos hr_pos hD_pos_q
  have h_apply_thm1 : ∀ r : ℕ, 1 ≤ r → r ≤ h →
      ∃ m₀_r : ℕ, ∀ M : ℕ, m₀_r ≤ M →
        ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
          StrictMono n ∧ (L < n 0) ∧
          ((r : ℚ) / (D : ℚ) = ∑ i, (1 : ℚ) / (n i)) ∧
          ((M : ℚ) = ∑ i, q.eval ((n i : ℕ) : ℚ)) := by
    intro r hr1 hr_le_h
    exact theorem_1 ((r : ℚ) / (D : ℚ)) (hα_pos r hr1 hr_le_h) L hL_pos
      q hq_int hq_lead_pos hq_no_fixed
  classical
  let mthresh : ℕ → ℕ := fun r =>
    if hr : 1 ≤ r ∧ r ≤ h then
      (h_apply_thm1 r hr.1 hr.2).choose
    else
      0
  set m₀_base : ℕ := (Finset.Icc 1 h).sup mthresh with hm₀_base_def
  set m₀ : ℕ := h * (m₀_base + 1) + 1 with hm₀_def
  refine ⟨m₀, ?_⟩
  intro m hm_ge
  have hDm_pos : 1 ≤ D * m := by
    have : 1 ≤ m := by
      have : 1 ≤ m₀ := by rw [hm₀_def]; omega
      omega
    have : 0 < D * m := Nat.mul_pos hD_pos this
    omega
  set M : ℕ := (D * m - 1) / h with hM_def
  set r : ℕ := D * m - h * M with hr_def
  have hr_pos : 1 ≤ r := by
    rw [hr_def, hM_def]
    have h1 : (D * m - 1) / h * h ≤ D * m - 1 := Nat.div_mul_le_self _ _
    have h2 : h * ((D * m - 1) / h) = (D * m - 1) / h * h := by ring
    omega
  have hr_le : r ≤ h := by
    rw [hr_def, hM_def]
    have h1 := Nat.div_add_mod (D * m - 1) h
    have h2 : (D * m - 1) % h < h := Nat.mod_lt _ (by omega)
    have h3 : (D * m - 1) - h * ((D * m - 1) / h) = (D * m - 1) % h := by
      have h4 : (D * m - 1) / h * h ≤ D * m - 1 := Nat.div_mul_le_self _ _
      have h5 : h * ((D * m - 1) / h) = (D * m - 1) / h * h := by ring
      omega
    omega
  have hD_eq : D * m = h * M + r := by
    rw [hr_def]
    have h_div_le : h * M ≤ D * m := by
      rw [hM_def]
      have h1 : (D * m - 1) / h * h ≤ D * m - 1 := Nat.div_mul_le_self _ _
      have h2 : h * ((D * m - 1) / h) = (D * m - 1) / h * h := by ring
      omega
    omega
  have hr_in_Icc : r ∈ Finset.Icc 1 h := Finset.mem_Icc.mpr ⟨hr_pos, hr_le⟩
  have h_thresh_le : mthresh r ≤ m₀_base := Finset.le_sup hr_in_Icc
  have hM_ge : mthresh r ≤ M := by
    have h_m_ge : h * (m₀_base + 1) + 1 ≤ m := by rw [hm₀_def] at hm_ge; exact hm_ge
    have h_Dm_ge : h * (m₀_base + 1) + 1 ≤ D * m := by
      have h_D_ge_1 : 1 ≤ D := hD_pos
      calc h * (m₀_base + 1) + 1 ≤ m := h_m_ge
        _ = 1 * m := by ring
        _ ≤ D * m := Nat.mul_le_mul_right m h_D_ge_1
    have h_step1 : h * m₀_base ≤ D * m - 1 := by
      have : h * (m₀_base + 1) ≤ D * m - 1 := by omega
      have h2 : h * m₀_base ≤ h * (m₀_base + 1) := by
        apply Nat.mul_le_mul_left; omega
      omega
    have h_div_ge : m₀_base ≤ (D * m - 1) / h := by
      rw [Nat.le_div_iff_mul_le hh_pos]
      linarith
    have h_M_eq : M = (D * m - 1) / h := hM_def
    omega
  have hM_ge_unfold : (h_apply_thm1 r hr_pos hr_le).choose ≤ M := by
    have hmt : mthresh r = (h_apply_thm1 r hr_pos hr_le).choose := by
      simp only [mthresh]
      rw [dif_pos ⟨hr_pos, hr_le⟩]
    omega
  obtain ⟨k, n_seq, h_strict, h_L_lb, h_recip_sum, h_M_sum⟩ :=
    (h_apply_thm1 r hr_pos hr_le).choose_spec M hM_ge_unfold
  refine ⟨(Finset.univ : Finset (Fin (k + 1))).image
    (fun i => p.eval ((n_seq i : ℕ) : ℚ) + 1 / ((n_seq i : ℕ) : ℚ)), ?_, ?_⟩
  · -- (X : Set ℚ) ⊆ imageSet p \ ↑B
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ,
               true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨?_, ?_⟩
    · refine ⟨n_seq i, rfl⟩
    · have h_lb_i : L < n_seq i := by
        have h_le : n_seq 0 ≤ n_seq i := h_strict.monotone (Fin.zero_le _)
        omega
      exact hL_avoid (n_seq i) h_lb_i
  · -- ∑ x ∈ X, x = (m : ℚ).
    have h_inj : Set.InjOn
        (fun i => p.eval ((n_seq i : ℕ) : ℚ) + 1 / ((n_seq i : ℕ) : ℚ))
        ((Finset.univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))) := by
      intro a _ b _ hab
      have h_lb_a : L < n_seq a := by
        have : n_seq 0 ≤ n_seq a := h_strict.monotone (Fin.zero_le _); omega
      have h_lb_b : L < n_seq b := by
        have : n_seq 0 ≤ n_seq b := h_strict.monotone (Fin.zero_le _); omega
      have h_n_eq : n_seq a = n_seq b := hL_inj _ _ h_lb_a h_lb_b hab
      exact h_strict.injective h_n_eq
    rw [Finset.sum_image h_inj]
    rw [show ∀ (s : Finset (Fin (k+1))) (f g : Fin (k+1) → ℚ),
          ∑ i ∈ s, (f i + g i) = (∑ i ∈ s, f i) + ∑ i ∈ s, g i from
          fun s f g => Finset.sum_add_distrib]
    have hp_eq : ∀ z : ℚ, p.eval z = ((h : ℚ) / (D : ℚ)) * q.eval z := by
      intro z
      rw [hq_eval, hDp_def]
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      field_simp
    have h_sum_p : ∑ i, p.eval ((n_seq i : ℕ) : ℚ) =
        ((h : ℚ) / (D : ℚ)) * ∑ i, q.eval ((n_seq i : ℕ) : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hp_eq _
    rw [h_sum_p, ← h_M_sum, ← h_recip_sum]
    have hh_pos_int : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh_pos
    have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    have hD_ne_q' : (D : ℚ) ≠ 0 := ne_of_gt hD_pos_q
    have h_combine : ((h : ℚ) / (D : ℚ)) * (M : ℚ) + ((r : ℚ) / (D : ℚ)) =
        ((h : ℚ) * (M : ℚ) + (r : ℚ)) / (D : ℚ) := by
      field_simp
    rw [h_combine]
    have hD_eq_q : (D : ℚ) * (m : ℚ) = (h : ℚ) * (M : ℚ) + (r : ℚ) := by
      have : ((D * m : ℕ) : ℚ) = ((h * M + r : ℕ) : ℚ) := by exact_mod_cast hD_eq
      push_cast at this; linarith
    rw [← hD_eq_q]
    field_simp

/-! ## Case negative leading coefficient (impossibility) -/

/-- For `p` with **negative** leading coefficient, `A_p` is *not* strongly
complete: only finitely many elements of `A_p` are positive, so subset sums are
bounded. (Not needed for FC #351; included for the corrected mathematical
statement.) -/
theorem not_strongly_complete_of_neg_leadingCoeff
    (p : ℚ[X]) (hp : p.leadingCoeff < 0) :
    ¬ IsStronglyComplete (imageSet p) := by
  classical
  intro hsc
  -- Step 1: Find `N₀ ≥ 1` with `p.eval n + 1/n ≤ 0` for all `n ≥ N₀`.
  have h_neg_eventually : ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) + 1 / (n : ℚ) ≤ 0 := by
    by_cases hd : p.natDegree = 0
    case pos =>
      -- Constant case: `p = C c` with `c = leadingCoeff < 0`. For `n ≥ ⌈1/(-c)⌉ + 1`,
      -- we have `1/n < -c`, so `c + 1/n < 0`.
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hd
      have hlc : p.leadingCoeff = p.coeff 0 := by
        rw [Polynomial.leadingCoeff, hd]
      set c := p.coeff 0 with hc_def
      have hc_neg : c < 0 := by rw [← hlc]; exact hp
      have hcneg : (0 : ℚ) < -c := by linarith
      refine ⟨max 1 (⌈1 / -c⌉₊ + 1), ?_, ?_⟩
      · exact le_max_left _ _
      · intro n hn
        have hn1 : 1 ≤ n := le_of_max_le_left hn
        have hn_ceil : ⌈1 / -c⌉₊ + 1 ≤ n := le_of_max_le_right hn
        have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn1
        have h_le : (1 / -c : ℚ) < (n : ℚ) := by
          have h2 : (⌈1 / -c⌉₊ + 1 : ℕ) ≤ n := hn_ceil
          have h3 : ((⌈1 / -c⌉₊ + 1 : ℕ) : ℚ) ≤ (n : ℚ) := by exact_mod_cast h2
          push_cast at h3
          linarith [Nat.le_ceil (1 / -c : ℚ)]
        have h1 : 1 / (n : ℚ) < -c := by
          rw [div_lt_iff₀ hn_pos]
          rw [div_lt_iff₀ hcneg] at h_le
          linarith
        rw [hpC, Polynomial.eval_C]
        linarith
    case neg =>
      -- Non-constant case: `0 < natDegree p`, so `Polynomial.tendsto_atBot_of_leadingCoeff_nonpos`
      -- gives `p.eval x → -∞`. In particular, eventually `p.eval n ≤ -1`, and `1/n ≤ 1`,
      -- hence `p.eval n + 1/n ≤ 0`.
      have hd_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hd
      have hp_ne_zero : p ≠ 0 := by
        intro hpz
        rw [hpz] at hp
        simp [Polynomial.leadingCoeff_zero] at hp
      have hdeg : 0 < p.degree := by
        rw [Polynomial.degree_eq_natDegree hp_ne_zero]
        exact_mod_cast hd_pos
      have h := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos p hdeg (le_of_lt hp)
      rw [Filter.tendsto_atTop_atBot] at h
      obtain ⟨N₀, hN₀⟩ := h (-1)
      refine ⟨max 1 ⌈N₀⌉₊, ?_, ?_⟩
      · exact le_max_left _ _
      · intro n hn
        have hn1 : 1 ≤ n := le_of_max_le_left hn
        have hn_ceil : ⌈N₀⌉₊ ≤ n := le_of_max_le_right hn
        have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn1
        have h_evalQ : p.eval (n : ℚ) ≤ -1 := by
          apply hN₀
          have h1 := Nat.le_ceil N₀
          have h2 : (⌈N₀⌉₊ : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn_ceil
          linarith
        have h_inv : 1 / (n : ℚ) ≤ 1 := by
          rw [div_le_one hn_pos]
          exact_mod_cast hn1
        linarith
  obtain ⟨N₀, _hN₀_pos, hN₀⟩ := h_neg_eventually
  -- Step 2: Define the bound `M`.
  set M : ℚ := ∑ n ∈ Finset.range N₀, max (p.eval (n : ℚ) + 1 / (n : ℚ)) 0 with hM_def
  -- Step 3: Any subset sum over `imageSet p` is bounded by `M`.
  have h_bound : ∀ X : Finset ℚ, (↑X : Set ℚ) ⊆ imageSet p → ∑ x ∈ X, x ≤ M := by
    intro X hX
    -- `S` is the image of `[0, N₀)` under `n ↦ p.eval n + 1/n`.
    let S : Finset ℚ :=
      Finset.image (fun n : ℕ => p.eval (n : ℚ) + 1 / (n : ℚ)) (Finset.range N₀)
    -- Every `x ∈ X` is either in `S` (came from `n < N₀`) or `x ≤ 0` (came from `n ≥ N₀`).
    have h_split : ∀ x ∈ X, x ∈ S ∨ x ≤ 0 := by
      intro x hx
      have hx_im : x ∈ imageSet p := hX hx
      obtain ⟨n, hn_eq⟩ := hx_im
      by_cases hn_lt : n < N₀
      · left
        simp only [S, Finset.mem_image, Finset.mem_range]
        exact ⟨n, hn_lt, hn_eq⟩
      · right
        push_neg at hn_lt
        have := hN₀ n hn_lt
        simp only at hn_eq
        linarith
    -- Split `∑ x ∈ X, x = ∑_{X∩S} + ∑_{X\S}`. The second sum is ≤ 0; the first is
    -- ≤ ∑_S max x 0.
    have h_bound1 : ∑ x ∈ X, x ≤ ∑ x ∈ S, max x 0 := by
      rw [show ∑ x ∈ X, x = ∑ x ∈ X ∩ S, x + ∑ x ∈ X \ S, x from
          (Finset.sum_inter_add_sum_diff X S id).symm]
      have h1 : ∑ x ∈ X ∩ S, x ≤ ∑ x ∈ X ∩ S, max x 0 := by
        apply Finset.sum_le_sum; intros; exact le_max_left _ _
      have h2 : ∑ x ∈ X ∩ S, max x 0 ≤ ∑ x ∈ S, max x 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.inter_subset_right
        · intros; exact le_max_right _ _
      have h3 : ∑ x ∈ X \ S, x ≤ 0 := by
        apply Finset.sum_nonpos
        intro x hx
        simp only [Finset.mem_sdiff] at hx
        rcases h_split x hx.1 with h_in | h_le
        · exact absurd h_in hx.2
        · exact h_le
      linarith
    -- Sum over `S` (image) ≤ sum over `Finset.range N₀` (preimage), since elements
    -- under `max · 0` are nonnegative.
    have h_bound2 : ∑ x ∈ S, max x 0 ≤ M := by
      apply Finset.sum_image_le_of_nonneg
      intros; exact le_max_right _ _
    linarith
  -- Step 4: Apply the strong-completeness with `B = ∅` and pick `m > M`.
  have hev := hsc ∅
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  let m : ℕ := max a (⌈M⌉₊ + 1)
  have hma : a ≤ m := le_max_left _ _
  have hmceil : ⌈M⌉₊ + 1 ≤ m := le_max_right _ _
  obtain ⟨X, hX_sub, hX_sum⟩ := ha m hma
  have hX_sub_no_B : (↑X : Set ℚ) ⊆ imageSet p := by
    intro x hx
    have := hX_sub hx
    simp only [Finset.coe_empty, Set.diff_empty] at this
    exact this
  have h_le := h_bound X hX_sub_no_B
  have hmM : M < (m : ℚ) := by
    have h1 : M ≤ (⌈M⌉₊ : ℚ) := Nat.le_ceil M
    have h2 : ((⌈M⌉₊ + 1 : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hmceil
    push_cast at h2
    linarith
  rw [hX_sum] at h_le
  linarith

/-! ## Combined corollary 7 statement -/

/-- **Corollary 7 (PDF, combined).** If `p = 0` or `p` has positive leading
coefficient, `A_p = {p(n) + 1/n}` is strongly complete. (Includes positive
constants — `p = C c` with `c > 0` — in addition to nonconstant positive-leading
polynomials. FC #351 separately requires `0 < natDegree p`.) -/
theorem corollary_7 (p : ℚ[X])
    (h : p = 0 ∨ 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := by
  rcases h with rfl | hl
  · exact corollary_7_zero
  · exact corollary_7_pos_leading p hl

end PolynomialEgyptianSums

/-! =============================================================
    Section from: Erdos/P283/FC.lean
    ============================================================= -/

/-
Erdős Problems 283 + 351 — `formal-conjectures` upstream wrappers.

This file lives in *separate* namespaces (`Erdos283`, `Erdos351`) from the core
proof in `PolynomialEgyptianSums`, to avoid future name collisions when
`formal-conjectures` is imported alongside.

Bridges between our internal forms and FC's literal syntax:

  * `Erdos283.Condition`           — FC's per-polynomial condition (sentinel
                                      `n 0 = 0`, sums over `Finset.Icc 1 (Fin.last k)`).
  * `Erdos283.erdos_283`           — `True ↔ ∀ p : ℤ[X], Condition p`
                                      under `answer := True`.
  * `Erdos351.HasCompleteImage`    — strong completeness of `imageSet`.
  * `Erdos351.erdos_351`           — `True ↔ ∀ P : ℚ[X], 0 < P.natDegree →
                                      0 < P.leadingCoeff → HasCompleteImage P`
                                      under `answer := True`.
-/


/-! ## #283 wrapper -/

namespace Erdos283

open Filter Polynomial Finset

/-- The condition appearing in FC's `erdos_283` for an integer polynomial. -/
def Condition (p : ℤ[X]) : Prop :=
  p.leadingCoeff > 0 → ¬ (∃ d ≥ 2, ∀ n ≥ 1, d ∣ p.eval n) →
    ∀ᶠ m in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
      1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
      m = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i)

/-- **`formal-conjectures` upstream form for #283** under `answer := True`.

Bridges from `PolynomialEgyptianSums.theorem_1` (with `α = 1`, `L = 1`, `p`
coerced from `ℤ[X]` to `ℚ[X]`) to FC's sentinel-indexed `Fin (k+1) → ℤ` form. -/
theorem erdos_283 :
    True ↔ ∀ p : ℤ[X], Condition p := by
  refine ⟨fun _ p => ?_, fun _ => trivial⟩
  unfold Condition
  intro hlc hnf
  rw [Filter.eventually_atTop]
  -- Coerce `p : ℤ[X]` to `pℚ : ℚ[X]`.
  set pℚ : ℚ[X] := p.map (Int.castRingHom ℚ) with hpℚ
  -- `pℚ` is integer-valued: at any integer `z`, `pℚ.eval (z : ℚ) = (p.eval z : ℤ → ℚ)`.
  have hp_int : PolynomialEgyptianSums.IntValued pℚ := by
    intro z
    refine ⟨Polynomial.eval z p, ?_⟩
    show ((Polynomial.eval z p : ℤ) : ℚ) = pℚ.eval ((z : ℤ) : ℚ)
    rw [hpℚ, Polynomial.eval_map]
    rw [show ((z : ℤ) : ℚ) = (Int.castRingHom ℚ) z from rfl]
    rw [Polynomial.eval₂_at_apply]
    simp
  -- `pℚ.leadingCoeff = (p.leadingCoeff : ℤ → ℚ) > 0`.
  have hlc_pℚ : 0 < pℚ.leadingCoeff := by
    rw [hpℚ]
    rw [Polynomial.leadingCoeff_map_of_injective (f := Int.castRingHom ℚ) Int.cast_injective]
    show 0 < ((p.leadingCoeff : ℤ) : ℚ)
    exact_mod_cast hlc
  -- `intEval pℚ hp_int z = p.eval z` (as ℤ).
  have h_intEval_eq : ∀ z : ℤ,
      PolynomialEgyptianSums.intEval pℚ hp_int z = Polynomial.eval z p := by
    intro z
    have h1 := PolynomialEgyptianSums.intEval_spec pℚ hp_int z
    have h2 : ((Polynomial.eval z p : ℤ) : ℚ) = pℚ.eval ((z : ℤ) : ℚ) := by
      rw [hpℚ, Polynomial.eval_map]
      rw [show ((z : ℤ) : ℚ) = (Int.castRingHom ℚ) z from rfl]
      rw [Polynomial.eval₂_at_apply]
      simp
    have h3 :
        ((PolynomialEgyptianSums.intEval pℚ hp_int z : ℤ) : ℚ)
          = ((Polynomial.eval z p : ℤ) : ℚ) := by
      rw [h1, h2]
    exact_mod_cast h3
  -- `NoFixedDivisor pℚ hp_int` from `hnf` (FC's no-fixed-divisor on ℤ).
  have hnf_pℚ : PolynomialEgyptianSums.NoFixedDivisor pℚ hp_int := by
    intro d hd hdvd
    apply hnf
    refine ⟨(d : ℤ), by exact_mod_cast hd, ?_⟩
    intro n hn
    obtain ⟨n_nat, hn_eq⟩ : ∃ n_nat : ℕ, (n_nat : ℤ) = n := ⟨n.toNat, by omega⟩
    have h1n : 1 ≤ n_nat := by omega
    have hdvd1 := hdvd n_nat h1n
    rw [h_intEval_eq, hn_eq] at hdvd1
    exact hdvd1
  -- Apply `theorem_1` with `α = 1`, `L = 1`.
  obtain ⟨m₀, hm₀⟩ := PolynomialEgyptianSums.theorem_1 1 (by norm_num) 1 (le_refl 1) pℚ
    hp_int hlc_pℚ hnf_pℚ
  refine ⟨m₀, fun m hm => ?_⟩
  -- `m : ℤ` from `Filter.atTop` over ℤ; coerce to ℕ via `m.toNat`.
  have hm_cast : (m.toNat : ℤ) = m := by omega
  obtain ⟨k, n_int, hStrict, hLb, hsum_recip, hsum_p⟩ := hm₀ m.toNat (by omega)
  -- Build `n_FC : Fin (k+1+1) → ℤ` as `Fin.cons 0 (fun i => (n_int i : ℕ → ℤ))`.
  refine ⟨k + 1, by omega, Fin.cons 0 (fun i : Fin (k + 1) => (n_int i : ℤ)), ?_, ?_, ?_, ?_⟩
  · -- Sentinel: `n_FC 0 = 0`.
    rfl
  · -- `StrictMono n_FC`: case-split on `i, j` via `Fin.cases`.
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd hij (lt_irrefl _)
      | succ j' =>
        rw [Fin.cons_zero, Fin.cons_succ]
        have h1 : n_int 0 ≤ n_int j' := hStrict.monotone (Fin.zero_le _)
        have h2 : 1 < n_int j' := lt_of_lt_of_le hLb h1
        have h3 : 0 < n_int j' := by omega
        exact_mod_cast h3
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ j' =>
        rw [Fin.cons_succ, Fin.cons_succ]
        have hij' : i' < j' := Fin.succ_lt_succ_iff.mp hij
        exact_mod_cast hStrict hij'
  · -- Reciprocal sum: `1 = ∑ i ∈ Icc 1 (Fin.last (k+1)), 1 / n_FC i`.
    -- Re-index `Icc 1 (Fin.last (k+1)) = image Fin.succ univ`, then use `Fin.cons_succ`.
    have h_eq : Finset.Icc (1 : Fin (k + 1 + 1)) (Fin.last (k + 1)) =
        Finset.image Fin.succ (Finset.univ : Finset (Fin (k + 1))) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro ⟨h1, h2⟩
        obtain ⟨v, hv⟩ := i
        simp [Fin.le_def, Fin.val_last] at h1 h2
        refine ⟨⟨v - 1, ?_⟩, ?_⟩
        · simp; omega
        · ext; simp; omega
      · rintro ⟨j, rfl⟩
        obtain ⟨w, hw⟩ := j
        refine ⟨?_, ?_⟩
        · simp [Fin.le_def]
        · simp [Fin.le_def, Fin.val_last]; omega
    rw [h_eq]
    rw [Finset.sum_image (fun a _ b _ h => Fin.succ_injective _ h)]
    simp_rw [Fin.cons_succ]
    convert hsum_recip using 1
  · -- Polynomial sum: `m = ∑ i ∈ Icc 1 (Fin.last (k+1)), p.eval (n_FC i)`.
    have h_eq : Finset.Icc (1 : Fin (k + 1 + 1)) (Fin.last (k + 1)) =
        Finset.image Fin.succ (Finset.univ : Finset (Fin (k + 1))) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro ⟨h1, h2⟩
        obtain ⟨v, hv⟩ := i
        simp [Fin.le_def, Fin.val_last] at h1 h2
        refine ⟨⟨v - 1, ?_⟩, ?_⟩
        · simp; omega
        · ext; simp; omega
      · rintro ⟨j, rfl⟩
        obtain ⟨w, hw⟩ := j
        refine ⟨?_, ?_⟩
        · simp [Fin.le_def]
        · simp [Fin.le_def, Fin.val_last]; omega
    rw [h_eq]
    rw [Finset.sum_image (fun a _ b _ h => Fin.succ_injective _ h)]
    simp_rw [Fin.cons_succ]
    -- Bridge `pℚ.eval ((z : ℕ → ℚ)) = ((p.eval (z : ℕ → ℤ) : ℤ → ℚ))`.
    have h_eval : ∀ z : ℕ,
        pℚ.eval ((z : ℕ) : ℚ) = ((Polynomial.eval (z : ℤ) p : ℤ) : ℚ) := by
      intro z
      rw [hpℚ, Polynomial.eval_map]
      rw [show ((z : ℕ) : ℚ) = (Int.castRingHom ℚ) (z : ℤ) from rfl]
      rw [Polynomial.eval₂_at_apply]
      simp
    -- Cast `hsum_p` over to the ℤ-valued sum.
    have h_rat : (m : ℚ) =
        ∑ i : Fin (k + 1), ((Polynomial.eval ((n_int i : ℤ) : ℤ) p : ℤ) : ℚ) := by
      rw [show (m : ℚ) = ((m.toNat : ℕ) : ℚ) by exact_mod_cast hm_cast.symm]
      rw [hsum_p]
      apply Finset.sum_congr rfl
      intro i _
      rw [h_eval]
    have h_int : (m : ℚ) =
        ((∑ i : Fin (k + 1), Polynomial.eval ((n_int i : ℤ) : ℤ) p : ℤ) : ℚ) := by
      rw [h_rat]; push_cast; rfl
    exact_mod_cast h_int

end Erdos283

/-! ## #351 wrapper -/

namespace Erdos351

open Polynomial

/-- FC-named alias for `imageSet`. -/
def imageSet (P : ℚ[X]) : Set ℚ := PolynomialEgyptianSums.imageSet P

/-- FC-named alias for `IsStronglyComplete (imageSet P)`. -/
def HasCompleteImage (P : ℚ[X]) : Prop :=
  PolynomialEgyptianSums.IsStronglyComplete (imageSet P)

/-- **`formal-conjectures` upstream form for #351** under `answer := True`.

Direct from `PolynomialEgyptianSums.corollary_7_pos_leading`. -/
theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      HasCompleteImage P := by
  refine ⟨fun _ P _ hlc => ?_, fun _ => trivial⟩
  exact PolynomialEgyptianSums.corollary_7_pos_leading P hlc

end Erdos351

/-! ## Axiom audit -/

-- Uncomment to inspect the trust boundary at build time:
-- #print axioms PolynomialEgyptianSums.theorem_1
-- #print axioms PolynomialEgyptianSums.corollary_7_pos_leading
-- #print axioms PolynomialEgyptianSums.corollary_7
-- #print axioms Erdos283.erdos_283
-- #print axioms Erdos351.erdos_351
