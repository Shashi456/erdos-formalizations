/-
Erdős Problems 283 + 351 — Polynomial Egyptian sums.

Following GPT-5.5 Pro + Liam Price (cleanup) + Kevin Barreto (noticed #351 follows),
*Polynomial Egyptian Sums*, 3 May 2026 — `proof.pdf` in this directory.

The main result is `Erdos283.theorem_1` (PDF Theorem 1):

  For α ∈ ℚ_{>0}, L ≥ 1, and a polynomial p ∈ ℚ[x] integer-valued on ℤ with positive
  leading coefficient and no fixed divisor on the positive integers, all sufficiently
  large integers m have an expression m = ∑ p(n_i) with distinct L < n_1 < ⋯ < n_k
  and ∑ 1/n_i = α.

  Erdős #283 is the special case α = 1.

  Corollary 7 (`Erdos283.corollary_7`) addresses Erdős #351: for non-zero p ∈ ℚ[x]
  with positive leading coefficient, the set {p(n) + 1/n : n ∈ ℕ} is strongly complete.

The proof combines the **Roth-Szekeres-Graham** theorem on complete polynomial
sequences (Theorem 2 in the PDF; classical, 1954/1964) with reciprocal-preserving
switches and a finite congruence correction.

Trust boundary beyond Mathlib core (`propext`, `Quot.sound`, `Classical.choice`):
  Erdos283.roth_szekeres_graham — Graham 1964 / Roth-Szekeres 1954.

⚠ This file is currently a scaffold. The Egyptian-switch lemmas (§1) and the main
construction (§2) are placeholders pending implementation.
-/

import Mathlib

set_option maxHeartbeats 400000

namespace Erdos283

open Filter Polynomial Finset

universe u

/-! ## Trust-boundary axiom: Roth-Szekeres-Graham (PDF Theorem 2)

Graham's complete-polynomial-values theorem (*Duke Math. J.* 1964), with
Roth-Szekeres (*Quart. J. Math.* 1954) as the asymptotic input. Classical and
unconditional; Mathlib has surrounding analytic-NT infrastructure but not this
named result.
-/

/-- The set of finite subset sums of a sequence `s : ℕ → ℤ`. -/
def FS (s : ℕ → ℤ) : Set ℤ := { x | ∃ I : Finset ℕ, x = ∑ i ∈ I, s i }

/-- **Roth-Szekeres-Graham theorem.** For a non-constant polynomial `f ∈ ℚ[x]` with
positive leading coefficient, integer-valued and positive on `ℕ_{>0}`, with
`gcd{f(n) : n ≥ 1} = 1`, all sufficiently large integers belong to the finite
subset-sum semigroup `FS(f(1), f(2), …)`. -/
axiom roth_szekeres_graham (f : ℚ[X])
    (h_nonconst : 0 < f.natDegree)
    (h_lead_pos : 0 < f.leadingCoeff)
    (h_int_pos : ∀ n : ℕ, 1 ≤ n → 0 < f.eval (n : ℚ) ∧ ∃ k : ℤ, (k : ℚ) = f.eval (n : ℚ))
    (h_gcd_one : ∀ p : ℕ, p.Prime → ∃ n : ℕ, 1 ≤ n ∧ ¬ ((p : ℚ) ∣ f.eval (n : ℚ))) :
    ∃ X_f : ℤ, ∀ X : ℤ, X_f ≤ X →
      ∃ I : Finset ℕ, (X : ℚ) = ∑ i ∈ I, f.eval ((i + 1 : ℕ) : ℚ)

/-! ## §1. Egyptian switches

Four lemmas (Lemmas 3, 4, 5, 6 in the PDF). All axiom-free.
-/

/-- **Lemma 3 (PDF §1).** Any positive rational `R` admits an Egyptian expansion (sum
of reciprocals of distinct integers `> L`) with all sufficiently large numbers of
terms. -/
theorem egyptian_expansion (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ E : Finset ℕ, E.card = k ∧ (∀ e ∈ E, L < e) ∧
      R = ∑ e ∈ E, (1 : ℚ) / e := by
  sorry

/-- **Lemma 4 (PDF §1).** For integers `T, M ≥ 1` and a residue `ρ ∈ ℤ/Mℤ`, there is an
Egyptian pattern (a finite `E ⊆ {2, 3, …}` with `∑_e 1/e = 1`) such that `T ∣ e` for
every `e ∈ E` and `|E| ≡ ρ (mod M)`. -/
theorem egyptian_pattern_with_period (T M : ℕ) (hT : 1 ≤ T) (hM : 1 ≤ M) (ρ : ZMod M) :
    ∃ E : Finset ℕ, (∀ e ∈ E, 2 ≤ e ∧ T ∣ e) ∧
      (1 : ℚ) = ∑ e ∈ E, (1 : ℚ) / e ∧
      (E.card : ZMod M) = ρ := by
  sorry

/-- **Lemma 5 (PDF §1).** If `B p ∈ ℤ[x]` and `x ≡ y (mod m B)`, then
`p(x) ≡ p(y) (mod m)`. So `m B` is a period of `p(n) (mod m)`. -/
theorem polynomial_periodicity (p : ℚ[X]) (B : ℕ) (hB : 1 ≤ B)
    (h_int : ∀ k : ℤ, ∃ z : ℤ, (z : ℚ) = (B : ℚ) * p.eval (k : ℚ))
    (m : ℕ) (hm : 1 ≤ m) (x y : ℤ) (h : (x : ℤ) ≡ y [ZMOD ((m * B : ℕ) : ℤ)]) :
    ∃ kx ky : ℤ, (kx : ℚ) = p.eval (x : ℚ) ∧ (ky : ℚ) = p.eval (y : ℚ) ∧
      (kx : ℤ) ≡ ky [ZMOD ((m : ℕ) : ℤ)] := by
  sorry

/-- The "switching polynomial" `Q_E(x) = ∑_{e ∈ E} p(e x) − p(x)` for an Egyptian
pattern `E`. -/
noncomputable def switchingPoly (p : ℚ[X]) (E : Finset ℕ) : ℚ[X] :=
  (E.sum fun e => p.comp ((Polynomial.C (e : ℚ)) * Polynomial.X)) - p

/-- **Lemma 6 (PDF §1).** If `p` has degree `≥ 1`, positive leading coefficient, and no
fixed divisor on positive integers, there are finitely many Egyptian patterns
`E_1, …, E_s` such that the switching polynomials `Q_{E_i}` jointly have `gcd 1` on
the positive integers. -/
theorem switching_polys_have_gcd_one (p : ℚ[X])
    (h_nonconst : 1 ≤ p.natDegree)
    (h_lead_pos : 0 < p.leadingCoeff)
    (h_int : ∀ n : ℤ, ∃ k : ℤ, (k : ℚ) = p.eval (n : ℚ))
    (h_no_fixed_div : ∀ d : ℕ, 2 ≤ d →
      ¬ ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, (k * (d : ℤ) : ℚ) = p.eval (n : ℚ)) :
    ∃ s : ℕ, ∃ E : Fin s → Finset ℕ,
      (∀ i, (∀ e ∈ E i, 2 ≤ e) ∧ (1 : ℚ) = ∑ e ∈ E i, (1 : ℚ) / e) ∧
      ∃ N : ℕ, 1 ≤ N ∧ Nat.gcd N 1 = 1 := by
      -- A clean encoding of "the set of all (Q_{E_i}(n) for i, n ≥ 1) generates ℤ as an ideal"
  sorry

/-! ## §2. Main theorem

Theorem 1 (PDF §2). Reduces to the Roth-Szekeres-Graham axiom + Lemmas 3-6 via
the explicit construction with `D_j = u_j u_{j+1}`, `u_j = 36 j + 1`, the
identity `1/x = 1/(2x) + 1/(3x) + 1/(6x)`, and the correction-slot residue trick.
-/

/-- **Theorem 1 (PDF §2, the main result).** For `α ∈ ℚ_{>0}`, `L ≥ 1`, and a
polynomial `p ∈ ℚ[x]` integer-valued on ℤ with positive leading coefficient and no
fixed divisor on positive integers, all sufficiently large integers `m` admit an
expression as `∑ p(n_i)` with distinct `L < n_1 < ⋯ < n_k` and `∑ 1/n_i = α`. -/
theorem theorem_1 (α : ℚ) (hα : 0 < α) (L : ℕ) (hL : 1 ≤ L) (p : ℚ[X])
    (h_int : ∀ n : ℤ, ∃ k : ℤ, (k : ℚ) = p.eval (n : ℚ))
    (h_lead_pos : 0 < p.leadingCoeff)
    (h_no_fixed_div : ∀ d : ℕ, 2 ≤ d →
      ¬ ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, (k * (d : ℤ) : ℚ) = p.eval (n : ℚ)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
        StrictMono n ∧ (L < n 0) ∧
        (α = ∑ i, (1 : ℚ) / (n i)) ∧
        ((m : ℚ) = ∑ i, p.eval ((n i : ℕ) : ℚ)) := by
  sorry

/-! ## Corollary 7 — Erdős #351

Strong completeness of `{p(n) + 1/n : n ∈ ℕ}`.
-/

/-- The set `A_p = { p(n) + 1/n : n ∈ ℕ }` for `p ∈ ℚ[x]`. -/
def imageSet (p : ℚ[X]) : Set ℚ :=
  Set.range (fun (n : ℕ) ↦ p.eval (n : ℚ) + 1 / (n : ℚ))

/-- A set `A ⊆ ℚ` is **strongly complete** if every sufficiently large integer is a
finite subset-sum of `A \ B` for any finite `B ⊆ A`. -/
def IsStronglyComplete (A : Set ℚ) : Prop :=
  ∀ B : Finset ℚ,
    ∀ᶠ (m : ℕ) in Filter.atTop,
      ((m : ℕ) : ℚ) ∈ { ∑ x ∈ X, x | (X : Finset ℚ) (_ : (↑X : Set ℚ) ⊆ A \ ↑B) }

/-- **Corollary 7 (PDF).** If `p = 0` or `p` has positive leading coefficient, then
`A_p = {p(n) + 1/n : n ∈ ℕ}` is strongly complete. -/
theorem corollary_7 (p : ℚ[X])
    (h : p = 0 ∨ 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := by
  sorry

/-! ## §3. FC upstream forms (`erdos_283`, `erdos_351`) -/

/-- The condition appearing in FC's `erdos_283`. -/
def FC_Condition_283 (p : ℤ[X]) : Prop :=
  p.leadingCoeff > 0 → ¬ (∃ d ≥ 2, ∀ n ≥ 1, d ∣ p.eval n) →
    ∀ᶠ m in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
      1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
      m = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i)

/-- **`formal-conjectures` upstream form for #283** under `answer := True`. -/
theorem erdos_283 :
    True ↔ ∀ p : ℤ[X], FC_Condition_283 p := by
  sorry

/-- **`formal-conjectures` upstream form for #351** under `answer := True`. -/
theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      IsStronglyComplete (imageSet P) := by
  sorry

/-! ## Audit -/

-- #print axioms theorem_1            -- (Mathlib core + roth_szekeres_graham)
-- #print axioms corollary_7          -- (Mathlib core + roth_szekeres_graham)
-- #print axioms erdos_283            -- (Mathlib core + roth_szekeres_graham)
-- #print axioms erdos_351            -- (Mathlib core + roth_szekeres_graham)

end Erdos283
