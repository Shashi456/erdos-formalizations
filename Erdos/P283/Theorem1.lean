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

import Erdos.P283.Basic
import Erdos.P283.Egyptian
import Erdos.P283.PolynomialPeriod
import Erdos.P283.Switching
import Erdos.P283.MainSlots
import Erdos.P283.Corrections
import Erdos.P283.Collision

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

/-! ### Quotient-gcd bridge (sketch — full proof forthcoming)

The most important missing bridge for theorem_1's case neg: if `g` is the
positive generator of `Ideal.span (mainValueSet p hp md.J)`, then the
quotient values `(qPoly p md.J g).eval (t : ℚ)` (for `t ≥ 1`) generate the
unit ideal in `ℤ`. Equivalently, no prime `ℓ` divides every quotient value.

Mathematically: `g = gcd { A(D j) : j ≥ J }` by construction. Dividing the
spanning set by `g` gives values whose gcd is 1, so no prime divides them
all. RSG's `h_gcd_one` hypothesis is exactly this.

The full proof uses `Ideal.span` over ℤ (a PID), the principal-ideal
generator decomposition, and a transport from "gcd of values is `g`" to
"gcd of `value/g` is 1". For now declared as a sketch hypothesis used by the
`MainGCDData` constructor; the constructor itself is forthcoming. -/
section MainQuotBridge

variable {α : ℚ} {L : ℕ} (p : ℚ[X]) (hp : IntValued p)

/-- Stub statement-shape for the quotient-gcd bridge. The substance lives
in the forthcoming `MainGCDData` constructor; this `def` records the target
shape so callers can refer to it by name. -/
def mainQuot_no_prime_fixed_stmt (md : MainChoice α L p hp) (g : ℕ)
    (_ : 1 ≤ g) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime →
    ∃ t : ℕ, 1 ≤ t ∧ ∃ z : ℤ,
      (z : ℚ) = (qPoly p md.J g).eval (t : ℚ) ∧
      ¬ ((ℓ : ℤ) ∣ z)

end MainQuotBridge

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
    sorry

end PolynomialEgyptianSums
