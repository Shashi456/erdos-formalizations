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

import Erdos.P283.Basic
import Erdos.P283.Egyptian
import Erdos.P283.Theorem1

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

/-- **Corollary 7, positive-leading case.** For `p` with positive leading
coefficient, `A_p` is strongly complete.

Reduction (uniform in `natDegree p`): scale to `q := D·p/h` where `D` is the
common denominator of `p`'s coefficients and `h := gcd { (D·p)(n) : n ≥ 1 }`,
making `q` integer-valued, fixed-divisor-free, and positive-leading. For each
`m`, take `M := (D·m - 1) / h, r := D·m - h·M ∈ {1, …, h}` (Euclidean
division), then apply `theorem_1` to `q` with `α := (r : ℚ) / D`. The
identity `∑ (p(n_i) + 1/n_i) = (h/D) ∑ q(n_i) + ∑ 1/n_i = hM/D + r/D = m`
recovers the imageSet form.

The constant case `natDegree p = 0` is handled uniformly: if `p = C c` with
`c > 0` integer (forced by IntValued + lc > 0), then `D = 1`, `D·p = p`,
`h = gcd{c} = c`, and `q = c/c = 1`. Then `theorem_1` reduces to its
already-proved constant case. No separate proof is needed. -/
theorem corollary_7_pos_leading (p : ℚ[X])
    (h_lead_pos : 0 < p.leadingCoeff) :
    IsStronglyComplete (imageSet p) := by
  sorry

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
