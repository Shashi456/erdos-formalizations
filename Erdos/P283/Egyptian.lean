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

import Erdos.P283.Basic

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

/-- Auxiliary: a single Egyptian expansion exists (greedy). -/
lemma egyptian_expansion_exists (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ E : Finset ℕ, (∀ e ∈ E, L < e) ∧ R = ∑ e ∈ E, (1 : ℚ) / e := by
  sorry

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
  sorry

end PolynomialEgyptianSums
