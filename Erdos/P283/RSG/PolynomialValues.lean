/-
Copyright (c) 2026

Integer-valued polynomial value sequences for Graham's complete polynomial
sequence theorem.
-/

import Erdos.P283.RSG.CompleteSequences
import Erdos.P283.RSG.PolynomialDifferences
import Erdos.P283.RSG.PolynomialResidues

namespace Erdos.P283.RSG

open Polynomial
open Filter

/-! ## Chosen integer values of a rational polynomial -/

/-- The integer sequence attached to a rational polynomial whose positive
integer inputs are positive integers. Index `i` represents the value at
`i + 1`, matching the RSG wrapper shape used by P283. -/
noncomputable def polyValueSeq (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ)) :
    ℕ → ℤ :=
  fun i =>
    Classical.choose
      (h_int_pos (i + 1) (Nat.succ_le_succ (Nat.zero_le i)))

lemma polyValueSeq_pos (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (i : ℕ) :
    0 < polyValueSeq p h_int_pos i := by
  exact (Classical.choose_spec
    (h_int_pos (i + 1) (Nat.succ_le_succ (Nat.zero_le i)))).1

lemma polyValueSeq_eval (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (i : ℕ) :
    (polyValueSeq p h_int_pos i : ℚ) =
      p.eval ((i + 1 : ℕ) : ℚ) := by
  exact (Classical.choose_spec
    (h_int_pos (i + 1) (Nat.succ_le_succ (Nat.zero_le i)))).2

lemma eq_polyValueSeq_of_eval {p : ℚ[X]}
    {h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ)}
    {i : ℕ} {z : ℤ}
    (hz : (z : ℚ) = p.eval ((i + 1 : ℕ) : ℚ)) :
    z = polyValueSeq p h_int_pos i := by
  have hz' : (z : ℚ) = (polyValueSeq p h_int_pos i : ℚ) :=
    hz.trans (polyValueSeq_eval p h_int_pos i).symm
  exact_mod_cast hz'

/-- A finite subset sum of the chosen integer value sequence is the corresponding
rational finite subset sum of polynomial evaluations. -/
lemma polyValueSeq_fs_eval {p : ℚ[X]}
    {h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ)}
    {x : ℤ}
    (hx : x ∈ FS (polyValueSeq p h_int_pos)) :
    ∃ I : Finset ℕ,
      x = ∑ i ∈ I, polyValueSeq p h_int_pos i ∧
      (x : ℚ) = ∑ i ∈ I, p.eval ((i + 1 : ℕ) : ℚ) := by
  rcases hx with ⟨I, rfl⟩
  refine ⟨I, rfl, ?_⟩
  calc
    ((∑ i ∈ I, polyValueSeq p h_int_pos i : ℤ) : ℚ)
        = ∑ i ∈ I, (polyValueSeq p h_int_pos i : ℚ) := by norm_cast
    _ = ∑ i ∈ I, p.eval ((i + 1 : ℕ) : ℚ) := by
      exact Finset.sum_congr rfl
        (fun i _hi => polyValueSeq_eval p h_int_pos i)

/-- Completeness of the chosen integer value sequence unwraps to the rational
subset-sum conclusion used by the P283 axiom. -/
lemma complete_polyValueSeq_to_eval_subsets {p : ℚ[X]}
    {h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ)}
    (hcomp : Complete (polyValueSeq p h_int_pos)) :
    ∃ X_f : ℤ, ∀ X : ℤ, X_f ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, p.eval ((i + 1 : ℕ) : ℚ) := by
  rcases hcomp with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro X hX
  rcases hC X hX with ⟨I, rfl⟩
  refine ⟨I, ?_⟩
  calc
    ((∑ i ∈ I, polyValueSeq p h_int_pos i : ℤ) : ℚ)
        = ∑ i ∈ I, (polyValueSeq p h_int_pos i : ℚ) := by norm_cast
    _ = ∑ i ∈ I, p.eval ((i + 1 : ℕ) : ℚ) := by
      exact Finset.sum_congr rfl
        (fun i _hi => polyValueSeq_eval p h_int_pos i)

/-- The positive-input no-fixed-prime condition gives arbitrarily late
nondivisible terms in the chosen value sequence. -/
theorem polyValueSeq_infinite_nondivisibility_of_no_fixed_prime
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (h_gcd_one :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ n : ℕ, 1 ≤ n ∧ ∃ z : ℤ,
          (z : ℚ) = p.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z)) :
    ∀ ℓ : ℕ, ℓ.Prime →
      ∀ N : ℕ, ∃ i ≥ N, ¬ ((ℓ : ℤ) ∣ polyValueSeq p h_int_pos i) := by
  intro ℓ hℓ N
  obtain ⟨n, hn_ge, z, hz_eval, hz_ndvd⟩ :=
    infinite_nondivisibility_of_no_fixed_prime p h_int_pos h_gcd_one ℓ hℓ (N + 1)
  have hn_pos : 1 ≤ n :=
    (Nat.succ_le_succ (Nat.zero_le N)).trans hn_ge
  refine ⟨n - 1, Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn_ge), ?_⟩
  have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
  have hseq_eval :
      (polyValueSeq p h_int_pos (n - 1) : ℚ) = p.eval (n : ℚ) := by
    simpa [hn_sub] using polyValueSeq_eval p h_int_pos (n - 1)
  have hz_eq : z = polyValueSeq p h_int_pos (n - 1) := by
    have hz' : (z : ℚ) = (polyValueSeq p h_int_pos (n - 1) : ℚ) :=
      hz_eval.trans hseq_eval.symm
    exact_mod_cast hz'
  intro hdiv
  exact hz_ndvd (by simpa [hz_eq] using hdiv)

/-- Every residue attained by the chosen polynomial value sequence recurs
arbitrarily far out modulo any positive modulus. This is the denominator-cleared
periodicity input needed to turn finite Bezout witnesses into frequent
generators. -/
theorem polyValueSeq_residue_frequently_equal
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) :
    ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧
      ((polyValueSeq p h_int_pos j : ℤ) : ZMod m) =
        ((polyValueSeq p h_int_pos i : ℤ) : ZMod m) := by
  obtain ⟨B, hBpos, hB⟩ := exists_integral_multiple p
  intro N
  let step : ℕ := m * B
  let j : ℕ := i + (N + 1) * step
  have hstep_pos : 0 < step := by
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hm)
      (lt_of_lt_of_le Nat.zero_lt_one hBpos)
  refine ⟨j, ?_, ?_⟩
  · dsimp [j]
    have hmul : N + 1 ≤ (N + 1) * step := Nat.le_mul_of_pos_right _ hstep_pos
    omega
  · have hzx :
        (polyValueSeq p h_int_pos j : ℚ) =
          p.eval ((((j + 1 : ℕ) : ℤ) : ℚ)) := by
      simpa using polyValueSeq_eval p h_int_pos j
    have hzy :
        (polyValueSeq p h_int_pos i : ℚ) =
          p.eval ((((i + 1 : ℕ) : ℤ) : ℚ)) := by
      simpa using polyValueSeq_eval p h_int_pos i
    have hxy :
        ((j + 1 : ℕ) : ℤ) ≡ ((i + 1 : ℕ) : ℤ)
          [ZMOD ((m * B : ℕ) : ℤ)] := by
      refine Int.modEq_iff_dvd.mpr ?_
      refine ⟨-((N + 1 : ℕ) : ℤ), ?_⟩
      dsimp [j, step]
      ring
    have hper :
        polyValueSeq p h_int_pos j ≡ polyValueSeq p h_int_pos i
          [ZMOD ((m : ℕ) : ℤ)] :=
      polynomial_periodicity_of_integral_values p B hBpos hB m hm
        (((j + 1 : ℕ) : ℤ)) (((i + 1 : ℕ) : ℤ))
        (polyValueSeq p h_int_pos j) (polyValueSeq p h_int_pos i)
        hzx hzy hxy
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mpr
      (Int.modEq_iff_dvd.mp hper)

/-! ## Finite differences as signed sums of even tails -/

/-- Every Graham finite difference evaluated at a positive natural input has an
integer representative, because its explicit expansion is a signed sum of
positive integer values of `p`. -/
lemma Delta_eval_integer_polyValueSeq
    (k : ℕ) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (x : ℕ) (hx : 1 ≤ x) :
    ∃ z : ℤ, (z : ℚ) = (Delta k p).eval (x : ℚ) := by
  let y : ℤ :=
    ((deltaTerms k).map fun q : ℤ × ℕ =>
      q.1 * polyValueSeq p h_int_pos (4 ^ k * x + q.2 - 1)).sum
  refine ⟨y, ?_⟩
  have hval :
      ∀ q ∈ deltaTerms k,
        (polyValueSeq p h_int_pos (4 ^ k * x + q.2 - 1) : ℚ) =
          p.eval ((4 ^ k : ℚ) * (x : ℚ) + (q.2 : ℚ)) := by
    intro q _hq
    have harg_pos : 1 ≤ 4 ^ k * x + q.2 := by
      have hxpos : 0 < x := Nat.lt_of_lt_of_le Nat.zero_lt_one hx
      have hbase : 0 < 4 ^ k * x :=
        Nat.mul_pos (pow_pos (by norm_num) k) hxpos
      omega
    have hidx_succ : 4 ^ k * x + q.2 - 1 + 1 = 4 ^ k * x + q.2 :=
      Nat.sub_add_cancel harg_pos
    rw [polyValueSeq_eval]
    congr 1
    rw [hidx_succ]
    norm_num
  have hmap :
      (deltaTerms k).map
          (fun q : ℤ × ℕ =>
            ((q.1 * polyValueSeq p h_int_pos (4 ^ k * x + q.2 - 1) : ℤ) : ℚ)) =
        (deltaTerms k).map (deltaTermValue k p (x : ℚ)) := by
    apply List.map_congr_left
    intro q hq
    simp [deltaTermValue, hval q hq]
  rw [Delta_eval_eq_deltaTerms]
  dsimp [y]
  norm_cast
  rw [List.map_map]
  change
    ((deltaTerms k).map
      (fun q : ℤ × ℕ =>
        ((q.1 * polyValueSeq p h_int_pos (4 ^ k * x + q.2 - 1) : ℤ) : ℚ))).sum =
      ((deltaTerms k).map (deltaTermValue k p (x : ℚ))).sum
  rw [hmap]

/-- The top Graham finite difference is an integer constant on positive natural
inputs. The remaining hard analytic/algebraic fact is positivity of this
constant under positive leading coefficient. -/
lemma Delta_top_integer_constant
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ)) :
    ∃ m : ℤ,
      ∀ x : ℕ, 1 ≤ x → (m : ℚ) = (Delta p.natDegree p).eval (x : ℚ) := by
  obtain ⟨m, hm⟩ :=
    Delta_eval_integer_polyValueSeq p.natDegree p h_int_pos 1 (by norm_num)
  refine ⟨m, ?_⟩
  intro x _hx
  calc
    (m : ℚ) = (Delta p.natDegree p).eval (1 : ℚ) := hm
    _ = (Delta p.natDegree p).eval (x : ℚ) := by
      rw [Delta_top_eq_C p]
      simp

/-- The top Graham finite difference is represented by a positive natural
constant when `p` has positive leading coefficient. -/
lemma Delta_top_positive_integer_constant
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hlead : 0 < p.leadingCoeff) :
    ∃ m : ℕ, 0 < m ∧
      ∀ x : ℕ, 1 ≤ x → ((m : ℤ) : ℚ) = (Delta p.natDegree p).eval (x : ℚ) := by
  obtain ⟨mZ, hmZ⟩ := Delta_top_integer_constant p h_int_pos
  have hmZ_pos : 0 < mZ := by
    have hq_pos : 0 < (mZ : ℚ) := by
      calc
        0 < (Delta p.natDegree p).eval (1 : ℚ) := by
          rw [Delta_top_eq_C p]
          simpa using Delta_top_coeff_zero_pos p hlead
        _ = (mZ : ℚ) := (hmZ 1 (by norm_num)).symm
    exact_mod_cast hq_pos
  rcases Int.eq_ofNat_of_zero_le (le_of_lt hmZ_pos) with ⟨m, rfl⟩
  refine ⟨m, ?_, ?_⟩
  · exact_mod_cast hmZ_pos
  · intro x hx
    exact hmZ x hx

/-- Graham's `Delta` expansion uses only even offsets. Therefore, if an integer
`z` represents `Delta k p` at a positive natural input `x`, then `z` is a
signed finite subset sum of the even tail
`p(4^k*x), p(4^k*x + 2), p(4^k*x + 4), ...`. -/
lemma Delta_eval_integer_mem_signedFS_even_tail_polyValueSeq
    (k : ℕ) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (x : ℕ) (hx : 1 ≤ x) (z : ℤ)
    (hz : (z : ℚ) = (Delta k p).eval (x : ℚ)) :
    z ∈ SignedFS
      (fun a : ℕ => polyValueSeq p h_int_pos (4 ^ k * x + 2 * a - 1)) := by
  classical
  let S : ℕ → ℤ :=
    fun a : ℕ => polyValueSeq p h_int_pos (4 ^ k * x + 2 * a - 1)
  have hhalf_nodup :
      ((deltaTerms k).map fun q : ℤ × ℕ => q.2 / 2).Nodup := by
    refine (deltaTerms_nodup k).map_on ?_
    intro a ha b hb hhalf
    have hoff : a.2 = b.2 := by
      rcases deltaTerms_offset_even ha with ⟨aa, haa⟩
      rcases deltaTerms_offset_even hb with ⟨bb, hbb⟩
      rw [haa, hbb] at hhalf ⊢
      norm_num at hhalf ⊢
      omega
    exact deltaTerms_offset_injective_on ha hb hoff
  have hnodup :
      (((deltaTerms k).map fun q : ℤ × ℕ => (q.1, q.2 / 2)).map
          fun q : ℤ × ℕ => q.2).Nodup := by
    simpa [List.map_map] using hhalf_nodup
  have hsign :
      ∀ q ∈ (deltaTerms k).map (fun q : ℤ × ℕ => (q.1, q.2 / 2)),
        q.1 = 1 ∨ q.1 = -1 := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨a, ha, rfl⟩
    exact deltaTerms_sign_eq_one_or_neg_one (p := a) ha
  have hS_eval :
      ∀ q ∈ deltaTerms k,
        (S (q.2 / 2) : ℚ) =
          p.eval ((4 ^ k : ℚ) * (x : ℚ) + (q.2 : ℚ)) := by
    intro q hq
    have harg_nat : 4 ^ k * x + 2 * (q.2 / 2) = 4 ^ k * x + q.2 := by
      rcases deltaTerms_offset_even hq with ⟨a, ha⟩
      rw [ha]
      norm_num
    have harg_pos : 1 ≤ 4 ^ k * x + q.2 := by
      have hxpos : 0 < x := Nat.lt_of_lt_of_le Nat.zero_lt_one hx
      have hbase : 0 < 4 ^ k * x :=
        Nat.mul_pos (pow_pos (by norm_num) k) hxpos
      omega
    have hidx_succ :
        4 ^ k * x + 2 * (q.2 / 2) - 1 + 1 = 4 ^ k * x + q.2 := by
      rw [harg_nat]
      exact Nat.sub_add_cancel harg_pos
    rw [polyValueSeq_eval]
    congr 1
    rw [hidx_succ]
    norm_num
  let y : ℤ :=
    ((deltaTerms k).map fun q : ℤ × ℕ => q.1 * S (q.2 / 2)).sum
  have hy_mem : y ∈ SignedFS S := by
    have hy_mem_of :
        y ∈ SignedFSOf S
          (((deltaTerms k).map fun q : ℤ × ℕ => (q.1, q.2 / 2)).map
            fun q : ℤ × ℕ => q.2).toFinset := by
      simpa [y, List.map_map] using
        (signedFSOf_list_sum
          (s := S)
          (l := (deltaTerms k).map fun q : ℤ × ℕ => (q.1, q.2 / 2))
          hsign
          hnodup)
    exact signedFSOf_subset_signedFS S _
      hy_mem_of
  have hmap :
      (deltaTerms k).map
          (fun q : ℤ × ℕ => ((q.1 * S (q.2 / 2) : ℤ) : ℚ)) =
        (deltaTerms k).map (deltaTermValue k p (x : ℚ)) := by
    apply List.map_congr_left
    intro q hq
    simp [deltaTermValue, hS_eval q hq]
  have hy_eval : (y : ℚ) = (Delta k p).eval (x : ℚ) := by
    rw [Delta_eval_eq_deltaTerms]
    dsimp [y]
    norm_cast
    rw [List.map_map]
    change
      ((deltaTerms k).map
        (fun q : ℤ × ℕ => ((q.1 * S (q.2 / 2) : ℤ) : ℚ))).sum =
        ((deltaTerms k).map (deltaTermValue k p (x : ℚ))).sum
    rw [hmap]
  have hcast : (z : ℚ) = (y : ℚ) := by
    rw [hz, hy_eval]
  have hzy : z = y := by
    exact_mod_cast hcast
  rw [hzy]
  exact hy_mem

/-- The sequence of even positive inputs `p(2), p(4), p(6), ...`. -/
noncomputable def evenValueSeq (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ)) :
    ℕ → ℤ :=
  fun a => polyValueSeq p h_int_pos (2 * a + 1)

/-- If `Delta k p` is represented by a fixed integer `m` at every positive
natural input, then `m` lies in the signed finite subset sums of every tail of
the even-value sequence. -/
lemma Delta_constant_mem_signedFS_evenValueSeq_tail
    (k : ℕ) (hk : 0 < k) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    {m : ℤ}
    (hm_eval : ∀ x : ℕ, 1 ≤ x → (m : ℚ) = (Delta k p).eval (x : ℚ)) :
    ∀ N : ℕ, m ∈ SignedFS (tail (evenValueSeq p h_int_pos) N) := by
  intro N
  let x : ℕ := N + 1
  let A : ℕ := 2 * 4 ^ (k - 1) * x
  let M : ℕ := A - 1
  have hx : 1 ≤ x := by
    dsimp [x]
    omega
  have hpow_pos : 0 < 4 ^ (k - 1) := pow_pos (by norm_num) _
  have hA_ge_succ : N + 1 ≤ A := by
    calc
      N + 1 ≤ 4 ^ (k - 1) * (N + 1) :=
        Nat.le_mul_of_pos_left _ hpow_pos
      _ ≤ 2 * (4 ^ (k - 1) * (N + 1)) :=
        Nat.le_mul_of_pos_left _ (by norm_num)
      _ = A := by
        dsimp [A, x]
        ring
  have hA_pos : 1 ≤ A := (Nat.succ_le_succ (Nat.zero_le N)).trans hA_ge_succ
  have hM_ge : N ≤ M := by
    exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hA_ge_succ)
  have hbase : 4 ^ k * x = 2 * A := by
    dsimp [A]
    have hk_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    nth_rewrite 1 [hk_eq]
    rw [pow_succ]
    ring
  have hM_succ : M + 1 = A := by
    dsimp [M]
    exact Nat.sub_add_cancel hA_pos
  have hdelta :
      m ∈ SignedFS
        (fun a : ℕ => polyValueSeq p h_int_pos (4 ^ k * x + 2 * a - 1)) :=
    Delta_eval_integer_mem_signedFS_even_tail_polyValueSeq
      k p h_int_pos x hx m (hm_eval x hx)
  have hseq :
      (fun a : ℕ => polyValueSeq p h_int_pos (4 ^ k * x + 2 * a - 1)) =
        tail (evenValueSeq p h_int_pos) M := by
    funext a
    simp [tail, evenValueSeq]
    congr 1
    omega
  have hM : m ∈ SignedFS (tail (evenValueSeq p h_int_pos) M) := by
    rw [← signedFS_congr (by intro a; exact congrFun hseq a)]
    exact hdelta
  exact signedFS_tail_mono hM_ge hM

/-- Constant top-difference signed tails, together with residue coverage by a
second sequence, give Graham near-completeness. -/
lemma nearlyComplete_evenValueSeq_of_Delta_constant_and_residues
    (k : ℕ) (hk : 0 < k) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (m : ℕ) (hm : 0 < m)
    (hm_eval :
      ∀ x : ℕ, 1 ≤ x → ((m : ℤ) : ℚ) = (Delta k p).eval (x : ℚ))
    {T : ℕ → ℤ} (hres : CoversResidues T m) :
    NearlyComplete (interleave (evenValueSeq p h_int_pos) T) :=
  nearlyComplete_of_signed_tail_and_residues hm
    (Delta_constant_mem_signedFS_evenValueSeq_tail
      k hk p h_int_pos (m := (m : ℤ)) hm_eval)
    hres

/-- Tail version of the even-value near-completeness lemma. This is the form
used after a finite residue prefix has been separated from the later odd/even
tails. -/
lemma nearlyComplete_evenValueSeq_tail_of_Delta_constant_and_residues
    (r k : ℕ) (hk : 0 < k) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (m : ℕ) (hm : 0 < m)
    (hm_eval :
      ∀ x : ℕ, 1 ≤ x → ((m : ℤ) : ℚ) = (Delta k p).eval (x : ℚ))
    {T : ℕ → ℤ} (hres : CoversResidues T m) :
    NearlyComplete (interleave (tail (evenValueSeq p h_int_pos) r) T) := by
  refine nearlyComplete_of_signed_tail_and_residues hm ?_ hres
  intro N
  rw [tail_tail]
  exact Delta_constant_mem_signedFS_evenValueSeq_tail
    k hk p h_int_pos (m := (m : ℤ)) hm_eval (r + N)

/-! ## The odd polynomial tail is a Sigma-sequence -/

/-- Along any fixed odd-tail shape `f(2r + 1), f(2r + 3), ...`, consecutive
values are eventually within a factor of two. -/
lemma polyValueSeq_odd_tail_eventually_doubling
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hlead : 0 < p.leadingCoeff) (r : ℕ) :
    ∀ᶠ k in Filter.atTop,
      polyValueSeq p h_int_pos (2 * r + 2 * (k + 1)) ≤
        2 * polyValueSeq p h_int_pos (2 * r + 2 * k) := by
  have hratioQ :
      Tendsto
        (fun x : ℚ =>
          p.eval (2 * x + (2 * r + 3 : ℚ)) /
            p.eval (2 * x + (2 * r + 1 : ℚ)))
        Filter.atTop (nhds (1 : ℚ)) := by
    simpa using
      polynomial_eval_same_slope_ratio_tendsto_one
        (f := p) (a := 2) (b := (2 * r + 3 : ℚ))
        (c := (2 * r + 1 : ℚ)) (by norm_num) (ne_of_gt hlead)
  have hratioNat :
      Tendsto
        (fun k : ℕ =>
          p.eval (2 * (k : ℚ) + (2 * r + 3 : ℚ)) /
            p.eval (2 * (k : ℚ) + (2 * r + 1 : ℚ)))
        Filter.atTop (nhds (1 : ℚ)) := by
    simpa using hratioQ.comp (tendsto_natCast_atTop_atTop (R := ℚ))
  have hlt_event :
      ∀ᶠ k : ℕ in Filter.atTop,
        p.eval (2 * (k : ℚ) + (2 * r + 3 : ℚ)) /
            p.eval (2 * (k : ℚ) + (2 * r + 1 : ℚ)) < (2 : ℚ) :=
    hratioNat.eventually (eventually_lt_nhds (by norm_num : (1 : ℚ) < 2))
  filter_upwards [hlt_event] with k hk
  have hleft_eval :
      (polyValueSeq p h_int_pos (2 * r + 2 * (k + 1)) : ℚ) =
        p.eval (2 * (k : ℚ) + (2 * r + 3 : ℚ)) := by
    rw [polyValueSeq_eval]
    congr 1
    norm_num
    ring
  have hright_eval :
      (polyValueSeq p h_int_pos (2 * r + 2 * k) : ℚ) =
        p.eval (2 * (k : ℚ) + (2 * r + 1 : ℚ)) := by
    rw [polyValueSeq_eval]
    congr 1
    norm_num
    ring
  have hk_seq :
      (polyValueSeq p h_int_pos (2 * r + 2 * (k + 1)) : ℚ) /
          (polyValueSeq p h_int_pos (2 * r + 2 * k) : ℚ) < (2 : ℚ) := by
    simpa [hleft_eval, hright_eval] using hk
  have hden_pos :
      0 < (polyValueSeq p h_int_pos (2 * r + 2 * k) : ℚ) := by
    exact_mod_cast polyValueSeq_pos p h_int_pos (2 * r + 2 * k)
  have hlt_q :
      (polyValueSeq p h_int_pos (2 * r + 2 * (k + 1)) : ℚ) <
        2 * (polyValueSeq p h_int_pos (2 * r + 2 * k) : ℚ) :=
    (div_lt_iff₀ hden_pos).mp hk_seq
  have hlt_z :
      polyValueSeq p h_int_pos (2 * r + 2 * (k + 1)) <
        2 * polyValueSeq p h_int_pos (2 * r + 2 * k) := by
    exact_mod_cast hlt_q
  exact le_of_lt hlt_z

/-- The odd tail used in Graham's final split is a Sigma-sequence. -/
lemma polyValueSeq_odd_tail_sigmaSeq
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hlead : 0 < p.leadingCoeff) (r : ℕ) :
    SigmaSeq (fun k : ℕ => polyValueSeq p h_int_pos (2 * r + 2 * k)) := by
  refine sigma_of_eventually_doubling ?_ ?_
  · exact Filter.Eventually.of_forall
      (fun k => polyValueSeq_pos p h_int_pos (2 * r + 2 * k))
  · simpa using polyValueSeq_odd_tail_eventually_doubling p h_int_pos hlead r

/-! ## Conditional Graham assembly -/

/-- Conditional assembly of Graham's final complete sequence from the two
remaining mathematical inputs: a positive constant top difference and residue
coverage. This packages the already-formalized Sigma/near-complete glue. -/
lemma complete_interleaved_values_of_Delta_constant_and_residues
    (k : ℕ) (hk : 0 < k) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hlead : 0 < p.leadingCoeff)
    (m : ℕ) (hm : 0 < m)
    (hm_eval :
      ∀ x : ℕ, 1 ≤ x → ((m : ℤ) : ℚ) = (Delta k p).eval (x : ℚ))
    {T : ℕ → ℤ} (hres : CoversResidues T m) :
    Complete
      (interleave
        (fun n : ℕ => polyValueSeq p h_int_pos (2 * n))
        (interleave (evenValueSeq p h_int_pos) T)) := by
  have hsigma :
      SigmaSeq (fun n : ℕ => polyValueSeq p h_int_pos (2 * n)) := by
    exact SigmaSeq.congr
      (fun n => by simp)
      (polyValueSeq_odd_tail_sigmaSeq p h_int_pos hlead 0)
  exact complete_of_sigma_nearly
    hsigma
    (nearlyComplete_evenValueSeq_of_Delta_constant_and_residues
      k hk p h_int_pos m hm hm_eval hres)

/-- Shifted conditional assembly: a finite prefix can be reserved for residue
witnesses, while Graham's odd/even tails begin after that prefix. -/
lemma complete_interleaved_tail_values_of_Delta_constant_and_residues
    (r k : ℕ) (hk : 0 < k) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hlead : 0 < p.leadingCoeff)
    (m : ℕ) (hm : 0 < m)
    (hm_eval :
      ∀ x : ℕ, 1 ≤ x → ((m : ℤ) : ℚ) = (Delta k p).eval (x : ℚ))
    {T : ℕ → ℤ} (hres : CoversResidues T m) :
    Complete
      (interleave
        (fun n : ℕ => polyValueSeq p h_int_pos (2 * r + 2 * n))
        (interleave (tail (evenValueSeq p h_int_pos) r) T)) := by
  exact complete_of_sigma_nearly
    (polyValueSeq_odd_tail_sigmaSeq p h_int_pos hlead r)
    (nearlyComplete_evenValueSeq_tail_of_Delta_constant_and_residues
      r k hk p h_int_pos m hm hm_eval hres)

lemma shifted_interleaved_values_eq_oddEvenPrefixAssembly
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (r : ℕ) :
    (interleave
        (fun n : ℕ => polyValueSeq p h_int_pos (2 * r + 2 * n))
        (interleave (tail (evenValueSeq p h_int_pos) r)
          (finitePrefixSeq (polyValueSeq p h_int_pos) (2 * r)))) =
      oddEvenPrefixAssembly (polyValueSeq p h_int_pos) r := by
  have htail :
      tail (evenValueSeq p h_int_pos) r =
        fun n : ℕ => polyValueSeq p h_int_pos (2 * r + 2 * n + 1) := by
    funext n
    dsimp [tail, evenValueSeq]
    congr 1
    ring
  simp [oddEvenPrefixAssembly, htail]

/-- Shifted conditional assembly transferred back to the original polynomial
value sequence. The residue witnesses live in the finite prefix before `2*r`;
the Sigma/AP machinery uses the disjoint odd/even tails after `2*r`. -/
lemma complete_polyValueSeq_of_shifted_prefix_residues
    (r k : ℕ) (hk : 0 < k) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hlead : 0 < p.leadingCoeff)
    (m : ℕ) (hm : 0 < m)
    (hm_eval :
      ∀ x : ℕ, 1 ≤ x → ((m : ℤ) : ℚ) = (Delta k p).eval (x : ℚ))
    (hres : CoversResidues (finitePrefixSeq (polyValueSeq p h_int_pos) (2 * r)) m) :
    Complete (polyValueSeq p h_int_pos) := by
  let shifted : ℕ → ℤ :=
    interleave
      (fun n : ℕ => polyValueSeq p h_int_pos (2 * r + 2 * n))
      (interleave (tail (evenValueSeq p h_int_pos) r)
        (finitePrefixSeq (polyValueSeq p h_int_pos) (2 * r)))
  have hshifted : Complete shifted :=
    complete_interleaved_tail_values_of_Delta_constant_and_residues
      r k hk p h_int_pos hlead m hm hm_eval hres
  have hassembly : Complete (oddEvenPrefixAssembly (polyValueSeq p h_int_pos) r) := by
    exact Complete.congr
      (fun n => congrFun
        (shifted_interleaved_values_eq_oddEvenPrefixAssembly p h_int_pos r) n)
      hshifted
  exact Complete.of_oddEvenPrefixAssembly r hassembly

/-- Conditional assembly transferred all the way back to the original value
sequence, assuming residue coverage by the full value sequence. The finite
prefix needed by Graham is extracted automatically. -/
lemma complete_polyValueSeq_of_residues
    (k : ℕ) (hk : 0 < k) (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hlead : 0 < p.leadingCoeff)
    (m : ℕ) (hm : 0 < m)
    (hm_eval :
      ∀ x : ℕ, 1 ≤ x → ((m : ℤ) : ℚ) = (Delta k p).eval (x : ℚ))
    (hres : CoversResidues (polyValueSeq p h_int_pos) m) :
    Complete (polyValueSeq p h_int_pos) := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨N, hprefix⟩ := hres.exists_finitePrefixSeq
  have hprefix_two :
      CoversResidues (finitePrefixSeq (polyValueSeq p h_int_pos) (2 * N)) m :=
    CoversResidues.finitePrefixSeq_mono (S := polyValueSeq p h_int_pos)
      (by omega) hprefix
  exact complete_polyValueSeq_of_shifted_prefix_residues
    N k hk p h_int_pos hlead m hm hm_eval hprefix_two

/-- Top-difference version of `complete_polyValueSeq_of_residues`. At this
point the only remaining mathematical input is residue coverage modulo the
positive top-difference constant. -/
lemma exists_complete_polyValueSeq_of_residues
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hdeg : 0 < p.natDegree)
    (hlead : 0 < p.leadingCoeff) :
    ∃ m : ℕ, 0 < m ∧
      (CoversResidues (polyValueSeq p h_int_pos) m →
        Complete (polyValueSeq p h_int_pos)) := by
  obtain ⟨m, hm_pos, hm_eval⟩ :=
    Delta_top_positive_integer_constant p h_int_pos hlead
  refine ⟨m, hm_pos, ?_⟩
  intro hres
  exact complete_polyValueSeq_of_residues
    p.natDegree hdeg p h_int_pos hlead m hm_pos hm_eval hres

/-- Final assembly in Graham's frequent-generator language, transferred to the
original polynomial value sequence. This is the target interface for the
remaining residue-cover proof. -/
lemma exists_complete_polyValueSeq_of_frequent_generators
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hdeg : 0 < p.natDegree)
    (hlead : 0 < p.leadingCoeff) :
    ∃ m : ℕ, 0 < m ∧
      ∀ {w : ℕ} (ρ : Fin w → ZMod m),
        AddSubgroup.closure (Set.range ρ) = ⊤ →
        (∀ i : Fin w, ∀ N : ℕ,
          ∃ n : ℕ, N ≤ n ∧
            ((polyValueSeq p h_int_pos n : ℤ) : ZMod m) = ρ i) →
        Complete (polyValueSeq p h_int_pos) := by
  obtain ⟨m, hm_pos, hcomplete⟩ :=
    exists_complete_polyValueSeq_of_residues p h_int_pos hdeg hlead
  refine ⟨m, hm_pos, ?_⟩
  intro w ρ hgen hfreq
  exact hcomplete (coversResidues_of_frequent_generators (by omega) ρ hgen hfreq)

/-- Final assembly reduced to a finite Bezout combination of actual polynomial
value residues. Periodicity supplies the required frequent recurrence of each
chosen residue. -/
lemma exists_complete_polyValueSeq_of_index_zsmul_eq_one
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hdeg : 0 < p.natDegree)
    (hlead : 0 < p.leadingCoeff) :
    ∃ m : ℕ, 0 < m ∧
      ∀ {w : ℕ} (idx : Fin w → ℕ) (a : Fin w → ℤ),
        (∑ i, a i • (((polyValueSeq p h_int_pos (idx i) : ℤ) : ZMod m)) =
          (1 : ZMod m)) →
        Complete (polyValueSeq p h_int_pos) := by
  obtain ⟨m, hm_pos, hcomplete⟩ :=
    exists_complete_polyValueSeq_of_residues p h_int_pos hdeg hlead
  refine ⟨m, hm_pos, ?_⟩
  intro w idx a ha
  let ρ : Fin w → ZMod m :=
    fun i => ((polyValueSeq p h_int_pos (idx i) : ℤ) : ZMod m)
  have hfreq : ∀ i : Fin w, ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧
        ((polyValueSeq p h_int_pos n : ℤ) : ZMod m) = ρ i := by
    intro i N
    exact polyValueSeq_residue_frequently_equal p h_int_pos m (by omega) (idx i) N
  exact hcomplete
    (coversResidues_of_frequent_zsmul_eq_one (by omega) ρ a (by simpa [ρ] using ha) hfreq)

/-- Graham's no-fixed-prime condition gives the finite Bezout input needed by
`exists_complete_polyValueSeq_of_index_zsmul_eq_one`, hence completeness of the
chosen integer value sequence. -/
lemma complete_polyValueSeq_of_no_fixed_prime
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hdeg : 0 < p.natDegree)
    (hlead : 0 < p.leadingCoeff)
    (h_gcd_one :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ n : ℕ, 1 ≤ n ∧ ∃ z : ℤ,
          (z : ℚ) = p.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z)) :
    Complete (polyValueSeq p h_int_pos) := by
  classical
  obtain ⟨m, hm_pos, hcomplete⟩ :=
    exists_complete_polyValueSeq_of_index_zsmul_eq_one p h_int_pos hdeg hlead
  let P : Finset ℕ := m.primeFactors
  let e : Fin P.card ≃ P := (Finset.equivFin P).symm
  let q : Fin P.card → ℕ := fun i => (e i).1
  have hq_mem : ∀ i : Fin P.card, q i ∈ m.primeFactors := by
    intro i
    exact (e i).2
  have hq_prime : ∀ i : Fin P.card, (q i).Prime := by
    intro i
    exact (Nat.mem_primeFactors.mp (hq_mem i)).1
  let n : Fin P.card → ℕ :=
    fun i => Classical.choose (h_gcd_one (q i) (hq_prime i))
  have hn_spec : ∀ i : Fin P.card,
      1 ≤ n i ∧ ∃ z : ℤ,
        (z : ℚ) = p.eval (n i : ℚ) ∧ ¬ ((q i : ℤ) ∣ z) := by
    intro i
    exact Classical.choose_spec (h_gcd_one (q i) (hq_prime i))
  let idx : Fin P.card → ℕ := fun i => n i - 1
  let v : Fin P.card → ℤ := fun i => polyValueSeq p h_int_pos (idx i)
  have hq_not_dvd : ∀ i : Fin P.card, ¬ ((q i : ℤ) ∣ v i) := by
    intro i hdiv
    rcases hn_spec i with ⟨hn_pos, z, hz_eval, hz_not_dvd⟩
    have hn_sub : n i - 1 + 1 = n i := Nat.sub_add_cancel hn_pos
    have hz_eq : z = polyValueSeq p h_int_pos (idx i) := by
      apply eq_polyValueSeq_of_eval
      simpa [idx, hn_sub] using hz_eval
    exact hz_not_dvd (by simpa [v, hz_eq] using hdiv)
  have hcover : ∀ k : ℕ, k.Prime → k ∣ m →
      ∃ i : Fin P.card, ¬ ((k : ℤ) ∣ v i) := by
    intro k hkprime hkm
    have hkmem : k ∈ P := by
      exact Nat.mem_primeFactors.mpr ⟨hkprime, hkm, Nat.ne_of_gt hm_pos⟩
    let i : Fin P.card := e.symm ⟨k, hkmem⟩
    refine ⟨i, ?_⟩
    have hqi : q i = k := by
      simp [q, i, e]
    simpa [hqi] using hq_not_dvd i
  have hcop : Nat.Coprime m (intGcdFin P.card v) :=
    intGcdFin_coprime_of_primeFactors_covered v hcover
  obtain ⟨a, ha⟩ := exists_zmod_sum_zsmul_eq_one_of_intGcdFin_coprime v hcop
  exact hcomplete idx a (by simpa [v] using ha)

/-- Graham's complete polynomial values theorem, in the positive-input rational
polynomial shape used by the P283/P351 `roth_szekeres_graham` wrapper. -/
theorem graham_complete_polynomial_values
    (f : ℚ[X])
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
        (X : ℚ) = ∑ i ∈ I, f.eval ((i + 1 : ℕ) : ℚ) :=
  complete_polyValueSeq_to_eval_subsets
    (complete_polyValueSeq_of_no_fixed_prime
      f h_int_pos h_nonconst h_lead_pos h_gcd_one)

/-- The same conditional assembly with Graham's positive top-difference
constant chosen from the polynomial. The only remaining external input is
residue coverage modulo that chosen constant. -/
lemma exists_complete_interleaved_values_of_residues
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hdeg : 0 < p.natDegree)
    (hlead : 0 < p.leadingCoeff) :
    ∃ m : ℕ, 0 < m ∧
      ∀ {T : ℕ → ℤ}, CoversResidues T m →
        Complete
          (interleave
            (fun n : ℕ => polyValueSeq p h_int_pos (2 * n))
            (interleave (evenValueSeq p h_int_pos) T)) := by
  obtain ⟨m, hm_pos, hm_eval⟩ :=
    Delta_top_positive_integer_constant p h_int_pos hlead
  refine ⟨m, hm_pos, ?_⟩
  intro T hres
  exact complete_interleaved_values_of_Delta_constant_and_residues
    p.natDegree hdeg p h_int_pos hlead m hm_pos hm_eval hres

/-- Conditional final assembly phrased in Graham's residue-generator language.
Once the top-difference modulus is fixed, it is enough to find finitely many
frequently occurring residues whose additive closure is all of `ZMod m`. -/
lemma exists_complete_interleaved_values_of_frequent_generators
    (p : ℚ[X])
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = p.eval (n : ℚ))
    (hdeg : 0 < p.natDegree)
    (hlead : 0 < p.leadingCoeff) :
    ∃ m : ℕ, 0 < m ∧
      ∀ {w : ℕ} (ρ : Fin w → ZMod m),
        AddSubgroup.closure (Set.range ρ) = ⊤ →
        (∀ i : Fin w, ∀ N : ℕ,
          ∃ n : ℕ, N ≤ n ∧
            ((polyValueSeq p h_int_pos n : ℤ) : ZMod m) = ρ i) →
        Complete
          (interleave
            (fun n : ℕ => polyValueSeq p h_int_pos (2 * n))
            (interleave (evenValueSeq p h_int_pos) (polyValueSeq p h_int_pos))) := by
  obtain ⟨m, hm_pos, hcomplete⟩ :=
    exists_complete_interleaved_values_of_residues p h_int_pos hdeg hlead
  refine ⟨m, hm_pos, ?_⟩
  intro w ρ hgen hfreq
  exact hcomplete
    (T := polyValueSeq p h_int_pos)
    (coversResidues_of_frequent_generators (by omega) ρ hgen hfreq)

end Erdos.P283.RSG
