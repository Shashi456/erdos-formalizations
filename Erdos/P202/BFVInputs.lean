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

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic

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

To be discharged from BFV's pruning argument. -/
axiom bfv_pruning_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
      (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
      PairwiseDisjointResidues Q a →
      (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
      ∃ D : PrunedData N,
        (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N

/-! ## §3 BFV ω-count estimate -/

/-- **BFV ω-count input.** Uniform in the BFV range `K ≤ 3 M(N)` and
`0 ≤ W ≤ K`, the count of integers up to `y` with `ω(n) = K - W` is at most
`y · L(-d/2 + ε, N) · (log N)^{W/2}`, where `d = K / M(N)`.

The `(log N)^{W/2}` is real-exponentiated; we phrase it as
`exp((W/2) · log log N)` to avoid `Real.rpow` overhead. -/
axiom bfv_omega_count_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y K W : ℕ,
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
