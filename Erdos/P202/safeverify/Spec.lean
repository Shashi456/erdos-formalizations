/-
SafeVerify target for Erdős Problem 202.

This file records the public statement, the four named trust-boundary inputs,
and the major conditional theorem surface. The bodies here are `sorry` by
design: SafeVerify compares these declarations with the submitted `.olean` and
checks that the submitted proofs depend only on the allow-list:

  Mathlib core (`propext`, `Classical.choice`, `Quot.sound`)
  + `Erdos202.spread_disjointness_input`
  + `Erdos202.bfv_pruning_input`
  + `Erdos202.bfv_omega_count_input`
  + `Erdos202.bfv_lower_bound_input`

The current P202 development is not ready for SafeVerify replay yet because
`chain_step_selected_block_bound`, the final estimate used by `chain_step`,
still has a `sorry` body in the submission.
-/

import Mathlib

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Statement layer -/

def residueClass (q : ℕ) (a : ℤ) : Set ℤ := sorry

abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop := sorry

def Admissible (N : ℕ) (Q : Finset ℕ) : Prop := sorry

def PossibleCard (N r : ℕ) : Prop := sorry

noncomputable def f (N : ℕ) : ℕ := sorry

noncomputable def Zscale (N : ℕ) : ℝ := sorry

noncomputable def Lscale (α : ℝ) (N : ℕ) : ℝ := sorry

noncomputable def Mscale (N : ℕ) : ℝ := sorry

def HasErdos202Asymptotic (F : ℕ → ℕ) : Prop := sorry

def Erdos202Statement : Prop := sorry

lemma residueClass_inter_nonempty_iff
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (a b : ℤ) :
    (residueClass q a ∩ residueClass r b).Nonempty ↔
      a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := sorry

lemma residueClass_disjoint_iff
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (a b : ℤ) :
    Disjoint (residueClass q a) (residueClass r b) ↔
      ¬ a ≡ b [ZMOD (Nat.gcd q r : ℤ)] := sorry

/-! ## Arithmetic and spread inputs -/

def primeSupport (n : ℕ) : Finset ℕ := sorry
def omega (n : ℕ) : ℕ := sorry
def rad (n : ℕ) : ℕ := sorry
def hExp (n : ℕ) : ℕ := sorry
def exactBlock (C : Finset ℕ) (q : ℕ) : ℕ := sorry

def UniformFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (k : ℕ) : Prop := sorry

def SpreadFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (κ : ℝ) : Prop := sorry

def PairwiseDisjointMembers {α : Type*} [DecidableEq α]
    (B : Finset (Finset α)) : Prop := sorry

axiom spread_disjointness_input :
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
        B ⊆ A ∧ B.card = r ∧ PairwiseDisjointMembers B

theorem dense_core_from_spread :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ {α : Type*} [DecidableEq α]
        (A : Finset (Finset α)) (k K : ℕ),
        A.Nonempty →
        1 ≤ k → k ≤ K →
        UniformFamily A k →
        (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
        ∃ C : Finset α,
          C.Nonempty ∧
          ((A.filter fun S => C ⊆ S).card : ℝ) >
            (A.card : ℝ) /
              (C0 * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card := sorry

/-! ## BFV inputs and chain surface -/

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

axiom bfv_pruning_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
      (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
      PairwiseDisjointResidues Q a →
      (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
      ∃ D : PrunedData N,
        (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N

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

axiom bfv_lower_bound_input :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ)

structure ChainState (N : ℕ) (D : PrunedData N) where
  r : ℕ
  blocks : List ℕ
  blocks_length : blocks.length = r
  Qsurv : Finset ℕ
  Qsurv_subset : Qsurv ⊆ D.Q
  Qsurv_nonempty : Qsurv.Nonempty
  W : ℕ
  productP : ℕ
  product_eq : productP = (blocks.foldr (· * ·) 1)
  blocks_pos : ∀ P ∈ blocks, 0 < P
  productP_pos : 0 < productP
  pairwise_coprime : blocks.Pairwise Nat.Coprime
  exact_divides : ∀ q ∈ Qsurv, productP ∣ q
  no_selected_prime_remains :
    ∀ q ∈ Qsurv, ∀ p ∈ primeSupport productP,
      p ∉ primeSupport (q / productP)
  residues_agree :
    ∀ qi ∈ Qsurv, ∀ rj ∈ Qsurv,
      ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
        D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (productP : ℤ)]
  W_eq : W = omega productP
  W_le_K : W ≤ D.K

def ChainState.BlocksOmegaPos {N : ℕ} {D : PrunedData N}
    (_S : ChainState N D) : Prop := sorry

noncomputable def chainT {N : ℕ} {D : PrunedData N} (_S : ChainState N D) : ℕ :=
  sorry

noncomputable def chainLambda {N : ℕ} (_D : PrunedData N) : ℝ := sorry

def ChainState.HasLowerBound {N : ℕ} {D : PrunedData N}
    (_S : ChainState N D) (_Λ : ℝ) : Prop := sorry

noncomputable def chainStepBound {N : ℕ} {D : PrunedData N}
    (_ε : ℝ) (_S : ChainState N D) : ℝ := sorry

noncomputable def chainProductBound {N : ℕ} {D : PrunedData N}
    (_ε : ℝ) (_S : ChainState N D) : ℝ := sorry

noncomputable def initialChainState (N : ℕ) (D : PrunedData N) : ChainState N D :=
  sorry

theorem chain_step
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
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
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBound ε S := sorry

theorem chain_inequality
    (N : ℕ) (D : PrunedData N) (ε : ℝ) (hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
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
      (S.productP : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) ^ R
        * Real.exp ((R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        * Real.exp (((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := sorry

/-! ## Optimization and public theorem surface -/

lemma sum_inv_sq_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := sorry

lemma quad_bound (c σ : ℝ) : c * σ - c ^ 2 / 4 ≤ σ ^ 2 := sorry

lemma chain_T_bound
    {R K : ℕ} (hRK : R ≤ K)
    (w : Fin R → ℕ) (hw_pos : ∀ j, 1 ≤ w j)
    (hw_sum : (∑ j, w j) = K) :
    (∑ j : Fin R, (R - j.1) * w j) * 2 ≤ 2 * R * K - R * (R - 1) := sorry

noncomputable def sigmaN (N : ℕ) (Qcard : ℕ) : ℝ := sorry

theorem sigma_lower_bound :
    ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
      ∀ Qcard : ℕ, 1 ≤ Qcard →
        (∃ D : PrunedData N, D.Q.card = Qcard) →
        1 - η ≤ sigmaN N Qcard := sorry

theorem f_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N := sorry

theorem erdos202_upper_bound_from_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N := sorry

theorem erdos202_main : Erdos202Statement := sorry

end Erdos202
