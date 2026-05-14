/-
SafeVerify target for Erdős Problem 202.

This is the external contract for the flattened proof in
`Erdos/P202/Proof.lean`.  The bodies in this file are placeholders by design:
SafeVerify compares the matching declarations in the submitted `.olean` and
checks that their axiom dependencies stay within the allowed core set
(`propext`, `Classical.choice`, `Quot.sound`).
-/

import Mathlib

set_option autoImplicit false

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## Basic public vocabulary -/

def residueClass (q : ℕ) (a : ℤ) : Set ℤ :=
  {n : ℤ | n ≡ a [ZMOD (q : ℤ)]}

abbrev ResidueAssignment (Q : Finset ℕ) : Type :=
  {q : ℕ // q ∈ Q} → ℤ

def PairwiseDisjointResidues
    (Q : Finset ℕ) (a : ResidueAssignment Q) : Prop :=
  ∀ i j : {q : ℕ // q ∈ Q}, i ≠ j →
    Disjoint (residueClass i.1 (a i)) (residueClass j.1 (a j))

def Admissible (N : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

def UniformFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ S ∈ A, S.card = k

def SpreadFamily {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (κ : ℝ) : Prop :=
  ∀ T : Finset α, T.Nonempty →
    ((A.filter fun S => T ⊆ S).card : ℝ) ≤
      (A.card : ℝ) / κ ^ T.card

def PairwiseDisjointMembers {α : Type*} [DecidableEq α]
    (B : Finset (Finset α)) : Prop :=
  ∀ S ∈ B, ∀ T ∈ B, S ≠ T → Disjoint S T

noncomputable def f (_N : ℕ) : ℕ := by
  sorry

noncomputable def Zscale (_N : ℕ) : ℝ := by
  sorry

noncomputable def Lscale (_α : ℝ) (_N : ℕ) : ℝ := by
  sorry

noncomputable def Mscale (_N : ℕ) : ℝ := by
  sorry

def omega (_n : ℕ) : ℕ := by
  sorry

def rad (_n : ℕ) : ℕ := by
  sorry

def hExp (_n : ℕ) : ℕ := by
  sorry

def HasErdos202Asymptotic (F : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) * Lscale (-(1 + ε)) N ≤ (F N : ℝ) ∧
    (F N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N

def Erdos202Statement : Prop :=
  HasErdos202Asymptotic f

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

/-! ## Park--Pham surface -/

namespace ParkPham

def IncreasingIn {α : Type*}
    (_X : Finset α) (_U : Finset (Finset α)) : Prop :=
  by
    sorry

def pSmall {α : Type*}
    (_X : Finset α) (_U : Finset (Finset α)) (_q : ℝ) : Prop :=
  by
    sorry

noncomputable def muP {α : Type*} [DecidableEq α]
    (_X : Finset α) (_U : Finset (Finset α)) (_p : ℝ) : ℝ :=
  by
    sorry

noncomputable def ell {α : Type*} [DecidableEq α]
    (_X : Finset α) (_U : Finset (Finset α)) : ℕ :=
  by
    sorry

theorem park_pham_threshold_not_small_lt_exists :
    ∃ CKK : ℝ, 0 < CKK ∧
      ∀ {α : Type*} [DecidableEq α]
        (X : Finset α) (U : Finset (Finset α)) (q : ℝ),
        0 < q → q ≤ 1 →
        CKK * q * Real.log (ell X U) < 1 →
        (∀ S ∈ U, S ⊆ X) →
        IncreasingIn X U →
        ¬ pSmall X U q →
        muP X U (CKK * q * Real.log (ell X U)) ≥ 1 / 2 := by
  sorry

universe u_2

theorem spread_disjointness_theorem :
    ∃ Csp : ℝ, 0 < Csp ∧
      ∀ {α : Type u_2} [DecidableEq α]
        (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
        A.Nonempty →
        2 ≤ r →
        1 ≤ k →
        Erdos202.UniformFamily A k →
        Erdos202.SpreadFamily A κ →
        Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
        ∃ B : Finset (Finset α),
          B ⊆ A ∧ B.card = r ∧ Erdos202.PairwiseDisjointMembers B := by
  sorry

end ParkPham

/-! ## BFV and public theorem surfaces -/

theorem bfv_omega_count_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  sorry

theorem bfv_lower_bound_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * Lscale (-(1 + ε)) N ≤ (f N : ℝ) := by
  sorry

theorem bfv_pruning_theorem :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        (Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N := by
  sorry

theorem erdos202_upper_bound_from_inputs :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      (f N : ℝ) ≤ (N : ℝ) * Lscale (-(1 - ε)) N := by
  sorry

theorem erdos202_main : Erdos202Statement := by
  sorry

end Erdos202
