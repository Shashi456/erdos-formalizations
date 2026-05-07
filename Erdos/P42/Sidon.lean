/-
Erdős Problem 42 — Sidon predicates and the elementary cardinality / difference
lemmas every route depends on.

We define `IsSidonInt` over `Finset ℤ` (the natural setting for the analytic
proof) and `IsSidonNat` over `Finset ℕ` / `Set ℕ` (the FC-aligned setting).
Bridge lemmas live in `FCWrapper.lean`.
-/

import Erdos.P42.Basic

namespace Erdos42

open Finset

/-- A `Finset ℤ` is Sidon iff all unordered pair-sums are distinct, i.e. no
nontrivial additive collision `a₁ + a₂ = a₃ + a₄` with `{a₁, a₂} ≠ {a₃, a₄}`. -/
def IsSidonInt (A : Finset ℤ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-- A `Finset ℕ` is Sidon under the same rule. -/
def IsSidonNat (A : Finset ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-- A `Finset (ZMod p)` is Sidon under the same rule. -/
def IsSidonZMod {p : ℕ} (A : Finset (ZMod p)) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

lemma isSidonInt_empty : IsSidonInt ∅ := by
  intro a₁ ha₁
  simp at ha₁

lemma IsSidonInt.mono {A B : Finset ℤ} (hB : IsSidonInt B) (hAB : A ⊆ B) :
    IsSidonInt A := by
  intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
  exact hB (hAB ha₁) (hAB ha₂) (hAB ha₃) (hAB ha₄) hsum

/-! ## Elementary cardinality bounds (TODO) -/

/-- For `A ⊆ {1, …, N}` Sidon, the nonzero differences `(A - A) \ {0}` have
cardinality at most `2N - 2` (equals `|A|(|A|-1)`). -/
theorem sidon_nonzero_diff_card_le
    (A : Finset ℤ) (N : ℕ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (_hSidon : IsSidonInt A) :
    ((DiffFinset A A).erase 0).card ≤ 2 * N - 2 := by
  classical
  let box : Finset ℤ := (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0
  have hsub : (DiffFinset A A).erase 0 ⊆ box := by
    intro d hd
    rw [Finset.mem_erase] at hd
    rcases hd with ⟨hd0, hdDiff⟩
    rw [mem_diffFinset] at hdDiff
    rcases hdDiff with ⟨a, ha, b, hb, rfl⟩
    obtain ⟨ha1, haN⟩ := hAint a ha
    obtain ⟨hb1, hbN⟩ := hAint b hb
    change a - b ∈ (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0
    rw [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨hd0, ?_, ?_⟩ <;> linarith
  refine (Finset.card_le_card hsub).trans ?_
  by_cases hN : N = 0
  · subst N
    simp [box]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have h0 : (0 : ℤ) ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hcard_int :
        ((box.card : ℤ) = (2 * N - 2 : ℕ)) := by
      change
        ((((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0).card : ℤ) =
          (2 * N - 2 : ℕ))
      rw [Finset.card_erase_of_mem h0]
      have hIcc :
          (((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).card : ℤ) =
            2 * (N : ℤ) - 1) := by
        rw [Int.card_Icc_of_le]
        · ring
        · omega
      omega
    exact le_of_eq (Int.ofNat_inj.mp hcard_int)

/-- For `A ⊆ {1, …, N}` Sidon, `binomial(|A|, 2) ≤ N - 1`. Standard counting:
the `binomial(|A|, 2)` positive differences are distinct elements of
`{1, …, N-1}`. -/
theorem sidon_choose_two_le_interval
    (A : Finset ℤ) (N : ℕ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    Nat.choose A.card 2 ≤ N - 1 := by
  classical
  let f : ℤ × ℤ → ℤ := fun ab => ab.1 - ab.2
  have hmaps : Set.MapsTo f (A.offDiag : Set (ℤ × ℤ)) ((DiffFinset A A).erase 0 : Set ℤ) := by
    intro ab hab
    have habFin : ab ∈ A.offDiag := by simpa using hab
    rw [Finset.mem_offDiag] at habFin
    rcases habFin with ⟨ha, hb, hne⟩
    change ab.1 - ab.2 ∈ (DiffFinset A A).erase 0
    rw [Finset.mem_erase, mem_diffFinset]
    exact ⟨sub_ne_zero.mpr hne, ⟨ab.1, ha, ab.2, hb, rfl⟩⟩
  have hinj : (A.offDiag : Set (ℤ × ℤ)).InjOn f := by
    intro ab hab cd hcd hdiff
    have habFin : ab ∈ A.offDiag := by simpa using hab
    have hcdFin : cd ∈ A.offDiag := by simpa using hcd
    rw [Finset.mem_offDiag] at habFin hcdFin
    rcases habFin with ⟨hab1, hab2, hab_ne⟩
    rcases hcdFin with ⟨hcd1, hcd2, _hcd_ne⟩
    have hsum : ab.1 + cd.2 = cd.1 + ab.2 := by
      dsimp [f] at hdiff
      linarith
    rcases hSidon hab1 hcd2 hcd1 hab2 hsum with h | h
    · exact Prod.ext h.1 h.2.symm
    · exact False.elim (hab_ne h.1)
  have hoff_le :
      A.offDiag.card ≤ ((DiffFinset A A).erase 0).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hordered_le : A.card * A.card - A.card ≤ 2 * N - 2 := by
    rw [← Finset.offDiag_card]
    exact hoff_le.trans (sidon_nonzero_diff_card_le A N hAint hSidon)
  have hdiv :
      (A.card * A.card - A.card) / 2 ≤ (2 * N - 2) / 2 :=
    Nat.div_le_div_right (a := A.card * A.card - A.card) (b := 2 * N - 2) (c := 2)
      hordered_le
  rw [Nat.choose_two_right]
  have hleft : A.card * (A.card - 1) = A.card * A.card - A.card := by
    rw [Nat.mul_sub_one]
  have hright : (2 * N - 2) / 2 = N - 1 := by omega
  simpa [hleft, hright] using hdiv

/-! ## Difference-set helpers -/

lemma diffFinset_erase_zero_card_le_offDiag_card (A : Finset ℤ) :
    ((DiffFinset A A).erase 0).card ≤ A.card * A.card - A.card := by
  classical
  let f : ℤ × ℤ → ℤ := fun ab => ab.1 - ab.2
  have hsub : (DiffFinset A A).erase 0 ⊆ A.offDiag.image f := by
    intro d hd
    rw [Finset.mem_erase, mem_diffFinset] at hd
    rcases hd with ⟨hd0, a, ha, b, hb, rfl⟩
    have hab : a ≠ b := sub_ne_zero.mp hd0
    exact Finset.mem_image.mpr ⟨(a, b), by
      rw [Finset.mem_offDiag]
      exact ⟨ha, hb, hab⟩, rfl⟩
  calc
    ((DiffFinset A A).erase 0).card ≤ (A.offDiag.image f).card := Finset.card_le_card hsub
    _ ≤ A.offDiag.card := Finset.card_image_le
    _ = A.card * A.card - A.card := by rw [Finset.offDiag_card]

lemma diffFinset_self_symmetric (A : Finset ℤ) :
    SymmetricFinset (DiffFinset A A) := by
  intro x
  simp only [mem_diffFinset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, by ring⟩
  · rintro ⟨a, ha, b, hb, h⟩; exact ⟨b, hb, a, ha, by linarith⟩

lemma zero_mem_diffFinset_self {A : Finset ℤ} (hA : A.Nonempty) :
    (0 : ℤ) ∈ DiffFinset A A := by
  obtain ⟨a, ha⟩ := hA
  exact mem_diffFinset.mpr ⟨a, ha, a, ha, by ring⟩

end Erdos42
