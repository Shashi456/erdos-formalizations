/-
Erdős Problem 42 — `formal-conjectures` wrapper, Route B (compact-Cayley).

Mirrors `FC/Local.lean` but invokes
`Erdos42.CompactCayley.theorem_1_1_from_compact_cayley` instead of the
Route A finite-Fourier-avoidance theorem. Since `compact_cayley_clique` is now
proved (no Route B axiom), the resulting `theorem_1_1_via_cayley` and
`erdos_42_via_cayley` depend only on Mathlib core
(`propext`, `Classical.choice`, `Quot.sound`).

The `IsSidon`, `IsMaximalSidonSetIn`, and `isSidonInt_of_isSidon` definitions
and the bridge proof are reused from `FC/Local.lean`; only the call site for
the underlying `Finset ℤ` theorem differs.
-/

import Erdos.P42.FC.Local
import Erdos.P42.FC.Shape
import Erdos.P42.CompactCayley.Main

namespace Erdos42

open Filter Set
open scoped Pointwise

/-! ## §1 Theorem 1.1 (the Erdős statement, Route B) -/

/-- **Theorem 1.1 (Erdős #42), Route B variant.** Same statement as
`Erdos42.theorem_1_1` but proved through the axiom-free
`CompactCayley.theorem_1_1_from_compact_cayley`. -/
theorem theorem_1_1_via_cayley :
    ∀ M : ℕ, 1 ≤ M → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 N → IsSidon A → A.Nonempty →
        ∃ B : Set ℕ, B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
          ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  intro M hM
  classical
  obtain ⟨N₀, hN₀⟩ := CompactCayley.theorem_1_1_from_compact_cayley M hM
  refine ⟨N₀, ?_⟩
  intro N hN A hAint hSidon hAnonempty
  obtain ⟨A', hA'int, hA'sidon, _hAcard, hA'mem⟩ :=
    isSidonInt_of_isSidon (A := A) (N := N) hAint hSidon
  have hA'nonempty : A'.Nonempty := by
    obtain ⟨a, ha⟩ := hAnonempty
    exact ⟨(a : ℤ), (hA'mem a).mp ha⟩
  obtain ⟨B', hB'int, hB'sidon, hB'card, hAvoid⟩ :=
    hN₀ N hN A' hA'int hA'sidon hA'nonempty
  let Bn : Finset ℕ := B'.image Int.toNat
  let B : Set ℕ := (Bn : Set ℕ)
  have hB'_nonneg : ∀ b ∈ B', 0 ≤ b := by
    intro b hb
    exact le_trans (by norm_num) (hB'int b hb).1
  have hB'_mem_nat : ∀ x : ℕ, x ∈ B ↔ ((x : ℤ) ∈ B') := by
    intro x
    constructor
    · intro hx
      change x ∈ Bn at hx
      change x ∈ B'.image Int.toNat at hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨z, hz, hzx⟩
      have hz_nonneg : 0 ≤ z := hB'_nonneg z hz
      have hz_cast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
      rw [← hzx, hz_cast]
      exact hz
    · intro hx
      change x ∈ Bn
      change x ∈ B'.image Int.toNat
      rw [Finset.mem_image]
      refine ⟨(x : ℤ), hx, ?_⟩
      simp
  have hBn_card : Bn.card = B'.card := by
    change (B'.image Int.toNat).card = B'.card
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx_nonneg : 0 ≤ x := hB'_nonneg x hx
    have hy_nonneg : 0 ≤ y := hB'_nonneg y hy
    calc
      x = (x.toNat : ℤ) := (Int.toNat_of_nonneg hx_nonneg).symm
      _ = (y.toNat : ℤ) := by rw [hxy]
      _ = y := Int.toNat_of_nonneg hy_nonneg
  have hBn_cardM : Bn.card = M := by
    rw [hBn_card, hB'card]
  have hB_nonempty : B.Nonempty := by
    have hBn_pos : 0 < Bn.card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hBn_pos
    exact ⟨b, hb⟩
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hb' : (b : ℤ) ∈ B' := (hB'_mem_nat b).mp hb
    have hb_bounds := hB'int (b : ℤ) hb'
    exact_mod_cast hb_bounds
  · intro b₁ hb₁ b₂ hb₂ b₃ hb₃ b₄ hb₄ hsum
    have hb₁' : (b₁ : ℤ) ∈ B' := (hB'_mem_nat b₁).mp hb₁
    have hb₂' : (b₂ : ℤ) ∈ B' := (hB'_mem_nat b₂).mp hb₂
    have hb₃' : (b₃ : ℤ) ∈ B' := (hB'_mem_nat b₃).mp hb₃
    have hb₄' : (b₄ : ℤ) ∈ B' := (hB'_mem_nat b₄).mp hb₄
    have hsum_int : (b₁ : ℤ) + (b₂ : ℤ) = (b₃ : ℤ) + (b₄ : ℤ) := by
      exact_mod_cast hsum
    rcases hB'sidon hb₁' hb₂' hb₃' hb₄' hsum_int with h | h
    · exact Or.inl ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact Or.inr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · rw [Set.ncard_coe_finset, hBn_cardM]
  · ext d
    constructor
    · intro hd
      rw [Set.mem_inter_iff] at hd
      rcases hd with ⟨hdA, hdB⟩
      rw [Set.mem_sub] at hdA hdB
      rcases hdA with ⟨a₁, ha₁, a₂, ha₂, haDiff⟩
      rcases hdB with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
      rw [Set.mem_singleton_iff]
      by_cases hd0 : d = 0
      · exact hd0
      · exfalso
        have hDiffA_int : (a₁ : ℤ) - (a₂ : ℤ) = (d : ℤ) := by omega
        have hDiffB_int : (b₁ : ℤ) - (b₂ : ℤ) = (d : ℤ) := by omega
        have hdA' : (d : ℤ) ∈ DiffFinset A' A' := by
          rw [mem_diffFinset]
          exact ⟨(a₁ : ℤ), (hA'mem a₁).mp ha₁, (a₂ : ℤ), (hA'mem a₂).mp ha₂,
            hDiffA_int⟩
        have hdB' : (d : ℤ) ∈ DiffFinset B' B' := by
          rw [mem_diffFinset]
          exact ⟨(b₁ : ℤ), (hB'_mem_nat b₁).mp hb₁, (b₂ : ℤ), (hB'_mem_nat b₂).mp hb₂,
            hDiffB_int⟩
        have hd_int_zero : (d : ℤ) = 0 := hAvoid (d : ℤ) hdA' hdB'
        have : d = 0 := by exact_mod_cast hd_int_zero
        exact hd0 this
    · intro hd
      rw [Set.mem_singleton_iff] at hd
      subst d
      rw [Set.mem_inter_iff]
      constructor
      · rw [Set.mem_sub]
        obtain ⟨a, ha⟩ := hAnonempty
        exact ⟨a, ha, a, ha, by simp⟩
      · rw [Set.mem_sub]
        obtain ⟨b, hb⟩ := hB_nonempty
        exact ⟨b, hb, b, hb, by simp⟩

/-! ## §2 FC upstream form (Route B) -/

/-- **`formal-conjectures` upstream form for #42, Route B variant** under
`answer := True`. Same statement as `Erdos42.erdos_42` but axiom-free —
proved through `theorem_1_1_via_cayley`. -/
theorem erdos_42_via_cayley :
    True ↔ ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
      ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  constructor
  · intro _ M hM
    obtain ⟨N₀, hN₀⟩ := theorem_1_1_via_cayley M hM
    refine eventually_atTop.2 ⟨max N₀ 1, ?_⟩
    intro N hN A hMax
    have hN₀le : N₀ ≤ N := (Nat.le_max_left N₀ 1).trans hN
    have hNpos : 1 ≤ N := (Nat.le_max_right N₀ 1).trans hN
    rcases hMax with ⟨hAint, hSidon, hMaximal⟩
    have hAnonempty : A.Nonempty := by
      by_contra hne
      have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have h1Icc : 1 ∈ Set.Icc 1 N := ⟨le_rfl, hNpos⟩
      have h1notA : 1 ∉ A := by simp [hAempty]
      have hnot := hMaximal 1 h1Icc h1notA
      apply hnot
      rw [hAempty]
      intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ _hsum
      simp at ha₁ ha₂ ha₃ ha₄
      subst a₁
      subst a₂
      subst a₃
      subst a₄
      exact Or.inl ⟨rfl, rfl⟩
    exact hN₀ N hN₀le A hAint hSidon hAnonempty
  · intro _
    trivial

/-! ## §3 FC-shape variant (matches FC's `∃ᵉ` and FC's local Sidon predicates) -/

namespace FormalConjecturesShape

/-- **Formal-conjectures shape for #42 (Route B variant).** Matches the
upstream FC statement after replacing `answer(sorry)` by `True` and
interpreting `∃ᵉ` as `ExplicitExists`. Axiom-free — proved through
`erdos_42_via_cayley` plus the (definitional) FC-shape equivalence. -/
theorem erdos_42_via_cayley :
    True ↔ erdos42RHS :=
  Iff.trans Erdos42.erdos_42_via_cayley erdos42RHS_iff_localRHS.symm

end FormalConjecturesShape

end Erdos42
