/-
Erdős Problem 42 — `formal-conjectures` wrapper.

Translates the working `Finset ℤ` statement of Theorem 1.1 (proved by either
Route A or Route B) into:

  * `theorem_1_1` — the Erdős statement over `Set ℕ` matching the README.
  * `IsMaximalSidonSetIn` — the FC predicate.
  * `erdos_42` — the FC iff form `True ↔ ∀ M ≥ 1, ∀ᶠ N in atTop, ...`.

The bridge from `Finset ℤ` to `Set ℕ` is harmless but explicit; natural
subtraction is truncated, so we go through signed integer differences.
-/

import Erdos.P42.Basic
import Erdos.P42.Sidon
import Erdos.P42.FourierPositive.Application

namespace Erdos42

open Filter Set
open scoped Pointwise

/-! ## §1 FC-aligned Sidon predicate over `Set ℕ` -/

/-- `A ⊆ ℕ` is Sidon iff every additive collision is trivial. Matches the FC
skeleton's definition. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-- The FC `IsMaximalSidonSetIn` predicate: `A ⊆ [1, N]` is Sidon and cannot be
extended by any element of `[1, N]` while staying Sidon. -/
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Set.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)

/-! ## §2 Bridge `Finset ℤ` ↔ `Set ℕ` for Sidon sets in `[1, N]` -/

/-- Bridge: a `Set ℕ` Sidon subset of `[1, N]` corresponds to a `Finset ℤ`
Sidon subset of `[1, N] ⊂ ℤ`. -/
theorem isSidonInt_of_isSidon
    {A : Set ℕ} {N : ℕ} (hA : A ⊆ Set.Icc 1 N) (hSidon : IsSidon A) :
    ∃ A' : Finset ℤ,
      (∀ a ∈ A', 1 ≤ a ∧ a ≤ (N : ℤ)) ∧ IsSidonInt A' ∧
      (A.ncard = A'.card) ∧
      (∀ x : ℕ, x ∈ A ↔ ((x : ℤ) ∈ A')) := by
  classical
  let An : Finset ℕ := (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A)
  let A' : Finset ℤ := An.image (fun n : ℕ => (n : ℤ))
  have hAn_mem : ∀ x : ℕ, x ∈ An ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      change x ∈ (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A) at hx
      rw [Finset.mem_filter] at hx
      exact hx.2
    · intro hx
      have hxIcc : x ∈ Finset.Icc 1 N := by
        rw [Finset.mem_Icc]
        exact hA hx
      change x ∈ (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A)
      rw [Finset.mem_filter]
      exact ⟨hxIcc, hx⟩
  have hA'_mem_nat : ∀ x : ℕ, ((x : ℤ) ∈ A') ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      change (x : ℤ) ∈ An.image (fun n : ℕ => (n : ℤ)) at hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyx_nat : y = x := by exact_mod_cast hyx
      rw [← hyx_nat]
      exact (hAn_mem y).mp hy
    · intro hx
      change (x : ℤ) ∈ An.image (fun n : ℕ => (n : ℤ))
      rw [Finset.mem_image]
      exact ⟨x, (hAn_mem x).mpr hx, rfl⟩
  refine ⟨A', ?_, ?_, ?_, ?_⟩
  · intro a ha
    change a ∈ An.image (fun n : ℕ => (n : ℤ)) at ha
    rw [Finset.mem_image] at ha
    rcases ha with ⟨x, hx, rfl⟩
    have hxA : x ∈ A := (hAn_mem x).mp hx
    exact_mod_cast hA hxA
  · intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
    change a₁ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₁
    change a₂ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₂
    change a₃ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₃
    change a₄ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₄
    rw [Finset.mem_image] at ha₁ ha₂ ha₃ ha₄
    rcases ha₁ with ⟨n₁, hn₁, rfl⟩
    rcases ha₂ with ⟨n₂, hn₂, rfl⟩
    rcases ha₃ with ⟨n₃, hn₃, rfl⟩
    rcases ha₄ with ⟨n₄, hn₄, rfl⟩
    have hsum_nat : n₁ + n₂ = n₃ + n₄ := by exact_mod_cast hsum
    rcases hSidon ((hAn_mem n₁).mp hn₁) ((hAn_mem n₂).mp hn₂)
        ((hAn_mem n₃).mp hn₃) ((hAn_mem n₄).mp hn₄) hsum_nat with h | h
    · exact Or.inl ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact Or.inr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · have hAset : A = (An : Set ℕ) := by
      ext x
      exact (hAn_mem x).symm
    have hAcard : A.ncard = An.card := by
      rw [hAset, Set.ncard_coe_finset]
    have hA'card : A'.card = An.card := by
      change (An.image (fun n : ℕ => (n : ℤ))).card = An.card
      apply Finset.card_image_of_injOn
      intro x _hx y _hy hxy
      exact Int.ofNat_injective hxy
    exact hAcard.trans hA'card.symm
  · intro x
    exact (hA'_mem_nat x).symm

/-! ## §3 Theorem 1.1 (the Erdős statement) -/

/-- **Theorem 1.1 (Erdős #42).** For every `M ≥ 1`, all sufficiently large `N`
admit, for every non-empty Sidon `A ⊆ [1, N]`, a Sidon `B ⊆ [1, N]` of size
`M` with no nonzero common difference.

This wrapper uses Route A's `theorem_1_1_from_finite_fourier_avoidance`, then bridges
the `Finset ℤ` construction back to the FC-style `Set ℕ` statement. -/
theorem theorem_1_1 :
    ∀ M : ℕ, 1 ≤ M → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 N → IsSidon A → A.Nonempty →
        ∃ B : Set ℕ, B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
          ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  intro M hM
  classical
  obtain ⟨N₀, hN₀⟩ := FourierPositive.theorem_1_1_from_finite_fourier_avoidance M hM
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

/-! ## §4 FC upstream form -/

/-- **`formal-conjectures` upstream form for #42** under `answer := True`. -/
theorem erdos_42 :
    True ↔ ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
      ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  constructor
  · intro _ M hM
    obtain ⟨N₀, hN₀⟩ := theorem_1_1 M hM
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

end Erdos42
