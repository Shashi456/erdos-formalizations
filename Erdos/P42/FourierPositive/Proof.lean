/-
**STANDALONE FLAT BUNDLE** of Erdős Problem #42 — Fourier-positive route.

This file concatenates the P42 shared machinery plus the Route A/Fourier-positive development.
It is intended as a one-file snapshot: no project-local imports.

Trust boundary (verify with `#print axioms`):
  Mathlib core (propext, Classical.choice, Quot.sound) +
  Erdos42.FourierPositive.finite_fourier_avoidance_exists
-/

import Mathlib
import Mathlib.Analysis.Fourier.ZMod


/-! =============================================================
    Section from: Erdos/P42/Common.lean
    ============================================================= -/

/-
Erdős Problem 42 — shared finite-combinatorial primitives.

`DiffFinset`, `SymmetricFinset`, `AvoidsNonzeroDiff`, plus tiny lemmas that both
the Fourier-positive and compact-Cayley routes use. We work with `Finset` rather
than `Set` because Lean's `Set ℕ` subtraction is truncated.
-/


namespace Erdos42

open Finset

/-- Difference set of two `Finset`s: image of `(a, b) ↦ a - b` over `A ×ˢ B`. -/
def DiffFinset {α : Type*} [DecidableEq α] [Sub α] (A B : Finset α) : Finset α :=
  (A ×ˢ B).image (fun ab => ab.1 - ab.2)

@[simp] lemma mem_diffFinset {α : Type*} [DecidableEq α] [Sub α]
    {A B : Finset α} {x : α} :
    x ∈ DiffFinset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a - b = x := by
  simp [DiffFinset, Finset.mem_image, Finset.mem_product, and_assoc]

/-- A `Finset` is symmetric under negation. -/
def SymmetricFinset {α : Type*} [Neg α] (S : Finset α) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

/-- `A` and `B` share no nonzero difference. -/
def AvoidsNonzeroDiff {α : Type*} [DecidableEq α] [Zero α] [Sub α]
    (A B : Finset α) : Prop :=
  ∀ d ∈ DiffFinset A A, d ∈ DiffFinset B B → d = 0

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/Sidon.lean
    ============================================================= -/

/-
Erdős Problem 42 — Sidon predicates and the elementary cardinality / difference
lemmas every route depends on.

We define `IsSidonInt` over `Finset ℤ` (the natural setting for the analytic
proof) and `IsSidonNat` over `Finset ℕ` / `Set ℕ` (the FC-aligned setting).
Bridge lemmas live in `FC/Local.lean`.
-/


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

/-! =============================================================
    Section from: Erdos/P42/FiniteFourier.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite-Fourier predicates used by the route-axioms.

These predicates use Mathlib's discrete Fourier transform on `ZMod p`. The
transform `ZMod.dft` is unnormalized, so `normalizedDftCoeff` multiplies by
`p⁻¹`, matching the averaged Fourier coefficients in the compact-Cayley and
Fourier-positive notes.

`FourierLowerIndicator` is used by Route A: lower bound `Re ≥ -ε`.
`FourierUpperIndicator` is used by Route B: upper bound `Re ≤ ε` at
nontrivial characters.
-/


namespace Erdos42

open scoped BigOperators ZMod

/-- Complex-valued indicator of a finite set in `ZMod p`. -/
noncomputable def indicatorC {p : ℕ} (T : Finset (ZMod p)) : ZMod p → ℂ :=
  fun x => if x ∈ T then 1 else 0

/-- Normalized DFT coefficient of the indicator of `T`.

Mathlib's `ZMod.dft` is the counting-measure transform
`∑ x, stdAddChar (-(x * r)) • f x`; the compact-Cayley statements use the
averaged coefficient, hence the factor `(p : ℂ)⁻¹`. -/
noncomputable def normalizedDftCoeff {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) : ℂ :=
  ((p : ℂ)⁻¹) * (ZMod.dft (indicatorC T) r)

/-- Normalized Fourier *lower* bound: every character of `ZMod p` evaluated on
`1_F` has real part `≥ -ε`. Used by Route A (Fourier-positive). -/
def FourierLowerIndicator {p : ℕ} [NeZero p] (F : Finset (ZMod p)) (ε : ℝ) : Prop :=
  ∀ r : ZMod p, -(ε : ℝ) ≤ (normalizedDftCoeff F r).re

/-- Normalized Fourier *upper* bound: every nontrivial character of `ZMod p`
evaluated on `1_T` has real part `≤ ε`. Used by Route B (compact Cayley). -/
def FourierUpperIndicator {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (ε : ℝ) : Prop :=
  ∀ r : ZMod p, r ≠ 0 → (normalizedDftCoeff T r).re ≤ ε

lemma normalizedDftCoeff_eq_sum {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) :
    normalizedDftCoeff T r =
      ((p : ℂ)⁻¹) * ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) := by
  classical
  rw [normalizedDftCoeff, ZMod.dft_apply]
  simp [indicatorC, smul_eq_mul]

lemma normalizedDftCoeff_zero_eq_card_div {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) :
    normalizedDftCoeff T 0 = (T.card : ℂ) / (p : ℂ) := by
  rw [normalizedDftCoeff_eq_sum]
  simp [div_eq_inv_mul]

/-- Fourier inversion in the normalization used by the compact-Cayley route. -/
lemma indicatorC_eq_sum_normalizedDftCoeff {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (x : ZMod p) :
    indicatorC T x =
      ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftCoeff T r := by
  classical
  have h :=
    congrFun (LinearEquiv.symm_apply_apply (ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ))
      (indicatorC T)) x
  calc
    indicatorC T x =
        ((p : ℂ)⁻¹) * ∑ r : ZMod p,
          ZMod.stdAddChar (r * x) * ZMod.dft (indicatorC T) r := by
          simpa [ZMod.invDFT_apply, smul_eq_mul] using h.symm
    _ = ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftCoeff T r := by
          simp [normalizedDftCoeff, Finset.mul_sum, mul_comm, mul_left_comm]

lemma sum_stdAddChar_neg_mul_eq_zero_of_ne_zero
    {p : ℕ} [Fact p.Prime] [NeZero p] {r : ZMod p} (hr : r ≠ 0) :
    ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) = 0 := by
  classical
  have hnontrivial :
      AddChar.mulShift (ZMod.stdAddChar (N := p)) (-r) ≠ 1 :=
    (ZMod.isPrimitive_stdAddChar p) (by simpa using neg_ne_zero.mpr hr)
  have hsum :
      ∑ x : ZMod p, AddChar.mulShift (ZMod.stdAddChar (N := p)) (-r) x = 0 :=
    AddChar.sum_eq_zero_of_ne_one hnontrivial
  simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

lemma sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) =
      ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
  classical
  refine Finset.sum_bij (fun x hx => -x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (hT x).mp hx
  · intro x₁ hx₁ x₂ hx₂ h
    exact neg_injective h
  · intro y hy
    refine ⟨-y, ?_, ?_⟩
    · have hy' : - -y ∈ T := by simpa using hy
      exact (hT (-y)).mpr hy'
    · simp
  · intro x hx
    simp

lemma star_sum_stdAddChar_neg_mul_eq_self_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (starRingEnd ℂ) (∑ x ∈ T, ZMod.stdAddChar (-(x * r))) =
      ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) := by
  classical
  calc
    (starRingEnd ℂ) (∑ x ∈ T, ZMod.stdAddChar (-(x * r)))
        = ∑ x ∈ T, (starRingEnd ℂ) (ZMod.stdAddChar (-(x * r))) := by
          rw [map_sum]
    _ = ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hchar := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (x * r)
          simp [hchar] at *
    _ = ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) :=
          (sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric hT r).symm

lemma star_normalizedDftCoeff_eq_self_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (starRingEnd ℂ) (normalizedDftCoeff T r) = normalizedDftCoeff T r := by
  rw [normalizedDftCoeff_eq_sum]
  simp [star_sum_stdAddChar_neg_mul_eq_self_of_symmetric hT r]

lemma normalizedDftCoeff_im_eq_zero_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (normalizedDftCoeff T r).im = 0 := by
  have h := congrArg Complex.im (star_normalizedDftCoeff_eq_self_of_symmetric hT r)
  simp at h
  linarith

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/FiniteReduction.lean
    ============================================================= -/

/-
Erdős Problem 42 — shared compact-Cayley downstream machinery.

This file contains the finite pieces used by the compact-Cayley route and now
also reused by the Fourier-positive Route A:

  1. Greedy Sidon subset lemma: any sufficiently large finite integer set
     contains a Sidon subset of any prescribed size.
  2. Allowed-difference set: for `A ⊆ [N]` Sidon and prime `p > 2N`, define
     `T_A := (ZMod p) \ ((A − A) ∪ {0})`. Then `T_A` is symmetric, `0 ∉ T_A`,
     `|T_A| ≥ p/2`, and the normalized Fourier transform satisfies an upper
     bound `≤ (|A|−1)/p ≤ ε` for `p` large.
  3. Cyclic-interval averaging: some cyclic interval of length `N` in `ZMod p`
     contains `≥ greedySidonThreshold M` clique elements (uses `p < 8N`).
  4. Lift the clique-in-interval to an integer set `X ⊆ [1, N]` avoiding
     `A − A`; greedily extract a Sidon subset `B ⊆ X` of size `M`.

The Route B theorem that actually invokes `compact_cayley_clique` lives in
`CompactCayley/Main.lean`.
-/


namespace Erdos42.CompactCayley

open Finset Erdos42

/-! ## Step 1 — greedy Sidon subset bound (compact PDF Lemma 3.2) -/

/-- The compact PDF's greedy Sidon threshold:
`R_M = 1 + (M − 1) + binomial(M−1, 2) + 2 (M − 1) · binomial(M−1, 2)`.

Any finite integer set of size `≥ R_M` contains a Sidon subset of size `M`,
proved by a greedy argument that excludes (a) already-chosen elements, (b)
elements producing an old difference, and (c) midpoints of two chosen
elements. -/
def greedySidonThreshold (M : ℕ) : ℕ :=
  1 + (M - 1) + Nat.choose (M - 1) 2
    + 2 * (M - 1) * Nat.choose (M - 1) 2

/-- The midpoint map on unordered pairs from a finite integer set. -/
noncomputable def midpointMap (B : Finset ℤ) : Sym2 (B : Type) → ℤ :=
  Sym2.lift ⟨fun a b : (B : Type) => (a.1 + b.1) / 2, by
    intro a b
    change (a.1 + b.1) / 2 = (b.1 + a.1) / 2
    rw [add_comm]⟩

/-- Midpoints of distinct unordered pairs from `B`. These are the new values
that would create a collision `x + x = b₁ + b₂`. -/
noncomputable def midpointSet (B : Finset ℤ) : Finset ℤ :=
  ((⊤ : SimpleGraph (B : Type)).edgeFinset).image (midpointMap B)

/-- Values obtained by translating an old nonzero difference by an old point:
these are the new values that can create a one-new-point collision. -/
def shiftedDiffSet (B : Finset ℤ) : Finset ℤ :=
  (B ×ˢ ((DiffFinset B B).erase 0)).image (fun bd => bd.1 + bd.2)

/-- The finite set avoided in the greedy Sidon construction. -/
noncomputable def greedyBadSet (B : Finset ℤ) : Finset ℤ :=
  B ∪ midpointSet B ∪ shiftedDiffSet B

lemma midpointSet_card_le (B : Finset ℤ) :
    (midpointSet B).card ≤ Nat.choose B.card 2 := by
  classical
  calc
    (midpointSet B).card ≤ ((⊤ : SimpleGraph (B : Type)).edgeFinset).card :=
      Finset.card_image_le
    _ = Nat.choose (Fintype.card (B : Type)) 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = Nat.choose B.card 2 := by rw [Fintype.card_coe]

lemma mem_midpointSet_of_two_mul_eq {B : Finset ℤ} {x a b : ℤ}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) (hmid : 2 * x = a + b) :
    x ∈ midpointSet B := by
  classical
  let aa : (B : Type) := ⟨a, ha⟩
  let bb : (B : Type) := ⟨b, hb⟩
  have hne' : aa ≠ bb := by
    intro h
    exact hne (Subtype.ext_iff.mp h)
  have hedge : Sym2.mk (aa, bb) ∈ (⊤ : SimpleGraph (B : Type)).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simpa [SimpleGraph.top_adj] using hne'
  refine Finset.mem_image.mpr ⟨Sym2.mk (aa, bb), hedge, ?_⟩
  change (aa.1 + bb.1) / 2 = x
  have hdvd : (2 : ℤ) ∣ aa.1 + bb.1 := Dvd.intro x (by simpa [aa, bb] using hmid)
  exact (EuclideanDomain.div_eq_iff_eq_mul_of_dvd
      (aa.1 + bb.1) (2 : ℤ) x (by norm_num) hdvd).mpr
    (by simpa [aa, bb] using hmid.symm)

lemma shiftedDiffSet_card_le (B : Finset ℤ) :
    (shiftedDiffSet B).card ≤ B.card * (Nat.choose B.card 2 * 2) := by
  classical
  calc
    (shiftedDiffSet B).card ≤ (B ×ˢ ((DiffFinset B B).erase 0)).card :=
      Finset.card_image_le
    _ = B.card * ((DiffFinset B B).erase 0).card := by rw [Finset.card_product]
    _ ≤ B.card * (B.card * B.card - B.card) := by
      exact Nat.mul_le_mul_left _ (diffFinset_erase_zero_card_le_offDiag_card B)
    _ = B.card * (Nat.choose B.card 2 * 2) := by
      rw [Nat.choose_two_right, Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one B.card)]
      rw [Nat.mul_sub_one]

lemma greedyBadSet_card_le (B : Finset ℤ) :
    (greedyBadSet B).card ≤
      B.card + Nat.choose B.card 2 + 2 * B.card * Nat.choose B.card 2 := by
  classical
  calc
    (greedyBadSet B).card ≤ B.card + (midpointSet B).card + (shiftedDiffSet B).card := by
      unfold greedyBadSet
      have h₁ :
          (B ∪ midpointSet B ∪ shiftedDiffSet B).card ≤
            (B ∪ midpointSet B).card + (shiftedDiffSet B).card :=
        Finset.card_union_le (B ∪ midpointSet B) (shiftedDiffSet B)
      have h₂ : (B ∪ midpointSet B).card ≤ B.card + (midpointSet B).card :=
        Finset.card_union_le B (midpointSet B)
      omega
    _ ≤ B.card + Nat.choose B.card 2 + B.card * (Nat.choose B.card 2 * 2) := by
      have hmid := midpointSet_card_le B
      have hshift := shiftedDiffSet_card_le B
      omega
    _ = B.card + Nat.choose B.card 2 + 2 * B.card * Nat.choose B.card 2 := by
      ring

lemma greedySidonThreshold_le_succ (M : ℕ) :
    greedySidonThreshold M ≤ greedySidonThreshold (M + 1) := by
  unfold greedySidonThreshold
  have hM : M - 1 ≤ M := Nat.sub_le M 1
  have hchoose : Nat.choose (M - 1) 2 ≤ Nat.choose M 2 :=
    Nat.choose_le_choose 2 hM
  have hprod : (M - 1) * Nat.choose (M - 1) 2 ≤ M * Nat.choose M 2 :=
    Nat.mul_le_mul hM hchoose
  have hlast :
      2 * (M - 1) * Nat.choose (M - 1) 2 ≤ 2 * M * Nat.choose M 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) hchoose
  rw [Nat.add_sub_cancel]
  omega

lemma isSidonInt_insert_of_notMem_greedyBad {B : Finset ℤ} {x : ℤ}
    (hB : IsSidonInt B) (hx : x ∉ greedyBadSet B) :
    IsSidonInt (insert x B) := by
  classical
  rw [greedyBadSet, Finset.mem_union, Finset.mem_union, not_or] at hx
  rcases hx with ⟨hxOldOrMid, hxShift⟩
  rw [not_or] at hxOldOrMid
  rcases hxOldOrMid with ⟨hxB, hxMid⟩
  have no_mid : ∀ {a b : ℤ}, a ∈ B → b ∈ B → a ≠ b → 2 * x ≠ a + b := by
    intro a b ha hb hne h
    exact hxMid (mem_midpointSet_of_two_mul_eq ha hb hne h)
  have no_shift :
      ∀ {c d : ℤ}, c ∈ B → d ∈ (DiffFinset B B).erase 0 → c + d ≠ x := by
    intro c d hc hd h
    apply hxShift
    exact Finset.mem_image.mpr ⟨(c, d), by
      rw [Finset.mem_product]
      exact ⟨hc, hd⟩, h⟩
  intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
  rw [Finset.mem_insert] at ha₁ ha₂ ha₃ ha₄
  rcases ha₁ with h₁ | ha₁
  · subst a₁
    rcases ha₂ with h₂ | ha₂
    · subst a₂
      rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exact Or.inl ⟨rfl, rfl⟩
        · exfalso
          have hx4 : x = a₄ := by linarith
          exact hxB (by simpa [hx4] using ha₄)
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx3 : x = a₃ := by linarith
          exact hxB (by simpa [hx3] using ha₃)
        · exfalso
          by_cases h34 : a₃ = a₄
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · exact no_mid ha₃ ha₄ h34 (by linarith)
    · rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx2 : x = a₂ := by linarith
          exact hxB (by simpa [hx2] using ha₂)
        · have h24 : a₂ = a₄ := by linarith
          exact Or.inl ⟨rfl, h24⟩
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          have h23 : a₂ = a₃ := by linarith
          exact Or.inr ⟨rfl, h23⟩
        · exfalso
          by_cases h42 : a₄ = a₂
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · have hd : a₄ - a₂ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h42, ⟨a₄, ha₄, a₂, ha₂, rfl⟩⟩
            exact no_shift ha₃ hd (by linarith)
  · rcases ha₂ with h₂ | ha₂
    · subst a₂
      rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx1 : x = a₁ := by linarith
          exact hxB (by simpa [hx1] using ha₁)
        · have h14 : a₁ = a₄ := by linarith
          exact Or.inr ⟨h14, rfl⟩
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          have h13 : a₁ = a₃ := by linarith
          exact Or.inl ⟨h13, rfl⟩
        · exfalso
          by_cases h41 : a₄ = a₁
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · have hd : a₄ - a₁ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h41, ⟨a₄, ha₄, a₁, ha₁, rfl⟩⟩
            exact no_shift ha₃ hd (by linarith)
    · rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          by_cases h12 : a₁ = a₂
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · exact no_mid ha₁ ha₂ h12 (by linarith)
        · exfalso
          by_cases h24 : a₂ = a₄
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · have hd : a₂ - a₄ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h24, ⟨a₂, ha₂, a₄, ha₄, rfl⟩⟩
            exact no_shift ha₁ hd (by linarith)
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          by_cases h23 : a₂ = a₃
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · have hd : a₂ - a₃ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h23, ⟨a₂, ha₂, a₃, ha₃, rfl⟩⟩
            exact no_shift ha₁ hd (by linarith)
        · exact hB ha₁ ha₂ ha₃ ha₄ hsum

/-- Greedy Sidon subset bound: every large integer `Finset` contains a Sidon
subset of any prescribed size. -/
theorem exists_sidon_subset_of_card_ge
    (M : ℕ) (X : Finset ℤ)
    (hX : greedySidonThreshold M ≤ X.card) :
    ∃ B : Finset ℤ, B ⊆ X ∧ B.card = M ∧ IsSidonInt B := by
  classical
  induction M with
  | zero =>
      exact ⟨∅, by simp, by simp, isSidonInt_empty⟩
  | succ M ih =>
      have hXM : greedySidonThreshold M ≤ X.card :=
        (greedySidonThreshold_le_succ M).trans hX
      obtain ⟨B, hBX, hBcard, hBsidon⟩ := ih hXM
      have hbad_lt : (greedyBadSet B).card < X.card := by
        have hbad_le := greedyBadSet_card_le B
        have hbad_leM :
            (greedyBadSet B).card ≤
              M + Nat.choose M 2 + 2 * M * Nat.choose M 2 := by
          simpa [hBcard] using hbad_le
        have hthresh :
            greedySidonThreshold (M + 1) =
              1 + M + Nat.choose M 2 + 2 * M * Nat.choose M 2 := by
          unfold greedySidonThreshold
          rw [Nat.add_sub_cancel]
        have hbad_lt_threshold : (greedyBadSet B).card < greedySidonThreshold (M + 1) := by
          rw [hthresh]
          omega
        exact hbad_lt_threshold.trans_le hX
      obtain ⟨x, hxX, hxBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
      have hxB : x ∉ B := by
        intro hxB
        apply hxBad
        unfold greedyBadSet
        simp [hxB]
      refine ⟨insert x B, ?_, ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hxX
        · exact hBX hy
      · rw [Finset.card_insert_of_notMem hxB, hBcard]
      · exact isSidonInt_insert_of_notMem_greedyBad hBsidon hxBad

/-! ## Step 2 — allowed-difference set & Fourier upper bound -/

/-- The allowed-difference set: `T_A := (ZMod p) \ ((A − A) ∪ {0})` viewed
through the natural cast `ℤ → ZMod p`. -/
noncomputable def allowedDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Finset (ZMod p) :=
  (Finset.univ : Finset (ZMod p)).filter
    (fun t => t ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t)

/-- The allowed-difference set is symmetric. -/
lemma allowedDiffSetMod_symmetric (p : ℕ) [NeZero p] (A : Finset ℤ) :
    SymmetricFinset (allowedDiffSetMod p A) := by
  intro t
  simp only [allowedDiffSetMod, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht0, ht⟩
    refine ⟨?_, ?_⟩
    · intro hzero
      exact ht0 (by simpa using congrArg Neg.neg hzero)
    · intro a ha b hb hdiff
      have hswap : ((b - a : ℤ) : ZMod p) = t := by
        calc
          ((b - a : ℤ) : ZMod p) = -(((a - b : ℤ) : ZMod p)) := by norm_num
          _ = t := by simp [hdiff]
      exact ht b hb a ha hswap
  · rintro ⟨ht0, ht⟩
    refine ⟨?_, ?_⟩
    · intro hzero
      exact ht0 (by simpa using congrArg Neg.neg hzero)
    · intro a ha b hb hdiff
      have hswap : ((b - a : ℤ) : ZMod p) = -t := by
        calc
          ((b - a : ℤ) : ZMod p) = -(((a - b : ℤ) : ZMod p)) := by norm_num
          _ = -t := by simp [hdiff]
      exact ht b hb a ha hswap

/-- `0` is not in the allowed-difference set (by construction). -/
lemma zero_notMem_allowedDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    (0 : ZMod p) ∉ allowedDiffSetMod p A := by
  simp [allowedDiffSetMod]

/-- Density bound: for `A ⊆ [N]` Sidon and `p > 4N`, the allowed-difference
set covers more than half of `ZMod p`. -/
lemma allowedDiffSetMod_density
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    (1 / 2 : ℝ) * p ≤ ((allowedDiffSetMod p A).card : ℝ) := by
  classical
  by_cases hN0 : N = 0
  · subst N
    have hAempty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have ha' := hAint a ha
      omega
    have hcard : (allowedDiffSetMod p A).card = p - 1 := by
      have hallowed_eq :
          allowedDiffSetMod p A = (Finset.univ : Finset (ZMod p)).erase 0 := by
        ext t
        simp [allowedDiffSetMod, hAempty]
      rw [hallowed_eq, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
        Finset.card_univ, ZMod.card]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [hcard]
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp2
    nlinarith
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    let P : ZMod p → Prop :=
      fun t => t ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t
    let bad : Finset (ZMod p) := (Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t)
    let forbidden : Finset (ZMod p) :=
      insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
    have hbad_subset : bad ⊆ forbidden := by
      intro t ht
      change t ∈ (Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t) at ht
      rw [Finset.mem_filter] at ht
      rcases ht with ⟨_htuniv, htbad⟩
      by_cases ht0 : t = 0
      · change t ∈ insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
        simp [ht0]
      · have hnot :
            ¬ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t := by
          intro hall
          exact htbad ⟨ht0, hall⟩
        push_neg at hnot
        rcases hnot with ⟨a, ha, b, hb, hcast⟩
        have hdiff_ne : a - b ≠ 0 := by
          intro hzero
          apply ht0
          simpa [hzero] using hcast.symm
        have hdiff_mem : a - b ∈ (DiffFinset A A).erase 0 := by
          rw [Finset.mem_erase, mem_diffFinset]
          exact ⟨hdiff_ne, ⟨a, ha, b, hb, rfl⟩⟩
        change t ∈ insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_image.mpr ⟨a - b, hdiff_mem, hcast⟩))
    have hbad_card : bad.card ≤ 2 * N - 1 := by
      calc
        bad.card ≤ forbidden.card := Finset.card_le_card hbad_subset
        _ ≤ (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p))).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ ((DiffFinset A A).erase 0).card + 1 :=
          Nat.add_le_add_right Finset.card_image_le 1
        _ ≤ (2 * N - 2) + 1 :=
          Nat.add_le_add_right (sidon_nonzero_diff_card_le A N hAint hSidon) 1
        _ ≤ 2 * N - 1 := by omega
    have hsum : (allowedDiffSetMod p A).card + bad.card = p := by
      change
        ((Finset.univ : Finset (ZMod p)).filter P).card +
            ((Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t)).card = p
      rw [Finset.card_filter_add_card_filter_not]
      simp [ZMod.card]
    have hbad_half : 2 * bad.card ≤ p := by omega
    have hallowed_nat : p ≤ 2 * (allowedDiffSetMod p A).card := by omega
    have hallowed_real :
        (p : ℝ) ≤ 2 * ((allowedDiffSetMod p A).card : ℝ) := by
      exact_mod_cast hallowed_nat
    nlinarith

lemma int_difference_eq_of_zmod_eq_of_interval
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    {a b c d : ℤ}
    (ha : 1 ≤ a ∧ a ≤ (N : ℤ))
    (hb : 1 ≤ b ∧ b ≤ (N : ℤ))
    (hc : 1 ≤ c ∧ c ≤ (N : ℤ))
    (hd : 1 ≤ d ∧ d ≤ (N : ℤ))
    (hcong : ((a - b : ℤ) : ZMod p) = ((c - d : ℤ) : ZMod p)) :
    a - b = c - d := by
  have hdiv : (p : ℤ) ∣ (c - d) - (a - b) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (a - b) (c - d) p).mp hcong
  have hp_bound : (2 * (N : ℤ) : ℤ) < (p : ℤ) := by exact_mod_cast (by omega)
  have habs : |(c - d) - (a - b)| < (p : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : (c - d) - (a - b) = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs
  linarith

lemma offDiag_diff_cast_injOn
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    Set.InjOn (fun ab : ℤ × ℤ => ((ab.1 - ab.2 : ℤ) : ZMod p))
      (A.offDiag : Set (ℤ × ℤ)) := by
  intro ab hab cd hcd hcast
  have habFin : ab ∈ A.offDiag := by simpa using hab
  have hcdFin : cd ∈ A.offDiag := by simpa using hcd
  rw [Finset.mem_offDiag] at habFin hcdFin
  rcases habFin with ⟨hab1, hab2, hab_ne⟩
  rcases hcdFin with ⟨hcd1, hcd2, _hcd_ne⟩
  have hdiff : ab.1 - ab.2 = cd.1 - cd.2 :=
    int_difference_eq_of_zmod_eq_of_interval (p := p) (N := N) hbig
      (hAint ab.1 hab1) (hAint ab.2 hab2) (hAint cd.1 hcd1) (hAint cd.2 hcd2) hcast
  have hsum : ab.1 + cd.2 = cd.1 + ab.2 := by linarith
  rcases hSidon hab1 hcd2 hcd1 hab2 hsum with h | h
  · exact Prod.ext h.1 h.2.symm
  · exact False.elim (hab_ne h.1)

/-- Nonzero ordered difference residues from `A`. -/
noncomputable def offDiagDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Finset (ZMod p) :=
  A.offDiag.image (fun ab : ℤ × ℤ => ((ab.1 - ab.2 : ℤ) : ZMod p))

lemma zero_notMem_offDiagDiffSetMod
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) :
    (0 : ZMod p) ∉ offDiagDiffSetMod p A := by
  classical
  rw [offDiagDiffSetMod, Finset.mem_image]
  rintro ⟨ab, hab, hcast⟩
  rw [Finset.mem_offDiag] at hab
  rcases hab with ⟨ha, hb, hne⟩
  have hcong :
      ((ab.1 - ab.2 : ℤ) : ZMod p) = ((ab.1 - ab.1 : ℤ) : ZMod p) := by
    simpa using hcast
  have hdiff :
      ab.1 - ab.2 = ab.1 - ab.1 :=
    int_difference_eq_of_zmod_eq_of_interval (p := p) (N := N) hbig
      (hAint ab.1 ha) (hAint ab.2 hb) (hAint ab.1 ha) (hAint ab.1 ha) hcong
  exact hne (by linarith)

lemma allowedDiffSetMod_union_forbidden (p : ℕ) [NeZero p] (A : Finset ℤ) :
    allowedDiffSetMod p A ∪ insert 0 (offDiagDiffSetMod p A) =
      (Finset.univ : Finset (ZMod p)) := by
  classical
  ext t
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_univ, iff_true]
  by_cases ht_allowed : t ∈ allowedDiffSetMod p A
  · exact Or.inl ht_allowed
  · right
    rw [allowedDiffSetMod, Finset.mem_filter] at ht_allowed
    simp only [Finset.mem_univ, true_and, not_and, not_forall] at ht_allowed
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    · right
      have hnot_all := ht_allowed ht0
      push_neg at hnot_all
      rcases hnot_all with ⟨a, ha, b, hb, hdiff⟩
      rw [offDiagDiffSetMod, Finset.mem_image]
      by_cases hab : a = b
      · subst b
        exfalso
        exact ht0 (by simpa using hdiff.symm)
      · refine ⟨(a, b), ?_, hdiff⟩
        rw [Finset.mem_offDiag]
        exact ⟨ha, hb, hab⟩

lemma disjoint_allowedDiffSetMod_forbidden (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Disjoint (allowedDiffSetMod p A) (insert 0 (offDiagDiffSetMod p A)) := by
  classical
  rw [Finset.disjoint_left]
  intro t ht hforbidden
  rw [allowedDiffSetMod, Finset.mem_filter] at ht
  rcases ht with ⟨_htuniv, ht0, hno⟩
  rw [Finset.mem_insert] at hforbidden
  rcases hforbidden with rfl | hoff
  · exact ht0 rfl
  · rw [offDiagDiffSetMod, Finset.mem_image] at hoff
    rcases hoff with ⟨ab, hab, hdiff⟩
    rw [Finset.mem_offDiag] at hab
    rcases hab with ⟨ha, hb, _hne⟩
    exact hno ab.1 ha ab.2 hb hdiff

lemma sum_allowedDiffSetMod_eq_neg_forbidden
    {p : ℕ} [Fact p.Prime] [NeZero p]
    (A : Finset ℤ) {r : ZMod p} (hr : r ≠ 0) :
    ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
      - ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) := by
  classical
  have htotal := sum_stdAddChar_neg_mul_eq_zero_of_ne_zero (p := p) hr
  have hsum_union :
      ∑ x ∈ allowedDiffSetMod p A ∪ insert 0 (offDiagDiffSetMod p A),
          ZMod.stdAddChar (-(x * r)) =
        ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) +
          ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) := by
    rw [Finset.sum_union (disjoint_allowedDiffSetMod_forbidden p A)]
  rw [allowedDiffSetMod_union_forbidden p A] at hsum_union
  have hadd :
      ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) +
          ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) = 0 := by
    rw [← hsum_union]
    exact htotal
  exact eq_neg_of_add_eq_zero_left hadd

lemma sum_forbidden_eq_one_add_offDiag
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (r : ZMod p) :
    ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) =
      1 + ∑ x ∈ offDiagDiffSetMod p A, ZMod.stdAddChar (-(x * r)) := by
  classical
  rw [Finset.sum_insert (zero_notMem_offDiagDiffSetMod (p := p) (N := N) hbig A hAint)]
  simp

lemma sum_offDiagDiffSetMod_eq_sum_offDiag
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (f : ZMod p → ℂ) :
    ∑ x ∈ offDiagDiffSetMod p A, f x =
      ∑ ab ∈ A.offDiag, f (((ab.1 - ab.2 : ℤ) : ZMod p)) := by
  classical
  rw [offDiagDiffSetMod]
  rw [Finset.sum_image]
  intro ab hab cd hcd h
  exact offDiag_diff_cast_injOn (p := p) (N := N) hbig A hAint hSidon
    (by simpa using hab) (by simpa using hcd) h

lemma sum_product_eq_sum_diag_add_sum_offDiag
    (A : Finset ℤ) (f : ℤ × ℤ → ℂ) :
    ∑ ab ∈ A ×ˢ A, f ab =
      (∑ a ∈ A, f (a, a)) + ∑ ab ∈ A.offDiag, f ab := by
  classical
  rw [← Finset.diag_union_offDiag (s := A)]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag A)]
  rw [Finset.sum_diag]

lemma sum_product_stdAddChar_neg_diff
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    (∑ ab ∈ A ×ˢ A,
        ZMod.stdAddChar (-(((ab.1 - ab.2 : ℤ) : ZMod p) * r))) =
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))) := by
  classical
  rw [Finset.sum_product]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  norm_num
  ring_nf

lemma sum_diag_stdAddChar_diff
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    ∑ a ∈ A, ZMod.stdAddChar (-((((a - a : ℤ) : ZMod p) * r))) = (A.card : ℂ) := by
  simp

lemma sum_offDiagDiffSetMod_stdAddChar_eq
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (r : ZMod p) :
    ∑ x ∈ offDiagDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))) - (A.card : ℂ) := by
  classical
  let F : ℤ × ℤ → ℂ :=
    fun ab => ZMod.stdAddChar (-((((ab.1 - ab.2 : ℤ) : ZMod p) * r)))
  have hoff :=
    sum_offDiagDiffSetMod_eq_sum_offDiag (p := p) (N := N) hbig A hAint hSidon
      (fun x : ZMod p => ZMod.stdAddChar (-(x * r)))
  have hsplit := sum_product_eq_sum_diag_add_sum_offDiag A F
  have hprod := sum_product_stdAddChar_neg_diff A r
  have hdiag : ∑ a ∈ A, F (a, a) = (A.card : ℂ) := by
    simp [F]
  rw [hoff]
  have hsplit' :
      ∑ ab ∈ A.offDiag, F ab =
        (∑ ab ∈ A ×ˢ A, F ab) - ∑ a ∈ A, F (a, a) := by
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact hsplit.symm
  rw [hprod] at hsplit'
  simpa [F, hdiag] using hsplit'

lemma stdAddChar_neg_eq_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    ZMod.stdAddChar (-x) = (starRingEnd ℂ) (ZMod.stdAddChar x) := by
  simpa using AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) x

lemma sum_stdAddChar_neg_eq_conj_sum
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    ∑ b ∈ A, ZMod.stdAddChar (-(((b : ZMod p) * r))) =
      (starRingEnd ℂ) (∑ a ∈ A, ZMod.stdAddChar (((a : ZMod p) * r))) := by
  classical
  calc
    ∑ b ∈ A, ZMod.stdAddChar (-(((b : ZMod p) * r))) =
        ∑ a ∈ A, (starRingEnd ℂ) (ZMod.stdAddChar (((a : ZMod p) * r))) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact stdAddChar_neg_eq_conj (p := p) (((a : ZMod p) * r))
    _ = (starRingEnd ℂ) (∑ a ∈ A, ZMod.stdAddChar (((a : ZMod p) * r))) := by
      simp

lemma stdAddChar_neg_product_re_nonneg
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    0 ≤
      ((∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r)))).re := by
  classical
  let S : ℂ := ∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))
  have hneg :
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) =
        (starRingEnd ℂ) S := by
    simpa [S] using sum_stdAddChar_neg_eq_conj_sum A r
  rw [hneg]
  rw [← Complex.normSq_eq_conj_mul_self]
  simpa using Complex.normSq_nonneg S

lemma sum_allowedDiffSetMod_stdAddChar_re_le
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    {r : ZMod p} (hr : r ≠ 0) :
    (∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r))).re ≤
      ((A.card - 1 : ℕ) : ℝ) := by
  classical
  let P : ℂ :=
    (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
      (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r)))
  have hallowed :=
    sum_allowedDiffSetMod_eq_neg_forbidden (p := p) A hr
  have hforbidden :=
    sum_forbidden_eq_one_add_offDiag (p := p) (N := N) hbig A hAint r
  have hoff :=
    sum_offDiagDiffSetMod_stdAddChar_eq (p := p) (N := N) hbig A hAint hSidon r
  have hsum :
      ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
        (A.card : ℂ) - 1 - P := by
    rw [hallowed, hforbidden, hoff]
    simp [P]
    ring
  have hP_nonneg : 0 ≤ P.re := by
    simpa [P] using stdAddChar_neg_product_re_nonneg A r
  rw [hsum]
  by_cases hA0 : A.card = 0
  · simp [hA0]
    linarith
  · have hApos : 1 ≤ A.card := by omega
    have hcast : ((A.card - 1 : ℕ) : ℝ) = (A.card : ℝ) - 1 := by
      rw [Nat.cast_sub hApos]
      norm_num
    rw [hcast]
    simp
    exact hP_nonneg

/-- Sidon Fourier estimate (normalized): `Re 1̂_{T_A}(r) ≤ (|A|−1)/p` for every
nontrivial character `r`, for `T_A = (ZMod p) \ ((A−A) ∪ {0})` and `A` Sidon
(compact PDF §3 calculation).

This is a finite Fourier calculation, separate from the compact-Cayley clique
theorem. It expands `ZMod.dft`, uses the vanishing of nontrivial character sums,
and rewrites the nonzero-difference contribution as
`|∑ a ∈ A, χ a|^2 - |A|`. -/
theorem allowedDiffs_fourier_upper
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (ε : ℝ)
    (hε : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε) :
    FourierUpperIndicator (allowedDiffSetMod p A) ε := by
  classical
  intro r hr
  have hp_pos_nat : 0 < p := (Fact.out : p.Prime).pos
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos_nat
  have hsum_le :=
    sum_allowedDiffSetMod_stdAddChar_re_le (p := p) (N := N) hbig A hAint hSidon hr
  rw [normalizedDftCoeff_eq_sum]
  have hinv : ((p : ℂ)⁻¹) = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [hinv, Complex.re_ofReal_mul]
  have hmul_le :
      (p : ℝ)⁻¹ *
          (∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r))).re ≤
        (p : ℝ)⁻¹ * ((A.card - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hp_pos.le)
  refine hmul_le.trans ?_
  rw [div_eq_inv_mul] at hε
  simpa [mul_comm] using hε

/-- Eventual smallness of the normalized Sidon-size error term.

For `A ⊆ [1,N]` Sidon, `choose |A| 2 ≤ N - 1`, so `|A| = O(sqrt N)`.
Since the chosen prime satisfies `p > 4N`, `( |A| - 1 ) / p → 0`. This
elementary asymptotic bound is kept separate from the finite Fourier identity
above. -/
lemma sidon_card_minus_one_div_prime_eventually_small
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Nε : ℕ, ∀ N p : ℕ,
      Nε ≤ N →
      4 * N < p →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) →
        IsSidonInt A →
        ((A.card - 1 : ℕ) : ℝ) / p ≤ ε := by
  classical
  have hden_pos : 0 < 8 * ε ^ 2 := by positivity
  obtain ⟨Nε, hNε_gt⟩ := exists_nat_gt ((1 : ℝ) / (8 * ε ^ 2))
  refine ⟨Nε, ?_⟩
  intro N p hN hp A hAint hSidon
  let t : ℝ := ((A.card - 1 : ℕ) : ℝ)
  let k : ℝ := (A.card : ℝ)
  have hN_large_base : (1 : ℝ) / (8 * ε ^ 2) < (N : ℝ) :=
    hNε_gt.trans_le (by exact_mod_cast hN)
  have hN_large : 1 < 8 * ε ^ 2 * (N : ℝ) := by
    have := (div_lt_iff₀ hden_pos).mp hN_large_base
    nlinarith
  have hN_pos : 0 < (N : ℝ) := (one_div_pos.mpr hden_pos).trans hN_large_base
  have hp_pos : 0 < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hp_gt4N : 4 * (N : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hchoose := sidon_choose_two_le_interval A N hAint hSidon
  by_cases hAcard0 : A.card = 0
  · simp [hAcard0, le_of_lt hε]
  have hAcard_pos : 1 ≤ A.card := by omega
  have ht_eq : t = (A.card : ℝ) - 1 := by
    dsimp [t]
    rw [Nat.cast_sub hAcard_pos]
    norm_num
  have hchoose_real :
      (Nat.choose A.card 2 : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast hchoose
  have hchoose_le_N :
      k * t / 2 ≤ (N : ℝ) := by
    have hformula :
        (Nat.choose A.card 2 : ℝ) = k * t / 2 := by
      simpa [k, ht_eq] using (Nat.cast_choose_two (K := ℝ) A.card)
    have hsub_le : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.sub_le N 1)
    nlinarith
  have ht_nonneg : 0 ≤ t := by positivity
  have hk_nonneg : 0 ≤ k := by positivity
  have ht_le_k : t ≤ k := by
    dsimp [t, k]
    exact_mod_cast (Nat.sub_le A.card 1)
  have ht_sq_le : t ^ 2 ≤ 2 * (N : ℝ) := by
    have hsq_le : t * t ≤ k * t := by nlinarith
    nlinarith
  have htarget_sq : t ^ 2 ≤ (ε * (p : ℝ)) ^ 2 := by
    have hεsq_pos : 0 < ε ^ 2 := by positivity
    have hp_sq_gt : (4 * (N : ℝ)) ^ 2 < (p : ℝ) ^ 2 := by
      nlinarith [hp_gt4N, hN_pos, hp_pos, sq_nonneg ((p : ℝ) - 4 * (N : ℝ))]
    nlinarith
  have ht_le_epsp : t ≤ ε * (p : ℝ) := by
    exact le_of_sq_le_sq htarget_sq (by positivity)
  rw [div_le_iff₀ hp_pos]
  simpa [t] using ht_le_epsp

/-! ## Step 3 — cyclic interval averaging -/

/-- Cyclic interval `{s, s+1, …, s+N-1}` in `ZMod p`. -/
noncomputable def cyclicInterval (p N : ℕ) [NeZero p] (s : ZMod p) :
    Finset (ZMod p) :=
  (Finset.range N).image (fun i : ℕ => s + (i : ZMod p))

lemma nat_eq_of_zmod_eq_of_lt {p i j : ℕ} [NeZero p]
    (hi : i < p) (hj : j < p) (hij : (i : ZMod p) = (j : ZMod p)) :
    i = j := by
  have hmod : i % p = j % p := (ZMod.natCast_eq_natCast_iff' i j p).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hmod

/-- Integer lift of clique points lying in the cyclic interval
`{s, …, s+N-1}`. The residue `s+i` is lifted to the integer `i+1`, so the
lift lies in `[1, N]`. -/
noncomputable def intervalLiftSet (p N : ℕ) [NeZero p] (s : ZMod p)
    (C : Finset (ZMod p)) : Finset ℤ :=
  ((Finset.range N).filter (fun i : ℕ => s + (i : ZMod p) ∈ C)).image
    (fun i : ℕ => (i + 1 : ℤ))

lemma intervalLiftSet_card_eq
    {p N : ℕ} [NeZero p] (hpN : N < p) (s : ZMod p) (C : Finset (ZMod p)) :
    (intervalLiftSet p N s C).card =
      (C.filter (fun x => x ∈ cyclicInterval p N s)).card := by
  classical
  let I : Finset ℕ := (Finset.range N).filter (fun i : ℕ => s + (i : ZMod p) ∈ C)
  let f : ℕ → ZMod p := fun i => s + (i : ZMod p)
  let target : Finset (ZMod p) := C.filter (fun x => x ∈ cyclicInterval p N s)
  have hinjI : Set.InjOn f (I : Set ℕ) := by
    intro i hi j hj hij
    have hiI : i ∈ I := by simpa using hi
    have hjI : j ∈ I := by simpa using hj
    rw [Finset.mem_filter] at hiI hjI
    apply nat_eq_of_zmod_eq_of_lt
      (Nat.lt_trans (by simpa using hiI.1) hpN)
      (Nat.lt_trans (by simpa using hjI.1) hpN)
    apply add_left_cancel (a := s)
    simpa [f] using hij
  have hI_image_card : (I.image f).card = I.card :=
    Finset.card_image_of_injOn hinjI
  have hI_image : I.image f = target := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨i, hiI, rfl⟩
      rw [Finset.mem_filter] at hiI
      rw [Finset.mem_filter]
      refine ⟨hiI.2, ?_⟩
      rw [cyclicInterval]
      exact Finset.mem_image.mpr ⟨i, hiI.1, rfl⟩
    · intro hx
      change x ∈ target at hx
      rw [Finset.mem_filter] at hx
      rcases hx with ⟨hxC, hxInt⟩
      rw [cyclicInterval, Finset.mem_image] at hxInt
      rcases hxInt with ⟨i, hiN, rfl⟩
      rw [Finset.mem_image]
      exact ⟨i, by
        rw [Finset.mem_filter]
        exact ⟨hiN, hxC⟩, rfl⟩
  have hlift_card : (intervalLiftSet p N s C).card = I.card := by
    unfold intervalLiftSet
    change (I.image (fun i : ℕ => (i + 1 : ℤ))).card = I.card
    apply Finset.card_image_of_injOn
    intro i _hi j _hj hij
    have hnat : i + 1 = j + 1 := Int.ofNat_inj.mp hij
    omega
  calc
    (intervalLiftSet p N s C).card = I.card := hlift_card
    _ = (I.image f).card := hI_image_card.symm
    _ = target.card := by rw [hI_image]

lemma mem_intervalLiftSet.mp
    {p N : ℕ} [NeZero p] {s : ZMod p} {C : Finset (ZMod p)} {b : ℤ}
    (hb : b ∈ intervalLiftSet p N s C) :
    ∃ i : ℕ, i < N ∧ s + (i : ZMod p) ∈ C ∧ b = (i + 1 : ℤ) := by
  classical
  rw [intervalLiftSet, Finset.mem_image] at hb
  rcases hb with ⟨i, hi, rfl⟩
  rw [Finset.mem_filter] at hi
  exact ⟨i, by simpa using hi.1, hi.2, rfl⟩

/-- Pigeonhole: a clique of size `8R` in `ZMod p` (with `p < 8N`) intersects
some cyclic interval of length `N` in at least `R` points. -/
theorem exists_large_intersection_cyclicInterval
    {p N R : ℕ} [NeZero p] (hpN : N < p) (C : Finset (ZMod p))
    (hsize : C.card = 8 * R)
    (hpupper : p < 8 * N) :
    ∃ s : ZMod p,
      R ≤ (C.filter (fun x => x ∈ cyclicInterval p N s)).card := by
  classical
  by_cases hR0 : R = 0
  · subst R
    exact ⟨0, by simp⟩
  · have hRpos : 0 < R := Nat.pos_of_ne_zero hR0
    let D : Finset (ZMod p × ℕ) := C.product (Finset.range N)
    let start : ZMod p × ℕ → ZMod p := fun ci => ci.1 - (ci.2 : ZMod p)
    have hlarge :
        (Finset.univ : Finset (ZMod p)).card * R < D.card := by
      rw [Finset.card_univ, ZMod.card]
      change p * R < (C ×ˢ Finset.range N).card
      rw [Finset.card_product, Finset.card_range, hsize]
      calc
        p * R < (8 * N) * R := Nat.mul_lt_mul_of_pos_right hpupper hRpos
        _ = (8 * R) * N := by ring
    obtain ⟨s, _hsuniv, hs⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s := D) (t := (Finset.univ : Finset (ZMod p))) (f := start) (n := R)
        (by intro x _hx; exact Finset.mem_univ _) hlarge
    refine ⟨s, ?_⟩
    let fiber : Finset (ZMod p × ℕ) := D.filter (fun ci => start ci = s)
    let target : Finset (ZMod p) := C.filter (fun x => x ∈ cyclicInterval p N s)
    have hmaps :
        Set.MapsTo (fun ci : ZMod p × ℕ => ci.1)
          (fiber : Set (ZMod p × ℕ)) (target : Set (ZMod p)) := by
      intro ci hci
      have hci' : ci ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hci
      rw [Finset.mem_filter] at hci'
      rcases hci' with ⟨hciD, hstart⟩
      have hmem : ci.1 ∈ C ∧ ci.2 ∈ Finset.range N := by
        simpa [D] using hciD
      rcases hmem with ⟨hc, hi⟩
      have hpoint : ci.1 ∈ cyclicInterval p N s := by
        rw [cyclicInterval]
        refine Finset.mem_image.mpr ⟨ci.2, hi, ?_⟩
        have hadd : ci.1 = s + (ci.2 : ZMod p) := by
          simpa [start] using (sub_eq_iff_eq_add.mp hstart)
        exact hadd.symm
      change ci.1 ∈ C.filter (fun x => x ∈ cyclicInterval p N s)
      rw [Finset.mem_filter]
      exact ⟨hc, hpoint⟩
    have hinj :
        (fiber : Set (ZMod p × ℕ)).InjOn (fun ci : ZMod p × ℕ => ci.1) := by
      intro ci hci cj hcj hproj
      have hci' : ci ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hci
      have hcj' : cj ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hcj
      rw [Finset.mem_filter] at hci' hcj'
      rcases hci' with ⟨hciD, hstart_i⟩
      rcases hcj' with ⟨hcjD, hstart_j⟩
      have hi : ci.2 ∈ Finset.range N := by
        have hmem : ci.1 ∈ C ∧ ci.2 ∈ Finset.range N := by
          simpa [D] using hciD
        exact hmem.2
      have hj : cj.2 ∈ Finset.range N := by
        have hmem : cj.1 ∈ C ∧ cj.2 ∈ Finset.range N := by
          simpa [D] using hcjD
        exact hmem.2
      have hci_add : ci.1 = s + (ci.2 : ZMod p) := by
        simpa [start] using (sub_eq_iff_eq_add.mp hstart_i)
      have hcj_add : cj.1 = s + (cj.2 : ZMod p) := by
        simpa [start] using (sub_eq_iff_eq_add.mp hstart_j)
      have hcast : (ci.2 : ZMod p) = (cj.2 : ZMod p) := by
        apply add_left_cancel (a := s)
        calc
          s + (ci.2 : ZMod p) = ci.1 := hci_add.symm
          _ = cj.1 := hproj
          _ = s + (cj.2 : ZMod p) := hcj_add
      have hmod : ci.2 % p = cj.2 % p := by
        exact (ZMod.natCast_eq_natCast_iff' ci.2 cj.2 p).mp hcast
      have hilt : ci.2 < p := by
        exact Nat.lt_trans (by simpa using hi) hpN
      have hjlt : cj.2 < p := by
        exact Nat.lt_trans (by simpa using hj) hpN
      have hidx : ci.2 = cj.2 := by
        rw [Nat.mod_eq_of_lt hilt, Nat.mod_eq_of_lt hjlt] at hmod
        exact hmod
      exact Prod.ext hproj hidx
    have hfiber_le : fiber.card ≤ target.card :=
      Finset.card_le_card_of_injOn (fun ci : ZMod p × ℕ => ci.1) hmaps hinj
    have hs' : R < fiber.card := by
      simpa [fiber] using hs
    exact (Nat.le_of_lt hs').trans hfiber_le

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/FourierPositive/FiniteAvoidance.lean
    ============================================================= -/

/-
Erdős Problem 42 — Route A trust boundary: finite Fourier avoidance theorem.

Combined-PDF / Ulam-note finite theorem: for fixed `m, α, ρ`, there exist
`ε, p₀` such that for every prime `p ≥ p₀`, every symmetric `F ⊆ ZMod p`
containing `0` with density `≤ 1 − ρ` and Fourier *lower* bound `≥ −ε` and
every `U ⊆ ZMod p` of density `≥ α`, there is an ordered `m`-tuple in `U^m`
whose pairwise differences all avoid `F`.

Mathematically: classical, via Green-Tao `U²` regularity + complexity-1
counting. The downstream Lean proof of #42 is then elementary combinatorics,
the Sidon Fourier estimate, and greedy Sidon extraction.
-/


namespace Erdos42

open Finset
open scoped Classical

namespace FourierPositive

/-- An ordered tuple in `U^m` whose pairwise differences avoid `F`. -/
def AvoidsForbiddenDiffs {p m : ℕ} [NeZero p]
    (F U : Finset (ZMod p)) (x : Fin m → ZMod p) : Prop :=
  (∀ i, x i ∈ U) ∧
    ∀ i j : Fin m, i ≠ j → x i - x j ∉ F

/-- **Existence-only finite Fourier avoidance theorem.**

This is the Route A trust boundary. It is the weaker form of the combined
PDF / Ulam-note counting theorem actually needed downstream: apply it with
`m = greedySidonThreshold M` and then extract a Sidon subset greedily. -/
axiom finite_fourier_avoidance_exists
    (m : ℕ) (α ρ : ℝ)
    (_hm : 1 ≤ m) (_hα : 0 < α) (_hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ ≤ p →
    ∀ F U : Finset (ZMod p),
      SymmetricFinset F →
      (0 : ZMod p) ∈ F →
      (F.card : ℝ) ≤ (1 - ρ) * p →
      α * p ≤ (U.card : ℝ) →
      FourierLowerIndicator F ε →
      ∃ x : Fin m → ZMod p, AvoidsForbiddenDiffs F U x

end FourierPositive

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/FourierPositive/Main.lean
    ============================================================= -/

/-
Erdős Problem 42 — Route A application.

Derives Theorem 1.1 (Erdős statement, `Finset ℤ` form) from the single
trust-boundary axiom `finite_fourier_avoidance_exists`. Pipeline (combined PDF /
Ulam note Section 3, with Tao's greedy-Sidon simplification):

  1. Forbidden set: `F := (A − A) mod p` for `p` a prime in `(4N, 8N)`.
     Symmetric, `0 ∈ F`, `|F| ≤ 2N − 1 ≤ (1 − 1/2) p`.
  2. Sidon Fourier lower bound: `1̂_F(r) = |1̂_A(r)|² − (|A|−1)/p ≥ −(|A|−1)/p`,
     which is `≥ −ε` for `p` large enough (combined PDF §3).
  3. `U := [1, N] mod p` has density `≥ 1/8 · p` (since `p < 8N`).
  4. Apply `finite_fourier_avoidance_exists` with
     `m = greedySidonThreshold M` to get a large distinct tuple avoiding `F`.
  5. Take its image `X ⊆ [1,N]`; because `0 ∈ F`, the tuple is injective.
  6. Greedily extract a Sidon subset `B ⊆ X` of size `M`.
-/


namespace Erdos42.FourierPositive

open Finset Erdos42
open scoped Classical

/-! ## Step 2 — Sidon Fourier lower bound -/

/-- The forbidden set: `F_A := (A − A) mod p` projected into `ZMod p`. -/
noncomputable def forbiddenDiffSetMod (p : ℕ) (A : Finset ℤ) : Finset (ZMod p) :=
  (DiffFinset A A).image (fun x : ℤ => (x : ZMod p))

/-- Forbidden set is symmetric. -/
lemma forbiddenDiffSetMod_symmetric (p : ℕ) (A : Finset ℤ) :
    SymmetricFinset (forbiddenDiffSetMod p A) := by
  classical
  intro x
  rw [forbiddenDiffSetMod, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨-d, ?_, by simp⟩
    exact (diffFinset_self_symmetric A d).mp hd
  · rintro ⟨d, hd, hdx⟩
    refine ⟨-d, ?_, ?_⟩
    · exact (diffFinset_self_symmetric A d).mp hd
    · simp [hdx]

/-- `0 ∈ F_A` (when `A` non-empty). -/
lemma zero_mem_forbiddenDiffSetMod (p : ℕ) (A : Finset ℤ) (hA : A.Nonempty) :
    (0 : ZMod p) ∈ forbiddenDiffSetMod p A := by
  classical
  rw [forbiddenDiffSetMod, Finset.mem_image]
  exact ⟨0, zero_mem_diffFinset_self hA, by simp⟩

/-- For `A ⊆ [1, N]` Sidon, `|F_A| ≤ 2N − 1`. -/
lemma forbiddenDiffSetMod_card_le
    {p N : ℕ} (_hp : 0 < p) (_hbig : 2 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) (hA : A.Nonempty) :
    ((forbiddenDiffSetMod p A).card : ℤ) ≤ ((2 * N - 1 : ℕ) : ℤ) := by
  classical
  have hNpos : 0 < N := by
    obtain ⟨a, ha⟩ := hA
    have hNint : (0 : ℤ) < (N : ℤ) := by
      linarith [(hAint a ha).1, (hAint a ha).2]
    exact_mod_cast hNint
  let nonzeroMod : Finset (ZMod p) :=
    ((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p))
  have hsubset : forbiddenDiffSetMod p A ⊆ insert 0 nonzeroMod := by
    intro x hx
    rw [forbiddenDiffSetMod, Finset.mem_image] at hx
    rcases hx with ⟨d, hd, rfl⟩
    by_cases hd0 : d = 0
    · simp [hd0]
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_image.mpr ⟨d, by simpa [hd0] using hd, rfl⟩))
  have hcard_nat : (forbiddenDiffSetMod p A).card ≤ 2 * N - 1 := by
    calc
      (forbiddenDiffSetMod p A).card ≤ (insert 0 nonzeroMod).card :=
        Finset.card_le_card hsubset
      _ ≤ nonzeroMod.card + 1 := Finset.card_insert_le _ _
      _ ≤ ((DiffFinset A A).erase 0).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ (2 * N - 2) + 1 :=
        Nat.add_le_add_right (sidon_nonzero_diff_card_le A N hAint hSidon) 1
      _ = 2 * N - 1 := by omega
  exact_mod_cast hcard_nat

lemma forbiddenDiffSetMod_eq_insert_offDiagDiffSetMod
    {p : ℕ} [NeZero p] (A : Finset ℤ) (hA : A.Nonempty) :
    forbiddenDiffSetMod p A =
      insert 0 (Erdos42.CompactCayley.offDiagDiffSetMod p A) := by
  classical
  ext t
  constructor
  · intro ht
    rw [forbiddenDiffSetMod, Finset.mem_image] at ht
    rcases ht with ⟨d, hd, rfl⟩
    rw [mem_diffFinset] at hd
    rcases hd with ⟨a, ha, b, hb, rfl⟩
    by_cases hzero : ((a - b : ℤ) : ZMod p) = 0
    · exact Finset.mem_insert.mpr (Or.inl hzero)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [Erdos42.CompactCayley.offDiagDiffSetMod, Finset.mem_image]
      have hab : a ≠ b := by
        intro hab
        subst b
        exact hzero (by simp)
      refine ⟨(a, b), ?_, rfl⟩
      rw [Finset.mem_offDiag]
      exact ⟨ha, hb, hab⟩
  · intro ht
    rw [Finset.mem_insert] at ht
    rcases ht with ht0 | ht
    · subst t
      exact zero_mem_forbiddenDiffSetMod p A hA
    · rw [Erdos42.CompactCayley.offDiagDiffSetMod, Finset.mem_image] at ht
      rcases ht with ⟨ab, hab, rfl⟩
      rw [Finset.mem_offDiag] at hab
      rcases hab with ⟨ha, hb, _hne⟩
      rw [forbiddenDiffSetMod, Finset.mem_image]
      exact ⟨ab.1 - ab.2, mem_diffFinset.mpr ⟨ab.1, ha, ab.2, hb, rfl⟩, rfl⟩

/-- Sidon Fourier lower bound (normalized): `Re 1̂_{F_A}(r) ≥ -(|A|−1)/p` for
every character `r` (combined PDF §3). For `p` large enough in `N`, this is
`≥ −ε`, hence `FourierLowerIndicator F_A ε`. -/
lemma sidon_forbidden_fourier_lower
    {p N : ℕ} [Fact p.Prime] [NeZero p] (_hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) (hA : A.Nonempty)
    (ε : ℝ)
    (hε : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε) :
    FourierLowerIndicator (forbiddenDiffSetMod p A) ε := by
  classical
  intro r
  have hε_nonneg : 0 ≤ ε := by
    have hleft : 0 ≤ ((A.card - 1 : ℕ) : ℝ) / (p : ℝ) := by positivity
    exact hleft.trans hε
  by_cases hr : r = 0
  · subst r
    have hcoeff_nonneg : 0 ≤ (normalizedDftCoeff (forbiddenDiffSetMod p A) 0).re := by
      have hp_pos : 0 < (p : ℝ) := by
        exact_mod_cast (Fact.out : p.Prime).pos
      rw [normalizedDftCoeff_zero_eq_card_div]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
      simp [div_nonneg (Nat.cast_nonneg _) hp_pos.le]
    linarith
  · have hF_eq :=
      forbiddenDiffSetMod_eq_insert_offDiagDiffSetMod (p := p) A hA
    have hsum_allowed :=
      Erdos42.CompactCayley.sum_allowedDiffSetMod_eq_neg_forbidden
        (p := p) A hr
    have hsum_forbidden :
        ∑ x ∈ insert 0 (Erdos42.CompactCayley.offDiagDiffSetMod p A),
            ZMod.stdAddChar (-(x * r)) =
          - ∑ x ∈ Erdos42.CompactCayley.allowedDiffSetMod p A,
              ZMod.stdAddChar (-(x * r)) := by
      calc
        ∑ x ∈ insert 0 (Erdos42.CompactCayley.offDiagDiffSetMod p A),
            ZMod.stdAddChar (-(x * r))
            = -(-∑ x ∈ insert 0 (Erdos42.CompactCayley.offDiagDiffSetMod p A),
                ZMod.stdAddChar (-(x * r))) := by simp
        _ = -∑ x ∈ Erdos42.CompactCayley.allowedDiffSetMod p A,
                ZMod.stdAddChar (-(x * r)) := by rw [← hsum_allowed]
    have hcoeff :
        normalizedDftCoeff (forbiddenDiffSetMod p A) r =
          - normalizedDftCoeff (Erdos42.CompactCayley.allowedDiffSetMod p A) r := by
      rw [hF_eq, normalizedDftCoeff_eq_sum, normalizedDftCoeff_eq_sum, hsum_forbidden]
      ring
    have hupper :
        (normalizedDftCoeff (Erdos42.CompactCayley.allowedDiffSetMod p A) r).re ≤ ε :=
      Erdos42.CompactCayley.allowedDiffs_fourier_upper
        (p := p) (N := N) _hbig A hAint hSidon ε hε r hr
    rw [hcoeff]
    simp
    linarith

/-! ## Step 3 — final assembly from existence avoidance + greedy Sidon -/

/-- **Theorem 1.1, Route A.** Same statement as Route B; intended to be proved
from the existence form of finite Fourier avoidance, the forbidden-set Fourier
estimate above, and the shared greedy Sidon extraction. -/
theorem theorem_1_1_from_finite_fourier_avoidance
    (M : ℕ) (_hM : 1 ≤ M) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) → IsSidonInt A → A.Nonempty →
        ∃ B : Finset ℤ,
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ (N : ℤ)) ∧
          IsSidonInt B ∧ B.card = M ∧
          AvoidsNonzeroDiff A B := by
  classical
  let R := Erdos42.CompactCayley.greedySidonThreshold M
  have hRpos : 0 < R := by
    dsimp [R, Erdos42.CompactCayley.greedySidonThreshold]
    omega
  have hRge : 1 ≤ R := Nat.succ_le_of_lt hRpos
  obtain ⟨ε, hεpos, p₀, havoid⟩ :=
    finite_fourier_avoidance_exists R (1 / 8 : ℝ) (1 / 2 : ℝ)
      hRge (by norm_num) (by norm_num)
  obtain ⟨Nε, hNε⟩ :=
    Erdos42.CompactCayley.sidon_card_minus_one_div_prime_eventually_small ε hεpos
  refine ⟨max (p₀ + 1) Nε, ?_⟩
  intro N hN A hAint hSidon hAnonempty
  have hNpos : 0 < N := by
    obtain ⟨a, ha⟩ := hAnonempty
    have hNint : (0 : ℤ) < (N : ℤ) := by
      linarith [(hAint a ha).1, (hAint a ha).2]
    exact_mod_cast hNint
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  haveI : Fact p.Prime := ⟨hpprime⟩
  haveI : NeZero p := ⟨hpprime.ne_zero⟩
  have hp₀le : p₀ ≤ p := by omega
  have hpN : N < p := by omega
  have hpupper : p < 8 * N := by
    have hple' : p ≤ 8 * N := by omega
    have hpne2 : p ≠ 2 := by omega
    have hpodd : Odd p := hpprime.odd_of_ne_two hpne2
    have hpne : p ≠ 8 * N := by
      intro hpeq
      have heven : Even p := by
        rw [hpeq, even_iff_two_dvd]
        exact ⟨4 * N, by ring⟩
      exact (Nat.not_even_iff_odd.mpr hpodd) heven
    omega
  let F : Finset (ZMod p) := forbiddenDiffSetMod p A
  let U : Finset (ZMod p) :=
    (Finset.Icc 1 N).image (fun n : ℕ => (n : ZMod p))
  have hF_sym : SymmetricFinset F := by
    simpa [F] using forbiddenDiffSetMod_symmetric p A
  have hF_zero : (0 : ZMod p) ∈ F := by
    simpa [F] using zero_mem_forbiddenDiffSetMod p A hAnonempty
  have hF_density : (F.card : ℝ) ≤ (1 - 1 / 2 : ℝ) * p := by
    have hcard_int :=
      forbiddenDiffSetMod_card_le (p := p) (N := N) hpprime.pos (by omega) A
        hAint hSidon hAnonempty
    have hcard_real :
        (F.card : ℝ) ≤ (((2 * N - 1 : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast hcard_int
    have hbound :
        (((2 * N - 1 : ℕ) : ℤ) : ℝ) ≤ (1 / 2 : ℝ) * (p : ℝ) := by
      have hcast : (((2 * N - 1 : ℕ) : ℤ) : ℝ) = 2 * (N : ℝ) - 1 := by
        have hle : 1 ≤ 2 * N := by omega
        rw [Nat.cast_sub hle]
        norm_num
      have hpgtR : 4 * (N : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
      rw [hcast]
      nlinarith
    have hhalf : (1 - 1 / 2 : ℝ) * (p : ℝ) = (1 / 2 : ℝ) * p := by ring
    rw [hhalf]
    exact hcard_real.trans hbound
  have hUcard : U.card = N := by
    dsimp [U]
    have hinj :
        Set.InjOn (fun n : ℕ => (n : ZMod p)) ((Finset.Icc 1 N : Finset ℕ) : Set ℕ) := by
      intro i hi j hj hij
      change i ∈ (Finset.Icc 1 N : Finset ℕ) at hi
      change j ∈ (Finset.Icc 1 N : Finset ℕ) at hj
      rw [Finset.mem_Icc] at hi hj
      exact Erdos42.CompactCayley.nat_eq_of_zmod_eq_of_lt
        (p := p) (i := i) (j := j) (by omega) (by omega) hij
    rw [Finset.card_image_of_injOn hinj]
    simp
  have hU_density : (1 / 8 : ℝ) * (p : ℝ) ≤ (U.card : ℝ) := by
    rw [hUcard]
    have hpupperR : (p : ℝ) < 8 * (N : ℝ) := by exact_mod_cast hpupper
    nlinarith
  have hsmall : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε :=
    hNε N p (by omega) hpgt A hAint hSidon
  have hF_fourier : FourierLowerIndicator F ε := by
    simpa [F] using
      sidon_forbidden_fourier_lower (p := p) (N := N) hpgt A hAint hSidon hAnonempty ε hsmall
  obtain ⟨x, hx⟩ :=
    havoid p hp₀le F U hF_sym hF_zero hF_density hU_density hF_fourier
  have hxU : ∀ i : Fin R, x i ∈ U := hx.1
  have hxAvoid : ∀ i j : Fin R, i ≠ j → x i - x j ∉ F := hx.2
  have hpre :
      ∀ i : Fin R, ∃ n : ℕ, n ∈ Finset.Icc 1 N ∧ (n : ZMod p) = x i := by
    intro i
    have hxi := hxU i
    change x i ∈ U at hxi
    change x i ∈ (Finset.Icc 1 N).image (fun n : ℕ => (n : ZMod p)) at hxi
    rw [Finset.mem_image] at hxi
    rcases hxi with ⟨n, hn, hncast⟩
    exact ⟨n, hn, hncast⟩
  let nOf : Fin R → ℕ := fun i => Classical.choose (hpre i)
  have hnMem : ∀ i : Fin R, nOf i ∈ Finset.Icc 1 N := by
    intro i
    exact (Classical.choose_spec (hpre i)).1
  have hnCast : ∀ i : Fin R, (nOf i : ZMod p) = x i := by
    intro i
    exact (Classical.choose_spec (hpre i)).2
  let X : Finset ℤ := (Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ))
  have hXcard : R ≤ X.card := by
    have hinj :
        Set.InjOn (fun i : Fin R => (nOf i : ℤ)) ((Finset.univ : Finset (Fin R)) : Set (Fin R)) := by
      intro i _hi j _hj hij
      by_contra hijFin
      have hnEq : nOf i = nOf j := Int.ofNat_injective hij
      have hxEq : x i = x j := by
        rw [← hnCast i, ← hnCast j, hnEq]
      exact (hxAvoid i j hijFin) (by simpa [F, hxEq] using hF_zero)
    change R ≤ ((Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ))).card
    rw [Finset.card_image_of_injOn hinj]
    simp
  have hXint : ∀ b ∈ X, 1 ≤ b ∧ b ≤ (N : ℤ) := by
    intro b hb
    change b ∈ (Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ)) at hb
    rw [Finset.mem_image] at hb
    rcases hb with ⟨i, _hi, rfl⟩
    have hi := hnMem i
    rw [Finset.mem_Icc] at hi
    exact_mod_cast hi
  have hAvoidAX : AvoidsNonzeroDiff A X := by
    intro d hdA hdX
    rw [mem_diffFinset] at hdA hdX
    rcases hdA with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    rcases hdX with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
    by_cases hzero : a₁ - a₂ = 0
    · exact hzero
    · exfalso
      change b₁ ∈ (Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ)) at hb₁
      change b₂ ∈ (Finset.univ : Finset (Fin R)).image (fun i => (nOf i : ℤ)) at hb₂
      rw [Finset.mem_image] at hb₁ hb₂
      rcases hb₁ with ⟨i, _hi, hb₁eq⟩
      rcases hb₂ with ⟨j, _hj, hb₂eq⟩
      have hij : i ≠ j := by
        intro hij
        subst j
        apply hzero
        rw [← hb₁eq, ← hb₂eq] at hbDiff
        linarith
      have hFmem : x i - x j ∈ F := by
        change x i - x j ∈ forbiddenDiffSetMod p A
        rw [forbiddenDiffSetMod, Finset.mem_image]
        refine ⟨a₁ - a₂, ?_, ?_⟩
        · rw [mem_diffFinset]
          exact ⟨a₁, ha₁, a₂, ha₂, rfl⟩
        · calc
            ((a₁ - a₂ : ℤ) : ZMod p) = ((b₁ - b₂ : ℤ) : ZMod p) := by rw [hbDiff]
            _ = ((nOf i : ℤ) - (nOf j : ℤ) : ℤ) := by rw [hb₁eq, hb₂eq]
            _ = x i - x j := by
              rw [← hnCast i, ← hnCast j]
              norm_num
      exact (hxAvoid i j hij) hFmem
  obtain ⟨B, hBX, hBcard, hBsidon⟩ :=
    Erdos42.CompactCayley.exists_sidon_subset_of_card_ge M X (by simpa [R] using hXcard)
  refine ⟨B, ?_, hBsidon, hBcard, ?_⟩
  · intro b hb
    exact hXint b (hBX hb)
  · intro d hdA hdB
    apply hAvoidAX d hdA
    rw [mem_diffFinset] at hdB ⊢
    rcases hdB with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨b₁, hBX hb₁, b₂, hBX hb₂, rfl⟩

end Erdos42.FourierPositive

/-! =============================================================
    Section from: Erdos/P42/FC/Local.lean
    ============================================================= -/

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

/-! =============================================================
    Section from: Erdos/P42/FC/Shape.lean
    ============================================================= -/

/-
Erdős Problem 42 — formal-conjectures shape wrapper.

The repository does not currently vendor `formal-conjectures`, so this file
mirrors the upstream RHS locally and proves it equivalent to the existing
`FC/Local.lean` statement. If the FC package is later added as a Lake
dependency, this is the file to replace by an import of
`FormalConjectures.ErdosProblems.42` plus a proof of its exact theorem.
-/


namespace Erdos42

open Filter Set
open scoped Pointwise

namespace FormalConjecturesShape

universe u

/-! ## Upstream-shaped local aliases -/

/-- Local stand-in for FC's explicit-exists binder `∃ᵉ`.
Semantically this is ordinary existence; FC uses the notation for linting. -/
def ExplicitExists {α : Sort u} (P : α → Prop) : Prop :=
  ∃ x, P x

theorem explicitExists_iff_exists {α : Sort u} {P : α → Prop} :
    ExplicitExists P ↔ ∃ x, P x := by
  rfl

/-- FC-shaped Sidon predicate. This is definitionally equal to `Erdos42.IsSidon`. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

theorem isSidon_iff_local (A : Set ℕ) :
    IsSidon A ↔ Erdos42.IsSidon A := by
  rfl

/-- FC-shaped maximal Sidon predicate. This is definitionally equal to the local
predicate in `FC/Local.lean`. -/
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ x ∈ Set.Icc 1 N, x ∉ A → ¬ IsSidon (insert x A)

theorem isMaximalSidonSetIn_iff_local (A : Set ℕ) (N : ℕ) :
    IsMaximalSidonSetIn A N ↔ Erdos42.IsMaximalSidonSetIn A N := by
  rfl

/-- The upstream FC RHS, with `ExplicitExists` standing in for FC's `∃ᵉ`. -/
def erdos42RHS : Prop :=
  ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
    ExplicitExists fun B : Set ℕ =>
      B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B)) = {0}

/-- The already-proved local RHS from `FC/Local.lean`. -/
def localRHS : Prop :=
  ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : Erdos42.IsMaximalSidonSetIn A N),
    ∃ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ Erdos42.IsSidon B ∧ B.ncard = M ∧
      ((A - A) ∩ (B - B) : Set ℕ) = {0}

/-- The FC-shaped RHS and our existing local RHS are definitionally equivalent.

This is the key handoff theorem for later replacing the local aliases by the
real `formal-conjectures` imports. -/
theorem erdos42RHS_iff_localRHS :
    erdos42RHS ↔ localRHS := by
  unfold erdos42RHS localRHS ExplicitExists IsMaximalSidonSetIn IsSidon
    Erdos42.IsMaximalSidonSetIn Erdos42.IsSidon
  rfl

/-- **Formal-conjectures shape for #42** under `answer := True`.

This matches the upstream theorem after replacing FC's `answer(sorry)` by
`True` and interpreting FC's `∃ᵉ` as `ExplicitExists`. -/
theorem erdos_42 :
    True ↔ erdos42RHS :=
  Iff.trans Erdos42.erdos_42 erdos42RHS_iff_localRHS.symm

/-- Equivalence between the local FC wrapper theorem and the upstream-shaped
wrapper theorem. -/
theorem erdos_42_iff_local_wrapper :
    (True ↔ erdos42RHS) ↔ (True ↔ localRHS) := by
  rw [erdos42RHS_iff_localRHS]

end FormalConjecturesShape

end Erdos42
