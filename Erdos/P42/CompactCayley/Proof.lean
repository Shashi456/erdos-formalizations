/-
**STANDALONE FLAT BUNDLE** of Erdős Problem #42 — compact-Cayley route.

This file concatenates the P42 shared machinery plus the Route B/compact-Cayley development.
It is intended as a one-file snapshot: no project-local imports.

Trust boundary (verify with `#print axioms`):
  Mathlib core (propext, Classical.choice, Quot.sound) +
  Erdos42.CompactCayley.compact_cayley_clique
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
    Section from: Erdos/P42/CompactCayley/CliqueAxiom.lean
    ============================================================= -/

/-
Erdős Problem 42 — Route B trust boundary: compact Cayley clique theorem.

Theorem 2.1 of `erdos42_compact_sidon_clean.pdf` (Google Drive link in
`forum.md`). A dense symmetric Cayley graph on `ZMod p`, with `0 ∉ T`
and small nontrivial Fourier coefficients (upper bound), contains a clique of
any prescribed size for all sufficiently large primes.

Mathematically: classical, unconditional. The compact-Cayley PDF proves it via
Fourier extraction (Lemma 2.2), equidistribution of finite lifts (2.3), basic
limit properties (2.4), spectral cut-norm control (2.5), counting convergence
(2.6), and clique forcing on connected compact groups (2.7).

This file is the trust boundary for Route B: replace this `axiom` with a
`theorem` once those six lemmas are formalized.
-/


namespace Erdos42

/-- A `Finset C` is a clique in the Cayley graph on `ZMod p` with allowed
difference set `T`: every pair of distinct vertices in `C` has its difference
in `T`. -/
def CliqueInCayley {p : ℕ} (T C : Finset (ZMod p)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x - y ∈ T

namespace CompactCayley

/-- **Compact Cayley clique theorem (compact PDF Theorem 2.1).** Trust
boundary for Route B. For every clique size `ℓ ≥ 2` and every density `η > 0`,
there exists `ε > 0` such that for all sufficiently large primes `p`, every
symmetric `T ⊆ ZMod p` with `0 ∉ T`, density `≥ η`, and Fourier upper bound
`≤ ε` (at every nontrivial character) contains an `ℓ`-clique in its Cayley
graph. -/
axiom compact_cayley_clique
    (ℓ : ℕ) (η : ℝ) (_hℓ : 2 ≤ ℓ) (_hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      FourierUpperIndicator T ε →
      ∃ C : Finset (ZMod p),
        C.card = ℓ ∧ CliqueInCayley T C

end CompactCayley

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CliqueEndpoint.lean
    ============================================================= -/

/-
Erdős Problem 42 — internal finite lemmas for the compact-Cayley theorem.

This file starts opening the remaining Route B trust boundary
`compact_cayley_clique`.  The lemmas here are finite bookkeeping around the
endpoint of the compactness argument: once counting convergence gives an
ordered tuple whose pairwise differences lie in the allowed set, `0 ∉ T`
turns that tuple into an actual finite clique.
-/


namespace Erdos42.CompactCayley

open Finset Erdos42

/-- An ordered `ℓ`-tuple whose distinct pairwise differences all lie in the
allowed Cayley set `T`. -/
def CliqueTuple {p ℓ : ℕ} (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : Prop :=
  ∀ i j : Fin ℓ, i ≠ j → x i - x j ∈ T

lemma cliqueTuple_injective_of_zero_notMem
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hT0 : (0 : ZMod p) ∉ T) (hx : CliqueTuple T x) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  have hdiff : x i - x j ∈ T := hx i j hne
  apply hT0
  simpa [hij] using hdiff

/-- A zero-free ordered clique tuple yields the `Finset` clique required by
`compact_cayley_clique`. This is the finite endpoint used after the compact
counting argument proves that at least one ordered clique tuple exists. -/
theorem exists_clique_of_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    {x : Fin ℓ → ZMod p} (hx : CliqueTuple T x) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  classical
  let C : Finset (ZMod p) := (Finset.univ : Finset (Fin ℓ)).image x
  have hinj : Function.Injective x :=
    cliqueTuple_injective_of_zero_notMem hT0 hx
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro y hy z hz hyz
    change y ∈ (Finset.univ : Finset (Fin ℓ)).image x at hy
    change z ∈ (Finset.univ : Finset (Fin ℓ)).image x at hz
    rw [Finset.mem_image] at hy hz
    rcases hy with ⟨i, _hi, rfl⟩
    rcases hz with ⟨j, _hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      exact hyz (by simp [hij])
    exact hx i j hij

/-- Contrapositive form: a zero-free Cayley graph with no `ℓ`-clique has no
ordered clique tuple of length `ℓ`. -/
lemma not_cliqueTuple_of_no_clique
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C)
    (x : Fin ℓ → ZMod p) :
    ¬ CliqueTuple T x := by
  intro hx
  exact hNoClique (exists_clique_of_cliqueTuple hT0 hx)

/-- Boolean-valued indicator for ordered clique tuples, useful when connecting
finite homomorphism densities to actual cliques. -/
noncomputable def cliqueTupleIndicator {p ℓ : ℕ}
    (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : ℂ :=
  by
    classical
    exact if CliqueTuple T x then 1 else 0

lemma cliqueTupleIndicator_eq_zero_of_no_clique
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C)
    (x : Fin ℓ → ZMod p) :
    cliqueTupleIndicator T x = 0 := by
  classical
  unfold cliqueTupleIndicator
  simp [not_cliqueTuple_of_no_clique hT0 hNoClique x]

/-- The finite set of ordered `ℓ`-tuples forming a clique in the Cayley graph. -/
noncomputable def cliqueTupleFinset {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : Finset (Fin ℓ → ZMod p) :=
  by
    classical
    exact (Finset.univ : Finset (Fin ℓ → ZMod p)).filter (fun x => CliqueTuple T x)

lemma mem_cliqueTupleFinset {p ℓ : ℕ} [NeZero p]
    {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p} :
    x ∈ cliqueTupleFinset (ℓ := ℓ) T ↔ CliqueTuple T x := by
  classical
  simp [cliqueTupleFinset]

lemma cliqueTupleFinset_nonempty_of_cliqueTuple
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    {x : Fin ℓ → ZMod p} (hx : CliqueTuple T x) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty :=
  ⟨x, mem_cliqueTupleFinset.mpr hx⟩

lemma exists_clique_of_cliqueTupleFinset_nonempty
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (h : (cliqueTupleFinset (ℓ := ℓ) T).Nonempty) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rcases h with ⟨x, hx⟩
  exact exists_clique_of_cliqueTuple hT0 (mem_cliqueTupleFinset.mp hx)

lemma cliqueTupleFinset_nonempty_of_clique
    {p ℓ : ℕ} [NeZero p] {T C : Finset (ZMod p)}
    (hCcard : C.card = ℓ) (hClique : CliqueInCayley T C) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty := by
  classical
  let e : C ≃ Fin ℓ := C.equivFinOfCardEq hCcard
  let x : Fin ℓ → ZMod p := fun i => (e.symm i).1
  refine cliqueTupleFinset_nonempty_of_cliqueTuple (T := T) (x := x) ?_
  intro i j hij
  have hxi : x i ∈ C := (e.symm i).2
  have hxj : x j ∈ C := (e.symm j).2
  have hne : x i ≠ x j := by
    intro h
    have hsub : e.symm i = e.symm j := Subtype.ext h
    exact hij (by simpa using congrArg e hsub)
  exact hClique (x i) hxi (x j) hxj hne

lemma cliqueTupleFinset_nonempty_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  refine ⟨exists_clique_of_cliqueTupleFinset_nonempty hT0, ?_⟩
  rintro ⟨C, hCcard, hClique⟩
  exact cliqueTupleFinset_nonempty_of_clique hCcard hClique

/-- The edge set of the complete graph on `Fin ℓ`, oriented by the natural
order to avoid double-counting. -/
def cliqueEdgePairs (ℓ : ℕ) : Finset (Fin ℓ × Fin ℓ) :=
  (Finset.univ : Finset (Fin ℓ × Fin ℓ)).filter (fun e => e.1 < e.2)

/-- Product weight for the finite Cayley `K_ℓ` homomorphism density. For
indicator functions this is `1` exactly on ordered clique tuples and `0`
otherwise, once `T` is symmetric. -/
noncomputable def cliqueKernelWeight {p ℓ : ℕ}
    (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, indicatorC T (x e.1 - x e.2)

lemma cliqueKernelWeight_eq_one_of_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hx : CliqueTuple T x) :
    cliqueKernelWeight T x = 1 := by
  classical
  unfold cliqueKernelWeight
  apply Finset.prod_eq_one
  intro e he
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  have hmem : x e.1 - x e.2 ∈ T := hx e.1 e.2 (ne_of_lt hlt)
  simp [indicatorC, hmem]

lemma cliqueKernelWeight_eq_zero_of_not_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hTsym : SymmetricFinset T) (hx : ¬ CliqueTuple T x) :
    cliqueKernelWeight T x = 0 := by
  classical
  rw [CliqueTuple, not_forall] at hx
  rcases hx with ⟨i, hx⟩
  rw [not_forall] at hx
  rcases hx with ⟨j, hx⟩
  rw [Classical.not_imp] at hx
  rcases hx with ⟨hij, hnot⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · unfold cliqueKernelWeight
    apply Finset.prod_eq_zero (i := (i, j))
    · simp [cliqueEdgePairs, hlt]
    · simp [indicatorC, hnot]
  · have hnot' : x j - x i ∉ T := by
      intro hji
      have hneg : -(x j - x i) ∈ T := (hTsym (x j - x i)).mp hji
      exact hnot (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg)
    unfold cliqueKernelWeight
    apply Finset.prod_eq_zero (i := (j, i))
    · simp [cliqueEdgePairs, hgt]
    · simp [indicatorC, hnot']

lemma cliqueKernelWeight_eq_cliqueTupleIndicator_of_symmetric
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hTsym : SymmetricFinset T)
    (x : Fin ℓ → ZMod p) :
    cliqueKernelWeight T x = cliqueTupleIndicator T x := by
  classical
  unfold cliqueTupleIndicator
  by_cases hx : CliqueTuple T x
  · simp [hx, cliqueKernelWeight_eq_one_of_cliqueTuple hx]
  · simp [hx, cliqueKernelWeight_eq_zero_of_not_cliqueTuple hTsym hx]

/-- Ordered clique-tuple count. This is the finite, unnormalized version of the
`K_ℓ` Cayley homomorphism density for indicator functions. -/
noncomputable def cliqueTupleCount {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ∑ x : Fin ℓ → ZMod p, cliqueTupleIndicator T x

lemma cliqueTupleCount_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueTupleCount (ℓ := ℓ) T = 0 := by
  classical
  unfold cliqueTupleCount
  simp [cliqueTupleIndicator_eq_zero_of_no_clique hT0 hNoClique]

lemma cliqueTupleCount_eq_card_cliqueTupleFinset
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    cliqueTupleCount (ℓ := ℓ) T =
      ((cliqueTupleFinset (ℓ := ℓ) T).card : ℂ) := by
  classical
  rw [cliqueTupleCount]
  change
    (∑ x ∈ (Finset.univ : Finset (Fin ℓ → ZMod p)),
        if CliqueTuple T x then (1 : ℂ) else 0) =
      (((Finset.univ : Finset (Fin ℓ → ZMod p)).filter
        (fun x => CliqueTuple T x)).card : ℂ)
  rw [Finset.sum_boole]

/-- Normalized ordered clique-tuple density. -/
noncomputable def cliqueTupleDensity {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) * cliqueTupleCount (ℓ := ℓ) T

lemma cliqueTupleDensity_eq_card_cliqueTupleFinset
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    cliqueTupleDensity (ℓ := ℓ) T =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ((cliqueTupleFinset (ℓ := ℓ) T).card : ℂ) := by
  simp [cliqueTupleDensity, cliqueTupleCount_eq_card_cliqueTupleFinset]

lemma card_fun_fin_zmod (p ℓ : ℕ) [NeZero p] :
    Fintype.card (Fin ℓ → ZMod p) = p ^ ℓ := by
  simp [ZMod.card]

lemma cliqueTupleDensity_re_eq_card_div
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    (cliqueTupleDensity (ℓ := ℓ) T).re =
      ((cliqueTupleFinset (ℓ := ℓ) T).card : ℝ) /
        (Fintype.card (Fin ℓ → ZMod p) : ℝ) := by
  rw [cliqueTupleDensity_eq_card_cliqueTupleFinset]
  have hden :
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) =
        (((Fintype.card (Fin ℓ → ZMod p) : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [hden, Complex.re_ofReal_mul]
  simp [div_eq_inv_mul]

lemma cliqueTupleDensity_re_pos_iff_cliqueTupleFinset_nonempty
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    0 < (cliqueTupleDensity (ℓ := ℓ) T).re ↔
      (cliqueTupleFinset (ℓ := ℓ) T).Nonempty := by
  rw [cliqueTupleDensity_re_eq_card_div]
  have hden_pos : 0 < (Fintype.card (Fin ℓ → ZMod p) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin ℓ → ZMod p))
  rw [div_eq_inv_mul, mul_pos_iff_of_pos_left (inv_pos.mpr hden_pos)]
  constructor
  · intro hcard
    exact Finset.card_pos.mp (by exact_mod_cast hcard)
  · intro hnonempty
    exact_mod_cast (Finset.card_pos.mpr hnonempty)

lemma cliqueTupleDensity_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T) :
    0 < (cliqueTupleDensity (ℓ := ℓ) T).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [cliqueTupleDensity_re_pos_iff_cliqueTupleFinset_nonempty]
  exact cliqueTupleFinset_nonempty_iff_exists_clique hT0

/-- Product-form `K_ℓ` density, matching the notation in the compact-Cayley
PDF before it is specialized to indicators of Cayley sets. -/
noncomputable def cliqueKernelDensity {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, cliqueKernelWeight T x

lemma cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) :
    cliqueKernelDensity (ℓ := ℓ) T = cliqueTupleDensity (ℓ := ℓ) T := by
  classical
  simp [cliqueKernelDensity, cliqueTupleDensity, cliqueTupleCount,
    cliqueKernelWeight_eq_cliqueTupleIndicator_of_symmetric hTsym]

lemma cliqueTupleDensity_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueTupleDensity (ℓ := ℓ) T = 0 := by
  simp [cliqueTupleDensity, cliqueTupleCount_eq_zero_of_no_clique hT0 hNoClique]

/-- Nonzero ordered clique-tuple count yields an actual finite clique. -/
theorem exists_clique_of_cliqueTupleCount_ne_zero
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hcount : cliqueTupleCount (ℓ := ℓ) T ≠ 0) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  by_contra hNoClique
  exact hcount (cliqueTupleCount_eq_zero_of_no_clique hT0 hNoClique)

/-- Nonzero normalized ordered `K_ℓ` density yields an actual finite clique. -/
theorem exists_clique_of_cliqueTupleDensity_ne_zero
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : cliqueTupleDensity (ℓ := ℓ) T ≠ 0) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  by_contra hNoClique
  exact hdensity (cliqueTupleDensity_eq_zero_of_no_clique hT0 hNoClique)

/-- The form used at the end of the compactness proof: once counting
convergence gives a strictly positive real part for the finite `K_ℓ` density,
the finite Cayley graph contains an `ℓ`-clique. -/
theorem exists_clique_of_cliqueTupleDensity_re_pos
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : 0 < (cliqueTupleDensity (ℓ := ℓ) T).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  refine exists_clique_of_cliqueTupleDensity_ne_zero hT0 ?_
  intro hzero
  exact (ne_of_gt hdensity) (by simp [hzero])

lemma cliqueKernelDensity_eq_zero_of_no_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    (hNoClique : ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C) :
    cliqueKernelDensity (ℓ := ℓ) T = 0 := by
  rw [cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric hTsym]
  exact cliqueTupleDensity_eq_zero_of_no_clique hT0 hNoClique

lemma cliqueKernelDensity_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T) :
    0 < (cliqueKernelDensity (ℓ := ℓ) T).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric hTsym]
  exact cliqueTupleDensity_re_pos_iff_exists_clique hT0

end Erdos42.CompactCayley

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
    Section from: Erdos/P42/CompactCayley/Main.lean
    ============================================================= -/

/-
Erdős Problem 42 — Route B final assembly.

This is the only compact-Cayley downstream file that imports the
`compact_cayley_clique` trust-boundary axiom. The finite allowed-difference
Fourier estimates and greedy Sidon extraction stay in `Application.lean` so
Route A can reuse them without importing this axiom.
-/


namespace Erdos42.CompactCayley

open Finset Erdos42

/-! ## Final assembly: Theorem 1.1 from `compact_cayley_clique` -/

/-- **Theorem 1.1, Route B.** For every `M ≥ 1`, there is `N₀` such that for
all `N ≥ N₀` and every non-empty Sidon `A ⊆ [1, N] ⊂ ℤ`, there is a Sidon
`B ⊆ [1, N]` with `|B| = M` and no nonzero common difference. Proved
conditional on `compact_cayley_clique`. -/
theorem theorem_1_1_from_compact_cayley
    (M : ℕ) (_hM : 1 ≤ M) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) → IsSidonInt A → A.Nonempty →
        ∃ B : Finset ℤ,
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ (N : ℤ)) ∧
          IsSidonInt B ∧ B.card = M ∧
          AvoidsNonzeroDiff A B := by
  classical
  let R := greedySidonThreshold M
  have hRpos : 0 < R := by
    dsimp [R, greedySidonThreshold]
    omega
  have hCliqueSize : 2 ≤ 8 * R := by omega
  obtain ⟨ε, hεpos, p₀, hcompact⟩ :=
    compact_cayley_clique (8 * R) (1 / 2 : ℝ) hCliqueSize (by norm_num)
  obtain ⟨Nε, hNε⟩ := sidon_card_minus_one_div_prime_eventually_small ε hεpos
  refine ⟨max (p₀ + 1) Nε, ?_⟩
  intro N hN A hAint hSidon _hAnonempty
  have hNpos : 0 < N := by omega
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp₀lt : p₀ < p := by omega
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
  let T : Finset (ZMod p) := allowedDiffSetMod p A
  have hT_sym : SymmetricFinset T := by
    simpa [T] using allowedDiffSetMod_symmetric p A
  have hT_zero : (0 : ZMod p) ∉ T := by
    simpa [T] using zero_notMem_allowedDiffSetMod p A
  have hT_density : (1 / 2 : ℝ) * p ≤ (T.card : ℝ) := by
    simpa [T] using allowedDiffSetMod_density (p := p) (N := N) hpgt A hAint hSidon
  have hsmall : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε :=
    hNε N p (by omega) hpgt A hAint hSidon
  have hT_fourier : FourierUpperIndicator T ε := by
    simpa [T] using
      allowedDiffs_fourier_upper (p := p) (N := N) hpgt A hAint hSidon ε hsmall
  obtain ⟨C, hCcard, hCclique⟩ :=
    hcompact p hp₀lt T hT_sym hT_zero hT_density hT_fourier
  obtain ⟨s, hs⟩ :=
    exists_large_intersection_cyclicInterval (p := p) (N := N) (R := R)
      hpN C (by simpa [R] using hCcard) hpupper
  let X : Finset ℤ := intervalLiftSet p N s C
  have hXcard : R ≤ X.card := by
    dsimp [X]
    rw [intervalLiftSet_card_eq hpN]
    exact hs
  obtain ⟨B, hBX, hBcard, hBsidon⟩ := exists_sidon_subset_of_card_ge M X hXcard
  refine ⟨B, ?_, hBsidon, hBcard, ?_⟩
  · intro b hb
    rcases mem_intervalLiftSet.mp (hBX hb) with ⟨i, hiN, _hiC, rfl⟩
    constructor <;> omega
  · intro d hdA hdB
    rw [mem_diffFinset] at hdA hdB
    rcases hdA with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    rcases hdB with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
    by_cases hzero : a₁ - a₂ = 0
    · exact hzero
    · exfalso
      rcases mem_intervalLiftSet.mp (hBX hb₁) with ⟨i₁, hi₁N, hi₁C, hb₁eq⟩
      rcases mem_intervalLiftSet.mp (hBX hb₂) with ⟨i₂, hi₂N, hi₂C, hb₂eq⟩
      have hbne : b₁ ≠ b₂ := by
        intro hb
        apply hzero
        rw [hb] at hbDiff
        linarith
      have hine : i₁ ≠ i₂ := by
        intro hi
        apply hbne
        rw [hb₁eq, hb₂eq, hi]
      let y₁ : ZMod p := s + (i₁ : ZMod p)
      let y₂ : ZMod p := s + (i₂ : ZMod p)
      have hyne : y₁ ≠ y₂ := by
        intro hy
        apply hine
        apply nat_eq_of_zmod_eq_of_lt
          (Nat.lt_trans hi₁N hpN) (Nat.lt_trans hi₂N hpN)
        apply add_left_cancel (a := s)
        simpa [y₁, y₂] using hy
      have hallowed : y₁ - y₂ ∈ T := hCclique y₁ hi₁C y₂ hi₂C hyne
      have hyDiff : y₁ - y₂ = ((a₁ - a₂ : ℤ) : ZMod p) := by
        calc
          y₁ - y₂ = (i₁ : ZMod p) - (i₂ : ZMod p) := by
            simp [y₁, y₂]
          _ = ((b₁ - b₂ : ℤ) : ZMod p) := by
            rw [hb₁eq, hb₂eq]
            norm_num
          _ = ((a₁ - a₂ : ℤ) : ZMod p) := by
            rw [hbDiff]
      have hcast : ((a₁ - a₂ : ℤ) : ZMod p) ∈ allowedDiffSetMod p A := by
        simpa [T, hyDiff] using hallowed
      rw [allowedDiffSetMod, Finset.mem_filter] at hcast
      exact hcast.2.2 a₁ ha₁ a₂ ha₂ rfl

end Erdos42.CompactCayley
