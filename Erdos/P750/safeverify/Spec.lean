/-
SafeVerify target for Erdős Problem 750.

Enumerates the public theorems and the supporting definitions that `Proof.lean`
provides. The bodies in this file are `sorry` *by design* — SafeVerify only
inspects signatures here; the actual proofs live in `Proof.lean`, where they
are sorry-free. SafeVerify replays both files and checks the submission's
matching declarations only depend on the allow-list:

  Mathlib core (`propext`, `Classical.choice`, `Quot.sound`)
  + `Erdos750.stiebitz_lower_bound`  -- Stiebitz's theorem (1985 thesis), only
                                        used by `infinite_chromatic_local_oct`
                                        and `erdos_750_independence`.

The extra axiom name is local to this problem; reproduction recipe in
`../README.md` § "Verifying with SafeVerify".

Lemmas 3.1, 3.2 and Theorem 4.1 do **not** depend on Stiebitz; the trust boundary
attaches solely to the infinite-construction step where chromatic-number
unboundedness is asserted.
-/

import Mathlib

namespace Erdos750

open SimpleGraph Filter

universe u

abbrev MycVerts (s : ℕ) (V : Type u) : Type u := (Fin s × V) ⊕ Unit

@[reducible] def apex (s : ℕ) (V : Type u) : MycVerts s V := Sum.inr ()

def genMyc (s : ℕ) {V : Type u} (G : SimpleGraph V) : SimpleGraph (MycVerts s V) := sorry

noncomputable def oct {V : Type u} [DecidableEq V] (G : SimpleGraph V) (X : Finset V) : ℕ :=
  sorry

def IsRecursivelyBuiltMr : ∀ (_r : ℕ) {_V : Type u} (_G : SimpleGraph _V), Prop := sorry

theorem genMyc_chromaticNumber_le_succ {V : Type u} (s : ℕ) (G : SimpleGraph V) :
    (genMyc s G).chromaticNumber ≤ G.chromaticNumber + 1 := sorry

lemma oct_mono_edges {V : Type u} [DecidableEq V] {H G : SimpleGraph V}
    (hsub : H ≤ G) (X : Finset V) :
    oct H X ≤ oct G X := sorry

theorem oct_genMyc_le {V : Type u} [DecidableEq V]
    (s : ℕ) (G : SimpleGraph V) (X : Finset (MycVerts s V)) :
    oct (genMyc s G) X ≤ s * oct G ((X.biUnion (fun a => match a with
        | Sum.inl (_, v) => ({v} : Finset V) | Sum.inr () => ∅))) +
      (if apex s V ∈ X then 1 else 0) := sorry

theorem genMyc_oddCycle_through_apex_long {V : Type u} (s : ℕ) (_hs : 1 ≤ s)
    (B : SimpleGraph V) (_hB : B.IsBipartite) :
    ∀ (c : (genMyc s B).Walk (apex s V) (apex s V)),
      c.IsCycle → Odd c.length → 2 * s + 1 ≤ c.length := sorry

theorem finite_oct_profile (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsRecursivelyBuiltMr r G ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card := sorry

/-- Strengthened form of `finite_oct_profile`: also asserts `χ(G) = r`. Depends on
`stiebitz_lower_bound` (the original `finite_oct_profile` does not). -/
theorem finite_oct_profile_with_chromatic
    (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsRecursivelyBuiltMr r G ∧
      G.chromaticNumber = (r : ℕ∞) ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card := sorry

theorem infinite_chromatic_local_oct (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card := sorry

theorem erdos_750_independence :
    ∀ (f : ℕ → NNReal) (_ : Tendsto f atTop atTop),
      ∃ (V : Type) (G : SimpleGraph V),
        G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m / 2 : ℝ) - f m ≤ I.ncard := sorry

/-- Wrapper matching the upstream `formal-conjectures` syntax with NNReal-truncated
subtraction (where `m / 2` is natural-number division). -/
theorem erdos_750_independence_FC_form :
    ∀ (f : ℕ → NNReal) (_ : Tendsto f atTop atTop),
      ∃ (V : Type) (G : SimpleGraph V),
        G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ ((m / 2 : ℕ) : NNReal) - f m ≤ (I.ncard : NNReal) := sorry

end Erdos750
