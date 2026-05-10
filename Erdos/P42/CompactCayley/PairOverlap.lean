/-
Erdős Problem 42 — generic finite pair-overlap predicates.
-/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos42.CompactCayley

open scoped Classical

/-- The finite fiber of pairs in `Q × Q` with prescribed difference.  This
definition fixes the otherwise hidden decidability argument of `Finset.filter`,
so downstream bounds can share exactly the same finite set. -/
noncomputable def pairFiber {G : Type*} [Sub G] (Q : Finset G) (γ : G) :
    Finset (G × G) := by
  classical
  exact (Q.product Q).filter (fun pair => pair.1 - pair.2 = γ)

/-- Generic lower-overlap form of the Fejér coefficient bound. -/
def PairCoeffLowerBound {G : Type*} [AddGroup G]
    (Q B : Finset G) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ)

/-- Absolute-error real-ratio form of the finite pair-overlap bound. -/
def PairCoeffRealBound {G : Type*} [AddGroup G]
    (Q B : Finset G) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    |1 - ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ)| ≤ M

namespace PairCoeffRealBound

variable {G : Type*} [AddGroup G]

lemma pairFilter_card_le (Q : Finset G) (γ : G) :
    (pairFiber Q γ).card ≤ Q.card := by
  classical
  let fiber := pairFiber Q γ
  have hmaps :
      Set.MapsTo (fun pair : G × G => pair.1) (↑fiber : Set (G × G)) (↑Q : Set G) := by
    intro pair hpair
    have hpair' :
        pair ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair').1).1
  have hinj :
      Set.InjOn (fun pair : G × G => pair.1) (↑fiber : Set (G × G)) := by
    intro pair hpair pair' hpair' hfirst
    have hpair_mem :
        pair ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair
    have hpair'_mem :
        pair' ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair'
    have hdiff : pair.1 - pair.2 = γ :=
      (Finset.mem_filter.mp hpair_mem).2
    have hdiff' : pair'.1 - pair'.2 = γ :=
      (Finset.mem_filter.mp hpair'_mem).2
    have hsub : pair.1 - pair.2 = pair.1 - pair'.2 := by
      simpa [hfirst] using hdiff.trans hdiff'.symm
    have hsecond : pair.2 = pair'.2 := by
      simpa [sub_eq_sub_iff_add_eq_add] using hsub
    exact Prod.ext hfirst hsecond
  simpa [fiber] using
    Finset.card_le_card_of_injOn (fun pair : G × G => pair.1)
      hmaps hinj

lemma of_lowerBound {Q B : Finset G} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : PairCoeffLowerBound Q B M) :
    PairCoeffRealBound Q B M := by
  classical
  intro γ hγ
  have hQpos_nat : 0 < Q.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hQ)
  have hQpos : 0 < (Q.card : ℝ) := by exact_mod_cast hQpos_nat
  have hratio_le_one :
      ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hQpos]
    norm_num
    exact_mod_cast pairFilter_card_le Q γ
  have hratio_ge := hM γ hγ
  rw [abs_le]
  constructor <;> linarith

end PairCoeffRealBound

end Erdos42.CompactCayley
