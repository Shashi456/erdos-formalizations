/-
Erdős Problem 42 — torsion-freeness of the compact-Cayley extraction quotient.

Finite lifts land in cyclic groups of prime order tending to infinity along the
stable subsequence.  A fixed nonzero scalar cannot create persistent torsion in
those cyclic groups, hence the eventual-kernel quotient is torsion-free.
-/

import Erdos.P42.CompactCayley.QuotientLift
import Mathlib.Algebra.Group.Torsion

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Classical Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

lemma eventually_prime_gt
    (data : F.StableSubseqData labelFreq) (q : ℕ) :
    ∀ᶠ n in atTop, q < F.p (data.φ n) := by
  rw [Filter.eventually_atTop]
  refine ⟨q + 1, ?_⟩
  intro n hn
  have hq_lt_n : q < n :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self q) hn
  have hn_le_φn : n ≤ data.φ n := data.strictMono_φ.le_apply
  exact lt_trans (lt_of_lt_of_le hq_lt_n hn_le_φn)
    (F.p_gt (data.φ n))

lemma zmod_nsmul_eq_zero_iff_of_prime_not_dvd
    {p q : ℕ} [Fact p.Prime] (hnot : ¬ p ∣ q) (x : ZMod p) :
    q • x = 0 ↔ x = 0 := by
  have hunit : IsUnit (q : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnot).symm
  constructor
  · intro hx
    have hxmul : (q : ZMod p) * x = (q : ZMod p) * 0 := by
      simpa [nsmul_eq_mul] using hx
    exact hunit.mul_left_cancel hxmul
  · intro hx
    simp [hx]

lemma quotient_nsmul_eq_zero_iff_eventually_lift_nsmul_eq_zero
    (data : F.StableSubseqData labelFreq)
    (q : ℕ) {w : ExtractionFreeGroup} :
    q • (QuotientAddGroup.mk w : data.Group) = 0 ↔
      ∀ᶠ n in atTop, q • data.finiteLiftHom n w = 0 := by
  rw [← QuotientAddGroup.mk_nsmul
    ((data.seq).eventualKernel data.subseqLabelFreq) w q,
    data.quotient_eq_zero_iff_eventually_lift_eq_zero]
  simp [AddMonoidHom.map_nsmul]

lemma finiteLiftHom_eventually_eq_zero_of_eventually_nsmul_eq_zero
    (data : F.StableSubseqData labelFreq)
    {q : ℕ} (hq : q ≠ 0) {w : ExtractionFreeGroup}
    (h : ∀ᶠ n in atTop, q • data.finiteLiftHom n w = 0) :
    ∀ᶠ n in atTop, data.finiteLiftHom n w = 0 := by
  filter_upwards [h, data.eventually_prime_gt q] with n hn hgt
  haveI : Fact (F.p (data.φ n)).Prime := ⟨F.prime (data.φ n)⟩
  have hnot : ¬ F.p (data.φ n) ∣ q :=
    Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hq) hgt
  exact (zmod_nsmul_eq_zero_iff_of_prime_not_dvd hnot
    (data.finiteLiftHom n w)).mp hn

/-- The stable compact-Cayley extraction quotient is torsion-free. -/
theorem group_isAddTorsionFree
    (data : F.StableSubseqData labelFreq) :
    IsAddTorsionFree data.Group where
  nsmul_right_injective := by
    intro q hq x y hxy
    induction x using QuotientAddGroup.induction_on with
    | H w =>
      induction y using QuotientAddGroup.induction_on with
      | H v =>
        have hsub_q :
            q • (QuotientAddGroup.mk (w - v) : data.Group) = 0 := by
          rw [QuotientAddGroup.mk_sub]
          simp [nsmul_sub, hxy]
        have hlift_q :
            ∀ᶠ n in atTop, q • data.finiteLiftHom n (w - v) = 0 :=
          (data.quotient_nsmul_eq_zero_iff_eventually_lift_nsmul_eq_zero
            q).mp hsub_q
        have hlift :
            ∀ᶠ n in atTop, data.finiteLiftHom n (w - v) = 0 :=
          data.finiteLiftHom_eventually_eq_zero_of_eventually_nsmul_eq_zero
            hq hlift_q
        have hsub :
            (QuotientAddGroup.mk (w - v) : data.Group) = 0 :=
          (data.quotient_eq_zero_iff_eventually_lift_eq_zero).mpr hlift
        rw [QuotientAddGroup.mk_sub] at hsub
        exact sub_eq_zero.mp hsub

instance (data : F.StableSubseqData labelFreq) :
    IsAddTorsionFree data.Group :=
  data.group_isAddTorsionFree

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley
