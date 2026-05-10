/-
Erdős Problem 42 — compact-Cayley counterexample subsequences.

Fourier extraction repeatedly passes to strictly monotone subsequences.  This
file keeps that bookkeeping out of the later compactness files.
-/

import Erdos.P42.CompactCayley.Counterexample

namespace Erdos42.CompactCayley

open Filter
open scoped Topology

/-- Pass a compact-Cayley counterexample sequence to a strictly monotone
subsequence. -/
def CayleyCounterSeq.subseq
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    CayleyCounterSeq ℓ η where
  p n := S.p (φ n)
  prime n := S.prime (φ n)
  p_gt n := by
    have hn_le_φn : n ≤ φ n := by
      induction n with
      | zero =>
          exact Nat.zero_le _
      | succ n ih =>
          have hstep : φ n < φ (n + 1) := hφ (Nat.lt_succ_self n)
          omega
    exact lt_of_le_of_lt hn_le_φn (S.p_gt (φ n))
  T n := S.T (φ n)
  T_sym n := S.T_sym (φ n)
  T_zero n := S.T_zero (φ n)
  T_density n := S.T_density (φ n)
  eps n := S.eps (φ n)
  eps_pos n := S.eps_pos (φ n)
  eps_tendsto_zero := by
    exact S.eps_tendsto_zero.comp hφ.tendsto_atTop
  T_fourier_upper n := by
    simpa using S.T_fourier_upper (φ n)
  no_clique n := S.no_clique (φ n)

@[simp] lemma CayleyCounterSeq.subseq_p
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).p n = S.p (φ n) := rfl

@[simp] lemma CayleyCounterSeq.subseq_T
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).T n = S.T (φ n) := rfl

@[simp] lemma CayleyCounterSeq.subseq_eps
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).eps n = S.eps (φ n) := rfl

/-- The epsilon bias still tends to zero after passing to a strictly monotone
subsequence. -/
lemma CayleyCounterSeq.subseq_tendsto_eps_zero
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Tendsto (fun n => S.eps (φ n)) atTop (𝓝 0) := by
  exact S.eps_tendsto_zero.comp hφ.tendsto_atTop

end Erdos42.CompactCayley
