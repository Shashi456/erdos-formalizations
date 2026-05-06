/-
Copyright (c) 2026

Basic complete-sequence infrastructure for Graham's theorem on complete
sequences of polynomial values.
-/

import Mathlib

namespace Erdos.P283.RSG

open Filter

/-! ## Finite subset sums -/

/-- Finite `0/1` subset sums of an integer sequence. This is Graham's `P(S)`. -/
def FS (s : ℕ → ℤ) : Set ℤ :=
  {x | ∃ I : Finset ℕ, x = ∑ i ∈ I, s i}

/-- Finite `0/1` subset sums of `s` using only indices from `A`. -/
def FSOf (s : ℕ → ℤ) (A : Finset ℕ) : Set ℤ :=
  {x | ∃ I : Finset ℕ, I ⊆ A ∧ x = ∑ i ∈ I, s i}

/-- Signed finite subset sums of an integer sequence. This is Graham's `A(S)`. -/
def SignedFS (s : ℕ → ℤ) : Set ℤ :=
  {x | ∃ I J : Finset ℕ, Disjoint I J ∧
      x = (∑ i ∈ I, s i) - (∑ j ∈ J, s j)}

/-- Signed finite subset sums using only indices from `A`. -/
def SignedFSOf (s : ℕ → ℤ) (A : Finset ℕ) : Set ℤ :=
  {x | ∃ I J : Finset ℕ, I ⊆ A ∧ J ⊆ A ∧ Disjoint I J ∧
      x = (∑ i ∈ I, s i) - (∑ j ∈ J, s j)}

/-- A sequence is complete if its finite subset sums contain all sufficiently
large integers. -/
def Complete (s : ℕ → ℤ) : Prop :=
  ∃ C : ℤ, ∀ x : ℤ, C ≤ x → x ∈ FS s

/-- A sequence is nearly complete if finite subset sums contain arbitrarily long
intervals of consecutive positive integers after a translate. -/
def NearlyComplete (s : ℕ → ℤ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ c : ℤ, ∀ j : ℕ, 1 ≤ j → j ≤ k → c + (j : ℤ) ∈ FS s

/-- Graham's Sigma-sequence condition. The tail is eventually small relative to
the finite prefix sums that precede it. -/
def SigmaSeq (s : ℕ → ℤ) : Prop :=
  ∃ k h : ℕ, 1 ≤ k ∧
    (∀ m : ℕ, 0 < s (h + m)) ∧
    ∀ m : ℕ, s (h + m) < (k : ℤ) + ∑ n ∈ Finset.range m, s (h + n)

/-- Finite subset sums of `s` contain every residue class modulo `m`. -/
def CoversResidues (s : ℕ → ℤ) (m : ℕ) : Prop :=
  ∀ r : ZMod m, ∃ x ∈ FS s, ((x : ℤ) : ZMod m) = r

/-! ## Elementary API for `FS` and `SignedFS` -/

lemma fs_empty (s : ℕ → ℤ) : (0 : ℤ) ∈ FS s := by
  refine ⟨∅, ?_⟩
  simp

lemma fs_singleton (s : ℕ → ℤ) (i : ℕ) : s i ∈ FS s := by
  refine ⟨{i}, ?_⟩
  simp

lemma fsOf_subset_fs (s : ℕ → ℤ) (A : Finset ℕ) :
    FSOf s A ⊆ FS s := by
  intro x hx
  rcases hx with ⟨I, _hIA, hI⟩
  exact ⟨I, hI⟩

lemma fsOf_empty (s : ℕ → ℤ) : (0 : ℤ) ∈ FSOf s ∅ := by
  refine ⟨∅, ?_, ?_⟩
  · simp
  · simp

lemma fsOf_singleton (s : ℕ → ℤ) (i : ℕ) :
    s i ∈ FSOf s {i} := by
  refine ⟨{i}, ?_, ?_⟩
  · simp
  · simp

lemma fsOf_sum_self (s : ℕ → ℤ) (A : Finset ℕ) :
    (∑ i ∈ A, s i) ∈ FSOf s A := by
  exact ⟨A, subset_rfl, rfl⟩

lemma fsOf_mono {s : ℕ → ℤ} {A B : Finset ℕ}
    (hAB : A ⊆ B) : FSOf s A ⊆ FSOf s B := by
  intro x hx
  rcases hx with ⟨I, hIA, hI⟩
  exact ⟨I, hIA.trans hAB, hI⟩

lemma fsOf_add_index {s : ℕ → ℤ} {A : Finset ℕ} {x : ℤ} {a : ℕ}
    (haA : a ∉ A) (hx : x ∈ FSOf s A) :
    x + s a ∈ FSOf s (insert a A) := by
  classical
  rcases hx with ⟨I, hIA, hI⟩
  have haI : a ∉ I := fun hai => haA (hIA hai)
  refine ⟨insert a I, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hIA hi)
  · rw [Finset.sum_insert haI, ← hI]
    abel

lemma fsOf_add_of_disjoint {s : ℕ → ℤ} {A B : Finset ℕ} {x y : ℤ}
    (hAB : Disjoint A B) (hx : x ∈ FSOf s A) (hy : y ∈ FSOf s B) :
    x + y ∈ FSOf s (A ∪ B) := by
  classical
  rcases hx with ⟨I, hIA, hI⟩
  rcases hy with ⟨J, hJB, hJ⟩
  have hIJ : Disjoint I J := hAB.mono hIA hJB
  refine ⟨I ∪ J, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_union] at hi ⊢
    rcases hi with hi | hi
    · exact Or.inl (hIA hi)
    · exact Or.inr (hJB hi)
  · rw [Finset.sum_union hIJ, ← hI, ← hJ]

lemma finset_subset_range_sup_succ (A : Finset ℕ) :
    A ⊆ Finset.range (A.sup id + 1) := by
  intro i hi
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup (s := A) (f := id) hi)

/-- A predicate that occurs arbitrarily far out has finite subsets of arbitrary
cardinality all of whose elements satisfy the predicate. -/
lemma exists_finset_card_eq_of_frequently_atTop {P : ℕ → Prop}
    (hP : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n) :
    ∀ k : ℕ, ∃ A : Finset ℕ, A.card = k ∧ ∀ n ∈ A, P n := by
  classical
  intro k
  induction k with
  | zero =>
      exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
      obtain ⟨A, hAcard, hAP⟩ := ih
      obtain ⟨n, hn_ge, hnP⟩ := hP (A.sup id + 1)
      have hn_not_mem : n ∉ A := by
        intro hnA
        have hn_lt : n < A.sup id + 1 :=
          Finset.mem_range.mp ((finset_subset_range_sup_succ A) hnA)
        exact (not_lt_of_ge hn_ge) hn_lt
      refine ⟨insert n A, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hn_not_mem, hAcard]
      · intro a ha
        rw [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact hnP
        · exact hAP a ha

lemma disjoint_range_of_forall_le {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, N ≤ a) :
    Disjoint (Finset.range N) A := by
  rw [Finset.disjoint_left]
  intro a ha hA_mem
  have hlt : a < N := Finset.mem_range.mp ha
  have hle : N ≤ a := hA a hA_mem
  omega

lemma fs_add_of_disjoint_witness {s : ℕ → ℤ} (I J : Finset ℕ)
    (hdisj : Disjoint I J) :
    (∑ i ∈ I, s i) + (∑ j ∈ J, s j) ∈ FS s := by
  classical
  refine ⟨I ∪ J, ?_⟩
  rw [Finset.sum_union hdisj]

lemma signedFS_zero (s : ℕ → ℤ) : (0 : ℤ) ∈ SignedFS s := by
  refine ⟨∅, ∅, ?_, ?_⟩
  · simp
  · simp

lemma signedFSOf_subset_signedFS (s : ℕ → ℤ) (A : Finset ℕ) :
    SignedFSOf s A ⊆ SignedFS s := by
  intro x hx
  rcases hx with ⟨I, J, _hIA, _hJA, hIJ, hsum⟩
  exact ⟨I, J, hIJ, hsum⟩

lemma signedFSOf_empty (s : ℕ → ℤ) : (0 : ℤ) ∈ SignedFSOf s ∅ := by
  refine ⟨∅, ∅, ?_, ?_, ?_, ?_⟩ <;> simp

lemma fs_subset_signedFS (s : ℕ → ℤ) : FS s ⊆ SignedFS s := by
  intro x hx
  rcases hx with ⟨I, rfl⟩
  refine ⟨I, ∅, ?_, ?_⟩
  · simp
  · simp

lemma signedFS_neg {s : ℕ → ℤ} {x : ℤ} (hx : x ∈ SignedFS s) :
    -x ∈ SignedFS s := by
  rcases hx with ⟨I, J, hIJ, rfl⟩
  refine ⟨J, I, hIJ.symm, ?_⟩
  abel

lemma signedFS_sub_of_disjoint_witness {s : ℕ → ℤ} (I J : Finset ℕ)
    (hdisj : Disjoint I J) :
    (∑ i ∈ I, s i) - (∑ j ∈ J, s j) ∈ SignedFS s := by
  exact ⟨I, J, hdisj, rfl⟩

/-- A list of signed `±1` terms with no repeated indices gives a bounded
signed finite subset sum. -/
lemma signedFSOf_list_sum {s : ℕ → ℤ} :
    ∀ {l : List (ℤ × ℕ)},
      (∀ p ∈ l, p.1 = 1 ∨ p.1 = -1) →
      ((l.map fun p : ℤ × ℕ => p.2).Nodup) →
      (l.map fun p : ℤ × ℕ => p.1 * s p.2).sum ∈
        SignedFSOf s ((l.map fun p : ℤ × ℕ => p.2).toFinset)
  | [], _hsgn, _hnodup => by
      simpa using signedFSOf_empty s
  | p :: l, hsgn, hnodup => by
      have htail_sign : ∀ q ∈ l, q.1 = 1 ∨ q.1 = -1 := by
        intro q hq
        exact hsgn q (by simp [hq])
      have hnodup' :
          (p.2 :: (l.map fun q : ℤ × ℕ => q.2)).Nodup := by
        simpa using hnodup
      have hp_not_tail : p.2 ∉ (l.map fun q : ℤ × ℕ => q.2) := by
        exact (List.nodup_cons.mp hnodup').1
      have htail_nodup :
          ((l.map fun q : ℤ × ℕ => q.2).Nodup) :=
        (List.nodup_cons.mp hnodup').2
      rcases signedFSOf_list_sum htail_sign htail_nodup with
        ⟨I, J, hIA, hJA, hIJ, hsum⟩
      have hp_not_I : p.2 ∉ I := by
        intro hpI
        have : p.2 ∈ (l.map fun q : ℤ × ℕ => q.2) := by
          simpa using hIA hpI
        exact hp_not_tail this
      have hp_not_J : p.2 ∉ J := by
        intro hpJ
        have : p.2 ∈ (l.map fun q : ℤ × ℕ => q.2) := by
          simpa using hJA hpJ
        exact hp_not_tail this
      have hI_sub_cons :
          I ⊆ ((p :: l).map fun q : ℤ × ℕ => q.2).toFinset := by
        intro x hx
        simp [hIA hx]
      have hJ_sub_cons :
          J ⊆ ((p :: l).map fun q : ℤ × ℕ => q.2).toFinset := by
        intro x hx
        simp [hJA hx]
      rcases hsgn p (by simp) with hp_one | hp_neg
      · refine ⟨insert p.2 I, J, ?_, hJ_sub_cons, ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · simp
          · exact hI_sub_cons hx
        · rw [Finset.disjoint_left]
          intro x hxI hxJ
          rw [Finset.mem_insert] at hxI
          rcases hxI with rfl | hxI
          · exact hp_not_J hxJ
          · exact (Finset.disjoint_left.mp hIJ) hxI hxJ
        · rw [List.map_cons, List.sum_cons, hp_one, one_mul, hsum]
          rw [Finset.sum_insert hp_not_I]
          ring
      · refine ⟨I, insert p.2 J, hI_sub_cons, ?_, ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · simp
          · exact hJ_sub_cons hx
        · rw [Finset.disjoint_left]
          intro x hxI hxJ
          rw [Finset.mem_insert] at hxJ
          rcases hxJ with rfl | hxJ
          · exact hp_not_I hxI
          · exact (Finset.disjoint_left.mp hIJ) hxI hxJ
        · rw [List.map_cons, List.sum_cons, hp_neg, hsum]
          rw [Finset.sum_insert hp_not_J]
          ring

lemma fs_congr {s t : ℕ → ℤ} (h : ∀ n, s n = t n) : FS s = FS t := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨I, hI⟩
    refine ⟨I, ?_⟩
    rw [hI]
    exact Finset.sum_congr rfl (fun n _ => h n)
  · intro hx
    rcases hx with ⟨I, hI⟩
    refine ⟨I, ?_⟩
    rw [hI]
    exact Finset.sum_congr rfl (fun n _ => (h n).symm)

lemma signedFS_congr {s t : ℕ → ℤ} (h : ∀ n, s n = t n) :
    SignedFS s = SignedFS t := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨I, J, hIJ, hsum⟩
    refine ⟨I, J, hIJ, ?_⟩
    rw [hsum]
    congr 1 <;> exact Finset.sum_congr rfl (fun n _ => h n)
  · intro hx
    rcases hx with ⟨I, J, hIJ, hsum⟩
    refine ⟨I, J, hIJ, ?_⟩
    rw [hsum]
    congr 1 <;> exact Finset.sum_congr rfl (fun n _ => (h n).symm)

/-- Map signed subset-sum witnesses through an injective index map. -/
lemma signedFS_map_of_injective {s t : ℕ → ℤ} {φ : ℕ → ℕ}
    (hφ : Function.Injective φ)
    (hval : ∀ i, t i = s (φ i)) :
    SignedFS t ⊆ SignedFS s := by
  classical
  intro x hx
  rcases hx with ⟨I, J, hIJ, hsum⟩
  refine ⟨I.image φ, J.image φ, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨j, hj, hij⟩
    have hji : j = i := hφ hij
    subst hji
    exact (Finset.disjoint_left.mp hIJ) hi hj
  · rw [hsum]
    rw [Finset.sum_image, Finset.sum_image]
    · apply congrArg₂ Sub.sub
      · exact Finset.sum_congr rfl (fun i _ => hval i)
      · exact Finset.sum_congr rfl (fun j _ => hval j)
    · intro a _ b _ hab
      exact hφ hab
    · intro a _ b _ hab
      exact hφ hab

/-- Completeness is invariant under pointwise equality of sequences. -/
lemma Complete.congr {s t : ℕ → ℤ} (h : ∀ n, s n = t n)
    (hs : Complete s) : Complete t := by
  rcases hs with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x hx
  rw [← fs_congr h]
  exact hC x hx

/-- Near-completeness is invariant under pointwise equality of sequences. -/
lemma NearlyComplete.congr {s t : ℕ → ℤ} (h : ∀ n, s n = t n)
    (hs : NearlyComplete s) : NearlyComplete t := by
  intro k hk
  rcases hs k hk with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro j hj0 hjk
  rw [← fs_congr h]
  exact hc j hj0 hjk

/-- The Sigma-sequence condition is invariant under pointwise equality. -/
lemma SigmaSeq.congr {s t : ℕ → ℤ} (h : ∀ n, s n = t n)
    (hs : SigmaSeq s) : SigmaSeq t := by
  rcases hs with ⟨k, h0, hk, hpos, hsigma⟩
  refine ⟨k, h0, hk, ?_, ?_⟩
  · intro m
    simpa [← h] using hpos m
  intro m
  calc
    t (h0 + m) = s (h0 + m) := (h _).symm
    _ < (k : ℤ) + ∑ n ∈ Finset.range m, s (h0 + n) := hsigma m
    _ = (k : ℤ) + ∑ n ∈ Finset.range m, t (h0 + n) := by
      congr 1
      exact Finset.sum_congr rfl (fun n _ => h _)

/-- Shift the index set of an `FS` witness by a function that preserves the
sequence values on that finite set. -/
lemma fs_map_of_eq_on {s t : ℕ → ℤ} {φ : ℕ → ℕ} {I : Finset ℕ}
    (hφ : Set.InjOn φ (↑I : Set ℕ))
    (hval : ∀ i ∈ I, t i = s (φ i)) :
    (∑ i ∈ I, t i) ∈ FS s := by
  classical
  refine ⟨I.image φ, ?_⟩
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl hval
  · intro a ha b hb hab
    exact hφ ha hb hab

/-- A sequence whose nonzero terms inject into another sequence has finite
subset sums contained in the latter sequence's finite subset sums. -/
lemma fs_subset_of_eq_zero_or_subsequence {s t : ℕ → ℤ} (φ : ℕ → ℕ)
    (hφ :
      ∀ ⦃i j : ℕ⦄, t i ≠ 0 → t j ≠ 0 → φ i = φ j → i = j)
    (hval : ∀ i : ℕ, t i ≠ 0 → t i = s (φ i)) :
    FS t ⊆ FS s := by
  classical
  intro x hx
  rcases hx with ⟨I, hI⟩
  let K : Finset ℕ := I.filter fun i => t i ≠ 0
  refine ⟨K.image φ, ?_⟩
  rw [hI, Finset.sum_image]
  · calc
      ∑ i ∈ I, t i = ∑ i ∈ I with t i ≠ 0, t i := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl
          (fun i _hi => by
            by_cases hi0 : t i ≠ 0
            · simp [hi0]
            · simp [not_not.mp hi0])
      _ = ∑ i ∈ K, t i := by
        rfl
      _ = ∑ i ∈ K, s (φ i) := by
        exact Finset.sum_congr rfl
          (fun i hi => hval i (Finset.mem_filter.mp hi).2)
  · intro a ha b hb hab
    exact hφ (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab

/-- Completeness transfers along inclusion of finite subset-sum sets. -/
lemma Complete.of_fs_subset {S T : ℕ → ℤ}
    (hsub : FS S ⊆ FS T)
    (hcomp : Complete S) :
    Complete T := by
  rcases hcomp with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x hx
  exact hsub (hC x hx)

/-- Completeness transfers from an injective subsequence to the ambient
sequence. -/
lemma Complete.of_injective_subsequence
    {s t : ℕ → ℤ}
    (φ : ℕ → ℕ)
    (hφ : Function.Injective φ)
    (ht : ∀ n, t n = s (φ n))
    (hcomp : Complete t) :
    Complete s := by
  rcases hcomp with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x hx
  rcases hC x hx with ⟨I, hI⟩
  rw [hI]
  exact fs_map_of_eq_on (fun _ _ _ _ h => hφ h) (fun i _ => ht i)

/-! ## Simple sequence combinators -/

/-- Interleave two sequences, taking `S 0, T 0, S 1, T 1, ...`. -/
def interleave (S T : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then S (n / 2) else T (n / 2)

@[simp] lemma interleave_even (S T : ℕ → ℤ) (n : ℕ) :
    interleave S T (2 * n) = S n := by
  have hmod : (2 * n) % 2 = 0 := by
    exact Nat.mul_mod_right 2 n
  have hdiv : (2 * n) / 2 = n := by
    exact Nat.mul_div_right n (by decide : 0 < 2)
  simp [interleave, hmod, hdiv]

@[simp] lemma interleave_odd (S T : ℕ → ℤ) (n : ℕ) :
    interleave S T (2 * n + 1) = T n := by
  have hmod : (2 * n + 1) % 2 ≠ 0 := by
    have h : (2 * n + 1) % 2 = 1 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [h]
    norm_num
  have hdiv : (2 * n + 1) / 2 = n := by
    have h := Nat.mul_add_div (m := 2) (by decide : 2 > 0) n 1
    simpa using h
  simp [interleave, hdiv]

/-- Prefix a finite list in front of a sequence. This is useful for Graham's
finite residue prefix followed by a tail. -/
def prefixSeq (pref : List ℤ) (tail : ℕ → ℤ) : ℕ → ℤ :=
  fun n =>
    if h : n < pref.length then
      pref.get ⟨n, h⟩
    else
      tail (n - pref.length)

/-- The tail of a sequence starting at offset `N`. -/
def tail (S : ℕ → ℤ) (N : ℕ) : ℕ → ℤ :=
  fun n => S (N + n)

@[simp] lemma tail_tail (S : ℕ → ℤ) (N M : ℕ) :
    tail (tail S N) M = tail S (N + M) := by
  funext n
  simp [tail, Nat.add_assoc]

/-- The finite prefix of a sequence, padded by zeros after `N`. -/
def finitePrefixSeq (S : ℕ → ℤ) (N : ℕ) : ℕ → ℤ :=
  fun n => if n < N then S n else 0

/-- The sequence obtained by taking the odd/even tails after `2*r` and a
zero-padded prefix before `2*r`. This is Graham's final disjoint split of the
original sequence. -/
def oddEvenPrefixAssembly (S : ℕ → ℤ) (r : ℕ) : ℕ → ℤ :=
  interleave
    (fun n : ℕ => S (2 * r + 2 * n))
    (interleave
      (fun n : ℕ => S (2 * r + 2 * n + 1))
      (finitePrefixSeq S (2 * r)))

/-- The intended ambient-sequence index for a term of
`oddEvenPrefixAssembly`. Terms in the zero-padded part with index beyond the
prefix are harmless; they will be filtered out by nonzero-term transfer. -/
def oddEvenPrefixAssemblyIndex (r n : ℕ) : ℕ :=
  if n % 2 = 0 then
    2 * r + 2 * (n / 2)
  else
    let q := n / 2
    if q % 2 = 0 then
      2 * r + 2 * (q / 2) + 1
    else
      q / 2

lemma nat_eq_two_mul_div_of_mod_two_eq_zero {n : ℕ} (h : n % 2 = 0) :
    n = 2 * (n / 2) := by
  have hdiv := Nat.mod_add_div n 2
  omega

lemma nat_eq_two_mul_div_add_one_of_mod_two_ne_zero {n : ℕ} (h : n % 2 ≠ 0) :
    n = 2 * (n / 2) + 1 := by
  have hdiv := Nat.mod_add_div n 2
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide : 0 < 2)
  omega

lemma oddEvenPrefixAssembly_value_eq_index_of_nonzero
    (S : ℕ → ℤ) (r n : ℕ)
    (hnz : oddEvenPrefixAssembly S r n ≠ 0) :
    oddEvenPrefixAssembly S r n = S (oddEvenPrefixAssemblyIndex r n) := by
  by_cases hn : n % 2 = 0
  · simp [oddEvenPrefixAssembly, oddEvenPrefixAssemblyIndex, interleave, hn]
  · let q : ℕ := n / 2
    by_cases hq : q % 2 = 0
    · simp [oddEvenPrefixAssembly, oddEvenPrefixAssemblyIndex, interleave, hn, q, hq]
    · by_cases hprefix : q / 2 < 2 * r
      · simp [oddEvenPrefixAssembly, oddEvenPrefixAssemblyIndex, interleave, hn, q, hq,
          finitePrefixSeq, hprefix]
      · exfalso
        exact hnz
          (by
            simp [oddEvenPrefixAssembly, interleave, hn, q, hq, finitePrefixSeq, hprefix])

lemma oddEvenPrefixAssemblyIndex_inj_of_nonzero
    (S : ℕ → ℤ) (r : ℕ) {i j : ℕ}
    (hi0 : oddEvenPrefixAssembly S r i ≠ 0)
    (hj0 : oddEvenPrefixAssembly S r j ≠ 0)
    (hidx : oddEvenPrefixAssemblyIndex r i = oddEvenPrefixAssemblyIndex r j) :
    i = j := by
  by_cases hi : i % 2 = 0
  · by_cases hj : j % 2 = 0
    · have hii := nat_eq_two_mul_div_of_mod_two_eq_zero hi
      have hjj := nat_eq_two_mul_div_of_mod_two_eq_zero hj
      simp [oddEvenPrefixAssemblyIndex, hi, hj] at hidx
      omega
    · let qj : ℕ := j / 2
      by_cases hqj : qj % 2 = 0
      · simp [oddEvenPrefixAssemblyIndex, hi, hj, qj, hqj] at hidx
        omega
      · have hpj : qj / 2 < 2 * r := by
          by_contra hpj
          exact hj0
            (by simp [oddEvenPrefixAssembly, interleave, hj, qj, hqj, finitePrefixSeq, hpj])
        simp [oddEvenPrefixAssemblyIndex, hi, hj, qj, hqj] at hidx
        omega
  · let qi : ℕ := i / 2
    by_cases hqi : qi % 2 = 0
    · by_cases hj : j % 2 = 0
      · simp [oddEvenPrefixAssemblyIndex, hi, qi, hqi, hj] at hidx
        omega
      · let qj : ℕ := j / 2
        by_cases hqj : qj % 2 = 0
        · have hii := nat_eq_two_mul_div_add_one_of_mod_two_ne_zero hi
          have hjj := nat_eq_two_mul_div_add_one_of_mod_two_ne_zero hj
          simp [oddEvenPrefixAssemblyIndex, hi, qi, hqi, hj, qj, hqj] at hidx
          omega
        · have hpj : qj / 2 < 2 * r := by
            by_contra hpj
            exact hj0
              (by simp [oddEvenPrefixAssembly, interleave, hj, qj, hqj, finitePrefixSeq, hpj])
          simp [oddEvenPrefixAssemblyIndex, hi, qi, hqi, hj, qj, hqj] at hidx
          omega
    · have hpi : qi / 2 < 2 * r := by
        by_contra hpi
        exact hi0
          (by simp [oddEvenPrefixAssembly, interleave, hi, qi, hqi, finitePrefixSeq, hpi])
      by_cases hj : j % 2 = 0
      · simp [oddEvenPrefixAssemblyIndex, hi, qi, hqi, hj] at hidx
        omega
      · let qj : ℕ := j / 2
        by_cases hqj : qj % 2 = 0
        · simp [oddEvenPrefixAssemblyIndex, hi, qi, hqi, hj, qj, hqj] at hidx
          omega
        · have hpj : qj / 2 < 2 * r := by
            by_contra hpj
            exact hj0
              (by simp [oddEvenPrefixAssembly, interleave, hj, qj, hqj, finitePrefixSeq, hpj])
          have hii := nat_eq_two_mul_div_add_one_of_mod_two_ne_zero hi
          have hjj := nat_eq_two_mul_div_add_one_of_mod_two_ne_zero hj
          simp [oddEvenPrefixAssemblyIndex, hi, qi, hqi, hj, qj, hqj] at hidx
          omega

lemma fs_oddEvenPrefixAssembly_subset (S : ℕ → ℤ) (r : ℕ) :
    FS (oddEvenPrefixAssembly S r) ⊆ FS S :=
  fs_subset_of_eq_zero_or_subsequence (s := S) (t := oddEvenPrefixAssembly S r)
    (oddEvenPrefixAssemblyIndex r)
    (fun {i j} hi0 hj0 hidx =>
      oddEvenPrefixAssemblyIndex_inj_of_nonzero S r (i := i) (j := j) hi0 hj0 hidx)
    (oddEvenPrefixAssembly_value_eq_index_of_nonzero S r)

lemma Complete.of_oddEvenPrefixAssembly {S : ℕ → ℤ} (r : ℕ)
    (hcomp : Complete (oddEvenPrefixAssembly S r)) :
    Complete S :=
  Complete.of_fs_subset (fs_oddEvenPrefixAssembly_subset S r) hcomp

lemma fs_tail_subset (S : ℕ → ℤ) (N : ℕ) :
    FS (tail S N) ⊆ FS S := by
  intro x hx
  rcases hx with ⟨I, hI⟩
  rw [hI]
  exact fs_map_of_eq_on (φ := fun n => N + n)
    (fun _ _ _ _ h => Nat.add_left_cancel h) (fun _ _ => rfl)

lemma signedFS_tail_subset (S : ℕ → ℤ) (N : ℕ) :
    SignedFS (tail S N) ⊆ SignedFS S :=
  signedFS_map_of_injective (s := S) (t := tail S N)
    (φ := fun n => N + n) (fun _ _ h => Nat.add_left_cancel h) (fun _ => rfl)

/-- A later tail has fewer available terms, so its signed finite sums are also
signed finite sums of any earlier tail. -/
lemma signedFS_tail_mono {S : ℕ → ℤ} {N M : ℕ} (hNM : N ≤ M) :
    SignedFS (tail S M) ⊆ SignedFS (tail S N) := by
  exact signedFS_map_of_injective (s := tail S N) (t := tail S M)
    (φ := fun i => M - N + i)
    (fun _ _ h => Nat.add_left_cancel h)
    (fun i => by
      dsimp [tail]
      congr 1
      omega)

/-- A signed subset-sum witness in a tail can be reindexed as a witness for the
original sequence whose support lies at or beyond the tail offset. -/
lemma signedFS_tail_witness {S : ℕ → ℤ} {N : ℕ} {x : ℤ}
    (hx : x ∈ SignedFS (tail S N)) :
    ∃ I J : Finset ℕ, Disjoint I J ∧
      (∀ i ∈ I, N ≤ i) ∧ (∀ j ∈ J, N ≤ j) ∧
      x = (∑ i ∈ I, S i) - (∑ j ∈ J, S j) := by
  classical
  rcases hx with ⟨I, J, hIJ, hsum⟩
  refine ⟨I.image (fun n => N + n), J.image (fun n => N + n), ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨j, hj, hij⟩
    have hji : j = i := Nat.add_left_cancel hij
    subst hji
    exact (Finset.disjoint_left.mp hIJ) hi hj
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨a, _ha, rfl⟩
    omega
  · intro j hj
    rcases Finset.mem_image.mp hj with ⟨a, _ha, rfl⟩
    omega
  · rw [hsum]
    rw [Finset.sum_image, Finset.sum_image]
    · rfl
    · intro a _ b _ hab
      exact Nat.add_left_cancel hab
    · intro a _ b _ hab
      exact Nat.add_left_cancel hab

/-- Bounded inductive form of Graham's arithmetic-progression construction from
signed tail differences. It produces progressions `c, c + m, ..., c + k*m`
using only a finite prefix of `S`, while allowing the caller to request that the
construction starts after an arbitrary lower bound `N0`. -/
lemma arithmetic_progressions_of_signed_tail_difference_aux {S : ℕ → ℤ} {m : ℤ}
    (htail : ∀ N : ℕ, m ∈ SignedFS (tail S N)) :
    ∀ k N0 : ℕ, ∃ B : ℕ, ∃ c : ℤ, N0 ≤ B ∧
      ∀ j : ℕ, j ≤ k → c + (j : ℤ) * m ∈ FSOf S (Finset.range B)
  | 0, N0 => by
      refine ⟨N0, 0, le_rfl, ?_⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      simpa using
        (fsOf_mono (s := S) (A := ∅) (B := Finset.range N0)
          (by intro x hx; cases hx) (fsOf_empty S))
  | k + 1, N0 => by
      rcases arithmetic_progressions_of_signed_tail_difference_aux htail k N0 with
        ⟨B, c, hN0B, hAP⟩
      rcases signedFS_tail_witness (htail B) with
        ⟨P, Q, hPQ, hP_ge, hQ_ge, hm_eq⟩
      let B' : ℕ := max B (max (P.sup id + 1) (Q.sup id + 1))
      have hBB' : B ≤ B' := by dsimp [B']; omega
      have hrange_sub : Finset.range B ⊆ Finset.range B' := by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      have hP_sub : P ⊆ Finset.range B' := by
        intro x hx
        rw [Finset.mem_range]
        have hxle : x ≤ P.sup id := Finset.le_sup (s := P) (f := id) hx
        dsimp [B']
        omega
      have hQ_sub : Q ⊆ Finset.range B' := by
        intro x hx
        rw [Finset.mem_range]
        have hxle : x ≤ Q.sup id := Finset.le_sup (s := Q) (f := id) hx
        dsimp [B']
        omega
      have hdisjP : Disjoint (Finset.range B) P :=
        disjoint_range_of_forall_le hP_ge
      have hdisjQ : Disjoint (Finset.range B) Q :=
        disjoint_range_of_forall_le hQ_ge
      refine ⟨B', c + ∑ q ∈ Q, S q, ?_, ?_⟩
      · omega
      intro j hj
      by_cases hjk : j ≤ k
      · have hold : c + (j : ℤ) * m ∈ FSOf S (Finset.range B) := hAP j hjk
        have hneg : (∑ q ∈ Q, S q) ∈ FSOf S Q := fsOf_sum_self S Q
        have hsum :
            (c + (j : ℤ) * m) + (∑ q ∈ Q, S q) ∈
              FSOf S (Finset.range B ∪ Q) :=
          fsOf_add_of_disjoint hdisjQ hold hneg
        have hmono : Finset.range B ∪ Q ⊆ Finset.range B' := by
          intro x hx
          rw [Finset.mem_union] at hx
          rcases hx with hx | hx
          · exact hrange_sub hx
          · exact hQ_sub hx
        have htarget :
            c + (∑ q ∈ Q, S q) + (j : ℤ) * m =
              (c + (j : ℤ) * m) + (∑ q ∈ Q, S q) := by ring
        rw [htarget]
        exact fsOf_mono hmono hsum
      · have hj_eq : j = k + 1 := by omega
        subst hj_eq
        have hold : c + (k : ℤ) * m ∈ FSOf S (Finset.range B) := hAP k le_rfl
        have hpos : (∑ p ∈ P, S p) ∈ FSOf S P := fsOf_sum_self S P
        have hsum :
            (c + (k : ℤ) * m) + (∑ p ∈ P, S p) ∈
              FSOf S (Finset.range B ∪ P) :=
          fsOf_add_of_disjoint hdisjP hold hpos
        have hmono : Finset.range B ∪ P ⊆ Finset.range B' := by
          intro x hx
          rw [Finset.mem_union] at hx
          rcases hx with hx | hx
          · exact hrange_sub hx
          · exact hP_sub hx
        have htarget :
            c + (∑ q ∈ Q, S q) + ((k + 1 : ℕ) : ℤ) * m =
              (c + (k : ℕ) * m) + (∑ p ∈ P, S p) := by
          have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by norm_num
          rw [hm_eq, hcast]
          ring
        rw [htarget]
        exact fsOf_mono hmono hsum

lemma arbitrary_APs_of_signed_tail_difference {S : ℕ → ℤ} {m : ℤ}
    (htail : ∀ N : ℕ, m ∈ SignedFS (tail S N)) :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c : ℤ, ∀ j : ℕ, 1 ≤ j → j ≤ k →
        c + (j : ℤ) * m ∈ FS S := by
  intro k hk
  rcases arithmetic_progressions_of_signed_tail_difference_aux htail k 0 with
    ⟨B, c, _hB, hAP⟩
  refine ⟨c, ?_⟩
  intro j _hj1 hjk
  exact fsOf_subset_fs S (Finset.range B) (hAP j hjk)

/-- Completeness of a tail implies completeness of the original sequence. -/
lemma Complete.of_tail {S : ℕ → ℤ} (N : ℕ)
    (hcomp : Complete (tail S N)) :
    Complete S :=
  Complete.of_injective_subsequence (s := S) (t := tail S N)
    (fun n => N + n) (fun _ _ h => Nat.add_left_cancel h) (fun _ => rfl) hcomp

/-! ## Residue-cover API -/

lemma exists_eq_add_mul_of_zmod_eq {m : ℕ} {x y : ℤ}
    (h : (x : ZMod m) = (y : ZMod m)) :
    ∃ q : ℤ, x = y + (m : ℤ) * q := by
  have hdvd : (m : ℤ) ∣ y - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x y m).mp h
  rcases hdvd with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  have hmul : (m : ℤ) * -q = -((m : ℤ) * q) := by ring
  rw [hmul, ← hq]
  ring

lemma CoversResidues.of_fs_subset {S T : ℕ → ℤ} {m : ℕ}
    (hsub : FS S ⊆ FS T)
    (hcov : CoversResidues S m) :
    CoversResidues T m := by
  intro r
  rcases hcov r with ⟨x, hx, hxmod⟩
  exact ⟨x, hsub hx, hxmod⟩

lemma CoversResidues.of_tail {S : ℕ → ℤ} {m : ℕ} (N : ℕ)
    (hcov : CoversResidues (tail S N) m) :
    CoversResidues S m :=
  CoversResidues.of_fs_subset (fs_tail_subset S N) hcov

lemma coversResidues_one (S : ℕ → ℤ) : CoversResidues S 1 := by
  intro r
  refine ⟨0, fs_empty S, ?_⟩
  exact Subsingleton.elim _ _

lemma zmod_addSubgroup_eq_top_of_one_mem {m : ℕ} [NeZero m]
    {H : AddSubgroup (ZMod m)}
    (h1 : (1 : ZMod m) ∈ H) :
    H = ⊤ := by
  apply eq_top_iff.mpr
  intro x _hx
  have hxval : x.val • (1 : ZMod m) ∈ H := H.nsmul_mem h1 x.val
  simpa [ZMod.natCast_zmod_val] using hxval

lemma sum_zsmul_mem_closure_range {w m : ℕ}
    (ρ : Fin w → ZMod m) (a : Fin w → ℤ) :
    (∑ i, a i • ρ i) ∈ AddSubgroup.closure (Set.range ρ) := by
  apply AddSubgroup.sum_mem
  intro i _hi
  apply AddSubgroup.zsmul_mem
  exact AddSubgroup.subset_closure ⟨i, rfl⟩

lemma zmod_closure_range_eq_top_of_sum_zsmul_eq_one {w m : ℕ} [NeZero m]
    (ρ : Fin w → ZMod m) (a : Fin w → ℤ)
    (ha : ∑ i, a i • ρ i = (1 : ZMod m)) :
    AddSubgroup.closure (Set.range ρ) = ⊤ :=
  zmod_addSubgroup_eq_top_of_one_mem (by
    rw [← ha]
    exact sum_zsmul_mem_closure_range ρ a)

/-! ### Finite Bezout helpers for residue generation -/

/-- The gcd of a finite family of integers indexed by `Fin n`. This recursive
form is convenient because `Int.gcd_dvd_iff` directly gives Bezout
coefficients at each step. -/
def intGcdFin : (n : ℕ) → (Fin n → ℤ) → ℕ
  | 0, _ => 0
  | n + 1, v =>
      Int.gcd (v (Fin.last n)) (intGcdFin n (fun i : Fin n => v i.castSucc))

lemma intGcdFin_linear_combination :
    ∀ n : ℕ, ∀ v : Fin n → ℤ,
      ∃ a : Fin n → ℤ, (intGcdFin n v : ℤ) = ∑ i, a i * v i := by
  intro n
  induction n with
  | zero =>
      intro v
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      simp [intGcdFin]
  | succ n ih =>
      intro v
      let tail : Fin n → ℤ := fun i => v i.castSucc
      obtain ⟨b, hb⟩ := ih tail
      let gTail : ℕ := intGcdFin n tail
      have hgcd_dvd :
          Int.gcd (v (Fin.last n)) (gTail : ℤ) ∣
            Int.gcd (v (Fin.last n)) (gTail : ℤ) :=
        dvd_refl _
      obtain ⟨x, y, hxy⟩ :=
        (Int.gcd_dvd_iff
          (a := v (Fin.last n)) (b := (gTail : ℤ))
          (n := Int.gcd (v (Fin.last n)) (gTail : ℤ))).mp hgcd_dvd
      let a : Fin (n + 1) → ℤ := Fin.lastCases x (fun i : Fin n => y * b i)
      refine ⟨a, ?_⟩
      have hsum :
          (∑ i : Fin (n + 1), a i * v i) =
            (∑ i : Fin n, (y * b i) * v i.castSucc) + x * v (Fin.last n) := by
        rw [Fin.sum_univ_castSucc]
        simp [a]
      have htail_sum :
          (∑ i : Fin n, (y * b i) * v i.castSucc) =
            (intGcdFin n tail : ℤ) * y := by
        rw [hb]
        rw [mul_comm (∑ i : Fin n, b i * tail i) y]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [tail]
        ring
      calc
        (intGcdFin (n + 1) v : ℤ)
            = v (Fin.last n) * x + (gTail : ℤ) * y := by
                simpa [intGcdFin, gTail, tail] using hxy
        _ = ∑ i : Fin (n + 1), a i * v i := by
              rw [hsum, htail_sum]
              simp [gTail, tail]
              ring

lemma intGcdFin_dvd_entry :
    ∀ n : ℕ, ∀ v : Fin n → ℤ, ∀ i : Fin n,
      (intGcdFin n v : ℤ) ∣ v i := by
  intro n
  induction n with
  | zero =>
      intro v i
      exact Fin.elim0 i
  | succ n ih =>
      intro v i
      let tail : Fin n → ℤ := fun j => v j.castSucc
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have hwhole_tail :
            (intGcdFin (n + 1) v : ℤ) ∣ (intGcdFin n tail : ℤ) := by
          simpa [intGcdFin, tail] using
            Int.gcd_dvd_right (v (Fin.last n)) (intGcdFin n tail : ℤ)
        exact dvd_trans hwhole_tail (ih tail j)
      · simpa [intGcdFin, tail] using
          Int.gcd_dvd_left (v (Fin.last n)) (intGcdFin n tail : ℤ)

lemma intGcdFin_coprime_of_primeFactors_covered {m w : ℕ}
    (v : Fin w → ℤ)
    (hcover : ∀ k : ℕ, k.Prime → k ∣ m →
      ∃ i : Fin w, ¬ ((k : ℤ) ∣ v i)) :
    Nat.Coprime m (intGcdFin w v) := by
  refine Nat.coprime_of_dvd ?_
  intro k hkprime hkm hkg
  obtain ⟨i, hi⟩ := hcover k hkprime hkm
  have hkgZ : ((k : ℤ) ∣ (intGcdFin w v : ℤ)) := by
    exact_mod_cast hkg
  exact hi (dvd_trans hkgZ (intGcdFin_dvd_entry w v i))

lemma exists_zmod_sum_zsmul_eq_one_of_intGcdFin_coprime {w m : ℕ}
    (v : Fin w → ℤ)
    (hcop : Nat.Coprime m (intGcdFin w v)) :
    ∃ a : Fin w → ℤ,
      ∑ i, a i • (((v i : ℤ) : ZMod m)) = (1 : ZMod m) := by
  obtain ⟨b, hb⟩ := intGcdFin_linear_combination w v
  let c : ℤ := Nat.gcdB m (intGcdFin w v)
  refine ⟨fun i => c * b i, ?_⟩
  have hbez :
      (((intGcdFin w v : ℤ) * c : ℤ) : ZMod m) = 1 := by
    have hbezZ :
        (1 : ℤ) =
          (m : ℤ) * Nat.gcdA m (intGcdFin w v) +
            (intGcdFin w v : ℤ) * Nat.gcdB m (intGcdFin w v) := by
      have h := Nat.gcd_eq_gcd_ab m (intGcdFin w v)
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at h
      simpa using h
    have hcast := congrArg (fun z : ℤ => (z : ZMod m)) hbezZ
    simpa [c] using hcast.symm
  calc
    ∑ i, (c * b i) • (((v i : ℤ) : ZMod m))
        = (((∑ i, (c * b i) * v i : ℤ) : ℤ) : ZMod m) := by
            simp [zsmul_eq_mul]
    _ = (((intGcdFin w v : ℤ) * c : ℤ) : ZMod m) := by
          congr 1
          rw [hb]
          rw [mul_comm (∑ i : Fin w, b i * v i) c]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = 1 := hbez

/-- If finitely many residues `ρ : Fin w → ZMod g` generate `ZMod g` as an
additive group, then duplicating each residue `g - 1` times lets every residue
be represented as a subset sum. -/
theorem duplicated_generators_subset_sum_all_residues
    {w g : ℕ} (hg : 1 ≤ g) (ρ : Fin w → ZMod g)
    (hgen : AddSubgroup.closure (Set.range ρ) = ⊤) :
    ∀ r : ZMod g,
      ∃ T : Finset (Fin w × Fin (g - 1)),
        r = ∑ t ∈ T, ρ t.1 := by
  intro r
  haveI : NeZero g := ⟨by omega⟩
  have hr : r ∈ AddSubgroup.closure (Set.range ρ) := by
    rw [hgen]
    trivial
  obtain ⟨a, ha⟩ := AddSubgroup.exists_of_mem_closure_range ρ r hr
  have hgZ : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hg
  set k : Fin w → ℕ := fun i => ((a i) % (g : ℤ)).toNat with hk_def
  have hk_lt : ∀ i, k i < g := fun i => by
    have hnn : (0 : ℤ) ≤ (a i) % (g : ℤ) := Int.emod_nonneg _ hgZ.ne'
    have hub : (a i) % (g : ℤ) < (g : ℤ) := Int.emod_lt_of_pos _ hgZ
    rw [hk_def]
    exact (Int.toNat_lt hnn).mpr hub
  have hk_le : ∀ i, k i ≤ g - 1 := fun i => by
    have := hk_lt i
    omega
  have key : ∀ i, (k i : ℕ) • ρ i = a i • ρ i := fun i => by
    have hnn : (0 : ℤ) ≤ (a i) % (g : ℤ) := Int.emod_nonneg _ hgZ.ne'
    rw [hk_def]
    rw [show ((((a i) % (g : ℤ)).toNat : ℕ) • ρ i) =
        ((((a i) % (g : ℤ)).toNat : ℤ) • ρ i) from
      (natCast_zsmul (ρ i) _).symm]
    rw [Int.toNat_of_nonneg hnn]
    rw [show ((g : ℤ) : ℤ) = (Fintype.card (ZMod g) : ℤ) by simp [ZMod.card]]
    exact mod_card_zsmul (ρ i) (a i)
  let T : Finset (Fin w × Fin (g - 1)) :=
    ((Finset.univ : Finset (Fin w)) ×ˢ (Finset.univ : Finset (Fin (g - 1)))).filter
      (fun p => p.2.1 < k p.1)
  refine ⟨T, ?_⟩
  show r = ∑ t ∈ T, ρ t.1
  have hsum : (∑ t ∈ T, ρ t.1) = ∑ i, k i • ρ i := by
    show (∑ t ∈ ((Finset.univ : Finset (Fin w)) ×ˢ
            (Finset.univ : Finset (Fin (g - 1)))).filter
            (fun p => p.2.1 < k p.1), ρ t.1) = ∑ i, k i • ρ i
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show (∑ y : Fin (g - 1), if y.val < k i then ρ i else 0) = k i • ρ i
    rw [← Finset.sum_filter, Finset.sum_const]
    congr 1
    have heq : ((Finset.univ : Finset (Fin (g - 1))).filter
                  (fun j : Fin (g - 1) => j.val < k i)) =
               (Finset.range (k i)).attachFin (fun j hj =>
                 lt_of_lt_of_le (Finset.mem_range.mp hj) (hk_le i)) := by
      ext ⟨b, hb⟩
      simp [Finset.mem_attachFin, Finset.mem_range]
    rw [heq, Finset.card_attachFin]
    simp
  rw [hsum, ha]
  exact Finset.sum_congr rfl (fun i _ => (key i).symm)

/-- Choose distinct natural indices for a finite family of predicates that each
occur arbitrarily far out. -/
lemma exists_injective_indices_fin :
    ∀ n : ℕ, ∀ P : Fin n → ℕ → Prop,
      (∀ a N, ∃ j, N ≤ j ∧ P a j) →
        ∃ idx : Fin n → ℕ, Function.Injective idx ∧ ∀ a, P a (idx a)
  | 0, _P, _hP => by
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro a
        exact Fin.elim0 a
      · intro a
        exact Fin.elim0 a
  | n + 1, P, hP => by
      obtain ⟨idx, hidx, hidxP⟩ :
          ∃ idx : Fin n → ℕ, Function.Injective idx ∧ ∀ a, P a.castSucc (idx a) :=
        exists_injective_indices_fin n (fun a N => P a.castSucc N)
          (fun a N => hP a.castSucc N)
      let B : ℕ := Finset.univ.sup idx + 1
      obtain ⟨j, hjB, hjP⟩ := hP (Fin.last n) B
      let idx' : Fin (n + 1) → ℕ := Fin.lastCases j idx
      refine ⟨idx', ?_, ?_⟩
      · intro a b hab
        rcases Fin.eq_castSucc_or_eq_last a with ⟨a0, rfl⟩ | rfl
        · rcases Fin.eq_castSucc_or_eq_last b with ⟨b0, rfl⟩ | rfl
          · simp [idx'] at hab
            exact congrArg Fin.castSucc (hidx hab)
          · simp [idx'] at hab
            have ha_le : idx a0 ≤ Finset.univ.sup idx :=
              Finset.le_sup (s := Finset.univ) (f := idx) (Finset.mem_univ a0)
            have : idx a0 < j := by omega
            omega
        · rcases Fin.eq_castSucc_or_eq_last b with ⟨b0, rfl⟩ | rfl
          · simp [idx'] at hab
            have hb_le : idx b0 ≤ Finset.univ.sup idx :=
              Finset.le_sup (s := Finset.univ) (f := idx) (Finset.mem_univ b0)
            have : idx b0 < j := by omega
            omega
          · rfl
      · intro a
        rcases Fin.eq_castSucc_or_eq_last a with ⟨a0, rfl⟩ | rfl
        · simpa [idx'] using hidxP a0
        · simpa [idx'] using hjP

/-- Realizing the duplicated generators by distinct sequence indices upgrades
the abstract duplicated-generator subset-sum lemma to `CoversResidues`. -/
lemma coversResidues_of_duplicated_generators {S : ℕ → ℤ} {w m : ℕ}
    (hm : 1 ≤ m) (ρ : Fin w → ZMod m)
    (hgen : AddSubgroup.closure (Set.range ρ) = ⊤)
    (idx : Fin w × Fin (m - 1) → ℕ)
    (hidx : Function.Injective idx)
    (hres : ∀ t : Fin w × Fin (m - 1),
      ((S (idx t) : ℤ) : ZMod m) = ρ t.1) :
    CoversResidues S m := by
  classical
  intro r
  obtain ⟨T, hT⟩ :=
    duplicated_generators_subset_sum_all_residues hm ρ hgen r
  refine ⟨∑ t ∈ T, S (idx t), ?_, ?_⟩
  · refine ⟨T.image idx, ?_⟩
    rw [Finset.sum_image]
    intro a _ha b _hb hab
    exact hidx hab
  · calc
      (((∑ t ∈ T, S (idx t) : ℤ) : ℤ) : ZMod m)
          = ∑ t ∈ T, ((S (idx t) : ℤ) : ZMod m) := by norm_cast
      _ = ∑ t ∈ T, ρ t.1 := by
        exact Finset.sum_congr rfl (fun t _ht => hres t)
      _ = r := hT.symm

/-- If a finite family of residues generates `ZMod m` and each generator occurs
arbitrarily far out in the sequence, then finite subset sums cover all residues
modulo `m`. -/
lemma coversResidues_of_frequent_generators {S : ℕ → ℤ} {w m : ℕ}
    (hm : 1 ≤ m) (ρ : Fin w → ZMod m)
    (hgen : AddSubgroup.closure (Set.range ρ) = ⊤)
    (hfreq : ∀ i : Fin w, ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ ((S n : ℤ) : ZMod m) = ρ i) :
    CoversResidues S m := by
  classical
  let e : Fin w × Fin (m - 1) ≃ Fin (w * (m - 1)) := finProdFinEquiv
  obtain ⟨idxFlat, hidxFlat, hidxFlat_res⟩ :=
    exists_injective_indices_fin (w * (m - 1))
      (fun a n => ((S n : ℤ) : ZMod m) = ρ (e.symm a).1)
      (fun a N => hfreq (e.symm a).1 N)
  let idx : Fin w × Fin (m - 1) → ℕ := fun t => idxFlat (e t)
  refine coversResidues_of_duplicated_generators hm ρ hgen idx ?_ ?_
  · intro a b hab
    exact e.injective (hidxFlat hab)
  · intro t
    simpa [idx, e] using hidxFlat_res (e t)

/-- A convenient Bezout-style version of
`coversResidues_of_frequent_generators`: if a finite family of frequently
occurring residues has an integer linear combination equal to `1`, then it
covers every residue modulo `m`. -/
lemma coversResidues_of_frequent_zsmul_eq_one {S : ℕ → ℤ} {w m : ℕ}
    (hm : 1 ≤ m) (ρ : Fin w → ZMod m) (a : Fin w → ℤ)
    (ha : ∑ i, a i • ρ i = (1 : ZMod m))
    (hfreq : ∀ i : Fin w, ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ ((S n : ℤ) : ZMod m) = ρ i) :
    CoversResidues S m := by
  haveI : NeZero m := ⟨by omega⟩
  exact coversResidues_of_frequent_generators hm ρ
    (zmod_closure_range_eq_top_of_sum_zsmul_eq_one ρ a ha)
    hfreq

/-- If at least `m` distinct terms have the same unit residue modulo `m`, then
their subset sums cover every residue class. This is the finite cyclic-group
core used in Graham's residue-system lemma. -/
lemma coversResidues_of_constant_unit_residue {S : ℕ → ℤ} {m : ℕ}
    (hm : 0 < m) {u : ZMod m} (hu : IsUnit u) {A : Finset ℕ}
    (hcard : m ≤ A.card)
    (hA : ∀ i ∈ A, ((S i : ℤ) : ZMod m) = u) :
    CoversResidues S m := by
  classical
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  intro r
  let v : ZMod m := (↑hu.unit⁻¹ : ZMod m) * r
  have hv_mul : v * u = r := by
    change ((↑hu.unit⁻¹ : ZMod m) * r) * u = r
    have hucoe : (hu.unit : ZMod m) = u := hu.unit_spec
    calc
      ((↑hu.unit⁻¹ : ZMod m) * r) * u =
          ((↑hu.unit⁻¹ : ZMod m) * r) * (↑hu.unit : ZMod m) :=
        congrArg (fun a : ZMod m => ((↑hu.unit⁻¹ : ZMod m) * r) * a) hucoe.symm
      _ = r := by
        calc
          ((↑hu.unit⁻¹ : ZMod m) * r) * (↑hu.unit : ZMod m) =
              ((↑hu.unit⁻¹ : ZMod m) * (↑hu.unit : ZMod m)) * r := by ring
          _ = r := by simp
  have hv_le_card : v.val ≤ A.card :=
    (Nat.le_of_lt v.val_lt).trans hcard
  rcases Finset.exists_subset_card_eq hv_le_card with ⟨K, hKA, hKcard⟩
  refine ⟨∑ i ∈ K, S i, ⟨K, rfl⟩, ?_⟩
  calc
    (((∑ i ∈ K, S i : ℤ) : ℤ) : ZMod m)
        = ∑ i ∈ K, ((S i : ℤ) : ZMod m) := by norm_cast
    _ = ∑ _i ∈ K, u := by
      exact Finset.sum_congr rfl (fun i hi => hA i (hKA hi))
    _ = (K.card : ℕ) • u := by simp
    _ = (v.val : ℕ) • u := by rw [hKcard]
    _ = (v.val : ZMod m) * u := by simp [nsmul_eq_mul]
    _ = v * u := by rw [ZMod.natCast_zmod_val]
    _ = r := hv_mul

/-- If at least `m * m` terms are units modulo `m`, then some unit residue
appears at least `m` times, so finite subset sums cover all residues modulo
`m`. This is a finite pigeonhole wrapper around
`coversResidues_of_constant_unit_residue`. -/
lemma coversResidues_of_many_unit_terms {S : ℕ → ℤ} {m : ℕ}
    (hm : 0 < m) {A : Finset ℕ}
    (hcard : m * m ≤ A.card)
    (hA : ∀ i ∈ A, IsUnit (((S i : ℤ) : ZMod m))) :
    CoversResidues S m := by
  classical
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let f : ℕ → ZMod m := fun i => ((S i : ℤ) : ZMod m)
  have hmap : ∀ i ∈ A, f i ∈ (Finset.univ : Finset (ZMod m)) := by
    intro i hi
    simp
  have huniv_nonempty : (Finset.univ : Finset (ZMod m)).Nonempty :=
    Finset.univ_nonempty
  have hcard' : (Finset.univ : Finset (ZMod m)).card * m ≤ A.card := by
    simpa [ZMod.card] using hcard
  obtain ⟨u, _hu_mem, hu_card⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := A) (t := (Finset.univ : Finset (ZMod m))) (f := f)
      hmap huniv_nonempty hcard'
  let K : Finset ℕ := A.filter fun i => f i = u
  have hKcard : m ≤ K.card := by
    simpa [K] using hu_card
  have hK_nonempty : K.Nonempty :=
    Finset.card_pos.mp (hm.trans_le hKcard)
  obtain ⟨i, hiK⟩ := hK_nonempty
  have hiA : i ∈ A := (Finset.mem_filter.mp hiK).1
  have hi_eq : f i = u := (Finset.mem_filter.mp hiK).2
  have hu : IsUnit u := by
    simpa [f, ← hi_eq] using hA i hiA
  exact coversResidues_of_constant_unit_residue hm hu hKcard
    (by
      intro j hj
      exact (Finset.mem_filter.mp hj).2)

/-- A frequently occurring unit residue condition implies residue coverage. -/
lemma coversResidues_of_frequently_unit_terms {S : ℕ → ℤ} {m : ℕ}
    (hm : 0 < m)
    (hunit : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsUnit (((S n : ℤ) : ZMod m))) :
    CoversResidues S m := by
  obtain ⟨A, hAcard, hA⟩ :=
    exists_finset_card_eq_of_frequently_atTop hunit (m * m)
  exact coversResidues_of_many_unit_terms hm (by simp [hAcard]) hA

/-- If all residue classes are covered by arbitrary finite subset sums, then a
single finite prefix already contains witnesses for every residue class. -/
lemma CoversResidues.exists_prefix {S : ℕ → ℤ} {m : ℕ}
    [Fintype (ZMod m)] (hcov : CoversResidues S m) :
    ∃ N : ℕ, ∀ r : ZMod m,
      ∃ x ∈ FSOf S (Finset.range N), ((x : ℤ) : ZMod m) = r := by
  classical
  let x : ZMod m → ℤ := fun r => Classical.choose (hcov r)
  have hx : ∀ r : ZMod m, x r ∈ FS S ∧ ((x r : ℤ) : ZMod m) = r := by
    intro r
    exact Classical.choose_spec (hcov r)
  let I : ZMod m → Finset ℕ := fun r => Classical.choose (hx r).1
  have hI_sum : ∀ r : ZMod m, x r = ∑ i ∈ I r, S i := by
    intro r
    exact Classical.choose_spec (hx r).1
  let A : Finset ℕ := Finset.univ.biUnion I
  refine ⟨A.sup id + 1, ?_⟩
  intro r
  refine ⟨x r, ?_, (hx r).2⟩
  refine ⟨I r, ?_, hI_sum r⟩
  intro i hi
  rw [Finset.mem_range]
  have hiA : i ∈ A := by
    change i ∈ Finset.univ.biUnion I
    rw [Finset.mem_biUnion]
    exact ⟨r, Finset.mem_univ r, hi⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (s := A) (f := id) hiA)

lemma fsOf_range_subset_finitePrefixSeq (S : ℕ → ℤ) (N : ℕ) :
    FSOf S (Finset.range N) ⊆ FS (finitePrefixSeq S N) := by
  intro x hx
  rcases hx with ⟨I, hI_sub, hsum⟩
  refine ⟨I, ?_⟩
  rw [hsum]
  exact Finset.sum_congr rfl
    (fun i hi => by
      have hiN : i < N := Finset.mem_range.mp (hI_sub hi)
      simp [finitePrefixSeq, hiN])

lemma fs_finitePrefixSeq_subset (S : ℕ → ℤ) (N : ℕ) :
    FS (finitePrefixSeq S N) ⊆ FS S := by
  classical
  exact fs_subset_of_eq_zero_or_subsequence (s := S) (t := finitePrefixSeq S N)
    (fun n => n)
    (fun _ _ _ _ h => h)
    (fun i hi0 => by
      by_cases hiN : i < N
      · simp [finitePrefixSeq, hiN]
      · exfalso
        exact hi0 (by simp [finitePrefixSeq, hiN]))

lemma fs_finitePrefixSeq_mono (S : ℕ → ℤ) {N M : ℕ} (hNM : N ≤ M) :
    FS (finitePrefixSeq S N) ⊆ FS (finitePrefixSeq S M) := by
  classical
  exact fs_subset_of_eq_zero_or_subsequence
    (s := finitePrefixSeq S M) (t := finitePrefixSeq S N)
    (fun n => n)
    (fun _ _ _ _ h => h)
    (fun i hi0 => by
      by_cases hiN : i < N
      · have hiM : i < M := hiN.trans_le hNM
        simp [finitePrefixSeq, hiN, hiM]
      · exfalso
        exact hi0 (by simp [finitePrefixSeq, hiN]))

/-- Residue coverage can be witnessed by a finite prefix, padded by zeros. -/
lemma CoversResidues.exists_finitePrefixSeq {S : ℕ → ℤ} {m : ℕ}
    [Fintype (ZMod m)] (hcov : CoversResidues S m) :
    ∃ N : ℕ, CoversResidues (finitePrefixSeq S N) m := by
  rcases hcov.exists_prefix with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro r
  rcases hN r with ⟨x, hx, hxmod⟩
  exact ⟨x, fsOf_range_subset_finitePrefixSeq S N hx, hxmod⟩

lemma CoversResidues.finitePrefixSeq_mono {S : ℕ → ℤ} {m N M : ℕ}
    (hNM : N ≤ M)
    (hcov : CoversResidues (finitePrefixSeq S N) m) :
    CoversResidues (finitePrefixSeq S M) m :=
  CoversResidues.of_fs_subset (fs_finitePrefixSeq_mono S hNM) hcov

lemma fs_interleave_left_subset (S T : ℕ → ℤ) :
    FS S ⊆ FS (interleave S T) := by
  intro x hx
  rcases hx with ⟨I, hI⟩
  refine ⟨I.image (fun n => 2 * n), ?_⟩
  rw [hI, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _
    simp
  · intro a _ b _ hab
    exact Nat.mul_left_cancel (by decide : 0 < 2) hab

lemma fs_interleave_right_subset (S T : ℕ → ℤ) :
    FS T ⊆ FS (interleave S T) := by
  intro x hx
  rcases hx with ⟨I, hI⟩
  refine ⟨I.image (fun n => 2 * n + 1), ?_⟩
  rw [hI, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _
    simp
  · intro a _ b _ hab
    have h2add : 2 * a + 1 = 2 * b + 1 := hab
    have hsucc : Nat.succ (2 * a) = Nat.succ (2 * b) := by
      simpa [Nat.succ_eq_add_one] using h2add
    have h2 : 2 * a = 2 * b := Nat.succ.inj hsucc
    exact Nat.mul_left_cancel (by decide : 0 < 2) h2

lemma CoversResidues.interleave_left {S T : ℕ → ℤ} {m : ℕ}
    (hcov : CoversResidues S m) :
    CoversResidues (interleave S T) m :=
  CoversResidues.of_fs_subset (fs_interleave_left_subset S T) hcov

lemma CoversResidues.interleave_right {S T : ℕ → ℤ} {m : ℕ}
    (hcov : CoversResidues T m) :
    CoversResidues (interleave S T) m :=
  CoversResidues.of_fs_subset (fs_interleave_right_subset S T) hcov

lemma even_odd_images_disjoint (I J : Finset ℕ) :
    Disjoint (I.image fun n => 2 * n) (J.image fun n => 2 * n + 1) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨j, _hj, hji⟩
  omega

/-- A subset sum from each side of an interleaving can be added as a subset sum
of the interleaved sequence. -/
lemma fs_interleave_add {S T : ℕ → ℤ} {x y : ℤ}
    (hx : x ∈ FS S) (hy : y ∈ FS T) :
    x + y ∈ FS (interleave S T) := by
  classical
  rcases hx with ⟨I, hI⟩
  rcases hy with ⟨J, hJ⟩
  refine ⟨(I.image fun n => 2 * n) ∪ (J.image fun n => 2 * n + 1), ?_⟩
  rw [Finset.sum_union (even_odd_images_disjoint I J)]
  have hIimg :
      (∑ a ∈ I.image (fun n => 2 * n), interleave S T a) =
        ∑ i ∈ I, S i := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      simp
    · intro a _ b _ hab
      exact Nat.mul_left_cancel (by decide : 0 < 2) hab
  have hJimg :
      (∑ a ∈ J.image (fun n => 2 * n + 1), interleave S T a) =
        ∑ j ∈ J, T j := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j _
      simp
    · intro a _ b _ hab
      have h2add : 2 * a + 1 = 2 * b + 1 := hab
      have hsucc : Nat.succ (2 * a) = Nat.succ (2 * b) := by
        simpa [Nat.succ_eq_add_one] using h2add
      have h2 : 2 * a = 2 * b := Nat.succ.inj hsucc
      exact Nat.mul_left_cancel (by decide : 0 < 2) h2
  rw [hIimg, hJimg]
  rw [← hI, ← hJ]

lemma int_le_toNat_cast (z : ℤ) : z ≤ (z.toNat : ℤ) := by
  by_cases hz : 0 ≤ z
  · rw [Int.toNat_of_nonneg hz]
  · have hzle : z ≤ 0 := le_of_not_ge hz
    exact le_trans hzle (Int.natCast_nonneg _)

lemma neg_le_toNat_neg_cast (z : ℤ) : -z ≤ ((-z).toNat : ℤ) :=
  int_le_toNat_cast (-z)

/-- Graham's AP-plus-residue glue: if one sequence has arbitrarily long
arithmetic progressions with step `m` and the other covers all residues modulo
`m`, then their interleaving is nearly complete. -/
lemma nearlyComplete_of_APs_and_residues {S T : ℕ → ℤ} {m : ℕ}
    (_hm : 1 ≤ m)
    (hAP :
      ∀ k : ℕ, 1 ≤ k →
        ∃ c : ℤ, ∀ j : ℕ, 1 ≤ j → j ≤ k →
          c + (j : ℤ) * (m : ℤ) ∈ FS S)
    (hres : CoversResidues T m) :
    NearlyComplete (interleave S T) := by
  classical
  intro k hk
  have hkpos : 0 < k := by omega
  let r : Fin k → ZMod m := fun a => ((a.1 + 1 : ℕ) : ZMod m)
  let x : Fin k → ℤ := fun a => Classical.choose (hres (r a))
  have hx : ∀ a : Fin k, x a ∈ FS T ∧ ((x a : ℤ) : ZMod m) = r a := by
    intro a
    exact Classical.choose_spec (hres (r a))
  have hxmod_int :
      ∀ a : Fin k, ((x a : ℤ) : ZMod m) = (((a.1 + 1 : ℕ) : ℤ) : ZMod m) := by
    intro a
    simpa [r] using (hx a).2
  let q : Fin k → ℤ := fun a =>
    Classical.choose (exists_eq_add_mul_of_zmod_eq (hxmod_int a))
  have hq :
      ∀ a : Fin k, x a = ((a.1 + 1 : ℕ) : ℤ) + (m : ℤ) * q a := by
    intro a
    exact Classical.choose_spec (exists_eq_add_mul_of_zmod_eq (hxmod_int a))
  let P : ℕ := Finset.univ.sup fun a : Fin k => (q a).toNat
  let N : ℕ := Finset.univ.sup fun a : Fin k => (-(q a)).toNat
  let M : ℕ := P + 1
  let K : ℕ := P + N + 1
  have hKpos : 1 ≤ K := by
    dsimp [K]
    omega
  rcases hAP K hKpos with ⟨c, hc⟩
  refine ⟨c + (M : ℤ) * (m : ℤ), ?_⟩
  intro j hj1 hjk
  let a : Fin k := ⟨j - 1, by omega⟩
  have ha_val : a.1 + 1 = j := by
    dsimp [a]
    omega
  have hq_le_P : q a ≤ (P : ℤ) := by
    calc
      q a ≤ ((q a).toNat : ℤ) := int_le_toNat_cast (q a)
      _ ≤ (P : ℤ) := by
        exact_mod_cast Finset.le_sup (s := Finset.univ) (f := fun a : Fin k => (q a).toNat)
          (Finset.mem_univ a)
  have hnegq_le_N : -q a ≤ (N : ℤ) := by
    calc
      -q a ≤ (((-q a).toNat) : ℤ) := neg_le_toNat_neg_cast (q a)
      _ ≤ (N : ℤ) := by
        exact_mod_cast Finset.le_sup (s := Finset.univ) (f := fun a : Fin k => (-(q a)).toNat)
          (Finset.mem_univ a)
  let tZ : ℤ := (M : ℤ) - q a
  have htZ_pos : 1 ≤ tZ := by
    dsimp [tZ, M]
    omega
  let t : ℕ := tZ.toNat
  have ht_cast : (t : ℤ) = tZ := Int.toNat_of_nonneg (by omega : 0 ≤ tZ)
  have ht1 : 1 ≤ t := by
    have : (1 : ℤ) ≤ (t : ℤ) := by simpa [ht_cast] using htZ_pos
    exact_mod_cast this
  have htK : t ≤ K := by
    have htZ_le : tZ ≤ (K : ℤ) := by
      dsimp [tZ, M, K]
      omega
    have : (t : ℤ) ≤ (K : ℤ) := by simpa [ht_cast] using htZ_le
    exact_mod_cast this
  have hS : c + (t : ℤ) * (m : ℤ) ∈ FS S := hc t ht1 htK
  have hT : x a ∈ FS T := (hx a).1
  have hsum : (c + (t : ℤ) * (m : ℤ)) + x a ∈ FS (interleave S T) :=
    fs_interleave_add hS hT
  have htarget :
      c + (M : ℤ) * (m : ℤ) + (j : ℤ) =
        (c + (t : ℤ) * (m : ℤ)) + x a := by
    rw [ht_cast]
    dsimp [tZ]
    rw [hq a, ha_val]
    ring
  rw [htarget]
  exact hsum

/-- Direct Graham glue: signed tail differences of size `m`, together with
residue coverage modulo `m`, imply near-completeness after interleaving. -/
lemma nearlyComplete_of_signed_tail_and_residues {S T : ℕ → ℤ} {m : ℕ}
    (hm : 1 ≤ m)
    (htail : ∀ N : ℕ, (m : ℤ) ∈ SignedFS (tail S N))
    (hres : CoversResidues T m) :
    NearlyComplete (interleave S T) :=
  nearlyComplete_of_APs_and_residues hm
    (fun k hk => arbitrary_APs_of_signed_tail_difference htail k hk) hres

/-! ## First Sigma-sequence lemma -/

/-- A concrete tail-doubling criterion for Graham's Sigma-sequence condition.

This is the reusable core of Graham's "eventual doubling gives a Sigma-sequence"
lemma. A later wrapper can choose `h` and `k` from filter/eventual hypotheses. -/
lemma sigmaSeq_of_tail_doubling (S : ℕ → ℤ) (h k : ℕ)
    (hk : 1 ≤ k)
    (hpos : ∀ m : ℕ, 0 < S (h + m))
    (hbase : S h < (k : ℤ))
    (hdbl : ∀ m : ℕ, S (h + (m + 1)) ≤ 2 * S (h + m)) :
    SigmaSeq S := by
  refine ⟨k, h, hk, hpos, ?_⟩
  intro m
  induction m with
  | zero =>
      simpa using hbase
  | succ m ih =>
      rw [Finset.sum_range_succ]
      calc
        S (h + (m + 1)) ≤ 2 * S (h + m) := hdbl m
        _ = S (h + m) + S (h + m) := by ring
        _ < ((k : ℤ) + ∑ n ∈ Finset.range m, S (h + n)) + S (h + m) := by
          linarith
        _ = (k : ℤ) + (∑ n ∈ Finset.range m, S (h + n) + S (h + m)) := by
          ring

/-- Graham's eventual-doubling criterion for Sigma-sequences. -/
lemma sigma_of_eventually_doubling {S : ℕ → ℤ}
    (hpos : ∀ᶠ n in Filter.atTop, 0 < S n)
    (hdbl : ∀ᶠ n in Filter.atTop, S (n + 1) ≤ 2 * S n) :
    SigmaSeq S := by
  rw [Filter.eventually_atTop] at hpos hdbl
  rcases hpos with ⟨Npos, hNpos⟩
  rcases hdbl with ⟨Ndbl, hNdbl⟩
  let h : ℕ := max Npos Ndbl
  let k : ℕ := Int.toNat (S h) + 1
  have hk : 1 ≤ k := by
    dsimp [k]
    omega
  have hpos_tail : ∀ m : ℕ, 0 < S (h + m) := by
    intro m
    exact hNpos (h + m) (by dsimp [h]; omega)
  have hdbl_tail : ∀ m : ℕ, S (h + (m + 1)) ≤ 2 * S (h + m) := by
    intro m
    have hstep := hNdbl (h + m) (by dsimp [h]; omega)
    simpa [Nat.add_assoc] using hstep
  have hbase_pos : 0 < S h := by
    simpa using hpos_tail 0
  have hbase : S h < (k : ℤ) := by
    have hnonneg : 0 ≤ S h := le_of_lt hbase_pos
    dsimp [k]
    rw [Int.toNat_of_nonneg hnonneg]
    linarith
  exact sigmaSeq_of_tail_doubling S h k hk hpos_tail hbase hdbl_tail

/-- Bounded core of Graham's Lemma 1. Starting from `k` consecutive subset sums
of `T`, the first `m` terms of a positive Sigma-tail of `S` extend this to a
longer interval. The conclusion is decomposed as a bounded `S`-sum plus a
`T`-sum; this avoids any hidden reuse of Sigma-tail terms. -/
lemma sigma_nearly_interval_decomposition
    (S T : ℕ → ℤ) (h k : ℕ) (c : ℤ)
    (hpos : ∀ m : ℕ, 0 < S (h + m))
    (hsigma :
      ∀ m : ℕ, S (h + m) < (k : ℤ) + ∑ n ∈ Finset.range m, S (h + n))
    (hnear : ∀ j : ℕ, 1 ≤ j → j ≤ k → c + (j : ℤ) ∈ FS T) :
    ∀ m : ℕ, ∀ y : ℤ,
      1 ≤ y →
      y ≤ (k : ℤ) + ∑ n ∈ Finset.range m, S (h + n) →
      ∃ a ∈ FSOf (tail S h) (Finset.range m), ∃ b ∈ FS T, c + y = a + b
  | 0, y, hy1, hyk => by
      have hy_nonneg : 0 ≤ y := by linarith
      let j : ℕ := y.toNat
      have hj_cast : (j : ℤ) = y := Int.toNat_of_nonneg hy_nonneg
      have hj1 : 1 ≤ j := by
        have : (1 : ℤ) ≤ (j : ℤ) := by simpa [hj_cast] using hy1
        exact_mod_cast this
      have hjk : j ≤ k := by
        have : (j : ℤ) ≤ (k : ℤ) := by simpa [hj_cast] using hyk
        exact_mod_cast this
      refine ⟨0, fsOf_empty (tail S h), c + (j : ℤ), hnear j hj1 hjk, ?_⟩
      rw [hj_cast]
      ring
  | m + 1, y, hy1, hy_upper => by
      let L : ℤ := (k : ℤ) + ∑ n ∈ Finset.range m, S (h + n)
      let s : ℤ := S (h + m)
      have hs_pos : 0 < s := by
        simpa [s] using hpos m
      have hs_lt_L : s < L := by
        simpa [L, s] using hsigma m
      have hy_upper' : y ≤ L + s := by
        simpa [L, s, Finset.range_add_one, add_assoc, add_comm, add_left_comm] using hy_upper
      by_cases hyL : y ≤ L
      · rcases sigma_nearly_interval_decomposition S T h k c hpos hsigma hnear
            m y hy1 hyL with ⟨a, ha, b, hb, hsum⟩
        refine ⟨a, fsOf_mono ?_ ha, b, hb, hsum⟩
        intro i hi
        exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
      · have hy_gt_L : L < y := lt_of_not_ge hyL
        have hy_sub_low : 1 ≤ y - s := by omega
        have hy_sub_high : y - s ≤ L := by omega
        rcases sigma_nearly_interval_decomposition S T h k c hpos hsigma hnear
            m (y - s) hy_sub_low hy_sub_high with ⟨a, ha, b, hb, hsum⟩
        refine ⟨a + s, ?_, b, hb, ?_⟩
        · have hmem :
              a + tail S h m ∈ FSOf (tail S h) (insert m (Finset.range m)) :=
            fsOf_add_index (by simp) ha
          simpa [Finset.range_add_one, tail, s, add_assoc] using hmem
        · calc
            c + y = (c + (y - s)) + s := by ring
            _ = (a + b) + s := by rw [hsum]
            _ = a + s + b := by ring

/-- Graham's first sequence-combination lemma in the form needed later: a
Sigma-sequence interleaved with a nearly complete sequence is complete. -/
lemma complete_of_sigma_nearly {S T : ℕ → ℤ}
    (hS : SigmaSeq S) (hT : NearlyComplete T) :
    Complete (interleave S T) := by
  rcases hS with ⟨k, h, hk, hpos, hsigma⟩
  rcases hT k hk with ⟨c, hnear⟩
  refine ⟨c + 1, ?_⟩
  intro x hx
  let y : ℤ := x - c
  have hy1 : 1 ≤ y := by
    dsimp [y]
    omega
  have hy_nonneg : 0 ≤ y := by linarith
  let m : ℕ := y.toNat
  have hm_cast : (m : ℤ) = y := Int.toNat_of_nonneg hy_nonneg
  have hsum_ge :
      (m : ℤ) ≤ ∑ n ∈ Finset.range m, S (h + n) := by
    calc
      (m : ℤ) = ∑ n ∈ Finset.range m, (1 : ℤ) := by simp
      _ ≤ ∑ n ∈ Finset.range m, S (h + n) := by
        exact Finset.sum_le_sum (fun n _ => by
          have hn := hpos n
          omega)
  have hy_upper : y ≤ (k : ℤ) + ∑ n ∈ Finset.range m, S (h + n) := by
    rw [← hm_cast]
    have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.zero_le k
    linarith
  rcases sigma_nearly_interval_decomposition S T h k c hpos hsigma hnear
      m y hy1 hy_upper with ⟨a, ha, b, hb, hsum⟩
  have ha_tail : a ∈ FS (tail S h) := fsOf_subset_fs (tail S h) (Finset.range m) ha
  have haS : a ∈ FS S := fs_tail_subset S h ha_tail
  have hab : a + b ∈ FS (interleave S T) := fs_interleave_add haS hb
  have hx_eq : x = a + b := by
    dsimp [y] at hsum
    omega
  exact hx_eq.symm ▸ hab

end Erdos.P283.RSG
