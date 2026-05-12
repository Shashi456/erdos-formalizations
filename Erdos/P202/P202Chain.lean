/-
Erdős Problem 202 — Descending chain.

Heart of the new contribution. Builds an `R`-step chain of pairwise coprime
prime-power blocks `P_1, …, P_R` such that every surviving modulus has
`P_{≤r}` as an exact divisor, residues agree mod `P_{≤r}`, and the size
inequality (PDF eq. 9)

  P_r ≤ (N / |Q'|) · exp((-d/2 + ε) Z) · (log N)^{W_{r-1}/2} · LowerOrder(N, ω(P_{≤r}))

holds at each step.

Combines the gcd criterion (`P202Basic.lean`), the dense-core lemma
(`SpreadCore.lean`), and the BFV ω-count input (`BFVInputs.lean`).
-/

import Mathlib
import Erdos.P202.P202Basic
import Erdos.P202.P202Arithmetic
import Erdos.P202.SpreadCore
import Erdos.P202.BFVInputs

namespace Erdos202

open Filter Finset
open scoped BigOperators

/-! ## §0 Weighted pigeonhole -/

lemma nat_cast_le_of_le_floor {m : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (h : m ≤ Nat.floor x) : (m : ℝ) ≤ x := by
  exact (Nat.le_floor_iff hx).1 h

/-- Weighted pigeonhole principle. If a finite weighted average is formed
with positive weights, at least one summand is at least its weighted share.

This is the finite lemma used in PDF Lemma 4.1 to select an attained exact
block value. -/
lemma weighted_pigeonhole {α : Type*} [DecidableEq α] (I : Finset α)
    (N w : α → ℝ) (hI : I.Nonempty)
    (hw : ∀ i ∈ I, 0 < w i) :
    ∃ i ∈ I, (∑ j ∈ I, N j) * w i / (∑ j ∈ I, w j) ≤ N i := by
  classical
  let totalN := ∑ j ∈ I, N j
  let totalW := ∑ j ∈ I, w j
  have htotalW_pos : 0 < totalW := Finset.sum_pos hw hI
  by_contra h
  push_neg at h
  have hlt : ∀ i ∈ I, N i < totalN * w i / totalW := by
    intro i hi
    simpa [totalN, totalW] using h i hi
  have hsum_lt : ∑ i ∈ I, N i < ∑ i ∈ I, totalN * w i / totalW := by
    exact Finset.sum_lt_sum_of_nonempty hI hlt
  have hsum_rhs : (∑ i ∈ I, totalN * w i / totalW) = totalN := by
    calc
      (∑ i ∈ I, totalN * w i / totalW) =
          ∑ i ∈ I, (totalN / totalW) * w i := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (totalN / totalW) * totalW := by rw [Finset.mul_sum]
      _ = totalN := div_mul_cancel₀ totalN htotalW_pos.ne'
  have : totalN < totalN := by
    change (∑ i ∈ I, N i) < totalN
    rw [← hsum_rhs]
    exact hsum_lt
  exact lt_irrefl _ this

/-- Weighted pigeonhole applied to fibers of a finite map. For any positive
weight on the attained values of `B`, one value has a fiber at least its
weighted share of the whole domain. -/
lemma exists_fiber_weighted_share {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (B : α → β) (w : β → ℝ) (hS : S.Nonempty)
    (hw : ∀ b ∈ S.image B, 0 < w b) :
    ∃ b ∈ S.image B,
      (S.card : ℝ) * w b / (∑ c ∈ S.image B, w c) ≤
        ((S.filter fun a => B a = b).card : ℝ) := by
  classical
  have hImage : (S.image B).Nonempty := hS.image B
  rcases weighted_pigeonhole (S.image B)
      (fun b => ((S.filter fun a => B a = b).card : ℝ)) w hImage hw with
    ⟨b, hb, hbshare⟩
  refine ⟨b, hb, ?_⟩
  have hsum_counts_nat :
      (∑ b ∈ S.image B, (S.filter fun a => B a = b).card) = S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      exact h.1
    · intro ha
      exact ⟨ha, a, ha, rfl⟩
  have hsum_counts_real :
      (∑ b ∈ S.image B, ((S.filter fun a => B a = b).card : ℝ)) =
        (S.card : ℝ) := by
    exact_mod_cast hsum_counts_nat
  simpa [hsum_counts_real] using hbshare

lemma fiber_nonempty_of_mem_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {B : α → β} {b : β} (hb : b ∈ S.image B) :
    (S.filter fun a => B a = b).Nonempty := by
  rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
  exact ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩

/-- Ordinary pigeonhole over a finite codomain, in the real-valued form used
for residue classes modulo the chosen exact block. -/
lemma exists_fiber_card_div_le {α β : Type*} [DecidableEq α] [Fintype β]
    [DecidableEq β] (S : Finset α) (r : α → β) (hS : S.Nonempty) :
    ∃ b : β,
      (S.card : ℝ) / (Fintype.card β : ℝ) ≤
        ((S.filter fun a => r a = b).card : ℝ) := by
  classical
  haveI : Nonempty β := by
    rcases hS with ⟨a, _ha⟩
    exact ⟨r a⟩
  have hUniv : (Finset.univ : Finset β).Nonempty := Finset.univ_nonempty
  rcases weighted_pigeonhole (Finset.univ : Finset β)
      (fun b => ((S.filter fun a => r a = b).card : ℝ)) (fun _ => (1 : ℝ))
      hUniv (by intro _b _hb; norm_num) with ⟨b, _hb, hbshare⟩
  refine ⟨b, ?_⟩
  have hsum_counts_nat :
      (∑ b ∈ (Finset.univ : Finset β), (S.filter fun a => r a = b).card) =
        S.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  have hsum_counts_real :
      (∑ b ∈ (Finset.univ : Finset β),
          ((S.filter fun a => r a = b).card : ℝ)) = (S.card : ℝ) := by
    exact_mod_cast hsum_counts_nat
  have hsum_weights :
      (∑ _b ∈ (Finset.univ : Finset β), (1 : ℝ)) =
        (Fintype.card β : ℝ) := by
    simp
  simpa [hsum_counts_real, hsum_weights] using hbshare

/-- Residue-class pigeonhole specialized to `ZMod P`. -/
lemma exists_zmod_fiber_card_div_le (T : Finset ℕ) (P : ℕ) [NeZero P]
    (r : ℕ → ZMod P) (hT : T.Nonempty) :
    ∃ b : ZMod P,
      (T.card : ℝ) / (P : ℝ) ≤ ((T.filter fun q => r q = b).card : ℝ) := by
  rcases exists_fiber_card_div_le T r hT with ⟨b, hb⟩
  exact ⟨b, by simpa [ZMod.card] using hb⟩

lemma List.mem_dvd_foldr_mul {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    a ∣ l.foldr (· * ·) 1 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.mem_cons] at ha
      cases ha with
      | inl h =>
          subst b
          simp
      | inr h =>
          exact dvd_mul_of_dvd_right (ih h) b

private lemma List.foldr_mul_pos {l : List ℕ}
    (hpos : ∀ a ∈ l, 0 < a) : 0 < l.foldr (· * ·) 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.foldr_cons]
      exact Nat.mul_pos (hpos a (by simp)) (ih (by
        intro b hb
        exact hpos b (by simp [hb])))

private lemma List.coprime_foldr_mul_of_forall
    {P : ℕ} {Ps : List ℕ} (hcop_all : ∀ Q ∈ Ps, Nat.Coprime P Q) :
    Nat.Coprime P (Ps.foldr (· * ·) 1) := by
  induction Ps with
  | nil =>
      simp
  | cons Q Qs ih =>
      simp only [List.foldr_cons]
      exact Nat.Coprime.mul_right (hcop_all Q (by simp)) (ih (by
        intro R hR
        exact hcop_all R (by simp [hR])))

private lemma sum_inv_sq_range_le_two (m : ℕ) :
    ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤ 2 := by
  have hstrong : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Finset.range m, (1 : ℝ) / ((ν + 1) ^ 2) ≤
        2 - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero =>
        cases hm
    | succ m ih =>
        cases m with
        | zero =>
            norm_num
        | succ m =>
            rw [Finset.sum_range_succ]
            have ih' : ∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2)
                ≤ 2 - 1 / ((m + 1 : ℕ) : ℝ) :=
              ih (by omega)
            have hstep :
                (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                  1 / ((m + 1 : ℕ) : ℝ) -
                    1 / (((m + 1 : ℕ) : ℝ) + 1) := by
              have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
              have hm2 : 0 < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
              field_simp [hm1.ne', hm2.ne']
              ring_nf
              nlinarith [show 0 ≤ (m : ℝ) by positivity]
            calc
              (∑ ν ∈ Finset.range (m + 1), (1 : ℝ) / ((ν + 1) ^ 2))
                  + 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2
                  ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ))
                      + (1 / ((m + 1 : ℕ) : ℝ) -
                        1 / (((m + 1 : ℕ) : ℝ) + 1)) := by
                    gcongr
              _ = 2 - 1 / ((m + 2 : ℕ) : ℝ) := by
                    norm_num
                    ring
  by_cases hm : m = 0
  · simp [hm]
  · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    exact (hstrong m hm1).trans (by
      have hnonneg : 0 ≤ (1 : ℝ) / (m : ℝ) := by positivity
      linarith)

private lemma one_div_sq_nat_prod {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (1 : ℝ) / (((∏ i, f i : ℕ) : ℝ) ^ 2) =
      ∏ i, (1 : ℝ) / (((f i : ℕ) : ℝ) ^ 2) := by
  simp [one_div, Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_pow]

/-! ## §1 The chain state -/

/-- Snapshot of the chain after `r` selection steps. -/
structure ChainState (N : ℕ) (D : PrunedData N) where
  /-- Number of completed steps. -/
  r : ℕ
  /-- The selected prime-power blocks `P_1, …, P_r`. -/
  blocks : List ℕ
  blocks_length : blocks.length = r
  /-- Survivors of the chain. Subset of the pruned family. -/
  Qsurv : Finset ℕ
  Qsurv_subset : Qsurv ⊆ D.Q
  Qsurv_nonempty : Qsurv.Nonempty
  /-- Total exponent count `W = ω(P_{≤r})`. -/
  W : ℕ
  /-- The product of all selected blocks. -/
  productP : ℕ
  product_eq : productP = (blocks.foldr (· * ·) 1)
  blocks_pos : ∀ P ∈ blocks, 0 < P
  productP_pos : 0 < productP
  /-- Selected blocks are pairwise coprime — equivalently, their prime
  supports are pairwise disjoint. -/
  pairwise_coprime : blocks.Pairwise Nat.Coprime
  /-- Every surviving modulus has `productP` as an *exact* divisor, i.e. no
  prime in `primeSupport productP` survives in `q / productP`. -/
  exact_divides : ∀ q ∈ Qsurv, productP ∣ q
  no_selected_prime_remains :
    ∀ q ∈ Qsurv, ∀ p ∈ primeSupport productP,
      p ∉ primeSupport (q / productP)
  /-- All surviving moduli agree on residues modulo `productP`. -/
  residues_agree :
    ∀ qi ∈ Qsurv, ∀ rj ∈ Qsurv,
      ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
        D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (productP : ℤ)]
  W_eq : W = omega productP
  W_le_K : W ≤ D.K

/-- Every selected block contributes at least one prime. This is true for
states produced by the descending-chain constructors, but kept as a predicate
rather than a structure field so basic APIs can still talk about arbitrary
chain states. -/
def ChainState.BlocksOmegaPos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : Prop :=
  ∀ P ∈ S.blocks, 1 ≤ omega P

lemma ChainState.Qsurv_card_pos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : 0 < S.Qsurv.card :=
  S.Qsurv_nonempty.card_pos

lemma ChainState.productP_le_of_mem {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    S.productP ≤ q := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
  exact Nat.le_of_dvd hqpos (S.exact_divides q hq)

lemma ChainState.productP_hExp_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    (hExp S.productP : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hle_nat : hExp S.productP ≤ hExp q :=
    hExp_le_of_dvd (S.exact_divides q hq) hqne
  have hle_real : (hExp S.productP : ℝ) ≤ (hExp q : ℝ) := by
    exact_mod_cast hle_nat
  exact hle_real.trans (D.hExp_bound q hqD)

lemma ChainState.block_dvd_productP {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {B : ℕ} (hB : B ∈ S.blocks) : B ∣ S.productP := by
  rw [S.product_eq]
  exact List.mem_dvd_foldr_mul hB

lemma ChainState.selected_remaining_disjoint {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    Disjoint (primeSupport S.productP) (remainingSupport S.productP q) := by
  rw [Finset.disjoint_left]
  intro p hpP hpRem
  exact S.no_selected_prime_remains q hq p hpP hpRem

lemma ChainState.remainingSupport_card_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    (remainingSupport S.productP q).card = D.K - S.W := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqpos : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have homega :
      omega (q / S.productP) = omega q - omega S.productP :=
    omega_div_eq_sub_omega_of_dvd (S.exact_divides q hq)
      S.productP_pos.ne' hqpos (S.selected_remaining_disjoint hq)
  calc
    (remainingSupport S.productP q).card = omega (q / S.productP) := by
      simp [remainingSupport, omega]
    _ = omega q - omega S.productP := homega
    _ = D.K - S.W := by
      rw [D.omega_eq q hqD, ← S.W_eq]

lemma ChainState.remainingSupport_nonempty_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K)
    {q : ℕ} (hq : q ∈ S.Qsurv) :
    (remainingSupport S.productP q).Nonempty := by
  rw [← Finset.card_pos, S.remainingSupport_card_eq hq]
  omega

lemma ChainState.remainingSupport_card_pos_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K)
    {q : ℕ} (hq : q ∈ S.Qsurv) :
    0 < (remainingSupport S.productP q).card := by
  exact (S.remainingSupport_nonempty_of_room hRoom hq).card_pos

lemma ChainState.gcd_dvd_productP_of_disjoint_remaining {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q r : ℕ} (hq : q ∈ S.Qsurv) (hr : r ∈ S.Qsurv)
    (hdisj : Disjoint (remainingSupport S.productP q) (remainingSupport S.productP r)) :
    Nat.gcd q r ∣ S.productP := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqpos : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hrpos : r ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1).ne'
  exact gcd_dvd_of_disjoint_remainingSupport
    (S.exact_divides q hq) (S.exact_divides r hr)
    S.productP_pos.ne' hqpos hrpos hdisj

lemma ChainState.remainingSupport_not_disjoint_of_ne {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q r : ℕ} (hq : q ∈ S.Qsurv) (hr : r ∈ S.Qsurv)
    (hqr : q ≠ r) :
    ¬ Disjoint (remainingSupport S.productP q) (remainingSupport S.productP r) := by
  intro hdisj
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1
  have hgcd_dvd : Nat.gcd q r ∣ S.productP :=
    S.gcd_dvd_productP_of_disjoint_remaining hq hr hdisj
  have hmodP := S.residues_agree q hq r hr hqD hrD
  have hmodG :
      D.a ⟨q, hqD⟩ ≡ D.a ⟨r, hrD⟩ [ZMOD (Nat.gcd q r : ℤ)] := by
    rw [Int.modEq_iff_dvd] at hmodP ⊢
    have hgcd_dvd_int : (Nat.gcd q r : ℤ) ∣ (S.productP : ℤ) := by
      exact_mod_cast hgcd_dvd
    exact dvd_trans hgcd_dvd_int hmodP
  have hres_disj :
      Disjoint (residueClass q (D.a ⟨q, hqD⟩))
        (residueClass r (D.a ⟨r, hrD⟩)) :=
    D.pairwise_disjoint ⟨q, hqD⟩ ⟨r, hrD⟩ (by
      intro hsub
      exact hqr (Subtype.ext_iff.mp hsub))
  exact ((residueClass_disjoint_iff hqpos hrpos
    (D.a ⟨q, hqD⟩) (D.a ⟨r, hrD⟩)).1 hres_disj) hmodG

/-- The family of remaining prime supports of surviving moduli. -/
def ChainState.remainingSupportFamily {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : Finset (Finset ℕ) :=
  S.Qsurv.image (fun q => remainingSupport S.productP q)

lemma ChainState.remainingSupportFamily_nonempty {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : S.remainingSupportFamily.Nonempty := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  exact ⟨remainingSupport S.productP q, Finset.mem_image.2 ⟨q, hq, rfl⟩⟩

lemma ChainState.remainingSupportFamily_card_le {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    S.remainingSupportFamily.card ≤ S.Qsurv.card := by
  rw [ChainState.remainingSupportFamily]
  exact Finset.card_image_le

lemma ChainState.remainingSupport_injOn_Qsurv {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    Set.InjOn (fun q => remainingSupport S.productP q) S.Qsurv := by
  intro q hq r hr hqr
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hrD : r ∈ D.Q := S.Qsurv_subset hr
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hrne : r ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 r hrD).1).ne'
  have hqsupp :
      primeSupport q = primeSupport S.productP ∪ remainingSupport S.productP q :=
    primeSupport_eq_union_of_dvd (S.exact_divides q hq) S.productP_pos.ne' hqne
  have hrsupp :
    primeSupport r = primeSupport S.productP ∪ remainingSupport S.productP r :=
    primeSupport_eq_union_of_dvd (S.exact_divides r hr) S.productP_pos.ne' hrne
  have hsupp : primeSupport q = primeSupport r := by
    change remainingSupport S.productP q = remainingSupport S.productP r at hqr
    rw [hqsupp, hrsupp, hqr]
  have hrad : rad q = rad r := by
    unfold rad
    rw [hsupp]
  exact D.rad_injective q hqD r hrD hrad

lemma ChainState.remainingSupportFamily_card_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    S.remainingSupportFamily.card = S.Qsurv.card := by
  rw [ChainState.remainingSupportFamily]
  exact Finset.card_image_of_injOn (fun q hq r hr hqr =>
    S.remainingSupport_injOn_Qsurv hq hr hqr)

/-- Survivors whose remaining support contains a fixed core. -/
def ChainState.coreSurvivors {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  S.Qsurv.filter fun q => C ⊆ remainingSupport S.productP q

/-- Exact prime-power block values attached to a fixed core. -/
def ChainState.coreBlocks {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  (S.coreSurvivors C).image (fun q => exactBlock C q)

/-- Weighted pigeonhole on exact block values carried by a fixed core. This
is the formal selection step for the paper's attained value `P_r`, before
the subsequent residue-class pigeonhole. -/
lemma ChainState.exists_coreBlock_weighted_share {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ)
    (hCore : (S.coreSurvivors C).Nonempty) :
    ∃ P ∈ S.coreBlocks C,
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) := by
  classical
  rw [ChainState.coreBlocks]
  exact exists_fiber_weighted_share (S.coreSurvivors C) (fun q => exactBlock C q)
    (fun P => (1 : ℝ) / ((hExp P : ℝ) ^ 2)) hCore (by
      intro P _hP
      exact hExp_inv_sq_pos P)

/-- Quotients `q / productP` for survivors carrying a fixed core. -/
def ChainState.coreQuotients {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) : Finset ℕ :=
  (S.coreSurvivors C).image (fun q => q / S.productP)

lemma ChainState.remainingSupportFamily_filter_subset_coreImage {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.remainingSupportFamily.filter fun A => C ⊆ A) ⊆
      (S.coreSurvivors C).image (fun q => remainingSupport S.productP q) := by
  intro A hA
  rw [ChainState.remainingSupportFamily] at hA
  rw [Finset.mem_filter] at hA
  rcases Finset.mem_image.mp hA.1 with ⟨q, hq, rfl⟩
  exact Finset.mem_image.2 ⟨q, by
    rw [ChainState.coreSurvivors, Finset.mem_filter]
    exact ⟨hq, hA.2⟩, rfl⟩

lemma ChainState.remainingSupportFamily_filter_card_le_coreSurvivors {N : ℕ}
    {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ) :
    (S.remainingSupportFamily.filter fun A => C ⊆ A).card ≤
      (S.coreSurvivors C).card := by
  exact (Finset.card_le_card (S.remainingSupportFamily_filter_subset_coreImage C)).trans
    Finset.card_image_le

lemma ChainState.quotient_injOn_Qsurv {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    Set.InjOn (fun q => q / S.productP) S.Qsurv := by
  intro q hq r hr hqr
  have hqmul := Nat.div_mul_cancel (S.exact_divides q hq)
  have hrmul := Nat.div_mul_cancel (S.exact_divides r hr)
  calc
    q = (q / S.productP) * S.productP := hqmul.symm
    _ = (r / S.productP) * S.productP := by
      exact congrArg (fun x => x * S.productP) hqr
    _ = r := hrmul

lemma ChainState.coreQuotients_card {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.coreQuotients C).card = (S.coreSurvivors C).card := by
  rw [ChainState.coreQuotients]
  exact Finset.card_image_of_injOn fun q hq r hr hqr =>
    S.quotient_injOn_Qsurv (Finset.mem_filter.1 hq).1
      (Finset.mem_filter.1 hr).1 hqr

lemma ChainState.coreQuotients_subset_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreQuotients C ⊆
      (Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W) := by
  intro n hn
  rw [ChainState.coreQuotients] at hn
  rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := (Finset.mem_filter.1 hq).1
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (S.productP_le_of_mem hqsurv) S.productP_pos),
      (Nat.div_le_self q S.productP).trans (D.modulus_upper q hqD)⟩,
    S.remainingSupport_card_eq hqsurv⟩

lemma ChainState.coreSurvivors_card_le_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    (S.coreSurvivors C).card ≤
      ((Finset.Icc 1 N).filter (fun n => omega n = D.K - S.W)).card := by
  rw [← S.coreQuotients_card C]
  exact Finset.card_le_card (S.coreQuotients_subset_omegaCount C)

lemma ChainState.coreSurvivors_card_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    (S.coreSurvivors C).card ≤
      Nat.floor
        ((N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) := by
  exact (S.coreSurvivors_card_le_omegaCount C).trans
    (hCount N D.K S.W le_rfl S.W_le_K D.K_bound)

lemma ChainState.coreSurvivors_card_real_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((S.coreSurvivors C).card : ℝ) ≤
      (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  apply nat_cast_le_of_le_floor
  · positivity
  · exact S.coreSurvivors_card_le_bfv_omega_count C ε hCount

lemma ChainState.coreSurvivors_subset {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreSurvivors C ⊆ S.Qsurv := by
  intro q hq
  exact (Finset.mem_filter.1 hq).1

lemma ChainState.core_subset_remainingSupport {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    C ⊆ remainingSupport S.productP q :=
  (Finset.mem_filter.1 hq).2

lemma ChainState.exactBlock_eq_quotient_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    exactBlock C q = exactBlock C (q / S.productP) := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  apply exactBlock_congr_on
  intro p hpC
  have hpRem : p ∈ remainingSupport S.productP q := hC hpC
  have hpNotP : p ∉ primeSupport S.productP := by
    intro hpP
    exact (Finset.disjoint_left.1 (S.selected_remaining_disjoint hqsurv)) hpP hpRem
  have hPzero : S.productP.factorization p = 0 := by
      unfold primeSupport at hpNotP
      exact Finsupp.notMem_support_iff.1 hpNotP
  rw [Nat.factorization_div (S.exact_divides q hqsurv)]
  simp [Finsupp.coe_tsub, hPzero]

lemma ChainState.quotient_pos_of_mem {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {q : ℕ} (hq : q ∈ S.Qsurv) :
    0 < q / S.productP := by
  exact Nat.div_pos (S.productP_le_of_mem hq) S.productP_pos

lemma ChainState.exactBlock_dvd_quotient_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    exactBlock C q ∣ q / S.productP := by
  rw [S.exactBlock_eq_quotient_of_core hq]
  exact exactBlock_dvd C (q / S.productP)

lemma ChainState.exactBlock_pos_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    0 < exactBlock C q := by
  exact Nat.pos_of_dvd_of_pos (S.exactBlock_dvd_quotient_of_core hq)
    (S.quotient_pos_of_mem (S.coreSurvivors_subset C hq))

lemma ChainState.primeSupport_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    primeSupport (exactBlock C q) = C := by
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  rw [S.exactBlock_eq_quotient_of_core hq]
  exact primeSupport_exactBlock
    (fun p hp => prime_of_mem_primeSupport (hC hp))
    hC

lemma ChainState.omega_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    omega (exactBlock C q) = C.card := by
  simp [omega, S.primeSupport_exactBlock_of_core hq]

lemma ChainState.product_mul_exactBlock_dvd_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    S.productP * exactBlock C q ∣ q := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  rcases S.exactBlock_dvd_quotient_of_core hq with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have hdiv := Nat.div_mul_cancel (S.exact_divides q hqsurv)
  calc
    q = q / S.productP * S.productP := hdiv.symm
    _ = exactBlock C q * t * S.productP := by rw [ht]
    _ = S.productP * exactBlock C q * t := by ring

lemma ChainState.productP_coprime_exactBlock_of_core {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {q : ℕ}
    (hq : q ∈ S.coreSurvivors C) :
    Nat.Coprime S.productP (exactBlock C q) := by
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hC : C ⊆ remainingSupport S.productP q :=
    S.core_subset_remainingSupport hq
  have hsupport : primeSupport (exactBlock C q) = C :=
    S.primeSupport_exactBlock_of_core hq
  refine coprime_of_disjoint_primeSupport S.productP_pos.ne'
    (S.exactBlock_pos_of_core hq).ne' ?_
  rw [hsupport]
  rw [Finset.disjoint_left]
  intro p hpP hpC
  exact (Finset.disjoint_left.1 (S.selected_remaining_disjoint hqsurv)) hpP (hC hpC)

lemma ChainState.coreBlock_pos {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : 0 < P := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.exactBlock_pos_of_core hq

lemma ChainState.coreBlock_coprime_productP {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : Nat.Coprime S.productP P := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.productP_coprime_exactBlock_of_core hq

lemma ChainState.coreBlock_omega_eq_card {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : omega P = C.card := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.omega_exactBlock_of_core hq

lemma ChainState.coreBlock_primeSupport_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : primeSupport P = C := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact S.primeSupport_exactBlock_of_core hq

lemma ChainState.product_mul_coreBlock_dvd {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P q : ℕ}
    (hq : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P) :
    S.productP * P ∣ q := by
  have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hq).1
  have hP : exactBlock C q = P := (Finset.mem_filter.1 hq).2
  simpa [hP] using S.product_mul_exactBlock_dvd_of_core hqcore

lemma ChainState.product_mul_coreBlock_no_selected_prime_remains
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P q : ℕ}
    (hq : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P) :
    ∀ p ∈ primeSupport (S.productP * P), p ∉ primeSupport (q / (S.productP * P)) := by
  intro p hpNew hpRem
  have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hq).1
  have hP : exactBlock C q = P := (Finset.mem_filter.1 hq).2
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hqcore
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hqne : q ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1).ne'
  have hPmem : P ∈ S.coreBlocks C := by
    rw [ChainState.coreBlocks]
    exact Finset.mem_image.2 ⟨q, hqcore, hP⟩
  have hcop : Nat.Coprime S.productP P := S.coreBlock_coprime_productP hPmem
  have hnewdvd : S.productP * P ∣ q := S.product_mul_coreBlock_dvd hq
  have hltNew : (S.productP * P).factorization p < q.factorization p :=
    (mem_remainingSupport_iff_factorization_lt hnewdvd).1 hpRem
  have hsupportNew :
      primeSupport (S.productP * P) = primeSupport S.productP ∪ primeSupport P :=
    primeSupport_mul_of_coprime hcop
  have hfacNew : (S.productP * P).factorization p =
      S.productP.factorization p + P.factorization p := by
    rw [Nat.factorization_mul_of_coprime hcop]
    rfl
  rw [hsupportNew, Finset.mem_union] at hpNew
  cases hpNew with
  | inl hpOld =>
      have hpNotRemOld : p ∉ primeSupport (q / S.productP) :=
        S.no_selected_prime_remains q hqsurv p hpOld
      have hnotltOld : ¬ S.productP.factorization p < q.factorization p := by
        intro hlt
        exact hpNotRemOld
          ((mem_remainingSupport_iff_factorization_lt (S.exact_divides q hqsurv)).2 hlt)
      have hleOld : S.productP.factorization p ≤ q.factorization p :=
        (Nat.factorization_le_iff_dvd S.productP_pos.ne' hqne).2
          (S.exact_divides q hqsurv) p
      have hq_le_old : q.factorization p ≤ S.productP.factorization p :=
        le_of_not_gt hnotltOld
      have hEqOld : S.productP.factorization p = q.factorization p :=
        le_antisymm hleOld hq_le_old
      have hpNotP : p ∉ primeSupport P :=
        (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hpOld
      have hPzero : P.factorization p = 0 := by
        unfold primeSupport at hpNotP
        exact Finsupp.notMem_support_iff.1 hpNotP
      rw [hfacNew, hPzero, add_zero, hEqOld] at hltNew
      exact lt_irrefl _ hltNew
  | inr hpP =>
      have hsupportP : primeSupport P = C := by
        rw [← hP]
        exact S.primeSupport_exactBlock_of_core hqcore
      have hpC : p ∈ C := by
        simpa [hsupportP] using hpP
      have hpNotOld : p ∉ primeSupport S.productP := by
        intro hpOld
        exact (Finset.disjoint_left.1 (primeSupport_disjoint_of_coprime hcop)) hpOld hpP
      have hOldzero : S.productP.factorization p = 0 := by
        unfold primeSupport at hpNotOld
        exact Finsupp.notMem_support_iff.1 hpNotOld
      have hCprime : ∀ r ∈ C, Nat.Prime r := by
        intro r hr
        exact prime_of_mem_primeSupport (S.core_subset_remainingSupport hqcore hr)
      have hPfac : P.factorization p = q.factorization p := by
        rw [← hP]
        exact factorization_exactBlock_of_mem hCprime hpC
      rw [hfacNew, hOldzero, zero_add, hPfac] at hltNew
      exact lt_irrefl _ hltNew

lemma ChainState.coreBlock_card_le_remaining {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : C.card ≤ D.K - S.W := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  exact (Finset.card_le_card (S.core_subset_remainingSupport hq)).trans_eq
    (S.remainingSupport_card_eq (S.coreSurvivors_subset C hq))

lemma ChainState.omega_product_mul_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    omega (S.productP * P) = S.W + C.card := by
  rw [omega_mul_of_coprime (S.coreBlock_coprime_productP hP), ← S.W_eq,
    S.coreBlock_omega_eq_card hP]

lemma ChainState.selectedFiber_card_real_le_bfv_omega_count_div
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.coreBlocks C) (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
      ((N / (S.productP * P) : ℕ) : ℝ) *
        Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  classical
  let T : Finset ℕ := (S.coreSurvivors C).filter fun q => exactBlock C q = P
  let dP : ℕ := S.productP * P
  let quotient : ℕ → ℕ := fun q => q / dP
  have hdP_pos : 0 < dP := by
    dsimp [dP]
    exact Nat.mul_pos S.productP_pos (S.coreBlock_pos hP)
  have hWle : S.W + C.card ≤ D.K := by
    have hcard := S.coreBlock_card_le_remaining hP
    have hWK := S.W_le_K
    omega
  have hinj : Set.InjOn quotient T := by
    intro q hq r hr hqr
    have hq_dvd : dP ∣ q := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd (by simpa [T] using hq)
    have hr_dvd : dP ∣ r := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd (by simpa [T] using hr)
    calc
      q = quotient q * dP := (Nat.div_mul_cancel hq_dvd).symm
      _ = quotient r * dP := by rw [hqr]
      _ = r := Nat.div_mul_cancel hr_dvd
  have hsubset :
      T.image quotient ⊆
        (Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card)) := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨q, hqT, rfl⟩
    have hqT' : q ∈ (S.coreSurvivors C).filter fun q => exactBlock C q = P := by
      simpa [T] using hqT
    have hqcore : q ∈ S.coreSurvivors C := (Finset.mem_filter.1 hqT').1
    have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hqcore
    have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (D.admissible.1 q hqD).1
    have hqne : q ≠ 0 := hqpos.ne'
    have hdvd : dP ∣ q := by
      dsimp [dP]
      exact S.product_mul_coreBlock_dvd hqT'
    have hdisj : Disjoint (primeSupport dP) (primeSupport (q / dP)) := by
      rw [Finset.disjoint_left]
      intro p hp hqrem
      exact S.product_mul_coreBlock_no_selected_prime_remains hqT' p (by simpa [dP] using hp)
        (by simpa [dP] using hqrem)
    have homega :
        omega (q / dP) = D.K - (S.W + C.card) := by
      calc
        omega (q / dP) = omega q - omega dP :=
          omega_div_eq_sub_omega_of_dvd hdvd hdP_pos.ne' hqne hdisj
        _ = D.K - (S.W + C.card) := by
          rw [D.omega_eq q hqD, show omega dP = S.W + C.card by
            dsimp [dP]
            exact S.omega_product_mul_coreBlock hP]
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hqpos hdvd) hdP_pos),
      Nat.div_le_div_right (D.modulus_upper q hqD)⟩, homega⟩
  have hcard : T.card ≤
      ((Finset.Icc 1 (N / dP)).filter (fun n => omega n = D.K - (S.W + C.card))).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsubset
  have hcount := hCount (N / dP) D.K (S.W + C.card) (Nat.div_le_self N dP) hWle D.K_bound
  dsimp only at hcount
  have hfloor :
      T.card ≤ Nat.floor
        (((N / dP : ℕ) : ℝ) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ)))) :=
    hcard.trans hcount
  simpa [T, dP] using nat_cast_le_of_le_floor (by positivity) hfloor

lemma ChainState.selectedFiber_card_real_le_bfv_omega_count
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} (hP : P ∈ S.coreBlocks C) (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
      ((N : ℝ) / (S.productP * P : ℝ)) *
        Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
  have hdiv := S.selectedFiber_card_real_le_bfv_omega_count_div hP ε hCount
  have hquot :
      ((N / (S.productP * P) : ℕ) : ℝ) ≤ (N : ℝ) / (S.productP * P : ℝ) :=
    by
      simpa [Nat.cast_mul] using
        (Nat.cast_div_le (m := N) (n := S.productP * P) : ((N / (S.productP * P) : ℕ) : ℝ) ≤
          (N : ℝ) / ((S.productP * P : ℕ) : ℝ))
  have hfactor_nonneg :
      0 ≤ Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
        Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) := by
    positivity
  calc
    ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ)
        ≤ ((N / (S.productP * P) : ℕ) : ℝ) *
            Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
            Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
              Real.log (Real.log (N : ℝ))) := hdiv
    _ = ((N / (S.productP * P) : ℕ) : ℝ) *
            (Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
              Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ)))) := by ring
    _ ≤ ((N : ℝ) / (S.productP * P : ℝ)) *
            (Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
              Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
                Real.log (Real.log (N : ℝ)))) := by
          exact mul_le_mul_of_nonneg_right hquot hfactor_nonneg
    _ = ((N : ℝ) / (S.productP * P : ℝ)) *
            Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
            Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
              Real.log (Real.log (N : ℝ))) := by ring

lemma ChainState.W_add_coreBlock_card_le_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : S.W + C.card ≤ D.K := by
  have hcard := S.coreBlock_card_le_remaining hP
  have hW := S.W_le_K
  omega

lemma ChainState.productP_eq_of_W_eq_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hW : S.W = D.K) {q : ℕ} (hq : q ∈ S.Qsurv) :
    S.productP = q := by
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hqdivpos : q / S.productP ≠ 0 := (S.quotient_pos_of_mem hq).ne'
  have hremcard : (remainingSupport S.productP q).card = 0 := by
    rw [S.remainingSupport_card_eq hq, hW]
    simp
  have homega : omega (q / S.productP) = 0 := by
    simpa [remainingSupport, omega] using hremcard
  have hquot : q / S.productP = 1 := eq_one_of_omega_eq_zero hqdivpos homega
  have hdiv := Nat.div_mul_cancel (S.exact_divides q hq)
  calc
    S.productP = 1 * S.productP := by simp
    _ = q / S.productP * S.productP := by rw [hquot]
    _ = q := hdiv

lemma ChainState.productP_lower_of_W_eq_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hW : S.W = D.K) :
    (N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) := by
  rcases S.Qsurv_nonempty with ⟨q, hq⟩
  have hqD : q ∈ D.Q := S.Qsurv_subset hq
  have hpq := S.productP_eq_of_W_eq_K hW hq
  rw [hpq]
  exact D.modulus_lower q hqD

lemma ChainState.pairwise_cons_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : (P :: S.blocks).Pairwise Nat.Coprime := by
  rw [List.pairwise_cons]
  constructor
  · intro B hB
    exact Nat.Coprime.of_dvd_right (S.block_dvd_productP hB)
      (S.coreBlock_coprime_productP hP).symm
  · exact S.pairwise_coprime

lemma ChainState.extend_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ} {Qnext : Finset ℕ}
    (hP : P ∈ S.coreBlocks C)
    (hQnext_nonempty : Qnext.Nonempty)
    (hQnext_subset : Qnext ⊆ (S.coreSurvivors C).filter fun q => exactBlock C q = P)
    (hResiduesP :
      ∀ qi ∈ Qnext, ∀ rj ∈ Qnext,
        ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
          D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) :
    ∃ S' : ChainState N D,
      S'.blocks = P :: S.blocks ∧ S'.r = S.r + 1 ∧ S'.productP = P * S.productP ∧
        S'.Qsurv = Qnext ∧ S'.W = S.W + C.card := by
  classical
  refine ⟨{
    r := S.r + 1
    blocks := P :: S.blocks
    blocks_length := by simp [S.blocks_length]
    Qsurv := Qnext
    Qsurv_subset := ?_
    Qsurv_nonempty := hQnext_nonempty
    W := S.W + C.card
    productP := P * S.productP
    product_eq := by simp [S.product_eq]
    blocks_pos := ?_
    productP_pos := ?_
    pairwise_coprime := S.pairwise_cons_coreBlock hP
    exact_divides := ?_
    no_selected_prime_remains := ?_
    residues_agree := ?_
    W_eq := ?_
    W_le_K := S.W_add_coreBlock_card_le_K hP
  }, rfl, rfl, rfl, rfl, rfl⟩
  · intro q hq
    exact S.Qsurv_subset (S.coreSurvivors_subset C
      (Finset.mem_filter.1 (hQnext_subset hq)).1)
  · intro B hB
    rw [List.mem_cons] at hB
    cases hB with
    | inl h =>
        subst B
        exact S.coreBlock_pos hP
    | inr h => exact S.blocks_pos B h
  · exact mul_pos (S.coreBlock_pos hP) S.productP_pos
  · intro q hq
    have hfiber := hQnext_subset hq
    have hdvd := S.product_mul_coreBlock_dvd hfiber
    simpa [Nat.mul_comm] using hdvd
  · intro q hq p hp
    have hfiber := hQnext_subset hq
    have hno := S.product_mul_coreBlock_no_selected_prime_remains hfiber p
    simpa [Nat.mul_comm] using hno (by simpa [Nat.mul_comm] using hp)
  · intro qi hqi rj hrj hqiD hrjD
    have hqicore : qi ∈ S.coreSurvivors C :=
      (Finset.mem_filter.1 (hQnext_subset hqi)).1
    have hrjcore : rj ∈ S.coreSurvivors C :=
      (Finset.mem_filter.1 (hQnext_subset hrj)).1
    have hqiSurv : qi ∈ S.Qsurv := S.coreSurvivors_subset C hqicore
    have hrjSurv : rj ∈ S.Qsurv := S.coreSurvivors_subset C hrjcore
    have hOld := S.residues_agree qi hqiSurv rj hrjSurv hqiD hrjD
    have hNew := hResiduesP qi hqi rj hrj hqiD hrjD
    have hcopInt : (S.productP : ℤ).natAbs.Coprime (P : ℤ).natAbs := by
      simpa using S.coreBlock_coprime_productP hP
    have hBoth :
        D.a ⟨qi, hqiD⟩ ≡ D.a ⟨rj, hrjD⟩ [ZMOD (S.productP : ℤ)] ∧
        D.a ⟨qi, hqiD⟩ ≡ D.a ⟨rj, hrjD⟩ [ZMOD (P : ℤ)] := ⟨hOld, hNew⟩
    have hMul := (Int.modEq_and_modEq_iff_modEq_mul hcopInt).1 hBoth
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hMul
  · rw [Nat.mul_comm]
    exact (S.omega_product_mul_coreBlock hP).symm

lemma ChainState.exists_residue_subfamily {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    ∃ Qnext : Finset ℕ,
      Qnext.Nonempty ∧
      Qnext ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      (∀ qi ∈ Qnext, ∀ rj ∈ Qnext,
        ∀ hqi : qi ∈ D.Q, ∀ hrj : rj ∈ D.Q,
          D.a ⟨qi, hqi⟩ ≡ D.a ⟨rj, hrj⟩ [ZMOD (P : ℤ)]) ∧
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ) ≤ (Qnext.card : ℝ) := by
  classical
  let T : Finset ℕ := (S.coreSurvivors C).filter fun q => exactBlock C q = P
  let residue : ℕ → ZMod P :=
    fun q => if hq : q ∈ D.Q then (D.a ⟨q, hq⟩ : ZMod P) else 0
  have hPpos : 0 < P := S.coreBlock_pos hP
  haveI : NeZero P := ⟨hPpos.ne'⟩
  have hTnonempty : T.Nonempty := by
    dsimp [T]
    rw [ChainState.coreBlocks] at hP
    exact fiber_nonempty_of_mem_image (S := S.coreSurvivors C)
      (B := fun q => exactBlock C q) hP
  rcases exists_zmod_fiber_card_div_le T P residue hTnonempty with ⟨b, hb⟩
  let Qnext : Finset ℕ := T.filter fun q => residue q = b
  refine ⟨Qnext, ?_, ?_, ?_, ?_⟩
  · have hratio_pos : 0 < (T.card : ℝ) / (P : ℝ) := by
      have hTcard : 0 < (T.card : ℝ) := by exact_mod_cast hTnonempty.card_pos
      have hPreal : 0 < (P : ℝ) := by exact_mod_cast hPpos
      exact div_pos hTcard hPreal
    have hQreal : 0 < (Qnext.card : ℝ) := lt_of_lt_of_le hratio_pos hb
    exact Finset.card_pos.1 (by exact_mod_cast hQreal)
  · intro q hq
    exact (Finset.mem_filter.1 hq).1
  · intro qi hqi rj hrj hqiD hrjD
    have hqiResidue : residue qi = b := (Finset.mem_filter.1 hqi).2
    have hrjResidue : residue rj = b := (Finset.mem_filter.1 hrj).2
    have hqiCast : ((D.a ⟨qi, hqiD⟩ : ℤ) : ZMod P) = b := by
      simpa [residue, hqiD] using hqiResidue
    have hrjCast : ((D.a ⟨rj, hrjD⟩ : ℤ) : ZMod P) = b := by
      simpa [residue, hrjD] using hrjResidue
    have hcast : ((D.a ⟨qi, hqiD⟩ : ℤ) : ZMod P) =
        ((D.a ⟨rj, hrjD⟩ : ℤ) : ZMod P) := hqiCast.trans hrjCast.symm
    exact (ZMod.intCast_eq_intCast_iff
      (D.a ⟨qi, hqiD⟩) (D.a ⟨rj, hrjD⟩) P).1 hcast
  · simpa [T, Qnext] using hb

lemma ChainState.exists_extended_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    ∃ S' : ChainState N D,
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) := by
  rcases S.exists_residue_subfamily hP with
    ⟨Qnext, hQnext_nonempty, hQnext_subset, hResiduesP, hcard⟩
  rcases S.extend_coreBlock hP hQnext_nonempty hQnext_subset hResiduesP with
    ⟨S', hblocks, hr, hprod, hQsurv, hW⟩
  have hsubset : S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) := by
    intro q hq
    rw [hQsurv] at hq
    exact hQnext_subset hq
  exact ⟨S', hblocks, hr, hprod, hsubset, Finset.card_le_card hsubset, hW,
    by simpa [hQsurv] using hcard⟩

lemma ChainState.exists_weighted_extended_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    ∃ P : ℕ, ∃ S' : ChainState N D,
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) := by
  rcases S.exists_coreBlock_weighted_share C hCore with ⟨P, hP, hshare⟩
  rcases S.exists_extended_coreBlock hP with
    ⟨S', hblocks, hr, hprod, hQsubset, hQcard_le, hW, hcard⟩
  refine ⟨P, S', hP, hblocks, hr, hprod, hQsubset, hQcard_le, hW, hshare, ?_⟩
  have hPreal_nonneg : 0 ≤ (P : ℝ) := by positivity
  have hdiv_share :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤
        ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) /
          (P : ℝ)) := by
    exact div_le_div_of_nonneg_right hshare hPreal_nonneg
  exact hdiv_share.trans hcard

lemma ChainState.coreBlocks_subset_omegaCount {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) :
    S.coreBlocks C ⊆
      (Finset.Icc 1 N).filter (fun n => omega n = C.card) := by
  intro B hB
  rw [ChainState.coreBlocks] at hB
  rcases Finset.mem_image.mp hB with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hblock_le_quotient :
      exactBlock C q ≤ q / S.productP :=
    Nat.le_of_dvd (S.quotient_pos_of_mem hqsurv) (S.exactBlock_dvd_quotient_of_core hq)
  have hblock_le_N : exactBlock C q ≤ N := by
    exact hblock_le_quotient.trans ((Nat.div_le_self q S.productP).trans (D.modulus_upper q hqD))
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.succ_le_of_lt (S.exactBlock_pos_of_core hq), hblock_le_N⟩,
    S.omega_exactBlock_of_core hq⟩

lemma ChainState.coreBlock_le_N {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : P ≤ N := by
  have hmem := S.coreBlocks_subset_omegaCount C hP
  exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hmem).1).2

lemma ChainState.coreBlock_hExp_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) :
    (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, rfl⟩
  have hqsurv : q ∈ S.Qsurv := S.coreSurvivors_subset C hq
  have hqD : q ∈ D.Q := S.Qsurv_subset hqsurv
  have hle_nat : hExp (exactBlock C q) ≤ hExp q := hExp_exactBlock_le_hExp C q
  have hle_real : (hExp (exactBlock C q) : ℝ) ≤ (hExp q : ℝ) := by
    exact_mod_cast hle_nat
  exact hle_real.trans (D.hExp_bound q hqD)

lemma ChainState.coreBlock_card_le_K_of_nonempty {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) : C.card ≤ D.K := by
  rcases hCore with ⟨q, hq⟩
  have hle := Finset.card_le_card (S.core_subset_remainingSupport hq)
  have heq := S.remainingSupport_card_eq (S.coreSurvivors_subset C hq)
  omega

lemma ChainState.coreBlock_card_bound_real {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    (C.card : ℝ) ≤ 3 * Mscale N := by
  have hCK : (C.card : ℝ) ≤ (D.K : ℝ) := by
    exact_mod_cast S.coreBlock_card_le_K_of_nonempty hCore
  exact hCK.trans D.K_bound

lemma ChainState.coreBlocks_card_le_bfv_omega_count {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) (ε : ℝ)
    (hCore : (S.coreSurvivors C).Nonempty)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    (S.coreBlocks C).card ≤
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)) := by
  have hsubset := S.coreBlocks_subset_omegaCount C
  have hcard : (S.coreBlocks C).card ≤
      ((Finset.Icc 1 N).filter (fun n => omega n = C.card)).card :=
    Finset.card_le_card hsubset
  have hcount := hCount N C.card 0 le_rfl (Nat.zero_le _) (S.coreBlock_card_bound_real hCore)
  dsimp only at hcount
  have hsimp :
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((0 : ℝ) / 2) * Real.log (Real.log (N : ℝ)))) =
      Nat.floor
        ((N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N)) := by
    simp
  exact hcard.trans (by simpa [hsimp] using hcount)

lemma ChainState.coreBlocks_card_real_le_bfv_omega_count {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (C : Finset ℕ) (ε : ℝ)
    (hCore : (S.coreSurvivors C).Nonempty)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ((S.coreBlocks C).card : ℝ) ≤
      (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) := by
  apply nat_cast_le_of_le_floor
  · positivity
  · exact S.coreBlocks_card_le_bfv_omega_count C ε hCore hCount

lemma ChainState.remainingSupportFamily_uniform {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    UniformFamily S.remainingSupportFamily (D.K - S.W) := by
  intro A hA
  rw [ChainState.remainingSupportFamily] at hA
  rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
  exact S.remainingSupport_card_eq hq

lemma ChainState.remainingSupportFamily_intersecting {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    ∀ A ∈ S.remainingSupportFamily, ∀ B ∈ S.remainingSupportFamily,
      A ≠ B → ¬ Disjoint A B := by
  intro A hA B hB hAB
  rw [ChainState.remainingSupportFamily] at hA hB
  rcases Finset.mem_image.mp hA with ⟨q, hq, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨r, hr, rfl⟩
  exact S.remainingSupport_not_disjoint_of_ne hq hr (by
    intro hqr
    subst r
    exact hAB rfl)

lemma ChainState.remainingSupportFamily_rank_pos_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) : 1 ≤ D.K - S.W := by
  omega

lemma ChainState.remainingSupportFamily_rank_le_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) : D.K - S.W ≤ D.K :=
  Nat.sub_le D.K S.W

lemma ChainState.remainingSupportFamily_denseCoreData {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    S.remainingSupportFamily.Nonempty ∧
      1 ≤ D.K - S.W ∧
      D.K - S.W ≤ D.K ∧
      UniformFamily S.remainingSupportFamily (D.K - S.W) ∧
      (∀ A ∈ S.remainingSupportFamily, ∀ B ∈ S.remainingSupportFamily,
        A ≠ B → ¬ Disjoint A B) :=
  ⟨S.remainingSupportFamily_nonempty,
    S.remainingSupportFamily_rank_pos_of_room hRoom,
    S.remainingSupportFamily_rank_le_K,
    S.remainingSupportFamily_uniform,
    S.remainingSupportFamily_intersecting⟩

/-- A fixed dense-core constant supplied by the spread-core input. Keeping it
fixed is important for iterating the chain. This file only needs the
`α = ℕ` instance, so the universe is fixed to avoid polymorphic choice
metavariables. -/
noncomputable def denseCoreConstant : ℝ :=
  Classical.choose (dense_core_from_spread.{0})

lemma denseCoreConstant_pos : 0 < denseCoreConstant :=
  (Classical.choose_spec (dense_core_from_spread.{0})).1

lemma dense_core_from_spread_fixed_nat
    (A : Finset (Finset ℕ)) (k K : ℕ) :
    A.Nonempty →
    1 ≤ k → k ≤ K →
    UniformFamily A k →
    (∀ S ∈ A, ∀ T ∈ A, S ≠ T → ¬ Disjoint S T) →
    ∃ C : Finset ℕ,
      C.Nonempty ∧
      ((A.filter fun S => C ⊆ S).card : ℝ) >
        (A.card : ℝ) /
          (denseCoreConstant * Real.log (Real.exp 1 * (K : ℝ))) ^ C.card :=
  (Classical.choose_spec (dense_core_from_spread.{0})).2 A k K

noncomputable def chainKappa {N : ℕ} (D : PrunedData N) : ℝ :=
  denseCoreConstant * Real.log (Real.exp 1 * (D.K : ℝ))

noncomputable def chainLambda {N : ℕ} (D : PrunedData N) : ℝ :=
  2 * chainKappa D

lemma chainKappa_pos {N : ℕ} (D : PrunedData N) : 0 < chainKappa D := by
  have hKreal : 1 ≤ (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_ge : Real.exp 1 ≤ Real.exp 1 * (D.K : ℝ) := by
    nlinarith [Real.exp_pos 1, hKreal]
  have hlog_ge_one : 1 ≤ Real.log (Real.exp 1 * (D.K : ℝ)) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) harg_ge
    simpa using hlog
  exact mul_pos denseCoreConstant_pos (zero_lt_one.trans_le hlog_ge_one)

lemma chainLambda_pos {N : ℕ} (D : PrunedData N) : 0 < chainLambda D := by
  dsimp [chainLambda]
  exact mul_pos (by norm_num) (chainKappa_pos D)

lemma ChainState.exists_dense_core_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∃ C : Finset ℕ,
        C.Nonempty ∧
        ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
          (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases dense_core_from_spread with ⟨C0, hC0, hcore⟩
  rcases S.remainingSupportFamily_denseCoreData hRoom with
    ⟨hA, hk, hkK, hUniform, hIntersect⟩
  rcases hcore S.remainingSupportFamily (D.K - S.W) D.K
      hA hk hkK hUniform hIntersect with ⟨C, hC⟩
  exact ⟨C0, hC0, C, hC⟩

lemma ChainState.exists_dense_core_fixed_of_room {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C : Finset ℕ,
      C.Nonempty ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.remainingSupportFamily_denseCoreData hRoom with
    ⟨hA, hk, hkK, hUniform, hIntersect⟩
  rcases dense_core_from_spread_fixed_nat S.remainingSupportFamily (D.K - S.W) D.K
      hA hk hkK hUniform hIntersect with ⟨C, hC⟩
  exact ⟨C, by simpa [chainKappa] using hC⟩

lemma ChainState.coreSurvivors_nonempty_of_filter_card_pos
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ)) :
    (S.coreSurvivors C).Nonempty := by
  have hfilter_nat : 0 < (S.remainingSupportFamily.filter fun A => C ⊆ A).card := by
    exact_mod_cast hpos
  have hle := S.remainingSupportFamily_filter_card_le_coreSurvivors C
  have hcore_card : 0 < (S.coreSurvivors C).card := lt_of_lt_of_le hfilter_nat hle
  exact Finset.card_pos.1 hcore_card

lemma ChainState.exists_dense_core_with_survivor_of_room
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∃ C : Finset ℕ,
        C.Nonempty ∧ (S.coreSurvivors C).Nonempty ∧
        ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
          (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases S.exists_dense_core_of_room hRoom with ⟨C0, hC0, C, hC, hbound⟩
  have hKreal : 1 ≤ (D.K : ℝ) := by exact_mod_cast D.K_pos
  have harg_ge : Real.exp 1 ≤ Real.exp 1 * (D.K : ℝ) := by
    nlinarith [Real.exp_pos 1, hKreal]
  have hlog_ge_one : 1 ≤ Real.log (Real.exp 1 * (D.K : ℝ)) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) harg_ge
    simpa using hlog
  have hbase_nonneg : 0 ≤ C0 * Real.log (Real.exp 1 * (D.K : ℝ)) := by
    exact mul_nonneg hC0.le (zero_le_one.trans hlog_ge_one)
  have hden_nonneg :
      0 ≤ (S.remainingSupportFamily.card : ℝ) /
            (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
    exact div_nonneg (by positivity) (pow_nonneg hbase_nonneg _)
  have hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ) :=
    lt_of_le_of_lt hden_nonneg hbound
  exact ⟨C0, hC0, C, hC, S.coreSurvivors_nonempty_of_filter_card_pos hpos, hbound⟩

lemma ChainState.exists_dense_core_fixed_with_survivor_of_room
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (hRoom : S.W < D.K) :
    ∃ C : Finset ℕ,
      C.Nonempty ∧ (S.coreSurvivors C).Nonempty ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.exists_dense_core_fixed_of_room hRoom with ⟨C, hC, hbound⟩
  have hbase_nonneg : 0 ≤ chainKappa D := (chainKappa_pos D).le
  have hden_nonneg :
      0 ≤ (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
    exact div_nonneg (by positivity) (pow_nonneg hbase_nonneg _)
  have hpos : 0 < (((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℕ) : ℝ) :=
    lt_of_le_of_lt hden_nonneg hbound
  exact ⟨C, hC, S.coreSurvivors_nonempty_of_filter_card_pos hpos, hbound⟩

lemma ChainState.coreSurvivors_card_gt_of_dense_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ} {A : ℝ}
    (hbound : A < ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ)) :
    A < ((S.coreSurvivors C).card : ℝ) := by
  have hle : ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ) ≤
      ((S.coreSurvivors C).card : ℝ) := by
    exact_mod_cast S.remainingSupportFamily_filter_card_le_coreSurvivors C
  exact hbound.trans_le hle

lemma ChainState.coreSurvivors_card_gt_qsurv_div_of_dense_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ} {Λ : ℝ}
    (hbound :
      ((S.remainingSupportFamily.card : ℝ) / Λ ^ C.card) <
        ((S.remainingSupportFamily.filter fun B => C ⊆ B).card : ℝ)) :
    ((S.Qsurv.card : ℝ) / Λ ^ C.card) <
      ((S.coreSurvivors C).card : ℝ) := by
  have h := S.coreSurvivors_card_gt_of_dense_bound hbound
  simpa [S.remainingSupportFamily_card_eq] using h

lemma ChainState.coreBlocks_nonempty_of_coreSurvivors
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) : (S.coreBlocks C).Nonempty := by
  rw [ChainState.coreBlocks]
  exact hCore.image _

lemma ChainState.coreBlocks_weight_sum_pos
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hCore : (S.coreSurvivors C).Nonempty) :
    0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) := by
  exact Finset.sum_pos (fun B _hB => hExp_inv_sq_pos B)
    (S.coreBlocks_nonempty_of_coreSurvivors hCore)

lemma ChainState.coreBlocks_weight_sum_le_card
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) (C : Finset ℕ) :
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
      (S.coreBlocks C).card := by
  calc
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        ∑ _B ∈ S.coreBlocks C, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun B _hB => hExp_inv_sq_le_one B)
    _ = (S.coreBlocks C).card := by simp

lemma ChainState.coreBlocks_weight_sum_le_two_pow_card
    {N : ℕ} {D : PrunedData N} (S : ChainState N D) {C : Finset ℕ}
    (hC : C.Nonempty) :
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ C.card := by
  classical
  let Index := {p : ℕ // p ∈ C}
  let E : Finset (Index → ℕ) :=
    Fintype.piFinset fun _ : Index => Finset.range N
  let vec : ℕ → Index → ℕ := fun B p => B.factorization p.1 - 1
  let term : (Index → ℕ) → ℝ :=
    fun e => ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)
  have hvec_mem : ∀ B ∈ S.coreBlocks C, vec B ∈ E := by
    intro B hB
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    have hsupport : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hpSupport : p.1 ∈ primeSupport B := by
      simp [hsupport, p.2]
    have hBne : B ≠ 0 := by
      intro hzero
      subst B
      simp [primeSupport] at hpSupport
    have hfac_pos : 1 ≤ B.factorization p.1 := by
      unfold primeSupport at hpSupport
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
    have hfac_le_N : B.factorization p.1 ≤ N := by
      exact (Nat.factorization_lt p.1 hBne).le.trans (S.coreBlock_le_N hB)
    dsimp [vec]
    omega
  have hvec_inj : Set.InjOn vec (S.coreBlocks C) := by
    intro B hB R hR hBR
    have hsupportB : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hsupportR : primeSupport R = C := S.coreBlock_primeSupport_eq hR
    have hBne : B ≠ 0 := by
      rcases hC with ⟨p, hp⟩
      have hpSupport : p ∈ primeSupport B := by simpa [hsupportB] using hp
      intro hzero
      subst B
      simp [primeSupport] at hpSupport
    have hRne : R ≠ 0 := by
      rcases hC with ⟨p, hp⟩
      have hpSupport : p ∈ primeSupport R := by simpa [hsupportR] using hp
      intro hzero
      subst R
      simp [primeSupport] at hpSupport
    apply Nat.eq_of_factorization_eq hBne hRne
    intro p
    by_cases hp : p ∈ C
    · have hcoord := congrFun hBR ⟨p, hp⟩
      dsimp [vec] at hcoord
      have hBpos : 1 ≤ B.factorization p := by
        have hpSupport : p ∈ primeSupport B := by simpa [hsupportB] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      have hRpos : 1 ≤ R.factorization p := by
        have hpSupport : p ∈ primeSupport R := by simpa [hsupportR] using hp
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      omega
    · have hpB : p ∉ primeSupport B := by simpa [hsupportB] using hp
      have hpR : p ∉ primeSupport R := by simpa [hsupportR] using hp
      rw [Finsupp.notMem_support_iff.1 hpB, Finsupp.notMem_support_iff.1 hpR]
  have hterm_eq :
      ∀ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) = term (vec B) := by
    intro B hB
    have hsupport : primeSupport B = C := S.coreBlock_primeSupport_eq hB
    have hhexp :
        hExp B = ∏ p : Index, B.factorization p.1 := by
      calc
        hExp B = ∏ p ∈ C, B.factorization p := by
          simp [hExp, hsupport]
        _ = ∏ p : Index, B.factorization p.1 := by
          rw [Finset.prod_coe_sort]
    have hsucc : ∀ p : Index, vec B p + 1 = B.factorization p.1 := by
      intro p
      have hpSupport : p.1 ∈ primeSupport B := by simp [hsupport, p.2]
      have hpos : 1 ≤ B.factorization p.1 := by
        unfold primeSupport at hpSupport
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpSupport))
      dsimp [vec]
      omega
    rw [hhexp, one_div_sq_nat_prod]
    dsimp [term]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [hsucc p]
  calc
    (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))
        = ∑ B ∈ S.coreBlocks C, term (vec B) := by
            apply Finset.sum_congr rfl
            intro B hB
            exact hterm_eq B hB
    _ = ∑ e ∈ (S.coreBlocks C).image vec, term e := by
            rw [Finset.sum_image]
            intro B hB R hR hEq
            exact hvec_inj hB hR hEq
    _ ≤ ∑ e ∈ E, term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro e he
                rcases Finset.mem_image.mp he with ⟨B, hB, rfl⟩
                exact hvec_mem B hB)
              (by
                intro e _heE _heNot
                dsimp [term]
                positivity)
    _ = ∏ _p : Index,
          ∑ ν ∈ Finset.range N, (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2) := by
            change
              (∑ e ∈ Fintype.piFinset (fun _ : Index => Finset.range N),
                ∏ p : Index, (1 : ℝ) / (((e p + 1 : ℕ) : ℝ) ^ 2)) =
              ∏ _p : Index,
                ∑ ν ∈ Finset.range N, (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)
            exact
              (Finset.sum_prod_piFinset
                (ι := Index) (κ := ℕ) (R := ℝ)
                (s := Finset.range N)
                (g := fun _p ν => (1 : ℝ) / (((ν + 1 : ℕ) : ℝ) ^ 2)))
    _ ≤ ∏ _p : Index, (2 : ℝ) := by
            exact Finset.prod_le_prod
              (s := (Finset.univ : Finset Index))
              (fun _p _hp => by positivity)
              (fun _p _hp => by
                simpa [Nat.cast_add, Nat.cast_one] using sum_inv_sq_range_le_two N)
    _ = (2 : ℝ) ^ C.card := by
            simp [Index]

/-- Prefix-omega sum for a newest-first list of selected blocks. Since the
chain constructor prepends the new block, the prefix before the head is the
product of the tail. -/
noncomputable def chainTFromBlocks : List ℕ → ℕ
  | [] => 0
  | _P :: Ps => omega (Ps.foldr (· * ·) 1) + chainTFromBlocks Ps

/-- The accumulated `T = ∑ W_{r-1}` along a chain, computed from the stored
block list. -/
noncomputable def chainT {N : ℕ} {D : PrunedData N} (S : ChainState N D) : ℕ :=
  chainTFromBlocks S.blocks

private lemma chainTFromBlocks_le_length_mul_omega_foldr
    (blocks : List ℕ) (hpos : ∀ P ∈ blocks, 0 < P) :
    chainTFromBlocks blocks ≤ blocks.length * omega (blocks.foldr (· * ·) 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      have hPs_pos : ∀ B ∈ Ps, 0 < B := by
        intro B hB
        exact hpos B (by simp [hB])
      have htail_le_full :
          omega (Ps.foldr (· * ·) 1) ≤ omega (P * Ps.foldr (· * ·) 1) := by
        apply omega_le_of_dvd
        · exact dvd_mul_left (Ps.foldr (· * ·) 1) P
        · exact (Nat.mul_pos (hpos P (by simp)) (List.foldr_mul_pos hPs_pos)).ne'
      calc
        omega (Ps.foldr (· * ·) 1) + chainTFromBlocks Ps
            ≤ omega (P * Ps.foldr (· * ·) 1) +
                Ps.length * omega (Ps.foldr (· * ·) 1) := by
              exact Nat.add_le_add htail_le_full (ih hPs_pos)
        _ ≤ omega (P * Ps.foldr (· * ·) 1) +
                Ps.length * omega (P * Ps.foldr (· * ·) 1) := by
              exact Nat.add_le_add_left
                (Nat.mul_le_mul_left Ps.length htail_le_full) _
        _ = (Ps.length + 1) * omega (P * Ps.foldr (· * ·) 1) := by
              rw [Nat.add_mul, Nat.one_mul]
              omega

private lemma chainTFromBlocks_real_quadratic_bound
    (blocks : List ℕ)
    (hpair : blocks.Pairwise Nat.Coprime)
    (homega_pos : ∀ P ∈ blocks, 1 ≤ omega P) :
    ((chainTFromBlocks blocks : ℝ) * 2) ≤
      2 * (blocks.length : ℝ) * (omega (blocks.foldr (· * ·) 1) : ℝ) -
        (blocks.length : ℝ) * ((blocks.length : ℝ) - 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      rw [List.pairwise_cons] at hpair
      have hPs_pair : Ps.Pairwise Nat.Coprime := hpair.2
      have hPs_omega : ∀ B ∈ Ps, 1 ≤ omega B := by
        intro B hB
        exact homega_pos B (by simp [hB])
      have hPomega : 1 ≤ omega P := homega_pos P (by simp)
      have hcop : Nat.Coprime P (Ps.foldr (· * ·) 1) :=
        List.coprime_foldr_mul_of_forall hpair.1
      have homega :
          omega (P * Ps.foldr (· * ·) 1) =
            omega P + omega (Ps.foldr (· * ·) 1) :=
        omega_mul_of_coprime hcop
      have hih := ih hPs_pair hPs_omega
      have hPomega_real : (1 : ℝ) ≤ (omega P : ℝ) := by
        exact_mod_cast hPomega
      have hlen_nonneg : 0 ≤ (Ps.length : ℝ) := by positivity
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      rw [homega]
      norm_num [Nat.cast_add, Nat.cast_mul] at hih ⊢
      nlinarith [hih, hPomega_real, hlen_nonneg]

private lemma chainTFromBlocks_add_omega_real_quadratic_bound
    (blocks : List ℕ)
    (hpair : blocks.Pairwise Nat.Coprime)
    (homega_pos : ∀ P ∈ blocks, 1 ≤ omega P) :
    (((chainTFromBlocks blocks + omega (blocks.foldr (· * ·) 1) : ℕ) : ℝ) * 2) ≤
      2 * (blocks.length : ℝ) * (omega (blocks.foldr (· * ·) 1) : ℝ) -
        (blocks.length : ℝ) * ((blocks.length : ℝ) - 1) := by
  induction blocks with
  | nil =>
      simp [chainTFromBlocks, omega, primeSupport]
  | cons P Ps ih =>
      rw [List.pairwise_cons] at hpair
      have hPs_pair : Ps.Pairwise Nat.Coprime := hpair.2
      have hPs_omega : ∀ B ∈ Ps, 1 ≤ omega B := by
        intro B hB
        exact homega_pos B (by simp [hB])
      have hPomega : 1 ≤ omega P := homega_pos P (by simp)
      have hcop : Nat.Coprime P (Ps.foldr (· * ·) 1) :=
        List.coprime_foldr_mul_of_forall hpair.1
      have homega :
          omega (P * Ps.foldr (· * ·) 1) =
            omega P + omega (Ps.foldr (· * ·) 1) :=
        omega_mul_of_coprime hcop
      have hih := ih hPs_pair hPs_omega
      have hPomega_real : (1 : ℝ) ≤ (omega P : ℝ) := by
        exact_mod_cast hPomega
      have hlen_nonneg : 0 ≤ (Ps.length : ℝ) := by positivity
      simp only [chainTFromBlocks, List.foldr_cons, List.length_cons]
      rw [homega]
      norm_num [Nat.cast_add, Nat.cast_mul] at hih ⊢
      nlinarith [hih, hPomega_real, hlen_nonneg]

lemma ChainState.chainT_le_r_mul_W {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    chainT S ≤ S.r * S.W := by
  have h := chainTFromBlocks_le_length_mul_omega_foldr S.blocks S.blocks_pos
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_le_r_mul_K {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) :
    chainT S ≤ S.r * D.K := by
  exact (S.chainT_le_r_mul_W).trans (Nat.mul_le_mul_left S.r S.W_le_K)

lemma ChainState.chainT_real_quadratic_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hblocks : S.BlocksOmegaPos) :
    ((chainT S : ℝ) * 2) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) := by
  have h := chainTFromBlocks_real_quadratic_bound S.blocks S.pairwise_coprime hblocks
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_add_W_real_quadratic_bound {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) (hblocks : S.BlocksOmegaPos) :
    ((((chainT S + S.W : ℕ) : ℝ) * 2)) ≤
      2 * (S.r : ℝ) * (S.W : ℝ) - (S.r : ℝ) * ((S.r : ℝ) - 1) := by
  have h := chainTFromBlocks_add_omega_real_quadratic_bound
    S.blocks S.pairwise_coprime hblocks
  simpa [chainT, S.blocks_length, ← S.product_eq, S.W_eq] using h

lemma ChainState.chainT_cons_eq {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {P : ℕ} {S' : ChainState N D}
    (hblocks : S'.blocks = P :: S.blocks) :
    chainT S' = S.W + chainT S := by
  calc
    chainT S' = omega (S.blocks.foldr (· * ·) 1) + chainTFromBlocks S.blocks := by
      simp [chainT, hblocks, chainTFromBlocks]
    _ = S.W + chainT S := by
      rw [← S.product_eq, ← S.W_eq]
      rfl

/-- Cumulative lower-bound scale for the survivor set after a chain state.
This is the formal slot for the PDF's iterated lower bound (12), with
`Λ` standing for the spread/block loss constant. -/
noncomputable def chainLowerScale {N : ℕ} {D : PrunedData N}
    (Λ : ℝ) (S : ChainState N D) : ℝ :=
  (D.Q.card : ℝ) /
    ((S.productP : ℝ) * (hExp S.productP : ℝ) ^ 2 * Λ ^ S.W)

/-- The cumulative survivor-size invariant needed to turn the local
structural step into the global chain inequality. -/
def ChainState.HasLowerBound {N : ℕ} {D : PrunedData N}
    (Λ : ℝ) (S : ChainState N D) : Prop :=
  chainLowerScale Λ S ≤ (S.Qsurv.card : ℝ)

private lemma div_scale_le_weighted_share
    {a q c w p h κ : ℝ} {n : ℕ}
    (hq_nonneg : 0 ≤ q) (hw_pos : 0 < w)
    (hp : 0 < p) (hh : 0 < h) (hκ : 0 < κ)
    (haq : a ≤ q) (hdense : q / κ ^ n < c) (hweight : w ≤ (2 : ℝ) ^ n) :
    a / (p * h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) / p := by
  have hκpow : 0 < κ ^ n := pow_pos hκ _
  have htwopow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hΛpow : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
  have hq_lt : q < c * κ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hdense hκpow
    rwa [div_mul_cancel₀ _ hκpow.ne'] at hmul
  have haw_le : a * w ≤ q * (2 : ℝ) ^ n :=
    mul_le_mul haq hweight hw_pos.le hq_nonneg
  have htarget : a * w ≤ c * (2 * κ) ^ n := by
    calc
      a * w ≤ q * (2 : ℝ) ^ n := haw_le
      _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
            (mul_lt_mul_of_pos_right hq_lt htwopow).le
      _ = c * (2 * κ) ^ n := by
            rw [mul_pow]
            ring
  calc
    a / (p * h * (2 * κ) ^ n)
        = (a * w) / ((p * h * (2 * κ) ^ n) * w) := by
            field_simp [hw_pos.ne']
    _ ≤ (c * (2 * κ) ^ n) / ((p * h * (2 * κ) ^ n) * w) := by
            exact div_le_div_of_nonneg_right htarget
              (mul_nonneg
                (mul_nonneg (mul_pos hp hh).le hΛpow.le)
                hw_pos.le)
    _ = (c * (1 / h) / w) / p := by
            field_simp [hp.ne', hh.ne', hΛpow.ne', hw_pos.ne']

private lemma div_scale_le_weighted_fiber
    {a q c w h κ : ℝ} {n : ℕ}
    (hq_nonneg : 0 ≤ q) (hw_pos : 0 < w)
    (hh : 0 < h) (hκ : 0 < κ)
    (haq : a ≤ q) (hdense : q / κ ^ n < c) (hweight : w ≤ (2 : ℝ) ^ n) :
    a / (h * (2 * κ) ^ n) ≤ (c * (1 / h) / w) := by
  have hκpow : 0 < κ ^ n := pow_pos hκ _
  have htwopow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hΛpow : 0 < (2 * κ) ^ n := pow_pos (mul_pos (by norm_num) hκ) _
  have hq_lt : q < c * κ ^ n := by
    have hmul := mul_lt_mul_of_pos_right hdense hκpow
    rwa [div_mul_cancel₀ _ hκpow.ne'] at hmul
  have haw_le : a * w ≤ q * (2 : ℝ) ^ n :=
    mul_le_mul haq hweight hw_pos.le hq_nonneg
  have htarget : a * w ≤ c * (2 * κ) ^ n := by
    calc
      a * w ≤ q * (2 : ℝ) ^ n := haw_le
      _ ≤ (c * κ ^ n) * (2 : ℝ) ^ n :=
            (mul_lt_mul_of_pos_right hq_lt htwopow).le
      _ = c * (2 * κ) ^ n := by
            rw [mul_pow]
            ring
  calc
    a / (h * (2 * κ) ^ n)
        = (a * w) / ((h * (2 * κ) ^ n) * w) := by
            field_simp [hw_pos.ne']
    _ ≤ (c * (2 * κ) ^ n) / ((h * (2 * κ) ^ n) * w) := by
            exact div_le_div_of_nonneg_right htarget
              (mul_nonneg (mul_pos hh hΛpow).le hw_pos.le)
    _ = c * (1 / h) / w := by
            field_simp [hh.ne', hΛpow.ne', hw_pos.ne']

lemma ChainState.chainLowerScale_extend_coreBlock_eq
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hP : P ∈ S.coreBlocks C)
    (hprod : S'.productP = P * S.productP)
    (hW : S'.W = S.W + C.card) :
    chainLowerScale Λ S' =
      chainLowerScale Λ S / ((P : ℝ) * (hExp P : ℝ) ^ 2 * Λ ^ C.card) := by
  rw [chainLowerScale, chainLowerScale, hprod, hW,
    hExp_mul_of_coprime (S.coreBlock_coprime_productP hP).symm, pow_add]
  norm_num [Nat.cast_mul]
  ring_nf

lemma ChainState.hasLowerBound_extend_coreBlock
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {κ Λ : ℝ} {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hκ : 0 < κ) (hΛ : Λ = 2 * κ)
    (hP : P ∈ S.coreBlocks C)
    (hLower : S.HasLowerBound Λ)
    (hDense :
      ((S.Qsurv.card : ℝ) / κ ^ C.card) <
        ((S.coreSurvivors C).card : ℝ))
    (hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card)
    (hCard :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ))
    (hprod : S'.productP = P * S.productP)
    (hW : S'.W = S.W + C.card) :
    S'.HasLowerBound Λ := by
  rw [ChainState.HasLowerBound]
  rw [S.chainLowerScale_extend_coreBlock_eq hP hprod hW, hΛ]
  have hCore : (S.coreSurvivors C).Nonempty := by
    have hPmem := hP
    rw [ChainState.coreBlocks] at hPmem
    rcases Finset.mem_image.mp hPmem with ⟨q, hq, _hP⟩
    exact ⟨q, hq⟩
  have hWeight_pos :
      0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) :=
    S.coreBlocks_weight_sum_pos hCore
  have hP_pos_real : 0 < (P : ℝ) := by
    exact_mod_cast S.coreBlock_pos hP
  have hExpP_pos : 0 < (hExp P : ℝ) := by exact_mod_cast hExp_pos P
  have hh_pos : 0 < ((hExp P : ℝ) ^ 2) := sq_pos_of_pos hExpP_pos
  have hq_nonneg : 0 ≤ (S.Qsurv.card : ℝ) := by positivity
  have hstep :
      chainLowerScale (2 * κ) S /
          ((P : ℝ) * ((hExp P : ℝ) ^ 2) * (2 * κ) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) :=
    div_scale_le_weighted_share
      hq_nonneg hWeight_pos hP_pos_real hh_pos hκ
      (by simpa [ChainState.HasLowerBound, hΛ] using hLower)
      hDense hWeight
  exact hstep.trans hCard

lemma ChainState.selectedFiber_lower_from_invariant
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ}
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hLower : S.HasLowerBound (chainLambda D))
    (hDense :
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card)
    (hWeightedFiber :
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ)) :
    (D.Q.card : ℝ) /
        ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
          (chainLambda D) ^ (S.W + C.card)) ≤
      (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) := by
  have hCore : (S.coreSurvivors C).Nonempty := by
    rw [ChainState.coreBlocks] at hP
    rcases Finset.mem_image.mp hP with ⟨q, hq, _hP⟩
    exact ⟨q, hq⟩
  have hDenseQ :
      ((S.Qsurv.card : ℝ) / (chainKappa D) ^ C.card) <
        ((S.coreSurvivors C).card : ℝ) :=
    S.coreSurvivors_card_gt_qsurv_div_of_dense_bound (Λ := chainKappa D)
      (by simpa using hDense)
  have hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card :=
    S.coreBlocks_weight_sum_le_two_pow_card hCne
  have hWeight_pos :
      0 < ∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2) :=
    S.coreBlocks_weight_sum_pos hCore
  have hExpP_pos : 0 < (hExp P : ℝ) := by exact_mod_cast hExp_pos P
  have hh_pos : 0 < ((hExp P : ℝ) ^ 2) := sq_pos_of_pos hExpP_pos
  have hq_nonneg : 0 ≤ (S.Qsurv.card : ℝ) := by positivity
  have hstep :
      chainLowerScale (2 * chainKappa D) S /
          (((hExp P : ℝ) ^ 2) * (2 * chainKappa D) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) :=
    div_scale_le_weighted_fiber
      hq_nonneg hWeight_pos hh_pos (chainKappa_pos D)
      (by simpa [ChainState.HasLowerBound, chainLambda] using hLower)
      hDenseQ hWeight
  have hstepΛ :
      chainLowerScale (chainLambda D) S /
          (((hExp P : ℝ) ^ 2) * (chainLambda D) ^ C.card) ≤
        (((S.coreSurvivors C).card : ℝ) *
            ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) := by
    simpa [chainLambda] using hstep
  have hleft :
      chainLowerScale (chainLambda D) S /
          (((hExp P : ℝ) ^ 2) * (chainLambda D) ^ C.card) =
        (D.Q.card : ℝ) /
          ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
            (chainLambda D) ^ (S.W + C.card)) := by
    rw [chainLowerScale,
      hExp_mul_of_coprime (S.coreBlock_coprime_productP hP), pow_add]
    norm_num [Nat.cast_mul]
    ring_nf
  rw [← hleft]
  exact hstepΛ.trans hWeightedFiber

lemma ChainState.blocksOmegaPos_extend_coreBlock
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hBlocks : S.BlocksOmegaPos)
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hblocks : S'.blocks = P :: S.blocks) :
    S'.BlocksOmegaPos := by
  intro B hB
  rw [hblocks] at hB
  rcases List.mem_cons.1 hB with hBP | hBtail
  · subst B
    rw [S.coreBlock_omega_eq_card hP]
    exact Nat.succ_le_of_lt hCne.card_pos
  · exact hBlocks B hBtail

/-! ## §2 Initial state -/

/-- The chain starts with no selected blocks, all pruned moduli surviving,
product `1`, and accumulated exponent count `0`. -/
noncomputable def initialChainState (N : ℕ) (D : PrunedData N) : ChainState N D where
  r := 0
  blocks := []
  blocks_length := by simp
  Qsurv := D.Q
  Qsurv_subset := by intro q hq; exact hq
  Qsurv_nonempty := D.Q_nonempty
  W := 0
  productP := 1
  product_eq := by simp
  blocks_pos := by intro P hP; simp at hP
  productP_pos := by norm_num
  pairwise_coprime := by simp
  exact_divides := by intro q _hq; exact one_dvd q
  no_selected_prime_remains := by
    intro _q _hq _p hp
    simp [primeSupport] at hp
  residues_agree := by
    intro qi _hqi rj _hrj hqiD hrjD
    rw [Int.modEq_iff_dvd]
    exact one_dvd (D.a ⟨rj, hrjD⟩ - D.a ⟨qi, hqiD⟩)
  W_eq := by simp [omega, primeSupport]
  W_le_K := by omega

lemma initialChainState_room (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).W < D.K := by
  simp [initialChainState]
  exact D.K_pos

lemma initialChainState_r_zero (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).r = 0 := rfl

lemma initialChainState_product_one (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).productP = 1 := rfl

lemma initialChainState_chainT (N : ℕ) (D : PrunedData N) :
    chainT (initialChainState N D) = 0 := rfl

lemma initialChainState_blocksOmegaPos (N : ℕ) (D : PrunedData N) :
    (initialChainState N D).BlocksOmegaPos := by
  intro P hP
  simp [initialChainState] at hP

lemma initialChainState_hasLowerBound {N : ℕ} (D : PrunedData N) (Λ : ℝ) :
    ChainState.HasLowerBound Λ (initialChainState N D) := by
  rw [ChainState.HasLowerBound, chainLowerScale]
  simp [initialChainState, hExp_one]

/-! ## §3 Structural chain step -/

theorem chain_step_structural
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      0 < C0 ∧
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) /
          (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card := by
  rcases S.exists_dense_core_with_survivor_of_room hRoom with
    ⟨C0, hC0, C, hCne, hCore, hDense⟩
  rcases S.exists_weighted_extended_coreBlock hCore with
    ⟨P, S', hP, hblocks, hr, hprod, _hQsubset, _hQcard_le, hW, _hShare, hcard⟩
  have hWincrease : S.W < S'.W := by
    rw [hW]
    exact Nat.lt_add_of_pos_right hCne.card_pos
  exact ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hcard, hDense⟩

theorem chain_step_structural_with_lowerBound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card := by
  rcases S.exists_dense_core_fixed_with_survivor_of_room hRoom with
    ⟨C, hCne, hCore, hDense⟩
  rcases S.exists_weighted_extended_coreBlock hCore with
    ⟨P, S', hP, hblocks, hr, hprod, hQsubset, hQcard_le, hW, hShare, hcard⟩
  have hWincrease : S.W < S'.W := by
    rw [hW]
    exact Nat.lt_add_of_pos_right hCne.card_pos
  have hDenseQ :
      ((S.Qsurv.card : ℝ) / (chainKappa D) ^ C.card) <
        ((S.coreSurvivors C).card : ℝ) :=
    S.coreSurvivors_card_gt_qsurv_div_of_dense_bound (Λ := chainKappa D)
      (by simpa using hDense)
  have hWeight :
      (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (2 : ℝ) ^ C.card :=
    S.coreBlocks_weight_sum_le_two_pow_card hCne
  have hLower' : S'.HasLowerBound (chainLambda D) := by
    apply S.hasLowerBound_extend_coreBlock
      (κ := chainKappa D) (Λ := chainLambda D)
      (hκ := chainKappa_pos D) (hΛ := by rfl)
      (hP := hP) (hLower := hLower) (hDense := hDenseQ)
      (hWeight := hWeight) (hCard := hcard)
      (hprod := hprod) (hW := hW)
  exact ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le, hW,
    S.chainT_cons_eq hblocks, hLower', hShare, hcard, hDense⟩

lemma ChainState.coreSurvivors_nonempty_of_coreBlock {N : ℕ} {D : PrunedData N}
    (S : ChainState N D) {C : Finset ℕ} {P : ℕ}
    (hP : P ∈ S.coreBlocks C) : (S.coreSurvivors C).Nonempty := by
  rw [ChainState.coreBlocks] at hP
  rcases Finset.mem_image.mp hP with ⟨q, hq, _⟩
  exact ⟨q, hq⟩

theorem chain_step_structural_with_counts
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K) :
    ∃ C0 : ℝ, ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      0 < C0 ∧
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) /
          (C0 * Real.log (Real.exp 1 * (D.K : ℝ))) ^ C.card ∧
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) ∧
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) ∧
      P ≤ N ∧
      (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases chain_step_structural S hRoom with
    ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hweighted, hDense⟩
  have hCore : (S.coreSurvivors C).Nonempty := S.coreSurvivors_nonempty_of_coreBlock hP
  exact ⟨C0, C, P, S', hC0, hCne, hP, hblocks, hr, hWincrease, hprod, hweighted, hDense,
    S.coreSurvivors_card_real_le_bfv_omega_count C ε hCount,
    S.coreBlocks_card_real_le_bfv_omega_count C ε hCore hCount,
    S.coreBlock_le_N hP, S.coreBlock_hExp_bound hP⟩

theorem chain_step_structural_with_counts_and_lowerBound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ C : Finset ℕ, ∃ P : ℕ, ∃ S' : ChainState N D,
      C.Nonempty ∧
      P ∈ S.coreBlocks C ∧
      S'.blocks = P :: S.blocks ∧
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      S'.productP = P * S.productP ∧
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P) ∧
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card ∧
      S'.W = S.W + C.card ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) ∧
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ) ∧
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card ∧
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))) ∧
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N) ∧
      P ≤ N ∧
      (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ))) := by
  rcases chain_step_structural_with_lowerBound S hRoom hLower with
    ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le,
      hW, hT, hLower', hShare, hweighted, hDense⟩
  have hCore : (S.coreSurvivors C).Nonempty := S.coreSurvivors_nonempty_of_coreBlock hP
  exact ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, hQsubset, hQcard_le,
    hW, hT, hLower',
    hShare, hweighted, hDense,
    S.coreSurvivors_card_real_le_bfv_omega_count C ε hCount,
    S.coreBlocks_card_real_le_bfv_omega_count C ε hCore hCount,
    S.coreBlock_le_N hP, S.coreBlock_hExp_bound hP⟩

noncomputable def chainStepBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  (N : ℝ) / (D.Q.card : ℝ)
    * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))

noncomputable def chainProductBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  ((N : ℝ) / (D.Q.card : ℝ)) ^ S.r
    * Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ)))

lemma chainStepBound_nonneg {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 ≤ chainStepBound ε S := by
  rw [chainStepBound]
  positivity

lemma chainProductBound_pos {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 < chainProductBound ε S := by
  rw [chainProductBound]
  have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
  have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
  positivity

noncomputable def chainStepBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (_S S' : ChainState N D) : ℝ :=
  (N : ℝ) / (D.Q.card : ℝ)
    * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp (((S'.W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
    * (hExp S'.productP : ℝ) ^ 2
    * (chainLambda D) ^ S'.W

noncomputable def chainProductBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : ℝ :=
  ((N : ℝ) / (D.Q.card : ℝ)) ^ S.r
    * Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
    * Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ)))
    * Real.exp (2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)))
    * (chainLambda D) ^ (chainT S + S.W)

lemma chainStepBoundWithLosses_nonneg {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S S' : ChainState N D) : 0 ≤ chainStepBoundWithLosses ε S S' := by
  rw [chainStepBoundWithLosses]
  have hΛ : 0 ≤ chainLambda D := (chainLambda_pos D).le
  positivity

lemma chainProductBoundWithLosses_pos {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) : 0 < chainProductBoundWithLosses ε S := by
  rw [chainProductBoundWithLosses]
  have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
  have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
  have hΛ : 0 < chainLambda D := chainLambda_pos D
  positivity

lemma log_chainProductBound {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) :
    Real.log (chainProductBound ε S) =
      (S.r : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
        (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
        ((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ)) := by
  rw [chainProductBound]
  set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
  set a : ℝ := (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N
  set b : ℝ := ((chainT S : ℝ) / 2) * Real.log (Real.log (N : ℝ))
  have hq_pos : 0 < q := by
    dsimp [q]
    have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
    have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    positivity
  have hqpow_ne : q ^ S.r ≠ 0 := pow_ne_zero _ hq_pos.ne'
  have hexpa_ne : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have hexpb_ne : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
  rw [Real.log_mul (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne,
    Real.log_mul hqpow_ne hexpa_ne, Real.log_pow, Real.log_exp, Real.log_exp]

lemma log_chainProductBoundWithLosses {N : ℕ} {D : PrunedData N}
    (ε : ℝ) (S : ChainState N D) :
    Real.log (chainProductBoundWithLosses ε S) =
      (S.r : ℝ) * Real.log ((N : ℝ) / (D.Q.card : ℝ)) +
        (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N +
        ((((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))) +
        2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ)) +
        ((chainT S + S.W : ℕ) : ℝ) * Real.log (chainLambda D) := by
  rw [chainProductBoundWithLosses]
  set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
  set a : ℝ := (S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N
  set b : ℝ := (((chainT S + S.W : ℕ) : ℝ) / 2) * Real.log (Real.log (N : ℝ))
  set c : ℝ := 2 * (S.r : ℝ) * Real.sqrt (Real.log (N : ℝ))
  set Λ : ℝ := chainLambda D
  have hq_pos : 0 < q := by
    dsimp [q]
    have hN : 0 < (N : ℝ) := by exact_mod_cast D.N_pos
    have hQ : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    positivity
  have hΛ_pos : 0 < Λ := by
    dsimp [Λ]
    exact chainLambda_pos D
  have hqpow_ne : q ^ S.r ≠ 0 := pow_ne_zero _ hq_pos.ne'
  have hexpa_ne : Real.exp a ≠ 0 := (Real.exp_pos a).ne'
  have hexpb_ne : Real.exp b ≠ 0 := (Real.exp_pos b).ne'
  have hexpc_ne : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  have hΛpow_ne : Λ ^ (chainT S + S.W) ≠ 0 := pow_ne_zero _ hΛ_pos.ne'
  rw [Real.log_mul
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne) hexpc_ne)
        hΛpow_ne,
      Real.log_mul (mul_ne_zero (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne) hexpc_ne,
      Real.log_mul (mul_ne_zero hqpow_ne hexpa_ne) hexpb_ne,
      Real.log_mul hqpow_ne hexpa_ne,
      Real.log_pow, Real.log_exp, Real.log_exp, Real.log_exp, Real.log_pow]

lemma initialChainState_productBound {N : ℕ} (D : PrunedData N) (ε : ℝ) :
    ((initialChainState N D).productP : ℝ) ≤
      chainProductBound ε (initialChainState N D) := by
  simp [chainProductBound, initialChainState]

lemma initialChainState_productBoundWithLosses {N : ℕ} (D : PrunedData N) (ε : ℝ) :
    ((initialChainState N D).productP : ℝ) ≤
      chainProductBoundWithLosses ε (initialChainState N D) := by
  simp [chainProductBoundWithLosses, initialChainState, chainT, chainTFromBlocks]

lemma chainProductBound_step
    {N : ℕ} {D : PrunedData N} {ε : ℝ} {S S' : ChainState N D}
    (hr : S'.r = S.r + 1)
    (hT : chainT S' = S.W + chainT S)
    (hProd : (S.productP : ℝ) ≤ chainProductBound ε S)
    (hStep :
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBound ε S) :
    (S'.productP : ℝ) ≤ chainProductBound ε S' := by
  have hstep_nonneg : 0 ≤ chainStepBound ε S := chainStepBound_nonneg ε S
  calc
    (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBound ε S := hStep
    _ ≤ chainProductBound ε S * chainStepBound ε S := by
          exact mul_le_mul_of_nonneg_right hProd hstep_nonneg
    _ = chainProductBound ε S' := by
          rw [chainProductBound, chainStepBound, chainProductBound, hr, hT]
          set q : ℝ := (N : ℝ) / (D.Q.card : ℝ)
          set a : ℝ := (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N with ha
          set l : ℝ := Real.log (Real.log (N : ℝ))
          rw [pow_succ]
          have hExpR :
              Real.exp ((S.r : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) =
                Real.exp ((S.r : ℝ) * a) := by
            rw [ha]
            ring_nf
          have hExpR1 :
              Real.exp (((S.r + 1 : ℕ) : ℝ) *
                  (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) =
                Real.exp (((S.r + 1 : ℕ) : ℝ) * a) := by
            rw [ha]
            ring_nf
          rw [hExpR, hExpR1]
          change
            (q ^ S.r * Real.exp ((S.r : ℝ) * a) *
                  Real.exp (((chainT S : ℝ) / 2) * l)) *
                (q * Real.exp a * Real.exp (((S.W : ℝ) / 2) * l)) =
              q ^ S.r * q * Real.exp (((S.r + 1 : ℕ) : ℝ) * a) *
                Real.exp ((((S.W + chainT S : ℕ) : ℝ) / 2) * l)
          calc
            (q ^ S.r * Real.exp ((S.r : ℝ) * a) *
                  Real.exp (((chainT S : ℝ) / 2) * l)) *
                (q * Real.exp a * Real.exp (((S.W : ℝ) / 2) * l))
                = q ^ S.r * q *
                    (Real.exp ((S.r : ℝ) * a) * Real.exp a) *
                    (Real.exp (((chainT S : ℝ) / 2) * l) *
                      Real.exp (((S.W : ℝ) / 2) * l)) := by
                    ring
            _ = q ^ S.r * q * Real.exp (((S.r + 1 : ℕ) : ℝ) * a) *
                  Real.exp ((((S.W + chainT S : ℕ) : ℝ) / 2) * l) := by
                    rw [← Real.exp_add, ← Real.exp_add]
                    congr 2
                    · congr 1
                      norm_num
                      ring
                    · norm_num
                      ring

lemma chainProductBoundWithLosses_step
    {N : ℕ} {D : PrunedData N} {ε : ℝ} {S S' : ChainState N D}
    (hr : S'.r = S.r + 1)
    (hT : chainT S' = S.W + chainT S)
    (hProd : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S)
    (hStep :
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S') :
    (S'.productP : ℝ) ≤ chainProductBoundWithLosses ε S' := by
  have hstep_nonneg : 0 ≤ chainStepBoundWithLosses ε S S' :=
    chainStepBoundWithLosses_nonneg ε S S'
  have hExpBound : (hExp S'.productP : ℝ) ≤
      Real.exp (Real.sqrt (Real.log (N : ℝ))) :=
    S'.productP_hExp_bound
  have hExpSq :
      (hExp S'.productP : ℝ) ^ 2 ≤
        Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
    have hnonneg : 0 ≤ (hExp S'.productP : ℝ) := by positivity
    calc
      (hExp S'.productP : ℝ) ^ 2
          ≤ (Real.exp (Real.sqrt (Real.log (N : ℝ)))) ^ 2 :=
            sq_le_sq₀ hnonneg (Real.exp_pos _).le |>.2 hExpBound
      _ = Real.exp (2 * Real.sqrt (Real.log (N : ℝ))) := by
            rw [sq, ← Real.exp_add]
            ring_nf
  calc
    (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := hStep
    _ ≤ chainProductBoundWithLosses ε S * chainStepBoundWithLosses ε S S' := by
          exact mul_le_mul_of_nonneg_right hProd hstep_nonneg
    _ ≤ chainProductBoundWithLosses ε S' := by
          rw [chainProductBoundWithLosses, chainStepBoundWithLosses,
            chainProductBoundWithLosses, hr, hT]
          set q : ℝ := (N : ℝ) / (D.Q.card : ℝ) with hq
          set a : ℝ := -((D.K : ℝ) / Mscale N) / 2 + ε with ha
          set l : ℝ := Real.log (Real.log (N : ℝ)) with hl
          set u : ℝ := Real.sqrt (Real.log (N : ℝ)) with hu
          have hΛnonneg : 0 ≤ chainLambda D := (chainLambda_pos D).le
          calc
            (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                  Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * (S.r : ℝ) * u) *
                  (chainLambda D) ^ (chainT S + S.W)) *
                (q * Real.exp (a * Zscale N) * Real.exp (((S'.W : ℝ) / 2) * l) *
                  (hExp S'.productP : ℝ) ^ 2 * (chainLambda D) ^ S'.W)
                ≤
              (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                  Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * (S.r : ℝ) * u) *
                  (chainLambda D) ^ (chainT S + S.W)) *
                (q * Real.exp (a * Zscale N) * Real.exp (((S'.W : ℝ) / 2) * l) *
                  Real.exp (2 * u) * (chainLambda D) ^ S'.W) := by
                    exact mul_le_mul_of_nonneg_left
                      (by
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_left hExpSq (by positivity))
                          (pow_nonneg hΛnonneg _))
                      (by positivity)
            _ = q ^ (S.r + 1) *
                  Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) *
                  Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) * l) *
                  Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
                  (chainLambda D) ^ (S.W + chainT S + S'.W) := by
                    rw [pow_succ]
                    calc
                      (q ^ S.r * Real.exp ((S.r : ℝ) * a * Zscale N) *
                            Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                            Real.exp (2 * (S.r : ℝ) * u) *
                            (chainLambda D) ^ (chainT S + S.W)) *
                          (q * Real.exp (a * Zscale N) *
                            Real.exp (((S'.W : ℝ) / 2) * l) *
                            Real.exp (2 * u) * (chainLambda D) ^ S'.W)
                          =
                        q ^ S.r * q *
                          (Real.exp ((S.r : ℝ) * a * Zscale N) *
                            Real.exp (a * Zscale N)) *
                          (Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l) *
                            Real.exp (((S'.W : ℝ) / 2) * l)) *
                          (Real.exp (2 * (S.r : ℝ) * u) * Real.exp (2 * u)) *
                          ((chainLambda D) ^ (chainT S + S.W) *
                            (chainLambda D) ^ S'.W) := by ring
                      _ =
                        q ^ S.r * q *
                          Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) *
                          Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) * l) *
                          Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) *
                          (chainLambda D) ^ (S.W + chainT S + S'.W) := by
                            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
                              ← pow_add]
                            have hA :
                                Real.exp ((S.r : ℝ) * a * Zscale N + a * Zscale N) =
                                  Real.exp (((S.r + 1 : ℕ) : ℝ) * a * Zscale N) := by
                              congr 1
                              norm_num
                              ring
                            have hL :
                                Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) * l +
                                    ((S'.W : ℝ) / 2) * l) =
                                  Real.exp ((((S.W + chainT S + S'.W : ℕ) : ℝ) / 2) *
                                    l) := by
                              congr 1
                              norm_num [Nat.cast_add]
                              ring
                            have hU :
                                Real.exp (2 * (S.r : ℝ) * u + 2 * u) =
                                  Real.exp (2 * ((S.r + 1 : ℕ) : ℝ) * u) := by
                              congr 1
                              norm_num
                              ring
                            rw [hA, hL, hU]
                            ring

theorem chain_terminal_with_product_bound_from_state
    {N : ℕ} {D : PrunedData N} (ε : ℝ)
    (hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S')
    (S : ChainState N D)
    (hLower : S.HasLowerBound (chainLambda D))
    (hBlocks : S.BlocksOmegaPos)
    (hProd : (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S) :
    ∃ Sfinal : ChainState N D,
      S.r ≤ Sfinal.r ∧
      Sfinal.r ≤ S.r + (D.K - S.W) ∧
      Sfinal.W = D.K ∧
      Sfinal.HasLowerBound (chainLambda D) ∧
      Sfinal.BlocksOmegaPos ∧
      (Sfinal.productP : ℝ) ≤ chainProductBoundWithLosses ε Sfinal := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ S : ChainState N D,
      D.K - S.W = n →
      S.HasLowerBound (chainLambda D) →
      S.BlocksOmegaPos →
      (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S →
      ∃ Sfinal : ChainState N D,
        S.r ≤ Sfinal.r ∧
        Sfinal.r ≤ S.r + (D.K - S.W) ∧
        Sfinal.W = D.K ∧
        Sfinal.HasLowerBound (chainLambda D) ∧
        Sfinal.BlocksOmegaPos ∧
        (Sfinal.productP : ℝ) ≤ chainProductBoundWithLosses ε Sfinal
  have hmain : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn hLowerS hBlocksS hProdS
        by_cases hdone : S.W = D.K
        · refine ⟨S, le_rfl, ?_, hdone, hLowerS, hBlocksS, hProdS⟩
          rw [hdone]
          simp
        · have hRoom : S.W < D.K := lt_of_le_of_ne S.W_le_K hdone
          rcases hStep S hLowerS hBlocksS hRoom with
            ⟨S', hr, hWincrease, hT, hLower', hBlocks', hStepProd⟩
          have hProd' : (S'.productP : ℝ) ≤ chainProductBoundWithLosses ε S' :=
            chainProductBoundWithLosses_step hr hT hProdS hStepProd
          have hlt : D.K - S'.W < n := by
            rw [← hn]
            omega
          rcases ih (D.K - S'.W) hlt S' rfl hLower' hBlocks' hProd' with
            ⟨Sfinal, hle_start, hle_budget, hWfinal, hLowerFinal, hBlocksFinal,
              hProdFinal⟩
          refine ⟨Sfinal, ?_, ?_, hWfinal, hLowerFinal, hBlocksFinal, hProdFinal⟩
          · have hstep : S.r ≤ S'.r := by
              rw [hr]
              omega
            exact hstep.trans hle_start
          · have hbudget :
                S'.r + (D.K - S'.W) ≤ S.r + (D.K - S.W) := by
              rw [hr]
              omega
            exact hle_budget.trans hbudget
  exact hmain (D.K - S.W) S rfl hLower hBlocks hProd

theorem chain_terminal_with_product_bound_from_initial
    (N : ℕ) (D : PrunedData N) (ε : ℝ)
    (hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S') :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.HasLowerBound (chainLambda D) ∧
      S.BlocksOmegaPos ∧
      (S.productP : ℝ) ≤ chainProductBoundWithLosses ε S := by
  let S0 := initialChainState N D
  have hRoom0 : S0.W < D.K := by
    simpa [S0] using initialChainState_room N D
  have hLower0 : S0.HasLowerBound (chainLambda D) := by
    simpa [S0] using initialChainState_hasLowerBound D (chainLambda D)
  have hBlocks0 : S0.BlocksOmegaPos := by
    simpa [S0] using initialChainState_blocksOmegaPos N D
  have hProd0 : (S0.productP : ℝ) ≤ chainProductBoundWithLosses ε S0 := by
    simpa [S0] using initialChainState_productBoundWithLosses D ε
  rcases hStep S0 hLower0 hBlocks0 hRoom0 with
    ⟨S1, hr1, hWincrease1, _hT1, hLower1, hBlocks1, hStepProd1⟩
  have hProd1 : (S1.productP : ℝ) ≤ chainProductBoundWithLosses ε S1 :=
    chainProductBoundWithLosses_step hr1 _hT1 hProd0 hStepProd1
  rcases chain_terminal_with_product_bound_from_state ε hStep S1 hLower1 hBlocks1 hProd1 with
    ⟨S, hle_start, hle_budget, hW, hLower, hBlocks, hProd⟩
  refine ⟨S.r, S, rfl, ?_, ?_, Or.inr hW, hLower, hBlocks, hProd⟩
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    exact hS1r ▸ hle_start
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    have hS1W_pos : 0 < S1.W := by
      have hS0W : S0.W = 0 := rfl
      omega
    calc
      S.r ≤ S1.r + (D.K - S1.W) := hle_budget
      _ ≤ D.K := by
        rw [hS1r]
        omega

theorem chain_terminal_from_state
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (hLower : S.HasLowerBound (chainLambda D)) :
    ∃ Sfinal : ChainState N D,
      S.r ≤ Sfinal.r ∧
      Sfinal.r ≤ S.r + (D.K - S.W) ∧
      Sfinal.W = D.K ∧
      Sfinal.HasLowerBound (chainLambda D) := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ S : ChainState N D,
      D.K - S.W = n →
      S.HasLowerBound (chainLambda D) →
      ∃ Sfinal : ChainState N D,
        S.r ≤ Sfinal.r ∧
        Sfinal.r ≤ S.r + (D.K - S.W) ∧
        Sfinal.W = D.K ∧
        Sfinal.HasLowerBound (chainLambda D)
  have hmain : ∀ n, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn hLowerS
        by_cases hdone : S.W = D.K
        · refine ⟨S, le_rfl, ?_, hdone, hLowerS⟩
          rw [hdone]
          simp
        · have hRoom : S.W < D.K := lt_of_le_of_ne S.W_le_K hdone
          rcases chain_step_structural_with_lowerBound S hRoom hLowerS with
            ⟨_C, _P, S', _hCne, _hP, _hblocks, hr, hWincrease, _hprod,
              _hQsubset, _hQcard_le, _hW, _hT, hLower', _hShare, _hcard, _hDense⟩
          have hlt : D.K - S'.W < n := by
            rw [← hn]
            omega
          rcases ih (D.K - S'.W) hlt S' rfl hLower' with
            ⟨Sfinal, hle_start, hle_budget, hWfinal, hLowerFinal⟩
          refine ⟨Sfinal, ?_, ?_, hWfinal, hLowerFinal⟩
          · have hstep : S.r ≤ S'.r := by
              rw [hr]
              omega
            exact hstep.trans hle_start
          · have hbudget :
                S'.r + (D.K - S'.W) ≤ S.r + (D.K - S.W) := by
              rw [hr]
              omega
            exact hle_budget.trans hbudget
  exact hmain (D.K - S.W) S rfl hLower

theorem chain_terminal_from_initial (N : ℕ) (D : PrunedData N) :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧
      1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.HasLowerBound (chainLambda D) := by
  let S0 := initialChainState N D
  have hRoom0 : S0.W < D.K := by
    simpa [S0] using initialChainState_room N D
  have hLower0 : S0.HasLowerBound (chainLambda D) := by
    simpa [S0] using initialChainState_hasLowerBound D (chainLambda D)
  rcases chain_step_structural_with_lowerBound S0 hRoom0 hLower0 with
    ⟨_C, _P, S1, _hCne, _hP, _hblocks, hr1, hWincrease1, _hprod,
      _hQsubset, _hQcard_le, _hW, _hT, hLower1, _hShare, _hcard, _hDense⟩
  rcases chain_terminal_from_state S1 hLower1 with
    ⟨S, hle_start, hle_budget, hW, hLower⟩
  refine ⟨S.r, S, rfl, ?_, ?_, Or.inr hW, hLower⟩
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    exact hS1r ▸ hle_start
  · have hS1r : S1.r = 1 := by
      rw [hr1]
      simp [S0, initialChainState]
    have hS1W_pos : 0 < S1.W := by
      have hS0W : S0.W = 0 := rfl
      omega
    calc
      S.r ≤ S1.r + (D.K - S1.W) := hle_budget
      _ ≤ D.K := by
        rw [hS1r]
        omega

/-! ## §4 Chain step -/

/-- The remaining quantitative estimate in PDF Lemma 4.1: once the
structural step has selected an exact block `P`, the BFV count, dense-core
lower bound, weighted block choice, `hExp` control, and lower-order estimates
bound that block by the one-step product factor. -/
theorem chain_step_selected_block_bound
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (_hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D))
    (_hBlocks : S.BlocksOmegaPos)
    {C : Finset ℕ} {P : ℕ} {S' : ChainState N D}
    (hCne : C.Nonempty)
    (hP : P ∈ S.coreBlocks C)
    (hStepProduct : S'.productP = P * S.productP)
    (hStepW : S'.W = S.W + C.card)
    (_hStepLower : S'.HasLowerBound (chainLambda D))
    (_hQsurv_subset :
      S'.Qsurv ⊆ ((S.coreSurvivors C).filter fun q => exactBlock C q = P))
    (_hQsurv_card_le :
      S'.Qsurv.card ≤ ((S.coreSurvivors C).filter fun q => exactBlock C q = P).card)
    (hWeightedFiber :
      ((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ))
    (_hWeighted :
      (((S.coreSurvivors C).card : ℝ) * ((1 : ℝ) / ((hExp P : ℝ) ^ 2)) /
          (∑ B ∈ S.coreBlocks C, (1 : ℝ) / ((hExp B : ℝ) ^ 2))) /
          (P : ℝ) ≤ (S'.Qsurv.card : ℝ))
    (hDense :
      ((S.remainingSupportFamily.filter fun A => C ⊆ A).card : ℝ) >
        (S.remainingSupportFamily.card : ℝ) / (chainKappa D) ^ C.card)
    (_hCoreCount :
      ((S.coreSurvivors C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
          * Real.exp (((S.W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))
    (_hBlockCount :
      ((S.coreBlocks C).card : ℝ) ≤
        (N : ℝ) * Real.exp ((-((C.card : ℝ) / Mscale N) / 2 + ε) * Zscale N))
    (_hP_le_N : P ≤ N)
    (_hP_hExp : (hExp P : ℝ) ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)))) :
    (P : ℝ) ≤ chainStepBoundWithLosses ε S S' := by
  have hFiberLower :
      (D.Q.card : ℝ) /
          ((S.productP : ℝ) * (hExp (S.productP * P) : ℝ) ^ 2 *
            (chainLambda D) ^ (S.W + C.card)) ≤
        (((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℝ) :=
    S.selectedFiber_lower_from_invariant hCne hP hLower hDense hWeightedFiber
  have hFiberUpper :
      ((((S.coreSurvivors C).filter fun q => exactBlock C q = P).card : ℕ) : ℝ) ≤
        ((N : ℝ) / (S.productP * P : ℝ)) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) :=
    S.selectedFiber_card_real_le_bfv_omega_count hP ε hCount
  have hWithLosses :
      (P : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) *
          Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) *
          (hExp (S.productP * P) : ℝ) ^ 2 *
          (chainLambda D) ^ (S.W + C.card) := by
    have hcompare := hFiberLower.trans hFiberUpper
    have hDQpos : 0 < (D.Q.card : ℝ) := by exact_mod_cast D.card_pos
    have hSpos : 0 < (S.productP : ℝ) := by exact_mod_cast S.productP_pos
    have hPpos : 0 < (P : ℝ) := by exact_mod_cast S.coreBlock_pos hP
    have hHpos : 0 < (hExp (S.productP * P) : ℝ) ^ 2 := by
      have h : 0 < (hExp (S.productP * P) : ℝ) := by exact_mod_cast hExp_pos (S.productP * P)
      exact sq_pos_of_pos h
    have hΛpos : 0 < (chainLambda D) ^ (S.W + C.card) :=
      pow_pos (chainLambda_pos D) _
    have hEpos :
        0 < Real.exp ((-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N) *
          Real.exp ((((S.W + C.card : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ))) := by
      positivity
    field_simp [hSpos.ne', hPpos.ne', hHpos.ne', hΛpos.ne'] at hcompare
    have hmain :
        (D.Q.card : ℝ) * (P : ℝ) ≤
          (N : ℝ) *
            Real.exp ((-((D.K : ℝ) / Mscale N) + 2 * ε) * Zscale N / 2) *
            Real.exp (((S.W + C.card : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) / 2) *
            ((hExp (S.productP * P) : ℝ) ^ 2) *
            (chainLambda D) ^ (S.W + C.card) := by
      have hmul := mul_le_mul_of_nonneg_right hcompare hHpos.le
      rw [div_mul_cancel₀ _ hHpos.ne'] at hmul
      nlinarith [hmul]
    field_simp [hDQpos.ne']
    nlinarith [hmain]
  rw [chainStepBoundWithLosses, hStepW, hStepProduct]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hWithLosses

/-- **One chain step** (PDF Lemma 4.1). From a chain state with at least
one prime still to commit, the dense-core lemma + BFV count + residue
pigeonhole produce a next block `P_{r+1}` and a still-large surviving
sub-family. -/
theorem chain_step
    {N : ℕ} {D : PrunedData N} (S : ChainState N D)
    (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ)))))
    (hRoom : S.W < D.K)
    (hLower : S.HasLowerBound (chainLambda D))
    (hBlocks : S.BlocksOmegaPos) :
    ∃ S' : ChainState N D,
      S'.r = S.r + 1 ∧
      S.W < S'.W ∧
      chainT S' = S.W + chainT S ∧
      S'.HasLowerBound (chainLambda D) ∧
      S'.BlocksOmegaPos ∧
      (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by
  rcases chain_step_structural_with_counts_and_lowerBound S ε hCount hRoom hLower with
    ⟨C, P, S', hCne, hP, hblocks, hr, hWincrease, hprod, _hQsubset, _hQcard_le,
      _hW, hT, hLower', _hWeightedFiber, _hweighted, _hDense, _hCoreCount, _hBlockCount,
      _hP_le_N, _hP_hExp⟩
  have hBlocks' : S'.BlocksOmegaPos :=
    S.blocksOmegaPos_extend_coreBlock hBlocks hCne hP hblocks
  refine ⟨S', hr, hWincrease, hT, hLower', hBlocks', ?_⟩
  have hPbound : (P : ℝ) ≤ chainStepBoundWithLosses ε S S' :=
    chain_step_selected_block_bound S ε _hε hCount hRoom hLower hBlocks
      hCne hP hprod _hW hLower' _hQsubset _hQcard_le _hWeightedFiber _hweighted _hDense
      _hCoreCount _hBlockCount _hP_le_N _hP_hExp
  rw [hprod]
  calc
    ((P * S.productP : ℕ) : ℝ) = (P : ℝ) * (S.productP : ℝ) := by norm_num
    _ ≤ chainStepBoundWithLosses ε S S' * (S.productP : ℝ) := by
          exact mul_le_mul_of_nonneg_right hPbound (by positivity)
    _ = (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by ring

/-! ## §5 The chain inequality (telescoped) -/

/-- **Chain inequality** (PDF Proposition 4.2). The full descending chain
runs for `R` steps until either `W = K` or `productP ≥ N L(-2, N)`. -/
theorem chain_inequality
    (N : ℕ) (D : PrunedData N) (ε : ℝ) (_hε : 0 < ε)
    (hCount :
      ∀ y K W : ℕ,
        y ≤ N →
        W ≤ K →
        (K : ℝ) ≤ 3 * Mscale N →
        let d : ℝ := (K : ℝ) / Mscale N
        ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
          ≤ Nat.floor
              ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
                * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))) :
    ∃ R : ℕ, ∃ S : ChainState N D,
      S.r = R ∧ 1 ≤ R ∧ R ≤ D.K ∧
      ((N : ℝ) * Lscale (-2) N ≤ (S.productP : ℝ) ∨ S.W = D.K) ∧
      S.BlocksOmegaPos ∧
      -- telescoped product bound, parameterized by ε, with the explicit
      -- lower-order losses from the paper:
      (S.productP : ℝ) ≤
        ((N : ℝ) / (D.Q.card : ℝ)) ^ R
        * Real.exp ((R : ℝ) * (-((D.K : ℝ) / Mscale N) / 2 + ε) * Zscale N)
        * Real.exp ((((chainT S + S.W : ℕ) : ℝ) / 2) *
            Real.log (Real.log (N : ℝ)))
        * Real.exp (2 * (R : ℝ) * Real.sqrt (Real.log (N : ℝ)))
        * (chainLambda D) ^ (chainT S + S.W) := by
  have hStep :
      ∀ S : ChainState N D,
        S.HasLowerBound (chainLambda D) →
        S.BlocksOmegaPos →
        S.W < D.K →
        ∃ S' : ChainState N D,
          S'.r = S.r + 1 ∧
          S.W < S'.W ∧
          chainT S' = S.W + chainT S ∧
          S'.HasLowerBound (chainLambda D) ∧
          S'.BlocksOmegaPos ∧
          (S'.productP : ℝ) ≤ (S.productP : ℝ) * chainStepBoundWithLosses ε S S' := by
    intro S hLower hBlocks hRoom
    exact chain_step S ε _hε hCount hRoom hLower hBlocks
  rcases chain_terminal_with_product_bound_from_initial N D ε hStep with
    ⟨R, S, hR, hRpos, hRle, hStop, _hLower, hBlocks, hProd⟩
  refine ⟨R, S, hR, hRpos, hRle, hStop, hBlocks, ?_⟩
  simpa [chainProductBoundWithLosses, hR] using hProd

end Erdos202
