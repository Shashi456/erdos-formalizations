/-
Erdos Problem 42 — Route A Fourier coefficient limit facts.

The compact extraction assigns limits to selected finite Fourier coefficients.
This file records the axiom-free consequences that come only from the Route A
counterexample hypotheses: Fourier lower bias `ε_n → 0` gives nonnegative real
parts in the limit, and symmetry of `F_n` makes the limiting coefficients real.
-/

import Erdos.P42.FourierPositive.LargeSpectrum

namespace Erdos42.FourierPositive

open Filter Erdos42
open scoped Topology Classical

lemma real_limit_nonneg_of_eventually_lower_neg_tendsto_zero
    {ε a : ℕ → ℝ} {L : ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 L))
    (hlower : ∀ᶠ n in atTop, -ε n ≤ a n) :
    0 ≤ L := by
  have hneg : Tendsto (fun n => -ε n) atTop (𝓝 0) := by
    simpa using hε.neg
  exact le_of_tendsto_of_tendsto hneg ha hlower

lemma complex_limit_re_nonneg_of_eventually_lower_neg_tendsto_zero
    {ε : ℕ → ℝ} {a : ℕ → ℂ} {z : ℂ}
    (hε : Tendsto ε atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 z))
    (hlower : ∀ᶠ n in atTop, -ε n ≤ (a n).re) :
    0 ≤ z.re := by
  exact real_limit_nonneg_of_eventually_lower_neg_tendsto_zero
    hε (Complex.continuous_re.tendsto z |>.comp ha) hlower

lemma complex_limit_im_eq_zero_of_eventually_im_eq_zero
    {a : ℕ → ℂ} {z : ℂ}
    (ha : Tendsto a atTop (𝓝 z))
    (him : ∀ᶠ n in atTop, (a n).im = 0) :
    z.im = 0 := by
  have haim : Tendsto (fun n => (a n).im) atTop (𝓝 z.im) :=
    Complex.continuous_im.tendsto z |>.comp ha
  have hzero_to_z :
      Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 z.im) :=
    Filter.Tendsto.congr' him haim
  exact tendsto_nhds_unique hzero_to_z tendsto_const_nhds

lemma complex_limit_re_nonneg_and_im_zero
    {ε : ℕ → ℝ} {a : ℕ → ℂ} {z : ℂ}
    (hε : Tendsto ε atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 z))
    (hlower : ∀ᶠ n in atTop, -ε n ≤ (a n).re)
    (him : ∀ᶠ n in atTop, (a n).im = 0) :
    0 ≤ z.re ∧ z.im = 0 :=
  ⟨complex_limit_re_nonneg_of_eventually_lower_neg_tendsto_zero hε ha hlower,
    complex_limit_im_eq_zero_of_eventually_im_eq_zero ha him⟩

lemma normalizedDftCoeff_zero_re_eq_card_div
    {p : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    (normalizedDftCoeff T 0).re = (T.card : ℝ) / (p : ℝ) := by
  rw [normalizedDftCoeff_zero_eq_card_div]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
  simp

lemma normalizedDftCoeff_zero_im_eq_zero
    {p : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    (normalizedDftCoeff T 0).im = 0 := by
  rw [normalizedDftCoeff_zero_eq_card_div]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
  simp

lemma exists_strictMono_subseq_tendsto_of_norm_le_one
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∃ z : ℂ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 z) := by
  let K : Set ℂ := Metric.closedBall 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : ℂ) 1
  have haK : ∀ n, a n ∈ K := by
    intro n
    simp [K, Metric.mem_closedBall, dist_zero_right, ha n]
  rcases hK.tendsto_subseq haK with ⟨z, _hzK, φ, hφ, hlim⟩
  exact ⟨z, φ, hφ, hlim⟩

lemma exists_strictMono_subseq_tendsto_on_finset_of_norm_le_one
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (a : ι → ℕ → ℂ)
    (ha : ∀ i ∈ I, ∀ n, ‖a i n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ I, ∃ z : ℂ,
        Tendsto (fun n => a i (φ n)) atTop (𝓝 z) := by
  classical
  revert ha
  refine Finset.induction_on I ?base ?step
  · intro _ha
    refine ⟨id, strictMono_id, ?_⟩
    simp
  · intro i I hiI ih hInsert
    have hI : ∀ j ∈ I, ∀ n, ‖a j n‖ ≤ 1 := by
      intro j hj n
      exact hInsert j (by simp [hj]) n
    rcases ih hI with ⟨φ, hφ, hconv⟩
    have hi_bound : ∀ n, ‖a i (φ n)‖ ≤ 1 := by
      intro n
      exact hInsert i (by simp) (φ n)
    rcases exists_strictMono_subseq_tendsto_of_norm_le_one
        (fun n => a i (φ n)) hi_bound with
      ⟨zi, ψ, hψ, hi_lim⟩
    refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
    intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hjI
    · refine ⟨zi, ?_⟩
      simpa [Function.comp_def] using hi_lim
    · rcases hconv j hjI with ⟨zj, hj_lim⟩
      refine ⟨zj, ?_⟩
      simpa [Function.comp_def] using hj_lim.comp hψ.tendsto_atTop

lemma exists_strictMono_subseq_tendsto_fintype_of_norm_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ → ℂ)
    (ha : ∀ i n, ‖a i n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, ∃ z : ℂ,
        Tendsto (fun n => a i (φ n)) atTop (𝓝 z) := by
  classical
  rcases exists_strictMono_subseq_tendsto_on_finset_of_norm_le_one
      (I := (Finset.univ : Finset ι)) a (by
        intro i _hi n
        exact ha i n) with
    ⟨φ, hφ, hconv⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  exact hconv i (by simp)

/-- Closed unit disk, used as a compact target for countable diagonal
subsequence extraction. -/
abbrev ClosedUnitDisk : Type :=
  {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) 1}

lemma compactSpace_closedUnitDisk : CompactSpace ClosedUnitDisk := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    ProperSpace.isCompact_closedBall (0 : ℂ) 1
  exact isCompact_iff_compactSpace.mp hK

lemma exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one
    {ι : Type*} [Countable ι] (a : ι → ℕ → ℂ)
    (ha : ∀ i n, ‖a i n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, ∃ z : ℂ,
        Tendsto (fun n => a i (φ n)) atTop (𝓝 z) := by
  let x : ℕ → (ι → ClosedUnitDisk) := fun n i =>
    ⟨a i n, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact ha i n⟩
  letI : CompactSpace ClosedUnitDisk := compactSpace_closedUnitDisk
  rcases CompactSpace.tendsto_subseq x with ⟨y, φ, hφ, hlim⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  refine ⟨(y i : ℂ), ?_⟩
  have hcont :
      Continuous (fun y : ι → ClosedUnitDisk => ((y i : ClosedUnitDisk) : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have hi := (hcont.tendsto y).comp hlim
  simpa [x] using hi

/-- Countable diagonal stabilization for decidable relations.  This is the
relation-theoretic companion to coefficient convergence: after passing to one
subsequence, every countably indexed yes/no relation is eventually constantly
true or eventually constantly false. -/
lemma exists_strictMono_subseq_eventually_const_countable_family
    {ι : Type*} [Countable ι] (P : ι → ℕ → Prop)
    [∀ i n, Decidable (P i n)] :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, (∀ᶠ n in atTop, P i (φ n)) ∨
        (∀ᶠ n in atTop, ¬ P i (φ n)) := by
  let x : ℕ → (ι → Bool) := fun n i => decide (P i n)
  rcases CompactSpace.tendsto_subseq x with ⟨y, φ, hφ, hlim⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  have hcont : Continuous (fun y : ι → Bool => y i) := continuous_apply i
  have hi : Tendsto (fun n => x (φ n) i) atTop (𝓝 (y i)) :=
    (hcont.tendsto y).comp hlim
  have hmem : ({y i} : Set Bool) ∈ 𝓝 (y i) := by
    exact (isOpen_discrete ({y i} : Set Bool)).mem_nhds rfl
  have heq : ∀ᶠ n in atTop, x (φ n) i = y i := by
    simpa using hi.eventually hmem
  cases hy : y i <;> simp [x, hy] at heq ⊢
  · exact Or.inr heq
  · exact Or.inl heq

/-- Any convergent sequence of Route A forbidden-set Fourier coefficients has
real nonnegative limit.  This is the finite-hypothesis part of the future
large-spectrum compact model. -/
lemma FourierAvoidanceCounterSeq.fourierCoeff_limit_re_nonneg_and_im_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (r : ∀ n : ℕ, ZMod (S.p n)) {z : ℂ}
    (hlim :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            normalizedDftCoeff (S.F n) (r n)))
        atTop (𝓝 z)) :
    0 ≤ z.re ∧ z.im = 0 := by
  refine complex_limit_re_nonneg_and_im_zero S.eps_tendsto_zero hlim ?hlower ?him
  · exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
      exact S.F_fourier_lower n (r n))
  · exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
      exact normalizedDftCoeff_im_eq_zero_of_symmetric (S.F_sym n) (r n))

lemma FourierAvoidanceCounterSeq.forbiddenCoeff_subseq_limit_re_nonneg_and_im_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (r : ∀ n : ℕ, ZMod (S.p n)) {z : ℂ}
    (hlim :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            normalizedDftCoeff (S.F (φ n)) (r (φ n))))
        atTop (𝓝 z)) :
    0 ≤ z.re ∧ z.im = 0 := by
  refine complex_limit_re_nonneg_and_im_zero
    (S.eps_tendsto_zero.comp hφ.tendsto_atTop) hlim ?hlower ?him
  · exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩
      exact S.F_fourier_lower (φ n) (r (φ n)))
  · exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩
      exact normalizedDftCoeff_im_eq_zero_of_symmetric
        (S.F_sym (φ n)) (r (φ n)))

lemma FourierAvoidanceCounterSeq.exists_forbiddenCoeff_subseq_tendsto
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (r : ∀ n : ℕ, ZMod (S.p n)) :
    ∃ z : ℂ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        Tendsto
          (fun n =>
            (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
              normalizedDftCoeff (S.F (φ n)) (r (φ n))))
          atTop (𝓝 z) := by
  let a : ℕ → ℂ := fun n =>
    (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
      normalizedDftCoeff (S.F n) (r n))
  have ha : ∀ n, ‖a n‖ ≤ 1 := by
    intro n
    dsimp [a]
    letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
    exact norm_normalizedDftCoeff_indicator_le_one (S.F n) (r n)
  rcases exists_strictMono_subseq_tendsto_of_norm_le_one a ha with
    ⟨z, φ, hφ, hlim⟩
  refine ⟨z, φ, hφ, ?_⟩
  simpa [a, Function.comp_def] using hlim

lemma FourierAvoidanceCounterSeq.exists_forbiddenCoeff_subseq_tendsto_on_finset
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (r : ι → ∀ n : ℕ, ZMod (S.p n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ I, ∃ z : ℂ,
        Tendsto
          (fun n =>
            (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
              normalizedDftCoeff (S.F (φ n)) (r i (φ n))))
          atTop (𝓝 z) := by
  let a : ι → ℕ → ℂ := fun i n =>
    (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
      normalizedDftCoeff (S.F n) (r i n))
  have ha : ∀ i ∈ I, ∀ n, ‖a i n‖ ≤ 1 := by
    intro i _hi n
    dsimp [a]
    letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
    exact norm_normalizedDftCoeff_indicator_le_one (S.F n) (r i n)
  rcases exists_strictMono_subseq_tendsto_on_finset_of_norm_le_one I a ha with
    ⟨φ, hφ, hconv⟩
  refine ⟨φ, hφ, ?_⟩
  intro i hi
  rcases hconv i hi with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simpa [a] using hz

lemma FourierAvoidanceCounterSeq.exists_forbiddenCoeff_subseq_tendsto_fintype
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ∀ n : ℕ, ZMod (S.p n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, ∃ z : ℂ,
        Tendsto
          (fun n =>
            (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
              normalizedDftCoeff (S.F (φ n)) (r i (φ n))))
          atTop (𝓝 z) := by
  classical
  rcases S.exists_forbiddenCoeff_subseq_tendsto_on_finset
      (I := (Finset.univ : Finset ι)) r with
    ⟨φ, hφ, hconv⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  exact hconv i (by simp)

lemma FourierAvoidanceCounterSeq.exists_forbiddenCoeff_subseq_tendsto_countable
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (r : ℕ → ∀ n : ℕ, ZMod (S.p n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ℕ, ∃ z : ℂ,
        Tendsto
          (fun n =>
            (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
              normalizedDftCoeff (S.F (φ n)) (r i (φ n))))
          atTop (𝓝 z) := by
  let a : ℕ → ℕ → ℂ := fun i n =>
    (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
      normalizedDftCoeff (S.F n) (r i n))
  have ha : ∀ i n, ‖a i n‖ ≤ 1 := by
    intro i n
    dsimp [a]
    letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
    exact norm_normalizedDftCoeff_indicator_le_one (S.F n) (r i n)
  rcases exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one a ha with
    ⟨φ, hφ, hconv⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  rcases hconv i with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simpa [a] using hz

lemma FourierAvoidanceCounterSeq.exists_forbidden_and_vertexCoeff_subseq_tendsto_countable
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (rF rU : ℕ → ∀ n : ℕ, ZMod (S.p n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i : ℕ, ∃ zF : ℂ,
        Tendsto
          (fun n =>
            (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
              normalizedDftCoeff (S.F (φ n)) (rF i (φ n))))
          atTop (𝓝 zF)) ∧
      (∀ i : ℕ, ∃ zU : ℂ,
        Tendsto
          (fun n =>
            (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
              normalizedDftCoeff (S.U (φ n)) (rU i (φ n))))
          atTop (𝓝 zU)) := by
  let a : Sum ℕ ℕ → ℕ → ℂ := fun tag n =>
    match tag with
    | Sum.inl i =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          normalizedDftCoeff (S.F n) (rF i n))
    | Sum.inr i =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          normalizedDftCoeff (S.U n) (rU i n))
  have ha : ∀ tag n, ‖a tag n‖ ≤ 1 := by
    intro tag n
    cases tag with
    | inl i =>
        dsimp [a]
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        exact norm_normalizedDftCoeff_indicator_le_one (S.F n) (rF i n)
    | inr i =>
        dsimp [a]
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        exact norm_normalizedDftCoeff_indicator_le_one (S.U n) (rU i n)
  rcases exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one a ha with
    ⟨φ, hφ, hconv⟩
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro i
    rcases hconv (Sum.inl i) with ⟨zF, hzF⟩
    refine ⟨zF, ?_⟩
    simpa [a] using hzF
  · intro i
    rcases hconv (Sum.inr i) with ⟨zU, hzU⟩
    refine ⟨zU, ?_⟩
    simpa [a] using hzU

lemma FourierAvoidanceCounterSeq.zero_forbiddenCoeff_limit_le_one_sub_rho_and_im_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) {z : ℂ}
    (hlim :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            normalizedDftCoeff (S.F n) 0))
        atTop (𝓝 z)) :
    z.re ≤ 1 - ρ ∧ z.im = 0 := by
  have hre_tendsto :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            (normalizedDftCoeff (S.F n) 0).re))
        atTop (𝓝 z.re) :=
    Complex.continuous_re.tendsto z |>.comp hlim
  have hupper :
      (fun n =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          (normalizedDftCoeff (S.F n) 0).re))
        ≤ᶠ[atTop] fun _n => 1 - ρ := by
    exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
      have hp_pos : 0 < (S.p n : ℝ) := by exact_mod_cast (S.prime n).pos
      change (normalizedDftCoeff (S.F n) 0).re ≤ 1 - ρ
      rw [normalizedDftCoeff_zero_re_eq_card_div]
      exact (div_le_iff₀ hp_pos).mpr (S.F_density n))
  have hre_le : z.re ≤ 1 - ρ :=
    le_of_tendsto_of_tendsto hre_tendsto tendsto_const_nhds hupper
  have him : z.im = 0 :=
    complex_limit_im_eq_zero_of_eventually_im_eq_zero hlim
      (Filter.Eventually.of_forall (fun n => by
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        exact normalizedDftCoeff_zero_im_eq_zero (S.F n)))
  exact ⟨hre_le, him⟩

lemma FourierAvoidanceCounterSeq.zero_forbiddenCoeff_subseq_limit_le_one_sub_rho_and_im_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {φ : ℕ → ℕ} (_hφ : StrictMono φ) {z : ℂ}
    (hlim :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            normalizedDftCoeff (S.F (φ n)) 0))
        atTop (𝓝 z)) :
    z.re ≤ 1 - ρ ∧ z.im = 0 := by
  have hre_tendsto :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            (normalizedDftCoeff (S.F (φ n)) 0).re))
        atTop (𝓝 z.re) :=
    Complex.continuous_re.tendsto z |>.comp hlim
  have hupper :
      (fun n =>
        (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
          (normalizedDftCoeff (S.F (φ n)) 0).re))
        ≤ᶠ[atTop] fun _n => 1 - ρ := by
    exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩
      have hp_pos : 0 < (S.p (φ n) : ℝ) := by
        exact_mod_cast (S.prime (φ n)).pos
      change (normalizedDftCoeff (S.F (φ n)) 0).re ≤ 1 - ρ
      rw [normalizedDftCoeff_zero_re_eq_card_div]
      exact (div_le_iff₀ hp_pos).mpr (S.F_density (φ n)))
  have hre_le : z.re ≤ 1 - ρ :=
    le_of_tendsto_of_tendsto hre_tendsto tendsto_const_nhds hupper
  have him : z.im = 0 :=
    complex_limit_im_eq_zero_of_eventually_im_eq_zero hlim
      (Filter.Eventually.of_forall (fun n => by
        letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩
        exact normalizedDftCoeff_zero_im_eq_zero (S.F (φ n))))
  exact ⟨hre_le, him⟩

lemma FourierAvoidanceCounterSeq.zero_vertexCoeff_limit_ge_alpha_and_im_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) {z : ℂ}
    (hlim :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            normalizedDftCoeff (S.U n) 0))
        atTop (𝓝 z)) :
    α ≤ z.re ∧ z.im = 0 := by
  have hre_tendsto :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            (normalizedDftCoeff (S.U n) 0).re))
        atTop (𝓝 z.re) :=
    Complex.continuous_re.tendsto z |>.comp hlim
  have hlower :
      (fun _n => α) ≤ᶠ[atTop]
        fun n =>
          (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            (normalizedDftCoeff (S.U n) 0).re) := by
    exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
      have hp_pos : 0 < (S.p n : ℝ) := by exact_mod_cast (S.prime n).pos
      change α ≤ (normalizedDftCoeff (S.U n) 0).re
      rw [normalizedDftCoeff_zero_re_eq_card_div]
      exact (le_div_iff₀ hp_pos).mpr (S.U_density n))
  have halpha_le : α ≤ z.re :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hre_tendsto hlower
  have him : z.im = 0 :=
    complex_limit_im_eq_zero_of_eventually_im_eq_zero hlim
      (Filter.Eventually.of_forall (fun n => by
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        exact normalizedDftCoeff_zero_im_eq_zero (S.U n)))
  exact ⟨halpha_le, him⟩

lemma FourierAvoidanceCounterSeq.zero_vertexCoeff_subseq_limit_ge_alpha_and_im_zero
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {φ : ℕ → ℕ} (_hφ : StrictMono φ) {z : ℂ}
    (hlim :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            normalizedDftCoeff (S.U (φ n)) 0))
        atTop (𝓝 z)) :
    α ≤ z.re ∧ z.im = 0 := by
  have hre_tendsto :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            (normalizedDftCoeff (S.U (φ n)) 0).re))
        atTop (𝓝 z.re) :=
    Complex.continuous_re.tendsto z |>.comp hlim
  have hlower :
      (fun _n => α) ≤ᶠ[atTop]
        fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            (normalizedDftCoeff (S.U (φ n)) 0).re) := by
    exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩
      have hp_pos : 0 < (S.p (φ n) : ℝ) := by
        exact_mod_cast (S.prime (φ n)).pos
      change α ≤ (normalizedDftCoeff (S.U (φ n)) 0).re
      rw [normalizedDftCoeff_zero_re_eq_card_div]
      exact (le_div_iff₀ hp_pos).mpr (S.U_density (φ n)))
  have halpha_le : α ≤ z.re :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hre_tendsto hlower
  have him : z.im = 0 :=
    complex_limit_im_eq_zero_of_eventually_im_eq_zero hlim
      (Filter.Eventually.of_forall (fun n => by
        letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩
        exact normalizedDftCoeff_zero_im_eq_zero (S.U (φ n))))
  exact ⟨halpha_le, him⟩

/-- Countable coefficient-limit data after passing to a common subsequence.

This is the countable diagonal-extraction part of the future compact limit
model: for chosen finite frequencies `rFᵢ,n` and `rUᵢ,n`, all corresponding
forbidden and vertex-weight Fourier coefficients converge along one strictly
monotone subsequence.  The Route A lower-bias and symmetry hypotheses already
force the forbidden limits to be real and nonnegative. -/
structure CountableCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (rF rU : ℕ → ∀ n : ℕ, ZMod (S.p n)) where
  φ : ℕ → ℕ
  strictMono_φ : StrictMono φ
  fCoeff : ℕ → ℂ
  uCoeff : ℕ → ℂ
  fCoeff_tendsto : ∀ i : ℕ,
    Tendsto
      (fun n =>
        (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
          normalizedDftCoeff (S.F (φ n)) (rF i (φ n))))
      atTop (𝓝 (fCoeff i))
  uCoeff_tendsto : ∀ i : ℕ,
    Tendsto
      (fun n =>
        (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
          normalizedDftCoeff (S.U (φ n)) (rU i (φ n))))
      atTop (𝓝 (uCoeff i))
  fCoeff_nonneg : ∀ i : ℕ, 0 ≤ (fCoeff i).re
  fCoeff_im_eq_zero : ∀ i : ℕ, (fCoeff i).im = 0

theorem FourierAvoidanceCounterSeq.exists_countableCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (rF rU : ℕ → ∀ n : ℕ, ZMod (S.p n)) :
    ∃ _data : CountableCoeffLimitData S rF rU, True := by
  classical
  rcases S.exists_forbidden_and_vertexCoeff_subseq_tendsto_countable rF rU with
    ⟨φ, hφ, hF, hU⟩
  choose fCoeff hfCoeff using hF
  choose uCoeff huCoeff using hU
  refine ⟨{
    φ := φ
    strictMono_φ := hφ
    fCoeff := fCoeff
    uCoeff := uCoeff
    fCoeff_tendsto := hfCoeff
    uCoeff_tendsto := huCoeff
    fCoeff_nonneg := ?_
    fCoeff_im_eq_zero := ?_
  }, trivial⟩
  · intro i
    exact (S.forbiddenCoeff_subseq_limit_re_nonneg_and_im_zero
      hφ (rF i) (hfCoeff i)).1
  · intro i
    exact (S.forbiddenCoeff_subseq_limit_re_nonneg_and_im_zero
      hφ (rF i) (hfCoeff i)).2

lemma CountableCoeffLimitData.fCoeff_zero_index_le_one_sub_rho_and_im_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {rF rU : ℕ → ∀ n : ℕ, ZMod (S.p n)}
    (data : CountableCoeffLimitData S rF rU) {i : ℕ}
    (hi : ∀ n : ℕ, rF i n = 0) :
    (data.fCoeff i).re ≤ 1 - ρ ∧ (data.fCoeff i).im = 0 := by
  have hlim0 :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩;
            normalizedDftCoeff (S.F (data.φ n)) 0))
        atTop (𝓝 (data.fCoeff i)) := by
    refine Filter.Tendsto.congr' ?_ (data.fCoeff_tendsto i)
    exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
      simp [hi (data.φ n)])
  exact S.zero_forbiddenCoeff_subseq_limit_le_one_sub_rho_and_im_zero
    data.strictMono_φ hlim0

lemma CountableCoeffLimitData.uCoeff_zero_index_ge_alpha_and_im_zero
    {m : ℕ} {α ρ : ℝ} {S : FourierAvoidanceCounterSeq m α ρ}
    {rF rU : ℕ → ∀ n : ℕ, ZMod (S.p n)}
    (data : CountableCoeffLimitData S rF rU) {i : ℕ}
    (hi : ∀ n : ℕ, rU i n = 0) :
    α ≤ (data.uCoeff i).re ∧ (data.uCoeff i).im = 0 := by
  have hlim0 :
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩;
            normalizedDftCoeff (S.U (data.φ n)) 0))
        atTop (𝓝 (data.uCoeff i)) := by
    refine Filter.Tendsto.congr' ?_ (data.uCoeff_tendsto i)
    exact Filter.Eventually.of_forall (fun n => by
      letI : NeZero (S.p (data.φ n)) := ⟨(S.prime (data.φ n)).ne_zero⟩
      simp [hi (data.φ n)])
  exact S.zero_vertexCoeff_subseq_limit_ge_alpha_and_im_zero
    data.strictMono_φ hlim0

/-! ## Large-spectrum labelled coefficient limits -/

/-- Countable index type for all dyadic large-spectrum labels. -/
abbrev LargeSpectrumIndex : Type :=
  Sigma LargeSpectrumLabel

/-- The frequency selected by a large-spectrum label index at finite level `n`.
Unused labels are interpreted as the zero frequency. -/
noncomputable def FourierAvoidanceCounterSeq.largeSpectrumIndexFreq
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n : ℕ) (idx : LargeSpectrumIndex) : ZMod (S.p n) :=
  S.largeSpectrumLabelFreq n idx.1 idx.2

lemma FourierAvoidanceCounterSeq.exists_largeSpectrumIndexFreq_eq_of_mem
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    {n k : ℕ} {r : ZMod (S.p n)} (hr : r ∈ S.largeSpectrumAt n k) :
    ∃ idx : LargeSpectrumIndex,
      idx.1 = k ∧ S.largeSpectrumIndexFreq n idx = r := by
  refine ⟨⟨k, S.largeSpectrumAtEmbedding n k ⟨r, hr⟩⟩, rfl, ?_⟩
  exact S.largeSpectrumLabelFreq_embedding r hr

/-- Coefficient limits indexed by all labelled dyadic large spectra. -/
structure LargeSpectrumCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) where
  φ : ℕ → ℕ
  strictMono_φ : StrictMono φ
  fCoeff : LargeSpectrumIndex → ℂ
  uCoeff : LargeSpectrumIndex → ℂ
  fCoeff_tendsto : ∀ idx : LargeSpectrumIndex,
    Tendsto
      (fun n =>
        (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
          normalizedDftCoeff (S.F (φ n))
            (S.largeSpectrumIndexFreq (φ n) idx)))
      atTop (𝓝 (fCoeff idx))
  uCoeff_tendsto : ∀ idx : LargeSpectrumIndex,
    Tendsto
      (fun n =>
        (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
          normalizedDftCoeff (S.U (φ n))
            (S.largeSpectrumIndexFreq (φ n) idx)))
      atTop (𝓝 (uCoeff idx))
  fCoeff_nonneg : ∀ idx : LargeSpectrumIndex, 0 ≤ (fCoeff idx).re
  fCoeff_im_eq_zero : ∀ idx : LargeSpectrumIndex, (fCoeff idx).im = 0

theorem FourierAvoidanceCounterSeq.exists_largeSpectrumCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) :
    ∃ _data : LargeSpectrumCoeffLimitData S, True := by
  classical
  let a : Sum LargeSpectrumIndex LargeSpectrumIndex → ℕ → ℂ := fun tag n =>
    match tag with
    | Sum.inl idx =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          normalizedDftCoeff (S.F n) (S.largeSpectrumIndexFreq n idx))
    | Sum.inr idx =>
        (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
          normalizedDftCoeff (S.U n) (S.largeSpectrumIndexFreq n idx))
  have ha : ∀ tag n, ‖a tag n‖ ≤ 1 := by
    intro tag n
    cases tag with
    | inl idx =>
        dsimp [a]
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        exact norm_normalizedDftCoeff_indicator_le_one
          (S.F n) (S.largeSpectrumIndexFreq n idx)
    | inr idx =>
        dsimp [a]
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        exact norm_normalizedDftCoeff_indicator_le_one
          (S.U n) (S.largeSpectrumIndexFreq n idx)
  rcases exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one a ha with
    ⟨φ, hφ, hconv⟩
  have hF : ∀ idx : LargeSpectrumIndex, ∃ z : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            normalizedDftCoeff (S.F (φ n))
              (S.largeSpectrumIndexFreq (φ n) idx)))
        atTop (𝓝 z) := by
    intro idx
    rcases hconv (Sum.inl idx) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [a] using hz
  have hU : ∀ idx : LargeSpectrumIndex, ∃ z : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            normalizedDftCoeff (S.U (φ n))
              (S.largeSpectrumIndexFreq (φ n) idx)))
        atTop (𝓝 z) := by
    intro idx
    rcases hconv (Sum.inr idx) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [a] using hz
  choose fCoeff hfCoeff using hF
  choose uCoeff huCoeff using hU
  refine ⟨{
    φ := φ
    strictMono_φ := hφ
    fCoeff := fCoeff
    uCoeff := uCoeff
    fCoeff_tendsto := hfCoeff
    uCoeff_tendsto := huCoeff
    fCoeff_nonneg := ?_
    fCoeff_im_eq_zero := ?_
  }, trivial⟩
  · intro idx
    exact (S.forbiddenCoeff_subseq_limit_re_nonneg_and_im_zero
      hφ (fun n => S.largeSpectrumIndexFreq n idx) (hfCoeff idx)).1
  · intro idx
    exact (S.forbiddenCoeff_subseq_limit_re_nonneg_and_im_zero
      hφ (fun n => S.largeSpectrumIndexFreq n idx) (hfCoeff idx)).2

/-! ## Extended large-spectrum coefficient limits including zero frequency -/

/-- Extended large-spectrum index. `none` denotes the zero character; `some idx`
denotes a labelled dyadic large-spectrum frequency. -/
abbrev ExtendedLargeSpectrumIndex : Type :=
  Option LargeSpectrumIndex

/-- Frequency selected by an extended large-spectrum index. -/
noncomputable def FourierAvoidanceCounterSeq.extendedLargeSpectrumIndexFreq
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ)
    (n : ℕ) : ExtendedLargeSpectrumIndex → ZMod (S.p n)
  | none => 0
  | some idx => S.largeSpectrumIndexFreq n idx

/-- Coefficient limits for all labelled large-spectrum frequencies and the
zero character, along one subsequence.  This is the coefficient-level interface
needed before building the compact group/model. -/
structure ExtendedLargeSpectrumCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) where
  φ : ℕ → ℕ
  strictMono_φ : StrictMono φ
  fCoeff : ExtendedLargeSpectrumIndex → ℂ
  uCoeff : ExtendedLargeSpectrumIndex → ℂ
  fCoeff_tendsto : ∀ idx : ExtendedLargeSpectrumIndex,
    Tendsto
      (fun n =>
        (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
          normalizedDftCoeff (S.F (φ n))
            (S.extendedLargeSpectrumIndexFreq (φ n) idx)))
      atTop (𝓝 (fCoeff idx))
  uCoeff_tendsto : ∀ idx : ExtendedLargeSpectrumIndex,
    Tendsto
      (fun n =>
        (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
          normalizedDftCoeff (S.U (φ n))
            (S.extendedLargeSpectrumIndexFreq (φ n) idx)))
      atTop (𝓝 (uCoeff idx))
  fCoeff_nonneg : ∀ idx : ExtendedLargeSpectrumIndex, 0 ≤ (fCoeff idx).re
  fCoeff_im_eq_zero : ∀ idx : ExtendedLargeSpectrumIndex, (fCoeff idx).im = 0
  zero_fCoeff_le : (fCoeff none).re ≤ 1 - ρ
  zero_uCoeff_ge : α ≤ (uCoeff none).re
  zero_uCoeff_im_eq_zero : (uCoeff none).im = 0

theorem FourierAvoidanceCounterSeq.exists_extendedLargeSpectrumCoeffLimitData
    {m : ℕ} {α ρ : ℝ} (S : FourierAvoidanceCounterSeq m α ρ) :
    ∃ _data : ExtendedLargeSpectrumCoeffLimitData S, True := by
  classical
  let a : Sum ExtendedLargeSpectrumIndex ExtendedLargeSpectrumIndex → ℕ → ℂ :=
    fun tag n =>
      match tag with
      | Sum.inl idx =>
          (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            normalizedDftCoeff (S.F n) (S.extendedLargeSpectrumIndexFreq n idx))
      | Sum.inr idx =>
          (letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩;
            normalizedDftCoeff (S.U n) (S.extendedLargeSpectrumIndexFreq n idx))
  have ha : ∀ tag n, ‖a tag n‖ ≤ 1 := by
    intro tag n
    cases tag with
    | inl idx =>
        dsimp [a]
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        exact norm_normalizedDftCoeff_indicator_le_one
          (S.F n) (S.extendedLargeSpectrumIndexFreq n idx)
    | inr idx =>
        dsimp [a]
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        exact norm_normalizedDftCoeff_indicator_le_one
          (S.U n) (S.extendedLargeSpectrumIndexFreq n idx)
  rcases exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one a ha with
    ⟨φ, hφ, hconv⟩
  have hF : ∀ idx : ExtendedLargeSpectrumIndex, ∃ z : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            normalizedDftCoeff (S.F (φ n))
              (S.extendedLargeSpectrumIndexFreq (φ n) idx)))
        atTop (𝓝 z) := by
    intro idx
    rcases hconv (Sum.inl idx) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [a] using hz
  have hU : ∀ idx : ExtendedLargeSpectrumIndex, ∃ z : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (S.p (φ n)) := ⟨(S.prime (φ n)).ne_zero⟩;
            normalizedDftCoeff (S.U (φ n))
              (S.extendedLargeSpectrumIndexFreq (φ n) idx)))
        atTop (𝓝 z) := by
    intro idx
    rcases hconv (Sum.inr idx) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [a] using hz
  choose fCoeff hfCoeff using hF
  choose uCoeff huCoeff using hU
  have hf_nonneg_im : ∀ idx : ExtendedLargeSpectrumIndex,
      0 ≤ (fCoeff idx).re ∧ (fCoeff idx).im = 0 := by
    intro idx
    exact S.forbiddenCoeff_subseq_limit_re_nonneg_and_im_zero
      hφ (fun n => S.extendedLargeSpectrumIndexFreq n idx) (hfCoeff idx)
  have hf_zero :
      (fCoeff none).re ≤ 1 - ρ ∧ (fCoeff none).im = 0 := by
    exact S.zero_forbiddenCoeff_subseq_limit_le_one_sub_rho_and_im_zero
      hφ (by simpa [FourierAvoidanceCounterSeq.extendedLargeSpectrumIndexFreq]
        using hfCoeff none)
  have hu_zero :
      α ≤ (uCoeff none).re ∧ (uCoeff none).im = 0 := by
    exact S.zero_vertexCoeff_subseq_limit_ge_alpha_and_im_zero
      hφ (by simpa [FourierAvoidanceCounterSeq.extendedLargeSpectrumIndexFreq]
        using huCoeff none)
  refine ⟨{
    φ := φ
    strictMono_φ := hφ
    fCoeff := fCoeff
    uCoeff := uCoeff
    fCoeff_tendsto := hfCoeff
    uCoeff_tendsto := huCoeff
    fCoeff_nonneg := fun idx => (hf_nonneg_im idx).1
    fCoeff_im_eq_zero := fun idx => (hf_nonneg_im idx).2
    zero_fCoeff_le := hf_zero.1
    zero_uCoeff_ge := hu_zero.1
    zero_uCoeff_im_eq_zero := hu_zero.2
  }, trivial⟩

end Erdos42.FourierPositive
