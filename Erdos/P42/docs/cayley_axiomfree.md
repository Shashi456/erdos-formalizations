# Compact-Cayley Axiom-Free Roadmap

This note records the concrete implementation route for replacing

```lean
axiom compact_cayley_clique
```

with a theorem of the same name.

The compact-Cayley PDF proves exactly the theorem currently axiomatized: dense
symmetric zero-free Cayley graphs on `ZMod p` with nonpositively biased
nontrivial Fourier coefficients contain fixed-size cliques. The proof is by
contradiction through Fourier extraction, compact dual limits, spectral/cut
counting convergence, and compact clique forcing. The active public Route A has
a different axiom, `finite_fourier_avoidance_count`; this note is only about
removing the Route B axiom.

The target audit is:

```lean
#print axioms Erdos42.CompactCayley.compact_cayley_clique
```

Eventually this should report only Mathlib foundations such as `propext`,
`Classical.choice`, and `Quot.sound`.

## 0. Do Not Start By Editing `Main.lean`

`Main.lean` is already the downstream application. It is not the problem.

The problem is isolated in:

```lean
CompactCayley/CliqueAxiom.lean
```

Current declaration:

```lean
axiom compact_cayley_clique
    (ell : Nat) (eta : Real) (_hell : 2 <= ell) (_heta : 0 < eta) :
    exists eps : Real, 0 < eps /\
    exists p0 : Nat, forall p : Nat, [Fact p.Prime] -> p0 < p ->
    forall T : Finset (ZMod p),
      SymmetricFinset T ->
      (0 : ZMod p) notin T ->
      eta * (p : Real) <= (T.card : Real) ->
      FourierUpperIndicator T eps ->
      exists C : Finset (ZMod p),
        C.card = ell /\ CliqueInCayley T C
```

The first real goal is to replace it by a theorem of the same signature.
Everything else should be built to fill that proof.

## 1. Prove The Countersequence Contradiction

Do not try to prove the quantified `eps, p0` theorem directly. The existing
files already set up the correct contradiction reduction:

```lean
def CompactCayleyCliqueStatementExplicit (ell : Nat) (eta : Real) : Prop := ...
```

and

```lean
structure CayleyCounterSeq (ell : Nat) (eta : Real) where
  p : Nat -> Nat
  prime : forall n, (p n).Prime
  p_gt : forall n, n < p n
  T : forall n, Finset (ZMod (p n))
  T_sym : forall n, SymmetricFinset (T n)
  T_zero : forall n, (0 : ZMod (p n)) notin T n
  T_density : forall n, eta * (p n : Real) <= ((T n).card : Real)
  eps : Nat -> Real
  eps_pos : forall n, 0 < eps n
  eps_tendsto_zero : Tendsto eps atTop (nhds 0)
  T_fourier_upper : forall n, ...
  no_clique : forall n, not exists C, C.card = ell /\ CliqueInCayley (T n) C
```

The central theorem should be:

```lean
theorem CayleyCounterSeq.false
    {ell : Nat} {eta : Real}
    (hell : 2 <= ell) (heta : 0 < eta)
    (S : CayleyCounterSeq ell eta) :
    False := by
  ...
```

Then `compact_cayley_clique` becomes a short wrapper:

```lean
theorem compact_cayley_clique
    (ell : Nat) (eta : Real) (hell : 2 <= ell) (heta : 0 < eta) :
    exists eps : Real, 0 < eps /\
    exists p0 : Nat, forall p : Nat, [Fact p.Prime] -> p0 < p ->
    forall T : Finset (ZMod p),
      SymmetricFinset T ->
      (0 : ZMod p) notin T ->
      eta * (p : Real) <= (T.card : Real) ->
      FourierUpperIndicator T eps ->
      exists C : Finset (ZMod p),
        C.card = ell /\ CliqueInCayley T C := by
  classical
  refine compactCayleyCliqueStatement_from_explicit ?_
  by_contra hfail
  rcases exists_cayleyCounterSeq_of_not_compactCayleyCliqueStatementExplicit hfail with
    ⟨S, _⟩
  exact CayleyCounterSeq.false hell heta S
```

## 2. Keep The Existing Finite Part

Treat these pieces as essentially done:

```lean
SpectralCutNorm.lean
CountingConvergence.lean
CliqueEndpoint.lean
Shared/FiniteReduction.lean
```

The crucial finite endpoint is:

```lean
exists_clique_of_spectral_density_transfer_sq
```

Morally, if a bounded model kernel `g : ZMod p -> C` has positive finite
`K_ell` density, and `g` is spectrally close to `1_T`, then `T` contains an
actual clique.

This avoids proving the full PDF Lemma 2.6 in maximum generality. Prove only
the narrower smoothed-kernel version needed for contradiction.

Final contradiction shape:

```lean
-- S : CayleyCounterSeq ell eta

obtain ⟨E⟩ := exists_cayleyExtraction S
let f := E.allowedKernel
have hpos : 0 < continuousCliqueDensity E.haar ell f := ...
obtain ⟨q, hq_spectral_small, hq_density_pos⟩ := ...
obtain ⟨n, hn_density, hn_spectral⟩ := ...

have hclique :
    exists C : Finset (ZMod (S.p n)),
      C.card = ell /\ CliqueInCayley (S.T n) C :=
  exists_clique_of_spectral_density_transfer_sq
    (S.T_sym n) (S.T_zero n)
    ...

exact S.no_clique n hclique
```

## 3. Add A Subsequence API

Fourier extraction passes to subsequences. Add:

```lean
CompactCayley/Subseq.lean
```

with:

```lean
def CayleyCounterSeq.subseq
    {ell : Nat} {eta : Real}
    (S : CayleyCounterSeq ell eta)
    (phi : Nat -> Nat) (hphi : StrictMono phi) :
    CayleyCounterSeq ell eta := ...
```

Fields:

```lean
p n      := S.p (phi n)
prime n := S.prime (phi n)
T n      := S.T (phi n)
eps n    := S.eps (phi n)
```

For `p_gt`, use:

```lean
have hn_le_phin : n <= phi n := ...
exact lt_of_le_of_lt hn_le_phin (S.p_gt (phi n))
```

Also prove:

```lean
lemma CayleyCounterSeq.subseq_tendsto_eps_zero
```

from:

```lean
S.eps_tendsto_zero.comp hphi.tendsto_atTop
```

Status: implemented in `CompactCayley/Subseq.lean`.

## 4. Build A Generic Fourier Extraction Module

Add:

```lean
CompactCayley/FourierExtraction.lean
```

Parameterize it over a bounded sequence of functions on prime cyclic groups:

```lean
structure FourierSeq where
  p : Nat -> Nat
  prime : forall n, (p n).Prime
  p_gt : forall n, n < p n
  h : forall n, ZMod (p n) -> C
  h_bound : forall n x, norm (h n x) <= 1
```

For a Cayley counterexample:

```lean
def CayleyCounterSeq.toFourierSeq
    (S : CayleyCounterSeq ell eta) : FourierSeq where
  p := S.p
  prime := S.prime
  p_gt := S.p_gt
  h := fun n => indicatorC (S.T n)
  h_bound := ...
```

Define normalized coefficient:

```lean
noncomputable def FourierSeq.coeff
    (F : FourierSeq) (n : Nat) :
    ZMod (F.p n) -> C := ...
```

Use the existing Parseval lemmas, or move the generic one from
`SpectralCutNorm.lean` into `Shared/FiniteFourier.lean` if needed later.

Status: first generic version implemented in `CompactCayley/FourierExtraction.lean`.

## 5. Use Non-Nested Large Spectrum Labels

For each positive threshold `q`, define:

```lean
def largeSpectrum
    (F : FourierSeq) (q : PNat) (n : Nat) :
    Finset (ZMod (F.p n)) :=
  Finset.univ.filter fun r =>
    ((q : Real)^-1 : Real) < norm (F.coeff n r)
```

Prove:

```lean
lemma largeSpectrum_card_le
    (F : FourierSeq) (q : PNat) (n : Nat) :
    (largeSpectrum F q n).card <= q^2 := ...
```

The proof is Parseval:

```text
|L_n(q)| q^-2 <= sum_r |hhat_n(r)|^2 <= 1
```

Introduce:

```lean
def LargeLabel := Sigma fun q : PNat => Fin (q^2 + 1)
```

For every `q,n`, choose a covering map. Duplicates are harmless; the quotient
will identify eventually equal labels.

Required helper:

```lean
lemma exists_cover_map_of_card_le
    {alpha : Type*} [Inhabited alpha]
    (s : Finset alpha) (m : Nat)
    (hcard : s.card <= m) :
    exists f : Fin m -> alpha, forall x in s, exists i, f i = x := ...
```

Status: implemented in `CompactCayley/FourierExtraction.lean`.

## 6. Build The Extraction Group `Gamma`

Let:

```lean
Label := LargeLabel
FAb := FreeAbelianGroup Label
```

For every word `w : FAb`, define its finite lift:

```lean
noncomputable def wordLift
    (F : FourierSeq)
    (labelFreq : Label -> forall n, ZMod (F.p n))
    (w : FreeAbelianGroup Label)
    (n : Nat) :
    ZMod (F.p n) := ...
```

The lift is the additive evaluation of the free abelian word using the finite
frequencies.

Use a diagonal subsequence on the countable family of words. Stabilize/extract:

```lean
-- eventual truth value
wordLift w n = 0

-- coefficient convergence
F.coeff n (wordLift w n)
```

Target theorem:

```lean
theorem exists_stable_fourier_subseq
    (F : FourierSeq)
    (labelFreq : Label -> forall n, ZMod (F.p n)) :
    exists phi : Nat -> Nat,
      StrictMono phi /\
      (forall w : FreeAbelianGroup Label,
        exists b : Bool,
          forallᶠ n in atTop,
            (wordLift F labelFreq w (phi n) = 0) = b) /\
      (forall w : FreeAbelianGroup Label,
        exists c : C,
          Tendsto
            (fun n =>
              letI : NeZero (F.p (phi n)) := ⟨(F.prime (phi n)).ne_zero⟩
              F.coeff (phi n) (wordLift F labelFreq w (phi n)))
            atTop
            (nhds c)) := ...
```

After passing to the subsequence, define:

```lean
def eventualKernel
    (F : FourierSeq) (...) :
    AddSubgroup (FreeAbelianGroup Label) where
  carrier := {w | forallᶠ n in atTop, wordLift F labelFreq w n = 0}
  ...
```

Then:

```lean
abbrev Gamma := FreeAbelianGroup Label ⧸ eventualKernel F labelFreq
```

Needed instances:

```lean
instance : AddCommGroup Gamma := ...
instance : Countable Gamma := ...
```

Finite lifts of quotient elements should use arbitrary representatives:

```lean
noncomputable def lift
    (gamma : Gamma) (n : Nat) :
    ZMod (F.p n) :=
  wordLift F labelFreq (Quot.out gamma) n
```

Algebraic properties are only eventual:

```lean
lemma eventually_lift_zero :
    forallᶠ n in atTop, lift (0 : Gamma) n = 0 := ...

lemma eventually_lift_add (gamma delta : Gamma) :
    forallᶠ n in atTop,
      lift (gamma + delta) n = lift gamma n + lift delta n := ...

lemma eventually_lift_neg (gamma : Gamma) :
    forallᶠ n in atTop,
      lift (-gamma) n = - lift gamma n := ...

lemma eventually_lift_ne_of_ne {gamma delta : Gamma} (h : gamma != delta) :
    forallᶠ n in atTop, lift gamma n != lift delta n := ...

lemma eventually_injOn_lift
    (E : Finset Gamma) :
    forallᶠ n in atTop,
      Set.InjOn (fun gamma => lift gamma n) (E : Set Gamma) := ...
```

Status: formal word lifts and the eventual-kernel quotient skeleton are
implemented in `CompactCayley/ExtractionGroup.lean`. Diagonal stability is in
`CompactCayley/StableExtraction.lean`, and the quotient representative lift API
with eventual zero/add/neg/sub/nonzero and finite-set injectivity facts is in
`CompactCayley/QuotientLift.lean`.

## 7. Prove `Gamma` Is Torsion-Free

This is required for connectedness of the compact dual.

Target:

```lean
instance extractionGroup_isAddTorsionFree :
    IsAddTorsionFree Gamma := ...
```

Proof outline:

If `m • gamma = 0`, then for large `n`,

```lean
m • lift gamma n = 0
```

inside `ZMod (F.p n)`.

Since `F.p n -> infinity`, for fixed `m`, eventually `F.p n` does not divide
`m`. Since `F.p n` is prime, `ZMod (F.p n)` has no nontrivial `m`-torsion, so
`lift gamma n = 0` eventually. Therefore `gamma = 0` in the quotient.

Needed finite lemma:

```lean
lemma zmod_prime_no_smul_eq_zero
    {p m : Nat} (hp : p.Prime) (hpm : not p ∣ m)
    {x : ZMod p} :
    m • x = 0 -> x = 0 := ...
```

For prime `p`, use that `ZMod p` is a field and
`m • x = ((m : ZMod p) * x)` with `(m : ZMod p) != 0`.

Status: implemented for stable compact-Cayley extraction data in
`CompactCayley/TorsionFree.lean`.

## 8. Define Coefficient Limits On `Gamma`

For each word, use the extracted limit and push it down to the quotient.

Targets:

```lean
noncomputable def coeffLimit : Gamma -> C := ...

lemma coeffLimit_tendsto (gamma : Gamma) :
    Tendsto
      (fun n =>
        letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
        F.coeff n (lift gamma n))
      atTop
      (nhds (coeffLimit gamma)) := ...
```

For each `q`, define:

```lean
def Fq (q : PNat) : Finset Gamma :=
  Finset.image
    (fun k : Fin (q^2 + 1) => classOfLabel ⟨q, k⟩)
    Finset.univ
    ∪ {0}
```

Prove:

```lean
lemma eventually_largeSpectrum_covered
    (q : PNat) :
    forallᶠ n in atTop,
      forall r : ZMod (F.p n),
        ((q : Real)^-1 : Real) < norm (F.coeff n r) ->
        exists gamma in Fq q, lift gamma n = r := ...

lemma coeffLimit_norm_le_inv_of_not_mem_Fq
    (q : PNat) {gamma : Gamma}
    (hgamma : gamma notin Fq q) :
    norm (coeffLimit gamma) <= (q : Real)^-1 := ...
```

This is PDF Lemma 2.2(iv).

Status: implemented in `CompactCayley/CoeffLimit.lean`, including quotient
coefficient limits, finite generator sets `largeSpectrumGenerators`, eventual
large-spectrum coverage, and the tail bound outside those finite sets.

## 9. Specialize Extraction To The Cayley Countersequence

Define a named structure if it helps:

```lean
structure CayleyExtraction
    {ell : Nat} {eta : Real}
    (S : CayleyCounterSeq ell eta) where
  Gamma : Type*
  instAddCommGroup : AddCommGroup Gamma
  instCountable : Countable Gamma
  instTorsionFree : IsAddTorsionFree Gamma
  lift : Gamma -> forall n, ZMod (S.p n)
  coeff : Gamma -> C
  ...
```

Specialized facts:

```lean
lemma coeff_zero_density :
    coeff 0 = limit of normalized densities := ...

lemma coeff_zero_ge_eta :
    eta <= (coeff 0).re := ...

lemma coeff_im_zero
    (gamma : Gamma) :
    (coeff gamma).im = 0 := ...

lemma coeff_neg_eq
    (gamma : Gamma) :
    coeff (-gamma) = coeff gamma := ...

lemma coeff_nonpos_of_ne_zero
    {gamma : Gamma} (hgamma : gamma != 0) :
    (coeff gamma).re <= 0 := ...
```

Use:

```lean
normalizedDftCoeff_im_eq_zero_of_symmetric
```

and `S.T_fourier_upper`. For nonzero `gamma`, eventually `lift gamma n != 0`,
so the finite Fourier upper bound applies and then passes to the limit using
`S.eps_tendsto_zero`.

Status: implemented in `CompactCayley/CayleyExtraction.lean`. The current
specialization proves coefficient convergence, imaginary part zero,
nonpositive real part away from zero, and zero-frequency density at least
`eta`. The explicit `coeff_neg_eq` lemma is still not isolated as a named
theorem.

## 10. Build The Compact Dual Group

Need:

```lean
G = Gamma^
```

Prefer generalizing the Route A `ExtractionCompactDual` infrastructure.

Target file:

```lean
CompactCayley/CompactDual.lean
```

Target objects:

```lean
abbrev ExtractionCompactDual (Gamma : Type*) [AddCommGroup Gamma] := ...
```

Required instances:

```lean
instance : CompactSpace (ExtractionCompactDual Gamma) := ...
instance : T2Space (ExtractionCompactDual Gamma) := ...
instance : AddCommGroup (ExtractionCompactDual Gamma) := ...
instance : IsTopologicalAddGroup (ExtractionCompactDual Gamma) := ...
instance : MeasurableSpace (ExtractionCompactDual Gamma) := ...
instance : BorelSpace (ExtractionCompactDual Gamma) := ...
instance : MeasurableAdd2 (ExtractionCompactDual Gamma) := ...
instance : MeasurableNeg (ExtractionCompactDual Gamma) := ...
```

Haar probability measure:

```lean
noncomputable def haar : Measure (ExtractionCompactDual Gamma) := ...

instance : haar.IsAddHaarMeasure := ...
instance : IsProbabilityMeasure haar := ...
instance : haar.IsOpenPosMeasure := ...
```

Connectedness:

```lean
instance extractionCompactDual_connected
    [IsAddTorsionFree Gamma] :
    ConnectedSpace (ExtractionCompactDual Gamma) := ...
```

This is one of the hardest infrastructure steps. It is the Pontryagin fact that
a compact abelian group is connected iff its discrete dual is torsion-free.

Status: compact dual, additive wrapper, Borel/measurable group instances, and
Haar probability measure are implemented in `CompactCayley/CompactDual.lean`.
The connectedness theorem for torsion-free discrete duals remains open.

## 11. Character And Haar Orthogonality API

Characters indexed by `Gamma`:

```lean
noncomputable def evalChar
    (gamma : Gamma) : ExtractionCompactDual Gamma -> C := ...
```

Prove:

```lean
lemma evalChar_zero :
    evalChar (0 : Gamma) = fun _ => 1 := ...

lemma evalChar_add (gamma delta : Gamma) :
    evalChar (gamma + delta) = fun x => evalChar gamma x * evalChar delta x := ...

lemma evalChar_neg (gamma : Gamma) :
    evalChar (-gamma) = fun x => star (evalChar gamma x) := ...

lemma norm_evalChar (gamma : Gamma) (x : ExtractionCompactDual Gamma) :
    norm (evalChar gamma x) = 1 := ...
```

Haar orthogonality:

```lean
lemma integral_evalChar
    (gamma : Gamma) :
    integral (fun x => evalChar gamma x) haar =
      if gamma = 0 then 1 else 0 := ...
```

The nonzero case uses translation invariance and a separating dual point.

Needed separation lemma:

```lean
lemma exists_dual_point_ne_one
    {gamma : Gamma} (hgamma : gamma != 0) :
    exists x : ExtractionCompactDual Gamma, evalChar gamma x != 1 := ...
```

Do not postpone this: without Haar orthogonality, compact density convergence
will not close.

Status: character evaluation, add/neg/star/norm, and continuity are implemented
in `CompactCayley/Characters.lean`. Haar orthogonality and the separating dual
point lemma remain open.

## 12. Trigonometric Polynomials

Add:

```lean
CompactCayley/TrigPolynomial.lean
```

Practical structure:

```lean
structure TrigPoly (Gamma : Type*) [AddCommGroup Gamma] where
  support : Finset Gamma
  coeff : Gamma -> C
  coeff_zero_of_not_mem : forall gamma, gamma notin support -> coeff gamma = 0
```

Evaluation:

```lean
noncomputable def TrigPoly.eval
    (P : TrigPoly Gamma) (x : ExtractionCompactDual Gamma) : C :=
  sum gamma in P.support, P.coeff gamma * evalChar gamma x
```

Finite lift:

```lean
noncomputable def TrigPoly.evalFinite
    (E : CayleyExtraction S)
    (P : TrigPoly E.Gamma)
    (n : Nat) (x : ZMod (S.p n)) : C :=
  sum gamma in P.support,
    P.coeff gamma * ZMod.stdAddChar (... using E.lift gamma n and x ...)
```

Needed lemmas:

```lean
lemma TrigPoly.compactAverage_eq_coeff_zero :
    integral (fun x => P.eval x) haar = P.coeff 0 := ...

lemma TrigPoly.finiteAverage_eventually_eq_zeroCoeff
    (P : TrigPoly Gamma) :
    forallᶠ n in atTop,
      avg over ZMod (S.p n) of P.evalFinite n =
        sum of coefficients whose finite lifted frequency is zero := ...

lemma TrigPoly.finiteAverage_tendsto_compactAverage
    (P : TrigPoly Gamma) :
    Tendsto
      (fun n => avg over ZMod (S.p n) of P.evalFinite n)
      atTop
      (nhds (integral (fun x => P.eval x) haar)) := ...
```

Reuse/generalize Route A trigonometric-polynomial machinery where possible.

Status: implemented in `CompactCayley/TrigPolynomial.lean` using `Finsupp`,
including finite cyclic lifts, DFT formulas for lifted polynomials, coefficient
selection under finite-lift injectivity, and finite-average convergence to the
algebraic zero-frequency compact average. Haar-integral compact averages remain
to be connected to this algebraic average.

## 13. Fejer Kernels And Folner Sets

Add:

```lean
CompactCayley/Fejer.lean
```

For finite nonempty `Q : Finset Gamma`, define compact and finite Fejer
kernels:

```lean
noncomputable def compactFejer
    (Q : Finset Gamma) (x : G) : Real :=
  (norm (sum gamma in Q, evalChar gamma x)^2) / Q.card

noncomputable def finiteFejer
    (E : CayleyExtraction S)
    (Q : Finset E.Gamma)
    (n : Nat) (x : ZMod (S.p n)) : Real :=
  (norm (sum gamma in Q, finiteChar (E.lift gamma n) x)^2) / Q.card
```

Prove nonnegativity, normalization, coefficient formulas, and finite analogues
valid eventually when lifts are injective on `Q - Q`.

Folner theorem:

```lean
theorem exists_folner_finset_for_finite_subset
    {Gamma : Type*} [AddCommGroup Gamma] [IsAddTorsionFree Gamma]
    (E : Finset Gamma) (delta : Real) (hdelta : 0 < delta) :
    exists Q : Finset Gamma,
      Q.Nonempty /\
      forall gamma in E,
        1 - delta <=
          ((Q ∩ (Q shifted by gamma)).card : Real) / Q.card := ...
```

Mathematically, the subgroup generated by finite `E` is finitely generated
torsion-free, hence isomorphic to `Z^d`; take a large box.

Status: Fejer kernels, Fejer trigonometric polynomials, finite average
normalization, nonnegativity/real-valued finite and compact kernels, finite DFT
coefficient identities, finite smoothing, boundedness, convolution DFT, and
the large-spectrum spectral-smoothing interface are implemented across
`CompactCayley/Fejer.lean` and `CompactCayley/Smoothing.lean`. The Fejer
coefficient API now includes real pair-ratio coefficient formulas and a shared
`pairFiber` overlap predicate in `CompactCayley/PairOverlap.lean`.
`CompactCayley/Folner.lean` proves the generic finite-subset lower-overlap
theorem: integer intervals, product boxes in `Z^d`, finite-support free
abelian groups, finitely generated torsion-free groups, and finally arbitrary
torsion-free extraction groups via the subgroup generated by the finite set.

## 14. Compact Limit Kernel

For the Cayley countersequence, let allowed coefficient limit be:

```lean
a gamma := E.coeff gamma
```

Complement coefficients:

```lean
noncomputable def gCoeff (gamma : Gamma) : Real :=
  if gamma = 0 then 1 - (a 0).re else - (a gamma).re
```

Need:

```lean
lemma gCoeff_nonneg : forall gamma, 0 <= gCoeff gamma := ...
lemma gCoeff_zero_le_one_sub_eta : gCoeff 0 <= 1 - eta := ...
```

For nonzero `gamma`, nonnegativity follows from `(a gamma).re <= 0`.

Prove finite partial-sum bound:

```lean
lemma sum_gCoeff_le_one
    (E0 : Finset Gamma) :
    sum gamma in E0, gCoeff gamma <= 1 := ...
```

Then:

```lean
lemma summable_gCoeff : Summable gCoeff := ...
lemma tsum_gCoeff_le_one : tsum gCoeff <= 1 := ...
```

This is a key milestone.

Status: the definition of `gCoeff`, nonnegativity, `gCoeff 0 <= 1 - eta`, and
the preliminary bound `norm (E.coeff gamma) <= 1` are implemented in
`CompactCayley/LimitKernel.lean`. The finite partial-sum bound, summability,
and `tsum` estimate are now unconditional: `LimitKernel.lean` imports the
finite Folner theorem and proves `E.summable_gCoeff` and
`E.tsum_gCoeff_le_one` directly for every compact-Cayley extraction.

## 15. Define `g` And `f = 1 - g`

Use complex-valued series first:

```lean
noncomputable def gComplex (x : G) : C :=
  tsum fun gamma : Gamma => (gCoeff gamma : C) * evalChar gamma x
```

Then prove real-valuedness:

```lean
lemma gComplex_im_eq_zero :
    (gComplex x).im = 0 := ...
```

using symmetry of coefficients and `evalChar (-gamma) x = star (evalChar gamma x)`.

Define:

```lean
noncomputable def gReal (x : G) : Real := (gComplex x).re
noncomputable def fReal (x : G) : Real := 1 - gReal x
```

Prove continuity from uniform convergence of an absolutely summable character
series.

## 16. Pointwise Bounds

Need:

```lean
lemma fReal_nonneg : forall x, 0 <= fReal x
lemma fReal_le_one : forall x, fReal x <= 1
lemma gReal_nonneg : forall x, 0 <= gReal x
lemma gReal_le_one : forall x, gReal x <= 1
```

Do not prove `g >= 0` from nonnegative Fourier coefficients; that is false in
general. Use Fejer smoothing and finite inequalities.

For each finite Fejer kernel `K_Q`, prove:

```lean
0 <= integral (fun y => fReal y * compactFejer Q (x - y)) haar
integral (fun y => fReal y * compactFejer Q (x - y)) haar <= 1
```

Pass finite inequalities through Fejer smoothing, then use approximate identity
convergence, which is easy here because `fReal` has absolutely summable Fourier
coefficients.

Status: the full pointwise package is now unconditional in
`CompactCayley/LimitKernel.lean`. The upper bound `gReal <= 1` comes from
bounding the Fourier-series norm by `tsum gCoeff <= 1`, and the lower bound
`0 <= gReal` is proved from compact-phase shifted Fejer kernels, finite
complement nonnegativity, Følner lower-overlap estimates, and summability tail
control. Consequently both `0 <= fReal` and `fReal <= 1` are unconditional, and
`compact_limit_cliqueDensity_pos` invokes the infinite-index compact endpoint
without any remaining pointwise hypothesis.

## 17. Mean Bound

Need:

```lean
lemma integral_fReal_ge_eta :
    eta <= integral fReal haar := ...

lemma integral_gReal_le_one_sub_eta :
    integral gReal haar <= 1 - eta := ...
```

By Haar orthogonality, `integral fReal` is the zero Fourier coefficient. That
coefficient is the limit of:

```lean
normalizedDftCoeff (S.T n) 0 = (S.T n).card / S.p n
```

and the countersequence density gives the lower bound by `eta`.

## 18. Level-One Subgroup Branch

Use or add:

```lean
theorem levelOneSubgroupKernel_of_nonneg_fourier_series
    {Gamma G : Type*} ...
    (gCoeff : Gamma -> Real)
    (hg_nonneg : forall gamma, 0 <= gCoeff gamma)
    (hg_summable : Summable gCoeff)
    (hg_sum_le_one : tsum gCoeff <= 1)
    (g : G -> Real)
    (hg_def : forall x, g x = ...)
    (hg0 : g 0 = 1) :
    LevelOneSubgroupKernel g := ...
```

Proof idea: equality in the weighted average of character real parts forces
every positive coefficient character to equal `1`; this is closed under
subtraction.

This avoids constructing an explicit Hilbert representation.

## 19. Positive Compact Clique Density

Use:

```lean
continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel
```

Target:

```lean
theorem compact_limit_cliqueDensity_pos
    {ell : Nat} {eta : Real}
    (hell : 2 <= ell) (heta : 0 < eta)
    (E : CayleyExtraction S) :
    0 < continuousCliqueDensity E.haar ell E.fReal := by
  ...
```

Branch on `g 0 < 1`; otherwise use the level-one subgroup theorem from the
nonnegative Fourier series.

## 20. Finite Smoothed Model Kernels

For finite Folner set `Q : Finset Gamma`, define:

```lean
noncomputable def finiteSmooth
    (E : CayleyExtraction S)
    (Q : Finset E.Gamma)
    (n : Nat) :
    ZMod (S.p n) -> C :=
  fun x =>
    avg over y : ZMod (S.p n),
      indicatorC (S.T n) (x - y) *
      finiteFejer E Q n y
```

This is the finite convolution:

```text
g_{n,Q} = 1_{T_n} * K_{n,Q}
```

Prove:

```lean
lemma finiteSmooth_norm_le_one
    (hQ : Q.Nonempty) :
    forall n z, norm (finiteSmooth E Q n z) <= 1 := ...
```

It is real and in `[0,1]`.

## 21. Spectral Closeness Of Finite Smoothing

Target:

```lean
theorem spectralBound_indicator_sub_finiteSmooth
    (q : PNat)
    (Q : Finset Gamma)
    (hQ_folner :
      forall gamma in E.Fq q,
        1 - (q : Real)^-1 <= fejerCoeff Q gamma)
    :
    forallᶠ n in atTop,
      SpectralBound
        (fun z => indicatorC (S.T n) z - finiteSmooth E Q n z)
        ((q : Real)^-1 + S.eps n) := ...
```

The proof splits by frequency:

1. Low spectrum: `norm (hat 1_T r) <= 1/q`.
2. High spectrum: use large-spectrum coverage, represent `r = lift gamma n`,
   and use the Folner multiplier bound.

This must be a complex norm bound, not just a real-part bound.

## 22. Finite Density Convergence For Smoothed Kernels

Define compact smoothing:

```lean
noncomputable def compactSmooth
    (E : CayleyExtraction S)
    (Q : Finset E.Gamma) :
    G -> Real :=
  fun x => integral (fun y => E.fReal (x - y) * compactFejer Q y) E.haar
```

Target:

```lean
theorem finiteCliqueDensity_finiteSmooth_tendsto_compactSmooth
    (Q : Finset Gamma) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩
        finiteCliqueKernelDensity
          (ell := ell)
          (finiteSmooth E Q n))
      atTop
      (nhds ((continuousCliqueDensity E.haar ell (compactSmooth E Q) : Real) : C)) := ...
```

Proof: expand the finite smoothed kernel as a finite Fourier polynomial, expand
the finite clique density product, use eventual lift relations and finite
orthogonality, and pass coefficients to the compact Haar integral.

## 23. Compact Smoothing Approximation

Need:

```lean
theorem compactSmooth_uniform_tendsto_fReal :
    Tendsto
      (fun q => compactSmooth E (Q q))
      atTop
      (nhds E.fReal)
```

Use absolute summability and dominated convergence for Fourier series.

Also prove clique-density continuity in sup norm:

```lean
lemma continuousCliqueDensity_lipschitz_sup
    {f g : G -> Real}
    (hf : forall x, 0 <= f x /\ f x <= 1)
    (hg : forall x, 0 <= g x /\ g x <= 1)
    (hclose : forall x, abs (f x - g x) <= delta) :
    abs (continuousCliqueDensity mu ell f -
      continuousCliqueDensity mu ell g)
      <= ((continuousCliqueEdgePairs ell).card : Real) * delta := ...
```

Then choose `Q` so the compact smoothed density is positive with margin.

Status: the deterministic product estimate and the integrated sup-norm
Lipschitz bound are implemented in `CompactCayley/ContinuousEndpoint.lean` as
`abs_continuousCliqueKernel_sub_le_card_mul` and
`continuousCliqueDensity_lipschitz_sup`. The real-part compact smoothing
interface is now also in place: `compactSmoothReal`, its continuity lemma, the
finite Fejer-multiplied `gCoeff` identity, the dominated signed-tail estimates,
and the packaged uniform approximation theorem
`exists_compactSmoothReal_uniform_close`. A bounded-kernel density-continuity
estimate is now implemented as `continuousCliqueDensity_lipschitz_sup_two_pow`,
and the compact smoothing density-margin endpoint is packaged as
`exists_compactSmoothReal_cliqueDensity_pos`. The compact smoothing
approximation/margin part is now discharged; the remaining analytic bridge is
finite smoothed clique-density convergence.

## 24. Finish `CayleyCounterSeq.false`

Final proof skeleton:

```lean
theorem CayleyCounterSeq.false
    {ell : Nat} {eta : Real}
    (hell : 2 <= ell) (heta : 0 < eta)
    (S : CayleyCounterSeq ell eta) :
    False := by
  classical

  obtain ⟨E⟩ := exists_cayleyExtraction S

  have hcompact_pos :
      0 < continuousCliqueDensity E.haar ell E.fReal :=
    compact_limit_cliqueDensity_pos hell heta E

  obtain ⟨q, Q, hQ_nonempty, hQ_folner, hQ_density_margin⟩ :=
    choose_good_fejer_smoothing E hcompact_pos

  have hfinite_density_eventually :
      forallᶠ n in atTop,
        ((ell * ell : Nat) : Real) * ((q : Real)^-1) <
          (finiteCliqueKernelDensity
            (ell := ell)
            (finiteSmooth E Q n)).re := ...

  have hspectral_eventually :
      forallᶠ n in atTop,
        SpectralBound
          (fun z =>
            indicatorC (S.T n) z - finiteSmooth E Q n z)
          ((q : Real)^-1) := ...

  obtain ⟨n, hn_density, hn_spectral⟩ := ...

  letI : NeZero (S.p n) := ⟨(S.prime n).ne_zero⟩

  have hclique :
      exists C : Finset (ZMod (S.p n)),
        C.card = ell /\ CliqueInCayley (S.T n) C :=
    exists_clique_of_spectral_density_transfer_sq
      (T := S.T n)
      (g := finiteSmooth E Q n)
      (M := (q : Real)^-1)
      (S.T_sym n)
      (S.T_zero n)
      (by positivity)
      (finiteSmooth_norm_le_one E Q hQ_nonempty n)
      hn_spectral
      hn_density

  exact S.no_clique n hclique
```

## 25. Replace The Axiom File Only After The Theorem Exists

Once `CayleyCounterSeq.false` builds, temporarily create:

```lean
CompactCayley/CliqueTheorem.lean
```

with:

```lean
theorem compact_cayley_clique_proved ... := ...
```

Test:

```lean
#print axioms Erdos42.CompactCayley.compact_cayley_clique_proved
```

Only after this is clean should `compact_cayley_clique_proved` be renamed to
`compact_cayley_clique` and the axiom removed.

## 26. Implementation Order

1. `CayleyCounterSeq.subseq`.
2. Generic `FourierSeq`.
3. Parseval and large-spectrum cardinal bound.
4. Non-nested large-spectrum labelling by `Sigma q, Fin (q^2 + 1)`.
5. Free abelian word lifts.
6. Countable diagonal subsequence extraction.
7. Eventual-kernel quotient `Gamma`.
8. Eventual lift API: zero, add, neg, injective-on-finite-sets.
9. Torsion-free proof for `Gamma`.
10. Compact dual construction and connectedness.
11. Character evaluation and Haar orthogonality.
12. Trigonometric polynomial finite-lift average convergence.
13. Fejer kernels and Folner finite-set existence.
14. Complement coefficient summability.
15. Continuous kernels `gReal` and `fReal`.
16. Pointwise bounds `0 <= fReal <= 1`.
17. Mean bound `integral fReal >= eta`.
18. Level-one subgroup property for `gReal` when `gReal 0 = 1`.
19. Positive compact clique density.
20. Finite smoothed kernel definition.
21. Spectral closeness of finite smoothing.
22. Finite smoothed clique-density convergence.
23. Compact smoothing approximation.
24. `CayleyCounterSeq.false`.
25. Replace `compact_cayley_clique` axiom by theorem.
26. Run axiom audit.

Skipping steps 6-23 will almost certainly reintroduce a hidden theorem-shaped
axiom.

## Current Implementation Status

Implemented and compiling:

- `CompactCayley/Subseq.lean`: subsequences of `CayleyCounterSeq`.
- `CompactCayley/FourierExtraction.lean`: generic bounded Fourier sequences,
  normalized coefficient bounds, large-spectrum labels, and cover maps.
- `CompactCayley/ExtractionGroup.lean`,
  `StableExtraction.lean`, `QuotientLift.lean`,
  `TorsionFree.lean`, and `CoeffLimit.lean`: stable subsequence data,
  eventual-kernel quotient, eventual lift API, torsion-free extraction group,
  and coefficient limits.
- `CompactCayley/CayleyExtraction.lean`: specialization to Cayley
  countersequences, including real/symmetric coefficient facts and
  nonpositive nonzero coefficient limits.
- `CompactCayley/CompactDual.lean` and `Characters.lean`: compact additive
  dual, normalized Haar probability measure, character algebra, continuity,
  character separation via Mathlib's character-module API, and unconditional
  Haar orthogonality for extraction characters.
- `CompactCayley/TrigPolynomial.lean`: finite lift averages, compact-dual
  evaluation, continuity, unconditional compact Haar average formula, and the
  Haar identity for multiplying a trig polynomial by a fixed character.
- `CompactCayley/PairOverlap.lean` and `Folner.lean`: shared finite pair-fiber
  overlap predicates, transport under additive equivalences and injective
  homomorphisms, integer/product-box lower-overlap estimates, and finite-subset
  lower-overlap existence in arbitrary torsion-free abelian groups.
- `CompactCayley/Fejer.lean` and `Smoothing.lean`: finite Fejer kernels,
  Fejer coefficient interfaces including lower-overlap-to-norm conversion,
  real/even pair-ratio coefficient formulas,
  compact Fejer kernels as trigonometric polynomials, unconditional Haar
  average-one for compact Fejer kernels, finite smoothing, compact smoothing
  trigonometric polynomials, the real-valued compact smoothing wrapper and
  finite real-part expansion, real-valuedness of `compactSmooth`, norm bounds,
  weighted-average convergence, the compact integral interpretation of the
  smoothed coefficient functional, and spectral closeness from large-spectrum
  Fejer bounds.
- `CompactCayley/LimitKernel.lean`: initial complement coefficient facts
  (`gCoeff` nonnegativity/evenness/basic upper bounds), pointwise
  large-spectrum tail bounds for finite sums, the bridge from finite Fejer
  lower-overlap estimates to finite partial-sum bounds, unconditional
  `Summable E.gCoeff`, unconditional `tsum E.gCoeff <= 1`, unconditional
  `0 <= gReal <= 1`, and unconditional `0 <= fReal <= 1`. It also defines the
  shifted-Fejer coefficient identity, quantitative tail estimate used to prove
  `gReal_nonneg`, compact-smoothing approximation estimates bounding
  `|compactSmoothReal Q z - fReal z|` by a `gCoeff` tail plus finite Fejer
  coefficient errors, the packaged uniform approximation theorem
  `exists_compactSmoothReal_uniform_close`, the extra-constraint variant used
  for the final spectral bridge, and the smoothed positive-density endpoint
  `exists_compactSmoothReal_cliqueDensity_pos`. It also defines the absolutely
  summable Fourier-series kernels `gComplex`, `gReal`, and `fReal` with
  continuity, real-valuedness, zero-value, and mean identities under the local
  `Summable E.gCoeff` hypothesis used by those analytic lemmas. It also now
  proves the
  positive-definite equality case: if `gReal 0 = 1`, then level-one points
  trivialize every positive coefficient character, the level-one set is a
  subgroup, and finite index of that subgroup contradicts extraction
  torsion-freeness plus the mean gap `eta > 0`.
- `CompactCayley/ContinuousEndpoint.lean` and
  `CompactCayley/PositiveDefinite.lean`: in addition to the connected compact
  endpoint, there are now null-subgroup and infinite-index variants of the
  compact clique-forcing endpoint. `ContinuousEndpoint.lean` also contains the
  sup-norm Lipschitz estimates for continuous clique density, including the
  bounded-kernel variant needed for smoothed kernels. This gives Route B a
  narrower target than proving global connectedness of the compact dual.
- `CompactCayley/QuotientLift.lean` and
  `CompactCayley/SmoothDensityConvergence.lean`: the finite-density bridge is
  complete. The quotient lift has finite-sum transport lemmas, and
  `SmoothDensityConvergence.lean` contains support-sum evaluation for trig
  polynomials, finite product averaging over `Fin M -> ZMod p`, compact product
  integration over `Fin M -> E.CompactAddDual`, vertex-balance definitions,
  finite/compact balance equivalence, per-assignment finite and compact
  orthogonality, finite and compact clique-density expansions for a fixed
  trigonometric polynomial, the coefficient-convergence theorem that sends
  finite fixed-polynomial clique densities to the compact density, the
  specialization to `finiteSmooth`, and the real clique-density convergence
  statement.
- `CompactCayley/Contradiction.lean`, `CliqueAxiom.lean`, `Main.lean`, and
  `Proof.lean`: `CayleyCounterSeq.false` is proved, `compact_cayley_clique`
  is now a theorem rather than an axiom, the Route B downstream theorem builds
  through it, and the historical flat-bundle entry point is now a modular audit
  wrapper.

Still open:

- no Route B axiom-removal tasks remain in the compact-Cayley module tree.

## 27. Pitfalls

First, the Fourier upper condition is only an upper bound on the real part:

```lean
FourierUpperIndicator T eps :=
  forall r, r != 0 -> (normalizedDftCoeff T r).re <= eps
```

Use symmetry:

```lean
normalizedDftCoeff_im_eq_zero_of_symmetric
```

before turning real-part inequalities into coefficient inequalities.

Second, large-spectrum control must be norm-valued, not real-part-valued. The
smoothing spectral bound needs:

```lean
SpectralBound ...
```

which is a complex norm bound.

Third, do not claim `g >= 0` from nonnegative Fourier coefficients. Prove
`0 <= g <= 1` by passing finite inequalities through Fejer smoothing.

Fourth, the compact endpoint needs either connectedness of the compact dual or
the narrower fact that the relevant level-one subgroup is Haar-null. The
current implementation targets the latter via infinite index, using
torsion-freeness of `Gamma`.

Fifth, avoid general `t_H` counting convergence unless needed. The existing
finite transfer theorem makes a narrower smoothed-kernel contradiction more
efficient.

Sixth, keep the quotient lift API eventual. Use arbitrary representatives and
prove all algebraic facts eventually.

## 28. Final Verification Target

Commands:

```bash
lake build Erdos.P42.CompactCayley.Main
lake build Erdos.P42.Proof
```

Audit:

```lean
#print axioms Erdos42.CompactCayley.compact_cayley_clique
#print axioms Erdos42.CompactCayley.theorem_1_1_from_compact_cayley
#print axioms Erdos42.theorem_1_1
#print axioms Erdos42.erdos_42
```

For the compact route, the extra axiom

```lean
Erdos42.CompactCayley.compact_cayley_clique
```

must disappear. SafeVerify Route B should no longer need it in the allow-list.

## Bottom Line

The axiomless route is not to touch the Sidon downstream proof. It is to prove:

```lean
CayleyCounterSeq.false
```

from the existing counterexample sequence.

The efficient chain is:

```text
counterexample sequence
-> Fourier extraction group Gamma
-> compact dual G
-> absolutely summable complement kernel g
-> allowed kernel f = 1 - g with 0 <= f <= 1 and integral f >= eta
-> positive compact K_ell density via the infinite-index level-one endpoint
-> finite Fejer-smoothed models
-> spectral transfer to the original finite Cayley graphs
-> contradiction with no_clique
-> theorem compact_cayley_clique
```

That is the precise chain that removes the compact-Cayley axiom while staying
aligned with the Cayley graph method in the PDF.
