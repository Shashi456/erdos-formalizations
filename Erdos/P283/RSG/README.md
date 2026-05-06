# Roth-Szekeres-Graham Formalization

This folder contains the Graham complete-polynomial-values formalization that
discharges the former `PolynomialEgyptianSums.roth_szekeres_graham`
trust-boundary axiom used by Erdos/P283 and Erdos/P351.

For the detailed theorem shape, source-page dependency map, and phase-by-phase
proof design, see [`ProofDesign.md`](ProofDesign.md).

Current status: `graham_complete_polynomial_values` is proved and
`PolynomialEgyptianSums.roth_szekeres_graham` now re-exports it from
`Erdos/P283/Basic.lean`. The reusable complete-sequence API and Graham
finite-difference machinery include the Sigma/nearly-complete combination,
eventual-doubling Sigma
criterion, signed-tail arithmetic-progression construction, and the
finite-difference-to-`SignedFS` bridge. The residue-cover API has the first
finite cyclic-group core, `coversResidues_of_constant_unit_residue`, plus the
duplicated-generator subset-sum bridge and the frequent-generator constructor.
It also has `finitePrefixSeq`, which packages finite residue prefixes as
zero-padded sequences for the final disjoint-tail assembly, and
`oddEvenPrefixAssembly`, which transfers that disjoint assembly back to the
original sequence without reusing indices.
`PolynomialResidues.lean` now contains the denominator-clearing periodicity step
and arbitrarily late nondivisibility. `PolynomialValues.lean` packages the
chosen integer value sequence, the odd-tail Sigma proof, the positive
top-`Delta` integer constant, the even-tail signed-`Delta` bridge, and
the final finite-Bezout bridge from no fixed prime divisor to residue coverage.

## Target Statement

The former axiom form used in P283 is now the proved theorem
`graham_complete_polynomial_values`:

> Let `f : Q[X]` be nonconstant, have positive leading coefficient, satisfy
> `f(n)` is a positive integer for every `n >= 1`, and have no fixed prime
> divisor. Then every sufficiently large integer is a finite subset sum of
> `f(1), f(2), f(3), ...`.

This is a slightly specialized form of Graham's complete-polynomial-values
theorem. The positivity-on-all-positive-inputs assumption is stronger than what
the classical theorem needs, but it matches the P283 application and avoids
irrelevant bookkeeping around early exceptional values.

## Assessment

I agree with the main assessment: formalizing this theorem should not require
any axioms beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`).
The mathematics is classical, elementary number theory and finite combinatorics,
with ordinary asymptotic reasoning.

The main correction is tactical: the best formalization target is Graham 1964,
not Roth-Szekeres 1954. Graham gives an elementary proof and packages the hard
part into reusable complete-sequence lemmas. Roth-Szekeres is historically
important and is cited as the earlier analytic proof, but Graham is the cleaner
Lean source.

The proposed effort estimate of roughly 3000-6000 lines is plausible. Following
Graham's proof may reduce the need for sharp partial-sum asymptotics: the key
growth input is closer to eventual gap control, such as `f(n + 1) <= 2 * f(n)`,
than to a full asymptotic formula for `sum_{k <= n} f(k)`.

## Primary Sources

* R. L. Graham, "Complete sequences of polynomial values", Duke Mathematical
  Journal 31 (1964), 275-285.
  DOI: <https://doi.org/10.1215/S0012-7094-64-03126-6>.
  Project Euclid: <https://projecteuclid.org/journals/duke-mathematical-journal/volume-31/issue-2/Complete-sequences-of-polynomial-values/10.1215/S0012-7094-64-03126-6.full>.
  Accessible scan: <https://sites.math.rutgers.edu/~zeilberg/akherim/graham1964.pdf>.

  This is the preferred proof source. It defines finite 0/1 subset sums,
  complete sequences, nearly complete sequences, and proves the polynomial
  classification.

* K. F. Roth and G. Szekeres, "Some asymptotic formulae in the theory of
  partitions", Quarterly Journal of Mathematics, Oxford Series (2) 5 (1954),
  241-259.
  DOI: <https://doi.org/10.1093/qmath/5.1.241>.

  This is the older analytic source cited by Graham. It is useful for historical
  provenance, but Graham's paper is the better formalization blueprint.

## Secondary Sources

* Doyon Kim, "On the Largest Integer that is not a Sum of Distinct Positive nth
  Powers", Journal of Integer Sequences 20 (2017), Article 17.7.5.
  <https://cs.uwaterloo.ca/journals/JIS/VOL20/Kim/kim6.pdf>.
  Useful for seeing Graham-style completeness arguments in a concrete case.

* John P. D'Angelo, "Symmetries, rational sphere maps, and complete polynomial
  sequences", Complex Analysis and its Synergies 8 (2022).
  <https://sites.math.rutgers.edu/~zeilberg/akherim/dangelo2021.pdf>.
  Good readable motivation and examples.

* Shalosh B. Ekhad and Doron Zeilberger, "Automating John P. D'Angelo's method
  to study Complete Polynomial Sequences", arXiv:2111.02832.
  <https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/jpda.html>.
  Computational follow-up with useful examples and terminology.

* David Conlon, Jacob Fox, and Huy Tuan Pham, "Subset sums, completeness and
  colorings", arXiv:2104.14766.
  <https://www.its.caltech.edu/~dconlon/subset_sums.pdf>.
  Modern additive-combinatorics context; not a proof of Graham's theorem.

## Suggested Lean Decomposition

1. Complete-sequence API.
   Define finite 0/1 subset sums `P(S)`, complete sequences, nearly complete
   sequences, Sigma-sequences, and signed finite sums `A(S)`.
   Started in [`CompleteSequences.lean`](CompleteSequences.lean).

2. Graham's preliminary lemmas.
   Formalize the reusable lemmas from Graham 1964:
   * Sigma-sequence + nearly complete interleaving gives complete.
     Started as `complete_of_sigma_nearly` in
     [`CompleteSequences.lean`](CompleteSequences.lean).
   * Eventual doubling/gap control gives Sigma-sequence.
     Proved as `sigmaSeq_of_tail_doubling` and
     `sigma_of_eventually_doubling`.
   * No fixed prime divisor gives complete residue systems modulo every `m`.
   * Signed tail-sum divisibility gives arbitrarily long arithmetic progressions
     in finite subset sums. Proved as
     `arbitrary_APs_of_signed_tail_difference`.

3. Integer-valued polynomial theorem.
   Prove Graham's integer-valued form: positive leading coefficient plus no
   fixed prime divisor implies completeness of `(f(1), f(2), ...)`.

4. Rational/binomial-basis bridge.
   Prove or import the binomial-basis representation for integer-valued
   rational polynomials and connect Graham's classification to the P283 axiom
   statement over `Q[X]`.

The finite-difference operator `Delta1 f(x) = f(4x + 2) - f(4x)` is started in
[`PolynomialDifferences.lean`](PolynomialDifferences.lean).

5. P283 integration.
   Replace `PolynomialEgyptianSums.roth_szekeres_graham` in
   `Erdos/P283/Basic.lean` with the proved theorem, then rerun the P283
   SafeVerify/audit commands.

## Cost Notes

The work is not likely to be blocked by missing axioms. The risk is engineering
surface area:

* Mathlib has surrounding polynomial, asymptotic, finite-set, `ZMod`, and gcd
  infrastructure.
* Mathlib does not appear to have a complete-sequence/subset-sum API at this
  granularity.
* The residue and filling lemmas are the main new formal infrastructure.

A bespoke theorem just for the P283 polynomial `qPoly p md.J g` could be shorter,
but it would be less reusable and would not establish the standard Graham
theorem. The reusable Graham route is the better long-term target if P283 is
being turned into a flagship axiom-free formalization.
