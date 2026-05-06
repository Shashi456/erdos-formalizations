# Proof Design: Formalizing Graham's Complete Polynomial Values Theorem

This document records the roadmap used to replace the P283
`roth_szekeres_graham` axiom with a proof of Graham's 1964 theorem in the exact
shape needed by the current Lean development. The roadmap is kept as handoff
documentation for the proof architecture and later extensions.

## Source Choice

The best source is Graham 1964 itself, and the intended formalization target is
Graham's proof, not a modern paraphrase.

R. L. Graham, "Complete sequences of polynomial values", Duke Mathematical
Journal 31 (1964), 275-285.
Project Euclid: <https://projecteuclid.org/journals/duke-mathematical-journal/volume-31/issue-2/Complete-sequences-of-polynomial-values/10.1215/S0012-7094-64-03126-6.full>.
Working PDF mirror: <https://sites.math.rutgers.edu/~zeilberg/akherim/graham1964.pdf>.

Graham defines `P(S)` as finite `0/1` subset sums of a sequence, defines
"complete" as containing all sufficiently large integers, and proves the exact
integer-valued polynomial characterization in Theorem 1.

Kim 2017 is the best orientation source: it restates the completeness notion,
says Roth-Szekeres proved the integer-valued polynomial criterion and Graham
reproved it by alternative elementary techniques, then reuses Graham-style
machinery for powers. It is not the primary proof source for the general theorem.
D'Angelo and Conlon-Fox-Pham are useful context, but RSG should not be
formalized from them.

The current P283 development is set up for this: the README reports zero
executable sorries, and `roth_szekeres_graham` is now supplied by the
`Erdos.P283.RSG.graham_complete_polynomial_values` theorem. This removes the former
mathematical trust boundary.

The expected axiom result is also part of the design: formalizing Graham's proof
should not require any problem-specific mathematical axioms. The proof uses
ordinary classical reasoning, finite combinatorics, modular arithmetic,
polynomial algebra, and eventual-growth facts, all of which sit inside Mathlib's
standard foundation (`propext`, `Classical.choice`, `Quot.sound`).

## Axiom Boundary

Formalized RSG does not need any axioms beyond the standard Lean/Mathlib
foundation. The proof is classical in the ordinary mathematical sense, but not
in the sense of relying on a new unproved theorem.

| Proof component | Expected axioms |
| --- | --- |
| Polynomial asymptotics and eventual growth | Mathlib core foundations |
| Bezout, gcd, and ideal arguments over `Z` | Mathlib core foundations |
| Residue-cover argument modulo `M` | Mathlib core foundations |
| Sieve/pigeonhole finite-combinatorial filling | Mathlib core foundations |
| `atTop`, `Tendsto`, and eventual gluing | Mathlib core foundations |

The payoff is that replacing `roth_szekeres_graham` by this proof makes the
P283 and P351 applications axiom-free modulo Lean's usual foundations and
Mathlib, rather than axiom-free modulo an external RSG postulate.

## Current Lean Scaffold

The RSG work lives under `Erdos/P283/RSG/`.

* `CompleteSequences.lean` contains the generic subset-sum vocabulary:
  `FS`, `SignedFS`, `Complete`, `NearlyComplete`, `SigmaSeq`,
  `CoversResidues`, tails, interleaving, finite-prefix witnesses, and the first
  substantial Graham Lemma 1 core:
  `complete_of_sigma_nearly`. It also contains the bounded signed-sum API
  `SignedFSOf`, `signedFSOf_list_sum`, the zero-padded finite-prefix sequence
  `finitePrefixSeq`, the final disjoint split `oddEvenPrefixAssembly`, the
  FS-transfer lemma `Complete.of_oddEvenPrefixAssembly`, the filter wrapper
  `sigma_of_eventually_doubling`, and the Graham AP construction
  `arbitrary_APs_of_signed_tail_difference`. The residue API now includes the
  `ZMod` lift helper `exists_eq_add_mul_of_zmod_eq` and the finite cyclic-group
  core `coversResidues_of_constant_unit_residue`. It also contains the
  duplicated-generator subset-sum lemma and the bridge
  `coversResidues_of_duplicated_generators`, plus
  `coversResidues_of_frequent_generators`, which chooses distinct late
  occurrences of a finite generating residue family. The closure helpers
  `sum_zsmul_mem_closure_range` and
  `zmod_closure_range_eq_top_of_sum_zsmul_eq_one` package the Bezout-style
  path from integer combinations of residues to additive generation of
  `ZMod m`.
* `PolynomialDifferences.lean` contains Graham's operator
  `Delta1 f(x) = f(4x + 2) - f(4x)`, its iterates, degree/constant-top
  infrastructure, exact degree drop with positive leading coefficient, and an
  explicit finite expansion through `deltaTerms`. The `deltaTerms` bookkeeping
  now includes length, sign, offset bounds, offset parity, no-duplicate terms,
  offset injectivity, and the bridge `Delta_eval_integer_mem_signedFS`.
* `PolynomialResidues.lean` contains denominator clearing for rational
  polynomials, congruence periodicity for integer values, and
  `infinite_nondivisibility_of_no_fixed_prime`.
* `PolynomialValues.lean` contains the chosen integer sequence
  `polyValueSeq`, conversion from integer sequence completeness back to the
  rational subset-sum statement, the odd-tail Sigma proof, the even-tail
  signed-`Delta` bridge, the positive top-`Delta` integer constant, the
  finite-Bezout bridge from no fixed prime divisor to residue generation, and
  the final theorem `graham_complete_polynomial_values`.
* `README.md` gives the short source list and project-level orientation.

At the time this note was updated, `lake build Erdos.P283.RSG` succeeds and the
P283/P351 wrapper `PolynomialEgyptianSums.roth_szekeres_graham` depends only on
Mathlib core axioms. This file remains useful as a proof-design map and as a
roadmap for formalizing Graham's printed Theorem 1 iff statement, Theorem 2, and
Theorem 4 later.

## Main Recommendation

Formalize the theorem in the exact shape needed by the current axiom, then derive
Graham's printed Theorem 1 as a corollary later if desired.

The current axiom is slightly more convenient than Graham's printed statement:
it assumes `f(n) ∈ Z_{>0}` for `n >= 1` and a no-fixed-prime-divisor condition
over positive inputs. Graham's printed Theorem 1 assumes `f` maps all integers
to integers and has no fixed prime divisor. Graham's proof only needs positive
integer values at the positive arguments it evaluates, plus denominator-clearing
congruence lemmas, so the shortest path is to prove the positive-input version
directly.

The replacement theorem should have this Lean shape:

```lean
theorem graham_complete_polynomial_values
    (f : ℚ[X])
    (h_nonconst : 0 < f.natDegree)
    (h_lead_pos : 0 < f.leadingCoeff)
    (h_int_pos :
      ∀ n : ℕ, 1 ≤ n →
        ∃ z : ℤ, 0 < z ∧ (z : ℚ) = f.eval (n : ℚ))
    (h_gcd_one :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ n : ℕ, 1 ≤ n ∧ ∃ z : ℤ,
          (z : ℚ) = f.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z)) :
    ∃ X_f : ℤ, ∀ X : ℤ, X_f ≤ X →
      ∃ I : Finset ℕ,
        (X : ℚ) = ∑ i ∈ I, f.eval ((i + 1 : ℕ) : ℚ)
```

Then replace the axiom in `Erdos/P283/Basic.lean` by:

```lean
theorem roth_szekeres_graham := graham_complete_polynomial_values
```

That keeps the rest of the P283 formalization untouched.

## Practical Strategy

Do not formalize this monolithically. The reusable proof should land in
separate pieces:

1. Complete-sequence and finite-subset-sum infrastructure.
2. Graham's residue-cover and signed-sum lemmas.
3. Polynomial finite-difference machinery.
4. The final Graham theorem and P283/P351 integration.

Before building more analytic-number-theory infrastructure from scratch, scan
existing Lean work related to Graham-style arguments. In particular, Woett's
arXiv:2502.02200 on the binomial case of Graham's conjecture and its
`ExplicitGraham.lean` development may contain useful lemmas or proof patterns.
That work is not the direct source for the general theorem, but it may reduce
the engineering cost of the polynomial/asymptotic side.

There is also a bespoke fallback: prove the theorem first for the concrete
P283 polynomial `qPoly p md.J g`, rather than for arbitrary rational
polynomials. That could be shorter, but it would lose the standard Graham
statement and would be less reusable. The preferred route remains the theorem
in the exact axiom shape above.

## Source-Page Dependency Map

Graham p. 275 gives the sequence definitions needed for the proof:

* `P(S)`, finite `0/1` subset sums.
* complete sequences.
* nearly complete sequences.
* Sigma-sequences.

Lemmas 1-5 build the subset-sum machine:

* Sigma-sequence plus nearly complete implies complete.
* Eventual doubling gives a Sigma-sequence.
* Residue systems modulo `m`.
* Signed sums `A(S)`.
* Arithmetic progressions in subset sums.
* The final nearly-complete interleaving lemma.

Theorem 1 begins on Graham p. 279. It states the integer-valued polynomial
criterion: for a polynomial mapping integers to integers, `S(f) =
(f(1), f(2), ...)` is complete iff the leading coefficient is positive and no
prime divides every value.

The proof introduces finite-difference operators `Delta_k`, proves the top
difference is a positive integer `m`, gets complete residue systems modulo `m`,
builds long arithmetic progressions from signed tail sums, and finishes by
splitting the polynomial values into a nearly complete subsequence and a
Sigma-sequence.

Theorem 2 on Graham p. 281 is the rational/binomial-basis generalization, and
Theorem 4 on p. 284 is the combined real-coefficient classification. These are
worth formalizing later, but are not needed to discharge the P283
`roth_szekeres_graham` wrapper.

## Phase 0: Keep the Target Narrow

Do not start with Graham's full Theorem 4. For P283, only this is needed:

```text
positive-leading rational polynomial
+ positive integer values on n >= 1
+ no fixed prime divisor on positive values
=> all sufficiently large integers are finite subset sums of f(1), f(2), ...
```

This is the theorem currently postulated as `roth_szekeres_graham`.

## Phase 1: Generic Subset-Sum Infrastructure

Create a module such as:

```text
Erdos/P283/RSG/CompleteSequences.lean
```

Define:

```lean
def FS (s : ℕ → ℤ) : Set ℤ :=
  {x | ∃ I : Finset ℕ, x = ∑ i ∈ I, s i}

def SignedFS (s : ℕ → ℤ) : Set ℤ :=
  {x | ∃ I J : Finset ℕ,
      Disjoint I J ∧ x = (∑ i ∈ I, s i) - (∑ j ∈ J, s j)}

def Complete (s : ℕ → ℤ) : Prop :=
  ∃ C : ℤ, ∀ x : ℤ, C ≤ x → x ∈ FS s

def NearlyComplete (s : ℕ → ℤ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ c : ℤ, ∀ j : ℕ, 1 ≤ j → j ≤ k → c + j ∈ FS s

def SigmaSeq (s : ℕ → ℤ) : Prop :=
  ∃ k h : ℕ, 1 ≤ k ∧
    (∀ m : ℕ, 0 < s (h + m)) ∧
    ∀ m : ℕ,
      s (h + m) < (k : ℤ) + ∑ n ∈ Finset.range m, s (h + n)
```

Also add subsequence-transfer lemmas:

```lean
lemma Complete.of_injective_subsequence
    {s t : ℕ → ℤ}
    (φ : ℕ → ℕ)
    (hφ : Function.Injective φ)
    (ht : ∀ n, t n = s (φ n))
    (hcomp : Complete t) :
    Complete s
```

This will save pain at the end, because Graham's final constructed sequence is
a subsequence/reordering of `(f(1), f(2), ...)`, not definitionally equal to it.

## Phase 2: Graham Lemmas 1-5

Formalize the five sequence lemmas independently of polynomials.

The most important statements are:

```lean
lemma complete_of_sigma_nearly
    {S T : ℕ → ℤ}
    (hS : SigmaSeq S)
    (hT : NearlyComplete T) :
    Complete (interleave S T)
```

This is now started in `CompleteSequences.lean` as
`complete_of_sigma_nearly`, with a bounded helper
`sigma_nearly_interval_decomposition`.

```lean
lemma sigma_of_eventually_doubling
    {S : ℕ → ℤ}
    (hpos : ∀ᶠ n in Filter.atTop, 0 < S n)
    (hdbl : ∀ᶠ n in Filter.atTop, S (n+1) ≤ 2 * S n) :
    SigmaSeq S
```

```lean
lemma residue_system_of_infinite_nondivisibility
    {S : ℕ → ℤ}
    (hprime :
      ∀ p : ℕ, p.Prime →
        ∀ N : ℕ, ∃ n ≥ N, ¬ ((p : ℤ) ∣ S n)) :
    ∀ m : ℕ, 1 ≤ m →
      ∀ r : ZMod m, ∃ x ∈ FS S, (x : ZMod m) = r
```

```lean
lemma arbitrary_APs_of_signed_tail_difference
    {S : ℕ → ℤ} {m : ℤ}
    (hm : 0 < m)
    (htail : ∀ N : ℕ, m ∈ SignedFS (fun i => S (N+i))) :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c : ℤ, ∀ j : ℕ, 1 ≤ j → j ≤ k →
        c + (j : ℤ) * m ∈ FS S
```

```lean
lemma nearly_complete_of_APs_and_residues
    {S T : ℕ → ℤ} {m : ℕ}
    (hm : 1 ≤ m)
    (hAP :
      ∀ k : ℕ, 1 ≤ k →
        ∃ c : ℤ, ∀ j : ℕ, 1 ≤ j → j ≤ k →
          c + (j : ℤ) * (m : ℤ) ∈ FS S)
    (hres :
      ∀ r : ZMod m, ∃ x ∈ FS T, (x : ZMod m) = r) :
    NearlyComplete (concat T S)
```

The hard finite-combinatorial lemma is the residue-system lemma. Graham's proof
is finite: choose many terms avoiding each prime divisor of `m`, pigeonhole
congruent values, and build `m` residues represented by sums of a common unit
modulo `m`. It should not need analysis or number theory beyond
`Nat.factorization`, `ZMod`, finite pigeonhole, and divisibility.

## Phase 3: Polynomial Finite-Difference Machinery

Create:

```text
Erdos/P283/RSG/PolynomialDifferences.lean
```

Define Graham's operator:

```lean
def Delta1 (f : ℚ[X]) : ℚ[X] :=
  f.comp (Polynomial.C 4 * Polynomial.X + Polynomial.C 2)
    - f.comp (Polynomial.C 4 * Polynomial.X)

def Delta (k : ℕ) (f : ℚ[X]) : ℚ[X] :=
  Nat.iterate Delta1 k f
```

Prove:

```lean
lemma Delta_natDegree
    (hf : 0 < f.natDegree)
    (hlead : 0 < f.leadingCoeff)
    (hk : k ≤ f.natDegree) :
    (Delta k f).natDegree = f.natDegree - k
```

```lean
lemma Delta_leadingCoeff_pos
    (hf : 0 < f.natDegree)
    (hlead : 0 < f.leadingCoeff)
    (hk : k ≤ f.natDegree) :
    0 < (Delta k f).leadingCoeff
```

```lean
lemma Delta_top_constant_pos
    (d := f.natDegree)
    (hf : 0 < d)
    (hlead : 0 < f.leadingCoeff) :
    ∃ m : ℤ, 0 < m ∧
      ∀ x : ℕ, 1 ≤ x →
        ∃ z : ℤ, (z : ℚ) = (Delta d f).eval (x : ℚ) ∧ z = m
```

You also need the key signed-subset-sum lemma:

```lean
lemma Delta_eval_mem_signedFS_even_tail
    (d := f.natDegree)
    (x : ℕ) :
    (integer value of (Delta d f).eval x)
      ∈ SignedFS (fun i => integer value of f at even arguments beyond a chosen tail)
```

For this, the clean route is to prove the explicit expansion of `Delta k f x`.
The arguments are of the form:

```text
4^k * x + 2 * sum_{j < k} epsilon_j * 4^j
```

They are distinct, positive, and even when `x` is chosen appropriately. This is
the indexing-heavy part, but it is elementary.

## Phase 4: No-Fixed-Prime Gives Infinitely Many Nondivisible Values

Create:

```text
Erdos/P283/RSG/PolynomialResidues.lean
```

Reuse the denominator-clearing idea already present in the P283 formalization.
The needed lemma is a positive-input version of the existing periodicity lemma:

```lean
lemma polynomial_periodicity_positive_inputs
    (f : ℚ[X])
    (B : ℕ)
    (hB : HasIntegralMultiple B f)
    {m x y : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x ≡ y [MOD m * B])
    (hfx : ∃ z : ℤ, (z : ℚ) = f.eval (x : ℚ))
    (hfy : ∃ z : ℤ, (z : ℚ) = f.eval (y : ℚ)) :
    f(x) ≡ f(y) mod m
```

Then prove:

```lean
lemma infinite_nondivisibility_of_no_fixed_prime
    (h_no_fixed :
      ∀ ℓ : ℕ, ℓ.Prime →
        ∃ n : ℕ, 1 ≤ n ∧ ∃ z : ℤ,
          (z : ℚ) = f.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z)) :
    ∀ ℓ : ℕ, ℓ.Prime →
      ∀ N : ℕ, ∃ n ≥ N,
        ∃ z : ℤ, (z : ℚ) = f.eval (n : ℚ) ∧ ¬ ((ℓ : ℤ) ∣ z)
```

This is where denominator clearing is used: once `f(n0) != 0 mod ell`, all
sufficiently large `n ≡ n0 mod ell * B` have the same nonzero residue.

## Phase 5: Prove Graham's Completeness Theorem

Create:

```text
Erdos/P283/RSG/GrahamComplete.lean
```

Follow Graham pp. 279-281.

Let `d = deg f`. Define `m` to be the positive constant value of `Delta d f`.
Then:

1. By infinite nondivisibility and Graham Lemma 3, `P(S(f))` contains a complete
   residue system modulo `m`.
2. Since there are only finitely many residue classes, choose a finite prefix
   `f(1), ..., f(r)` whose subset sums already contain a complete residue system
   modulo `m`.
3. Let the even tail be `T = (f(2r), f(2r+2), f(2r+4), ...)`. The constant
   difference `m = Delta_d f(x)`, with `x` chosen large, belongs to the signed
   subset sums of every tail of `T`. Therefore `P(T)` contains arbitrarily long
   arithmetic progressions with difference `m`.
4. By the AP-plus-residue lemma, the sequence
   `U = (f(1), ..., f(r), f(2r), f(2r+2), ...)` is nearly complete.
5. Let `W = (f(2r+1), f(2r+3), f(2r+5), ...)`. Since `f` has positive leading
   coefficient, `f(2r+2k+3) / f(2r+2k+1) -> 1`, so eventually
   `W_{k+1} <= 2 * W_k`. Hence `W` is a Sigma-sequence.
6. Apply Graham Lemma 1 to `W` and `U`. The resulting interleaved sequence is
   complete.
7. Transfer completeness to the full sequence `(f(1), f(2), ...)` by the
   injective-subsequence lemma.

The only analytic-looking ingredient is the ratio limit for polynomial values
on two affine-linear arguments. Make this a standalone helper:

```lean
lemma polynomial_eval_linear_ratio_tendsto_one
    (f : ℚ[X])
    (hlead : 0 < f.leadingCoeff)
    (hdeg : 0 < f.natDegree)
    {a b c d : ℚ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto
      (fun n : ℕ =>
        f.eval (a * n + b) / f.eval (c * n + d))
      atTop
      (𝓝 ((a ^ f.natDegree) / (c ^ f.natDegree)))
```

For Graham's odd tail, `a = c = 2`, so the limit is `1`. Then derive eventual
`W_{k+1} <= 2 * W_k`.

## Phase 6: Replace the Axiom and Verify

This phase is complete. `Erdos/P283/Basic.lean` was changed from:

```lean
axiom roth_szekeres_graham ...
```

to:

```lean
theorem roth_szekeres_graham ... :=
  graham_complete_polynomial_values ...
```

The verification command is:

```bash
lake build
#print axioms PolynomialEgyptianSums.roth_szekeres_graham
#print axioms PolynomialEgyptianSums.theorem_1
#print axioms PolynomialEgyptianSums.Erdos283.erdos_283
```

The observed result is that the only remaining axioms are Lean/Mathlib
foundations: `propext`, `Quot.sound`, and `Classical.choice`.

## Should Theorem 2 or Theorem 4 Be Formalized?

Not first.

For P283, formalizing Graham's Theorem 1 sufficiency in the positive-input form
above is enough. Theorem 2 and Theorem 4 are useful for a polished standalone
formalization of Graham's whole paper:

```text
Stage A: current axiom replacement
  Graham Theorem 1 sufficiency / positive-input version.

Stage B: printed Graham Theorem 1 iff
  Add necessity and the exact all-integers integer-valued formulation.

Stage C: Graham Theorem 2
  Binomial-basis rational-coefficient classification.

Stage D: Graham Theorem 3/4
  Irrational-coefficient obstruction and full real-coefficient classification.
```

Stage C requires more infrastructure around binomial polynomials `choose x k`,
integer-valued polynomial bases, and gcds of binomial-basis numerators. Stage D
requires finite-dimensional linear algebra over `Q`. None of that is needed to
remove the P283 axiom.

## Confidence and Expected Hard Parts

No additional mathematical axiom should be needed. Graham's proof is elementary
and self-contained after standard finite combinatorics, modular arithmetic,
polynomial degree/leading-coefficient algebra, and eventual-growth facts.

The main work is Lean bookkeeping. The hardest parts are likely:

1. Graham Lemma 3: complete residue systems modulo `m`.
2. The signed finite-difference expansion of `Delta k f`.
3. Tail bookkeeping showing `Delta d f(x)` uses only even-tail values.
4. The final subsequence/interleaving transfer.

The shortest practical path was to prove the theorem in the exact shape of the
current `roth_szekeres_graham` wrapper and keep Graham's Theorem 2/4 as later
extensions.
