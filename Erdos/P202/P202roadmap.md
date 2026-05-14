Current audit note, 2026-05-14: the roadmap formalization is closed in the
modular proof tree.  The BFV omega-count theorem, lower-bound theorem, pruning
theorem, hExp rarity theorem, and the Park--Pham threshold package all print
only Lean/Mathlib core axioms.  The public theorem `Erdos202.erdos202_main`
now has no project-level dependency beyond:

```lean
propext
Classical.choice
Quot.sound
```

Sections 3--8 are archival
source-mapping and closure-pass notes; do not use them as the current task
queue.  In particular, any older paragraph in Sections 3--8 that describes a
BFV `sorry`, BFV theorem-shaped stub, or BFV input axiom as a live blocker is
superseded by this audit note.

Authoritative live status:

| Front | Current status |
| --- | --- |
| BFV omega-count / Mertens weighted sum | Closed; `bfv_omega_count_theorem` prints only Lean/Mathlib core axioms. |
| BFV lower construction / Chebyshev intervals | Closed; `bfv_lower_bound_theorem` prints only Lean/Mathlib core axioms. |
| BFV `hExp` rarity and radical multiplicity | Closed in the pruning path; the exported pruning theorem prints only Lean/Mathlib core axioms. |
| BFV pruning proposition | Closed; `bfv_pruning_theorem` prints only Lean/Mathlib core axioms. |
| Park--Pham / Kahn--Kalai expectation threshold | Closed; `park_pham_threshold_not_small_lt_exists` prints only Lean/Mathlib core axioms. |

If any older roadmap paragraph appears to contradict this table, this table and
the audit above are the current source of truth.

The final target should be:

```lean
#print axioms Erdos202.erdos202_main
-- propext
-- Classical.choice
-- Quot.sound
```

No `Erdos202.*` axioms. No `sorryAx`. No theorem-shaped “published input” left as an axiom.

## 1. Alignment with the PDF

The PDF’s proof has four real imported inputs:

1. **Park–Pham spread-disjointness**, used to prove dense core.
2. **BFV pruning**, producing the pruned family (Q').
3. **BFV omega/quotient count**, used inside the chain.
4. **BFV lower bound**, giving the matching lower construction.

That matches the original four-axiom boundary. The PDF itself says the analytic and pruning input is exactly BFV, and the new ingredient is the spread-core lemma replacing the old Erdős–Lovász/minimal-family loss. 

The PDF’s Section 2 derives spread-disjointness from Park–Pham/Kahn–Kalai: it defines (p)-smallness, (q(U)), (p_c(U)), uses (p_c(U)\le C_{\mathrm{KK}}q(U)\log \ell(U)), then uses a random partition into (2r) parts.  The Park–Pham arXiv abstract states exactly this expectation-threshold theorem for increasing properties on finite sets. ([arXiv][1])

The PDF’s Section 3 gives BFV pruning, including the five properties (P1)–(P5): (S'\ge SL(o(1),x)), lower modulus cutoff (xL(-2,x)), (h(q)\le e^{\sqrt X}), fixed (\omega(q)=K\le 3M), and distinct radicals.  The same section gives the quotient count, uniformly for (1\le y\le x), (0\le W\le K\le 3M). 

The chain and optimization layers in your Lean setup are aligned with Sections 4 and 5: the PDF uses the gcd congruence criterion, builds exact prime-power blocks (P_r), gets the product inequality, then optimizes through (c\sigma-c^2/4\le \sigma^2).  

## 2. Current trust boundary

From the current `#print axioms Erdos202.erdos202_main` audit, the active
project-level `axiom` declaration is:

```lean
ParkPham.park_pham_threshold_not_small_lt_exists
```

There are no remaining proof-body `sorry`s in the current BFV chain.  The old
four input names are no longer live axioms: omega-count and lower-bound are
theorem aliases, pruning is proved, and spread-disjointness is proved from the
single strict non-smallness Park--Pham package.  The closed-endpoint
non-smallness theorem `park_pham_threshold_not_small_exists`, the
exact-threshold `qSmallUpper` wrapper `park_pham_threshold_at_exists`, and the
larger-density wrapper `park_pham_threshold_exists` are now theorems.  The BFV omega-count,
lower-bound, pruning, and hExp rarity chains now depend only on Lean/Mathlib
core axioms (`propext`, `Classical.choice`, `Quot.sound`).

That is not a problem as a **work-in-progress**, but it is not acceptable as the final “only three classical axioms” proof. In Lean, a theorem proved with `sorry` depends on `sorryAx`. A theorem proved from a declared `axiom` depends on that axiom. Published papers do not count as Lean proofs unless their arguments are formalized or imported as proved theorems.

## 3. `hExp` rarity target

The earlier weak `Lscale (-(1/6)+ε)` target was not strong enough for BFV
pruning.  The current file has been patched to expose the BFV-strength target:

```lean
theorem hExp_rare_count_bfv32 :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        ((Finset.Icc 1 N).filter
            (fun n => hExpCutoff N < (hExp n : ℝ))).card
          ≤ Nat.floor
              ((N : ℝ) *
                Real.exp (-c * Real.sqrt (Real.log (N : ℝ)) *
                  Real.log (Real.log (N : ℝ))))
```

and proves the consumer form:

```lean
theorem hExp_rare_count_superL :
    ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N)
```

from it by scale algebra.  This front is now closed in `BFV/HExpRare.lean`;
`#print axioms Erdos202.hExp_rare_count_superL` reports only core axioms.

The PDF cites BFV Lemma 3.2 in the form

[
#{n\le x:h(n)>e^{\sqrt X}}
\ll x\exp{-\tfrac15\sqrt X,Y}
=============================

o(xL(-1,x)).
]



Since (Z=\sqrt{XY}), the exponent (-c\sqrt X,Y) is much stronger than (-A Z)
for any fixed (A), because (\sqrt X,Y = Z\sqrt Y).

## 4. Source map for each dependency

| Lean target                 | PDF/source                                                   | Correct source claim                                                                                                                                      | Formalization route                                                                                                                                                   |
| --------------------------- | ------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `spread_disjointness_input` | PDF Proposition 2.1, Corollary 2.2; Park–Pham Theorem 1.1    | Park–Pham gives (p_c(U)\le Cq(U)\log\ell(U)); spread implies (q(\langle F\rangle)\le \kappa^{-1}); random partition gives disjoint members.  ([arXiv][1]) | Prove finite Boolean-family layer, product measure, p-smallness, random partition; then formalize Park–Pham theorem itself or import a proved Lean theorem.           |
| `bfv_omega_count_input`     | PDF Lemma 3.2, derived from BFV Lemma 3.1                    | Uniformly for (1\le y\le x), (0\le W\le K\le 3M), count (\omega(n)=K-W).                                                                                  | Prove Rankin omega-tail + Euler product/Mertens bound; derive exact count.                                                                                            |
| `bfv_pruning_input`         | PDF Proposition 3.1; BFV Section 4.1 and Lemmas 3.1–3.3      | Extract (Q') satisfying (P1)–(P5).                                                                                                                        | Formalize deletion sequence: small moduli, large omega, large `hExp`, fixed omega pigeonhole, radical representatives.                                                |
| `bfv_lower_bound_input`     | BFV lower bound, cited as the left-hand side of estimate (1) | (f(x)\ge xL(-1+o(1),x)).                                                                                                                                  | Formalize BFV’s explicit CRT construction of pairwise disjoint congruences. BFV is the Acta Arithmetica paper by de la Bretèche, Ford, and Vandehey. ([eudml.org][2]) |

## 5. What must happen to make the theorem depend only on the three core axioms

The final dependency tree should be:

```text
Erdos202.erdos202_main
├── f_upper_bound
│   ├── bfv_pruning_theorem
│   │   ├── bfv_lower_bound_theorem
│   │   ├── bfv_omega_tail / omega_count theorem
│   │   ├── hExp_rare_count_superL
│   │   └── rad_multiplicity_bfv33
│   ├── bfv_omega_count_theorem
│   └── dense_core_from_spread
│       └── spread_disjointness_theorem
│           ├── park_pham_threshold_theorem
│           └── partition_density_to_disjoint_members theorem
└── bfv_lower_bound_theorem
```

Everything in that tree must be a theorem with a proof body. No project-level axiom should remain.

The final audit command is:

```lean
#print axioms Erdos202.erdos202_main
```

and the only acceptable output is:

```lean
'propext'
'Classical.choice'
'Quot.sound'
```

Those are standard Lean/mathlib foundations. They are not mathematical assumptions about Erdős 202.

---

# 6. Archival Formalization Plan, Dependency By Dependency

This section records the original dependency-closure plan.  It is no longer the
live work queue: the BFV omega-count, lower-bound, pruning, hExp-rarity, and
radical-multiplicity fronts have since been closed in the modular tree.  The
only current project-level axiom is the Park--Pham expectation-threshold
package named in Section 2 and Section 9.

Do not dispatch new work from the "Current Lean status" paragraphs in this
section. They are preserved to explain how the closure passes got here, not to
describe the present theorem-audit boundary.

## A. First cleanup pass: lock the correct theorem statements

Before proving anything else, do this.

### A1. Replace the weak `hExp` target

In `BFV/HExpRare.lean`, replace the current weak theorem with:

```lean
theorem hExp_rare_count_bfv32 :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        ((Finset.Icc 1 N).filter
            (fun n => hExpCutoff N < (hExp n : ℝ))).card
          ≤ Nat.floor
              ((N : ℝ) *
                Real.exp (-c * Real.sqrt (Real.log (N : ℝ))
                             * Real.log (Real.log (N : ℝ))))
```

Then prove:

```lean
theorem hExp_rare_count_superL :
    ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter
          (fun n => hExpCutoff N < (hExp n : ℝ))).card
        ≤ Nat.floor ((N : ℝ) * Lscale (-A) N)
```

This matches the PDF’s BFV Lemma 3.2 usage. The existing `Lscale (-(1/6)+ε)` version should be deleted or renamed as an unrelated weak lemma.

### A2. Remove unused old axioms once replacements exist

The flat file still declares:

```lean
axiom bfv_lower_bound_input
```

even though `erdos202_main` uses `bfv_lower_bound_theorem`. Once the lower-bound theorem is genuinely proved, remove the old axiom entirely.

Same pattern for:

```lean
bfv_omega_count_input
bfv_pruning_input
spread_disjointness_input
```

The historical names can be preserved as theorem aliases:

```lean
theorem bfv_omega_count_input : ... :=
  bfv_omega_count_theorem
```

but not as `axiom`.

---

## B. Formalize `bfv_omega_count_input`

### Source

PDF Lemma 3.2 derives the exact quotient count from BFV Lemma 3.1 and explicitly requires uniformity for (1\le y\le x), (0\le W\le K\le 3M). 

### Closed Lean status

This front is complete in the modular proof. `bfv_omega_count_input` is a
theorem alias to `bfv_omega_count_theorem`, and the Euler-product/Mertens
weighted-sum estimate in `BFV/Mertens.lean` is proved. Current audit:

```text
'Erdos202.bfv_omega_count_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

### Formal proof plan

Create or complete:

```text
Erdos/P202/BFV/Mertens.lean
Erdos/P202/BFV/OmegaTail.lean
Erdos/P202/BFV/OmegaExact.lean
Erdos/P202/BFV/OmegaCountInput.lean
```

#### B1. Prove the divisor expansion

For (z\ge1),

[
z^{\omega(n)}
\le
\sum_{\substack{d\mid n\ d\ \text{squarefree}}} z^{\omega(d)}.
]

In Lean:

```lean
lemma zpow_omega_le_squarefree_divisor_sum
    (z : ℝ) (hz : 1 ≤ z) (n : ℕ) :
    (z ^ omega n)
      ≤ ∑ d in divisors n,
          if Squarefree d then z ^ omega d else 0 := by
  ...
```

This is finite arithmetic over `Nat.factorization`.

#### B2. Exchange sums

For (y\le N),

[
\sum_{n\le y} z^{\omega(n)}
\le
y\sum_{d\le y,,\mathrm{sqfree}(d)}
\frac{z^{\omega(d)}}{d}.
]

Lean target:

```lean
lemma omega_weighted_sum_le_squarefree_dirichlet
    (y : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (∑ n in Finset.Icc 1 y, z ^ omega n)
      ≤ (y : ℝ) *
        ∑ d in Finset.Icc 1 y,
          if Squarefree d then z ^ omega d / (d : ℝ) else 0 := by
  ...
```

#### B3. Bound the squarefree Dirichlet sum by an Euler product

[
\sum_{d\le y,,\mathrm{sqfree}(d)}
\frac{z^{\omega(d)}}d
\le
\prod_{p\le y}\left(1+\frac zp\right).
]

Lean target:

```lean
lemma squarefree_dirichlet_le_euler_product
    (y : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    (∑ d in Finset.Icc 1 y,
      if Squarefree d then z ^ omega d / (d : ℝ) else 0)
      ≤ ∏ p in (Finset.Icc 2 y).filter Nat.Prime,
          (1 + z / (p : ℝ)) := by
  ...
```

This is standard finite Euler-product bookkeeping.

#### B4. Bound the Euler product

Use:

[
\log\prod_{p\le N}(1+z/p)
\le
z\sum_{p\le N}\frac1p.
]

Then prove or import a Mertens-type upper bound:

[
\sum_{p\le N}\frac1p \le C+\log\log N.
]

Mathlib’s index includes `Mathlib.NumberTheory.SumPrimeReciprocals`, and mathlib has prime-counting infrastructure; use existing results where possible rather than reproving from scratch. ([leanprover-community.github.io][3])

Lean target:

```lean
theorem omega_weighted_sum_bfvz_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ y : ℕ, y ≤ N →
        (∑ n in Finset.Icc 1 y, (BFVz N) ^ omega n)
          ≤ (y : ℝ) * Real.exp (ε * Zscale N)
```

This was the original closure target; it is now proved in the modular tree.

#### B5. Rankin tail

For (z=BFVz(N)=\sqrt{\log N}/\log\log N),

[
#{n\le y:t\le\omega(n)}
\le
z^{-t}\sum_{n\le y}z^{\omega(n)}.
]

Lean target:

```lean
lemma omega_tail_rankin :
    1 ≤ z →
    ((Finset.Icc 1 y).filter (fun n => t ≤ omega n)).card * z ^ t
      ≤ ∑ n in Finset.Icc 1 y, z ^ omega n := by
  ...
```

Then prove the scale algebra:

```lean
lemma rankin_factor_bfvz :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ t : ℕ, (t : ℝ) ≤ 3 * Mscale N →
        Real.exp ((ε / 2) * Zscale N) / (BFVz N) ^ t
          ≤ Real.exp ((-((t : ℝ) / Mscale N) / 2 + ε) * Zscale N)
```

This uses:

[
\log B = \frac12\log\log N-\log\log\log N.
]

#### B6. Exact count

Then derive:

```lean
theorem bfv_omega_count_theorem :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y K W : ℕ,
      y ≤ N →
      W ≤ K →
      (K : ℝ) ≤ 3 * Mscale N →
      let d : ℝ := (K : ℝ) / Mscale N
      ((Finset.Icc 1 y).filter (fun n => omega n = K - W)).card
        ≤ Nat.floor
            ((y : ℝ) * Real.exp ((-d / 2 + ε) * Zscale N)
              * Real.exp (((W : ℝ) / 2) * Real.log (Real.log (N : ℝ))))
```

Then replace the axiom:

```lean
theorem bfv_omega_count_input : ... :=
  bfv_omega_count_theorem
```

Prompt for a separate session:

> Work only on `Erdos/P202/BFV/Mertens.lean`, `OmegaTail.lean`, `OmegaExact.lean`, and `OmegaCountInput.lean`. Replace `omega_weighted_sum_bfvz_bound : ... := by sorry` with a proof using finite Euler products and the prime reciprocal sum bound. Then prove `bfv_omega_count_theorem` and replace `bfv_omega_count_input` by a theorem alias. Do not touch pruning or Park–Pham. Final audit: no `sorry`, no `Erdos202.bfv_omega_count_input` axiom, and no `sorryAx` in `#print axioms Erdos202.bfv_omega_count_theorem`.

---

## C. Formalize `bfv_lower_bound_input`

### Source

The PDF uses the matching BFV lower bound as the left-hand side of estimate (1), then says this completes the proof after the upper bound.  The BFV paper is de la Bretèche–Ford–Vandehey, *On non-intersecting arithmetic progressions*, Acta Arithmetica 157(4), 381–392. ([eudml.org][2])

### Closed Lean status

This front is complete in the modular proof. `bfv_lower_bound_input` is a
theorem alias to `bfv_lower_bound_theorem`, and the lower-path construction,
capacity bookkeeping, and dyadic interval supply have all been discharged in
the current theorem path. Current audit:

```text
'Erdos202.bfv_lower_bound_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The notes below are archival source-mapping for the closure pass, not live BFV
work items.

### Formal proof plan

Create or complete:

```text
Erdos/P202/BFV/Chebyshev.lean
Erdos/P202/BFV/PrimeIntervals.lean
Erdos/P202/BFV/LowerConstruction.lean
Erdos/P202/BFV/LowerBoundInput.lean
```

#### C1. Weaken the prime-interval theorem to Chebyshev strength

The original prime-interval theorem targeted:

[
#{p\in(y,2y]}\ge (1-\varepsilon)y/\log y.
]

That is PNT-strength. For BFV lower bound, this is unnecessarily strong. A fixed positive constant is enough because constants across (R=O(M)) choices contribute only (\exp(O(M))=L(o(1),N)).

Use this instead:

```lean
theorem dyadicPrimeInterval_card_lower_bound_const :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ y : ℝ in atTop,
        Nat.floor (c * y / Real.log y)
          ≤ (dyadicPrimeInterval y).card
```

This should be derivable from Chebyshev-style prime counting. Mathlib has prime-counting definitions and Chebyshev-related number theory infrastructure; if the exact dyadic lower bound is not packaged, make that a small upstream-style theorem, not a P202 axiom. ([leanprover-community.github.io][4])

#### C2. Prime blocks

Define dyadic prime blocks:

```lean
def lowerPrimeInterval (N : ℕ) (i : lowerIndex N) : Finset ℕ := ...
```

Prove:

```lean
theorem lowerPrimeIntervals_pairwise_disjoint :
    ∀ᶠ N : ℕ in atTop,
      ∀ i j : lowerIndex N, i ≠ j →
        Disjoint (lowerPrimeInterval N i) (lowerPrimeInterval N j)
```

and:

```lean
theorem lowerPrimeInterval_card_lower :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ i : lowerIndex N,
          Nat.floor (c * lowerY N i / Real.log (lowerY N i))
            ≤ (lowerPrimeInterval N i).card
```

#### C3. Product bound

Prove every selected modulus is at most (N):

```lean
theorem lowerModulus_le_N :
    ∀ᶠ N : ℕ in atTop,
      ∀ P : LowerChoice N,
        lowerModulus N P ≤ N
```

This is just scale algebra: product of the chosen prime blocks is constructed to fit inside (N).

#### C4. CRT residue construction

Formalize the CRT assignment BFV uses. You already have congruence infrastructure in `P202Basic.lean`.

Target:

```lean
theorem exists_residue_for_lowerChoice
    (N : ℕ) (P : LowerChoice N) :
    ∃ a : ℤ,
      -- residues modulo each prime block encode the next prime/index
```

Then define:

```lean
noncomputable def lowerResidue (N : ℕ) (P : LowerChoice N) : ℤ :=
  Classical.choose (exists_residue_for_lowerChoice N P)
```

#### C5. Decoding/disjointness

Prove:

```lean
theorem lower_intersection_implies_same_choice :
    x ∈ residueClass (lowerModulus N P) (lowerResidue N P) →
    x ∈ residueClass (lowerModulus N P') (lowerResidue N P') →
    P = P'
```

Then:

```lean
theorem lowerQ_admissible :
    ∀ᶠ N : ℕ in atTop,
      Admissible N (lowerQ N)
```

This is the heart of BFV’s lower construction.

#### C6. Cardinality lower bound

Use prime-block cardinalities and product estimates to prove:

```lean
theorem lowerChoices_card_lower_bound_eventually :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Nat.ceil ((N : ℝ) * Lscale (-(1 + ε)) N)
        ≤ (lowerChoices N).card
```

This replaces:

```lean
axiom lowerChoices_card_lower_bound_eventually_analytic
```

Also replace:

```lean
axiom lowerEncodingCapacity_eventually_analytic
```

by the actual CRT/decoding proof.

Finally:

```lean
theorem bfv_lower_bound_input : ... :=
  bfv_lower_bound_theorem
```

Prompt for a separate session:

> Work on `Erdos/P202/BFV/Chebyshev.lean`, `PrimeIntervals.lean`, `LowerConstruction.lean`, and `LowerBoundInput.lean`. The goal is to remove `lowerEncodingCapacity_eventually_analytic`, `lowerChoices_card_lower_bound_eventually_analytic`, and the `dyadicPrimeInterval_card_lower_bound` sorry. Weaken the dyadic prime interval supply to a Chebyshev constant if needed. Prove the BFV lower CRT construction, admissibility, decoding/disjointness, and the cardinality lower bound (N L(-(1+ε),N)). Final audit: `#print axioms Erdos202.bfv_lower_bound_theorem` has only Lean/mathlib core axioms.

---

## D. Formalize `bfv_pruning_input`

### Source

PDF Proposition 3.1 is the pruning proposition. It explicitly cites BFV Section 4.1 and BFV Lemmas 3.1–3.3. 

### Closed Lean status

This front is complete in the modular proof. `bfv_pruning_input` has been
removed from `BFVInputs.lean`, and `bfv_pruning_theorem` is proved in
`BFV/Pruning.lean`. Current audit:

```text
'Erdos202.bfv_pruning_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The notes below are archival source-mapping for the closure pass, not live BFV
work items.

### Formal proof plan

Create or complete:

```text
Erdos/P202/BFV/Filtering.lean
Erdos/P202/BFV/HExpRare.lean
Erdos/P202/BFV/RadMultiplicity.lean
Erdos/P202/BFV/Pruning.lean
```

#### D1. Decide extremal vs near-extremal interface

The PDF’s pruning proposition starts with an **extremal** family (Q) of size (f(x)). Your Lean axiom is stronger: it accepts any near-extremal family (Q) with

```lean
(Q.card : ℝ) ≥ (f N : ℝ) * Lscale (-ε) N
```

This is probably provable, but it is not literally the PDF proposition. If the upper-bound proof only needs pruning for an extremal (Q), I recommend narrowing the theorem to the PDF-aligned statement:

```lean
theorem bfv_pruning_extremal :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ Q : Finset ℕ, ∀ a : ResidueAssignment Q,
        (∀ q ∈ Q, 1 ≤ q ∧ q ≤ N) →
        PairwiseDisjointResidues Q a →
        Q.card = f N →
        ∃ D : PrunedData N,
          (D.Q.card : ℝ) ≥ (Q.card : ℝ) * Lscale (-ε) N
```

If downstream code truly needs the stronger near-extremal version, prove the extremal version first, then prove a generalized version as a corollary using the same deletion bounds.

#### D2. Generic deletion lemma

```lean
lemma filter_large_of_bad_small
    (Q Bad : Finset ℕ)
    (hBad : Bad ⊆ Q)
    (hsmall : (Bad.card : ℝ) ≤ δ * (Q.card : ℝ))
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ((Q \ Bad).card : ℝ) ≥ (1 - δ) * (Q.card : ℝ)
```

You will use this three times.

#### D3. Delete small moduli

Bad set:

```lean
q < (N : ℝ) * Lscale (-2) N
```

Its cardinality is at most roughly (NL(-2,N)), because the moduli are distinct and below (N). Compare this to the lower bound (f(N)\ge NL(-(1+η),N)). This uses `bfv_lower_bound_theorem`.

#### D4. Delete large omega

Use `bfv_omega_count_theorem` or the tail theorem with (\alpha=3):

[
#{n\le N:\omega(n)>3M}
\le NL(-3/2+o(1),N),
]

which is negligible relative to (NL(-1-o(1),N)).

#### D5. Delete large `hExp`

Use the corrected theorem:

```lean
hExp_rare_count_superL
```

with, say, (A=3). This gives a bad set of size at most (NL(-3,N)), hence negligible.

#### D6. Pigeonhole fixed omega value

After (\omega(q)\le3M), there are (O(M)) possible omega values. Prove:

```lean
∃ K,
  K ≤ Nat.ceil (3 * Mscale N) ∧
  ((Q.filter fun q => omega q = K).card : ℝ)
    ≥ (Q.card : ℝ) / (Nat.ceil (3 * Mscale N) + 1)
```

Then prove:

```lean
1 / (Nat.ceil (3 * Mscale N) + 1 : ℝ) ≥ Lscale (-ε) N
```

eventually.

#### D7. Radical multiplicity

The PDF uses BFV Lemma 3.3: under fixed (\omega=K) and (h(q)\le e^{\sqrt X}), each radical fiber has multiplicity at most (e^{2\sqrt X}2^K). 

Lean target:

```lean
theorem rad_multiplicity_bfv33 :
    ∀ Q K H r,
      (∀ q ∈ Q, omega q = K) →
      (∀ q ∈ Q, hExp q ≤ H) →
      (Q.filter fun q => rad q = r).card ≤ H^2 * 2^K
```

This appears to be substantially formalized already. Make sure it has no `sorry` and does not depend on a project axiom.

#### D8. Select one representative per radical

Use a finite choice lemma:

```lean
theorem choose_one_per_fiber_card_lower :
    ∃ Q' : Finset ℕ,
      Q' ⊆ Q ∧
      (∀ q ∈ Q', ∀ r ∈ Q', rad q = rad r → q = r) ∧
      (Q.card : ℝ) / C ≤ (Q'.card : ℝ)
```

Then absorb:

[
e^{2\sqrt X}2^K=L(o(1),N)
]

using (K\le3M).

#### D9. Package `PrunedData`

Construct:

```lean
theorem bfv_pruning_theorem : ... := by
  -- deletion small moduli
  -- deletion large omega
  -- deletion large hExp
  -- omega pigeonhole
  -- radical representatives
  -- package PrunedData
```

Then replace:

```lean
theorem bfv_pruning_input : ... :=
  bfv_pruning_theorem
```

Prompt for a separate session:

> Work on `Erdos/P202/BFV/HExpRare.lean`, `Filtering.lean`, `RadMultiplicity.lean`, and `Pruning.lean`. First replace the weak `hExp_rare_count_rankin_squarefull` target by the BFV-strength super-(L) theorem. Then prove the pruning theorem from the lower bound, omega tail/count, hExp rarity, omega pigeonhole, and radical multiplicity. Keep the theorem aligned with PDF Proposition 3.1 unless downstream code truly needs the stronger near-extremal form. Final audit: remove `bfv_pruning_input` as an axiom.

---

## E. Formalize `spread_disjointness_input`

### Source

The PDF’s Proposition 2.1 is a short derivation from Park–Pham: prove (q(\langle F\rangle)\le\kappa^{-1}), apply (p_c\le Cq\log\ell), then randomly partition into (2r) parts.  The Park–Pham theorem itself is the Kahn–Kalai expectation-threshold theorem for increasing families on a finite set. ([arXiv][1])

### Current Lean status

The old `spread_disjointness_input` name is now a theorem alias in
`SpreadCore.lean`, backed by `ParkPham.spread_disjointness_theorem`.
The finite random-partition/double-counting layer has been formalized in
`ParkPham/SpreadDisjointness.lean`:

```lean
theorem ParkPham.partition_density_to_disjoint_members : ...
theorem ParkPham.spread_disjointness_theorem : ...
```

The current Park--Pham trust boundary is a single existential package:

```lean
axiom ParkPham.park_pham_threshold_not_small_lt_exists : ...
```

No separate `CKK_const`, `CKK_const_pos`, `park_pham_threshold_package`,
`park_pham_threshold_at_exists`, `park_pham_threshold_exists`, or
`partition_density_to_disjoint_members` axiom remains in the active theorem
path.  `park_pham_threshold_at_exists` is now derived from the non-smallness
axiom by a constant-factor argument, and `park_pham_threshold_exists` is
derived from the exact-threshold theorem plus `muP_mono_density`.

### Formal proof plan

Files:

```text
Erdos/P202/ParkPham/BooleanFamilies.lean
Erdos/P202/ParkPham/ProductMeasure.lean
Erdos/P202/ParkPham/Smallness.lean
Erdos/P202/ParkPham/Threshold.lean
Erdos/P202/ParkPham/RandomPartition.lean
Erdos/P202/ParkPham/SpreadDisjointness.lean
```

#### E1--E2. Completed: random partition and existential threshold package

`ParkPham/SpreadDisjointness.lean` now contains the finite coloring model,
successful color count, extraction of `r` pairwise-disjoint members, and the
final spread-disjointness theorem.  `ParkPham/Threshold.lean` exposes only the
strict non-smallness existential package
`park_pham_threshold_not_small_lt_exists`; the closed-endpoint theorem
`park_pham_threshold_not_small_exists`, exact-threshold wrapper
`park_pham_threshold_at_exists`, and larger-density wrapper
`park_pham_threshold_exists` are theorems, and the constant is chosen locally
inside `spread_disjointness_theorem`.

#### E3. Prove spread implies (q(\langle F\rangle)\le\kappa^{-1})

Target:

```lean
theorem qSmallUpper_of_spread
    (hA : A.Nonempty)
    (hκ : 1 < κ)
    (hUniform : UniformFamily A k)
    (hSpread : SpreadFamily A κ) :
    qSmallUpper X (upClosureIn X A) κ⁻¹
```

This is exactly the counting argument in the PDF:

[
|F|
\le
\sum_{G\in\mathcal G}|F_G|
\le
|F|\sum_G\kappa^{-|G|}.
]



#### E4. Apply Park–Pham

Prove:

```lean
theorem mu_at_partition_density_ge_half :
    A.Nonempty →
    2 ≤ r →
    1 ≤ k →
    UniformFamily A k →
    SpreadFamily A κ →
    Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
    muP X (upClosureIn X A) ((1 : ℝ) / (2 * r)) ≥ 1 / 2
```

Use deliberately crude constants:

```lean
def Csp : ℝ := max 16 (8 * CKK)
```

No sharp constants matter.

#### E5. Prove spread-disjointness

```lean
theorem spread_disjointness_theorem :
  ∃ Csp : ℝ, 0 < Csp ∧
    ∀ {α : Type*} [DecidableEq α]
      (A : Finset (Finset α)) (r k : ℕ) (κ : ℝ),
      A.Nonempty →
      2 ≤ r →
      1 ≤ k →
      UniformFamily A k →
      SpreadFamily A κ →
      Csp * (r : ℝ) * Real.log (Real.exp 1 * (k : ℝ)) ≤ κ →
      ∃ B : Finset (Finset α),
        B ⊆ A ∧ B.card = r ∧ PairwiseDisjointMembers B
```

Then:

```lean
theorem spread_disjointness_input : ... :=
  spread_disjointness_theorem
```

#### E6. Remaining: formalize Park–Pham itself

This is the largest remaining independent project. To get down to only the
three Lean core axioms, you cannot leave
`park_pham_threshold_not_small_lt_exists` as an
axiom. The source is Park–Pham’s proof of Kahn–Kalai, not the Erdős 202 PDF.
([arXiv][1])

Prompt for a separate session:

> Work only in `Erdos/P202/ParkPham/`. Formalize Park–Pham’s Theorem 1.1 from arXiv:2203.17207 in finite-family form: definitions of increasing family, p-smallness, expectation threshold, threshold under product measure, complexity (\ell(U)), and the theorem (p_c(U)\le C q(U)\log\ell(U)). The random-partition, density-monotonicity, closed-endpoint, and `qSmallUpper` wrapper layers are already proved. Final audit: replace `park_pham_threshold_not_small_lt_exists` by a theorem and verify `#print axioms Erdos202.ParkPham.spread_disjointness_theorem` has only Lean/mathlib core axioms.

---

# 7. Current recommended order of work

Do not start another BFV closure pass.  The BFV theorem path is already clean.
The remaining sequence is:

1. **Park--Pham theorem**
   Replace `park_pham_threshold_not_small_lt_exists` in
   `ParkPham/Threshold.lean` by a theorem formalizing the finite
   Park--Pham/Kahn--Kalai expectation-threshold implication:

   ```lean
   (∀ S ∈ U, S ⊆ X) →
   IncreasingIn X U →
   ¬ pSmall X U q →
   muP X U (C * q * Real.log (ell X U)) ≥ 1 / 2
   ```

   under the existing positivity and `≤ 1` hypotheses.  The ground-set
   hypothesis is essential: Park--Pham is a theorem about Boolean families on
   a finite universe, and the downstream application has
   `U = upClosureIn X A`, so the condition is automatic there.

2. **Final audit**
   Re-run the axiom and syntax scans below.  The public theorem is complete
   only when no `Erdos202.*` axiom remains in `#print axioms
   Erdos202.erdos202_main`.

After each stage:

```lean
#print axioms Erdos202.erdos202_main
```

and also:

```bash
grep -R "axiom\|sorry\|admit\|unsafe" Erdos/P202
```

The final theorem is only genuinely useful once both checks are clean, except for the three core Lean axioms.

## 8. Current assessment

The formalization’s **chain, optimization, BFV, and Park--Pham layers are
aligned with the PDF and currently build through the modular theorem path**.
The last Park--Pham/Kahn--Kalai dependency has been discharged via the finite
Park--Vondrak reduction and the scalar snoc schedule in
`ParkPham/Threshold.lean`.

The project is now an axiom-free correctness certificate modulo Lean/Mathlib's
standard core axioms.  The audit:

```lean
#print axioms Erdos202.erdos202_main
```

reports exactly:

```lean
propext
Classical.choice
Quot.sound
```

[1]: https://arxiv.org/abs/2203.17207 "[2203.17207] A Proof of the Kahn-Kalai Conjecture"
[2]: https://eudml.org/doc/278905 "EUDML  |  On non-intersecting arithmetic progressions"
[3]: https://leanprover-community.github.io/mathlib4_docs/Mathlib.html?utm_source=chatgpt.com "Mathlib"
[4]: https://leanprover-community.github.io/mathlib_docs/number_theory/prime_counting.html "number_theory.prime_counting - mathlib3 docs"

---

## 9. Current Lean State After The Full Closure Pass

This section records the current state of the actual files after the BFV,
Park--Pham, and public-theorem closure passes. It supersedes older references
in this roadmap to
`bfv_pruning_input` as a live trust-boundary axiom, and also supersedes older
references to separate Park--Pham constants such as `CKK_const`.

### 9.1 Closed since the original audit

The following old input names are no longer project-level axioms in the modular
development:

```lean
bfv_omega_count_input
bfv_lower_bound_input
bfv_pruning_input
```

Current status:

* `bfv_omega_count_input` is a theorem alias to `bfv_omega_count_theorem`.
* `bfv_lower_bound_input` is a theorem alias to `bfv_lower_bound_theorem`.
* `bfv_pruning_input` has been removed from `BFVInputs.lean`.
* `bfv_pruning_theorem` is proved in `BFV/Pruning.lean`.
* `P202Optimization.f_upper_bound` uses the proved pruning path.
* `ParkPham.partition_density_to_disjoint_members` is proved in
  `ParkPham/SpreadDisjointness.lean`; it is no longer an axiom.
* `ParkPham.spread_disjointness_theorem` now depends on the proved strict
  Park--Pham package, `park_pham_threshold_not_small_lt_exists`, rather than
  separate exposed constants `CKK_const`, `park_pham_threshold_package`, the
  closed-endpoint theorem `park_pham_threshold_not_small_exists`, the
  exact-threshold wrapper `park_pham_threshold_at_exists`, or the larger-density
  wrapper `park_pham_threshold_exists`.
* `safeverify/Spec.lean` now names `bfv_pruning_theorem` rather than the old
  pruning axiom, and its omega-count surface includes the needed `y <= N`
  hypothesis.

The current flattened artifact typechecks:

```bash
lake env lean Erdos/P202/P202Flat.lean
```

`P202Flat.lean` is now a small compatibility wrapper around the maintained
modular proof tree, not a generated 10k-line snapshot.

### 9.2 Current `#print axioms` boundary

The current audit for the public theorem is:

```lean
#print axioms Erdos202.erdos202_main
```

which reports:

```text
[propext, Classical.choice, Quot.sound]
```

The spread-disjointness subtheorem has the same boundary:

```text
'Erdos202.ParkPham.spread_disjointness_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

and the pruning theorem has the BFV-only boundary:

```text
'Erdos202.bfv_pruning_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The BFV subtheorems are now clean:

```text
'Erdos202.bfv_omega_count_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]

'Erdos202.bfv_lower_bound_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]

'Erdos202.bfv_pruning_theorem' depends on axioms:
[propext, Classical.choice, Quot.sound]

'Erdos202.hExp_rare_count_superL' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

There are no remaining proof-body placeholders or project-level axioms in the
P202 Lean source.  The Park--Pham package
`park_pham_threshold_not_small_lt_exists` is now a theorem proved from the
scalar schedule `pvSnocScalarParameterScheme_128_div_log_two`.

### 9.3 Historical lower-construction obstruction

This obstruction has been handled by the lower-path redesign now consumed by
`BFV/LowerBoundInput.lean`.  Do not spend another bookkeeping pass trying to
revive

```lean
lowerChoices_card_lower_bound_eventually_analytic
```

for the old fixed-root lower construction as if it were merely missing Lean
algebra. With those definitions, the family was too small for the stated BFV
lower-bound target.

The old construction fixed a shared root factor at block `0`:

```lean
lowerP0 N = floor (lowerY N (lowerZeroIndex N)) + 1
```

and varies only over the tail blocks. Since the corrected scales satisfy

```text
prod_i (2 * lowerY_i) = N
```

the tail-choice count has the heuristic size

```text
prod_{i > 0} lowerY_i / prod_{i > 0} log(lowerY_i)
  ~= N / (2^r * lowerY_0 * prod_{i > 0} log(lowerY_i)).
```

For the present centered arithmetic-progression scales:

* `log lowerY_0 = Zscale N + o(Zscale N)`, so the fixed root costs about
  `Lscale(1, N)`;
* `sum_{i > 0} log log lowerY_i = (1/2 + o(1)) * Zscale N`, so the logarithmic
  prime-density denominators cost about `Lscale(1/2, N)`;
* the `2^r` factor is only `Lscale(o(1), N)`.

Thus the old fixed-root construction heuristically gave only

```text
N * Lscale(-(3/2 + o(1)), N),
```

not the required

```text
N * Lscale(-(1 + epsilon), N)
```

for arbitrary small `epsilon > 0`.

This was why the old lower-bound axiom needed a structural redesign of the
lower construction, not just a proof of the old C5 statement.  The current
BFV-compatible replacement uses a rooted path construction that keeps pairwise
residue classes disjoint without paying a full `Lscale(1,N)` fixed-root loss.

The relevant BFV lower-bound construction is in [3, Section 2].  In the paper,
each modulus is written

```text
q = p_0 p_1 ... p_r,       p_k in [y_k, 2 y_k],
```

and the residue is defined by CRT from

```text
a_q == pi(p_{k+1}) (mod p_k)     for 0 <= k < r,
a_q == 0          (mod p_r).
```

The capacity condition is `pi(p_{k+1}) < p_k`.  The scale choice should
therefore make each next prime block encodable by the previous prime, while
still giving

```text
prod_k (2 y_k) <= N
prod_k |[y_k,2y_k] ∩ primes| >= N * Lscale(-(1+o(1)), N).
```

The old fixed-root model paid for a whole root block and was too small.  The
source-aligned refactor instead uses a path construction with roughly
`r = 2 M(N)` levels, first scale around `exp(sqrt(log N))`, and logarithmic
gap around

```text
(1/2) log log N - sqrt(log log N),
```

so the root/path startup cost is only `Lscale(o(1),N)`, the product of prime
density denominators contributes `Lscale(1+o(1),N)`, and the encoding
inequalities `|block_{k+1}| <= p_k` remain eventually true.

### 9.4 Closed Park--Pham Infrastructure

No remaining formalization session is required for the roadmap target.  The
Park--Pham theorem path is now closed; the finite Boolean-family,
product-measure, p-smallness, random-partition, and spread-disjointness
consumer layers are proved.  The local expectation-threshold infrastructure
includes:

   * `pSmall_mono_density`
   * `coverWeight`
   * `coverWeight_union_le`
   * `groundCoversIn`
   * `coverCost`
   * `coverCost_le_of_ground_cover`
   * `exists_ground_cover_weight_eq_coverCost`
   * `self_covers`
   * `coverCost_le_coverWeight_self`
   * `coverCost_empty_eq_zero`
   * `coverCost_eq_one_of_empty_mem`
   * `coverCost_pos_iff_empty_mem_of_forall_card_zero`
   * `pSmall_iff_coverCost_le`
   * `not_pSmall_iff_half_lt_coverCost`
   * `coverCost_mono_family`
   * `coverCost_union_le`
   * `not_pSmall_of_qSmallUpper`
   * `not_qSmallUpper_of_pSmall`
   * `qSmallUpper_mono_q`
   * `qSmallUpper_one`
   * `pSmall_empty`
   * `nonempty_of_not_pSmall`
   * `pSmall_one_iff_empty`
   * `not_pSmall_one_iff_nonempty`
   * `pSmall_zero_iff_empty_not_mem`
   * `not_pSmall_zero_iff_empty_mem`
   * `not_pSmall_of_empty_mem`
   * `qSmallUpper_of_empty_mem`
   * `exists_pos_pSmall_of_empty_not_mem`
   * `qSmallUpper_zero_iff_empty_mem`
   * `pSmall_of_cover_sum_le`
   * `cover_sum_gt_half_of_not_pSmall`
   * `not_pSmall_iff_forall_cover_sum_gt_half`
   * `CoversIn.mono_cover`
   * `CoversIn.mono_family`
   * `CoversIn.union`
   * `CoversIn_iff_subset_upClosureIn`
   * `CoversIn_upClosureIn_iff`
   * `CoversIn.filter_subset_ground`
   * `pSmall_upClosureIn_iff`
   * `pSmall.exists_ground_cover`
   * `not_pSmall_upClosureIn_iff`
   * `qSmallUpper_upClosureIn_iff`
   * `pSmall_mono_family`
   * `not_pSmall_mono_family`
   * `qSmallUpper_mono_family`
   * `minimalMembers_cover`
   * `generators_cover_upClosureIn`
   * `subset_upClosureIn`
   * `upClosureIn_mono`
   * `nonempty_of_upClosureIn_nonempty`
   * `empty_mem_upClosureIn_iff`
   * `empty_not_mem_upClosureIn_iff`
   * `upClosureIn_eq_self_of_increasing`
   * `upClosureIn_singleton_subset_of_mem_increasing`
   * `upClosureIn_idempotent`
   * `top_mem_of_nonempty_increasing`
   * `eq_powerset_of_empty_mem_increasing`
   * `minimalMembersIn_subset`
   * `not_ssubset_of_mem_minimalMembersIn`
   * `eq_of_subset_of_mem_minimalMembersIn`
   * `InclusionAntichain`
   * `InclusionAntichain.eq_of_subset`
   * `minimalMembersIn_inclusionAntichain`
   * `mem_minimalMembersIn_upClosureIn_iff_of_inclusionAntichain`
   * `minimalMembersIn_upClosureIn_eq_of_inclusionAntichain`
   * `ell_upClosure_eq_of_inclusionAntichain`
   * `card_le_ell_of_mem_minimalMembersIn`
   * `exists_singleton_mem_of_mem_card_eq_one`
   * `exists_singleton_mem_of_mem_minimalMembersIn_card_eq_one`
   * `minimalMembersIn_nonempty_of_nonempty`
   * `nonempty_of_mem_minimalMembersIn_of_empty_not_mem`
   * `two_le_card_of_mem_minimalMembersIn_of_empty_not_mem_of_no_singleton`
   * `upClosureIn_minimalMembersIn_eq_of_increasing`
   * `mem_minimalMembersIn_upClosureIn_iff`
   * `minimalMembersIn_upClosureIn_eq`
   * `ell_upClosure_eq`
   * `CoversIn_minimalMembersIn_iff`
   * `pSmall_minimalMembersIn_iff`
   * `not_pSmall_minimalMembersIn_iff`
   * `qSmallUpper_minimalMembersIn_iff`
   * `pSmall_of_minimalMembers_sum_le`
   * `half_lt_minimalMembers_sum_of_not_pSmall`
   * `half_lt_generators_sum_of_not_pSmall_upClosureIn`
   * `exists_mem_weight_gt_inv_two_mul_card_of_half_lt_sum`
   * `exists_minimalMember_weight_gt_inv_two_mul_card_of_not_pSmall`
   * `exists_generator_weight_gt_inv_two_mul_card_of_not_pSmall_upClosureIn`
   * `half_lt_minimalMembers_card_mul_pow_of_not_pSmall_card_ge`
   * `inv_two_mul_inv_pow_lt_minimalMembers_card_of_not_pSmall_card_ge`
   * `half_lt_minimalMembers_card_mul_sq_of_not_pSmall_no_singleton`
   * `inv_two_mul_inv_sq_lt_minimalMembers_card_of_not_pSmall_no_singleton`
   * `half_lt_minimalMembers_card_mul_of_not_pSmall_empty_not_mem`
   * `inv_two_mul_inv_lt_minimalMembers_card_of_not_pSmall_empty_not_mem`
   * `minimalMembersIn_nonempty_of_not_pSmall`
   * `exists_mem_minimalMembersIn_of_not_pSmall`
   * `muP_le_half_of_pSmall`
   * `not_pSmall_of_muP_gt_half`
   * `qSmallUpper_of_forall_muP_gt_half`
   * `muP_upClosureIn_eq_self_of_increasing`
   * `muP_insert_split`
   * `muP_mono_density`
   * `exists_powerset_value_lt_of_bernoulli_average_lt`
   * `nat_mul_q_mul_one_sub_q_pow_le_one_sub_pow`
   * `q_mul_one_sub_q_pow_div_one_sub_pow_le_inv_nat`
   * `bernoulliMass_self_one`
   * `bernoulliMass_one_of_ne_top`
   * `muP_one_of_mem_top`
   * `muP_one_of_nonempty_increasing`
   * `bernoulliMass_empty_zero`
   * `bernoulliMass_zero_of_nonempty`
   * `muP_zero_of_mem_empty`
   * `muP_zero_of_not_mem_empty`
   * `muP_eq_one_of_eq_powerset`
   * `muP_eq_one_of_empty_mem_increasing`
   * `pow_card_le_muP_of_mem_increasing`
   * `density_le_muP_of_singleton_mem_increasing`
   * `pow_ell_le_muP_of_nonempty_increasing`
   * `CriticalAtMost`
   * `ExpectationAtMost`
   * `CriticalAtMost.mono_density`
   * `ExpectationAtMost.mono_q`
   * `ExpectationAtMost.of_not_pSmall`
   * `CriticalAtMost.of_empty_mem_increasing`
   * `ExpectationAtMost.one`
   * `ExpectationAtMost.zero_iff_empty_mem`
   * `ExpectationAtMost.minimalMembersIn_iff`
   * `fragmentFamily`
   * `minimalFragments`
   * `largeMinimalFragments`
   * `smallMinimalFragments`
   * `minimalFragments_cover`
   * `fragmentFamily_card_le_card`
   * `minimalFragments_card_le_card`
   * `largeMinimalFragments_card_le_card`
   * `smallMinimalFragments_card_le_card`
   * `fragmentFamily_card_le_of_forall_card_le`
   * `minimalFragments_card_le_of_forall_card_le`
   * `CoversIn.of_minimalFragments`
   * `empty_mem_fragmentFamily_iff`
   * `empty_mem_minimalFragments_iff`
   * `exists_minimalFragment_subset_iff_source_subset_union`
   * `empty_mem_fragmentFamily_minimalFragments_iff`
   * `minimalFragment_subset_of_source_subset`
   * `largeFragmentWitnesses`
   * `largeFragmentWitnesses_subset_source_powerset_filter`
   * `sum_largeFragmentWitnesses_pow_le_two_pow_mul_pow`
   * `exposureUnion`
   * `iteratedMinimalFragments`
   * `exists_iteratedMinimalFragment_subset_iff_source_subset_union`
   * `coverCost_le_minimalFragments`
   * `coverCost_le_small_add_large_minimalFragments`
   * `largeMinimalFragments_subset_ground`
   * `coverCost_largeMinimalFragments_le_card_mul_pow`
   * `coverCost_largeMinimalFragments_le_source_card_mul_pow`
   * `coverCost_smallMinimalFragments_pos_of_large_cost_lt`
   * `coverCost_smallMinimalFragments_one_pos_iff_exists_subset`
   * `coverCost_smallMinimalFragments_one_iterated_pos_iff_exists_subset_union`
   * `iteratedSmallFragments`
   * `iteratedLargeCostSum`
   * `exists_exposure_largeCost_lt_of_bernoulli_average_lt`
   * `bernoulli_average_largeCost_le_source_card_mul_pow`
   * `exists_exposure_largeCost_lt_of_source_card_mul_pow_lt`
   * `coverCost_le_iteratedSmallFragments_add_largeCostSum`
   * `exists_source_subset_union_of_largeCostSum_lt_append_one`
   * `exposureUnion_mem_upClosureIn_of_largeCostSum_lt_append_one`
   * `CriticalAtMost.of_mu_ge`
   * `CriticalAtMost.of_pow_ell_ge_half`
   * `CriticalAtMost.of_mem_pow_card_ge_half`
   * `CriticalAtMost.of_mem_card_le`
   * `CriticalAtMost.of_exists_mem_card_le`
   * `CriticalAtMost.or_many_minimalMembers_of_not_pSmall`
   * `CriticalAtMost.of_singleton_mem`
   * `CriticalAtMost.of_minimal_card_one`
   * `park_pham_threshold_not_small_lt_of_empty_mem`
   * `park_pham_threshold_not_small_lt_reduce_empty`
   * `q_lt_one_of_large_constant_threshold_le_one`
   * `q_lt_one_of_large_constant_threshold_lt_one`
   * `StrictNonSmallCoreOn`
   * `StrictGeneratedCoreOn`
   * `StrictHardCoreOn`
   * `StrictGeneratedHardCoreOn`
   * `StrictAntichainHardCoreOn`
   * `StrictAntichainMultiHardCoreOn`
   * `StrictAntichainLargeHardCoreOn`
   * `StrictAntichainSparseHardCoreOn`
   * `StrictAntichainScaledHardCoreOn`
   * `StrictAntichainScaleOnlyHardCoreOn`
   * `StrictAntichainReducedHardCoreOn`
   * `strict_nonSmallCoreOn_of_generatedCoreOn`
   * `park_pham_threshold_not_small_lt_of_pow_ell_ge_half`
   * `strict_nonSmallCoreOn_of_hardCoreOn`
   * `strict_hardCoreOn_of_generatedHardCoreOn`
   * `strict_nonSmallCoreOn_of_generatedHardCoreOn`
   * `strictGeneratedHardCoreOn_of_antichainHardCoreOn`
   * `strictAntichainHardCoreOn_of_multiHardCoreOn`
   * `strictAntichainMultiHardCoreOn_of_largeHardCoreOn`
   * `strictAntichainLargeHardCoreOn_of_sparseHardCoreOn`
   * `strictAntichainSparseHardCoreOn_of_threshold_at`
   * `strictAntichainSparseHardCoreOn_of_threshold`
   * `strictAntichainReducedHardCoreOn_of_threshold_at`
   * `strictAntichainReducedHardCoreOn_of_threshold`
   * `strictAntichainReducedHardCoreOn_of_expectation_critical`
   * `exists_generator_scale_pow_lt_card_of_sparse`
   * `scale_lt_card_of_sparse`
   * `two_le_scale_of_large_constant`
   * `two_lt_card_of_scale_lt_card`
   * `strictAntichainScaledHardCoreOn_of_scaleOnlyHardCoreOn`
   * `strictAntichainScaleOnlyHardCoreOn_of_reducedHardCoreOn`
   * `global_pow_lt_half_of_noHeavy`
   * `strictAntichainSparseHardCoreOn_of_scaledHardCoreOn`
   * `park_pham_threshold_not_small_lt_of_strict_core_on`
   * `park_pham_threshold_not_small_lt_exists_of_strict_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_generated_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_antichain_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_antichain_multi_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_antichain_large_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_antichain_sparse_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_antichain_scaled_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_antichain_scale_only_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_antichain_reduced_hard_core`
   * `park_pham_threshold_not_small_lt_exists_of_threshold_at`
   * `park_pham_threshold_not_small_lt_exists_of_threshold`
   * `park_pham_threshold_not_small_lt_exists_of_expectation_critical`
   * `park_pham_threshold_not_small_lt_large_exists`
   * `park_pham_threshold_at_exists`
   * `bernoulliMass_insert_of_notMem`
   * `bernoulliMass_insert_with_mem`
   * `insert_injective_on_powerset_of_notMem`
   * `powerset_disjoint_image_insert_of_notMem`
   * `not_pSmall_of_spread`
   * `mu_at_partition_density_ge_half_of_threshold`
   * `partition_density_to_disjoint_members`
   * `spread_disjointness_theorem`

   What remains is the strict-density Park--Pham/Kahn--Kalai implication from
   `(∀ S ∈ U, S ⊆ X)`, `¬ pSmall X U q`, and `IncreasingIn X U` to
   `muP X U (C * q * log (ell X U)) >= 1/2` at the exact threshold, under the
   additional hypothesis `C * q * log (ell X U) < 1`.  The endpoint
   `= 1` is already proved in `park_pham_threshold_not_small_exists`.

   After the latest finite reductions, a focused proof of the remaining core can
   assume the genuinely nontrivial case:

   * `(∅ : Finset α) ∉ U`; the `∅ ∈ U` whole-cube branch is handled by
     `park_pham_threshold_not_small_lt_of_empty_mem` and
     `park_pham_threshold_not_small_lt_reduce_empty`.
   * For the enlarged constant used downstream, `q < 1`; this follows from
     `q_lt_one_of_large_constant_threshold_le_one`.
   * `minimalMembersIn X U` is nonempty under non-smallness, and its members are
     nonempty under `(∅ : Finset α) ∉ U`.
   * The generated-family reduction may assume an inclusion-antichain generator:
     `StrictGeneratedCoreOn` now requires `InclusionAntichain A`, and
     `strict_nonSmallCoreOn_of_generatedCoreOn` supplies this by taking
     `A = minimalMembersIn X U`.
   * For generated antichains, the minimal members of the upper closure are now
     identified exactly with the generator by
     `minimalMembersIn_upClosureIn_eq_of_inclusionAntichain`, and
     `ell_upClosure_eq_of_inclusionAntichain` rewrites the complexity parameter
     to `max 2 (A.sup Finset.card)`.
   * The easy high-density branch is closed: if
     `1 / 2 <= (C * q * log (ell X U)) ^ ell X U`, then
     `park_pham_threshold_not_small_lt_of_pow_ell_ge_half` proves the desired
     product-measure lower bound.  Thus the remaining proof can target
     `StrictGeneratedHardCoreOn`, where the additional hypothesis is the
     genuinely low-density condition
     `(C * q * log (ell X (upClosureIn X A))) ^
        ell X (upClosureIn X A) < 1 / 2`.
   * The remaining generated hard core can also be stated in the explicit
     antichain-generator form `StrictAntichainHardCoreOn`, where the complexity
     parameter is `max 2 (A.sup Finset.card)` and the automatic hypotheses
     `A.Nonempty` and `(∅ : Finset α) ∉ A` are exposed directly.
   * The one-generator antichain hard-core case is elementary and closed by
     `strictAntichainHardCoreOn_of_multiHardCoreOn`.  The remaining explicit
     antichain target can therefore assume `1 < A.card`, exposed as
     `StrictAntichainMultiHardCoreOn`.
   * The two-generator antichain hard-core case is also elementary and closed
     by `strictAntichainMultiHardCoreOn_of_largeHardCoreOn`: the smaller
     generator alone has enough principal-up-closure mass.  The remaining
     explicit antichain target can therefore assume `2 < A.card`, exposed as
     `StrictAntichainLargeHardCoreOn`.
   * Any branch where a single generator already has target-density mass at
     least `1 / 2` is closed by
     `strictAntichainLargeHardCoreOn_of_sparseHardCoreOn`.  The remaining
     explicit antichain target can therefore assume every generator has
     `(C * q * log(max 2 (A.sup card))) ^ S.card < 1 / 2`, exposed as
     `StrictAntichainSparseHardCoreOn`.
   * A proof of the standard expectation-threshold package, either at exact
     density (`park_pham_threshold_not_small_lt_exists_of_threshold_at`) or at
     any larger density (`park_pham_threshold_not_small_lt_exists_of_threshold`),
     now also plugs directly into the remaining public package.  This is the
     cleanest bridge from the usual Park--Pham/Kahn--Kalai theorem statement to
     the repo's current non-smallness axiom surface.
   * The same standard expectation-threshold package now plugs directly into
     the current sparse hard-core formulation through
     `strictAntichainSparseHardCoreOn_of_threshold_at` and
     `strictAntichainSparseHardCoreOn_of_threshold`.
   * It also plugs directly into the current reduced antichain hard-core
     formulation through `strictAntichainReducedHardCoreOn_of_threshold_at`
     and `strictAntichainReducedHardCoreOn_of_threshold`; the extra reduced
     hypotheses are finite reductions that become irrelevant once the standard
     `qSmallUpper` theorem is available.
   * A conventional theorem stated using this file's `ExpectationAtMost` and
     `CriticalAtMost` predicates plugs directly into the reduced core through
     `strictAntichainReducedHardCoreOn_of_expectation_critical`, and into the
     public package through
     `park_pham_threshold_not_small_lt_exists_of_expectation_critical`.
   * A local search of Mathlib v4.27.0 found no packaged
     Kahn--Kalai/Park--Pham expectation-threshold theorem to import directly;
     the local Park--Vondrak-style formalization below supplies the needed
     finite theorem in this project.
   * The Park--Vondrak simplified proof route has now been started in
     `ParkPham/Fragments.lean`: fragments `F(H,W) = {S \ W | S in H}`,
     minimal fragments, and their large/small cardinality split are defined
     with the basic finite cover and boundedness lemmas.  This is
     infrastructure for the cost lemma in that proof, not a new trust-boundary
     assumption.
   * The finite cover-cost layer is now in `ParkPham/Cost.lean`: cover cost
     is defined as a finite minimum over ground-supported covers, is connected
     back to the existing `pSmall` predicate, and has monotonicity and union
     subadditivity lemmas.  This is the local API needed by the Park--Vondrak
     cost iteration.
   * `ParkPham/FragmentCost.lean` proves the deterministic cost step used in
     the Park--Vondrak iteration:
     `coverCost H <= coverCost smallFragments + coverCost largeFragments`.
     It also proves the cutoff-`1` endpoint converting positive final
     small-fragment cost into an original source member covered by the exposed
     set.
   * `ParkPham/FragmentIteration.lean` packages the finite deterministic
     Park--Vondrak iteration: repeated small-fragment steps, accumulated
     large-fragment cost, the telescoping inequality, and the endpoint theorem
     that a strict total large-cost loss yields an exposed union lying in the
     original upper closure.  It also includes the finite Bernoulli averaging
     choice step turning an expected large-fragment cost bound into one
     low-loss exposure.
   * The loose Park--Vondrak large-fragment averaging estimate is now proved
     as
     `bernoulli_average_largeCost_le_muP_mul_two_pow_inv`:
     the expected large-fragment cover cost is bounded by
     `muP X (upClosureIn X H) rho * (2^ell / L^m)`.  This estimate is threaded
     through the snoc exposure sequence by the refined budget lemmas in
     `FragmentIteration.lean` and the scalar bridge in `Threshold.lean`.
   * `ProductMeasure.lean` now includes the finite Markov/complement lemma
     `half_lt_weighted_good_of_average_lt_half_of_bad_le`, its Bernoulli
     specialization `half_lt_muP_of_average_lt_half_of_bad_le`, the exposure
     tuple space/weight API
     (`exposureTupleSpace`, `exposureTupleWeight`,
     `sum_exposureTupleWeight_eq_one`, `exposureTupleUnion`,
     `tupleUnionDensity`, `tupleUnionDensity_snoc`,
     `tupleUnionDensity_const`, `exposureTupleUnion_measure_zero`,
     `exposureTupleUnion_measure_one`,
     `exposureTupleUnion_measure_eq_muP`), the fixed-union slice
     `unionShiftFamily` with coordinate-splitting rewrites and
     `muP_insert_unionShift_absent` / `muP_insert_unionShift_present`, and the
     scalar Bernoulli union bound `one_sub_one_sub_q_pow_le_nat_mul`.
     `FragmentIteration.lean` now
     connects these to the fragment machinery through
     `exposureTupleSteps`, `exposureTupleStepsSnoc`,
     `smallStepExposureUnion_exposureTupleSteps`,
     `smallStepExposureUnion_exposureTupleStepsSnoc`,
     `exposureTupleStepsSnoc_last_shape`,
     `exists_exposure_largeCost_lt_of_muP_mul_two_pow_inv_lt`,
     `exposure_mem_upClosureIn_of_largeCost_lt`,
     `half_lt_muP_of_average_largeCost_lt_half_coverCost`, and
     `half_lt_muP_of_muP_mul_two_pow_inv_lt_half_coverCost`, the
     non-smallness budget corollaries
     `half_lt_coverCost_of_not_pSmall_upClosureIn` and
     `half_lt_muP_of_not_pSmall_upClosureIn_muP_mul_two_pow_inv_lt_quarter`,
     plus the multi-outcome endpoints
     `half_lt_weighted_endpoint_of_iteratedLargeCost_average_lt` and
     `half_lt_exposureTuple_endpoint_of_iteratedLargeCost_average_lt`, and the
     direct `muP` snoc endpoint
     `half_lt_muP_of_iteratedLargeCostSnoc_average_lt`, together with the
     non-smallness-budget corollary
     `half_lt_muP_of_not_pSmall_iteratedLargeCostSnoc_average_lt_quarter`.
     The same file now also has the finite snoc bookkeeping needed for the
     remaining induction:
     `smallMinimalFragments_subset_ground`,
     `smallMinimalFragments_card_le_of_forall_card_le`,
     `iteratedSmallFragments_subset_ground`,
     `iteratedSmallFragments_card_le_of_forall_card_le`,
     `exposureTupleStepsSnoc_snoc`,
     `iteratedLargeCostSum_exposureTupleStepsSnoc_snoc`,
     `iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc`,
     `bernoulli_average_iterated_final_largeCost_le_muP_mul_two_pow_inv`,
     `iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_of_final_average_le`,
     `iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_muP_final`,
     `iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget`,
     `iteratedLargeCostSum_exposureTupleStepsSnoc_sum_snoc_le_tail_add_budget_of_current_bound`,
     `snocCurrentCardBound`, `snocLargeCostBudget`,
     `iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_snocLargeCostBudget`,
     `iteratedLargeCostSum_exposureTupleStepsSnoc_sum_le_budget_sum`,
     `iteratedSmallFragments_exposureTupleStepsSnoc_card_lt_last`, and
     `iteratedSmallFragments_exposureTupleStepsSnoc_card_le_last`.
   * `ProductMeasure.lean` now also has scalar density union bounds
     `tupleUnionDensity_le_sum`, `tupleUnionDensity_le_sum_of_le`, and
     `tupleUnionDensity_one_sub_pow_le_q_sum`.
   * The sparse hard-core assumptions now expose the finite size consequence
     `exists_generator_scale_pow_lt_card_of_sparse`: some generator satisfies
     `(C * log(max 2 (A.sup card))) ^ S.card < A.card`.  This isolates the
     combinatorial growth obstruction that a direct Kahn--Kalai/Park--Pham
     proof must overcome.
   * With the downstream large-constant hypothesis, this implies the cleaner
     necessary condition `scale_lt_card_of_sparse`:
     `C * log(max 2 (A.sup card)) < A.card`.
   * The current sparse target can therefore be sharpened to
     `StrictAntichainScaledHardCoreOn`, where that scale condition is an
     explicit hypothesis supplied automatically by
     `strictAntichainSparseHardCoreOn_of_scaledHardCoreOn`.
   * The scale condition itself implies the previously separate cardinality
     lower bound `2 < A.card` via `two_lt_card_of_scale_lt_card`, so the current
     target can be stated without redundant nonempty/cardinality hypotheses as
     `StrictAntichainScaleOnlyHardCoreOn`.
   * The global low-density hypothesis
     `(C * q * log(max 2 (A.sup card))) ^ max 2 (A.sup card) < 1 / 2`
     is also redundant once every generator is individually light; this is
     captured by `global_pow_lt_half_of_noHeavy`.  The current clean target is
     therefore `StrictAntichainReducedHardCoreOn`.
   * The reduced hard-core target is now itself reduced to the explicit
     Park--Vondrak finite-iteration certificate
     `StrictAntichainReducedPVCertificateOn`.  The theorem
     `strictAntichainReducedHardCoreOn_of_pvCertificateOn` proves that such a
     certificate gives `StrictAntichainReducedHardCoreOn`, and
     `park_pham_threshold_not_small_lt_exists_of_pv_certificate` plugs a
     uniform certificate directly into the public strict Park--Pham package.
     The cleaner quarter-budget surface
     `StrictAntichainReducedPVQuarterCertificateOn`, with bridges
     `strictAntichainReducedHardCoreOn_of_pvQuarterCertificateOn` and
     `park_pham_threshold_not_small_lt_exists_of_pv_quarter_certificate`, uses
     non-smallness to replace the cover-cost-relative loss bound by the
     absolute target `< 1/4`.
   * `Threshold.lean` now includes a coarse numeric bridge
     `StrictAntichainReducedPVNumericSchemeOn` and
     `park_pham_threshold_not_small_lt_exists_of_pv_numeric_scheme`.  This
     bridge is a valid sufficient criterion for the existing fixed-`ell`
     budget lemma, but it is probably too strong for the final parameter
     choice: the viable Park--Vondrak proof should use the current
     post-small-fragment cardinality bound at each stage, exposed by
     `iteratedSmallFragments_exposureTupleStepsSnoc_card_le_last`, rather than
     charging every stage against the original `max 2 (A.sup card)`.
   * The corresponding refined bridge is now present:
     `StrictAntichainReducedPVSnocBudgetSchemeOn`,
     `strictAntichainReducedPVQuarterCertificateOn_of_snocBudgetSchemeOn`, and
     `park_pham_threshold_not_small_lt_exists_of_pv_snoc_budget_scheme`.
     This is the finite target used for the Park--Pham proof: construct `L`
     and `cutoff` with
     `q * sum_i L_i <= C*q*log(max 2 (A.sup card))`,
     `cutoff last = 1`, and
     `snocLargeCostBudget (max 2 (A.sup card)) cutoff L < 1/4`.
   * This has been reduced one step further to a pure scalar target:
     `PVSnocScalarParameterScheme`.  The theorem
     `park_pham_threshold_not_small_lt_exists_of_exists_pv_scalar_parameter_scheme`
     shows that an existential proof of a large enough scalar constant
     satisfying this scheme proves `park_pham_threshold_not_small_lt_exists`.
     The concrete theorem `pvSnocScalarParameterScheme_128_div_log_two` supplies
     that scalar constant using block length `64` and power-of-two cutoffs.
