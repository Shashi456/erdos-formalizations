# Erdős #202 — informal statement

## Problem

Given integers `n_1 < n_2 < ⋯ < n_r ≤ N` and residues `a_i mod n_i`, suppose
that no integer lies in more than one of the residue classes
`{m : m ≡ a_i (mod n_i)}`. How large can `r = r(N)` be?

Let `f(N)` denote this maximum.

## Sharp asymptotic (May 2026 proof)

```
f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))   as N → ∞.
```

This matches BFV's (de la Bretèche–Ford–Vandehey) unconditional lower
bound, and tightens the BFV upper bound which had `(1 + o(1))` replaced by a
larger constant.

The matching upper bound is the conjectured "BFV-sharp" form.

## Key ingredients

1. **BFV pruning** — pass to a subfamily `Q'` with all moduli in
   `[N · L(-2, N), N]`, all `ω(q) = K ≤ 3 M(N)`, all `h(q) ≤ exp(sqrt(log N))`,
   and distinct radicals; loses at most a factor `L(o(1), N)` in cardinality.
2. **BFV ω-count** — `#{n ≤ y : ω(n) = K - W} ≤ y · L(-d/2 + o(1), N) · (log N)^{W/2}`
   uniformly in the relevant range.
3. **Spread-core lemma** *(new ingredient)* — a non-disjoint uniform family
   on `[K]` always has a "core" appearing in at least
   `|A| / (C₀ log(eK))^{|C|}` many members. Derived from Park–Pham.
4. **Descending chain** — at each step, the gcd intersection criterion
   forces the remaining-support sets to form an intersecting family; the
   spread-core lemma extracts a heavy core; weighted pigeonhole on
   exact prime-power blocks gives `P_r`; residue pigeonhole modulo `P_r`
   keeps `Q'` large; iterate.
5. **Optimization** — set `σ_N = log(N / |Q'|) / Z(N)` and show
   `1 ≤ c σ_N - c²/4 + o(1)` where `c = R / M(N)`; quadratic completion
   forces `σ_N ≥ 1 - o(1)`.

## Lower bound

Unchanged from BFV — explicit construction. The spread-core ingredient is
needed only for the matching upper bound.

## What `o(1)` means here

In every step we replace informal `o(1)` by an explicit `ε > 0` with
"eventually" quantification over `N`. The pruning, count, and chain
inequalities all have such uniform `ε`-statements; the final optimization
performs `ε`-bookkeeping at the end.

## Reference

PDF: `docs/spread_core_proof.pdf` (to be added).
