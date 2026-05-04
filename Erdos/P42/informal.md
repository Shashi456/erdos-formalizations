# Erdős Problem 42 — Sidon difference avoidance

> Sources:
> - **Harjas / GPT-5.5 Pro** (April 27 2026, corrected): *A Fourier-Compactness Proof of Erdős Problem 42* — `proof.pdf` in this directory.
> - **Kevin Barreto / GPT-5.5 Pro** (April 29 2026): *Sidon Difference Avoidance* — combines #42 + #43 — `proof_combined_42_43.pdf`.
> - **natso26 / Tao** (April 30 2026): *A Fourier-positive proof of Erdős Problem 42* — clean continuous-version note — `proof_ulam_note.pdf`.
> - Forum: [erdosproblems.com/forum/thread/42](https://www.erdosproblems.com/forum/thread/42) — captured as `forum_thread.md`.

## Problem statement

**Erdős #42** (`[Er95]`). For every integer `M ≥ 1`, is it true that for every sufficiently large `N` (in terms of `M`) and every Sidon set `A ⊆ {1, …, N}`, there is another Sidon set `B ⊆ {1, …, N}` of size `M` with

```
(A − A) ∩ (B − B) = {0}?
```

(For `A = ∅` the equality `= {0}` is impossible since `0 ∉ A − A`; the natural form is `(A − A) ∩ (B − B) ⊆ {0}`, which we use.)

## Main theorem (Theorem 1.1 in `proof.pdf`, Theorem 1.1 in `proof_combined_42_43.pdf`)

For every integer `M ≥ 1` there is `N₀(M)` such that the following holds for every `N ≥ N₀(M)`. If `A ⊆ [N]` is a non-empty Sidon set, then there is a Sidon set `B ⊆ [N]` with `|B| = M` and `(A − A) ∩ (B − B) = {0}`.

## Proof outline (following natso26's note `proof_ulam_note.pdf`)

The cleanest exposition uses **Tao's continuous analogue + compactness** to reduce the discrete problem to a continuous one. Three layers:

### Layer 1: Continuous key lemma (Tao, May 2026)

**Theorem.** Let `G` be a connected compact abelian group, and let `f : G → [0, 1]` be measurable, positive definite (i.e., `\hat{f} ≥ 0`), but not identically `1`. Then for almost every `(x_1, …, x_M) ∈ G^M`, `f(x_i − x_j) < 1` for all `1 ≤ i < j ≤ M`.

*Proof sketch.* Write `f(x) = ∑_ξ \hat{f}(ξ) e(ξ · x)`. Non-negativity of `\hat{f}` makes `f(x) = 1` exactly when `ξ · x = 0 mod 1` for all `ξ ∈ supp(\hat{f})`. So `{x : f(x) = 1}` is a closed subgroup, proper (since `f ≢ 1`) and not open (since `G` is connected), hence has Haar measure zero. Apply Fubini.

### Layer 2: One-sided finite avoidance lemma (compactness)

**Lemma 2.1 in the ulam note.** Fix `M ≥ 1`, `0 < α₀ ≤ α₁ < 1/2`. Let `p_n → ∞` (primes), `α₀ p_n ≤ L_n ≤ α₁ p_n`, `I_n := {1, …, L_n} ⊆ 𝔽_{p_n}`. Let `F_n ⊆ 𝔽_{p_n}` be symmetric, `0 ∈ F_n`, `|F_n| ≤ p_n / 2`, and `\hat{1_{F_n}}(γ) ≥ −o(p_n)` uniformly. Then

```
liminf_n Pr_{x_1,…,x_M ∈ I_n}[ x_i − x_j ∉ F_n for all 1 ≤ i < j ≤ M ] > 0.
```

*Proof.* By Tao's `U²` arithmetic regularity + complexity-1 counting (Green-Tao), pass to a subsequential continuous limit `f : G → [0, 1]` on a connected compact abelian `G` with `\hat{f} ≥ 0` and `∫ f ≤ 1/2`. Apply the continuous key lemma to `f` (so `f ≢ 1`) to get the limiting probability is positive.

### Layer 3: Erdős #42 from the avoidance lemma

Given Sidon `A ⊆ [N]` (non-empty, WLOG `0 ∈ A` after a shift). Pick a prime `p` with `2N < p < 4N` (Bertrand). Embed `A ⊆ 𝔽_p`. Let `F := A − A ⊂ 𝔽_p` (symmetric, `0 ∈ F`, `|F| ≤ |A|² ≤ N + 1 ≤ p/2` for large enough `N`).

The Sidon property gives `\hat{1_F}(γ) = |\hat{1_A}(γ)|² − (|A| − 1) ≥ −(|A| − 1) ≥ −√p`. So Lemma 2.1 applies: a uniform random `M`-tuple in `(0, p/4)` has all pairwise differences `∉ F` with positive probability `≫_M 1`.

Among these `M`-tuples, the probability that `B = {x_1, …, x_M}` is *not* Sidon is `≪ M⁴ / p`. For `p` large enough (`p ≫_M 1`), positive probability remains, so a Sidon `B ⊆ (0, p/4) ⊆ [N]` of size `M` with `(A − A) ∩ (B − B) = {0}` exists. ∎

## Black-box dependencies

The proof rests on **Green-Tao `U²` arithmetic regularity + complexity-1 counting lemma**. Mathlib has substantial Fourier-analysis machinery (Fourier transforms on `ZMod p`, characters, Pontryagin duality for compact abelian groups) but does *not* yet have:
- The arithmetic regularity lemma in its `U²` form
- The complexity-1 generalized von Neumann theorem of Green-Tao

The **Tao continuous-analogue lemma** (Layer 1) is essentially Mathlib-provable directly: Fourier series on compact abelian groups + closed-subgroup measure-zero from connectedness. ~50 lines once the right Mathlib pieces are in scope.

We propose **two trust-boundary axioms** (analogous to `stiebitz_lower_bound` / `mertens_product`):

1. `complexity_one_counting_lemma` — the finitary counting principle stating that, for any function `g : 𝔽_p → [0, 1]` and any constant-density set with controlled `U²`-norm, the count of complexity-1 patterns matches the random expectation up to lower-order error. Classical (Green-Tao 2008).

2. `compact_U2_regularity_subsequential_limit` — given a sequence of functions `f_n : 𝔽_{p_n} → [0, 1]` with `p_n → ∞`, a subsequence converges in the `U²` sense to a model function on a compact connected abelian limit group. Classical (compactness packaging of Szemerédi-style regularity).

(These could be folded into a single axiom if preferred; we'll keep them separate for clarity.)

## Stretch goal: formalize the underlying lemmas

Both axioms are real Mathlib gaps. Proving them cleanly inside Mathlib would be a significant analytic-combinatorics contribution and is a natural follow-up PR. The scope is comparable to the cycle-reduction lemma we extracted from P750.

## Differences from the LaTeX (planned)

- We follow natso26's exposition (`proof_ulam_note.pdf`) since it's the cleanest.
- Sidon sets are encoded via Mathlib's `IsSidon` (in `Combinatorics.Additive.Sidon`).
- The discrete-to-continuous reduction is treated as a single named axiom; layer 1 (the continuous lemma itself) is proved in Mathlib-style if reachable.
- The probabilistic argument in Layer 3 is replaced by a *constructive* counting argument: pick a tuple by enumerating over the positive-density set guaranteed by the avoidance lemma.

## Comparison with Sedov's `M = 3` formalization

Sedov's [github.com/Gusarich/erdos42](https://github.com/Gusarich/erdos42) handles only `M = 3` via the Balogh-Liu-Sharifzadeh-Treglown 2/5 trichotomy (Astérisque 258, 1999). Our target is the **general `M`** case via the Fourier-compactness proof. The two approaches are essentially independent — `M = 3` axioms (sum-free trichotomy) are unrelated to ours (Green-Tao counting).
