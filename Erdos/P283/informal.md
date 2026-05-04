# Erdős Problems 283 + 351 — Polynomial Egyptian sums

> Source: GPT-5.5 Pro + Liam Price (cleanup) + Kevin Barreto (noticed #351 follows), *Polynomial Egyptian Sums*, 3 May 2026.
> Forum: [erdosproblems.com/forum/thread/283](https://www.erdosproblems.com/forum/thread/283), [erdosproblems.com/forum/thread/351](https://www.erdosproblems.com/forum/thread/351).

## Problem statements

**Erdős #283** (`[ErGr80, p.32]`). Let `p : ℤ → ℤ` be a polynomial with positive leading coefficient and no fixed divisor (no `d ≥ 2` with `d ∣ p(n)` for all `n ≥ 1`). For all sufficiently large `m`, are there distinct positive integers `n_1 < ⋯ < n_k` with `1/n_1 + ⋯ + 1/n_k = 1` and `m = p(n_1) + ⋯ + p(n_k)`?

**Erdős #351** (`[ErGr80, p.58]`). Let `p ∈ ℚ[x]` be non-constant with positive leading coefficient. Is `A_p = { p(n) + 1/n : n ∈ ℕ }` strongly complete (every sufficiently large integer is a finite subset-sum from `A_p \ B` for any finite `B`)?

The May 3 proof resolves both: **#283 affirmatively** for any rational `α > 0` (a strict generalization of Erdős's question with `α = 1`), and **#351** affirmatively after the corrected hypothesis (allow `p = 0` or `p ≠ 0` with non-negative leading coefficient).

## Main theorem (Theorem 1 in the PDF)

Let `α ∈ ℚ_{>0}`, `L ≥ 1`, and let `p ∈ ℚ[x]` satisfy `p(ℤ) ⊆ ℤ`. Suppose `p` has positive leading coefficient and no integer `d ≥ 2` divides `p(n)` for all `n ≥ 1`. Then there is `m_0` such that for all `m ≥ m_0`, there exist distinct positive integers `L < n_1 < ⋯ < n_k` with

```
∑ 1/n_i = α        and        ∑ p(n_i) = m.
```

Erdős #283 is the special case `α = 1, L = 0`.

## Black box: Roth-Szekeres-Graham (Theorem 2 in the PDF)

> **Theorem 2 (Roth–Szekeres–Graham).** Let `f ∈ ℚ[x]` be nonconstant with positive leading coefficient, satisfying `f(n) ∈ ℤ_{>0}` for `n ≥ 1` and `gcd{f(n) : n ≥ 1} = 1`. Then there is `X_f` such that all integers `X ≥ X_f` belong to `FS(f(1), f(2), f(3), …)` (finite subset sums).

This is **Graham's complete-polynomial-values theorem** (Duke Math. J. 1964), with **Roth–Szekeres** (Quart. J. Math. 1954) as the asymptotic input. We treat it as the single trust-boundary axiom for the proof.

## Proof outline

### §1. Egyptian switches (four lemmas, axiom-free)

**Lemma 3.** Any `R ∈ ℚ_{>0}` admits Egyptian expansions (sums of distinct unit fractions with denominators `> L`) with all sufficiently large numbers of terms. Proof: greedy + replacement `1/y = 1/(y+1) + 1/(y(y+1))`.

**Lemma 4.** For any integers `T, M ≥ 1` and `ρ ∈ ℤ/Mℤ`, there exists an Egyptian pattern `E` (a finite set with `∑_{e∈E} 1/e = 1`) such that `T ∣ e` for every `e ∈ E` and `|E| ≡ ρ (mod M)`. Proof: rescale Lemma 3.

**Lemma 5.** If `Bp(x) ∈ ℤ[x]` and `x ≡ y (mod mB)`, then `p(x) ≡ p(y) (mod m)`. So `mB` is a period of `p(n) (mod m)`.

**Lemma 6.** If `p` has degree `≥ 1`, positive leading coefficient, and no fixed divisor, there are finitely many Egyptian patterns `E_1, …, E_s` such that the switching polynomials `Q_{E_i}(x) := ∑_{e ∈ E_i} p(ex) − p(x)` jointly have `gcd 1` on the positive integers.

### §2. Proof of Theorem 1

Constant case (`deg p = 0`): trivial via Lemma 3.

Non-constant case (`deg p ≥ 1`, leading coefficient `a > 0`, degree `r`). Set up *three families of denominators*:

- **Main slots.** With `P := 36`, `u_j := P j + 1`, `D_j := u_j u_{j+1}`. Note `1/D_j = (1/P)(1/u_j − 1/u_{j+1})` (telescopes). Use the identity `1/x = 1/(2x) + 1/(3x) + 1/(6x)` (the Egyptian pattern `E_0 = {2,3,6}`); the switching polynomial is `A(x) := p(2x) + p(3x) + p(6x) − p(x)`. The leading coefficient of `A` is `a · Θ` where `Θ = 2^r + 3^r + 6^r − 1 > 1`.

- **Correction slots.** Choose finitely many Egyptian patterns `E_{i_σ}` so that `Q_{E_{i_σ}}(a_σ) (mod g)` (with `g := gcd{A(D_j)}`) generate `ℤ/gℤ`. Build correction denominators `c_ν` with prescribed congruences (using Lemma 5's periodicity). Each `c_ν` admits a switch with switching polynomial `b_ν := Q_{E_{i_σ}}(c_ν)`.

- **Filler denominators.** Use Lemma 3 to get `R_0 = α − 1/(P u_J) − C_0` as `∑_{f ∈ F} 1/(Λ f)` for an integer scaling `Λ` (chosen `> Y_corr` and `8 ∣ Λ`, ensuring no collision with main/correction). These never switch.

The reciprocal identity `∑ 1/D_j + 1/τ_N + ∑ 1/c_ν + ∑ 1/(Λ f) = α` holds (with `τ_N := P u_{N+1}`).

**Switch operations** preserve the reciprocal sum:
- Main slot `D_j`: leave alone, OR replace with `{2 D_j, 3 D_j, 6 D_j}`. Δp-sum = `+ A(D_j)`.
- Correction slot `c_ν`: leave alone, OR replace with `{e c_ν : e ∈ E_{i_σ}}`. Δp-sum = `+ b_ν`.

**Collision avoidance.** Use 2-adic and 3-adic valuations: each `D_j` (and its multiples by `1, 2, 3, 6`) has a unique `(v_2, v_3)` profile that distinguishes from `τ_N`, correction slots, and filler denominators (the last enforced by `8 ∣ Λ`).

**Attainable intervals.** For each large `N`, the set of attainable `m` covers `[B_N + B_* + M_0, B_N + μ N^{2r}]`, where `B_N` is the base sum and `μ ∈ (a P^{2r}, a Θ P^{2r})`. The lower endpoint is reachable by a correction subset hitting any residue class `mod g`; the upper endpoint by Roth-Szekeres-Graham (Theorem 2) applied to a rescaled polynomial `q`.

**Overlap of intervals.** Consecutive intervals overlap because `B_{N+1} − B_N = λ N^{2r} + O(N^{2r-1})` with `λ < μ`. So `⋃_N I_N` covers all sufficiently large integers. ∎

## Corollary 7 (Erdős #351)

**Strong completeness** of `A_p = {p(n) + 1/n : n ∈ ℕ}`:
- If `p = 0`: every positive integer is a sum of distinct unit fractions with denominators bounded below (Lemma 3).
- If `p ≠ 0` with positive leading coefficient: scale to `q(x) := Dp(x)/h` (integer-valued, no fixed divisor) and apply Theorem 1 to each residue `r ∈ {1, …, h}` of `Dm` mod `h`.
- If `p` has *negative* leading coefficient: `A_p` is bounded above by finitely many positive elements, so cannot be strongly complete.

## Black-box dependency

`roth_szekeres_graham` (= Theorem 2) is the single non-Mathlib axiom. Both Roth-Szekeres (1954) and Graham (1964) are classical, unconditional results. Mathlib has surrounding analytic-NT infrastructure but not this named theorem.

## Differences from the LaTeX writeup (planned)

- Egyptian patterns will be encoded as `Finset ℕ` with the `∑_{e ∈ E} 1/e = 1` predicate (rationals).
- Polynomials use `Polynomial ℚ` (we cast to `Polynomial ℤ` when convenient).
- The `(v_2, v_3)`-valuation collision-avoidance argument inlines `padicValNat`.
- The `Fin (k+1) → ℤ` indexing in FC's `Erdos283.Condition` is preserved; we provide a wrapper at the end.
