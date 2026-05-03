# Erdős Problem 694 — Totient Fibre Extremes

Source problem: [`google-deepmind/formal-conjectures/.../694.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/694.lean)

PDF: `694.pdf` (5 pages, "TOTIENT FIBRE EXTREMES" by GPT-5.5 Pro)

Forum thread: <https://www.erdosproblems.com/forum/thread/694> · cached at `data/thread_cache/694.html`

Authorship: **Liam Price** prompted **GPT-5.5 Pro** (May 1 2026). Cleanly rewritten outline by **Thomas Bloom** (May 2 2026 forum comment).

## Problem

Let $\phi$ be Euler's totient. For $n$ in the image of $\phi$, define
$$
f_{\min}(n) = \min \{m : \phi(m) = n\},\quad f_{\max}(n) = \max \{m : \phi(m) = n\}.
$$
Investigate
$$
\mathcal{R}(x) := \max_{\substack{n \le x \\ n \in \phi(\mathbb{N})}} \frac{f_{\max}(n)}{f_{\min}(n)}.
$$

The FC file additionally records two related sub-problems:
- `erdos_694.variants.carmichael` — Carmichael's question (open).
- `erdos_694.variants.inf_unique` — Erdős's permanence theorem.

## Result (Theorem 2.1)

$$
\mathcal{R}(x) = (e^\gamma + o(1))\log\log x.
$$

## Section 1 — Preliminaries

**Standing facts used (all unconditional):**
- **Prime number theorem (Chebyshev form):** $\vartheta(y) := \sum_{p \le y} \log p \sim y$.
- **Mertens' product theorem:** $\prod_{p \le y}(1 - 1/p)^{-1} \sim e^\gamma \log y$.
- **Linnik's theorem:** there are absolute constants $C, L \ge 1$ such that for every $a \ge 1$, the least prime $\ell \equiv 1 \pmod a$ satisfies $\ell \le C a^L$.

**Fibre finiteness.** For every prime power $p^a$,
$$
\phi(p^a)^2 = p^{2a-2}(p-1)^2 \ge p^a.
$$
Multiplying over prime-power factorisation gives $\phi(m)^2 \ge m/2$ for all $m \ge 1$. Hence if $\phi(m) = n$, then $m \le 2n^2$. So $f_{\min}, f_{\max}$ are genuine finite-valued functions on $\phi(\mathbb{N})$.

**Lemma 1.1 (Landau's max-ratio asymptotic).** As $T \to \infty$,
$$
\max_{1 \le m \le T} \frac{m}{\phi(m)} = (e^\gamma + o(1))\log\log T.
$$

*Proof sketch.* Let $N_k = p_1 p_2 \cdots p_k$ (the $k$-th primorial). Choose $k$ so $N_k \le T < N_{k+1}$. For any $m \le T$ with $\omega(m) = r$, sorting primes shows $m/\phi(m) \le \prod_{i=1}^r p_i/(p_i-1) \le \prod_{i=1}^k p_i/(p_i-1)$, with equality at $m = N_k$. Mertens gives the product equals $(e^\gamma + o(1))\log p_k$. Then $\log N_k = \vartheta(p_k) \sim p_k$ and $T < N_{k+1}$ pin $p_k \sim \log T$. ∎

## Section 2 — The asymptotic formula

**Theorem 2.1.** $\mathcal{R}(x) = (e^\gamma + o(1))\log\log x$.

### Upper bound

Let $n \le x$ be a totient value, $M = f_{\max}(n)$, $m = f_{\min}(n)$. Since $\phi(M) = \phi(m) = n$,
$$
\frac{M}{m} = \frac{M/\phi(M)}{m/\phi(m)} \le \frac{M}{\phi(M)}
$$
because $m/\phi(m) \ge 1$. Fibre-finiteness gives $M \le 2n^2 \le 2x^2$, so by Lemma 1.1,
$$
\frac{f_{\max}(n)}{f_{\min}(n)} \le \max_{1 \le t \le 2x^2}\frac{t}{\phi(t)} = (e^\gamma + o(1))\log\log(2x^2) = (e^\gamma + o(1))\log\log x.
$$

Taking the max over $n \le x$ proves $\mathcal{R}(x) \le (e^\gamma + o(1))\log\log x$.

### Lower bound (construction)

Let $y \to \infty$ and put
$$
P_y = \prod_{p \le y} p,\qquad A_y = \prod_{p \le y}(p-1).
$$

By **Linnik's theorem**, choose a prime $\ell = \ell_y$ with
$$
\ell \equiv 1 \pmod{A_y},\qquad \ell \le C A_y^L.
$$

Set
$$
U_y = \frac{\ell - 1}{A_y},\qquad Q_y = \prod_{\substack{q \mid U_y \\ q > y}} q
$$
(squarefree product of "large" prime divisors of $U_y$), and define
$$
a_y = \ell\, Q_y,\qquad b_y = P_y\, U_y\, Q_y.
$$

**Claim:** $\phi(a_y) = \phi(b_y)$.

*Verification.*
- $a_y$: Since $U_y < \ell$, $\ell \nmid Q_y$, so $a_y$'s prime divisors are $\ell$ and the $q > y$ in $Q_y$ — all squarefree. Hence
$$
\phi(a_y) = (\ell - 1)\prod_{q \mid U_y,\ q>y}(q-1) = A_y U_y \prod_{q \mid U_y,\ q>y}(q-1).
$$
- $b_y$: prime divisors are exactly the $p \le y$ (in $P_y$) and the $q > y$ in $Q_y$. Therefore
$$
\phi(b_y) = b_y \prod_{p \le y}\!\left(1-\frac{1}{p}\right) \prod_{q \mid U_y,\ q>y}\!\left(1-\frac{1}{q}\right) = P_y U_y Q_y \cdot \frac{A_y}{P_y} \cdot \prod_{q \mid U_y,\ q>y}\!\frac{q-1}{q} = A_y U_y \prod_{q \mid U_y,\ q>y}(q-1).
$$

Both equal $A_y U_y \prod_{q \mid U_y,\ q>y}(q-1) =: n_y$. ✓

**Ratio.**
$$
\frac{b_y}{a_y} = \frac{P_y U_y Q_y}{\ell\, Q_y} = \frac{P_y}{A_y} \cdot \frac{\ell-1}{\ell}.
$$
By Mertens, $P_y/A_y = \prod_{p \le y} p/(p-1) = (e^\gamma + o(1))\log y$. And $(\ell-1)/\ell = 1 + o(1)$ since $\ell \to \infty$. So
$$
\frac{b_y}{a_y} = (e^\gamma + o(1))\log y.
$$
For large $y$ this exceeds $1$, hence $a_y < b_y$ and
$$
\frac{f_{\max}(n_y)}{f_{\min}(n_y)} \ge \frac{b_y}{a_y} = (e^\gamma + o(1))\log y.
$$

**Bounding $n_y$.** Since $Q_y \le U_y$,
$$
n_y = A_y U_y \prod_{q\mid U_y, q>y}(q-1) \le A_y U_y Q_y \le A_y U_y^2.
$$
Using $U_y = (\ell-1)/A_y$ and $\ell \le C A_y^L$, $U_y \le C A_y^{L-1}$, hence
$$
n_y \le A_y (CA_y^{L-1})^2 \ll A_y^{2L-1}.
$$
Also $\log A_y = \sum_{p \le y}\log(p-1) = \vartheta(y) + o(y) = (1 + o(1))y$ (the correction term sums to $\sum_{p \le y}\log(1 - 1/p) = O(y/\log y) = o(y)$ via Mertens).

So $\log n_y \le (2L - 1 + o(1))y$.

**Choice of $y$.** Set
$$
y = \frac{\log x}{4L}.
$$
Then $\log n_y \le \left(\frac{2L-1}{4L} + o(1)\right)\log x < \log x$ for large $x$, hence $n_y \le x$. So $n_y$ is admissible in the maximum, and
$$
\mathcal{R}(x) \ge \frac{f_{\max}(n_y)}{f_{\min}(n_y)} \ge (e^\gamma + o(1))\log y = (e^\gamma + o(1))(\log\log x + O(1)) = (e^\gamma + o(1))\log\log x.
$$

Combining: $\mathcal{R}(x) = (e^\gamma + o(1))\log\log x$. ∎

## Section 3 — Permanence observation

**Proposition 3.1.** Suppose $a > b$ and $\phi(a) = \phi(b) = n$. Then there are infinitely many distinct totient values $N$ with $f_{\max}(N)/f_{\min}(N) \ge a/b$. In particular, the existence of one nontrivial totient fibre implies infinitely many.

*Proof.* For any prime $r \nmid ab$, multiplicativity gives $\phi(ra) = (r-1)\phi(a) = (r-1)n = \phi(rb)$. So $N_r := (r-1)n$ has both $ra$ and $rb$ as preimages, and the ratio is $ra/rb = a/b$. The $N_r$ are distinct as $r$ ranges over the infinitely many primes coprime to $ab$. ∎

This is a small but useful observation: it gives a strengthening of `erdos_694.variants.inf_unique` (which Erdős proved). The PDF's Proposition 3.1 says any *nontrivial collision* (not just unique-preimage situations) propagates to infinitely many.

## Mapping to the FC skeleton

```lean
namespace Erdos694

theorem erdos_694 (max min : ℕ → ℕ)
    (hmax : ∀ n, IsGreatest (Nat.totient ⁻¹' {n}) (max n))
    (hmin : ∀ n, IsLeast (Nat.totient ⁻¹' {n}) (min n))
    (x : ℕ) :
    IsGreatest
      { (max n : ℚ) / min n | (n : ℕ) (_ : n ≤ x) }
      answer(sorry) := by
  sorry                                          -- ← Theorem 2.1 of the PDF

theorem erdos_694.variants.carmichael :
    answer(sorry) ↔ ∃ n > 0, ∃! m, Nat.totient m = n := by
  sorry                                          -- ← NOT addressed by the PDF (still open)

theorem erdos_694.variants.inf_unique
    (h : ∃ n > 0, ∃! m, Nat.totient m = n) :
    { n | ∃! m, Nat.totient m = n }.Infinite := by
  sorry                                          -- ← Proposition 3.1 (PDF strengthens this)

end Erdos694
```

The PDF gives:
- A full proof of `erdos_694` (Theorem 2.1).
- A proof of `erdos_694.variants.inf_unique` (Proposition 3.1; in fact, a strict strengthening — any non-unique fibre suffices, not just a unique one).
- **Nothing** about `erdos_694.variants.carmichael`. That remains genuinely open.

The current `erdos_694` Lean signature is awkward for an asymptotic — the natural Mathlib idiom is a `Tendsto`/`IsLittleO` form against $(e^\gamma \log\log x)$. The `IsGreatest { … } answer(sorry)` shape needs the answer to be replaced with the explicit asymptotic. One reasonable target:

```lean
Filter.Tendsto
  (fun x : ℝ => Real.iSup { ((max n : ℝ) / min n) | (n : ℕ) (_ : (n:ℝ) ≤ x) }
                 / (Real.exp γ * Real.log (Real.log x)))
  Filter.atTop (𝓝 1)
```

(Alternatively a paired upper/lower `IsBigO` × `IsLittleO`.)

## Mathlib readiness

| Prerequisite | Available in Mathlib? | Notes |
|---|---|---|
| `Nat.totient` | yes | basic |
| `Real.eulerMascheroniConstant` (γ) | likely yes | search `Real.eulerMascheroni`, `Real.gamma`. If only `Real.Gamma` (the function) exists, might need a constant defn. |
| Mertens' product theorem $\prod_{p \le y}(1-1/p)^{-1} \sim e^\gamma \log y$ | partially | `Nat.Prime.mertens` etc. exist; the limit form may need stating. Search needed. |
| Chebyshev PNT $\vartheta(y) \sim y$ | yes | `Nat.PrimeCounting.theta_asymptotic` or similar; PNT was formalized in Mathlib in 2023. |
| Linnik's theorem | **NO** | Not in Mathlib. **Must be axiomatized.** Standard Aristotle pattern (cf. #205, #862). |
| Landau's `max m/φ(m) = (e^γ+o(1)) log log T` | **NO** | Mathlib has neither this nor Robin's theorem. The PDF gives a complete elementary proof in Lemma 1.1, so this can be proved from Mertens + PNT directly — does NOT need axiomatization. |

So the formalization plan is:
1. **Axiomatize Linnik's theorem** (1 axiom, with a comment that it's a true theorem unavailable in Mathlib).
2. **Prove Lemma 1.1** from scratch using Mertens (Mathlib) + the primorial structure. Concrete and short.
3. **Prove Theorem 2.1 upper bound** from Lemma 1.1 and fibre-finiteness ($\phi(m)^2 \ge m/2$).
4. **Define the construction** $a_y, b_y, n_y$ as in the PDF.
5. **Prove Theorem 2.1 lower bound** by verifying $\phi(a_y) = \phi(b_y)$, the Mertens-based ratio asymptotic, and the choice $y = (\log x)/(4L)$.
6. **Prove Proposition 3.1** (1 paragraph; uses `Nat.totient_mul_of_coprime`).
7. **Glue into the FC `erdos_694` and `erdos_694.variants.inf_unique` signatures.**

Step 1 is the only place an axiom is needed. Steps 2–6 are all "elementary" from Mathlib's existing PNT and Mertens infrastructure. Step 7 is a signature-translation exercise.

## Suggested handoff prompt for Codex / Aristotle / Claude Code

> "Open `formalizations/694/`. Read `informal_proof.md` (faithful summary of the PDF) and `694.pdf` (the source). Write the formalization in `formalizations/694/Erdos694.lean`.
>
> Plan:
> 1. Axiomatize Linnik's theorem near the top, with a comment.
> 2. Prove Lemma 1.1 (Landau's max-ratio asymptotic) from Mathlib's Mertens + PNT.
> 3. Prove Theorem 2.1 upper bound from Lemma 1.1 + the fibre-finiteness inequality $\phi(m)^2 \ge m/2$.
> 4. Build the lower-bound construction $a_y, b_y, n_y$, verify $\phi(a_y) = \phi(b_y)$, and complete the lower bound.
> 5. Prove Proposition 3.1 separately (it's a 5-line argument).
> 6. Use the lean-lsp MCP tools after each meaningful change: `lean_diagnostic_messages`, `lean_local_search` for Mertens/PNT lemmas, `lean_leansearch`/`lean_loogle` for missing pieces. Run `lake build` only when needed.
>
> Don't blind-scaffold. Read the PDF first (it's in `formalizations/694/694.pdf`). Each lemma in your file should map to a labelled section of the PDF."
