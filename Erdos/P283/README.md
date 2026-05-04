# Erdős Problems 283 + 351 — Polynomial Egyptian sums

> [erdosproblems.com/283](https://www.erdosproblems.com/283) ·
> [erdosproblems.com/351](https://www.erdosproblems.com/351)
>
> ⚠️ **In progress.** PDF + informal outline + scaffold in place; the Lean
> proofs of Theorem 1 and Corollary 7 are placeholders. See
> [§ Current state](#current-state).

The May 3 2026 proof (GPT-5.5 Pro, cleaned up by Liam Price; Kevin Barreto
noticed #351 follows) resolves both problems simultaneously.

**Erdős #283.** For every `p ∈ ℚ[x]` integer-valued on ℤ with positive leading
coefficient and no fixed divisor, every sufficiently large integer `m` is
expressible as `p(n_1) + ⋯ + p(n_k)` with distinct `n_i` satisfying
`1/n_1 + ⋯ + 1/n_k = 1`. The proof in fact holds for any rational `α > 0`
in place of `1` — this is **Theorem 1** in the PDF.

**Erdős #351.** For non-zero `p ∈ ℚ[x]` with positive leading coefficient,
the set `{ p(n) + 1/n : n ∈ ℕ }` is strongly complete. **Corollary 7** in
the PDF.

The proof combines the **Roth-Szekeres-Graham theorem** on complete
polynomial sequences with reciprocal-preserving switches (the identity
`1/x = 1/(2x) + 1/(3x) + 1/(6x)`) and a finite congruence correction.

## Files

| File | What |
|------|------|
| [`Proof.lean`](Proof.lean) | Lean 4 / Mathlib formalization. Single `Erdos283` namespace, `import Mathlib`. |
| [`proof.pdf`](proof.pdf) | GPT-5.5 Pro + Liam Price, *Polynomial Egyptian Sums*, 3 May 2026. |
| [`informal.md`](informal.md) | Human-readable proof outline matching the PDF section-by-section. |
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target — public theorems with `sorry` bodies. |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P283.Proof
```

**Online (no Lake required):** open in
[live.lean-lang.org against Mathlib v4.27.0](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP283%2FProof.lean).

## Current state

Scaffold in place. Theorem statements wired to FC's
[`erdos_283`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/283.lean)
and
[`erdos_351`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/351.lean)
(matching the upstream `answer(sorry) ↔ …` shape). Proofs are `sorry`
placeholders pending implementation:

| Theorem | Status |
|---|---|
| `roth_szekeres_graham` (axiom — Graham 1964 / Roth-Szekeres 1954) | postulated |
| Lemma 3 (Egyptian expansions, axiom-free) | `sorry` |
| Lemma 4 (Egyptian patterns mod M, axiom-free) | `sorry` |
| Lemma 5 (polynomial periodicity, axiom-free) | `sorry` |
| Lemma 6 (gcd 1 from finitely many switches, axiom-free) | `sorry` |
| Theorem 1 (main, depends on `roth_szekeres_graham`) | `sorry` |
| Corollary 7 (Erdős #351, depends on Theorem 1) | `sorry` |
| `erdos_283` (FC iff form) | `sorry` |
| `erdos_351` (FC iff form) | `sorry` |

## Target trust boundary

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Extra axioms (target) |
|---|---|
| Lemmas 3-6 | (none — Egyptian-fraction combinatorics) |
| Theorem 1 (main), Corollary 7, `erdos_283`, `erdos_351` | `roth_szekeres_graham` |

`roth_szekeres_graham` is Graham's complete-polynomial-values theorem
(*Duke Math. J.* 1964), with Roth-Szekeres (*Quart. J. Math.* 1954) as
the asymptotic input. Both are classical and unconditional; Mathlib has
surrounding analytic-number-theory infrastructure but not this named
result.

## Alignment with the informal proof

[`proof.pdf`](proof.pdf) is the GPT-5.5 Pro / Liam Price PDF the
formalization is based on. We split it into the §1 Egyptian switches
(four lemmas), §2 main proof, and Corollary 7 derivation; each section
will be audited independently against `Proof.lean`.

Notable encoding choices:
* **Polynomials** use `Polynomial ℚ` (we cast to `Polynomial ℤ` where
  the integer-valued / fixed-divisor predicates apply).
* **Egyptian patterns** are `Finset ℕ` with the predicate
  `∀ e ∈ E, e ≥ 2 ∧ ∑_{e ∈ E} (1 : ℚ) / e = 1`.
* **Collision avoidance** uses `Nat.padicValNat 2` and `Nat.padicValNat 3`
  for the `(v_2, v_3)` argument.
* **The `Fin (k+1) → ℤ` indexing** in FC's `Erdos283.Condition` is
  preserved; an internal `Finset ℤ` form is bridged at the end.

## Relationship to `formal-conjectures`

* Upstream
  [`FormalConjectures/ErdosProblems/283.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/283.lean)
  states `erdos_283 : answer(sorry) ↔ ∀ p : ℤ[X], Condition p`. We discharge
  this under `answer := True`.
* Upstream
  [`FormalConjectures/ErdosProblems/351.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/351.lean)
  states `erdos_351 : answer(sorry) ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff → HasCompleteImage P`.
  We discharge this under `answer := True`.
