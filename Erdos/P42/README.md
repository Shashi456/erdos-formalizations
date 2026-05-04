# Erdős Problem 42 — Sidon difference avoidance

> [erdosproblems.com/42](https://www.erdosproblems.com/42)
>
> ⚠️ **In progress.** Three proof PDFs + forum-thread snapshot + informal outline + scaffold in place; the Lean proof is a placeholder. See [§ Current state](#current-state).

For every `M ≥ 1`, every sufficiently large `N`, and every non-empty Sidon set `A ⊆ {1, …, N}`, there is another Sidon set `B ⊆ {1, …, N}` of size `M` with

```
(A − A) ∩ (B − B) = {0}.
```

Erdős's #42, [`[Er95]`]. The April 2026 Fourier-compactness proof (Harjas / GPT-5.5 Pro, with subsequent ideas from Bloom, Sawin, Tao, and natso26's clean exposition) reduces the problem to a continuous compact-abelian-group lemma plus Green-Tao `U²` regularity / complexity-1 counting.

## Files

| File | What |
|------|------|
| [`Proof.lean`](Proof.lean) | Lean 4 / Mathlib formalization. Single `Erdos42` namespace, `import Mathlib`. |
| [`proof.pdf`](proof.pdf) | Harjas / GPT-5.5 Pro, *A Fourier-Compactness Proof of Erdős Problem 42*, corrected version, 27 April 2026. |
| [`proof_combined_42_43.pdf`](proof_combined_42_43.pdf) | Kevin Barreto, *Sidon Difference Avoidance*, 29 April 2026 — combines #42 + #43. |
| [`proof_ulam_note.pdf`](proof_ulam_note.pdf) | natso26 / Tao, *A Fourier-positive proof of Erdős Problem 42*, draft note, 30 April 2026 — the cleanest exposition; we follow this layout. |
| [`informal.md`](informal.md) | Human-readable proof outline matching `proof_ulam_note.pdf`. |
| [`forum_thread.md`](forum_thread.md) | Snapshot of the forum thread (relevant comments + links). |
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target — public theorems with `sorry` bodies. |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P42.Proof
```

**Online:** [live.lean-lang.org against Mathlib v4.27.0](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP42%2FProof.lean)

## Current state

Scaffold in place. Theorem statement wired to FC's [`erdos_42`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/42.lean) (matching the upstream `answer(sorry) ↔ …` shape under `answer := True`). Proof is `sorry` pending implementation:

| Theorem | Status |
|---|---|
| `complexity_one_counting_lemma` (axiom — Green-Tao 2008) | postulated |
| `compact_U2_regularity_subsequential_limit` (axiom — classical compactness packaging) | postulated |
| `tao_continuous_avoidance` (Layer 1, axiom-free) | `sorry` (provable in Mathlib) |
| `finite_avoidance_lemma` (Layer 2, depends on the two axioms) | `sorry` |
| Theorem 1.1 (Layer 3, the Erdős statement) | `sorry` |
| `erdos_42` (FC iff form) | `sorry` |

## Target trust boundary

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Extra axioms (target) |
|---|---|
| `tao_continuous_avoidance` (continuous-version key lemma) | (none — Mathlib Fourier on compact abelian groups) |
| `finite_avoidance_lemma` (one-sided avoidance), Theorem 1.1, `erdos_42` | `complexity_one_counting_lemma`, `compact_U2_regularity_subsequential_limit` |

Both axioms are classical, unconditional results from Green-Tao 2008 ("Linear equations in primes") and the standard compactness/regularity-lemma packaging.

## Comparison with Sedov's `M = 3` formalization

Daniil Sedov's [github.com/Gusarich/erdos42](https://github.com/Gusarich/erdos42) handles the **special case `M = 3`** via a sum-free 2/5-trichotomy axiom (Balogh-Liu-Sharifzadeh-Treglown, 2014). Our target is the **general `M`** case via the Fourier-compactness route.

The two approaches are independent — Sedov's axiom is a finite Ramsey/sum-free statement; ours is Green-Tao analytic. There's no direct sharing of code or lemmas, but Sedov's `IsSidon` API and `(A − A) ∩ (B − B) ⊆ {0}` lemmas may be re-usable.

## Alignment with the informal proof

[`proof_ulam_note.pdf`](proof_ulam_note.pdf) is the canonical reference; we audit `Proof.lean` against it section-by-section.

Notable encoding choices:
* **Sidon sets** use Mathlib's `IsSidon` (or the FC skeleton's `IsMaximalSidonSetIn` + `IsSidon`, whichever lands cleanest).
* **Fourier transform on `𝔽_p`** uses `ZMod p` + Mathlib's `AddChar` / `Real.fourierIntegral` infrastructure where applicable.
* **Compact abelian groups** in Layer 1 use Mathlib's `CompactAddCommGroup` + `Pontryagin` API.
* **The "almost every" in Layer 1** is `MeasureTheory.AEStrongly` over Haar measure.

## Relationship to `formal-conjectures`

Upstream
[`FormalConjectures/ErdosProblems/42.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/42.lean)
states `erdos_42 : answer(sorry) ↔ ∀ M ≥ 1, ∀ᶠ N in atTop, ∀ A …`. We discharge this under `answer := True`.

The FC file also provides `IsMaximalSidonSetIn`, `IsSidon`, and basic worked examples (`{1, 2, 4}` is maximal Sidon in `[4]`, etc.) which we will reuse where applicable.
