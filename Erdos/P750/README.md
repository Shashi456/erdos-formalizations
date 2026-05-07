# Erdős Problem 750 — Almost-half independent sets

> [erdosproblems.com/750](https://www.erdosproblems.com/750)

For every `f : ℕ → ℝ≥0` with `f(m) → ∞`, there is a graph `G` of infinite
chromatic number such that every finite subgraph `F ⊆ G` on `m` vertices
has an independent set of size at least `m/2 − f(m)`.

The Lean proof in fact establishes the stronger **odd-cycle-transversal**
form (Chojecki + GPT-5.5 Pro, May 2026): for every nondecreasing unbounded
`g : ℕ → ℕ₀` there is `G` with `χ(G) = ∞` and `oct(F) ≤ g(|V(F)|)` for
every finite `F ⊆ G`. The independence-number statement is an immediate
corollary.

## Files

| File | What |
|------|------|
| [`Proof.lean`](Proof.lean) | Lean 4 / Mathlib formalization for **Mathlib v4.27.0** (the toolchain pinned in `lean-toolchain`). Single `Erdos750` namespace, `import Mathlib`, ~2000 lines. |
| [`Proof_v4.28.lean`](Proof_v4.28.lean) | **Mathlib v4.28+ port** of `Proof.lean`, with the few API-drift fixes (`Std.Irrefl`, explicit-vertex `Walk.rotate`, etc.). Same proof, same trust boundary. Use this against `live.lean-lang.org`'s newer-Mathlib projects. |
| [`compact_cayley_proof.pdf`](compact_cayley_proof.pdf) | Chojecki + GPT-5.5 Pro, *Local odd-cycle transversals in generalized Mycielski graphs and an Erdős problem on almost-half independent sets*, 3 May 2026. |
| [`proof_outline.md`](proof_outline.md) | Human-readable proof outline / strategy notes. |
| [`safeverify/Spec.lean`](safeverify/Spec.lean) | SafeVerify target — the public theorems with `sorry` bodies. |

## How to verify

**Locally (with Lake):**
```
lake build Erdos.P750.Proof
```

**Online (no Lake required):** two flavours, depending on which Mathlib version
your live target supports:

- v4.27.0 (matching our `lean-toolchain`): [load `Proof.lean`](https://live.lean-lang.org/#project=mathlib-v4.27.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP750%2FProof.lean)
- v4.28.0+: [load `Proof_v4.28.lean`](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FShashi456%2Ferdos-formalizations%2Frefs%2Fheads%2Fmain%2FErdos%2FP750%2FProof_v4.28.lean)

## Trust boundary

Beyond Mathlib core (`propext`, `Classical.choice`, `Quot.sound`):

| Theorem | Extra axioms |
|---|---|
| `genMyc_chromaticNumber_le_succ`, `genMyc_colorable_succ`, `genMyc_minus_apex_isBipartite`, `genMycMinusZero_isBipartite` | none |
| `oct_mono_edges` (edge-monotonicity wrapper) | none |
| `oct_genMyc_le` (Lemma 3.1, projection inequality) | none |
| `genMyc_oddClosedWalk_through_apex_long`, `genMyc_oddCycle_through_apex_long` (Lemma 3.2, apex cycles) | none |
| `finite_nonbipartite_induce_has_short_odd_cycle` (graph-theory bridge) | none |
| `finite_oct_profile` (Theorem 4.1, finite OCT profile — axiom-free version) | none |
| `finite_oct_profile_with_chromatic` (Theorem 4.1, with `χ(G) = r`) | `stiebitz_lower_bound` |
| `infinite_chromatic_local_oct` (Theorem 1.1, infinite construction) | `stiebitz_lower_bound` |
| `erdos_750_independence` (Cor 1.2, real-valued form) | `stiebitz_lower_bound` |
| `erdos_750_independence_FC_form` (Cor 1.2, NNReal-truncated form, matches `formal-conjectures` syntax) | `stiebitz_lower_bound` |

`stiebitz_lower_bound` is Stiebitz's theorem (1985 thesis): the chromatic
number of any recursively-built generalized Mycielski graph in `Mᵣ` is
at least `r`. It is classical and unconditional; its proof goes through
the topological method of Lovász. Mathlib has surrounding combinatorics
infrastructure but not this named result, so we postulate it as the
sole non-Mathlib-core dependency.

The local OCT combinatorics — Lemmas 3.1, 3.2, and the finite profile
theorem in its current shape — are **entirely axiom-free** beyond
Mathlib core. Stiebitz is only invoked at the very last step, where
we conclude `χ(G) = ⊤` for the infinite disjoint union, which needs
the chromatic-number lower bound `(r : ℕ∞) ≤ G.chromaticNumber`.

The audit block at the bottom of [`Proof.lean`](Proof.lean) (`#print axioms …`)
reproduces this trust-boundary table at build time.

## Verifying with SafeVerify

[SafeVerify](https://github.com/GasStationManager/SafeVerify) replays each
declaration through the kernel via `Environment.replay`, enforces a hard
axiom allow-list, and bans `partial` / `unsafe` constants.

Our proof depends on one named axiom beyond `{propext, Quot.sound,
Classical.choice}` — `Erdos750.stiebitz_lower_bound`. SafeVerify's default
allow-list needs to be extended with this name; the extension is local to
this problem.

**Reproduction** (assumes a clone of SafeVerify pinned to
`leanprover/lean4:v4.27.0` — the same toolchain this repo uses):

```bash
# 1. Build this repo so Erdos/P750/Proof.olean exists.
cd erdos-formalizations
lake exe cache get
lake build

# 2. Build the SafeVerify target spec to .olean.
lake env lean -o Erdos/P750/safeverify/Spec.olean Erdos/P750/safeverify/Spec.lean

# 3. In your SafeVerify clone, extend `allowedAxioms` (Main.lean:355)
#    with the axiom used by this proof:
#
#      allowedAxioms := #[`propext, `Quot.sound, `Classical.choice,
#        `Erdos750.stiebitz_lower_bound]
#
#    Then `lake exe cache get && lake build`.

# 4. Run the check.
cd /path/to/SafeVerify
lake exe safe_verify --verbose --disallow-partial \
  /path/to/erdos-formalizations/Erdos/P750/safeverify/Spec.olean \
  /path/to/erdos-formalizations/.lake/build/lib/lean/Erdos/P750/Proof.olean
```

Expected output ends with `SafeVerify check passed.`.

## Alignment with the informal proof

[`compact_cayley_proof.pdf`](compact_cayley_proof.pdf) is the Chojecki + GPT-5.5 Pro writeup the
formalization is based on. We split it into Sections 2–5 and audited
each independently against `Proof.lean`. **All sections are faithfully
aligned**, with the following deliberate, documented deviations:

* **Vertex encoding for `Mₛ(H)`.** The PDF uses `{0,…,s−1} × V(H) ∪ {z}`.
  Lean uses `Sum (Fin s × V) Unit` with the apex tagged `Sum.inr ()`.
* **Membership in `Mᵣ`.** We do not encode `Mᵣ` as a heterogeneous class
  of graphs; we expose the recursive witness as a predicate
  `IsRecursivelyBuiltMr`, and the Stiebitz axiom is stated against it.
  Same statement in the recursive-only regime, no deviation in scope.
* **Disjoint union.** Mathlib has no primitive infinite-indexed disjoint
  union of `SimpleGraph`s; we build `⨆ Hᵣ` on the global vertex type
  `ℕ × ℕ` (each `(r, ·)` slice indexes into `Hᵣ` via a `Fintype.equivFin`,
  with out-of-range indices isolated). This avoids dependent-sigma pain.
* **Cor 1.2 minorant.** The PDF uses a tail-infimum `inf_{n≥m} 2f(n)` then
  floors. Lean uses a threshold-based monotonised integer minorant
  (`Nat.findGreatest` over per-`k` thresholds where `(k : NNReal) ≤ f`),
  which avoids `iInf`/`floor`/NNReal-coercion overhead. The Lean minorant
  bounds `g ≤ f`, *strictly tighter* than the PDF's `g ≤ 2f`; the resulting
  independence bound `α(F) ≥ m/2 − f(m)` is identical (using `f ≥ 0`).
* **Subgraph vs induced subgraph.** The PDF's Theorem 1.1 quantifies over
  every finite *subgraph* `F ⊆ G`; we state the result for finite *induced*
  subgraphs `G[X]`. The induced form is logically stronger for the
  independence corollary (an independent set in `G[X]` is independent in
  every subgraph on `X`); for the literal subgraph form, the wrapper
  `oct_mono_edges` (proved) gives `oct H X ≤ oct G X` for any `H ≤ G`.
* **Cycle reduction.** The PDF says "every odd cycle in `H[X]` ..." and
  uses cycle length to bound `|X|`. Mathlib has the closed-walk parity
  characterization (`two_colorable_iff_forall_loop_even`) but not the
  cycle-reduction step, so we proved
  `finite_nonbipartite_induce_has_short_odd_cycle` from scratch via the
  splice argument (shortest odd closed walk has nodup support tail and
  hence is a cycle). This is a small piece of Mathlib-quality combinatorics
  that could be upstreamed.

## Relationship to `formal-conjectures`

Upstream
[`FormalConjectures/ErdosProblems/750.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/750.lean)
states `erdos_750` in the shape

```lean
answer(sorry) ↔ ∀ (f : ℕ → ℝ≥0) (hf : Tendsto f atTop atTop),
  ∃ V (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧ …
```

Our `Erdos750.erdos_750_independence` proves the right-hand side directly,
filling that conjecture under the `answer = True` reading.
