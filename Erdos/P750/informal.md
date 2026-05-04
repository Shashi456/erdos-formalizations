# Erdős Problem 750 — Almost-half independent sets in graphs of infinite chromatic number

> Source: [Chojecki + GPT-5.5 Pro, *Local odd-cycle transversals in generalized Mycielski graphs and an Erdős problem on almost-half independent sets*](https://www.ulam.ai/research/erdos750.pdf), 3 May 2026.
> Forum: [erdosproblems.com/forum/thread/750](https://www.erdosproblems.com/forum/thread/750).

## Problem statement

**Erdős (1994).** Let `f : ℕ → ℝ≥0` satisfy `f(m) → ∞`. Does there exist a graph `G` of infinite chromatic number such that every finite subgraph `F ⊆ G` on `m` vertices has an independent set of size at least `m/2 - f(m)`?

The known linear-error version `(1−ε)·m/2` follows from Erdős–Hajnal–Szemerédi (1982); the open question is the *additive* regime where `f(m)` is allowed to grow arbitrarily slowly.

## Main theorem (positive answer)

The proof actually establishes a stronger statement in terms of the **odd-cycle transversal number**

```
oct(H) := min { |T| : T ⊆ V(H), H − T is bipartite }.
```

If `|V(H)| = m` and `oct(H) ≤ t`, then deleting `t` vertices leaves a bipartite graph on `≥ m − t` vertices, one of whose parts is independent and has size `≥ (m − t)/2`. Hence `α(H) ≥ (m − t)/2`.

**Theorem 1.1 (paper).** For every nondecreasing unbounded `g : ℕ → ℕ₀`, there exists a graph `G` with `χ(G) = ∞` such that every finite subgraph `F ⊆ G` satisfies `oct(F) ≤ g(|V(F)|)`.

**Corollary 1.2.** For `f : ℕ → ℝ≥0` with `f(m) → ∞`, the graph above (applied to a suitable integer minorant of `2f`) satisfies `α(F) ≥ m/2 − f(m)`.

## Construction: generalized Mycielski graphs

For a graph `H` and `s ≥ 1`, the **generalized Mycielski graph** `Mₛ(H)` has vertex set
```
V(Mₛ(H)) = { (i,v) : 0 ≤ i < s, v ∈ V(H) } ∪ {z}
```
with edges:
- `(0,u)(0,v)` for every edge `uv ∈ E(H)` (a copy of `H` at level 0);
- `(i,u)(i+1,v)` and `(i,v)(i+1,u)` for every edge `uv ∈ E(H)` and `0 ≤ i < s−1` (cross-level edges);
- `z ∼ (s−1,v)` for every `v ∈ V(H)` (the apex `z` is adjacent to all top-level vertices).

`M₂(H)` is the classical Mycielski graph. The recursive class is

```
M₂ = {K₂},   Mᵣ₊₁ = { Mₛ(H) : H ∈ Mᵣ, s ≥ 1 }.
```

**Theorem 2.3 (Stiebitz, used as a black box).** Every graph in `Mᵣ` has chromatic number exactly `r`.

The upper bound `χ(Mₛ(H)) ≤ χ(H) + 1` is elementary: extend any proper colouring of `H` to all levels and use one new colour for the apex. The lower bound (`χ ≥ r` *for recursively built graphs*) is the topological theorem of Stiebitz, which we admit as an axiom.

> **Important caveat from the paper:** `χ(Mₛ(H)) = χ(H) + 1` does **not** hold for every graph `H` and every `s ≥ 3`. The recursive hypothesis is essential.

## Key combinatorial lemmas

For `X ⊆ V(Mₛ(H))`, let `π(X) := { v ∈ V(H) : ∃ i, (i,v) ∈ X }` (the apex is ignored).

**Lemma 3.1 (Projection inequality).** For every `X ⊆ V(Mₛ(H))` with projection `P = π(X)`,
```
oct(Mₛ(H)[X]) ≤ s · oct(H[P]) + 1{z ∈ X}.
```

*Proof.* Let `T ⊆ P` be a transversal of `H[P]`. Delete `(i,v)` for every `v ∈ T` and every level `i`, plus `z` if `z ∈ X`. The number of deletions is `≤ s|T| + 1{z∈X}`. The remaining graph inherits a bipartition from `H[P \ T]` (colour `(i,v)` by the side of `v`); each cross-level edge connects opposite sides because `H[P \ T]` is bipartite.

**Lemma 3.2 (Odd cycles through the apex are long).** For every bipartite graph `B` and every `s ≥ 1`, every odd cycle of `Mₛ(B)` containing the apex `z` has length `≥ 2s + 1`.

*Proof.* `Mₛ(B) − z` is bipartite (use `B`'s bipartition on every level), so every odd cycle contains `z`. Such a cycle splits as `z − (s−1, u) − ⋯ − (s−1, w) − z`, where the middle path lies in `Mₛ(B) − z`. The path has odd length. Cross-level edges change the level by `±1`; the only level-preserving edges sit inside level 0. A path between two top-level vertices that uses no level-0 edge has even length, so an odd path must use a level-0 edge — meaning it descends `s−1` steps to level 0, takes at least one level-0 step, and ascends `s−1` back. Adding the two `z`-incident edges gives total length `≥ 2s + 1`. ∎

## Finite profile theorem (the engine)

**Theorem 4.1.** Let `g : ℕ → ℕ₀` be nondecreasing and unbounded. For every `r ≥ 2` there exists a graph `H ∈ Mᵣ` such that every nonempty induced subgraph `H[X]` satisfies `oct(H[X]) ≤ g(|X|)`.

*Proof by induction on `r`.* Base case `r = 2`: take `H = K₂`. Bipartite, so `oct(K₂[X]) = 0`.

Inductive step. Assume the result for `r`. Let `m₀ := max{m : g(m) = 0}` (with `m₀ = 0` if no such `m` exists). Choose `s ≥ 2` so that `2s + 1 > m₀`. Define

```
h(m) := max{0, ⌊(g(m) − 1)/s⌋}.
```

Then `h` is nondecreasing and unbounded. By the inductive hypothesis pick `G ∈ Mᵣ` with `oct(G[Y]) ≤ h(|Y|)` for every nonempty `Y`. Set `H := Mₛ(G)`; then `H ∈ Mᵣ₊₁` and `χ(H) = r + 1` by Stiebitz.

Take nonempty `X ⊆ V(H)`, `m = |X|`, `P = π(X)`. If `P = ∅` then `X ⊆ {z}` and `oct(H[X]) = 0 ≤ g(m)`. Else by Lemma 3.1 and monotonicity of `h`,
```
oct(H[X]) ≤ s·h(|P|) + 1{z∈X} ≤ s·h(m) + 1{z∈X}.
```

- If `g(m) ≥ 1`: `h(m) = ⌊(g(m)−1)/s⌋ ≤ (g(m)−1)/s`, so `s·h(m) + 1 ≤ g(m)`. ✓
- If `g(m) = 0`: then `m ≤ m₀ < 2s + 1` and `h(m) = 0`, so `h(|P|) = 0`, i.e. `G[P]` is bipartite. Hence `Mₛ(G[P]) − z` is bipartite. If `z ∉ X` we are done. If `z ∈ X`, an odd cycle in `H[X]` would be an apex-cycle, length `≥ 2s + 1 > m`, contradiction. ✓

## Infinite construction (Theorem 1.1)

Given `g : ℕ → ℕ₀` nondecreasing unbounded, define `gᵣ(m) := ⌊g(m) / 2ʳ⌋`. Each `gᵣ` is nondecreasing and unbounded. By Theorem 4.1 pick `Hᵣ ∈ Mᵣ` (so `χ(Hᵣ) = r`) with `oct(Hᵣ[X]) ≤ gᵣ(|X|)`. Let
```
G := ⨆_{r ≥ 2} Hᵣ      (disjoint union).
```
Then `χ(G) = ∞` because `χ(Hᵣ) = r → ∞`. For a finite subgraph `F ⊆ G` with `|V(F)| = m`, write `Xᵣ := V(F) ∩ V(Hᵣ)`. Odd-cycle transversals of disjoint unions are direct sums, so
```
oct(F) ≤ ∑_{r : Xᵣ ≠ ∅} oct(Hᵣ[Xᵣ]) ≤ ∑_r gᵣ(|Xᵣ|) ≤ ∑_{r ≥ 2} g(m)/2ʳ ≤ g(m).
```

## Cor 1.2 (independence number)

For `f ≥ 0` with `f → ∞`, define `g(m) := max(0, ⌊inf_{n ≥ m} 2 f(n)⌋)`. Then `g` is nondecreasing, unbounded, and `g(m) ≤ 2 f(m)`. Apply Theorem 1.1 to get `G`. For finite `F ⊆ G` with `|V(F)| = m`, `oct(F) ≤ g(m)`, so deleting `g(m)` vertices leaves a bipartite graph on `≥ m − g(m)` vertices; one part is independent and has size `≥ (m − g(m))/2 ≥ m/2 − f(m)`.

## Black-box dependency

Stiebitz's theorem on the chromatic number of recursively built generalized Mycielski graphs (`Mr ⇒ χ ≥ r`) is the only non-Mathlib ingredient; it sits alongside our P694 axioms (`mertens_product`, `linnik_dvd`) as a classical, unconditional result not yet in Mathlib. The corresponding axiom in `Proof.lean` is `Erdos750.stiebitz_lower_bound`.

## Differences from the LaTeX writeup (planned)

- **Vertex encoding.** The LaTeX uses `{0,…,s−1} × V(H) ∪ {z}`. Our Lean `Mₛ(H)` lives on `Sum (Fin s × V) Unit` with the apex tagged `Sum.inr ()`.
- **Membership in `Mᵣ`.** We do not encode `Mᵣ` as a class of graphs (that would force a heterogeneous existential over types). Instead we expose the recursive *witness* directly: `IsRecursivelyBuiltMr` is a predicate that the graph was assembled from `K₂` by iterated `Mₛ`-cones, and the Stiebitz axiom is stated against that predicate.
- **Disjoint union.** Mathlib's `SimpleGraph` lacks a primitive infinite disjoint union; we encode `⨆ Hᵣ` as a graph on the sigma type `(r : ℕ) × V(Hᵣ)` with edges drawn only within each component.
- **Cor 1.2 normalisation.** The `g` constructed from `f` matches the LaTeX up to floor placement.

The construction and bounds match character-for-character; no logical deviation.
