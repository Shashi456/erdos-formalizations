# Erdős Problem 202

Sharp asymptotic for the maximum size of a family of pairwise-disjoint
arithmetic-progression residue classes with distinct moduli `≤ N`.

> Given `n_1 < ⋯ < n_r ≤ N` and residues `a_i mod n_i` chosen so that every
> integer lies in at most one class, how large can `r` be?

The May 2026 PDF (`docs/erdos202.pdf`) proves the BFV-conjectured asymptotic
`f(N) = N · exp(-(1 + o(1)) · sqrt(log N · log log N))`. The single new
ingredient is a **spread-core lemma** replacing the Erdős–Lovász /
minimal-family loss inside the BFV descending chain, derived from Park–Pham
(Kahn–Kalai expectation-threshold; arXiv:2203.17207).

The problem page on `erdosproblems.com` currently says "Formalised
statement? No"; an immediate goal of this scaffold is the formal statement
itself, suitable for a `formal-conjectures` upstream PR.

## Status

**Conditionally formalized end-to-end.** The
statement layer, arithmetic API, dense-core corollary, initial chain state,
nondegenerate chain-state invariants, remaining-support chain API, the
dense-core setup inside the chain (including nonempty core-survivor
extraction), finite weighted/residue pigeonhole lemmas, exact-block
chain-extension constructor, the `2^|C|` exact-block weight-sum estimate,
the cumulative survivor lower-bound invariant and its preservation across a
structural step, the newest-first `chainT` update law for telescoping,
the basic and quadratic `chainT` bounds for positive selected blocks,
structural terminal-chain existence from the initial state,
conditional quantitative product telescoping from an invariant-threaded
per-step product estimate, the selected-block estimate, and the public
loss-aware `chain_inequality`, the logarithmic optimization absorbing the
explicit lower-order losses, and the final pruning-to-upper-bound step now
have proof bodies. `Erdos.P202.P202Main` builds. The BFV theorem path and the
finite spread-disjointness bookkeeping are discharged; the only remaining
project-level axiom in the public theorem is the Park--Pham/Kahn--Kalai
expectation-threshold package
`Erdos202.ParkPham.park_pham_threshold_not_small_lt_exists`.

Current submitted-code proof gaps:

| Declaration / file | Role |
|---|---|---|
| none | All non-SafeVerify submitted-code declarations build without `sorry`, `admit`, or `unsafe`. |

`safeverify/Spec.lean` deliberately contains `sorry` placeholders because it
is the target interface for SafeVerify, not the submitted proof.

## Layout (`Erdos.P202.*`)

| File | Purpose |
|------|---------|
| `P202Basic.lean` | Residue classes, admissibility, residue-assignment restriction, `f(N)` and its extremal API, `Zscale`, `Lscale`, `Mscale`, elementary and exact large-`N` scale lemmas, `HasErdos202Asymptotic`, `Erdos202Statement`, gcd intersection criterion. |
| `P202Arithmetic.lean` | `primeSupport`, `omega`, `rad`, `hExp`, `exactBlock`, coprime support/`omega` product lemmas, pointwise exact-block factorization, elementary `hExp` weight bounds, quotient support arithmetic, gcd-vs-remainder support lemmas, `remainingSupport`, all over `Nat.factorization`. |
| `SpreadCore.lean` | `UniformFamily`, `SpreadFamily`, `PairwiseDisjointMembers`, `spread_disjointness_input` as a theorem alias to the proved Park–Pham spread-disjointness layer, `dense_core_from_spread`. |
| `BFVInputs.lean` | `PrunedData N` with nonempty/positive-`K` and residue-disjointness invariants plus `PossibleCard`/`f` bridges, theorem aliases `bfv_omega_count_input` and `bfv_lower_bound_input`. |
| `BFV/` | Proved BFV omega-count, lower-bound, hExp-rarity, radical-multiplicity, filtering, and pruning modules, including `bfv_pruning_theorem`. |
| `ParkPham/` | Finite Boolean-family, product-measure, smallness, finite cover-cost, fragment/minimal-fragment, fragment-cost, deterministic fragment-iteration, random-partition, and spread-disjointness layers. The remaining deep theorem is isolated as `ParkPham.park_pham_threshold_not_small_lt_exists`. |
| `P202Chain.lean` | `ChainState` with nonempty-survivor/positive-product invariants, finite weighted/residue pigeonhole lemmas, remaining-support uniformity/intersection/dense-core lemmas with nonempty core-survivor extraction, exact-block selection and state-extension lemmas, selected-block size/`hExp` bounds, the `2^|C|` exact-block weight-sum estimate, fixed dense-core constant, cumulative survivor lower-bound invariant, stopping/initial-state lemmas, newest-first prefix-omega `chainT` with constructor update law and basic/quadratic bounds, proved `chain_step_structural` and `chain_step_structural_with_lowerBound` with explicit `W`-increase, structural terminal-chain existence from the initial state, conditional quantitative product telescoping, core-survivor and core-quotient cardinality bridges, `initialChainState`, loss-aware invariant-threaded `chain_step`, proved loss-aware `chain_inequality` (PDF Prop. 4.2 with explicit lower-order factors). |
| `P202Optimization.lean` | `sigmaN`, `card_le_of_sigma_lower`, `quad_bound` (proved), `sum_inv_sq_le_two`, `chain_T_bound`, logarithmic σ-bookkeeping for the loss-aware chain inequality, eventual `Mscale`, `sqrt(log log N)`, and `log Λ / log log N` growth estimates, proved `sigma_lower_bound`, and proved `f_upper_bound`. |
| `P202Main.lean` | `erdos202_upper_bound_from_inputs`, `erdos202_main`. |
| `safeverify/Spec.lean` | Draft SafeVerify target for the public statement, trust-boundary inputs, chain, optimization, and main theorem surfaces. |

## Trust Boundary

The current `#print axioms Erdos202.erdos202_main` audit reports exactly:

- Mathlib core: `propext`, `Classical.choice`, `Quot.sound`.
- Project-level theorem axiom:
  - `Erdos202.ParkPham.park_pham_threshold_not_small_lt_exists` —
    Park–Pham/Kahn–Kalai expectation-threshold theorem in finite
    non-smallness form.

The BFV inputs and spread-disjointness wrapper are theorem paths, not live
trust-boundary axioms. There are no proof-body `sorry`, `admit`, or `unsafe`
uses in submitted-code modules. `safeverify/Spec.lean` remains a separate
specification surface and deliberately contains placeholder `sorry`s.

## Three deliverables

The staging is designed to ship value early:

1. **Statement-only deliverable.** `Basic.Erdos202Statement` plus the
   gcd intersection criterion. Already enough to flip "Formalised
   statement? No" on the problem page and to submit a `formal-conjectures`
   upstream PR.
2. **Conditional theorem deliverable.** `erdos202_upper_bound_from_inputs`
   — the new spread-core + descending-chain argument. This is the formal
   artifact that mechanically checks the *new contribution* of the May 2026
   proof; the BFV load has now been discharged and the Park–Pham load is
   isolated to one named theorem.
3. **Axiom-free deliverable.** Discharge each input one by one. Each is
   an independent project. At the current state, only the Park–Pham theorem
   remains.

## Detailed roadmap

### Stage 1 — Statement layer

Close the two foundational lemmas in `P202Basic.lean`:

- `residueClass_inter_nonempty_iff` — `(a mod q) ∩ (b mod r) ≠ ∅ ↔
  a ≡ b [ZMOD gcd q r]`. This is the formal version of equation (7) in
  the PDF and is non-coprime CRT (Bézout). Mathlib's coprime CRT for
  `ZMod (m*n)` does NOT cover this; that is precisely why we use
  `Int.ModEq` (notation `a ≡ b [ZMOD n]`) rather than `ZMod`.
- `residueClass_disjoint_iff` — falls out of the previous lemma plus
  set disjointness.

These two lemmas drive the entire chain construction (the "remaining
supports must form an intersecting family" step uses them).

### Stage 2 — Arithmetic API

Close `P202Arithmetic.lean` lemmas. All reduce to `Nat.factorization` API.
Conceptually easy, proof-engineering heavy because mathlib's
multiplicity-related APIs (`primeFactorsList.count`, `padicValNat`,
`multiplicity`, `Nat.factorization`) are not fully unified — pick
`Nat.factorization` and stay there.

- `exactBlock_dvd`, `primeSupport_exactBlock`, `omega_exactBlock`,
  `hExp_exactBlock_le_hExp`.
- A small helper library will likely be needed: `card_filter_cast_le`,
  `nat_prod_cast`, `exp_loglog_pow`, `Lscale_mul`, `Lscale_mono_in_alpha`.
  Keep these local and small rather than fighting the main theorem in
  one giant file.

### Stage 3 — Spread → dense core

`SpreadCore.dense_core_from_spread` is closed from
`spread_disjointness_input`, which is now a theorem alias to the proved
finite spread-disjointness layer in `ParkPham/SpreadDisjointness.lean`.
The remaining deep dependency is not this dense-core counting argument; it is
the Park–Pham/Kahn–Kalai expectation-threshold theorem used upstream inside
the spread-disjointness layer.

### Stage 4 — Chain inequality

The chain inequality is the **best first serious proof target**. It is
the mathematical heart of the new contribution and is much more
Lean-friendly than BFV's analytic estimates or Park–Pham itself. Order:

1. `chain_step` (PDF Lemma 4.1) — at stage `r`, under the local
   fixed-`N` instance of the proved `bfv_omega_count_input` theorem alias:
   - remaining supports `A(q) = primeSupport (q / P_{≤r-1})` form an
     intersecting family of size `K - W_{r-1}` (by the gcd criterion);
   - dense-core lemma extracts a heavy core `C_r`;
   - weighted pigeonhole on exact prime-power blocks fixes `P_r`;
   - residue pigeonhole modulo `P_r` keeps `Q'` large.
2. `chain_inequality` (PDF Proposition 4.2) — proved by telescoping the
   invariant-threaded per-step product estimate under the same local fixed-`N`
   BFV count hypothesis. The structural terminal chain is proved independently
   of BFV counts.

Engineering note: the structural selection part of `chain_step` is proved,
including `W`-increase, the fixed dense-core constant, the
`2^|C|` weight-sum estimate, and preservation of the cumulative
survivor-size invariant (PDF inequality (12), with the `h(P_{≤r})²` and
`Λ^{W_r}` losses). The selected residue subfamily is now exposed through
the structural APIs as a subset of the selected exact-block fiber, with the
corresponding cardinality upper bound, and the pre-residue weighted share is
also exposed. The selected exact-block fiber now has proved lower and upper
BFV-count comparisons inside `chain_step_selected_block_bound`, yielding the
paper's selected-block inequality with the explicit lower-order factors
`h(P_{≤r})^2`, `Λ^{W_r}`, and the extra `(log N)^{|C_r|/2}`. The positive-block
predicate is threaded through `chain_inequality`, giving the optimization
layer proved quadratic bounds for both `chainT` and `chainT + W`; `hExp`
monotonicity under divisibility and the chain-state `hExp(productP)` bound
are also in place. The public invariant-threaded `chain_step`, loss-aware
`chain_inequality`, and optimization absorption of those explicit lower-order
factors are all proved.

Engineering note: blocks are stored as a `List ℕ` rather than `Fin R → ℕ`
to avoid dependent-index pain when `R` is determined dynamically.

### Stage 5 — Final optimization (no informal `o(1)`)

Close `P202Optimization.lean`. Key explicit replacements vs. the PDF:

- **Replace `π²/6` by `2`.** The proof only needs an absolute constant
  in the block-pigeonhole loss, so `∑_{ν=1}^m 1/ν² ≤ 2` (telescoping,
  `1/ν² ≤ 1/((ν-1)ν) = 1/(ν-1) - 1/ν` for `ν ≥ 2`) suffices. This
  removes a Basel dependency — `sum_inv_sq_le_two` does the work.
- **Exact `T`-bound.** Replace the PDF's `T = RK − R²/2 + O(R)` by the
  finite `T ≤ RK − R(R−1)/2` (the maximum of `∑ (R−j+1) w_j` subject to
  `w_j ≥ 1`, `∑ w_j = K` is at the all-excess-on-`w_1` corner).
  `chain_T_bound` does the work.
- **σ-bookkeeping.** Define `sigmaN N Qcard = log(N / Qcard) / Z(N)`.
  The optimization now formally takes logs of the chain inequality, uses
  `M(N)Z(N)=log N` and `Z(N)/M(N)=log log N`, cancels the quadratic `T`
  contribution, and reaches
  `1 − (2/M + 3/(4M) + 3ε) ≤ sigmaN²`; eventual largeness of `M(N)`
  now makes this explicit error at most `η`, closing `sigma_lower_bound`.
- **Lower-order terms.** `R · sqrt(log N) = o(log N)` and
  `T · log Λ = o(log N)` with `Λ = C log(eK)`, `K ≤ 3 M(N)` — small
  custom log/sqrt asymptotic library on top of
  `Mathlib.Analysis.Asymptotics.SpecificAsymptotics`.
- **Crucially: no informal `o(1)`.** Every BFV input is quantified with
  an explicit `ε` ("for every `ε > 0`, eventually …"). The chain
  multiplies `O(M)`-many `L(o(1), N)` factors so this uniformity is
  not optional.

### Stage 6 — Discharge the Remaining Axiom

The BFV inputs are already discharged in `BFV/`, and
`spread_disjointness_input` is a theorem alias to the proved finite
spread-disjointness layer. The only remaining project-level axiom is:

- `ParkPham.park_pham_threshold_not_small_lt_exists` — Park–Pham
  (Kahn–Kalai expectation threshold), in the finite non-smallness form used by
  this project.

The surrounding finite Boolean-family, product-measure, p-smallness,
q-smallness, finite cover-cost, fragment/minimal-fragment, fragment-cost,
random-partition, density-monotonicity, and reduced-core bridge layers are
already formalized.
A local search of Mathlib v4.27.0 found no packaged Kahn–Kalai/Park–Pham
expectation-threshold theorem to import.

### Stage 7 — Audit

`#print axioms Erdos202.erdos202_main` should report only
`propext`, `Classical.choice`, and `Quot.sound`. Until the Park–Pham theorem
is proved, the audit also reports
`Erdos202.ParkPham.park_pham_threshold_not_small_lt_exists`.

## Design choices and rationale

These mirror the strategy doc; record them so future contributors know
what was deliberate.

- **Naturals, not reals.** The PDF uses `x ≥ 1`; Erdős' page uses `N` and
  `n_i ≤ N`. The Lean statement is over `N : ℕ`. A real-`x` version is
  recoverable via `⌊x⌋` if ever needed; doing it the other way around
  buys nothing and costs floor/cast headaches.
- **`Int.ModEq`, not `ZMod`.** The proof's central criterion is
  `(a mod q) ∩ (b mod r) ≠ ∅ ↔ a ≡ b [ZMOD gcd q r]`. `ZMod`'s coprime
  CRT does not cover this. `Int.ModEq` (`a ≡ b [ZMOD n]`) is the smoother
  primitive; coprime CRT is recovered as a special case.
- **ε-form, not `L(o(1), N)`.** The `o(1)` shorthand on paper would
  silently demand uniformity that informal prose can hide but Lean
  cannot. Every input is `∀ ε > 0, ∀ᶠ N, …`.
- **`Real.exp` over `Real.rpow`.** `(log N)^{W/2}` is written as
  `exp((W/2) · log log N)` everywhere to avoid `Real.rpow` overhead.
- **Project-local `omega`, `rad`, `hExp`.** Defined on top of
  `Nat.factorization` to avoid drift between mathlib's multiplicity
  APIs (`primeFactorsList.count`, `padicValNat`, `multiplicity`).
- **List-based chains, not `Fin R → ℕ`.** Subfamilies and partial
  products of the chain cause coercion pain with `Fin`-indexed
  collections. Lists with a `length = r` invariant are easier.
- **`f` defined classically.** `Nat.findGreatest` needs
  `DecidablePred`; rather than carry a decidability instance the whole
  way, we use `by classical; exact …`.

## Mathlib friction points (the seven that will bite)

1. **BFV `o(1)` uniformity.** Already addressed by the ε-form discipline.
2. **Park–Pham is a multi-week independent target.** Treat its finite
   consequence as an axiom for now; do not gate the conditional
   deliverable on its formalization.
3. **Non-coprime gcd criterion.** Small but central; not in mathlib.
4. **Factorization API discipline.** Use `Nat.factorization` everywhere
   and a project-local `omega`/`rad`/`hExp`/`exactBlock` layer.
5. **BFV counting.** Specialized; not a drop-in mathlib theorem.
6. **Dependent finite families.** `ResidueAssignment Q := {q // q ∈ Q} → ℤ`
   is mathematically clean but causes restriction-to-subfamily coercion
   issues. Plan helper functions for those restrictions.
7. **Real / nat coercions.** Almost every inequality compares a natural
   cardinality to a real exponential. A small library of cast lemmas
   (`card_filter_cast_le`, `nat_prod_cast`, `exp_loglog_pow`,
   `Lscale_mul`, `Lscale_mono_in_alpha`) pays for itself.

## Optional follow-on: Problem 1190

The PDF also derives the asymptotic for `ε_m` (Problem 1190) by partial
summation and the integral estimate
`∫_m^∞ dt/(t · L(β, t)) ≍ L(-β + o(1), m)`. **Not** in this scaffold —
introduces `sSup` over reciprocal sums, partial summation, and improper
integrals. A natural follow-on module once 202 is fully axiom-free.

## Operating notes (for an autonomous formalization loop)

These are pitfalls and habits learned from the other P-formalizations in
this repo (P42, P283, P694, P750). Read them before iterating.

### Priority order — do not skip

1. **Stage 1 (statement layer) ships first.** Close
   `residueClass_inter_nonempty_iff` and the disjointness companion.
   Then commit and stop. That alone flips "Formalised statement? No"
   on the problem page and is shippable on its own.
2. **Stage 2–5 (conditional theorem) has shipped.** The descending chain,
   optimization, BFV pruning, BFV lower bound, BFV omega count, and finite
   spread-disjointness layers build through `Erdos.P202.P202Main`.
3. **Stage 6 is now the live target.** Do not spend another pass on BFV
   bookkeeping as if it were still a trust-boundary blocker. The remaining
   formalization work is the Park–Pham/Kahn–Kalai expectation-threshold
   theorem isolated in `ParkPham/Threshold.lean`.

### Trust boundary discipline

- `ParkPham.park_pham_threshold_not_small_lt_exists` is the only remaining
  project-level trust-boundary axiom. **Do not introduce new axioms.** If a
  sub-proof seems to need one, the right move is to add a theorem-shaped
  finite reduction around the existing Park–Pham target, not to widen the
  trust boundary.
- After every non-trivial milestone, run `#print axioms` on the
  affected theorem and verify the list still matches the target. Catch
  axiom leakage early; the alternative is a 14k-line bundle that
  silently depends on the wrong thing.
- `sorry`, `admit`, `unsafe`: never. The only accepted project-level axiom is
  the existing Park–Pham theorem package; do not add replacement axioms for
  local proof obligations.

### Mathlib / toolchain

- Pinned to Lean / Mathlib `v4.27.0` (see `lakefile.toml`). **Do not
  bump.** The other problems in this repo have been verified at
  specific tags and the live links assume them.
- Run `lake exe cache get` only at the start of a fresh checkout with no
  usable `.lake` cache. Do not re-fetch the cache in this working tree unless
  the cache has actually been removed.
- `autoImplicit = false` is set. Expect "Unknown identifier" errors
  from missing explicit binders; introduce the variable properly
  rather than papering over with `_`.

### Sorry hygiene

- `sorry` count in submitted-code modules should stay at zero. If a step
  introduces a new `sorry`, it has regressed the current state.
- The current source scan should find no proof-body `sorry`, `admit`, or
  `unsafe` in submitted-code modules. The remaining blocker appears as the
  single axiom declaration in `ParkPham/Threshold.lean`, not as a `sorry`.

### Build loop

- Build per-file: `lake build Erdos.P202.P202Basic`,
  `lake build Erdos.P202.P202Arithmetic`, etc. Do **not**
  `lake build` the whole project after every edit; it will recompile
  too much.
- After all P202 files build, do one final
  `lake build Erdos.P202.P202Main` to confirm end-to-end, then run
  `#print axioms Erdos202.erdos202_main`.

### Common failure modes

- **`Real.rpow` confusion.** `(log N) ^ (W/2)` over reals will get
  parsed as `Monoid.npow`. Always write `Real.exp ((W/2) * Real.log (Real.log N))`.
  This is hard-coded into the axiom statements for exactly this reason.
- **`∀ᶠ N in atTop, …` defaulting to ℝ.** If `N` is not annotated
  `(N : ℕ)`, Lean infers from `Lscale (-(1+ε)) N` (which expects ℕ)
  but resolves the `Filter` first and gets ℝ. Always write
  `∀ᶠ N : ℕ in atTop, …`.
- **`Nat.findGreatest` decidability.** Wrap with `by classical; exact
  …` or `open Classical in`. Already done in `Basic.f`; mirror that
  pattern if `findGreatest` shows up elsewhere.
- **Subfamily coercions.** `ResidueAssignment Q : {q // q ∈ Q} → ℤ`
  does not restrict to `Q' ⊆ Q` automatically. Add a
  `restrictAssignment : ResidueAssignment Q → Q' ⊆ Q →
  ResidueAssignment Q'` helper to `P202Basic.lean` the moment the chain
  needs it; do not inline it five times.
- **Cast-lemma proliferation.** Build a small helper library
  (`card_filter_cast_le`, `nat_prod_cast`, `exp_loglog_pow`,
  `Lscale_mul`, `Lscale_mono_in_alpha`) in a single file —
  `Erdos/P202/Casts.lean` is a fine name — instead of inlining 50 copies
  of `exact_mod_cast` and `push_cast`.
- **`omega` failing on `Fin`-indexed list `.get`.** Switch to
  `List.Pairwise` or `List.get?` rather than fighting `Fin` index
  arithmetic. The current `ChainState.pairwise_coprime` already uses
  `List.Pairwise` for this reason.

### What "done" looks like

- All submitted-code `sorry`s remain closed, and
  `ParkPham.park_pham_threshold_not_small_lt_exists` is replaced by a theorem.
- `#print axioms Erdos202.erdos202_main` reports exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build Erdos.P202.P202Main` passes from a clean checkout with a
  populated `.lake` cache.
- A `Proof.lean` flat bundle (single-file, `import Mathlib`, no
  project-local imports) is generated and verified on
  `live.lean-lang.org`. Mirror the layout used in
  `Erdos/P42/CompactCayley/Proof.lean` and
  `Erdos/P283/Proof_flat.lean`.
- Keep `safeverify/Spec.lean` aligned with the public theorem surfaces. It is
  a specification artifact and may contain placeholder `sorry`s by design.
- Update the top-level `README.md` table and trust-boundary section
  with a P202 row.
- Update `BACKLOG.md` to move "Erdős #202" out of the active section
  if it lands there during the loop.

### What NOT to do in the loop

- **Don't widen the trust boundary.** The remaining axiom is the Park–Pham
  theorem package. Downstream proofs are already written through theorem
  aliases for BFV and spread-disjointness.
- **Don't add features.** No new theorems beyond the seven in `P202Main.lean`
  and the lemma chain that supports them. No "while I'm here" cleanups.
- **Don't restart BFV closure.** BFV is clean in the current axiom audit. The
  live work is Park–Pham itself or finite reductions around its exact theorem
  surface.
- **Don't formalize Problem 1190.** Listed as a follow-on; not in scope.
- **Don't push to remote on every iteration.** Commit, but only push
  on shippable milestones (Stage 1 done, Stage 5 done, axiom
  discharged).

## References

- Erdős Problems #202: <https://www.erdosproblems.com/202>
  / forum thread: <https://www.erdosproblems.com/forum/thread/202>
- BFV: de la Bretèche–Ford–Vandehey, *On non-intersecting arithmetic
  progressions*, Acta Arithmetica 157(4), 381–392 (<https://eudml.org/doc/278905>).
- Park–Pham, *A proof of the Kahn–Kalai conjecture*, arXiv:2203.17207.
- `formal-conjectures` upstream: <https://github.com/google-deepmind/formal-conjectures>
  (target for a statement-only PR mirroring `Basic.Erdos202Statement`).
- May 2026 spread-core proof: `docs/erdos202.pdf` (this directory).
