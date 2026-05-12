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
have proof bodies. `Erdos.P202.P202Main` builds. Trust boundary is fixed at four
theorem-shaped axioms in `SpreadCore.lean` / `BFVInputs.lean`.

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
| `SpreadCore.lean` | `UniformFamily`, `SpreadFamily`, `PairwiseDisjointMembers`, `spread_disjointness_input` (axiom — Park–Pham consequence), `dense_core_from_spread`. |
| `BFVInputs.lean` | `PrunedData N` with nonempty/positive-`K` and residue-disjointness invariants plus `PossibleCard`/`f` bridges, `bfv_pruning_input`, `bfv_omega_count_input`, `bfv_lower_bound_input` (all axioms). |
| `P202Chain.lean` | `ChainState` with nonempty-survivor/positive-product invariants, finite weighted/residue pigeonhole lemmas, remaining-support uniformity/intersection/dense-core lemmas with nonempty core-survivor extraction, exact-block selection and state-extension lemmas, selected-block size/`hExp` bounds, the `2^|C|` exact-block weight-sum estimate, fixed dense-core constant, cumulative survivor lower-bound invariant, stopping/initial-state lemmas, newest-first prefix-omega `chainT` with constructor update law and basic/quadratic bounds, proved `chain_step_structural` and `chain_step_structural_with_lowerBound` with explicit `W`-increase, structural terminal-chain existence from the initial state, conditional quantitative product telescoping, core-survivor and core-quotient cardinality bridges, `initialChainState`, loss-aware invariant-threaded `chain_step`, proved loss-aware `chain_inequality` (PDF Prop. 4.2 with explicit lower-order factors). |
| `P202Optimization.lean` | `sigmaN`, `card_le_of_sigma_lower`, `quad_bound` (proved), `sum_inv_sq_le_two`, `chain_T_bound`, logarithmic σ-bookkeeping for the loss-aware chain inequality, eventual `Mscale`, `sqrt(log log N)`, and `log Λ / log log N` growth estimates, proved `sigma_lower_bound`, and proved `f_upper_bound`. |
| `P202Main.lean` | `erdos202_upper_bound_from_inputs`, `erdos202_main`. |
| `safeverify/Spec.lean` | Draft SafeVerify target for the public statement, trust-boundary inputs, chain, optimization, and main theorem surfaces. |

## Trust boundary (target)

The current `#print axioms Erdos202.erdos202_main` audit reports exactly:

- Mathlib core: `propext`, `Classical.choice`, `Quot.sound`.
- Project-level theorem axioms (named, published inputs):
  - `Erdos202.spread_disjointness_input` — Park–Pham finite consequence.
  - `Erdos202.bfv_pruning_input` — BFV pruning to `PrunedData N`.
  - `Erdos202.bfv_omega_count_input` — BFV ω-count uniform estimate.
  - `Erdos202.bfv_lower_bound_input` — BFV unconditional lower bound.

No other project-specific axioms; no `sorry`, `admit`, `unsafe` in the
submitted-code modules. `safeverify/Spec.lean` remains a separate draft spec
surface with placeholder `sorry`s.

## Three deliverables

The staging is designed to ship value early:

1. **Statement-only deliverable.** `Basic.Erdos202Statement` plus the
   gcd intersection criterion. Already enough to flip "Formalised
   statement? No" on the problem page and to submit a `formal-conjectures`
   upstream PR.
2. **Conditional theorem deliverable.** `erdos202_upper_bound_from_inputs`
   — the new spread-core + descending-chain argument compiled against the
   four axioms. This is the formal artifact that mechanically checks the
   *new contribution* of the May 2026 proof, with the Park–Pham and BFV
   load explicit and named.
3. **Axiom-free deliverable.** Discharge each input one by one. Each is
   an independent project (Park–Pham is its own multi-week target; BFV
   pruning / counting / lower bound is conventional analytic-number-theory
   formalization on top of mathlib's sieve and Chebyshev infrastructure).

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

Close `SpreadCore.dense_core_from_spread` from `spread_disjointness_input`.
This is PDF Corollary 2.2; conceptually a counting/averaging argument.
The full Park–Pham theorem is **not** required here — we only need the
finite combinatorial consequence.

### Stage 4 — Chain inequality

The chain inequality is the **best first serious proof target**. It is
the mathematical heart of the new contribution and is much more
Lean-friendly than BFV's analytic estimates or Park–Pham itself. Order:

1. `chain_step` (PDF Lemma 4.1) — at stage `r`, under the local
   fixed-`N` instance of `bfv_omega_count_input`:
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

### Stage 6 — Discharge axioms (independent sub-projects)

In rough order of size:

- `bfv_lower_bound_input` — explicit construction; classical, smallest.
- `bfv_pruning_input` — combinatorial pruning argument plus standard
  multiplicative-function bounds.
- `bfv_omega_count_input` — Selberg-Erdős / Selberg-Sathe-style ω-count.
  Mathlib has `Mathlib.NumberTheory.SmoothNumbers`, Chebyshev functions,
  Dirichlet's theorem, but the BFV count is not a one-line theorem there.
- `spread_disjointness_input` — Park–Pham (Kahn–Kalai expectation
  threshold). The biggest single sub-project: needs finite product
  probability spaces, increasing properties, expectation thresholds.
  Several weeks.

### Stage 7 — Audit

`#print axioms erdos202_main` matches the trust-boundary list above.
Optionally drop the `bfv_*` axioms one at a time as each is discharged.

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
2. **Stage 2–5 (conditional theorem) ships second.** This is the goal —
   a mechanically-checked version of the new May 2026 contribution
   compiled against the four axioms. Do not start Stage 6 until this
   is done.
3. **Stage 6 (discharging axioms) is multi-month and not gating for
   the conditional theorem.** Park–Pham *will* be formalized
   eventually — it's what makes the project axiom-free up to BFV — but
   not before Stage 5 ships. Until then, do not let the loop drift
   into it. If a single iteration starts editing files that look like
   they belong to a Park–Pham formalization (probability spaces,
   increasing properties, expectation thresholds) before Stage 5 is
   complete, kill the run.

### Trust boundary discipline

- The four axioms (`spread_disjointness_input`, `bfv_pruning_input`,
  `bfv_omega_count_input`, `bfv_lower_bound_input`) **are** the trust
  boundary. **Do not introduce new axioms.** If a sub-proof seems to
  need one, the right move is almost always to *strengthen the
  hypothesis* of the existing axiom, not to add a fifth. Fewer, more
  precisely-shaped axioms beats many narrow ones.
- After every non-trivial milestone, run `#print axioms` on the
  affected theorem and verify the list still matches the target. Catch
  axiom leakage early; the alternative is a 14k-line bundle that
  silently depends on the wrong thing.
- `sorry`, `admit`, `unsafe`: never. Replace with axioms only at the
  pre-declared trust boundary; otherwise leave the `sorry` and move on.

### Mathlib / toolchain

- Pinned to Lean / Mathlib `v4.27.0` (see `lakefile.toml`). **Do not
  bump.** The other problems in this repo have been verified at
  specific tags and the live links assume them.
- Run `lake exe cache get` at the start of any fresh checkout. The
  Mathlib build is otherwise prohibitively slow.
- `autoImplicit = false` is set. Expect "Unknown identifier" errors
  from missing explicit binders; introduce the variable properly
  rather than papering over with `_`.

### Sorry hygiene

- `sorry` count must monotonically decrease. If a step introduces new
  sorries faster than it closes old ones, revert.
- Some sorries block others. Roughly:
  - `residueClass_inter_nonempty_iff` blocks all chain reasoning.
  - `dense_core_from_spread` blocks `chain_step`.
  - `bfv_omega_count_input` (axiom — no sorry) is consumed by
    `chain_step`; do not add a sorry that reproves it.
  - `Optimization.f_upper_bound` is the final consumer.
  Prioritize blockers.

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

- All `sorry`s closed except inside the four named axioms (the axioms
  themselves stay as `axiom` declarations).
- `#print axioms Erdos202.erdos202_main` reports exactly the trust
  boundary list above (Mathlib core + four `Erdos202.*` axioms).
- `lake build` passes from a clean checkout with `lake exe cache get`.
- A `Proof.lean` flat bundle (single-file, `import Mathlib`, no
  project-local imports) is generated and verified on
  `live.lean-lang.org`. Mirror the layout used in
  `Erdos/P42/CompactCayley/Proof.lean` and
  `Erdos/P283/Proof_flat.lean`.
- Add a `safeverify/` subdir with a `Spec.lean` and an allow-list
  matching the four axioms, mirroring `Erdos/P42/safeverify/SpecCayley.lean`.
  See `Erdos/P694/README.md § Verifying with SafeVerify` for the
  reproduction template.
- Update the top-level `README.md` table and trust-boundary section
  with a P202 row.
- Update `BACKLOG.md` to move "Erdős #202" out of the active section
  if it lands there during the loop.

### What NOT to do in the loop

- **Don't refactor the trust boundary.** Don't rename or restructure
  the four axiom statements. Downstream proofs are written against
  them; any rename cascades.
- **Don't add features.** No new theorems beyond the seven in `P202Main.lean`
  and the lemma chain that supports them. No "while I'm here" cleanups.
- **Don't formalize Park–Pham *yet*.** It is Stage 6 and yes, it is
  the long-run target — discharging it is what makes the formalization
  axiom-free up to BFV. But it is the single biggest temptation to
  start early and the single most expensive scope error: it will
  consume weeks-to-months of effort while the conditional theorem
  (which is the actual *new contribution* of the May 2026 proof) sits
  unshipped. Treat `spread_disjointness_input` as truly axiomatic
  until Stages 1–5 land. Once they have, Park–Pham becomes a
  first-class target, almost certainly in its own subdirectory
  (`Erdos/P202/ParkPham/`) and probably with its own Mathlib upstream
  PR pipeline — see `BACKLOG.md` "Mathlib upstream PRs" for the
  pattern other ingredients have followed.
- **Don't formalize Problem 1190.** Listed as a follow-on; not in scope.
- **Don't push to remote on every iteration.** Commit, but only push
  on shippable milestones (Stage 1 done, Stage 5 done, axiom
  discharged).

## References

- Erdős Problems #202: <https://www.erdosproblems.com/202>
  / forum thread: <https://www.erdosproblems.com/forum/thread/202>
- BFV: Bourgain–Filaseta–Verstraëten, *On non-intersecting arithmetic
  progressions*, Acta Arith. (<https://eudml.org/doc/278905>).
- Park–Pham, *A proof of the Kahn–Kalai conjecture*, arXiv:2203.17207.
- `formal-conjectures` upstream: <https://github.com/google-deepmind/formal-conjectures>
  (target for a statement-only PR mirroring `Basic.Erdos202Statement`).
- May 2026 spread-core proof: `docs/erdos202.pdf` (this directory).
